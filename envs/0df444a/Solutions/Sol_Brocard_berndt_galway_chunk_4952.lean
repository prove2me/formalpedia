-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4952
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:01.40881+00:00
-- url     : https://prove2.me/submissions/edfb40f8-dbc6-4c7c-ae34-193d7d68d67f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 890467625 ≤ n < 890647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 890468875 1250 890467625 890467631
    0x20d1401081c0c08300f06060a050a121a01110105010602060c0a090e01030b162a0606050a030602191e110c090f160305090c0114072103 60
    0x20300c91501c1d03aa0b800d540010404a030b4410302c040d06550144030949001070254201034070748110714068070392100081c408401d0000707403164080d02d0851030400c52a8080344021400700103050010008801d4020260342d8002c014001401035030043c4519110031030300317054410502c0482216503500340308500000685001514004800300841c0050007841d040348c12540241c88a6107501000a04a61110b1026420300011003000142e2400340d0011500842c0076003a2202582011034400c003411028020540400c5000000c00b1000400e000c1c0001090b0800669810048114036141000d41070039845264098503c000c00014030031150001c2c0794004100d01d000750004002c0500740c03400410b91054040707407030200101e07000030f6000e800c190740c0501405d8210341145202c100055981034080311040c01d07596462007030181440040200d80882070079410184411b283c2100c820b591111414900707810004443e00d0b1200c1382d90298215004a500f022412062482c08003c01c40149407030160b11000902d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 890470125 1250 890468875 890468879
    0x106032105031005060903070f06020703110f032a030708150610050901031d010213030b01060f0c06110c0d030b010e150d0b03030405041e05010603090506190f020d1401 74
    0x8030410840744070b43d00b814a4944440d00b0803041c001c0c00d8002c00081500b51050001c08610b80f58101140b0300101a240d004000d640c1c103514007490030f9030510000d98004c206580c4e14403410368000c113002040602c002d4540768003419001c56107241034020000305405001d00e0101107400c0201188901a040500c03502142585800051210902140124400040080c40038480c0c0750300c41d42000000b803140780083c403000300516005071308903804244006040415031a0400c20003a03183e001074018030300780c00d10342d0f81c4041000e00609101c04161000749020b07a17802c21540c00c0850742042d140a001907504884a07000c04140c041d0051150416442c041031549000c01100d1520003071400014080600c0315081511814501003e040e10010702545404103000204d41511140f00b80d14050030030025040c44488060002021a10181c105008260508007004040b81c030008566802070082e0400d180d415190342081c50003004c4140c91000020f00014503000d05400c01c0d088103070b80202440e1101a683d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 890471375 1250 890470125 890470127
    0xd1b081b091611010b1f0906030c120b032806060b160201030f114b030a0f051302100e010807031d060a0c0f050906031504090501060321 60
    0x18030304640b5140e0a100c2121482100e5200f45800c102140d428000410811a80b0b4009003a43c010995030119058100035100140c81c1e02954041c02041c1500703041160300300601c4c00501205518000c0d0790307a01e071912a01c10181e2800c00098040d003548114010150601c0d1000207804881c1d804156029414000046690301c2c00408480c541100c12a0030050070409070300560203401c1d4504900009540c9a200d40b042e04003400081041d070107841c005015249804648195108001d01c401c0c0c0e0844c04800b0b80309450b0f1025501c2c00e0340c1442c454505480f507507410010741c0601503100003180312900303102c01d201d00b03000c00c000b10850f624422103100c001482c0340704080711030322140c1041341c1c0003d4100003c18801da0180d070204d03071000095070a40d281d00e0035042e1039074980030f0140c0341240c01d1a42c0d0643c100706a5408094102d0f100000c0c42d020340791001070f20000307a090202410b080c56121185003038000700c0c0c0e51070b849504001e0b8444024402075649051510351412840000f203080340c401500c41340b4607 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 890472625 1250 890471375 890471389
    0x80601180b06071e120f110a0506040602070512040801091e03080c0307090302031605010201060815150a1205060a0f0207020a0e041707050a0201090902030c090d1b081b 74
    0x2180301a10b0507061000d540c903040110440110408003c0030724118007800320310100703003140c501c1030303a51605203400c0b00f4904010480105150b8042d91a001401c1040c00100045a8980c109030058405a15a01c850400c1030403d40030340744500c02000d00040c0080c401d40706420040c440350040604a20040c1c210350080d50348010740600a001038001e800142540d081031000e150480e0480c0f40c8450a00c1e1250b0210b40b4003480081040855900c118080000f0741c0d09000b55405018040040c0c4622044500343d614841e0010b0300e10000c6039502404102c154480070f1802c4001c000d9800c1105513648141401503c800d8195040c48415040400c0d6184a8020b8001c031404194040d06e50300f02145082034002d61204068030840d641a4880d00e44007001d070584001e05081401034026054103602440090086041a440707403550b00d00500400c07101141040980c2c1c00b075001074680620600d200c1c5444005032000c05080d4014240f003400100381c102d40041e170600c00807014656420384980000400000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 890473875 1250 890472625 890472641
    0x6030b0108070c05010f020703120f0e0a06050a110f03040b011e030f08161a06030114041101140a0e0307170a080a090509070e090a06080d0c1b08060118 67
    0x4648100c01245007144941c0409404134043c1c0300018100b0b01c1d0b81100c10990740580320a400041d4a0a0f85d039900596500c071b50b0500c1c4540140401500668000050302d03092a00382c05446603544100260640d0f6190b0410245500881d0b040b5540710f1000c2ca40d40640e0f08240d80c00e58402134440004111141620070003820203045446680c046441c42c0d8602d401482d255008076501d00c428800254080c00d0603012410803413045400441890f420f004513031040c2d60003030810707110740c0c180b0100d24407440d00c0220150b0425003001c041c0344025041c400607582c2c2044000d1115070a580000c2e00b42000b54020301c9031b44a1032044095608855544038504000c0f441c000801314217802c424030f26400507240f4801065640000d04110000c031b651038000030011801124140c2c0400c81d207003815042071408008a41e80310b124100200f021604104000f992070454185e0607081c8941c943c000720901074103680c12504a00504c44100c040c81e01c40c0c20301f60321a54280700345114101d0103161514290384501503066 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 890475125 1250 890473875 890473877
    0x504320d120e010507080112210203041e0608180c1206060f010e062b0e01020a0f1e080702010b120703050c0303180907030f0515090108012c0f06090a0c06030b01 71
    0x1050764201001243c848400782411940881c3c0005c1c80350800e4228001d24282080a4000e98cca50745070684012845160a101002c2034045507028031207950840606030304508038800e112800c0c42440089490820401e01056000980700100c044081000803018401d10080c1d42102c00002200015940003680d0801e490380300a040c4420a10070300d6400550145480040c001c1764010364800d86d03441184d80710441c001803a500050410b400c540c02c041a4020319607185000110250b9901200d10250716000801007000985408030b00b20740d01c00d400001c80c00c0c0307005205c0c55108602d121115600e000301d07c800c0b1014061035032100314034078002c8107841c6c44032040c2c0404503100c85424104507224070300074086410706641300d0f8007031541041485040e204200b00380740f12910480c148204407007074005901084660b81001a012440448a14071081017140340e440300c0002c0107180c0340c03103080c016540100f0035070f4840c440800c0907548001501c0304049008134501174105490744000c80a03600c900620b64 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 890476375 1250 890475125 890475137
    0x302010e09060a050d03110c10050a0e0312040b0408070e1621020c010b1f0203041e0801020a02150703021602060703030e030f0a0e040504320d120e010507 68
    0xd1407801c110210507484803006190030607503610343e40058000c41155074280d00082c00d9045000101c0c1c000c000407840580c045a403100505042c030340c01002c900c03070b00d86124208100c200017104a91001c01c140130401700c2c0e0148050700e0700e80301c079101e0403240c003e481250b0152150702c80001c0c0c15030312881c0131402280302071140d20485411540586050308107500811076101d100a08400300c3c2550701c09030010000000010800718000300402c407201004000895808000701d0203142a40d400200701c404541c4007226610000000d200c0c0890241c03e0f0b6800000701d0b50000400404640e408101c2d8a410301d800b80d001000e0f0344507000d08600700d000301c5103c3c03402e01e1041741c00340d0054603200014086843c420314000c902030910b006928190f40140703000d1489202c000c180d02c1111038200c0042d4984240948041007585416200c404494403042644480355508502d0350410101c0d003920301c0001c01e0803508440c2d8890250380c0c020000c0811500b196822450041803690400341030084a004180e199298 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 890477625 1250 890476375 890476397
    0x601080412050903060f0412110718021c050907062a060209031b03071706150d0606030305092d100201060302040e06010e010e01060915050c1902040e0106030201 71
    0x100300c692001d0400300040c0501031140d0364040d501003008522420392003002030b045007058944a21030707111a000c0780040c450b00d03444a0405c601c002445030110b0300b840d802c0100d4014a600600c3c02032044041d4043e45505001021429801c0e076007203540240c05010440b406185d44081c1182c40495400600d18048024500703408034605c041b6400f140c450003000010300c1d02e051000020729040f003103803801030502134102040074140703801d000a8008062550842c81402044003289444010041c00000c090311181c01e84072403921000a0039004540c00002002219100c0c240504203400c4900341c0d501c00c08080c92070030110120a02929261051002c001200d1081da104005021010307000d06411590303544400400b40e51103008016030607058034040c00103541805e060070340000050b0443d28003542514010450706500c404000107e03001d404e0062110314a0300003c0381c503032090070844400c40c8500b041c115200807440707000e88003a40c0b08550804c9210384410030982a0390b11440040d011800501e84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 890478875 1250 890477625 890477633
    0x80105042a15030f090f0606060215130f120203121005061206151813061a1c290102011a130608011103100e0105090a09051c0c0203120306010804 64
    0x42e002e072114180410060815500c0104440018605888403107501540800b40215480b90f00d000d0310352032000d882c0060403100a0b1081c118043d0502258801040002060042000e0490b45650b40039451a03103035281c100000756660007a0040c480901000c03400b042900040380b40c1001143d5029081d00c0c102103c5480a0b00c4010740200001c1e0801002c0003250704030a4000c0040c810055a07400b20444011420b042c07088030b40c203400c140c049080c6050f100b48040a04400c01c45e0112800302e20b0f560751621088902216140b08000d84130340c0c50301b40941a03c9811004030402c0404500206400d1800c0021004900340d41160300111010241001800042e05104a480c8a0100d43c00310115100c5c1e41e46d031001c0d003110b402c800c2c04c0002c00c4011080c03003803201c0c1c5030010b0350050503500d070345c000194180400101d140202074040d034421543c0d05884810042e00380f000e1011041b0036808000350561401d40507010300002d48003240710380520000c426600d00000280c901451060356600c0c02540d0341e40d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 890480125 1250 890478875 890478899
    0x2010e19080c0a150606170f010b0c0a1203140610050906160c140108010f080c0f01021606050415210216050703210f1707090e01080105042a 62
    0x911a503a405070030180404103c0c00c40c4d80e40300740c1d0404070000601ea40340030401004040381d0f01e403240d0911903c500303010700d40e6150056241915090030002c4e03510b41d04608070314030b0310f580043e00074070017130814083c81440c0d505075104005460715425400c0e610703603e00080201c594186450038000ca201030100c80300b9420103402415420769000066080d100e00d94688543c10741c3d060b0300031400e041c2201c030440e0351941d00242c441d0041483d80c0354840651304000460341c94201a44850340986031000c40046070b60710030801c50406200600001c40340c00d4403450001d149031f01a004050710400c0c91140d05880d64441d21441401400040c415500d5813184d2903943c01950005c042088040d051032010008074106000701d50003507108040d1791070b40c0c011440150000c2c40d60703500b070310061000d12040c036400b05800540110340b11003ca245c451081ea5120f00036503a00c80300d0703000501c030441800c0c0003242c0e07134505612060040b4003c82c0409031070480768441c4084160003001c140f01455038240d0030490156044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 890481375 1250 890480125 890480137
    0x10e090708100f030602090109050315070f030209120106080f191407031203060503010b060a020d0e030709112218050a1107030c03120c2106031a0702010e1908 70
    0x40350608105540f08000c120740501e43d082500c1807940007821492640e0404401001440c0c10b030702070040300d00b403c0b000c031088500003800c40d001c0c000b0842102030b003d4801d90441e0040000107111113418025590214024082802607400c1e0b40f2410b801070400b100c000920340701c210341c2c212a60582441d127996500c100d0300c50314000c002c1e9101e0080d000c40090226440b012500c403465400148503441c060070142550300300c000c994010381040203d04403040d40070035850344a1800f0300b07018081c40402001309180c5101a8080d0703d0041c0340c4408900084480b50080c00034100031150441c1c58466044000c5030008248524086032080200d08000c07040c05030805035016403500c01c000780c10034203401c8481d0f0960000c03004400040101801208042d0003100080651031042000c1043c40d02c00704025052002d01e0360134440c09400030b500400314580f1740c4c104201855200b075842410384030590212003502c60680f098005542001c198460304400010400203000d4004075004e2100101e8807804d11a038004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 890482625 1250 890481375 890481391
    0x606041214030c0d0807080103030509040c18080a0309080309090f0a0b0411120f0106050d0b03010608010f02300411120d020d0215060303040302044106010e090708 72
    0xc07114080c804001d1000d007003100d6800c0043c0408850f0300718010201c45008103043c0500044800500100b54014280e980c040c20503103000504200c240c805170760050a0301840c001d040c443e5540410b0001012075024582403194445903081074441c001983c80c0d0040044498002c07440c0400540d00391590354125030000b242030000642400800041070543d813807580d4000444030f00040d080408a0715038111750748841005282c0f0004e506005c0010b041d40300d101c001000094444200e92101e43e0207501c458018098480208043c1c140251410080c0d004121100c80f6003403405a03543c400b030020b01300148801d0b03144070b52103425a01e542d1920f1030361000c01549504590440c60310012500104800020b01245400915401032406d20091900c2c2a0030380041e80e04030070a080c0459500d000040d2015254101ea0209000b01d4000785055552032085030703210000300d176040c43c001a20030003161071414207403d0110361190340c0d600300556821003802d81c0325800c40071040000d100e03c0d01c2002410340001c81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 890483875 1250 890482625 890482643
    0x2010b0a0e060d290114060c0a0b18060f010602010e1b1302040302130e0105070c0302060c030a1103010306060e010609030f060c09171501050d0b0a020d02130b030906010e06060412 79
    0x15413140f03150b410b180122102c2d84200308000501a100c20011020480703035044598610301056250701e180c44030031806000b000480310b000812001c4500051522000301550f04030b42d010f2815005180c0c40803c20f1040304050f520b05000c01903030020100d40d0080102c2e91500e40018007510382d06012a10845030742d514030466080c40f010005a07194082c800f00d0080c01d034408120700c0c01c2c2d03482d01c03400c560000e0504010f1220f420400000070703401082042c2d01508040c4a107849541d8811a10023074071180303001040c5100008008020445d05901c25410340318100580003842c0c4e2034110a5480c0616408040c1c49440c00a143e48001401d94000f00402c41c0d0758540681070541d5840c01c001d07034010310107404003103401c021080d2030310707024244045004040848004082400380c1c1c590031481c040281401540302c0c0c0000d0017464408868040312114460b48140300040c59031800d2480c00c0b82c005640e1104203002d2540001420080443d0060160301c008000c1441d044c035141c0d04103c000301040342204c10000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 890485125 1250 890483875 890483903
    0x1150c02010203091003090b060a0513020906130f29071203091e110301180311010b0303030106030e0f07081f060b07050a0c0b070302190503090d06020a02010b0a0e060d 74
    0x11540b805d4101900d95403004502e000907845c100b00c41b1040100f400f070182d401018100182c0d680c2c0d03840014010821500107948400d07034404030350030f441042c508200110404900264903481521100212840004e81e01c3d131074448800c0c5500072020079100d088085a0030f220300707070104207404000c80400c50a420000740c407043c2c560b80d942040010903500310b0184854074049003400b40107814840b48640c04c1f0001c2200300a10400e032510309007008005410005c588c20a900350304025803250090030300040c1102c2e1603680d2040d000b80a080c18000c44c4225014210709140e01c00b8001580e403013964040c030064001c100f03000310900c2c6040101e101c08190991a12800208d9840c0c100c0100302107802800604048407086c200342d415031005902007560b111040105101107503011070b062110183c0042c17065035650140c14003524601952034501e031301000c0062143d0421419034028001401603070001e000c91762204041028040aa2248600451401c00000ca2502c0c183c40f100c0300c4548100116200ba00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 890486375 1250 890485125 890485129
    0x1512060f1914030f0a050d0503090f01050903030402010e01211109040204090e160b1c020405120a1403091807051612080a06081009141009140601150c0201020309 71
    0x502503403040400d00d00b03090a0b07500505080c0480040c508003e00149081090740e5912547c602c504110201007000c0407020614060051100e0b00ea21807031040203100c80d0802c103991341d407282d0068408030301258115034002c076254007070109901e01e00040210200310091424450028100310004d40c03500c1071040000c100ea5a58a00c0988007904500c040024000400c0c22800d1420b420781100001c111000d035820041c0d045540300b1520049004010311008000034090310300a0b01640d00069400040385001510002000074007910203070050030503036034208681040700e44910495500340d4121103841001e2031094060550541c001c0090314010b45400c2d50b02c403103800c00c80c4841e00102c6d68610351141c1c0b1039285510901c005d400ca014404c082286a1074031610035a20218149100f90250f22a03000c50144803c00012200d035041d407005581d24010300c40c54640c000c3c03160740030889501c0720503451888a8076002545506842d121050124400e0304150700b922000b5a2180c224114401040300c04559 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 890487625 1250 890486375 890486419
    0x10c0f0303020c07080f01150e1801020720030709020c0a03030504140a0b010303030e070617060d02091f152007080a1202191707031e0e1512060f 64
    0x5e165000140148041c0a503065080d00d5010420b50120790520310b092001c00008100d0f55000580580b4800602c050f01c0b8807507000e07015061000c0e04981441100c2e0090a411071100d04144a0840c2500c0049449004207012405100e100007095400b1b9a41c03c0c001038007951140d50480e004000000401c001c030108245081c00307281048800c4002500100101a0540100d010089800d00500250f0381040d2004081c200c8508003120910507070070104440da21540f000e05026600074010703a40314544a0005841c2c10200007407040101955800016902c3e0108204030120045640760f001c070114001c20f00c2c0f24000e0340d4024840f03500a14400181e081c0003040007110702c503c6a400039203018407080010303080c031800201030a0900c86c00451100012241c071203080c4c4006a584149484010074102120007030030313028030f040003560340e07020090703a650f0040d9100544d004212030451040300010220103483c00340800d0f1890070000807020604074600221100c0e130401d00500700d050501c1c0820000c8404c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 890488875 1250 890487625 890487629
    0x2040501081c020105070203121801050403030b10030b13021c0e07050f03030306100302030a11040f09050112110603060d05031810022109030705030619150302010c0f0303020c07 78
    0xa1540900d41d0501881442003a00680b0803550000700010f02c4c0c410b82c043d45920855544039103102c03840000030034021350030132100702808241b8020043c51406240140c0205444209a4410200525841d000500c00d002e01030140c40041d03c6e11142c1042c064451003e5004403c5001c0b20109000c80a10b41030010300c111075542d41103600810109141030140448005000f000d94001e0300200304001e11611859002040506246001603032955199209001000c514040303a901d10800038000546488a1031101c007900e0803000304010700d076640c45441c1031920700d4080040c441c03407100c41e1a840d10300e0545c015560041c00a0525100007090b503075040e04581c40710101c0307030442e00078041c10006410503a541c43d14080c050b00080038a0030f00b50084880550500700c4000545400080348540f54038144551801444081d0072640c00341003201007400300b50741040e8100c4200d807074415042a60200180a08201c03501a1681d101c051119110016043c0380c2c41c0c41030302495001c100c0700c160b5040c100304403c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 890490125 1250 890488875 890488889
    0x715210603021e0f180f15101e08060d150b0d06020a0f0813021c05030a050301170a110603040c0b0307050927060d0303091509020117011a0702030a02040501 69
    0x8000d0703400790030072a4184009408a0281400c1048140020a05c201040d0044403660b02440566940205801c40b01d403248074140d048500340f02d000c19280e420003010b00c001001c3c441c00e60b20f0340d00030b1141210802c03004c81d2400c2d0310905d05a01c0e100464560705901c0c0c00382c1c01c411070200344822020041040c0c110110320480300c040d40055001c82943d4010341c810300f0443c040c5040da003d0700b03009a445846201b035010192158001040700c028140000e016010314580c08015240c80e801040310180c40da4209224040e81e846185156401303280020403d221081e9101244070100d285d40d00501015810080041f13807400b21400380480c0a6441d44051885640d060303547c3d941c1c034100c04042c00301221110400070014104034040c0031541c114036a24640c010420b0f205214041a40e050840c0a03007800400903000d4064000d00601100ea07542017000a80e0007a01c4450b403914036518200c0f2548024403d80040c4d0350b40c241c0070140114040014908940000c044a04d142100c0c1c00080c1107030030a80c0461 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 890491375 1250 890490125 890490169
    0x1002030417210a1d09010513090f1412070c0603051f032a080a0f1a090a02100f0918140a05010f080a030503190e15010503071521060302 60
    0x12150391250808003840181c4e240b580c250107001002c00c20481c81801030340e1050901e246800000c040d82e90207000212b400454003d01d06149041c800984017505280040c140526042c1e21801101d650031100459403107040c094000c0d20f0004110000d14010780720f000742142c0b88459100c8544181c6542c80914014030040c454043d0120384c1c280b01c1011250070004180c0d100703104015001002c42e450031b10341c3e08160405444905840d00d40310564055140f00d020b5488034081c40900b00c80000e032101d02c00d1083d5031f020324242e4284000d44040544d503090000058080d10300740180b003501c0032109641d0aa400d1f012510741c2e00c041403e0b03020041110340c0011566540e004002406026465400400c06075000e400307140d4503524002d002c1c1c84010064000301c09043e0061450615561180c2c00924950050b11428104a141294100f00030310031184244120b07007000c0f4031400c40e2564144d0404454941c0810880314024415000f5504100100056904c04002015840703800159000c811343c60084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 890492625 1250 890491375 890491387
    0x9030c0907051210082d0a080f16080c010f05060409020306040f0510020d2429070606080c030d09150c020d080c0a0501061d07111c0e04050105100203041721 69
    0x40318440800c40c4009900d47e1002030800c000c1440c00b4210b23504440c0c8168099607821036400c42d22900510b50200804201e80083c4070b055240c0194401c0182510707890060005480d402d04210a070345550304007a5040e040000481d000420302000300100e00d214800f41c5008010081c40074080348c1024080c1301189131500e14160184002130100660340303040e10a03885405041c021030368803402c000d0034010546200c43d80070071403100030141595407495002c0030600c0003079220340040da107034000c142200703000f881082c0c050540180540c03030388000d468103c0b603510100a5556011202e8480142c41a0f822140d0180c0110100d88030b03c0090007550810030051040f60707040d01c0c1460845210358410070001c052114601460202c038080b0301d8000c4c1d51858001d001380044183c060801840b540c521801007181500c0c00070664021940800b941d008490401950fa41c0d10284044500c02107840d6006030001c0106000102c84d00c0e0480000d00c1c0b500307041fa030750b00c1500006a04010301c2c41e110859190404540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 890493875 1250 890492625 890492683
    0xa0504050a17070b1b011e0506041b03090201030b030106091b08090706260916090501030c0b03040317100f29160b0c09030c090705121008 61
    0x1034040204011108454419503050825841d07003018000d040130745074006400c6020340524403190030101c401030f0017000010000f10215841c240440b1170700c880603040c44001802441c0038407030303810400c000b441c0d0001c81c01040780c000c03801410400d030101d051640d24500194503403400d1144d00b000d00759900d000a6050500c08409444088a81e0032104005d14242002000030300411080112211801c0840300d00f14040c25842040885a1100308034080c03c5040043c0c0034000034041c1c000c04802c421309000142c03540410011746d13a09000240007501d50b120304005141c0204002d550080c000d1600100d070b0054454100b4500f030058441420b400301d042c509110308c8140c2d0303070700c8002800c0400c4013400080b00110350890a40d4100313001a4089804a0b815174044c24080d42d001d81950700c09545083c51070b00e02030210094102c5014280248121661f5408074105110f441d401403503e03440c1c690034150005003600c10001700520205461049549c0082c4c608410040391445040220017070348841c000c80c030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 890495125 1250 890493875 890493889
    0x72102030712030516030e2701080d1d041104060804050c06091c0201090f0602010e0d0305010b0f160c26070b04051e120f1c0518010c080a050405 64
    0x7a02c031400900311840000790010101d8074804622207540d086146a4281581c410b03181c094031542001400031b0741d5111010f0f44901030b07180846440c070590541d803680c10075a40d4009140310134010980c03000700c2c034082400c1050145c880500080002c0b81c20b04200c1c4030f905484e08542d00000c0424040c00501007045001c0c4180c55400b48183c070740b14180500c840000d4202e41881d0144030030008481d040c107003136920940c0c0020191240f800710b000d2042d40c401d4001e000b0000000d021020b030254807a403e4141e0b01c43e0280d03504a40420484a00f49105c078880c140b200da01c2070109500b031265200703006d000242130700c0c0c10400030107018030580301c58140d225000408250040c00840701c1d401c044c4003485524452016142640c0e41a1622010f940c08a18000403141106c000141c1c800c0610950201c40070001a014009940903c10340b175444000d481c801031501c072a40403170310110f041400807240d502038188043c1c0c0c1000d414580885085034940740c1c940b2607800360150200154000601348210b0074607170 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 890496375 1250 890495125 890495129
    0x30207090f0b0607030f020c06130303110304030c061412010e2703180a0801110a120b030a12030906060b04170601081b12030a02070f1e060e01020721020307 69
    0x7802d000c00c006480000b800f0788281e02009040c000080096011141b08202d401d01001c80901020b55400103020728070300c1c10155100803800201c40204002c1072850110503201101d81c4005a4202141800025556100800481002d40200744550344000100140c80790091204c900e40030740b0f81c00d1013410024100160080042c041410300c80d802c4d05184000111000008100d1162881000c080c0018940c036030b0302c1e4081d002c25800d120b0540a0309010340000d1011000d0303a1620044054901e1400041e0340500d000c0c81d90541180d038007540461039007814003003101c01c240740000700d50050f076844604803040d94111842c9110301050600800500c9104040b5504211008003007941c03514101983d01d100900c00c004400c0d906003000c41b5107413a0400d81103c1810034100303480c1c4400001c00000e665003520300ca003030b01542c2d05030000541c0026010101700e04400d80e0703c001900e28100101901c8285aa01450341184245180010341401c90041c0e0a8101c00c06500d506800d500b0713004061804201d6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 890497625 1250 890496375 890496401
    0x9010e010314191e023001030206072d110d02060f070206090a090516030501030308130c0b071505010e071b061407030203041a16050c0c06040303020709 67
    0x44038116480d60401074030b040d405000c4000d0b55803800e0301d404440001d04602081121490300c3c01059400604103a000350440001351214403420f000d488070403888101ea10741944894030403582c018005810284c2c0101f1500e07000c1da640b03d012000650b101e1000305003008003a404010400c2083c0d081101042080c091020b08451801c5144010780000d8001c2c4248c00711046030b060000b840d00110748424080d190041d10003000074080c55610a0080050981110b58000760b502002154480f24000e20846050b40d400d0750b1000801c2e5074140b0040a017015001086d07440e14409400012074130b2440009000c1e042c81044858a01e61001c0658000c1e41e42c1a080f10701035101d01c1c402c100000e5440243c00a101031288044101e209903424407400400c643e42e048000040d40c5410484c85a826400650060740301c2d190506d51341030701c540c490310786501c00d030b134008420710418106030304640c03040014008034800003043d1500c5181681c002200c99029500403005a0441c030420480c1464030b1141c40003030800703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 890498875 1250 890497625 890497631
    0xc01110102030c042601050106080a05010504022106011218061a0906011202090603010909020310090206030a09060b0d06050412050a0e040903120905031803031c05092109010e0103 79
    0x11407900303180f5601450241005800480c0d24402540c400c1041d400141c005800080005584982c40100503c1c0d0480d0303001d4115003440f0000959040c54400c031003086031508400c100405c2d014090900e07481c1c0160440341000f850403060031030010144200c0d03254074101944011000028a4910141c0d00007881d0f06450b504104101d030415143c0d09081caa00c8102464007c00c0107041c005550000d0280e94403681d00b0047c0840042400440c9034003c3c04814001c40c100c0704034010b030f18501d00955081c5103000303412090500208500070100d40215059074820b80380482c08000d96004a12100c0d1068001e4a41540b00d1040c8002e000720601440c00c0001185041450711704c82c2174002d0100c00c251a410343c002d030380d1020744100745442100c204180043c00c01e1b060110510074188503507070340c100d0030303140c41c58400c030800400d400d150010440d2202481d030800e040e00280594000301c01004010100203090040031915030300600c40c0a0b50703071010503120314455210710044000400c02c8102024150500d85 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 890500125 1250 890498875 890498881
    0xc09040e1e031305100c0606060c031409100813080c0a1a011505070602040e10030c050604051f0306030f080a02120412140304050d061b140322140c0111010203 70
    0x240d40f0302d502603030410b4036454546954100d04503406403245030080c0190345429000b2030300c0c5a000200c80c0e400c900139940c01080c040540c1c04044544502150380e54041010900722200c01d0260801c0c5038807200001c041d505180c5280c50703da034903505c000c05002e003941107a040c03041001064885422043e0b0588a58040d07581003030f14403020600c9202008040c4179001c074401c010130240340c0484010700310080d040f240c80e06002403500c1d032540e954001121074a4920303c010a45007844801d880803141d008045000c41c0c000000c24000b10541000007004040d02c030030000c40480d48070303213001d0744140c40346c0034982ea100c44c2d10000901381804d2081c044110380c402c010402004420017800d006803078201c5101c1d0348070544803002900d14400c99100c0c0d600000f86d202c4450520803190700c80a9039010365a2141610741c0341c29400ca0344211070042d0204403283c00e1012072501100750307854004079002002c0c00f55183c4400d03264400a40070340340241c3c80700d61290314003000325640500300300f8012402a00950440c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 890501375 1250 890500125 890500147
    0x60504020411120f0a06053001020906070212330a0b0904030e0f090a06090f02160b07020c060f2502010e2b060c08070e0306010902030c09040e1e03 65
    0x1890140c007400c509103030305000c55907090403540040c008040081c02085000d4203923442c141c2c2901101d100c54543c11039000c4602c4007801c180226446001d00500b15440c00c7c02d280d0070805180c0030100030302d001d881544140d623150042c803400400030808005c04400021082481e119040c007001300600d6500c1c0c200102c110040d01d0701003006401c2903260030080c2e403072404140070840d503c644440b51a40441e1501c14050040c0982d4041d030152003294400780000032005015100760310a6102e50f0141c0d020402e02c103c0031415012609130040342d2441070b240040d008400080c4180c01c41d1501c6100c020001a8040124180d040b0851125251102c0d481c006200e9030006002080500340840c0181c070f9020300100c01c4003d004150080e103408200100f140d414038189034001b4181c039080700c03010034815404500e2440c020005c20341c072220010020710b91607007001c482001a400140c07096000910500001c54555158001e0320f0003c11407200510601c2d0401404410b044a0380c030005426400400ca0b400840c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 890502625 1250 890501375 890501407
    0x23150f03010b070609050604060518060603070605071502030c1c0b18180a080a02060106181a0702060a081009060e0609090319021606050408101d0a060504020411 71
    0x464010318400d490315518200b54028040105c00100307036001e010100401c00401c1c0d8003650040305518982801030b102008250707a5031000340c0705164940c0c4030071001c20105100c0c1d0018103200d449005041e00110090805c14285d030401e5410300d03d4014003103211031602d00724604001d01c2654180b81403001402082c0400c603c841001504940385900800180002201e006010840460707442122886407546c00c0803610703038000c50b206070010b00880c00002003061250510103a415040320744070f82140d10305180440550300300d400c1d0720074025080c070030003026980351009484000116140c5000031300d8046a000e414903a15040480c2c01071500400340111043c42c140668400740c1910916190340322184520300c0e500546071901e1030041150030a000407680030030301020000300c151841d01040c0c0c813140240c44038080c0d4050322800343c3c408410320b2114501c81c0c101d175072003596001d080e410103031960b00d00303034203001d200802500d81c00e403100240b10450806100704114104d1074000e160404481030403150031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 890503875 1250 890502625 890502629
    0xc03080a020d090b0d0b0f130b040b0a0b1603170103140c1c0b06031603240b2d0402030c040602060a0b030307170f180f03012c030423150f0301 63
    0xb0307aa50746d2440c4140754a881b00400603100000305090b43d00b041e005101c50240091248440c05241040110b40741410000c1d0340c441a10f28007901103051410b101100400300441c4a000d0741000300e1484401009000401c1d400c0c06107000781c0c021840755502908161501e48040c030054007039840d00071a55100039103c07411a20040d40281810041c2c1c48140c0002d242201c1c0368007441c14000c248a00000304402107407031000e80402c1410b00d0001c60b03103034000c0c1e82c21124151801e94008808690108024480000c5590790889a40c81d40c01d0442d940d0703000c01c1c200c0c8c00894100806c900001824441e03244c040001c0c5602c6142013005019040350000401e80b20301a0080040000704c0344140c6000d51540b20041c1c0759005a031100560311030180355901c100703407a05502c040d4082c000c0a164040726080600a0320961900e102454401d00210556600400c40021202155000c28000400d0030000d118116a14841c04000c102c0d209124000300242d0216491414903820f01c20000044882030500070350781 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 890505125 1250 890503875 890503897
    0x3061e0601051308061815040201200a060f0c0201201207020a0f03022a0a1a07020904140c0915090c04050402030f0f1005060301050d050a0c03080a020d090b 69
    0x1880f01069807400c0d4458409821918150040d40d0030004c007808108071400920004c03d0803a0b124800d000e0300f02c21192030035503010380040c005070141c1d56034000c9001d6000c0315081342012510b8081042d25004c2c11141485c5580c4407c036110158200d000f0350902402d507021408140c000300d810b91070403001d002031241032180c001d4a01e0180004100074020f11502502c29084590b10203019010b00d0025124003910701c1c031940e0020300449204208208080e060b0700600f0240100103030320f0910b06e051440f060454682500e59200300f281074016215003c104e8000ca00c548003801800500c00083c13802c15541503249400ba05074401005018a5440c0c0b402401080c00e0b5140c501c140c4481c1d00110081c401e54015680060000041c0f18841c07046c200102d11070b041c002c00c80340300c1d9183d80d000b40d041d5400310b10440342e2146041c00180058503144000001c1e1622540890b01c4075411030b510508140741950003562865170200703811941540510042c0310388106071400d02512410000000348600503450340076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 890506375 1250 890505125 890505127
    0x11100906061a04030c06030e1906062c07020604030f08040203151501020d02070f05011206121515030b190f060902090f060306010507030c0f0c09020903061e060105 72
    0x2409000441d0721440103403441060190448800c0029245603078010722048403e40f400d0070b00050050300c01d04c87d03040d1a540c2c4a000c1e04805807603440c054400c4944900503500140c3d81d07400041e0306004601010884500c1c0c030700c40080103c0d98810030b0300c91607004104200f9500054200700000e0340c4240c07040e15103000c40c1010b900c581c40c0d600120345000505141d004d400c4c3e0b00700003030103d041a1a8a01e1250035426801c54500b00c0f08400205c1c2c0ba5102c910880d250614011010321566001d1b080d116a40f0301c13581c0d400104955130f1026a10f03059151881900d403d140c510300c001c000c000c1c41c020085140814100c01d0100c600d15520010f0014005111214212041c0403081c10241203804c601f039401100642840750a80b00d00d1500029840800010b00ca1002e442c48003a0b5400d102e01030b40d110b520161201c1c0c0c245000740e20103642d0002490802c079180c04c00313038440780b002902d000c1943c07001d030540d40d00050f15104507000349440c0003000b5010207000842200b0080b0a0071800c0039055022400b841d00c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 890507625 1250 890506375 890506391
    0x10302061c061a1b120d0b010311040603230402180414011536021b0604050307032c0103020f0903070e100614180109030b041407061110 60
    0x70000401240e04966040d2507050082c0c40405019406031034a00306080410040d070340500001603460458040020345100d0038030002440c1c000f40e600903401900b06050204401c448902020700d564410b130089008607589040002e40d00000b481c81521541585000c42043c3c1001d400203012017880035500108800e0820006040194042d440d400d16901d00c5d00a0211400c2c4032984451400369002e1940c2018511302081401500c0c004806501403000b011a4510200003108101940c0301e0591418000e038440080e041e1090f0030421035100e24002d9000e540c440d002440c00901100d50b480b0003a503000000304401003c0b0700d4041140a0803102401d0040e0b0b03d2a1240440d4028001d104d00301d035140c041e02000080d01c684000d0b00b82d225241c038811040b00c050300c0700070540d24032051303480300054550184084108489152030100482805040131100c80395255038615981c202100c0c202d41646036003100c0c1c03031440400c0210601801c0c450030b15200415056081c1a91100d402c0500e0b0030003034036507540c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 890508875 1250 890507625 890507677
    0x60e070e091b1204030e180105092205010605030606041109010e1903140609030c0604030e0105122d0c1806040f0308070c0e06090106030c0207080607210501030206 72
    0x1015401c000c2c05a40c035034507020002800e0a100034221401d038045543c021900105140c1403407101801908245984116401d080c00d0007000c440042080d440c1c00b00815003203010300842a01207030294031501c0080b44640c02c140038542440405040c0501850030450b056880040d00420350348640028030f07211120807000800a003462100c0681004c4414241101109004442040d070303c3d020f18010448401c0d0321402c00301c40d42d1f8414101900400d40020300030030000707841440c8064034440b0515165003400201c10080b4034086058409540019010000c01320b012054807103120100c40402c4d003d4044e140c01181c0600e6440b07180d01a4003289136070422030090365113107020703100038003c58460800c0040d2a8905010aa480080140c62020851100040148690500758842e62001c3c202201a07441d01c602078024000d010401d6040d40611320b80414450410010144038540556130307202d80c0c010707030044042c004a040149902c0c245c00d1400600150b00e901007101c82400c40d1803505041d586248007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 890510125 1250 890508875 890508901
    0xc15050d0f061a0703090e01030b0c07050c130e0d030509060114030f031602121b0108060d0b101a1306050a0908070612050601020c030c061b10020409060e070e09 71
    0x10aa0041d801c00381505020f00420000c0d000261181d10752902058450f2450345185800348801083da40032440002e124407404006010302502c14821140980341600006005d0b0700f004226001481d641e00c8402c40c14401080385003045101ca081c00c00450500050064583d9414021411161921000c544490301c00f04448403012044000341c2e44c4030351400b0010b2855540020080c1d100780d0852010b25000345002c6049007500c0041a005c044a900040042d070300c400e0010305480c0c0c0409003420b18008503c1c14914948035044030f05843c0040b904102507088822245074243c261120207204420000009480440c280c40017420080d844051000084681c01c22540200c601030090348000201d2540207540707402c03040c14003031041c00b03650740e15030049a0380d24003001301035455400010164880c3c1005001040e880860100c0d244071002100768a03843c4c504184a407900d2160b0004041140c038810b4070684000e4108815103000d14206810028041091020020703ca10130603000b0440108a00b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 890511375 1250 890510125 890510129
    0xc050d020d230f03030109060602030a080609040303060801020316030e0c01020a170403080c010926091203090604080606030609061603360b0a050721020c01020f070c15050d0f06 78
    0x84202d98283c8104146203807603030402e2141210040c20800c01003070460001c000d4456407041d42c2c0e503250308c56031418100b02489101070030a07800d02d56a01004142c45a0a00081d445050040d0f0601e550800480c0c0090032900e01484545194200d100110000d030323130220b50305503400c0d000150310703101c1c00e140c200002480c459035000400500c00010803440c8403c040d0000d02d5181c2c0031b00007000c941070b18140d03203001c0a4402e030704015080e0350400c00380c5204e1500002900701c4010410890f41800d49140114569500c9900078400a42c00fa604100c000d140030064180d011940b00081d1813a400c18148403034103280310000b0355080c551150207035068072890341032060002503050b05d948650503507810b59030b030103042d510000e031807000e031001c0001c0003000a070150b680606850340d611508140c5600702800b40240d0301080108036a0200b1416060240074009852a4190001c4955a603002d6107040c180746140c0c1e030321a00d41c054841c41410032094201065412540420001082c020030718a5203030b0042c5032a07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 890512625 1250 890511375 890511443
    0x90c060304031112030415051f080106090b1915050705011805060907080706030902040b1e0a0f0b0304060b03010e120a09050a0f03020409020a0f030f0c050d020d 71
    0x84100014140d0001200082d948402c3c1a24030340104507a44c02c5842c40100d5010b05a03203002c03408107003200340b654807560f8000b651883e10084160700300c000c5190703104240d0020740240e4582d01c090201076214401e400700b56038100d8440104460241441383e11483c00e00c105071411001550100300b1902410131039940c0c5502c40700800c02c00c030100500300181d0040e5202581d0f40e1061b00c0c0042c650b6100020010241d0b94940d0052612901c1e100044026204155040342c01c26101e07480c8074001e441c3c80040c442c2d500c42c0ba02202c404845034109000c18490f941e03020b1001d045d40000c081010001c81d07400c9070b806c02e80080021902c00b0042c0c01080c09010340c28004041071180d0004210214090303c00b0300b07086491a40c0b106c1c421a610810004040c003e80202c1004c1c0351004402c20043c078144e0f1100c0a09840038020800304ad0781c596180405025961003501c0c1d640704881d40c4010004035034111000b4042c1200d030b880d504901e40e008940c0a400c041402400b0040040305046c18a00c1c0b031207406803004603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 890513875 1250 890512625 890512627
    0x50f0309010203010e091915110316020f03071101140f181315090c020106170109020108010b39030d06080c0321030705160614060a1d090c06 62
    0x1010085074001c0d80248240180b0801100118800802c08219404500a1100c0c0c62010781c1180d201c500c400c11070b40180e41041e0342d070b8400920400741000e014500c2840d42d00046404480703170480187c1018460300342d4030355a0300100302000c0014148403242c84e8800081c600500542000d6041030b1a6100300340c1c00c40f285240100e5044d8444803a01c540c0c4c00d4062040c4c0b030000030305a4010b000d0302589c080300008410b00650820502101056034403441c1d2072070790380c4000300340c2540c1e8000030708030307103214541c08102079442d03140361006c1d0358000d4800c90042940715030407440d201400403450722129620500f00c4820b15203e40f6941031110659840c503641400c5815a65951025600b10006040c0d500c42d1441034006d10241c003501d450080346801045c240c83e09900004c5a480c0307080b211580c0001d00e00001d2050602c0030a60f090b48829910f00c03201e01c62100080c2562a04024030b10040c0c00815851140c50b60810070f11050300c83e42e0180f0000520b0180ca9816030321800109401c015500c8507603038000c0f00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 890515125 1250 890513875 890513881
    0x10f0503071d090a02090c09131b0503150406060221040605031501110d0e123c06190e0601060f05250f030f0f0f140c070305030d151401050a050f03 65
    0x10700707c0020050244100c62020382107410140510a171010500150416052114a42841800b400044d60305c40f9441440405480400b4005401ca920640050005070b0080c00b08101c00104c6070454625071a130352401c42e0510380f03070150052040c0300090644502803084420300d410b0303900903541d0701d8000d6802e07030594408288903000104081100d00085d4426030760a40740c600b088602055028010460411b40891803d010404800c1e20000d0442c480c03900c61201c803900d01c14001407000381d000e01601c2aa1601c0405074084c460309803a0200060800c030303004240100b2600390004030b440c228004a0402e29141e01c0740f19842c90264040c2039030449084455003e801c01c21800002503c98184280c603207007202609800d00700d9042400441c200c011071040903001c81001d000d039801d803ea00b18103404030362030038040d143d41c1414410141e208403055880800c051201488034041c0c000301007407d0301d035007043e00c0c03400308084e0860b8140380178203052140006043c6044c0344548202c645091000b044142d80e0300b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 890516375 1250 890515125 890515141
    0x50405070614130e09121213080d0608010903080609100303081f0312030c0807120b0a080a0317070e090a0b04060b0705070911070f0b220506010f0503071d090a0209 72
    0x4c086580b814903000e10382510442950240580b50078045e1741540f11400c1e501c0b4040c1c030290b09291a0280c48074603090024140c0310100b4042d982c054540c0c41e002113000210b43c540540440000f41c081d0b03109080c42d5080040301c9000c40b44d08000c4903014500700030317180c0341c074030b21002c100b0960f58011001c801032030070200130b100c3c0030345a043c00c90240c0e540c1003190010b0207004803521a410350310f001c0080c0c003443c420400f007001c3d50802c01c20350707800800782000940d032960210310b40b1404201c200c01044140400d1400401c003040055030000306420301e8101d801c41c102c0002c203003d100620038a2181e0b034503100d40311640c4842d8080005404500c2c04541e640006007001a42d0f51510f1140b200c030541815020f8407031350702c000c0c00d507031059600200c0c4401c088002d03500c0007403006000301401e002c09502d54031442606134800c0c2d0031201d54007820180016504040e420003a080254001601a92010760f08020503068034980c100e101001040554640e1900740c0c4660a00c0d03001d60000c3d50107070b40d00081c81442c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 890517625 1250 890516375 890516399
    0x40e0a02150901020a140c0402210c0301050303070f050a02210c244005090606032d0a050612011406210703060e0d0305040507061413 59
    0x2440c02100d540ca10306840882150952286862850050f00940e0f035800c0006c1118030b4400b00c038080c01d03007603440030714486003c18200d0b000b800540c1c1d031064102100769040c0340c035080440e0704111440318451856050102280e520303c504400140b8448546031403006004041c049201c450740e0080c900c00f00e0009001105003018000c1d48038410501504100c1901c502c0c03ca0103202441c605040018000305100c61075030300c1c41e0044080300d8600405000d808450001154801c00085481d5400c6103840d42d0303d20040c9201142500287d010346451820310031540d80700d009882d07004041d9034013641000489030041094108249c030b003050140d041d00034451283c0054200600c2884140c0302c003042d40070b00ba6221800c3c0c1c0e5010602071403120041000c2061410176010741c80c451020b56203040c8072a02101d0555280616a500a03150103076a120100360200b4140481d032003042052400340300300e0401c1c0e2140754036604244106428001031650840c542034814041d42d240d104491015000e4641c2d4144050035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 890518875 1250 890517625 890517643
    0x30c020f07060207060f120c120c0c020604050f1201051009051f0e06120f011506170f190c0c030f09030c1703070209010308090f0402030108030304150b040e 69
    0x540900011021800400250741d41110301d154020312410307140030030070343c0c012a091840d442000490501d001c0c00054900403154031017059a624145400b41400d180d048404020300a8100130980d0031800c0942d481e20140c50503a0821030348641d40e07142d10700004050505482c100b110700d50074841042880d1040004640071a07032500418403481c0d858002c81c5c054600100542c144415101100307024100134404c0b0325a0140300039000708519146400c00d01d181003100c0c0c10f10200750703440e0300030318003054040d403400e100031306060410304121040744401030300e0315030700401c040307007500300c0c200000c12401207071030a90741e440601801040400d00c3c1c0c05005041c10f07258070094003c115140c01400d1690b20820803103044a800172400302c2000d09002821494100544180d0307000d101c2032000001590329699024000c5225004080d83c5d01e40e46c00030310040d052240002031207644140010492008040101c0c1d03441584101c240d22191107000c426001001070050064200c2e16200010084042c00140b000c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 890520125 1250 890518875 890518877
    0x20c01090f060204031703010602250503030c0303090c0307051516081206040b060906041205030d150f0504090305040b03041410061a030108150a0204090f020406030b0a050307140d050d030c 83
    0x3d101d03146c08855810340300078465580117034450006c02041070302451f405d4034100c13081e00c040c0d43c405a8400c00030380345402041e0320350290781000081c401c030900200405140070340154040e040451500c1c000070180100c240c4211600080022a405100091402c80205503809101161984004400803503401c0040f2241c60003249008210301240c508441030311001230004000b0b40c5410304001211107074412100048405120501204a41051a003d1501c0d11a0b01c0c20110310050310b04500105198202d6002d03034003036403801d400c081c0401e50110440b0223a81c034040c1c0c01907480e100c1d442d018210421154248000740110a0b0003007800c01185c102d54100c980d081e8140c000f103401c00081c4181403200384030f81c000701d500c01c840200c20000d10382545c5505c82010100141400e980d88411010360b04080b4004503c2540000c0c1402000c1d010310500c005a01c1c19a003502c502ca08180200707030b80e01d805000c0c4001c01c0305000201300c0079544d407060014040354000d0a494078407001e8100500682a00b00c1301c40c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 890521375 1250 890520125 890520143
    0x31404150c080105060d0c201c0509030618031309060f05011707030e1504060c1202070b0c0f0403150b09090f07150e120d0320030604020c01090f06020403 68
    0x200161003000401d041e04e100400c06480c01c0c10441d840402440c1a01d400000e0226144581d0782c51038500c40c10700044c507000b40140081c84800e001059002c01c108200e403003802000d02040030305450014846901c41d00c2e01625503000070b81504210700c0e5000701124200800c0b0b01d0342022070402c20541000d02221460101c0c0802d180e212801501c003080101800343c030740c402d003000080c06203200e50071141c0d042240500380d0340041451020203c1481c4100e60545245071118040c44106620496981c11182c0f114011403c0c81116503031a0003028019010340c8141c02c0c0411820080c240a0044500840d800b00f4545000e0012405210141850f4440244500c4008000440c00030010440203503202c010409001400c0c181111440342c0480100c100040010b09081c20000752607001d019403e18800c403000344424102288000d0039a00b541804130711315075042c00e400904140500a0b60740118003120050b032500800d5042500401811760058841000b00c600c1109003c0c140e03000f80281c900a8a410f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 890522625 1250 890521375 890521391
    0xd0624030b01090b01020c100c08030c0702030d110a0201030b06130e0105040b040908030a020708040e04060f0e071d06042c07090203150405100302030d0509040f051e0703140415 78
    0xc0111034024076136901603003218408801c1803401500000c501e2000b07042070210032950392206c44540d002100c1c440100d0000040007400e40c0f40c20002c4025401c1285002d4100c008401a0b050f2182004c5100074185500c40c0320130500c665030301d41a90b240b02c0900144002c455620f01d60003420003001e2041501642c68100c0d004107c0c20030f4080c9035070482d00806030b585942ca134080001c0080d4003100040e120f1620a202c046083c2d07461001e4a80664000d81000c0303500c89160020104036005003828800582c071883e41042440c04202c0e2102e210039002011b07420b6075403140d0110307001d44492922003044440f6102c000982e82030484810400e607042c1d008440b5041d44a00a03101244000e80340101c080240d8001000d00303240a81105600140c8121003504280d40c82d03002c6803510b215007a000b00818000704824806003050b10444441c0d944920703040c0194101030071201860003808110040d48101040020000c0d0700a80112041c400c000142e8512444c007814500002c41e60545044580c90a05c0b00c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 890523875 1250 890522625 890522639
    0x80d030b011e02030a2a03050405032e0b0301110301030c0f0b03010807090b041b0801210b040605041e030810060f09060513030c09050a050c0f090d0624030b01 70
    0x50102ca00626800440c5003104840c006d542c001595a040440c0c0190306103024000d84c690850002000c0c440e403215500d0364201030400d41030120f100041400050f4100b400310809200621480140000040010b80500c250780401c0c058003060030000e004c000000000400c00002152900c121a070b14035088407025224422004c0300e00c400e108042c03580e80302c404c0a010359031041e400b4018518004100081d895511100c0300d5540c5459040701021500003030041003600c000b00c05080c80640205919402c0d0700c1c107030f80c801190280180000c1d0641da51140004c0400c03c42c51241c840d050f40062414100904518000b4030741401255480042401a09d000078210300801880300c0300d55281d01d039490000e0030303c8812907c541040301d01c40c600c007a4403003001000c00d1208064001409a055001c50349180404680b001ea90003e8060b2071b40309000c0206048124010007030354072030281101c1061510030942040e50140801880c41717154100c01707071f15040d402c04030f0086030012a0b02c6180240700c941e9841c84 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 890525125 1250 890523875 890523917
    0x350c0712050c07090c050403050f0f07090e03030a05041b12020f100c02010e0a0b040906090b0916030b210109110906131d1207050c03060601050d020310080d030b01 72
    0x40b200180743d000c07040900c142001ca070403092550300c0c540340c0700d41041d61740d40340c1a240041c460b0341d4440c2c9401c046030011000c1d40c140710a030003600b0034600902c00c000352004030550380d01c0018016188550390307001080801c0100b0300c1110100205903080d0004603161941140c40b038000039005c92107421401d0f03000c0d4850801d1546648510496240d039a804c00c09a001903800d5801c070182d44c0c7d44428500008511141c0c0c0c0ca02800280c100b02c800001d000c0d00f0301c0441c00032954402c6902d840b809091082090300745452822110200307407031030302203030f00185000402c500030301800720001c0c82c2509a4000340d803000154044d6000e54081d041002c1404805030900502d03803010340754241c01c0701d80400a4444030b442d9070440088800c0200581d24500e180300e504608003541516504c0d4001400546601032000400075620301c40011400343c90142888030002c0c1451151050451620360003000260b0b54525011a02d00100041006c1d2965a02c103554001d0092541d914000e001c505401140001208401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 890526375 1250 890525125 890525137
    0x40e0708060a05010509030a061d12120105100c050d08060118050108060607020f0d05030309060a051005010c06021303110a0608010302090f0612070305030307140703350c071205 78
    0x1600001d80303075082800440b00c90740000c1c0c6e65034042c1316020aa00002e103c0e44074061000782e41c3e16400085100c0c6084031350612444107003041441c4020b01601c03069102d1101042e044a40403207841944200a04040e504814034030406071450240c4141e844c1001e03001703502c85100b410260394140308002d20320030380300d40a0018044d290019500500048042c20888020804180000c0a9820050303400000449441c48451f0031a0b854102101b4001111000c10145800400125040c0020b103000701100100585e40c2c8905410420210003413028000380c1c0d8100c1d00c4e4401c000c035515805a0322402c100e00c2210100402c50b00403442e04200140581c0b18444050507264010101d0040742c0360210040103040d0050300140c1d010010540d00b40e0000c40810500700207500c0f42002d10345a00d03003c60094201000402070888219080240703d0010f03500800c507809240d080c881444e210f4098254042200008020504014641c01c0c14440c100003110003074411184034142c130300c40344030203104200d40310f0142d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 890527625 1250 890526375 890526379
    0x605011802090a060f1707210c17130c081e0607080c07030507120f09050103020403050a081312060c0e09040201170c090406030507090e030702060d020a02101d011113091505030f03040e070806 84
    0x1c0ac44000304962542115a00a248446000000d03404c9440383d00303400c80c4a0340b007061070390b119000a20041c610845186201c0c22050040d013540d14007801c0103442a00f0091006c0d1081c1c10010b00c500c2018019020340740b0941e080005070140009803440034041031004100c944c0416039030078001a26621a000701c0d402d0740d601201800e4940c9091359800c0007500b000c42050819540d4550118030211558500c08040c1d004110208059100c2c050150022218100660091611208107c0545d82207100c4806e041a55000c404140d510200d03200854015583e80c0742d80541450350000c107000b0001888020342c0e0b40c0c01000c018408884c030b1896941c0c030030800020b4014000b80402c4030101440d030b0107450040c01600540d0043c00c010800d01c3c1c2111404042020010703c0002107929030307442403051080b066011082c503845e0a42100482c0c3c45440244500352a44e034496031000c2c01d035070350501000d0041102604803145007110302c0341c00784c407500680142018250820000b0f13004500c00c0c2d42d443c0c054000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 890528875 1250 890527625 890527637
    0x603060c0f180907050d3210031212060906241413031a04030206060d020a05090c0a020f0604030903022b0605011802090a060f1707210c 60
    0xc00c040076500703a0020506540d00b0410b0400200c0d00d61220400c0e144980c42980d9460b03074070410080d4080469070205414200d00c2d44081e01c0d0b00c61382013a14195214400000403001140c2d60340c4003000c02d07074011908010481010207045546080d04401750f511b0314060b140c030500440b41c0f038000c1241110038a10441d100d034030140100003903c12221900c01804c41e060314044048000e680440d01c5942e00c0507582007228002d0040030010302000c508003200c8040c40e42c151400030f00b01618000e581d20809014640300f44a42402c800456846603140700c010f00c00170340035114501d002c00d00300c581e9070803185281d005806000c400c8040590045003a520403175250300c030b4028240c1560240505c00269100f8246c400210b211074400e0703548654802025207200d00000300b41507041032110501072540550480c0482d00512490341180e54101040c001d4032100d00d0700014404e81000308455094906510049902031141440303107650788480c032884485c4004160742d482148411842e001c40c0c0c030f103600c680d0008a0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 890530125 1250 890528875 890528887
    0x106060f0201091a13050d05030a0b01031a1509120a0b1e01260a11010e0103090807060b0f0607030e100c2609120c1003090f030f02161d0603060c 64
    0xc915617400c19804000c1c3c030f9400300b00c2d6403442d10340058072540c0310105401108104280101d401100b84c840710070f00c0c0c14058401c100d441c1c0d201c0110510f14640c868450462018603a60340082a5504d00000808003a000b0001c074848503240e0808580a5500d5403648002440c0710249643c0039810100c00c0b076411003140e290201e605060130b050400005500031000d011281c0344000c00000d90050300030600d200e0881c0d003070000540180c0740e100034a414907081c458418003103050755040d41c800c150851700202c1d5118580c0d0000d1a00b040c4103910f00c0c0c3c03054021a111061541c8030307035040b64508095a80416071101418103840c80542031400801c500c0c65642e11900da43c1030b000c40c28540114000e0a1414101c1c01030005400046a0096100540c4148502c030a545081307491007c03a280f150804000e80390f00350f11351542e082540203000d0207101c003100010451602c200204043c400407411118503198485074020b0075404000c4103104a8400040030030741c1440c010507442c0c018600003205a10303000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 890531375 1250 890530125 890530163
    0xc070b04080705010f0e0c01090e010f0618080a0b0a0c030b1e010c0c0603090507050a062c15030105042a1412010605030123010c0605150d050106060f020109 69
    0x15100c900c085540c4c0d521480100d6460010303010754111a5800c10203086503104020005041074503d5000403c2e150160004000401083c64008140d0341946030103403403099060580280d100c0d0351b44c801407003841505000f005110b5050445400b07203220078400e1184c01c441d028110283c804206c079150b880401da5141040224002e1420082000103060038003655200e0340b10305580d141c2c1c035404034000c40c0c1c644084900f001070612800b00030749012141d54000078144040104071480081d0901c40c0300340c0c06039500e14403654400c0200000030b8020310310703d03200f03004e019460400e070400c0c45140e0141e41802e00012448002083c0c1c55002031440070b1aa07201070f1810002c0780c0501e407002646500c1c1d141006244200b0b5031805249001c2c04003601c56960301d500d40102c1c50a482e07446d400500d28118500b81c5154182c0c4e001029841c0c05400280110702529071542c034140041c00000510361054040852200300034040d002481118103685842100840900050b0709031060030000034150303008001020821 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 890532625 1250 890531375 890531377
    0x10f020a240f050711010f060b09061b061911120a15030506040b01030b01050306010e0a0b0109050414010f09110304060c0c0b130b060d0b1503030c1902090c070b0408 73
    0x700d441e00e010800c074641e0307000401240c00565013100010031505007059014000d0081c12290003490400704401441c1c802c40010b28015403080324401c2e100001e040c2e00807480c00381c2c40c0a0260741d040a850040c1484800700311502203041c1c14502040c00c0000d00700050350706005450010300f50352804585690f0300b2207501d0050402d05c4d001590021011000f2010600410130240706920400d54000254110308118000303650503403220f8800c3d8001c80052100354041c100c1c55070841e9206130041015051503005072000e25a64005582052400d01a01040407212a0550407103000c1d54203004595120070030310b420346d4590452810300d20f10070000b040008030542e0080c0468075880c60140603413482a03031586401c0b181911001280c107103581e511801d102a40d00407503008101206d81d042010780941d10755440190080a00c4000c1e0183c404240d01910280704981c0e000004109480707207003100d004480031800511100340c0c0560001e50007e50420321042c00c880040382c1102000640d9581c80c0d0350b111031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 890533875 1250 890532625 890532683
    0x90515010e0307080106090914030f070b251d09060a0e091207080a0e0f0a062f07180b0603160e031b04050708042102010204030b0114010f020a 63
    0x5403043c0f0b04009035010080c4a03100c00303401000700c081090b401d10b0030203426401c01400c10304480d8108005403e901c400d400120790400758400161a0365903030b103500104d071340d0902082119424942400f501345941d848811010301d0a00304410314041100c56061000d030b60310480300d4641141007010244a00030346c3e540030f6075000f4814012240100b07c42041102d0b2600040d90407900c00c41c020552140c055004040b401000d1420360391100e0800078a00000c60081840c0301c2d85e824007031a940b16040520241c4141c2032031564580848036039405140751199600858031801c0c00146108a4607483e0443d58000c031030010318024410741c115115852b151403d90702845202c01030140c420b0f204040d94030180b0503426007880500301001000d40311001d11041e62002000c04c000c200030b0320700700030020780340041080c0042c518201d060384010244900b41d009210300e401c041c00500100300000ba000b00d09002c0c0043c0c0c00801c0c2c0ea449a4048410400d0745c3d2035058a400800c10400f40003140c0d407034140f948482076 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 890535125 1250 890533875 890533879
    0x6010c0507090f060807210f030e031f0b0604151107080d03051501030e0a080a0c02040609050403020f1f020307090504091a10030308060907110d05070606090515010e 73
    0x44030795031440210100c40d16281042642c90720703001d08202d610800e000000052801101c80304002d6000c01c07001d000f08148210051405121960307203028148210035800701842c015003200c0c3d103e1400441603408017403540c0502c0704203080166001441c01e001c01920116040c58803500743c50060b200c3d054480c0c0320490803c0c110745c802e19030300141e03880341048803070030084545c3c5000600e0704120111803140c100c040300041c181401c221400c41c03003080011300c1e1041c0c2c2c0c1d0003040d03207500d030b00b9040000c54002d152820003030352041c2060400304061246901c0280280e209400b02e4a60020140c81725488a209070303004440d1790320084e41252040b4540d002558010002d02c2c007080080c0e07c0e100010115594902d040d9543ca8581e40420186601c400c030203a04280a440175401c00c03865590001c0c0204001042d06001c0c06d500782c041202c0601407507440c107194501c0030565200b203001e00c1005119400141c2c041e5100c81c10100d0000c1c000c40513208207070240207224022040300b00c20300e00544080c600500c0c02c40e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 890536375 1250 890535125 890535133
    0x5031b060d0f09241104030f0209070201061701020c1c05030a0504150905030c210a1d1f031802010c080313080c031b0105070c14030d0606171e06010c05 67
    0x2400542e04280714811215004071344000c1c03001102d0b181044401803589502c0014040000380b01240220b24102140d40d41121025025620b524003240940105d40c450f045222840590084a031010f401074079941d80954100c548000194840240b42c3c0007100640001c65402c000ac0b4001340f06681107182e01501030000d9501e040c0c01d802c080c004480450200707942c2a00045112603a03240f0074008a4082881d060745100c0c440c005901481c903510401a070307007050001c07074940780d02c2c00040030700c1c01c040c0030700c00500d80201c681311541c1d8134812842c1000c0e031900083c54154080b56141c540070700c9408054045e0b44540b07180c0099600e0160903480075004d0503003c006030f141c03000000d449500500840304070201030741d140c2d01c058042422030202c07562103041d280d04100802010030740c000d003403140040e00000f0055190141003c04c905510504109100150800402143e07940d0850440f6a0a450486039028942d6441041e00c2ca20909440700500d408281130104909611403821562000c2c0610181c0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 890537625 1250 890536375 890536391
    0xa0b180a020d08040e130b01060f110708060106140f09060304030203070c06020c0f061e0304020d12030204030c05030c0906010e010504170a051c0804080d0f02030a050105031b060d0f 80
    0x1c0703500001e100103d59142e000038044c400341c640d244002d50481060a00e0310102c245079910310b01d84080500132901040361a4ac0c032071295510600b103a1074040c0f4190155051aa180c0100c41d4a0304001d001d0b40c03002c588141c00d440c00003200d150485008403000b401242c01c1401c420300b0403102e9072003c0d001350114401440f131200400e02036005440241101d070010440b14600c0750a0000010210002c144118002d212100554207000d82d071544007800c80044940d03e503158400603046140708200a80144c04100d0b80d070300300c95090340c02401628007036000d201645640703104065952400403d01500110101c001c02d03040c0d40110034129140505040941c1040d81390541804941c28051360820300ba4080d00500c000c0c4107041c00000311021a8401c4941e900041020240104101400050842100003200482d4409681c815190030756081801c3d5620304040b031011000d40030a0046610a014502c5084414441880900426180900340501300100d480204006014001e48030b1205910ba402c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 890538875 1250 890537625 890537629
    0x190507020d0219030605061e0f12060414070b0c03180619090306050709060f0e0a03080325050a0f0c020a0806070807020106090605220f061401020f0a0b180a02 70
    0xe40c89000f4015400055203195040c0700095441c05840c0074000c2a81c0b0482c10b010030a150410042c0450540d00190900240030200300441c0304005440614019101444100300c0106944140303c0f03810012203400b1a120715440610b0f1159400c2d842d0741c0e500801540241c140a110601041c02c2c00500f10b40c24000c006400103280c00c152110b4a00180c0e081e402802004450711515401100f58981940043e00305040130701101001405032080c00980044e100c5d80b07030384405180003e158400d20071922410404082c4031444000d0a1801418007a50901483c00784a2429520840350303075515071840002400c0283d5944004039401d80e0880c2e54101e0116111401f042480d01400705661505078914200c0c0c1c00a0848041e50041c0d00101e061040810080d610420b10003402c201002117000c00c0342c0c289010303c00038a0703100002d00743e460804d400080e0100700d540c580c0c500c0c81c100b038003512580030101088584070001220b000f09200303038000c04141708040600e80741d100e00c441c0c24200c0d880c580041d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 890540125 1250 890538875 890538889
    0xa0c02010e0f0307051b030631030f111219200a02090112050a06020a27170c0928110d11090918150c0403060c05190507020d02 56
    0x3282e1442d40d400021443d0070094100159407448840c0801d11000e0b40d0400e002a88924021340541701c0c4003904d0f09100c810040350045200c0786140103950a00b90300403850060701401803610054046000203030a21440c050100d00c00d42d0110f00348900c6031404030248600c0340c03020381d480c2e0035004010081d51000e1003078a001002021040c0190003c00101003140f040100400d0705800100075011a2055035001603400940d07890626406500580c0765980c506044481c00c9160100d03050301d40d80388100c95865418015464142c07a4280d04100c008070220752042e50303134161b130200399401400030030020b2040f050000140030b0700e50a4849070700802104c40c0500c0283d560315261591840000115000c005100c1d20944000d01c0b1a44199803d00c85200005151141c00808201c05c0700b400f210130210b050001e100d4501c080640300707541c1415062100842006030000d001c2101d1a034540a0307040c200d81c0c012801d0304e4040101d071184000030f8100d081c00f1541078102e0f501c200e030003103c401040c80050365064 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 890541375 1250 890540125 890540143
    0x50711010501081e0a05150c090603040c0e0c07021f030e0d0206063f070f08010203090d0903050a1401020405090c31052101090f050c0f090a0c02010e 66
    0x41c000701403464100342d03c4d4801201040050391503910480344140010408164040000c0241a030341685a0750b6420080e003c5c420082e90982c4000c0001c104010865001c0c104002d0f20b00c02070840046c0e81e200d15150200344500c90021b9480700303000c0382c510307188010510503011b55881da1070302192401c0346a00d1a458000401c0c2c0d20f00c003507003241c8100101800c1440f401d58225801c0c0440c0d8801c104509081075503100d900421000c0f00d00561074808074108200048002490000c400064050f03541c8440c0b070003034001b903c81c46070170b001c2e011448130481d104142d000c05503030300600038003402013003a9200c200034200300710b99002c1550203000004460b80c1e64030b1035030700c14803c44400340e98680300c03025201d8400042194800c460703515200078001c2c2031022140c03a402d440c0c040d03443c0c62070381001d282412410b009a0041c4880d6600b0f0408007010885901b103222201c43c41001110303400d61007002004042012030009a4000e070003000043d404149030b40046180c3d6680b800001412581c100d1040d040a4000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 890542625 1250 890541375 890541389
    0xc06010e04110105030c0f0d0e07080d0909020f030622050c0304020909120a0507030504080105011706011410050307030b1002060106090b0711060f041211040b04150306050711010501 80
    0x590820041c842030318440420700c0c41c00d280151440c07800255144190240381e003450480d01000c1440c00000b289036126009d020380794402c550340c01d071792070036460340c0c8401c04640d00c400241c15240c00a541003240c000e85513555140725107281140d840c40144226403e041401501c1028069100c0280d00124130609000d2010811865540e203070900601ca03580d20007a0030f421070366001140c03807000d910105055513100582c921b0f041d95070f0070301380c01c080300c09016070b0700104441e510300780001a01054480621154120101c00d585c4260382e1003521075480703881c03680e843c0d4100e54428a42405184100b00450b840074003801c1c00130301c808103c0c0c0494450444404590056880f510041c070003503810400d00c800400100d0f00ca42e2800115664100a140c20f5210460240d1b0001c41c02001078280c035015070703000d0b02c0c90b0f5034000c1c03e142e094208011200c0a03902a01d009901d09910217050742080c2c0165030105d4904040050654516034441004210042185c0c00b00074900303030b01c01003c020070701803e4020104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 890543875 1250 890542625 890542649
    0x5040506011404140f0f0f09090109080d0b0315090a02011404150807110d0207030818130213060503041e02010909021204061a010207210f0b040506010b2a030c0601 72
    0x1c1005124903100003000846c881d400c075940400b20790707440071224802104103030740c10003680d15222a418050090ba03580140042808a084034103403c984c1d0100290b00c0c000c070129051401110382200a032607050300c442d440c070b4000e40c0341c08001d0350082034882040b07101030f030b615803419980b05e1004c5030070f04046860100281400d0240030980340e100b03441d4411184042d010f40455030540302c002c4d684d04001d100c000d000c60350102d03d452040550341589144480c003d4843d00c0c88050381c2c0034000003940400e4138801c2d0300103850300106440c0d03c40d0703003640d10540e800261540408401010114031991140049042049140303010805d01880d0025002c0340d900300240c80b015081031310b010320550b40c216074004041140c80181e04020b0784c0c0052040c04648260342d0f030300007843d404032800c205d810454030b01401043c12180380c1402c2040c802c034281e106038080c41c02d5070201d9881d00000001ca10400503480910704086501480900e06101034800440700401203d01e8440302c80c00180c1414004d034092a460f4070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 890545125 1250 890543875 890543909
    0x90509150a0b03090d0c0c05031207050106150c03051e0f07020901090c0c021311040f15020d140a12050a0c0f0206221a0405030409060501090302060405040506011404 73
    0x100003110300003801c0c408640b1400c0d4a031403049955100061110401040200e400c4042801442924407000e4540603055804c000c84c0c0340404072540d842003408983c50b41ca803210000d142c0c03140700d00f40240c0340c481d59a00c00000445403012100c41c2c001c1c4508003400b900700d08c40407241a00c0d540050883c142224440c41d03c50341076004001c55614168000004181000c40c031911196002d084420050780c102c81140040c60042c8070003004190350102400003500c00100811410100c000c3d4030111210410711580c1e0382090700080341c807a65910b1410000c10114500000300b00b0500000d03054140d03030b03407805070120710b40e940e204000da890035503521441035580d64400000e15407162b1403802d59000c50000b06910304001890041c1391311340364a10300010001405407030400100c1c010164030f81010940c084004d08003410030945036482b500c032b0460041e1415100042d1540201507000840390020030300c90a10349818140070240170020456410031441803101005000e018014001401000b00100c050710 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 890546375 1250 890545125 890545129
    0x82101061103040b03060402070804090504051b0f10050a0e0a12060c081e0703110711012703060209190603020901030606030203190e01020c030a020a0c270c09050915 73
    0x100840d600740c81160400c101c01e2000500403021284c1012040e54016500e2500e0300b0810000d01590f04804517050806090000b80407000825203031110320714550784078009480040003000700c41c50381d4040c1c1001071203581c3c42c0130728054405003405c074038981001c50903a58410001aa81a056040001ca802500d900704007404103d2096036404112810b0120316401c110f0700085100402c8030401d11850701080002e00034a20907003110501120464403686c851805182010301010910301940c0041c40c02c2000410280c240403040150881d840043c080017819900c450020750301201d54240c0103440b12850080f00745c5222520b100600b1a50390058489002c1c00006090780d075030b54080c004050040c401d02c008600d602000501d04c1c0d601240019440992105542c0079010348c125160a80c04082800e080d00c517004110b000c0c0d054030400385800181e8850805809103a85444019803041c004905c240d4040d4481d801040041c2850a101c0d0321290b842000800724101117030074051010b000e1807121028 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 890547625 1250 890546375 890546387
    0x9250c051006081b010c12110d09060e19030206043015020c120d02041a0a020604030c050a0f12020105060406050f041d0f030304120302030403090b0708210106 70
    0x41e14014092000902e8443c09a80d140203500044240c408142c0414559a0044580c40703401340d400344030300c500c03400c0c607010207044141668043d5440f801002e243e404054420360700b8400303440300385c4c46002c1140c2c1180107101082e66404a46104038060143c0400940c0e03841c40600000c02d80710301c080103544e0540d503c2030544000b211014108100000700d46000074800c50a0100750a00d8240040c0c4940310040013602c2c0c12804100355452440004062510070500e40040090364802080e8846c000c0004c810156584140410130005070003500c080703400288100354019100d03004070225410040c03640c075040118a9022011601a806010860708181d0207005060740451700301d80401000b460400401c0407103503e0301100344a25601c0b449146114500c13030f111a0701c00d00c3c2400302c4500380c1c0c0004245a595105441c203440000800d03c81141103442402140d00c80c1e81e01d503960241071845c00d00c8810081d04465400c03030b0103034000c3c44000d242c40301e90300000c954041d1200d80c4070a5035240107000b0303250f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 890548875 1250 890547625 890547643
    0xf1204122d1a0906070c03210c030e0703232a090115020709180c0305210301030f1e1a1519300b0619120209250c05 51
    0x42c0110b82004480036010840036800f450074202010442c46900c2e007140d89039010300c3c00d10304502180a14694000386944501a15180c50728100412600504019a07030403a52000420710445032000c10a84403001e6811402c081141e811280c0460305040c80d22100310a000c408290b82e03104950070704031880d0843c01d480c01002c0900e060380d242c08270514001e45407510380c0a00004280c45030240000c1c00c11b90050b0044454020044410f400e03140e242c01030f225100c601000482c920280c0d5691a0340798420101d0381266800041b10080042683e81c0d40403020080c1040c01301038020b84000e2000c95042800d44091394680e12890b403051604595100c142046000e00b2801450162103040f01d0382c11344007008040d03c06044c2140f26200403d80950403045c00e405d0850707003c00000310308908000d95080c54502a10003101c001c218100002985e158229042c402c6e80c400c82ea070360343e000c009414044803041e000080c4040c4a2031442c7c0402e4a40041a0341121820000b0483c81c2080c0034060b0900100d21 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 890550125 1250 890548875 890548913
    0x602070507180b120606090709080d021e0309012304030c091d06060a060e12030a0f0f1b02040b010e1207030b0a1401030212010e0d0f020f1204122d 65
    0x20a00c0c90141307580e943d032034005010360700a031013032408501804e0180e42268014403035003044401106080000030340b2107102e604e04411581c0f0500c2c002030080f902204ad1148004180e60b1120582c20f0004110b5003070400b000243c00541c070802020010074032410300a00900525031000c21020140300c40f107016207510091555a40d0020003e00040380c0e28a0045070071500302d454881224030203440054001d00f60034240791a0340c40009151000070360403100f91004050151100c0f8180d04403260141c0f041e02200c2c1e141d400c60701c61020500f005140c00e27070003e05004018506170007140f140401003100610b105030521501ea22010080003041043c5208a0740940e09140901ca110580d919484032081c1c1030200034451640c03200083c80100b8258001c04214614508440b0024051a0090300c1154420007180050064204d619025000014074a00140340542a5460140303060382450810245480484a103001c5c1c070329501c0214102c061144410304200358504040c130301031400003501220558030030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 890551375 1250 890550125 890550139
    0xf1401020f01091112030d020a030b030f1c0530150109051c03120501030c1d0f01090e070e0405030406031d0703110f0d12090603061206090602070507180b 68
    0x40300056004030302000684c03058449581d040c000e10a82800d600a41d00c00c585200c0c40440c0307421000e9450340200341109001e07030a44d0700f10407213019015100c50030300038010b1070381c0319100762400128421402840c0110107203080d0701145080035813010006846900c4506c142c0b401c041400413039128211052000c12003401c1200c216413030180818803070212040d881c40c0c50018101008185805420350f0030950110714410030841da100d1030000340e0020140181c0d000010b85081c101c481030840b820107402862002d0822041e6840c0458a80290000150710385040c019510001008007a2100c258010ae01c1403000c1d50316141003000041c111090003c941040d00d034400c032550216480030031140141c0350010001488102108086a600407036042d0164000480c01e50110a1066610380c040c00d0590a03991070764007a40c0c98000b20162031050050114010326240f035000010712950094000c50310036030340503040019540b01c040c18090a50f0061422100c40304005030305600368419104050b100701c40355 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 890552625 1250 890551375 890551391
    0x90606090e042d0b06010e01020c10050412150b03160e040305040b0c010f0e0714060c0109060c050307090914060f0d080a0e09101a0f040f1401020f01 66
    0x422248440c4111410200d0240c041018400f011408034102006040100c0389400480720424140c019008241c1c0c0a00e072010200c0d190398400c60358543c4044059000f00040300c448030400c040d80c400200d1107020300c80c00b000001454000c03d10100845c0c2e006219001c00c0c1200b071142c0074291060b415400e40f0075085801900f0380c1150709469102070b60032825000082e51f44a103020f40e43d42c4215080250003080c04541ea040c8544150000d83c1da0040c000b0080c40100240c00e078443e03603001e96008000152403690b1185515042c020054020f41030030030000318080301a510388404840d503191107400000e02c00070030440c080c0c0d003080d0303074400a0020300340400c00030318404010150800701520052141012400001c000d0760350007020000140c014803082c3d5030714a410806045520000f5000d4041c01355140081e030301007a16044a0100ca00035002c4200e403884c945000403c0c0e9018900d840445007083c003010910801400000c0c0181c40071210244044200303c00292a01c8030844404000340c0c104046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 890553875 1250 890552625 890552627
    0x60d02130c0e0d210c051e15010b0f070f0602210c072d0209010e07090b0c06010302040905160f091d07180b06030c0d0605180402010c0303090803090d0801090606 71
    0x1082c8014a480c00c0d00d120100340310f00803075070706120744400746c01889440901d210f03800481072951460560042200c4215291f909003c00c5042e0900c56111400c0050081400015601c0c0061803006c0c0704070ba0000920140c0e0750341c24120b8000001d4004240c9a1000440c1c40750242c50000381c010000c082c055092110590307481e1825071180246940c00c0440c0344a8100509a082403041015801400c8016540c0c40356480ca1185100b00c44200010303072070003400240700040c0e1003101d400d440c01c0b0001c0d0800b0317800c540038071000d03020300c0d0421a05c52042c507807050018041d28605001505a008200780f1031450320f03000c64250342c001a1040d400058904c050b900341c0d90700180600c110b45c0c100810140c0c00440325800700062050694603070304440000200f00c00855114020101c12880b4082000042e031601300303020465404141580c10b100380e000218000d0740c003955030810307114800d180104040c881991035042d10340090300c2c006000d44c000c120001230940c00c540d0540c00340070100c408200304d40c41e20750 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 890555125 1250 890553875 890553893
    0x1050603060705280c150b0301050c070825021809060c180f060d06080f10140714160f1203050c0406031d0106081501120317060d02130c0e0d 62
    0x180c0c03010020548030400c400a405048a24650354100d070340040d0201b145038806010742420b4000358403951906000450004440066500240d042418542000c1005203085498010000351840008900a0340401661000d50044450000811120312403c00741d02e62813528502400c1c0c0e0480381c0050044030b041c50110040121014412100c08008590086c0402d04500c59409001003090030004042210b03500042d4041d849040041200c0703e40400c02c084c407040760303210052641110024408a28114810803441c220070761042c482c06c0c82c1140078094010b40c0310050341c044422a443c0340000d01803004000c4541300701501400d052240d80b8000c1d803600103e00c42c500904003032541d40c400c030b044202e034010f001161240c00c160003041000c3e00c80603c80e5a032480c4031910ba2080c1160400414461600d411200200e903040d100c0481101c0c041e1091588804000c10094120045c2044540541d079088440707069034003080300001c0e40d03031420071009165031040c00019001e168000b880d100041c070308107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 890556375 1250 890555125 890555167
    0x61308090405060409020406170c0301050907060f0905030a0b011d070504090c05040504050c03160e1e1c0b0a1811061b03070b010608011415030613060801050603060705 74
    0xc50000d55552001e00060042c100e1a05c041d4116140090124108960308807060212003180e00301c965100c80c0004142c283e55085500c008603403c5030000700502e9016005142507901d240c01c000400310b8441004c2880d16a12a000b0b80e031120444004104804009a0b14a1a009042a4031900340303405c0001400c17520941c031500038510ba58080b804203162281c0152409018024014042401d111034244100d40040c0c4100300c0c0905c008903040c115038059141c80c580c1510241600081d0311216090b0024441140c003455006807001c44181c0c00f81d40900d9901000a106090070300309030030701e60300c0d00e42140c00130b000710480c1007008804580070406000304100782800454080d80d0711200c5120b28070354890004880c100354407000c00c1100401c042254014107861040d50b0701c201a0b1b0742c81d62811440e0004003200d5400002040d980a40303420000700950740a4409001010030803403414905c000c0310540d038403d801c03d03503641c0207000c0249000e0051a800c1801c0b45002410800805120007100b8151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 890557625 1250 890556375 890556379
    0x40e09011415010c260412060c080915131202060a0c0507030813080702030706020a060f090f03030504060b1203041d011a07020a050402121b0f07030806030703022106130809 76
    0x1049241c05d07800889039000850900f0382c03500d038856558000500c079601c00341e44101c805078248081000114811052503120f205094018600c3c883c80800742c0094220180001c1c90341114100060302040118400e491000c1d950381c000c02492074a964000b00f00c500741041c1c0c00401c9020068034021952107124150001c1104010b900d5880d808d1620140b14419500005c0d00760140c008001811500464060342040c0500000e0040da00e000800c00100c50922600074404600c604c00d04010134441c0d4440b42d072042c401c0d0342c00a07100300c0c071714000f0f100381c1c0004601e03080301d0b40005814420819284094071040d40d00186400855050402c51241c0e83d42c00f02d000300704580082210001d658407040040010722016204565651400c444156503032000c403010140e440001c003409101c101c41804403250076201d208594244281070f9000c80e42c401028082030303810700c04c81a002c000350303035044c0154407131030140c0411f10108806180c00b80d041c28001025807454122803e00f16010800040803241c0316901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 890558875 1250 890557625 890557643
    0x301200906041505040303030f0c09060e0a0e1005031203092e06031406090c03060c130b0f040e07020f0d030e1504060b24120c040e09011415010c 64
    0x81035010990a001e036501c80c0c0c40211941c031035090010381000040041d00c0c041d9501740054003d080ea034000b920109940000042ca40c220700f046042d2050031040210480202040d184583d1200b00703102e0064143e40c642c18420444030208a640340800c940b04211500c44030f5a4110318066818541769000c4114940c0c04810940c1d9201021b1a8034603058140d01c1c141008001050b02c90902d20301881504000c10440d21030040840d5180c0c200280b1201c0d4004003c0007403001d80e03075109003c091500501928020740510100115418180402504901e01c4146070203469a01c0d00702c09101d01c05010386070100f9508807054052010201080c400071151107820086125450504000d00d4451495a0f445050b075030a01404100550303900000390841003121078103202c0c18070340090300c06448112800c002a0350100141407984424600c0540c0c01941c40403210705103959644400440401290b0300100f0340d5440845036855003210b04080d410405010722440b03841c4a58001902e0075050f60809480001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 890560125 1250 890558875 890558887
    0x50a030f05100e01051005031c051b102c060720100e010b010e0d020d020102031216090e01050d060515040e0102031611060a0b04230403020c030120 65
    0x3070400c1081000a4600b00812000c00300c440d85600801080d140403203000c9440d40c00041c64900000c84490400c0752600701500102020710548a562025000100d070b828500c5030703403651410a1148030300411003400040350b40380b1404060f600080c01180c211624840307410307503c209003500041141d84192941003503d82d1500010000ca6942080605850b40d03100710b56441700b030240035421954508400400034406455030302d00645e182d0b552000065003048002c1700c110050700c0e0a46410041c0c500600690f45002d20018040750206022900401210f80d41174203141f941e503000c0d41002c002c15560400180325410b00d40000c40317501c001480504015191b00101d041032865102c0810b200390010020441c03412161f907194041d400071105c0203820280704069161003405207625024200b80617018010035910b0007513070300081c103024821580041c1c0d98543d8401c890500201d00054480340301c0b002d0b50900d080e00d0001e207001e0a4121250013a41003140b25aa40e91200741914085000061040d0f1a40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 890561375 1250 890560125 890560133
    0x30406090f0b04080901030e1c0516120c0b010605041a070c05030601080f07050f1f0216140f010c0528050703061e09080403082110080115050a030f 65
    0x704210000d4050070300c0c20184020004c080e0003c09a244082e01d061000420519440391580c158039800c4030040b10314072004081c4c07031284005140c683c4028601c06c41c2500b6689800012450604818011440403030445040c0b1290001483c01012940345c890310b03040c14107003002114241c10805100c85500491140c0400c4001c03800302011305000380c11160b040d80c3d5850300564540701e90300c01001c00d0050040110b228184403002e40c4290b480a89a5611320980713407031628038500612403020450080c00d08110b00e000018070460001c25880644048143c0c0203c00c024503480e2070401d85051100c0752000000107440851085040d4520440542c44481301d41c118a0b845d07040044000c2c001d0086000110070041d0681c4682070a841009503140c640c80034404c202c04403600c0345006003140405003c10030014010780300804c3c269250b11320890903c2165110b100c124041a00c2070181021145418420310000740326030f00500311504e010019403444c0c031001c21044000f9001c00b030440c031082900c07030080c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 890562625 1250 890561375 890561393
    0x3060b030c0907052706070210050412080a08010834080f010507020f0a080409050c1b011b170105130e061f0e07020d080411060a1809020a020303040609 67
    0x3002010b8034035030790b03071600140c010229030048618170300d8034070000780182080040f8041c0d00680032019004518080700c2c0d0b02003052020502c0541400c00c0340070040070038003e514441c500030301c5105592058556000c031201808800051b0007280e00b641c07200780c4a040f4403a104e13021900c81950001440c4004507489044416407031540c03c071110034896881c1074070035410b056008501ca560564292100302c0002068039495141d003075409019040188802e000f0180541d100580100e0f0725900f0918201c10300046d1040307d58011445c81c0c04c4e03591108210b2441034841203e0500070124038000c0501e40c020841382000e51811702915002d40c01504500266044640c002e0100c40c252a0445009262480c104034945661038030004d140f0702c103004001282c0c1c00500703600d4011100c5802500941c2240307541203d04d240c0082090396083c0c2c450040031100e882c1e00c0d0003020b0270419035641d044001e0504d1420240428a603102c00003080c03040041d11800c90780401901d8009034084070100c2d13003400904241402d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 890563875 1250 890562625 890562643
    0x19140f3d0c031104180c0203031311180412030c0306050a06030209031204030503070501140f04140a23060606131221080f0f0907060f091706010f080f0703060b03 71
    0x20f000005000b250044103007020b8414454080d00c14481741c0389502c41280c9900064070000480040121002e002440404e1080005d80020b441c9901900300c4901800400c503080c3c5003555450095010f00010b5503060240c14044c2c0d00340c1c101400a5442c25011070324030f0a15214410425502090320842d56805028214030035520209058641c0d4036800c082d91030b40c2c41007204890703035840e0000c01641d4000d5044001d01c104900a1180070503a103548a06d2040c1104c0e405003042c500680040320001002e140101129038500f803040700c8900841070341e240c9044070103416207105280c00e2001c0c92072400b0300e41e4610165406040540300101c9185003452203911102042801c2808404c42003c0480d813000c1401c1c0304005405030240301e03403a11141d40901250540c0c2e104085e800846080c403485000e114003046101c0d40e450b004100c50759079020840600e0b901110340b50141c100320010044603101c100002c1c042d244140c050b264a001c0d4400069642445100080589403110700303c6100d40d0f002d0040701c403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 890565125 1250 890563875 890563901
    0xf16090b0c011107060b1903022b02040e0f01060807230d0c140114031005061b0105090a110a061205180307121b02010219140f3d0c03 59
    0xc1c41390154034001c0060011500c40f82c1c010800601c090a650940c80540c004070303500940140b100a00203194403004406281c40039055408590b000c00050320741c0d1045003030142c0248003407d000301902c01c0302803e554071544040700304e6000034424042c1410031040741c1c103070a50126607840400a1240403e203104501200030300a04001c0000081e40812641040800c3d4000da80720071420120315a600c4030b5000968550032011070380d03001441242400c1c402020741e90141c1e541d1400c0000c0c0f0000c8242522002c50315440540c000511b00d50821034100304001d002d010445603440b1184c00c040340104104002080740c00e6a03512080480e40601d007046000209054103000d4036500c180509112505400c111034000006018500700f214907089000c174001525070584c0603003010090703003c4100080522540986203000c0154552414881c204900003070107a11001030070004a0a45040100101c00190f4040300642000410180d0030075902c4002210714404000034903041c400000c41c004c1c2041d003003401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 890566375 1250 890565125 890565127
    0xb1903050105070306170a0308060102120c010e011a0625020d0602090f100c08301504020909010b0c070b04170106080708150a020f0409050f16090b0c0111 68
    0x40280031040d0002881407441c1e4a01380011039440850603156003264281603c6074001620b1240001d01c03032113459401c044144101c0305e080801d40301091043c0c0c005503e0708007981d0354110004d042d0000b80a66414003003031614109842d00c41101040c014400c003580e50412211030345000740240d05400d0500002c903006070001c80b01c148207250100c000d6200d4040303240f044035141c0070308403945006125064100c03c203644044024015903103c09168100900341c3d260049070444039030030081c00268490501304501c40c41d030705900f4001101c3c0c0004d824105882d008900402108909440e101983d6045034620900c490781c400b01003818074204191500141d100d503200140004c1d00402014030000441d9009008006036903a41080c3c55407821710388101385282e0044000b13110800303021454a54400308011001d843c000c40400303801c10582c05078019401c01513545051002e440c3c42510420750007107101c0030810005803042000f91021a0301c0c40303040c451245c00a40c0c104c11000079007103940041c060031101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 890567625 1250 890566375 890566379
    0x9040303090f061a0d03120b2412070903020a17010209040c030b0a0603050421051909260a080a111b030105160522180603020f150d0b19 60
    0x80800361060b610070b0600010b124080c0d42c240d240003202580225496103500207c20b26502c22080a00700c240380e100d90240e1040960860700e4034140003a9494000c0c100741950b00c5150590142c030070380c4c01070240c004014040c8010310040c2c031403000340c9050780e4510402c00c1c0c81a04440202d0701a01c16101919080303401e103507c208443d50103800c64401c0c240c040325416500c0352140e404404951040b1000b80c4207070742241c0419001082c00003044c000e92150710b03207035140240901d0700069460707140e910500042c09210040220121440e003982c260032a444250706841408600c05076601d100400152070503c0000d00000c0b001c0c014811403140805d04420703901918040100041c200e0703060380d81140a5401e20300010b10340c4501fa000883c040c035441d01d03524100f0a0201d070700c110b0590759110b18041d0314081100812a40a01c80d19111548404d03000032a0050461040c0010180120352450007621400031a541c020940e07820388001c424a918001b501003902d00019620308030b0855000304000c001c05c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 890568875 1250 890567625 890567633
    0x60714061603090b0f060609060a0e0901060504062304151116060207031115040e0610030c09030b060418050f0f06060a0603020a12060b0d15120209040303090f 70
    0x3890310940125620551070003001409405032103800000406518000e03000400e0200d1142e4030580011000c3c10a0741015010400724001c0e600c24610302d004a00c016444400700e260010303015000d800545095410300e45044005003054403036241c203c03030b01c070100c800841d001290542030b18002c0c095492038500030004807170702070100c0c003c01c2e42c2c10f00340c0d00400d40c00100810490340010216811b540c01480c189141d921451005451064a640e00c040489500310245d040c1501034070260100045958082c1401c904004c0300441120b010800d250400c03a00e529441c6d0080008001c0304e4128420341c40594400300000c00902c5c00b0b0004100d00452614494140800054040f09101200e812518800383c040c0082c0ea030703074404861031903102035107050620940d0b1103030700508017a078410304080c0d00c0c0220062201003070380c00c1900189940300340802c1003030b0300c0c461a01900310341c0ca240802c0700c0421418402c181106007803100c00a800b51300d40380046003c00d40f00350b00c032a80860b00541074000440d11858 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 890570125 1250 890568875 890568883
    0x2d0e0619180506040608090118061a033f0309030301031b0f050616020a03141015050d0213090305070b0606030f0406051e040b010602070605070f11060714 68
    0x501000511210000300011007400c0c1107015100c0080140342024a030460803956032500814900140d500c4504112410300c0380e41c0030100e0284600800701e0240c0c82c958003a5038a00d01c000d07460f846680301040c940808110240055000c81d590320614081040304822009500480c00030f0946641d000410012a000d010000e107069030300c200340d4100c8010fa449200950510213000303a0842c0d000c1d0304410052441e1542c000c210042a0520003811441590000307100110660b100b07540100410343d500c0c0b40e2070300c2030059010017440c1100400c000090302007c0f10043e013080c090b060054605032140300555603440c15401d030118240074140550580d80c94003c00720b401c024030454000c030515000c2a40382c075282d030a691058441e0014071520350b686132a50005024003030102c541c0344030700300c2d02100310750000d84c0243d1146014601840d07441d45001e60003440c0500c15400b090400c00107011200c00141c401c11081ca07000e03080b1241c201001c03c180c0010381e0b40c1c4a05040100703040300c80800300c103810070040b07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 890571375 1250 890570125 890570167
    0x19080915030903090f0d1a18250b040e06060304060924150f03020607030c0b07110c0105030106440915010302030616030f0e010b0306010e060a03080708070b130605072d0e06 76
    0x49e14900286030340d100f1a00e00d6004074007a04000c0c00d403c000041e1075082c203801556106000706000318914000e0b4071401180700f5001602c52100e2030131400261901018000c51181d000062060303101c05d807505182d0180b685081c00b00070b1203400000390401c141449610b100c001c180e00b091400c42242001c40d8080d104d804081187d01d440e002c0d40c100e2403031540c0100d0589040740e900d9100d114800c403a4a18007510444034400004010500c4001c9001e00c403e15001c1e14020070b102400c1c10802d0074001c0c0c5031450306c02d468461b00c5c1484a168010320050301c021440e550040d80c003071103460003404c0f0740d44150040c000c0c21250030a03841c540000e46070909415003080740c100c0410382c10340300c1503601c1d404035101e00300701101d0040d0800e00a11007000094144001046428054107609041030b80c4c2d540d801750039a805442d400481c2c0101c541c0d40041c407005129064005e81603040410165044110858603110a12034402d0086200e4295210f4140503010244404a004041554903072a0302a00b594401c0d101e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 890572625 1250 890571375 890571433
    0x3030706060f1802040f21050318130612030f050409140604050f060303040b070c030f030320030103050604020f03012307090819080915030903090f0d1a18 68
    0x44540c5183c0030400c3c42250251039004485550840c01c00501140544400c072011101050303d5440ca130201d4400c3c40540002d41101d16040461600f0104001c0c0d000b90300d403040351490780380c96020401c806019502c80582585820002d0b045441d0b1602030b195401141d2041c0031003410085d90b8008a0342c1c0240c8580f080310100c804000640398410300c1c010311101240d40540681c000c000500041c5011009807101d18441d0f1041c0c6620354590741da011481c600b41604601081e1641c0c20140101e14151201840f039508401c1a41550f00d503444032a5105000780c4003a0159032025046c01070f5407820741080083c100b0b014804420700d01c162205a01c0050700b2a092000100c598034045101c032400704004c031000e8020f0400326071081094842c800168070840940b0751102c00d0101d2503420040e0300001d54400c101403030195843d004400c0a00ca44983d441d0501886080646201c07000903001034840a10b0309410620b05074145d481d00c070034540202080d40f00350100d100390300341241005d4000c0c40041c820740744 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 890573875 1250 890572625 890572649
    0xf1b0a0605040b19170411360c1e0301060e0904030f030f0b09090d030b0a140909031204030203091309080d0504030e032b0c05030301090e03280f091202090603030706060f 75
    0x6502e090282c8c40e40005503c440324441c00c40d52100f0302c0d04140c60f15008445407459038a0204403100d028410440c80c0481d8507444070110040045542000f981a20000180da0007019850103590007001341d03180081c2c40080c107a03264641d2204986940c4881083c540c0a00415220700b820f000055407503d440a00c400000d040c0600380c50542000c2107210100c540c0d94045c0c1404c0c1c800c650030412882001080ca03092440240080d074001c2c04502001c42c000c90194024550701d8040307000b4004418050544a5506070800c903050700010045021140d24900301c440014498607503103812aa082800f001481c0d00d84182c3c820030004003100028003044440741d0710745006151280009a0340e00b500480d0180a44e0014801000303082d0b0140c20034500d0080a00940349000b600718881041100d404420042d8031061541d007511444d00110403040080d02c508142070300b5480d14040c1c1a05a40c0f1240090149008002081013500c040003503400290b0f101c2c10602c40281c8900005860344498807610021f580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 890575125 1250 890573875 890573899
    0x180609110306150a02070501050d0b0405010b12070806060315010210060b09040e01090b06120120040905060409080409090204061205060f010905060a0303030902030f1b0a0605040b19170411 83
    0x4403035404c48000034481d4001d800c03c0761600005499640080c200d001c0c003039440f8400c030126565244600d40c041c03c0b101801c81e4071549030192020507100c00601500500040e0020710807140c0c3c03104d0030359501207180714031400041c4485004070704104c0101c010844003800c0a002240c42c090f030b40081c100200081e102000311014030720f0114207079281810050f14a18184c0d001c1170041c100701640001c101d0a0a0010402c00c1e90200c04c42140c1c2c0fa500c0d500300d881c1001140c140200403060144139000308003102c1c00c2c0012880794440d001c4074030844c414100c01c155120300c610215200c036003021008204000f0074001c400c006060050b1101d40448488400321540800070030440d0f554840e0900070100500310015443c15a070303050b002040e4280302640c1c58498500c98415451041100755000009075003c1803103d0b014200b440400b01d0107400020610200748414845140140c0075603182000340302d4045521901a08259800b001144604c0045031000007000107000f18000c80c0100500c0c241c4100040d14 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 890576375 1250 890575125 890575159
    0x10602011e05160302300a0e011b03050a1e060609080d080c0f0d0f0603110a0b03150d020d060c0206070305040519150c020604020a0b0403050601180609110306 70
    0x5204650700010704405045803c14913100364050300441c150b04409000b440751075020201090020009900d414420804003c50f4100b940a00c0c0c00d4154075000074041c090203100c0601c10350310341d8501c420406907100d001941d4103031302d60072041c294081100d502003c3d80f2820010005401d0501071407000c41d00703211000500d03a5001981c125085960b588061468664082c4903190340e019103902c41c0844402d001051480049105000d1001145600010000c2c5545040003610320f4000340707544100502d410801100d90700d08200c0303034404000903049080075005800280070000303d00b0701a400c051484840001c02007103501c0740100c8031040c0c0031660b00e5900c098046080e1042102c004029030045e01c02102c0030307020340042400d09841100312442c0c4451040b00d0070210740d60442881d005038031210a1006504058002c200a4031950f80c0032450141562201940c0e9181071064100d005e802400c00b40140302c0035030160000e07208031401400500000505143c01e6003003596600d00c03c4141200030b034402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 890577625 1250 890576375 890576381
    0x6010b04120507030222050f07170a090c12060501080a080712170a090201030b0603090604030804050a0206040e091605240d0615020607090f141206010602011e 70
    0x210101024540340c2810001c0e84484807846039012211480ba0b11400b0005944400741c0380b11283e003120249220307441c42c1000c24195000031f0110005608040c0500c01d134a60300c400d0b80120440110200075007519210000c000928001c0c2e0b001d41381da1071528000ca503000c290650140d0240c0180703c04c1c0020390701c580f034094980c010a2002008075a04105420005e40318102500b1403400600709045000071207001c0802d100f10840d01c819040c2e60303507883d402c02c66070180300e04510460281c0d0b002d8110310300608156a1070038040d00160900801100082c1000b50800c40b1005550f40070305803584940d940e80c0440c00c20350090320084c506018241c03070b1500492519021108840c030052001c001c0070000000104100a010358000c0c00075802c0145480b0304546001d68001452019400803110f1001a4001d013000405000c810801610010801c4800c00c1d11410302c007620591080c00407001c00c0c800c002000f154021009001e94001d001c0005038040c1c0660203074842c9a00d050118011450b012802021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 890578875 1250 890577625 890577629
    0x703170106031401091d0a110117010506041a0c16050a0b030601020a030e2103030a18080f0a030b031501180213090f0e0f010917030103080a0809070f03081306020601 73
    0x88604a100100080100c0e42c00242090442c4001e6810008040850604180401d44152232102c0031016100796075900c01d070b190803001c1c04440c95060a506003400555244500d110301e44100502c80c1003004107070300204c22107194280c04812210040d8008441742038500c0e03a8402d031403045100410005125a44000302c03882080164068801e862103950107a40b004840d410280d08072345030616007608102c04440c0d02c07504641250007035484e850000c0c00d030f1051f5a0100c6c0060703030032144101003070009115041030300d0240107412903064a680701c04108800402003100003d03454131404402c500805802e0184c00e060390f942045c041036410001001c81d0503441111050f001650b004401044540502e51100c00903604004010403d405004403140c07401c0f807011007859203070f5915420b11003080070817071b24443d507400d0701740c075103400c0d9850342e00d4495560143c82c103030005120360200000c0c400035007030000074054034101681c05401a00ca00b004032068111443c0040d5200701000c001c56014000119581 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 890580125 1250 890578875 890578901
    0xc1806100507030c03270e04061a01050a051e0f07030225030b100911030f060d0804090c090806010807030515150d06060f06113c12070317010603 64
    0x1081d001c0c6640c01c94045107005407410001c1006c4140018103a40480700c80018410340a95103058101424203108507445c1d0307800306491024141d95201c069030841d09455000e121810191f4031688001034804030204440350005060600181100102c4000000380c100e16003e90f0844104032101c620303d0030450310000020800d5a800003080001aa00b4400242d11021041e00c1c181515554008070003503c1008400745480b560100800102d40c145411041d44280d003282c0c424581c0c4100d465407203076445079005808403e80c840181c02c41103405584014000c2c5005001c070382e070b0343d03079542034840e1107020500003200d460207400c0300b480c3d410001d0b02840d03005140300880740f0a02102c1c5020080030900c04401290a81d4850b4400601d000c4071b00043c0009080540341c446000241400039030600a0030004102c5003220b02020000b002c1c40b0044080701c029900500310110b10301980c4042c5014030075251001134104c005805002c00d640400361024201a610113614680d0b220402034065901c80c2c10380301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 890581375 1250 890580125 890580137
    0x402211024030b060d080906162006030408160c090e1e15090f15041103010507020c0105090102100920030304080d20060403080405100b010e10020c180610050703 71
    0x409500d017101031050b8091082041c10302c1d1411280218040e80c20400c40c075004140d15542d00e6090148000da8203d00704400f05001c5256410200029a1070001900140c640400400c0d070742019a460000c2c500c48503000700c00781003c2559444407102a080d4407040454500442c0306c6840d201140240c0d0444143c2c0203000341c0444e40e403541034081882d1004081e21814402c4801036440c25074140512504c00c1d0140358400072524250407c4200d01e240b1840f0300340030760b25020400c100306a0105209458000034a0110f0741e4501050040349445011002c0d010443e02c0c01c030040040011340d1700b42c89a8102100f0600f0385a811000416842c0e020b18842c0da04940c00c482c202e0102c9620a21030f102c00040f80b66010000d0700c5c181c4480601c4c0030700484017100800d01410034441032140400c5080410080400184001076007840001c0a4003c4000840d014000c0141c01510340da00912484000c01c402070181d00300080c01541005c114042600c141340113030402e11720828844d03c00e80843d0a1b594143e1691 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 890582625 1250 890581375 890581381
    0xa060e1614060a170a02071709131a040630030203040603230115030b04020a1b06230a0c030c0504140301061502010c021c02060402211024030b 63
    0xc01065400850f81070200148002240e400341e841e0b91545008175101040181c6440d02850319064107202c0100801e1214018040c0342e007a9590303030b1800405402c458402107010a000004140160144000141d100341001c40118400104000c0e102ca81e00c1c0f542d09960040e1000907044254600545000d030060b0030030081400014000d400040c6080d00600c9142604000d640111340c00d01000c1e00004540003070026195880c0360f240c041d12010740411203045203060722900c03016140c86200c0e0104004000d1121403102440004d0348110304940c141644400703034594160742d40c1d00111040b100d80c8a02031504449840842c40786c0302e1000a6005515032034507080c01d110072500c40c22040306c100c035495921040081013090030310684210850b01c40d000404c10720300141d406810312604105851251505401c3e044803558000f80c2c554010360140e0b61521003038400150604008100706501e0485c4c421020031840384009688100e040080712248060640409540102d800d8024400588043d07565804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 890583875 1250 890582625 890582629
    0x105010e0708071404050a0b0304030e04140105010c030e10030509060a09050718200d1a0a15110f0606090703050601020d1107051504091121040c03050a060e1614 71
    0x84e088141c800303154490038541c0c2c0704c0005a4034a1a504498020080407052004054200510b8031010000315414441d02c1c031480c000416070b1405100e01c50403c00c1d00c1d0583c40034503000d1312442c0d00c0c0500142504110384030700303080a4040d001c00e940d00229440750400148600205114030700c0c002e0f0340700026010712403030020040311250100924840307960783d611a00c10010660300d4038600c84010700f601c841c0c5030000f41e0546421240ca040d0101c10142400814409540d100d00400e025075040c2c001d0b14040e0f62003100d00710fa500400010724111b40c032400030326044072400001d80c60721881d41101c0d0300c480d81d40d42c210110180c1d03000791ba1290142c4e10420b200c1510502070105030340d41940500407682c501c7d50701c000041c0d4410850301c032003041400c002414080d6001c1c2e80a001d11001c80c00380356500e03210b03c0e560038003082034902001903c1d544500c00800e08014007440e03e60700440e0084100c41d900780060a00c00c006260b040480c420381d02c0380e010031090381c01440840d80704446002255000105140003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 890585125 1250 890583875 890583887
    0x3161403010e150d0302070f09022503180f03111008040b0c1908090f0a12141e1b07121502220305011401050a090f0b040513050105010e070807 63
    0x2020960702d003d41c2c080c8200d40c0c2c468484000460b4082d6000f0f003403492828550000f14503158004603085801000384506400d0340600403c0300d500039000050117001c081c1001c0380d46070159810425152007a260025032482d5580c061000e41e0302500024101240c200100b0000032440d082e1100851100c0b00020301061500440640c4a042006203038070b400508105040c0301d1100b00080d9001c10076130020b0104000342000814903000c1c00c800100480c990b9030711a03030016080c1943c1d42d41005402c2c4140805050110252501c140d0102000404076130460b05140142d00918802410941c5840c505003000400081990881d07181c0e10803858108116160006041c9070701011245041c0c080001c583c24400d41ca255130300440000c032040348901d0561034001c0c00e40c4c4240414010203140c1e1001801155601020101118010000040d01d80d014040c103902030514155419401860401001407800013000d951035400e1084000700480d80e21a18541103001c1c09880c9080050700010004881c0c3e400381c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 890586375 1250 890585125 890585131
    0x40b030906070c0f1218081509010e0601051e09010b03061c03050405040f0b031b0112151205010b1504080f0703080703050306033405040c0e15071703161403010e 71
    0x101e000341400312848446e90741c9900a5000d8416079001c1c800040441010b40580358203e45610024048071400300c0c200d999804042c003403070b44102d018a801644d560302d4840da003030780890040c24003403540d81c1d1800c00d2280c90f0400c407020340c01140f82031162210300104101c1220400d03410f49889051a0811003440024038100048080582e6180c0103031b40035550800c085121180e442c1d449650300d44005000502c0d101c00d00c05000744881c00e0008050302040c03103801040a8030144800d500e541e10403810f05038050942c42a00c4c9420001202c004450003406000910680c0e2445003210034806c3c15840c02030742c1d810300c0d2102900c0c140342406031030300280c07142e402190000c030014226507514004210a41c0c0c40c01c03485120700130035950041a4004044019500e01c000c18003154200040100380c00064149164040414410011181c40c8017180e0491420f417a8040d40016807a42c07200900b20b000c81d07060313200355400d0192100a045040708541704441d0a100308001500941c2140d02e81003948052107805 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 890587625 1250 890586375 890586377
    0x16020f2805060907050f0d032a061d0118050703171912050601080405060417190e03010e011811031509160e070507170c03040b030906070c0f12 63
    0x140d11030010a90070003115002d800e07540c1c040e081c3d1514080401840004010225005000c0b124a10002c00d810002c005486042440a03200e00c0813101b004030329092007110014800381c5442805190750307240c020b4440c01301985400810154001d03600b208060101e0460041c00c6901500e0184001012a882c4504520a0304006401d0904884081a000e028084100300182c0340280c1d01c00b001405004040d0001e0003824000c1c00d81c01c1503158143c44003002000078003211107411482e150301f03042904030f561841003103c54a400c101401c50041c410351503280f007648698200008480c1440061041c0155962128114080e64103159901140300071034490744d55041c0510b5442a07004a944200d261042e15490007400d169850606840c120a0381c0d60003608481d161001040301c416004001c4561858219661a065425541d64050a84100c01175030520307000c042000241d18541402075030040ea15a004e5410780e40c3da4800c1220300100310100a0094070118542002180745409413104002c0c807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 890588875 1250 890587625 890587693
    0xb101e0b09193803070806010903061b080f010b07170702040507120e0d022d0d080106120504030e0103020702040906060f29041401020f1516020f 64
    0x2d515020300810402da4003501007807002ca2154429000c8020040c82d8030040c4041540d802d140d01034031416207010003005e004c1407100c0356000c41c80c06e0380624004801154400e800740007260f804900030380d8124803004800003080804001c00d40c0c100e18002100c0c10703544008000c50800c030540e1941d18a01c0591039000440302d00411424015032220301503503118200c1502d4000c4a81c2400480100b2225065020100c0350002d50010180036800700d030720700c010301b1249030b074a08071425040c0e581d064041543c02004541f04054500712183c2d04a500d840c1240c666440d07540b642e09460b103035581918011500203002440c81c40d2800903540c060b5000c1d01505002420019040c0d07501d42d282c40c01c8903140c1c1c004964080e402030307042180c00321040d601001021002e180100b80c41900d500b44a1074040da01500d0170002c100002991070341d1081181d81e00488280b400c4590000d206072940861070020746030b203811a29034141010290380002102d84102c1e031948000c00c54594904400024903240d201c0c10154066 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 890590125 1250 890588875 890588899
    0x8160c0c09020d061829040209040504060b010906080c0405010f1b06090b07020c0906040b0409050303151905030303190b10180e0105030d0c17070b101e0b09 69
    0x140601c040c160400e4454000907646040502140d0341200600385011030740d08144034012080750310702200801c01c421100c01403246c400070380010064001d04480b550130501e0a0308003c18014103421032120021f00780c032448215512480100c4003107000b00c0384540c600f08104001c2200c1c1d4400c00c940d580a400d41d140c074205170709940302c0300385106031102001c1d03610a4441c00e070030040c49202c030b05c040d030001901d0008252a04804001c1800b100000344481d100750396030303140900b886d115078021481d60795000065903580c0c90001103180c842d200b21488180941441082c1c2401030008074200c1c4265000100150b0440d600c0070902003110482400850405403070702c810304601e80f100600c030100c00c0d90715158044005403070985ea0321014290b9114040c4011080010040307500c001c2131204103001149004400c0c0811b0b42044250440d05030640a11060700050f02d40a0141001318a4011415504003411180e035861000e28204a6500c0e084c07681305070014204010900003005014000c2c0c040c1c0f1880000c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 890591375 1250 890590125 890590139
    0xc0b07051b030309010510080a0609060b030a080409050907051807030605270f010f0608101d07080f0709170c1009050102070602031206040f140405031908160c0c 71
    0x32410041d4035805034004000d0010000080c020107a01c9003c203c941030600d460080c0345039407031059030009032269035144108024071180743c20480c0d0301030024045407440009440c2c45002030780700d8070500c6191071810010071340036400840c901c000c030341000f4169441400189d00200704140c02078003003000e0594809000134984c55544e54051032850001d9034904201d40c061166140001c000c0004528209100051211504410700c00054030000c0c90003410350303559030300c1c0203016400681000d61000c0341c04584d0342c4514609280c4501c180c6c25030703a421100c2d07100c0c1804440900d806a41c400c01180c2515804c0c0b28500210701482800a5404c1c00c441008030348101103807a206082c00b002c1e0000b01085014130080d6010046080180700c1440218a80000c12a5441d882e00740503007603621840d10756807400d16038841d42c0c0120409089140801c0d5003802d040c0f801c903030740e030b80308098401c40c0389050701c0541c2d20507005001300340c41480c408182d10f043c0c5038a0203007155180030300c0c030044848032904000400d5031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 890592625 1250 890591375 890591407
    0x120109060614012616200703140c0a05130b1201050a05091204090c09090c020708010b18010e0a110403050a11060a050a1d03030d0501050406090207030c0b0705 70
    0x146602c010528628203404001070030701e2500040f002401c08001d0040c1d0500c09941d042542c8440000c0042a1012107044116201e20003c464080e94603c04500644100c50100d10078003140c1c0709000c00401b00d0854a080340e1544c1c0704a900319400b07003100342c007089142429221a41c56414011f400200c1d0b80d02180041e603148441400c241103a03559008000355901288201604007200703c0060440c0256a00858001e10460080600107900da005460000340135103001d00203450140010302620f4000c11000303548440c42d20030480c103076080036041103c1e82441c1c1000400540d8410354003da0360300f041c1b90030b640c200780a411318400d00c0c3c0d1004c4111025402d000a00701441c82070015000729412818030103100c0705d07148482031181008112486510741c100b011501020101d0401c0490804c58003031022408a1154403150540070002c0d804400c81425803100341a44d034111003c0100e603444403012422405801070040100d000c4926840c0480c0444030100e5008040e0300e48a032404201c04010000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 890593875 1250 890592625 890592629
    0x2060613060807170d080c0a0507020109031e0c0e091207020a03081b060a02031311030f0607031d0c0105040302210304060302190c2102070f060c0218090307021201090606 75
    0x1201c8894160900e441e411702500b04100107616103080380f41865000800c2520454075002c080c064000361860469003e0b900e160019504110b0000003242400e905612210303818070200c441c1e1000540c0403450942030001c460045c58600018190645c0c0480d00c42410b50050700180ea1100c150000000019016001440c0c0c60000012000c850001d00030700c6450500c000e4031202c1d20743d0060080150324180c65404516440d008040201651a0a0046401c101c031001d480180303400381d0720030003010b55095044583c0b40340c6203840340c89112444200c041d03124000140c2990000d03400700000c00c050320301f40281242c10b0640303c100103111210384031403601d59070065104801103600420788840c1c8885016511031304500310308101c0f1000358a036480c81401c00203c18040012842c500c00a26514400c019000c0a810041e0382d0342c0a83d0788989024003000400c0c04128422107c40f8640304070440d10b04007090050000d40c0007113062a2450b0b00700a02034140000c050ba40d507503070390b82d9240428014058200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 890595125 1250 890593875 890593889
    0x5030102131a0304030c080f0d110c0d05120c0901140c010b13020711012703111c030e10110619180803010308030a090c030812011502060613060807 65
    0x320251030b107a59904981d502c000c404116241c180100700120303411107540950320b81c0c424419969400c1280e98003d41340075500111948500d40484580d6080350340380244900c0aa8200311fa0600000751421030722131140200510943c45c840340410404000340c0040d00c1407500c1410b08030a2051074440100050b00507049202c5a41c2d183e03424001581021080b00780c1c00b00f188076080d8034052094490310514060b43c1240b6040080119107070701070340490a89000c902a040b030342e81c102203940e410a4580b070760019042c4c0c1d200720b00d0789156a10007440d24062080d101e600d501e80e035a94010440403c06000d01001642d020300c10040f001005a9600b0f0000d02d114a003168012865402044010821144003010031044145d46031040d201003980841aa41183d80c050b03880d0355241d407038030700c04c034050208032800401e40c43c410400802080002c0001e0600401c44120010480c0c4e03851a601001142d03c82038800547c101401240041c00c0c2115401c1003002001d03004501c2c907030781c0c042c1c03130b8a00340d9590310142c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 890596375 1250 890595125 890595157
    0x2040b0f07110d2109030305120c13030c14010c0b04031407150c09140609041a060307050301090b061602060a0309050609100f0e06070c0c0f0e0610030e060a0e0705030102 75
    0x1590152104c51300710309045a00c0d140700744504543c3c0c05401071244c501c143c5010720004d000241142c5c0d2240403100c400c0c49155070212055a00d02d01003800c2c0049014070f68105942c0e002c40042d551080b103542c84110f80281e182922034903592016102c0b001140780c0007216070010456440401c0904054070005254017000040010520714010b00b1400360790071645000c5078030a5482c1095883c9401d443c0000022030700001c040c004000384140d1000c4106079035030056008403c0003805a00880030394100c8030300074410720106880104010052103440e041441210301c1c02444009030a005010b00b45034a039a040020380b42105445091900b4400c942020382980035495140c0790160394014040816032140090010980441403103841c0c000c001d005208100360322410307400b809101002900200040c207003615045403129001c2000103c11a0464003d1102c0042018814840d2041d0510b0b405a0005006d59446448008020300000f03c00e5024610843d9408912642c0030b200910010034092222 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 890597625 1250 890596375 890596403
    0x12030f0a0c02091f0b091908070608100f030f060b0409061a0a0806010519030b04060c110c091909060527070b071b030803100906080102040b0f07110d 66
    0x22140140081c440405510076210b1300e4441d001001e5020f040d0792110082c1078851a0700001328844c2110a005000f40074000700c0d00080c40c80020404d141500e107039a540b0410f940d18840c032041d071940688200e119440309682c0c02c001050038103a900000b1481400702040c034803007960010b03050f540c000c001030720035541c1c1d80c2c0c16401040c44c0300002c00c843d01c0c0c00d5814800d0389141c01c1c4002d449010520911f4080e0074141c0204507100c1042c41000d01a46d4014582d4200d800e01e402d2a07130080c52081075603404182d07045d0381e481e107002d400200f0300d0035020003e18591043d51101c070101c20403445181c03114800c2c0d0704c07156900e0024010b80141c611030700500348035140c044070400c1084120009000b2150042c0c1000f0801c2c840516060f044810032508040c03070112002c00c10346022401c451135800940003110110a200818000c054020b04980d501042404400c0c1c0781d0303120318200c0c40740e0311807040424410410f107048514084058807d0f075001d1050940c41401040208030440d00c1c0003800c40342e540c0c02c1450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 890598875 1250 890597625 890597629
    0x111f061e0f05300c0d0b07080a090f02010309110307080c2e140d11220f1a041205030712021c030e100614030105150901030212030f0a0c02 61
    0x5044001c202c2201d41415200a00c1e40c1ca100d850718420303245142c0811a40f41442c207510030040705000000140400d041081d00c3e0414002d1403030705a51080024100d00c000c1814080b02d401980003a5070000003003080f04110b0f80c0150300403c540c2c84200d13000d4001b0782d0f40c03d8480ea01404000021b10700203020701002c12001041009003109145924146910780c410f4003502c8001d400803101e801a603080c881c402c0c0d42080c0615202d406902d1101c0c000341d0408840040c85960744d800350441c030f140c0161500301c0e20000c4030041411141d0303000f0314404084c0210304115a01c0000a40005210324660345031a06403604004484aa0b035000300741c3c0e0651000504804010076480c0c0300660500724405080001140d040304442644040c01c00c000b0036803076504c103a0808509101c0007a070790480480401c041c903510804110452130904119109520f0704d000a00150307005524a00e52280080010030103030308503070800c40a0f41100c400c0c800b451001344508140b0342c01c010000c126001813516056041401481 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 890600125 1250 890598875 890598899
    0x80a170408060105011d06072915010c0804120f020a080304060914040b1009091d0c01030e240406050123090603120f19111f061e 57
    0x4621102008200020400312401080240c1942c4003440d010803d007a04042ca4460342c154001c04680c0a54001036410070400141401c0519125614001200460307180c800e229500c0304680c60042c01010101c006410f40c802c4010069280c4225500750a040c4c603000b500041810450b011201c0f0392030074050a0651402d1a900d000038a08000214502402c05c1c03802060b00d8054410392111141412800f252a6240e4214410001000d04607000f2000456001002086a1300c84c400e0100e103400c05075502c0cc200500380c10240030000000302034011440004400614400d814200c0354000c0c1091996144242c41c00d07010080740b01440500241440d013400411500180e20440750342c007006003001588130801c9105204500100c03203d8a0355651140424241030442c01000d00e00b0200190000103024558040c2484101d440040e09460442c1b04090790000381655400e0240d0740003000c2900f0800305041128a8400d0000c5d002c2491507075600d0861030702d07030301028007450004e40440078458028a61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 890601375 1250 890600125 890600153
    0x90504110f0d12030902150a0c0201030b1c0b0a091406092a15040810020c01050f04151e06060210050a150b070204060b0a05031f061205130c080a 64
    0x120041d0a66007203a03146000000f110704400249905c4443c918199a60402d21640d01c1002040d469030700c100340c1d40001e0140081800407400b092511190f5945814000d40091000312103d40c9104020700c140c0300e80c054600024180080c8a0711002901c00140209091200b105148802400e06060120b0310a080654003888074510502c0c00003060101d6070b034040300e1a4420000c1c2c500d401c0006c0107a040300740920568020700d07103c5c89030074104d00c850101c6030f00030646410010020803503522131248c141650201500c0281c40690100070300140d150080d81300c11613000b40000d03507903051250020007200741c1c0d54550001c0050f8201c002900c20395541c2e4011540c1c0021001010031060701e0741c0628800e40c2c003813400765408281d0701184001c00c40d11039500030340c080c0c1074a0038102e40b144411103005020340d00032105100b03415426007854000d102e560585c14180c1d203041d12800110306410100600605004054680f2603019446600c04240c0001c148000760040d07102501e5158014204021515080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 890602625 1250 890601375 890601379
    0x60b0f070f0501061511120301140f1f0e0f010212030a060509010f03120201060503030f0a120204170f0c030606060304050a0b07081008071212090f090b010e06120601030b0a090504110f 81
    0x1050f01f044030074000040b01d06490300504044800140034021801288100c40c001f0340041000005241a01c2504446d90800602c0c0da170700c1c540c1d451040c0c14070003480c44a000300740c0540d1084150b00708204544024543c0008103490004489170380b24001205204c0070382c04014403c40c85282030052051000d4a10210401750000744611843e14010030f0b40d0703104003003400380b01007804101c005516114101e46280f80c06800402d54945840701c00d12500c160548086102c41d201c0c0e082ea4140711a0082158a40010020090281c558031001404070035030005000300e483d40920081c80f03000401c40c000e00303402444da5640c1c141d060b240411588070150300c0c075044041307986c1c17040d8410040700103003c885075003003980402d2401c0714115440080d1002c55a03a00b003651544010a004522600d0583c00038501d040240e0b0745603020007450091000700d00c14851203d003510b07242070006440e540650041e1201d203101030b0101403401c2d07484030310b50101c440603901214074007080f01054400b4a400041d842c0318801c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 890603875 1250 890602625 890602633
    0x60203070518060c07050f010903080d0608071a030c0d0e0d11160503030d110f07050d080705070201050315010519120510080d12021905030712060b0f070f0501061511 73
    0x103404499030305c1e00c0510544d0711840781019150f080740d10540105c4000d6602820407a203610455808001400ca20300500003103204140b8005985141405c14864a103110035030107107140c40c0c0e03465008581c2e100020034030401c2d88a00f00e50050420801503072203080c03095034074041c5001c032241c01703613040024007500749641b081d503c0c038113010f10b98004c4110b64040310000c000040c120501c11450195004403850700030f10070404580082803090110b0460300755505990b40183c6e41d65840c00660390740c060303000c020780014030902c00a81c0c45d40d074551200103141c80504059050460211140c40c403994018101c0c00081e1100710015000c0c6014041e494001c984202c08022042c1008809a42d51124002c03902c20032490f000144100030f501c0e41142c052110300524a070201e90907850103011fa03801552604001a10000c01000400981c07103280705440c0440e100b20b10303008038035001c0074154200d040d0a03186400d4546010000500c04d1003140000c00880143d001040b000b0700001e40038a2240e807854406400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 890605125 1250 890603875 890603887
    0x150506090705090613080f060f09070b070311070b041d0109060302010f181e031407061b03140403060b100e011e0203130608012102090106050a0c06020307051806 71
    0xa0810309032054450151041e41c0c0300c0900381c809000068590340320b1242801f401c00d030780c0d040b1000856954868450750800926540386c9058443d503c1c1c0380c621515580d05014000c9a000074401d12480e00b003c00603200320f070001502c6510850240c0e20541c450684c80038034480e107540c01d003d81a59280140707108103082010314616000a0412120240750b901003102251101da202b095000118000d80321000700128a004004100c00d003014035408240c980071140010345000d80800030b6501e081c0c0e03440ba512000340000c00055080343c1c142a003000c406105503841e406038200d1b02c40d0302901c021400341c0408078584220340c0a00001a1142c191340007000800b006a10b20359800400020500618410800d2aa188031408900b18080c1d00315403902031031000310024006521040c0e20303040c0c6040f0701d100c010003000058904003180002000941000c1110010492180a0f034040d050b40309181c2840c0d0143d550341c0d900c400490703200b01c417981c020a03008a03400240c04161458442c1c40380c015202145010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 890606375 1250 890605125 890605127
    0x60605120f040c09060312030e012c0316260a05030c0906040302130b1005040315050601351003020d060905120705010e060609010303120507020c0604031505060907 72
    0x51000709400d0401601d600407500304040a6800c0005040c1c0074070821804c4d40f2031034001001d0700c2c0403002100007414080191504c290610070b9140d8142e14114400d040e481e040f800c1c1c81030120019800301280002d0241044003a01002c100d07820510030700d041600c41d01c0b5030485481031092020006a0001d062214024854100c5e0131240c0124004481c21380368980c0a0009040b8400c541000350424580481400b901c48540c01c0a000007a0844400042441e04d0308201c07482d006510002c0c1085814205030600c0d9055036001c9034000c181031402044440302403403003585181020f08044085506c022000104071000354206410000d45510340c440c0c546107400091070000382039030240450390303101c0c1d03440c040142c01c1213840c1c810f440d407441c01a150607090134418000c2c016074030ba420090049200090861801c91030302030590794036807104c03103602410110b190000c100003400001036205900141c01e00d580c1e240003500040d88241070b081040c03060f10001d08240e60020f000280500005d5007801899 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 890607625 1250 890606375 890606407
    0x4091b0602030c12041a07150f02130e070c1b0b042c0103152c0c0a05100f0c0c050301050c0901030b0420092b0b09060402090402130e0d050409060605 66
    0x3c60b06074580352150418180000508c540707046e074070010340c908100000311160607005000040c1ca00d9000da018180d075484101d41c1244122181c00c0011003441091001030004248a40ea100d90b001100201c40e803a081200025400340c1c1010310044004164001600e469810715104c00c3c0303aa00854005514540d10740614624079980341c44e00a480b1184c2c41a091a20100444640c0c18075652545003c1000b807615211032100e018140200074021010800c0d0501512140c80c00b0321598074880c051110040480314110710410407196161400c0000807141e07406d020700360003601d101030346603a95003c800001d170484014000c3c4501803070400360000d4103040c0317410841d003800c07420703201d480e94490101c400121841450000010121a80041b8100010907126001e203c0e901c280c101ca0802d45602040a5442500303c400035031001d9000d000900500f000307000107041030380018011078060000390300d0a0030501c1c0c2c4003500b80002c0300850108400415400f610008014034103203d45880c141d40d09407204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 890608875 1250 890607625 890607659
    0xd230109080f033403270b040f0b0702030912060f010608060607020402040e0609010605070c03030e04180b0f060d051c2007230105070204091b0602030c1204 69
    0x110900110014551300c1030301c210415000d029007404000d840034004d01c0c06031868000304d00000a454207607000503607901040e40e4022515030603044860a01165a0110403003001170084840204540b41100043c0c1d181d00040c0c000d8801e60040c40d11540c8400901084840c04106002140d1000c010b01c03048080a20b5594151a0b0301c1c5010001ca543c0e0402081036481510302c001d400c07903c005800560726001d541424080c150403184c101c41a41e1b030304011035050042134405040c4d60740811041000a000d00749544100e400a040402c4810380c02650341d030130309001e0783c00ba20340340e01440401400088284040da0300c40421620751900309030944607030b584c8038200fa00b401c04c0045100c030788075940f80c001c80d124500d41b420340b202c102c40b08181400c0c41e07450703c00b0743c440c0103041d404021144243c1c0c05002603821300e002c0103a507680c0c1803d2303030380c0c0800c4007a1100440548130003c16240055111518100c600c01400c01900150303900d20780c000d05c0386e240c40d0741c840f40c0c46003141040c0414000e5010741300b00181 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 890610125 1250 890608875 890608897
    0x50306040507020712081308030705030a03050a0612110406060f0c170c070f1514070b180303010f030218062110060909021002060403020601230d23010908 68
    0x150030b40d11510243e00d050b2040c1c0000148010415105c070412990400428404150b03281444280e40d0b2900c0750369982c058020002d2050308203120f447d5401c0d209a012940c03000c8044808544c0300e03900d030020323041404580000d43d4040b80c05c00401e107403070800d4028200100140d2405076100720b0310100041243e00e014070700500c841e0420b40ca540c0958400429220021500403c0d9607810b9a0707090841c00102c081c1c0f08404042d0100da0b000e6820600500d02c41e244905036404c1c1c030386031040a03030300c000041100802d040303000c0da01130502c00c1114008002650180c228407900541040c00c0d80100100d1070418400d541d84407424004100440e25240f410200d41403801b644448808203982c000c42c1420f40d00c1c038200303924601d003480003d0340f004245c0000d0403c0f07000b030b01c01504684c0e032481d0881c0c440f001140c01501590001004000031320070380d041c04a400b00c01ca00107241100e4101e000400743d0714a0001070303035403603030803004c0c0c00c000c0b07011010b800040c0314004001c02090b210340e40c44040074068004120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 890611375 1250 890610125 890610131
    0x140f010915030207050303150108070e0618010c1205030603070e0103021c08070803040b0414030712080709092c030a0f0f09080115170f0c151306120c0f05030604 71
    0x40001d03000c0c1e0161081e182e4084c058a44a280c0304141100c4c0100c111300e071600207070080020840c118011444401c6514000e1310607031800c52860418003170020750461103410412020462004500c2d98047d82110042076500c40d5542d0409a04151811744160022010356102c01d00402c0140d4461030b0010040170346038480c8490801c1d500b41908a40601040641104000000c01c01041140b080701c03445140716030004a128080355907096035034007404100804000001c2c0101442c280036038141648001d0318035200c0d100548441918003a9607826203500b40018007540c0c0803420f114103055442801483d50011820701c004280010030f000c40881061051000074a86051f10f188982508006003404600178000000e2140c1d00d2012445103210b4039104407240c2010310b070181d00c00309040ce1803c00030001030140c241040d0401c060913110340c8811922070800c001c5001c0700c03a040048040100395a0300c408440310b9503064482c0554408004c91420400c0103606051601e4100042e203811040582e000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 890612625 1250 890611375 890611409
    0x60c060e03091504030b390405060a0e03010c320405041a01111b151306020604030f0c0201080a0203090a0804080f0c04060b070206070c0b13140f0109 66
    0x508502c110007003a90044800c090480f5400819070042c412a445941d41d0026955032850a1a0401146990f111028846540d113900b0201017a40c6401d1044e444810380d10f4a0340d5080041c1456200300d224a001c40d4031500051542d203003c0c405c1412040017810300782c400b194050602007403241188001c0c041c4075600003115002c100700c07800b91000b17040c0c0600304105840c0a060200d070742d4504603482c14006448081c03660101c3d280450741424554085c0d03606e44000c90580100f0030003003400034503611601c00501c002518158100d00c444000e00081e0042c21040c2014100100f207100e10582000a1016951000d00145d82c4850382640c010900b038001a182d4641c0c9a410f4140307021080041e240c8180071070701040a24002c90030040c0c4481010446040013102c0d014801512810b101e02100814140007160240c2003030030051954620884941c0c4401d83c40c0c0482c154540c0001031411500c40003030308144405940d81081f2010003404960000005203a0310000380030240d68060001584440054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 890613875 1250 890612625 890612651
    0x4060f02010e0118201003090f08070303060302090c0304120318050a03210e030315010c0b01030b040b0109020c100c05071a04060507084b04031107060c06 68
    0x102c2500c8211000a02c03414043d00c0d0102e24904681070190350f070305d0308046010b0210b0884154041ca0200140803600a03a09059003640241441315041e00d0401045040070002003016000b0240300e07201e40c400203035a46c118011321007207480051144845120030000d11000c910319801862840250780b0b004a4410b0a40d000c2d04002050900000d080d80b1814201d0790070180c02030700f01e8a4a811558845e14400446011003054900e000802c101640080004c9421a4070140003012492018101010b4400a590300c0c1010040240e000707075030841158061100b000100100180103188401003942840141c034074207525800140010000942c2e41d281180166000b40e050b542c809030001e101105041500b20200c0d40303210704490441d43c5520380340010f03210340c0c01071140030301603901141102c01203c01c509507103440030000c0803044070302034074110002000c1d103000b000e003040040c1c2540c070440315051074540542040c001da102c0b2290740c0c1241c0014414503070b00003c11a04076400c900082502000581 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 890615125 1250 890613875 890613881
    0x100c03090c0305060f0f15240c010f05061801090c0302070c060809060c030402010219021516021305040312020d0b0405090c100e06090d0c090e070e01060827070503060907052404060f0201 82
    0x31148c80744401107007644040c0c04c19440300c600f40c07443c0c0c0c034240300369a0b0f4078041046042400c1041d03190036015000501502e10700e640402588a85810014540100c603155422400341f540c1c80000012001c40030040d8110040c009150488074440c1c03400c2c110304040d0b00203511a1200400d109151034070011a0003036682d00c030f601c05000550948059921141d0f900c11018616020300103a0054030000856844459a4421544600c0c0c06907102000074007003d81074801b0f03522441c0d40e40c01003900d882c0218015601c40c031441d4020404500180100c942c500248004800145644028401d08140d04c810689842c8112151490212041c2c08203546a00c1c000c1c8400509030000030401c0d10380041d0004007440007940e00242e880390107d070341d47d903030303840c8030440c0c040004455810600a0310703103601c16803060b04950b00300703a40014015a41042d80720800f08e4900401155004242d0b0700c001d8003081141080701d80f46202e02c2e800118003c107800c500a4481340381c40b4a1081c1000c0000f001d100c2c0507500c0c801c0d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 890616375 1250 890615125 890615179
    0xe0c0724021611060705070e1302130506010806100f0509030a0f0305040e0c03070509040c21051906050d080c1903020307060605010c0302100c03090c0305060f0f15 72
    0x1031021511101082030003065100c41030001c981c1440c8211500e6550310341001501c4100360710400030a005414541002e5030418040d0180c149100140b141c1c00040e654910b5000d40d001d48800000391700c0c80d1000004200c0b690280c00f80c1e004004808940d522958000301d03104800d942401c21556400681c0040703803a103003220303102a00c121a4003811100b00350f4000014011038034811180d8120380c4814140d40c0d814403007500c4003800f2031703c100000d04050801d03030801c0d89100303480d0421078400c8642d04101311840e580012049462580d0380200013020450f8201a441154003041c1082402c0c00c16010406007140c500028000d040c0c041282c24000ba001c01005000c0391041311142034140305e82c41c0280d0340307800001b0115202424a107020a0951080300740100003505503005202c10070610f06c0303c90040c00404502400c143c0c41f089101e01180c0c04012400007544140020801450172401241640901a0031000c1c148000c5090010055101041c1494400112008034211440070100c4000320900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 890617625 1250 890616375 890616443
    0x50702010e1c0f08041508151c2102160e040605060f120c10080606030601030509010e0a080c0d0215013609050d020f0d030509240703060e0c07 63
    0x95000f502000040c4003c0c104440110b1440303003000305034403070a0340c3c190000c403102e01040141d6a0078070b040b40b624141c100000700f8032580c941140001ca0311156182901e108503111308aa03609110b42109a0401a140046121114001c022414201031100d14200540b01404030754a41e00402e036140d41e008e080809030200201071011041e114980b0316204e801c0101141e2140c0c18220422200074043c0494511401004140b2455640c400e8019001400050511411907595400180350800200700700c008250240c0c0d00070f41c556600103c881d20b06148000000b0854000c440d0280369007590030241410340303900844100075440b044540c1455082154504400e0001503011a03d001400b03500003a81c0a000720141c640041030100c0030ba80d84c0b4141c2c2d00c510a01c0e4040003042d0038880c400d50001d07070081c0c680400e0b6181942400340c0040300c203e8140800c2480c80910082c031481a07018070969004040080d000c140a103010443c04201d4001d03402c010384400d1188201c101100403d807525401c900107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 890618875 1250 890617625 890617643
    0x6070918020309030d0c0c1e030903080703020708060118051005030c1e03030a0806040c0f02060c2a03030f0a0e0a0f0f1709100e1021060b090907050702010e1c 70
    0x801030f03004003258030008055490905001c3c0001e6030480c0e2361307507011044d609a280c0c0803100d407030341e43c402d512640150406d0342103010b1131902141094081c400c140c0204181c842c0400c55851640c030341411184003030807103503081c00d5a86041155440101c0c2140310340d581140c1c004928841d403030011400c01d529041a55242c000000e100c2009a0003002241c01003209032020420035080c00415980704085046c020003681c010400224080b02c40c02c000d2142900c3c6414100c044c0c1411864007010700452600510160404400c1100109100c80e00c1e6600050404007800403511100c1d0b41c581301d84601c1405801ea541c0074803207038240050035807540d0320564400700c4000806c2020802044581100207424441d066150030b681055100d07007055503801600404d039103460348070807005480c0300340300d0040b0b5240029582c1440001d03001074881d02000302240f8902556030717010b9000700140042c0c024100030501074140089400360740e21000c0401c111205a440c5008102c009410703c9410600b642c0040c00011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 890620125 1250 890618875 890618891
    0x3011a0118080105070c120804020d080d0b0411030708131e060e06040c080f0c01090b090a03050a08030a050c031e06210c0405070504210609020d031106070918020309030d 75
    0x2a001100400f0240941401c07e48500c03000c10480701e0780000c0d82c000c1d40c0451080b440f03001061083c801480007880d02980098803041445c049000d841c00d004ea2038024950200401034401e030858100c0b175010301c40300c1c1150a40601507030381e002d43c6403400105a079906080c42d21501000030b240d001c403092310365410485190340381501d4000c0c0016004e00683c2464014a000e06641181c0016541031400c4c1c16151100144e051543c50400d580000034426844124034100101148050080a1046004180855491500311304c190141c4002400f039040201e410001c03c107420034407044050b01d81943d294043c80603124440040c2c840ca001c0700c40a00511046125001040000a0258818001030380c0170f0203070b50380c0d01c0c0042d2568062031040c3c0312940400852514101d92410303500500303520940000407528500d4000c81c5d940201c50604402090220b506d0b556031030340400c5031980c0320380c80b07140c0602c040741416080f00240c050141c45000b11a004800f149105c4010300994504001c0b045040000308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 890621375 1250 890620125 890620127
    0x7030912050115083d1a0d1506050a060f030207060e031306090503060108030a140f0d0e010b0405160c050703060c022b0801030b040602130801061403011a011808010507 74
    0x45100503000a44020f001e24001c030b07149012102c00011041c0c1080008001d0705c0d00144405090114004022854102002c40d2544d0303c03a694050f81d01d004003801c281c0200301602e604115503c0350085031207181880f0080151a60240c0c000c4030b402c10078036015854102c2ea29105c4040c1c8a41d682c03982841c00007190303401000030302c00c1064084404030766030407502c590380320249134440c4030a020302e910b550800c211071240503020310075044092488001d41072510140800e00c20950704250200d0036030944034113411114003400d0207860300030141101d041040d420100800c1c1880c1a00081030f00c140001280c0400c2446401d00c0704900031500100184a072503007031a030081d21030116040e000c0c0465260542c1c10004400903107172204040444d15207124590030364451035045d0200070012126a0b40800c03080c095400c540038a40c0003021078a0020403003504103c0d18440d02450012101c0c0203a1400300c128004051030150025500307020300b4145200c0030034540038140c032012a000403d1355801d10303041c000d0701 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 890622625 1250 890621375 890621383
    0x5070303032307210b0a060f0909090507170114012105011103010806011a0a12060b0705060603010c260403030e0d0e0a0504140f0c1603230703091205011508 69
    0x80755142d405107190f601104c5000c0c212402c1d80b80c3d8540103003211605120450203003c032004500800e0514a4180c0d984c5c9001100f540d90450044820f40c0011a0400c0501c480e9400c8200400300301d0005d010804000e403280e074440030705200d20099500505130000d14a10804980034071150400024020702c010107440d90180e0340207101d100c02900c240c000001e000c1c45411000c401c0402e090302803919200c0c050004803080c60f401c5d0940c00c0781c580d4440c0300040090a8000030004c4920441c05810140f51000806084940b070564080902400030001d51301c03103400500c901240c40e110512141703542c4030b03810211b005200d500345881c801e01c20718445922040e0003011016200700100c440c11212030b21582030100380d500c664181c28030031061a01064036098156a0681d000170b2240656082012052080881040407142035001c40d000a40d40c0103001c0d10000d203140800f01c80003c41d843c0c00e419990040c802140c0c1d1048125240300071a000007040001e420415921074054240102a038444003060b0701e03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 890623875 1250 890622625 890622647
    0x405091512031201080d050c0a080d2d06060806060d02030a06120c1a16030e0d06020a0e010212040b091c050a03170708040b01140a0e0a090302150405070303032307 72
    0x141d100e59050242120b101f0400c035840700c841a4041d040c05242d41e0f40b050303c0368020400c205400c1d525503003484403040510304e50407203a1003803e08041e9408403401c041d4040350703469003080c410030605a080220700c1e11a00c00b110565104440016929603820341840001c02d0180c00427031400c0d5459036018207000e50644150190b540740440c915406c030003402514141d10414441046400501181d800072901880c40904031581c05002990748500c990750300e000306d80c48000200045054044000c0695074100321030301a0014030070039185818205400600c4a0140c8020148190040c0811043e051000c1c030a10301c0c5244d001c404c5900c10185403a010703251201124041d920311840b1700c002042d1512500442c0d00558003c2c00d00304840e42041606a849002c140000f41c1111820000150007014511654814001c41d90b0005250506180c001c1c2020201c901c0d00e07280000c0e101c02d01002ca5400318904003181da06090001e00d0045500003120031084440462040c18028010017490580002000358 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 890625125 1250 890623875 890623889
    0x909070917011a090403030207141c140304060b24120609160e0315101a0705060f150409061e021c0c020102072001030f020405091512031201 62
    0x810700e00410401c0d82203034008601485010100c1800700e00500b45080640e40050091a0141c50100151200914800030381841070003940408607280c0030504010811544003201d107480c024001c6413400441c298040a00f0140440366109200c07030701c0e80c0d201003003042e41418844200d1b865a040500c00d01013500580005003051182400140b19440d00300e074058428440b800185100b5000e51408450407001086140d03010310031204180c050340344090800788038040a001d0054060305104401822044143c0b14031411481484260006007001c0340440c5d02c2204820001e0381035488411104040101446083d0800c1c5000c41c240d09200d16034008401480c0b50000352082440f608081c08202d102d14141d0064803144e024510414002e260810303588901944005404d011a90315400011200e11000b01100b61022051103101e507058000c10036015a4000c04505240c50440480d1428500811200315405070a842c516107942d07042d401040d1b100c49104503515135078825200d844064081c0a800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 890626375 1250 890625125 890625149
    0x14190b0a050606250c0f260d0c0b0606040e1602061b0406080a0b030f03030f0703060f030308061807050408120a05040b0d2a110c0604120809090709 65
    0x150711030620200300c42e894000508003110201d413030015407000012008048646680b02040000c030b9001c0401c100019103420b00c001c014212140a1034098507940703603448282c6410402d2601d81e000e410500d60000c0d50341044030a0496170703032040092190b210302c1c2c103d855000c48a10500c80303000910080c440f8040803d400b105c00584a507070010100180c060301003a20030500f0041440004e21602210f600b1500c08035021032130480500001e41010401c0c0c81000880d4804008c214409100d1510b4a4014017223040401c07502d4103084040139240c086000c003409000c501c201149403501c801c0640c0e40400513102d107048050411110081681c1e02510400c100c91080c0402c1d03415040040c03088945000d22a00d49a1519150103580105c6403ca80e408425080d940e54103281d19820b02d00c07485400c0303150802000000020742e0030103000c0d400003180ca20340070340c0141c19201141d151a4121400d46450704e20440d20084a4605051140719504009800070600c82c103104555800c4169130f07068580d41c820300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 890627625 1250 890626375 890626381
    0x618040c031d060c0409020a030b030d03090b0f0906010e1f15140408030d0905030d0903091a0a08060f0303070f08030702010e12040603021305042903030f0714190b0a05 74
    0x542c0d50380341d091342d104444607401c1108001c1041130351300400c8140d1441c1008100c00b4a41c0c0b00190404002800300c2c00400d444049110821540455965121020034886201810010043c503a100c0b0140941d5040820134008100c00c003034089020307644106180300c0b80034103a03100d581e40c1c542c003480304c1c5a09000c1442c110a0044200341401036600380e524010045040074010018000076050158003601d03940010044e41038080082d01954211a001e500e82c001024503246018004030109018800815800d1001400c0268000c0c0220703080b580855056042c428040e000908605c070f20340009250b4030741c0e500d543c010440e446015504c120019002041103811160b003254507034070100d15190300c0010411007404824003a5010340f19098550441c1c81c56a07864001240807038503210200c8800e0141c8030300c01b07081c1803400e03950300140b868103801460a00141a482c20201c0c000c41030000d040d440d2502c1d09688403242017103011002407411130040e018104038148500d8410301918000303405401c103400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 890628875 1250 890627625 890627681
    0x71103010509010b0607060506061308060702100c05030a0504060f0603050a05010b010f0206040318030c0b07020a1502030714030d140f160503070c0c05190f050f0f0618040c03 77
    0x205102400007905d20b078500001b9507540c0f80100002401c01e5440034060016407002e6000c24012000351480800500d02d50414240207807400d8006241c0c41c80030b074280035020a0f00303507028003134035000109281c000c1015101c901d840703400f9110044450780443d1400d040002032100c001554036699000b40c008006041c4200c0044031210350655164015a00003008900080e204421180c07842d00d0b000c0c1000b0071551280e48a0710303529100d50107080718840c0810f10905515096003c140240b1301000c40400c58015444065101c1c06004030103840303403940c146811007003001401210305844058000304500050701300e540c010724006485802003800e90b140090440381b601c1c513003419450070343c3e111321342103075201141100c951486100031940700d044150001016158180c84064800c041c14001c2062410004501380707660f0294480e5108101644154245071201507032628114006e40d00c6560340d80707080403046101c1141e00b6005800c10b1030b0101402440754140d1040308103c12030812002d0000700505 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 890630125 1250 890628875 890628881
    0x30b310e0712030c0618121707120902100c140a0201080406050601025d0c072102130c0816020c060d061e150503070309020607110301050901 62
    0xd02515554051002403140d09000ea4050340d2007842441c185000040b82c1d941c8505482022400022880810001a0800c460360039081000030141c50a40589550380e4001c0d004e00e1b5002d010700d0705021940c02c0741d0341caa1086402c021180f6402511a030300600714120000c140500079101907079003450320500c0f800444408280303801d100d41c05a485150b1a11580c49100040030082c00890540c0701c4c003207840b41c0c03480b212000108001e07444221011106910f6030074100140c1645240038a00514603507040b140c19409500794500c1841500081d11020b803147c034140f4180980d0403408030381000c0d40d07003004031b51044032703040c403030107109807017004083d0003001004040d030f0403448200006c00d00302800900c60001420300c8000902d11417040780c001c002c0920102d546544250071400e256074444006001072440462940b400301d5011704000c9505203410040c1c07a101c0101450a001c120703000000ca40043d101e90000015160020036155a40055180000c4200c0805030711300c0c000c4d401c060001e40d06100c184 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 890631375 1250 890630125 890630141
    0x62103031510180b030a02190e0f01030c0c0b040501022817151315140405100f0308033303060f10050d02030133080c01120c030b31 58
    0x201c000b418072080c0d1800303400c010240001e540c1c0c240230b05a90b08105062400152440d034a84d140801890b03018460700d082c120300c0c0141410f050400c03040866501400d8145042d802c030101403180d403228a0007c1c0607109044680c84019000d240500119240314202c080340180d68a42032203101400007009244101155000d40d0309500001000040c28414005d400351080381000041c81213610084841c1242b00b030700031a0b00143e1000c1c69624a0409220319600f020540c40d54403c07ca1071302a456401c0702590000038401c0c80d000c804242008802e03120300301d0f040d503080544014000f401ca104c552058041021034468412400403505403c00600218044d000154412110700e040030140001c100a6502c02ca030036650381c8400707102000c9540a0b032490f50b40707101d041c04140c0510030085d1241c0490764200000079000800200407585e0061040202045104000f107907d40a41c08140e0041118000280e0080c82d81c003c0f03207003c041611050b0041d00c00340f055400141100c400e00701d08490680c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 890632625 1250 890631375 890631407
    0x180609060708071805060a0507030e06031003020d0f0f2901181d07060c0506090309010c02120a0c0b0a03180557010302030708062103031510 62
    0x440301040c016846084001d000440880300c01880e56507800106c1d115a1050440034001800421180101680058501d1b050b00301103403601d09504040e4240300040c181071000074450b880d01ca00101c10841500070f10b04050350010f0780351031240141d05000407420f00d8012804900312075810000d0038031009911181c1030b100c000c2c5044041c1761620510a004100b42118039a610f1100304c403030020241c080013510b002c1e121030ba4560000c070031b580c5001d500d082c0c0040c00d00b00d4590400c3c821000966403003e030f61030600d41c04480030aa441c0201c0541400c00d243c1c1c90b0042c105006032a0041401d6558400900a214503030f9401c0100702c61040d101541d46200700c2c1e0040c0182c00c03522200300340e8402d480d401c2c0c552005040e02460701d000202200c01010fa0300c09090000d01c1410003580c44048450601c124211b54282019032075490311520051581100504292040c0c0782c00008194003107000f0203152070542e00004032541e9042102264600580001c41544641c1d10180d0800c132040c41191843d0100c000c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 890633875 1250 890632625 890632637
    0x613140d1e03020d0e0307120206010e1308040302030607030c1b0b0c0d0b0607060e0c0d02130c02030f0f04150c0203100c0e150c070b03130303050417031806090607 72
    0x84400c1c403100c800da907040040425400b440701090110051184464021203800195a54051803908508410030382d42e0314019900441c0c010041a030003024241d42c88a600c0702100c2101e50700e45803112681c0070b1030700f02940502c25030041023501ca4042d40404651000c1c0d0300d50520481c001c009802031050f600000038a03d014020202e01140d01080c040d24bd010030b811004640705000c1d40201d0000d0f0003c020580b262510b8403501910440d050040d400141c0c1c05840d00703021502c942e0080364501000903048980103550f2001702410038424015a20580702c51226aa92150000790800d4503401c64014a82c010384003401004129000b00ca00984075603001d4064414100a01c04010040c10074448007418010442401865562100c403407002065080b41c0254940282648031442d01c00190080210050200f0a0186030004a80d01721a21645403901003000d6941c2c0c90b220025025450000680310004401d000c501c101d04422401d5035503d103022160103682d10504aa86c64605584100100700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 890635125 1250 890633875 890633897
    0x801170a0b070f171e0603010617030d0e01060e060105090102100c0c020307050319030818030d0617060712150b030a0e1506060a0e011b05011d0318210613140d 70
    0x44101d454586c0000c00800000744aa070b110700c0e81552038a48480e981c05030304002a40094210580303d400a000e24440080013124106a10512840c1c800b620413818044080740c010004d030702c200711031201111404c800f84060112003502520050200720204c5c441e020b070300c0e000318a60500160803015022046c41051120546071424381e284000507010a28074140101e00d1401001e040005101d1601601c130006621803a101084012075024810819240c01100074802c106034000d000080d2071813505000980c0280c0c004004500d100755070700c194403c550100c2004415943c640c44030101c0c407081c10599503c108404581400507030221a06c0da8004003d11464110703a01c10716408425913810f05080200c40340c00034003044002011002101d143c0c0d128a4900c0781113a00d580c1345410316080000940c00c00c0462010a503000d0408100140209484074030400c08490301411100703031078003800c25a80981007584202140400303500003560002d1501e08402c102e40c0b4001085502d5859a81d5644000c42c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 890636375 1250 890635125 890635171
    0x14060c0d050702030307060501140907021912020f19050c060f030a0207020103060b1c0b0a060203030a1107020604080a0204063003031d010b10050a0801170a0b070f17 73
    0x14114942c281d0301072209001e86030006595100d45406425440381e20b8044440c03403c10000d000c1001042202190003040c01c0c0601d81c03c5520b1001e107600c0d440074072602042411441281b6158084005031894420862001c0802d090b40f000c0307183c1ca038064401d50f0848805401804031038070480c00c00b030500d80c600700002010b0366070660140c6001da00c14503010a140d0780d030323401462042d00854600000d030410740440f042800050b01c00d1022b09041502c100c03003024070f0694080d44900004150441d141d80751103038814a26003003c2210009540100056251900e46000a54071141001c08078010741c641040070511500c12014201e0072a003c15040e070907844901240d903030120642c0c0040b0141034450008485400d08004100104002000001327504d5078010b0401c2107040e55102c20109001042103059603040e88251501c0c1176590300100c0605000c41e06040500e080c403084000340003113441c00d081c020081d510042504032169107942c0e202101e4804043c00c496403034107a840c818a01c08814514102c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 890637625 1250 890636375 890636377
    0xd1a100f18090803011413050112020105031b040b0a022e09051e1f140105190b0f030105010e040b06031b07060c051209061b0306060d06080102030114060c0d05 70
    0x64031000700451030100682e103d400a070001c0c1c0041180c9070002c006032016050014407803170414000c032000c0c0720070351418100d140003140048000c1d0401500000181c0301500400c1e0031807e402c94015115601c5684083d50348140d084502c0c058010702070b1492414034460f170320001801d40002c008103c81040107803080700004108000e400c03245801192410000c9454841c9041184100e40015118518050809401080b902c400d00704400d0f01d0b1120a480c0341307000d4036400d170540da8282d4000541100000300c41d1400e030002e030f01512045200080c1c80b59005040400b45040703600a884540b20484500204001e440c40f4498082d000441030000134031084a04080ca01c003100c000340180c1c40c0469a40302c0ca0107031010118000d004c540c0c0050000e80040280d175259078000348401c05407c43d4100540300481d518099902980c9800c0e0100114103583d5400f0111480003104200400c0960360b2429098081e4000f44111541700e2030150b0590b0207070910200716800500e4010140c604d03081c2e082c60a90741 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890638875 1250 890637625 890637659
    0x1f08100e1006060f020c011b111f02031b0a05060720010608030c150f010b03270105040b13050705090417120f0a0204030809010311090d1a100f 63
    0x11610a1103030035640701c0d20a00c107501c0680000e07030383c0400c07029814601925001c109244a41004400c2055100c00c5916000d680000366110307445004116144001500c4510700846030307440c6041004000700c1c180d800200504441c0402000c03500e81d16014105552151080d020140c0640c03c4107001a81c454480c142d40b0022400f0440e40c0000206080318131130031107c0641041031150f0002801d407481c04010824514030706104042e0a01d140740a4505c8082490b041c41500e600c0c0300d011020403003090b00900e01d03c182d201440407581c000d44003514100d010b00425141603545241c2c07440460b026000e14042c8152080c2c1003c02800041c3c6490284412900018000d99904c000c4818070540d00c00078200904040b25840031a001c24206001696054032000d41110440d510400c0100700041400702070b107014203002d01700091030200c201c0109940384240000c19501c0f0242059030010007040840141d420110680e103180680d4840700761006070328980c084d000e40c013078800d01c0c1040001404079400c14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 890640125 1250 890638875 890638901
    0x510020a030e031f1a09090307030507020d021201020d1103090c19050a0602101109150d092102150106080c0a030906020f0306030c0f0105030a0b06211f0810 69
    0x42040b6808811440004018108480c0291111010100020b281c040f03464422403c45600555061041f2030035901c0c403405400509010010419105550307440c003a12000540142c0244085045420003e0003903004000c5d200300c9900e003030848001c11100d00142ca10600081004100c0111380c10100500b0107058200c80b00240da4048d8003154503192032080c04005e003030035001030041501141e5140306442c0c0440c1c01500104080c00555a1ba640701c41c56018040780b2a400b60707580d1810814044068015440c0c0070f42024040100c10500907950411512100c503d9802c0d210440b1010100c400761080030f01c140800034003944041002c1216102c018008600c650400240d04281580c400342a0780110707041202e2074001004115031800d0520404401c854102e60036204442003e001034214080039008112041d518441041c0760b8a0b8481100c1c0c4801104c00710f103010241c14a0f8540c1561b4044801040e07020b041840d4010694014280c0d2051710380000c042d1410b01014076582004025081d4060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 890641375 1250 890640125 890640133
    0x10509041d010e0d2604031b0204060f0f0b090f01032c01140601050705100e070f1202011e020303060d111206061005041a0c070f09150510020a030e03 66
    0x100e2500003d02c5454142c0c46440040d2090004075803000e41480c0c0c41900c2c0a1603030f28940000b8030b00141c000c1099500980c5418a22140100b02c20b8520f0f0041c0c4942000b908145801e801048849000b07000740300302c90041828880181e20750308080340306d0140d81c901315000003001000a90541c002e8004141000030301c2d12200c1c0c10040c80119008150202d2040c8500365501c400c2e84c003c09086102c5550300100078280075281c15003c2e0b07100e5a840e075241074010811540c80100101d404d0061003080028594121384000a075101c10b400c6d01c1501051a04074046030f04004031000c004100146640b400805801842c00d5545840a00102603003b01c1c044500c1001c0d2000c4a85559030b0000200e01800058002d08443c600103052003444c1c0442801d031818880240720400040035016a5068515a42143c01d5100c5148101c510703e0804150018141400805004980c484c110360210316482c2c8854142509039560707405210405004165040050304241c22110101e4010040942d94800181c111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 890642625 1250 890641375 890641421
    0x40303140306030c1e04050f070509010c0201120f0e100c02100b0604090c050901031a15071b170c04020a080703051302120d0206091504030c030e0a031410090201050904 74
    0x10b1910444424005179120311132504015401c0c90700c42c40c4c0d44450000840c03001410004400303011406400000f80c100180c500b103400840e44603800b03680545031201c1042c03101304410b20341d12024101c07810407241c0351b200c1d135a26001000820702030550b0046035078000e8494210b4640003030014004a83c4200e401c803404210000700940640b01d40e001c404110396815445011040c001400c3d00c1618001c0b03c0001d8400114550700e5580d04007009120500c0750101d07558150624081c0152034180d1946045601c0203040050448100148070b1280c031800e4082d11080d0004108100407070060040e140c00059401c1d0000c7d150342d029501c41600b200c05089600c001c612079038002050804a80c40208003508080d114401e442e80410540da01f050300800641284c005019078010907041c024000b41c1040f5a8541507010703d80944001e046403013028103c041029201d0801403030240501c5810038041c80780a14035540e00d002880362500c12a8141c0d01c503031401d80740c030041102804906031001b801d800c8040304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 890643875 1250 890642625 890642629
    0x7140f070909050613210c0c0303090f06080118050415090302101505031921080708150906040218030a060f060f030b190605030a0f060b06040303140306030c 69
    0x210310003001001c0002c01c0d00c2030289006410300c0c001515940410314001040d10000308100d066005e10840300c00d140140c3c14411104607180c800c0c8680103082e42c1c41e181d0b800300505600c009050140c0d1080b41d032121015a85000450350440c0c2445078040010b100304106c2100d19540d0015a006030080381400b05000d5505201411940d00d00303c22800750b0b102c00140c006500e1107014020300d01d81c02e00d900040c028900004a61204e0902a9801c021880c0401090030040c44100c001c072084210030b544c606012140c94060030000c070503940440464421000552816001c01c0203d42040780606880c2c0716494100902000e50045044003410811412031507040d40c0302002000c40c80c50081c2d1010175003604c0c560005084400c10342100143c245180d100f840030030303144404950460382040c00702d90008009034108009100641100d0343c1401170840040030b0060b11826000342e58042c1c1030400c122130400080003413a10581c40005e002c81c60034600d2070701480388240510341c811000f0b0240e9002000c4040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 890645125 1250 890643875 890643883
    0x19030c1212060504021c0203100e0106020a0b0c0702030a0b0603120f0414030601030f1401060b160213060f0302090c04090e0a0b07020321060a05040c170c0f07140f 72
    0x59000000c0c07a05009041c800401d80120b000801c4150b404500c2c0c102c0f21000c40304400d0251400032240c50300003020078206182c04480800605045480c04403d50311224000d480340c40500301031b2110a6a03d011601001c400422284030990040c02003111800d1503441503000c003801042c055143c01000c01501c04410914000c01054032600000c40d0307140c1c10140481030f00c1c1c20002c41d00b8041c0c3d200b40018000a041803224001c4a034021031074282c0058414a91400b50007240c2001403601c0e000304950840123481144005114404c8a54444200014004000716005886000c84040784220f041000d4248825190341003140c400b062403034907488004820648034080c5518040340c0c018010f001c1400301e0112460f41049061000c0e40c60114580003100011070349126401540103000e011070341c0340daa203520100c001c00020300244845800c1840c0034000002503ca0004030840442c0065455001c1c6012140c01203188001c2c03900705002a00c4825204e10310244d806100e00c0b551840d282d210078100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 890646375 1250 890645125 890645153
    0xc061401060e0a0801020c06190b1e0103050a110306060703031508030c210405010e270a06060201060b03040f02013e1f051302220c0503070219030c 65
    0x1031202501c081c0071034140003d00100343d00000c40c5034410f110510b460300000c14038640005400f000300c407034a0f2800303180d107000348030500c40980d00801610344665002040c0150003010356098904121070b03900c42070708105491407074001c0911000100002480307445d0000182600500a07d0005075180200074070312040718454010f1070b0ba580c0080381d2034400038800c204261050800c5400c22003001008020302c03005000d140105410f000346400c10081540f40c19007011000380c0c00c001003100f0340008482020b0501070a40d80f8640503810000d0114240303005002c0c0004803220b09240c649190382d0b5403a0b0700c0d03100341d1041d07089042100c0c00d81e072965002410360249800d400e00401e4400010300068038080c80c44926014045190410354001905520110000c4a41100401c0101e00e5548141d188001e03100c0c500300c002c0d40001c600e044546c076142c1c104078220409240d5007080028112103031083d40da50208550f2580107a02981440002188112060308a1842410441c01c50f22260f0b64154003d4501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 890647482 1107 890646375 890646377
    0x6040807060f0c060c0903020f01030c090509060a0f0b03090d0f05090d06290901060c0f1101140a120507090b0708130510050d06051806010c06140106 66
    0x307040d40364610766010350f04000485d11450050000041c60006900440d0515480d032440d500900c0342198241e5180c5500360700e00d01d403904000c00e104000b840d2507003207014080001182000b004820020b0411002c0c119204d26048403841e103001882c81c407600130400102500d06c0b88036003080403542c089005076036605510f111401c055000d4092441e0a030303040301c0e03415065208107003003d030540c50556013280c010d407159030381d0740e001c841c505101e140107001c0200054040c400940290084507140034103041c1040c0d2581c2c41c40071384100f030300a5821203010444004803000c4800180c4900c0f0f6000c4442d040040380c0a082c80611042c0e030042d510002c01c00d06000800f00380300400340c0b002c0c0004050080074400d0724800814020950341014100c1e9804502f00b010120703031481d2200c9540d00b8070b0180760b0008159038070040111003d242108054802c942e40300f04030101c83c908002040c0c041c20701 = true := by decide +kernel

theorem cover : BRFrame.Cov 890467625 890647482 := by
  have h0 := BRFrame.cov_init 890467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 890467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 890467625 ≤ n) (h2 : n < 890647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
