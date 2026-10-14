-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3292
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:55.334532+00:00
-- url     : https://prove2.me/submissions/a7466083-4f6e-4de6-91a3-c723093d4f6b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 591906474 ≤ n < 592086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 591907724 1250 591906474 591906503
    0x105030d050f0706150e0105011b03080604020a02030c060708190608191a0703020310080705030d030209030f1009061109010e01080a0603150617121905071506060315082503 76
    0x22146d485030685109807100700703207032030a8540800c18003130a050050008072032802081d05414607030007620110000c4d00580c0d08022a818a151915000f1100c50001400e040306201c828907084882d000e032411410001d00038181001c010742e917542c03034403000340444540c000d903030b6800e10840d8485040b954080d1044c401c8036043c409001006034005503141c0c0361080001d0303000554003a0000b80c0e06c00311100900900402a220f02017500250400040180c15003d2070b0008a0901e400f03000f8006911101103001542010900b0803104507401e9855980840104100d01c406ca070780c10040c03900e0048030910b0900041d80e034400c00031020740a61f07840200b1f010400c5040c62078100198001c041541e900030a000040004103160544d1005a0b60710400503800c1082201084044440c4007409030040381402c602d000440d07519232115130501506881110740d507800510149505000c0c00b100d070f98030325170151002800c00c48642e0300d403256032012800400c3c03102411801c2c04402c680010085400608a181580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 591908974 1250 591907724 591907739
    0x130c080103060c030207022101090b180606040b0d020d05030c0709021b03030103020619030908030c070501150531020a0503040506010605040f060c050111130305060105030d050f070615 81
    0x880a0104950290501c203030042d12a10070302c01d9501494004142014000314101101416051640018159525100c0721004030703010104690158800e00000250514206240317030403c82d01412052190382810002c401580e6004510071805404680b80780f072400c0e1030310f40075203541302c0e5040c10303110741c0a69600020080e0160780034144529048045101820080c0c02d06500c034402404020342c401c02c140a044030031025031800090204035410002941d039029207506c00700ea04112410848000c0c009a100b0170020700707000340148407000441149150381400009801d24000e00d034111010411040000f000c003070091090b03140014038070421580c2c1e001d8050010f02550003200c0a03a418440d2000009240c0d2043c0100d038115424010780840c52801e02c4000c035080c10794001c00790f40d65904c88642064400c13042c0001c0840105181080b95040d180d4544581400c405900c0240f04e03400c0380004c1e021468100c402c4074805601d880b480b070740c2c499a80ca01000180110380412a503605240d9004c18191f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 591910224 1250 591908974 591908987
    0x50607050703110706081b040e25020a03080601230406030615021207141e030c0c060702091501121407030513120e1c050d080709030c14130c 62
    0x54029641e01c42e0002c001e0b0301c0c641e40c441d104d21417079001405c80000500c90044d9211803a00b940c25001c00a8034196917541c0c0710f0310242c010f48041181c0303980300400d241f03103559051880340b40121900241448032000d440c050240e17440107003410b040c80102c080e0070320000d00c0c40101c4440300c81006103c648441d2141e50040050040e030107800720904001c210071504900029490001c1000142e209182c17200310359860191500300c0a1850042c811060760400041e203c03442000c0c0d030010040150380314882e10480ba45003c0b450025903014072010004403002d038440c82007466101a030b2039400b4400c400668012240416405d0308207401a02d000809a1011410b2140c0c90190602d0341e41445551901041c0e04103c024030f6100501c100e00d0441000260344c0200c42c1050154002024480103001c403c08400d400403421400b252540c201c40c080900268100c1c080c10740080040c601400164250f0b5901140c0746050b0245000080d9140c8190400343d41e88180ea0b070b0203004c0c204092040e5010004080c090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 591911474 1250 591910224 591910237
    0x207060209040c14041e081b0f0402130915080312153313080601030203060708010f09090204020d0207060b2d0103022208030a030f0606050f09030a05060705 69
    0x5500308001c0080c55441000601c3d0000a001c0da803504e086d14010703100c83e0108002608500300082c400700060b80040510461200300303048200d006020400704100982030ba14081c0b4984154410f0121a030011160364980c01a03030750610001903c00f131044a02006e0054550120306544800119145054a05c1c1d00c40360240d940c042c114003891442000708803a801000640385956074920000e40c031245000403540c011100103144140c940b00711030341031a005030000d4114640c2941310313800400440c00c0402420350312145515001c4281d504100000c00f441696100c0c801e10f0342d448581d95020b55075954115580511101400c543e187e1040c58a40040d02510744c104d84240684c141290740340301c04002246400115260006900b501c0c440190025007112503c0244109100404c0c0d5440c04207420903030181101c50002c545030608540000c2c00c0c0c50b040458541c0403800c00d642002200c5c1c000c030940700407054400a903a1601500070119181c90161400075100f886270909010203240c0000081c101d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 591912724 1250 591911474 591911479
    0xf05160206043201080406020304030c0212030c0c1e0d0528030e0102010c12330e07090308040b070303230a0c050405030c0d23070f081902010302130302040207060209 73
    0x3c680c42540c40c120581208940320300e0104507044000307800281541d0055074001d100e810800c2142c40d240c0c000c03c1c03100849815500050f400054030011042041041c807007003440c1211542409000403503004c4806002d049081c2c026081a0904410044e0030704c0b10310000138050504005201400340150b10308615a0000c2d0042280c400d14400e02d5441130041f010004002d48a1060b000324880c00400140340705400305104c020130844808200d01c8200300e440d416080410900d05140c240740100d249500f01400d0f4200703000d00c00c101080020909010385040781c0d81c2c070250685844a40c142030b2301410490b80804004403100701c40301c5a0701c544141031070207200b1000040040c0c1c500e07644107580520a90042d183c0c10340c0a90341d0b85091b4070b006282d00b038445109000b00d42c81596440d00310000816880100da580303800c000380c00d00c840c061101c080c4004202c244024010422003142c1c40c112000c54010180c10036400040303814191420a1051000f10303400b400440d03680105003040d100035004070b080e292 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 591913974 1250 591912724 591912779
    0x7050c01080a02031302091911120c0412030513031203050108010609020c120c012403030f090303170718091a060c2e0603050f070807060f0516020604 66
    0x1410840c035442528440d400008142e10408069000c1105141c1d0082c00224002401141c0207402c1c2c82501502003000209c2c8201525005088910141030000503d4a400c10350b05200c1042100c904c21010103460707416040c1180d885400d1003404854050940001e03058041e6141a01ca0303841d403550000c0d0481c1e203800000c02125443ea1480010392062150380c4000d5417042091400e101e5140e0014100844840000142c8a00030b0082c0822100f41c1801107000f00340d064010010b150700420340031a503c03941c1c50015036080c19070f54040c1000101c07100080312030203e403000030340c083e00a1444080285000b504607406170b9541e6004406451740020030411741047c0c0d0340b02c201d98104181034590100c0e0940c05803825030800401640d0120070a15080c0314801903090840300110144a043c01450241e8003504d0705590001145150030324039800281c4a0340b04030400c100050744029012480300340d62614940e0360711a90080148505540e80180d40014000741c001050700081c00508880c80c031544482 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 591915224 1250 591913974 591913981
    0x130f050a031205101406090916030b060a0f0c24290612101a0909062b02010201020409240803031005010305041506030615082410080307050c0108 64
    0x40d0b081c0c8005440c22020b042c0341d140d040c083d0306030246000b6a150307130141031641000380380702c0003c405080c1038400d00100082a05403480181d49405041e402440c240d0b03985207012410307100100300d100900d0011080080000b005e07010070104410700c6000e2140e5807602c41c10800f84a400500814242d440e0550200c40c5050700c24540602112248600c0b0004103071509140e25001529a550341c01400d500c0e26805116002c40d41d480d000056020445500e801b2646030395440062044e000f001800c01d0b40300f80346005444032207202070340018828100c00c00c0c3c07014114100b880142c1c0603015940200c540e4074207259012810f10903100c2005139404141c00c2d25414256182d40340703500c038842503414071101e108000c402d0149501076040030341c0281c410b082081001c0002c0c0380c3c913400c4038800e410403184140c0f5140000041080e071108a405030441c0b40150014241c40c0c04101d10070000c07000d2104040440e0f400117043c0c85442c5611400900c1400e0a50750785039807505c3c2c880e03160303007464040c540450147e4012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 591916474 1250 591915224 591915257
    0x30d0c050309070e040b01030b070c140604170922140411010e09041e03090b030916090c0203090d11030f15011527080d080f0f06010c0605130f050a03 66
    0x39400b61ba0402e040304e6041c1d0940c0c56031001da420052040c401e0000e0b000c910070020780303140304001464900038082c0646080c5441c1c0412040c000e980029a0100144064902780d030310b50320030001c07a51007001c1e08040d40c141c0e43e0618015003845001001524004001c00003444088440025034003003d81e9082c2800740da513003c0001c2307805e0984002d8a0030864600742d41d01c2d010385d035008150b0300b4000d0901d81812991744001c142a5401250082d289030801502c1869085146507074002421200708244124800140c0c020340d00d016038688107200d0911110703420140203e040d00c0e100e80c4074024043c1e464076074507a5051540d0342d00410b2848528a0000000a03c0d513803402000342101e104da5440c2160369600c1001101e5030504080d100100d0a2000c000062072001080050075000c519100c1502e5464040b00d0b2400b0840014a00011030019408001ca240c0e40540c01141c00c6030700810000305030f10340c022501201600c0000c020140a800300ca000306001c40020050070300d6100741e4031004c801058110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 591917724 1250 591916474 591916499
    0xd1413030507120513080d02010c090b0a031109040501150f03420603090c0503120304080c0f060a0e0c1e04020f09030105180610050d1202030d0c05030907 68
    0x4000c0c000030018044040003c410307901c2d19280d42594a403450400e10070f007081010b10061a0310824440d80848601003984c1e4081c001c06c0b084400c181800c2c014a40340024002d92842421855820150b40300401a01090301c00117540100001030f104205940c1c50741401e00141020346071000120300300010420f0818813a00807050304a000b81240c2c600ca81c0e03840d24801c0f0480000e444401d0104440c4131401000000440000040010b41d80202d00c0a0783c0d4201104461a19081180a41c0100c4144082e00d1000e10499030020760000d0550358236540f046205041c00d0b0361241100550081d0390901041040030b411040c071801c80001501c08640407502000010549c1c040810b52000c40f84081d4000791400d075018116019984076418600018000040c0c21a4004c803650301d40000c48c02c0390020b000604002c056403201c13450840c40103007810140003e102801400004000030703800b0201c41c44440c42401a01c1c0f10100d60901405441d01b003031400b03041780e001114008024800c40c0c0c1d00003200c054410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 591918974 1250 591917724 591917761
    0xb0a02070c03030806010e0415060909091a0402060705060108150604020c1c11060f09070602122713050103020f0402090f0d0203070f080109030306060503150405090c060d14 76
    0x20810082d01d107603400e540208004003198140600c659900c0c1580c2c8440c020f03407241c0440d258104c400320b410404040c298041903000380340b019280c1303864040000c40162007914449104401034555648520020304180320703030762004000307000d4100000f4a0b628005018a0842c04002d10b154150740c0d0041440308900400d0016106a8400c1d0b0b07400744042011800c0f888070f64824a0a2403000c002500b9142c80c11070141c40d86104200c801e001c0121120050140300043c0100c0d06c06017000c64009100d0303000c24019585000c030700549008c3d5807040100d00c0709a4103200840036040700300418184a0040041200348420781c05075030808011346080c0703460f1003141e103030b1038005040030342c20700c900030511181e15008007040744c0502c110803010440c000c7d81c5ca02000203000300c40022400b50941d1a0090550700e6a500c0341003801424000d115001040d50450302c085002a6000261507075541c880350f1401140ca91703995000000010319403443c0b05142c1080314280990380d40c504a540310040f03501c0c016040e40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 591920224 1250 591918974 591918983
    0x90c03020a020a030c02011b0b0a050703091a0a1b080618060105040e04140109210201061401030f110f04030218130807050a081801030b030f0d0324060c0b0a0207 71
    0x7407040800090245d40c00703a0b81180180350034011243d0340a100c0c80031030302240082d264568004200150508140540c3c4c1d407184551a0920002ea80c503a5002802d60500d0048076801c1b03200000142c850406502003003840c0601c03c408240108400d1016000c508150340c0703903005190b0071f12000b0354045491180f41c055138060391903500c1d081c0703030451800903070501402c01c503a00e01800804507a107144c02d00070360010500610490025408040f440f464021a80a9820569041100c1049154094031101c801d54100b8207010641200b0521207200034080030401d440801d070080392201800e802c071b60250040d0b0344240d800d41d10740700b440c0010741041842214002214146807503404e00141808005e0120140300345c0031621042034030398440d0486e0300994403c00c40310a13000c8080c280c641c0d05000d43c0c0c0c03072802c05402901407007140d00a0340b5110b8404586000c281911461000001200e1192121260140280031001140c6070100180020803001d0240c81c020544004110001d501c3c0c403c45401d150302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 591921474 1250 591920224 591920233
    0x20306062409030307060e01020310090c1d040b0a030b06011701080303070f09080a0303050a0b1e041a06031006230715021b0604031d01050318070506070c090c03020a02 74
    0x2031560307040d11a84103400c800d405010510100001911500071080b05000b00000503880b4904660002c41500d0039500021855090103054080c030340d004003080950b90401032035040b135251100c0100340500081100350307801900c1c48a0003c2071000d0381c6100341c010f100999994660301c0d402c503001040501c0a01400ea1680c00800c0401d10b8140a02c2503040440d405040506280b599a64441e040600c016800d0303011980741d41c10400341112512842908400485503001d000000309011201d2601034140140503030303034580b2000084150b507400107004010041029030341e4940142e030b115030458184a180301084501540030f00710003034045030001c80c00c0034840740d5042c100e198854045142c03d110504010030f070b0030031640210114000314004103652120045c441030405140042c04058000840104c240c030081940d1a80c2c1c0c1c0c00b5003280d8216007070325030201c0d5107194010300d40d0426000390300c0f441e8001c070005000810030012144100403145160000c100381e806992064040c1d1040407490741c01070300f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 591922724 1250 591921474 591921529
    0x6151203090f12150f01210302060a0504061d0a0b0105041b0311040e090a0c0f0501090e061503041202011109060d0e0c130603151a01051e070f02030606 67
    0x6000400e543c408100d201120007a40b80741e40c41c0d0441c030205882012140032410f00500012036000540e800312208215202c08212803914000c4d204d50740900220005501c85020a0621550780c01005505541b031640071840400e83c8246540e072004082e04035090b4440000004080c5494440c01e00444400c0c1c011080503020260110001d001c4001c2d0b01c801080d080c031000c606d03002c480030154401e503034034001032032039220b1800c0c484000d0389180d00403001103012920510080c2d03400300010049a4445003a031081ea10740390001000b050700e48240c4460004007201700028400c0041c1a00030081c1c49400030032900c001c43c0c2d8021280e1140c50b04058129104210241c4144001c0d0321180710990454180c8400b034840400098100c4c0c0401080e2040507100e8409206101445001009030089490b08102211103500d8220200d0030a8810394103000e0701041c44c8001408104400d080340ca04841c840d9a03407a52441c11142a06122200343c1c040c0c41250002800c5081c207003292409011030400c18035441c1d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 591923974 1250 591922724 591922729
    0x9110304020d0302100501060c02090a291c08031803090d020d060e0703030513050405012115060906170d021e1011040e3d0806151203090f 61
    0x1c2c402c01101184110814040c8000c01031241c540a0551035440d0030441a40b40104813a01601408d03056a69281008030940c40c1c040b9910b0400ea954440c1c0f10000d00d00319240001d8140c41c0c4000510865044040c003603007000f80b654001d62007241c0100c03110000c8409455045d0382c0740640346420b600038440c84520005807524203c0d5180d86841130001003601400c0d907540a0401049600440206101080041d0202958001e800190030103550401c01c0350700d440565141c0e020308441c003d006d03004d415465028088550038a025200c44180140071641c1d440144500602591240d028061746950741c11042e1038010131a000c080d02d15600a240c9582c0307a81000e401c0c2d000c8654150040c0c031480c84c0e03402c1022081c0c001c8007040260144d0b030648581c9400344004203074034014081d181d00c541003c04022030b40703007070881d0340300c60310340c1c072080801a000d1106107000300d0714540c020300d01a00c540000c004501d40d548000758001417094881d9440d11404036011780c2d690151880060f4000742c0a05914081d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 591925224 1250 591923974 591923989
    0x40807240513090c021612050a020904030509090709030606050f011205091f06170d140a050417100b0a181107020a06020610050a0627030611070b010911030402 70
    0x15000c000c2c441505941c80403040129045650000003503040740b21404200150401900300074605903005c1c14810300c07246e540340c1d01c40c81801c000030707c51110030021a050522481c16202880406004254241403c0d0009840c00009100c111449420900003045a0400e003451500d02401a1519040c40d12400306640240c5002881040c03540325102086805500d441046914502898400202c80381098400c60000000350401c1d001a03000b580c4090310550b00050780ca031003c0703855100988034140d54200312400e03c1242c4c081000d100c0041a0f4400070310002c0b420011528240c45c0800c01942104188403042d085441030485402d1500304841d0f1a84180e040300c0103c81e00301450b28903140b9030b81d0004601c1c1c125070308403070f00583c005410030110129015004002d014100c0d04036807207500e8070708000c08503c0e6100fa000001d089081c1c1d001080507105105101035503128000b070100300706550790302c0c90f541c105141c1515500380d540d0002900c4032843c400c80350798280d004045031466680b80c0921860b07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 591926474 1250 591925224 591925237
    0x1e0e060402071b2c07050a050c0f030d06060f030b03101a09160809280302030705070902090f192607060c03080901180209061210020408072405 63
    0x1109507900d240c0d000519000b1007001038001c00c40e460711403030344d04038840307038040507101584113207800c031209200f01e064000c42550310b00001850082d5403920b03907900040c00c5c4106507004880c8ea110101e2200407002c0707150400b070b05890703440c2d44910071800d040c90101e06403661201c803940c01d900003e8007842101e400d50000003c5170701042a10071142c0307040d001301d541e01c02d088030120441c13403c4641890056034061021500401603000400400e80100d545011000450711421406030030507071500100360003807040d0f41007550084103848001c0d42c0e40415601a520030600c040c4a141c02c6d520590030380c68906038142812241d117480c0408142400180c0071442c1a041c5a40324144801e071229907074403c104980c0e8054038113960380409110b214500a81005070142c801303055030741407544d42000f41c042c000301160400d03011203040b146501d5603804200d107940c40c5140314409004034032040b50495160f070018011104008215850555a41602548bc01400a00c00046000186415071061203200600780c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 591927724 1250 591926474 591926483
    0x6100315030b18250609210c080a03030f063203031902010605150301050603061003110406030504020918060a0906110408060414031305041107020405010305071e0e06040207 76
    0x2c665041840f2070b150045010800d0726004002c0d100c0c0300200c6000c941c01c0010402414040a0f0790304014a8a0240200c4150300004407085201e800034411000d00c208020100c0320155030780d1800509000340500700b940c2d40c4410302e03401e0560001e0f6900310102040c1072086103000c10000c0780b00c0a80d00341d611106008815034940300c2881040d0030885400b41100200c080782d00001807003031a2000744220406810000940440d041c00100602d48441d002c595200321b0888407210b804c5000841900100300d010540b08070014003040100320660150710141c0528002c40340c0c41c1803070740d95040d05d00c0b031940600c1554045400000103d441c1c005150810201c01d8890000410f215040c01144e001c550800ea0010f030481d807001041c801848401038401c2008004d000c05103141000141c8881c41d0300b541c0e8030826008075a03602d15900341d12a0790081d24402ca6004100380029656803e2440c5d540b2018007035000345601584c2403031544c1c0b082d011418110780d00300c000901d44e5501c40d0300700300094002010984 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 591928974 1250 591927724 591927751
    0x30a020d0c2109080c09070504060503060315010f0501081609030b15030d0801230105160f0c0f03170c0d0804030c05010e0f1212040f1502030103050606100315030b 72
    0x400c820b420501001c8080380907a80c00301154548800a0724040c141800a80200b0044043c0042560b0100031203050710390500f8199502d468003004a40f60504182940c0c2d007403c8000004501c0c42c906400388011580243c0e00c041240d241c040303005c0ea00400208081011580a060401c0041e68000c04d1a900c04100e0603c0c80c4000740540200c0c2c18840364a04800000765404014002e22101001c00042c480e0380c2186080c02e201c6107000038000e4415000003022984003480203070300f0880030710b0b1382c0a10f059004001a011540d14032941d000031180e408101c0d1485078010704400c100c0c00b000251480c448e072441c01001c1d0300c00c0c0b41d501643c01002c094401e404001c50080340c0c0380855000d024004a181040300101444e02c0f09024103400c00c4203071103d8000c800d004020401c1c40e5607070641c0054105800c000540c1102d501072400000850386c0d0750b90a40294000b20000080c0305012030b80074030842c0140c07190031a88101c400120111148070b500b05505040006040c00407801c0d000e60365502121032000309 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 591930224 1250 591928974 591929003
    0x1403011509031b0501090819060518030408030d2301050f010c05010c080411040e150a1805010c08100b190207091d0d0918020708040b0703030e060603030a020d0c 71
    0x164903850145a215107001010b43c01c11065074081d69440040c1100c1000c0c240c2c0300010040e0205180700400040c5c03050344c49502041540c0c0030580c811880315029811203551300d50f6110440c1d125003100d102e03e0580c0c1d18040803c002018580207020040c2c0c0701c0450ae0030160708080811103a2222100e920303040114021301c1c0b00005030240304032034000f4035989800c0328524152424003480d584010050307004905046820502d0307500003c0c0d0385110106020004940c1d9900207000c3c00038001101c100300020f20540c654024020b040d0701c60394000042c0d541da01416075400080000c44901c5200784058564100001540e241d140044040c602055105981405130303503a4811040d18001030b0703601c20030340794042c440c00b007076a081000c00254421070405807161031034003400c40444030740400c500b103403941c000920800300081c0408850283c108241030944410311410014018000102440524030810001c9002440d0000589500c00341650003051140cad24800215146c00d00020308a81c100c0c18416030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 591931474 1250 591930224 591930233
    0x3080313080d0b090108190b18060103240b01320301091a09040c0b280806040c030b15071106070b06011b08040909080c0a11040606140301150903 64
    0xd06450001181c0825550f03062020001c0704031069100c0c10140d409190001c8002c203111440400c11600035582c69015a034107908480312087c000003010003405600e00110412107030907401241880640e05032003c8414512a030340c2200c1d1405052404203000d5480031600d6010168110006001003921043d004d0002d0005178081e0003c0e00071030184c9440308103204d04901300b0b400c03d03a469001140e00c0e144904090f2a1480030700601e014540304c1d690009800060307060081100c540d91444e11034141c0072000560300c001c0c42d85005848092140341400441c911551003405142e40c0c0c2000103059486052408050141c942c3c072000302211446088072503044696180009011443e006000c03c04d0f151811a00040880c03e02d00d1100700861040030074440412400b4066406581c00f1620000f55981c460410f1201400b42500046551240c201d110040080c650003608021409940030701c507050f2901800c1d25040d4141103001c18842040c00104890300100d0f00c0031038200d0071420107031210740d126101e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 591932724 1250 591931474 591931477
    0x61a090d0b0711072705130204050c0f03010f06090e151e03160306150f0902092b1b05010516020d12180f030809040e0717060f0f010f0308031308 64
    0x400d0310320f2018081581ca20321400728654889101c00010082440c14075441f45800c020300e640a07005076581c3d40040c000c103244400b12001843c2c0d05501c0340d1a50b80d50804001b15609030701074400061940500001e5500d100c0580380e0145040c00c2840540412990502c00c1a070701803c00c14482d201a2110001c642c1c40c28041c07494454820303016904035070b0560a209095070440b0105a40403540d000741008908103594a903402e0720103607030f0090f0b5141c0c1900000340d602c000000c0d20ba11080ca8003040d071180e400703c0d81900306c42588600c03d05403e4510380c2c40c070b0603051030240c450700e0f010900400400d81c003403001d80030100232148000c011498402590300c41c105038018006441d40030900d0f41c3c241c40c0c09803030b403000300c1401003a115150340103c605580d501000c40c0580945280515168400003070780c41024020038000e09440c005c01c80000001c1d03254582c1d140004d80303000520141700c00128024680480d440b81c1601d0000e031072a8040c5255030794203649588010a03210000b0b1400e01ea98000404020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 591933974 1250 591932724 591932729
    0x71d061e0604080304080d0203041d0c0d02040e0a05060f1503090a080c0703170f04031b030b0717090703080702100504091a01030b010305042004020c030706061a090d0b071107 77
    0x4021034882e400c180c0e1031487c00101d0590082554420311041180c071014645075280304895284000c51500e900c0312035011406034902000c0c24600215003ca41c0744080d43c1c1c058410203046105002c0c68540391305100710850703510449034028000c844c5c0c03c1c0540c0741182c0116044850507003122159110307502d0743e005640000481c408184c2240c1000c0007407001c0d400d820242c005012000c1480d011030f02299266a1160f07110007030244e08009a918500503440c2c15100003107811094000c1e15181c1410024007641d9121500d41c020a40b01000c603211407030008000064035400b44d0f20624004842c1c08000e038000c5101d00d071348100706003000f02250480030b0f4020b200a05507a81102a141c680780d00024050300c104540050416191904000c00301c2c400c50400d800601c2c50955210b031503404100811b000c0e1140c0c0c49006d0440c4070010b100020130500c0e0b40444212694110b850001c1103a80c0840d115504c1526074895100c5441115000400ea075030303100c69080412800c260403403d0700502c8040c141880d5a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 591935224 1250 591933974 591933989
    0x3040909021f0305010602100c05160206130e01061407021305060a0f27050708010302041d03070f0b010b18090622050a05010b0a14070201030b0a0314071d061e0604 72
    0x244c00410055404001c020032410034800700b44801c03a8252002480360007280040c03c601c07a80c101c910350641d16414201d910b0042c18940c03c0810540341e1051a01d166020700c15500007540c10113100141c00c1070726054a60003a4020580034120000c000070740b0103004040c003041d61100340110b00249103064010504002d00d03400000502011401f80480da2483c0c031030005d002720500301010842041d910100140c1034a5040740c00003010440c00b0304031003401420241d00d01c600d00c000100070040c0320003008290030161140d0000071003680c94070100c1d2154000c00d0382032070300d074211840f940f42a442c0081c0c4803a03000710040c04194004048014005401a04040413a80140d40d0300a114031500c55000700b44c01344c040001420320341520308800400d58810f10401d5812680f01290b800111380c0329030002c01070707200020321800100d40c9a08040c41d01c04128107500d202e40c8190b0302d0000d207101051002164400d03032078107451403640d94402031181c200060407552041c8440400840c2030b81d56140b02a10144c60034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 591936474 1250 591935224 591935231
    0x60403141c02060f0c0f04060e0406170303010909050a080a05131401051c0f050403020d1803020d060c0309080d060503010e150c0f0c19060b0405010803040909021f03 73
    0x401155500741180c0c201d5403030511422101c036240e001e400180c081d82088004103440d1041d5207040c0d0100240c01012490002c1c1040040c0c00550207a109120811500c4101c80800c0000c1c1c0d960900d80382650000b561641c41d40003440100005080f42d07001d800281c2c006c405980c0e0100c0d079035550f01d01c0c0f1f40c00401c3d0300b03010500204220184450501c1a40007601c0034640968140c541e80001a042d4083c00008100101110301c20a0300303220302e9001545044500c2c48140881d05061501940b00c00c0340c06584000a5118442441c0014410010302c08407600035041100810450f103c2d80060140303060040181501e50f001480018000d40050000a0040000281041c1000e08150965050101c00f100c0d5600a440c4840c030052000074940c1c001118001d40342c0e40d141c0608100309640542c0d000d4820600940d0400c0040d0007140740c606403414825102005100200d9003084112007080c01035400940c030510040c402c80b03105510030b54600740028010b0301c43c0c0312044800400129a084078070300007030701c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 591937724 1250 591936474 591936503
    0x150c050106090c08130c0902160c081e01060b040b070302010207170c0f06010515030709030b010b0409050a020a0c20061c0518150c2101150c0807110a05060403 70
    0xf13100100d83c1d00311118000750f24002e4803d03110480030100c58040d545505a0010741121140d074509500d059003a4044441050395583d000d030310340c4035040080d013039070b228a088060541c0410103100316026500f0041c0b8160602e0b040c490b5281c45034000040407400d56608001c4c800c04141070700d0308400c1407101c860344c0350341e101c60801030203007003a11512044100e94007a030018001c2d581e030850110540c0040302080c0ba16581c40550803600c0400da60b00143c1003c40c0c1708000304108054000034070035075503101e00c140482d803120f0441004920030f0300c222782d000421064181c0000340301101c0c061410302a00d0300c2055507440d460001a455448280c0c492285100c3c0c4203500c0712140280143d40d4040b0080d02c1201007a0400e40c000c41d01c441100c3c07a002010380c0701000250407a10403c040e03441540700042800340181c01200c01d401440020b002c2c000d500045032404406881c840c00800c1c000076804560b050030709043e503985807d10481041c420398451220000850151542c1c40038000460040c4a005c04034203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 591938974 1250 591937724 591937727
    0x4030c270e01050919110402090a030f060203091b100c0c0515091f090b031306090506090601080705012f0111041d13031b0605010f170f0601150c050106090c 69
    0x31008000b12445040030740080c001c20117000c00b581280301b09070b90269951a401c0c0014000c01c115820003060001d1484892051082d10707030255220b108114221100c6c108500310704d400000078802481d0b444022008901030b8944502414010284604010540140c03a83c0010f5210340d980d076a460168100401c0d50804cc1c17034040420180c19031000e03601003074001e0306000140101c0c030a02802d4840c01d400808203402ca00694821028181c1000d800c00400d24140740c65030315540c055405017003500c0740100200c0c034840081380c1d41c422604140c4504880c000300c81090807030b40c0c0ea40d0148450714134415003c1103021000b07010b82000d252580c506c4582c1d6038100081c058442d80c4400403166240030090803c004074130840c81c400e103d240c042c28441c890024940d001c0c000b00054000003066582007400004661441840072404da641480c01c2c0f17450740048a40b40c50b0f0307a21800700402c01a5126600402c0b44002c00030480c0610720f0340d85007032001c0b00302c82e403101429904994800e41901d903840d42080e0f0b006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 591940224 1250 591938974 591938983
    0x130e03090406091104052707031b0f120903140307020703030f0f0516050c130515061603031d0718050601050703022113031103011104030c270e010509 66
    0x1c010440f0f08000400e440c03100e086040c065406030318003c255105d0300750034602203091120f41c8802030314203091f00c500d440c000040c060120b000001e07124014000e01a6603060250004245402c981c0c1c2d52062142460540e0102600000005400303210010034021421009640254415001d80c0c0013822000d14500d0000c0407841160582410001000124001558482c0441c1e0f06c40002503240700310348009060041c02c0c60503004c605c65004044560704007c180b8190016841455420000e000304c421031410300480d449a171400c04402c400e04605400003070301a07072010314225800340460142d444000342161420040d1380140001545120310628080300300c0c065968400c9007803070413031300f040000e56000c2d6880308000c0c82c0c80000c0008000c0c0c00a070380703401c0c015640005070081640c0250365032428082040c0c180b40e6031050081d400e00548100c5255084111000c40f680b00c1c4072003140503d01041069058a8000d0031500345901280d0304808039031602035241056484000040e44d814208442440c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 591941474 1250 591940224 591940229
    0x40803210f01080c061c05070309050c100c0b1b0708070519080a081906060804020307050103110a120908120f0703151202030c060c060f0c0711010e130e03090406 71
    0xc1c034001800500210300042614807600300e003660302d00e4983c0403400010f204c1030700304010009905d1800c0c0400c002254180c220100c4240a8000d542082014905014042e08140444008541000842c1001451400c2c529a120504d4014075284c03c5105895075129444047c2c1981c42240c00b1448006221f000d00171140e40300d030b02d42000c01d800102d941d40c4441500075442c0d40c80501400200244400d0880c000000030791070200000c015540e19200040c1241c001a074003070b8064480c002001c11503501a124940508100010050400b44010400c41d1980000078071000f100351101e1007030b0001030003074018100d03419421038031160303a2400700f401c8001c1c0e4000410010405050800c4580c900d20f004d04180203682c10300820403905085400440d107002100104030f5001300c000608500444400325110b409525001840d4580d6100c16459500c1c0d80502c40f4081c0500c09804800364696019014122032070b00050505000c41104442c88821500c0c03000c4110035a800008a0b20341d149070a2048802 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 591942724 1250 591941474 591941491
    0x708010b0d0303020703020a0804080a230705120a020a0b090909012c032223090c2b0b280614071b0504061202150f04080321 55
    0x10412031a40041c000015a020103801e141c1d00084010902d403092107a040ba49401c4520760703540780e81c1d407040c65a54412120080d592040c14004185d0a8507981c60004048030003040100312550504003044450016400503d195204802a600c0140c8a81d544c0c200209440a003450716a1440410b205040b180101030140e20707490300140c0001100d074101c011214209030b030785900c01c0c0c010b00303d1514910303c21610703030b03110b403c3c1258101d50440710000c0c441c01c00d0780c02d0340c0d443e000c0004111881161080709514850303884506400001c9050031110007800101d82c5902060869005040c1e003070121030a01010000025120b40b0f841005060203011881d00340420034040e00312048a00c4108482070720b6000d104204070003030383d1a081c0c04080b0700907507a155400c51412452429032003c807000c1200b0318402d4502540c1000d00024021040882d010b0b4a180c0241c443c070701c8051207114170381007a88103009840b6040020f100101c0c010008201810717000f0014040349a004050f29540200e40303d00409510 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 591943974 1250 591942724 591942731
    0x10c020307120c0f12020120040911030405060109050c090607060f0c092411070905070215070f2316151b0309020109170309010801060f140d0b04021b070801 69
    0x5000031201004ca0101a4100c0d01c035031642e60701e41508a016110070103d00341c50000082040301c91014a8008104403100104100b05c40d2008900c00e541034003003101c0140080d0003100042010a62940009600c03043d14101c852034409a0030008140b41c1102400780d4030140c0d580b405082040161150314003085403801c00e900301d20724081200c1c1c0c004411042490300c00300e85200d00c011a034001c4c0200112400d405054520043c1c0751904036004140446100c4010300c140c2c080001c80c10041143c0780e001c0c500e2a03070340f107991250012041e80d00100c4140c079218402d190315a510302203c0d4000150003c07c42c0810031540148603800d003074503609251001c6490141c900304604030700403c010b1180d555090241404202003065000681d1070141c29072040600218001d11000c1c409404001090032401c2600c402d011641c0301c0c141210041e031440c24040100300c0e142c400d0304d641054140030b080241510440402c070070038404085020fa1300524002c081074001c007151120780680900029024050000082 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 591945224 1250 591943974 591943997
    0x90c01030b100e030c271b0304020909070f0803091306060504050907030b0306181603020f010507050a050328020f030d0e0a02030601181410030303020c0f010c02030712 74
    0x2c00302c01c8620360035010301441014445003500d0510071030f1140000200040079000d04c0144001040c1507643c3c0383c00855500c08005030401c2c07110303071180502c0c44008404509582d0307580d09020850304040c00d1411284121100020404516842c0d60b01030b18600c3c0c059500d40c1d44440c00c0c422804070160413035603600d0402200b400400e0784a010349084a804607004442030311008030950007050503100c0c194260140504011650741060b40703031000c0607100411103040e00c5101715003075015040c0340002903102c41c0101c0007203030030740c402e2001d41900e50040d01610400561a600e9524680c8032100c80d0f84c02c0c0062404402204440c0c149420380b20429001038a900180c52a655443c3c1c8254452205080c3c1d40f820440020b501c10010341600765400b4080b60680d5071911400c0309406111503501202c1410300d4a030764100c0c0d8240410034040c41320711403105800c0f82180e4041e8083d40082c844444184580000603054500c24061611000242d4000d103944480a090070780c5002c40e80c504040510071100000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 591946474 1250 591945224 591945229
    0x504111e031c050705010c030903080c180f040b1e10080f07051602100905040f23060d0f1208011421190b09100504170d110a08090c01030b 61
    0x2802c0c0c00200040155000e0205580262201c1c064103801529545ca00000ca80c9400d030140c2c020128a8000d4490300e4882c1d80310103c07091f052240b103805004060406003c108030382801c5803a00200c0d1030090001c0380c410214004203902e04040c3e009031034441200c40e41c10249041504840144c10071624008440f850211014840c04d840034010314100b0800141c5100382244043c4100720b034581c014090210f0080345000144403800f03500aa912852800c00c00419240716031085045035000c480300c03000380704420302c0c1110300c140c0d005090b039402540f1115040c0000702d40c2c5a01d43e40c46032007210070354520607080328010501d43c0305030003450541952013403410303007039440301000411200032403441c0c00b401c41c0300c540541c20003034100310414070606503918880400c5820078100d03104440b8542201d0540c054170f900c0c201520790503078000d07002c0d101d51006441240c035004010721440c14060340105501c81301401c15500703640400b0340b000004095800740103a401060061300404c0109182c144110f8822800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 591947724 1250 591946474 591946483
    0x111280c050318060403061e05060604050f041104080114010812120103120903060e07050414070f140c1903110109111e13021c090f02060d0f0504111e03 67
    0x19050f054a460380c1e00d05015910182101d000d5540884284205450b02035103811038403054080d000c4507800c040000e03c00e8105582620201c40c00103001c190903094040910004090303907030184480300420040407511060034002c01045004c0302d4404032b00c40d0324040c0100d042c055040c4032926105001c006112210740024207443c15a80c01050840f02d13a1400315040c4c036901c0c0c55074002070440e8100345180041110100b02d18046803001c0c1e8042c0b181106050307614244800840300180070400e0001122025071040186425200001035403c3c87c08840074105454007116035207647c020303005c24880e00304055028580c006400c803500001c1c0100701180e903800f00420720491f0030398000d10300425003408020f514901302e280040c01810244030501f40c0200d443c007035404000003c00341117241220b0b00c10b0b0380081c800d108401d074000c200100007916a0342002125400703050b40980180d00d07928088903601c8a4407885000b030b4031038034401e26500351450a11141000c00d4291800a030054200c007071a549001c01d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 591948974 1250 591947724 591947737
    0xc0c1c0c030b1305010f0605031009120e0a081b01200607051804050906070f021b15070b0f150105040b0912010e0604030f08010b04050102030901030504050111280c0503 74
    0x252400c41c0756180f444a2044031100c0030050130660030420b0148074a1030b264003240c25100180c090390101e05105041d6401c0e038034007a000400b101c00d511010303075840e44240c04d145200b03200180700c410403980d01d102540ca446480480c0016895540a4145e40c070f6810070308410008035070088a164502c000c2410988a5400400394024400c0c0012100804142e6410950300554020010000ca040203801c2ea80e80340000c890b144040746004c490205a103000007054104007001c0d0714000c0103408018240040440d082280701501c0505101340c034005039541c22220710940c44280084501d00d002c014029107514000d4810723044c07007030812060056141031411208000800d44804898450080c510750061040503103e0419004540c1800109540a046110041216514118940d032201c1119103a84140c2c4031b001e000d644104102c000c50750194005903070103070141000065110b13140a40004039071001d5182280ca511448503600840050b81802c42003020502c0d1484c1d851b50250f669540c1c910541c2c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 591950224 1250 591948974 591948983
    0x140703080601030605130204031109040b070c050a0c09020d060905010501090e04080705011b110118060c180609171605150904020f072001020d120609020c0c1c0c03 72
    0x340059101d034020b4101c81c0003004040d00d01e28000c0700720340a100080d003050108031170300ca01c2c200d110121450260b403014040ea40101c040600c5882c3ca000590340750340c0e141c400b1110b030700484c611000410031950005c0014030078114056660350380c1d08500d0088445681210080300c3c07500c0010302081e6070221880050307890f4424803103c030352030382d00342a0030a00802c40300802541c02c201501c500d000d02401500500016034031101d5200b8000b94185081e20b00c07148102d1140042055101d002c0740c0340c0d811044030242c5504140810b03003111206000d110340d198011501084861404201c3c500d810480500800005000780a26601c0d903001e44010100c40d06c19544149080d480c118000040a022141c4100b0010011550351180e000c080c0f00a4001980c242c4107d40701c3c0c00402c80b0414103405465410905078040c022880c1c40d1041502c003500c00d100d440c082241c0da01004685e0080520040030034042c02c0d4014880c40300303484d0401450f170700400f00f1880410014504030300000c0000000c541130300c0e0300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 591951474 1250 591950224 591950237
    0x14091006020d0e010e030111120109050f0a11130e070212041202010c051213090e0303060904150b0306010308121b07033b1c021305100321030c140703 66
    0xa003401202e004030341c8441170340c1c1075203015038130022142d4100c002c001e904060110141503a0341d0b520508111501203039255a01d000c0140040c1c58064941d02410300030030460700c154100301010200e00090009504030b48003030300c80d1100f0700664503010490301005000c060b0b08985014201154044104c031100c40080c184440400c20500b088010b111007140c0c91501e103a250b0303d544122424064120680c410011341500c0d2488807030840c03070040100c0340314201c05800790384039881c0d0b5542d5a44036041d484050010942d20f040c45105643c05114050003140a85603250302e40c0c000600d044440d9401030300a1241c040300e42c00260010b4110400d0b0380107d03400d414102d620002d040c6c0042055113061621280c8840c5028a0b00020000790340c81001d0f00c1d1040c1d070020414140e103141382e05911240c04020f58840e008110050302c2031126003042c1ea00c034503d50445000903941c0d075910bd03c0c065085130740807509000c06204000300c0707030706104447e40c408681c5000040303c43c11814062884c0b00b20100601005903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 591952724 1250 591951474 591951497
    0x200a0506030a110d06060f090302031510150215060111070603151701020a2c1306050d050a030215010e04081b03042705100b03070e0a14091006020d 65
    0xc2503215420f402640b6003419920300400c4000c034020601c601440021800307500c400c04040b8820070103c0141c0364040d000b055560604190758029410040c54441c0400c01c51201040d114162543c04881e41c03413540042106030410000003028030320042c826410000d10031a090480840040c114044401c40e0900007080c1c52020541c05819101b5006400d0414004881810500e8154004c2003146801c0e40c032918841c0100180381c15004603049086007461780e00c041c142040c503140c4560340d1208007001002501541d1800820055a2068410754080d00074052040c103064050241022440314040324181e01c1d810101c0b00700f040b030005803010b01212004100c1d00303c622945c00e04848094001d00c01c41e910341da9211100307031803500c0c403a40b010011800305449180c5002907000d014002e007480040114400e0810351500166000240840304005100054621988074625000003500c05070001111318012481406240100904072140c4801016420010711341d002c58188529082840d100e0540e45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 591953974 1250 591952724 591952741
    0x51605010609060b27030309010324060557071e08070b09010c081c0203011719110607020405270f03160204110a080103200a050603 58
    0x140e60b4004240c442e140c030f0404100c458100c405002e02a141081d409000d0f880403203400b0507900034082c002d4050340705000d40d20b01d560003504601e211028805c00c032035081078108801c5540100b154416008140f0028040340841400c94034544076a40041900d800c506451400d070b070804005084281c203078410342c04000c000b100002d442c0300c4642050802c03500c05507126465007043c05411113200b19240f96420000516040102d0690100d03000a1041030420001a00540b015030518100300c4816508001ca000750484051855410700a07841c40103843e507040c510583c50580980c1821001c59100381404142d0741401500300042a5028200350100a480740c0802c5c614004d110009610030304180401c946046194000c8407508124501e50300e205d1000405180c41d40e207200a245801c0d002000500480301c8010350b00e0713070b40c584050310000e00000910325440b26030704009505000204080c0c010410b214925000c7d0514800f86032000c80c01c44215400103040c5807031882031034000c100100000701880c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 591955224 1250 591953974 591953981
    0xb0a0207120804064415150f0405030f0304050103060e040b0406092108100b0f040312050421110109080705010c1a090a0b0f0c0307031805100c0905030d05160501 71
    0x42881103170707944181c00c4249000ca8032600d45545c1c0d002680000040811000c40d036046c80d04040a00b070b4040c0645007400500d410790062942c501504403c0200042d5910200040a58010f40201443c0c45900340f80005060360366551100701907101440074000820102680942c002d940702500180443e0b56140c00080044010b46816140120910800c0300e10b8000030b040f48294007981030f290516031240407401c03080c013880a03441c422907011710007800000e20303400d548200091641800f604180c1d0321401544c0c4490f506009106810380c20381e502c000c02c1603000b00024070480c01d081c5041c0d03980c2400b07040d680ea90007500c41c1e1810848000128400e200000e400410080701198809142e8a000754415a0312816644201e0380c072654840051800003688c52050b003c2c1c040c2d01384161464960800c00c4000d400910300d0810030b0801010004e0000b4010400c20440c4825003d000c508280c0a45000c4c01c0354902e030303001d2400f03500b0000240e40342c6039000301210303086112610086c019441d10709045005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 591956474 1250 591955224 591955277
    0x40b07180504092a03230607050a020718020c16060228021810060810060e01020f060103051e070f03020919061413020a0c1e0501060b0a020712080406 66
    0x110b548144001360955840081d002d480c050665000700040c800380c08900000700c0c80d8051b025802841c0810030302c6200d44028003084165104943c1c50300d80790b58090003030285965102500740c0e400555031004250901c04180c0c40e0640e51004a1114900744019450390b1120039600314540541c442c01e000c403031144088100c13054001d84074401d00019201c0680305c420050b15204502d22560380c0000307545c1c0c0310b03242c031510404071004c0064405240817415540c165042185030b06601682c21014100c15040144034000d500600007400f40301580c48014120304001c140564642d002030b1000d01500700b030004100122541070f42c0d0100180e0f520801c808481e64884400894241410f4001481510302080003100c10001c0b1104506100203440500c00c0740701d0540c406011680301345d08100450396904a010f003200c2502091145181641d0310780d4211103141c3c020002940000c10103880041d0304215900c00740000384588600c0b03844a4980d8203042c00783c1c3c031904040050710136040c440010317000c060341d81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 591957724 1250 591956474 591956513
    0xa0e030123090114160306050303070f020d08250209060105041d0c1309050702070f03020d021002010f020d140c2502040b0604080606120102040b0f0f160506040b0718050409 76
    0x2203081400c0718031180c1d00340e480b4520006e410b00f1800700e014600030045514140d40300328650001038035a4280418100c80c0d8800765042c08080c08001c00f03031158188600464031803030749501e00e00a068030401c040004c01030039284c1007000a01c4140906410f40d94003030340c00400100814103641e14088060114810f00134903a0091000000025803c500c1c1d4005d03030b0080c041a025a0031641c1c444c00d03d511215414031010f9404071400103e00d01600b8940b612003031011862002050b024108000710050f80d00861500d030a2039070b5102440380c020003400c41c968104001ca40da95141943c11800746c1101ca0744600042030100200c0d000508643c0d8540c0003141c0b02001400135600d850ba0740000c80d480303502c1260200c1c0500c440100e0f250301c1c20030610866094405d11300b05603041c0303911601c4400c565045105040c0c03610300208007050754441c4d031000102c1101d01c01c1000f46998030b003914120a0510019105405001d502d01034000b00c056041844c80030344906450009024501d030070300764501d400c0e100281b007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 591958974 1250 591957724 591957761
    0x27080316140a08031506031504020319020c0f12030903120709031b060e030109080409091a340c030e06071b151d0d02030f010f020a0e0301230901 64
    0x410003558801541c410300c0f850780c5140c5204064818442c003481f08a421810050061384816154030b4198041e6801081944101d124134040c246904126402010844c034030b540f02c48444888108100107010f098206110183d0440c10030303503401c2c0c0e643d002d14402c10000e91081030010720034500c501004070040d074000c1c1141001035010b25814145800c41d0050000003400342d00f003083c1509050160410080c2d004550620b01072909842000800026070100c5101c41c4801c0d42c500076200b0642c3c80f50046000c0d1568034850300380c4207100880d05500e001e50685120900e452450f2080e08003032040540c070f8240c00c003800c2c031880f9140004d02520900e01d000305014641403402c1d00c0c1000844414003510380942e0004200c090a000c00d641c0c0c42d00c030a03c1d0154200110a41c040d45080404102c0d00d4680b01074100c60004110724821820741e007a255120140707039030114845402c55400441002d00c4241a0020011100000310840580c10281c4441c88903204c0c400100d460360800351300c241513042410b003028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 591960224 1250 591958974 591958993
    0x3021006060c0c3b0412180303110109060207050102090a050d0503070314070f0b01050906011814011b060519020901020a02041d0d09090e03040501020307030c021c032708031614 78
    0x1301c00701d5505480540305404154038500b4014003400c0001d01c4055100001120b061030341d42d04681c161194101403206548404d8040002903003800a0428548103400258a0301c07090414041c084410740d01440c45174001c03100c0b00780482c2c1301004031400c0a2f05882c28003500340c0e100010201600c11703d040248560368611081080c04070300e207403050580c1e9085541c00c8035501d644c0d00440e41002c80c110520701c4601e500408200302e210036510030360111010304050000e40b12002c030444001d102c1c0b00701950504e407128100140901c000c440b903904031220940450824001d600000e580d0240008028040c0c1d54031022100790458000c440381c2e0b07150709035080721101414484000d16000651080e003040310700b0102080060580402035400351681a40114146042c0c1d03181140c0007011303481c040ea00b20b840410708140c0816445650040c80b4080e03100c0c441c0a2000b41d151900000e00e84481400e058001e040500c041c48001c811241504a0655a16a201d1090400c000700840d0f400b044070300ca20461011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 591961474 1250 591960224 591960329
    0x50724021e0702090a020f040603150302060a020d0305071706100c080a030606110601080a030c0311030d0e0c03060403090506090f1206040302060a0504020907050703030e0a03021006060c0c 83
    0x42680070303c207944100f10f5890700d82e0750806a0140e404010006801031200748152072207a070042144441c00080350540c1680c1c0e40218403a030b0b22805860b00141c000741c0610002c9901401074a03008001450b2500340100741400340780b40c1c02d2018240c9489000d40c40c00a125840c40b4071192486a90001c41c3e040d40c494114502030010320240c41a0300c00304141c007103841050301c00803c101d81218841c402400c01040c4a9a00f1681c01031a00011002c0c402454181c10300000104080d060881c00d41c0340004981c00640c52161900c00c600b022148664032083c200400079900000c030004982d8251419915a1f2116002841656420050b01c2d0011104921503110510004411b4060360103a005c0c0c980c103440301c0c0d4200058406c1104e01171341050400b40852440743c03280d00100350700c9003c2d19001850801034519282030040216040e00140e011104d41c0c4d901c41244d1003944020710050601c2d5501540d181d41d0071140b400d1510804000020303500c0aa81c0041d0984180790524801e000c501101041400c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 591962724 1250 591961474 591961477
    0xf0c02060604110c03031501120e010504030e12101505041a0a0e04030c110406031b0e011401140705010e070906181103061e18041101050724021e 64
    0xa2003803045080214040c3c07821034400440305000c140300701a51a560b250b0864405c0c030500c02a020741007064048100c0a418400c2c0b15403004202d810b0b0010a0500705824010008410002442d10603511041c44441c04040010710203010444201c0100780d400000c01100454451980130369002402d1080406421440f125240c480030403c031000090903032141341300c4881080c1140c0003800318039100100004100a01c3c90781e90a80c000600206040307403290340e00113000c14104500300a500c0d18103005d005000e515403200740500b01c1000c0c0710b0071070100c003400200031407040030b1000318040e03000a4050502c1001c0d040340d5401c140300f4080310805c55640c171441c4024042d80c4648020701520407010400d07881540203101000c03101405043c00c50320703103901b085881070124042c02d00310944520388000549802004a03110580412040198034107414105c850a0351152014100502000b60300300260064000380310580d42d001842c2c11a0360034604482c001d100303c170898405080740003038180c02000306a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 591963974 1250 591962724 591962731
    0x2041d011508011b02060103080306190308070b07020c0d080306041122121a060406090c0e0a0812030c0a05040509102103080a151502011d0604170a030f0c0206 70
    0x10b000700480004440841c050703030007400040300160001e000410114200754040c5030840001010720718032400d100b4554404060300d501c211403054007c5910b800340501e04030350503440b50740c41c0040c10214800c140050324014215000030040080480421b119031225440b40409110345800c69960b0900440040311350081100c05a80f904007424010030342d01911a20f8082241d480f284031018403242103031000c1c080c0030080080f0307006680e441c03000034104124001c842a0b0003c0d41c5030680c1c0c0e89548400e00c180c540841c0c01120040c0d000c0107158920381d41c8001141e6100750101c49072a19100c00c240125624030481d4030066012201009102d0001d5074103000b1006c41f00e13030b10000c410394408110b2103800c5a2460b1000381c0420225000030340441620b80081440f0a113070340960343e09907260416060300c40700c01c040490051307545600c12500b010340001c4c070141c200c40c500018403a44c03030588d881c1c81061103642c02c04014800b012030b03250341c42d074020741003610384894009040c0004a0101002940c0d000100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 591965224 1250 591963974 591963989
    0x306070206060330030a14010306201201030308041a040c170d020d0509010311040311030f030f1801030e0f0604062f070206070b04050a05010f0b090402041d0115 71
    0x2c080200038810f0f900080c509040103070360040000c1082c10720b616507600010a4040041e031a014100a11103a00c3c030701c94049c611482c4001101c4045a85c0c001040241c0d00e440064a013003041040d158069001c6614116589881c100f00c103076855180c501d042003400741030b06101d080003000b8001046443c1c2e958100360f174502c8000c5284e50540c42c0c81035544400701d040420140c0c0000c82c28011051040c0028030800340103041c0172604422413000c584059000b51700a03100258152480c00240c40c0c28000d20862100420066061000391410314881c3d204005c1e010500b08031601c56881682d0107500714105124440c0140c0700c0b000703c2180c0440d2216030880e07088901e1703860108403400310aa02405141000f0f090924881e944041504031800c550000c0d0741640e0003482807111000040d0001c1d07085209903c1030024004c0c54444d85099402d41e00744002c3c9950042c20103940b06041d4890040f03036684541c04660110302d810780c8400d0350a085085010507400346d404c005038810601c03030210302d0758200d9808 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 591966474 1250 591965224 591965233
    0x10b10030b100e01031b02010506030d0f12150f0603020705100e030405060c12030c04140a05090402041d030d0902191a0a03061e03050c0a03081605030903060702060603 74
    0x140008408989616180c50b034048025403881000078400e84040110100604000521048a0422400d6002102e107041d005030b4640d8100102810203022061000e50381d420702d61488004880040e1840c80c4418144c8401c0e83d440500a1414501402020040c40c445010300703661900d804009000e5804100160703a40e02c6185182800c4241034418965003043c29800f0390304040c2810200000f0b40c5c407404800745d06205180c490300709401c1351001580070383c0406441e190354516001313041d9240c00e80c0740c003524842c030a258401c009980742c1703190140d030055048800140107582e013000017400e04c01e00e41c02c52404e4031011807014040c0c00c0a9100c03181c494002c070741c1c07203c0210b14400c0d00b4070582914094000394130085100c401710f50a00750060181c40505080c0846c03c19102d00d45031014110600b40c00d107544a00395010414440d06100c0c07400713600001c3d00c414000c1810364940c1c001c2841030300034041309882080220b50030b100e030510a95006503002800d440c81402c00356402503413003005551180c441d009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 591967724 1250 591966474 591966499
    0xc09060323060609040b03010e160801020c0d200a0c0503010b090c07032609010c090510020d0f1407050703020a06171b0433110319030e0f010b 63
    0x400c4004509506014245000240d0b144400e000d5950004042c4030382181d20b901d1244d40036a428087d0880c405560750050820400380b10f02d0340410f00495021035145d9104200310a6441c102140c0b00350340c8504c0e82089080b12903203100110103090108462040c50181c0c480c0d40080000d0300c62450100c0300700720002d03c5450f03038207420001c2419068501003e1040c0c00c200c07050000c4d000e00c0d141105c001031540748000d00c0f16013031607481107000b00300c5000820b40d655269810b21103800011110141c0401e03912044c00701240300c806550740b040c41d8071440c1400702c00d40c0c1002c04944a42e28124114103c00341503900c0300300514002c2c2d074031007042c00120f1041c126214040785441c407030200442c0c201d20040c406800b541f5403007000c0125007044074404100071030070000401c0403140043c084540300d0f030420100e0b80800c2c69a81980701258656821020841000d000f0500e284000050740c0b4a0071000c503400310708071075020065008000c07600c00487c050003412030459075408191b1001441002c1030307803161003409 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 591968974 1250 591967724 591967751
    0x1b050c060a14220506250c1203080405010501210213060f0603060302090f220f080c100c02030f07030509130c0f020706050906040603050a241a0403030e0d080d0c090603 74
    0x1d400070102030f40d48016051b4246005d034090b5038001500590340403900a446109441000080c45800c1d40455151001e00080010074403490780100314030303000034101e511070f50003e0a40000100c0003034403805150b2820120301001e40c5c8504c005141602d9400e85840d40c848001d00a8404c51100344d00c214400c10015a610b8020980b04d48aa03030000804c10b051519000c92103800c801c0c4150a4403180c106c1111800080d8040d0000d060301ca8100d802844410802c203240313819118507003002d0045400501c011040314039102c050710882076250400641b0b0f1444800805d52070041c0c0350840d0f225504042d0714030031403900029402e00030521503007918152a100c0d03400366514420080340c50303005a010042004020702ca54011a0070458020b000304285c038005407a0f80e80100340c500740004c94043c81d8030400031402c01712440451100c0010b103481c01e003451928058650701710dc0d642d050040c190b41c85402c040122040c2184d102da98001420069442102030080404446000f203402280c40d01c00700c0900c0d02d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 591970224 1250 591968974 591968977
    0x60e1504050901120f0b04080c06090c010f2607031b05090112050c090d11040b15030703090c1703030f090c1e0d05010f0203071b050c060a14220506 65
    0x70780c0050002600c69282031803007a00c600540c00261041000c0601c02c100044001e2012801a030140214a84605906003590b003800c2000c1d04d0000c2d0ba80c4040f800030300c5640c0200403224025200c1c10891039042c40c801c030b076250004a840d22425010204408c05c21080c0d05580003440391416512003c0310074005080554a5104141e80e10340428100701070340c00044180d8015550110041820a0504e485080403811303403409040100c139086001551411141804d201301c0881c480d0271107540d02200801c20600800d4032001e024501015295403110302808800a600e0008020740c1c05201da90803403000d8510340782e8100b9202e0008800d00d070400304540ca800040c100320000c07401440703a9a9170b00318114440902c10130800807034200d429140c916000c02c6c828410014503e003a03080150381d0f442c1c00341c0c0c000c00214a40c10451601802100507201281c000155842c00800584c1c000340d5401c040300d8103881241c400503004040c28000514400580124582611003026000d800ca525984070404c00109 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 591971474 1250 591970224 591970229
    0x7030b0118030b042d0201030e0705180702210904050c04060807030e100e01020705190515061503011203080106021b061b2409070302010f0302090118060e1504 70
    0x1641c90400c002d0000c160030307400f03064016115140d2066260115440c1006000854a4401c01c01130300318103a03030541d60507014034440300c600703440a04a21400c103800241040c960242c0c104000445100240010780200245004000c001e5062054040d0140a0001c69484045100d0080d424580401c00c510500001e0b981a00c0b16504c0b070321401c0d550104110000c040d20810b5000c144651540a1384503841882410006404800096a40d0641e418480e207000d030303a403100c07081d07000c00c05081201281c404a001c46203c000c160b1080130300d407594000100545500e01581103940400800001c0644d4001e05850b44140f00c0d80761280107a0b0307251405d076101c502c2c0085084a120075201404030515142c0014521040c903401e0044a0409000d5094640342c0c4011079541580800c40f0300c0004c0c0c0e10342d0a5a13541c068082c900601102d1b00356400200903042e1070010205042d00401c0070f5056030301503040704001040c1400c1084405980300002400d5a5001106234020030585c9505954100c0c4102124207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 591972724 1250 591971474 591971507
    0x6181403030c0714280303150311090702070b0d09030e01020c03030301090908040308070c0612020c070e060d0f030905131401030b13050d0e130203190e030408100507030b01 76
    0x2c04445440b03003510643e541048000c2401030315202c21507001440c07207500700b0120005c00c42400c96840d180140858045140b04262000700640410005410310002d050610083e0f4584000d81c4a08405078a8030169411036602c40901040c810701c2510300c0d038809011a03002c6e0b50780302150001d0134010b81c3c0303c400c202c41d03807501500100014000c958982c0c120440d9184605c044030700e059925122a20150060030003103a2004081000f003184a9200c240d14140e014040f208500d40381d0f0001c8140d0f40c95109109440108030180b00054299890180700c15816070040e00c42400e9400c213190003000716030f0b98005c417403081641344d0004921130118403d80704403001e49481440e0b1a42941c561006030580204410f001c80d510f01071000014105000c0d9060a4545490390148201c2d20400c0040c00320611024029192050080000c204401015402c2500c8030307035070000307a41c160041c010342184501d801501a52203200f10ba89020325180d4030052242030740d998200540d0309880011605030344980380026 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 591973974 1250 591972724 591972727
    0xe1003090201080406020c030702030f0a12141813020a022107080708030417180f06030c122508010f0806040201050307081e1518070c030c020d06181403030c 69
    0xb8001505c81c1e008091014007c400c4a040103200d500080c078280f8001304484040d040008107200b00030324100c502e4111020790501106e460000307420410741d4022580c40d080441a501807500a503124001ea02402d007559000955851f0031305240690394080f5107090020001c042c50b4000e46451009080d900701aa1085100d450700050b6100c0784907503080036000380c0317411032190201085105020000d10f031481902e940c5000100c0704008028010032076803c2c1e01d004500070400c110f00402c81c2d104440348100360b160145802d45030005940e49a11450400c0e80740500b54050302a000c0c0e81002e0f0150480c1c040320710069409844164641c2c80e40030684000780824420f01c04a11003901600300541d0041083c00b0203a407a5032034083c52290440140d80007e9204403c0c2200104c80c24090b0004240c100e02c4081c9403180d0400d94001020944469005410803c840800d44115910590b034442c01a41008042c0300b440506541502221020340088508400c541c0c0b801501e00c00c08070170790303114440303004500f0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 591975224 1250 591973974 591973981
    0x6150a06030e030906031806130c05100e060408010f060506070b27010c0503042a05010f090e090102030108160605030106050d0f140a240b1c06060e100309020108 71
    0x76005848820078206440c08113025108840d19a0b901031071095800d8500324070001ea0b842c4105003000070152074411100e10403d10b05001c1540104e85000f21b50017a1030025103504030410440784410000013117a841000000d001411203815040703001204c030b2030581080351543d05d100b0005503100b0b509006150700301c0040020b01402c0714200400000034806440c50155603a4508542100e8100c1b40b044041400441800140320005031128616240701110380b0441c541d07444c10161640301c511582c0d0404c03046844402e090303803056040350002e1026020079441400c10f210582e010350001d0081c54281c0c401c0848101201400445040c122081c0e912200d20756400e1840460380342c3d0041001d07440580d11041d02c201c0d036100a10600023480e440d80d50b114164101440c0003000e4444003c070860108100c00d03034804200f40004080011102c4018015688201a0304900f030810b4a103514a070099140280005210b0f401415039006844200d50781c00c2e41c90b5500800303400321000c40c1c001a0000c2c907102d000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 591976474 1250 591975224 591975227
    0xa20031f0b0123030106030629090409060203090105072c1e0d0309030c09060e1305072103030c1719021c0b0f04021905131d0906150a06 60
    0x501e09920614052481c0403807a8100e400d020351603092003c031490b000004110442c0d0612656002e08840c0c4d510040c016240b0140071406400012a41d404d0900014256030582e541c2c0d000d84036040e486903040d9140d00e041443c40e402404203d40c1c1c0004030700b503400c82882110300c070703000c4414100518031401d424040840921031058508a240f00d545031a032144a8125900c10000315011842550354250041c10340c030b010340d03000d40c086e8054000c407800c100082c020001d076100e005a00255240300d002c80007106003002072819500c1d0f0f0064070706a400e401c05039440c00f0442c110300c00c0b26012303407020b00c02e914040d90211010718039a4041c0c41c88007034000100d0030701c0700302030712840307030401074040c007501f80b03414520702030604650110032411150740c0320420344003030501c0180b003a03c01c402190110300b4191010b0b07805a0303c032214440e0208000000410207103040c00d007080da1000d8022591030191741046c09507600700a140654820500c0d104000001d002c14a0041140d2008030000d004140c029140540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 591977724 1250 591976474 591976481
    0xc0b0c0607110307060203010801020315011b02060315120304080c0108160f02010615091d01080606060c0109060603080307030e060702120a05040513590a20031f 71
    0x2d41803568001007200002055483c0007442c0600f04d100001a0f40c0d0800a001003112130f11990800c2c140002104010507410b105014111003035016035180c0e40c0c80e541d81c1a410a10a008241c4aa000c81108142c0703c00d10000000307032083e5000c480490f01c980d5148801076590040840307076105140c000d03141a040b040d01c41c52061800c991240004100640ca4454002800c4501c040f0f010000303481113020403940e40191801015401c210710805615410800a1074450200074160780c080d4000040d0020455003d50003842d641d0b8003e802000a01d441c2c0c607100c56264025580c46002030f003030001030a950703180819001c1c003903c41d9800070107803440d201c1c02d51500c581001c5254028000c003804001400c2e1540c9000031030307140100100041540c815665010004561a1008049280780c240d00158030f0800390602180407500e803051040d45054003900c184400b141c03080e003000d40180c407000810006079032501c04901e8541195000140b00300000c1c90f03540c0d0fa041c00f10300e980e8480308156500c442e40951 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 591978974 1250 591977724 591977747
    0x60f0e120f0631030509040c030c12020705030d110c0304030c0e0f060901150c0507150305160e040207020f220507050a0516030e0a0308031605070f0b0c040f030f0c0b0c0607 76
    0x28003900f080c6d4840d000070201c40081c640300000c00d441e1100040c1c1142e02101c07400d07000814080031030074000e01d511025501d018000c0c061041955a02c0502460404030056982c10950300702126900c54807860b014501404612800c0819403181c8041042105214400c911403500070305218101c3e840c10455444140c1c0b4040d645091002c0d88040d00d02085090082c1c1001d003200c0d0303500712494141000d004089030802062440b2030742d0540d42460b03c5a42c0250801e0242c0002c071405612541c4500000e1081d00f980341d0318a42c000b805644112070314080184810f560384200108100359911008260340d0303485a80048400104100032960b0058850400304550034002d1611040114440300842c82210300c942003900c69010200401c05010049201d5082840c0c440ca070190400b0415a1003c03a03902d02100001c0c0200c0c1e5100c001201d0045540030385008007010855050801e81d203081880d000b0050340000e581e01420100041103070540507041304c200d0303840740c0001c00e03150f81c5805048030300640c00d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 591980224 1250 591978974 591978977
    0x20d06060e01170a02090a14030f01021e0a1214060a09020339040608100f052d0312040501030513170703020a02060a030b1905010801060f0e120f063103 67
    0x3d000812068581c010500081d04500042d0000c41e18400b0805261200e000b2b003250407a8010000b4a064644070f440c00802c05000c1e00c409a103421100700280c1d810456115034075140d0b450f0174102e00544000d140e055004160a41e4140d00d140d89415010040e40f1044480d48040c40e802c0c8501649081e101c034142c140b81d42801e113102d101801407000b200003a4442d0707000c40b0005040c24140071046810041d080000c1c00c0892003004024a4070f40880c400451540b90b1400c8408080000c00d0700c0400e03440c000c0300c1c007280103054401e000210401c00c621a006405002e000a24000004080302c00f120001d800b059007104406400030107184030100113500c10b190450860086062100050700c804000e024540e155840c0810302050880c28803000b08625840e800011b500107004010590b005100c1da81074845514050303e03100280d41c01502c0f030001c10100e0b250800441c4d440e80300200c8001c204020801c503800180d6081e9101d000035222040d403c005000c569441d0042d901c40c80131607003102c20301030a100703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 591981474 1250 591980224 591980227
    0x303050306280308070308101202012f0601081e0309040c090f0909060f140609060a0b0309060109060b03012d0b120a1803090905070e0303040801020d06060e01170a02 73
    0x40701d9002d12501d5a200325070300d201c0031640004040d0841c0d0981c0e406800d10268101d00c031700d00b10400c080c0440c3c0d10f5001e414000304e01c4481401640201041900c914454404c003031050804040e150b44c1d100901c81c02500c0d008140030017441442c0b88003681c1510308110000c50420002d50200001407040031800c1e001e010508100103020409041400020b14010348001800d440780d08181065814400509641518041c903419144075425006a0803402c00d66500311540c0e0340f8808a0700303044d6660400524074201004200301082c1c0041c00c94140d81044c0003e009039036840343d600080340400c0c000c4d5582b428480c000c0207004070448008408040a0051140e801603480924141c2940b210500c0101c121044080220203400340c02000050b000840b5141800810707a00c008005600c0c0d801951900303a140c002040e1482c0c8105c010515408004054031b50721350380c84070300c40d000f50b21803264044001e080c0640014001d02a03100c60030001c0c0c068550707441c00165070080f92140400103180707008080d070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 591982724 1250 591981474 591981529
    0x80a090f08010605010f08061309051018110a0302130c120603060e160518090c040510030b010510120e01060b0c010b0f060f04060f05070b1003030f08010303050306 72
    0x400d5003400c40100410740000401500b0480018510400307510b4075402c1c4440481408110381b100c0001c19100800c00710f00040e0180c01d45049410b00300700c501002d000f079003000c0d818071a05203543e852070000c903c101048120004e2080620000c00305d5440081c2d481480303035074028a5000e0380d0708030307a802003a24540090070241e024992002c039240c507002960240ea0b6001c8803203280300208200001440e6a9510400241c0303014005032203a01041c40021414a4060114102d04800c0000c20030404000b0300c1030100c0e24207440c442041980c00e02c01580c03846800307000060182800b904d01d000003103075580c48480c0360440c1c0032604041d03d80455461901d650f00d0304009404418880540fa4181c3d104d800801c0344070611040054000300b5080c602d00c00c0c40708020b11620050031804540c110f078070900b081c0f0410300d03030250280c40a002d5030780c0c050040301444003008101410f220108056904c40d865254030101c042d03a0440702d0150900005004c51010808918540f8080c40010380d400c81101274400c00c1075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 591983974 1250 591982724 591982739
    0x4050d03090909080c1608060712090c060c1a0103081207020a0215040603060609080d0e0d240c021f05090a02061b1218010c060b030313030b0c090a03080a09 69
    0x40f03080000762a628070104100514403000e000c03103c0c052410380482d025160501c1107194807108040c01400c10711114210324401c403500344d00401c0c11541c2020608540c0350b669017000c0c2c6070804208007100c411801c03505a10b00c8001c1411918142d83c0c01000740d030309000c040040100d004c1b5000e8600c42c151b100d40018200141e0303d001001224100700d0184548031441c0c0320001d402d4607a00e80051043c450048014004c0282c0010f02441d001010310786100003440c500085503800d141c481c009401c2105100b080252040146541d00003401c020b0010807400d0000c09049885541801c030982045180f810701c40d03544103660300501d23000b4550f10241e65076200a039000504a501c60b1200485a69807500d0190099409211941240a4071141145450402c072010140e02c400c2d0740725207043c0701490b18107406020716a03102030b01210002d41100e0741d54801c0e4001c400040b01c184000c4074602c41a2000503206c0e44101c066070340c0058050034200920741142d031b80000300c2d08940301103c100602a5800101c40d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 591985224 1250 591983974 591983981
    0xc03060507030b0f040b060f0d060b0f0909060114070b07020f0d0806031905031e041214011512031103070c0303081f031e030c080d0f0f0e0304050d030909 68
    0x101056200000c1803c01d400600a180100d04022481145000442010341d254203007214050340c0003614135a41d070400126140e0040c00d075a00905500750000c142c103480e40400000a10441c4012160070245983d0100112074858010f04060107400e030a0090200290300101025001034050043d141c500d04016401840c080210410318001042803050040d203003818881d24030303d03c030741c9545c1070b0b15640c2e5600c80555910a1000c64290020041000c020b042c1c90201a5000b0307140d055030060b00000c0d9800c05010030703040280703280c00b554645154030040ca01c001c40428201c400304a016445200b07035403000e480340b0124020151041c081044100c001419042400018520a4070307440c00b10b06061200242c21461701420249546428a0030b10108150705850110b03460a0014111003c03541d00d4102d51900041d50001e08245002c240740802240a4010920030b43d5103107030801000c10540311840545d040303003916600641013048148494213000b0710070600d841c003a080850455580341040400c030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 591986474 1250 591985224 591985231
    0x10e060c09091b030708070e2d010c0c06030e0304030f0f0302210927090f010e0304120b1b0f21060a0e07020f030d090c06020708030d090c030605 64
    0x1856000210081586070509100d9040f004004419032021142d000c1c21141d44805841c0a00b8010150005007106208007807480c11441d0203040c4c01d49440f1600130448080c2c48550441038029505100c0c1d2a0652180d054001e00f560040585d40c0124a401029401400d0500380d0000700c4c002080f0100202d4403d00041040c1d0340b255842c890f40603041d0400a06001503c0031903031303614458854a984925a1070305453b10f25804070340c9a020100281100d101c0d10a8079405003800301d044104206c0410008244002d00075a0741009000c5010002102d9032a8800c81c01404200c9150344c2821020035a002042503210b110741c1c410b55036020010340303001d1075904a9900d040820038002008050711a0070100f440320186001412503a07810b003074000690610007030017012070308081c00b0b00041348940300b04041c0c400750502c1c8041d40c0d0340d04101c501d02005860440010b0740c0b00d0229a0000840c01c0c80021341c5412a13090002550030400c08004003c00303010030400c01d4401d030900c61000f00c0858683d1285502 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 591987724 1250 591986474 591986491
    0xa24090f020306010e0403091a04080f0705040c02070810050916030f03020706030513030e1c050105010f0f180e0c0603070c0606080303150d020a151205090105010b0a03020903010e06 80
    0xd5031481014942407050b000414104260024000005c1c0c10a4480f4251440030459041d01c1000300e10182403409544d0040b2628817801c0a012244030b00480c4001c00d8588c01d5400f401780081907035051340c1e140024422201542e101d800490021b0032a17500c000c2c1c200b44a0b0003581d20707001c14690000165401d5820590381014130682e200300b01134040180d08010140b03030409015a00d40443c0600380403001c000060144480c0000500701ca5941c070303a1441c220444000c51b808000004e08100d030082a00740520008004d07407900104000c0c0001162008441180068410010514174510060b16441c20415800e126081c000006641c840c400383d0b2040740690358851503601c0701c0c1465010744820b0360004805400c20403c1c04020540410907030901c81095071110501440351011860b8140c10394444100048190039005181b13601400c0c040e084400b910b01403005440d00b00d803880c202d0781c003031140e2100804200071041038503020b86c01400350000300170300010303051040c240810b051807411039290a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 591988974 1250 591987724 591987743
    0x3060316080d2703030e01020a023003031524040e090c0f0907031d0102040303020a0515011d062103041a19050714100c030f0903020a2409 61
    0x3500039840400710610300003004050603ea000900b204601010324000502000000e4445126590003004201012030b409045031385110030b45400c000c8100400c10b11100d01c0c018081c50100042d8000041c0d030f00403100080680b0803e04184100000802c1c03402d180d81c140024030742c0c45140c500102018100401c40d0308210f020900d4041940c50030018840d00c00340c4103900c40741c101303a002e490380d5803829402191410001801c800c10910b44d40721071541c8042c1d0b40198000200401095030201d030348203125125104a500c180a1100b0012424000740110a034001c000300d64003104c80394000306542c000d407003d028104881162580b04401d035180c880440b40e2913000183c06c0001c81d040c0c0c0c1c0c116a40b0941007442d1424034000302c0d804900382004002280c2080320100d0120248440488080e141c0700701102101d055200c8100d050b00039123242c018a5021134544071309420240001c1c01400309440d459806840c0c450120fa542c03043c100030440c2e1903002c1c000d518090704401d02052290003800c43c040c1d41d0b544d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 591990224 1250 591988974 591988993
    0xa0b0a0b01080f01031502040902040b04030309050a180f0b0d030201090510090302031c1104090b0f040905030901030510080706091703270303070204050f090f0718020306031608 78
    0x2401a2a90300380c0e001e042150380300c01c120440380c683c02690705513075001c0200700071001c0b1610007601031300490300301d282d03c180300080c0041c60b50340c00c030000c0044078825101d400c081540ca504110043c09644920703803a201e160195110f4481481d40030f00324070041150001000c1100c200864110504610102c001d40e5643c400c80050000c20800d2041d615a010014030011244da50003e49134040c20030803200e0f0701007820301c101800c001a0031040f4260f0388161107640300e40e80c680d80350b406880030300c94a40c0600340c00842d440300360a150156040c0c40b60031100551401003000011001024020594194900c5900380410019024411070300103064070307600c14501501f004985a015401e02c0c80c1101558410440700715114462000c410590084616403060f0b0340e15400402c0c29440380c0040254800e03c0c143c1002400340d9040d00e902e008082070700465006041422000d0754070340b11b5004152020500750440140d0400940003154805405130540761410003011280e8110740c0c4e1038000240075004a00304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 591991474 1250 591990224 591990241
    0x70501020a1d1c0f020409150b0a03030503040816082709040c05010c0303020c031227060c09042009010f0906050301120302150108030c1209060d1d0a0b 67
    0x355400340380700c1000307080100044800650b110f400311100b0702900c1e61056110301400907980a4030076550b0054010301c081c0c84030307180940b01d070788460004441241c5003d66010346802c08030b50000940e0784c5034a4880c070355200d9490707034030184c0c005900380b101500f4070003c80000200440003401d46061035254031106506001c00e840744502d864007540d401107520303404101c0420f040000c690200d034420300f4410018400e50a00b02e010b407082041060441c0301c005102ca014041040b1094818060254072100d4004202c000d60b60303030084428100400e82c45200801c1c0c254038510000d00010720010000100402003062100c01c88460000121500300017040c40101940c00003c00610342d01a440c2071900e1509102c000b500d64001030250b00d51f60611841c200c0c04240c020810342a4202c000783e0f82d1105582d4880b401075603944441909541400340c0b07250420b0001d40c600039258403260051209040c10141244403006010144204069075840c0408402c1008184031400c2e42c140603074182c1f40a031070801c46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 591992724 1250 591991474 591991487
    0x4020c15151c03030b19140f04020307090504050601121e0e0604080d021c0525030e0606101416021e10180b0406020708010b010e01050708030a060308070501020a 71
    0x40842c0500c0707001c5440c0e40515100907a8081150f45400c00060584a400210b1040b4416251106800320a10400709040c0c0d030715104030b50b40700300444100d451122441300b800141c1c0003e030340403804201ca0010500951405c0e410680c0d01103c103150a554580b00c08183e441034944031004000ca081c1c01981c1a5940c5c40c550040d03801070045070004000d6400e155898401c035109442d4042401540818100c40340c0740e2084c1d24807001d80f4002c80601c0981040b003019144609800041212190400c40e07085105001c2d02031760315041c01060150005540c3c9000740240c04188202c0d00041140701542c0861602465016128001c0c2c1041015020010340c030500048030000e40241344880142185040190b40d0340b0700215a040d141c1c64500c282159504100340c4c2d12a03e500b01c3d500800010401140341c65000441c02c1c100d40c042c1009110346166071005481c9075900d040700724001181004481b0200351b0010046d074000c1c8100400044556583d101d42ca07954100b8030f8100c03245d075000580b00c40126070154 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 591993974 1250 591992724 591992761
    0x10f05060a0c030c020a0e0702030a0f08060d0b0a0f1b260c0d06050a060201140f16050307020708031b06090607120902040f050408070b1303020d05030604020c15 71
    0x1100c6070318218003500060040000108018200130f400310316041151035012800c40245103446828820741000c0c60702a450303410801c1c102c2c002600a0307454458a03486804218040c0e000501804064090781d101c4641076003008041440036900c0d8003c01c1210165841080f020100800551035000003180c40100741c0c242c04041028520000f0440c1a801e202211130310740c00440310300a881c0d441410404000c007400c80350f8001c40e4030201f100701c00280141c043d0441503100042032805001c5582e592800904182c0030b880c82d41c003062019940c21000b83c040c000035038200060740102c4090740d42e0707010201d180da8000340b410f00302d0300680481a1000001000a144c010800e04060629860a901e0040039010302c5001031001944440300341080d9201c990120321000c3c45084184010b140c1400c000030154004003088481d02d4046002814400e5060030b01c110b080d50541c0031304254814200110307000d030400350039164480e074200032400c040d1354104402541c0000c034581c031303040514004031400c05100707075003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 591995224 1250 591993974 591993979
    0xa0606030c0609060503070e030c10020102040513020309070b070302070801050702030a08010b0a080408090415121703040816140312070807112104050d0501090c0b1602010e150a08010f05 82
    0x194020300080f42c004060340da0002180c505071000703d5010b0004ac4c074041c8400d103400e4120302224003000c21254190020170985030240d07022040d202030720345894100d00c803c440c1c2041c07941008005001c182115001040301174007034411100403e4840920301d003169001d40741e800140e0710024010300d00c0343e00150400c0c0145500380c4590b09190021002829840340203100030304220b0700085004003581c80340c0c0107690b10044d0f591207042082d00c0740d181c0298600480c1c010381d0783c00116a80e0b10309000c031003411288180d80c0b02840c01e0801c001508240380450880d41c0443e81008142004040c90000b04080c000701c0c0500031001c00c0d1800c0c0b40303001620f0440e024004404100160720110124440010022101404e0010401456500202d421072034080c0f80c0056901000b03c0102d1814440150421400240900303c02c1100d20ba0358450a01a0b1140041105c082c04040703080002540c0500e00359440c003840900702002031392480210405943c0510442d1010900581c01805054005d21102000e041709 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 591996474 1250 591995224 591995237
    0x1003060e0a0c080c032401210e070e01050604030b06031903030c0e0102190308090c100f080601080601120504060617070819020108041b0308070303020406180e06040209030c030a0606030c06 83
    0x400c2140480140b1009224000c1c951b90a10b00c00701e0b445003099080c1c0100c2031070b1700c66054042074204001b5042c00852100b10388101c400c085022403501420070304844c0020708079031400d1f03e50b40d58001c802c83d000f0b0010343c3c940540300d40f0780c00409806042c0c0700d83c01d1007a82d00240c0c0c010300940103080c100a45c00150b04661000403c14640c602016041c10781c580c250406480c0b981c0c039090458074242100710030031b803c820014012000907412990540042c3c1c0700791640000765803a0301c011504410219880d03800036a951103481c02481d00d5600190700309014410100310305441e10751200c48400005094125540000020003001900340b00710042c100304211200c1c400e05d6240c00007404a1005040a810804102075022615640b2400c084c015988040010b8a1700c2581c10080c000350403502c189404035480b007100885c600401c85848054450008881c1c2c02d5884e0035050000031b400008003550036100b000d0b0300e420182e6040040c0000b0500c5803001107681402d51a1160654016612840030b0046 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 591997724 1250 591996474 591996481
    0x1104150b040501140c0115061707020c010f030b0d1b090e0c01050306180a1a120d0f05070804030b010623040623070b090f07050604051003060e0a0c080c03 68
    0x20000c11a001c4030740900c0d0402c4006000d40d04040f00748140201d1410079803a111540c005401081001e01c215000e54030b80718031406901c4420060b143d01100c8079801a00702c48554580c56004d4590030a102402c1d141c0064040490800702d580c0400c40c040540c1c0309450701c1239511b1585510724004002e0411561b042c88002001d603503103075036240080844c0741484000b10024490b62124101c040e001c5e44501d8822405041c02450030005200c0340824000010090007442402d003098080b0b4103141141c0c00003841140c0300858111041c0c040c50301140c081100401c0010042030042016001450068030a130080c6d51406001030080c0f0040c400c81e03160b105c0380c280d070b8441202c100c10a80e41103508a040000c44102c1040c00800c100f242c4504408001d400030501d4014002c82c0100640b048480c0b10484901c80000c50050780e54040500c41c0540c000e0301080140210f0520598810841c0f0712800c0208185885034200340004c1811244842c525941c1c98040000707c6e40029581d8110142e448090f2031401c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 591998974 1250 591997724 591997739
    0x30c030f0709090218041a0105010f020303040204050c0d02040602010b09010608040201080c07051e031902030f0409150312120605040506060405040504111020060126030d0207110415 80
    0x70303188551010150764280b0b02040d501c50341c021000350800c0a810100c03c0c6003034a42112020901110301c0c01c884000360020803503502584540031948102c1d0010340c2159034039401c00003c1c0c5001084460721503414001c103003400500380041d101500d032a0300085030895880d0240142440e05a010400b00400c0c0401d000c00f50741c029100d1900a5403075130940e9621907a5043c002d00c1e1080701d5541c1d0f21020350000702c1e0b442145000c0050b2606004001c00410715520601080780e0300c0c090b4102c100c000c14800c100c2042403c200790b21400c040d00c406156403548a50381d450352000201c00c840014081500c2c6115984408814803c0c5070103828200c40c100803e041800106049000314002c181c0281e99641c049414001d9005c840f000e182c40080552184c0100341d9001820700f001c0c403151002110f00100e1620701c074a008600503058a2041440c080c020340c00001084401444c80d142c0c0301a800300300034a6034810900d00040c400140240c061805040307014003404121040191800d0748218117013810301444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 592000224 1250 591998974 591998983
    0x9010b27010c0201052b0209030c032b0201092a120c050904051e0705030d030203090c0409080d2a020312240a030b01090c05160308190509010b030c030f 67
    0x203070740a180031511600c451081c000e246c01e01740c425903019809454040140c41d9180c0081c00440380c10340998207150890414503a40b5250078540900b003101c4081c4035034560304009241c030701000c150310021595140307070344521000181c00c843d8504041c110000508806510306100c100a1a4110312041c0034045515000000d8416014591003a84400041803d0100400031003100c1340c0410f8120003081207100c40d02d940c640461003624000e000d6550020f2140f0700038400e0f644110300001c0039107400b400680c10000201101d0b60201c2d016030b41807116580c9444d071403044007402d61202401001c48400c9001d032005003c600c200140c11544100034022003001c00c0750b0340c00d4002c001410020460740221089102050408080c16007214440800000340811005010b048a0441c03208000c6a80103100489480c07003641c00400003620320100c02d4000038482e0302d04550003074002040c43c80e80c0c4014000402611000d841c400c80503034603501c0740044c502d03050101056003c0b04600074420b4201e50f0300c186844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 592001474 1250 592000224 592000247
    0x90a08121005030f1009080c190308100311040207050718060f0509060d110301180302011506081006050c0309040c020f07050a06170a0e03030f0a18030504050402090d0209010b2701 79
    0x6d85410326203080001202c10364040d400000e0036105840c0c0a1840d6000030103625100354001030001000c596215144a00c00f030030f4980043e03044145000410502003c0d600402003107402d07100f030003000a1206107111070300c241c4021040c1d010a603a403521189042042d0701d5044648501d64010034007407136903503010001c090664002e02d40c14080882400180c010321007a40711005040e1003404140405038198050700103642103039070b0200d59649030181101c1c0c96104460016a2100c114400d1018600610141c440d0001403001c0760b161090040200b4140c0ea080400400917034420294840000c1060200401034030303055488109451402d100100600c05550700f80345103014400208110b05410b420010264955034201d9660341015030b0503606810003100c121221070b02d410312300c40704440f0502030500c03001d415a503881d0506041c4010080254041960603900040c100d41d07a50041c0c07100e51000c0e00078082003d1894495134a8051404643c00030340c86a030550700c000ca560210b50b07070801c1c5c14914 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 592002724 1250 592001474 592001503
    0x9200609091501140d090510050c04231c0b1305190812070f0908070b04150c020307030503031501020a0f0b100e19060e0f070305090a08121005030f 65
    0x9890300b0400c016290010300e10810802c241c400112403443d500c8940015020744d2140c41119004070f5141c0e81c030f82c02c917482600c089036071601c104000c10643c40042d50312850300380b94100c0c0c15008140d8a0008411613038170041a140700694070501e105115031851a07550000b00d442c80d8072000a030b142d0318243c03139a081d000101403040c241205842449200b07002d803501c2c092824511800740c200400d01400409e589001c04000a403221401b0442c1d800100f0720b40c0849241c120301c45d09050601441c2c0041491b40b03107407074042050b03000042015913420404940258000c0001c1d42d56820134078898070f14100e00c0040b40741594012039810001905020303442302d1080d040000703501952500c0b580488402100d5210540b100c0c6444140062105030404c801007883d8201d40c10400b03165202101041010215020420030b6168030004242600070340080b0340c801e004005444085a19981d0941c0399005000d0400001c14100108180d41600340a141d000c0e0030b0440041c045240680002035070b82c03030003900c4400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 592003974 1250 592002724 592002751
    0x60b031003120c0f0c080115152115060e060c0606060a02160608060a050405010e13020112020f040911040b16030c061a010201051506090f060d0920060909 68
    0xc210900c00c2440b20042d50b4000600c0480130f049090480c03c1815601941900f946001c01c164044600041d0303220855030001c614079103220071007070282c030100c0c68005605000303043c040381c0d86a440b2040c0f06405841e00b20114036144103040c8940244079008400d1140d0048400300408100018005a4994000d03002c40344595101c070700ca48128105110344000003070383c00304500089107580e00f190b1000c2c41a0800c1d518800c240c3d59035420001035407003c0c0701d5000850101404034542840717030b0310002c15081c01070528075640c15940800004903844001054803200020030305104180f01405850f8030440d100c0c21f031605041c01c0158101ca544108845030742c200200101c5c007020180184076507850260000390400200b58419090030046001002c024015441c040c001281c4182d0120143c8500a005d02807900300320003041402515000d6078059a440581844049901d403060f0040c0440360707100303074a401c41e01c0204a11014484c0040c91016104070700074001c400c103540302c400340135507c900300c000f454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 592005224 1250 592003974 592004003
    0x50906250209010f0e091b040b010e060301080309090901110f0d0912031b020a0c1512180201110102180d060b150a0215060306010e04081c0603020103060b031003 71
    0x11100c4000090029000403540000148001d11207000200700c0e80b030701c903900c9401c4da41c0158481d00c0b00d03144c10711820740c550305658003e01e50a09610908054206042500506d41400700180d19038100368441d054030b91000401d0040381c140000c819400083d400c00a102502d100203421100780203190201c1c0c02040041007a1400006036040b0000c0c66030030902c41c03501c07a0f858000003030141c0740c2111030304c12480c902101402c00314030000384d5a04181c0c01c0a015000c59041c0a104140d14a59001550411001065241c070344e0b1400d12410802c00c1e8407107110103580080384005030460141c004603c40591050200c1c02c074642d205905030941000854100c000f0102c149400c41c020603400302601e070084c0040d00340c0a590600c8000501041031150229071440102c200c84026004d8110390035901900000e004103c40c1d41f0307012040d07130840c2c898068a41403074150955441078092080c0303044000c0d130b120748080056582600c5081c02514010b0301c418a545002505d003407043e0000d11000300100703c114180c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 592006474 1250 592005224 592005277
    0x1e09030406030225120e12060a05060111060a0c090f030305030105010309060e0d03061410172212030c110d0e0f04090803041104020301030201142b0905010b01050906 73
    0x84812844a24041100d8140e17050205070f40344407801110208081c1242131280f4a01240310030798040104008080c0c51ba5091005005050080d00c0d190500c410b41000d102190800d00125101710748540000030740200c1c10304000c0c07158016503c40c041210048009101003540907088034190390007801c0100b1352095614140e40207040003e002d1096020705c2101c44406681070b0048002c81e90300008940000b6864801c001c458241ca03240400894140e251184c0440440004140d205455580f0b4240b103031300c035840744249a0034100044030900133119aa18402e0307050301c10340070951840e140c5884004d5180318007a640310f101d83c030f80030140644611041c2407980c6107406410424406041403040c8405071408648680003600d00f11034075420303981d002a040c1041e01c01d59040b04e4059440e454891641c0440d01141d500003140c10b0400800950051400c41c040e42d0005012070440c1c00018240c0002d0808508481c01080d102d410090200304000d09a920242501c811103c208540710040540c500d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 592007724 1250 592006474 592006507
    0xa0b041a01030b0709060e010c110d05032109030a0914040f15080708030702010c080f0d0612020906100e0103020c03220305070b070803011a070213051e090304060302 73
    0x94603240c206a040040304102010710703003d0284c001034960010300c5440319001d84d485041916032a000940c41001d42d0049403180785100c03000103014086255a14198481c070b0300310b5104211014058115602e8114200ea5203010181e0100e280800303503090150741c02000700350103000d100e803803402103803144210b0f4141d4075580301080c00d041e0b0301c00800030315100460319441401248075400749400307004400174590340301101b156541c50b8141d584040b0700034503594051064001c2c03c004a40104c0c01d1002070000542403061001a003545800e050140304503204008806600a1030a0300558032050030420140e0016405403c40c002401c02685a0038031903010352850248070b540c080c0d241a41290403152030410413019007902d00413419510403548420741c80300e00e8071035440001c1840400b003004100e40a007820641030396a084001d110b182c4180b540009640365840f24044000725916402d0220b00071506100160b80718200003a91200d00d0080c841d191680100d2040c10245500021b803811074054484 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 592008974 1250 592007724 592007753
    0x405060f0a0b040501060e03070515030c0307050c0106080a020a0b1e03060105091c0b0f0f04020f011e18080d020a060e12030a020a0228030e130e0f0606120a0b04 71
    0x10f004000035a5101d000408000307007009194000e01a60402040605000c1401603005078009480791540c1c03520745400400d5030000b040d90040102c1440103623a6040c0030300401c0024402e9100501d0340070040d0041000715129680a60002802003080b42032405158005002e000f5040300308640300c0d5100d10040c3c61920500300c0301c583c055850b0f42d00c4040010b1078041e605031180210b1600200c0d56503140744100c0e82c2c000340da00030076010103800000c005140200d0713103c0c507400c010f01d03090750164100440c01810240c41c84021011400340400307a84410f441282c070200134240704000303000109403503070080d45a149030b06c0702030f124030f4071004002161001041007140b403015504a842e668982480054025042016503034014000c828100d540c1580785403031003801400050008104400965080d41c03084c00c01000d01c0c0d00700114503010b514048852144d80e145000f1180604100c440d0b410a083c104180108920321444044404600001d800240100441c0d40243c13016496100e500f4207030103004030300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 592010224 1250 592008974 592008979
    0x80c0d0906090b0907030c03080918010e0714190806030f03030403051305090c040905070e190905060612040b0403090e070905120f121c06080c090a050405060f0a0b 72
    0x204020401c0201e92001101d9801848084881d8440307201d019140c3e0309510002d466003003101000d1001c100540002c0280700001041781c40c058650028250451b04260300428110f42600d00b0400e0b425008451501c91505461300c20b440c102859402c040d215800e084841c00b0403640c04000384860300d04011414a409105048a84a140c01d00d03004109900c95480110444a65000094182010000c007402112007078001d605060500f90303904010310300200b0385020441d035802d2400302601d64286080460f499001110b40e20750428500006950010706014001c010821140015001d50740700d030750f041544019481c0c2140c45a080449003940d56030030440d04080034070140403900740c00c2001c040441d135050b90307c004c0085800c40d589458100e600b1484903c1d80200c440200b480c4c90420041640d0031043d46000007140e08020b81c0c034101c4030340750008a4036501c00c18017522a4604102c0040d484900420280507a281542d640ca465a02c080d04103204028140041032145445801102200310003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 592011474 1250 592010224 592010231
    0x1090507090e0304050409230d0c0809010215190608030c0601140303040306020d02031b07150b0a171e0d0c0308070302090613050109090b0105160212100614060415080c0d 75
    0x1814148070403021004201c2001c01b800118100d0030308c021408100400c0c164030b500b0b000c00d0550700d42d200207030321941e00c0394114010080e509080c0307201701e8900350041c03100f080f02c540010110a40141200d006400c034100982c03080c8851844000c0015086041d42c14010916500881c62404240f0b103000d5504010b000500201e41c2078030b10042e61f800b0b10302c81c0040610080c2c1d4041c00061104c3d41d80b1500002a268081505080d0f4500d2a190000a25000040c1c003490320706942e03c82d14030240c0e01481141640d50005a2602c0151429020480c403501200f000340c02d00c041c9009001d01020101c0c0d44c0202031050840020718442c0c000d60546070b4420001d0f10160b550174402c030b00341d00c2044444c080e190104001740e6011030310602ca0303c20410701680c184c4a0302d1070008000018141060744950407a070000c0080c0d00c0b0301074041c090000020b00d41203600c01050362824000d25891507110b0310384807409002c060008120b4000d203600c0411a80316141880016600d441c0b11241586c810100c118000b2800d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 592012724 1250 592011474 592011491
    0xa020d0311070b130e040302030702150d18060b010305060913060605060406111c0c0b09030408011404110108070f030e010b040e100609140601110102160f031101090507090e03040504 80
    0x7203d02c000c2c520062110b0310000019114071401c030802205031000b4005900910a010050501c00200112181c00d0000d01b400c0400704c7c04c80c02e0540701400700d03c000c0c6003c46899103003000600d02030300c02c4640302404c0a0005181c603401151400d00000d261050f100075420402d01840203507400171028001c041c1250b561192a0507002e01240700043d80f200d205d00c0355030003400562441c03004401100b100c0e6aa00c0c5e4035560740da1100325002c007010f07000c102c10380030412000802620034030035000440040e0511000c0340c601810801d45850500c5039a506000b680030400c20f500380d0004400e14075046c90305001402d02c82041d030290052100342c1006401514100306100700c2040040c440016100100d020310529403102801015561040001d02c2d4030006030703000c10059801111280786803480d0800060801d6070f404d03220301745031500ea4425504080301da141d83d8140b41e440b820302c40c0380089803002030080c03000e65036810360f0718015445540f4400342e82d10100c054041c0180100c50040200400c11b200581 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 592013974 1250 592012724 592012739
    0x60b030103050f061009090812042103050106020307020409110d0503180103060308092419081e011a040509090705040b10020d0c150203070207090c0c050a020d031107 73
    0x9000307000550b901d00c41c43c0c1803220101400600311788105805440c800ca003600d051641c902070004050210307541c3c90184901d40c060a06414090f21590040041407020704080b00c0040400031000318040401d801d100061007810340020880301d01550580c0c0c001500842d6051405119840d00c8019501c42090500f050070700c0301c0000a00322070f0b42c421070714007540920710006601300e9100d8800100b03400014040700c13a6a01c7c10a035100020304503a46007940c1d02a120b04840b000d98090000c160509403080003200c0e101d9400b40803071f035100324000d0540046842c0e0741090f2452840c14411034030b16140300c40140d00758400010660b0f0052034003810a40d8141880440c0381e44402650043c680a6450100d0040c0c2070b1400380f10800c184060b58014010702070820008035202c20700e0f40d90a440c40c4a000c011080c0201481c0f0046201d00340c264042c4c68600d051005078001c0e201d086a56508011800306001d0124002040d600742c025811901c0310800c0805180684014401d48400c5c1c00e0390260400005048 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 592015224 1250 592013974 592013977
    0x70e0a061d0708132303130303020d090911070f03020721050c061606110403201e06041403100204030b010f0f141327020913020f0919060b 61
    0x7400c0903240c1c2100c0c0e6843c440845000036503408060281715940304440f207499140303401c040c2c00b100b4140c2541d1810b5030b541ca03c04803501c001d03407003200181e00081c2d4440c0c50381d80c0304621002600c5159024000d1360010b4150501c04e00610101a00701c4e010005c50604250007001182c00810003c80020100da16200da0760703040b0380c000c207015280342c001c41c3c450018078500102140d10b28030400140b40710b1404192030340e800074000440c9140e41d14004000200100e030258544140d804000c040c079814006860b0140410b411324085440c0001100c2003001041b55206402cee2800d072101c1794641c10440d04000d0000f803501c000c3d8000364440510006010051154441025058440c0760401c06a16a99918001b4483c000e5118100140c40c140604a0551070040c1c20300122182012000c9860304542d10300071440c8081c040402c0b200f441040c840d40440c2812074429a01440540e0080d4000410307402140100c1d00c0c82501c3d5105c0c0e40f540e00000d110342c1500f80c4045099140c440d08014294a402100303405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 592016474 1250 592015224 592015231
    0x30b01020a15140f04030813031809020307020f0c060d0b060405091005030708060c0405100e1005040501120b030a06020313050616080a02090a14011419090f08070e0a061d 75
    0x90007094002070781340b600084c60180510380c5640e44c0016903031021424441d92054280131801c200302e040f120780c49c20981080301e2000d0400e105c00181c1c2d03811b00040281c81c1036107070b8030031107000e0b0020000302042c4d039241000d03262101485c0c200031840265080028046110f550001030f405200c02043c001144040700a980c151603068084074a116240c040180d6140c604480d0201c01d1003041000b8016402c00c0804456400041d0900701c60001207500010405064081c041d0001000800c1c108800d40e801400c10b08072002a030400c0004026480100f9122a0740c1e00e03001d000542c000000c0b415144000300c00110140d04070b02540c1041c144041c0150b40046001c3d00707500020102c0010464018951007160202c8000401c4446554503280d10b00b03000c2100c40001a042c4880700c400e141a00807158010a60011284418100c4000046015185203a550402c0748450582c02090010300700000740403059403c0000c15085564a9400d01b1015001941080d243c500c401c0d1240250018501c4280d0f00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 592017724 1250 592016474 592016501
    0x30d050d0b060408010e010605030a0c15121b080705040f03060e1c0807020c120c01031e020c060405060a060b0f13030c0602010c09080105090d0e0402090a1205160501050703030b01020a15 82
    0x8c1c960f510760406558028030040030f40240789040c420061440c21040304c0f2410803890a000506070b030703010510b001f1100065855040c0c0103110740c441100c141d00c140d4481d0700c6010341c1009402c00e801c2c5400d00c44a010280030007010555101503050b040b0318100002c0c443c5e01070200a045101c0d0001c4001041c0d120b0a45040300903105070800c5214501d00014045040c032500002040f000e020080110050150540b00007404c42c1900020092111940000d0401481c0d01d0020314440c100303485c00910b400750041455110500e07240003132229181140c00c0380c00c2500c511200c0c0d5201d050205c814055202180d000811000c0942000111142c040d0003010b41c985031a11241e28413941d8060444c242c030000c485041d02d9810203119050b131140a40c054646460001c0d200500b041e5224011620000540d000310060340c10300c02c4510100902004882c642001d004295401e0a2504001800c24040c009005003415251040c103c1240d1080208190040c3c001c1010648014951212001032101e54080d04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 592018974 1250 592017724 592017731
    0xc081f060909030c320a0c080309030c092e080609010c0f0f1403040b0108120702030d21050a020c0d1805090c12010902090a1202030d050d0b060408010e01 68
    0x504004a4403a02d0041c54054a500103914000d5417600000000000b54110318007000990f00c0e201108941001c0f04103901900510818481c2c1c109a00d940384254803850080e030042090359050341707010480c64030f03000059a03a06181d84828140310500341244e0401440070240100b42c421010491010f00c088072001d400391200d60315507104042c2603501d0383c0390500101c0d50254040c83d2007072040800b880070810f68540040c0c81540f40f45140d00e00e5005960964483c1c82900c0103000303000d0188180072681c840c001201d407400c02680d012a440c0c011a64030801409000c3c0f0100813040c40130b0189500e107108800c0104480e107401200c03000290001c1c00290001c1c070401038114400b81c001c0c4588011124004500140146803004000100c1e00084c14895021018410469850101030005018220320750b8056114441541800822280c0b0350046049000c14840d40d40581c4000c42c152130b24000f60300d003990ba42c845800e040700c0079003002014280c000760005070001d041001948650602c1c03034140000d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 592020224 1250 592018974 592018979
    0x10204090c08061503090c060706391209050a0605070929091504180b09152e090504050717070e0301140103061a030718090c081f06 58
    0x1102c1070681103650a803c4844010b040c0d01080400028540c03011803082100c3c4680503e402040003900b210300e00301c54040d11030003425102070100a0000310922822a551040c0303ca842e0f143e2100d000c07640b08041030140c10722821503405c0b619040f810040e50031004889468807141f43c40c01c024402140c907040000c3d0300b00c5d80030030078010780c14184a41140d1100580714040803200744400329032000742483c2d440700c040201440a01c4002c00544020848600300c1c0c419004010886829030f00c101e00828410300300d400800c030f400c45180122082c5850300795201c9607850095501c03031030320008882504020354042c100c46a0b9a135404140314065032402e0740d041c400c0d5200e460050b1201541c40c0ca803d1000c10205000981003403040c40d0031341d40d20304010000f00351203200031141c6000703040c280c1050315015113481103085405c1d00021000700c00c48049c0c0041440e0351400c42454150899102c02c00c1c070460700c600d17030601404011031000b0007400c11b20003640d495442c0030410680408905068024980c2401e900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 592021474 1250 592020224 592020227
    0xc0a080a11030615120a050a03050406020f03090d0807030e12010c2d05030c0403060516180605180f090c09091018020c011d0f0c0f0a05040c0207030f05010204090c 72
    0x7450160714000c0307064540054000801805c4508007007080304500c41c821200f00460010002046940d0207501c6942e0349038145500281440c01000d041405544100203030941d6865103102c540b4001e030028821074481c101c600c1d00319415850749442951040e001c440b481e038501d2066100501c07050241d1680d00c0404201c20039947c402c000d0340541c41d250307802c0420348608076002d00f00a591088400c0b12080c0760135104c3c0e0359001220000c1ea400444088a540741004280c0c000c1301155019803007a2000c000d451a010b00140a841507841201200340108240062512210f001c1e2350241001040340c900c0f854a480030320031035000150a030344500313200000306d0381c860806601c1405658950074411680b81003441d00401a42c4500c405c400159030b603414580c8031202040d801c425558081010341881702c80a95082d140c03d50f05030b8220f101c1c0603600b41030551075413554150790880d0002d440100d0b4554444c101a81085040e90010384102a054100410008103500034030039503482500411a52804010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 592022724 1250 592021474 592021483
    0x30a120e192103090b010608091f020702090903070c12200a03020405150909011107060e0c060a1e1724030703031805060a0f110c0a080a1103 62
    0x484005030740100c2402921a014100070495a60003070001e00e044034000715449440c10050350180001030b684400001c10009017030b030070300c3c01003441d460310405030b0900e103200c0381e255005464003c01401c04a140c005030b203810340d0155154190014904c010380e1400d8514640c40b0340c0103080848580e108000d0210b03c1740321001070404030680000d00742e018501c04209040c5050860ba503916401003803040001f00582c4c80d4002c45105d0001c18242d8a051841e40f4107000d803d81016001c120540d0500c0b03c2c0d5141a07280303809688d0f01d541c21110119031108006c410f02d042031525040d40e03812840002c3c03440d81003504a90314580320b0080300748060396101c031903004564802800d2080a80f0145a001142044000c660380710f00c540342c1003a012210040c0800040d1501d1403640c412400b01d90a0080d52042c3e082038021100204015500b0710f10b040c0420000a11551046000358284482c2600402d4010001c0055004111010f400d00407000e4441a0b45a03884220a02c110740400d200c005003a050b050104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 592023974 1250 592022724 592022741
    0x7120606080f012003060a0510050903011401060c170f131502030307080402120c030d020d08090a24020c030a031d16121a13050f030301180c031805030a12 68
    0x108a400b0f00130018900081d40040c2017240d10040b500b50105066540d0841800d4240050301e5090f583d1503c0814182500c01c601ca0f0054507140200040000381d0300f104000da4416442101010441f10119000140c0d000700701200070b07194804200c03145202e03513007170081c17090302c003070000342683d41814180490f0340344021584680003800742000710f001824880d0000000d60401e2050b104d499510f40042841c205c28026482c0044e8400d060340e2180b80c0d080200307160890035a4000d0040010a070311071414070002c1603101804060411b490b2101812035a065071410907240b03040e26070700c000018001b4058500125000501ca83c42c800c8810034000c0040c2d281c42c190041804500e00501d00040e80117812800708d401e58102460034503142070403d030001d115100b4031450004a40203141d50a00d00c0c0350010310403110030154810801800707500c400b0f040781e1040138944840400c40c445240e101310090f2145004c070031225898100c2043c1000781c04405002c80075001e64644540080e840ca0403001d81d030004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 592025224 1250 592023974 592024001
    0x115120510050d080d1509140105100509190b070311012f0d0f0f050c040303020a0204020322030804120203181314090a05190305031807120606080f01 66
    0x10502040700f400e00b0740c002c40d1518040c0d1030050602c101d4004080c15506007070b0540030801c00c5400d040c0407005d5244680c00d09a4122a04803440e503050001094807200b20300040c40034000c0106038440d4580d20042e10003096080b841c140341d08641e6a040c011020341110000700d0104100084c0840403240c14032400c6456405520810004019070f0000c42425400e0150400d2244c0d082042039030760440f602a28441e00303005480014140c18141c2000126080076045a6400c0c00c100b20801c00309034000b904801003070301240c006942e52100c44888100009041d10f500310140001e411900340764010039a00d1080e401020b8210180b2120102280c49224050101141501c1c1d900601c06a0034039105210700c01030344840c001402c141d00384800513004403c5850745629404001c0603000c0150921078100d0580c1c00054100d02c500c6d1340d41d00070b0081d0000803c0201c401c480308080030300c070302c00c20420800200f00201c035110041c1c20508040300903100c14060740949114480202618040500c51409518a00d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 592026474 1250 592025224 592025251
    0x7080301350a020103110c19020406080102040e041203090323040504060806090f06160c0809060f0a0f03110f28020309011706030706111f09061a060412060e030301151205 75
    0x45514014088e000307031016030b000360707a805001c6001c0c1804d10007400985403c0b0b0303020949161600c5c00400c0701092105c40c0080608007543e20001a0308080e070203982c1d842da6443e10080b40d1810107100030714059513010aa1180c14400c0020b0030403000703c1c00c01e0084203480c06540040200d0418255622010b03036282058100c40c0180c1d44a461103040b01c01074291050010a140158110006883d07400c0004212a5040001583c9180d290080d40b030001c15051400c0074845440c4044000303486000d4000312464090000903411409521414408002a0700340006020781c0c0003181e000b9602c1c3c01010b0628040f540b107a0400d0490341200e050307240310f071400600410910381003480c00c894940e078074452f040c55441201440070020b03007030b40c035502900413400d40000740b940c036607081c00019601400d1030080b00c024001300040641d10343e07000f1282a150a180c80444044041c9001c43c0248021600c018590202100100740e203801507114404243c150350f1200182c03c20781c8508012144142c410010027000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 592027724 1250 592026474 592026493
    0x30506130c0e130219020303100e0f190b102606030606120a080a050a09060f1e0909060e060f10020604022101140105040606020307080301350a020103110c 68
    0x2422900358031038254074a80581401a1528403807868174824111401681000c400c1011092840301894000d104610186c100c604000b50401c1100704081d00b800d00d85841c0c03880c006000f41381604140e206010240811000e0400c81c1e0000f000d0740c0b00d07032541ea0000c2000d45a080c05e40341020f000107018860060242020352219401c01803800d204095411041c0604136050001c01c810401819240e1816140c2c1941d0b09803881c401004102c1d1501300200780440599210105a84050701d0503028a500854440d80c185400b8180e0b0310f420182e0000c800d190402001185512030344481d2401024191032400001c005c102c204114000754083c6600141d01a04c0094058905504104040e1580748444002c0d170560302501070035070310702c54a440c0c2441c0040d0010401d07070a1034480d44000301101d01c095801c000c1c69035101101c501c818490302c10032903440403c0c0d20440a0b40f5801080c0c40c6407026554000b1075000c031603c0e8031980c00d1207083e070119250904800fa280c040c13004580080c0240d2014007074089 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 592028974 1250 592027724 592027729
    0x20102030d0902030c0a1403150c07031d041a0f240d090b0720160902090316030506070801060903080306060a0c060f062c191b030506130c0e 62
    0x540c2c480140c0c1e05104080c81107200d500c0c3d51241e50081c0160340d8042c0e4040d0a82c0050516021220b40c41c5134014403100200000802d840f0141d03100d0703503454039240c00000180501d0403000c003003846010343d11500d8211454051640e804001d0100f4505461f501910b8032401c00700300d56010450301da8218001010813101002c01c00d10003c02040c0d8007100c000511050580b44d9a160103c00c464550210328421000426440c0302060201d1101e1805c005280800c00c40a1a03411a034052280342e00e0b1980100300d013030455806201c54550841c3c100c004c4081903641f805c00503520f01e0305840c503c010442210002c140e0911908080090305d4000b20400d10f16145d5800384074440e03201070840b90811207026085000111240035403407042561100100e21742d418003003d588050307880d41107240c072107a4807101e0780c94054009003041c0c2c4c802c02c0f100740c2d4000c1140060280700606203515202481c0705040c5d80c0414400d070154003190140c2020b4440c0602110b10101d8a000c940c192417900d004146506040011803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 592030224 1250 592028974 592028981
    0x15080115020102041d0609151302180303030c070b011719150e010c110a02090703271a150a05090a020f0714010c022e110d050103030207050d020102030d 67
    0x5100c0c601c001480c180e514418419020822040402c000c258071003400340b6032500d9241107420044013503039100704540e01400101c42102c20b03c8140502d9401007894140e1480350b211320240d40e5005420303070f0356030324002c20400616440b1401c21038070034140b0400450b01f9840200207004404841e4018070241c500c46061100c075110815088400040c040e480038850300d024003980c00c0004441c000414803200d044c0001d400d00c0c1d185509441e03aa40120203c0c3e01590745c007414160418076905000409030a00340244071180b449801412100201d45074940820804010310300b0301d107081c42d00d0710f0300c59141d0020040440b031500c14196400641300100703200c2846c181001070b4105480510052074010301a04844464200c0740042d2109060102a207150710000e000e0308611411a101410200d04a40d8080030b54010042150002d10400028807603580b07800d5005441ea421a48642c54442105864400c043e00303003404202e005000d080d0000529062920700c6868080c1c1c160003550500f4030b62094507004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 592031474 1250 592030224 592030259
    0x19240504110f0714010c03021317010905030714190f1b05100306180504080403062304211d0d020406050409030804060e0706050403020d0204150b040f150801 69
    0x4030300801042c0090304540340104002c501c21080c80403070b120445202804c40e92613810b02020b00d0300400009280c4200560398030140ca40320101e8400140081c5401d500401070035600400600c00003802e08180308036001c040201110042c00c940000d200000c4a00c0600c01e030110051000821000c1040040c01845410044104034501d00194550f45e00c0024900f01d04d01c4103c01c08a41e42d80f909000c144160745102003051702a10081c4500c0c04c003541c0f44c0d4802d100e50310010b88956a03419400c0b100a0000b000d4084140f20b282d0001120b08080c2041349144017000301c601103105e0444030300300482c0e01425046950b1031510b8524202d6031400f50511500e441d12a404903880f07680c036840480c0d40d643d01e110340304038540241d40b8042070f490300e482c2c09000ca940501c5110069880f00d03408000d2075a100b0104c50603a40d0640b601c904103c41071020501030880106502c0d40749400c5c080200700ca04d00907000e00100c4080c8841c08500aa032419005100e0081c1c044807000507240340d00501c10008544505c240303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 592032724 1250 592031474 592031501
    0x5161805010f0b0f09031c180b0307020a02060307030207080d0b0405090c0f0d03050c0105010b040f0f030f0f02011130040515070c031a1024210519240504 68
    0x2c40d207110416403101d00c548442c7c1580403c070900c41042030420295002c801a00c041003196155081080c0e01030740d607802e0020001c4c820000000040d0045120390151104941c3c00200c160700d848a54a150020300500030389607002d64a031a00141d407031200080c0c034a4a44d800542041c0c001520041400500c01c0c8500c4150248801007011021682c000d115103802044130181454030380d824000c50015aa4056020310000912043d0600115045000d0408070903070003108842c0070041440140d80c0c080703441d01e07404240e000303458007103080340c0341c00141240e045628040721030307084442607022095000742c2c02030700e0300010700c88801040003040310000d224541c0518149010180d590b2345600c41000e02c403c01c89104500c0d64148401a2400d20550f0050503030000702122860310b000680b050b00003891a504100a81204d15034801e80044007000300c0c840c0103400c01e0003140340520680c14060b009407481100d140c80c100ca4040c0d00c000c02c5001c1012201c0c00c1003008166072410f82000003814525403005c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 592033974 1250 592032724 592032733
    0x806040209060f0d09110303040f0b1c0911011b0803040b1503060901060f05101e030605031002070b0a0e0d030507031d0c0108010f0b0a0c05161805010f0b0f0903 71
    0x1c1d00c00ca05000134180a0200440110b00100c5c645002c0c94440d101104680c0264410300041c045c041000c2085400d4952440607642c0700c801080c00b50300d00c20b03400c50001303580c107141c0061902841042a00094008003c0e00e502c4a80182265520303032401020001a0054105001040c000350300441c0c1a0f400502420b44144150031810000e8203280059031000300581d0748410411401403c02d244e14014101150b068005884a200c041c101203880b402c00180201c000090411040c02039010034050306020301112200d07040010740100940c4a00c0b0152817400281000a00c6c0c14498050074203d41ca03a0005400300010055050f806420301802c00b100b4161103800d00c0d0414555a22040c600351910f0000b1311404084100240c40d030032042e00300e1101008010001c0c440e41d8022400c0b140340c000d2a1802461007a194100207041c40d10050000d089a031711468002004421180700129060726181e0400c0b9030f903a070b40f0f0164650109031140e245404018062916503041d0a8050035074607001a0a49 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 592035224 1250 592033974 592033987
    0x3130b0711041b0e1009120f0804170c0307080d21050f06100c020108060105160605070203030108070f030b18010207060f0e010c021209060a0908011b030b0907080604020906 76
    0x10182d0301c12420580f0005195000c506000d41d100201030301c0100c058400d08281c0413000c0c001490800c0e40d0060740314442e13000386000d0404c1f51104a6030360540e006007401d500c03070f601c4404045c0b10a01400e0081c000d486601031220081c98040f40c250100e94040004006141d0314104c2900e001c10341088006200e21181c1001100200c61301034544113401c00044520300d8a011001c1004100400d00c6410800c4034655443c00140d0700308230081e40115003400c1c8240c5504043d02c00c5c0d1601c89200e0f0008084600340ba080c40005c40c0c00001440c1611440740c1901c1140d519008a0150303d4a1480041c20b2143e0990120781c103103003000c5200b403192007020009450691315442d6003041c0d54891941813215a43c1d19012010418207124444032414144042c0c400c40c40c01d8150b154946c002c0616051184900256506c44076010b00d82442c010b01c6c1c4803009000441c1c06016040c01140c2c01c0d0028804a400e00008400320700c2c01015080c814255a141c10103c0c0d00c4140a0100a40003000c00d141c0003c41003007003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 592036474 1250 592035224 592035229
    0x1005030c061210170718200c010e07030b010e09030a09090903090e150a0801230907121401050c03090615120a0827090a0b010c0c06110105060303130b0711 68
    0x4034440da84d8010014200320f0f02d4421100b00e50304206080780c4100f807900c100214484401c411501c000c10b20f55400980b100d000c100601e0041400c511081850f2080504c00020004410038071412605000c035a40c400d80d8603c02400d40702e215102c2c41030000746d0703010020b000c00c0700c0305c0d8007410303940d8020b00d408010303241c54948881c1d00c1c44040d10411b0301409206880078079807a080c02c080001d400000003d01100008881035035036a04200600310b066032420340010f0707806908114500c0140008049400610310380e041000406801141036140e55003003c00042c990180c42040328000c020000c000c00460b40e4881b100e11004100c414030982c0251058030010340144100240010b00380102052950b4040c4004008007032800f0030b0603111000b07180a8030255699617100305950010388054080340080d41500100c0b2001e801c100d005220042002001c40e00b10740c001000104109104000c10450702c445040641c0c90142005984032510840d90900004521001501c1c030305100300000621640070400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 592037724 1250 592036474 592036499
    0x70209071b0b0405100501080d0504090926030403030b04050105100f030e030c160909111302040503151807082104090e030a090b0403080712120905061005030c061210 73
    0x78251343c240c1c030009008140d8821807003030710f0040290600800c08100320741d17006000742c0140d1041601d01c80e510000740041c000c3c0e000c0448e801b005043e11400b5070b00e051410b00262a042614107400291800d00c010610f410140301c1c00303060f240b0042010300d000418000c100c6000d00017201050401d51640301c501c005007001c1016140c400c0300320016088601c0080203d0841311400c0d070220100c0e5040c44500310204400001080a9143c103590390009503034510a100064496070340120380503c01d9000c414814030203242c1090040340030341c0003160f2480c29800c8543e60317000140502c603030b031340c04c8290402c4141155112401c544c0140712002810b05a03101003c20071911186501441034000007446003029030701c458600054000e00b03040034100740c20740d2626801d41c001d0080c020262690f0050300c105250080715542c8014641d4a000d00840d022494000c0e12040140c40c102d044a540a0000c180341c40c000c51311902464010340124100070040200d0042404041c00c194052a101c00000c510343d0b00c21003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 592038974 1250 592037724 592037731
    0x40812090c031605150310150203041701020a080a050708280617010e03040b040506130e040f12020109020f090402040905060c031005010318060b030c04090b1b070209071b0b 76
    0x200c04001803505040c00010100c92070150205c000402c20480c04980c0c152000f000d48050034a0045001c0c021201031b03143d0b100d2508004800c2c1040f03081034022a00540003002c24280d10750342c4248603202c14101000751442650414042001c08001a4660240030400300c0300071100148200c2e0b448511403054216199038020035100c02068283c43d003488801d02400d81e02040003402146454070788104400d55006a00903039100d11400519511342108540c1001c0181c07021803407074426030920380f51980307031100303024000c03503020034040005c207a07150046c45081c0240e07401038050b000c1f034014581000154000140200d03132165aa00c51040400c0701004182e00c01c0d005a0003050f9603042555a9109450072035114034101400c000740302004d0060f5021241c0b007581e01c0080468455402000603040c28070030603a00343c210f4075000034001801040c0a01c6070281c3c0881da00c6601214a1051601251082076006504000c1032030118905c680b060504a000c10803c4416440019066450000d02e11054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 592040224 1250 592038974 592039003
    0xd150e01022a06010e04030c140a0c0501050a090605250f0b0609130f0c080d0f080901050c04030b04080415030c0e190b0a020c0411030103030215040812090c03 70
    0x8214a490b401c100005410320540c1001c108a14480d012089542d039101402070502108008000c03c0415005904403100350754070825801d11041c208140c190b5559035040f081d100900e02a02c00203031075005004613850b68541d80e90b555216030500c541640e19921405011900c2009800c6194041c500d03094080360b10361240c1044406107505042c022a101006001c0d18403c25120701403240602880142130501c5a01c90445180c10003d4184003111041550082c1c4076801102034028940f94800e14600780c0c01c4090301d41410300c0c0c941c044000d089403c00c03076a00c00350900802040c0f022940005102c0c0e80144102d081c107140685503a600c50450304801c4000c40865228041d4034112500940285840c1038295440c543c0d40003021981c400c405030030322031001138200008810b03c09920230b11044583c00d101920501c0036094244048086520911047d801400b4149950384040c22030703004e09026980100001d07080c1240c01908004845010713141d49568841e10010384d0050301d0034045204c110100c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 592041474 1250 592040224 592040227
    0x6060b1b0105010b0403200a080c190f09090f060c05070606050d0203060c0307020a0b01120606050d0f02010e210c09090129010e030609071404020c0a020d150e0102 72
    0x9428103140c8050441505030580d04002c0144040302d000815201140d8000410000c00c02043d0601d40c9034103400648a50084610080030804280c0000c03140c01c1d094040d00d1406900790307024014000002e290164005401d91407004004588450b003100803414041e810131800e900c0a07960700c6044606040d40040032500c0030a01030f041c45a54416003004102c2a990030b1015561a0b00094036148014402e50310400c0200c04104954800c01541c81c041d503004002000558403640321590f09400494104c8401741003201c007049a050581941030456804a0452096a040d82c019250907441c0584e450b04001203841c112426031126811101507031218002e89180c02c000000e2011100c0c0052035400035038180300b072000c080301d600b100190320006400e52100100b9010130040711941403540c50281c1c10700c42d84041c06202d8a01203a55070446800c034116480140103001400240d0064614501d21508000c480758054240b000c07902c81181d120320312451607420a00c40303003c102d07181c407078900615079030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 592042724 1250 592041474 592041487
    0x6012a08070327080c151615020c0303040c0603060e07031128030e071a030c041a1201143708010209130902221806091101170a0b0d06060b 61
    0x60a12107603c0050003074030150318401c0744210101b0540b10b41c0180070241c0300110003110501c0604280c020280000e000c2c10f41d41c9403500110550749800540302511a513804200000750306001e40b148034210380144610400643d40e86005800900b015565203003100c10801c0f4554604034460031071b00300903c50401e0a210040b102200504868945540390305903845200709010b1078460f040b04020245a16001503079a0345c80e911865182d000350741c05070700061008085a071412103084041c21100e500302000f500f90303aa9581480407a640c401006a40000f20f22511001d44240c0c1207600c1e04101c0b040110501680441a0503034249a5950140d9596580400d58038034904c1c00032151400800c21034428442c00e01150001802c0742280c1c403560b8180042201040000d40890f08611000c8a9805d0850385a10301410620f014081e007610490b80074012400301c0500d50f00410300c60850700c0c0e00403180e00796541e881c0d508500034020101c1c1258001d4800304141c0001d0494054031010b8407094a13032589982 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 592043974 1250 592042724 592042739
    0xc0121090b0f01091d0309120a050102030703050103021c080702010e010c0c0b1c020c1005060a0b0c06070305060916030c1b0c0f050604030302100b060405130506012a08070327 77
    0x2520b900d0901c05485ea00c40d60440c4040c400000d503010910112528a8500c3e10094044c0c90150007500044c0194004010000342070f805600c401d04032402595502180041c0342c441071107035406900001c013050004d10940340594402c590084031500103040200c035000c41d9480b031408500a56100d000002800a105044184802c043c0340c100c2c10741a00641c108514580c1c96915000b140c1e00c00b43ca96551400003500325680d20800600a00355038100310f40c1d603045500826102c060490341007000c00d0070b00000c01c40318203100014074451900d401c03402c07034800c005d000103c0180c010708500600300a080c55141c000a80c01d18080c00c0c1c490720075483c2c941d0304c0307260804940e0724500c6a07100500c03441d020b01003080429008182c044404440f0117002810b070781e06200103072440c041e0340c1100d038220301d0080b442d0110341080c5c2e0110b4061482600c804004130440506490f40c02c644184010310010880c510000280861020345a0740d403103400c0030395040c903000041c0c5240041c540003100507110325020820880 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 592045224 1250 592043974 592043981
    0x111804020f041505040c1806030204150c02010c021306151d0603010e011415073509060f0f032502011b3903030e0c0121090b0f0109 58
    0x1805950501c0502c0f095020b22903200d446118090003507131580c0d110b0341240d10a05051107400c0b00110303c0d074041030b144d4800800940007806403c040e1007105654070304c514010701d09408810750581d01c10145c080f6681c01d101c0800001c0b44401f200b10b807500b20108040061224449459200b40c0e21040c0c2211000140380d000f42c00e800e81b2501403641000184281c0c50a014054107441280386104641c10280011507030700500d21400d9641e80d0404240081000010b601c0001d60901103c0120759880f00d00c00b5a07007140412800031000c165003005513400c681000c1c00030f0000d12124103103480c204248118650000d9000301d84180b424064280c408480a100f10641c07100012213100070411510800d081104c0080603000c588103110b80b46003460f240140481c1070994404108914030300451390300c083c021a020400d0421008641030410203840c5050025064100b00d405946100301900d8841d02411400c00c00511410041d4403607c1c01c9000c10b000344103881c010010984100303d00e40c5490308038000c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 592046474 1250 592045224 592045249
    0xd060f0b090723090306070c0f020303030a050a0b19120302101a0a060302070f200d0b061c11010c1704080d0e060a020604320307020a1a07060911180402 67
    0xb050a020188040c3c45c00a1800e60082d890f041c880340d40b074028285007c50607007404009505100001c02c0106001d000d8101e00d0140380c08400500011581c0d90800503000d408400502c04045002020014900118118400f01d030182c016202e10380143c01da104152060380340900340d28020318512010900b0031111041c020300c124a41141400415541d60100000f90310014004041018143c089146a1002c0201ca08d10041040d481d05c00c0900d4611009401154524410200c9942041c1411004042106130340c5d444501c1440c07102c2e6100041d40d1040d520b00042c1c1d20b812203020103208a4010000920140505100814001c040c0c4030009208008261109000d4501404540d0b40c032900000e4041d00250b009130a00c02e0b0f07410030116004481d11020f02c2e6480002d803c0341c0e09142040110040480030f00946aa40c030321520b94000c103098480203040030800100401440e0b012483c0e40d800300030682d10524140709958072140000d030391b0004080740095814054001e210451601d00000c40c00d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 592047724 1250 592046474 592046537
    0xb0708070b0c03010b09040c0519091412070e0a021e1903020c1b15070c03020a0b0a020304120203070527090c010e0d0602040e1e0f060d060f0b0907 65
    0xe10b44c104005c01c5858066016914051a215031842e41000e01a20a89101400e22103500d05140400b078001040380046200344100c0318501b401c0340100d41881c50102d03103c4562007000706811071420031500f1103504000c101284080e400d02000d07407124580000c0108403200901150388606140b030f9200c200c3c01d54801c40780e003418810408204070b05004140d4940c5c54941d505502101580840401c083c0140e911344540c200c0800a14070081050075074003901503034001d40324200d01645030000a0058400c400e80c000160344140401c21420100142c5115858800703004d8850451755100031a400c0d000300e000d4011600340d0301c1c1d84500c2c0c2442e200d8407540d2240d88280100920b8550000103811081142c041902a60103003030340301c003800306540440300100180c2c3c448191b903103041103289242800c202c0801413184960030229a140086501541c001d5000030a00341b43d43c180c540c4e40a00520345601010761907a140c0a25000e5561a96078191141b1b4003602c9041c07980300c14249000d00442043e603401c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 592048974 1250 592047724 592047727
    0xb1e130311011a01050313060e03072913080c0111040806150109061b0203070e0403020d03050906060609040e0607080a11041503110c03160311010c0f180b0708070b0c 73
    0x203400c1d024003691603d10b09000e08095a82e500c43d080c500072581c61000000d05170a00b4401c1440800038000002d1450038098045484002e1070342c45545425420b0703d44260548e40881c003c12019075404816200c071500c240728a40c540300011800d40d080d54001001011025070116041120b0f1030107001d225440b90f80c02c1c130361691460341140081c2142c421401032100308000d8540000d0381c18444090844e900b03030011b00b02c900da1a91044448a81841221b084005025884110001c1c5019000300d41c000c26600c07003d000c065403110f050040c0360b040301082541c40b80d26561402082c9009010040c081c0c080c0d50745449032850090b83e504e041c0e40c0440c56001021500300010000b6031f14002c40505071541c54900880c18600d18100c0c4111805803850900702f501000802d801035810103510305c60b000b8840d46079640d0415a080e2160b00702d41d00c180968002c01c02d049498809140701d8440d8040b030041d41654460001d840e110103804070380250034101d41f039400c001068414488061203075a0301c6106060340a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 592050224 1250 592048974 592048991
    0x515040c0b270f030106081b0901270219020f071a030a150f0b09010306150206391c0501080d14071505040c0605090d0b1e13031101 58
    0x1880d0002e29015a00035a00c84100d14602907803000b0141202c0180100280103082d01c0b02c0b5a90380364030b284030401c03005480d124040c02ca00d08104200504031284c941340c18480c0d00d9400840c03804e000441d02a0700c8007036820404200c1d0704040550309480452684d004110360381e00c01c56041d00d0b100039501b00c07524401021840c001580c048104803540120781031701c007040f03140404c0d900d42d5660381160002c1d0031075001c420f000b058a41d070500181a0004003640e0034002039075524442030718801070118010041c1c001500185d07441c085980b2940b51030365142c0383e020314410b2001c01d10000104200b1942c0000c0b400040c40c00e0810b01103003820542c10700d607090401c07680d450f2000182d41c1720300f44041e04043c050000000e02c0d5180105095070241a0443c600c640002c40c0c860f02c02c5c0c020401140d0884440740d050901188480c8108251007030100d016002c0941c0d091645c4401d0780c5c2200081c00150030340010341c010743c060042d1030141030096241700c41c15044800e2915025000000340c02c0e2060340c580c50180300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 592051474 1250 592050224 592050247
    0x3060a080102180f0607020a2403020403030e10180f08010b060406021c020f030d0504060e01050c03060103020904062102090f071b0809030a03020d09120f0602160515040c0b 76
    0x50009018101c40003c0e030401c00c2030201e0103034010030764060750141043c0f0001401030111020700441e041121011080c40c149c0e0b80040d403ca02550001034002003c6a40011003407c104956550303d141a0400305810346615074030380c0064407503412011701c3e208028020400c04c41d0902074000601e070100c0d6090304040c14180002c1d91902400000c4001e0784c50400c48400c114000e00070200d600b83da0700b003500d586041c01070261001d07000588048544502d0089020710013181840307058007805a0362405031942d11408011406500215001940160307928000140004200108100440c0148000740c48070308600422142000090038400501c4001007040008c5502c08402004130414241c50b01107204203040c82060b50041580140d018032500c00c0c03000a040d00060a01c101c030754a0354922511075151409600e6044460b603005000d083d117007407600c2c0004c42d160084d141d1016844c4c0f0300000c001c00d40d11100e02d8014035480c0d05100504040a00051040314001c58002d0300000491074640f000d040103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 592052724 1250 592051474 592051507
    0x6180b03070806011404030b010e090f150a060806190b0a060c0215070b100905070f02120a03090804140a2709170f040f050103110a180e01030803060a080102 69
    0x1c500410024800280803680101c031442c0c2c4480000035015191a10307498880d5440100b8003d64404d6030180000031348001000505842d041548070160002100c00da078299000034010b41040c40c1a5118a000b00d0007400810880d840313030100103100700000d004210040212255001e0082c001d00714404240314094100e01e0b4440450b038181c603a0464000f50128251f40c43c003803503000902c5148500140082d4191a0711090103885007030100b00410344440a003580c50000840d031010150b00a0166202500d06070409091003d41c3c608000c9200c801e907a0706c400c0700703500c503411181911106402103042c07410141c000d00045e0208503031100481c0c2c40346080c0f041d003130368070900e04040503210345664040007130356a1001851803001c802c9549904040271a680280c200340507243c9510545c0c4400a5998800c0c040d054003a043d403456681350001d01d0341f0868542580405c0c924803810055000102c000001c80c070075000310f00903551907890382003d20400400c04855448a00c4036801030100c00849800d03241c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 592053974 1250 592052724 592052731
    0xd061b0c0309060e0a030209040f02030f0601060c030c05070801020a261512010e0304060e0405060a0e060105070602090a150206060a0b030a0216140309031603050a03030b0f150406180b03 82
    0x4144c0c4851005900003078a000098000941210080e8244803c110300d61701041c80f082e2084003030351000c0e500c0c0034659544210910410303000540090640703010038000c0f180e031a0010b0083c002e46141a86038501103007a40d210740f03040e20000303140051b03480000030366032800076444550018049050900000701c24910304c08500c0f052281b01c800c0808603611600758040c49151945a0603a612255650f1003e456a044885424041c2d0b0901001480600d4900003090560f01c6968002159854203001120141c010450446000c1c0c0d0030403e281440e90360140c3c880007040c417511042a0409400c40003801c00c0e0006d400d880c02000d006d203091084107a1903080d80e51003026a42c00580b40e4802c55141e07a0302c1101d00e00040c0041c0e60f00b40d4102081c8a0100080c070120b1070070b03011244a21118072400100c0503003440080c089070084408500064800e42100c490524000d219036046000440018035210519401c090050400901080f615410600180d01c0000c50408041c0300362800004a403d480000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 592055224 1250 592053974 592053977
    0x180305150a02090301060e0a0e191b12050706030e030a120e010b1302071101020a0b07120902130f11090312030403051606060305060610050a0f09050d061b0c030906 72
    0x4001114400705906a07551200024000d000680c1d0f185000d030030380402625104480c509028140034451000207125030029042e81101d010106c5a0b180d88a81207885d00003c500c3c0701d22210700055007400300548801d000d002d030010b010b18a01e04000902140c3c1c1c046841e05207030f0010b002d0007a21a410420492422005c2d500100b03c00a610b1006801071443c2480c46a10500c3c49610941d0903415038040e0400522910a182c01c204001d00103a1792007020880003056002e16000040d04c40d4030510610000144400b000300c2c42503a181d00060303480f0380801e410358100f03036222001c01080580b4000c50728106410180c0306c0c9020003c60100e52108450311035404080d100001280406100d00c04a942e203440511203d00700c1034191414038058581032109841c140f15030300c0403801603d00841c0003000307100c01c2e4946615140d80240e003552041d0b9845030b20b40c1400300c202c10000740ca0b25045c42c0010503502c511800104011090700e2a019607450558100c108954900c04c100001d800081e06401d44916 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 592056474 1250 592055224 592055263
    0xa0e2e0e100f0c171b07140a0f1e03080c03070b150f040e0f0a05160b0a0c230618010501140901061b05071805180712020d120f180305 59
    0x4800204550340718000203030703103030b550311124141d141d00c5c0102c0c01c101030701d841d08160b0391030010100800c00710075458043c4003500c400040c020020a8003080c0381c0780400da038214101340c40340c0d44c81d207884c10150024038a480650300001600030801c0681c44203154019440c040ca030707806084000210b984009a2000540103d0b921300c88002c14100070030504011624000845001400c1d6143c010340b20b040024544a60303004503080030503c60901e60035140d0242842d030b54020070306065154140d00a00040500d078800740494500c070002001400b01510825034600000c100014005000703007144e1059000d075415501040c9550740650712180402e044807c145000c1400102d14021001c001001c454002c10621402400007594091116140d49040100380100040c0d69143c81c40f114402c607810b06280903400259062181f8079a0b030f000000310900103401c00c4c0c1442100c0d6074034281400d0001c2030300c011407498452481201d0384851020314404d03903440980c00140c516991269504910003001d220b9025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 592057724 1250 592056474 592056503
    0x4060b041202060403140f07060e011e0e13051006031e020c0708030a031401080604020d060519060e01051f0c0b04081911120a0e2e0e100f0c 62
    0x898000303640c00380d6084106d0912041c4030401c1035540c0c0540301c5a02095008082c03000803198003503240c040c0342e0b0034180c450100c0c1d24045d5011070a0034800001140900003020464030a540720300805040541903400c00040b2402c1c540d4041c0d400b1502e5a00c01c0d02003500340a0003182e07143c49400d801c01c407c42e20030030140c0ca6111090055050040303641003180144400b1030041d21840c1d058001c0403031100301140d000101d90f221910242c8074002110302071f4204400d2111000044c44e9a485568003564250b203a6483d110014242c0003a2140f941c006040c0c0c0340e55038014080c0d8a0300c1c0406a50345080480241c20708034012601400d403440c6140b024003100c5010b80010284840740d4110b55103803168402c0c1e100344200e001d00182050f11134401b01000c40c0710308800482541004400c860f61444507881b000e482601c6030041101e100d03141c6404400650701c03888124000c0d244600041021803941d1a4856103460800900540200c00d581990801101d0400b2840441c1c004400001164003c14511310048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 592058974 1250 592057724 592057729
    0xa03051011160803101406031b04050d140c01030209131a090412030c0f09230a0e040312020403081206031e1501080a0b13060e010207030f0e04060b041202 68
    0x28800700c142c01800c4102101c0100003050f0000d6101341e440c501003074561911a60112111240308440d1358100c1010401300c3d03c03542003051000190f0304030b141070728035054403000400e80d100c204040448400d410100b02804c101e40c141b109008290f001c0c0707411070070410500700182e0f1407100341106156256507100002d40401420400340c00e00b135000352402606091501d002c06024072a189a04002031400d04034a010398440c00720544050816618220010704280400d410580d45a110002c4510149a0441540c0304c2110303841c000c1032111150b8085240a06011f001803011701002203d52f03204010501c00034548006a840c14039948520807001e6440700302007803400070a49040700304032400311490583c48400094002021140d03980000c4580d84e40c20780c4a50314a04100d00400e1810400001144122584200c590444c010000426282c82c25032919007282e01c201d2003580003c80800c1e407154215000b081718a03100134151020021180b821034a4071041c004c50017900c0b1168107101a207010356 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 592060224 1250 592058974 592058977
    0xe062a0426010c080601021e0a21021204081f140a05190e10150e15090601050901020a12142107020f0d0806011e08150a03051011 57
    0x411840d01e0116002904008003104a103400c0a140c00941c00c0164860720f152180305130500400044c1c0003801c15504440d480055914043c2d240d600900c41c24244030007040d03050751a560901188032945a4040c03140d207000f8144074441c030117100541e404000810403a0000500049440c54030300a00e80c20344800443c0401404d04034805980204220050003000e101135400380303018840b519512142e070085203c7c1e01e03050312550000d44985801118495082d0800c80d040130b118041c0d1402c4c03240c0d03003035107440180450b4582540c5d00c0020400010b1031030206d0400241464200c0c00c2403d03c1e5040c0160800000d55900e00464020701490140c0e00081c405030251005614070852400103584624100a25048044030340789501401001d403c049000c40d8000b04030380400000d1a80031f4900b4103840350044d117030410054015030400c88601c40952401042e50041132181c540c41d038030041581803151041c50038030840580e036442100803a108000150300003600c00300c441210280401e4400214a000055 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 592061474 1250 592060224 592060229
    0x604030807170a060915050901030b070c050d0201050708010b0c031812010c0c02030106060912030f050f03040308040b06100f0c14030f120f070e06280207030201030e062a04 76
    0x400480740074443c20070419006a016078100400030451014494189090003945125040d004020700d0010700105040d1210700b84e0010b80d90801d20303020241aa2507900e00b92450400d2401030b5920001d0140c4282c1c018202401025103402c62814140c1c8040d802d0b48a1048540c1200c075082c00303100c00c40990b11410034840a8541c03050003008400307244800508083c00b041c8040b8032951820001140d581d00a03441c02041d105c640d4000c1c00950403564050f00d0a198034a01078003481000d122010008041d00c000f588150700c41c0d0350b04001401c0602e02030041403c0942503c0c829092088440030182d0701c6414117641071003070b18000b5080d0303e0a0503c00d001c0c61420140104c40e000000781c207007046a04d00024042107082c000b20f450340e0760324055400f1203560141c908000081c906031408182d0711f040009003019440c4149190035001100708403081c04003802c110000543c0207101d040040d0742c4c0500c28103a0f0b0717000b010098441741c680400c07500c3c98800000304012804d1400b45021a8030303205002510301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 592062724 1250 592061474 592061507
    0x310c05030f0d030501051207050d030c080f04051e0f04091a100503070b040302060909041e0501051b03060f01050f07050105090102071217070e060f03180d110604030807 74
    0x80000803944a01c0d00c4540702c4081e031000c6400e1600016081c202640d010381c034000310f00d01401e0880e0500f000c02071500c0c81d200090b01003007000d404040129010f080106103076821142440d075658038100a110004000c414080096062095028040d445420003c0124803044500146070300c0c66292002c00ea01c485c00b000078524035690200000c0b1041c2cac2446c10700741c0c3c4c0e04074200e0348920790b984846141e501c80d6000094018000740a03800160924600e1190000e101c2c4200920080500848100315544840141c409a444000740080d40301c1a03071222408210580d000d07840c519007000840c0f20400e00d01107a40c104840051400d100c928954280c81c01198032400034060344c03c105030070300e010390002d66003501c030146d50100907041e040c01010035041e200600c0e201c4800aa03160030b400c0d02c560186202c0c43d0340200c010010b044111245000640c4503007501c00b045594140c5001c101494410801c04d1003051021940841c80345503400030b200c540c42585480e083c0b02d1541d485000700c4030002c04500c00803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 592063974 1250 592062724 592062733
    0xc0702131d010e0304030201021e1203060d02030109111e03122505064201090b0a0822050a060902010302071e05060a0c0f18051512310c0503 62
    0x2903c440c404002041102d000740e01b11541900040110110307244800d60800495003c1c00c240c1c002d10b24280d0145030f010300e005114240413182070f0040f070b00351074001c00e040320010454040001146040d12150031031341e21030440000351000031004650741351506201c40c1004840804e5550480840340720301c4940c51052800501080c120746801c035507403075041d10340a40106188044005070703180c104042c00541411094024004076040e05075008105000f40c03141081100300d00801d100000800802e4040000d5880000628146c0c15240d02810624107408104401042c88004154002080a891a000f42c1c000594640c41d20041e802449118401011040501d5016240317034032441400700b00d0f40c0120103030f41d01c45c3d9a0004070422680c0100c0190007181c03903e030b0040c50451188002d20749410740e100408885c0c0d5121000660740c3e030700902d000300100000145a541d85294286000e030070807030010081c40700501c20b156412900041c10300443c0d207200c01c20301c1c000070703c1807841c440e00040c030003e029203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 592065224 1250 592063974 592063991
    0x1020d0f0501081905210a02010507020a020f01031a0303040b0d0b040e0a0b0c130e0a0c0f090b0c1002030a2403050a080d02090a030b0718030b0403210204060201090b0c0702131d01 79
    0x1161f60804040600554a0701001414103170010504a030303113aa009101c0706250b10810010742c01003101da8080c40d0340d103107100e20b1a4040d0310b007000107201804241070129110358113003960906991000c00001d01650406401250060001580d0152070740d11003203040340381e900c414404165019600c3d80c080600f06100d80007403030441015280d03000344100402403024044c2041c054903611b200806050006c0c250035403c005802030b41000d800c03150320f100706682c01a01d13110040010398000341d515000b2944d03511240c0c41e43c0410704140b40300b0301d403581341c00c0390f6a54a143c59446e00c601109a02528010000403044c000e01415812a56441002042c0c0c50001c0c1c1ca90400501c0755100312241c0c40861070303044120609540360740c01582225030000c03100f1102c0d40c6a0b42c0455034003150105401c110003002c4241c2c80520001d002400240003036030300004000c11541040d80c0d4094010303000a5400c0310402c848400340c1c880e04031314901e0200425003c10401d100701508551050a840d1030a0305510f0040e80303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 592066474 1250 592065224 592065283
    0x6240303030b01090e04051e0a080705010e071a0d02071406150109120b0109020a030605030f030918010803030402040b2202041d0106051803160801020d0f0501081905 73
    0x102d01200c00703030307114110280c803001503000d500b1050b039010308541d020a041c4031254074a51a10007110020a0a031010a0384039075651030140c105100c11582a5159580c80d20400b10401409000340b000d0340c1415100301c1ea241e4019032a12981c0740755504103400003001c0040c03240c201e0740c0c5a00c20302c174201281d000f8a40707824148040c010450b4010b0000300a4040040c0072120003080c4120039420680c040740303613407908842030001d501400598050507103404002500759014032607110400c464901444d030303e9903044c04012002510505000108003094014052100000700380c0f40d003c1e6060300c000882d481c3e030b0400910071110140c11010000003150121450700c0301070300030304100c07008146102d020f0101d800350044508000d000304800520203000c400783c846d40243c04440b4514005e403d03036044251000380e00c240c859607600b02901582d00010341c01d4089102e4412810b075500814400c000315414002c41b07544455800d1105054031609500b6a404d00c9024055024801c0f0064503418030f0030000c106c3c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 592067724 1250 592066474 592066481
    0x130201140c16051009060c06060305011503050c09130b062206050112020304020906060f1e1903110a26040302010603021807120e0c043e04030624030303 67
    0x3400d81d001100c0400041c11300380701c0b141180c030700381e161a2120098104107040310141d11341d400513284961510f00000100e00c0c00c0c491500e41d4191004070001070350450030300925104800b948035000d084200100200782d003400f0040303a545940201e8003001c42c2c4a003000110080b95061440080c220a180080011240c607032007401180c1c008e880e005c80780c09124144038106e0004603000f030742250080c0b001946602e09480184001d402008405080101400c0e840c1c404482050791004c4424000504283c40e480d101c80950865002e1300d001c0c019020004d031414254080c0406220522000301d296082c401c00001c21041218003074900c0c3d500710714090500078060001844240e00507600030a1423400040441e002d103200340c1d07064840340741c19081c01450308010194120007000e05e004040e2143c0082d5554004c0c1d2140c0120204d071012002d020030051070200328410441d07514580c3c41301a16051100ca1010344084a400c09000541400101c1144807403841d080f906094041e459000481015090b50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 592068974 1250 592067724 592067743
    0x3091505090d020a1a04050a08070b0f090a05070302060307202b0918140a0f110c100510031a01031a150d03050d0f0207050d0f08130201140c 62
    0x1101c0c02d96150721000c1c0c0e29090035480140c01e10302030b207041c4501c803c65640d2043c2c01a10880441c1c002c61802e440308909030b0409841200c0440721882800301c03080e0400780c19504a43d1800281544020031b99031950b51301e00d00d02c0020301440002c80014000342c000c24070716842d9081c4420a61403c441c269582c0d40b42d4a02d09a00c0c480803c0d003440c45001d180c04882003c4400070991601c0403014204044c1000300400c9500502a407510340d40c140c845e04030250205801001842000704503644200410030a0b00d000c0c0c041021019014071401803808000a03c4d000c81500b1144000f419403568204445a4000c540014150048020480b024400c9031207003030341200d001e185c00c01188000c0803c40088094140c0302005070300c26069460071645444141021080d11a0810f0784c9000c40c400203600a9030502c01d0051400c99000c1010f07400c0c81030a00c500c3d032141c9050f00c3c0c407040321413540c1405004074801404850100080c1070001d400c69004400301300e4105840d50505407510300402c80140d5910304003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 592070224 1250 592068974 592068991
    0x7061107300f080402131107080913020928180c0f02060c0901080402040e01020a0c050606010905010c08030a0e0706020a060e0706080f07020a1a060f030706051b010603210f08010b0403021003091505 87
    0x2040c071a68042f042e442a00d400c40c1c0700514140c5980c1901d1443c0f44007403a441158821400c0810001801c17141503c100d000300050000302140b000034030007003d07011280703842d503000654020000304161060381e18100c605a070800d00302484103442e90300114009040400d2009590740c07000424040380c9030046442400303a1306c1101240e841c0d07034a800c0110745a0040740304a80c0466070542c1400d000801032800b03903a02c0791192000185010f0400c1030145000072980c000d80240c2c00981400d01404000e0080c0100d000707440c8000d1117200d144c8040200070460043c42c001d420740c0200045101103200348024802150048865880c1c24228210501e0b852b2059038401c0c4903c0b40802a103505050101e0142c0444105840d95030618504170100c032482c02c2c0b4092282c40c3d9541c0c400700800012040541e030480610600900000f10302c0112003e841c42d01341a078180d0920160000402c481d086000440e4181d0b030723041e02c03e241010100d4a0540203041c5c02140201000d03081000c1d142614440d600151190100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 592071474 1250 592070224 592070239
    0xa3b0909030702030705060d0906241409060105090111010c0512060306040b0c0a110a140606030615041a040504060506010e040b0607061107300f0804021311070809 72
    0x603503096580d82d10900c40020f4044d00100001c014600c3d0900c00f8240d40d0380060000b044005a42e612a411940030740c121400b290070703083d02c1304508c0c032804001802905000c1424941c0780007840014a00e42c1d4001e1450341000360000780707195243d1083c6440103500004400034082c1c103811000c003a10b503401a840f001c0040030010f00003400740c40e0024041d40125001110000562161070040659074010b98051052001c0d0000b040b10f0f482040003402c2e5103600813002c5013000100380e100384d41040d130041d0132544654000000d02500070301d030a10048244030111400111156400c00e0b00a601e84d0354a180c550282ca4542000709101c01c0ea0462441707540243e9401401c3c00c5140200300840e03400c0e40301d05400800038084800018100c0d03210f00346420404001c2c60a00300740b41d54004210480c15450180d81d8107000548403810851503140d0701a0a0074104664988801c8070300030b02000740240b0191144100c04030b120030142403a40005142c0041080f001e564405609000c81c06a02510446014070903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 592072724 1250 592071474 592071481
    0x10c0b091e1c05070b040f02150d0905070501090b1c111c050603031806090a1a0a090807060804030e281404110a0c052a03061006050a3b09 61
    0x843e41c219134400340d0004900d0b01c02e03269500c0d180b1403443c00a0040360000f0840c1c103a07038441001e88020b046d040c02c000d840424540854508030b4280002640260b0500c4401d01081c40700080e80c0e01030303848203802a280c051000c45041d85d07074800f40c107512003081400000040c90800380183c50504082d080903854040c0200c0c0c490b0418165030313105500d000021802c4520201146142c4071004040c03200001703004c3d564942c0c45840c9146030a00b400d000140440300003810080c0142c00400c1c090081030048040c2a134145050806489030a0090006040140342d04140c44203a4881c820001a601002da00100e1620004d0325026490080d0094285060220380180902e00c3d250294031103101c5809240350a280702008143c406003201c110480d00b80c0507c00050f950489034080e00030812a4105e00c21040c0b461804c21300d820040c0191211004c0d005602d41400229003140484500c8211032600e06003020501e809441440014400044842800d5022035508503901212046082c801c5480d41c99548 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 592073974 1250 592072724 592072727
    0xa0c0e070815011202070507090203010b0301030203070e0609180a0b0405010f0e070308070308071b0615050f0117070c021503060102160e010915030203010e0a0311010605010c0b091e1c 81
    0x102c0708210303240010100d0010b41c0700030100f5006442c4040c86074048542c100d0710f6070403510a90304260050138044002000401c00e516081110f10000c141e032607295109400c0000100d03c0b03800006218605982c01010043d0000c1d9082101e0341c200b540010140900c1d040c140b900c20701820f0080003072015142400e1484040542c0402c420301101d80c040401c52606800e6501550a0480240f44070180302c0450410504041036041801100b8403860700081d0340740e5180685050300130325800c424000d656001c05840141d0300b183d064452040001c3ea83e0426a89404044599001c0101c00035089005103054000d12014030340654000c0c00e09801342c601d44100c0d450004920b039118403c000900c650080100060003095001f804411041c81c5481941a20b07034012a017903403040e94820440380c0c4801d5582c01810b03070240306400d1044506c4000d22803140b038000000c05039240c0c02c1028001140302004142861001c100481308a9102a0180f4800503440050b070380750341c0381c0703411840f054511080301d02c01c65 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 592075224 1250 592073974 592074001
    0x51b0a08092812030e031810080403200c04020c01090b15061801031503080d1d03090f0d051509060a02070b070503060312030c0a0905030a03020715020a0c0e0708 71
    0x151080c41c18042c4101603100d07254801c075000c0b002d0050544d55013120001000030f000811400b500c0300300817418070892030240079080202d10020003c00500c03109200000350f012001c80285c01e0411249088600d0101907181466018440182d0103840052003126205042d0041c69000e03000d44004902c0d82d59400c10b13030401003a0200038681c0600100308191025a1000c00c030b0290345010b01d00010340030402c0d20141002c1c6a0f940055032020004100d80008100c035000b0b1072500c00b407019010a41c3e40b289080c096a0380140c90000f482580d1003041c40140f0784504001102c2c60740c002040b6900b12402c1d0040048a03103080c1c41c101c07071500440c00051084a114022219559800212255140e95040c0c0403152900040c08055040c0590031072303078502c01c0c00000954020304d00101c480b41c0d5030740d80745805800180160b0103d4081c0e0440310804002c01d0700400c401040314492040b80018880484080341000604030703000701004030303100c4041019050200394611440e00c544842103541c1310101094803d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 592076474 1250 592075224 592075273
    0x30a0e0d1b0f0302150403380112060f061512200703020d080603100504020f090702010b130e062a0706060303141611030f150405070605030f010504051b0a0809 70
    0x1090b1175140b0f1162504003481201c523100c501841c040810031040d2000210100082e481154a219186c91030300a1159a2103400000011100c04000c518502102c180008500c1c81e6401e05014904401c20b148400700d4000a00483c000100c10742e4003000190341e49001d40003050701b50014425050602d03a81070040e8842ea00a031030041c01481d03000c3c04442c2c3c910141c180200100e070002561060010143c82c2c030a83d550040903d9000071445100f800d00344060210680d071003403c2c0300e081600c440060030020610310b070010000c0c01d1501c600c06121b1a015030220822511070011400003600c03000b80840c40e840744041ea44681c0d00c01c0800c071403e40c80c10b88240191501480c4c00400d202c082c50020b40d10780300c01c1300704e01800360a0b2200000501c841e40c3c188000c0d80c56055013400e6202c01c01042040038005034002c1c0000e030a120341035041004c3c65681468050080501441c2e452001c903400d501c030700c03510400e241e80c00c070301c1245c0c0e806a1000040c444282a100b103c05441883c08403807840aa003418642d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 592077724 1250 592076474 592076483
    0x60a030b01030b0a0e0a050714030d12050705070c03050a0b0105040e0c0103270323040f350c0f1002031c0209090c040305070602030a0e0d1b0f0302150403 68
    0xe640d096841d802a0303008080c18244040381d680b41c0740340104206000c2c0c0d03044103005401410343c1a103006400d4403102d089500c5d9510a8103c0d1880862306a0084003140420f251420009140e85c3ca1080903103162007007010107082002c0785280001008000240030003290b11808004d040759230703544180070640305001c6c43d083c403640082e841403003603512a60050710800441d503014880b22203e45d40407030203001c00c8107060740080d82a0403291140c811807280350600440310380c4403038075191405049040f4010303d40524040d0400407003801c1d920704100c059209040d0070341008101940100101c10342d8814600f00701c00c0c060f40f810a5810b1640c03602c2255030304a540c071074000d1840c0084907031000540e00458614415019801d010b240c00a46655044038803603417000101031303030b16800c5061140c03500180368802c00c110b61081020316082036000307500b405040c0056401c14841c0801c0d140c04c1400d1201001c4903072510640000000f40c03d410150b0324021a8003c1d0381c2d040b00b01c20034600050301403103039010141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 592078974 1250 592077724 592077743
    0x709020f0708071a100815090c12120d0501050405130c12020607050d03050415090201090509131a0714070512090d0f030c0b070c1502030a061814060a03 67
    0x816100c40c001c100c440d110301c50903407013980b20f02844c2450013000d8590100341c1d442c92109014200b400c002580034074005210070341031031801e4112035546013143e400260088400103819000c042007001740740540b5282c4d904443d00d0b05040c4a0390001004244501c6214606150200e860804284c030340c8611035410071903000b0350700c1c00c3ca084414103146d0340d142260499010086100407a03000d000f054038401c00c2c0d0f46c01180fa03041504003003416814225480044600d0403211000503a044845030085a10030307601d0f4503080d5900440b0289000300360780040c090500005410f04540c6882482d144a02c1154840340e540200d5030401366071a01078a10010010762124083c5400035036100050500f10200800071080703000146d40d415140180072408802203898881207004228288189541c080003602e80680680074540b245045000103045200c0b9855000010502c0302c6040c0c1c101d240070f8440c0c15107651000b503040340e012005000c81c1e0402c40015282c40041085490a4240c80381282e40044890 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 592080224 1250 592078974 592078987
    0xa02010314040c062319090e1504110c0109050a030f0f050f130815040c09110d0b061e13090501181113060e0a21030e12030712020709020f 61
    0x1d40310f44900c45450708030414207400300000c17540020024500060b01032045c001d001850702000e4002c01071030b04140740c848444410402c028500e803a00c8101c0d04004c0701c02003500d003104a5600031303510443e07003225640c5d424030200b0814410b0000728040c40358420b64070b40000f60a40715084030b80b081d05400801c0082c10812442d4081c07044070002d0b0580c41680c02051410310b5480c2c506034545500c1c0600c005641540908220606c0142101c0300001c00903060144005501c0075014106403040c003048442180ea03070701d018a407a0300d900341a5901f2140407458a030361040d4042a040a60b001210441142003040d40c0c040740300303503280c01418104d03907003c60350481c4490303440754030310150800c0880d8522a2300280b100c280800310503581d200c0140990340b6426142081c07441848010311030b64104c000c045d40c54601419544182c02c1040c600c894041c6014044125000c0018404600105030b8a4003480003080260a200800303d070008642d0841d02141c0ca8035a0310308112081c1e02030200e85003110302d4180100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 592081474 1250 592080224 592080227
    0x8090913050c0411040e1902040e1501140f130305030a0c20150d0905060a27110f0f06030403020c09100602060117010f050718060302090a0b09150c0a02010314040c06 73
    0xc20b034000c5601c01c6d4034947d0210952a07a000c030780199200c2e0200001000501404d443c00c24a10b15642c01d0130b02c3c4c40d54a01c1410fa0010101e0301c0350002c0c80302c0c0c2c46c0c0c002840b51b8a00394006000c0000d0355100060320b40d0b03052585001004040250403d940b2450014007040441c20301004e403040381403001c0c1c000305407003408402c0000310b60080c80105161070b271520b61501c00258140f100c5882080c41010004401e06490207000647e454a4403207641f100c015114800070814009407540407100c100c40c44000984228046103200d8240a82c1d160010300101c240010181c0210f03c56036038500c10382d83c1020310307aaa110803122201e6140316510160704041c0050210150413000308040b02080c400106508620064201c03c42d80229909030014110001c01d9400c100e03840403601c0144800d00e415070030108403000283c51b103001e5124800c0080ca0014400902e900c45080d03035520780f01080200da80315506c80c80519100c0b448401c04a0000385003103005a4070900d0003000501658200c00e2041d54141031280 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 592082724 1250 592081474 592081499
    0x614120403050a050c1014130314030c04030209011827080d0b030f0601170312150103090b0c07020405161b060b0307061718030d050408090913050c041104 68
    0x1624081180811178410340050401202c180e00c204080001880790201c2090118074401400300d802c0e10708140c411a010a502c014140854848864402da4039160308007050b48034030403980003e41103e440400000c07041c003640f94200c00c10400c04020321182c0d003980e1811400c403e9030b900300c044901c0f0300e24440c0041341e000805030415440a42d4005407640c030440019103090461002c2d64180d0303005100504c4244d4041c01c4404201c8404801941000301d6150101242c0348001d00100c2d44000e20f10010025078441e40200d42400e420440702d40741c90a000d821810703a580300c4d030816400340b4205004650030122508080b41c5a030a07a41d521805403100031100b0300c10900041d01940c03001c0d140c1066601ea42c0d030070b0044200034951074071070441c50410913007080c000e120000c2510504c0040000007549007100401154403400c0b940c0c0740018956510315280e0340600840040c41e0b04104078604011100da40c50080900060290086400f420300070400c00c01070390707800340a064000206000c2000982284c0c1e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 592083974 1250 592082724 592082737
    0x30605150405010e0402030d0206271c0c0507141011010f18111203030118062619020a18020c010c08010f1403060708150d050106061412040305 63
    0x5503145000c50080000740c141c0354280c0292029903041001c0c44110720741044904903056203070001d08075510340f0403030181c0302c841d441d140340c3c0c042c0403d03020261204105001c0c11100c0310150340c18400c2c0d80c000036001403104554482c22030b41403280700808a54540e00244103030450704010400701e00440d0125040340c001d040e0400c3d02c0b0701503480c1e41400560801a0007241020f000300c0408442d180c4050410110004014126a004108150118840d480b010048034113445010000c1030741c000501c05100000c0032160301c21081c0100c0701168900d0b006450302c20006421856080741c070a03d1075800076101c6600c9510000303600081c514070410402c21500f094214040c3c91410060501c440560030a09464030b160315140007521200042c8011019401c01c0006003c107224440d06aa0300e20012075982c1c400580305c0c0b000c1c05030940004003255001e41ca02c07240510050984e55000460785400c0d0b000e0501030140c070001c91049003841d10040400c409a5510300d510b80c10b800029200c5840654090b80081d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 592085224 1250 592083974 592083991
    0x50c090d050f0f030a14040b04090b0a0e010e0402011e21110403060209031507050304030507060e0f0f0c01050a270f030c06020111120609070219060510120309030605 73
    0x258a02d42c03880001d0050440307140c1e00001440d030320b00c01040300a040c01d520750410700917050306200900610306d60703c05031016204000d20010b81c1c603042000040620b2440e51041c092084403a00100355102c44022960113540700f138965226188880c0034038190324138014a5100001c16070541407128030a00382981286122041c4000740c1e95000500001c242e5015400642d0407580009400985042c20007815200b1070301d006400c101790410920040c80307484040c1004c0c1c07c0040210703112050290300e901c08020324100c2400c40309002c100d00c90150b00c80304134800c00c40090040340a9005154040c1c0100c0b242000503a407000000780d0280054540f034242c040112850340c40c02e01000c07a11000440c0c25070302a40c0161000c140c0d0b6407801600a081d82c1a2500c01d0000d03000c00d0050324121950040c2d59a0005021525680903560715a01245841d400b0303c0f940c0c0002c000044498140302c1c080c0c0c00240aa0503061007004550303101c4064013800920072324000c00180d00c240080000c14001d521036900400c18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 592086330 1106 592085224 592085233
    0x30702180601050d090614010311032b03021c110705012906090f0405071d09060102060403081f030809010e0a0b09010c02060c010e0601030b0703050c090d05 69
    0x59680050f0415100d0b17007800c0c00c00045411030081c140c10709650f1503196a5a0070069000240502c03000d000f4050400301d0220448038480d061140da69444003800001c070088001c80c000d40c0188a500350325841c41c0c2c0c0440c0010040e000d0404465021403010740c8550342c07403d000382110812400d01d02e600300305070001310071612580e20410fa610700441e40592215810400308080d040a0b55000d94000e00e04004c001d032890700880620310521410400b001780542480500144601c142c44480c0540d1054000a00007403040b030a042d404901c458042800d02101c000e15032b1081500c0d0412100020081030603956542e0144072007003a060202c41d1041c2d82440e1401e840401c0c418807a41904004403052650f065440d060200c0306407040e003070020000814071070705181d22600280421511042e40e03a020508a500c64065680282070803005a850540361800704010408070310380c2111035018 = true := by decide +kernel

theorem cover : BRFrame.Cov 591906474 592086330 := by
  have h0 := BRFrame.cov_init 591906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 591906474 ≤ n) (h2 : n < 592086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
