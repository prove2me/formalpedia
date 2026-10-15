-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4544
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:58:15.004034+00:00
-- url     : https://prove2.me/submissions/f5485374-b964-449f-a7d5-57ea0ef753de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 817086330 ≤ n < 817266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 817087580 1250 817086330 817086337
    0x60e010b09030f03041707060f0c060e2e0c0f3c0509011205221103060f070201110702011e12061e050d02150304140604030816080108061302040908 65
    0x1c114201d141c6d43d0303a801201d5291038810303440030041000a00540d504244d001e02030600055100c08003203060408510150300d0b11b414a01c11503141240c070100c0d01131407100701d62a4015280101824417800c0400380302504d410145e208207a000c02c041d641d44c00d45211014403222490008506901c0380a50384e60052005499400390356004644c0028510700d2560304248069442c4030322400902203441d04841c1100f61050004a02c00c1c140c09008aa10402c03540786040c00044001400b2260540740101100d4001041902c1c4e040141d441d0100d14031002c01e004040780c00301501070f1a558090001c00c01e040030a032808008040802501003092015810700340035403001807080100c12318078098510f5814078001e0301940498452009400c0c40d03401622010020700d1160404022951a03588034104403983d45010865038000e070040008120030550440c40c054000c0014400c0807001e496917000944032000c0070b0050002e13560001d40003490805829207001d000d0342c405407001c180c9000f51f5841c1c540a41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 817088830 1250 817087580 817087589
    0xb0403020715080103060e01050c04120203011e0213080303060d020f01030b03060f0703110315040b19030606090509340e160f0203040b03040f0c050d060f0f060e010b09030f0304 78
    0x101c82400410070b02099000c0c591607d02440d00802203400e08001200d001e1086128000c0c00032080700c7e00700107644c0c007036019507001090390780d80a88403800221440b0082d400200c0b1081a91058100483d400d880002620300c42e9602038004e00310f0340e03c0c6400304803c4d1183c0b100702a042540710062100c1e0354a0a006ca54000c0c0340c180c1d0854010f00708500c000c1d041d905440301084462400b8420020701d410304405051a8142c1601e001a484014001040c15038803840014041900060000400c2043c2e540c442000ca441420007040243c43c0e034140b444c1c66004081505100d0781150104020402114a405021042a01085081c9565902c1580058030700300d402010404003880e50a500b00d4100d03620b814410820f201031850207003041c3d41e000b2540400f0b0000303800c1a1081107924100000404000c029000003042415000e48514110001d4842c02000502590400141e406440c040f801004203880619019070074681c02c01503807501c550810b0401652621541c0245003086074248010710140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 817090080 1250 817088830 817088837
    0x406141303061a0a120f0f03030b1905191211031f060905010803280302070f06020a0306090b0d03140f0406020f0606032a0f060301080706030e0105090303040b0403020715 75
    0x20540d4604000a5075a107a000e86010703402c5e1250080052915107207980030784d501203200001ca03606420100d0083c01165822508130040f00200d801c42186103400000301c0ea400c0307402c940120036581094007003181501c82c541c0c200d180f00000200165030341c1c104485602002d4219083c1000b00c05010641c4581290708c5054983c0e1980180072212281c01864058100c1e0300c0194640400108031000c00c07080b2440d1500b14400044814076103502c01e8040f030740415004900c11165001b641000c2d80294031910900703001c00e10f0b04d80005001c813400d00a0590700310300240f000c1146900c0740c600b6a2602c0c041c01415200020070030a0604600b1080080d0000d88540c2c2d00800d04c0d610400c40d880e00d851005400644250f01c2000e07002c00d0044507e034030084000d02080e04005180080008ca1300c000106880310b98486804400418404000070395141103c1d00ca5505000701000440360500301c0e170040d900000d49810400c0001c01144000f41043d410a20038811180d8148e81d0b0345080c905403441c210080d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 817091330 1250 817090080 817090121
    0xe040f0b10050c0601050414041203090b010e010e0a050702190503070b0a060812030903030109230103030509011d0307050105070f0b0f061f091e0f0902041505040614130306 76
    0x81e06000c1000b1030141c03c087d601048000c04840707072003081804c000e1008100c0d0000e01180b001c11403017600520f840940c01310100d205940c590348100030554090260203440b0225400090b0b412070b032401068011980780c0c01230a1803540c0780910018061210105460a110402801c1700240410a065102d0400304400003101420001d60500b4000c008030344d509808401e01c14440d04030000701c00c0301e045540788940000c0200d410b408990114004543c01400900b20400010915030880001e001402099031680070700c881e1140350141e60b454010005400d60701034401800194024401820302c070b4080c1e402600000c0c2507036106112880304a9108507101008410701545e41400c0c2145044015031171a004003c01e18818000c1a0780c05c0c51058420300195001d2207200040302c182480b002c0c01c2d410903101c1110f500c59803960080e41c06881064007911511000f0305240717219034240c401740c484682d240c017a41921010313442082e8100e64540c5420850f04d4500200007510792180800c11040c4c112070284 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 817092580 1250 817091330 817091347
    0x1811181f12050c1521060d051506030f03210a0209030f0102070b1012030305060609060a02010e0c040c0503010b0703020c0402071520040509130507080303090d050a0e040f0b1005 78
    0x81c000200c0800c0904c90288815070208030010840000000103c450001640ea540b00148080084120140441c090052008082460400064803400081e82240c002d02e001d14111580c81c401d003903280340121004c1041010700340e4100c05c81030308035111000260a00c188140001e0621545c0040c15071240e50000d6034504000c141c40c80141d02c034000781c003858055494104888451000040c005003050342d1840010400d80e5200140c903894540545003d4880e0030b03445c8064000d022403d0b200c030b098840d840700b1a5444c501406200100b08103580d58a055034030f01043d50b042034000c20400c03400e5010b4500c0c06070954407a8400307041c20368011501d050582c140100e1312011034650541d50009002070141642080c03a082040718100c41c0d098903d039041e9512040f501c01c203046e40030030050407401a0440014041c1e000006540518198025101001c00e9040103440034801c658030325020171554019030034585050f51051185d80d206600124510081c0d00000b0903449003080d0080110780080341010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 817093830 1250 817092580 817092589
    0x180103050c030a02060d05101a0405130e0a0311030706050406021b0106030209060613030203331608190c02010e010e0c13050603101811181f12050c 65
    0x300c5410242e0282002e69100e80100f2110b04c030381c600c910380445d102c4000c107103000402400c8100405800c1d101d003042a03004001310280740e01c2842030b03d100e04078602032007a4003c81441a01d08440c604402001c2001c0560b03410f5428602c449402c103000d0009000080105001b8003031184568441c20303005075900005120f032184180b0841d041a0142e02d80241800140c0b1502089500010212200c50703c804014070b03444021091a00021341500410040000ca007600c44c140002c0c0028206d10354069805010202c001c03000111031052501e01821940300341e00740620011508004510b03000034a003107840d0154020f03500c20501e0480141e644141a5016603003c0c401c2410b00010200a0024507000740000b03041e69907083c5001b06507030340d5900454019a010405e8240d45602c83c0c50501200601400d003498510f42c01c40140c45244128144040c0ea2411036034081c55903601c1c0c05a4566501e54901c002040c9181c0410f8510380312080002040d0046100b002d154018420002012030202c20790600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 817095080 1250 817093830 817093843
    0x61d06010507050a060606080c1608031b0712140f0403080d0f02070b060109060315090f090507030303051b04241803080309010f06150e0d0b010618060516150b18010305 74
    0x1200545020300502b120040c014140d1214240c03c044002d8407a12100d4008005140c00f10380c03002d08607000a2104100140341142c80e400c3c02803a10ad074061668502ea007480c0380d01c1000d160a018401c100002e00000d035408000d014205082c0c0d00000340070881d50022000c0740d1003030b5800e44205142e1400c00c203456a010310580040d06141c070b018030002c6220700c0786021083c0e80303000e603151003902ca4450b0015190341d0343c0b207503c403e0380050456242c0c030754a08015008140c140d440101c401c42e8840c481050054a00888040780c080600c1200420043c081d031903600c062120709001005902c205084d2003600c50f070b0310740c4040e6008003101c030b030f4905015030041d086601c0003002410082c2450f40c1041a03814031804600c024115040080304080c0c84000901103001c100c60046c5501c510384004100c142d0700030303c200c071070703003e000c1041416944030201901d65000b0071480092603140ca44a0307400050410101c001e4803000c802c00821003031080d20001d0f44044031a441c4807042d0840c40c004205100c4208000b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 817096330 1250 817095080 817095091
    0xc0705121507141602060f0318010605061305010e04140a0e010e010b0a0608040c0b13141905220501060c15060303081b09040e0c03070603061d06010507050a06060608 73
    0x7500b410182c800030381c2504e010703015540e0080d5a82071162415034541c10111401100c500400950700c0c580740c20300d2008010400944000b0750b182610100751402e001c1d08075a0811003808845c00b049180c036004540044c05011030b04c1d0030945409000144200c5442d40c54015250030401144034158201c0080c01c441a810880115a05006852046807529480d81c1c0030f466481c035120a0a030340c2c60030000c4200c0799580c8400d918050002308510320008a83d480006d540c0d0500da005103442d030100820141c00c01550300c64400300c042c03240c20086413801d102c002c43d000c1d009001820542c8400009841200c500364840400303d461410725004002c01c07a8406003181701c1c0c09000708805030a589006006090080049613100710146000d0f200d41c4411082e280e490400410902c0200c4c0c4c08030303116869180c0003880c54060f101d0002c012549c1c6000b40130781e0050b203150007821882c0b110a001f1241090700c02a1034035041c40001c008080c0400d80c10302c850300304240a0b090101d0018a0304000a00c0400c0c02401c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 817097580 1250 817096330 817096337
    0x11030f0d2303040812040206070c060c12050a09050108090c180403090b07050a02130b030f0c0103060f0503190303061d01140904080306012d090311090103170c0705121507 75
    0x4000c0003413000015900500c40030380034805190f5951011407010710a001003e0010112224005070980e800201850039620400e404603443c0068074055880d80514403540002c210044001c1c030465100c5c8040960018502040340c40040000001c0b681d0100000180700383c2260b10000c0009054010030010010100c1038000c07850581d00f81c603001c2d2a210203100003482408010001801c0800c5500403500e040c0d4000c0070388441414041400c1c2d40c48202c1c103000d03804282040e0000400414a0454604886d00034000d0182034219100310340d091f55040104605050f9900e0b03002c907601100c403594500080c411002d415a40d41412040c82007035070b0905003640324000724020000041e01d900700396500f1000c00e007001c266004a414840d5105581d1440b80d20b60300384200000162554402904070807a4005d6400455000d0481c040c014a19030900018022098001c10702c004e400c202c400500076290b00c4002d5603c620f807a50700050414420610780f4006610041301c0f071440c0d03480c03908481e80242c82800e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 817098830 1250 817097580 817097587
    0x33006080115270c09170a02010833060706140403180311011b1416080c030d050a0504050a091a0d031b02010201020f0d05100803040509010311030f0d23 67
    0x40c10f408441074a0320040403564483d07508112050044c20f044010346000420090340c0e451141d2843e41e607964104083c2c3c00a580c0e400800d04100708940c0018080030307144001c059a01508031201d84c091100b12409400c02420080400440c1d000e2080b0320710060019142c8004d42058100105010394506016504c880038000030000200040c04e0711411032802e08154845140124002120703040c0c2450160046031040300c100d844e40c8011480900c60300075210031095080c1c8039041c2130703954618803010741c1e00742d0321009105400318019000340403560800d1400d940b500361600d002c6151044540e201202c181d1f100d2071368001600c103410b83d03000605003c0e00c0d000c441e081c03551401012000f030390040c40301c00410303480501c0540e4400e40484512090b1852960340c6d511007044404002d00b07040314411034900c003101011840710404001c603400c5950042502d4066404d6498000d030801e202c0c3c40ca5503242c4602d00c0300086291041c08207039960201c0e038696024031000d060301410030f02030703c021410301c440042 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 817100080 1250 817098830 817098869
    0x2b0203120109090813090c0306080f0322150806090a020a020d0e060d05100806060324070e211204060903150213151704033006080115 59
    0x16a00c4504507042c400011509034075504040745503200e4008008000303e000d04010a04c0c00301038200503490740032940c040003000c2c0d036900d07000e0722000c40502c8130500760002c00c00040b0602d40400034188446082c44d014003159966544000e50109841c0f06002080807941084500d2810003000c80d0b002c800c2d0340055140403500ca100a44688540258030140b013041d138540c80d03090b01c90400761803440000440401c800e003046514000703000c0d860303c2040b075148507000008816044c0440c0c0641406082c0103024984801b007000e0508031400100f8680400c002c42804071030b15541c0b40c89001283c003240c0303080409110302c14411400c0044903104115030b41d100f00010414242d2018010007100c2c2c0048407c81c6141200d42c440c80070784944901d280d441c40480801060000c440130800e5013501c03241c1c80780e0100c0f035500ea10f9034101e90300c12940980494400381660707245510130803820200765600382c29400d600303044094241c2124019007105040b0ba64545420880100c034060b2100a803007915240c100324101c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 817101330 1250 817100080 817100107
    0xc0406020a0b040c082b0e0a0e0c09041802011e02100f0f0e0d180b03060f0a0306050a0b040b0d02150d020906040e090c0111030306100e032b0203 64
    0x9807000145007003500b1001400b40120007240101801020003522082035050a40664a00f41c0540e42c1200019501c2503150a50040da240c9501e01c001414412285242030001001c43d5030003000040d00d103030200801540ea5896229040d02500440b0042c9609003e85c0001480448654403004481e0b00c0451a5050b494000a10071609208094007060b2601418400350203842840050a44a42803210300320070340c01c000c070340410020394030795a02072000c40d40d8214940341041803041c034100e407400b000400d0300c40c20040b02d000c2e41404094150807070150b4a0341c031036040381c2c2c04036140d8543c10b6607440443e4861900b8014008190800c540041c2c84050580014059072030f460144c2c04225000a80e01a03140300580558041e054010040740e1115038451501c0c5003001d04a80540d10740c083e8011020441d8080c0752150744001c80701c801141565910002d000c904c0720344c498688140503962054401c141c1d020404444200c690041d284001e071407070b11125460084119684042d9001030200d156540403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 817102580 1250 817101330 817101343
    0x306180c080112020f032b1b02061b0604212c0d0f05100f2904110705010b09090a122307051f0603050c0906060912150c040602 56
    0x254014030680c3c040b0306200182e0f000840c1c00d1041d4040c0601c0007103c0003d245c818104030003c4a4500c1f1044a403c0450200c500404400b40071aa0201100c500d20142c1050000340c40c0310143c5180010311040c111003a646002c508540480f4104401c41701540298100ea2480045445600b8959440022418095401c0100b080325040181f20b00d80c031140c00d56507401c129400c0d1a080b04401039403a40074113001e0f03101c0c0300d0004181d1113503050480080040e03403e4480c1030000344848a1050b000144c42040c00000714110a01950007611210414030b0000180001e10555200d240005040c0b07010078140701640300020100400b039003206000a0114104540048038003101d498006d101c05100ca0316030001801469100c0c82c44800490040204030000034140e40100c500b40340343c3e00354406050800191959804000c0c410b41007501040c2e094103001080039008103004240c0f0b400c1010940215140203511205040c00d6030207050365540c1541d4440400b034002d84401d805510b850700b084030295481e071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 817103830 1250 817102580 817102589
    0x10e030601051c08030708070305060a030803070c151a0a270e120a1d0909150a1b0903030e0108041709030f07060c050f03040e01050d03031107030306180c0801 70
    0x10f503801854440c01c50988001e076102c0d0703ca441940c50342400c007001060b45078100c0d401008280f03403101150041c80e09022050031613030b200c240680796641d200030880d43c448020804694108c4041b42c4420810894050b0840204000404031940301e404401c1240031071250b0b1085d0209540b90051a15000041e403030941e151004510105134030b0707840241c0d1131515482e01c076042101c030f4001c5009441c540c0c2c44840d4410f01c94000d1012101d0803220000c004441e0001e803103650b51544189881319044000b2444640c1c40200500b0000e00a02102031101d200c901d420500c00c00141ca01310140b0405400451a2480c80c9081c0b130031150a00c2c00d40d032b4600d01031700a42c503a000c90900108811005d964100801c4018240b4802034460850b0b40d42c001910088041070700711707043d001d004190a40c0301000801d450480d030f1703008441490340e442d1000340568442d88803020b800301911130743c03d204060b800c4002003060354803039038000a40924000c40c2c080820b80000d150741c0580d00b424500005690700c80170a41c1582c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 817105080 1250 817103830 817103839
    0x80f15010f1a1201170105310f020a0305030a23070b0604020d1401140609180c040906031109090d121a0306040b0417070c1a21010311010e03060105 65
    0x1650220b12a41903800341d0a04400101c8180c0c001144240c0852840390140344032100038896900c408086140070096500315042d116140036034400441a0044a4141c81d80901076070142d83c403094012034010611604203403515440041c060082540c400500303407005801910200104030001c816151f28480c50b00c0180c042c0780356501007402580c4507811500488030390042044104190580b04003000e101340b054200f10083c90032002c082e0b04040e400c4541c0400000d101c10951641d18000f540610009007030f020000c01b00303100200700c580d1548190b02c0039601070305040403200804400c008680c02e00501e10385a41c0c11084040215a410143d042c500100421001c11042c00243e090080031102150295040c031900e0148401c0c07003054608140124004d004102020300400c2d5480b2562140c0b0600601c0601c181c84100160700007800419030780d0362400e03030f01b5241c01d0326060440004034107042d117070405c0b8a03040010410058440c00703015a1200c2800e01403401c5070418006603e42005200d0103016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 817106330 1250 817105080 817105109
    0x1b06030a0209030307111201021e16141b060403231f06080c0906130b031903020c09012304050c160b1f0b04030816020a080f15010f 58
    0x1406281c041e42c03140500902104c0d15140e140c10b2101c84030081d0320942d0b0203000402c21703461a81006000326a004000326030444885000b00c00d40d10000d0f400f005521740031100005611000540d000b201c80c1e024035140005108050840c0c0c0030660480c07000014a21410040008000081c3d0b12141c002d042d1540c000c0e0900490300320501142000c601000380001950079200e01075090069502c1013017503c3d190802c0310718111881040c00b402042c191162a400b90703030f0300c015030101491500100f00d44c03c1e0160a45040d412140c1051441103544542180560085607000980c0d003441d6881c5d0380140340510040c807040310080114404080d0071060a801a5111400600c03d4401ca00484002c02d9400d041a46800c00d2410080d0f20300ca030940b01d81070b15a032007140c0e0f400520745e401e0480081d9842d07489154941071555545180c00e91000039820680d210740c15600c009070381c51030388500091603e100a07004a50754460305604102c042140d0011511404005010100c1e510303100c1d6055a082c0c5408014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 817107580 1250 817106330 817106341
    0x1303050903070f080a0309120201022820030f06061e01111204060f020c03192307090b0303120c0a140301060306050f01020a11092a070b01081b0603 65
    0x402400d50011201220603e0b03000074107603c00108100110b000c1e9440500380740e00c819060300e100340b9140010340180d1000d5803c1c2146580f10f80c07003031085210300b1010030201545584104140101310355950104c03810301c04414003820180700c0b8060190f04e50024003283c0c5010b07400265112400111001114507128244082d0307400b411900394689480021140b102c0f0f0003a075104d290341e00c82e00131480090203000c01142042d0000550400e0650011301170910078880075442007400781316103c2070711012041c91900e00700100060403400c500000102410310351341062866019a80c400c040f0768001e900030080a001000d0740c0304a50341203400c04114681d140310313101e0111100c0e031a00318032404500c4000000140c0c903405070300101c12218140c41d8a03040100d00001a07031160365514002e4001e003504c824602e503a240c00000258410b040b29079400c81d8011031009454070401e640b0780e5488500000991a041c406103005442c01031101070000c1c104511000d044041c0d256402c41c0c00c0c0c3c060800800400c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 817108830 1250 817107580 817107583
    0x11706040204030602131d010f030318091406030601060516021311120717010305031603030e0a0303091403070201021c05041d0601030e0f03070212010e06040c0e0f1303050903 77
    0x20003c0d40c21035020364454883c1d42e407003e03c0c0c003031500c55290240103400c00307021000500300d030060484a80c42c0310f001405165032400d803110203a000e00b2543c114090f0038042502d00c114031a480e20b0a100d01110b024500c0c14005141ca4554180c00c00c8040c00414040c06030807400c20030901559642c141c0c4c021114204000c00301e80030704980c04c0036910407100407800032014008008002d00c81c40c8030b940c1da19400c0c1c4c02c40c84960341c048020302029241d60003c000d032101442c0c04848034481640300e03142c00070300d001d05c01200c681440d054100880c0041d0302c1d0510f00c4180250840e02c07100b007060b20000b442c41c142c103d60010b0364030076018403200805854125003010f641d0142e42a140104400702e41090100c044041c600361120049804030302003450030014442c1c0c1a40090381e4081340a240d0f00661428440307808100030603003c04040c10701992155550301140b141409000e01440c0f05513011440d02d13040480c1c41907400002403041040c51030072003c1081418942c0f01c2589201d1f014140381d551a4213040c04a17 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 817110080 1250 817108830 817108837
    0x40213050414090d0e0906042406030c02210418180f1e112e020105160305041e060902120c0a05180a020f0408060c040e0105010206060117060402 64
    0x1c0c0d001e490540c44a0400790440303001071084506070150b9900001200080da00c44240d0b514040e0003000020029020381404da00c030000903400e010361040f05508011307100ea031040c001c0e0000300c0002d8403100b40d01ca00d150100300703681825090b0707282840c204120510310080c0380100c0c8101c18800425080d00e210800c0e1540c0454400301c241d90944100310001d0030311418802000c2800c4030340b9060030105080c1c0316000340145010741d500c4206007070410581410408030081403000c05080e0544208011001c291103001c1c41c9075601190008902ca15101901d0944808800074070000c1c942000304020000e40c14080100d010750f4104141c00f40728400b828140024001064025086010358041c203001410004401440d410100c91003503c0395240c2080c06402e040294850003a402c540022800452030358001c0c0c040c40e00882d40300390034130342ea505d180340c0360002c244c0d003c180c9058001405d100c00b29190081902400007800205540d00385000004c00400542c030300c000d103061648012030035075035071a0101d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 817111330 1250 817110080 817110089
    0xb0d0818190e0f010e0f011502010209060d05090c0102060f0a110c1906050606040b0304021002010209032401090b0105270d111003050402030d030c090506040b0c06060a14040213 78
    0x1019041034480c103240e0542c400581d402d80041084100000e191000341c004603102d20480b00d42605182d20300f0510b05405400d0b6280350081d55024454081039440360005464689103200022485041041309213040c043c120040e03e0441d08450300700000c07a401c2840030b94000000000019400da201c242e050618082c84be520700760740c00b803500c8000c42c1e820007102e4081101c1c0a03002c01c00c9252a20010450184154400c840b82840305100040c09807034011401c026001441c00094a00060280040d05081039201c644420215001449904085000a050241c2030061040198030040340001c1c24500440c0c0c045200364000c9011071250200381030101079601c0d800f078400c8190403031510b420042c0745e500c081c0c624002c0b054001e0f000844c511a00516000e107801130040c044200250808901903c03480d40894207011b000c0c807000615480f040000c0c4000e208a414a98503242d03285880b500b0130101400d503d105d032003840000c2c000b40307224015915211744d007200c006035550004a04003c5402080c1e12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 817112580 1250 817111330 817111369
    0xc03051207090e0705180a0f03030e06300f01050d0b04140601060210140705030105120c060316030b010305102610020c0d05030f0109020c010921030b0d0818 69
    0x1340150690000c0151103940303100b2504c0325103080c1410500000308071511030000c100058140810119026807254443c030440504207500d44801210803c0710346050800804c2d071114100950100914124080c940042c0414580300480d450100090004103148401503c201e445c075001c2001c21024122110549010300107441496940b104042c0d2a444801c10181e034083c2410f5a003c8490042505503119040d40d840d45070541c0d08210a0104004121002c4603d9228056540c4c80c2e5903079910103140f094110200c1c12410b0000d82c0c0c0700070140d40401000310f05060030041030100b49050308c2d103020252807140303941d40b041220302c1e004402d0b400103110707640d40f240c0691a038404249031203400916210b10074170100c801c0858400d200726000d100031199440030480c42d80c01446039203950b070002c00300d08502d02d001291110040d1034296946d08040e4070140d500c0d410060b00c180340d0741c050140c3c403c0c1000440c0c011404081544403100c10b8451441c1036482500301502c0845265a0202624a04501d44a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 817113830 1250 817112580 817112609
    0x4031d18090f07080d111501030809041a011205130b090a02121603060c05221a040305060a050426071b0506090103052d010e070c0305120709 62
    0x461a10310040103680045032030007040c51052040d000058040100d9000000a1451034481d19003142c82103c00400080c49000d084040001084d451055a000c3c5000d02d40e880da68407040e8003000211f07595000c1c200001c2c00e04217076120191382c10a8500500c5807103410041803580d10001020440d9010010041002c40008280104024002030300e4504c02d10960b03044107030302d46421200c1e0f5181d8120041c1311344019a15028400a24150000c01024a0f1824410700b40380046c414010504e00c8144080381c1011000b10400200001050b00c90180d101c8107209440c1505545800361500da0040c0440c810540b208041001c03c8580500b001d01c00f034294400c00b000720342c41e0a400768154806102a150303030b031804000400740094400003408540b0b00a1103249046041001500600002800307a610b00c0d0050781c01e0591829100201d49c015601240014503540c18488008489000501042c0400c003002c246240060781003021135941000c400a01d1070240c3d070300d031012155061a904404240705c43d90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 817115080 1250 817113830 817113859
    0x408010f0e0c15091509030c0105070b13031701080303060f0a15030b031606050c0106093b010e0d110102070b01030b100302041a042f0a0516030e01022404031d 70
    0xd20241c00d0b5020101d0a92340700c030b031682004407020b00501c1c401034000e0308041c0c0407854000812004101c0507220741484125481c0d01014400342c044264850841508000201f004524241da80c00c900c000c01150360560301d40c2040c1c51200028260140d0100b4560354006a025550f400c114850001c0c81082d0030450181d1603800040c1143c100d1600c0c0c411941c00c080700407403100310074040d500e15845080042d8a9103071100c80614141c0b032012000c0001c152103005082c40c400c00c00e0091184110b10715008044c100760800005102c00e000d1228040c05074414460390b400601060000c2e41103d4004044291640750342000c403285810580c0000d601c2440c20328a426245403800075207188400880c1e04100f6510304038203007005d07a42000c286650000c1f008144c1e20700000c0c40005001911318a00e03140f03041140303010043e10781e40c48411060700400c0074031802000e1381da410009820070381c48500018408003010030341d184602c5005800101485900102c2c8501681000d156404820b4010301c0740c01e800ea01d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 817116330 1250 817115080 817115119
    0xe04052d09070b1e161704060206040312020c331303050903160f051f021c0c02060f0c060c0c03123301020d030c021525050408010f0e0c1509 62
    0x80c0f17503045443d5401070a08200d028200d0040c0d50890790b042d0082c0096554030790b0f003180e000440356200d1a6181d428840400059010000c01e41455103044a0031b00403c1a1400c40502c0c0c0741460460394102400410001040010611074a1080c0d050400ba6180d045030b00c002400c20b29082c0c480c202e00515a80001400700203c65140120380d801c2d030790103101c01000b11a0002c0540340d440120003590040700d610340024060f03600700c6c1c143c2c901464243c0010f807183d40081e00c03d902c407000480e2100d4006c900d0b0a87d055062024941005034103030844d14110085c040c0e81e481b40940428128002000c40000d14401101060303403070803440321100508d0600070344800112515078061507500500c00d0781c25101485000344164101c031000e0f0307001043d41c0c82085c09440c13007403a0000c050400412905485040d070a40100000340040800e4070340d1a03e0f1428244064210341307641441415080c00c01d00281310464010481c1070380701d50f0540e0401c660244d80c8151a0301c0d403048081d00da80121243d080603071031984 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 817117580 1250 817116330 817116367
    0x90301060b0c1b010311070b04050316061b09051f091503020c01050606041a030c070204020a0215150d3002071e030b060d030e04052d09070b1e 63
    0x40f8142c4010000c54480011402c4802c454506074002d9010419100400d80c800603455110344690116480c10f00303c941d11100340c41c3d5100b0216a05625035560720b2440f0320104030100d400746545864800207142000144c0c00803040c090700035540c100c1d002a030240c0d40c86a4144400307030001c041e9641c8092100340b4014003d42c00301c0e100c00002d5183c800468224541942103404852808203210000e0605007441540c650010f82015004501040520016142c0380044c091100050300641402000c070141000340800c02403201107444d0740100071108580c0c840030108207840c0c01c003010a5000d40b00c4840350306c10303c0d191000020b03a07000c0701c244081d0641d40080c46406071040440e0710b5000c1e00da809001c150082c0f80d4000201086109000201181005880742d202c0c140207140c00b8078049030080218089038402d94000034100c2588072580798072411640e1019050038200b2111180d40780141596407118103d00a070301d11601c0000c1c4198040c40401c8004e682d444030703405144e550760b6018076103404608 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 817118830 1250 817117580 817117603
    0x806040c05120c0f06180411040e090a081206120601090f1401120201030902060f0d0203042102071403100e03031518061c0506090c03100608070b090301060b0c 70
    0xa1110304411a280008500d00d43c403c440600f05510b0030014608000307075a085446c1c0c14003003084000540040d90780e1401221070b20142000c4503030b40e99040c40d0500114a200500d100342d60392141881c1c02c005040c1c0b5080321540d01d421600701e211625544c0c00078145500103403c440d42403140708000304420001d0382c0000104106541c04110130b0a15491719400c02030709106040c00b03448558000382c013650094005805162000380894a0103003000300140060f041080d015400c40c3c3d000c0104070810020701008105c41c0c01c800c0076402100c0c2d015070000c0d600c1c06a4003c8007140e005948601080340c0b402c0240555440c0d49000900042440e108081c0d92030300125449085526014400200e50803c41c0c240e0180d10442d207a102a95580d680600c0a52004070800040b26285c05c2046008a0010312845000d041d010000d40340c101c40c0e58040600c0c1c0400301c460340c035900c0d181950400c00b23020009a20b50441e8982480c4c5512012003400090043c0345940c000649444001200048188042207418103034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 817120080 1250 817118830 817118839
    0x11404090e010c020d2a170c01020703030b0109053a0b04021c20030a0f050c0f0418060506030a080a09060810060e06091f1d04050903040e100806040c05 67
    0xb11081003c0352808024851105a15144d01c1c400215407000c1b030788001b078640074000d500300d030301d00040075200c0c43d5124440070255030b5404103000080560601804585407401d203001d040843c1458000380541d003004212000d000714040524000c0000000d00440070490300104089981e01130500300090041100c08920030f41d64206800881f100c44001c030280c0f140c000180300d400200b000100040501d0101e401a0702d4819130300c20341c001039038125030304061620038030141c0f1384002120144913440117030303058080c407132820030508508050f91442112a15900214003040c640c07100c902190909410000140400d0000074098940d01d4001280c40c044402c00c0c0c2d1032640c2503135545040d4041441030301407900090348101c0c0419041c900310010b042d040d80010309450540c004038a0416060041d01c400001141800c014201210b4101b03450140e4030101341d805018074a0302800380c54580c81637002c3c1d015003d5105001c202401c0740c02210343e0240030f00c20200c41c1c660525080c4001c3c00d9040384070300c0d4800d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 817121330 1250 817120080 817120093
    0x13110301061d060a200f060106030e011805030d1107020a0b0301080f0c010c060903120504030306150504030c0510050f070303091716111219121706011404090e010c02 73
    0x40341070610407030ba101c1d03205540d0718998003086a4030300061030070045100a03611581006d03a0000d00b00380021030003031840e40c40000e66a040c50307000500b920b0303c2c00100312004d082c50020001150004c02210b502d00450800051102d03444507200115004030f0380c0194003d090306c000881c1c0b81d00c840c40114182d84040d0308031500c0c0d2800d848155641c03140017000900292090b0781c1c0c903000804a8000225051103801c00c00103030000e140b851001c55100311815000643c841c04100301c0020b140e201005a11060301d480d03440e0034119100c401d01c0b1075a5100b014010703007445000208040c41078054030740c0002c2c0c10b10326969808142c2001005404200c0050b0741c03c100d4101d5480d950700018003156219810251800c401c1c0c03c1d070b078542c844801c484018142c1c1043ca0110406036032401031080401d180202020b1115641c10b604010044030068421a41400000d402d54456194a01f074000d42c845800d28044480c120403107a00d078064041d590000070302e07034200103601004d5001900b1642c2c0408455003110745 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 817122580 1250 817121330 817121387
    0xe030c1005160e0f0a0503060411120309030319020106030807110a06110607030509011d061501050426010603060c0c15020a0f08150907020307050d0503060901051311030106 76
    0x8080c07544101201081482040c0340144c1001d0340482c1e0204001400d0700c52140d40c4002090800c44212000c80f43c800101000031103c0c60290702c107003500a444402103007400d2508002c00e40c0e0740f11b51340552246c1204505040c0c0310034800d41006025652001c5002e85500c6603146c280075480d400c032070080c4a02116800411000d1081c50306a07021000071004050540ba404000d6004200190258425540381d804d2100c5006241809800784443c000003018585040d520806940c2c05015210307040140c00c0100300032180c0100c0c2c4041140c480c03007007942008401c0c008814014502c55000400c914105941d0140c0c1c070f9040708109c04014010801c5440181021f848242240709800c1e0040101748030703c52a5240707510034074149521420803281d0302c13216005c1c00000345a90310222003807401a030000511404029050041c503c0c480b0841c10507504609100002407000c21050042a0240d4000c001c1140010b100d5000b810380404900c103480d59a586440c0c008004071104803180310b00d4400c0c45090403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 817123830 1250 817122580 817122601
    0xa0f1b06050a17040507031709010e1e0909030d06030803070f03060605180406330206061005090105070b0c030105030c150a0c150614090f0720010e030c1005 69
    0x125901826540e1041d4454100f01900c9100e50142003500da41c45a0000880041d015000c06141303070041d00101c68031a0301c00382c00100551540703080b481c045c0c07000502000c441045100200c000c0c00003200c09202558950700d0091540c01088030715400103050500010074041c64100a500420607039540c204030380c003006030980c181c45851081070001942000f60924021400601e01d4030060300601c0490b00c203540d02040384000c00d030301801c094504c034030307143e4203103c207414801015000000d4005840780707181100010b550607000641940500c2130000d21546940c0c070400c2128181c640c07080c003500346802e21864804040e0800d01907940284100700b220841403a004920001791301802c40e4840c07821054440498040c15508022601504098011401844107000d03c2c000f800e2103850841e18405c49070f0821042030400340040421040340c01c00d000d040343d40710392842d4440c0a030701000e000800e443c0070840c0c0181014400050240000b00e40d0041036140070441c5d1a40582c40801404030351205808036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 817125080 1250 817123830 817123837
    0x60c071a06090406020a051b030d1515050721030903091e0b09010309080706050a060b03060d0219050406060e041d0d0e03011517071a0a110a0f1b0605 66
    0xea42c0008004001400909030b0f400521031103903603107006400c204503c0c2009440682c510502442c98001040d01081130401748100040000a141100702d000e1500d1591110340d400381207181c00f00500040d0080c14080c050152010b1070241c01c040044d07103521510010001c1840310302c110002011041c0010307481401401c1c918660741000c000c440801c3c580f5000030810703446003103554140b40d120350381d00c3d02041a21016040d92030041d0004219440e0007200d01d001c0b1032958000303003600103050003032028546900e8030765540d081d810748080c0122024041001e105403280ea02055109043c4180401c4d259407100d41900d440105940521500160134803455280504400e06401035102041501d0324512907090340c9180030b00540002040d0202e0907000503180c9050300b000c080005840c3c0c0d49080c0800400003140102440d02c07400452554400d040c40d400c2c0310f004c0098041000c50a21101d418506018003039940b64044001c221002091034010241050040101a0100c41e1080001c0d6180140d045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 817126330 1250 817125080 817125091
    0x31d0c0a1e120215030f0a0b0307031502070f06110d15051005161a04050c030c030309061806040815070e09010312120501060909150b0415020f060c071a 67
    0x14030748000d0800040d801e401070b00000581c0d00800142900740405105001540901e80038100402c540c9842c82d0000182c0303030210903060099101c01d10400c0031496008018103c0c124401015956102c20300b014080c1c500c020724050b000c9032800002c1e1034451200310041a0101050fa001e2001141403c041c8143e06603d2050703a410548140040301158403941c01030502c01540403d40e1805240c03619442408061904501d43c001c020f80188001c0c01400c001c0360034561401c400405405021401007512809080f500324056040400c0d10410200074034610303204079002900241e00c8a42e101c1e04659075001c0a0122143d180d003140218031081e129102c4400002000741c1035841c2a40b13150b42d4402c1010303001c0700c0c03d001c01181074503000e52680076004803402131005603504800b080c14100a0802c541c80d14800400d082000101003007184e039400c042d90211010122349200643d5508800e074106119525202042e000d24000c00c403030502c005000d04482c40c000c0f2043e10b0781c0c003c00d0300c0d81607455070150384 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 817127580 1250 817126330 817126379
    0x7021006050a06111002040f05090c03070e1e030109051b0607050c06071a0412110d081512030a170f01060e0d0314070506091203040c15031d0c0a 64
    0x414070965010304251302e440c001e108101d9119400d0003000c141241c11a0304031041400820204000501c0c2c4658280e40010700000c00c030340b55082010010b0290003160043c0c40c094031903803000c407801d041224000941c220028000b840a0000ca1030481d8036101d400d00710f0200408601380412860801c0d60948000316402001000107121034030810110b40c000fa1011502110006000a4000c0014032414001c511882c0d0b2a01c225610000207403030100742c088120a694041b00c850198181e1050407950030010218444050301800700204041c0100078072581340341c4c440020081011680010280c074039901102a0314280d0311442044005140c0a2140c40c0000e8008075204d01d00d803406250f052082c51090810034608820a000c1c0341051f0003099068030039030016400c10540752800e0154080700180d01c0301c50341c95441d0036074a4810042c803a0046c094030710013000780425140d0195002903402e40c1c3c40c0c0a200c114103c2d80450319034580c0100d5829000705204040024484000828070081d00c0e5040c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 817128830 1250 817127580 817127599
    0xa020108040611040302040f0902030d08090a02060d02040b041e060206131136090a0807030507030e0303031929040e010b0402030c03040c08190803060f100201050702100605 76
    0x1100d080c054103c0e0003d02070910300c10040000140c2c2c66114035a0034070302803103021601d82c260380101402d1190303049045080c842c0f010104005004003180d86441c895040fa42580c43e05200b030113140081c0516040a045180001004500e03520400e15800500321030714003100050351100030898540340f0903103e54582c6541c03288003400042d2545507094802e034003c2c001c1d200c0d00c10b8240700c05d1501000102e00c14009404200551100c2c1850030704190b1004d9060020704a14015503901c00b458420038002600300100810200e080620441c0010181d1000804880e228100325041c0d81004021061245c00c2c40d20301111401c00013441020802aa41c1c00380b0310b601104203600c10f00018242c20304407102d85569801e00002240d8451001d940900040c10800c1d80300e18241ca00380c030000805401c00c0c00035a02101c0e25104c950840e802440801390f000382d00382c0e103d88a46020500d44543e02e00303200ea02107600510b1a04141c0d0540c0554414460f507400c5038030800801d6686000c4508a0140c69007010070b22 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 817130080 1250 817128830 817128833
    0x30709110a05090415140112060f050906010c05060c090a15090b180303160c06090b030610030e1c030b010c03140f0906030a150e06090612100c090807080a02010804 72
    0x10b102074411044041e0011914610082c50040b0008503a008070300741031072070705031a80c065a00c0703e0104050780b805078041015508000070b1004484803445001e20484c40070000405a9204c2d0018100c01d070390180850b492400d0030045203889820034240c00d07010342c1d4040300010b800000b02c00213a540d050291203034020300c0c2c1420403a4000b60710401103102c4280c03500c0c40c1c001c1749803810002400d8101c0c2c40b0802191000340c1c1e280170594003c0701d03400041001556003050010118100440e600068200c0b00400380145102068024208d200b200e000280202c1c1c0040f42d10300d17410040d41c1c1801906076000c02807440c144c4010341c1c0340701e03c6000150001d1605842c081d00848040000c00c06240780d2054907003481c03140c0000961f0343c0d02c00c580c14910307240c4600125090b0700030042041c01901110308010924502140841c1d1640801010030340300c0d491000c0e008000000a0000c0100d01503200428410f0725042c1e4405031000c025031007007542920911400003038140002c9002046c1f294140c1d61841d1a4846 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 817131330 1250 817130080 817130087
    0xa020d0801051e061905090406141507050703080708030a051f170c1017090a030806041a0909030a0e06090d0b0c0f070c030201080f010503030d0e01020f04030c05030709110a 76
    0x8070541a5004001007145560741d00741242d2041c040b54007590348503520951082404140c0300c0d603900c101c08ac880c0e988182c94072503032207040c0161040807a0309882c0d100c4c00c0d541020352030041c8584c8060f085260006003803091120b500c005502c02e4031414404e010645691126014a0081002c10540c40b03a590300709101441a040710004035034459001c984071038150364005001861800d0141020600006000b10b0801580e03026543c40314404001d4044202c117501c010781304410080c142ea03c0f0b140d6690100d0341495400203d0420b030f210150005410307181c5044c3d001c0e50782d400308220501043c080c01c0b40d1216480c10b0800c40c1d01c4404050018001d901e850766420040241c040c0450210080030f0001c400079030312002c058940b07640200322000034185180005844448047d00325070b80301c120380005000c0c5450001c1150301400410300c0009484c8a8038440600a000343d0b000503421404c0010f001041c0007d50b000782e416540e04a0130786503150354444800d801c503020240d0703000b1102c10500424508901 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 817132580 1250 817131330 817131379
    0x1030b0306010305070b0a27181503020f0102100f1d03030423190507090b012d0c0b0f090d020316030807170a06060e010c082a030f0a020d080105 64
    0x7107a0405d44081650541e0800243e070308d0f00117810400d107180c0e80400c8420820501c030b03281010104802c01a90100f105011b1005030381e0f007c064005c5d0b400c8540440107074820801000351040000301040146d03909411200a403a40c698020030b085424003180c0414840401204d003d590300c01d1040c205001728400c08444040110183d04075800303400c02e040034014107070f440c1c94121440781e40584002810400003100301c0c0c3c441010581003204a404d01c20010301540d00e800210f1145425641841c99003c60807241e07540c04a000500907481c0d1814800020301c0030707010074058a03120301901d20806a80c00102d03030340e0003031640c0100840813814151010030701800402d508198a407602d030303071080014131021031840010740d07104900f55941c2c081000103a034401d071460303017280b42403034003a00d020615180c10b900c82c0100c114102c9558500e003021840c0300c1c0c901d9100c0300e40100c2c01040d00d4075070b02ca900c45400c0039000000f002015004070340c401003000b4441c0b007007203043c0d550050011200300380300c0710480030640 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 817133830 1250 817132580 817132597
    0x90d210504140d08100f03020303090d0813270b01050301030b07020a1e0318050112050a06080a03080109060f0506032202030f0f1e0d050d06180b01030b0306010305070b 74
    0x150071002e5200d0340201804040810801074450440e581051020001480b21551103a5500148401d0030300c0140e8000c411180b8069044030b610490060b981071178140c920030700002110f50b620301c80000541c80000c03170710402d0540560311440032040520961708291041c00c044240003801c200010700000d860f400303d43c1d42011240c4102e070b603649055501c40080c6020183c1002000902001000070164010240d610201c1007060b10400145468000307042e00880c12048040350392a50006100c101096120100400e2050110341c417039801818040c1ca040b20070b004181c2c1c001c0c14400c0104903006c001c20418100e880241c000c030b10355070b6000d1101103201c074207086100040200c0c4031040d000d039804205070198000d441d000b51503862001482d1034504076000781e60800320403130001c241c507621501141d011124005410714554900501c5200c100400f21a040300d0300d1074002d1000c013610210310780e100b14030390142a09c0c03c21001c4040b00425548030024840204194080d07031040c4070010300000a450040c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 817135080 1250 817133830 817133843
    0xf1b02010e011b0f05120a0603201c050f190b010803040b0a030b0402090a0308040602075f040e0a050a03030218130509011104030506010b03060d0506090105090d210504 74
    0x21442e446c4031411401603403092042d41e03c0d00d1060003403100d100009810241404100554809840042a4800b1416603800405503001c42000180142030146451142140090301d24120b14003900e100c81c40f40300360003035803640b8420001203001c190010444042e80c03141010075040040000046019003d01d07410075030001c1d0240300d46800b58513000718480285200340e402503165414104020320b0812240e1082840490b020940000307030214481403040c02d0f00c5030060308005040c01844407140b00032418000303140d44814610030072503840f500c100f00c03480c1030884041c8042ca01d0389604d1a9244103582e809001c540142c03000b00c0c0024020350003000d04180b45050352000e00c440e070700000c050210301c00c0c2c0324004503207400402c020546d0a202d983d2542080c0300d642420103045031901541c80c1e01c14020484c031203500101103581fa5131460300452003c0e50220464006290000324039003c5d08003036484040350711403008c02c0d5a95178020030888240d20401e9000d0000c022010000601600020b801520207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 817136330 1250 817135080 817135087
    0x71e090902070c050405060618040207080906030c040f15200709021602040f0203010b04030308060409150c020d0306060221210f0c0306060306060d0f1b02010e011b0f05 74
    0x300300060000e004014000c10714880558545418403007a200000d00c614820241004200e403a02103080b04900f201000741c0703005071500741b00c0c601200365204028a040e840356000c010005648e031004000c00685000003424080c5507510b90301300342100034070f1090101040032132641281911001c0501c00c03070460b1035004c43e0200c0d0756421031311003207078440c07201c00545102c0f00d00c0c9402581043e014104038502c0c1340234110301e990300d0964442c5482c011400000c080000e40c0340403401e01e41d2a43c01c8040c0c1c1d01c0d080082460000085c1c10302c00004d0488403942d4003d0300036034246c9000d45010b8898007044070f46c250003500301c0c1040c00c81c41542c0b209003d4206002c2401c14007213007040259a260300c1d030278400c00c0c202d58046403c0152500700c00f40030092214101c02420410080c241d120baa09036500701400340c0c1c00c580c54507030f130441050282000881c1c480380705103403030200c0e1b0004081c0d8542d0007050001d80c008001079501d44060900303030f61140d030341200c00001a20101700102d20418406003240242e2400070b08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 817137580 1250 817136330 817136339
    0x40608180703080f070506060906240d05010b0711010305150409081c1d010b0f0904111e1201140619030b1017031801080c0409090b040b0609071e09 65
    0x210f41d00601c0c0d180d9039000000c94071408002c0c04001903500a42d085490100525204000489001940e240440c80c1c21850b03040d2103c2e200e0300b800780da041454044003440a50385410504c225504071200581c2c4070001c09112040c194001e11500e40180d224840030011400140f09100c003030300f148001154598410001a0038060589164401641e15084003103040401c0c00000403c1443c8003022601c20f904d00b05a40395143d40d041940d00450304103a0744640240d440341419204030110005580d00300001e480510401f021003910480000340c00c80e400c050700c0c00031820031803c882860407602030300503014000c00d659143c18213070302c803048420916000c502a180ea03115208201d042d905210210003100702804040b092580704208280e4100045080060111104404d0441241c60b40d0500c01e40c032001c14180301c904421a0081c00c0005030030700c00e01c505031411700050141101c0c1501e595070f032a008036a551808002541c000c204981e100b010032861a10301d5650340048030307a00d4003448008000003d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 817138830 1250 817137580 817137593
    0xb1605073206010f090f020415020a0c0b09030c0637021504080306010f110114040c0b040807060e0307030212030c060c090d030c050106092c0102040608180703 70
    0x1000349803031035070810080d00d01880c2052200c1c10700071401c890342c01c2000107100f45030750802c1c21400c42d429541c010802420035080b0310003d01ca150400d100d0301d8038070403507620310715000110015210700c544903100d800d40d030740c1c001c02015008520000d0b9040c2c1103100056060700d008006081d258146500d5640010b00000f0001003003840320091600100d182e03009111a650180450200c1a40e0301c002a01280b44c80c1d52000d62038800100849e0501282013094640d46d48504140380c1c103600d84a008201e8248100c0b543c101e4000116000c50b0004050000825203042040c240e908a0304004003c1c0b0350303a4200f5105440c1040e041e031106800d407161450010160303590f83c410585216030786001e15528005034980342d090101c010081a22908200440c410303948800200030030050301850b240b44180b2840c640b0a02402442d40318440c2c66080c03071926114038202c11020700100b01042c0181c010310541caa401800d038012881608042026000000d29082c0a04032050b810103002e03042d0b52400703072070f030f581c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 817140080 1250 817138830 817138853
    0xf0309010b0d0c090b0108070e0d0c0b0d1a060a050304031b12110d0c03200109050625020114040b0a0b0a060333090c170a0c14070b160507 61
    0x103491020f030041082004540c3c4d8410f601d040301003881c1138801c3d85070003040034060162010702240110300c01004501400b0002030a0009802e450f84902e988681c0012184040c0c50800c0c00c602d044401c80c000c855003840c0100071a803201e140350b1503241c01c0d41d481c2d84060f502d50000300800540c0811030a2020001203000b03a0840308a440c540380e1109004c1400407081c940045590071030309010b0720521460100e90008010a04140880194041000310483c0d80c0c2c00f520012a00400d2446070f00d00b030102013400c501c03400328500d548602d028051020103908900341c0c0c5d07042c1c2103818030a4000c030116020926203000d59900010603000410312195038000301c0c1c80098103078032450000e540c813001c09961107075885020030503002400031184200c0042090018a00c620700c90440341d1176981c082c24242d140500c14030390882003826020b840e545043c1c6104000703442141d03002d4002600b0100402c044441c024180c0348050f80008112025581d0884046428059552040288803040c03003800e0020340001e500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 817141330 1250 817140080 817140083
    0xa0c060e09040209222f060c0601092301030f0201020c090c0d1517070905130302030f03060316150801090c020c010e130c0e03060907061e0311120720030f0309010b0d 73
    0x101559082e446110b600b06ca03200c120340c10301c030b502d0402c0007154003440002c0e90350650f150301e540000c804403c0c145811802c00354030343c2007005654a01c000020320020024418413203000380c0075070f08002a010b00700840c1c903000711080702c4540c40510010707a4641d8141e100a02c40500d002c0e0b0b09200d141ca5a00c1c00c400000c82961803402640076502c24400700646018031078104015138644500d00c52141d40103901c80c091200262070383c100c00700c00201140d0b0f007008a45080c0c4030124080002c0c5450754446a40010300fa0488001326106c134000051901451082219441c1c440d400303050400300e5800111541c109140c401548640f039901c001c40d01546501c00c244004401d61141c1d07010320f0404090505080004001062a4201ca0010010305402510040d0406d10428801d5040c2903080000d400410112207007002c400400b081d031600c0100095842802000d4980f0380712450f18521991410501e01c0340101c070b103207800902094039021655006140c11188180000c281c8652484c042450500350010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 817142580 1250 817141330 817141373
    0x703032f010f0605011809050a140c0c1216020d02030f06160207121a041b03080a080f06060a0f031d030a08011211090c0c0a0c060e0904020922 63
    0x14850780b0a0503a12800380200030a00344042c00c0c1c00b6284804100c0740d0184a1048000c1e2030b9800181d640305640d00c10701016402d0000d24419050503054102c031030b001601c8032007480c03140b100700d140310942820654100e148084041c4285a03e40e03400d00045140c3c070380080f0303010b100e003a5084102880034001d0503ca500c3d8000141c10140c121940245400080e60040844c994862032003401300301404c010b04d000c48040b00c40340700d66131110302c0c0c500404580d0209503100c810007900c011040041c01001410b004113143c0d5410364545503280c980c10314040646040c3d41c07146080041d9038105002d550200710510b410300b800219001709540300451562801d82821140e0400101c0509440c1c10504070348c003501750000b0205035200d007999200f000b818840d110603c00e01110000038994081002244c040341d020805075901d99a4500e003210000744907000c2c0300041000c42c50b0a242904003050070030310860f00100b0034145038540c1300d03030a450210700c5c1800c41303440e411044520000c2101211000816100b488 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 817143830 1250 817142580 817142591
    0x90c110601090c0f0314070309051005070507152306190803030109060f0b16060b030327031f05040501060b031806070c020607110307050a0b04050406170703032f01 72
    0xa0040804c445804c0d01070a15152104540700895513210f401c1d03100f071041c240054408454141b86240c0040c85468444003401e01b0200004c036684074000e0050648203c0c001192041201e034120306503245064060311880d2140300c81005580e031a001c00d40c01c00c0340039000b402c1444500d1540403401240e84c00c01c5a1517030001004100d201100c1c8a100010510407190749042403c00d016001c03248a56140803140204405113002070024980c410a03001070001c1c1120394842c907103000c130099503950420f6440004810f03400004142004608800002507285c1100e80c0e0000000401e401801c0c090010740d220f42d0f8410000c03070320f10010030007140100c51516030b652807855114005441c0a034000d16031070030800f00c40c11900041e2505400e940ca82988200741c88000f041440100b803815400ea4000313a4005c26aa40014481d8030a0000b0800c2d030302d090340e0a100c3c2c5501c400e091404e0204001542001e03034003181c01000400d200c1c44840c0e80c18444948203124640d070501c078a491829401c0f5440e510b07655104d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 817145080 1250 817143830 817143851
    0x9180d03050c220e090f060103030e0a0b0a0809010605010e0f06221e080a0804060f0314011205010506090c0f0f04030b1501081e011806050d06020c1605060301090c11060109 76
    0x120b10b00e84d11180103030041c1101040c6c007004903100d88041c8001410f010280240d2841c0f5964000349001400401d0521500d5004091004020007029104000b50394a08440170449501c2111210380b44100602148201355454081c0040c650044400082c801d41070341e480410021030f00e0205c00280084183c1070380700740600c00b0f462100c1e01198010031456211614030000942e03031000ba2401c0341d20314241280d482e00c0110040d00a00145858ac24180c00706000100301d684034a445440000c1c090b02c000c000c541d99144c01c2c0301d1801c0003070300d0103515814144200101c00201000038a08000d8643c441e60a0580d00d5640748042d1109407120300c903500840e51461103950303101045d03039800940707010092805105003074004100304c0c040c010803808540144d000140d034800354001c003005250141c0341350b900c143e4504004000390418000c0407001e010381c2092400c042120b850744400da40c801801c0520b142d02c1d01440000a100d815806024410f946061150b83d1800303010040c001c20001e10301069640d0348 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 817146330 1250 817145080 817145099
    0xd1b02210a092c090f1002120a0216052422030e040b060403120809060405070e0a18050d0207230d030509130b09180d03050c22 56
    0x9242040314014041c410144455407095040b003c4a0403409200199102d07500428034038101244048440303000001405044040050003001840f158000e03070710001030940445080c0c1c45044401d003448403103500800ca00980b00e600920524242c0e400e28104601d29940703040c2031404510100d84000104c08000720880c40c003070905680700c1c0e00a092008840403035610042d06411303d401c040e0400450f0900c101054845030b1040030000c1004081544a580e645004014000340421980006488402090000700009200c1c1d00940c1e205e0050310155050a420400042004040c0018543c8850401e0b40f40310301c501d140a030303107030249019141200359aa8082d240c080c290b0700500c01030140140d48051a1441c1c0c10043c008041215110400d15446c10111000d001c1c50b03030000c0d807011029540441c41545607002400500054a0b070207800d5561404681d40d051100482e070b1035a400240340d01d95103074405c0d840240e022031910045030030003501c206c4600c3c281c03104101c0039040c048001e0042c80361840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 817147580 1250 817146330 817146373
    0x7020d0e010806011209150905060406150807090911060f131401120f0b04021603030c0507030504140102070b0406030903090b07020d032003070609031b12050d1b02 72
    0xb82000c48403801c01c50300003030031495822051882ca07692074a001c0101301d035141c51807080412483c8244507100e0141002622004240d80844129240100c045104070002000100b1251071341c000c1c0c84814900318999000d40451002100d0884601426146642e00e05000d4810003075948441a151041d81319007035500c8225400c100d403c0041020220566130344036201100c2900c0400700440c1045280c540800503002008495a10a0002c600001c900c0c40740b41920905074001d80e820b11080302401e00a407000c1c41408400390005400b04001e204001c0c20f0541c1c90040d540c1072040307440c02695802c841a503600950407030400030b601c03079188606040d4420039020150070700707503002880e00d1215400501d081c10200c0d0b00400348405041c1c1d20b0f40540c031156100303410301460f005036580c4140300d00e0020000c007002d1000700d000c1100f06016400306140240d1a0812503802800380d80010f809040603590794014410324158507459105d0460541d00000440215407059002469442c001c0d0100414088 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 817148830 1250 817147580 817147607
    0x150403080f0910020c15010611151501050313140616030b1023041202100c260c03040b0c0111070305030408030403030204030f150e070509270607020d 66
    0x341401c041c0305078240089405511820001e000682c0c3d208000c809605002c09549052030703030203003040002407980c0c01a0390302c80100904015202081400109a0109072040e21141ca01581c0d2a51041481d40180003c64009001ea10305c3c40303118140d60394415180142c0c4015906541183d8180218144644944054407405081c140b140d1123102d00421402c0d401c103e00d05080060b48c0c0741c2015180b4407958440c13850001081c2c5180d40e107884881d600e040359107200049020300c4d4440c000030401032044500c4401c80c0d034013203141200d00201502c01d072103400c00544941c0715101d04100c0c00c1400d19040000304010a8140c40311502c44205e50320303a5084403c209034115140208008800010f540030080340d5019a02000894503920b69007400c034020f0099810041440130001c21880502020356502a101e6128100c00e10400c205504401d84406032071043e1030300141c0c10008681c0e440c2640340b50200401c034480c4000c8200c2e8401010034a02401603883d1800b6802c21501c0c00d0f8801c0c1d1203200c2c40c1042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 817150080 1250 817148830 817148851
    0x50a1b080111030a0c051e0c0601091e0507050c0a0f05120702030709021e07030c0507090209030c041d032107090f0b16140706090801051017070815040308 68
    0x11400940703240030758031004250b050304c150740750144003810f0b014000742c481c0a030700c0030750f8200c190410100b03103501075020036010b075601c1c07282c40000075680d03503d4028110103801000660700c0109503039640c3c1020b0280a8044014880240310350051090100940401a40035030203010300841d150400318103000565121102da20b000304a40000758500140719400c5640300400103030303110141c112040d80000480c82c0356070f410b1746c00650703e014141d005070b400255500820903206290f61b103455900480c443c003501c0d0703501a000815207070b6843c9096803120010620804080c0c09501c0c000491b40d0555110005500160042c3e264034042c00c0c280040007a03108000e8101a0541e07418a225510b0640980c4545001c0c9080001c41c0741d100c1075a2265903806a920440c0f2101c0c2c000440072040e03c0346440d004207000549200f60009680c1c0b01401004c0c014035515801552650500a000002180c401107072009881560000100400c5c00c201230198441407440760239840c189468002e21100c805411030485 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 817151330 1250 817150080 817150091
    0x902042909370603050a1202010e0d090b0a03020f0d0507090806040b0f07020c03010e060603010b030106120f080f04032405040c0b1c02030901054609050a1b0801 71
    0x461051421080d5040e0039850310854600b5002a041c0103000c180e0001006401940560004c10144c80b801d00401d55098000780042442141129036520500003e0000105260001c200700501c003030040c0b031040b00920f000751070151400d618240d42ea01c2100f261400383d5565040180c51940b1032458000341c48a00c024107103608098a40c0310a15401929a849140306d400c04220824001c0041141070340b8003178000c0c0881e443c0c000f10780d601d808007222814043c4d420404848080e2138113103d00000c0d1100300307417011000700158885401c440c82210b422a0011700070000c5004050300500a0303c01588110b0f42e1034020b400c40e9a404420302409407210814038101818040000c2c0030a40250682d07036500c2d50141c44a00f18908180706e221030322407501b5001d1001040c000c9d01841908010321440c6e41d507408405c001c0b682d1500b4101071443c0e0024034080205160403c854441c00840d009031460014000704200d2456228141000340f15182181d260016140d0020702e40303402508900101100c0d0000c009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 817152580 1250 817151330 817151371
    0x1050306010b2718040b06010903050304090b0316080601080d03091203050402040b0a06110c030d021c03020d0c0f09170c01081915030606140a06030902042909 70
    0x5501445241c0f840205101e4440200004441c81ca110301000051400740d420040d044040580182138600b036488418603c00550780b5405950204100ea6002000b10b01d058582090f0200070030311040195414000c03a100302c0c40e1070103c00400c00c050040d5101404880d490016020310b0941d144000300240341c205550f00c0d020400110410860750124100401d0586d141e100240081944208a551101e2002000304010b503000c298401041c641a0071250707041c0e5043d042641e00c200c1c4078101c0d00168410f0000c0050260f25039803080010485003005410004071100c04800c3d03031110802c090000744590210310210703900bc059100200081440a501c803401d4662240e00e84001c003401b641441a40e402040c08114403074181c101e00c0080b200d00700040c0e03901d142c00219603e0248401e0b100ca90815402151180d88030041c800c0710b4400030104841146440c006034040c10940505a90040c3d03120003a80c5045816011900504c0d04c40c0100c1c00c805105004000c03c00b10040c0207400c00403039440c041c82 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 817153830 1250 817152580 817152599
    0x160305060d02010f0201090b360d1805101707031514061b0105011703030f040b04050114010905090f07080703080705030c07081005090c01021f020d0204030809090105030601 76
    0x110202d0702031a1403003400e81107400c140d0240100c840c000f020b2441507020420401601130014500d030a8503800035982c00da45500747c1215a851070101813498101046605a840c0207044817203e20310a180641c81a40d503441c0050b210a06d4110540c000c036200428000d1198180a0481e90151290404020020b40c4240e107800034840ca016558410150f0181c05d03140390341c0c40c0207a070070b01044046900000d0018a21450180c082031045c80020240ba8102203496000401601d01c1801e05880242c0e15680d04d403034241e04030310050410b0b10155030741d52402c05080c0580304218082c0400c105c0c081003509080c8265864903034844486400c4d074000c0c0109200c07005011688004490700101803980390402c5050081c19031050150625151103908800160303000c02150404001891440c01c0001d80e86500c14640c0310381400050310f00603080b221106022580e1424040348015540c00c0060800e4010b017802e01c01c0f80d1041d0421355400101058141c040c0c903000c04024003500003500035042c0c0303525148061 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 817155080 1250 817153830 817153849
    0x2e0b1008040809061e12071b20030604030c03140703020c150f0705010c090e04080d0c03150b0306031006050306041101030b15030a060911090424060816030506 70
    0x20500380b400030318000b0075a503803410ba5141444410100e40e021840310003000c40c9612003580c500d03064190100041e005405044140001c210307442c2111811002542c60042c603d4070040091203d40c00301c0d8420324283c8082142520480c46600d540e030071480d85007006003484140e103105104a2030204210740007e0b07408190b000c16101c050b141d11208801c10307200035085004601602c0d80f000c0b40807914505020054000f0180c90f15a0780710341341c0e000d449004000751402d0446001d05444401c10450103070402030ba121039005444c1d45800280024207070300405e01c5000c1a84079603010600403003440046d20f01404461015124540c0c01c0000b60b01c0d102c04242c58680041011304100220342d80403820340d0080c1c000e580038410081200c020140c840040200e96003054840e140c859140c1003001c0f51603c3c1c24032500501c804d0302e110013410b003030788442000b0240c5510320304034019040c8038030111100c56035041410301030880e030b440c1d05075245000c19480c0180c14050001070101400c080c18441140c036800041c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 817156330 1250 817155080 817155083
    0xe070c03110f01020a170a060609060c02011e390f24060602100b0306060f04060b1204021315060807020f060103050f0f060c0f03092e0b100804 63
    0x29220304045468681404007440e42c2e1038040d4000184c84240340e6000c542e560510343c006241301219116a54540c0444005005400c0400d0009105020030340c000c103040000e8a10500d0000b44041442420301d445040d001d00403030120b1400d03480c0300750f6004013801e040c4054041d01e586015100d24404010854800c280c800f9003440e03149150032061100d55100da41041c1800c0d611507010380e24164180700141440c1c4150b0005008551289521018600500c048010300070001c003255126002000b078031010900c011907000e42d0350000080c03449119005001c4406861000c0c4d591843c2a005108008513605011101585001200041001c07240380140130344002e03150a80c16551800403d0b450030201c000c0c2140700340710f1034000000b044000107681502d000315109942c0300c684c100210595880c0c081c1e500c0c0c40684002e021047c8040046c501444e8444204000c403010000c807080138800001810003c2440004108860780d10002503000301260f00307405032a0010441ca221100520030a0040c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 817157580 1250 817156330 817156337
    0x40f0e04023007060c0c05040219030b0409140102090a05060c06070c0602270109060e060f09180a05010e1b030f07030b060d020d0606140714070f0801050906010e070c03 74
    0x8007400c0d01a68807070195061400b91044a18158680401030803041d05803608031030703440c0300f440081003605080c001c0da0841c41d0040414204080303503081c180d010b018004c1c0040d41281d6030701e0034140880d01e81d032002425041083c0c00140d13582207440c00c0c866030001c1c540005000300b0f420010625201d2002071a80d5002480d4074002e003c00b0303c58641140a40300e10000b00c0780e400c8503820b918800ea1004814010809402d8a07040081d0b50380c4c003000d13908450360aa426900c40e81c00d02144c0c413017050508c000c200c03002c002441c500100b1007030720702084054810368007140040c2d4de9100500c0405000260150003031080c1010844012010111a03a103100c000c2c0f50301c0d04d500304400402c4216009030072181020b180200b600741c1380d289005245000350450050704142500702400001c109000341d800340c0500700d040c1c1019240c4246c64840c11544010840002c031184a960b100248804001c08a00d000d41640300020840b03040903440c6ca49840c0040c1c1040c25004023110034005000e4028004614845d450705 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 817158830 1250 817157580 817157629
    0x122706130314070602090415062f012408030909042310020d060f030507271503050d0e0a090e01200702011103030c0a20010e03040f0e0402 61
    0x2030122110600c102d8802040c440100b502020015281c01920f201712040d14200700348018841000c01001301c40c49404081054004403502c042584c0050080111510b070221500c041062041800c444013021021650500101586807120040030444010075400e401103041848140004240c8003000d071004000100c071110100814800710601c95441c076200041e907215250070b02210002c1c0d80055809003196140c08000310310403030042040c1c0f099076000710007005500e081c0401e03268140c000c04a134a03c00942c03081355501c0800c050244e4513045241c202c0d1900d805255280c01c51801507032004110502c40d04211080c255185e4030021421a401481c011403107510440c005401000c01069034000c485802c42501440300f481001003c042c0e01c00c3ea03034040000710302040f06499000595907004030701e42c1040b0005041d8881d101840ea6261610300101050341c81640e46802c60340c00d040340304090381021508101501001c1907880c02000c1440040170b15140c5030740003030403e41c2040300a036005618130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 817160080 1250 817158830 817158833
    0x1030c052205040503130b04080606040209190f030309080c0f1908102f030a0c2f0606030307020d060905010209060c010b0a090912081b12270613 64
    0x141c400100c1d80454030200120b00b49070074000d4480c2d04c40943c01e4450b051029001524110480455046555030409442076032180c90400004e03600c4149103a50000a03000155000a84030725000001c24880e207200c00d07128034510740034089901c02c5c1d01c000d1035600002c040d400c860700d40c0581030842120864441380035400d1b4400342e07550103015401c5440c2c2c40c03082c480c0c0246841075503031195440020001c6006070043c00414034120000121810703001050702440490b8110358641c2003402d41340034030700382840d0030584c2980121078880400070760030240c0001110302202c0342c014850320b6085141500038503d444142e4000c1200100c0000004002d165200a0b40e41840002e5043d40c0386c03818010001991448000c0541e0301801c0c003200102d204805120000888000c80e11032804150f901c000c5004282425450a540d0340d20010103040c0460a050513660560000b40700920406072002c0750070b003080c1806000c18a0903050b03240402444955038603c0b6484c514002101c43c2e1003403090643c141d080d62503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 817161330 1250 817160080 817160119
    0x4120b0601180909020f0d050304030602070501021209010c030501080615010c0501021e070506070c02090c0706060b0c07170303090703150e070617250f02030f0304030804150501030c05 81
    0x200000c2c52104091190042140c40c004d4228a00c1ca5000315031001030b003900c24007080605218514001c0c10350f4001c020420014500740c018100080c000c42c00142081c00c2d40c10311450581c0100d50080d510303551400340340c14142e01442150f025094481c0100854a03000c2510f0940d20303502000b1074144043c611219040013025011034000300041003090004155401c0c0100349078200742411610b50250000294089104960b50001541c0043c00c034001070302d6655007c0d2040e8000107090f9081c940703404c1c0100702120180c00400c0c40c4140f0f58018440c5070303d4900b00c8103400341140f40b216407d130401c00500600d50070010f24a002d85e40c1060880d4646000e009030700c4c0051080d00400c01d07880c00740480004200d5000760b882c002010f03900070b40781c182d0380e55048000300d00a50080c1300da2504c000d40344205900303172260000079083c01c4140102c919000d89207e402819030400c8400720300003800d8504020070481c543c01100603990349188240b010394119a220443c0c200c5600816001e551071100e8009280761 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 817162580 1250 817161330 817161347
    0xa020d06170304030312050601080103020d030e041a04150b0f0a02071701050f0a1b11420c0702150d0e0601061d0f2403090309010806040204120b0601 66
    0x318414020101e400c12440039126009480150081600f9806070403000700e950040340c1c0304400503034030024240c0c219801c002e0b1030840110f041d410018030501c01740c020740381e40c8604d0202130325907984841c556482c13200700003c0d13680f42081202c2680c001d1104004080c1a1030950b00c0031074426580c02d45841c03015504902c1d03d50194000841c00c900804020110141076200b54041c400610708840d40b83e440079000c500742d401c0410460a1000c01d020000c54003482410400400324080041d00c4010880000749207803c003c004c1007450141c40d081c40c0f05840003800d0041785090703034200c49102051906402c085400d024a21019004007210044030208005010031998043c55034101005986411261240d4500c002d01900021032840f9180c3e0301349a83c00030304182640c0008101a07242d450306000d00198802044181c0c42d07042c00004070740400c81c4800302440c03044800b00000c5071075413070540004150103806030086018520400091004810002c030b00400d583d04080110415150000101c81e0500c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 817163830 1250 817162580 817162589
    0x105121b3112020102030d1a150c010b100203070b04170d0e011505010c1214030c121012060213030203150702010b010503150402030612010c030902120105010e01170a0606090207061508060a020d06 86
    0x2705151741c405040080b400140c0740c500302c440c3c000c2040307500000c10712030020031140f01013000d81d00900c101400102031135906940070b4071804c0c140d0501d4845200340c1e0a03e401c0b8400e881c00c03c03074840e2004010a00b09216180c80c2806150522420615040c00a00301072900440030f0000c400714440300b80500e0003800380d502003080016096949180c410090031150f00010441a448000304000c0351038000000d0800c0162008040c050781550318a585440c020340c070110921035007500100c070000c0940e509102030854207040d41c4141c83d181c81d144000a0231145054080ba052080c28014000442c01c40106150f204005070350060b5280c40d141c1c0041d0804260341090300041d82003131401c1ca40b06915800c8503400a100341c07034610101c40401c0c08903090f01c400b40100052450340b04010810f031800f0360b00315035001e8095403d0751030482c22610380005950301600011006500000d120301045158400c20708824134017008440d000f42032801e51038031001d02408842680b50040380409400d42690f01190040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 817165080 1250 817163830 817163839
    0xa03140103140d030614060c0f030d0618050c090f010c02121b03060f3106050f090a0c0b2101080706030b0105121b3112020102030d1a 59
    0x40da500c0c50600040c82d184210400203024401c641201e0340d000340502400d80744a401d80c03401d800c0c030311002c3c0162a004400111814402d05018034080c1500780000c020090364080081517141c01c00101d503c00c0c4800700654503d043c54241000a44100070003034034111103040f80c10f03007a51201080100c07610700740d520f8040c3d840181c0401034115035000080c907050015100120a20410383c181c10152601400c41d580b0820ba2081000107050031202a001038038500088540707440001c0b090f0217071a045c92070030400c89106589900303101261081e84070145d03000c1404002071168890700d54803d800700c1400d100c0d10203056070114085409410010720400d01c030003401c00c2d5a003d980e5904281780e45483e503226982c0400d15120303080044d5446038044030803110000c10064840e803034006840b502032410003074404c074500d41881440c00151250040404c620580c40c203c40280000b024207014035121b95000c0c80c0d5440c000214500181d802006075030700c0314050714000131101200d50410b4010380640c2a1035522 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 817166330 1250 817165080 817165121
    0x31e020709112512050918220c030b1510030f0b1005120c0f0313060f06090b030f06010f2601060b130f0e01050409020f09161716050a03 60
    0x50740f8002c040c0d4145805180628801d886680040d19148203055106030040054201c00c01ca0882c26400b89810501d0a501040c100d0241c041d0b000805c001c0d0081280d810440300810001e11560700215604409012102c042101c1075000180d07042c0385285001d0241038a4001c44100c00815500120320b480000c0c06280c440c0c1b82c020001400b650103c19084079002c003200210392100c800724243c0300e0403d54090207a00e552900c40c240b210b40b2010210449a041c1c4524660780c0c900241d016040017084d441e04040790081c000810142000000742010500341e01c04001008a40306001e01501101c0e807070000324041040c0d230480e039610070700d44000c0c40c03080f50700b0000005425011800246603121440d04c0480710952a0507800700e0921080c841c1039404404600180494a0258081036401e84014501011200000c010900c00c400031550084094a11520280c0c007a4100c0f4a80181103084402c0e01c1061401c207514400b6042c00001c800200500070910700200c50090303021820320b000c9004a11030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 817167580 1250 817166330 817166377
    0xa0c0218070207060201050f0c220914010302030c090405030d091b0b0a260105010806040e0109080c0c0303070c0608090a0611030106120216060e0312040b04031e02070911 75
    0x1902d83c0300b032013484019844c043c0000c1c48940756120840c06990748500b00303072038844052058820610400c0c4c0c003802c14070350448001403a02c4a40b00d050080390001100a080b91715600400d41403441c12b82003680550a40340c02c02c80051404070031140c01c545003030030005a10010713040034252918200e5440022420541011940100460142c4100046079035100e13074800300940c1c02c0c403209005011039a142d100c038200500c000d40c002d800d020f903ca500903000188410480484c2401d588440d4002e0b41c04400006245582c0d01c030034810295484815002517144c1041e03580d4001c065140c503c00e5100308869000070500d131107000d203c0c80340c0e03580d000401404100445801403500c1e510a00c1040f010900010047c503242a180c003d444082c0511550030640382c0450300c40d24041d00c1c0c2c0e00f40381d83c418041006888240010742d10464055800f5451080e5a40703460b140180085000300740b00d40d9504220315002c80c1559000071100700b0b65808140105805441d80c11041240c02840b01c1c510812041e0142d891 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 817168830 1250 817167580 817167583
    0x1b080d14032e18091e080a140904020a08040606050409050c060a200c240a0e0f0307091a09091b011b150510051e12030f04170607050a0c02180702 64
    0x103840d4000d500100d581000810f4101490009180c000d0002c4010b01034070301c03005d0199248c0380340c0d62500c1415030300d040123078070004e0300306d074401d01941000c60106010701c17051244520070913010b86400c0e10100000702998640a1751030180f146a03e100b1032001808010702849080303400014802444a544207100110b80e1a880741a4042d4450080903000315002c2134016000c240e160140d00c0241c000d24000b0030500443d000c002d1481c10540042c50440002c00513201004148018075450400142208484100115007406441c0041c0315542c1c0d0300c1880080300011800840380f60f0520b03000c1080b04481e100581c3d1221036050101c0120300f10040000612a085111215507040041d04020942d0354112450000c6102e002e4103030407244c95440c1080c1c1c0c004001f100c0080c1c440045c04802d001da00d89032000d25580c040062103528040119003086000100120f00102d440a01c004c1c200524102c04001e066000d850215000c018000c1c40310001d64962107100802c0e40b401411100c4980b0b400100603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 817170080 1250 817168830 817168841
    0x31911040e07020307031b020a030c0b0904060911091c050102040b03010302030c101d0d0503040602010b2715180916090b0d030503041b080d14032e18 66
    0x1010401d440000801040c0302004440308264107407108800300810703030190f040c40b502c4401c0498100306c0116010001c10034182e0101e0040c03003411803003591401c680b81070209844059108140440c1003080c100e01c94801282601e00d4982d003030360004d044076140103011400d80c1c90f101001d0701a500c00580825850248030003181a2030080e412680c0c00c3e001c10082c48a11070103407544100140540c1c541c6c0c480041da800c5450b900100040003404000301c0d607180d17641154001c2e440400540c2d9281d1003021582415046641300b900700d51860b100444400c8107000941d00014403545003540b14021124141d40ea6800400034800c6030418400b8514014210641d00d02c21114062034460b840f6070001960440c070f00541401c0d034000740110003900700658084d03030341c1e800191003120b98441c40b8107100b40d47c145c0c02c1c120600400f40c0000909088040300e502a10f0300e41015600481d98004008009007052513084002030f403001c0c0d40c0001d51a00c5107004202c5806200d810501d80101d1130481c0c484080080d4028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 817171330 1250 817170080 817170089
    0x819020a140a1a0f0a050c21150603040b011401090803070303050402010e0a0614070201170c130e1515090418060501080a0f060f06030206040e07090f0807030803191104 74
    0x2d4810b0f02d0920210980c030741142c8540340030040c04002891040141c001d0364210303010011607070401618550341c0d00c1922240e803a08441150132804c019006000c046c004883d13003015106a4514103041d1903403200920140030307c000080c201484100c15034031558001009240307000540f51520782e140380c0140500002d9400740d00181c030364030301c01c0a00e00e0125200d5044615a803204000c801d0342003900300c140d811007882603051141819000040c0020420a60b10850040ca0001d540e03040c3d41d6100c49489080340c10a01500081c1800c200103c181c000001c00c65080480e000c1900c8414910340103030f117202d60b82069402c1420404818540f281400e1080440ca124481c144401e07a25022401c0d5920030880340a001400984c1d01038020034456440041d0020369a100840c0d03058894000c00d0055000c1e074410402026880100041d0302d6010303101c500545000300845040520f4902c505556840f28000035001d480c0010201c5c9020011041a1668041090043c00b5000112140f04600d4100c3d104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 817172580 1250 817171330 817171343
    0x1050a0501050103020a27050d0503040914011d1b0415030f050402010f18050301060b030a0e070501020606060a09051002030c070621050402130e010b1c0819020a140a 73
    0xb15466009000355a011103641e91080840e0700000c500840e0351200400400d05480d40940210310b0b51910102c0a000c107011f40300079990340e45402c190508035a100700c0000f000c030810700c0041c8011042428031f407404000401800c1c1c03036a10b52143c0c0801c00c00510310b00401c2c1c0b44001400051203801d203101c0b070403004100e450400903050b58a142c00c099920480f0024001001404c04c0510b150140c1d41010100c521910b924050340c0e114000b203821952240c00c01500c62030f02008028806180307000e4422202c1c44000501030a0f4030f000c0010b0355982c80904500e01c1120046801006c080c4101ca0420090500510141c210411200c02035140ea00070842815103000d07800c40403460602400d0035000d456a41000c44224400101070700005000162003240c0c0501c0300c0c162182100d420703010b061040e1040d5030000444c0008101088812070032100d00480254004040d100490024825039400b401d9a0b9002c0b072030554044801c0382007074620391009103102c40900c240d04241e0300c009035500080c0d100e0038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 817173830 1250 817172580 817172591
    0x2160b06180f0c0a0c060e0307140a020f2205010f081e0304090c11030a080f0709060215090f070303081f26030f180405070c03020a12020a02060c01050a 67
    0xd200d905150044910092020402c00854220301001c0c000300039401302840c05200ba40c0040d03440b08160303400c000a41681d40d101090100522015011103422402000000c1400c4082d039800311301244410280244125980400c4980c4003101442401d07090310a048100155a101c0e403203c1e5490174240207010341032068140c00810140c42c0042d4403c1e8070b083e80015070805140c0b542c0b51000e802c0c0c0b85440c9080004940c0702401c0744400300082c20880d01c61b62580c0100d403030560b10305101140000c140380c041008400040001507000308007031031504d0344005141c102e0307502d80803817034540600700300c0490141c8600d4400009055000b0b030018020041d000c40800f00c00003030300c26604045400c0c0100c03e150044442c51043e058017001c41441c006940c042030b20300b45040910310480d02e400c890756561350380b0200c80c0020805d1500b03124696001c960307402c125080b251076450003552020340300e01c020891000c055503141454002c012110805e030b40144460344d01c5c9804aa030764080c1c07605441d014089030428 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 817175080 1250 817173830 817173859
    0x40b03011508062a0d060e13050d02030f0a0309050f031903050a090c0501050a170705130b0a2c040207030c060c0e01121a0301150302030709110910020102160b06 71
    0x3080038521041e4100c40440300c94404c10301c4a4884d80c082c20410301c14550b03610000034299000300c0032900c5580040f210901903811400c000e814080c00301d0b0f8050071034204200002ca2040303038105450f541c0d43c1c640340000c1e030740c901450b00904c1d1020001c600718880c80041032180704e880401c00a4150712036907503014040381d00c5502d4400180e1b42d0403a801402601d04540074481e0703520840181030315120364500030803060100300103100c04a50954403080015800661862030400c0d032080c840003403000d9a0294075018080d100103041444d0780c14035100d0802c0001c4002513003041c4902c0103103000340084c000c540d120a245400351483e440d43d541155441e00b004c03104030b5540d0140741500c41e45901a10781d0725001c01da0000d004000c154047d94001c1200190b90700c0c20070303504c0034402c4100410048585608460a5004040c60001160320000026080040d124100156501039410045007038545401c164030701003041e07000e8060820700c28051071305800c070300d414000e8503998613010f22800e940865808810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 817176330 1250 817175080 817175101
    0x13150f030206040b0315040c020d021b030303040611071a160e0f091806101d0915130609110a05060a05090f0307080d21020702030604060b040b0301150806 68
    0x991001030b50100c4148410003280c441c2400860b404131200381d441000107450340024085410303c00d100030069002d01d42084003e50100103421b241552048038207400e46c03080300025030340e10004000404c0952100c8100020b5030900c0141c902d0036500c100c0d1800030082104610700400c2044810380b040c1ca000410b0f01003c9800b89003465191034000c1d0181c05103185140a220003c8000340c50f074181203601d07441045254006000780c40c082c04040311301c030001c140350107186c943d028035911481d20405003071000d1000705c810010f80c0e00890311024920184a648141000c01d140c40140740281250f81090301620400800118403420b101003116264170264903507040c44018014000c4640100d2002c10561110f850000344140e900b100040403200a2921256124104030203d24280701290b540740c50700204030304582e0702d00c0d00302d59450800c5092401540000740c0e00c68000d0b05c0a84040d6642d95402041c0e215a0480d4003201c6010b4024003081c0440c000b0f50300010000c0c401c08416000383c1d400304826003031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 817177580 1250 817176330 817176359
    0x317010608041a1905150411070c0602070e010909050c0405040503070209070905010504030204200712020105070c0c090b040e0102160201020c18160513030c05090f10060c020109051315 81
    0x19001085003512841800d90009142c0a404401c49020700c00403000d1b555502d004100107000c0341d00c031041c0c8400c0241340513100030f03071a038101c282550000e10083c4800d51182018604503004000007203041401410840d050102540c5410341250824040005204000000b8107009109036115040741e660050103e400803618011980014002c100800241c030385504407100300d006a0180040d01c060010442c01c0d181c0c0b01da0300c22181a072007101266159502031103040d901c80e1150803d40c1c0b1124242e5240d00d1260070318016100d50940c4e849084030380784c030349900900c03218202d04021555a0240030800b03440c04014001240180310b0741d10000c460f4142560040744445602c2c180001c50b4903001c0020b15520394080008040040c180300160603c00d5a000c07041c011400b601c92030409174204000d1280061000f4410030464042d0703418481500340704094602111300340e107040c4c0c1c2c40a68500c0103c0f00382901e98001070f4465000c0041045206107988140a0010400409050310b0b03a2000322255400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 817178830 1250 817177580 817177591
    0x180e010602100b060a0c050f030706050910050108100906180c08120915070305070f1211010207050606100e0405011509080f0c04022a0a0b100e060d0317010608041a 72
    0x8402d101781034046000305c11001407548a40c0c03d84030f0719440c12120b98a5600500e10507107029456205010501a003401500c54180606d04288080e42c106042140d0328280d1001c1d40d02c1a03555154000c0500041d544900c000c86000da480a00116803810000d41c0d94000d8016146180285035007190000c03150340481c2d05000b405807900340b1181074140080402d8200c18800d60602c802004108002492080c03090a00c41c0b08600480d500d00e00480e00030412240c11400c0c0c0d04982c8100076110101c2d8001a480703500c900c04440d143c0306040c07001011a807080d5055542c0e80c005091000100f2182203d000c40d40002d410f03030340c89031112581c41c11407580d02c20b1a440e114400d9000b02c03002400e2130500780c004014400780c102d140c2030458100544000d403408061030b8280c45401440074102001807410300c4d0b6800c800e0655070f0a00050401030a699840d03c0544100e12034480c142c00c14041501a05001c422205001c080d2804e642e542c0364054036404d07045404070341c05440c5808621003241030007030080c01076 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 817180080 1250 817178830 817178839
    0x1503010f0e1504050f0a031101150506070b04050f01020d02191b06052a0702010906080603030f03130c06080711030f180d0c08010b0f040203012103180e010602100b 72
    0x4444002c1000300000040d00c251001d0080240c4041840b0303003000010081c034825a5000d024044443d4071600310340d04801c08088130392850100300701540c0c402098404280d08032800f40b42036191498405e00d41000c203803490304954004140c2110b40710f10b03607015202004150f2801489009104400c036600011070140b01201e0300910701d1070020a4047e0b20513503010581a041c003c410f02000c811402041c4050141441d9140c0020854115640407030300000503c15418412194184200002d13160300601c04528031a182c084001415410603051310a0500c1c1c103d90012160307910340c00000c2480d0002c0b25004041405490702d913841c44000011206103c855040c06420080f000030030380e2980c2d10b00900298003040440804003c681d41d140e8a10040c03000700000201541400203101e0b0500e01011014030851040c401048002c3c40c5e085036040c86040e50381c54501c00e441d1403a06640c0b1483e52250310f161000440c030041441c540122089058a44540840f000b1207030003038500f004ea80d000308025400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 817181330 1250 817180080 817180093
    0x10f0b0a0b04080a0b1302030303100303030f050c04060f05071403030702071d01050d050c040501090b040c020f0606042703020606131b0e0310050c03011e031115040e1503010f0e 78
    0x114041e49681a040000c400b000b0100d01c1058000034527507042511b02c0039212a9407041001019018412400040d40d181300030300403440d0a540c201014000d034407901c1c0500c001c081240b070484d44104211181d490b0321102107083d040d0291201c5030359810464034100584100000828440d8183c80c8040110020401022040c3e0804092000a120084080300d06124000c0c0071212070383c0301d000d424041c10340c50740c0004251840b8403c1005880098402d0025500710b0303134481414080110f4140d52254084e84e02045000698032800c3c02c203801140c03c441084800d803a803104041d4046103c0340245812036007003004100d401c680c0301c116055103c1ca90f000c11060f80c0961241070040c2040210301400405a45411100044240030742c4c008440b00c42c0f00d1500000140150301c4501c480c6501c540c05a10990b01c8103003142c1c1c0b80010b441610b100244a560440405050140144120703000743c554038160010300e05224000b50160382c001c0307011511a50030320801801240c3c0074824140c4124031100104030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 817182580 1250 817181330 817181333
    0x2706030415020f1903200f07060b150a0221040e0a0b01030209040608070305060907080303190b0d0308040201090b0a0c1502070f0c1a04060c1b0503010f0b0a0b04080a 73
    0x2540302c04221046142e050289103055483d0400da95004e50315a280440c04040c1440750625510720044820502d02c018051a02c0c010041c50942d9091a0b000c100020140088030004040312102c0f04201c1103564001ba044040c1c0398045024401043c4503240e0555510404003d05403a00a60003110034071500c120004040305100c0c0c102c61038860060600600c4e10b26014041030a031007094101280642c0f0040b010000c2141c20000e00358403c140348045c040203410128080c0d01c81c030000c1c000070000e08150a40a1074a03407a03138040809090004d00921203104280707030103444250200c4007607011491031900013640c691410225444d00a0b280d90f0542e1040c140c0d55594090304c8142c00c028074856003803002500203040052000100c50241220700001460030407415a0a40311115a00d40034806000801c201070300000c01084440d80000d110364046240d1800d082a0406680002e5241d0300701100c2c081c810409900099058409490401c3c805403505800b10b8544102e2103005210b60003812880c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 817183830 1250 817182580 817182623
    0x120a0504080c0a180504020d022d040c090302090403020c090a0b270115120e151302090c0307180608090c010c1101030207151a0108010e04020112020c1227060304 71
    0x240d01c2031006223043c40b10030160300861f00e0360080c444085424001d6607103076150380d0300920b03441301c1c8810225020b00401c0e81c00c07000103103020f81501c0300074081e0304400c0114081600034071401003602406070a6900760b1800d00300140140c4052a070281c0a110b0310311004803c40501c03800c0b508548401c0e411030205919000785803a084000a40030410030102400d51013034441140100d00b808100e80d40102000100614040b9034110003038042c2c6031401032003035600c00584694035060b80c021210b19805441c0d0303a41000035204142d46c0420402084104000441d1850300601c00601840d4480c0484860420000040d11110142070000d000c2103103004002e1081d41c40380c0c00505850313108000d1102248100d1100300c0c1519041000c4040130b44520000c0003a03564030041c50342c0107190710b8801ca03c00342170a40010f40801c4400080c401c500742c001490740b040300340801c0008207203003142c5c01e00d6942c1d040c820104038075007400b1000b0410200e031100f504d03200342c07514509403030090750021154602900c4c007400b820b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 817185080 1250 817183830 817183841
    0xb030a0c1a04080307060902030d05070f080a1707030c080603012009010302220612020f03070e01230c100b010f120b091806090102040b07080903120a0504080c0a18 72
    0x4104100b00004103e0792410301c0600f403103d1250001143d0040e0500c1050305101c40a8213210411405200520100f200019804021604200640d0740c03400d03541000c86d000703000c1c0050101000311034024400c14035490b40c01182603c0781d55071024815120340c07040500303842c20b4003103a23420744240c0f0100314904003503600140f0100700141001450155103003412a4400318500c204008405812010040c2c6030b04050f0134900b004018508524010748106802c601c2d0001030843c9042010030051790119900500301902809501480040304031269048a0b04030750008902c10030a0198015004400c203c3c3e00401c074075810140c5405070409074280c8200c400f81149042031501546402004101d6120b01504a0080401c0d40e82007030031118008400e498494050803203007440c3c1c810807081001080790000d560b85c15600080d06642e50b480f9000080c1780c40105c0c103841e501c3c0c0343c000400c9040c054120300144100d508510076104491100420401d050130303207100e002c0342c80d400054000b046000b00da024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 817186330 1250 817185080 817185119
    0x30901030b06070606031209080a081903060905090d1202090f0d0305040317031e0415110405040516021e06070503090124060e3f010203040c05040b030a0c 68
    0xb05814203006484a209031410365000380d904550864a456580341c0c130044100240800c0390090007210040e560748076561003003030491b4450344030043e050350109210b03422600c000c000400081c030003418140c00098440080c1041200426002441c540071b001141c000d9451501d401020a160740d4060400e1000d20b000d00c201c2103003040001c010100001d6141d1010701454500e2111031a00c03481c18425860001250900454034074444604010010325a0201003003614460800410700c0403500c02510500c2c09642c0116502c5410b1508018401e588003201384825030095003200c001700b00e0220200307074861900300584016008003001401c0d03507010710f00440d000001c80c400004c09410142e96112404501922035002c0001d105040249581c0542c141205403822100e120312080b802c007280070001e200e00c400d9581000c40031014000e01416800ba410301c0c46003c030080d50b41c1e02c2c0c580f410900045c07442c05018882e0b85010742c101c2460600041814070b643d404101d4100160500c0044c4200440a900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 817187580 1250 817186330 817186339
    0x30106051606020d050709050d11010509030304120f0b0c0703020304230d03080a1d0a120c150f110a020a11310e010902060d09061d0a12050c030901030b 67
    0x7510000103065100600a1a8944a0001d4141404030001307094040c1c5622a5105403120455034000c036001445904807040242052a540c290041c040703820b600480e031007800011840c01480d41445101c0750000c600e64400e0117a0b00540c1d45144801646000320714001e00180e2051200340f210307681c3c2c4464482d405141404441c0b801b044c0000042181b03920000480002c1c5c4143e05100040025000e40300d1171038651141007070780010151b0841e82c0ca240c4e8450190989440c0c0001203021402134480c42d0100b50010071060900442c2038241000d4151298650007943c5401071106000c0c840c0d9080e03a050340c10f03940c058240310345940c9402000c181241490399200d4181c140c60f8003590030620103000500b0b00109540710600d41a940c4504582c02d000340c594241e41030500460060342c949c0d0480f025400703846000260209039050181c0207017001801007280500810401c0ca941c0b00014400f40c9440c401c50110a4000203400c0c12a0b10703000340c1050a026900034001c0180a600035004001c85640c00740 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 817188830 1250 817187580 817187617
    0xe0a0812190e150702090f07020c0906060f12070e03060709030b04052e05010918080a03020405031902030c041a040c0e091602060f0103080d0203150a090e07090e0303010605 76
    0x40042c00f03c41444001031105100010303048110308050f5031403a0b00054840165440d403606000c013075195401685141d118010741000a400c0707a80b04c01c20342d40c9804440714120f4a800306e0200742840040165032000200c0c0351940087d49501e800280300d442010709030f5138140c500b4916955000486000740084481c0d024603a0344110314428410103800e581d8011b1982d644403070320300110318120b034010b802088549042c103e80b04005620003030300c44036080c0d21440e03043da90b00d00e62400714024091500926030602a01a0b0080b9400c0c84468066a182c021010340e090a05050104821140130035a950449030351480d1a040a107003030350188001c0e038041e050507241c400701070001a000e00c0046510100080c142c4c1155400a503040242d07aa10060303008100440307504644840e00e0900803009821501c81d0004002110500c2c803445086451002800032180682c4405a110140c108001cac81d443d94400c004002900000f1402403a00b0700501da009146541d080140444030395101e07071411001b0341010b2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 817190080 1250 817188830 817188857
    0x3020709020f0913140c03070e040603120c140609030304030f170703021b0303010905010305060f01210c0b0307030906150f05040b01051615060b120718150e0a081219 73
    0x505500703105000b001035481d96460710007005080349d2001080c02e805940791174010b20000300c0c20b2412039044001130600d03d20090780d80c0740008807007464041c1c00d907140c0074000078000c140c0710000145005520a441c0e2096501041c1001c45044140512039400700c0111004a1803c1d8080d50043c4580c1e00d03040d84800b050480c240c0064907640c400c0c1d01a2908950fa5001001480014405d60b50003055010102925501d8181020f07111844c82007400001041580d07001d040221014202c0c0092480420070b58513407401000241c000d0401c4442901c80da820f0450301e139400b25035042041d0607240105001c650b40c07801c1800303100c000d00400310344505004080118985144645801441d01e80c400e42c01000c1981da018105019501c0750f40c8426400d002c20311142055086c2d940351154409030381e1411003040000704402c6017007081168889003601d500882c03c4070101ea03200314846810407007502c03807425607a07032140e0081e80c5842c15a01e03508420703004c1c040381f5000e41d06207003c19482d180c2d0385041402c03549803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 817191330 1250 817190080 817190111
    0x30a0f020415060801150306050312031012050d02060a0b151804060f030c0f061707020a06050c0c060f0405060412030608011107060b010e0a050f0402070c030c0303020709020f0913 79
    0x195041400401d140381300401c400b50303091094443c02c2c48a1302d0705116040c80c1c01c01082d070300e042072a220142c1180200010f01c035900da8645800090104034a44050100e040c20300c65103036038a62100700018050000007401c0705032113020310000c2c060080c01500c10000152924103550308029100d0750301c2011502112007a98440c0a2540078004d01d030940c1190721f01d54584202641d44913409482e095075100d5007003100540000d5900c1174003040310503548203a581c10070300328200021a0401406940fa1805004450092402030301ca0304140e8410ac07040340d256900011003440040380c0c000c0880d44a1301c0011b00081000341c41041020140c00c0204105460701d07011800d483c58481007801d0460089040c0c001d02c032090207420b10089083c02c241201c24509000300326041c5070341c0142e50051711281f9245981e034440303904680301c40340c00002ca00011906e1380362000e0ba0017907a1105900500c54110086140c7c25648202c03000346414404441c94130300e036403040c0f004d41003184a504402c15a0b852600c283c00b0700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 817192580 1250 817191330 817191371
    0x1d031501030506070f0f1407050c040908180111030f0a110303010801091205090a03060c231b160306050601110313090c03140606130810050609070c02030a0f0204 71
    0xb1801c00741040e454200c00003426a195801100100441d200002100d00c3e00a10340d007800a9032800040d64071603181c2812494402008001c43d0001c4c5480b14640c107002090011f0b041e40346c5000c04021164200400466440b0038a0040d02c0594000300802018028801c0050099010070f041c42002400741e0105107045070004d91161925945174403142e0304200c02504240c0e40607019080c450304101c0c00070041180300f402400000e184030340c1d84000d410300902610302c0e41c40c0c2d409d08076007003040010448410000d9810145140d8185405141f80401103500403030b051950040c021001c541e500e10315100c3c080540000b50901e0305000b050348032940c540005100410301c00c0c07440800402c800346410300740da08540c200c9601404051074064070b510404185a0403982240040b54404e8990410019000f42040660b0000c4030621504425810b001078a03040144552011940c0c00c0e440c2e40c403500207869940340da0b000207600d5040000d807000060400c44841c03041c07c0c00030340000340850900d1118618400e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 817193830 1250 817192580 817192583
    0x302120102090109050103050c16031407050a1101090b03190212040501242306090a1508010e04020612091c020a020f0d1208070e030607120f06061d03150103 69
    0x940000b40034540d0758114030500018030080c6010882c1b0300e8076030320300207a07400742440742501e41d8000b90182043c1361203101c0f81004942d1340e29400e5a1554240740143e0350f03d1009404880300000003030007070f00765801204c062044483d104039042c5550344003910420035181a00f0700c140030543c240070010820076a11b001910884c07249000040001800c010b00b250303401e5a0456008500880d007091058010f09400080d003586000d0018802034a4200020b101c2d001d400c42440e00452030b41400220560b5030030b001144620f01d03880e00f1502d81d807106c006241d194811280690082c804014500d1140c0784a08100d900c00110340c15503000300009600703040842031034140180143c1c44000c20009500d4000410009400c080311002015851a80c43c1000f0085c1039030b2038404e2221050006203854040c0c4000f501c0d040300101543d110340703000480074150b0b22602c55005002440e11a0050042c03030b0502c00c010030780d5200d8880c81010641d2000307144103040e2809007190980184c0689070382e44100d1050340c6002c3c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 817195080 1250 817193830 817193833
    0x120507030f0308181f020706060b0307080f090f030703110307060e010605130506031c051b1005010504090c09050c0c0615040c081018111602011e050f0310030212 71
    0x107042460407000d810680302d11344040798004200080c861410782c80402442d049030300300941c80c1c0010b4240680103014030749c001c2d62100d030000200800113a10000d25485a0102d4010303102580b100301002d6940d502400103020b00c3d0f4010003401010038002d4042c0c0d5050018441180c1c03404155568480603140756000181041c1c0d1103603000d11162074002070000c4643d54614040010745807020019a86016203645018800861500c100c95944500100d4001031a01d98040900140d4030f48002d0b540c032030310018140f0091600780040b035203203001c2c028203510300d800003100f0721741c1402c180342000200300203000e41e02200d4040041d600c20107028400e4910a0035081040013620024106020a90b05100070b540100074800082141e1460207403400010388940700c0b02c16511340e400341c141c00010451808007580000700410740c1010511100100c4036a58802e0341c5000c2c48070f40c040c40782c06c0e00c29034415240c0089001803189074030f4401000091035020514404641d4026502d4021410315034031041c003176125 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 817196330 1250 817195080 817195097
    0x31b1602030c030c010c140109020d051b090403080403033201030b0601080103020d0609020105090406030f0c060206280b10080f011d01030201050703020f0111090a080d0207120507030f03 82
    0x9601d0144003030403809074103801502c200c1805800003441e524224038002e01024000b00e03921b00090096114410f500e50181203c910a055410510b60366002c3c0200000c1041713000d0655009410020510f900a50341501c80d02925290369034198081c201117800803100040b081803040055803615009a51920769403071007c0994110305240c070191070001d2a00e41802500c1d4010401600e85101c2c161005400c03400c002100341440c40122444d114242031158000e00349a0040700b80550341d411411814072400079500e5050782c804040c0d0b202c420496a0100c0c0d103090202048810011104020b0040c181900020b218a0000c002890401c500440039000034200b40800000a600034041405087c00014110406a05030001c10100005000081c1040340208a2400b018020014800a801048000d000402030101c0b100c0041d006421107500c0b6841c25040040d00c064041020040000d0a6000d01242d40c201000040c00b00d10317104007110301d441081c0e00000482c010080070852140f181e40c03100c66 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 817197580 1250 817196330 817196333
    0xc030e130c11030405150d0f0510140102010c020d14070506010b03010e0705090f04020a2105070e01091202060c0708060c0d0606031406040b03010207020607050f0d1d06031b16 77
    0x14401002c0341e0859a03600420040c44031ba40e81603503e045185c04c10f00039a41c1e54415241e041c01a012400c042c0140d1400c19003400200d4459210b40c0e0161141003001070700d448030410049007030f01c00300e402e01405a00718646009109114007800c00656101d0703500b85107404d03010795600c1d02d404426030184034543c401100500907402800e01058100f040381c9800340c101410400050100c0c401c84c062a4030499001942a00c030742c1c0214840c1171042c80000e15030018803100c1117050040c0078115450000a07600da4403086403580200038a1042d903a0382640501034600c242e09205659000e501480c0d0fa0b44035441c0300041c185001c01403030703100d049008481610703610414040000d03913000f41c0024003454100642840c98000040c069548502c0484020820003800030201e4020700c2900006500b201d070010b60031b001d0120029100040f0358a030f404490483d4018001281d0b260001081c03c80807140026418205140600103190042d481742100c1d01c9141811080c141070382e000c4002c4241c3d03c10000d00b10070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 817198830 1250 817197580 817197587
    0xc16080d1a010f02060a020319150305010b0d0c030f1e03030905120a0e1005041a09091806040b040c050a17101b120207050a080c01060f14010c030e130c 67
    0xd811400b801c20b000c0034400fa0f900607407100b4000700303400060b0341d0100009000009061500800d041060b00030042003000323042d090b54a1840740002d075103960034640e2803d0f1701d0603c0181055002d80014411280a0460350f481c103141d1000203040e81c42500c41d400c0b0320131050380b43e110458003a209860000c6c3c0024240741103414400381090506622009100204001ea0004190b07150140100c612189195880a0aa503540030341c4d0861081c00d5047c1405034600321200c030040101c203600711604002d81d0786200c8000c48210340f00404100a802100c0403c00061211034156002485014410040391310b42c8041034030000c241d44084101400300c6007047d46440700740300708200c0342c0d8107410074045039081ca807061400c0071102201d401040b203a040c0c110044903960b8161031241d9400400e48221141f641400740498005c000d40703000c0ea501e0420001020200d000f500c17421a01503204105507809071500540b2440710110b0142c00b030003940f03030442226036a0b00110900f40181e01000017120301a09400a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 817200080 1250 817198830 817198871
    0xd020c0607030e060408040618030506010b040e010f050604030b0703090506070801170c01020c011b1e02031b0109030807062309150906040605180109030e090a140c16080d 75
    0x50241c0c0e00480240801b24007202c003214255000c60821a5120040f098220344c05145da030700107002c9000e40400450b4906e41c0301c000703208480b0000d1005001d40d0700c0d102c100d52030b941540305071980680104420400030f0b400100c1c0c25404181820002032448954648504181c0701b11400b01c00101e030000140211092040210170384403801000785150f443e0b2500103903880030038915513418040b0400c01c0d100340d40310002c2c104400c0741d40000503403002c4101d841841001403c4010403840782c0190380320301001c400203111005401105030744070311006203580c690b840d855001c030009a03400c50700c078601c0240080f03802c2c0b0101e0312005000340e15445841d01d0129076051401018501117280421028000c50706800204550072030341010002401c0c0d00e039506140da06d20350040c8038007030315400c080050701459007000080e1246402a1003c5480e503490310307058022101c0000c080d86d6800d441074040f0b02c0010031080640028405464401c0349020291100b4055410013449032014079102c404455517500c512820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 817201330 1250 817200080 817200101
    0x7230a09060f170114030f0f150106020f03090618090f04060b0a03050601051302070c0e04020118081e25150201090803070c0f0b090f070608101a0d020c060703 70
    0x20703c000d0380368951850224481032003801c2d43c10940d05441815a9014002c0e40310b50a060012641d0350381c03441001341d8a4198000400030b420041c0d000018603a4004070301171600780766000283d450583c514081245a03004070b03022602c0e4640c01e280014603900d4445c0b101d8042c2410215440c510b18261400f0019900d00060003401103144020030400241c000540d00e041d120202c03084d1250640600d8120001e02079040082c21002904d00005825a540074003a8001c0c0e000f030781c1c1c1d0f016104000d0399150300c0310050301c240c1080d980004140780d0000b140c8480000b02420320b405860700041d010512810340e290b20040165005030b616030810105c10341450064030719100e03000921040c00503496049490000820007014030040034410810008850314000b0100ea005180c04540c4c00d040d03600e182c0e81c456040c8940d10340c0c03040c0d0f0300100d40180100309103449100e050490401d01400c0c115001d159a4000704411441c140c24481d0703441100781d0780007134801c03c413101d0001c0c9003520305036a0080c19111581740 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 817202580 1250 817201330 817201337
    0x160e0a0b06041a09270a0e01050f130311070902091201050f130f060204090b0f031203160516050a020901090b011704150c020c1801050907230a09060f 66
    0xc1008011190000f0040d0350316000307505500c41480f040810304549001811202d013040c1440310a0b25164150041ea0180320003d40070004011520481400c0742c105a45180c43c25420500060000705211594042c851080c50414110301c001022240b804070141c0148104980100da45002810000305100510407214000d00030b80c241013070301d4170089d030b40500f80012071043d000d4250240503001865040c210b5115230115629591030704900010103100f8500c83c400c0c2441c10106c00245000070310b0007404504008c4a0f881c50308e034041007081d01c5121000c0742c070a00c54144800186040107034448101c46010324040c0903058198410850a240b058228010b007a1429185024599002c8203190340090116032407641d9032100d0808290082c0c2000c83c1c016002d0a0144e0240d6141c0e0110380006400000d5418070b032401c822010441b403002090090315006540c038000601c4040c0f054120902c91801032803412038880842046e0941c0358007441e00c0f02e01082034100c041008950015071140729498914 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 817203830 1250 817202580 817202587
    0x20105090f1b0420030702030417160b0c0109020904080403030807080115050d020c160302030f120d022b02030709060504080d0c15061202090c070b04030809160e0a0b06 74
    0x100c90b00b08048901c0031140240d5980d44480004100e0301d85120060640d61003c688074a050345000356030b0740c014041c11014061780720312180700303080001300e02d0b020100c1456005002800c2228506580d0040201540b0700d40d200c00700d480140c9c449000d401c2c01240518040d0fa41e460840c00c004c0c1c0180e001400340000c0100d5540100080d800510404014480904e021a502c1401e000404040d008203003289a15010303121038403c0340a800c0d032051088900c00d0b8140e031080c4042c244d4140d202c810075086201c1c43d00c8204070210388605030754020b002841040c1c00030001e4414080c5407034140240940317000308256001003406040d070303008030b807603001043c092a0503407a003420100581e40307401c2104001e60601044480440030403224240d009440c042203282001900ea9030901900c24920303040059000d8640d2502140201035040c040321038203508a418085191200d40c0c0454100000810028041c051914144141023005070150010301e030b65103450042d400d02030081021030b0300000b0b00170322071113040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 817205080 1250 817203830 817203853
    0x506040b0d0218040507033509030d0e0a03050d02150a09110904150f02040906051503060603071b030e0415081b01021015150306050d020d0f050d020105090f 69
    0xd85440c80f240e25451143e180c141c45501e0010300d002c44980004202140049465045072000385001342c0d10034020750170590348118a40c5001e41c0340325007056650507030844603505400d98052020b000c0f420343c0207450a00300307a035680c80e42410301000c80800700041c0c1114040403041d5102040c000c4c1c0008040c003081045c00d86542d01c5007401264034a070309000703039014000581071103001c040e20054403004c00310900030921082e81d41002503115001d940c8002d490f05101144034101445422802404070310080e1840d101c1c60100500d50300010019070401006a040402c0c414203201352258481c460f4842e02801401d81d000c01c02a58411241c00c032500020840130000c43e0781c001141c40c0100b0260700c0c4203400c15500700c0103d04180c008602005070724241224000001d403000d412500f102c41d00b00300c1d04002244d00340120180c50861040a078070100d421280c002501e407003032540d0701c85072142c030200b6800300145d65054100318414001d40302503503445e8108008001c080c01841d0080c0b07182d001805041105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 817206330 1250 817205080 817205089
    0x9160b1201140d0c0f050a0806010e0103030c020a09140604110711010f020a0506160e0105030408090f060909280b0d0b0c070f050102090f0f060d27060506040b0d02 72
    0x140b0802544070070010129072591901c4048148280d04104041c058139100c403462110080b81d4450035004e0542017000058a820105045059903048070350610707144d183da05c08641c03003589240203a82c001064200012821014400c503a280440e20b0080d100710314214007000b0484000709644d0306004800c1100d800059502c100442e002407003400d04094000ca10311080b440e1111940c8020018410361090180d80041c0e0242d01c2220141d40d600c0c10280b420200045480f03000030b440050849805200f40c410074600442e030010491009004681003e850000240c4e084d24161000305618001c00c80d00a840318030402c04040c2d1018002d41403280302c1a0301c0200d008840201d4000d881441680041080f250312402116143c03034010144d074120f0f00103820040e0007544203c070860301c1241a10958170450070071100343d04503840000d110328140240070051002901d0300c1c0722101141d011081c2051030300070000300115011401004c001446160200c2400215a0711824047c81401030f00b0b440703c0180c0d00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 817207580 1250 817206330 817206367
    0x30901090204200a030f060503010c030e0601060f02060f04061b110c15070f0f080c0f0106060813120315270b030a03110316030c051c09060c020109090509160b 70
    0x1203417600050180584640000a0200b90020b603415420444006001035040d0000e0303403004c0e08007042d1080c41e40d9403403054401e982111f0b124000f50b0403c00000d155030501061982d44a03008820103c4d900a85094558003840d0f48040d03040031601c2e1030705641501c00100004d04607050103899500d00303601740131052070260081d060014849040010140c0402240d258603414542d4890690350300e6041c8290b2044d2124a07068480f6010761030000000382040c0f04841c05800ba1006c800b0700c9510604903110300001541c5100c0f080141600e03810819403c824128810340105043c0501805018500401012095075010260045800e000c0c02800303d5802081c81250a9414103001ca01003c0cc0c003505810342c0500d200340c1031603004091854050540000340170740320b1031003027040e02c62159080300c030081c0500b91201420300050031404207000050040503d030301002d005041520030a42c0ea6080c21050302e204580921140e04203401402034118804089005415100023050406800c1050081001c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 817208830 1250 817207580 817207597
    0xc12030e210705070b04031203050103020931061e020315090601090308040305100e0a031205070e040f20040b1213020910080609190f080c0303090109020420 69
    0x881c8026040e418102490489801e260b200e0203079480942d4500313007890750760851320054441c5415019001c0c9030740c0c400d100700c41c162175002b48040030310744601d5004036030200040c00d66401c1d981000e0f203003c90084d1203a850355107588500310208013803000c0040d00c9907504100d0701e102c200900500c08d0140301412205040400f00c0b05491400240d035415004940411440e4000b03000e100700081d01105206002c41ea01c0c0480380310301c03814007048200308c0e0300603920041c4900c05000141085103030b00501d5441d402068010a103031408940c511500300008007103502e0400b150541c0b0740d44044800c02c5031107070201c5800129407080300a00309460001c80b11203c0c07003600b8002c0b9240204000207100c0c040303d94031003203c00b40c000c0c2903006240341040c45664091020b000351101c038070582c00081c1f44020002402149203101031030307082010a595444107034850051408844001c010b1089081000081024522039001d2a002050507621801400200c40c414002c02e02030602550394000c2d0342410790304644419 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 817210080 1250 817208830 817208863
    0x10603020f090928060612031d0103381801030b130c06020d021509070501030218040e0d080a05042d0b0115141e0c0712030c12030e 58
    0x29a0782c1040d40b81401c0301d401034140340c0d0b2020301c0180c9102d2851203034444c48a100740e6040002684840740713407111031501503004001030141140360741282d52542c03512810780818100030aa190b1002d0030216000f40c2d002a26101d62510303448003c15042010542d03104200c10b81300090661907807148808500b005000291100c161180031038082070040c00c04005080d0081021a100b5496980007500ca021522007000180306100c1d1900f100300c221418607018400b400700928405247c000190065040320500050060000100a1040c3c603107001d425591a000c4000e00016003100902521910010303002012813441c00c410400001c0300e0782d00740e140d42c00c07002c242c0b03c00d5000140e815901c200780d010b4005140c0c030b2402c400021346d4089a0501c6842e0091901ca52500ca200380c2041c150380e000b002800c01d0080c0b030038600c3c80600040741c0d004090421045042e240c85a48401c28400490003520044000906910038501801401c08003080140a2882e0901000e110700026556650100d603114074078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 817211330 1250 817210080 817210099
    0x3030306190b07080a1206060905150f0c03130b0a0806040506120a06150501020f1c051306051e0c120918010806070e180c07060b040f0c11010603020f 66
    0x4540340250004010740b0062580d140c600b450508581c1d08014154800704040014010030f0300e0042c003c0b181039440ca90f4035482400e06d4402048a456040140c00440f810104030800040403144018028001c2510045030f84140300d00e00c03500d00001c0d5034400c4454041c14841c901c1315a070b102c1074558200a0032580071601c0e4940c80001004a4a00e90b50360a4030301c260a0440100051900a801c075024102071010b1440d030b4400042ea2500d400315903030300454104c910381e41003d52980740300c684051350a01e40a401d0040702c03011569a003600d500030307802040c030229030000c00354040b60201d050f124940310680c3c14070254662990781c03584041e1551b0075800002c40e6102172a160b020701c010f141d8080e507000022070750b0748a02d0a41c41d201c060780c0c00c00001780764950341050340c1450f10a4042d604d030072006e4514203907621030036041d80350424403040310026180e040a2020f680c40c0d0045200d8085071701400982414000b1024040350b804d00d4107104941d050020400141e41e46012000c02080292184c108 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 817212580 1250 817211330 817211359
    0x5011b0219090f050103050c104401080c04060803182232010b07060f09030815120703020906040204030c170d020111030c07060f021615020903030306 66
    0x408101075040b6110782071404050001c02001034004c581228002c03c2650100c80c080010303c03070b11000300b00c0c681d4003199081061b1030f0340d4094150040030f1040d600c03800d4040c6085018521484465401481080e00d07100001841569014008a0300b0000304031000c100c20391030540c000e034583c0102c0d001c40d030b0720005140d112044c0ea16000406076448096030754640c040c48030482031100a03c02a03054050f6001b250800200c2e010648507800303040c0c0040c45088002d60700c1c0c0001d00610358440e02084400c01e8940201e025110030310b0207000201486919082001c0c41c0000f5850303c40c4010349442880352092070041c442100c00810880140c940640e00000591741d000e010074007034400d50340700500c0d00605100008600c000c150490022410300c900340c862060300454100c0c01d9840840b1341e03840c86002080401d41c22282c0c0c00051524503c648000302c7d40341022825a0b04a800000e050003101d0006c01c41c0358100500c0c4501070700c81407034a050850038444800c020a0340c90200178507a41c000e1504910550 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 817213830 1250 817212580 817212619
    0x3020306033301050906010912050705030a030306051e090606090d02090406090515040b0f07031508060105100c050706032307030b0906010e0d0308190203010f0e0105011b02 76
    0x9507846038164a1058040c1582d0030b21140a10402a18155864a07000800d0905c0e00d051542c2c02601e05a45072410305080c1840000240340e1590200c1d00381c41011800956030314188008110140203480000d4260300e40070900200c84481d00c10341c41712109000701d003100c95850380225134202c1c401351000e81c6c40301800707004074103200b10040010b94081c40300d104002c100682c43d003010441d98441c07804d03204881c1300f80c680300c4d80f8480b0680300180b05248000c0007903611940d0301d500903448941417901103003140d1541c0e0f900e0303010540c0381c0101c036032038100500610490501c0744400715000907a1400d141c0c0391805803145511481c19000d48020035849161341c40d62602c2d900e400b202031050041458071035051401001e0000c001c1c804109000d00d98000002d209503014600f4041c0050016011908040b001d07501210840d03802404110320000e80181c061417400244042e501038071420303a030790004904003800d00100000503400b0300e0402c0840c0c651020300510389400903036010350565034a01c580000c08400c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 817215080 1250 817213830 817213843
    0x30a150c1b0803060f090910020d0f09061d0307170a021e03040311060306010c11120a03050c010e031c0c1b06140901050610050304140a0f0b0112030f0302030603 71
    0x1d0141c0e0340498680c20034000c0c54402036000f102d003115902840d0080d0341c03d0004036442100e921656410080544092103519002084074446103440001d80700311405039802240d205c00010740e819540c8119522020004840010303100748200d0040d0708241d4240c0d282c064242c0d141d184581000740111b643c2220314020882c44100407003603040781c000002c82980956498101c0c0c4000c1c0c601c843da207058202c86040110131607005d040306955860070070003603841e03290600c60440e600b01d07004040d001001c00385801c14840001218441d03078400303944644900f030103070944003034070207220054004012040c1c1c0f00c1103600c0002c0d00000707500307404501c1103840300081d44c3c4070303006520704103621450590a40400c80c581d804203029084038450700b403050b1184102d241c00c07103030304413010b0fa007040904014045050187d8081d5520900c202e424015141d1403504140c10f046540200303c81515200407101e0412510300d044a0140840800e14020781c00c590710700509081c1c2041015050542c004040355554409110340c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 817216330 1250 817215080 817215107
    0x15100302221e051f1511071202090603070608190905070923061003020903030c01020d0e0f0d05030f07120509030a27050f01090e07020a11030a150c 65
    0xc110301c040a001034940c2e50001c0316400c1005140c800001c8010800a080d0786003441652084100b0904042014408400e00c05032070041c445040325141c81407000b048204042c00d038000140c0e0421000e4030601240d00809002e10b40719802080c8188000c5a000c540d040d44001c8035804400c60b4861032407418014040c04a014000d40500c143c042030000064200b11800c9052241c100035440c42c00b94803031110782c800e4850b281d202198191480526100c1d8000d8061000000c0640340342080c541c02480c00c90384041e02c03d50703c007a147c0c0c1d240140a02c043c420300080c11108000741c806a80490350052082c4002031880c00581d01c0d26003c115001d1088101e1000c2c01d0420700c08010900b440c1c0c000030365030703045189100c0002fa07154903007445031007a03d400b18554200300800e070b403169810407013007003900c40d9115a0b050420600031400118503800344110b03801405c00da00948050545821320344908260603021500a50000d4071043c00500380c080300200c42024020001208040e1444c102c85c0d0000b00c0d02c2c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 817217580 1250 817216330 817216399
    0x209060a08131a040b06120601051e130b010e03030712030515180a1b1b0f0f030e031203040b0609040c0f09050a0c02010636060b0c15100302 62
    0x44103880c0e01c0d0118943d4040c5005001c654100d03504d9504022032442002c01702d0002d5080480104450b0400d2010742d40f6040c4100450301d4404404000300b00e540c3c481503042000e031034aa41d0000e86e1543c1054803c3e805441c241c01440c500040c6031100e0325031030b0400060108159968000030b024061039074020201c170300011f123508400c400740c8205a044110170740340c51558a1130190090005550030380020b2403000c1e19160b400d41c0e091103211101c40600012416100c2101c5160301100080e504815144141d2181d20b58209403034132001414035040400c0f566410245041017800041004a030420703a102d901112560611390b2286030901c00781e2096844842000c800540104800c3c185801040c0304001e0100c042001c8a05943c04a00362007140c4160843d420408045a009405400c00700354400ca480744a0030010706140342d8102150103960114060700d0307004c216941e0882003031140f08199180040c1045540c101860b40c0700c80101107120007407044640c2504072100d10301101390410003104091 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 817218830 1250 817217580 817217603
    0x21c060209040f09050d03150608092b170103030516150203240d0201090614041e090509070b030a0c030608010e0a020319050d0302090102010b030109060b01120209060a0813 76
    0x799a001d044800d2048441b80104030659203e540710b8030031aa00d61542c101a20780903440c02d001a02c06c170b4800b420350b443c0350055034007040074880140040031440b0310700c100e060450701017510000c0c0b0060340c46601203107124440d00100003003075002041d160b03e0003c410b04000540028540541c42c0d480c1d0b950648102d5001104100105541034480d1001b58409580c45000210540801040d8100020001d021a40129042c450f0724400d070300d00002e007043c2c41ea03072500d011707140c4040e680100071424011a006850340e0f024022001180656504002c519004000c000c0c00c0440000c8103000091043c00007564540d1100c4840d44070303803c603000500b8844000c0003041003482100d074032406440416030103031150144101507110a0f1904940080c1c00402411410f05294012806580601d0405045648070820950559820f124240615101e0080010a242e5090024280d980c805032850382140c41403100200c03039101c600488140400070728000b1900e950390124030a40c0f580ca604060000000ca4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 817220080 1250 817218830 817218851
    0xf0702120d1202041a030402060d051609290d020418021305090c090112090519120c0312090807080304260a440f0c07021c06020904 58
    0x1c10038034103090060303882c0020750541242c2c0000364862403250040d00450f00d07010014605500001c2c54100784020405032401e207402d41d001d825520241c0320584900310410310891110b800014620041000240c810300c2c1111460015100c116059403082030f81a0008010f400c0c507629030b040700c01401400c1141c020200b41e03005400001e4000842d07440b4049903185010801d89040712599100b00d003110000361402e00e03800f004440300c42140d8015001107441e5100e50000032024403151280601d08158906001c1031414151007400003c0503007018031450140b0700c80401c1d8800000ca149c02c0f60340c00082241c40c80c03481d00c610940300b9888040c0c15408080140810403543c1c882e0941580c4028403540d00e0081e21031000d039024401c29407554041003101d0416542808890414500c1541d04e404460490190500300e4045004400b0600c100601d01400c2000000070030501035007060f02a1500780c00c1000980c003207900d040301d0100c1c56000c0b540389040d5104000281c1c040780d1a80e40090018407013113a44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 817221330 1250 817220080 817220083
    0x201270b04050307080304050306010315110a080709060f0e010809070509130b06010e22060b0a050c012714030d0609091e0b060d0501020706062918060f070212 70
    0x1d070182d94803d0160b40c000088114000041d01d056480c001c02902d41071346180c0c1c074500045061204400c54030f8880859041e207104090203090003d24a4640c0c44051401c080000c14010740381e0000303000d2084060070442c00c08e5020140020052003824002c1494842c039041a14101040d4000780e03001100f0f07400c008622281c00c002c200c04038401c400310480d54559900541d4101240c811440d0082c01101d8400d410b204d14003211041d0111107400020096201d0001b14460b906c0941110086480041e8030010350500740702e412400700b0300700d1120102d90b41000ca402401c10400c80041c01018200d0441c1c04030740360a00c1101c1c0e80d04900e420400526607035009060203054066400c0d9108410600d00c510340d40c0e038424005505a50103c01b0062640c1c45038104064808006010744407590f00748103c0d4000707032207482401e01800d038203e035103650083d0725200c59036009074050312404010001d00112410021010040b4800c0c80200c035060b807540b505a14049860150f480041d40c010001650703107041c0c050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 817222580 1250 817221330 817221337
    0x90a0305010e030c0f120304020f2202180402090315040314070c0306060905070c020909190501050f01170726100c021605010503060f010507021009050f04180201270b 73
    0x110700c10b44400d444117a0070243ca4403401441c4400b16a01000060014076140751440c2c4490300041000c0c400310307554455209191801810b20303810030313400155001d01e0380e034a0180c600c0d00385044600398900b0031400042034036810010203c5c41c0741d05224011904040c0228104407c1c00991218030380ca5405c18240b000c545e000354842501da451800c1e40210b621340840c06050300c217452039211503405440c140d09002e1014402041a1214000c00c41000315400740c110540350124061800800c1a05003115010302c80c2d0703010b921801c1e04600e80e0040708901c00012481408880c4800c200f0354101c0440c004018460b0444107505010340600301e0514200156070b0311241d200c1134140d08450921510240c005d020702d000340102408243c0a1000407060314000304070041052040c9002030a20388903a000c942618001700c0c08801007000298184139600342442043c076100c5007250b040c003415481d680a078001720341428019041085807c4c00400c103410070106409001c00c200d401000c11659000300c21690740 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 817223830 1250 817222580 817222597
    0xb15040326041d0f130b04020108090c0406030807020f220e1914010501061103121b0a020d080604090c1401031e24031e03020a050114070813080f090a0305010e03 71
    0x10078a201144003400119515207040368001b0004c0240c0e1610303001500c01550040000d03080d84943c0109000d5a02c81f4050034000703600c599030003a180d069520400c010403440090450040c80c120240c025545032154281d9003008201c40f00048e130b5410960f1040c200002d02c55500c0410603481c003074408020280e031072036003500707004002088581d88901046800825050000407103a10500207142c020442021150f001070300340326480b014444891544d126900f01540510141e0041403010b0500340e00710350415440342d0225000c00004076140d94100c4007880d540243c00d81074504083c10300c8070380d0080e48040b07410041c0983d007962084118880001400d01c4480b462440801341c68919120800020700e001900d90055481042c0491654507045114201405034118802d07505564007042081c17061501542d000c3c0c092062500e40707140003410f510409000c42491031f18590440000c85c06540a0381e00541c1111840c96403240b070080001c007030024981010b01554070348bd43c21151440004000c18004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 817225080 1250 817223830 817223851
    0x18091b091406031c02010b030604050109030f0e030a030c02060919090e0f03031308040f09060501270b13080f1516020d051606050a0b15040326041d 65
    0xc1c10403030001400e25806541ca150541e212030039620203800150b08200130720603c1d10000400c4203e0b003000901d031080c00c0d541a11943d5543c0c0442c0c0c240f69220055412000c002e0504211680d042c0020070f03034030f5544081c09810014480c071040215610841214803a09005110301400300c07200d42071500c00921842101415032411141c01080000422030300b1030100288081c504580da205480c078082602c1c03d00866404008000c045980c02c101417410003c2e104541001554908001c00904907545a0039440b503688001e1003020041807082ca030090540d6203c000c41e5441e452000012003160b42d442e0050015805404601c01034000c0005009404c820001960451500c4032000e0429241d249032000340143c02c02c01206e100c00740100001d04c1c0c4c00e846034440f2442c0c8002d0381c54040441320b0984620003030719194000c0c00c0d8603242c1008011000c03552880c049142078a99a030f24114440300b0544d07101800303440d0503140705610030f1000365402421580d050b00341740c500005410868110854000078507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 817226330 1250 817225080 817225091
    0xa030905030607031401030f06060512010b013b0a09060305030712031b031136030d05090103150b04080a0309080604150209030c04150306060902120118091b09 70
    0xc51310034001c1440744048040400800d0b420b58923046034898440505550841c2c40c1c41001400b600e0300207030b155007100100700000d54049407500040c0405184030780d903004981e0742e0340c008419000d208480e407252404900b010071285a000081443c8900039444207400300c1c6007020020034040040020400f951042e1400ca82030002200150b08640308400d00c800c0011a044901806a00036442034494021358031149003004103000a0641c1030030001103902203100030280098403049008101740702668118080c01e100e0520501c000c1050080d010703240c0c10951540c0e002d4131f00c4923802207888090040024401d588684a0485980d10308030032a084001a403c0c0030b002505070008110305000319402400c00b03440b032007442c1008001e5007000c0c1d880ca0703040c011401001c1c40380e6514030401c001d0640040c080444ca0b8603504041c82252416030114009030700400c1200c03440c001d02c0300d040b03055a1555200c00c2004040011003c02408610001488459a01c00c041107a06040076004101c0e0030002080c40b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 817227580 1250 817226330 817226341
    0xf080c0603070c0807030e0d0c0501030c1e1b1704060f0c02030705090a020919080d020a0c05061b16050f10080403051b0604080c01050f070203030402130b030a0309050306 75
    0x39240700860300400002c684945500010f1652001051075500920340180c0d07091a400020380003808100341100c0400c4200010021303940c05001b2a031980001d0704020490405001c680c0e4842e1142342c0052080124443c034020a200e603080d42000c1e00d0347c0100c1c0036101c09a50382d00e03048a0f58868090131010034800300c00b0040c9140702d103a4200301d0380c2d0f0213805411268680818044607201c090101c5072019001d00c100940e0b0346034482c2e9280e01d203803109100d90840b841d003403c4a042101d03003045001190005200240030400611603541180d0b02a601955a869500340d048503007011159284178170300aa02500980244080d4a40190390b0b0446d41c1504484202040100600d1402c9114021902500008000c40d0042019160b42c2012044540401d40d40c08401c504200c0304581c11034100034082420600c5460034030501e9400701c08441c0556440c08d05800195032400010301c003c5c42441a0036105070b035491280c2011003040700180450300c090000f450040c041000030b0040300e00078400c1400151 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 817228830 1250 817227580 817227589
    0x507090b07050325060f0605010e01090e130206090d030903031206060f080403050405030f01050a1a032a0901140909030415052d040e010b030708070302070204090c0f080c 75
    0x1800301e5440340055150013800c0020010950700c0805448502181c81211000300f00c0c103015114008408142c0040c1c464244000503203803d010381c000c4c9040211804050240b051481d403000e030005000c02203920351001c01d100042592040d40700c00d41c0c01141c41108681016040000740094900c40d455010442146408171030840300148240070000d030f000f0b0102006a03010310030140d0000e020346411441c0940300c17000f191800e000c211052040c1c0c0c2d5110200848081300b03120360150f0000c02042001c64102c60000641e5951340384800380d003554041c0c040201055440400d2040410b00542803410b00c0d139548021003501132400e60410300035804940000c401c040b020048074140c3d2030310340282003001c149820440e40b941200b207d50b0100a0044440c2a642110303400c0e80295001c03e611040c1c0c2d42d03042502c3d0000005040e031017808050000d0050003006c0e0741024095a002d1103074a0b005840d001e650000a0281c4090280903140c001051000700f007210344105203800f540c1743c41d01291140d41c0301c4005e20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 817230080 1250 817228830 817228837
    0x2b090201120b010215090c030f12030f130b070f030506042007030507050303010e091902060d1113060f020c010c08070f03021e01020d050604090b0402120a08030a0507090b 75
    0x240041c0001040401c46101c640c03000c88980818030440d0201e021003009a000301c80181c0718036030290310030070b1054480d10341000018110307907020b005001d944050b901003400c03d000c054000219044440f000a20400d0309034611203c01e60810f00141c480d0900f80c2015007c00340270b515140c000303800c000001d009030070180580200c038103001c003d004080883d1054200300c0d4201c1c680880420408224080200300c04001442c040d1800042500150800c0c90009140045c400789100603c00203485060150340c80d1000c2e500075500452000c2641c0514041100c01c1d44601d00e044240b840802801281c0c00354048082c509a020640840b10600c02000044da444c05d4040c2005011850811403000051805070144a501d4482d0048401d004091040c0c0e42120102902b01c5070303d82e5003c2110300c40303200c09014150700180c055030b0420201149441d8168000c0c80180080d000e44841c68039000260010041c1c007000c0303600070f404079480c1c0c2041e01c2c0400240009440900004010305404208014102c045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 817231330 1250 817230080 817230083
    0x40506060c0705120102120f010f08060c16020d080c070515040f090914060c0a03050c041514040915030204050a020408030d0b180103060c120515090a020405062b09 72
    0x5002c81c40c030b8241080368900c40c00300c403c21195020302c0203402d1100c80e0f960103401415808012442581010580c00c00500650301081c01c03a8800c2086c4120100d003081104c4450320034011a10f5901d80a0010a80300d00c01c5e1a402041a40001141202c0401c0443c2c481d065820407199045012a41011035079280564004d5040f111a0003508000c206816840020014880c001e1506614105080e140c14442d040b280c3c003413810f40024909402c2c613414420543e01407940070180d802c01d4140607660301501d40c21088142880800806440406016025038009004600c428008040986482e2007011905d00c4100e0046041102251903110f107402904d0654401000540c10141c000190740d002e4000c0800950f081903603501c00c15405030130400704034081d500034000451000c900b42401406840520000c145092400c41403007000c8101000c4d0314000c0d507007103030070840c00e85603103084000078810b60f8001c561251000426502c04050307030f103060064000303041c1e0745c55982c040c0d4500d4009a0321840b00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 817232580 1250 817231330 817231333
    0x15010f180f1d03071101020102070b040f060e16080f0145030e1305010b1c1506021608150103081803060a0204050a0f1a0c0f120405040506060c 63
    0x500048004680c0c80203001d295000408662403025049103144021a1150298540c01c002041001d1103d540c5003e04624000e10086203009655141e408020a02400082191624407120028401c040d0481d0a4040c61001941c0786504601405032015140f8407516016000b01035541c14010b4061041c0314000b9035400c44221142c10302c003000d05101c005a1000c0c2400f02807040e13198240480a10510029840390700c801100655100070000400301084441208900301001401000c0e0254140c4209400440d501081a0440c01588014100d02d510200c9400c1d842c1d0400a5403960014068450360b1200c0807800e4081e40b100300058aa04103544821448080c1000400008454500400c03a56954411084000c0038690003e420508280c03580300d001030700400c0134006440d0180c881c1d00100112101002c5403440e2945050350107422152911680c2804a030790a0403200901404644050410698090f08042c09605002d070308107018280c0210315000001c3da203402e1040031035925107520300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 817233830 1250 817232580 817232609
    0x201060b03060d03050412030e040506060921010b1f08010803030714070f0209180d03020c06190b06040303080103030f03111e16080403060e280c0506040815010f 71
    0xd0510002c880040b0f41281002420440080c1002050101000b010310a903101e40d101c0180404100c250b4801901d118441c00c410010f20305990380d401003c504a06500110040f030101d48a510fa0040c0300c00c54040c0d4110f02c094032110f510b41c41103000c8102000c07041d02c40107410303601c0f042c0407035803804100d42410101751200e0030b001423102884068a00c80d4494000c02c1c2e10071400b64081000c41c101500e071a040341101801c210038140c003c3c03161032096000e40c43d0840c101002a10340c141c0d5000c010b00880060f4200264040c4800a940c000450042002d4044e5680f250399240051010100744400c0d400a104078585e140b1180c0b10b4018880c0502c2180700c464244045a0001000d03126440c1c065001007030b08000e410400a0380d1601c0350001401841071f26103c3e0719600300901502c0100d00302ca015a002042140d00141c0800814001e148441d000e64058025030319190186840300d4005583c0100c3c003040005d841d0b400064804050700c0022503162150341d07120005e41c09441e050250925052258 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 817235080 1250 817233830 817233841
    0x503011d0105330f03060a15023a052205130e0705040e011a040507050403080705032701021e0729040803040515041503020d0905061006020c010201060b03 68
    0x7680c210000712080d0503845800e12803805000320341d440030111070702c04a800b20030420b4601c0d2850810340102413100d1250345070300b08c03104004d45910a8070004903500c0202124808a104001400390071060500180b4071140741c0c40300c01030200d070402e40900c0032420602c3e00ba030003101008001002101c801811030520402e078001d200c006401130a200307121764850b001c00002d59a980c0c1c040c1c080840280700001903005007600004c1c1d507070f0000481c1140a179092200740001c4950260403901182c2c0c001445944030002407400324114030522200905e41580200e580b4048a21000007180343d4109808944030418078a1a08080490410200e51785401c5000100706c02d2008003400d5506001d080c050b609160894400404141c0042d00b24240990010509010358107110750b400780840640880903041920344101d0311120302081c3c0c40310040540201d08085180801d4026561695001c001d680051a00c80301e90b0f501000316124490042c45000d035115150750040c403070032041c1c91000c80c150749599201c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 817236330 1250 817235080 817235119
    0x10912080408070203120409060b2703070801060905150f010f0f030603140a03090f0b0a0c080904050933011401020c1807080a18030c030302190503011d0105 69
    0x1c0081d9503800c4104000401681c0500c003980c811201401307503684943c180103010048902a4016115541040002e4030060b002d2501e229010084441c101c91501c424401190410f41d241d13001140e01d42c00c0c00c0c1702103017114098006a104010b480640c040c402074080400c00c0700c40706038002601140e04008119081c9108400207800e84a182c14049030700ba6036944d483c0c22005840e800000550403c4019000b0107500141c00f1006100410380000341e0741c00c040250003184034800035041030198040398601081180c00c01e0f20012440140108200c0c034107801d42586400181e80d8ad400c20450022261044c8001c90300c10b036080c9494403c9400cc40da003070006200110103500e20060552140c8000304030103548200384002c043c0703002c0c542c2e403045042c5150302824030300010b000f01c06014203001248088003140d0310f005d81859050328001c001d6005a050580c028070424141e51421502c1003400c0041c5900580214101c41486507400000c45404007150f10208080c018075610148050711080c40c1440e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 817237580 1250 817236330 817236347
    0xe0a140108060a12030c050606030a05060f10090c02010b03010606090b09090405010b091f060203030c03070815030708010b0f0607050a02060d020f121f0b03221a060a08010912 77
    0x500b8406001381c07595604a801c040c0010100c0005034040300746001c1180501180d5000303101030300141012131540e944d40f9184c1000805403034100180c08005500d00700b810400750010710078403400700010703894000c0090281c03a151503518000c0d030234000b000030014440c0d4420021a400c19001c9420180820100990100c01600a84a540d22012020925924199418003810030500101e1104000c81124041d801c001ea00140a640082c020046c1c84107606084030b40c020704078500b84d00e142e62186501c2074164005401030360140b0500b1030104180d0015480681049811600d0411407100c48081080b1031040c2000100960840c582c002c00505002001d0004010790307440150400500818076122608001400c2000814050a001100000100d540c05e0721140020503400d5504011182c0032901c0003428411801803003610060400e24258018080785510400c071800c01801c83c0c0304451141e20640b140c41c49400d150400060310351051142641c1554010395064000f10860300035a60b881 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 817238830 1250 817237580 817237591
    0x180f0619090206040f05030d0503090a030c14070e01171c230c0706031b0801270609020903060c0a02250314010911120c060d1d0d0e0a140108 62
    0x1034981c150440140d650344090006011039590b00c0b130703100b842c1004051070803d55030f17810010b0140400511000203408100c03000090f4050402e400c11707030041c1c0303081c3c28410443d2030006510b0041c9100440c65202c03e041d6103048a0034105514503400407182c13400e488862901c0100701600030302e1010602c0c035000d0b180407500c000307000d000e100000c0c11a2542000b5544090419801c03034000400034005590148101d28000c8240c4400f00342e6445400c1c8085d08900042c00f820314204c084000c4405c09184035128194940d01010b01030241d40d81c0c2d1540346000e90002c40d641440f82c050340c0700103105a080d420950311400310719401084074130f4081071151440c80c0a00107081800349000301c04000f2419030b5524001c40c2600c180001980d14540c2000103103140c00a90f413521502c0881482d15990314001450900c0550884920343e075100003100c2500201080b03610300302c0803017800e594440d10040204044804013542d4071074100c44000d21040140382c00c3c0c2d03401100040d484a012140032944646c00450b0703c134 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 817240080 1250 817238830 817238881
    0xe0c040f02250204050a02030708130212011e05070f080114030c04061509090203090c120a0b040302151f090903030f02031003031d0303040b0c1c08180f06 68
    0x2010798880903181c001108412100580b080d40490850900c3c2c8a00b81c0e0004c0e20000850a50400943c02000000d000d403081028984083c0c03445c0940d031314000d40104428080008015050310201d0702190f2490080c0307000403c41c501000116400e0145241c091500b54940e01c0010300e030300f044c40310b80052401d9070042e605841403000224050701da0384a032601800c80c40d40c81c007a4464100c0001001c144260300562020b42c010b10034000600320008003000c000c079044840481c8900c40c540300302c4c5404980075018014089130000c0c1f01c149078020422082c1c2000c501d074030b0503199a450f1800903290800ca45402821600c030748c410405600c0da0303070203010054030924010070b0b42060845184141d03001030301e01e00700b0311213001420010503400c00e00c42d410441d2020440290342000ca0002600ca000d24480c0101c0e02000040d8040000e10a000c0e0041d03503140440c04214201d00b1a600400c201c0342159400340d208407a406044c242c0000258200c468070143c001400b5596903103c805031040c55030075030b10349403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 817241330 1250 817240080 817240087
    0x1d07060527100504091b0f140f120f01080c030601050409081306020c0a050a180c0504030803010603020307111c0e040f02041202100804031d0a0302030303070c11040e0c040f02 77
    0x955568282d10407001e9641e4070701c2d4036541854283c0c0b04070b03a051507510b0b1407455103082000c103954100501c400314104034242081040f00c0290b120825101d0b805203110702200c002600f10380c621040281a009165011440070340341e1325010016501c00070740c4540380d81603000314010411480c01d50001c498240c85800400c0c2401e002e111113278500103150300703e400560480403801c1c0481c00c2140c1801c00800e01103171354080561800e280700102800c1c0130880d41c0196124070718103610a01510482e00203684c01481250340c0d40c0c0d40e240080080d081a510140010312175030302071641850009950030041030f012481c1d51541c0100380107403101c49d58a41800d80003a03e80f2091415001c1900c050002000c4c011403640c0011071a10411100c81014460350041c4200310f406c0c170011a074441d0388800346040b030501c3c196003003400f44001401c014207a071000b035052000004112000e40d2000603002082c2c131400b206c1c55207990b02c00c04c100a4030400c0740444040c0e4405072900145150a4001d1601801d0b5041c0051a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 817242580 1250 817241330 817241407
    0x3020f060c030c030424050105010305060607030804060e032503030c050304023a06051617010b18040501090f320a180506090f0303010e06041515031d070605 69
    0x3803606d040e200310b006182e600d4004200d1941c05014040c2d1080c001c03104285400b400d654054411007000e040078180c241d884200a4444408100301c1c0c0c4400082c0315007001c070f0321000402e0340d91801d00400450021b03050002000509000b03000352405194010201c038240702002c194401011000000191030410a110304495400c01c0c4505401c918003407080070825103071100031113000c800200400c00030082c0c413405007020b44203060000750554600300c001c2550391a00207004c6456074400903442c1e500a150000000d8010801d520516452100c8241803081040c0190319000c0d0380855000010b4020084a00c1700084d25250400ca0740042c7d0300c4400038030a5140b012a000c40a48003070100c03940c0e4440e00901940300000c02211a42450450056180d58144903601d243c1040180c0003d00654949144c103400c94402007624018040d40e42901c4143e00c41d848004000d451100d200b48a024100c901c1d5240400c00802d4010a980140d2565460020000249071940c4621040c1200080c440c800140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 817243830 1250 817242580 817242623
    0x70204060b040b0d060b1206010c05160b09040b01140913063602040f0611011b1d0105090906151902010c09050f0306060103020a1107030c0303020f060c030c0304 71
    0x1000d08400f004007078581400140f00402c4401c03a0300014035464090004180407407000000f107601000038a000c00c040f000c1d074a0503d15200030003980300409111207502182041c1503c0240030501800c9801b801082040001034505040003401d80d900014200143d840354141040d2542c10340310000d0000648a50b030b40407004005210450007541e031490000074054220180721040c4411508450031460b091500703a61420349041d03449038405000c00010a8458180290b0140c2050007054030407940c400c0300c0c50310082c14040241e10200680c101c1204100c9170354403078400c0d0b450101c009003445519880301c50030041300c49880c40c5910b024090811440e072440d41c464002c0603a0484640000c03d91801480700946a4942600043d002c1d445490f1503410980d400101542c024000f801c006a90343c0380d40004035207810400d848010f15200d418000410130002c00f0a48003164041d5080d60f4000c2071403510b45840d0700d0150742c0380a00031414400700b01c56110715001107411601c9445144880345c440500d05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 817245080 1250 817243830 817243837
    0x709180203070807060e06190c080906120103020928050a06030c060203091c020d060b040b270705030702070b09041503030305180102090114030604090c121103070b040308070204060b 80
    0x45040703410810302009500c1d085a0141000300b0f048031f5042c2420040400c200020a00c44529410005d40c2040308060100c068225074400c00c0182003140d55092400c01119030780d00030703c0201d001d0405e550008800d90524030402d003030400f074880071600e0400284054800307400b02900c03030051541c1c0d4800002c00981070348a8140100119005944c07141d5580d02009001c41d514a0821510fa10100003000140d8450000742040d43e4001d00028211090402080c01094014030a541144809607144043c011340c811105915501081d440840d070342d000310469080c00107441c10741c007687c8815418809010101c0282c10348840c0503000207007030a0a482ca0f204011001e034015030210787d50303400303110166152101400a0041020003580707840c001e040000c2102d0b40460224180c040e01202041030f9070303660342003c1d144c17542207400140c44d5601d559210084542c003003811603030800d0150000314681000719003c411150002015418075142d501c070614a41e1100600300d80c8150342e0800414084440c030040d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 817246330 1250 817245080 817245089
    0x50d1407060f030b1c03080406141911181c05100903030f0b01120905070e070503220b04060f020c0a110a0b03040f1e0611070c0e09070918020307 64
    0x5402e00480e150380b000c0c00312560700700c0d0f082c004d46400e20708041001035841c81c07100d041c1c1e161a140e050340d501c0e4280200140344c1e110345056000c001e44144910881705c1200d02561440b0070700c041098944500030f4603941e1140c0b000c52104441e03041c03030000c6070b45461101c078502c246802c0b1315180e1522003959094104a0078090340d4008607603032451502410f80c584902000d91060000801010340e420001070484296034100444643d1602603107801c0003800d0000340014208526801c040b07007040d220141154204481c0600c0e400c0000039410f81d4081411543c0c015660480441601c81e117454990f84040e00c125200c0745e041701c0d02049110760b0408100480040140561503011980c149441040070b4101c1c641e0080c00710041c02d20500012400c1180307809855603102508151040100ba28114041d0f00360f0001f42c40306107000e240150b00030802e80144411889921130008081d114966801c01d0142900d00c081160b1044209000c1c20758240d00440ca2442c9010300d01e80450242c0c2d00082c541f0007c1d411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 817247580 1250 817246330 817246337
    0x4030c0506041b15020615130906060303032d0504031e08040203120a080c07020d05030d02090a0b0c19050f1006080609030301060522090203090102121f050d140706 72
    0x60f40b1000c0c40b911840f00107000414240c880408154400950321040034284098031000c101018041d5503076a2031a0070030050106090040a0407070500754001c10300c40c441a000b003801c00060210520300c440c40d000a82800d000583ca41680c1c40000e080107201c000d000f01c0600c408001145e40b07036810441440c0e80d050655603641458980792041c5070600d000b070204080181401d002e0200400d400090b095801a40d042425445002c0c0303000003003140744080400307442070000003a4021410301c0d98004090010043c0c0b43e04401c15a642844d001178410381c09a241c0d15003007c80c020f081c4240c0c00760043d6140740900c080310a605040d50303680f4101807003c2020341805603103074010080d500051003c6a8840d50030760244d0b00f991301d0484054418460000070841074400082c9800c5d885503410712075006001440030841d1680b600c0000c190003944280c00442e940220400002c456103066440d800380c1c0e1500c1d1010000403807809084c0f007005100448121425840c468030f0111000c0200182801801141d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 817248830 1250 817247580 817247603
    0x24120c1303053403291603150b0703030203040614090a020307080114011701020d0f06140904020f240a020123010f1802090a03060501091109030c010804030c050604 72
    0xc00d03190b080c10107582114034010910801c41ca000c12000144402c032074002001c480100501c03080d1603400c0358440300d4000c0c85c00d41d56052000301d807010026140300301c195440c10007181c400d0f00303500c061400241c403c0da500c40302d040040c500024403e4002d5600640310b01030110b990000707551031450202c0111840080c540c0648482804d42c03804112240003810124020030900f444c1040d1140855414003c030310081c4685811080300413000d5040b120034000b03040b405c00410491480002c003408143c40343c4089541c140300500840c5c078003402068062a0300401728220803046000303200040070386080d00d04900c0c20b50400c00311200405030041c031a0720b01a900005120104d16107000c140320055905115482c5030300018400580b036040c01070180c40c070080008444801c52005040641b24080c201c40c0c0207407440c000001001560f400031416250412000e010072051101e2212407409042c21072540366110040d00103295014544032508180a407906001014217038a8480c58044142d40071a40d000860 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 817250080 1250 817248830 817248853
    0x602060906060d3909020304021305100314150711062403100b0307150f051602060a03051008010e1009020f0a030f050606011d12030d0c080624120c130305 68
    0x100881000e081040406c6003941000e4012a104a0004000b03400403035a0302e020804012190504000950b03121003180c402e031281d000c80c681c4501c0e800081443d6170041d030f401301d86682c0c02490014004210000101030590b101100186810200c54002d0800c0c0720004111020761024040302905d841c0071140422071100d140281441c10301e2a44c00705c03243d07440c04102005481e50006294041c1c085601c0c009441d1072603540010035007280c1c003d00035400000025802c1100f9096040984500e0071940900d800c1c039a60f0500302e0981341490b05520140d00014203143d80f01c4010ba10580400d40090310840071810307041d012981c004600c0d0070994000b1449036090b010000104195548841b0a182000c0784681070380e200c402680c030061103e48200c5507211a142084020000c0c0c0741400301030030301070010844100001d00559019100d01e40240006015030281e03042041480c41079140e039a403d00d14005a06005180c0d03180c004e00010803000003045402d80304150f1502c03082c091400341c0042c10840340355 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 817251330 1250 817250080 817250183
    0x18070e2125060e090f100b18100201051308030c040503010903020304090f02091809010b09075405060f0405310921030c02070602060906060d 62
    0x20b98040000c01042d00740c00c25441d100c0e5540e40c0d800100c014480c81180c1c55008407a08021070941004840903c04184040c1d01c00042103000368002066a028210a082d081c0490a1700c03021503110394481b10480411000400c00710086030b0060b10b480d000707810151078070002401d56920304426801640702003014807082e1168481c4030711030005410214540512000403c03050340301401042040c8443c41d00040c008c0c00c2c20f40101d5010030004091b04030a241c1490064036880c180f29003100b44c1980c0c130a40f20314255020b9030306584500c3c11b140140f011040d0b540088900c584106078600105031680c0c0000d07003a11064082d0403031561040c0741580300e41c00c1c4404d0103001107202e17520701e40700c00c280704040d02c40f1403402a2082c0700085500010031740811508103080d0300c03219400c400000b50290045000c04c643d00da80424418405a030a40e00e5650351020100d030350364425100320a81d5001400403900c01c2c901440d048014510490b0384900d44600400c4e66805003600000700700035900100c100d10b213048030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 817252580 1250 817251330 817251403
    0x109020301063b040816020d241112100e0106050403060e03071104020d14010305010e0f0a03050405040c110d0f02430b040b070218070e21 61
    0x2240605501c4603200f481e0000740088015101919a0718001a030200400000c449102480d801804107100d0300181d14101c040d01c1116546080700b04c1400d0000c2d0b008000b03034002c102e54242903205160400c0c0c6040300c0303006280400f820320461150b14941c005001258240120300030f0501d40c445035102e6107182000300a6405250200f031041c0c0041003a500011b80e045c14041c0504416240180c40c0d52050320010020540d2a1484451308a460000410840150800303800e401c40c0c0c000380e4111142c0c54900c0e55854500d010002d010a406001c280840e0410b41c0c40b11410035024908040288140c0c4200390500c561403908100080c1041c00d00c48259030100310003418108400848140600303180b215680424507803103030700701d078605011101441c030240e50031240191110310011a591591580d04c43c0d400d6009039000c900841445011541103507501135003d120302d6003921196080310114040007520031700fa0109000d14002510002c00c4401d080240c004018440d41000c0c010a02d400c1040e1426207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 817253830 1250 817252580 817252649
    0x91f0e041e0903120f0b031b0913030c0602030c07170a020a030516240506041103010e0702010f1a01080c040b04062d030c031a030c060a02010902030106 67
    0x5003001c203151403900c00070200722084021800c0020b0028a14507040750700a034610415241c09050100d00000041198030130b8450381030882c100e07004004070b403040d0402c0090035901d9551100307096001a85040781748001040080c403900e05840390160035a1014126007003540c0c0d40c5c0c0820780c0420244104802030304480188261900440d0424014600095032940340c05001003c01c0b4003c100244905165140c01d52103503489041081c40031704010b41c0c1f1a4940003c03e07807507042420100881c0c0e031410144513558100400b4408a890340c0c2c24045100d02102d40505050110741d42ca82c82e03000d100050713207d611507041c610303c620707080410987c000400740f00d0080e103241522a010001000184e0001c02220111042c0b0304010303070309203007031040458100d408400d0320003900541160015030300e0b49a0700402003440152010400c500300300c2200d240201010041d10f8256102401040c0a80780200103040815018800401d4203400395000c45e095418a81c4191020b0030b1510f00c041550083c1e100c04980741 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 817255080 1250 817253830 817253839
    0x1701030b0a0b0d080d020703260702060112030f0c02011206030b0603010e061009050c0c0d0801060908010e0d050f04050301090b1b031e060607141e030903070b0f091f0e 74
    0xc0845031140383c20f900c151066640345c0c80d40001c1c40c408250190528821400b842c44801c0e580400e00751081030070391002c580384401805602c0000c02d5001c003500394103400b00e400d40d40701401d0f03060b034000645004140b900c007a07051200001c0603020426131400351078042c40c85001034183c142003913000c0c1400d4541900510845800007003c01c840303001d010004008075440244049583d843d4410758044600c103034409403d0501501158000c0d8a40020032941250003a55400694550b1035400b68221070280403030400d5034205001d0408034511aa015100324043d1404c224070b010b50f60030000307003110543c441c100c840203d4201040000f0424840d001c8044200555103441e5160001d80484400030003062040b01d4408103000c00d07019140c58054030b501980c0140c225070411212050b03655510031420f203801407411501071103580345101000744d8184000103002003c1603800e00ea16110b0701d42050043c00d007a0a000d024520305681e07481007982e00d0000c960009460b804900d0401440f44941c1061107004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 817256330 1250 817255080 817255099
    0x50a0605090d080c0901030e03070605010509060f061c0f09030c1707080d0e03090a080f0d0212040b030c09060301062d050409020a020f011109030715020a121701030b0a0b 75
    0x20b0b42d0b0040c4440c2d51002d0b10140281d40c410032840103800810301d01c2042c441e284804207640c010000c2c02d0340218107a403400c8858640603510300040107942e034a05125140c005800307200170506218113640c090001c2d80140340202d80d1403902e444101c1101c205030030540c002500c1d40340380350a0103062040c3c0c40c2a023654920440c6440510740318501d081c892031070f44151071940d0780d46642c005001401958103a98008148814682d40c55820035602c90000d120104903014800c003e00302d2038000a203515112180e1041355007002e10308030340420280c10061408000a8040214504c0c5581c0d08004501800040d103502c0d00b200c03a1950030101984640507a614001c1d804407000041c0742d0004103640440b00220009680c90746181022810481c004e81c03000d0080d801e00b03014407403030103499000d0440c1182c290704070394a190351004001c54510b851011100541c20400c1000049105509120920001401c0c010a41d19a1031905020b0700001d0340f0944540380c0d01e0b030170704c071140c0e003d0300034170408000441d0716072071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 817257580 1250 817256330 817256353
    0x90f10021e0d090e0c2d0f0a270603150305060406140903040b03040b060f13360b07021f060512011b11070305060109020918070509060d1404050a060509 67
    0x20703035100e03001c950800310f442c045072445440d144020b2404040c140301074040c4c46660802c1041c0503074100540070380c04030301e8008102c00350b00807031101c01202949d04040752412528001c0300340d00804032015446010a50344401101040003040000d001740c0c804d10300010180c640701e91440d04a40041c0c003055654008010820240c00d500042da5001500180044031030b44420001071002507070700c02c9c0d180d00a0364030200c5400000c100d80c048007060505560303c12803c43d540302c41b0031500c03c111195400304104c1404440202d2500c034a9658418074600469440410324108808110000c080300340e072058441c00244028101401001c10b0040001d009100821240340b0098455420f9088a82001010b9106034000a070030840c910085802c0401e842313143d40c40304180d00195000091003802140c11b0300c1c0380101e60111400040c8103500719030b0350506258048003044041e03441942080c21440d15001c0010070385011028060055220f00001c0414099501d007401c1921001444c1d282103801c101109079 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 817258830 1250 817257580 817257601
    0x3090f010f0c060b0d02040c0810050103061d0414030706061d01060e0f15070f0b150310050709030605090c030106060f020c010c0501020c031308060903090f10021e0d090e 75
    0x2e503581c4141c003c030f2100300070302c0881c291000492000e50311500301003114045542041c90b660284840200d1300b034219494000540039500c0e3b47c0308546030301c0c0ca241c0300c020101d103400d00740c82d40cc60310410040341038500040d0b40310b241d6041104250741c03466981d40100000b94100203c56400601d0850480707007580740101c040c103000141c0300d2890042c02440e51f0b4844903a900c0c515500720081d0700c1c03001904c0e03213200d040c13940c2281e00512003100c4095400b004108042c2c4000090014400c2c001c0c020901c0804204014025100c05080c510501000d00b40202c001400303405042d10031048a4014402c14024104141c00c4d528564060402c0c002500700412441d2b13030114120f055040f003800c045016064070700d80707540207101304d064050960101040c546101004c00c1c240004503081b000440700706403603680c995516440b841030f195a020f034a02111a40c20f042248000c805400c050042d12442c441151080d100b00400300c00d40e01007508000d050074011a0003502c03034070103080c0c103980d500e402e4944000a60b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 817260080 1250 817258830 817258847
    0x8061f0501110705030303070314100f05060a030b0306240a05090601050c030408030a030605150a050301051c0614091005060a03020603041b030c050915010c06110f0c03090f010f 78
    0x450400c071500c0b0419800e6401040340400400c0045d003102e56900c0c200c0001070003400342c1a420310102e030605004c10780150075000203c050313402e00c2c0101c20380d4031303d003034108041c0c0d07031000c01c81000741030726000211035070ba80500845100d46ca42c601501c0103c00b420640340c00749040030114a101c0c0b60141414032460300c500d280580d001c0e40c01c0c24101c0d61008420a11481d5010315448400c0390310000038806c5110741e06070410360440d80291420010340300345009289840c00741e030480000298052004005a18107284001d00c4041d810362440c031101d41503180d00b81a071303140225084ca0403d2007000d0100c00e90041110b103030001c804d40d404000c5400c0220001d0b49074010761001034840c08000c0080740c01e005040502c215407000317121111002a036a0303c2c10b040c86110300c2c412075103c1c084860000d08040d100740d00c04200300205030b44299a40d0055950b580007442005075007605003105100740468100315a000748260940c00d00203640b00e03450705e020041c04041100f0b1607410845003214903c0c600b42c001140303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 817261330 1250 817260080 817260089
    0x2090c0715050a02161a0108060403050307030b150d05040c12030206160203272b0f030207090c1d1f030f091e0b0a0c1b0609020a0f08061f 61
    0x10546442d21100440071707000302944041010002c460410402c1a5150403420008003082d41e812281e0703035481c0c0c047d00d450b001c580c0600440d40c10030002d40c0e600d10030341c010544c1680c0280103056a44010180704416000001e400540039921018801480b1800a09800800c04940590300c0d802d80e030f40c1c00a4884d20083c0000100180c2140c3c0c0ca0b42060003403040c0c5081080c132400c10030181582000034052080040302c3d142c0590a558840c20703400d0b1a090310303040b078405401c07070310904550f596031401c1c06603070b0400043d021030180321804140c0b4062030003511984800c590b03903501120080d03642d11008030f1469803914800c0e0340c22107401c406180c201c012a8240340b41401c0c005803040305944400c0103000702c0b150052640c1d118502160817050040fa0940125020b004c2d020800d43c1c8802c05d640454440340620380100700b1741c02409502d000340720000040d80c0d10501001c186c29445070701064044400f50080414814000010301c0191010491035501c101d1219509117480c5403041a90702d0304c0c1042c041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 817262580 1250 817261330 817261373
    0xd0203061201020a0203270114070c090606210b030d08040f020301050c0d0c0801060e1201061a120a0207080d0b010309020927120a2f0a02090c07 64
    0x25519030351190448202a0401c0080d036595000960080d2290b000d0030303646d4481c071420014003002c00700300305010700300d03540c1a1500340d5119000702d01e080c5150010303103084401d403586002c04a004501400794500a00741ca407203602042905403030080c00004100f42100c0c3d054a0400d41240550f400101459030000c0c904014215441c2ca00b00f46a0f42d584034280a5090742c01d00e81484030000040c00141041100f0107001c00c403520340c1c01404c8450010131706c20382000911104045a1900c0c000408990401040c00002400d6560f022804284c0d14001c00000c00c138180441c0031216079a904e03104542c0122503000c21842d010540c4e88030b503030500540310507040440e41d400119805034081d5200e90441a0020409051450582035000101402d032403511134107901b604080d13403040400540c00b08074468610649082c0404d586040f00c5400e002d0301481d041915020b20040104400d1400d0745801c4480000b411350000d460041c49030038140035003203c80d02c141c10080720000c113140c424200b030f081c2c883c41e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 817263830 1250 817262580 817262587
    0x622020109091811091302010302030702070f030b16090f14010c020612010503011505090c03090132160c12091d01140301091e0804090f14100b0d02 65
    0x1201c12050310b420a152251611650030030700038100100120307540c42900031001c5001d902c070038081c458005490050740000540c0a0380015806034024541c06144d13441100c4080f60340301e12080c0707940d820f5802a10150000790034000012800300c0407420301692410440e003014034208001c5820100c520400a480c5900d282140b8243e2056046501d20b07030b0002c09050b110410319076804c0c00b4a00a00c1450700c01d40c07800e403a8544200a0100e1101256401000c80d010b6070b46034200000294001810350403d0b5507909400d0fa041c00b5410300b038400c01642ca8444499180c6454118051910064610003884080c0d5045c1120103174020304403058142c2c4030700318041101b0021000e451242c40342d00005a003895032400d10085c085081c81c518101c442d0903291040c8060460289800c030742901d8000750818070b0040e524100d0304c5050048040c0c0911511074286001e90301c0703512104407080e03900c0000c907031622141601d1650980d0079007150402c900c0580d81c03402e14601b000995042c41181c060640141c2c012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 817265080 1250 817263830 817263833
    0xe01060e180a141b01020133170303070e010207030c090c090503030d09060b10051b15040804080d090b0301061b0804080a170c0703110324011401020622 67
    0x40c0b001250480e445031050110199200c0c2190319a500c00ca05455a02c0da00041d0500e21740c41401030201c148075010382c604403125110444c580700d0324821881b4071681c13801c440005a01d110a1008038079500b103032020316140c0c104400001c05225100340c43c5130456000321130600205502160081c121a105840054034021185013503400b400ca03607001e07592502001c14000b480366510341100c0f00d200d10a85080040003036100c1082444220042007000040c403c1c0031400030f040424626807603001200040740c4031000200307800c8404240c107c2d070843d0320810200741009000002c021102c880c0c1c451b4208480309504110004c035a9000520401041000c000c02c041c1c11071a240304060b100641007220302e507a41da10342c81c54039641d14405034215216401d50001001000782030041d640c0404060004d001698030315100e80c074210020301c0c0c00315458094041e20302d5444c07482240c003071306500070a403402d03c2e0b0b50316041015202d004071a09a42c1990071a000300100058800241c061609043e4003030b1045042c0c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 817266187 1107 817265080 817265083
    0x50a140f0703050a0954180206030c12010501050f09010f05090409050c0102100b010507021c02030604111c020d0209190609060503010e01060e18 64
    0x384070700030000348030300000c02c180d6145190030754402e6210810144c850510b8280d090703400002c91007aa804003034038080104c80d0f0303503019821007001d20001400000c0151150802d44180c0e80d0351b0501c004056541600200a500601442d0300c82c6400c0315100480c0d0310000c034119000d031490000191940c400d008035810401406d0182e41811108001511010012032403041840f10900c840300240d140c138803e04a01902850042a10b160100c0000e410140a640341c800c245081411042c4566008021100b4155059540c51440d0000022104041e0702142000f0340c1805081c003844103100b0756020701c8100c42c20880c0c8080c0500c0c00502c5000904000c0340c1c000b5001107501c0d13007000243c50519605640840ca924841d642e170211a00c910045442a40000000a40e40c040c140582c3c00c003481020090b00581d002001554200000c1c415070b0700c8001c29103000d03016126540300e00c1100 = true := by decide +kernel

theorem cover : BRFrame.Cov 817086330 817266187 := by
  have h0 := BRFrame.cov_init 817086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 817086330 ≤ n) (h2 : n < 817266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
