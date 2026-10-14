-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3297
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:14:37.418135+00:00
-- url     : https://prove2.me/submissions/11f78ae7-6bef-4399-b066-43d666919520

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 592805755 ≤ n < 592985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 592807005 1250 592805755 592805819
    0x9030c06020f032b0e0102030402030c01021b090406021e0c0615150d060504020a020c0906030304061e050702030a030f03051005130f090605090a0c170714030f060f190501 75
    0x1311316000c030100101660144500b104000811b4000d400403201640130b40a0001c10801961001c110a100c8080b070642401451111000388510143c00510466542c2d030700300b0081d060b000c0301d01d07000000950102a800d44d10807003070710001d04000001d070000000a040408015541e81d602000380380b820100030078503456510000b0040007034256030b8403850300140b00090303510341d40d9030220708242624002d69404c121621400141640c0c1d110f60309c90b1100144600350041082400f200144440c0ea04901c0c01d141403c5094001a040222031a422000700d01101101280f55406002d2260300445246200c1495468000410301a800003440b0072a450360b0b9001d440c2c00e9080961101d00724903008441009945000300085030f4400250340706884200000f107000816240d9410754547c0000c2140c05404580e01c2c041c80c10810408045042d5418041d031b03803041800c0703402003200c0362207041055039584180c02c0c0415042c440320a100c091041190810b80148542400e40041c525055249000000c1840c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 592808255 1250 592807005 592807057
    0x901031503150b09010509150d0506091b040506100305092d1203091b1c05010614060a050f03040c0b0d060303080604140402100212040609030c06020f03 67
    0x290349108119203a685001c824000c404145080c00014010200000904031003041943e007024418103a21004103000200a24110545006080409090001ca0706101c0d0799090a00700e04850403402c540c07110281d0100c40b08600c0281c18072540a8404220504180003c141300d071035160003442c28036407200007180e034080e81042041881d85001d50501484c81c621700748031003500708034907d9446600c10251455a00c000e0f0604490044040000501590015080003100d4401250119a0005d2a0920381410101d04142042400c1c810000041d050b402d180031150701da202c04103424060b940070b00843c101160004c00300c17002c00080c0d1200d552296160300d0042561a219009803010030008038114207482c030035800c527201340c0340700351100c900ea5501c12040c0302c11180c040001d04210040c00d004a0058145010401c11710217080c415030704c0e41c1200c441120308550040e80884005080c0150070414003089150010107003a0a20203811070f01541880340340d5a0041440c494111410040c10004e45 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 592809505 1250 592808255 592808261
    0x712032f030703031e05240f1302190801050d060b030a0c030b09071409040809210c0a05030102030f06090705070b01151b02090c07050316110109080c060a0302090103 73
    0x600c08003125500c0a0700d00e00100544040d03d0003c11049003000407031103c22603070151500c2911078810ba1a180d00180c0c41c02e40c00344c031240c0070b80b540081e00b540c01155181c948001b900e100d441e41d800003513900e0039125040c00042e0324021308481006580c2005005541d50720009199068000c02c001c690481b0000001e07080c04041c000c002e19038049040c0000800844226403403050340d0341015a1440b50795010600501403601002c207506c100140700160024450b000603040190340513142c4101039480040014160181c401500ca07035034444901c0701000d20b44044414041c000c2030b030082d4250300340b44c019001c1202c0c01030f000522172540b50300007a001607ca1f20586000d95000b000c0701c1e0040d40c3d030303c1160344d0547c0300c100782c3c038002340140300c5103c040085041c0e46907580e5809841000581c0d82d48120f04d046800041c0200c46c0d0740020044801c14000e05084074084034062607a00440705c1902e000505014101e520040315030f04000c04031800d40d5120b9058a045401d070f81400350b07a80840000482c02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 592810755 1250 592809505 592809587
    0x190203192406060e0103050c0d090c090c0c020a151103030f0a06080a12030b010c020a080705120d090e0402120d03051515041703040b0309030903071203 67
    0x521000401010144000c10703001c8080c1c0801c08200320608100300600d40151100c03400341d0000300c0d424a42c000315551207580040c2e40154044a06814154500c038400c0641c0c102d041c00303075040c10904e20240103000705489902d01020705130034000b8031a00682d01248480760b440c4214007a0f900c0003403541d40c00e18003e001c071100300032401094a5491038081454500800e09440011324680351860100d03914000088015100f0740250411226101c2164102c0180c450840c20034104002c8140b8200180c072203400d5040130f40540409404c0d80c0341018184003d8203241e10040020b9488150300b40c5907d03800c100302006030368240402060664450010412202808085c00200e218503c01c403503420b43e055000d2405410714000c60b40000040c2401c12144d12405011401900c20821040221141c010351858a00c00c031041981d08240d07176042034800c950000c0306c40000796040000e51102503e41400020b000c2e0010540da1b40040d007083e24000c1c900d00c0c034808000794035010303103021142d072140106030104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 592812005 1250 592810755 592810783
    0x6070f050f0a0b0c0406120509070f0308180a0302100c03050f0a032a1215051f0809210705070509070207030b010801050702120f041d060918190203 65
    0x404000d9003201d0340d4030896039083e503100c0b10f1100407407480752030701c0102c50465003560f5500c120701d2140d99002c2c00030300000c0d2204100f4450000001008028200804021030040c030308951990710940800c3d00000c0d00381880c3d440b0f484442002d01c0141c0d00e400c2c184600d440035290084282c841890103a030a885159014018040045020800c0a50507084580601045001e0040c1c89080d49102c0711183d4400700c1140c00700c2e1480c00002c1c12000b0325800602c88800d40c0007403d111a80c2d4070080780440b002d0200c0070058600c6100020500c903001180150094541e03801090b20401d000810405c06c0c0300100910016240020301405000d010040c88001d403c0c001e0201c0a41c0c00c003042c0103540d480e03081c0700c00c03241c182020000164610061040610500080e00038014580031802d00c2526544648100030718400148000700b41c2c0014000031a5110046020074011414a00c08004400e40c00600341c40c011410036800e4446048041611040000c19030801c0640d58000d00c0000e04210180c14890 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 592813255 1250 592812005 592812013
    0x60a030201142b0e0d02010e0304060f05070b0403022a011d01051306031a0105180d1506060302040f0e070c030e030c0303160308181921020a0309050307050f06070f05 73
    0x24440a0f240d1141c14078801000454410001105059090315402d14006616400600080000c5801003640700c80701d03a8180f0b000d62404d00a0360360140d6000054506400582c480c80350305000000b5416103031080004c0665003051301092100080c0703650000800c2ca100b4900449a00c003131a4083c0044c0c0b5a075881542d00480c0e100e49500b80280200f04032500700c0314036140c64a0034801035008004070381018016100c443d9a007120803042c05048007854074205c0d4464080003040003092074510490300540201e5a002daa5240b51000100120006800c20f0881300140418056a2504803c0305c190003581410107021245407200000d051107011006181c160200140035414500650003005015200b0388400b00700c5e44507941e1104400000300000d098503482000d004480711003200c1c0c1000002d20440d00b2044c1c40442207046000184400300302d10240e401010000c04260700049608084e001c05d8005103190381c90080000c900003005a41240100c1001900b02c0a00151080c07103144150820221 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 592814505 1250 592813255 592813327
    0x182806030b22270209060d1b090501080724081008070b2a07030b0a0b0d030e0103110f0a030b06070615080d0311030f1510110105060a03020114 63
    0xb0303802030030400c0c00d190038501c600b4500c4081240f40030300340300505401521946295950f64140550050a9401038561024031650040a180e4080c100e00142101c8074011134654500300c0307143d02e00070b040d41000084c08013801d0b20080c2c0300480801840d440f4454a41501c0d01d44421804030800b421036000590240540b10001c12445607810040442140c0906000400d007840102e03150310441d828120005900803980410100301e10780c0c5503035041076109500050f103900b90000614812040c000841c003180040f03c03981019a0944a801e10a84040603003910748006e015949103607108040d260002e141d9950114849501c400c819100742da40c0c88030007005805003081e00e1448070085482128060301c213801a0755602c034424015082900c032113085440c00d507100c01d01c003030800c45001805403c2403243c031110720034595140000801004000d4550340d6030340d82c0885480307083d81c6005050302c2c0141c82600e01000141d038030a0b2141e4206805406a40d2292182100f500100219140c04a10750ba07a60b020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 592815755 1250 592814505 592814569
    0x3122508030c1b01151503020c070e0402130b030d2f011b020c03031803010b09070f02150402090a0c0210020c151311060c0111182806030b 61
    0x1020350340e80c0010070003480c1d11a94074050070303100d0786519176800002144013040001c80400308050140700030304025050480750140340d464042c440d400300c1c1d07040d44180240000d60904900c0c1c640044000304007031001c00701c1180030a6880100344400800c00c418070f143d4a224440b1011242e0020b8840188820525400003405000e412030045554100580904015140340002181c6002e9400540a1810400308280031401100340c0b01303025805540358022600d10b0b0340c44982c440e00c00e1030a81c54124046c004490300a103040ca030f071500c2c0901020444284070169480d005615805006004003203003820200d0422800c181d01c43e404804d50744e002159041c110000810300c4040071040b43c0003d038841e03943c510015a0140515405450f00e0000180741c01c96040c0000104411070b5540000701c1c50144208014503268000982514000d903280242034440c81c0c00501c0d94094074804480582c01a041d01454088980c18803415060503070b00c0301c041e100798a442e0345845005102241c150b004450390f100b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 592817005 1250 592815755 592815757
    0x80105010305060f090607030213150807090b0c070504050a06030b0c03011e050609040b1909140c0406020d030b030a1203020a090905071706040b0409051b03122508030c 74
    0x2203542d40951800200c05400c08a6080c1c420a4014002e00190b107440c1015002580034400c801200400b0480104030400904c544850f26030b55966a040c4901d05a600202180240d402412075014200101022403c00140c040156082101c00040030b4407080500d900030107640e800201413151500401a08410501c0510b040b920914007240c03001c290b00f014111904290302600b9402070041c4010065070034964001c00c8840390240010301c0d502110182129540b40503800b0681840e16200f008034aa03000321091030700700320b5100c84282883e041417400703502d03425005042c504040d910b000c0107090742d07410816800c039560811301203460040c41d00c3c002000b80d031001114030089401800b002491116602c180c9120b00c04d41da9a1454040006a2285c480c1074080e0080794415200d4994810aa890344601c42c0501e1040c0001c102c61049010740000c0c401c820070416103c0d070000c504a2801403640021100700104031003d2504e00041c585900c8600214054060910340b0302004109080b41420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 592818255 1250 592817005 592817009
    0x160609050d080c210406150f05010e03030901050a21050a02030a24060c08040b0c0c0a290705190b01060e030715080c0c190312020309062d0108010501 66
    0x540c502d0350a6840c5000c5920910030410300700e0340d09150f51562040c001116000700d0304103100d01c03000320303104208040304242408103411200d041008800c0070886980c105500038403101042d0082d40c142040f50300003070118002d91070b030344060010703540b01c10804100c02658440c020f0b10840c0300b0009400c1c9204450003d40003181c1001e5401c0c60900100b0001040712007005890b01000301800c4540e0030700108a40780c9000031710440381004c1c28803002c04d00c549800c01405810130140020300c0c0750040c0d0b808001003010903600514000300c4164222402c0c038036281842180224847e542e6035140c14609d407403494094031040200d82d100a0600940802911204d40c504070b440d0750340c0d55805140c0c09010952140c6092042082c084210210032012901803440c0c40c1d070000342c88100f036040415205229050003a42000c02503007075040d916100c00c140e001108500c0410804404604504d0040400c40d40c40d1005420300c0c0d800310301010800c180c0c071080304140842d8030403510f000740c1c07550707650384518040d00080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 592819505 1250 592818255 592818257
    0x3010e04020f091515070b040503070203011401080705060708190e100905030604020f01140c0a03121107021201060504060e0a0c0315030b090705100e03060604020f0f160609050d 78
    0x602e020400c0d14062007054040c801007922040300415010070400c042000807003c60700c5200500405c000b10b4002c1803518805d030302030030180d941e0750010700c105421034041e07641c07000007850680011711419200142541c2900d90945600b40d907003415080881d140c1c0500540303d2142104002c124143e01d500c0580c0358032244040d1580d040b0a55543c2080d210310145015064250384140c0c0000c015103440280359281080c18145807058290308112008503a02807120311056a01c2a0000d0f81019400f00741d03040400310084081104000f0700b15a00540e10030108083e1282d6108040205131400030350142005080c010800c0bc03c281c0e440c2d040c20840c4030201c0b01011a1841c00d102c0034510390080c011407403950b0140080e14003080c00e654603001c1c4500003801e0305550380309400c00400d040e122100b0b8102d10359440d4441001250a0304105071600c00010419402075005020301505100103a050310f480501c0c1c0307081940c03103482c07000b180c0c01c0b141c40c002c00241c445401c0c000300d03605111f00410a00d03030741030079 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 592820755 1250 592819505 592819519
    0xc060c0203012912120a08150d080a0210050705030c0304110406090c0305060a0302060f0a05040306090627080a1407050102040f150801150302030405150a06051c082d03010e0402 78
    0x604242551030741310006200400b03020800c21b0182c041c0c426491664410a800c0c0080c07001d6000e41d0220344515002441164a500000b03800096150108040100c42c0440d100520081c82c2103100102a80405441001c6000c0007101040810a4400b600d003040e010140042101681d203411580140c10800d201102092904010030321605059610310b0031f480e0040c1c0010f01e0320742c484000313500b268000356000c1c04100c0284404000500315000718121035001740350200c0c400500c4c4c80e03611250381500012840c100d2420071500e00040880b0306803180d03008242001c50312a003240040d1a0f6501c11100000c1c419480000c01140c08080f0107a00800c1d504100d540110001c610305c400d9079200401c3c00765070502c1d520b07135601842e42d600c2a001903a01c2441381065600115600b40780496020040e2440c4441e01c0d01c2d008144183c0c02c1c044403071300b2034549041e00d02030800d09580301c5c440a4802d080c0e2a00400120400c00f07540020b40201c403149042000c0d42050390380d80d480c1500b200400d02075900b280300c0e620b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 592822005 1250 592820755 592820779
    0x21902070f0b03010e0402061303050a08040e010b03060d08030702010e0a0b011a160f0303020f0d0e0c030d0c0b1005030a0b070810062f01020f03090c0603040c060c02030129 76
    0x900e040a0324142d0701d02085d44180b548582d02045419001a1161280d03c0e10038000480041e0080c0f1019468920541149444500700842d4588544051300090200700007441041301036540c4400e00300f0b501d40c101c0015a5207845120040303003d003403030114455141c4a01411041001501d500c000c2c12616003142e040c2002e000c0a0303400780540305494007180c80c0c42c1c460840c1d601050304a0040c0c030000e40b080c10010318003039a840c5110500e410814401420580c2d668000006030014030103081903480c02c40c080c08000fa0300c0300e4060454010342402400018140001a004a110f4000302014081c02000c0b1200c0710704520f024605440100c6110340014545000301e0a5030b201041c81100352041901c0f04084441d411540885940880001001c080b41c0f1104065203100b080c4000c00391b0307152004000360b403407030714a03003a900c0d0000004125002c0c003020020040425034841d8403005071400751801c413405030450b0002901400700400907100c558103000b00c5d1a07840c804200e103808038040580d10900c400c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 592823255 1250 592822005 592822019
    0x1506030613080406050a090f090207030f0206011215020f1c0c05030403080115020c0604173d0b040f05061f0e011808030408030301030309081b04050a021902070f 71
    0xa01d0140020030051042c0018081d4601413400b070464404d5915005140300c0d564401c81149030642d0380681e140340d900064a01c2410b92000c0d401f02041c0c00c80c001011154980769400451412048000c0c002645211106015218540407a607070340700010042c41d120403250920001e50f10604401540c814605030400220500401c00c2c2c81c49190113803680c0c90140e20380721100c01503c20641c88176046004003020319400380e90700c3e0003420140410300f02c0400b021004500d041d280078180600c4074804a844200d4810098a900640c400c0103140d805424114074000a072101400050722165805800c250090f0094039281d40a00e208803000c803080c4ea0082c1c8010005502101d082c101c40b400606841000884d9500814861690103400009440350a42e180001c50a5400039001902c2a400004c010000d241d4081405400f801c9000e0107000110f180100d1281c0c0c002c0d424400d1070265845070b000901c020082d6055907852204548003040440300198029220b207010b0180890380200254081210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 592824505 1250 592823255 592823281
    0x9020a0c15050609130206030402360a0b04060f060c0507030c0305060609060f0a030204050c090409140715050a0e1c030c030f0207260a080a0923030d110102090315060306 75
    0x26005840b01d2318603122902802030308510709a84040982d200f40a00d10501c3c00e1320b107651441440c19940200c01d0070003211030010380303a82c041028403c604000003482400d011605031011141181801620304515181603070400031264070151001e44104800400e000c0c1c00316005214000855210210740d8418007040182d50108220a410a82c54181400181032550040b070b0040304c001c561a003005964030014007500c00301074007241c014540c000581440002040104003500092240d0104080e40e030300010241e004400040e0b040180090b541c0e09030341c907800d505101c1d8045081074401d030b610032424064802401d1850440000d44548070018500e84089046400e6800010140c4040a1940301c1c0001c0078916030320080650196881d01030010700d4020003000484841d44445c00c04900c0c0ca04000b10301e4900748480560702514504a1784603a9001c01d00152a46550070040310007081000301e2402405803982080c1c01d40329a900c1040340076114001644619001c030210342c072a6480301201d41203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 592825755 1250 592824505 592824541
    0x60b0f0c0d140706090203011b18050906091501211b09050a121a040c0e280c1107092702010906051810200c010909020a0c15050609 58
    0x48840a03c01c59000505541258105500090001c2015000d840402c0b10f00180810040d0220b400c3c00441002090316025100040204480500c503a207040d00120b4089500207003041c141a07072041405c0f2041e8060700300305400d02d000341d1a1140d9800944a40c00c001c1400c4401e5442c2c800103206000440b078407402c1d03035409850b0064504020070307140807008030a4450304102200d61000380e0006e264082908000584124010b1920280d014035003404841d00100142041c9000e0145150b030360b52003c030044142d04540074841000070342a42c4e440b0308481c0d407005485817030094001c0080c0080c401e18207401403054078424000510f28046070075209070110040b04c0f07000340402c403425000c0100501480c060080c81400d001c407070011086010008204140b070000240200d40d0310b400c41c0054046451684d091020184010108803a682d230001e000905648520104690001807405010344150003c2e01825402640780087e001441c02800140c88100c4900f8042c407441c40024400314560320030200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 592827005 1250 592825755 592825787
    0x90103050c060703030b12010501051503070207050108090a02120c0a0909050a023d0f020606091f03080301180b0303120406050a0e0303090c10090b04050d06060b0f0c0d 74
    0x401201c0d014081d494104950503070038165107401a122035102d208210391420321503000040d02e0746c12b000070080514041540340d25420403c0c0200540580c001507043c050307490034245510b85503107050006107007000170400250083c2107007401036850310000420361800c100c101c5015000030340f01d8176030000304e9154942c0a06070351700c011a04009400c0880704030740f0318100140d4030b1480080100ca00b4403000079072240c0708203a001d1020b2905020364400d015407480f440c980301400c85070a000001a000326005400c005c0d00c2038040242040c10711100203090015544400925180d40c1d41d0051076140115a2040e000c1603804d01442d0075181c9070120032180b00340b49101708405141c460744c0301c04008041c010403400d6060f540d042c43c03500c144020409903115580d1980148100c0d19200103000d4200150608201407086489007809956924010784080d2482a213811f0300303007a55805d066020f000190710400c190900000c040e099090790317800500451a660007203030703258801c070402200c1c1005440c4c8148 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 592828255 1250 592827005 592827013
    0xe06090307090c02010e0a03020a02190e06100203160b10090204030507061d0d11040b100504030f1e030203040e070905060304080c1501060c0b10080307020d051c0c1109010305 77
    0x102c9286101d40c800c05a801c240e1000088004081c540c25107042c440c0541900541d1044102c0d004610b42048000c8504038611a000b2a0510b825220441024080d210600c50701d8014018041c0c1071003007041d18a00034840e84c1d004840f0416050100c42080c00340c881050302e403400080841c04410500856040700e503c00005c100a41c90494200d030342e80340c242c0ca07101d44801846214141c40da103916000704250f000d140703011000014031040004580014102c01d0003034400c40300c22061590840c0a480c00c076500a602d0b044140c480740781c080b40410b01c10b890781030b19091a0001500b81580000948140ca8000c09148046d88810205403080d00c00e40c42029070141c403c00004002030382c002c0180c08208031034011589404100c0d50742004600c400d0700b181c3c001880400041050080c034503051504801000d0825800e9424868030584a200d0080080d0082c04604e0785c120401600300401c01041c038110a124031644024030300240072020582098640c407002c0d4442e40e03014079040704014101d0742d00600030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 592829505 1250 592828255 592828259
    0xb0901030f09210c05100e0c010e030637050402190f030f03170c090a0f0b04030f05070b03040615090506010f03050c0d020315030d020703081c0605041406010e06090307 74
    0x90f4860004000b032071010451102c00440000e031040141d071210400280c00402c4842e12200310034942140c01840a04000f8043c070b00d04010745011400f160058202c4034061580d43d000f096805007100740700710b112040307501849a45a2010300d948158000c078401c442d06d050100d08480c06040100c62802404251072180008100041d07d03089940080b900c282070510300c05415011b00200a48226a401c0b000c50000690072482d1821200c01e501502000c4552503e070303810301000d2070242c0128003000b4843c00c3c42100780703401c2c02810806200106810a0143d680f840c092070070354007500580070600c402c03054202000c07400e09094086e0381c0c0b1a0310182d40d4000040540d40080b405001c002d05101810300c001c01c064245000703240021441a0040b40b20141d4021050381490710300040408800300715088000148000303083d080880f25621004984962035603404080c0e5001010594412613000d8506001040c12036000d10500d846020242c0364489101d00180510405101e208805545a0440501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 592830755 1250 592829505 592829543
    0x2a070201081f120f080a182c060114030403090e100e06010806041b0203070b0711071401090504020a11013209072c1605070201030209030a0c0b0901030f09 68
    0x43e01c41e03410301402e0f0344911207045880c1c1402550003c03070400e0004102c203442c442802101d08130a0018000341580c1e48141c00401c8075000300501401c2003420700446a07000c11782d96842000308202080c1d0117040e06a40741014980a8008404c80c8101001c1e0003031880050581b821429024048070098200c00e800d9540c0c200044030b00f140010003681c0d00c0380e0f50340c9003550388180d4000380c481d000d8281d07001180d82e44d102d824646c0102c8401000b5004005540c61804001200403804408484506400d58a032008040051391800101d0b04003a4200344007281c034036100f9a10645030405110b4100c02040003940e0822103100c19003403010352828640d50b40743c1180304012005650395008141800791140a03480c0c3c1060225041c40b002042440740e40004981100318018a0058024458800c1d00504401e81080a881030040c844083c0c14544e002c9030403074094030144110303810b4942c004c00d0001b441380c03504111a811303040082ca403400603190030a00440c0c4a4140f1506a469812800c400c2d0300d103c503100c3e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 592832005 1250 592830755 592830779
    0x302040506150c0d1103040317070501022b0e06070e010e030c100f08070903110103020c0f161403030f030f1e07050d05090d0f082a070201081f 63
    0x100c0320760049409020b40c50700442110160441070507a001130702c0b6240b00d952004060b20121800107209400811040000540803800c4144540d00c4001e0192684107606146009018140c01d03c078907088030100082485c00a0740607080c0c4d21007040c0080107007101e03041d41250784900413240701001c9940880c0d980303019800f50540c3c80040e08002c0491301d003122158041400158221100e0f03001c41c2c041184112552b0700f045c00140e01c00f80d24607181c04c090b45152580b011003051550300c9414954001030700c404c000414460088000001c20886559801025031100c0205042c4128000351554000c1454030f498040101d5003086001d080341402c640f244c4070040c800c0a40648070a58072402c400e503a131b0002c0703185c1001b5441240152189500d5050800700d503001e80314001c01003901c40c3c014020140e81d40340c00041c00407145000e440c001c4502d03039641040f030076400000e00005400c0072024409404109580c401400b0702c620070390b601c2c035154968045a5a035906040d0a10344c00d0f2940100034010102442 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 592833255 1250 592832005 592832011
    0x806190b030f071805160207060e0a030b09060103030908010c020309042a0c050d0c08071506081e100e0a1514010306050417090102030a0c02030a050717060c0f0403020405 75
    0x2400d540700502c2c40310410b4500602039100058032040300c0349500a1003224881c81e54031509004440c0024580c20100a446036064044c4200740010222911a6078a80040980103503034080030142181c01d00301c4420707542d07810034030080700060140500401d400d0f4040c0100d800104003a0000c604051481041000ac1d02c000c1000c01c268400749c94010f01c419030f02829850b250207454803200756414180c03d204e810150103402410032700c01016625030010310280d044424203500000340003c82d41e5024030243c0505400d034020112031241902c0c0e4502c607068801035841d804405012104200d01244c0b40303100390380c00d440d40c11b40700740c2144220764041807103402e01c1c03120700341441c400003018408440c0514038036201707030400d071b8150365a5003c000030000031041d1141c601400c50552410f145030000000d6a9100c0c03c494241004003400b043e904644082100b580311a60002c107640340e8a80300d00c402d0780c80400c3d4080701c0080f03220320400316232503042c0d00c012100c0d504820001c0c3c502c0d040c2182c0070b01003e0580030b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 592834505 1250 592833255 592833259
    0x90b03190c0503193e190e0d0201050306120a1416142809090c05040c3f14070219030c08030c0d1a0a09020903032a011b090806190b 58
    0x90178405c0588203042c03004100c0d80000c40600c05c194502000c000300403090100030913019117a43c61400d0050b07a0094240c0754410b0303088601084200c10a8180784c2040c1500800400245003251068560703003003c03a081d0000c0803041c021150840da180e900420310114042d265402c0704184100c0600c1141d941d0031050916400390900420654402c0d4081c11070760380500544180e00590000e204a01d001d0141161700c02d02440e10402b95240f00c540c80c0e80c19032405e14009904084a0036042c500801240d440543c951428020410b1115180c0f0740b11401e60111003210043c0500d5100039000000c84501040898040e40d9070413145103e40e81d03030780c0180d00141600503130500900c200d035103a080034040e015840004006c03040301041403c05001e0b03500c0c0260050584180148040c0c041c0c3c0d10b0010030348400c01c507043c206454903240e6200d20700c045880c0614005040d4205a850880d400c4c407840143c4c4201d90690b580c036444c0e41e41d060142d0b01c4e03070b4044d0340c3c105100b0f03200080c000c0e880b00b45800c80c40c154000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 592835755 1250 592834505 592834601
    0x80402060705061302040c03050907060f120f0902090906160518060c07141e04020711150703120504080a180f24020d090b03190c050319 60
    0x78a440b8146030580454009002d0382c04030000c0000c504241c040c2c05030321403490800f481603050000c5a00e4841c03605c0d0288000f044511402084460700c18034500c00340c07104031241006200103107111000940002041030f4012050040850801c07580003e00704e106031007401f03620000802559048480d54010f030032280c3d01862070540c160003640e4603401031410071503e07001800f81c0340c5090354409030900c40404441c41030705c1c2c5102e02c140782501d402c0b0340079044408940042c0e4555036450040b0404c03901d9610150098010602c80007140c9801009081ca240641c4420f85046164580d10041d650304443c0107291503018480c5c50356650141c04900607040d545c101b000142c1e912600ba03501d192640d40c9c010595180800031400901c076401c0781c4250300b1092440944805000b0030000340140c0620320070700c0d505920000010f00c83e113880f0000d001d06000d45160510504007420340040c541c3d04240c074025907040d030440c440320051050f0f00c1100c80f10082e40ca040728280d640144180124000103112031000d400c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 592837005 1250 592835755 592835767
    0x50c0307020a0e04030206090f0c0402130806042603040201140d093e0a061b0501151401090311040c0203090a0602010c02061609090b040b130c0e060f03010608040206 73
    0xc0c076070a2040240940360315000c010315160500a07e41070001e020320042d0b40200000c0c203040800820341c59550f490950340035030b81c1c0000702c02000305a80b03540d0180c8180c0c007505090101b00820500196038688800c0741d0400c2c03600040043c1c1c20365110a070b078001e002c14800403a00407441541c6001c0c2c40b01c821400070006003c0c281b5104d10007174144403008809000000c18881c1c003c0e0600c001e0240b0200028107402c003810801d44040343ca040598041e0105118501c11543c0b4804001e0070504e01c450782c030500a0102c400114807611a1035040d003e0541c800c000b0b544201d6455108055550031030750880c40c030541d44c0321842d0a00008240810101007140020480c81c0c0143c0c490480000047c00c042d400011b120000c248024108800640b8007018400025803c0c50314691200354001540d401d0480001c5010680000400401d04001d00790f0b0848400c1c0d11580c0420419445403a110b00c840e1507500d06100c1e004200100c0c1c3c81908201040788409200601a8921890b03845620a2000e01103c1c5841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 592838255 1250 592837005 592837009
    0x11d0a032009070504090608120f16150903090905091209010e180103120507110906130903120c05070b04080a0e030307051f0603111036080703030906050c030702 71
    0x90125480303c081100010208000d1038107115006c01424600090111584040c804a8241c41080e2825101d5080820100749000f80305114032a02a44003005401c411071505902e000b40c0b40e10321099010501c825170002c2e0442142c01018425100c1c80d0103042d5030b41070350030581c28030340180c0030301410410010801c52540d140c05c0f40c0214480a03640110310726624601d050b0710140e00d0700d640081041400c2c0003450018103014419a603600301250700d800b040d07482101054500d12040d0002e4a030604014203034040c190015080d004044080c0c000b4080c01c41100015200c070300c5074040050180c107443d000103001c50340e008080d1040001e54580300c14400c80c1c0b81c000902d180c10044095038950044140b2003a50803007001e40106600600100b400038500d1500c4280c040e0420400382401580310084003c1228481e10362211900600601e21111071800d802c00e4481c142c581030000c5001000300c81c003140c5a100000c0740004c41e0790564a140d600c0b42020000c407a107410150103403150f4442440340800503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 592839505 1250 592838255 592838269
    0xe0117040b072a0c08150c0a170c0903060c1603051e040602030307030c210902030c040509010603051614060f0d090b041505041709010c050714011d0a0320 68
    0x2c400c1d460041d030f82482c1c02c1c02e001000c000594070061140e40088600c41c5000c01e02e000b00f96200314038100b03240e01d454451074281d8101d030700d1b60603000c5814504410444200048000f4040c00c0320283c048910036a500c4001c0000c1d84903484a000046500c3c07181c0a001078820310061010303903800c0340700d540100c50000f05108241c00c0b0b03410503005a0008020000c500740d0600c18a44251120315094a04880c844c04682d6003d0600390294020b54407101d03da42903440802c0912260342e0043c1041060340b0b40240e04500030440c60004852030b00410b0802094450094110400e507011300c5c81510a00c3d15807c10400d00d80c0c81240481082d00060040104d4540d00f0710803400003602401240310780d0f141610704502856098510015110702d05018040410f5400e4038008186546c038071895602d5000c000182c40c1a402c18500808a21800102185110000e0200c4040050a0300d0308103138034045a015840d41c4800c825115081124003e041001c5400100c52f5500045100e10142880c40702c100481c2d41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 592840755 1250 592839505 592839557
    0xa0803040e041403191d090405030c0d0503060303180111070305010b0a0b18062109031e12041502040801140105032505090a02040b18010e0117040b07 66
    0x8500c49140400051154203c2c182a035081c00c2000385140a2000c0d41c0c09600f990a0a100010820030742c040a110008a0041c5852140d00401da080c061405203800c3d5034907444541c1c2c05503280261100040500d000d6001c1d24003d1130028091420701e440c44c403242c14004030400e5028100440c0344402c5500060600040d0055400f510021074078490541c14441d81e08000c0e840009140c1041001c031a42082c0d07050b44600001007101d00301d075604009101e083d80040f948003d110008035030700500c240110000300070309040e09010503601c0a918142200c815030300400031200c100042c0c080002e40003425074040c0410300070582000500b401c0c9c88451290131108013402980144c100e4400500480c83d04001d10311142802c03140c840c100c81200c0c040700030002d643d0b1003203034094042c2c4000302d035085940c2e0301640d0161000d0b541003901c0d01d07041d240140c07500b6101407445010954540c91000b041d4842ea80b1400c401140c1e401440d816181c950b00c440c41c8020060482c003c102c1204220b00742030011000742d0b52 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 592842005 1250 592840755 592840769
    0xc091502010204060e06040b18150c01020306030601050409080f090117040b06030c0405070e060f040824010b0a08040f0f0221060a020c0a30210b06090f0a080304 71
    0x10f2240e09104018041d0020203204505c07540c1c00380420061094004203d8240e1034000e1b4a02a030907003003e002c1a2000c00c0c0d03102e4204040c20100d2031100c410b005501440c072030340c4100d044030541d923a10424042214007100001d801c1e4078007040310086600c2c1f8440200803405040c0b40901d107039004c0b0303510a510500161001c46a0745221024002c403071504020070b89000a040b182000f0500b810301d4003030109030400c1c20540c05540f011581c0c0d00b43d410b0290540d4001d000c0079080e10704036001320700740b4004031081d01d051110103140d400006c40c10b10340c040151110008161592032241e100d5854161910400c1034045030a016105054401601c03151210f1824412022036960540d050300000c5041000041c42d09050b1071041c00710324084400007620503969a0003a0310b00500c041c08083c140c0d81101d410300b001d0070a03c092401800ca035a8418400f070350702d02609950041845c507071020841a07500c0041070315401001402452400d14000e01000d00ca0b44000b46003601180d035071044141950003681c03040c1d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 592843255 1250 592842005 592842007
    0x906070f060b011106070c0201090e0f180c0607020105090d12050a14161205120106020c1008070c06050a090c09050a05091912030f0f06080c030a03050304060c0915020102 75
    0xc01085041d00070300c080207000b400e114000600f150901965580018410702c200f14030307a264903045d640035000b0300028000040c042080c500d03068a0701c0602aa083e0340104000c0210420080001c1c004a2640a241802410740b86481746640045859800c400c90050b40310508910000000c0d03030b9107110628448060311201c0e02e46c0600e200103442c8042d19030b0400c3c3c813090100000d05241426201ea501400c3d44410302252941061030704130303030a01440045a04601e081e01c000b150746500050518000c440490340c504006c0f05028040390b25076001d85880010401600d01003001030b040e0703086079034801d4020710005032500c3c45480709151140300c0d43c051501e1660b40c0c8240640b1404601506900104c540000c01003201d0312141c2a084e0704450b41c0c05010801e049580080040c800d4000d0031550b044540240420380c10707442e205c0000d02c0c40d4810203a480c42800181801030801141071142190903440e214103640c0c1d9512204090084801108108400703503034041000d001c07512446502c00542d074001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 592844505 1250 592843255 592843283
    0xe07090819031206030b010306090609020a03061b0302070506180c18150a0509040b1306092909030906070501061a0408011109091602150a0903080c04080d08040503090607 75
    0x20f00750b25007007074a00000303074100308061000c502ca9600440c1166881a40000e0a05060901c0c500030324421000a40c421102c080010070722955810210409080342a01030319103070143d4080e4101e2281700c00042c9142c10501c001160b50882d2025a20070003c49401da414813003192000441400010b0090101c5000210500c0145100600c4d140800030044d146c55039100e0401d000514800002800104044005800240034107140d01488681c140d0101c001c1c0480401d5140800c0d9500d03000500081c0300002030340c0e1103008464144c050b030003020014040e51030402003006208140d03000000c181d555648801c8005555154a9148000c540785503140c151154217107004a030a5036882341c0f02199400c020b00800c0c08564440a4254000007050421100d490180c1000d0f0f003440d1101c0c030b444031a441d8140800050440903001800b82c40d10a603921030003075450380005d0480740518003903144650303c00c1084400d004c0c002d040c01c40d00280a6012682090201d0000503810b601c48a81140d28083d81410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 592845755 1250 592844505 592844507
    0x1d0703150b0d1a0a06090e070c060903080601020c0a03020906130213092c100b04330602161a0c06040f021804200f18061c0506010e0709081903 63
    0x10000700d5085070384c408003503d0a18018501c15090089501c0307075241001007101c090113507044040340c0f54002014410300c1c00c2401d002c2c00d10b01c3e040720424054003920140d03420034a0114840420789500070140c80e20350701c80300144006184203841076524a54200b00c031030b044034080441180201080344c40810380c0300c158110f0600902012000c5211021000141d884044000c1040100126203840000d080c030a60300018015204100c080d0403822241d80e04045010401981c01408604004c003415420741d45080483c1d17506c814841e1b202c6108084007080c0401c2111a0810103100d4460b0040303828100728803001401c0c030070700342e07022195140c00392000d80031410003030881c800f6a00101080c60a44c42c0584401d403944101140c00c03102010890001a000e9039000e03183c02003481c0150107601007204a01c0d1411008134140d544912801030940040c00e80c0115441140049500c00b0250001e64606034072064009400b03028070051041120003c5500042000301c44841013200d032080014107400e0030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 592847005 1250 592845755 592845791
    0x10020c1605010206010b2d07030314010803040e0c3006100503090d1107080a0308010e06040204051804020414040602070b0c0c19020f1210061d0703150b0d 68
    0x4481410f540050004000c41e080c3c103000d407103441541c0c07006c012040d0001203240018005007102c0703040710719021602101303140c2c0c1030740200740081c1050304440c45a40c072a01c00d107035680103038410003219182d2400065618a205400781240d107050038018043c820211900b0f048038078044160011107182101000802e01e804022030100d41c8050804510758240000d0b00d030f494504004211041c040c15500003020108100084802419408251420f204040c07030000c3c9450006e03c00c07200e03004000001708043d40b81a100f160101e401c010311716040c1c0d01c0c2090b841c401d240c4000340160ba000d9601e4003c2c000a95040c10000d110720703ca103d006980718801d252105181001406141e80c1010034010b0001300c002c00103800101040d0141011b82440c60341c8001003030f100e801c410701608094440c91801d202c041c0050503940e02c00508509000080c5c803165402c40e01c0c80c4404403911500c41510226840034040e034840080340c2030700d4044c50b40c559141c46440181e584a42603119119a8406041800942c00c0d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 592848255 1250 592847005 592847009
    0xb0f0d24060f0506090d0507081e0303010501210f0903031e0b0105030c0c0708072c0c071104090b040b060f0906130c1107060507150209130b0310020c16 67
    0x30381040500d0400d00c0b8844410310b54050103000d00d000140d507210954600078a11070f004c0d48401247c0301e240e02d4104540e290000741400c40c00e001c15802c18141c03205404010389041c0d0f5010303910007200036841048180d80d040e01c1851100565520321045403070500900542c03407040e01941b000b0031150004c80e009440b18000040c1214407a180c8801c1c0c4002d681c1c05001c83e40c214981e1035880303841d551980d461a0803c01c003a4000c4009100b55040042d403a02010b10480c200002403100390908003420301409642042158801c5117120200301000000340001400340721000007030800500c003801c650300c0201c82d4800395402e40394144030030100708161801c41c0f200d00c8508801c0d01e001c0990304060b80440da1080b92121018080ca03196050304111038454401c1102040080085691090b03035950f01030500e1740044000d42e0b80041100d5082840100b40c004c451104c0000f6112890300000341c040341c030040c0403c045040c0e040c020f90010b60b8000c0c82c2070001e440b5810501c0c0140c007820300e8040006010703610703d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 592849505 1250 592848255 592848323
    0x1a1b031e01080102090a05040209040e0a0b07020f071404020708120f060301050606040303021e12030106030519020a0e240408030408100b0d030e0f0a0803191b060b0f0d 74
    0x1003002005ca510342c50140c00840303400f500c016844a07003c0000802030b00c00145010110700c1069100c0d81800b81c42d06403a8003d180580a4400f014040000c2e0b585800490040700c1f0011000354140049052540c004d00745540202c01302c6050052410f00e25141900640c0c580e66050449014800c040c5400e220b001c0e04000112003da01d041c0ca5650040d490700d036031901d00000070414100c40701a070013060090001c070341c00f0056041c0d0b03250b86444019005100c10307602c1c131010800940062450f00427a2007150290455511502c1550700803100300540071740074035174220180103c8161001c400300d5100140004d403d009001c0d6072151b04051915207000408028404868148070a40c507641d19011043c800c0f00d500b610f0b1500c010425003003c0340b45074000c00d070b00356003004003038600288040f0044050014165000c600400021a98008031651b003061031861a59a24074840d0100040711039228000702e480240c000400140d05200007406216401c0e42a40c180c840794518040300301516001e60150080c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 592850755 1250 592849505 592849507
    0xc100e0a03030b01110c0114040803030c120603013b011a040b03030f190201020705030310080f0604030917010608011803092309150d05010c0f0c1a1b031e01080102 72
    0x51917404c6580c0d032034051150b80c18403548107042c0400e241c54004a4000e00000c004580d41c03401c10006046060340001a5034113811421004209945010302840382c801c1480074148150500c1401d06110180b100351a00113000301c1824000542c10003030080000c5004005401d42301d0010303038814401620549104c99102c0d410401030444082c0c4d01d00c0a4034402909000384168006078804103900a10590308040c00c1c0c0d1201004101f8842c0900d0091410340e4001e0307090341c0d0100c2c848400f507035440e00140e80043c08110301000074004003596000711b5410500c00c1c000811155602c1c8421030850380d40035610400c42e20306010a00038960000c40000080018410201c0301140c5000e03044c0d08046802c604503c100e2256001c01c1c0c46c0c00ca131030403440d00e071100100002e11200713003890814001e00c00110600041015501c00f48070540c0075014a10410390020841d044015104003402c41c021401071508101034200400c80c0c2c0100d0101c0b0240d881014501c008140d111540c15021550b0101688210039981c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 592852005 1250 592850755 592850777
    0x61e0608060901090c0219060b0a0608130b131401020d0c0c11100e12010b1f080a1104081b040b0d11010f0e19090c030506010f050c100e0a03030b01 65
    0x85501420f4112000d8100008900321003800c12401c00070445403106141c51619121002d0104580c00007581d28800c94036620959038484003550005811107000491655052141d000f051106040c2503101d00d40e800c22600b44840e580c2c40c1d03030071305074400c2c00200380743c0d0301140c1a040002248a840b5103680c5038104201100c84903594190280340c1055201d016941c011101c5801034001c055010017140d004110141345400400715900030199481401d00c1022900050345800600907284548600345e40d803420450f6961503000300c0a4105040c62030600201003100140c03c01060080d000280d01181c131641510301e00c02c08220550300034190b294402c4050841050003e8816100d240d040042802c0611090051510a80f02181180c80c0140c008074684c0d0701e0b07044181c60b00d00000c103a9031606000c000a12040c50100e08944084914a020503040c594116841d070280d4060400c0c4112501110488414802c0080c02ea96154014454aa20010001c001c143e01405440e0880d10203103070124900d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 592853255 1250 592852005 592852009
    0x703020f011410031403120a020d05010b0406141305030a03020303091516031e1803080c1303030c06091509031214011502031308060103020a15050a031e061e060806 72
    0xf260b82e00c07000304620811007074003480c468203100751030180c0450451105107192181000c0702a5000702151804580b92000100303029204405440c1591103554803101c10020000c8085603580c40317020610520a00b001000503d56820429900c6852003540510389a04003e0203882c035042c080100341d404601d00402300190008207000c5080d0300c0c040c2d0318010800340075a004a00801a9888d010074070103040c94031441102400010243e4054800c2d695012196607008203c5114012000520108041d058fc10004240708012282c4501e006020020300c2d14000e685801070380c5c4c0c600840b01c00854503004030100741a00241030b28031030f800030360702840111440c2d400704039030503c1406000184043d4442041d240c070303c200241d0300c0c2d90300d04445041403c0e840740e030b00d15600c3e402440700b01d200d01d6888202003940c803585455440207442a0b02c400307040030b010200507030150800711071400000014a19030f211301c110600402004118100c50b40c810450039144110707803800f05800070b6080c090380801b03003d065 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 592854505 1250 592853255 592853281
    0x403020a020402090d0506010602010c0e0406050604050d170d09140f060403080c0702130e070b0a0504060e1203030420040c080c0f040305060f061305011d09030c01020703020f0114 79
    0x85941150010382c1c504d40da00006140412070b0700040e0862003040700104050ba01540316203404009a00c1e079084113910700003000159186400b4981d007102d010302c0304110b2800c000300042000c51007001c02986038465804400c0840e0004041b202c8820b440d043c1c000203001c00142c04bc002501c060001d0005101c5c4150384540c1c3c1d0201420007010440da04002a5000a0a8041d40c0441d54004c150381d000301c00041d4100080d26140c041c104541c00340c43d01c001401c0806034101ca070469425201d9034241807901c00d0aa540c4504d641c43c2e9500200d04165102a5610520055219a01c15508803100c00b81005401c042c120310803003414010b40c13402c10382c10340d0617421180040d404040c0c900e0290340d50044a05c280000e00481d03100401502c50001800b00724110388001d644036090070703180d041c16101c998071070006541e420300c18403c0e02d070743c004030303400703c2c0303421030300b14a9010b402c002c200c03807803c155020040c0c22640610301c11380040c0c0120f115002c0082c001c0c0610744103039801c2600c5c089181003c1d4444011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 592855755 1250 592854505 592854523
    0x50712080f040f0c090f020918090d0e0607060e011506050c030412140303010e0906060a0e0c0307110d031509090206030f0405071a090120030901050702010201110d09140105040302 79
    0x150008880500b0804c002100c4450203401130040c203000101d80c3c1140c14019400c100411449024584058801214080d294034411040b940090800010903102130301d40742c00b01c2c030009400c58400c00042c0042202d50044442d6140c05500000b00d410a82840c0e42c0c40c48060307040030013041820054002c240c8000000d442c00d440340c40c641c8249100092520042c800724141c3e0b409100e02012000080b0095a0200544151091021388009941d840c00304aa41206030141100c05200c1d540450142c00440c1e0145a100703016040540741100b50211441ca0b25040026510010340c5600e0074203c81d0890b40c540100406004d5000d10401c069a07000850714040100f0407161107429400003014000c00b0081d40000b4013040344503207140290b4003d41d5150f64049444c450124070501581c01400440b036491140c4044024059418050b01c00700444040c1d201c00c0707041e4115900d0b90980c0540710072100041121107401300c0f0018610b410f52134120310000750b4015440031070b45018100404641c000c01ca09030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 592857005 1250 592855755 592855763
    0x604020112150e0109090c15020a0f020f1905030c181308130f050427030809070306051003050d090305060a230906041b03170f0f0703050712080f04 65
    0x391603000c1c00b1040c10340032041d42c404082000c84200015000e6003540c01000b03101d0150054502c8140c0350010390240340e010400e900c5c0141d0001404e0740c049900f900c0708256080c402040c0401900d00c40c0c0008a82455114501d95038a06240e0100030078a420410343e40071540c20390304038a110034150a481c2d0181c1c002007120b8030800c10a450b40d0200000c00c021105043c880f1684101c0290b22142c00c0544411179000d61406075150207510b40c00c10080328000c0c0350340c050b14201d24800c11015507080714a228041d00f04140d41c49030440100c00680d40c0d0050a10588108580c002c0c114910b0034042d19114003030400c2c60038000d04007003d001107400801d0055001010ba207001c600004c000c400510105034180300c0d80f000c104000e00b40800c03004007007600741c013443c010610034501004c0d9101c2c00030000790621008001508460100c841526444098215400d45465060526442480342c001030b82c880325040700011000640d2a0410100341080352081c0e10700d10b8603d0081c54000c022004202010304050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 592858255 1250 592857005 592857011
    0x61810020c0d0b060415091a06030f06040e031b1606031104090e0705061204030305062706030f0609150109060e0126030406090e0f060d020d060b0603010b12090604020112 75
    0x21303015111a0070003824136075a13446880ea91595240c180000341b14040c03841c400d50303501001c00c1d43c4a03d40001a05c0c0a1182669482c0701c170b07107401c401c1100610308049a00418002070104481c401501041c0500c150340c44c201400400c5c15405507450603c0e01500300e0400c1c03501d400c064950580c205000e40303040d150100000940300c005d882403245001c80c1a400503621590019a0780141100080c407030f2f0003148607803014046134491743d00301b10100e00f130300320504039003021540d401c066070403104003058200c071029054550b5410003494560420b81c045650b5152540005d40d031807a080400f005550042042000400406041564010800d101031041c1380d0180c1c400f02c803071145d1101ca01748840c20480c03d4411a680c56580d0940030348400f84510070040c2c000c0110000a4070040346001c1e140c03240a0003841c10300301100c15803c201c00308001d25000d941c000d9848240500b941c43d808020760107454118102074443c01d881988104c0158000d11b400b900760000c400340720060740c0260038141301ca004080c0c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 592859505 1250 592858255 592858261
    0xc061602090c0d05040c15031a040c03060f0603023105060a1e21090b040b041a040b0a0e1b100e04060f050f03030301030809190302061810020c0d0b 65
    0x20400758080e810f04100b4440c501014041044510303502c00e021603502c902805d590050300340d070035030884030103205000d003d0800b0300500c01d0320f14059200305860315031070500003021034952008206841035900300c0b10100c0c0e0f0000c1d04400800c03200055901c42400c006130480c2143c69000f4011882c0094440c541c051500420302c002d1260150146088081c1e89085656052042c90b0004007940d09031083c2140c0000c0040028007542c109010f1140120b130040f200d060f0f10b494542d00c0321f91400c4014002c3d91000280c00c03c050b0f00000c4080400d000b24052020303604a41011050041201d01c400202c003107540c0210800d11460f0701000c80401c002c0412141a410340313160342c0c81592030300c8640c281568800e2520700e002c0341c0540396490500a03510182c0d80f030808000c40740c1c241550ba21013070001810301041880004074918003141c15050031185006100441a40c070760209129030008150030100021501c80c80000741440ba41d11a444591480201204220540411108100f100b030160480d0514800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 592860755 1250 592859505 592859521
    0x3030f04080c03070e0c072006070f03080901090c050607020406050616020a150804030c020316081e0d08180102070221060702030a050a030203090c150a08070201020a050a0c060f150302030c06160209 87
    0x723284540000581515a20354985c541404026403c1e44114040740c124008a040c5890502c02c3c064a194007210500285040100b00105038002c2403049a005846000100380307030725140b000e0b000c05404800e0300f40649040740304220100c0c03440d8008405141008892445030f5030701418150300710780c2505022a10030601e0000c2420a07060a0503031a03802c505010008c0d500302c0004141078907008003a511072603805a840c0c2e031500e03411900a0030002500080c0841c0c42469400f591000511240d0001854204143e012541c00385017402d84010b145c0c2c1c03d4101150803441401a10b501203501e1025610340181c402c0050001d0013000c00700d02c20507034048002110f0090401103980c6071000108074101a208010901e000fa5000c25142400525880082040607005000b81e80c03d4410340d84a81e400c05040c010100c995400004003030f68210707180c611561014005d4030658a001c05e034070f0f8403800c80904600500d4600343d4814403181c000c01040005440c080c0307000a0307000c2010f5041710303000d02603140d8001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 592862005 1250 592860755 592860803
    0x60e101b0f120f020f0601050906120106030b1003061b09090f140c03090f070f230409080904140f010302060310210311030901120b03030f04080c03070e0c07 69
    0x34000b0920342e03619048000441e04000f07041e003d0000380d0700b1900c1451910000c42c0e1214401e11500d6000030008010a0692901860a00d190b112290000441e280c6d00d4845202d084025981c100c80310075005007e105001e8540180203260800e410000e03c0f028001c48021b210b00d2491086071081540d9440d050107039046900080b13000021800700c0031981c286032103c0c620650003034520f0700140c0303c0c00000c00301190011500d07030203d0304800c2004c808145000340150061070030b20001c0014420074416004107a4961068643d00c0e40521200c42e00c4614140a10040342c00c0721501100385001c500400c00c5c032004580a050540c0c5e4107850068407600c401c1d417020b910003200d0304003002d0310301d038100d080305541c8003c001d02e640580240d8403c07801c61401c040e900d840b48108d00c9410700003500114403d9480100f50055146644080c0499107010345040340d841d800e40058015800e03a800408105840d0b18040040b00c01621881d1181a5642000070006071144290b00006042c1010341e2000751072412029 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 592863255 1250 592862005 592862033
    0xe060c0a02120c0109050d1a06040905160e071103070204090309050603040b0f010909050303070e0111030a0909050c03061e0112020d1d0303060a1e0305011401060e101b 74
    0x9044201c848209150040d100c1c50404021400114000b500080904d001070b01107c029400c00040003500246000c411600c404c020007064000740c442c0050030000c1e5040003000551840100b0520200382087c45840c48078001604407400c0140c2c5018001078000003004580303203d44c1c1101c001440001d01e15054400c050542d0150741d0250011003080140038001c60b1484c840d0500c0003400c11540c0e01d450907041159000000540f00741d1052000491860143c803601501c1031050410044100d424014580345500030301020b0001000158108202c7c806805241d4203c00340700c400c1c0d821880c140011902c0107811040884000e0380407100782c4c249900850f03051000c1140c4042c15961441e84c0034140024044040980c62490007a0078003010fa104080180e1b4042c44004000c0740780c0710300d0b00401083c00949407032001d4480c02c40b0340001000036000d1140001c001d0030035060106541c50480054804554004100d004d91001596407120079809050103e056841c6030101c503031261141080d102c04c401d80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 592864505 1250 592863255 592863259
    0x91f0b090d0506090d0201110313020d020a230108102403062112021513030e04020a080619060c032706020f010f14010302090702032104140d0e060c0a02 67
    0x10b044c00000d04012170300494001c00c54009004440d03803203c04240d1072000315068034500200708a503d005140c0b240c03610441c02d00040402543d540c42f400036400d04180e5483e05031440f511a0007518487d41c0041d0b003140c0c0500e44490764889e0302d00c0c00142111400d525030360304103045000c1c1071a0407200d0180c5d2004001c1c03d50310300e1401100c46a40c8030340e88405850403003a41e0200c00e9941d91304500744001038484076192950201907581c0c903104c00c210b2819801c4031045050010b110004562600d65101501d1250b440fa51345da80b442c1400d17410b01c16194040c0f032000c1044800d54405101d100c1d004840d00154075490701d0402c420105140546035010192080c08036544010180055016030005468408a0b1a00020455110100070407800c54000850090b1004c40500040001d807402c507003016488082401030340c0c40c04400c220a40e05270900c94400044896004081c0800c0c81481e145444140224a00501074880c1c0b003030f00a061440d94030030b0f8601c81c0c000000e2105100c2c6007405080110780e80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 592865755 1250 592864505 592864513
    0x1e1b130e0408040306110309101805010231060c2315010e06060412110a0e0c0706060e0601080a2c071809120c081e09091f0b090d05 58
    0x820b00c0c12222a511030700c41a00d81034208200320210300c03610011240102c0c00c0600a0502c070384c80c3c0d2140e4018150000c100418900a102420040341007030000f44a07211035512038500f01103541124080d01600008805511900d01c0b009000341c81e0030144000e4141d41151403106424030182c0c4903113001c200c0c2050f0000ca4001c4c96404032015800c0c207601416104130020740d40c025512407003400701a010f244140c140810082e000c032404076500031425010800d026104100d180e4440211400941d0152401c240c0c0c0100021310078140700c076620804c80134210704514000a4108140006c0001401510b444000ea55480c003d1751850002c2e046000442d890070b642c0684000c00003051521038203284100402c0400c08c98120021580601c26404050340c04004d103448030764185412100c01451140840307a801080001e00c0c2c0214441a04061089405010503a0348031a1414403480280103040408005085880c80110360707401c070400000e44175a4080f003925800c008000802d100d82c00c50000d00f003401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 592867005 1250 592865755 592865761
    0x3010b1206190b1c0506010c03030911120a050d0c200a0314010b0f1203071b050a27050103050303010b07170a02070f060f020312060f040f051e1b130e 66
    0x1140004d001c03076140c041c4800700e07143c000500380000d5800449a6500103130400203030f100040d0103944510b54490040c40c884403003c44074004500400b01c04280205243d02800f490301c01c0010400c40d0324640b6041d450310702542031550340e540700e1004907107961400020540108001903260308121100544d0400f0941c40c0e5105804401c5000303040c049142c41c0265045120447c07641044d00e01c09250100010044d03240542944070000c056480515081a49001c448005207a94440030300d10701405d68100d220341010713184600401014031103201400e140741000d00410126001200381c0303044801d51905682d03100304e83d00e004522000700c00203844801c4000304940400d07980c0080c0131026101480b6000e108103446a001399480180d5806440069004010a0710022800a80c1c59041000600001031400e002e0300020180da92549640820707554840030482100e01103c9014331030006011042180c0c2015031194544541ca1000d2400391200001c4500014001c80a500e005094441c031014440c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 592868255 1250 592867005 592867019
    0x10219030f2c0c18150109180c030c0206060a05010f140301090209010917030a1d0d1202120403020f0918120405131404020108040305130605071703010b120619 70
    0x1d10038402d150948502c81c1008036506103012481c90064407885080156a0b031004058641c0c0f42d0a590b10f810001d0550b80020b061411100304800910742000100f06002c40e0a402800c03101c80d0646041154050070501180e030300c4003890b0300160340e404c3c81e10403030442c200c0a00391130207807460845400b403003800000040c0c2071007994050701c0d0100c030980c2c84003481c44c0c1d200c031404950303001034442050700e410800007412920700a8a2030099035800024071070801c0940070001d0b46044039180c043d030750342c981020110103c0d541404105400300e487e800050406042d6008641c4071810740c03041c103015a00e8031001c01c60090b8038001e840c1c480d08614044803100c443c1540c401d2100e800038812140a080349a146103007444190140240015038600316a00c6030340c03a60011078071400003920650030300500700020320480300c010092001800e915110f10355251f001e450719a42040f0007124003196142c040c001070280c00a441c003190105246c16038036407215200c660024564010701f000f1b1005919400c40c0001d906 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 592869505 1250 592868255 592868321
    0xf140a050903070501180b03060409020409140c01050c1e01060f0303110d0503040b0705181306030c080312190f050f0f1302030304061404050306091e010219030f 71
    0x401c0140c066501c141c1e91040155030703541e42c41780202c0b61000341c03020a00c072810b039440213581c3c000001007022a081c1c0c9580c01103021240c0b40407041e5080c40d2400040c24120400300308580f4901800e2034031034603181d503082040e501e80c0749481e46032404161503107030070900c40170035040b10010740110b101403960f07940e4078640540440300b80107000c0340e94014980700c80000c500541c2a20310603500310b0103201c9217075920081151268400d4031880f0740c1c80c080c50307108040c40c2c407000031482140345020000106075055080000d0225065402501305900c20440300c2c8442054140b69600f12f5040b140810001307002500e10740182c601d0302070410b4081d141a040101103d07220006501914600001c3c0c603298896020444805041d524003941580c41007004004080c86800d40441c06132110f07801038107290310b07040064200b02d425205400558050070110710143c40c0c0c1841a020415a400218580b0100044018009040700c0c21081030550f03c4180104200703268105643c84071241505014500d1100a1146c0d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 592870755 1250 592869505 592869517
    0x11100503070f0f2a0f230606030304050108091c0e0f040b09070e040608070e090c0904030f08070903140601091532030a0506160309120f140a05 63
    0x2c400c10002d006840c09252070302140803040e40e515403c501c5075203044000c400d5800300d205100084180b50004607080d4290042d500b403049080300384161803200c4030301c485113003006181115007110041c0001070350000300701c80403030302c0030300b410a080c0d500c541e03c0605010380244020509011000d51076000da5000c00700261280e82200c207001c11100c0702d070500080320160f144040e00042e608000c034500902503c0030501c0d1030401080454156290b4815078182015584a00c1640705040306004070044240803502d500002654071010a2401e03031001400c40744c01c1d10b031200074801180c0111350814070450600f400b840d0030100000c0501100394819660f03583c244a000c920741c0c50a01805001c0029408036130031605080303c841e41880d010191b030407a0201320301843c02c2100510402d84400c0c1c13018460755820900400c0986014540b58100d00040b54084950b8410140341c0022000090f2800712001c41e41d011600d0039101548007a002a075420380081c0b8520070b130780c030045031080076154000c000b441 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 592872005 1250 592870755 592870757
    0xd0804020a0e16030b0301020c0109030c05061e0a0b1503010305150105040509150606190c110906130e160f030303060b03060f120102130603060302120d05030a091110050307 76
    0x2502a541e001005024032040d21014051502d07210103200244c82a0400c840b4a000200014a4500101402d90031540201421400b240b07541d2884410b10006000d4507601120613948446442c0c02c2c0012030006038ac00070804150f040c1c2d86c2d094550141c0b0341c4081240605d4a503040944e0365610b90912a90700c42c010800491805032000c004035450405009040c00f030324a0b0001402210a00160581301ca000240116003101c1d040c802c0020b52103498405146246060700c80c14080c1c81c0c1424000c1480400b1006103004220341d45c180030050711903003040500c6908040000400054901c039090900c1410340b001d55483c9480d10b40462410380610000040740e129803800c00c4a00e0b034481501c0c80f54002280e0f41a4046010146e4158900780000380c8415400c80000041c40c2001849407500d500c0280d40100c5c0019a88072401d004601f04040540c0311011443c00402c001403000c07000401600c40200320452054407502281c0800c80201c505029a0000800e0440c004440b0680144150011140740c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 592873255 1250 592872005 592872019
    0x4090b0405150915030a1a1006051c091515050415030c06111029120a171b0a0b10030503031f05030118030e031605040b010309050d080402 61
    0x1407480c42c41000070740401c400280c940c6800c0da0358071100b03507694500c0d4010b00d80c15000c1c001c0c112000651803148503200c02050090002d80d4140399420900b10b840c180c110105100c0b04106400400001c0c1c04100e1501007504008034000d4050b141140041c51510b061813640c90030018070850601c0c41c08590703026160181c5041103481c0e40b1510f107104100007440060079404100f1400c2c40751620074003420a50b190107004031070012a039000c11f001264584800d17000b03a81d40350013000815503511494a01d500604950124001016111f0f80d600c402c2c0d60f200003040034140ba001c040c96200c1010a4a50744a03140c01d4114281c150302c2d100607141c0c80c0404d4100c4403204aa00081c2e6034105903d094000c0c1c0750003900450450b1350f00b4020004038411406842e4400405900000d800e6400b4021070740c0501d6140e881800c49241440c000d00345134103c009140c0700b5040000710445e0140e500e5010790407036100319004281401e80f0b0380143d00410850001610390b00880d40d07078462641c3c20096441c080c03031080e103141c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 592874505 1250 592873255 592873261
    0x9060a08090c1c02040b03030702031006081525020c04060602060a0e15040b090c040504030e0a060e0303220b1204050714090406091a07180b0a05070807150204090b0405 74
    0x1c000d03c0e0b940b0384400110f210314800c0981001d51000244074400707411030389410724680003c4d02c0c080c01b80401980080d140c40090045d03400900016080031400d0100200908000c02c68402c00510441002c000344078007400c00c98135520030841a41c0c542005401009101d4407540001d4441000b00c4051103c41d0800c0c3c030303450070703c20001850500b8a1060408601c1c9494545d01c1c1000f80d1310192404160340b1803950b80071180ea0300c900c5058003031403003030710741800988000086c0290481154819400d215800c03981c41c40644000c8100c0380300c02e581019000c094034249100a03440c000f075410502c42c103003000c42c03400d50a003041c0030410701a40c001c604488081e0703035840c1d160109520b64000260400e90003404180051465040710f904d042c82505d0030003200c100030b0b07140b030039440007151303a800050700d501065007606000e100342c0c2024000c02c0c140b031498a82d5200d030103049031040110041003060000362180c01d22000491030300c0380e804041810b5540f01d07030742c052901c054500c0d804000d100354941004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 592875755 1250 592874505 592874509
    0x604170601050a1508250c0b1e01140102010f05010605270a0b07060b100e010e01030902060a05071b060f03051302150906091320070317060609060a08090c 68
    0x4000f0407160b01c1c1045401401d00c461041300d001c240a0559800304402817884288600204007403185402565900902c000c610308040f15854006404032a8000d0b0042d007112482e4201000e0720b055940c56059042d002e4803040040780104208900000700c80c0c9440000b040d11070f03004006003910003400701c61300d550860700030a0500a20b0f8040000c1c0c0c0c8290614030400002104101400903240150800190100c881000c510310000381200c65000030031020343d41801e980c001e070168454070020b103030400190441d54007103403051181030344140503c030000c07400c14108010700c8454401d810440c10241542a070b00c5401034826050100d400001c2410f000001341c1d18004481d916014640007010f07410700c2001025542e069501c196040740d00b1520401905003242c58821408003009800300c00080e1415151200c4c200482c00c41250042d03802d020414500440d81c02141510121004240103686481d12000144a4442c100340300d6041000415a0043d03c3d0b00a0b0803603105111420a0328600c4c020041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 592877005 1250 592875755 592875769
    0xc0a0b0103050c10171b0711090912030c1b1c02011103071e03060906030f0606080705060f0d0b1203030412020f15100918030f0c030507061802060417060105 69
    0x101c0f000004130b13012401000f0010300104550040c1754000c04425040f10706101d9891035210078400c0d1610715100c6130290441c246681d01c0f43e401141200581101c05c52441c10342c0040c030000d081c0c4285688003083c0480d100b181c101303c0c1804201d003b01101e100c0301c00e10019980c42d00b030b60810500907510700b204c101e88404400342281d1241100da5110081604056140c1441c54140014a070816503a18404500d494141c403801000d03501231034400340d5035040c40c40d00c5815074030250040c00781500b180030304118589640782514140582c030741240307485422186140005180c40c0c56510b500c00102400059410340200003580a14012108180810300c0881c0c01d982d103052880a00780c2580c020f490000c00d0f405190364003038102d03a1080c103000d101c954540240b0103840c1105034004042e004107406104041d0032040e0712030110b01e20f04020140c0c040c030303403400f816501030102c0140c0342584074210314070f107500000030307402d8400d81c014440b03921070740c8910030301c4000e00f40c2d002644100d100d40310000c60359290583d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 592878255 1250 592877005 592877029
    0x10c020312010e1905090f121201170a0503070605071e020709021c0504050c10080103080d0b0d23010c02070f0b0a050409110316032a02030c0a0b0103050c 68
    0x8100440d5910301002c010038000b0081c020b50700b003015030003202c401c0c546078040d15000306801c8000700340e90003640c0e0343c448c01c0c0b8600b407400521441c4104000800c030f070020380b17401c3d04440d80d062194400d02d814440c07031801c114034460000c255010014603001049121741c8101c6c0181203507075400d03403074a400c04503c451100940b00000050707401504108020881900107100407138090b4607201005080045a0f4141ca2090b00c08a4961b000030881c1081402c000c03103000324076083c0b4600503190394515140c0031001e1050409407190180c8a1102c803c0307540f24141d200b0b030400d0f4446000510050300d15a04c25140d01c9a00e0300400c00e5082141c0c0e800300d10710008000c0161902d03206030b84605407409070038014a03803206c01c050303007444418400002c1c400d10700d10800900b110400c50180d90380c40e2069114022000b0170442d0818180751160b0401058607142504ca40e6040202c116035045610240591860064803002040c0d031040c240b00004100c185a030780e41c101c1c0c1c2710b4012a2080700c04007080000342e045a0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 592879505 1250 592878255 592878277
    0x306060109090c0e041e1116170c0303100f140303030f07020f0d03091b060c320703020906120303130f1a060f01020c0114130e0711010c0203 62
    0x503024008405076034000302d001c0f005401c041003480742420104081d126045d0a21065101801d01d4084030395a500440c280700c12401207881c41c0c1070351003961040e540805040a003660000c05201c030714460062044039519020741040304e46a1404280e54452803902d40600081140e4640b00002e140c002000d0200700e051006000d14196a80c0ca1007020b16000020a002e0840c41086000e40002006000001820400343c0d4040746111241c01c1100400303490381c1011900c0b0b5110501040b010382c4c050510150075a2003002c2916011051002d000038601c2d5038880c44078414140c104031260600000c918080782d100b520007003060740d5002c2c100018205218000a03135500100001514642800040d0700018425800c030081885e142c2c4402e90702d5901207a0204408400205204507031400c2419a01204024030090511310405800201130109002200d40d81c1c40c00490784150b20b100000e0240094221070360f20131a245017515009185c00c0310383e00340484135441c0c0349604280c0c0b48040201c0b0700c14601 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 592880755 1250 592879505 592879517
    0x7090b03030a030e12070302030d0c230a0e040c030c0206150607020d050a06050f150a2702192105040803060d03030e0d021f0e0d180b2703060601 64
    0x82081d0060301c902d4081c04c3c0c4602a0706026900c0c00059070107802d442c1c1c044c0d03008549442c800307003403082107507000b40380b40051052240c241c00c02e621041c130b80c58042d1802c503884c1c1a00d640c41c68030151480002d045c0001e80c03240c2059007000f00c407641680a101011340b0b035421101c1039242c035000d5410103040382c18003a4001104211620240c02c03c1500c02220328491001c0701c1c0520125220079003111b0042c0d507000740149110080c0030200d12403040340c0d07895110031652050258600420a005000b409514501c010300b4a02e1461800e28130f5415140201903107824402403000002e8020000312588139040c0c80c44110342550340c0c0420881c400e840c803460344060200c0c80c64031000104010103c088104508141d141d44200000e80c0c418000c268036403c1c01d030010b1000c00c240f50040f0101514011010303aa091402c46003400828001a0f400a0503907035081600030a00c801c00c2c0380010641d950000c0f0360400c0002143c1e4100000e65a0007840b410b024880d000b441c1c8040700415881e25400d817101400281 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 592882005 1250 592880755 592880767
    0x20a091d062e0510030c11070605090a0608090c100309021c0314071104020306130219030b10080105040b01021e0606010f0c0210120b04060e01050306090a020a0312090906080c010207090b0303 84
    0x3000758005041b0304014141004140c03036155015103455040e4201c00300140d030201e5651400c0c140400c0040c041c211904002255103010840c09956010107105284103101c2c40a6100c1080e0095200c0d40107650040c000c0480884c084c840d002d881390025400b00c0c00114040c9074600d13030740e04110640b40c1c010340c018400340d4850542d40c01c000c060340002c2c1143da4000b4217503071003940600325440200003007504501c000c000e008100b0300180880f10200c60003805004c900c1c0e04c10992070303409074003103064a00c03c40b0005500d61540300101c1c5040310034028000c00c070700c66001c1d00400800011305144500700923030780c0c0258960110011509a188464000c0d00048045446803640b401200c6031603084007200ca0000d612500c420010301030300d40039440500c00c0c03200307517005019609040c000c103940300e08580300400c2480c1709035004c58070319001403201030490300d80c01c0410806a40300759416030042940303206c140019915074414646034005221101d025120b9035000060360382e05402444002c4800030302075400c044c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 592883255 1250 592882005 592882007
    0x50f030c042004030f1b3206180108090105010b07020d06020c03130e130305070312090215040602160812030a0f0603060b031c230702060403030921020a091d062e0510 73
    0x25041f01c0c881c0300b80003604245019210380c0041c12003441403403c006d14801c004000988010400342200c081a4100b00041c000d9010910494094035410f41e040c0050040301d04000000340141d0b00c0980c0103010000d00803000141d42e600ca001512030020140400da00d44220805c4480e034010401000320b01e05100307690101380505800c4001e541c08503004218070000d54001f510ac130000c07c80c0d1600c03035000810140845030781000350b0f600910f4041d40d030506c498200700c0500c1c3d55042c000e408121080d8000300007140e00d1401d800c03000307411020340340a1004a480385040c00203480c2d1112f10f94041d120b10148800d12a403c100c0b07500041c8032948a81d0590001c004813068400c50b54039030400c1518041004100507291070006000850095683c0075015040c0442400800318411440c1210600002c0c180003590b1100c0001085034000c0324005002d98180d4011300500814114064850180c14100400d281c03280034120b441c04c041807039003503010040d180030780009006409820f07000911084050b43c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 592884505 1250 592883255 592883309
    0x1060c0f0b2a0319050105310e03030105040f02130512071701020d050108160506130302040c08070f0f0c020607020a260106050f030c042004030f1b 65
    0x101e5100c03002c407049154080a00850004400e15001244000108000181520f00344480754400308003404d00680d4508000151a509840c80328008607100d08401804c030720300001c003a500e40030300301001c1c403108403c2081c00c0d442c0d03002441407501490909401580e11601340c822a050f14245800701810581400c05001c0c0311481c0c14211020740c8034010000c40c0e0105080d00020100d032600c1c001583d280b0007519401c068400690081180c0da000403171440880c1d2845c0341c5041a64402d0b0341083e2240c1c42d455101100107503590019402c1803400c02910006e070b070b03c2070040344a0f88168950105200e1610000c4800301030380614480020300240c200740043c5061002840e00600081000350f072140c0381c440c0007d0030f042811009138006116541e84088242c20b000f41c03001040221005084141201e001c20b0712102d82600d000d214680e42c1da030f42d01c0d801c0741003948240d440911000c040d842c0ca8991a056141031010740090747c3d01d003848000c1d148043c030790801c40004d40380102459101d040040303507100c02c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 592885755 1250 592884505 592884511
    0x12020f1b0f100504061401061d0a120f060606210f0e010608070e06100f0e0109030611120c1e0a050d090c0306050a06060f0c020f151201060c0f0b 64
    0x10074054011045000403042089281a0030100000152070409250210480e440104044c0b419030302c500041242a411080c0781c0c0e208409505c2c4040c18a44400008a08584507000203505c401012004000c3c008290b0400918620076802005400d8440c44146c0b6071a228084500822040a03401c1001c074080c1d405c26501592454800320700020320702d050303030700390f44547e00403468590001d10200080c20040310314541144042d641501c1e0307581801c40080610142910300014000300840c2e5440a901c2101410025030f00202c5c2000824074280c0001400c2c1c3c41038000e00341480c0d4800204075407100c500111040044805845550140441c0404541c4d80003020003905116040c040c171554000640107007041180314a4510600270304600c2c02c0340031254040c3c503644a217450300c14184401174100014085101130b0313003071543c0802d10b1480040c254a01d4020429001000c24010709069181000504865207100070090196038803000c007180c62004034000a84070701500c04824020520460540390 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 592887005 1250 592885755 592885807
    0x30f030f0a0c0b0f09060a1a04050403020327040e0f07060f051c05011502030903071806170607110f190c0b031602010606020c090103150b0a06020a0312020f 69
    0x1c0000780e403203494a82c43c04441c4451903005a1082042c01c00007032020035449088010200408101d500c03c1e0750800358001c0005004d5544c132004641403600810a4400b010580c505020900042200801505200b942414050740c1000d1024051342c1c070201c0c2c4a040560150001c0c0402d80ca841c2c000c4640c004200a22000d1103000c1004000399031054080e600c0c940744001011480d545071006c41d55070195010400000c54100303005c02d5107155000316013041120070880388449241c02d80c960b4100108000c1d40180f2078071408218005044001203401c46c07180929450b41d6040402d00c01c0700b2902c42d0880c0c400d140ca190403509440100d01400c030701c074030ba22134001c2c41d40e0031200307841c0d500c00c01c0e656000b80c40c0300c40b84001750311a076070391541d09009410143c00c0d1032010300b5820692401040b140c0906000040010300f8682040d60800c44560001100300c40040518503065511840a03444242c0000184e0000f0200c1500c04048005070080341c1d480001000300c503207040c0900c4e038a100c1c0101ca40c070008e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 592888255 1250 592887005 592887017
    0xc02060c0a080c220e010503120408030d1125050607030618050415060602030711060903030d0506030c15120702031213030c170d0501080601030f02061b2a030f030f0a 73
    0x351001e42d164104e10141055a01800c03695040800309840d00b896001c9203510a80204402d01510307002105942e0705003c0e485000c5181200d80010400a015150b680c0c035800740e0307031020440c402c40085000314030140500f041e15103e4540d0700c070407400d5a245000d107103c924100d00d00a5052542076101c149d2003401880122041031018601d40d003510215404400160300c081041c0c030078042e141c00b80c00f040f220700311000c91411500c240842d449020b031a0340042145c0e5640c0001d20952404e10040208240c0103000c603ca8a010305c0d40701c0b1300e507000f036100c0d0040c1c500c800000480160000084030000310401c001d2042e6a0381e0420712454810035888100c04005020754441e000900d1000c075400b0360422101c4064560304030f10384481c22264164402c494a82c4002c0040000c50158150f100120390140c40041e40e80401289000701940300f41c46016003442400c0710f00c00440c50b00c132088148200b40d402d1800000280c00c0c209030742e551003554040d4040d0010025000001c1d00e0744020b03d081701c0c03542045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 592889505 1250 592888255 592888297
    0x30a081b0403150b03010b010212090d020a0321090302010207050906030f0d050406020f0c18041e0b0f0a09170a1101060f03050601080316060203100503100c02060c0a080c 75
    0x204000380c209520886a40c0300310803c2c060702e40c9281c02421007461081d0000c000080d10b40000030758a0720708403080041d00b8070000720788000d52501d08114090782d4000d00400459603880c90024000500104481c9819052814110403140706a000c0002c0340e070168001d0030413030b0030074041082c42c802c05041d0a40c140b1a00100c0c3c4411141442000c02030701807034540b03640791440d011000e03051882c1c942d210784d255005828544940d903144070016212780801c00711001d42d0766440c502843c052048040319400154440e9600b01000041c5044c81e1150404107900211500c034030700100241d0700e03a01c074020140a002d00c20181214441d402604100c00e8030314100300031080340304d00c460031251190001d98030070300d140034140240300d403c1010070300405040c0c0085160603c1c0d08509051482003030801000d42390000040b1b100c2005c94400080035020040c2510940224600c9420081c0310511402001d8000e4200040e04001c800042d68603004190310380800540c0c400c0c90385c04450380b01c03030b60088055810b1004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 592890755 1250 592889505 592889551
    0x80708042121051005060f040e09030403020d081e0414090a1508100528020706021306110607020318010309170720060f0a030e011e150506090102030a08 67
    0x781110b840d28821000401d401c2083e850b8459040c6508084d009038010408030f012001c2e200121402c44007003200c0300a803500d403c0303006811886658806540144400005014015002d00400100707454a5074182841031400b0f8820545c004c42c07044c2544502e6a60364040c00e81049000164815001207001135000300c0503a907442c00340d1890f00400e00650203440031590b0b2006074444c0c1908450302407070480001a0420040c55684010f0700722100b80c5401240e22000c101140c0c06840c0b501c4040681c5417406911450020008100841401c607588658804a1095800441104d40c02c2001800020b811a074000064020b04032901017241c1d40902c40d5098000d040310a07014100180c4101c01000f5044004c12039001180c6d006024944510b204111100742c504840c002c032120007505050104101c038101d64102c0c010150548024804140d802e42e40404056580c448d401114010911556843e00d038014425940104810140560300400c201039261b40510745c403540c800d0310f01c1d203444d0410f461120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 592892005 1250 592890755 592890797
    0x9050106030c0e01182c0c070f03140708030a1a010c2d080a1e0806030303042d08090a0e0f040f08070f05060a050903070c03122c010807080421 63
    0x1c00801c00785100e44000341480d24519985400c00380c7e0200306810801e003620342203420864283e009003070108450150100460304000d0b51160b07500070000c291030780b610007400000782600300c090b241c40d07545c018858082580a441803210040d00f2101881703081d048a500e0104802600c0d151024540d00607a003880011f0611000303024104841d0707545040302684d2002c0c1c00003c0c5038481c80d503041c004180d04101c12501c0010580740c3c4070750407101c2818482a1903516801401904c1c01d0002411091000072060100d194004c01050b003040d0b65583c800c070b07520300fa2521394400584202c0003500804004c00c0c00314912038070000c00a4000c10280c0c0c500481170741d80085072200d000c0308a40c6504082c00300451000c0d18484d803580030061501451404c41d540e40c52180c41c030b2407400b0050243c0840102000842e00c40c40d19a00d180c04401c1c1d00741d0440504242c40a603a00c01401c0d4180040e0b0a000041c6180e0300c00d03030200340603603442407680006840044421004c171004010300010021500001240400003003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 592893255 1250 592892005 592892039
    0x71e080106031101090e01081002160b04141b03060c0a0e060703110c1c0f030201061203030911030f070b07021c0b060301060e0c072301140109050106030c0e0118 71
    0x94260201003200d600145c14420180c1c00707403210a02c0c00004004680000c191080e402e209c83e0001039807404c3d0308600c0d04c4140708083d400b40c88090b60b00100820043e007206c90000c006107000c100c13611884015654048560400700c86601030300201c01003103c1c504240d000d081071003802d04015840a10010100b25550031109040d000905046201341c003000041c0b2200d003c014059608005d00520800611280d00740584000d107002e104036106802c0c14803e41c840300150140000c0c440862109040040142954080075110203682c142d44180e46e18001401312580300071140134080301882d2800024141e00080f40503a08207410413020030135000c61000b01c10b16544290940041410003006150844070f90f40c0145104940364414488a071101400380c2d20f5041e401002c090b1054007400c1004154070003004400d00a600302200d500d5241ca01145482c10f0b2000204200410b80e0317a07c2d07085055468103001c0402040e4141c00c08080395202c4da154174002c918540d0316400b003da403009030800400b002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 592894505 1250 592893255 592893263
    0xc0f03070b2205030106051503100806070309060b0a050108161106040305070501050f07120e1510031202060f1501210e01060b03010305101d0a03021b0102030c071e08010603 76
    0x281c910400300510200b560b0040c20041e002000382c40c0c10b10300840c1062142c0c3d031440c080d102c400b000040d4010b91244107a0007801041003580d040382808003018024100c2050101ea1450400c0c9008043c0d05100f6940307400c03110144d5911207a912002603503020180b40e101a20204090a1040c404011742040f032240118480e5403044daa660b01c0d414003e08444002d0100f509518084e42444003081d4090ba4444120b1320041000840219426a184c61704402004003510380c1019800c201100e140c10078502c044900915800c000540303284412a1140412560013005902d0000402c7d890a05000000506903040c10003060f04000042003424040d500520055569203034810012149001c0c051940100041600c49040d94110f03074800d030721162042c002c82e110f41d42d40d8a06c041c61480801c1000c10381030b1040e0035034540c5919808c00079141e02074179104c000792801c00100d01d105035200000f1107015980b444060f0500900741078000e007400c08050140200300c203880101064401c020710882c0015845 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 592895755 1250 592894505 592894537
    0x403120c030938070c030c0801050702070e130204110325090602100c0311040e01060f17070e061c0f1a0102030a0f03061d090f0f0c0f03070b 62
    0x251400805011883d00300240e0789100d40e1600038003000c41150000002284080581d8030803462004401a000c1c14a015040b046120307400020b00c181c98200005582d0410004d004954a4040990f0703102e80c18807400d150103d100e00025092040d40c06600036540c1f000f440490a07014850703c0c20340e1904152048405840080549041c05580c0301d288000d800d5141860380c07569140c00303006510340d0440c020401c1d03c580c030b035248841018460703400fa405922071500b0f016103842d203500340000352a1003401500c0118002c50300c1506414001e01007081074006014211003559a04501141e401c01c0d40f0211a420003030601c1500c900ca41d03460305a40c01e14a20444c0064070911120000c000d9030f080000003141d085103100103c0c15668007104980100f001420440c0c82004403440440040c416075000314003695074800d8007105582c25191032401501c01d82c00300c40141c040c200b2000d8480503a0500e4202a03880002d90140904007a846110303a03109c000c0948a1040c0d036004d110603150300400c0d0031054041c3d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 592897005 1250 592895755 592895777
    0x150a0605130209010f0e0a030b040819020a06060806010e1314100b0f1f1407020307030606030201030c1d040c02030903030409061a120f0411030109050309150708040b0a0203040312 79
    0x191045c000c003500d41051625000405034500030441140141c0800340500c2c1d00d00000406228116048504142d00201103282c24580706000a403200b40200007154480d0034040e0008111400141040c160b80702c031046013105485040c8a41880e4002c3c0300700f120800d8550441c1c44080c1ca003400032143d41c05005501050390140c00c010401303103000c1500711510940c81c01d00710340c0d138401c1d117861000080c5c4042d040c40042d40c44040c460314910b02031800020b40c148211280801040500c0e0480c0701164401e803410f000800d41803a00352641c0d01c1c80880412910040c0c140000240340c9a080b08c2c0c4004440e005480c501028080400e003580c1c05504400205521036034200525110700c0f8130114881c41c004056400c0844416104410540103000340010424900c04202409064002c00010140c001e0080003103440d81e180c0b46841b9000900304c14030404001c503007140301000c3d18040380d4100d0350100845250a080c4005800103030007101c00c50382184405e220101c0012000c103c0e1601d00e003115111607580382 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 592898255 1250 592897005 592897007
    0x30c270a27050a080c0f030a1706270606070f050615030d080105100e0301050f0105011d060d050403032004090b060c0a11060f0d051503010905150a060513020901 71
    0x8005580c104070012054501c1000c00c002241c80c0d20182e6014081e10354885400048514000700c101d884403c07800f00081d4801c00c950011842c041d0307252101c00c80016035440404012903900ca402400d445214504000d0714280002101558886401003c8905112042d210303400c1d83c203030680f0121041ea1005050240e005004000c51040c0380c0304500034545516204002801d1407010310034540104040030b148003903c0c0c003901c511944101c000d4020052450481032440701d481c403c0c4607443c007160a841c0d40340e401c0311340560f41c43c0a0322009092039207001101c0c14400d0080c140100103130105542ca04031000070300f0745000c0646c0c100e95969811910756050442140845a1201c00c60b031050408102900404401081b0200481c3d0444510903d840318100840d005101d18501c054a14100144601441149500481c0240174403050600b0b40c0314020203050803030740d1014016100340c0c082d00e1800c0695040315403055000c421042d02180d400c1d5100007049009080300702c50310f081900450344084039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 592899505 1250 592898255 592898291
    0x16080a0c080c0109140f04330b0f1602150c010f0207020f0909120a0c11040c080f1003081201050f09010b040b070c030212030c060a0506030c270a 64
    0x25041c8000035101c115101c10020f014400f903072041810f014508440b0b815690b80720b034041d003e84540603000b88101e540f80c1d04110880000a6502c0c41810140100f00b10070031603510600090310303203240700030745403841c0c20741d08402541180580c0c88540e401d07035201b0070041e200ca02d10080100c60007000700d41c448503414955400d41701d0b80e1908104030b62043c800c0c0005641e400590981c00740c41a694042a034031032208080c1080c07041080e0919008000568140556015000c40c2c070032030040350f00ca90a5411641000700750f40310360180c280010700307183c0401c4c040280c245169402c1b0381d4042c14900c80360b41e07a070b80d041d240b50401d490580b2008900c0f001004503050030034107190200300807030380c3c290b6540c1007030f0959446009600804a141d0701c0814540204a400c4144002960300104140141043c1e80c40141d6240e0001c0d1080c103190061402090f0410b006003c0c4a0103000003c0252045203192801d0140c40c070307000c12940404038030211f4000b0350408044a02d90040c40842404a0382d0182d0701c0d001109 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 592900755 1250 592899505 592899509
    0xb0705070905040c03030c0602091e010215040b040221100b09070f0f0305100b03040506010305010b0102030a080f040606030b0f1605090a03080d110a020d080f06012016080a0c 77
    0x30a0b060104000004602c0d140d9402640d0749828005030200c0d507402c05800900501d10f0542c3c02c449101e86005a6503840c044000504100f44e00b01e820403040c0481043c524481920001d140c40c0010000c20300500e450758024544007540701114490909005080f850f005004480c0001140c0e00c0070b645155052510015034000f140303040c55440740c0e1032184010410074030815100e04256441000c244024960400a4010031a200010b500c0341072a003480341c0c90318030a1200720b445600e1301241c0e13001c55001105a42d8540801d860711420303582c812880c040001c100410460742c1e595074100103c00114500e0890740a000c410070504090b142c101c0c00301001c03001d02c6c0c500900f070100500241d0701641d1007c0c0643c080c1c176407212040351903071000c0941c680608041052034000a1000c10340c1c146243d800950209103400d142d59038815504e405400c001500b50070f50f48940001e41d0258240503121b0742034540c000340041c80040751140c1c418241e0140c01c0e00950f0300122090f8101c20529020b06c00c8015242c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 592902005 1250 592900755 592900769
    0xf1c0305030a15061d03011d030c16081b011707110717101104030606060507030e0d02061207110115170102091f030204050406030f06050a0509060a0e0f03040b070507 73
    0x30514203059005e00b4211300040002d001c40d10307040d030303c0710305413801e4000c59500300c555068008446203064040c3c0d143e805c260040c0315a4032070300c22250100c80403800304908a6821801601c0544140040341803032030503510019041c4034504c1c034100c030001d61090490344107803201da4410605000a00350b0506003075036584551490baa912201100c11032000c11050100d500e03a850000c0e107140d004082040c0e5000d43d130720150086290030000545150054000c0c9034640c4a541d03100000d00703200302004211112400040e4000200780400380c2d281d09810580e5400078002c0c100500c1c0741e00c40c0c034190b41c25a00800514045441003034010408001042001c400a4102900175030808001e0f001040c0840400c00d1606480c0303182808001f00b15010f0381c1114060300001e40140300c1d040e12424030451804203801c00f100c2e95407500000803440c81c058420716004114800152043e6200c4680c0e071000b820306000300c2440383c0103000c101d0a01e041c1c200b00030f1008002440d152500d40c1b400d420221700703040e000c1d84a50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 592903255 1250 592902005 592902041
    0x9030b04170f04150f2a12080907120b01091a1f0f03091101180e0109051602030a0807050309010204120b04060c0f02030f0f040b0703031d0106060804020f1c0305030a 73
    0x1095040c2c22959501d04420603078500d040e84521540101c50710071b0b00c201c001d41041303c20800c2d000095404803100e4840d8811100b00d840070f0707035180c0c048a000d0b4030384e02c80030301100361010040c005100707950040d035000320740d0410302a0307200c400c00006040292015452003041071505030700e40c003040d000900c4081a1a860170f041250303164988441060701e16103131071241000070300004a411070200d42002809408904690052980c54141c050003c04054030141c070005101480d28504a10000c00c64000340056070701c070352590b00c03040c1081e180e0350006083d01142c1e54007131001052951091204410060183e9491021400c00703092420844e001c6108640820040703884104025400008481000402c034802d50742d0340510400c0a20b29011b5a040324490140000351101803540c50381020701d501801140d48040715410300141307400c0f13035000d100302c03000300c2c007940d0014004d80351008a100f00d509001d441c000c050201045d080300c1c0321503402c10031000700e06d0100510480c42140c0c46881d81440200c0000c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 592904505 1250 592903255 592903277
    0x312030e0309041805033c0a031a030a0b1503121209070302040911030f03090109090e2805060606160809030f1006030302100c09030b04170f0415 64
    0x1540c1ca074414200d6680c09251940050754000341c0e40c501c102c028903040000c1d65100c0c18240c00391249600301000040f1040d80c9080b400b140c40110109091101c0492200c00d49070180c403aa0070340160a0070b01850400100c41d0000f00c40030344041c0442140386104900c181480c0c1307071181c840e000440410801780d00a0b403081904d44203410712007044540001100d142c200b295956008802e00d01440c0f508001d40040c01c101d0001d040155003622148904821010780c0c5c10f1b06049450380c1c0d60b81c0a50309010b8000380700c10320104010a01940850041c454403012fa6005900442051241200481031210b204003911183c00034000c080c0a244e411035401c44120b40b400340c80281c0f50031540c0107400c0180929800055a008035542008100018800602a0b80141d01c10b560744600a181600c82039016000b400141e50a42c4c40a118900d894400c40d207420411505646810320000d42c020f10450f0f20444002c80c54140c8030200e40a82064050306203a940d4441c2840d6940721820030504003201030081c1480c00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 592905755 1250 592904505 592904531
    0xd020106170d0e01050d0902040f1b0c02010905010e0a170d023003150301060b0c070f08070b25080406030606030b1807020307060e28050619110c010501031203 70
    0x60180720f8803007441c010392207400280d200f8000f4440110300941c414600080104202d40d15000645841100c91110418510b0510141c0f040509400024001541250309208642c01008080d05560000d00004505030f00c4003070514041c200150f000b01140d0040c219070112690401c09034221452920300707a80740c00503485e0740e10700010142c4c0b510340ca000380120004044008000741c1d140b0490b030040c028812155104111002a40003208403442d5014647d40895080151a01e000486006000034034007646801e0400c42e43c1e0300141041c80d1102c01d001c03040c8150000640307200600c00e0181c80b9941c0e60b2450440d015080351120b03070104080c581040c22290301581e8a40310882c400881c0708504101303540d5007208a0840c407862900600d041c0c41c000703560644600000d483c0c5000034646030210000404000010044140758000070400c0c1c0c40400046c003904e14000e2284e20810702000701184465000074003581d281c100300c00d9011641c0d0341c4d000400a110008200c0b514500300b82c01c0801c210700364000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 592907005 1250 592905755 592905767
    0x50403080a03020f0909150901050307060c02100309140303060a0f0e070c02010201060b0703080a0608031c1a090702240106020d030209030304030206040e090609120405040c020f0d020106170d 84
    0x22000c240750380032401c0d050a500b142c08441c0c01c000006c11100440c5800d01c40c0d03006200101c10320078052800c03c40089a241400580041a40d85684884040d02243d5007000076030310800e040c07901090345079040107001a0708c02c124407a0816059026641300d150034024000007094a52007400181c0000204020410242c011039420644926040700c05809500040c1c0c05408151b20811070701400103200c0c000d260740010107a00810b400030052100e0741e580c070003107a52401030700c0c40c401d90480c03950910040300c40f565006107011445084038803e02e89500f03000413044081190440096040420600882c0e0350a1003041e11030f511000c188892075040200c004e64031310341c9050010905070300080000c4141c0d420800d550065070b000f0100c135a200c2c1c5505140b00e14a009031801a0107219050100ea400540428500d0f0400103280480341440d141c04100000350005000340029809501000f0089240900203d0181d4a041d00089095880c05540300c5d900019040403040d15000042d4100125501c00c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 592908255 1250 592907005 592907017
    0xc08070612200904140c1e042105100c050d0c0206010e070f03020d2d020301030f020d02040b130b010905120a033b0a290d0b130501080d05040308 64
    0x10342c0640300c00d1000040b074001c0081a01c641d0201240004000c680704003080200541c0780e4070b105840d184454981816540d00450081200c49000e80d10024485000101110f00d0507015034100c0311314002031041c14040300c2405801e040081c10000e4030100c0d1081038040c0f58003101c1c0d940b00401107507150140c621004000030f4048010010862541d0f22054400e406a48600c440c840041107910010003900b5024a800d0781041072110000b0f4030020b54030154400c0d20f04030394001fa410040941c496080140d0603000c03200803640b280e80c41182035956140c0700e00c0c0c0600042c0400700050211242000034016280a504c018803d00c0e0036411261141404a003015142d68076042403001d081c2c00e01400c401c004e0007a148076592421854001c0c021201820001c001040b0540315102d9668640340c03102c3c07146e019200380c4090200000440e00400c843c0c000200032200400e070002071258031200010b002202104001440305440704010300c0b19910a200d00e003000800f0303040042c581071441c0c0e03402c04280900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 592909505 1250 592908255 592908311
    0xb041d0c01201506031c09050415030f0c0e1302030a02130e060f01091a0627060714010b12060a09020a09020408030a0e040b03030f0f04030c08070612 66
    0x2201404080340c100100b0007084845060742d003200c41d91000d40f020100304841d070511922901c81c45207005220300b441c00c0b80540140c0c1d12540d016080c801071102901c038180c0140c4401c200d5000000101b801c00c40000000b0344500d8116078014684903c40b540c18102900c518110f41100007401d005035000201c0c80222039041c1d580180318050301c01a070006000e0901c01ea00751340220380c200070800030315152a90513100005410055220382c600001922840c0c10b80e03058024500300810008000d00304100c1c02807c19204200d8085041c03000440d54a802055003100e9031201c04070312500f00a0280100708100304180c600795668110106425551352019080f00941a621b400c15001d640701e9000720400391987c1d11055607110703900e8412550703a900440201d4000740c1d090035072a11514240c040c4c041c4c101c000400841c1441035a180c034601550014980030b801070703000c00000000908000351100101401405042181d01c1c02001600c8880d049004079646440c0550807010422407099011041001e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 592910755 1250 592909505 592909517
    0x1050601210213030f05010501060c120c0c0b041d06100c0b0c19110105130c090b01030f091a0c030c030408090d0b010e18371202010b041d0c01 63
    0x350140000e103e41c0442c5900d9000c01c04000c41813014459020b50498401d5008001981c1d82e0f110403290303031000d110010321506102e0303003015a40e031040003403030440da000e078907489021642c800011031250b200703502c102c444401c040c8501440b034003240609030740f084003558204820402032000800c3d480301e03200f000b06810074500201d2016540e01d02551000131300030160080c03405100314080d1060382c54811218003982442e0000b4407a000321000c55104907808002c5501480c08e184a280240c0010038030141015900c40344130075000c1c000c3c0500c10760315014854412070b03054580c2c03444440400092030b2801800c1e0410a02480070780d0f4204980d0308c150004480740d1218104000141c01c01500b07403000e002c20820600119a0b0a01c804c0668003400402d1506402e0781c52583c1541d440381200441c805d0134030101c030381d07200e440706007003401da0024000390742074100c1052a9075a80c2841001000842c006030744d07400d0609010308042c89101055402c4895652802c4400d800d280d69460b6034091503410004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 592912005 1250 592910755 592910807
    0x2101406060f0d0504230d0c080318160e060904240f020c07080601080d1b080f030403050a0813050d0309061d010f0f05060d030e010c0c08160801050601 67
    0xb1040042d103035041200034003809541014101448200c845203180c0004c1e04598003440700d9000b001911241c08a0b040d00e4482181309691903034004c40d08010b2a10751641c0343c401000765024401c0c000c0340c074500e401c0180e02c0d03050781c106121800005002803585001c3c80c3c0c07000c14080816500541c001c42c010a144a080c451820708100001038001800c40358003542c004a044912004081040401d0740c580400301c4250341c1c0c1e90100e5696545090b406003002c11351200d2071b9440c208501441da80c015010302450b500c0d25000300303483d42c0700780e008079800e600141000c9444081258030008894001c17941141040c11140f00c1c0c2c682a071500000e405074424140d480e0070100070480710b50002241c20303800c54442c0c0c040e010080012406010b01414145a01d07190052081074507071248034850140d64040d1003042102030329901038071220340c84044141804030409590b4001403003a0030000113801060007504400c00c04600800c1c11903003541056255034184020445240d80c040d1014400255618101d2a005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 592913255 1250 592912005 592912027
    0x804090203270136080c210c160e0a0203090c0402040b04031106040311060d291804030212090f131d0718020714060906070210140606 59
    0xc902c0c0d0340b145a1103044503002c07809280c1940496201600340409000420f240b4007180d004104080600f407440c2d403603541c40400301d42c140c0c0280141c03009003000c0300c0082445442c0020103034589509101541c030006031841c08850280218001007804030b5140781441c0c100220b00d140400b00818079400b0750750101c0007419031102001440000326020b0b00443d55151111410b001d150701c24002900c0415420702c821610b420040c0c01c682c1165000340e00b5002d400d280100700720040c0c1c422220705400b151a03240307608120500b00c0d00c1d548407a010380d0710f42609040c61400c3c0003001c0e403210242090050814100004a0b801151175051300b080c00030f09035914100c03180041c5004800c0645581c111565104483c480c458a40c403900000904459061515180400340c1d40d943d816800340c48440307480007140c05540507c60b0050000d561154056091170f1010140e00361130140c044403d035925902c5801803044098042c4540c011040c480f0f001804504000030034890b0a000140c18540170307040c000b03600b8a0701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 592914505 1250 592913255 592913281
    0xc03070f061401090509070806091c0215010e0f06090601170705040b0f0310080703050d0f030902040f0507030b03210d09080f0c0c0a060806190914040b0601020a0804090203 76
    0x101400b50707030410465071a500c03141d004007001c8a0702c0c0c265200e00800030412400c00a880391155064000030000f001056542c2c2010440d200040380543c8114002480750010642c0543d02803c000c54800c48503280500d580b01d861301002d000940110068030030f0224690380003040c1c0342c009c0d81001f0f4041103030301e40c80700458481c460341d4010301450201169920b201c101000080d40100c58600400450a4076203420544902c45444010016444100b0b91035849028844500280142d8100056101ca1070340101c0d055510440f419070300c240c0c1d2074003006429a010b01c0340c2d84401d441540100000c241d1042440c400c000884070301080c42c40c010a2003600c04a0942048540d944e11104264030740751140c01184d01a00004c201d1079150040709141d40941c106840400300311202940c4041c1940c46240c01c4c40b940030120040a80e880026080c0402d500c0d400b4004d0621541427100c0da03800c54a89401d10041030000500424110741004100a0100b4000c0d400da030255804003070016030fa82c840300880e40d42 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 592915755 1250 592914505 592914521
    0x8030a2705060603120f1b01090204020403050c090a0b180405030f0412120c170c0f07060504060306080102090a17010902041103060103140609160e0d21050c03070f06 73
    0x100c46a10400504101c0c010030b0706801841c00f0390448520304400845804540107546030750f45500710601c14160b403103c050810004801c0c4803000000d06104c16000300d0160781c010b4009481550001c82c0d041500d080c061300141c0d020426880130022400204002100340e0f52902245900c444070101080a000c8280100d41c2800791510841e40d1360755030f8560701015850b20110a80c0c1020440e4900c0d080180540030400e100c0e5480804001e0701b02442c00303e100c4030f030003000c3e41440324403642090111800341007115402400c20307070b00c4480c2c48130302c2d001c8010280c2c1c18a4020f854145d0052091071b00603111044840e0680380034490040030220203100d41c40c01041c0d250360107548079040030f1404204240500046000700400c2e6020f12410103036084043d40c54400350303039094200000600103210500d42d0074580e4094a13661401450306440c080000b0494071209006813220442108411004080c03c0240e0900c5032550074620b0501e003501e2050707504c1e405000f87c0a4406482000d400341048200e910040e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 592917005 1250 592915755 592915811
    0x6030b01090e250305270a060509010f06080304050607030f1205010f031a06150a0504090204090203061f0f1206030501021b1e060105061305030d030b0102120708030a 73
    0x2c0910b0322100c031000400781c0800d055068103201500c01c45240c482d010b0184203070f17003c080d2202003904040041c0201800c0600803c041c3c01a2218080011643e0040b2070007003014000110315039050254100898910317174045840707a031007040100710310349034242a14407403601418515000b07040e00000743c5900c91110a0900a00e16040011841034034401d40314040c3d82c0204940044103130b800b41402014041a140c00c0d500c0110900001c20f424007079001004040d0303103482c0007402c0699034550103050741c000313070481c2105980110820070b9a06005028420002e9200c0a0034000740c5002d201038801180441050108005100400c40f40f41d0300750000001564000700840d6075601380b41207031114901292110b10980105a041501d041f41c404442c0004120f00000e0318007039281c102081215030180d130780001020303281000040c0c207907000c1c801c1c6510f200d95034801040b0014551300090400c800083d4450004c0f805018980106803603100742ea034000490540000c03031080641000c2410402030001c44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 592918255 1250 592917005 592917029
    0x90f07230a06020f010c030b030613050c03030703031b08040803010e0a090c060c060e0319030207021f0210270f0201110726060103020d0b13170315100906030b0109 72
    0xa100c0f54001240540020000d000700801c031150201102503503502c41c401035042d40068080b030700c201401e0340c1c001000c0e07205008a8000d42e0301000400d0030340d04480c4007900032a54603a606500c0c0d4900e443c030383c14a90300518100d1040e2605139030307a803058001030103403812030b002c0740740000e03184481648140c0d800c13500285081c090307581d20131000f001124502e00840b0383d01d0600e05c026807004800000d07034090f6401080d15040b14081d82004400070341200c0000d9030300940203000d049040303041d05050703440d5020310740c003800045910074843c03810b545e4005002000251540a942103105400d410490890b40c8840041c0d0707009110b000403900c0d80d0b1041c03600c1405008030440020702c070420440c0944800c2c025009201d02100d0407480350b89501d400d100c060742244d240e8556100180d012200142c1c0500e148d50a030710b9032001a01c030030754040600400043c1d405000018804000b04101c01409664030885000000c0c043d00c1d00001c02e444280d01c505c005250f210700e883c42c01c0360302544481c4082d1851803840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 592919505 1250 592918255 592918259
    0x711070302041d0f010b061603031409061b0301050f0108041a010e010f060302030f1f03060f0c08130f032313030c0812031609170601030209090f07230a 67
    0x500c048040e2080f403c0464030400e070340c001403584c06003c4e041314800c00500c1c207070404040001e00d80d100c0c8054102102010360b00d1240c0711800c11444d80d150b010300c03076130380040203070703150400359024030400411078031040c0101440100040d54031034072903158550085c0b80c024416162480c2003208901c0c040c0c09600100b03001c0c0000308480c14030600090488001030030b000700980d0740340d0064041344029518010342c0c80c0f007070001406030390360741c18440002180315082c081e116030790303848403011200c0350f0f88070380d115a0300c8405100e000d0b58000807882c0c02617801c100740485038070199503c00034a00301900c010144280702c11b54101414104084580d900030035692590390b0203c3d0510070a0040c4580030450b212441c0b0500820700900000f0101c400a41c80c203452403643c1c40e2818003070503109510341481c0400034500701c042204d40c07944100c41c40ca1010b01d8000d00305941144104a440d10000f0700ea0521688203661102c100300c80000c03003204a1b448501c150480392182c0e8122092111040b05858004541c41e00c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 592920755 1250 592919505 592919531
    0x307050a050904090b0907091103010515090306010308091816030b0a09112208060408090a0b070b19112a0f060a0f09020612090a020a0f0503070e04020306071107030204 74
    0x40c1900c1070038106c0688802d244c80f450306404a408a814001e4450350600040c04241451250790700801003a42d80da42c10444400002490210260000c0300d0004001c204070003981002840c80707030801d401c401480a24036007040c0503124020303100000810951164002c80c099210307500d490029014016040c496034a041d014841c1300d41c8108040c81583d00301c0071000060341c041c48604820341c1c1c0594080c00050b165034581c440903410156170a5030000d020300001414180080003841c174640b0a4070009114607100c05030800b08411018205e020380d040c800d408030708a05001c02c552007820042c0c0003070b03071812052000c0d4240050303011400c0028450040c49007071003100062890710440c5e03210b0b001d11400380b00620905c15201d134024000d4022005200f86c8201001c10032080c1d90100841003100e281c034a40d6000211100001e070f0000818601c1c814042c88242810701000010384250540c00078a414103601003540c0d0324005140400700180d42f90f007035004003018082c504c01150001e0091044031640c0364 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 592922005 1250 592920755 592920773
    0xc15020406180305061b040b0301060e030d020c01021f18060b1e0109030213021e09030118150921030212070e03070e090a020301090b06090c040b0307050a05090409 72
    0xc400125405a0070b0b0880e102d00c00c481003080d41c0d4880701401c5640c54000d0003c00414250103165441103082c000070513032801c00300c013650080440f5524400710000c9102450300345401c2e0340ca98000c640220003031004690300001d2203520000c0240c9401c0c981c1c100100e00390018030302807904905442006070311509000c103a4002800b4800d00303d4403200c0c6840c101c1401004132003001d007207030f010503400602040545403401c0c0400c92140d0700c2502601d0007091036080400604a210280c180c0d40300400c0c101020b040074480c10b0741a065102c07248040c4c01268482e5076000c1810320000d20455114007100c4100088101c2c48510711134410440680d494140030701070081d4101c0d610310a0f054002c8000110744a119902c0e1101075030000d00641b0820b4201000ea168545008108030014480c00782c2981c0180ca0900c00c1c1c041003401034003400841d0400070100210a02c4c040c08854114400f40300c117100d069454811290088a01d003412540d03404060b5003034405004908000d035010b86003012060520070514 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 592923255 1250 592922005 592922009
    0xc13111201170d020705130e15040501110c0604080a2102190c0206090d290f0c0307021207050a020406120b1f0303030e100510091104060806040c0c150204 68
    0x16103030b0508070b500c0b000110b9558148204800050780540c000f00207a00700003903c0c04003911b2910380801c0020000c0d014500d45460b4001c000c150412020402090050a206100410122840e40d92030101ca00010681e140c00180c13000d80100800166110b0b0707180074035800c08805043e000c1c5070990b049099461402500490701604440401c5039180c00303118414240c848009500405c258102110700b801d00c2011020310f04102c400820a64030b0485050111004d9402c1e000c0c44c81e0840030f03d141c0801c1d0440404001b510440d4864024802d00007403d4011814414640b002c031586a100c81c0c0c50700742a0702d06904004040d4002c0d250450100f2094440030740820103600900d1440701546441000120404100c0007000c40e4010504050001038031a4000303100300d9050204680c207074030304d03680c17550708031030098805406111084108220340c1109014500c2e00340d03030001596040610b4581c01410702500103011901c50381d0740d6190821100d0107801080062034100d4034082034404585002d4001354001c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 592924505 1250 592923255 592923269
    0xc120d0e040e0618101e090609020a08030a090e0906010b0309190807030f020705010503060f030a0b07020303040c060905010801150315030308060f0406031208060303120a2a020c13111201 82
    0x200c5c41405114440d17014040450001d5a0080f1000d92541000380007000400011580e05031a49442000341e40d0306030394000603140c1400076664a901c0e0410140515a00c0d90118000a00300010070482e06d50118441341199141541c2d02c0c1c0c2c81e514060b00600f02507074418940d0b414210482d00d08140000380c4044c2860904c01c8e125000c2000d07801c0c40690b43c9a6983c41128006003040000503a00d007096070582d911b03401c02034125442411036503a140000e17602111210016403004c0100414003405d9415240108901d00300a03c603a410540000c080000c14000c554804544500003d0585c0c030035407100f0929414a00b0034520203441c0d180040000c0b4003558004e200e604a41d110389031900d020b10800f002c980e40700000c0047e06c42d0104007030701c1a032402820390382d047c0018003103000407003004d000c503d00c5035840b40400a8081e094941e181401d002040c2540050a41c03002c8000345075800090706030220108442c0601c10622810140c405000480028104e042c004075400904400307220240c0d050b2851 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 592925755 1250 592924505 592924513
    0x10c05030a11090306010611070902030a0b0312160803040f0f0516060e0105160203071205010f0606052d0c0a15200f1e0f09030c120d0e040e0618 64
    0xb03080c07851000e4060422a04d900d42c0101c401009100d02902880c50751560020581d141a030b55100c006040342c100700c41151b101500c0714039201c041d1a05203d4035031b6001c0501c141e01d05000a005500815000189000301034031000004074085c810740340d4041422590150301140f04610900c3c000d0344400c0e200c1005100b00c070000d640403801500582201e428030106a65550034601d191508030304038508103e05a805002d01900892200804021440b1083c001c00000c54800301003080442210600c0d8086d608100c014062001102e8020840b03114031401d0408101030b500703000c0660040380c859490700102038440c0c0e80c00501000145800310f0200ca0091408202d80002294031007210740180111000d50038003000a04400145240a018002e05111002c7e0b200c802c0703004443c1e13080c1d001c210b04c03d009440115042042d80b804001c105840e00050300c0d40d5485001c0c5018441c1e4480c0210101414070035a501c2041d42502ea5500442c4000150720440f070103403c00c00700c03c2c245103015003020707001070003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 592927005 1250 592925755 592925771
    0x109021e1806060d1a0a15020f0604020d080705010615030b1215012102100503010302030d180b0a0309050118050d0203030c18010302120405030318060f0403030c050705010c05030a 79
    0x100c0300600ca80320300800b0348403902c1c00010300c0c0e400d070040040145420003100b08006031901900c4400b80940607281038404001f5101003028082d1415a40c200100e0442e80483c0c00c03c4016103612130b031413081c20792140f045c0c0d0f25a001454118050542600400c921484c4d9502d407048980c2d0542140345c1e00b42c0143e0300c88000070503a070411511155041c5000702d0482100004100d03500034100c410751056503c1c4c000e00186107169002400c283c000d0203042e4002000400107205519007403040d54001d0542e402c052110443c414a1000d50640030301c50080011008500108901d020f43c001d441d580e81d00c40b00070001c48290100340e01800172020000d075010b104403ca1075036490f000000b101d010360962584281407043c2c10a80c240d00b10710b6040100d04254092000c001d05205590310b450150784182c001c6c58991810f040c03242e41031981848003002941c401d10a11014041e91504c05403c20340514000c15091103c8505a5083c410799100500b5903181a81c00c00000e50b101c80038601541100703505120340300c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 592928255 1250 592927005 592927039
    0x9060e010302090402100c0506040f03090503030a140a09090f02030406141509100806090d111b09060414040818010f0f08180712020a0501080403120e0109021e 70
    0x2602404001d42110941c40420302500d0803503280c06540c5c041c1d145c51591141c041c1d0b101c030b08100040c4d404807440b1900303219040825400a50398805440d003a80210704150118400511310101e106a07000081c40000e2400c00c1e492041d4444009004205024071140c044400e0ba100254800c40341038401500d03100d8503800340440c982c0100d0082c0d1020703080d41b41003220441003100070382010300580c11101c2280400250642d0078400188510101805081107103414000940039062510a5003219007120140d4039070700d108141014080c030b03c10380365101e8503928040858018945070a00455010691040000f00140c0034001d00083c03084120b80c50300c00e11048010742d009201c01c0c50800105031901421001c0d18031444045a00052600005140402150030b403402c2951540140e0091f00c080002c0c1e400398106a41c1c42c100800c000e103803003449440d041d00c00034001c041642c440c0403a07640b200311941c2c024809400001282c0e400910501c030488080c2081800d40c9240c05415010b0031414074409644 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 592929505 1250 592928255 592928279
    0xe0a0603020d11011e0203032e0306050603030d1506090504090c0b180604090605090606210702030403050d0e3a1a15011101020a140912060a02040906 66
    0x201e0303000d05801c6400c1c00c15a40c400070f03031494044850410401224072000c111014640320548101a00555524244410f0014821154186010341c2d0082074042d0403c510712511201c00b181c0c0c01110004607912824002415072243c01c200c611404d044c1007641403005401c0d1401000c0310404d88038090105d80c0e610510040e1601c0d440068030400c40340004004008a1b04028908005280b030081902c001000006001c6d41150704141e01450303685005100701d0600700180d1f504044100c3d006401e00c13584c08403d1000c000c401c0b401c514800040c46c0400c030168002c2065902a50340300c02030310110010150b0040c090318002603280e00c280e40000b200c6040d2450244840800b0900403090b10038112044030040d941180340c401101d000114042d01522a83ca80e00054021101444481240c01c0c030b134000140392114103c5104010f9104100d80000c1a03080b0200842203004150b00c9a262181000080d03c80f102001e003040580c062203040224140d0aa030040060322400b0408001c0326840c0d18080e1701d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 592930755 1250 592929505 592929509
    0x40806010819020d020d0b09010516030e061501050c03030a020d0c2c0d060203180d05180d03110d02011b0905030c13110f0d14090d12060506130e0a06 66
    0x80440082c004030142c01d141400a01e50f600281c01c070042140550b503225440f03031040f00d403050981d54510912003401e40101c07a40030745840a1800340010303146c0c0d02c07009880d8003000c0e040440c2049803000c071950a074052030a5800700f0356103205698883c6071610400d400f0b0b5000a20031420a480e043e410050b9a0107840c100c11411081d40b042042401c0798000e01c030761210800314030341d8804526010500001d9040c0021445041c42d00740040392030302042d2041d4030740700c86503160743e090150a10103403241400700346020140b22001c075074201140d440c1d401c05440c600410044580740d07020382e9460450058054101d15850300c0c18140c2c0700070402450b1030440d2110400c1c040c1581c160801311400303030740303180808507030f8280c0012600004800284142c981c40d540d06c030410003410624045803881c2c2c0000d1074400c1a81c04030390102d000300f01e485c01030400d41e100e00e41c02c4400001e02c500c03850100c9403490158011005000003030110791740c461030305138182030007041031040000c1c800c1d203003000a451041070300816007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 592932005 1250 592930755 592930783
    0xd05030d0507020c03010603060f060b030112120e06030a050702060f070e0d140304030c1701150501030e10050108070504111305060d090804061e09030b06010f030e060108030408060108 81
    0x400c0c038055000900203480c016120004601c99110012102d0740c0070b02c076240042d40300300d500160031030305510b4020944250303500c900486101800100180644d10948101081c2e011250850907444070724107903148a44400d25a1b04138102108002c401c0810f684418020365950b000c90304c00ea60349100000e00902d0840e1000002003466190380c5150500f07101500f60540700b1401c54800f40c0c1203407005455038100394010b5403040c14402c020009008005580320181c3c413200002e1101014a42e884004486613100f001d04041e035540d642e0f120808107221044070000703480030034050b5503520b0200e41c0c2d80c1c011900900303218600e40100c0e504107030922022909001442081401d1240c03070301d0100700c281e82042002ca10383e40d840d1401280007510381d00040c4094000e54441034424891021901c40301c400074620034050103085207051002c19981520300c0e500900920301b0240082e1008400c80c040d001c1c044440001c0d20400002241850009c0040d10a0741c29450844555a07038407250f0595800c40fa070b140760 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 592933255 1250 592932005 592932007
    0x402010e041e18020d060212070215150f03010507030507023703020f0d030c0e040b0904081c09140c01080f0103080307030b19030b010914160c080304060204050f0d0503 74
    0x68403603002500104070b048000d03c032072440d481580e004104040c0e980750b01210840d5002403080c48100b441d400158201240c0d20050118809010340004400701c00f8040192000b500040c803c100e0369081d000301d02196000e0700070300440c100b02e034020703010303010540f0180090b000714043c8c103910f80040305502c060400c4680e14415121802c22002801042c800f106404500480c01c498020355400c001081c951100c0c0c2c3e030005a26844140010300c9686640c1c49240700d00d00780502001c1e55500d46090680103a0020022035460081d610030300c041c1c80d04c4441e684105420009401d0a0146800088442c4070146060305c148907200e10046070744900807100414011003000060000c212214040c4d039001c01241800178510f250280010038200c40000b80d02d41c010440c3c4000c2c0100a5101d50750341c0104500001800034400102c1c00c80c901c40001413009000510342d0446418441c441d01a040803da0003689880c2c0da41080d0801d0000795225001c0d4a024106203803e203006c90412070101080160410051 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 592934505 1250 592933255 592933301
    0x1d040c1e1b14010e030c0a0c0905011503110c100515040b0310050702190b250903020628081602060601050702091005060c0a0515060a050d05030f030c030402010e04 72
    0xc00034400d020360301402c40e07650318001940b001c0c0040004000c0e940a01300142814501440e11844a40c0580c215640c55420071004201880c0c5098884082d49441c0c1008101c01c12202142d00a900828202e50fa15106110008014040c80c3d4043c80c002c1d6900c00e040101007500300103110558055800c00ca8155000040c0244600c000350301954110400388140c883c00e641c0e40c11a10800081f602040c3e03441c181c00e01c184061140c0e8107000c1b00d40300550b824150051240c0140203407150050b88406406490005402c00320b41c600300302500350800613985154004c800c8000020004e60742240c8841c400110303c01844515800000c08610540050b5242c6d41b030126154203200c2401c070060b246600300a060340f800304803561860b01404072600380f20001c1c95001041c1c1040ea282561501080201848110a0198035121003004000f614020364482c960440e0a00d82680742d031040d10065a40d5800c04014003800344117940056020398000d9840310411500401004119041000c15014046c040514 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 592935755 1250 592934505 592934513
    0x1b040b04092d0501060f060f02070303022509020a05070210090503071a0705100b3a050304210204050f2502031b0f0f0601151d040c1e1b 60
    0x242064081c00720071012000c0b01580d01e050a607001d9400c15603245080e820140311407a44010480b0403501703144000c1001502e10344002e074644c00d82550700c062501c81002d0040350314041c00c04901c0204965501159030b11440d0394000e200b604002000c2f40b0881081c01c80d09071140c420068103081d5a0000c0160400ba4a410b4000c0d1f5200344005e15140a0b140c14840306011880602000344500800c94020400c18080c0c000c00c10140c1c00342012055008440410321220600d154080c104489024109202c129070b0341082c2e4507500036a80908001460b020200540d11440041641140e10070340e02403207507880c2e80501e485262012120000f0100ea5440c40400d4801d00b11250303404072883d4011f03285014a0051070700840c2528500020032580b290349100d400032000c20000008010b00c02c0680020b50400b01c1201c11061a91894010415000c0010922040e0b0003000c04032803c00500802c1070b900020005080545203040340c900425102c5010300c41103001d0400801d081c00390081c085011400d56807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 592937005 1250 592935755 592935803
    0xf0108070e100306271104030f0816021c170406052a0706080907080c011209030327051002030108150a1503080d0c0509130c111b040b0409 61
    0x40003007059250480065070785000710b440c1d08030301104032203248170603505d40044007560800118241d403c2d0003000308001080c140c0e00c2c1c1504003503110880c01c1c0d5036518032034200d20300d03201414041d40c800b004005400d2404020002c04002911600c008404a51880360800c90790295104040202d01c0402070713400c09541c0c401c0000c540409083c0d9204403113407645995460484140c0100001c1101c0c101880b101e0703482084401c00a010304070007408201d111400081c0440201c1c0d8140c44580c3d10303242d11070704050198011213880c1c42003070003098040e001c40700d203403654012000064800d401005a0428540814000c07207041e201c0f41c000400c148101a020b204040728010310544441d80d4074440840030301501003c1c18021402188042d495104a0381d803c0129071803645c0800a000e410441c956180e00c442d50300c0f4200c4240820006a8808142c400390380201c13207004411114041c0262042c2c610240d82260307001020107170b80c10400c091490007440116201004090044022006014002c1d04000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 592938255 1250 592937005 592937029
    0xf090702070312030b22110d0605120102040303020309060c07080624010206090d20010203090c03100b0108131509080c160506041403070f12110904020d1218140f0108070e 75
    0x818500c0e0390b01d541101c0e040f5903c0608c50b25200c40b01040740e8034009140001c0c80600324002c5140ca46140d038044c2d9a413080020540c05603030027003004070b00308c03109000c141c000306048000d807600d5240145480d41107a0a510b0064502c40c06800358000d65440001e0710351080105400404620b804400203580c4130f40000500002c03020b498a105109100a0000c0d41c01101480d00500191440108040c2802c43d1004868040340c90500d01c1d00c0c10740c0c3c0c0f0228080d00701901a04198030308455003040c289080344008081d007603904101d0031a040040d0800100100030408098804001c03045c140808140201d2040e107074095018001800400038154652001400c028225401140e039640e501600021650001180d8886403030b0030710501c900d221190608003002c031030b80c1b9200d103030a9000030656111508040e00074580d040c01c69444601a004400115105960181a25507108546d010001203008594024481c0b491095983d500a841c001e0041c210350710313030f0785013486500140f1805c01258 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 592939505 1250 592938255 592938319
    0x3201e0f1c060c08130f020f060315040b0102031804020d18050303040b06012a05120f041d16080c090a03030807020d050c0a020d020f090702070312030b 67
    0x4410041150341d422980441c40c45014010180ea010709040c10303000c0303410812007041440a4201001700b050036496000e08078903442000341e5540121400030078081514407100940105000051008050081a041090704400c60301480083c2441d0012620ba000b0000c0c0250010604140c0c011649002c0d009000e00c3c816808000a403c0084042c4402d20300e00c010040d10035803c0007040c00700740b152001506510442c2030070301c1300c1a4a00d03110340b0b901c0b901d106420000d02c0300c502c0d00c005040200c03d2103d8030f800b000440005448801c0324107502c0d100d40c868450880c66003203800255800210320700314548240c42c0c03102803040d4410004000d441d8003400030000300403a9010022507400342d95904005020f50301a5031911454504464081d1400064606100c1801010b12560340881c42c0041e07000701c1140d05440386031031a00a4404640045258180240d21000c0c0d4001c01010550000e004000c49025000d00342e5034000d030601c2541110f0040a80c03503003100b41f41d44c841441106119070242c0701c4a003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 592940755 1250 592939505 592939519
    0x1f240207321810050d080f18100e0f0d1109070c020415090e060118020c070305010e0105100f14010e060705100515030303100e0603070801021303201e 66
    0x7032400084440c0b60040400e20b44040b950b081c0101c8011403aa1440580380541c2c2c003800c1003503107440313141d528040c18410031403845002a1203460000c003081c0c4c0c03540410001e050304038101d05c5210040d08844060366614010214010640f115141c070046000c4001e800004403003240c1e403031505001c1014001000d0100384110040e0281c0180c8a9201d203550014113021818070711801c105030030050b600c03a5649403240d9444a4018060b5955000c8850340c40d5a50b1040103998584141150f030502040e07a1019029518000e200000f030b01041d00124403519410501030710664540d442c044d804036a074050445400c0301d0100ca50003550107000740d4400030400800d29400e210040e51068039154081144011040d02e440a0128514840c2c81c86604424110007a50441c540b00594160301c0a00340304500440f0741101c04919141c500703102d00380150140000965403101c406218409054083c803040310342c00011040c00c60b0041d908140304090520040044621004000d580100002c44501d101e0b80a15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 592942005 1250 592940755 592940849
    0x120315230a1802071406060919060f031506170d030f090b1501020d0c0b0406240303090f0f1d040201180602010605040e0f0a0b1f240207 60
    0x140c08020240b20b441c0469015a41d520f25180c114900450400040680c0c0d000c0d10074415169110b058030355004081d08510418102e0070003540c2e02504030b030b6106040c1c0f680c280802009012807a191508a90075200b024004a5980c2111080103500340c098030080d900051020790b0030a2094000010704001200c01103034021454a0310b000e403e41c199044c604442030282c1348021035805000c07105c818442130501d5035240302d181d11a010208002040103280556a21a029081c1000c28100c0e1483c01840035601c506910f9140140120589002c0d002401c02481000648461400ba14034282c41159450828a0007d0302d54061140c0c0e000e0002c0f4103100315150f001c02c19460302c0ca0344100900260740081421842e180a00003110307284010f02d003598204164604c04a000081c4040d002c2e580203881d0601d075600c04a030258440d08101c0c0440744400d004d640024444641d00311040100c41e48640d40d140103094150980c4d543d00340e072107440d10188800c1c00056010114030384101c200200000c1440c6940 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 592943255 1250 592942005 592942019
    0x30a050a110f0702010305090601060c0b1803030711010b03120406080912160b0a090807021e060a0e0907020601060e100215010f033503060102010e010603120315230a 73
    0xb8100c40c040744101280450310009540c1d241c0107981d00040d125000d480b455040c110000d20220709000c01a00e8103145a01168a00d04000f0714641d1002049013070320b40300c0c01c012800800007840c03403c0c2c000c5258213003d07030000e41e840d000c81c5942c0d401100e000142e14003442c1500c1540d845400804100084c00740f50754038409107860000800c911500c4d00c005440700b454910b08004e10001c0600191142840c0c41e08010010b41c2a004481101d034042752142c00d102885000d131140d07000c90040c0542c2048c0049440c031241c64010a01d03d00340703030088800b07903480e0340d4500040365a0b40c001d02c100c400040e07c80c012128103042806840204000f1841030780c90024121f151030412403005c0c1d0000480ca140c0400400c148111442e10042114513510404980f4034056500c00e20084c00c4040c0f2080344d500000440e486a000f54001072040403920f0090143c59920300f001080c00a00e0324250700400d00b016180c00c3c000300c4c000c1d10141694241082c450003c1000c44040301d814080c0940c880e0444c076180c2c0045004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 592944505 1250 592943255 592943257
    0x3011b0201020a0909020c070b0913090b01030c240f020a1a06031207150f0f410c0706060323070f0303120905030d02070f0501050f010b030a050a11 65
    0x400640d0000350303031070030380203002095581c0039441110124811f100064030920041221000c03200345c98505138507a5007080002e01c005043c41280c03090281750010301020800301015650480380581880c10a1941e42c40d400b0240000c1c400c813600040c44050203110826019010031a01c107e00e52044410a00f0607585440d56002150204420402420100841442e042102d5284007a200101c18282a031940d55040300900d1000c08200881c2c40d44011607001c02190301001600c144010140303e10b0030000114021000100303038040100ba4178140d141e185002c4961000c40400d0103081090195030f4821f00e1380e0b0340d42c00c080000c0f98259150301000020649220b00340c5007001104001200e035035502d075059450042e03180c0c00640c00651030601040070980100c400420144040008115a41e07d86001410351040c2d009a08003a031020032504c00744a002e18401009500c1140200080d84a000d0b03011480e079001d204040b8000010000030300800300f180c01c05e81c6c0005401c4400314215005501094031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 592945755 1250 592944505 592944551
    0x5151302190b0c0304050f15030f09190605060f010503060f040e011805070f0801060303140a0c060c26061c06180f023109020105070501021809010906050904110301 72
    0x210f910115082c095031501090000c2c47c00402c8925404410650424240c41c0c00010046100e003448403000a0141700c00b400561010541c1d01401a0040c00324500303000101010342d40f45010700c0742800341c044030303501850441c0d010702d07002854130501200b00d808020161102c1460890255240c260403000300750b0320b15440326240d2080c809041014245a60a0050380050b406000c2c10f80c10400100042038028408102d501ca014114640e01e13501070f40c09031404100510014501c03403a080c028001990f01080144210410300c000b000051301002000040a009542807a480b50001805441180014440090592144002181846004171200a899110b40c2d003940d41c24880d01c400400c61820244000001765001d0780c190a610214100070488031010160300c520a43c2c03a00380106683c094001d9a1616601100030742d40d135060b050b1921250079a001006002d03003003002c004a0740c11210b0080c001079600140510310140d64a8403031040314103030320f001c0c40c0e055582c801d80c03103120178600c030440c01c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 592947005 1250 592945755 592945777
    0x18081e071509052e0e03070203100c0e1203030c071e03030504060b040c0c080a05132606010602031206061605060601300e030c060403030905151302190b 67
    0x68000160a0071800d080c440d40d0070301c101e12100b00d144a04c01894680b140504001440c001803c0f5070a07450072440c610881d60b01941c10f05c0b8152208680480030307040b91701c007003007196901205429141300b0303c04045944d41c20100aa041800007544410401d005407107507502400304600200c101607081356022034864003d50020f40c03510100010312403d13000d5040459019181003150000c1c0c500014403c01081100a089400004070821007600c10b9081d81e0040d0015140c03015625590260700b6078000d0300c031810303d000075004c2400100d2a08041410fa048884540180d8a407a20403080d009071460002d010a6000c8810b12000da00c1c10340700d071400052688240f00601041c28050005019103111910310344104008049100d00c480c041552100c40307202045004c2002c07400d00341b50394194021440d40c0051b61058004000a0540c15000b9004140c015003d4038140f80406410100c1c0400072241c503041c00801c41060001410701024007107900e01315850b1002100d84841e442c8109501c0500b22174 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 592948255 1250 592947005 592947011
    0x82503080703060b032518080a0b010f0305070b160c08030a030b06040f09020304080c060708100b090105091309081309110702092e090f18081e0715 65
    0x11001c540c00d482054040c0c10890242c5095103403607602c0155001603424000c84e01010300d00c0081d00d640c0a2190000c0d9040d40801c000403103a101c0356025a203a031300002c152011000c0c8000052040c12402c51542901d410401030240d0034200b10780b44805900c84c0040c6400c100c007a500b4100480c403800d03d082c010300703140c2015540c2c400b003d6000600f6a9203510485104a000700005c004441c66202c170079040f81c210301c0b80581c030307640c032428009401e0062000a11281c001d0310200503c450b40164500c0c814000300b01030050b00b6448481a401c280180888a804180200980c80c005c1ca440b607103411403c2140000450064519540e551081c0c1004000c91000c4c03004040605c00c0180703d01840c0e51066481140c41d060407001d400042122002904400340502500c044c0203c074014180100c0484000c40110703400c0d82d40d01c030031010050220150f070b02481c4d40f5000c00e90031031400410020841503000710ba107600303094000f0702c0305d0f40b60030740841d01c0007180c074040042e07000141016400f041e05000c246000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 592949505 1250 592948255 592948261
    0x807120213231f110a03020c03060f01032d1208180604020a03020913060603150e190611120a0c0e090f010b1b03070c091a0105040308250308 62
    0x940708000200c000402c50103009503524041d030300c60381e01a0340034000c41d425900b1409000030050310790810540c0001c046010f440480014540c00058208920b6000c2d02120500c0c0d864044400c50700c00c0a0100600d1440c03d00208005079003e2165070704080d00392481c60912025660740c2c0c010103048401d0605c04500704008200f200700e90b030b00e2804082d84041c0050f0071140742c02d900280d40c0d81c0f91400002ccc03041d803441e00800caa070099610740714415a4030039001c018994680c141240140c00551806aa42d402d00084c1c04276450041103950818002d0000306050380556503404000d011581c021701b860150038442a5602680508000d00038940010005050300e0b240800070260003c01c0382541c01400021b040c00000f2181690b00360440e50b40090742a250000401c1407451003c000340e40c0ea0152102007440c0c01401030b4500c40408036a0200c00410042c1c0074840c404584841e82d0040f00d0201d41c0c24002000400c0c10000100120481004d50a01c130142140f860104000304a4098000940000030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 592950755 1250 592949505 592949519
    0xb06090907020f19030215100e0405010203040605061c151b120501080d050d0209010e130e0105070e0d030305090a0c0b0408070506030606070f1a13170901020a030807120213 76
    0x200d0042440d441200c413107056450b14043c0d60740001c407201c466600300700000501c030780c6120048200a4620008d840c811070074141000c5002c5d4005481c183d07070345850704012079103d2500080c9211580e41008665280c000d16446420b0015580080e440718151a01c480c0c049641d1810300700000320101c1d441e284e80460241310140d00b00c44058000e900240c1c00302c84039030710340d542103030036200d80b004540009682d07808a40c00407582c25460f144450b81009901c00c500c0398001c4580c111680400e0140d000704170540c2d901c1000c417081000a1038454005950300184404203200390009a8000c3e0300504807140036010742e0b1030299202040c1c4c4911481680810148501c01d003e0085c00000d00040b03505500f0b40c100080000d90314482c0000052804001c0800e43c01080190056a01011140021800d591400d03240c50002c1581040b000c550301d0b590000000d034480b035030906072000140d042c0e009262810281ea410b40305000e018240c0002c1c080700c0f00c540c4805460500080150700000c649081c612842d02c86 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 592952005 1250 592950755 592950763
    0x1815040213060504150936140d0e0118030803060f030a0c0602030715140604051e0901020405030d081005210a030207090c05030412030c051c020301060801050d050703060b06090907020f 81
    0x4000301003031110320b0100c145498407000d01c0d0250b28100c504007c000000b80b0300031300c080d2030f0b8503032200f047d0065113104084035801101e4142c00705070a80761809001004108480742c001e05e17000c020718030581130021440c142800300d120215244043e007120800c3c185920303810451072541d80410b0040e40009544002c000c802000064580402c80d0180000d8141d06805541245c0040405004564920000303560b0080e034012260041012407008006040c1010b010b4085c0d4014058070b4001e1040301c0304207a58500c1040717843c2c49654910354603408075051408104414441410644c1c005890701921048040140400e03517400b8400c0d0003c10800b0700d440003180c10344451314040c3d0148002801004041101d80b1220360100000d8030f4000781040c5281d00c02d032114017488015005079074a01900d9101c0141355402141039450310b0304c413100f560b070b0303a0001c10550300116540104243c0001d03504000250403600b0100003008010030050610480202081c0b0b400001c58960380168040c2d460007080450501c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 592953255 1250 592952005 592952021
    0x1080601090b1e0d060b040e060703060b0a0e040b0102011118030709020705061807120507080f0304050a0303140405180601030614030705190806010303020618150402130605041509 79
    0x2551018200c600603412540c3d110141051500401c035422041041100c40d6100340030801e8010000c000c030700e400510655a80070700300e640b40042480c2903c007185504840042d00c5c0344c2800380e560a41071f000800d0603c0040c040100b1007505564032802090b4001c540c000c09480074601e015079407103c081d0120b0400d46000c405504c50100648100210408038401040b00b0754083c0000c0208030341200c0b910802864500a540240290302103003450a04000011561008440446088031500d0502c071002d10340f00e20803031141641c000c000020030400680504102c541e050904078103d4102656100070640b5412490300340c110303030b0380000108502d2b076805118182c081c192440ac1d1407420302d410800f10359540f080d030144510462000b8842c00c0110701216012010f0003040341a00c000f540d4a00c1c0195461009a0b020b1680e403a0002c8140406100090341000c078050b40802920940c0b01c2d90240300b0a11160707034045030603588038080421503844a000745612000004201ca0f601e901c1c08049008071f0700c1c40c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 592954505 1250 592953255 592953259
    0xc07061104030c060c1a09030c07170c150d1b12110d200c0304080706080f0a050703230118020f040b0c2a010e010f09062601080601090b 60
    0x30710041c008192001800300580b0722030b0500c0c003d400042d01301032000842200b40007100481260800036a400040702030903c003c159070865043d90f1b100e040c16002c0072000601c0d20340c1540074503c001c1c440d103020348805410028100003a803420000d0b80c41d000541c3e10810025143e0032224041e4400298041042d00110800017020003940c22041d001000c00e1240c0b440700340c0a562035a04041701b00d038000d002c400074010950921651110b00c2c401c0c0702d4494010b4801c0c1d1405025000000a400780920010b500c21009051044e6140e641c0c03550000090401420ba0f20405507240001c91144030307130940900c0e040071030104468866150000c10342601400443c00c1200c28011700050500c2c0314030100b0fa6050750152410107859209405d110781c079110315070324200003601d40d6040f4460303071135100d54440303201c0075081c1c0e14241d01c0c2c1080001034802c02c560318903038000a00c1008080100b988540b42000da690851205000d0b8228000b5400e0314504080c1c21a8010b40c0104d00108030004441c4600c9103030f1071007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 592955755 1250 592954505 592954507
    0x12130c080114150315010e040b0c0301081216080a02010f0c050703021507210506010f1b02150408030d0203220519110603010e090c01110a0f0f08030c070611 69
    0x144030300350b50040041c1000c100300907000640714140d03070244680e40904005002c0f03404d072503944041c1a15840810741b81950300d01108804100040080c4d42203905890900b002012a0040420380300c4041d44101031604040800482e2400080d1080e001040503122590011600707140c111460b6044481e44142101481400c200c0c1c000042e401096001070000c0c000c054070745d89ea40d844000c4d50000703000c02800308203003043c550300c100c91a00765000c43c2c0640700c281c0c4c850000c0010f030501500c00e14024086200c0880d4959005001440d01c1e0000250341c02d6440710311410300f03507980b04440c60750700800c8041155035000705c1002a80607014014401c4124020a8081c003003030280c032002d8440d02900e0342940f00e420000000014040742d0000e070500c842780989010f60b69a503a0200f0744c117080f0162050840d500a014020206610440801c1552400d002c0940001c40590f41c4065424051002c111460071480c81c2c10004503401c8006540f0451214a03102e07690200d500d8500120f40201c1e20714004190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 592957005 1250 592955755 592955771
    0x5010905010c0f060e0d0507050114040308040609050f0d091706040c0b0d02040f17390d062c0d0504090b04140a0209150f0a1412130c0801 61
    0xe8403602003200e00c1e0f00040e01140c0c0c1c40c250b0130070784040d1105182c41d0945106401c1c82c01003951740a0010100b00d4000c4008000103021060280b8500750140d901500040b12038020038007150455012240561041084034062039010080c103003803d251142d40008284a00c40421141c215804005c0240b01640080c00c1d90349032a51314404210ba09000e080c24120001c20650b41c5c0c28903d80c100c0303018007103503a03148004595072880d11a41e04403410000829006003100c44c50000c000a035000f0020840303880d00d0045448a1440c10540084500c4856101d0840701481c000b040300d0784580b0102c43e881c107210205129690310a40604d01282aa4150640c0032007503140b03d465009081d1410b0340e106000100c0c00456100000f4040c02e9030300131036a0703010148001c0c040c1991007507000700581601581d5030035803ca1811403490303030340c0035500c501d041014007003000041552182c0d140c0c444c07203241845a94113140503803000d902c0213442243c65004414112036031406002d48000420014040100203203e070380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 592958255 1250 592957005 592957007
    0x311070b030c070303020306030a080301030501051b1303080a171603050906090706031107050303090106060906020f03041202180703140c031611071d040c06080c040b090402130306050f010501090501 87
    0x4443d10801808059001c004101150707014010315490304d402c10407060b10f07561681811030082c68180c2e0342401d00d103415981244074890142c140d541d0b0040c86000360460b10b00d1916010246d50250302401c0c10010000036101d200d403804007070540500c03089000721150114a440103400c07658050030100256200300100410150005001829030b405481d002c104608070311380031111401850700080c000d0001100b0080b84eaa41580710038100d030700b1641c0b080912a90b4482c241d840e0012003520912a4008202c28868929282c0d90703061a148050700c202a0081c546890303041c92402591060300003901c2d0142506504892030f481d5420800e4801140c2c61414401c00f00c8014440300c2d8050001c0c4022181020049801804002c005101c0440c161800c00b00030b501c482e1005000701c038200d900e00b4000c07401080b100d01c0740106900c56040032441c0c5250504200c40da201c1600f10030301c00c1c0e600940804c400c0c3c0b4107803c1c0c4204080154402c82c0c6c01b181e07a0400e0410000e020005800c0035040103002c0d0300c108066 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 592959505 1250 592958255 592958257
    0xf05070617041103070e0a09110f0612090c0a03030503040606051e09071701060e030618030901110703210e0d0206091c0c0e160302040f1a12040311070b030c 69
    0x10391100c0064601500f260102c0d052000740e0380b10340300c10140312042101070301c3c868010402aa110307060440862000c201040b00c4c0300300c040007140d0400c0d010710040700341d451030b039050541058070442221400804800041c1500c03019400890003e5008010b1000700541030154002400b01202d01e0340500e0744585102d010721048000b858411100400032808044c0224072071120350203d848285019038441c0c002609616041c0c0105000b8810706002800a42500950014035505600a1460010200c00444041203080f89520301401030120003c0020000f170001082110034010500a000250b4001742c601450014514013810100380311303030300503550717401100c402507001c0b11010519108406214ac2600c5c3c2108c00400b0185042c40210f0161000381c0c106101c1c0c0000340c40540700400152088083c3d001c4c0e84555224502051400e01c0280311183c4100445a800640b407407c1903562203001070126070594040d400314030007920780d82d076660b401e1000c040548104040720789141040e01100d455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 592960755 1250 592959505 592959511
    0x927011b05090105070b1501020c0f0a17100c030606030b10090513020903030706090501050916030b06150d1506021f02030402061b010e010f1817160f05070617 70
    0x10880d0020310340c120b50b0f014200365034207a43c000030189000e19148451114601d070002d20107015200e8034080c41e039a868401c2d18451481c0001e0078010741c0501e0040040c0a440c080e445905040c041c2e034038608180040340c03050080c2c2210380d55001c280c1c00d14088000e01224001c07030515003d000b10403004104145c12130603140407106e040d1044034094800350010b2009010302c10303040b5414080042d81d5030030300160350031504815004000030002500e80c18038196440d41c0c0440b0050203032130000c0b02000803030000c01100c0e07072004010b00852014040404601c1c040c1d0300c4180c569172138a48d141d80f0421a00c0f030a500740c3e005084e50340000c095000c401c4410254110010a80001c03251300000001c04644451080c0c8081c103900072240115941d0886056010b0321092200e018550300c0c0641103100507015010703840140d10011807418007101e0035103d0010070f050410624404400030403801155980c00002810708a02808582a00f04018034040d8280080c507801030040003600520824819070f005034032a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 592962005 1250 592960755 592960757
    0x1209060819060906120c060801031208041a091605010311040b07020d0602120106031521020a03140f210f0706060503012c0105090d05090f0927011b 65
    0x180d00009440c00710241003107403c01007001c0d050400006000c03000014805805104000800c00301c1e0301c8401c121111802488041c02c07082c401d180303484802e80621241038000d409000d07040c095800145240300501c03400e84034507600da4090007041007501c500e45010406082e09207014400103080c00c142d401302c1d00490054152100380052142c003150b550540703070012036a000800b5500c0d0f0343c84010407181c2820034850b1102007810500034845c000303012000c1d1010b13265203200c4c001586003155203120010f102d00401700e1300f10010307000c084085110903001e0130744610700700000c000702418001d01c5414800c12054090f48140d20000c043c440701c61800070b5a0100c8130301c018698132941d490801d04e01601440e849150076510b02089407059541081030680d05410480d5880c03070005015030090b089501c22160403860303821010054020610a90045c40c0c400001401d4141d0000d81c0f000080586406591455860b002d400449820061306650307514605400300003040b1050303429000c9000504e20050303187c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 592963255 1250 592962005 592962031
    0x1501020706111e01050f1e010603052205030414010305010e0c070c09060e01090605090f0415020403080c0f0105070212090d150507020109020306011208190302040803070c0312090608 80
    0x4444420420803071100503010329500025403c109012402000240d4581c4048541c420000300d040c410500320302d00810040c40381e41c2c0d503a03203450b40440003883e01801240c20845c034507001c96201c986400301d010101d4020005180c1d5240380030a024400c2608a030801d05141c1000e00400900704607541c0035621010302030b9500da456600d803904c0a9040001c0e0811469640341c908080792004840c45000d069031881071301001072980710020029000000c840070101c0e400d03400002000982d0980c03106a000d015504003500f010745075558001c1e203801229000505070b005440a44800c0c4003402010381001150001e02902c91038064001500d10804809900800c0e62882c072004221755881a0916041c551200f0000740c2800301009001c0c0240b40780a81c8a842140008942c0d290600e4003544030a03480714156140010b9950800c5a452050864905050b402c1c00001032207201400100026440381c2c65131019603007140ba1540c0840d6814007550200542c01c0001c0c8105a0400100f43d049007242290b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 592964505 1250 592963255 592963277
    0x31b0904082101080601050108010501170a09030306150305041a040210030c050405090f0a060f14010c0206090315042006090d0f140a03020c1e010503090c09040f0302061501020706 79
    0x14110014000034a041d50302d803500001511100030a4442c141d134802da07142006640da5100440d4464881070340c0400d2000c41d000481c0b45034010350b024079036151083c140864282d03a9a44034030750078454002c01d000813076202e504010400ca01da07008010345603101d540e030001030b040c2030f00441c91300a059032014080c90756803207141d40800c0c05017003641c0080c80000d180c1a05884c3c41d0006001c6500706481d031402c414100140450400d0504034054151039101d00201109050f4000465001070841d41c166042442082070303000300e880034001c107482403103901d00d0701c1030a00b0f00b40351000401c02a45920b0140442c018018546907452000321801c1003000c07507000c50300410504000d011410044070040c400304104056540e024800f1404000860098090b102005184e50500105080c0728410030b0013101484255040b56000d03d0195130041c440c001102d6802c054540414001030701030b40c040d140100681400c40400d82d04101556110704051031490100c40c802001030750310b0545000714001d00081c00c102d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 592965755 1250 592964505 592964527
    0x3020712170307030f1a28030b070507031d030606012f1b03010b1c031101020f19030b09060f0f0904060e1e15060607081305031b090408 60
    0x40c0400310380328201007569070b0803c42800303001006407450160142e4140101802e03081000b8401e0642d400c409040b006600440c241d280c1c09501c254000c8000b110340103040403000c1422a40e00621682058991641d078649034140a440740d10301c4040600c41e0501d1015040558401149858011100382016443c1c400701c2206142d441c4a85518030540703c580501003002241e0004a141c11840c0c0c020141000403c40001d140c265034081d0040c075004046103041f80c980da0444441100d409010781782c10241a83c002445c9802d80c3e00041038807105440128622010a04994803406410385600b4200040102440401c01c20b14000b03000354452003a100c000c1e04941c1740c07010030180d0703040c00401e1a011850315203040b030000c101c5050400072610804c0c5c0424095407550701031140316070f1607200a01100c90355080c0303c12959801030070290400c0041c4000c40004120101502d95900240c0b1081109805c0c0000d252602e644000d118002c8480d064103255291a041440350700b25421040c160703500c1a401d51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 592967005 1250 592965755 592965773
    0x509010b280c020907020c1504260a021009063b041e020c0c010c030512070c0c08010e1002030c0a08060a0f08100e0a02010e0d02130f020a0201061203020712 69
    0x42d01035041403c4400708140c2030343c0031504c01c00c5200b0865581e1a01d8212007420001809140200600c103c10303010911291280c41d140300003c0290741003100c0180143d5404101d0380440a402d100118a02e2282401059000190302c001d5010030b880143d007000b648004802c4812003202111201c8540d00701c201059103c9410141c108001045400d98200d0709881140003507124071103e07001b5024003004001da03076105104a003040354050752041d050004580b00480c2c1614003400da44c0c14451000410400a0701c3c164140d00203049800000403001121080c06040494030702e644007059204201300304054a6180558030445014139110026a440e503001c42c60848494000540980f0002c0e00040e80081c00214444407080c03c2c9024002882500c031804d5440030307010b00c000d0210740110340041d0641000080807042e0760008004940691003603825000700c461043d00c90a00d46e0b00000c04d82001074090080000600e900e003d802c01410031620000c1d16595240244090010007911400a000301c004d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 592968255 1250 592967005 592967027
    0x8040c14010c0819120606230405180405240109090305041a091002060402130e1e01050106110c031b0d05030408010b04110909040b0a020f070c0509010b28 68
    0xe140340742d8500d03044c100d00405041a81d901e80028035101c00507500b503002ca004036030880780c031078407006000b0361105260162489070700c5042407002802e000028241d07503943c2c00526001c0301191514140d04003410040c2c10005c22006605040b80c601564000c14060600d5050440d0a09440040c1208140c90100c0b0300d8800c0742e204a03035000050315200407050b5440c1c000c01d058001140c090006080780f072000d0761103960440700a03510170541020b21008107515040484419080401e1f19110a0111404814411346000c003d00a80d51a401030210a07004906407810404141c000c05183c0304820019641d17940200d44e05c096905542604196516007109000941c1d5128065035215070719a10718034001c001c2103011600c02e9082c507400700c0c4c2072030042c411242e0841c1e0103090034569543d0742e11100a038840180840814650030406100400b08034009840200d02c148070380070f14a442d080070041c98403c1030b00880d039001c0041040c0e6074a0b4000001c1c421041c3d40c0ca4686841c1c00081a00a8070401c0a01c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 592969505 1250 592968255 592968263
    0x50a020a0b191b020703080a0302040305011812030605090a090606050a080d0806120d032708030f01090209090a0b0a05040501170601080f031c1b081608040c14010c 72
    0xd03509215507080401040c40c448420b20008201030010640020802049000b0400c00358008883c2400800c0d40709006221801503800c0c050318041d62039480608403018072040d0074004c040060b404c0c1c104605214089841c001d9450309104c41402d080c002483c00c40083c0c144106541c1c1c030200034040000030f4000d000102001003240f00c0c1c281e6100c00054a504452544000040128001130301c1c42c681900a0743d50700028000030000f0620048059000b07000c00f804412030000c2e14103c1c6070107502c1c0081c0e0783d90300e6403240c10030645904010310000021041070708031a07100350061081d001c40f074550320100341d400072600501040d0011140080f410102d0700c1d400c035580140c104000820510007507800c1c00380410421044a50b1686c1e601c045a4488058070f412280c1d42d0020000d20804243c0520528032001c000500081c00c40588500d0841c50b23440100c1080c0031036403010130014804800d15044055150500348144071b4030389030ba0f6025600c0c049000d00000029600d4002003680d2064070692515070740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 592970755 1250 592969505 592969523
    0x50a051905060f070c05010f05030408030702070906060201140f1e040c050d0b15011404180f0f090b0f0c090103020703020f2a1806040504021309030f090e060a06050a020a 75
    0x3100d0b03989a5260700400e13041e201d00e2002d03000050726501c2070400c200d034150b1030b0341d40506507115562014041c1d880900f01d03000314842c801001ca030040841c41100d0007420550000546524480c46211032a03000410525681c00801c040007060740c0d840c0c81494480d03145100140d110350700c03458100b80c141082d070049600040e4507a0000100140301c144280210003030361000c20904146001143c44125024120001c440b00307010801c84031480901398640e902c0c0c441008500d203280c3c0c0340003408540e1021440402c01c1d0721841c2c20702c04c0c024541c4000750407400d8407416440320f1500b032205e1125842101e510504050380001c5500601d0b10a000c000c89080240d0b003606c0d961101c21810705e070f043c031102d0070301030005c3d40b4015040305500e046401c0d00c4860314522140201540e0f24003c001c02410b00400681c1c101d4044055000141c2940c41604000c40c03094403132450004c070002000701070b0255604640b954030303a02c0041c00056541d0710750380700c203c941928007284d0f221041c400881c20700e001180001c1178007503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 592972005 1250 592970755 592970767
    0x1207032a0813050d170a090509042006160b10050904060603020f010509240c0601151b020d2004020c0a0b100302090c0c011e0207020102120301050a05190506 69
    0x40100002e24000c0c000d4121900101e440d00c040007020054020300034030680c550301c210426104c600d40600710002d81030030003c0c407503a40e41d03020885051044408950744980c620030404030320940704601540e0b10003610614200f5207503800036080e20031460006400f0080407400200c14540720500c3c1c0000e0680a0101e150500f03152800a002e40f1050004030300c1900305101a20243d48944261b5406600007410010b0b41c80c0c401400b00110740c1401814008035904004180d800b5400f00109070080c040318040b0304074441c10100084c103403210502d0ba00c0c2e880c01d52080b20b4015a898034858128940c000b40d100e003500e49040a00146080c2100000d80c01c82c0c000304251780314500c0412116403860280a000e850790340d9240d1030001308205800002e40c400300000114035900034500281c0340c4001c00790000600020312401403812803c004489000342c1e0b070002010411940e050000d1100d000020310304030305550403d00040c011050601070b80f801100303001c540960307052b144980c50004120250219076160 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 592973255 1250 592972005 592972013
    0x605030a02133b1314010603060c0809060919081606181a0c123301022406010e010314090109212a060501080706111207032a 55
    0xe01464440340800d40c3d07900443c80082d41e6041080e1151900c01505406910f551340c503c850801844484030710b540d80c40501100103903091250310303c3c001064440a059182c9a03810b1b07858000d0040030800260002120801a00101d03200c086960768043e80b0251903590f440e0400d40340c4882d0000103003c031400c0c0a584020384c3c03a0103d81208030b601840403580300c2c450425a80c102008241c507000805402001880c003c2c0186055158100c003041c42d6414068020407030442100401d1001161307400045207038160341d5a01084105001030740122000c103a9520a1140e040850004003640c1c148030000c000c442560f840f03a40042d2120001d50070700c4903182006e400640c000c1030361702d41c22184070359846007800307044d103c0d50014080c20300341d907507403035000d02c0c201c545018002d0100241341844982e0020090001d0030600455018110240040c00341c645040c0c0024401ca80c20100111070303801044040c120400c01c1c0c02140c00c13190305410304007041d01041404403429800358290880050240000b031b0200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 592974505 1250 592973255 592973309
    0x18020a06051c020316080702160308040e01050915121501030b010603150b030c0f0f160308060a12080f1c0c0e01030605061b0106050310090b07090605030a0213 70
    0x405a071424103052942c5110781c5a0883c8010744030790310f4004030342040f4618144034481c001d5121140e481660100c0302c0b80d8101000010f50b94004903010100860103206100300000d529004040c101e508001c2801d00702c400c0e0324440d0040d0503050142e90412800c107548681001401240101015041c19660f03503807c00700c1c1c03041c07401e00510000070b0407e202807144011215826068981010907940b4541390107150103103d0f44808100110044180030254103028904081d00f410305050501c0c481400952500a04028009091602c41c6030006000d01c40b02a9140c161050b0030ba122030f141e595207107a8802408280500e01085090b06a024102d6030780000d240c10107009041682c444070502900e0300c0040d41520410702609801c54400c3c081260f5403004103060141300c00700c902c00040e0481d00c60002c40d080000c0c0a80c10500540c503207c00e00b00f04490380380d540d9403004080c03a0810842d8203010000308284000782c007045400e50041003480c14401c0381e280c508000d1081d040880c0b2560301c20003c0d1151 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 592975755 1250 592974505 592974517
    0x1e1f05031803030708011512020f09030d110a020d152a0816031a1903030801090b090f070201021908070f021f020a050405030115050a080c01080a18020a0605 69
    0x428000d00c00e403025804800415640504150780350a072050b800c008604881683c1d80c0710710800c1000d281c2c0708d285040364510090903240c1d03a0912641c0d4401c100014189010203e901100030400000c0d01c00c1d17172865010501041c0680d045030300c07103207154050070901c001c500503980c080413143c60050b001c29003001c8400803070040c407141d5960f030310601480001a03440e13150131512040d0210f00c60004503030035403003540505481806680c0318031000b41035801054040942c00d030055068503039070b0002c3c0181904642050b0040124600c18899100c0d0400400c2680c031001d00b061040e1120600072036401c0b4000e405035000c2000c1a000707031250086161000b40602025901c00002c2200114181003051000c58800300e1801a0380303001c0c2c820126003003024029404044200d0420009000105c0d040d0350070b014030040c1c294241025210326040404101090f6441c0c0d01c005001d03030001e41c004543e6604076030398030f81c0404a442c0001c1c9a039101c000d5035115203071114000f5400038195030081103090708a405012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 592977005 1250 592975755 592975771
    0x106170609100212070c15050a0203070315080703120c0807030815090601080402061c05090d0e1002120d02042606090c030a12021608010609050a0b1e1f0503 69
    0x1800c401c840340502d040b4450f0100c0403846820500c0011a0700e8014002584001d20401c1d60741110030803403011000311340b4281c035044200d41d000000d0080480d0306002d41c030000b0200034a0300400514002c5c0c050303543c008902c001800040c2624112004c0d84c0204441c1c00150b4206414a0307944d402c0d0700d0700406404045429038008088183c4d035480e07a05006480921900c01a1200d01175030701c5a40070404580c1200c0041c144801c2030030800840c4490341d003e01e81c0039a4441008080d00300302507001400c08284103e034540204950041202401c1d800a4070080c10f201d5103c07820780c0e40c01c2d4071003400e001e442150480703516981d00f0340440318040b000c440d07514004000181074824649882c01301e180c07200316110600f989540701072900e00c08103440902d0f5880c04001d5004880728501800d038480006042c40d800f940c140e956880c400c1040a099000e8542d11403001703c810403d20b00010006400201c03c1004115541205010140284c0354128001508000140700701e500030313681d00c00204190710445201ea = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 592978255 1250 592977005 592977013
    0x1e0f0408070518060d11060f0703033903050405030412050d030605030d050403080319050106020307050d080613090c09020d020706060f05010806190b030705030403111b040e0106170609 81
    0x1c0c8501e2001c1c0030240070702c40017041007944521903194441400c510038905944514100140072080440e1030017072145900c00d0f100031030610f0060040801d07030a48896164100d05140ca007240311114002400a41c149181c100010702c2e45850410350700d0741c000c9401140e40d0440c0b400e0600180200012029241881ca83d0305000c03090b01c0e8414540c0b139060038410200410030a10080c00020f060101031944086028014000c40b814456100140c400a901140142c0c100280d120180001400308000098a5050005003070030b0101c04217410010215801e8081c82c0c2d611440780811161019850003800c5100c000c1d500c505420000200039800440110703040e80c901000020048c00040e1180304840c0141c550404558400c814420700d4141da045410b110030482e8008151290020301450140829650f015100d19162a01400c850514000360340d681d401808480f1000700c0110741401510340a1702d0101c0c0000440b0301b910b001d003489400a40003100080b207224407248000840c09d11449482c0122 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 592979505 1250 592978255 592978279
    0xf0609060117010b0d090209010605190804030f0e060d0c0f0306050301060e0109091a01061805040e06010323100903030b1014030402010905060a0305090c10051e0f04080705 76
    0x1542d4030b90814460003032030110240100070300c20401000e0170405200c54004030b1000c4070f070703030001d1171865090300140003141c1e01145411640d918145000750400c01418140030504042d200980038410040c1010104000b1190340c0060b502e848060701c44072251170f2000d21204281900181c1440400340103940041d162440010b0186014000c480844407101c951500a0b4200800385010f000c0090381135403440130800170303421411517020b1568001c3c0240d54031242c030500c058030712300d011003060307400184140d007420121010550f01140003030441c1e40c05600c1100000e142103500301c406c0340b41c0000694134019500221541c01c081d801c00c0200b40c0c4265130402440d440b500410a2401d44120b1000004000c00b0846c1c051080c110015500315005040a5041e5075444002400315400400004d001036210001d1001d0108200b204e100f80201c221040030001020040040c05400b40884650441c844d09101c0315648c4444812111222070700304c0541c1d5601e40700c0c111156501090b00c6080e001d0413449042c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 592980755 1250 592979505 592979507
    0x20060f031e13031e05130807030b06040c120f0b030a0302060f01060503070903030f0c021e13060b09040209040e1c0906090303050a0503090c0a080d170f060d0512030f06090601 77
    0x9000c00e280d89503c0b1304d400204180341c6280b034401d08009407001c0c0201001802c14199922040c01c000709440c1000344401030443ca468841c000000e080a4043d40c1002d050000d0640c00040104540e21042c1d8005105148000c01902904441602039014081c0d0742d201c400f459404a00a0700c240d4940013017401590780c60300100e80502c01210f003040000c1c03d003181400003074806d8035150300d05821850701c0250503407940c0010340c811100c1da100c1390000d507040c20b03041000e0500f8441d0000344090a071081043c1850301000413807502c504100036101d141d000880108a99680d480f09450413079100449401801c0e00e111001d41d480e101075032030b001c140300080c002019442041c424080c3c07a0305507100750600000d50b9059910750409454821540120100e12a0b1519600001002050b01500900310380960714006070450f0703040c906002030151f4000401035080c60846c003c079041030060f00c8018161003142829400c0c040c255107480303902e4000106102507540e0410145d40540320031102c40d0295110a80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 592982005 1250 592980755 592980781
    0x6030911030a170d0e0105190b01090e0105061e04060e03100506010c060e19051f180b04150504050c150c100b040b0d05070602010b0d20060f031e 64
    0x4008202d25905482c51810040f84400390010005040c404a100074a0f06441825900101c4046a0b1075006012100d03118100380691120f0440078240740c81683d0030000c520b003070142c050140c03602074000003d00514108440c0850520000c80a050710b49644e11502c0c01440b0500700c5480600c02d11960709080b04c250391501c6254010740c41610340485411341c0383e0b6284007401a8902e810194001c1c462002e044500c52448404042c2c41403018000308850b1105485481101c004900f1110f890900540c3d005c1018900500c207150f04020040000d69452030910031401c2072841501c9414106030520081140001d41045d405c1d600b00d80441d12012101002d04441c01740d400c3c1d116441e8040c50400f614400c0a0b4080141010050300100e009070340140414450030600a04403490303030154a080000315428402c3c03180810045400a4001c0070341d44030780408401903004070301c60b660b24400d42940355484204440f0352a100403a10b0b40ca0f0b242032000200c1c1e100e001a14000300c8240000003460f0000d40740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 592983255 1250 592982005 592982023
    0x1050f30061206060d08090316030c060e010c06110705031b100506030309040504031412040b0a05190507032d0b15070f0f0209010807090e0a0c0e150a0603091103 71
    0x20038560b135134501000004070440100b40c6049004100707601960310240100b07500494011072034032109241d807900244200e46644404100045a1201e0046a03403007212181248d4001c040450240580700c243c0d0958456444020918403000400303e070100c4139450000024660101510080d010070b1041409840c2c084a4455058008010341c2d1890300e45640155041030091a15000240d034545180d58190302c03505421012703c51010800081085510702c8a41c00741c40c022042c001410302c48006150320501d00c0320a2515600c500020743d00c1072203544001c05511030032180c03440a409002e0a005240112a40100d44500300310b107940950803c40c0313902180c583ea44a040349001c8094a6004041c035a115040b1942881072010b900544d60700c103031042c040e04490000c0c1c191035107810100b4080398840381c040c9916800c881600c1020444c550280307001c94240000c0740ca100d90b120701801c0c0c0b640c00c038030f40c0140d48501020f40120b5001e51540c00249a240b00b0b16140000c0300708881010380d561011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 592984505 1250 592983255 592983289
    0xc080f0c07180b090106120608010e031206040908030c07210302040519050f0f0409060f0501060f0903030203180f0d0b06010e1806150d0204031b050405070e01050f3006 74
    0x401c5000c0c403c10300e09240c10121f280010700c090f160500b032403d41d08041a420a250b102046040080f810150701e5500900101e408000607482a52445042d0100500f141184240480c03080240112a28400ba182e100480aa11071301501c8101500039045030044600446800701c050a03c207103031440a40580d6001030206440010f46020801c3d2214010f18450300a9142d1510f00c0010382a40100301524190800104540d07040c890020214503006c42c08104101d585102003020a4000c4100e4403684802c0e102405200100350110b814812103101641d084100c68170344605005450346c4003801810300740c1c3e503881d00c41203c00400000e46140b084404d94482d0400124a80740303414040100503940405015062072010010743d003c80e0130540c01a10406100d80b401150b0900901568000c1d2008480400050a10500c000c0001f14000509414410009041c100d00e030044001d40302d91180a107403010062250a060300c104841030b03c040c4950401c11008982980b406d018194040000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 592985611 1106 592984505 592984519
    0xc0c0d0803150102210304211205010f030309140414010b03010602010f050f0411060c030c1006060207180c0e1804030f0503160c080f0c07180b 63
    0x20140c506045400c5000454682c000f45d8207042d100910302c0b01d800313440c2d50b00c0d0315100550700c0480341c0f8519090600301001f82c1c0c090303200c04001010703109620b0038010740c0d0380e0711090702100120b404001c01103018024213005584800d440610003c034010b01c0810464000c0300408829442130304500d001c04030000042c0001602401250040e0048080411075407500941c1c48501410141008101225000342c62001d80e94620660700a821400d080e01d030b460001070907059562509800f00c041060804400048150012411070102d907421a41c0704440c001c2102000d004010180070041800130034010810b407034540c0d2070f4401c400031016001c0303103980c2030509001c2c081c40143c5810000b00b010800070095460711400007040345d000315003004807140c1820f240200351801001111448400d000c9208030440800095690441d0b48282a00d00b4081c030300807548003625450001a82c0002c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 592805755 592985611 := by
  have h0 := BRFrame.cov_init 592805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 592805755 ≤ n) (h2 : n < 592985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
