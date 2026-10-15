-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4458
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:40:57.645727+00:00
-- url     : https://prove2.me/submissions/735519d9-1e57-4ec6-bc83-f845581dfce2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 801618705 ≤ n < 801798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 801619955 1250 801618705 801618709
    0x80d320601030b01020c060702040b0105120903030108011d0a171b03030405520b03061206070e01030e0f010e0f010f11030f090c040203090307110d0c05060c1f0614 72
    0x3d10034441b02502890401c070a0307800300310241008048042c184401040149e41100032803158510035900f2000444d540c1d4540031110b4210380c0900039403500315006990b00f0070103c4010401c0740e41d0070b40128480c458800007010006040c850404e0490b5004c40e2180c60480c03031503005c8081c61046001d8001d07200c1100c003502c14040c0100401c20906000280e0b4142da100b0600000342c80820000c06141c099040c440400c440d2180c1a0301d0740002080400101c01c101c0f451600070300f104c1c0d0021070200600603508124001501d004a480340c3c0c5814982c0741e200c82d07119a07108219408950110000910441382d1906032140c0b84c03c45004e80c2040c40d400d2900402e07081025008550498800c044040c2c074580e01c0086000c648bd4000d4900318150050055406880d030711800910701408509018590312003852a12488100841110a000d11301d045010740200d045a00c2400840350161030b40382d900d1020945d440d04001040c000306580c00e006c560780f000d5800e000e074041020384144503011030301c0b110080d013 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 801621205 1250 801619955 801619963
    0x1a04022d1f17060303030f190501030606150201110412031e0c150516030c120c1107080f1b060c030d15060305060904110315040f0618080d320601030b0102 68
    0x81c3c0503415501c2000401c0c0720b070003071514042c0c0c481641c642c070700c8401540c1c003540e4003518001ea10503a88980c0b00d42080c00305190400085130748007000d000800461522204c401030502aa01c00c9038401070603041d54105040c0030310b842e40ca004132102c842106c441d0986501a100720f4000074107848801c1c520b901c02e0380c102200e104660040240c0c0c0000900006080310860143c88060f400d0010040000b400c1c403c124510b01901000c84066110104c1c0500c40180040c80e14256501440355948040712015031140080340c40041c014130410b0440c1652a01c0d00801d02a100e502441e4000e071000140b82d50f03000e801c0354403003206194854040d5814642d80d8008406075035046c0c030b4542d444041303400030034009810620440d2201d403028043e100300c21000310042d2108881181c0030780c0c40d460164800800c0012a01c502c4018a00b04001d00c1650b42803500c0e0180c1c24018461140710b20313942c801c030402c00e100c140c50071081000d007030006070400c000391501205010034044c0d800c1030102c6d04002c0780306401c0d80049 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 801622455 1250 801621205 801621211
    0x10507020c010c0b0411040207050307051c170c07020307170c0415080c130f060635010b071106030c1809070c0602091c0b041a04022d1f17 61
    0x21010304c002e500c4a49500710b0fa80e48128106600c564200229400a00180040d005640c01400500a01d4482c04841802604400b5403102000550001000e010359007a181c2038110551160b811f40300c06c2140301103842c0c101d6a4110b05208038404072202200000010160340e40c19042e80c0a01000300624190800205940580c204640000340b07130301142e0a0a000e02d0807a42c021001c0402c01d860225445c0c002c44a0300e40113000018820214042d01003880c21720b004400c0001c401038240d5500f50320030707907200044c103010b60789040b000082c00000307001c2c040361107446401000f0300c1c175940c07410001c1120520303a20070354651400c4000708420070780910740020140e1040b0550345400414003c40c0d680d0f00000d5100b802615440b908222064155034010221312110034801c81540700300c4c0c2440d040580d14000780c100c03600c558080f00404c100c01130300e07511040304400d5800811940308161128112103100d01e4050700342d801000001400a03004c1000821b101d1140c0c882d202c8424221080c40c41d102170005c21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 801623705 1250 801622455 801622463
    0x10c0512040201020a020418060509061003080f0409051003020429040b031207060518030301150f0e031609060e0103080711010504122001030e0604062309010507020c010c 75
    0x103110140100c0c0c403068100c1da100b8414815034110b00b01507400107080b5114500403500b00380141d1340c0b490400c80d0520400c0c4d08140d03000300030070046c40c003408056104d1545010060500b140030400310810800c0d031050350054002d260b024051490543d1070a0700b9400c0d1440b06921440c1000d211011000c00c00001032001031440303a041102901560500c0301401c05170707000582512035003014600450080e40034007c2c3c14400d01020032581007a1400303502001414900900940080004000000c0760708000c12900c1583c0c204108845030b030017002e03501510040310b0385030580110743d90b0151500045c8030f5582520b007000c00801041d80c403048d48070ec4640d800d00000700600002c121020109081100055050005141091a0603160003051403040c1d002842100d6090b2450401d5410032243e0311051104142841c003001a103400d92031169a915010340042d20166503800e00617202c010030070a0040022201881100e0360401182090007008202c641c0001406040300c0c0210b00d41c80b48652000e11504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 801624955 1250 801623705 801623707
    0x60c0c020901211e03020d0215060d0c03020d0f0b100501020c1203131203090506091807022112011212030c0203040315020c0709110403031202071a0103050c0102010c05 74
    0x1e00c46941a00c120400365907207603881d802c4203c00000c00200c0d502e02410061090760203421514a40a450201c044104509640001e015a000e640005800d141d0040040302c42a060350901d007030040f025601381c0c0004e50000382c445c2c0c403441401028209040c8151060460410f2551042c606032aa8243d50080b140140c00045880c1c0c150703e00100c00c04044404e6505607850840251a07180394214140d01240d171010680c4c020320185504000c18030010320084d68031718a440309000007e69503d08051000c500c4460345404a00214420041c00f1300017081c044081c0040c06204031000202c1e0003a8182d00002d980030030002c241c00100507210004c0039030022440c44803010500080e0f000e8150603200004512040c4400000300301c0d0302001c0d00740188802e80c0140d0b942c40840c19281400d407540c1080000500303017144082c40d00c03044821182141c0c5c2500d0174950340c506c440c0c2e2600191145010241400c1c4c020ba0f0408000005000d0300b80c100ca2194080b5190741d8030000040e0300380c82000a694002c940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 801626205 1250 801624955 801624959
    0x90f03072610060e070906030c0819091704050f100c030c050a05030a03091119061101060509040c0e0f0f01061d040504080a02010f090b0c091c0807060c0c020901 71
    0x5003501c20718039594141c0303082d03988002c0109511800c0f244141d01c20b015402440c2d0903c440c80743c10804600250107685010b001805a184e0050501d47c0f000e4642c1500380340315030700492100d5050340180c8080d42d111004003141c0755406222180b036045400340c1c070b00c40d80f01d4a448144a1505d84902030b4065000c0d140e6500c80c1e4500d444c26501200c0d00142510700f806a41c1031080090420f100620a02c0440d0300c0024400704642015a40c01c902069400c1c00307448041c1c110301381911008170324002c0f1038003480e04031843c1c40a042210701401c202e070b01c801c0d00000320100340010460460040e000b6102c21803031003050f981c0d9044003441d148406642c1c20120360a444011300540e031040420184034032030300301d0255240018401080c1145d404070381c16200c4480108030704d07440c02e60a01694058000c1c401c0b0602c000e00341901e68803813400000c1c0a00c403110381d00150070443e68507500b4a4449a5888160f040d00352441d509003070b00194044002110700c85c6c80c00030070900c2030340a4101d00010301d070003405d001910382c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 801627455 1250 801626205 801626249
    0x140c041a030108190203030f0301120605090c0a051002070b030a0f0c0206040c050d03091707030b01060c240b0d05012f0a030b040e03070c1401080115030b061e090f0307 74
    0x5038041402d98040c00108070b044423510100c80254000c041e044045408449282004011500058080d90480e00310340c40d07405041c0d40340010078050b00c4084542034010301000e10280d03d018400e51141c1424640402007119650031030f4803150300c030f081e4058240002c0300c0b40c01c400c98032400c040360020103003100900180440d0034841d01d280a440d00c2800c01280c1d50344c079020507101c2000c0c18100c4440580c02410244100b0000911450061840d8240704401d07001903910351b032040a06e00c404d4214848100e03d2401241040d42001005000103001031102c038409060a9010700340e20500d03000d80703000105c00c2e6446081c040c403420507000c040340d0280341804804003013180034100d03070b041642d0b01c1905c440d0041480c64092004001d01c5100d4841504170b0342c0780c080554102480b17170120741d0500a61700010841000e154442000000c40307840c0002d4040f20010000340305003d0031046481e444c10a074030300074041410100030f04014400b1100c0d0034a0160090801d43c3e284100e0040c46850061409840044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 801628705 1250 801627455 801627493
    0xd051201030f0807200a0503010203011401050309120f0a02010c020a0809090403120f020d05060603060307061b120512090f0709090c0306110910090518060103140c041a030108 77
    0x1441c8a0400a8076010f0a519403003071081080041c49001500c1c401740351614504240381038024041a03009504541c034190307070400b845071400d00c56030503c0740000002d0310100e01400103044da00c00d00100a44c503000c01c0c045041030368111140901c0036620708105215902d00009a54411940c4140391510b0300301e190060000841000d0b00840c20300140d60084480040309028010002c4070400005031580f07094054074041d00c90152480307024200c10003d020058402164240544820381085845200049480044020345107005002e0105444840064541c000c0c000c040b440010100c010040d1907801c100c3d5102c56152200d091a68050032007040f64121035007040701202e008207000b14040b44d59456801c1601c81c0c01c11b24442c04500003c07035021070f1030b02032244004c01101e441c080c9401e900340b40104024070030b05044082d00080d8003002071190380c0720360000700c006101440701f5102810712102e00e810700d410078010309401301b2003500d81107215211401a203040340e2962004051900329100b0240032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 801629955 1250 801628705 801628733
    0x91501030204091401090303020918040c09050c0409020c0105070921030e01110106120203071a04030201031e020a030e071712030403090b0408060f13230f19050d05120103 75
    0x7860711000c5213284006020310400303502e980281c4000d130756100300d0410440502041d80040f10300c07841c581c0a000114a011000600707072074201c0c42c00515500e92401d689002d00a603804140c880d0f00014001030010707419008107010b03026603112805016200e500d00c00003404940200fa644e0030503c10007001180c401c41c40c0350b00303405060600c01c1080f03100301c030f24a0a6985503000780c0c0255041c1c18959045003030410003031004145d00051805211a80041c2144521881c40701904140e1100581420140c80c00d0f414040707403a20342421540c031940080090040e14000804072510b0040000c006500b880c0038100b89020920540503102201c4009001f422981000c0d100741c042100c648408106441844010300142c54070600801c110b1400c00c0c0e90002081004004c180032804c14018040040c520559608020035510002d4030308048482c0c4181c03400c8044401c0541c14403403817582c941420b840c04980c125283c007900642d85001c0450b02c0540c0e41d4810140e0601c480c2144000400110364011840b030b603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 801631205 1250 801629955 801629963
    0xd0f0c121212061503090b0c0c120901030213090f0c1b0303090804031703162c010e19260c09070201020c0d0e01020c0312030a02070804080f0c010809150103020409 72
    0x520584c0703c14030f0503184c1c0c84104103040882d694035440800e000802413529030100c640f407550b600d448000d540058884803242d25549505002003084407a40e80071740c0541d003404414140480d8603036582c0d010715000d4501c00c10303030080540c600040e200216210300840350100601419044004e0181c0d0f900b100103103d0742c1400d5412400a000204c0003030440c0050080395410308402c1d80d100e007014105c074461305003190900d40a0042d02108100c140d44505202411900c2c00c0b4144481b108000300141c400101008440d680070301c54050b9a995102c0c2d45442c04180c0303501d0340c1034005022003104a4118a910844441c0303042e44001482e41f81803410402c4558056440d04c00035003051603001d0810310b044e003a032034100049202444010350550b8104100803030280c084000f4060090170b141c040d412480040d10800501744c000442105210103d0100c030014002d02e000c03151000308203907240d600c0305803c1c0101ea0018405c0e901003080d03a80006080000542e40e8800261035034a1035080000420728010304503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 801632455 1250 801631205 801631211
    0x901060e13020f0319021908060a0c05070c0905100605041d040f080c150601020604170a03060305030c0102040e100b030a0c0c023312040f02040207020d0f0c121212 72
    0x1030159201401269125805c2c02540582c400d510b2040101c1034540582c00c8242d030740c11000400c802400055a55000564507a001410200342c0c04200e41c0e0b4490448080c09500411800180848603580494420300d102c0c2840080d00d51034000444a1740305620452100c1c46020301c0b1850000c41c50000d29402620464481d5080071407a41c0d0307509141c200c1c001c10282c42d040601c04444444422080a910072424405861945080e076511020084d00340d003c6446a40003081d0003520078020341c0424080d5400c04116600ea110441e50580030354014026060380d034041c075012560307111b442e0030403c003560b01c0484035030b04580c3c80300020001464071104050400070516034690140e210402c0740241840360341c1740c0901c040d814010003503240ba820210540c44040408c10403a1f9034290f40310540d0401c0d409241091001e10500000c0c020740a10000a5402552620041c04014040d0608400988104030300851319985280b02b2480c10b0340d841c0c0c00340c030300b600c00c0400854081c400c18440004011080c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 801633705 1250 801632455 801632479
    0x5071205070f05100f0207030206151c0c051c051203060406240206180a0201110106080111030108100b0a060818060108010b04151203050a09080102071a0901060e1302 73
    0x11242440c2c462010340d000c1c2c020890310425803003103004007105201000415494042d040ea0000d50307540008081313800fa42c24280c540341c040c0e40c03038808905450304601004801e2041c541004031580250740311f1544074088140c1480140c40c1086100b486598218001d8812a000c3e1341c18800c0c03a5000a28503680542d80e000046801c995640c0f0140c0b4076000c000d500d9070743d00c540c880c020f480c0180140c07000e40c007000d1140201032802800a14558099420f00e060a104600c801e0400d02503c0c80750410b14095082980504140704034078080d5040318a043c04031148c034803113101e0b02000c940c1c0540d103c0c2c0d0801040b4409210f214001c03452030703410107140a0a0342340d4030424507499051107002c0e0410302c40c1d41d45074040d03050b05142c40e01507881c4824034501200141454030800c0070240940c02c030024244840402c40c40d400303d001ea40039000030f1144a0096545510918100d01100c1c0c000384010602c03c441c80205645d03c0d0148505c10540d04034069040070740e240da0032502031030302c05084100d07800895000d003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 801634955 1250 801633705 801633713
    0x30b0c04080d030221090c01120902090106030e10110a0f1b1b0b120a090c0305011416050307020c040b040b0a030b1b160b04060902180906010b0a0507120507 69
    0x4452404030890307a00507140d011103000424076900d0b100d101c0500414a0043c41131b006400300310240a0402400c0150401d140c003c2400098403501c00060f6210f449030b400041c0c1590103070041e903502c0701c9a50680e9218464103001c2012203099a16000450700188444500c09004148030039900401d41854030390031107021301c004140441d0000444047c0c1140040200032410800c642d0081c0c0041d01685040c1083c1417112090104000d011002141c0c41c0d03540802400300a100040146410000034400000c00d442201c1054400b075070410000c0e002501d104d0185c80c440e005582c01581903a01901c10f6182003c00c00014040134410300303034020b0792601e4282c00c60f40c03154841002140f04482417126032900a8240104051020b80c515482c20b0400030392004481c0c243c14141c0c01c40d0b1003081c0003803580351317410014010401801c00035084041700c59001108420380760f4480c4540c80c8042295103680c0c0350101080c15000341c139552804150203100103000140300018030f4003040b4681c2350a604041c1c00740c807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 801636205 1250 801634955 801634963
    0x703021b0d08071101081302030319110a0501140c03040f170c330603030f0706060f030b0906010f060c143a050702210705101d0901080304030b0c0408 66
    0x5021100c005043c403910b0f500b0358210046651008440e00c1507100850710b500460340324030421081c000c1011558810500d6940200203a0700c1540904cc05c40300c4c01052450001d0080c041c109200d03402c0302c080000100301501e00411640f00f680d00c0303442551034001c21303038511821140500504500f5102405501c1090384100040903885116403070503a0814007030032141c80c4642032000c002e602040620104002d0b900d0000c200c5010108036041c240d510f00d22420503900610b42034010b505c0c0b000c0458000404c3c404211aa02d00621400054400c3c83c1d9803581c6104181005118442c0450007410321200800c1861180ea0300300212032054503c0c803801c00007245012020559000c80000301c40582d08042c848903440c260f0404010304100d89400d045800044ca00e40d48000c40028a003c0c124007a411107406004410040070013074407400c01009a004050040400c1d0340c0d43c260f5001000e00503030031900c5c00405090403201480080d51501d070554458200f003100c0107010340c145000810000070b00c0c280401c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 801637455 1250 801636205 801636217
    0x509060f063106260c03040f1209030204050a15060507020f120336120109020409150f0204050603070e031501120b07080721060902041202030c060703021b0d08 70
    0x4080c1c20b429410710b5000b6140c102c90000c490401003210f03c1895076500c1010200350030030406000f00c0d4603039440346041d0100009108000f0501050306025001c107a4100380c505003038030300c02c84040c09580cbd5901060000c80e070710360326800706100d0510010042c250182c002000800c0c000b500c624680c0707240401188060300841041c001c0c40d4000a4038a80c88150365a01c81d41d654040000030000d210504068070782180840e03c1d45210309200c2861b61103042c025884882010b9014106001412082c00c01807000705d011714001c0209800c0c1204446500c0c0c0d180300b15429144020426070858503903002c200c0f420307103008564a82510401803e2403492540780e0240e40245000c6041e01c152300b0042c5407401c40c4800190030ba0b418400c0741c4041c030003e00c0d0004030b000035600766000768018047d403011440024024940c0102c041c2c40c40020042040c010a0f9a40160305000b541250496804c590920030940710311000500142c1040c00450244a40300d2241c41c0d84881c000c04459134900c140e200c2c80155403100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 801638705 1250 801637455 801637537
    0x9040f0e0d030e1603020906010909050a0603020307050d020a17071a0d14091e0102090604090e011107031205040804030b1509010e16030b12070b030708010509060f06 73
    0x7814212507850307141c0950f8000240850280c01c0210540e100c0c6411810140002071040040a000554036446403910700010501c221091001d400d00c0c7c10200c1c010b000070b020590090045803400300e41c81c10110142031281c2d034040e2600b5100381c940101c130103280d45a401e0004045c0501c0c0030004100c54020841c80c80d0003800351085644a0012981008480f03d03051141030203000e082c10401614000b0449515140d10a6031000030850140e450300e00911a80b8060fa80c080000320340442d81e030069511160360907401c20002c100300c0b00a0110354000c5d015142c0002d0000b084080000c1010001c0d42060303801a11901d08582003607201d44c0c03460110740c0110303400311804600309018056450600c071400c1c01401250840e0400c1e0400400201d420110001d940090545450f041035054a503103a03440e002c1148607040e00c22480e103840800c4803a5000f51000c1d800290007000202d010302d441d2032264000e0500034528030141d00d491080c8032583d00321400e00701c0f500e020310161a80c09181d00d0801c140c0c82000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 801639955 1250 801638705 801638713
    0x51b0f09030a03170a0b090c13081b130513120c06020403031710080303062707021f020c0c01080c09040e0d11011a091003050a1b0803070b0103030509040f0e 69
    0x2022400311408a0040c0303400c0e901406c0070018030503070300d03000381e800c1c8c0004981c0c020b242d80e084031001c11b81d1030b01b441d43c0c0082154802c074000c500010512203140c2100d49011140380d00300b4a000e4100320251001654148138101c080000e200010301c5041c0a000342e90824100322424640c44e0303c41c4c4c803c0341c00c194415000300b44050025401c3e94107803525a988010800d54a03000369003800c000d02c0d83c03400010f10f4103004109440c60b851461444861503404003c909a9143c076034507282100a41303c0196489444c048041c1072000030300150340e4000c0c1c4401811510083c4aa813076000011600c4500107018811940410880350b400c07515240a4900c1d921400c41c010909620030900c0208441000d01c020031700d0340d242030201d01c04c4900800740040304030011209002103840341c450800350300c0250f84c0000c005100e1085aa010080c1c4d0116440000c45110354480d201c0b40e41d20403050700c0303100398000140600c540200500000740184003a191902014200041000d40150440101c85c035130b2103810b0680c0c1c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 801641205 1250 801639955 801639977
    0x250306060f020d1d0d140a05010e07060806100504051c0c05041104030609050c030a0326041a2203020304030b01091401062303010905040b0a051b0f09030a03 69
    0x14000c01c4215071800c09100806182400e003200074009444107051034440309201e0340e560b07182d58402c040c80c0c030070a402450300e21080546400660341c4110300b050460329542405071441e041c600108e600c404850103070700c5074000d50b40d46100300032013145034009603000e0241c1800041141d45881c0520450f00200650031501c06070395003070011f41c00c512540580d201d00d09204804200c845040251011254404000710f0306211519180713052a654a002580601c01c5108020506510111030004403005a001c00c80c540c0e159155119045400c079400340080c661035005030100b010b0402c3c1c0c00d0740034003401c00c0c0034002d41c3e92040c05e1014944502e41940181d1000c202402440758510155005014440302040f0700703480e94017404d4010700305118005c10300c1111003204042c4807210402103800582841e00765513035a1140030040042106483c192400444a03000034098155445414051a0717040c080c06170705901d4a5042c40a5030040064400d41ca00510405000d6101040548542d0b44a42c1711000e1440e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 801642455 1250 801641205 801641207
    0x503120109020c0c010e0d08030c1c020a05090d1103030f130b180d060b04020415030c1715120717100207030f0f0302090d0c0810090210050325030606 66
    0x9901a0004600d103841044801504640050082d1080c0700c2030800c2c0000103a03550004c1d00c910b05948024100c1d604c000700704050032003000f00a20260030a85050b480801c01245424200e0240300701c95004550708002000603498150262485c903803184180c0904181644e01190541e081380144d070f15003120108450448414102001001e0b0540000c2942416401801d40e07009030002c913082070107640041c0c0301200f84482034100762805000078005540e40c683c1e4128414444070060f003070f10002840d01d142c41401604c0703802e880900703102000303041d20103490350216a401e20188642c5154000f514060a01540344140007240c0105200c1000103d071400324407100c2d0a00942c4180c1006480c07040000b10002a00000c07800f960341018079001684c0382542e0001c3e070003840ba1b48034845c0e02910f50503c0004000200070154142c2d011402959400c1807241c01030019030301070000083d4403200780412141c4491281010f5503202110082d00e9424800c46e086000920500501000000780c03242800c3c0025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 801643705 1250 801642455 801642487
    0x304111f0806120c06031b0d0c050405090a59150c18040605030f010c020d05160807020f090106020607020715080619090c080118022a0a06090503 64
    0xf00e40c4103001d800010000800100c151100a05194030100e40700000c5507581c0104060382c004071314100040001c0500080c0113412904144141c074131a1a1040020701c81744981d002d8207215a109025a00c1101040082240c6074403030741c2c942d81044c403c604414545480c803650380000380301c0700d5000c402d600d0780710010445c00d00440c03420711038002e201c1406000c240c41c0c1c40b00c1164403203904000c00518518090002501410722607100e0b40e4144500f140980c4100c1041d40074101462a5030211010b0011448081d071782806864034905001444603407000109080100801182e4070003007080032160103a030009205c849080e0401340c01607000b103040202064040108002178010300310614280ca0500c60000e00ac0ca5004040c5809411250310300c229240b14200c04502400c07000d94203110f42c00c84090024141002442810340498030940a9100c5a10364070844003118401c105602c0c07104c01c1c2504800310820a20700d4031580c0e21621181c50041502c074410700e08140e2164001d1503981190410104803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 801644955 1250 801643705 801643729
    0x1a09030703050a03050405190803101e0311031014070806061201030f151109190f0320041a010f090f050118030b01150906020f030304111f0806 63
    0x599004205420200c0d4201083e10b00311141c40c507010078165514500f0904048002e4001703007a0b194000e07804001c1152004c05184a80700c029084440b0301da0340c0142408200c0340f22110083c007140301c0720030700c0030038907080c000311010a011b0116500e400600d850b010450700a4200c00902d2040032041c060441d6000c43d1480d00b0182c111445820040b04d00135043c907448042c80700410070010044441c0411a8481484485140b060010810420b070b4141d101d41e29400001940c0c0f1601d40d4034049404001c00780030003020349016088650255080d1b80e2803401540721041c28000240310003654107030683d540e00030078540e0760880814800070303043d02d03001511051540a0410500088840c00c1c840440881344200c102d6109180054a1500f500400783c0c082c7c04a40003e0070454000001081c01d084445109515100d646d0b5803682c05903030380000300c0c0c41c1c100741a03440182c0d8101300003050200f1500d008540004000400740400030210310550500640c11292040220301020100f00740c03071400701120b0032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 801646205 1250 801644955 801644971
    0x7050c030f070e0f04050a1704060e010219080f0c0111180103050f0a0c0507020603090f16031e0618030c021e0a0b0a0309053a050d110c0102071a 64
    0x70b00d5400c0500a0300300100090103681d000c4408000581800340c204005169690803072400121410000c801c80d81682c8030b4001d56011461700b81b2030041e5540300103400c0200c494041e00340600400503588081c00c0c2d03400820b01c65400c1d401403000c2e10100c1000e06c180d003408843e8814080e5603860281020042030059460281803510301010884011202c60f051030b0f004410103800a01c18001c144295454000c5400c01f9401070300c0402046090000000c000900d2003040302103500040010b1408a001515800010b000019468240403011007010000c05130320b128000200301d9001c0740c2504081101a1034042e000529110b031000150306000740120301183c08010701061442e81130740490755601280c4201100b4100000300c000c440c034420790001240a6004045d00d12414619403984541e0b1051f039892120b402c000281942c000209039001d405070f01d80340c0c0701c02d405d02c0c491150381ca00800c0482002d40020604200c00b2071444c4c0284000e0075558410410b00e00c031504c4101c0300c1e00711440014180d907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 801647455 1250 801646205 801646213
    0x70807090603203601050906031b030307080c010b1311070b0c1911060906060d03110f07090e070b030f06210a0b16080f130305040b07050c030f 63
    0x4000f0400d90035030828401c0d041d801d41004220204046180d68598404240d8a0001e032000011130010403210303050724980c04021049a6629070701008030041c4245e5849915611203034441303c1400c500c1d104070403441001800d417800e200e9251110b02465022030620001a5990703220036070702c0c0c544200e8100c90a80104030810401d510008190110310466001409202003034000803504500e0000b121031010040003d03400d010b0310154043d1140d84070900e0340c04907010f00c00005001280c0015581c0c86607800606500c0c4007000c0380c0703041d07401070340090000216014002000701615000c01c60000180001d400c0021005131011209091114a8022460b2a0002c106100c03140d840c04014542042d002c45409100041c0128070452030141b03201c0b1b1900360f0099020400c240b01900c000244980340400500300180c0c851a0125608503085030410890300008020503015003020282c1c50307001384a801c09030314254880c00c450311940c00c140d404480903880004034503d142414080c911019020030010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 801648705 1250 801647455 801647459
    0x29121303110c0109140f060703080708180c04050606190f0f0503240328020f0409020a0303030c0e03072402031207050f0909071d030a020f060c1c020708070906 70
    0x1c14681117441040641c01c1c1381c0c1c0142101340d072904420783c0d0104004000eaa500d00c5946405404c0e10421250807020072a010f0000d5100c40d84c4049815590a00c40080c03c5090b41c554100002804080c01e0790750000780c00e1000b10801440611189900901d58540240310054801c0051411031034080a008210081c018000c10902c141d01003206c0d000c4112203084d91020000200c1e03c0c00c081159400c150045142c5044410783d0102a21480c182c02075410301c2000109400340016a41d4103140250850348100080010900c82e40c00320000c0c000918105000442410010340341a410790004540c095a001e110800c5084042c4841d40c0d210040c009181060448064241349540c014090000c2c050001a01505580404104c48064100130a662403e060400c03009048101d08040a5030f006c07a0112082d14078030b0002982c95641e0340c000d150f003844445580c01c3c01460b4001e400510b040340b08059507542c0075000300e041c60150085981c0108002032624281500e80060b9900c01c140c107514118003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 801649955 1250 801648705 801648707
    0xc050d082119090b0f04080c030a080115050708160c0504020c1014060a060c170d0c1218030c060207060207050a030f0c110405150306090c01081029121303110c01 71
    0x4c0990098024526060315034582c00c0035a01481080c100c1c2d607440c000042e00c02c0f006d5800c4240070781652544180c4016400e904107050b511441001c0e006020751b1342c10f00c10242034856504019165034803805c22034160583d6440420140d030404c02000c48150011340780c40d04044401d106400e031078a001e0070400060b00302800441c1a551301c0340180010420300011090902000382d10955070b240e80c1c01e190a69034922090346c24000c041103051038001851140b070544910040c1d0148105280c026601e03440c40e104e00ba50156800364843e441210219001d104110104440344060140703a0300a20240131181100c0c507005081551400034401030008540417100400d24034100241c40000030313140040c182d19050418031003a408032a110354103200700010011281804a981b80c1a8102a22805c2140d00c2d91145a8074007501030003108504445c0e03512000d44c00001d4200029907100d06901c2502e0240000c512400120701100c5004011850041c00c4042642c0064151846912000a4030a101e01000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 801651205 1250 801649955 801649973
    0x7121106040f0513090b0f040b0615030a180f0f21120209030a0606170106060527010c05030a05040f0603020c06360f12070c050d08211909 61
    0x58540900030300d13551296001907a40c880700605400441c0c803040b61600204042411b00215000c803034000c401408650380381480d09042032001d004030903060459450209241c01090340c2c1706508046684010001c4c045a10189007140302805406202180703062811705040c0301960007107080a41c0f0304c031301140765001e034004c090030b00c0a210f07440c0159a80030154000313882c095031000c01030105407a24500060140006c1c0c2c40f4880354021700002c0c0841c0b03035100030076119070203081c020f035442200751f4403840e03141107604204440d041414108850110307143c0d00c41d9481d50700581e07080000708070f0009061000c04904040000108080e24089d490460125421522140042e11165105141d18464080800122180d1015807842100d480070411460012640c902e0038030300308045401000002c50031604020111006950001c0031880d050740703040d050000400c1c54031030980d1105000d00c89100040d800300c0b980b440401c0e046100120034200601000181081900c10111541c03401e1000f20001d10001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 801652455 1250 801651205 801651209
    0x1515090b0403030c14100b0f0d021f0320090f0904051905010605120a0c050a030c0312020c1c0309090c1407150207080a09050312040b1b07121106040f 66
    0x442c112114601602d05044c150b034942866904901a4071181000090687e100c0002000121150700b55920702c0000d00103494140c1402075080302040a03c0070806401107902000d100f104d03e800913200e00e8030310040c6084c0380a201c4d05007040b500016010010300d88100c9540401c4001c81e01041035050030754a80390394403660400c0c41c260400104004082c04801e510640042c6000b80c05040303c1c00c40900d04607103d001c60710084500340c8041001142e81d08000400030700f60781d4040c94000602e030550326003d04040d45406d02c6011403068250300b0341d0315192040e00030b030000102c0752601c58034141c0c0c2c0340140c6814044d800c410340007442c0821070b4520030750000c2c43d1050014840102c540e41e1025003894940a07010710b140c1d5a4190000603030404010184004190403c0a6500d00d40c01640354000c06882c0c0c500c4c85c4201c405103c1c180414401b0742e000030002c0c003501012031011800c042480314803070708040003075106150094007010803a0510690302c0210300302e04400c031511490325041030700303085105207030b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 801653705 1250 801652455 801652457
    0x6031e10181805030409090309120201022e0c050c06070806010206150f030105041119030803061e03100204060306060905030706030e03070f12090e04111e041515090b040303 76
    0x1d4100a410102e100111040c09034019013030302c1d0b9607601d8945100c080e054501044002610381a00081c0d901c110b02e4480d0744865050f40904805407042d4802c0070000314582030801080494801101800d40794801c2c071105407016151940c4032002600820304004c401000482807110721070801c2011f03030740403980f103a000d1541c04540b680c841801c0c000ca40b014910302c0105ea059071800e41072206100580d645a050f044040380c26071006500b042210707862244a2100400514041c0081110303843d005400300b51040000040d62084050714002a00d0324200b200240d005a5000800f070114540c140180d401414950919603070b1a40b8100c04260703181d41d1480350408055844240c20301140040c022140c2158018048140102c3c0b00d0802140346502ca40444c0e000c10116000082c1c00e00c0c06141c0c040c0303c0c0c1d4202d01030a1800c050b220a21400310f000034003c00380304c2c0c2c245100034003e50300d42c864113005005241e000385c102410420145c5060382c0c070f18a400144520b080c1c0c10011003401d40c0454007941d40c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 801654955 1250 801653705 801653711
    0x3020c0f190b0f0d060f0812070b0705030a09021f091703070212150705090f101b0611160203160b030127060306020c070b090a050d020f06031e1018 65
    0x20108034110740d40100c05007a011320b4241100054004044e80c6948151100c190070f5807075000f003101e0103107014818058020320354021000000e08090045c006594044920000400e00003585e900044103d600d100c2c03001c55a1f9410012050324aa0100d810b1000d0700c8002110004030103040401650f901484a000303202d00c031011010000501c081c0103034400340981140095040c100164040d00315000045414040c81c00c8103080c0c042032500c0698030643e5101c83d11501c1d0008640b0640010030099080140d40e0541c0f640c60100e1086441ea00906006030f0003d02d4140c0145076104041c00e140d04031040d40c14201454000340440c6016104480c111186881c0c8003405507001c640f85d00d900784135a0040c16070646400c07000814481c41d5002003c0300038804099540c403c2c2c980710070b60750340e0007000340c46130708002d40700740034070140c00d19030042c96030b0b03034001080034501c00b8480c00020b02070b620803503008200381101100420065035456282d80c00207580c0c0901000b1505101c00841c4c220a10034090f820203403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 801656205 1250 801654955 801654967
    0x906020d1a1813020a03290c0403140f24060603040221010b090f160309050c040c1404030c1a03072a021305011a07020a03030e1c03020c0f190b 63
    0x4a500d41c428032483e4040c1c48030400d10f69901f8210a42804e400b038400195590b201401c1d00c00d2000e91005225441c000b00700c900341402c40d00c80000260a40a040f0403a00c00e54a00801718401002030700000003c102010011003a0782104544412020700524081e20b4140180001603807200c0b0700c1c180e83d11201030340c80848491211868054070700c202c0d84a0b04008c0c41800d00901c0c0000d40340d0390b4031a03411f0501c0c412403001c4080302102203552a003070140c225001355011a0302c602d043d4200351900c515a141800c13111f6905c0801907469401648200e1321001c00c05401c000c96040032000c07591a646014105003149040c400c080d02d00310080b8029030003641d160702c021240c104001e0b44500850b4003d4120f410300f031900708510340140801e0040d0030042810308641607015800714200c030002a4080d044920b00c81c80c642d01074601c06501503820350700c00501c0041111412265046961040c001e6009001c0e1281410500105200040c03410340600a50802600502c0342c46400b4400c0fa0760a0010300c0e0341391 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 801657455 1250 801656205 801656221
    0x1008060103121115040813050108070c12050c0106080102090109151b0c030b191a13052a03060f01080c030412050c0f0a050609010608060f10090906020d1a18 69
    0xf04022421450320784100c4d0600060002c80000ba14180c06480c000325003607074482e4010b490840080f19041d0000e6100400c980000b105d042242d0300148090809034142401c0c2d058590945840d50030852240c0c1d4041800380e42c941e844142d1034002c00e420090103584009400c0014000b010f03103409023020841c41e1407100304102c180c0256100641c0c100d1504401418201011000c1c1c0c42150048a006030a20310b41941c2e10345142417070000c1e4540241041e199941c80e01c85400508030007440b801d02d41502c0c0f001da415141200d51242c00203150850125070f00d16000b4100080c00e09400c135024104480d200c100720503240040100c030381068005c400300b550b52a044030700321010b100714544d0315220f014209502d0504200041c6030034000c0d20620035290103030341d81c41c00785080313a04521800c049a4400d02c04103400211000c030035a0054a80f08546045e1501d40c1108816102044002c0b1841940050080c426100c103102c0c9040009440a5010803240300c00005444010121441ea07038401450000ca0001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 801658705 1250 801657455 801657463
    0x60616050c0d0f020406060f050d1812080702011103060a0b071b0b0405010201050901020c071e081b030c1e0f060c01090309150e0d0b060d0b0f10080601031211 70
    0x100e100400c2d4071094049031920001018032814200d0040b030409102088140c0501d0009880e02c41a5032000c1c108400b5002c1d1401512000e03000f0030400c03200501010106824019000202c0030300d8484940c181002c02c0c00030300b191406a200f4105090a000b80003590303031407040d103104441c090850107403243c1280c148454280f507c0b00f01c424103800c00e80c1000400885680280c0105c40098000f0400ca9454041b09400d0340b0440c1c402c40c0d00c5410000042c0941c2888001074122445010440b0f503106e61101001460410b46ca9010b142580403000c0b000c0745c9240c1041540100c6d08165110001c8900007a0855211030072aa8843e1091900720409003564550b2002d59003290f00401c0240321000b054100586854580c0c000c49141045142004010170300a0314900c0e4150005081c2e40407680058072940654080900390030307404241e9605400115000d0303500c941c0159a0255210400e040c69032855408400300d80c400010b07a04080c0040012480003905044429554103100002411002c400c0e424 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 801659955 1250 801658705 801658723
    0x4050316050706110105010b09121213030b0702150c0c19150501120c030b0a090f0b060a06020f1b0406231c0b070309082a06010e06061605 61
    0x2100403052415060001c0010b55104956031601c601c90480248130000d030a07900d003405141c0000108004078021810812420a05000010b050355008500306441c004a580300c2402c60012241d075039828000e000d040c1c1030503a0007841c076000500840c0e200000720310060900500c08090f00c0380200303407183c1c080c2d018403401d20503d01ea98281006c00e522031402d0a0909000101e052042d8682000418034824050b40050100e800410b0791b00c40c0c0346144c0e242d101100c0018110780e0016180e149684c0002d07003000a100da0340e4440e5014030442d1410300203000303c00f0810b500000c11540810100c07044414045059204600c3c8a601e51030103081100100303000c0c1c15640e2046000d0401d1a400a003403654003000c1031402401100ca00340581100146880c1d9522190350181060045801040b40d0a000358081205580729103c0c1504041500480100e0311100e01981c40a00003008031207086d80703c0c203012181c054451035078120210704128001c0303500c60107a2205091200d06015850007408002c00c82409 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 801661205 1250 801659955 801659977
    0x90c040b01080420121f0b0a14010207050a0b0c0105070e2808070b03160e0609041e1517010911130e030f07112209080706111b060c070b040503 63
    0x8468040c521045da52111540d00f44400001c0c42c2100049000301400f03282003103100140b848400908101248861041c40c80c406410b45c49410320005090302d9203050500181000c010043d1501c036120011429210020910401c001d182200e41076280e0302d1154958805d0000c5051703a080c6449007034810039070b080c0c94001040314450031000060041c221002148a0000506048a5681126800d4942d02c15000700203a00000521107440a802c103503100a41c1d004000f08d3380c040c08908031410341c00716042d100d0b488030504e4082030103102405c50307440c030800101490300082001044c3c94698800c003114401405104030f41096034440e69200503040307084e101c0f12403000c0e60340c0c400d112110000c140c1e108810864119030b0744c40d40314545240c0800705828440007880c8182100102810410003088088030440303000c0360900120010998038450710032000d804500d07141e51001400c0c8800e1356107040c0f01807407015a108000308903009811b082a50905540019030034002d865910b451801e40c00744800e516 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 801662455 1250 801661205 801661219
    0x105150d1107261303060203090a0615050a06080c0306060304020d1401050106080a050f01140a030605040b0106090b040602032215020705131404080903070f0e090c040b01080420 78
    0x1d00640042031010441110151460807214114443c0c83c4c2c042c402d8600c18646050004202142e215001164450070410a47c5c2c1e004d200d59880300122181c10031486124000f554081c0540e045c0580c002020b0a003500b00300030140351442984006100090020303000c1c0303601001060464440203c8036012941c0441d0310320908030004003140c0240070920690300010814008580d00304071610450f8014510b03c01c0e1030705c0681c2011404c0c0c0204c038504c221650450040c410000104004d81708241c01584201140b500c0c3c4d514007039009111716a01e4200c1c1900d524100000c1205513000412251040386001c40809840c11040c200d408110207507001d0066803504158021071a640800c00340d00752001242c0c1d1710303a10070f2044c08071411103041468407044000c0c0d0f500424046420031016006c102402000c44824036218000355200d1902039011880510b82c1200f440102c0a09200c0350340406410355080020201c4035000030000130020700068103804441c81c01d5120050342510301d0319100005840704c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 801663705 1250 801662455 801662467
    0x3080412170309060a0605040b0904120212130503010501060201020f030412050d051305010c020d0f05160c38030a0b0a0305010c0507110f032e0606030b040e060105150d11 75
    0x3a141e500441790720305424500700011696240074440d508a6140140218426944568540202180d416003420a61143c070904145042c40b80700208640f15048800500251800080c94255001078000300256401402865070950403102600d034801d420080c04100a00c010405450324031480281c10342031410481040280f0441065071003129204500800110032503000072600c1d44d0000b04900002488071025240441c800c9000c5e20024100c10728120f162213032541d07002400c0c3d1017170744586508000c08412203c8c200020384c081011081510850407010601040c04000384401020480e010307a41b881809001e8441e420724002441c0d01c0b50080101402c3e00d00e020303201d504200002c0720484042c9540e2000344c1407140885240000c058010409201040c1c3e5000140100009250a80c13440c7c0ba092a00d4080c03a0040e400100401d8500203681005801803005880c130581074007150303a200c000100550b4940780c14584c01c000001d81d0490b281c1e011486100060034882440408840c0e0100b10707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 801664955 1250 801663705 801663721
    0x604031d03033f0114011106090c090a020703050a1b0c0902031005030a0507090207024e060105120c04021215010c051507030e25050307030804121703 66
    0x43c0c012010441d448620900d080b050b5440076a40700b000001283c815180010070501c046400c1541040c40141081302e11084001101d51600703a0440b245101e550002d4110806410310b2220310380c02540c207030340961405c02c15480c043c0c841c0c8070b149600300401070318a10fa40459030000e0a942800c80d071052079516141e0769290340c4006900305481446040b102c107100000c2d1490000b0344001041c1c1e009000c1d01d02103240038581c1c4025007080c502a600440e01d0f041c10072a0360140340a160358040005c07640314440889048600522400d03c0c040700096181c5404496000c100050050443d241115802280c82d80c18412500304174100c412140c02038004113041d503a0806030910a4800c00004d44c4142040100ca001107410a4902c10b0142c030681001d224802d145440400050703000c0d03240d04002c00c0c0d1a040d8041c0901d041c0e8080307694020980010246046201d2154512008001c102c1c003d20031541035031154603251280b88513070b42064140354a1402002400b40c0000004180d40300300035224500045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 801666205 1250 801664955 801664987
    0x60c0312060102011803360605030f0c031e060604090f0f0f02190507290405010506190506180604060908011118040f0905010e03121302030604031d0303 67
    0x1e4007409542040310113103000034005218402290140d40d07075010310511101c220305400e05404148204400301d2051a8903092000c201c100400c103a80c2c6d1181e5924099a11000312100504000840301041080c8061050410026a01d40d016004480000d03242c1d400018414822640095000d41c01c00c4c0020002008940c44101564000d140a1000c000b030310201c94101d104003c0c100048400410001c6c0e40e0503c902c01800c00244142a9100d80c10040150408401251443c00d01d07081001e0b0100801c2100a00401d90032640070303500b1f84a80b0b944210741214603d010300070a0b01a440104400b4080241011250041c02015100c180d0301e58880300c0c0204101e0303850141500540c03d04220051081102086540c01481032000364111110039003044050072210150b155640c4c3c4a600d004049107080c46100030320311120004594500001c050501e0f4840020a00a9240d2440860202503100400c0003640107034541b0300300c00724203a0500744031003141144491903050307c008210b299901c01e20301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 801667455 1250 801666205 801666211
    0x290724050a0b0a0b0c070b0d3c0e0c01030f0212180607090f15030b1504080d0912060902031204030f0c0503010b101b171305010824060c0312 62
    0x284098180300d03213541c10a542841840d481900030381c0f28407010054800c8420240142c0900240003240346885d22480101142c5c51203034014148241640c2000340c2400d1409900003060b94410500940c065910b009803101d00004120703062607221501c500440025504a842c080c40c81e5010558505040351400d0b0740d40b40040c041e01c02441850081145140100030f500e003110b04142c11801c0b1035040000c0d50046000009846040c541c40300c0c000c240d1075580102e0050003c0b2005022b640b5540b40c250309030315020584603090180060410b0500a41c090030b0700341c4012a03041700004c170380603000b840442d03d40345010200541500c07000ca000301c00c22003c24508101c8602600a20b079100f500c03841003500700c40c3c480350126406600802c0385403509000742d0040a00404001d903000b10b100c000c1d111415a8580c008400591030b0b80090b24100d04040c080c2d40002901d002e01e4003018918100c1002480314540003500c0355607450415500c65180e40d400304079000c4410381d030162a211b401c4540d41e906001c00c20f03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 801668705 1250 801667455 801667459
    0x60a0516140f1501030206090a0e15100c0f110a030203030d020a021612032304080307060f050709030b04060615050705010c081006051303060c0801290724050a0b 71
    0x1032445400c41d000018854098611240e07100f40691a650130030035a5880703c480c0c01d4100c52500000120440a140070038031500900d480d00700890402002c02180a200040c800c05003e440601c103804034110034502c00481781d00203500f80100c07c561000074040300b0513510095145c400010f8424041c80390741c0182500002640885515503585980440c0c1c0d90454010440e1407941d0092500102c1d1080030360682c402c03214003407001e1103080f43d80510002d034855000800207034030010780c500411205109002039986001800c12060070070510080c40d134891440064801404040420180b0145512040042a0010012042000c1c08401500542081c0c0c81900d46502c0e00f03000c03865060142d03018602c20205800b00071320050900d1819152504032412045400039408004400101e407071140100e81d0002d03485580507585030807078015031651800442c440c0031501c0340090045080ca80160303010613a202c48200d82c0042c200c0846145080b07030b14144009035081800780410b01725190f00a000741541 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 801669955 1250 801668705 801668713
    0x1020708010c0e1324090e0a031b110a0f0305060c121b090a0603050105040e1b040f0b0d03020313060c1509080702090c09030d050c06040b0c07060207122c060a051614 73
    0x181d64466468941080001d004102070143c62b030b545c3c2c44000d007661030883c481d001c000e01d030f002e820000c14030140c03950b048901e8002807a01c0500c10720904124581d882503184044901e00320601054020900e0041d2840b040e06a1008003041610030740d5081d114901005040c1180080e0b07500307002400381401b841690700651516403d0501d11202040a00c400460310500344074461201d003d010090401d03402a040d03113581c8507402c110f03c1d0380d036050b0451114002d90007140c0760704000980b0744081200e07620007420300640400324000190804003251040500642c009000825411b012003035104001c402984140e840d0100101c481d8003101034a8455000d80881d800c46500100684840c8206000d013451903000c1c1c40024001500c10907002d9200032520f82040c10030580e035548406a8005500464960640d20505140b160780718120505004400341107550400c09024404160070200385c415016100c00903241c01094003c070121034040051a0005104806608180c15108140211182d00d402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 801671205 1250 801669955 801669971
    0x207052808220602012d09050106150e2202071a1602010b15030f070306030b161d06030708090c21010c030b0307150212120601020708010c0e132409 65
    0x110501c0350308031580d017207500a08100a1a0102c00701d111b03034100703a103e010f1748580744e03500021028090700f8010002d800c4c0c1e13101111101038000e0074940051410300c0c025080c40350f40321184903850f000ca0401046900b40143c0d180c1890808283c20f400c0401401c01e1580c40c00c0a1120210581e0342041c0700110030780c001c0200d0341e9942d08115141076100b4100c646000c007400071803104115017900c10340100c1030303050000d90255250b940f865018002c80b84200203520548000a80079004140358200c0f0030382910105441c001500060040e002c050010320421101100290b008002005907040d0008020015841c0c0461135045503401040205440705c89d50030101c4044241e0300038003c64841c0c25005002d008101d0421369501c1070103242e60341d080110b105600142d040040c03031100401c2a4904400143c2640c0307800000a45018001c3c2d0000070f517a850a500d14000700c0e4404c0503003224410407038004022032030300d10307544029008290740b816900302d800903500903e2a214030600c048038030f11401400202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 801672455 1250 801671205 801671207
    0x6020d09080102040b07170409180c0603051603050604150909110904020d12022109011b11120a08030c0a09080c01020a0204050a140c04050f0402070528082206 70
    0xf0149224020300f080040c0030400014040380c00d0080c01e4a1f002c40c4440c02d25543e0f012080c260781d161130074102d800c140c4003450424071285a24220151441f410700f031106040c995140e44940e052010a0320400d540c1c0c0010501d141d03940d420000e6988480038028088540300d26101c0002c200f0500210b43c12180400e01c9506810544100c80c813541d002805a150b600c0c440d2070744041e0384035801c01a42140036140303090b100c18003e42c02503010b44058441f0b00740c50b81d82c0d00d000501001c00403400d40c0700514100988000107004004034046422096a8186040c80ca1102d502e142850340c04000f0b000841c04010441c0070b158040242032006800e0303075100b5025944121054031007a038990a140103810140300070340542025003240e9003040040100040c1c4400c0440303144202d12003691001c1c2c0c420030010381000307945080c40340540c504400b100c0071440c1400503912141d071640c402000610100b04014041110a06101c13082c45450700212503a948505403e4035442c0710460100046c2e51482c400e002103005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 801673705 1250 801672455 801672457
    0x3030b0a1a0406030905120711040b0607020a0513060503030f030a1d15072d08150f0f0411070b040b180d0e0f04090501051911070b040501090c06020d09080102 70
    0x807014424624549400c1000c01c8020f0142076a0542c0c151040c400c40100303c0700350a0007421075078042c0e002e000500103a1004c00003982c811403c0584602000c1c00403a026075140c031403101c1216002c550303004841000c00c4540300500032940c0402c0c0d0601011800149000b090b44c021803150650702c000300803032403141c2d1018000c0124031014229a0780403c400300c03000420480300680000403410702184d0040c0c200ca03038070101020f980ba65a42c0e4020b60003082c2c00e0b180c2144d02e0503008640c928840c10340650583c0800c8840482d00b0899119101958555040d42c590f544120144480709003a02d6071100d182c241000d1154059030103c8060090000140b01c1d40c8055171480714060707412010b4150980009011588201502981d0398440001c102a0f0410b03034a52041500d014840c40010510303282003c09965030041020703103804d5031810008540c50080060742140e850980c0303c40030b060f4030f883d1420000c3c0100304e203c00040109007242404150345400288030440640f041d559a202c03075864a40443c20307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 801674955 1250 801673705 801673739
    0x1b040b0901061407032d080f090c0108100e0906041101050313020d05150a1401090603050a0f0c120305070210030b0f0f1216150216140612010303030b0a 67
    0x240c10304010441507540d03c8002c0010b10300030f1900c42c916030010b690503407a241d214400d00083d02c02410020007440c1d003200c09994000012412404d491034010134a81d21040c3d400c07801410880250000390142c40e510f400341020303000c2500c90281e5481c20301c8540d6a00d000030b40e82501d01000031460901d040d8810011a8402d5a83d043d07800f00909441d0300f031004035681c0e101c084455010f010030454001c01c80301c61441c801c156603080815500e15014404546090680000c88240d0600c4024000701b80000354103a0103a50020280509803564100420b5900130754024a02c8078840c0350b019014540e020001c0d1108034001c6911400344640c0e11010303030840300c0d0441503c1d040f48201e10321500c030b440c0407001d03551002d4026200340c0a062240c180c41c2d0070801b62017280108160701d10002e200941006181415500c2c040c00104814100542d24800300ca415200351044000c0300c074605c0e84d890301c8150580e85070342d8a81210510b0317540c6a143c003030080c0040b0494140140359010000031024514409121 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 801676205 1250 801674955 801674957
    0x30c031106041509050316030816020a0b04032d0c230c010f020102070212070e011d1501030b100201050601030f0903050714010b1804120e030c040b010e031b040b090106 74
    0xf4079500d94103010028110413882902c090000b07000d80c980700c0541405134011188a80e0f15084640780c04014402403901030307851203003154880400340c40000c10020280f5006601800c20b100300c80b49901c80e0f507140c0b0341c05407861711a060740141300504d010341051070446090f210310700c0407030340d12080380b2007188000780841c40c8000c5502002c0301c00c5403940100c2e203240700c3e0000c0d0b2001520303100807070300407440071039002c00b00211660000004000b0404030108640c0500011a401c01c00741c030500352800c401d0300b006045e18040ea86c22a1528180f40c3c000d0b88504c04100c00030700f040c0c041000d05107019000f010102c50f40c42c00302c3c1c00d01c440150365500ca4410b400b42c0903810b440701420301c80705840d00c800c00d1281c4a0045040c1d96103045108255844040030481e00407510740800e901d2800d85401400000328012980501030f45030818441a0740200310400e00356401d60700081c640c0c0710a0b0048444028549400740c06000c0d0022100181c007810f900e943c5c0c00741c6d06a0b018450480d0300d5082c00034259007446600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 801677455 1250 801676205 801676223
    0x7150f0e04061706011a031006080601120c050d0c050f07150e15090c0a063005090a0c0b0f030c0c100c0f0e030f030301062a030c03110604 61
    0x551900400300d006440c0c102600c001841a00c0d9800a82c03080b4083e29501500d611810040150302d848040d030407201002214400e00f982000514400340143d140241028400c50100184050348038040c1600040040d02060140440c1e40700c01074079540c400030040c2121402c04010300d2055000310220385082c02c034240a1403070300c0030a031580e6180b00103980c0000c040700d455410701e1b41d4000d070402041d220600007503030349100c1e0305050f84410f103890349210b103c42c02221220800c2000d560040359562565106000065400700f08050107001c101031a005d80400e180340405024500c03000141c0d580c220741c031601c2096900c503182c5000c18410f02802c0035146a10004000143c100740688002e0501603407003400b00d8940381080440c803c01c0e0f510340c5005c500000c1248071340e141c805500402c0503030200c500b500900b412011400d0040c2d12480140a600140410a94002c1c4121807000300640380314080200500000d9130740c41d00030100c03400b0300c00a5000509041040f9401d40000c580e40b4000c690010701c0d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 801678705 1250 801677455 801677477
    0xa1406031c0909090b012d0b0c0109062d0608030d1e02072019140109050a0803030a0e070e06040c1209030c0c0b040302130e0a080a030e0715 62
    0x9944616480070215007000b81c0c00500040c0c00155025400071188190005403d80d0304050202c035210360340c1048180c0c1c003900c60200d44548251900c40300b041c3c94030413195903911040c50f40d9103400340c209440000d10b03851610b4403201030b0094800d581d124070701100840110181d100150201550314a000710780280e041000010304044031680442e02c0300000d20a05101900100707150030482e0030090040d101480348452810502803240400355000001303d074951200c1c41044c021404400144c0519061200704180b80c00d020b038015815000200401040c0320541501c0340d03500d075201d400990f1140c05607414808220018000071076104252a010310700d61010380c4d151003c22000e00450311400c418040054882170a1003041c2c0181d140d5076000b5103c084000301c4a10b002c244460240d4054054030300e040c0414401030740c07000c1038100380700201c0601081d0400078070f013118101000320600504d1070384000b0781c18200c160141c00103145600341a00340d406099445a88218042c2603a1003000003407404004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 801679955 1250 801678705 801678733
    0x1090c08130c080a080309010c0519120204090e010209100c0f290108030a0905040507020703080d0209040207050a150612060e0c030f010f1505010c1401140f0a140603 73
    0x1968001801103102e1000e076603990890908001034a4000c0d04e000e8000020440303114424000c0d1048000c1c5c0746481850620103442055034488028a17070000c10124001381700c0c00e10f00340c0e015030700940307a0500200285907181a0150003940300128030327070041c2c000e16050345809004900544c0a65000840580c6041e400d50320a50f0410b24162034100035030717108a4000c0300040c1e21280318080c00ea81c1c0002d542d00d40790390308041c000c0319255000500c00c50030328040104c01ca038041000c3c0112540003550341e84460400032500302074001d40b14565001440800d9800034040c0004010280742d00408803000a8011400c40006a0b00c050240c1d0700441080d44020f0002901e1317910050116a244041d80e4156092200282c104103c04000042c0c1e613454112003510501c9622075942c40e90651080d0f40401440c0ca40003034201d103110070001c0c0000c0030008440bc8200020340104001c440000445000362a1200601d00010000d5912101192929541d42c1801040c01a15801440c00400a06000c458140d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 801681205 1250 801679955 801679981
    0x50a09081e0c01050a0e06160909091707050109021512010e040f050a24050615070503041203090e06010804050c0f0315093d05040f080c100501090c08 66
    0x1005007001c420422005a42003000c0c400c4a004a11415003c5000a14090885d02c0c040014002c00a07e41c0c2c0742442e00681608401918215600f504010840381c1141c14035044560b2201802c904220b80007038040c08105040d40000d444500c00c641d842801002c80325200018098800e498505928500044c42450b008441880d0b000d4420b0007000e14a100d195500c6041042611381150b0250061003441000480304011a10444078080208083d140040001c0c040f13003020032441403044030024040c0144401482110701410041680d81c4901000b880c0003490204244515203003840301c5c1e80821160740c8504140381c011078009d0021b00c0c1d0000300d00100701c245a1034511456040c441d80a108004c0030f07011030428442e02c04d20018142c1c0304c019070307400150b1054680c5803e0882888410820142c02c6528008040b1501d00c0c00000e01c2e17944600e040b00350300c1640b004c0640b042c04080b81800c400100003440704801d240d040000d02140c5d07038401421055610006410000c204d2100002d401598008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 801682455 1250 801681205 801681247
    0x1d1c0c03120605060c010911060c0c090402060c03030f01180c2016031407050a030203060f0a0b06032a0310090b0f0603130501200304030e030708100b0103050a0908 72
    0x7070380001e0a19512000500300798004183ca2695075160007070b0304c00340074400c3d034504411202660702c02d250480610b01e490b200c040c050949441160004049819074a80905440c54800c442c4101e0307a503810040c0042c0b151901c00d00c03414010440340c44034052645400e0084d1039024403240c551004d00e441c4464010350715545900400070718480d840c40400040600400c5a0085002e406200380c41d02e124280c0c1303400c00711690043d0780145c007080c80c1040161800102203503c043c1400480d60b9035103c1d550804064205c1522441e8442000301c1400480e41240b0300c0c4020790584020200f82c210b200f006e41e00b005000c100e03100300800d1200b2008100d440040e42000d00c018200410750504c0c4001c0000040c565007043d1500d0408400c541c003c042005424880c8038408c0e80401c5a03588600d041e251645114070000384010100901020700c242282c030b040060b0000740641c10250b0703500c46180400c11004103400101240000c1c100800304446514a100314414143c200d45814070f4903c0001b49442810100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 801683705 1250 801682455 801682487
    0x806300f15102309044701140904050319050a0f021216150504030c050d09080a0327090c0e0108040507030b060d0804080a060b060313170c011d1c0c03 66
    0x1001c1b182c50042419181c2000c0042d600c1941807419660310780b02c030f21120340302e5001001c80002e1001444109065421400d800d2401c440c264219035503494800e045014040380303240601003050780026050f8200015200c600010355504008800900049030380e070040c40503803c3c40b010104200070641c00da007040001014028051306082c44100c00b60141181c40441d0140c7c00900320840c8241000b07418030002c0d014809900e02501106d0a196001d500d4040d11040281400300b40a100c1e150001c8608030138014076800d641d4140420364401842c0040c16111a03400000347d040c2003440c1481d07024240141c02103421000070071505095548400345400c01411590380083d5949924000075906801413000d00503500c06403d10b000c035468400c040d00d281402e001d00c508030500070450b4040302c3d54041110250001c988455880f4680b0012a01e88640c2c6054080c0354205002c0b080242c40c00e10081d040c1c225036408607411600415a01861198a81e180e20005440c4e800c1080100e845001880e030039000c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 801684955 1250 801683705 801683723
    0x1a01080712061a0301050111030f2205090a0905070504060b0301120606050910080706031404020906120d091712120c0d06060f0806300f1510230904 65
    0x210258214010380303001d4403800f400340000040c091940d00180340c2e143c21580100550074490303203001d40341c054040d4004511258045101d10b000640e202820305009050251400b4540d04081c107405000d0b0400d40015103151049a60005660405110300403c50315482e110300d0559086c80c00c1031040c0381080c1000d85043c1d845220100e034956584055074050104e00740e844035a945440c041c41c0c20b210065100300103051802040040803107203c1340b11035105604440407a240e955000c002010105000c3c0300c1d0007907100303000200f04030301c1c0c208040006462220201182d1007541e00c08580c0d4500d010440800d0249091049801811325504100c0e040983c0080b05428410020085400c4850070750110000030340000c0b41c01041900000002d8200000b40c400511030740b038028000c00c14004413078940031044242880d0038031102c002c2c0300e200340034264503050311810440c1c42c0d1002070301b920035162082505204080021107050703c5244501709070241214003e0a1aa081080715500780100241c8403444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 801686205 1250 801684955 801684959
    0x20f040213080d1101020a30020a0509040e010903020a120306030215041d040323121018020c0a0f0305090414100b0c030f0901090902120a1a0108071206 67
    0x600390124402401444004040c00c0c00c940c0c200138006000b1414400c1c1d56481000748480665000c4012500c111402111000c0c0480c00e200c540c50b403507824002062850b01c082802d10b54aa849001407100200c1207400b0f2005070401c500e0107080360000b0344000c0140e4803003103840c4006010a014058005100e0400140701d03a6241c000c0750f11f11140a00c150540a13002401740000440406042200000201c1c5030540c0c3c0344c20381d0041c21080000d00003802d02c40031040d001c1c00d48003403081290744481c014180c1118a0a006201d1891810180900c0a000f4030040401e10702c1840d601c2a58044103000004000441c55a11440d40c10080b0b00c90036410007104000c2d0004503216070182d03083e031505000e0010000c3c170344100c8001d20181c05401c80d8040003410021028200800416a000805d440310504c0d51240d0980060741c5903101c90344074012260000c6000d0002d00c20794007030350348180002c10040c0486c600d6000c3c46200303000d59160380344c0420381035000b160480c0c1c4560581086407035031010004d5110313 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 801687455 1250 801686205 801686227
    0x109180509100f0b010912120513080a2108040305070602031e10050102120a0903110f190e070c05210f040e0402240316030605100806040b09060607020f0402 69
    0x405604854100c16110805250b2650b1b1001120000789966202ca89200d1566030310303400c40700b1070202c24a040000228846400d00d4086002c94014010401110910000d034540001c6220300d500e0000251030428146413510f03400352408500c83c560546d5014600001c0e40d0f11417000b5040a00300d00d107490740c03c41c1ca4160007541c115079540507000321149070443c3c078508000203240501a200c0c814552205020302010030781c1103030352101504d502c4080001d0b0b040c00080800c00040011540e15070028410b080c420100358944460007c1d6012900100a20350340c101d0b069451407101507004015a01c45003009030390320f40c1c11100c0c0d48000e040e4201d41e49400404900d010301071300304e41c0100300e001c00c1d07003401d00007145040c40c003071702c4100c80f41e146401028020110001d083d0000902401c008000b206400509511079440170f00034210007018421100e241c004c000741100b6040324410f0085e4503002502d000c03807600895445c4268001020319140600a41c28002c1c1d04000401360f5070066000e0090307181e0384d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 801688705 1250 801687455 801687461
    0xf07030903060617010e0c100806030a1208100e04110609030703080c151b0304030f0e090703060509090f060705070809060703270f0506030711010f05090c010918050910 74
    0x4110304c040301003103004405a10f508480b005200218141d02c501203445c1d464681203403508106165090219031690355801180c10601160b00080040d6038140b441994540c000d4001800745034052490302c0c02c952a5803090b03803144002c2d20040c140c000103182c0c1e8080c900d003181c0101038030300c0b000e81900c1e5000e40e00e0b9244000c9400c8140900d400760026940649030b09040051300b5440001c560141c0340d58a0010242e01c0c00380710140014003001406d41e840c5038024010300403550206005070040d03840e4030f000c0d44018010700e08d03401202d01c240c0e900404581c2e9030000040c2415541079240c06851151142841030b03d80340d000000c2110a4041440818550b039039110141074424001d440390080c2d0810703410192025400311a07466509001e950081c00110720980100003540d1040e51010b68039215000291945048108550702540c20010f8416036568541c00c02c0d405840b80d007045a081516500040d01c403c411400b03080c403298081d202c2d440c54201c45030171594005000ca42030b00c1d0300000036250002a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 801689955 1250 801688705 801688709
    0xd0615140319150203040c120605060916171306020c0105070212040803040308210709030c12150203070504050306100608150612041e0c030c09020901050f070309030606 74
    0x3901000d00300c0404503040922074060348000900c619601520181da802068540c0c40701040845540030002504000190901c01d0240501c4a0030780090106403610304080c0c80d080350007900034441600424068200c10b06000c41064003911000e01006408080c2d000030f1800508008400c903820031103501041a91000700700300080017002003528a004100a4a8107000444c25041149c00300810040184040183d5003602d0340010025954400c50740d100781c00300d18481603007182407155004c1c800c409030811581812240703e00c043c01c080699860003400400840f031000b41c03144210a40c1c598100640341e006680c081c036281403960406858102207441c0c490200d0f03100b180360a4503041408000d4010001591104022500003441e080003c040354250056a66a04c10505480007060400a003090f8000706200c20342c07008889601c03207041c800a4820755110035910004480b40101c1c01007154003c440e041c00060f124a0701c0c020090040e0280c2d0350064500b1341c100040e130040800040d056020b0500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 801691205 1250 801689955 801689969
    0x12080a0b0d0f06050c0423041d0d030e0c0d020405041506081509030403030906080601110118140d020705130f020325170105040e030f07081b07050303090d0615 70
    0x22151a070b07031401604071030029005003050502404208120360021302449020211584460781d6940c0190210300030703018400e03d103500030030050314540c2601d8000448141800803075809100003011101d01640360b070300da0080035801900f04001c180240c18a03801040d0814481c07017140007100080c01e220800c45041e9000390800b50880500d000c04840001000d503003104400300a1490030b45150307400380480d9102e10032101485030b040001281a80146e11820034480b244000340040504101e05000c6040041011204111620410085418006411099a034146d002860250f091108000d020b40149a4511030030782c50b281242ca42c043c1034009140a1070442501c101d80404941c2e441c45012a441544010414240d5840b0781010200501c1d50460746d090314000368600218002500310321440b180c521300d242c0002254010040d9001c003c180701e111a145608000218205941d15150140b10310f651640c001d0024440e1445e0044d40380f040140f040600080c0150844039081c446401640290 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 801692455 1250 801691205 801691223
    0xe0a051f05160b0709170318130c0908010609060b0306040b0d060207050a02090603160b0a09050a03152f0f0415020c130c0c1103010216060e01110712080a0b0d 70
    0x342c403504089800e014188182a0b4500d1000224078583d0320300440384e0003403200d08447c40e5032023140c84810007524180320a030814811a881500d01802209541c4070b8484a50720f46080000c20768803074400c03c07080e100c0b01c103182480e54840304104000f4064500285602200502c0c04900007810342c0b00070321100d8481c5026003421915030041000f1078000400480c080d4000d61001d0340110303400c1c00f0803015218a0aa295110309214030b00700c075809241d8100e40c0d0400000b0001205000c45c9048441c00101180424850820080300310900041b0111580041501410a00d86080b80d158064800080e48003840c03400e040e9140034624200d000e07504000007580011001c0c190301e0400202161440511700024016100700c40801046020100c1c2d000d0f01d10750240e2a0156035641c04c1d01200c0741400c5000800b00c0c200c801d800c103840200a20034900c09658a442038007901c1c2c171241c0081d109055005070201c0703403004812100344c1d01040300a1420340700c01d55030320600040303035100c00041024900440c0c1030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 801693705 1250 801692455 801692461
    0x3061d060906040b01080a1a04060906051c05030d09080f04030b0f15031504170c06190501060c08030a060b031303020c0409120f020723010e0a051f05160b 68
    0x3106801d6000b030007880c092130610f00c0210640e60040c0481e6002486201d000400c50704d142c075100000c41c04440303c1c5600608040000807030442075000b00d826a0811103003690016106007852908a210440c01000e0360414410b0042c40c6c1510b6000751215402000c3c2e07240f41145552010400d0f80c003c0e01304403420790894083c0b00802c0f901d006100d40c01040c100f600316010f08180700281c1d8529410b414001030007100000181080031052a101c042c0c070104d0b249640b201d6030751641c0354031840704407003000d642403295004100e20b12841c01618102c0d81b064451400074415070704c0b0039503e030344001c041ea4185511a8000210054000c001310f00c250346810385045102200d15000f41130400303092560384518181400000480c4004281c1c031001c000c5400c0003c1078841800c4140d00b043e075203a0002c1002e5044e042c00035810030188400c015000e01c26079071400f0100c0e250701000050b0841d07000f007a07003040609480c1c2e99041c0b2f8014a000f5440e20600f851820240104010140804084000c0b56200204014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 801694955 1250 801693705 801693709
    0x11031b160f140105060406081c050d0f062c0a020a020f12040f050603010b0919170703060507050a36031118010305030d090c03140114060609031b0103061d06 69
    0x20301760042000c8409104d09032038500d000307a8541e00d8108142800e9504040464400d01070740032200f141c4e44480d0709010b104510440140142440d01c41d07030351b0480c240c6c4902840760003040075046034540d50320802130464680880c1c10700250051040c88065120320310401010740010450445011a22400b2030764035800d100d12801580c410b80e00c501c0c0584003d100522a081540c026144c09074402d44111032600941088841000c907036034808a0658900c81c4841c0c000600403841d03130166802a08244119204d2004c111158803990142d1000601a049d00c40c081800c0d43c4e0405c0140c0703070380c8085079801903031101d03c00c45003140552049448489514200e40d40342880749612104005a60000802c1c0d0303d16103416842e40300d603003144416180c2e1410900e017081200e0400c08044d680040d00d0710411100041094002c2551030703c4c03844a014840700141c41854182d0845400001c00b5014240500c4003042030380001c0c2610300c0480c181038884c031010880c2d0300101c3d08140580e0030907080315090300340142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 801696205 1250 801694955 801694961
    0x1515081b1201111207031d0d0314040201081b0c10051b07080304140a12031418151905130311061b031008190611031b160f1401 56
    0x20003041c859040500c1c004183c103101054508419a000907160159a544012001041c0306241d01150780450b4207008460503000410f40f803611040d440030041080000d039808110641110000d00260000b000550700d0704d4982d8a0080c0700c03442244082c1080b03d42c0e0346503802c0c01c1d900401c0304115582d1703100700b0000410151480c2030344c500c1031000c01e1800e026916004501d22009101808040784040300b0358144100b0804420503030b8003d400d202c1d904500c0c500060107031078201a50320b0b10051300780102d0b0f00700f501040c1c9141d50032902c0c4024411100c031140c8031720b24820010301200b4081c00c01001c2201c4400d0380d014036031184141d241c015400c0b541070f15001e80209065640d54000b0351003842000b02e144941744402128400134134010b07480795120400010381001581104549000790240b030710241d188075940040f0140320700400d002c640f030640a84001404105c0b40d0104070020f1003410400038038000014810380d884602c204d0306042264442e10800391107044103c400a030032040c400100c00080c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 801697455 1250 801696205 801696229
    0xc0a091a060406090b0c150a141501120f0b03190515070206180102070501060915060c12200a080a09060c0c03020907090504050a020c0c0303071515081b 67
    0x11106420700d81081d20041003840385005c1d05205c070000040900c64400708205400c2000c03601300111645142c40007104010346a100480751802050070041009000c04011921082c40182e68250700750414608000c00f0701400d0b201441b5880c1e0b40c074013040359a00d06000b40340c4005200c82d102010b5054a103482442c010fa41036030400741ca0f030b0103001e104086902281c119042900100d0100400c030031001100e0080c410303d00010000d62a0660010750034400c2e8102950181141c0d48404409a03074401c10740e1508c185000c01080c81000d03200c02c14126014800c01040e1000445003043d422240000d20752410300d03d05800e841040e00468098001c56020714000081c0c40185003039103403541c840e5644081118540070080c8036007880000a02d2041c8111207010051900601c10b10185c02e04181440007940644200240f60040c114508024140003049403906680440310243c3d0383d000003100001094140c0a600e5207091031080010410410400d66072010125680f0f212000a036404200b0281440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 801698705 1250 801697455 801697459
    0x1050103121107050d03032a1103040b0403020409320613050606010804080f071a0f070c0f03050d020a020c0a080708100519060f06020d050403020d060b030c0a091a 72
    0x64540b103010803404140d0100710340041e6114009050030b40750070790240114442c0c6850012500b41e002000d4076003031a40c0e641c031003001e8540d504141c0d06031080039264806c50180c5402e000003044200018103069222803001800340d605101a0040700b04200c40958008565111f24540d0000d5525070903001e009040d04802c400042d448109825910399031500c1004000e103040c01640d50024003407000400454003040f0360000200d075900c070f0500c2c0500450044031005840048038030001009050300c42c080d140030f14000d4503000707480314181d51450100840040c089041001c18030100d5800d0495001810398265141c02508000c59001c00384a014881c0744e11480c0b080d80102c408200c88103001c80c04041c1500c0356400810950340d4186c0b031090085a11192400591520800145911104400c2000d5550590aaa000c2078040004030f41500603400060b50103040015044001129544030310300405d4043d050718250030036240050200b034507075400a9080f64841c2c045401510007500b00075819602 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 801699955 1250 801698705 801698717
    0x40b0d0612020906040e0f060c0c0f011a1c1a0a0c1e03020a0c17030f0c0301142709010b1809070905090f0106030c06030c110d050904110c0105010312 66
    0x1900010030303d0001900c0203020700e548401c054140901030000801c40c003102000c84000b41400b00c04601140d001200c111518003c11a5141090b841801111078107031550102c1030040703824008002c411812640c4820401000000c200d00084020f0703e481120b68401c0c620413034514202441500752012038a04600b000301c00201000344545040028410f1080c5203001610741c0911482640c403501d02210260800b40181c0a210524000c18019440b0329507242003900ca6450340500303030140e4002030140d5103907e0226058107100f0b00f0154510a07403d0141c0790b45241c030454100d405144540240c1c1c0e001c60381c0c0d4644211501a0410b41c4203010724440f410a520800e00d00140540c0d00c401c1980582d01995443d5004a250b4480420601c4a9040c2400003000410b03901e24020540324114405d01008c28108140d200c000b5000f1506124080800405000045200b550850701c3e5402010341e581d11955401c441c1c2d080701d0310403000e8400e1100d1400000703103035411414a844046c401410394400c001c0c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 801701205 1250 801699955 801699989
    0x110304020f060a080a0f0902060f0a090f0e0703022109010605310507020c090c03061005070f060e120a090e10080d0819020304060c0909060b04050915030102040b0d06 73
    0x2071310080c085c1e802a80d5690028442456000540c064400b20303c002e0361041d000301c2c240f0f80d001d40400003040042c100b6207440340456990782240c034408d003c1d48680c1d9052202e010000d9000e502a40082c20200c501d10040c02c210b00482c0b441a4401a040e900c0b0462a0741d528005c0c8101e0030304141129141e40b859401400c0780705480a43c10302c106640000e03075903981c6c8800201d19903500803c0006149100100400300310b01c0c1a642183d21500110b429510604403008000c40c0d407401013080b2000c09410844d10070311003481c0d849030340180402c4a1519058403030544070003c81e810383c2014280b405020756a8481d03141c43d02e20a22134145000d02040c519004442040100350340c00102aa0500795a0070b00e10050340e03680540b251340700502c103c4c0880c441e000104204c2048250b41c0141180081d81d116200c44030348400006040311880e0240d01d0700c5001c200b0050100d46800040181d0010031880148078a500c05d0001c01e0036a04268080c0c14125000300310030b03a81d11341d140100c80161420b101112500300e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 801702455 1250 801701205 801701207
    0x406090e0d021209030d0302090a03021c050c010807050a081003050d050a0206100602151009060906052d0d0212030414130c09030b07050d1104080115030f030e0112110304020f060a 79
    0x103d40c0404406040d030000f0127916640f220400c44004580040c2107103810880362281f190f0850308404100c545019144820041d507001d0801d560060740c9a584050812803010300c145c54400d0040c0c401c1c42e50030304103032000001560070004040b500195584160302e440c0356102c083d1038032201802d0071145010001050011039070003c1d840503140200841060f441c0c80d9050b10340c103c040d80340c00c2080d0701801d0030400b166903401c1e60403202c100d4070241c4041c0031007024a038049070700400081d00810283d030005504646450450760354612517000170072400a82584480a40c41e51380a648503134240d0001500071041031400c0d0b03140310315609081e02c00b44240d0303540f281c0c0245025810b01004000120242c04160b56501c40d07003e4030440d500c041c40c10440c850340c05421143c5a041882040015802c2048c2568070701c4107446400d0440b58483ea20484526a80c3e5050320b40c800c00501c000d041085048024101070302c18000c0201c1c0c250039004860780c90404d4010b1181200c20740c0040c901170b00040084004d61 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 801703705 1250 801702455 801702463
    0x30c0c0b0a05041a01080d0e010e5b09080a0b0a0b0607060b1e03072607060f0f090e0a0f110705100509070e04110406090e0d02120903 59
    0x300d80300d44000034140d0384516041007410130a035586001c0211040c000302c0e40180005013412210040c4d1030b154809a1944c0044030036402c181a10b50708840384c588540000a240b0948102c0c0b06c0480c1e000a840e00c01c0181e500c403d2010b03840b030402885080d13605c5a0360248101d204591004d0603490145007840c103100d030311a42c0741004000202882d1041000541071f00c007643c0041005680104003d40d5001d5605240e000303450903007402c522648010181070416a404642e201e03914801801070844140f0700403841a0140712071a070301d00c200c1c1e008101204418002e00c084409401680c0b1480342042046000410312035002e1401c80510690403018007090080d04001a4425080003006c500115296020005400a004140184080032404004022011a0003508250320000420503596851b0442d96aa925849400009088200441d01094115140105503034018002169646e500c201d420116120315004859a400c80514900c6180e4140025660013120656450400c66054002921 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 801704955 1250 801703705 801703711
    0x1003020417070617040c210506060f01021e28060e19110a090203010801061e0302061e09130204050f04090506070e240301050a090501030c030206160b04030f030c0c0b 73
    0x10135400100002c04025114150f035002d401c49030b013259815446010192508145c200d8111054005e9500081850802400780016884147d000f00354039400407400d020710280000f6150010700030000c003690145804001d4548525003a43c08a00b50b0115090407021035401c0012000c2e2500203d01503640f00d0308110220003c2d64122200d1540040c11300001f83e00c02e4055400f407649a400440009903001c0198400011522500c000400c5000404031f100d00307a4046000c000d40c480d0081c801b451007010304515603070510307100c0740082e46010b5038900000c1c41010103141880495400042c01c3c0a1820300030321050340f4000c242d6007480a0341e41c1e560b40300d0f12488000c004004100c4003e090b1000c964403082c1b01400d64180d48401e207081201c0300302100b0309074000d001e514011500c814002806110520a00c5d0480b0b411120342001d09045508011183d030098500060300000f038056140884c0c98148028000d0f8800c0c0c45d00c8035080092503015007a50540100a400e0000d01d004041c0418030003003040394 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 801706205 1250 801704955 801704987
    0xc040e01090507020f0a03090906050906030307112e091202030c1002121225050a051b010c09030201090503030405090117030c06011d0109050c09041a10030204170706 73
    0x3040e5607918030480c5403000a031501178483c4102d441d69400e140d0011740000989030007060030700003a500c0e201400300700c0e2070503120b42e07825134010006080030642d001141240744000804e001e5076a0000f50103c0b480d450706408a118099111041114842e04010380e003005044186000c0c00c42581034001a0302c540542401c82d014076044569144a83c1c802d100c054107140e94221000e0321040325812100c10154119041c40900300900e00c0511305c43d80d09070b1945800100d03a0750b098a0100d1012089070380c1d0308200808054580c1e41c01086088480a01910108417410765450034210300d0b40c00010a92100340c0c0c41640a03410400c41441262590040e050542d4010092051540400175072a072562183c1c00f01501075004050000c203803001c0c1d04d25a030402d0b00000f01e448009980302d500704030840300150f079100c01c0301c3c4040000401905164100081801c420381e699918081441c02140306d0000111108000a500060034020340000c00e4141e14409045001080f180b810140007410580c94221006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 801707455 1250 801706205 801706211
    0x109110714011805032d0711060f0318010b101205130803091b060301050d020907020a0b161103491a190501121103130b0c040e0109 58
    0x7100003800350090000c0100c880f40c41e40e222000ba04001c0e0300c82e00310f04042e140c070b45a915610100b054142c4c64589107015086403c0e4070309a1a55a11108082500452900318800303000c4a0040c0309540007031486138404d00d03800761422000e4041d072800c4903694410648100440c002d2710103080da1044040107550544180000c85031210701c01580034066040c0d0050141a0000420801050200304083c004c20101c0700007640c0020102003000380d020074020a5000301003ca0380001501e84100b000c2c2c2c01054900540b000010107444d1040004404c5410b0082400180a110704095000740d103009501001e401035400d04007800c80c1041e8880c40003a29486030041c1c5203940b00d0041c0e091080c1160003e1101c00c840d45401c03880c00c5000501400c00700c040074071150795422401800c090954940c00784c8040980d50740541000c3c010b6079514a4031041d0340501340e4854422800310034400c003c50082440c092140c0040201d440c0c06c1503e400c000303000c011807a00900c0100b105600d020740050641c0c518003808 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 801708705 1250 801707455 801707483
    0x5090120040627061e080f271b030c06030c030a0b13020705010609050105121c03020d060e1f12080d02070b071e051e0a020c060309010f0501091107 65
    0x109100c20f52040b8400403803400840001113564000c003440c40710010001c00c2d40020002050180c50350a421501d90b40b07008135501c001441240e451060b4106107a4400150800e00010707154180743c00c0d0b903541d0f0f00c0d2003005540502035551604006c40c0c1d0350031404030340840c41c5140403001e8526501024260014445e1903403840341c143d82e9032000e000f16a440b580800c540314005420158040c100500c1412103551400001183d60304000e0708008590390350304004c1540710710300d000150744005101703203035010580d00748400401106980180801403003d07038001080da080061054070281c0040d0901c611090234032200300080c8414006d18411035070007240c269211440b5071f0068029100d6104010f1042040c10200039030f0799007001c0e00d618400700490f40001003c403403500541702071007a4003100c0d90f4075544401008250610750024410140144191510340a115002c101d01d60030036915034070680d444414048080c50a803040e1130040c482000e0502900b51090b460409610800602401000481c029 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 801709955 1250 801708705 801708737
    0x20c040218100c17031b091f030f020a050c010e060912030705040f15020f0c030a060209030106050604060503043c0c080304120b0108030306090c0a0e03060a050901200406 75
    0x141c94a220740103a212248138200c501c2043e440d078001c0b5141000b13120340c04024000a00440c0c1520309000002c1c0003a00b01c44500000044840c0c070a2001008041d02c420030000c0d0000303903001a148181132915019141e140385d662103820f40383c201807104c415a01800420414002c00102040c82503855040c40ea540d484194088406200316040b07002d2600c000000050342c1084c911501000c00403e5094600000010700310a03103500d812404181d0541c0070061081c04200107034002c1610a400500000742641d0301c2020440541055100c02c0c003103500481004140445004541803107105020146540040044810482c0351a02c51041085590b25440e0040000c500d4015029010000480b9140c130360742d400c0c80030b484602980440780725070541d000140800e00001170306d0240f0801055400940e030f441042544c00c1d0002d02d01d003802c111031880c0750141a1170910201d030003040c1c01c071800b050524129502c0d40c02e45410520050780c14010320110540320a6076001e0304c09071400c900d0000c49030580024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 801711205 1250 801709955 801709967
    0xa051011070f1704030b0f0916170109060606080609150319110d051e070b0406030e070308121602060f0f06040e03030901020d05130c0302010e062503020c04021810 72
    0x2000300c41030100002c01006003d05680c00511a07610b00b4114600c6548074412a0b032100305508008103402d500c3d80041c003010302100c0d408880c0726894000040d01d241603371070f91021b03201e1642c08180071a4400090110b181404c1c0c503542d5000c22100e507c1d094580c84900400d5807034150b09449041068541d442c80e007004420b649190031014001e0042110201500b08651609401505100041c041c0c00d58101184008a00d40c002c40e8500680c40b030906150500c180c02030204040e04402c0303802100310210000d45000090019841014001c812a1401410003848040810b282006562021081040041c61249290b5100c02c4881d0140d190391581c0e40850064423286114840b180400310800178203d50550140c03c07000601c06050205454644454044010f8081c015150544180c0240055405200c0c1c107020b251014104c140391007000700c1c415400014098904440380303090400041071560410241d02c43c0c540c01c03142145002006001e04022215221046001e941024003000310207001d08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 801712455 1250 801711205 801711233
    0x190f03020d0903021e150402300127080a1d0a180b040c0909150e0103050d1d0a03021203040b030c0a0f080c070b0603011d0a051011070f 60
    0x3000610088000d0f28010303488840c0c00440c1c40746803101c2150341c07046010000b1754120540c1e0b6000701c800540c44540900040021089400d00010216200c418041440c5e40c084243c90359180000038450f00b2030000401c0c0483c03030031131480c070100382c2c1441c19012588403c12160b06c0c0042c0c0c285003212401d003481d00203610304c40c0a4004d600c182082000103121844151a075004403071110f003084020350700810003040341c5115204070009010170005010701c00c2d0a5009950894801b010071102c913548440c0070b000c28800760030841c1e842d0480120b03421540e4000e908045051403414240710f419052002080b33200c0030314800a886003001f494a08411035040c821076015203101c1800541c1e07847c2020344104141d2141034410700040e02c0311100c035452031288500f203004200d4010424900300803520b680c0004c1d940a02f0b8940d040d540c8030061080001ea000c0700310455000c5c48041c150b4007006013402410000d008000000c16400c26003840b4480f2040b204680356250f2040c640c40294489003815078501c07560b9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 801713705 1250 801712455 801712477
    0x501150f120c050d15060203070b09070510090302130b0f190909030c170c0303040f020424080d020102090604050405100b0f13050d1203231f0803190f0302 68
    0x310601c0380782d03664810003d003410000030740140050700c030101e401c00300f0b01e10f00d105000c01a0030511030349001400146605402c6500c0300e00702c2d20318030f882d038001510502140030401c2c08a440c801c020001c50800e180c6010408510180801104000001148001c4000d03800c05202c0c140b01000c603000382802c40381510140010341d4040004007498a009031041300f0017407043c0c40503890b0090810034880074a044410481e0080042d60640e21b903981c0710810794015810403607016448040e03080c1c1c0148a401120071001d20111801207503480d0844050070141c60903520341c116401000381180648940b03040f5000c9a109403400120342d901c11105c4001d00300141c2051041c5200018214066040365000e007511031013019100c100f1a5560b01000305941c0c08460082c0621010b616181015020745c0c018243d00c42c8082500302034860a003a82400300c0022a40362180c4038110100011040d14258160090000e42d0025450b11042000040c200814207030030390308021002c00f0340641c15100f07030180c41c0b03101c04c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 801714955 1250 801713705 801713711
    0xf061f0e010f0c0506101a21270d030c0e1c050c120a060b04020a08190b0d0506090c0105030906180a08040e0402181b07050a0516060e040501150f12 65
    0x448040049032041034843c10210490303407e0401e1220400c10f08603241c144004585420803e000103c21544a20040040d42c014036003040d0804094031003180020181040d002030300e000c111011005d001c40d02103d0100081080049030300965803110483d21151280501c0c1d007002442032481e00070f01c0d00c280e9045107500403000c0301d0405003040000494034007483c4948400e010040b4803078107000c101d00a560107400082c148001090741000704502c1122070b8150f4440c040744180e050300200754440140c00084546610400411800c102c06010003655420309107400303461420b02c480c0140e91210702400c810b66190607181003000e540402c110450100790701020300c0e901e40b03607500030003404d02c00100c84c160301541000481d40b8148444c0900c0314450048071550550012071820002860f4015120407680c43c8030741740b07500c4045581044001d10414248411606207818018010b00800810242c18003460615006002c4c0c0b180304a100598000a4540200140c0c41d642d0121800f41c0641010210759203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 801716205 1250 801714955 801714961
    0x1209041a0a061701060513050d02012703020a090603021813050a0b0702010b010207030819051c060302011b051506130f0203060f012c1201050f061f0e010f0c0506 71
    0x10b0822001d05105022090f10b00150380c0e10030043c4c44611421800000926070b02d14140854501440300340440c80c018034103550740c61910b40549500c08015900d0702d162100499040085281c451601c2d030150182d0745090000c5851940400e4099034500070100701401188002140c1c2d224258460b10750a07042011500c40380c50505201e5a00b410685a580042d400d114494100354000985d810031258003c400300d02e840400401a0614036044111000704141005460001943c1101c2e594000040f181c000440a01e14400034000125078801c540484400c400c032007002c16004121109001c5801e1190310f41c0355550b80c0001c08040103c4983c6a01034603141c0d08044004540d4099845440c0654040008a0240b0010340b15282026055102444900340013418600008600070030040b000d0980402c002c1074a40040c04d41e8021551142d02000e003400700301075407a140c07841044e00d01d02c404420b82c208500c030000500c10450000740d14140074801102241d1f00b40705001030070f4400d421909541e400d007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 801717455 1250 801716205 801716207
    0x819051b0312030a0b09220204021c0219020d08130615050d06270f060209030a1707020405060a051309050c120105061f050a0e1504060810081209041a0a06 68
    0x5c000d86801155004001010f02100800040c1c94803294100742d000950b071503080001035072080d070041010380b0340c038084d0132b0b2686440c0c0080e0409a82d02c1030300c10004480020000d103805841c0540004000d102c81c140202d0300414426080c4e00717500b1180204e00036404404210b0080c400303510840c6c0142c522613841c030501c40300381d205009101c950800d0784100040e141a90030507200c0307480060241d4110180520015034654010030417004080c09031144185241c95031805810925070340a0350560000d41c4104500d0180700b040c0c0e00407000c640040b141e60610000c50030b000c02a52000f104aa500e8900105126080114801400009001145010149100b00c1c041c010680e401806040c80001c1c4080b50501030a444891800c00d40e08c69040c04c074501c4040b42c150034900c0d00c0580002e00280d0440c90751940c1001040980003a484541290038103140b1041030b00002e40c8800d40300e420090f0a05043c3c00341000300c130f002e2041110003064041089100d4003c01c245d28a40d0ba902c40500303c0002032003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 801718705 1250 801717455 801717461
    0x3060509070f1d090c0d03122a030e070b0315130506030c21030f030f0702010c050d0b131b0f0306080d08040807050d090819051b0312030a 61
    0x340141001e640680c1e40c0c91405410604003401250100d40e40c0c15000904a1142c140065024070602d0407120080301000201301c60b90070100094000036561018a048a541030044c041600c4080d100ca100040d02032604426891740c80014204054071010b050300402010840e80000d04001120296a81010240306c50382e0980111090301440b2840c3d0080001c2690307110b600d200c7d05001d0007600b017010384141001390700100f2040200b076111800703498070320f200e10030806070500c0c01e598549150340c0c0c10311a06411881c1e600401503c110381c10010390b04201544070054844d0902181800300d41c6001040c00220401c04143c04805040c1c5801d00046050300d813520309558810007600d0300d080e41c0c1c0030703403000310b090301d61501071654540d11910444040700c0c80f926500341d01c01d005504043c00c0c0b0b5036507030ba034030300f407103001c10b06c40d40040e0417024141302682080c89203002506c586041d00041c280182d507082c0e214001c21a002030403119070b40c030b5203c481e1420712229032404142c5841342c4e600d1900020704001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 801719955 1250 801718705 801718711
    0xf0d090906060c3203030702071703282703020423070804021c0507050f0d03020618071e09051302030a0204050a24051002120703030e070b04030605 65
    0x25030781070910008942d07000e0404001080d0708400701001c0c0507101c2d81d101a10b40c101314041030b00e042411940724480907060016500400140c0e028205240c42e04480921803a0401c80c040340d15041040400c403170b801c0f00c2e03400b000900000b03070320b4424494035901c0a48480d52441c0c9413140c034103040e10310180000741c0c0326040d82c1668400c8408100403034140d804412800d013000203402507034080d480403442c05402900d01c03070340c4148014004500c000c840c40307001250012125084400354041130040c00700f232412804024203508207443c2000d41c10481d0700c0095441e50007501c1c90b27500b00ca0000703072007a80002c180030038405000d0f100c02010341030700c20044040041c1230a216148400c0e1500020603241401508040365031074000f40100382d07244040d02088000c12025081648050b5540300300888895016481c40d01604200c403400e9a66140105105040c8070b440c070000b0454000e81c200c904c90450600c180c1d0f84842d090718000810360b20746d85245280050701c1d0001c0811181c08540007007045001d8015500c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 801721205 1250 801719955 801719969
    0xf030c03040e09010219030207020d0804030623070507140c09010b0a090b04060f08062409010201140417070302070e1008150621070b04080f190c03060e0f0d09 70
    0x1d810307901d00c5038240c00c0b4002c440c1006c0d0804d00002030103003098445e40182451600040104040d6a4a81d40c5d0146581c09a030049407401c2e219201c030401400f104800c0c0001d50402030455a44c0e107003428008056216884004003029074440003000c3c0b00100304075203011003a010b8001915941c40d070102c171445400a8900500007140c11101048100146054408907005d41e101c1c440040f03c0d452007911050b000078a219001000340741d40d02d40d56600e8856418036149039548450780c42400b00002425540040e0710038000a035040d09110004120030400c01c001461144495150040e0780340803030034800c0907402104c0010f0040b0170f00595190254104044504200407500008110251032000b40001c842c3c03143d102408401c040c82c000741d10343c0d586502d02d4140055510040d00c40c0303070080142d00700d900700030742c607038045c43c40c00510510820111002115544880c2c6200d043d0356078401d07440f402c6010003040c1c40d46035210503100b0b03101082002f1041c1200810303203503402e40c03c4c00c004100c9151845000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 801722455 1250 801721205 801721229
    0x4060203090f03090619120f1506080405070b030408070605090c21060a15050303043b0103020609010905030604150f06060816050403080304030509030c0619110f030c0304 75
    0x2001c0750b40b000040314003603003020300f003182016602100504d81c80300400182041c030001404800f030700c49840c89030b994a01c0d0b0742c80c0c0c00102d411985140d000041e26a821190034400c0001c2800003280740014208104d41015150b2a0782e0742d00c51030004194000c44900034001c0e401e0009110010303001007203142050805491840c400d001d03d520f404e0036100556403e0b011500203402180c2024540d0700006011201c090300c00350020344d1040803030b10391391041e400f40058246c03c92405501c4100314010806101e14400c050780c0084030307a8565032520f00c0c1884024400c007800904490b040e4041d200500040c034008080c0c403024541030800890100528680641040c5016236645801c2c1c0d00b0b100d444180c41a980c1c41c02c40c20f0340c543c2c0e90304840c495500752600030300000b4040000020000001584200c0c402c4e500c01d51111801c0d018149440d4180391602c5c45820140b0120403105000c84039820fa030016860708854001954180b10b040a40307040d140307410350000188001d50301d000040180100d46505c9644 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 801723705 1250 801722455 801722473
    0xa050412031a04050601050c031305030d020f2a0d050a020111030c07140d051915090206090f120f0a1506080706050c07081009061401030209010b210406020309 70
    0x840c02c807010002c481d10900c504680c82c6010b42000e42c0000d40c8031406042c81c030b1a02c1026581d42c0e145810a80303090404440b466800d0001e03080c144000c0070080714900007032807084502403007991102d01400c07150702c0905c071807406609402d04a44059010351001b40c9003200d800e0f61802d00b40d480d080905c4060380820200358a118203d04000100d80000c542c5a01038003000d401e09066540c1d00440308031159220490702d0315440862800d10202d88071070385540d2141b03c81707649490040d90a000c2900001c4c03006140c080d0038405a01c0304821652102c4080f141e0110b006e500000090360726a111004002c1e40c4102d88282542c80c0c400581f4642013405502c0f2046c1d1800d4160721401940c0c8580518030702da4111550410130140100e0281c280380200303409540000341c56005207460880c1210030146c207a900c800c40e502c00d00255100d5403a01040748103824402d50706503004910400010700c15299a03072000100070050700c0d0300320b041195003004455402085e04203030070940f020f03420581721b03100300e40945060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 801724955 1250 801723705 801723707
    0x6090303091211061b070204050f06090a2306061b160e01050607020d080705010e160902090a05193206190c060e030c010f050a0b0303250b0a050412 65
    0x30f80d05040080002840d0b1952071070303c12002c204444820701a4020180820001a511405000e00c6001c200c90510040d250000c00c102d5080030107095036054501d000b0700c00d0a011512742041d0640f881641c2080f4880c0c482e00f0100c0c1451041c40d62059088042d08a00e0b003c1c50004030b40d92040c007250301d11040070039846101c204d003010028816641e00c9842040104010308241c12156501400741182a003080d41e230f920b91030300351a95103003031584507004101e004582058102c00e0002030402d0000031800e0403000004191a821240151442490100c80d900c0b110382143c854a005400040c01d0041c03411108400c500c001c4800500c0c00d0140000c90305140c040c0e08000055030801085c190304090003200e0f21200742d40d40c1841034401e55286881d2047c2c2e000700c4104100520150b0503442c00000c0000e4003d50070422140090541c03140142481c000803c1703a075000065501d4012030303910142d00e140700c41c002c100c01580d64002c01409001428100021288281d0015100c0d50081001c3c094000002c84 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 801726205 1250 801724955 801724967
    0x10080610121106040f0b280c171b010e15100b070203010939050a0618050405010b1c02040f0311010201060503100b03120c0721060903030912 62
    0x740d107541c250900180400310341030088082c980340000d0012464940c40d80042444c1c40c450b50004802140e00180c03404103e14980d40d45924100c9020f84803205c04401c0600030700c0640c0682000d040395042d10b125041c0b0b003111030100c407c5200b41c0d010105180c0407080c51907018209864080c0c40c14080c003200000392018460a07107201d12000ca18070f4000c80d01b8042850304d150003184003660159a101c00000003d218407510911550701510110100d40c031f030490200e040030780341c0b0500d00207541d482004c0101da1511601842030f18510b00700b6600c8144030501d082c4848005030701c1980e11505007000002e08034601401840302120340f00700052080b45a804840581c420ba00c42d915003071101c403a04002140c0070755040000307030300c051001003080c136034450002c1e2030880d8000000618030b81c0c41e840c40b102880e080107852010360014201c0e40c14000f1502e0751a0300c0b03100c24400c51100c040d20a01c0e508804c40354500962907981d2040040000d0011803c0060040510b800c0449445404005003040a40544 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 801727455 1250 801726205 801726209
    0x901060b030f1005090114090603010903140a170f0118050105010203071106090405040b090d020c0d26070506010303141614010612050102070201021c020a120e040510080610 76
    0x100c00c14950b0b15800b101003034549005107460032040240c0c20100e4559145613085000301b40a00074580120a44002c0010100c00980218400d031300d89644040065000203001c145000b4103c2c04640b10002d1003c25112000f100051001051843c0e00b002049500c02d60501e068640c14164000740b0001441c00c2c004851080c000c450240c0e00600c24030000401d000498840100c014280c0303400c1090f1500420203440041ea01100d0507400303d400c000000004100076040e441c0b0138801000c0201921002c10704801242d84007425022440c004c40c0484098403941901e082e401c950303400d07550341c40b47c14101e440e90000e0004a0010321305941580074890518156a0925407501c0eaa8440d05140d648150284410b806d0100d03140d501d40c0030000d40804284030b5035500324040c030000741c0d5561280c0300082c00d140c00b516034040b0300d0b06040203004007140c3c00903212001d10791090020240c918410010741e251203400215581c002e0502003000000c482010214044035101d20403142c8948803090100e2200d0124 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 801728705 1250 801727455 801727469
    0xf0b090a0302060c0a0329011202130b0c011404050606010e09060913050709180209070804031b020d080d02071106032a1e03100f1401080403110d02010605010206090106 74
    0xc0865150091000181110a80d901b000a0f020090088042428841442d03010720008409490141540c20000300c2c007040541200451410402c61414100c2c10454015201244400b0031100401c0c5825404141d12081306900d104580c581441c0035540d03401c0891f9014001600110040e10506144d1803841c05108014a6990740350340700b101c01c4507507a5a007a01542c092092000010b603014130f5102e800c0e4112509440b1005a0000740184a0365110144c01d00c0c0400500c4020040400d40c0f0142c070880f070700d0040c0031121a440041c0001100348040361805004c14100148580c502095640180031aa2280450481c0c08800b041041800c0c0402c680032081c1000220020742e4a04c0d10420581500600c1201141060300c10f01d02d8011540b200d80800d03080e80000414444920100603a0a0007070040d083e08d0308407103080c0b4020650b05811400e140341809840f4012608050142c03000c80340440781036040b03405841540d0130082c007a180502c500d50150240b4800318210000602603001603540e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 801729955 1250 801728705 801728713
    0x30301031a0f040b0624090415050901052202040e0103122d0c1707200a0501050f09090a0b18060a1e03050f10050702010b01020703030503060a0906030f0b090a0302 72
    0x80c0d4442240300c1c0c000034406940b00648030200740046031040b01b00f01d820303003101141ca600c0701d90010034082250070390701214a411606520070132203550b81c005028103460080da039582e81c1c1d5280144400c800c1140c541d42c10740e600c3c00402c001c200b5081b842d900c18100c0380038400082e02107420403010b5450307e07081003038403810307003104402091034203040a513034015000c003880c0c552a2020b2949500d1001340300c000c400381d40d0010000b90319042c0600c1c601680c400c24440564170390003540090002d11440c00c203104440c107104000c9001802030324042c0c161244400007824040292a0401549006010b207100c1603100c3c3c50075418242c030005035444180d2180101800c200b2800e4100040c4034900c00c030b12001c01c030281c5040900030002803802c0c020108100d408000074103040038809094030a0341c000802d01805c581c035119400101d60380c00500d00d81160380500341703590380c0d48544000ca5400074803600600803c50a20500104000807021141e81803400758080700a00d80b280382040361142001e80c07000c1c0c01640 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 801731205 1250 801729955 801729961
    0xc080f1b09040536031c06050d0501060501030c0f090e0603120d0c0e09060d030f020f07030803010518100e27010c090f06090902071b0305030301031a0f 67
    0xd4240e84100100880344616418003034180c00040695108551400ca50100200216910030383e0141403280b0402c000044104924800600d541da802042d505a103507100c02c0c152404288004c1d44038070701078100900706110099041c1440c038041d003000d102d10b90000b440e000c0203100700c5204258455800c5086e9440c40b882601d850030740314600201a02e0070350b1501038403d0b5031008d5085980100704c8500d4030140450030781d10076100079114040001c0c0242c00348205108200c0345030740d0085602e403c0c5a0504061010020940c801c078070302140c528085001e0b108405000c4140940c0d907000d1030488004441c58042000c0b810f442c9520b11809907004c94040204610601c042407a840c0b00c1366005131440740c040c140d08060005104090101c622405c0141d6644640c8014154000882070240c0351800c0b6130b1110f5864503000034107a0081d44104000c2c00c3c2e000c00c4540c10050044100c6991601c204840c140351134480c184542c07290710038401141c00c5c2c1004c6000c131407001d400030320380c80c4150b8a07009280ea80f90303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 801732455 1250 801731205 801731221
    0x80f2107020123041e050307030308060607060e0d030e010e011b0c030e09100e070807020d0c030c050610050a08010e0c0103020913050702010518060103021e03071503020d0c080f 78
    0x5002c60034200300454900c0f03464200a40480050002002d046003420140c0745050001190303881c141e00030754081e8002c0710b01817010a40000c0d1103500300d4816544c0c42d640d12900d007000c60007130952140222680c007506002d2104158035400120342610040020030803181400d02c0e071800c0303958850385854002150130703203045444d0159400d4403015010b81401c8942281c1d0100049500008407030000315003000f204244422002c0708003003a4440428101080d80d420040d0001c1d513912528207001c420071518140c00c90405101e1038424000310f81c1301003151041c1c103111002c0743c900d68403401000c0c00f9a485002c00a054841402040114121040500750091041340110060341c4282e00068006041d000d414407107a40f148100d42c820009a40001000e041071410800e5500240004d80c0081d40400014000b580e074500b00c00814502d0001c4c6050900f40307103408a800c4c4003040d401240449a442c44414080f50550000e10044405400c204241420b80d1804d48020130150741d01461510114002030b241 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 801733705 1250 801732455 801732467
    0x504020916020f0d0c030e040507090918060e0d1e0903032a0501050406051e010b0918011e0f0b090f0609132004032406090501080f21070201 62
    0x6142071040e01c140c14686521240b13420324803d0b09038002403440090400345903201c0c6418803101c1044800344442c1c03c01e0b18006041050390700500300ca2036510100c9000c0e00c1c1c0005c02001e4200d5100c48c00f88203110144014940b52140711a810340400c000003108410400704404910482d690354903014a01825a102114902c541c02c0c0c0030480d81c200704040c40d080301240d5090341125480703540046240d10741440c101c1c0c11341c0c40c041e11340c0000c04c0008411694403110020054191941403048a860300c00c440001007030254400c03841680d1928420020401440080f849401502400c00070001c140d03583c86c02c400b0416051041214904051060619502d451117080d01140f40041000c0e080098180000d200d014040e665180700d141d0b90300d040c82c800c1c40a0804040c01c920351078285820f080c80e60704c41507081814107615500000810403022030098043d4402c0000c0d007c11001041250384890b00280d40300c8051628404902c0b60040c1c94200c2201050040d0603114015582130070041107074019600703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 801734955 1250 801733705 801733741
    0x1293f01030503180d1505070e040209100806030309040207080408071a0d1a06190207240804031b08070218060f010c030306081606090f1406030c1c15050405040209 72
    0x1000320866000008030740342c0041801c8401c0340d0f01c80000d1a050840000c0d002c1880c2211035402b95005115282d445e82d1984801c0c9500240750424500c0c51703a541e80024114401d03840e215034054404070b40708041c4141c00c00541b040c0e0303650004840b1700544500c03000d10600350440c4015a207000401038101340c85420f030014042d80000c8550003c0b02c101140000e000d42d0041301711204d40b1b2281c42c0300c0025075903040004078010024046a1a03003201d4011410071003100740702d1140280400500803e040521800035a0441001d89108205c821400d00c0d03d10f40e264844401a03115204000440104a4140701961f0140e01c0091488841c0c110401c010746000081080540905036540d10024034500c007449a820b40031010300b141c3c0c801c00c0c10040043d04c0b400761608040c5c0c04080301c003030601034056011a4140700302000c942007900c0c1c0d540c480a0102d03502c150700c2442c0403140608011f0381c54440742d41000102d00c0110840216990302e643c1408200c80c4c085901039400b90011004c10081050350780a000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 801736205 1250 801734955 801734959
    0xf0b1e04020d0602190e030106060e03060708071101110d05010b1c0c050f03151503090304051302071406010303120e0c06030705040e0411010f0801293f0103050318 72
    0x400c0002c40e0883d85c40001d01c402c810000b0032507a00c5c1e0f01245103400e02c5000c0c003502403801c020341198608004a5a6410010410f00038400b04401042c003850051070030707440d00c5403448000d20410b0140c901c4041c861b0881c6100c4024117081034004682051034200f600d41156407280445000310303030f424140b40031303021404c110307030510208218030788507458a01c0c000c40c454000b00320911036000401042c400c030075180603401140010b0900174402111004022541110821141943c80b59103190040f1300074455910300400da91b0300418605100d0402007025812240241c1b1030840c3c861600212405851018030a00410340000e502c070440c40c9028000396800108919145e4241b64032a21200040304e000d4405484040015544603065030307100c07041c003c0e4120325103021901c2c1d52501d030601c00451103425114202c0011700c3d40c126080c3c1c0e01071054981d6140011103190b00400400001c50009505001078610503a945100005841c607146d0821b0480e40d203d00198500328611081072000306240345d00b66 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 801737455 1250 801736205 801736207
    0x1517011211151308151003030c080d021207140c10050c0405030d02100c0e091815190609090506010b030a061a030f070f080a11090306040f0b1e04020d0602 68
    0x10210000a00141c40c1042401c140b0282040c1088003103032800202d44a02255800c842003044140140d85181130116230745070030800f010028030f103440007540c0100c01d2481c03c030500c0400d00c54540030408000601417440c94a81010742212207140410600c0f84068000d10b075444621001e44240c402e5000640c803683d00201103051640b54030002c0d08142c090341e0621f0040e4001198184004418030070360050b0350590400034201d0000e840820f14400d0f00070b003410b0341075405510100910b0001d102034440400362030341000c810f28002c20b88030002c002100118141a2400c070340481d2014082c840c0354060f0360042d00030322081e0b1070094810415880180600c0a080e1902000039035070751060b05208151f05001d940c0d5850303162043c0042c25102000300804100066103000e114619000002c580c0c02460117103022444066a4042419038071a81c004281c0522400f4104014040d640b0303410002107101e02c1d111003064484600301540c100758914006011900325010400600d030410800380716503c03480c409 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 801738705 1250 801737455 801737479
    0xf190608010212040b072c040b030d0206010f080127031e0f03050a02031306020a181203080106020f100c1101150e070906020a06020a03060806011517011211 69
    0x81401d90300122845a0f0b00040340c0144420001d010780e02d10343c4007802d850800c2020010356040c9a00e5411921000708180c0071074110240b5499075013003150722410240840c2d480d0190f24100a60355002449440c0303010192110100c0d600806001c0c2d030014214041d1000000410b03074603520003074a0290307000c5042c09201d0003074101034a00e1240c404820041c0b519160b06950100d01c000c4d042d42d000409a10340c0900c1041000502d098121740c0c074115640200700182c5a5403050810396100344003641102c203600304203400107004030020041c1214644280c0e60300035641d030303140c800341e07651419030a0002044c1c200c80d0387c64021241a074400380e644421840e10000d0300704080c4029085690f10302c0b0030740c00c01c10103010902401c1c1c10500440e400c0754440c174020001510740903000303441e012240030042c1050307000200c4c1c0700140d1182e0050400350030900c058658650355007008a52600541d012480840c00e03c030f010700b40162034000d800e8104e034030850a45025181e180c0d2514503e1038440c1c0d255622205180030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 801739955 1250 801738705 801738719
    0x702030a0303051501050a02030a2a11280e0a1e090c0f0b12040204021b24160f02010f0e0708010b060702060702100201020708070b060103050f0f1906 66
    0x40d105620340291000901418105982006502c200038180e0600c41c0400900d05501d5000080703074a1480c05151007806605000c541c041101602a203543d0100f80c030101c840140b01d0001501c08039810100d072084e04460307042c00901004070403031035410208414400100300b458806205143c1c0841c5000c40014050740400810900132420b2a04645644d900d54207041048481c5c60b07520050020340418140e214500001c4100c0c5100d81003840e01003c6a03500802e0454135503406031110740c44640007000000f140c4161041e941e0780801d401600102c000a82d40c04100700c0042800d0203030052104601411400c00800c0d02c20358400d541c4982150340c1c840014044901c1449074046010201018001040c0781c400a41e00f52001400900d220f14070401400c0c00681d946012190f45940c161644282160b03454020f03402030089540180000c07034002800408c200d0001c0001c0d1241800b604c00300704544800c050901c0c074150403140a03071040200000b007620040844d0510f044130741c00703171008280c26480e0b40d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 801741205 1250 801739955 801739963
    0x10522030f0308060d120c17030133051b10090c050a061e2601030b0402130504020114030907031a04110121020d0906180b0912040317070203 62
    0x4010766072910300c006030200301030b4000c03000c541041c011a99050b2444242c1c44400c1444102d40042040c452541003000811908155240240284441050312907956a800080590658480714405100400c1131040101a85003102c01e415260b030751642002407020b114655194200d0000704140315001d2501c00c500950700070060304500c0b41c805403408a1501040c00303041031141d0400c00600001044a0007081c0c09009200000d0340b1a00d09038885440d2034550802c9903a50604099022030750070004020b01080100990186109580ea0007a47d001040310743c040719404d890081c00130b0110701c01600700d505440d02031900300c107000c0140c07207040d5901e540702602143c400e004181d0201c00402040280b000c81d4110000e18082820010381d44a00d40d800c410003202220f2080c0007a80c1d000c5151110103810398044100558000b0003041040780200b450b012030040c003e0708803404e5200724005000b00303102080320410700808840845c240b5081da500e040c00d10340a48060710341c0000038170501c0c0140e58100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 801742455 1250 801741205 801741209
    0x11d06150c03070f03110c03191406130309050105040b0a08061c03080412090302091602011b030212070e152808070e09100b031801020d06081504080702010522 70
    0x850704884d5000c09290141441d119804802040e40254681070125200454081880401e84035140720b4040c0924060400e080d120402403910302c210030400510102414154181e24080d03129801aa0b80d44c05c011100c1c1d101d1401602502c55040c0134195000d400307184141c1d0011001002c0b180d0a06505e4494030008008510640c0000d641c103050005102c844110710500386607074039040119505580118600d90b80c0a080a01c4032a0b9402480340300901c00e500ca08a00521101155541a49100c4c010b002e0b400100c401410765680c3c0d00810748150250328411a440c1000d40981c24084403902e903444160412003802641210b82a600b2081e5240d01c0c002400e0110152108040e500300290000c00c11410000e0071405a12040d042c080d410840f03240080403035001a50207542d13640c80c000b955283d203083e80001e0509600105024400340003e8006030140c031140000c940c2a1a41c0100700711707210f0410f85000c1e003903010800c030601c09544140001c0420200c0400074a10740070004c0403c01c860025a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 801743705 1250 801742455 801742463
    0x12070923010806040b030604120e15040e0a0e0d050f090d0620041d0604090c03050105090d03020301030c0b130308120a11181023040905011d06150c0307 67
    0x5414411010340c2c1051a860300624203032410001244c0710000302e40d070782c0009000541a101060000b00080d4170409a00c04404000f40002c0c0d50301000540851650304030340a03441e5101017150014034030b00705038819078480c40c410000814401690b12002c1d917041c0d101c411810600c000802c060850381c2c0307660500321060742c0707c0d00340001c08076507524202850043c0c110b81310183c11002c0004200c0e0108081c0303070000e03015440840300791640b24080001c00805001d08002c1011301414400402c2c0141944020322842c1e4003c00d944070b804035141c046007280301c01d02000302114402901440b144511402804119a40f1a0110300503603c2e62a0426207401680a0080d850045400c0002044c100d000d0900b0907201c0596041c01c111800e041c106601d02c0140d49a0301404000000300d500398401e502a2031001620042240740100c05188400154061700400074518204000062028070704548000c08a5070101d02c4078035900c5020810143d40c81c664000c80c50200f0501401402c50341c01c0c0000c0091a1203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 801744955 1250 801743705 801743759
    0xf06070c0f06230403030e04060e130b10031a04083105060a0507021009090c1e0507032313060309150204050d0303090f0c031a060a0308120709 63
    0xb908030010702d90b06082180080d85101d405442514201caa0203403030903a54582001d04001d034191020500610103070780561005e00f8000107100d400c0480e040800701c038900030744501071603035204091240f600b00e080c440241358406030100c042d80e9100000072250051b2041c4a0340e803070948480000c1c098104648105444a00c20030100342800c04021030601c01018180c80d0642441210f281c050000c0c0203510019004191401c41040418401e5100c0006041508410060510140b030b0042c082090001c000411002c03042e44140080d00403c15a42e81036450742c2c3d03142c18480b807500c03e1041004060203068a88a0a014841c40d89840c2d04540b03010380402c0d40d0014641000703081900410f90003031220246e451040009200d59181e1081c03411040d509400c000c50780c1c207601d1030200d420310b181d668003a00240e500300002c010400d80114440e000ca21609540c40f040e1540300411030400c0300740c84000d144103010420070650b000c40308000e43d4801c48a09103840c81d00e90710144400214843e010a4802041e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 801746205 1250 801744955 801744959
    0x30309192d060f0807030b0d0b010b04030614010308030412020a02030706080a0513020f0d0206040515070c0b03061305060f0d0c050111070b030109092406032307050f06070c0f 77
    0x7404550070001407002d407400c054803061603c00944003400142009040546510582c0019100c07003400e400b01c19409940c141355983d44044a8081d6082070104850f940e0a003880202e4000c6403081d500d050300d0308494564551345480d03481c001c141050500100c01e501542c030a003005654144100801440d95854204061038481c1602048604c02081810501240304c0c1140c090780b500800305040d104140c7c0c100721540e1103400081c98a005940c4125401070001c40000d03070404030f09000d42510f0303102d0800d0303c0c09a512100c0307222040c00704460b05030308200405440c9c0c0481c1401d800650b00100081c0103034800d001114081580800c074080d05695810803043d040002e5640001121803034100c0e003001d031803030b00e080001075031581c401032003921980c1c4c2c1c5030320b140b03020301909040c030006c144080710f418007039960f40c00c0c8404058180d600c002e5480d144030410351900801084590f442036140c1c0400340a406040c5070401c13501071401ca01068001409201d0301c80010543c2d034050000d070604140d000a124 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 801747455 1250 801746205 801746279
    0x302090d0c0e1006032309070b220501090b07080d060302100201050f010b04081002030c04051f1407020918010b0a061707051c11090402030403050d0b0a0503030919 72
    0x11404e60000c01050700d40b03007121080303010000c528484180134914480c41921542585807070800c41d500890700f921000540707414003c501c1c4190f030350b9201105091880e165529401503c00780614440c0c0d07401200c0c1000a900025040001018401208080003401a4990300030582f4034804d01207403400750b90360700c0a00c811740082000c40c50061884030b402518050900703503c262941c4042e9a580c0c205500440891070b840030a100b61400b511014020312602520403440e0b42c0d000843c0221076001c100030801d2816841c40b00412034410940280003518203890780b0700804400d4420f00b210701d417a550784904105d50ad60b2070044030310050010365034130303041502c82482c450b402032405042c1e24180113003040f0710350756414420020f0700c504898040c00103152140c801c051ba0075105202e11a540548000100000c042d040b5000d402048031001e0200010390040007840000c0d907007401180d80c142d10610810800c3d03c4d08183c25600c1154441003800102c0c1e540303810320f91811b07044501d076000b0068200010444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 801748705 1250 801747455 801747481
    0x5060301050903090f09131212050709260106092306030a050717030d02030717100f140d0f03030501030312061d0702030c06070203180a150302090d0c0e 67
    0x10210345005503203030086880c000345c2e81c00312107000f582c01858080c000401056480640c1502d403904031000c0211a4103400004154800c1100e5600d2076625201c04143d480d80300781c100105840400d034001e040307842030040b100400721018103503c18540d251100415a5034640c024420421003140d42d038882c0c042520b29020005100a00c10b90003a8014500e800100b040010481c00716a42c2d9803111060780c9400070781c40d080d0300c00c450303180e00c1c5940000180301d580c6d50300440b4081569075100030200d40e5102c40c10070413031011881c440c0c009095140b84080c401c04102c54100031918100600700710310300220390346604410b8407a420550109554000410901d500300b00541c40e40203081c00c040011a003410070f1030943c45211482d500c500c0c81c40c54001509640208200da13300002641112501c0c80d00800c000d40e030741e000291102600218009922040c01d01340d00070400c0d04c100702c841c0c11010072500004c400a40004036100d5020f80101e60030030100d0704101d4440f000d4109440c42c5103040c80c00ca8450080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 801749955 1250 801748705 801748711
    0x2b3207151b090504020f0405040203070c06110a090e040203060403030209032103010f0b040f0303350405100e030d0c14030709030614090d0c0602251401020903190f0b01090506030105 80
    0x49004000e1039450006c200100d07410f0321001c0f18016166110b41070101c8030040f0440c0010075003860030b40011001c0308008050415420380c0e07550242d5150701c4130202c1c41c0004081c1c400a405a02810200300020b020382c01811502034050100c03a88565200000e070300e59000c1c00d41d608134400c0004010b000110b0074601074800750802c1c20b111132070507250403042c9030710803403521003d001c00802103014001081c080550400f100a0902102ea12004168031010440002da404903810701c19a02201c40303e03103950090407120042d000c00785041c040050070441c06800d084002404100c88075070240156082d58018500500c0aaa00e170001181185048401c0b90050000b0000c0100140100004c04500048403a0501083c0c58588032184e605d00d041c10180c001c05420301000424400c11501c0340b8008200c0300405030040515803610415004000d01b00d205440400b80c26030462102c0040c007100034485100b14900c192003070f030380d40c00960b1168a04000b00303030000c51880d0f41384e8003404000d141c00d00680750 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 801751205 1250 801749955 801749959
    0x91109090a080306031608030d060501030e03090108100f06021509070315180c0603020d1404050a120903080d0606170702060105010c052b3207151b0905 67
    0x4858102044010395451010034000c1c600140000001d545403401e010400c0301103000c2c14112a8140c80301c85d801d45903040040740c1d8155900d80140022550700c07900425480441c95000765180000c02c500441d1a000020702d84001c0c000d29207400a0313003a1a45403c0001041c45a000d031854071403c20901c83e003420090404511a4080801030004c03910711101c0d00e000c01e11904000489140c005840302c0f025203112006041c204074150000303061901500100b03105541000100812900008060302c400001d03500604180c0c003400c4d8103000103074003c202009801c41420f144010310790701c1daa2800582d0004618101090700c5550820049410001d8106000050741c40d070403252a005000a541e0901482124104075000f520501400310a01c90003680035070a10449403d010f000c2c41d00f030204801050400006401042500084084580c4803c00c0c0001d10008248401515100081d5504481d40c10350b800304040100e1103a803a13180c0725560080300c0c0d1030740e507500b01001c0c86d0380545440001d500c414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 801752455 1250 801751205 801751219
    0x6041401090b0409050a0323040e190e0a200411030403260a0606090503030c0d1d0d0f02011704030c12030212090a0516211106040b03060a090903021009031806030911 73
    0x402b4428044000d00da00c00d03101c01a039070b560b112400101c401391425040840c0c4600400c0241428400b41864004000c044a07080c0c8807030201d00c0040c042110078190451030b88140c1440460700191040410610006c05009248046e00f1160312040301441c0c15a041182c441e5222420051503400000d07410080070110042c50502500e40001520307030341041e07104420000400c01001800700c08410345aa0803002425010700c1c060a49070024103003021b40303416030100f5541c05c00c103680f11102c00d40c0288500d525a50f424201100d5a40d4a00340c88800601501810b8080c0002034140c516031031a20301c600540e40090038600c440d8200b88d07003491050b1100001c9020441414414444d0300750b0701d2060922444000c1441c0740590800e1110080c4403404030341c0c0b12000060006611414102940c002c0008071200c1d107407140c0d41c01000d030447c0c10248004000d40c0003003211007680842603000c041c1d1103001c0e00b09000c420300601d05040082c4040e0b00140c0110b66500c1705c0d00240880d4614001002005552503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 801753705 1250 801752455 801752459
    0x2340806070311211801020403060506040f1b140f0c0307031806021e160f14010e0109060c060e01020c100e0f0712060b03060c0702010806041401090b0409050a032304 73
    0x107500c4a00d204c2c2e2070035090700e0702c410104103200342d00c0140a0801e5403050086464a803289010405010140d582c1381c40f46003484543c0c0d40c01806840742c6804a8201030003244911149802540c0c0a000c8030ba100950344014030020069548090003440e0840d10b410240d503680c1c1c89840c01a00309020940608610301d1040700c00e122090f00040d4040d240c88500f803d0400c24440b00441c580340c0815108104c507910101000040c044020b00121420784020104880c1d0348809440110307000d800d0420104e00044030340a00700020741c0940702a440c0540944008662000c00c100c015080e40d0001c000307201365501040601e1642103ca01c20020b002d04014003030728045a0703c11550366074144602510544041034099281000390f03541c00909202005416105070b41741c038003031102403a008001c0a81c080303841113000503d545841c0c4100301c40801c40c1c40c44a50a40d003440ca0880c018040011a07030340080d40c860480011800030804483e400d8440e40ea020b13600342c0c0c8202d4110003481c00c1c00d07010350004403c3c401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 801754955 1250 801753705 801753727
    0xd0804080423030109030e09070f0509041802040e0303182410090e0c0a060e01080a0213080111030402030717030f090d080a110d020d02340806070311 66
    0x101c6003141c0814071441a010740d0038940d07441d14011840026032540c40c00405104141d0481001d0386500e0301140c0c54210790b5030790700041d10f10381c581c1e00d0350701d00040007080203030000c1c5040e80c07040e05083d0840d0202001d43e40c00f540410300315061451654001da001000300044240320700d055565101140d4040c061801e841c05501c1c02e404086074030180302c1036512000540f03403240155131070003c0148010038005403044901f0152113200003400c0f58000c000c05440880d0301409035103848401d00c81a540c3c0c1146030f480c1860b00c4001c5d00401151140310302130510024900d1030074080d0b04c41c0f0300c0c141159160307070b4142407040500e00611584212244080a0766071a810f01000c000d80749000c001741160340d541d111600001d812100c0640008201250201e070f42400310707510806402000449070221002c5a8444074240c0e900d0349030b03101007801a444100490740c048401c2c01440c01001280000907041400b203030902d007410855420641e096030103113003000101070341402620350881c10101c0c0f039440e10083d605 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 801756205 1250 801754955 801754957
    0x1d060d15080304050d08070f1502040608072d050f0d050612010e070306020d060b070311010b0411041a040b030c18090f13150f06080f1912020c150405030d080408 71
    0x5e40074015900105d109000d110701c503214030030460303031010303c800c3e00c0300d00418070500075041070250304009410800000c028502800c4084041009609220070740001c044c4400c081034035000d0003400304039090151002009005028251015100d10045010324040041c041802034150400900e44e06003008442e00d14400b08440094a0b040000541c3d0b07a451100b180340684510780c00800240c10001e40c00040c50703071003007051500c100700e8002400041108410401510000303c03c007061000104000c005120348625103180f1a19500102418a969100045490380044450286c0e0341400500301078203901c05450300803254411200f01600e410a410721042010005000900400c94420201e0900500a400c422048080c042c240203540703941240c003011f0700391b030721a00820b4810800d42c100b00e100c010540409030200c1150f1103088080a850721110b420078404550194000d03a00c0e80c66050302c90800c090040181000000d544901d040181440c0c441040001410484940140400625408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 801757455 1250 801756205 801756229
    0xc130608160f0e1e010b1b0c010e040b0406050d030206010609060512010b070312090309081603120f1404090203010314031e18040509010f0e1c1d060d1508030405 71
    0x480e88581540e80d507840c1040d580c10403002003a0f0382c00c81c4c8000145d00c0500000400d102000e1221203202036840005a566840584170320342d01094a124020b021810281c1c0500b10203100144041541a5580017240c1030358510001680142c00010040c800755030880328000040c0124a8401d00c1d0411074900101c090406024a401c8023500040003c1414441c1c025480603041c5060208000c640ca498080c0540c0f00701c1c40b03074a02a00481001460810201d0100403c490300000117980300e4241a10441e000040c80401005200f03002d003420312400200000b03080600b0340c901d401a5070b5410341c2440d20581445010886c1558800c120150300510b03658809200400304180c029100c3c0d44085c09058000e101c0340d6110740003803801c410400080030540112142e1400150100600c18043c0c9800c2d84510100c59084c0c0742240104003450b000d48900040d06e0754001032503615182c200c41c08005581680918141610b007501c07010040c0c80c0c4064641d80390300410164004514162401001c5407640f84c581e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 801758705 1250 801757455 801757469
    0x1308030703110a0909060b07030909020310030c06030222080a0213060b1809070306120b0c04030f08070c06020c011d120a0302070f050d1110020c130608160f 69
    0x4004a08054002e802c010241660400c02d42d40b540600340b030051800d00a4410009105c1c2000b400040f503100840407542026010380c0e4410680d410521210060352019240444804c2504070000101e002100000082c1c1040c1d40c0c0583d8540030503003030a1182c4005c0b4040d5124807141d0318200014a400242c99a07115410340d0b5140c015512664a20300a000715841101d101000089880600c0500d07071160b500207908490342000c58440701c0301201169120300078868071072060388018000c07038441c02e6075641c04030405080722304d803c1d00ca59502c090500405412606408041006000c0040791a00070010700207a100074030541000d400000c0c500099031148a034024000d00c09041c168403440401240a03003404102c1d80044510314000b035840c1c4ca81d220300892204024004150380c5005064240c09a405c8014080488032800400c04240103d210034003d500c01d683c980311064464488488030000d1003a0005095490303d911942400c21002c07c0010311000785006110b00d9550030611010f4860f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 801759955 1250 801758705 801758707
    0x3011815170313050f1f17130308090111090d0f150f0c080f0c07030c05030309060f090606030a02041e050408031b030c040608090316150b010e1e0411031e09061308 72
    0x4925007910000c5804d081046161f4079402041010340d05d07641c601e10054807a603145c0ca920fa5070078020740d00326a0503030100f00711402d0800400d5050303c0c2403184215141c2c0500c1101115072401e0740d03402d001003020f280c05184642c6405070407003540d800b4420a503120016041400d4103242030b50800d80c0024008200ca64458404541c0c181858812541101519800000c69589080000d4400e540d9481180e0f070000d107000500019001e48070209801e801030302e0141c02802c2000881d820080905052101e010085801c0a80c05503100444e01030a1300682c091010941d0703d04210726413855401a001100115400400c18445044900c00481302100d1051030002d00075241c45110508510400000c1185c0b403145851840c14421850642c0c4403181c2440c804014030102e41006454000398000300d540d100401075603140003800e40003280c25807200010000a0384641b405801006608166030307034044c000f04403c25854440e000e020040c0c0007490071001306603514101c030110707500207905507008202c100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 801761205 1250 801759955 801760009
    0xa060b041802013002091c420b01140a05090405060a08120a02010b0a030b0708070203040f0602060603070f0302060a0f0e042f03011815170313050f 65
    0x8250460710052248482135160415070600041e0042e4000d00c0040344101d485000c2501885440d8107112035059000103082d0404450f03c4294589a507040100c0d0310016000c00149039016140703050105502c08414005810305010000500b41d0640785811241d643d020401105040c0d0003006a03400715504440103e915a01e460100d00700d203081d40d120010f81c0c0700d0000500700780000ea01c050010700c0c2c100d40c02001591440c40800c4503212141c800a410000d806004c510b0561249000c0795000500d4012240340c156108841e610b4030615034000d80044e0080c1084c840d052800b4000240101841c403800d00c00941960005442c40c441d8100410910503118101184640211405007a0b400e00074401c0203c2da160b600310b4505c140d650613181d0001d03406100074024152a06058070b0599108480003800404c0840c0118000c0c00c200480c40c90110f00303c603000a1191116081420720342c85a005151600000641c0a640d90030981000e0f00c1003d90460f483c2c0c00e61201c80f07020061107500e00500607465 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 801762455 1250 801761205 801761237
    0x11d10051e04180822050607080304020f13091502040305030a08040c0e0f041a040803180a0f140f0a0b06101e050a0e0d1a1806090a060b04180201 64
    0xc020403490181d4a40003c01c09000e41240606084450f0049400004504020031400c3c05075038020658402400d00c02d8902065500025560261001d001002d8011030310380040c81c1e49007160320f03800d4040c1d02c1e8000c0c18100080085921620a1404c00a40c206421581c4003500c901900200e8800c01045074000f40038002200d45040042c03028414a40c2542040320303d00c00c0e907440490f0b00b507551030b158510116500161129640c800e9802455160942d1214401d2840306e60300a0003086440c4901418030000c0f130942e095812480348144034485c0004100d62510341843c11030180d40065401003000307080845c00300b1a109602903000c0703800c00042285440240c0e0034100d50304e152106034170480005420141c01034010020340069032181801c240000c01044804030b0201e000030030212461400d83c408074500041150046c0c80b04200813043c01041046516000c0b046884003e00d0707120040e250241700c001d00c0b50069404080d40d0922940103035001000509060b014020b04108000607449005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 801763705 1250 801762455 801762461
    0x904080c0313092007150c020304180b090105090c0f09040603080c0a0213111207020a0506040303200c0c100210150e0606130308070317011d10051e04 66
    0x1910349040350b00b80710307515603c0120003070080722400c80100d00411405020031030804151000da03a800503802800a104030b030154050222080004150f1105000c042801110b000003611a0b202d46840020800003030010407107298410303400075004100c401c0a100301038284008a51042444000d4140d6411002c800308004142c07130b82c80585090004144000700080c0030401070300003402210034140c0703449805200d1045a641400c06595503104000950b90280d4025840d0b80c4403103d401503c400007444e441d40c60034214100e8040307001030794401c0e0080900041d440440700383c10b00c0f19006801d00101064466888100117507851141072a404505072061003004045241d107034540c002d12400708400603144595003035005200d100340305000004c40d0f60900c0d606031410140fa05006032042d82c41e580300e416543e4000c0701d0950801407050380f0143d00021070b02001d17000b032220200c082c2642003a80044e800101c4064440c2d1480d141d1864100300550740c00c01e151125440000780d0101c010940700000f401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 801764955 1250 801763705 801763717
    0x5070f021801170111090307182003091207120e0d050f0f070b0708031b0705070b030103021c02031216050706050a0f080c0a031d010911010f08060904080c03 69
    0x32010305001050800d80b4075031004035414110001d205c901043c80c4041003900644a58640580c05982c0400101c81010030325041c4180c0103e0008011060350360144054980002c4419107503400414060110020010740100300b042c04040c41c2050015038070550349003046880603080000d803d00201041c1e031a032070035020650b481022100300c8003c00c96100d469083c058014801800345207400920a41e034242140d0b42ca5510290182ca546d580e224546011501c0c09030900040105102c540002841008410080c0101504181c1c1320340c0345104001c0800c0703d03192074444604501c00300c14010380b000900280e03001020440c00d6201c000d040c4401e128107c1c0f0110140452180718400140700350090010b1629030126a00c45d040e1b0302d02660305490941c42615a0118104c0c00c001185145110707902c4207120030000500c0b0200100030009490944403000e4080d5000302c000400d0880c550b0700025030000c812998180b01c88689005000546400b100410190035840001042c504240080c021501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 801766205 1250 801764955 801764989
    0x12180709060b0f1c2f04080a24090b0a0f0239011b0e030f3d061e12080306030c12070303080a02040503060a0c0504090606030b1008040305070f02 64
    0x84005804151191a4080d069120519800401810107034170b203030004943c01e03941d01c1030081024190301d50340c0d11420100c100c0e80c2c90700e841c3e80d8801154004d00324064001540d004e04001405810700040d10012625403201d945038882c810032a201a807200b580d043e5440080d4601340100c86041200200f455203940070034901c9552801e202e84a181031032a440c1c40745150565240012407070703900289590f0b00703007000c82e42200f0703030000d0400c41c1010103d84070030003c0d0040300100c42e002102229071080c8804603640d1300c1109515114140300185001291000f421032420a4240060ad40901151200c2804401034080b01d0f0010000307020f0f031802c0284041c0024080e140f07500100600105580301c03c0345010403800035016101098000b0550300a03142500c40c000c0180002d0f481d01d090001c014036044200c0000c3c444280b10000b5002141c0c4103034001003161713032030216106510804100700145d151180c101803111290921010a900205907012a948400206514020740c000921034001c0950404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 801767455 1250 801766205 801766211
    0x51507020c2701050d0f0f0309180f0b03070b090910080d080108010c02010b0f01050a141603030b040608030304030c080903100e010b03061501050f12180709060b0f1c 73
    0x1008190448644000080300b07858096501d0344c89a04000712201c0900d409485d4240030903ca901003490040c081e4210703482030804074200c3d5940c0c5102c03001030b01104403182c4012356801d1400c01800c100d00980c48a08030481c00f40c000340f41400f40343c101501510054030302070300d84040041c0e070414000c92044003500600b42200c1c4000f004100c004c1c020304003401a05455420041030303140f920700500030108114001070902101106080044426030001d1f885030080140c1d2049100c031180e17400d8010008200c40085041c00a80142006400c0c1ca01c091020360040c0c0c40c003481040341580c04019a50020380c145000b00030b135901418811030b01d02130111610307030502072864a062040c00e107601c20000042020000d00002624208140d02c2c0d2104503140c910385504c58908a00e20340c8610010f10204045003440c0d814036461044212000500704c0c1c030001360001101d1510240354003003000c40003c00c030030113003404080c5c01c10200f11640c0c01203449100800402142d2901d8120f400b880503846590404820 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 801768705 1250 801767455 801767479
    0x706030b0d0507080606210304140f0a08210f0d051009150e0c07030212160605090f011103010f21050303040308060406090c020c211f0c0804051507020c 67
    0x181d0340300d403030a0b80c4c038030b200d050b0744004443d0b000341c844e40c4031900408070409107027450300c2c10044d101508000454640d00080611030385515983c0c03400002d01a007811002071982e0fa003242c80400e03c041000d280d50580d603100307000b07050207032702e4080480e48040022000070a00e44c40d814840500d42240d600841da5543c141480c451490302c101070000200c40c0c101800c99183e403110114004203120300e030000741c01604083c6008a1000c0014020600c83e0201e618060f05062031ba2241c500b15441070b18104815044002510781c03414007401000c1d001c8201410755031465160400c01c4103024602c0c403da100b0900600c005484002512460303191042d001801d8a9881c41d09141c000c2c1100030803141584500e00c0c0c5900031076480b16072311a00ca611030a0760024100c0014031400c00c885030302c01c0035401c0101840f910140c072141d803060100e282d00c1400d08070940014206201d02000780c69501d910b40c002c0011503001c000100d00d00040c400184449214102201d460f51b1400302e0401c011070540a4112400c0481 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 801769955 1250 801768705 801768719
    0x9090317010e10060504050616080903010905101523152b05161110090510050105031906020a1106011d1501140d060504050f06030f0706020706030b0d0507 68
    0x100a00ca611030241c9240d55689448056505010f54010160040010b124241038827070790900c03104195018001c0726042004000019007502c4803500d0468442d0001c000e240309121f95402022840c112018040c015036042c10f00c03544015440c091420300748810241c0d10002034070b40381d03108040140160341490790390011901d01c000d100b4a140703a81c2c000100385c2c155988881c0036441664002c03501401810380c1a46032140884940501140c180250300030080250501500da1041405643c411005000160840010342c01102c0c2c059122500940081c4003070ac03001c5030280884807299511020060716400404e00031610783c0c4542c8040221071060300000700b0103c1c0400d100c400c0248510282d2600390380c9060886444010014030140812400710036080c04044000c040d00c40c440304c4480000301c7c0e99403480020103852003640c81c03040154044041c0005410240400c212240c0510000e100b142d240580013503882405115010401d07031383c0e40c4461880e075113402c007505010340c211085071410307038441007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 801771205 1250 801769955 801769979
    0x10c061104031a06041109130609091b170a1709101e0e03030405040c020a12090e090303040f03051305090103050d180614030402010c08030a050105040f0e0303010909031701 76
    0x3c04422080c034071001031000d01d0503000d9241c1c03480d40603000500f0b101d640018131008481081c1240c2d2801c1e15098003041e03040b10382c46180100c90041d20310882030701d0041101d891400c0b00d6000b01e42d4000d084040c0d1009001c0010b10085400e81c0220f40c400c40c6031200b000543d07107005089660b644002408585440ca5501540450303901c00e00300c604e2000503004400568000d040140c1e9141c15402c1404100320900d03180e840551440d110340107984942d074565807401200031030030060310041500318105001b03480c01819070a40c8186008000d510750304007030325400c40c04480800e004042000014203200400c06401c404801400090265022540c41e031a1641e02e8100c05d054044c001608c040510030003103d00c40e00364040300c1158480141c2c8090390019600c2302d60005100b6030521102d65070391b8001440450040d8854416500000382035410642004103442c10740401201c940d040c01e81400403c4c002104590455450100004042c200c51030199001043e0341d2120b01100c010748d0000486116000e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 801772455 1250 801771205 801771233
    0x15030b010e03010c0806060c01020c07240318140f120c01050a050709030b0405010b09090c0406080d090b071e05281502130504020c07030515090c010c06110403 70
    0x1803074a00030030801d40281822a13045412081c006501040032032061f042c454020301a00c540c03034001501d000741c00e280717551030160075074407003078104001c0c0c00c034041145c0e00901c01441c00704481ca414409294400d80762001c000c0c3d80b50002c4c020b401d0a801a29050750104400415130407000140e8a00d007050b40724030841900010320851881d4200030000740c132b261281c0324007445500381c1e407210701081c0c1c00e40d1268910103100400864456585034000c00325699100c1105215414038801020400b41e95000e00c0b050b640d49501c04050350384266240c6050315001f4400000780c4010502085e241e0409042951940c4400200f0313400080c1c22402c02c2003401008030302c0a0081d07004000348241801100c0100c91002002800903000340048404031300c4806841d0014010341c3c08140c41500519150400502203a0041c0d001c0410b40d4410750f8200f0400c00280010307814400105001c1900d494040180ea454440c501e1040c0d04001c058410b0404000103940301c48174402c0c9100c0c01640795522031820868412900c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 801773705 1250 801772455 801772457
    0xb03100320130b090103030507051005010e0601020f010615050c070e040b010305060903120727080303070e04090f06090c0b0408031b4b010209041506021b0a15030b01 73
    0x3480030080c2d40d0301c1030301946410800c0500a01c1d12603196403002c07162178004090840d080e004141c0500300a0340103001d4140079081481051650303050000000e80b4011012501590b00c0c0d050450804c04503408031890304d0061181d090040e81c6440b00c0c0081820880c96403c40036014072500180001e2141d07002845040e2445074045035035588504c48dc42d5524091119210001280d200004040c281326143e4110030a5030118600d24902601c0c4840701200301c1900300c1605588003104004a803a0b000043c1301401030180e804000c0401c05803107100076035003005405040281c485c0c54820800c900780750410001c2420030b000c01d4686480d548155180c1c2d20580e892905100c15060300404501d0103d180c042d2110580320548a400c54042c184c901c42c1c01801b021b00000d92840a159105021040c0e00350f81c1c00b511000069450341d0031003c000c01c6440c0030082c504d0310a0004014042a81c0001e555920700d00d40b0000c0c0c402054004000035500041a000292121000d018000055401d50030496001d002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 801774955 1250 801773705 801773719
    0xf0409090c0e010803040614190c0b160206040b040812010308040f0e012d150c1709060324041404020a05061c091505090d090501030507090b03100320 66
    0x244201060b8480801e02030a855604108000c004807030203100740e088000c403804001350401942c010300341c044450300d0703001c0004914007036002401c000707072240d1482e807001902029020f2a1403011009682e081e00410007015010a400070030280710100701910ba200108454010b411741e101c0c5000711580c1c00c98851040c010304918404900c40c821000041e043c1c5039074150703442d000380c840c4005084207031111800703440e00820f244000c252090404481030340d04945441c1e0200c0201180f0342495610303410020001110000d204445050b070b128012290800030070310310740d0202400d608282c810010802c0300719502c50f10304204404d11400620119114500844a00c815242c0d50002d22080b446403114403030324847c168081e003c0b840c1d0960f00c204a420b010b0105c800d01c452a59883c1021100c050754004c2c45030388a108a0109a5403204c60100a800203207428040d42c2403c46001d044d140d814003850010020102c0080d0b042840d041441e0300464000f002c2c2c020040840740c0c40c3d01c20501c80c0d0500d80c06102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 801776205 1250 801774955 801774959
    0x1801060c060902061905120a060b0a1209060518061501210e0a0f140a02030c0d06020f0c01020304021c0b0f06031606110f1b06072103050a1b140904020f0409090c 71
    0x5034809e040448494003419840e000611900700c48041e2b203126424006c65448880402040b55403007104d200d00b100150321141d074490b00c11841c1c5003800040c075002c1100540903040e003040c3da1040d0800c030071114615028200144c8081d40c10080c0846002800c518070404c03203007405020111a0801b0128007c8000c1454034140e10a400c0d1507003070801001e90568448450040d5a06240b80c5e1301c00c07402d005100040c14580d02920100056014030246425690080148020341c68002e01200700c8692100301541052119610807110010043c403180394007907814002551030300c0030f000f40d09801c440d2888400000341c6640001d003805448641c909800d1085007940545c0120014507003070b1084d4960b0013800b9100329141040029800401c080728954000000103403d0456010003081c280065180400d0f9468118050012201d08066200a000480006040c410b400c03c2048111481c40e40000da602ca260350007041c0a03206070395212405540008000031a1103856218041c03092150b40340e030075155 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 801777455 1250 801776205 801776221
    0x140d110a090e060307060f09170d111902040c05120a0515061611190305030406170103020f09073e120f0a0e10020c1801060c06090206190512 62
    0x1d9002ca07085501340d80503420500c0114060038520044003440c0c0751a0100304e0725072403580d121600c407030001c1c08a94060b0040707194143c0c010941c40007215941d03000348100368002081074503448800034040d00545c0e98000c0301d0000780c8902c4c03c8503a1454110310740c0ca114100711031220003c10040701d01411f036041410500700350340f420b801103c0c1c113002c0e00080c026064029458082c424921000110350044514501050075081100d03076000560160b0302441d105c034034005026240710202850b44860884020050005a0381c0d0a8507440c442d005035505c14055541900175034003013241851140d20503030340b81194600c07064410321003480040c41e0f15501102400310725000c0c0c2d507200444c0d5480c0ca24101444001ca9900401c40500800d00662400b4140d0a0700c400102e06100440400d0000680110803c40c11608168841990805c8090305980e11503161860050011000d810001c2c032141d2544141c80035507940b070040d1218010800303007000c0d026100c90300161841d80314600d0007104241d40300000c1c10403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 801778705 1250 801777455 801777479
    0xc02100504060c110a0e040b1501050a30060f090b1806091e0a0f05060d02010e010c0c08031612030b0f0d2102061b130303140d110a09 59
    0x2c418a4403400b007a800d65030f44a00b0704250440138260021040400010800c0c1e40e0741000340164059122a41141804800e9001c68030301140103c0c1403110420002d03140c5580540704559003801070008500c2c8036464000e185c01b00081d010146207146c10640d0215150f41500c9500c0200c030000182004038194802c2803040c11100e0080d00d03184980c0c0d410008120307050190000b07174040d42e03101e800b54281c003242c641c0c1441e060040c3c07080c002041c0c0e101e4103486841020f120f800e400a100b11000707402400309500080540f0329001540b410404003912100400c038854500b007014200c1e100540b61503481451440c0c1691006c80020f4806080c00c018054a0300e00906c681007041c40050003400d0a0302400081c03018140340c4150480c0e503a0031314110040112640405407012025660150507542080307142c0c070918030300310301101c1d816901c01c01580c075203945200c1400d0200c070380c1410500c441c400d00038940340e4140541500801140c0c186613420744000171080017404951600e4440d458229110b0102405c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 801779955 1250 801778705 801778709
    0x304090605031b100c1401020405010e0916030e16090c1803080a0e060d050906040b010f0b0313110d0302010f14010303021f0b0d080c010501081204060e041104060c02100504 76
    0x2200b50440303c4640350600e003242c5903000f0181e0803c030459030b4a9039a41541c000e1070114610b010796000c201070016603071001c44480c1c1c0c4601111040040c0c202000c66608038103021200c441031640d1002121190381007030148150070701c00b1740610800c641d0f0300c6210802a01c0300c17502410010300c030802100001d00c05550360300c0903a50445081401c1c0180001309440121903082203076030022090282c44800a894040c1900c114024405000c80d41054075000302e2042060300300d140103e94501c001c1c052462a07109490707002100c0032056440096900300307104104c0000c01c0d42d980015410300745001341501504001a04096482c00304a40422014841031800d820b0000500680101c0c007501c05401d046032003a10400640c080000b08580c0d820001114600b009500f102d220344003240a0b1034051003031240d00d004203107450143c441e201d0402042d0a5520640c002e00003441102c008014060310ba0354002c9100d00e104a04e6955200e0300c2d0039025001b9a20403204038810001d8500d5201c10b42c0c4940f05981c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 801781205 1250 801779955 801779983
    0x30d09170a11010509123405010905071502030a031503141e03130909021302030109060512070510050f040e070e03010e150105210d030203071701050108010b07050c03070305030409060503 82
    0x2042c0f9030791a51f0b20100100c03c54000c8049621000c204400070b15840180009920400000030040714a00d442801c107540c546c030000d440a91705000c204000d801000f100d0146000c2e180000e454500d0060000c0c6440b031076040544240001e807244040c0d00800660003e4982d2190038485a0031490304201d42d0381d218800110300400e4403003800308400d855540046406501c02052600034080340301c0d089003280c0099200c0e456090310350808004608001e80600e86211544029010040c24140481d00104c010b400714070421000041200d0400b18510644014010140b40f941e0581402c442c0200080e502c80c111b14070030351130300380781041100c00015100c01e0b88407a1040501540c0c81c01d02041030b541c44070340d90070512084400d241c0d200d43d40c0c1071290442c01e004685005803030b4182060020591000d40c51458141488080103100a0b0b820140f00e6045070403803183c59a0b00c152515040c1c0c103000380c0c0d00000e0f42521030540d01008008012016000b42d40102c175040000c280d0f110200b540c0d501c52000805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 801782455 1250 801781205 801781207
    0x503010f121703070c0204091203140907050d021f0c1118060118120c210302030f07110301140609090304050a140409150f050601030e030d09170a1101050912 69
    0x942d100050384082c41c1c0c00340761410b106107138820580224094039002c41c07007181d2074030002c0400e2100c1c1c0e80502c6401e0360807552038807a01440c607041c4036940d510000b5004192003244490031240455a42d03555001003500e5210420003415654107010300b03101c0107034004a0700f50000e0b4610100c6810700344410981c030920310300c00c40856200e10307005680c0081071110801e8054103404010030700403071300c3c400710502510030400e408a41b0300d020300c500303440440c442d1091032500b248e030380b6070700820b41c00000d440c1503c04507101c8590742e4a45141420080403040d135425015400c01e81c06082d0300c0001c01c0d12034494902660590011780d00d508090b42c503031049000f807590240a190050140503040c43e181541f440c5c02900008125640c0d4560814403420901616005900d820940c81d85640313a02501e500640282000d0041108613951107449014500d9901c0c0c0303803a62045c202c5d06001110400300b468150303c40200340e640446010080900700152007404180d0b0a00001c5460f0641c0024090171051307843c04d0071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 801783705 1250 801782455 801782483
    0xb040902010c0b041103030c0c0306071e030b0d0c06030207210212070503120c04030c120b0601050c07030c06020f061503070e07030e07060c1a011a0901050f0a0503010f12 75
    0x54000d003c4098810355031103130203c0d261961903c04200038a2659402001420003082040405161100c001e11150801000031807482d1048a900d5a0710244101400d021131100d40650200c2c03546500c6030380140510300d641c100060425015802000c0050050081115140504040c14090400b1460240042e80000728401410041002902c0c4441c400c00590349002c00380321035000d05042c2504c41c034012080019081040084102c103100040403080300c080d10505250700c1d02c100c006001442c4a05002c0e0010b22451406802d1000d003010303560202c103900d0740710f89454000b0341d1003e40c0402c2e0031103482240003042a00b8815002c9000307a81005000340403c90a01c0d14941000002514460a164544820350f01400c8107010396000ba0000390340c0d0b86501401400c1c080c0e0340b60103010108541d0051a0014098101c440c80d0704181c00d80e68501035a519110400102e40b603200c1c00714a41078040011a81c41c06080e4003400640c129040a05d900c0c10080c0c40700000f8a03070084048000f4401641d038400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 801784955 1250 801783705 801783713
    0x30a1a0f10110a11010207091b050306030c0a0906050a08011e020703020304080a03080420010c03110a0803040807050d0813020103091703070903050610050d02040b040b061303060b040902010c 84
    0x80307503045000d240352150507684084401441d10710b50480c01c4a9000020480161a50381002404020501e003030043c40500e00c508100d401c4c40c400194003108008002000410545003040110032401d805401880200c1e51110058000c09950298601c40c40303060b0000104004c0502410140710100d41a0211020f408103000c0700950041fa0120294041400002071065091050049131400380c0c913031070f260340381600d090122480c500c030340304200242c860328020403030b688900114010b0343d01d4188940700086051465143c150026802410641c002042108000d90079001d046c3c103e100c4c008036201c82e045600700b500d6020084030f01031240141c5440340009584a9080441c5641c0a00c0030071050b816490000c403450350044807040086240440100f08100d0104000c60b40104d1910013004101c0c20304000480c00402e080313000c1e10907900d81100703040c1a5101d600c111b020110082c10309035100d40e10306203824420100d1005565980c504410001c05003000d008140d20715505035101c8a07800c0e4a40c0e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 801786205 1250 801784955 801784969
    0x11a09010b0d0b03030c010b0103050a09031b051c0c0c060302070807112e0207140a0b0f2a010606050403020d080304111302121e2415030a1a0f 63
    0x581c0001552192101003044d10103000a00c036024a41001140305650000054280d51010f444400e000d031400300b040021a601200306c14014410355040041c1c0041420050301c1c1c0702542480ca40300d00d10b40d0584d124510b4006103c2c011842c4a0040400d296540d804240c04034054104080d0207000108461000903207507a4035588501d03401411800040c0070068042c00304600b4103210500c1c4038071008000c00035a0100803110081c121810460134800794000810b0101c0c0e41d84c0700e412800078001c170705080321243c414103980004205a1180201ca14502d08032486030b515801c004965501c0e1100109095201c0c50844007681e07000303446c0b40229005551010a5648003e0066a030328003c41007001866480c44003140c28444000c07005601c03480d4420b04907081031001741580848900e06000b00003401000b0000c6580401d14240428411802c02100d200c0041c5220100742d1010080214141703095142c00554000c464071142080000c0c2c4a9032044800b02e90b80c81090782c0004c403002c000f002883e040b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 801787455 1250 801786205 801786217
    0x9050604210302152706041101030c020304092f040f060c1104050703021b0a0f02040513080a02010c120905070302060a0203070b0108010515011b0210050c0d020609011a09010b 77
    0xc41241d01e0000031082c010000b913800c0d81c1c40340d10100003031358403404454048200558103c0581c0907003e24101641d4408207402c080003071505140d198940030b49401c2c0244141d40082042c10030900900210ba8104400c2402c0d141540c4000300e03803110450844000841981c05441c1c41d259038107290342c2056801e46040000b4441181e1240c04005811560341781d9021312809030f00c0c1514003580b0381d46a042050218490b0b805502090b5210054400c0402c0c0412103403000d141d0191400102e50321068410440c2011450002d050080c000410307109403030f4150f10a6848584a982d109071002043c0020000c2d200c0005000c1c04035402200c0a0000d464004002d2000709003a00440389010007a540b03a11240209900003845a550f030030030451340400c1c06041c40100c03c0700f440c1007480030012006a540040e00000e01038001c0313881c1001d41170310038007540c100c41c048a1441304030780b4600240c1a00035502c840498082040c2e50808202505607641c1d507200018040c402402d4200036803d01e004040b40ea007080e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 801788705 1250 801787455 801787457
    0x14040c050613030519050d03090201021e010b10080f0a1a01030c030b120703110324040507050d0f0614130311120708130b07020f042d0903090506042103 67
    0x2200000006030302041000c01900003805c09040401c4142802414507220540c0c0100f03050501040c0e0380140e0b400301d40c0c40007664200d40d10285d0070b942600018010040030841c1c0d80c000e80184e01480420b80c20601061240c00c14084565255894020f00030a4460b001510104000d010380d80c650150b0082d0072003880000149000902480781c000094203110345e07540864a190000b103014420b00c04012003140300010190001d05005601c68400c000160700b008081c403040440780c0109013080010300984005041c000c11244251809080010350304a16031001c9800c41d24001101000c8110814424482c0c4960390210000b108503840070b540d080f01410001440740141b58a0a02c0c00c00728030701409200e0701500c900b90702c84914815850f40240c080c4c028206040c801e01a01006968aa015041e400c00c01c0c1d4011912202e4514103808800c1010035a0381803942da00003e550000c0c055002d40001802560b614030620342c0c410500c48a84030f14011a014107440c50840451410721840d4640c11070300c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 801789955 1250 801788705 801788737
    0x161d010311010314010f1e051c1b0e1801060812130302060d0c0909110f180414090c06071112070801060303080109110a0c02040f11070b070314040c0506 67
    0x48100c1c444d507240980042e1111000b1100502c00e480000c0d01c0c41c040d101c0c8102044181d6030138080010f500c0c641403400c0014104c040004003040124558900d40c00398074a44c4040401074480015816032181280c40c1c10661101d00c0d04503510400c14000c6d4421a011080076154500c000700110805078410300365503180e403031540d0001006890b04001070104114070304000072009a000c10040140d11a40e0041318070906044400c9003460300c40c41182d41100540100350f6540c0b0510304050184800c242504d503000c3d1030210a1003180e5401a42c8503c2030f031b41c981c20780c0c0000382418200210b600400d900038040b04220621041607003412000003150450000c1190f0703509944880c402e003903a4143d0012400101308000401c07800b60503004491400e503000f80c0c1a8102a0304040c0140b404241d9000603100e251104402e07410101190b00140d0641d0079000c42030b55400803414034806054046e282c0000191800c0c800020b990003d504030782c05a607000c2d03807a400043c9132204021440d041101070307501d88a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 801791205 1250 801789955 801789971
    0x2011a0603060a05090406020711010c0308070807030f05040606050f06040b09150c0d1d12030d0c270311011103030a0e0319080402130213090f090b09161d0103110103 73
    0x14610b11824400d47c0303d403d01690715200da19250035403441c801c0465040c400501ca49200007a0050400c41d809286403420130000e41c0d951328124042c08020841c120a42d18044c107100502041c0d070004415074105a61a4000d0390452041c8a018440c40c80781045c04441441080218a894a00010040c401500c0942000140c3c4107403400c0c0550034200001041d035031507000c4d00d50b2203006001c5900d01412184483e10001d034070700c0c050300c81c441d400717100c54544d641c0c401c4140050f0190003414404601d11110110003240c480754030040d02903d001c240d07400d014940381c2c84106e40c07050003181c071012840e1001e9419622a08401c40151000030341d01c10300c50200384451200581030720040095080305a0701c000c43c1d401c060044c05201d02034081031b44200c074010880382c46d844a1012100301120072400c0005814031302c00030a40b00406107000018a4032401a00f4841c42040024550401c00040c42001914035a00c024070b080e0b001681d10000c060001c03110040020030450440c44441c540e0604001c5442c203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 801792455 1250 801791205 801791209
    0x30d050f24100c0f0618150b0112020a032a09050301050405030a0c15022701031119170106030b09090114040f0f120f020c09101a0c03041202010f02011a0603060a05 72
    0x7682e454441080c920590003480034820600442c82d51f82255100c02c00148080d07000081c112010700d85400c0040307400088448015119a204828881c483d0300704031090304144005800e4161300d1092840090710035100820649018803a00d030045501c10011450501009019295014805000d84040807600e180d801d80e90394500003002e1310a00a514800c84407103030084030944030b03d04548a410585807a00c680412801c180482c0c1e400c250394040da161415007030804552080c0382480000303007a0140c20001034040d07016007044a006608443c0b08840d6500e011000e800c840804480e01010000a40841c0200366082041c000705030007440700d401c5416140d103800300d400001031400c1c0002891480c000316400c0d410302c84cc40700c3c0c0c00304036545885410945200d0034149568020024880310042303002803000c60490444001c410744c80b050302c3c0c0f00ca5a4100000c04600c0006003a404268401ca480044034070603c1064905964003100515880e921002d20040703810003007484e9005908000301084c1c03a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 801793705 1250 801792455 801792461
    0x501260c040b0a0306060f0f080a0209030c030109140c0d0c031b09020a090503011820010215150a0512060a05060f0a121401110a080702030d050f24100c0f06 69
    0xf16070140c4000c19441d161040c01403148030000608020840e0080c1c14143c00750b4040b841542080d418079015031144030fa20f0000b030824180c45030159140d0b00c0c1c8000034080202c200b05060350b1000c2d0205540f0f0402416040c00f00281d080ca80003000000320700c40900001e07601c284034030380441801801c0f0f4120394688020804a85c0400c0070000821180c550412803450240600012100300b03080c01407070030146640b81c0d0082c4140034540900e0800c0c070100ea0005900c01c11562400c100644000b5034030f4100800e00e81860156207050a004604d5860013003481d04094010b030b03484808100040c1001d903a00401c90380285400380820b541f14540b002660001c5e0350b02c01c1504060080142c000c0030101107450030681c1d175204000040c000741d0510007480500e02e0204140d41c1d02510605024060703990341d510480c00c5205402123140e14030710301414044800c00203001244214005ea0031032816001c1030780e25200d01d4155501440e40081e007081e842001c144242031124145114103203c500687c0c03560340d41030603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 801794955 1250 801793705 801793717
    0xf140703120503090d0f120509101407020c0303250201020c03030a02030d05090c0d020d060608010f02031e10120201020a060f0507020d0318080726130501260c040b 72
    0x600040203100c07055505000c1c8844001c4141041101403440c18001f402115401381c1d079003071040e918400280b8000003071106844000c0a0941081042c000b10301160070240141c0f00c81c401032255100400080c1400000c45581c103401400c0360020b0504078000300c0c49030061400482c114020006400c0c1c03a031301e003000581300c20b590715000303103807124003554040d01100c83c02040c1c020940d000032042d010035210265408015038055580243e40d000600305030303000c3d0050b80e200c64069841c05961116206281c1d020318094009001c580c19801200520f50710940d80c15a001d490004901d4410024408450813031401d0500c180142c441d00407054650b02d04440c40c190092040580b50010082d503030b58148014503500000d4201009150203441040c5010f06442e440207108a000248810504c5150400c001c2d03458808640e00520759800e0f4911601c40e00704400d110420750b00a0004100b0398000e0410000702d008000005189421695101ca00300c070000c0d00b4941e1120040102258403070903c001020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 801796205 1250 801794955 801794957
    0x21c1b0c03171e0c3c0f0408030705010b01141c1e0e1507020d0806130216050c0411070f06090303091709090a0501150309030e060a080906070c0f14070312 68
    0x5182c4004420b0003100458065040b03404004c4040c04400e1707400c10385540041c0e43c1030140c0c0141c80d485918a035610342d01c140e0308040064803000c102101041015000009160002e981d00d0b2240308010004903007500810000080c103440b101c01a41c80d4510b6076110711508403042d24080320311080400003c0032110901c40f800c07415081051006031400c80c01400d243c0140c0c0d40c1c030080184802000b001172024001a15035031065030110344036002c203446501501c85018004e0b0301e5070301e164900d1030040d5580320a07010b00c6000c0e0b400d003203804041744030100c10b5440c0c3c036400c080202d400c40083c0d55018014814400120285555280b14401040220b50150010a41d020307500ea0f6a8414108009080302e000300714122090600d00107104007940b00d82401c1484549007004280000700e89015100b00c40203049003500400045120000d481d4030000d030b54022800340342070300c0c0c40e5110040304a51840354004082c001000036820305001503071040362201c2802001058404640e1a80e0f51482403540d840384101c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 801797455 1250 801796205 801796207
    0x1415130f1e1a0105010f0807080907090507030e2107031808060c0315060a0e010804022d1201060501090b03130602040e0a0b03160b0d021c1b0c03171e0c 67
    0x19110102c642c4140d02400702420850480c2c01000802000e04100915440400c0007500103c0c0c2e00d046c0c20004800a8204031106225520340b4610050003044400e0790307005144545180c0403032031b05074050714111040410480700d2501d03000c1e440070380d01c500000031840400d600d005070001d140b910500050740035030903070503e0343d50b28140b821080c3e0070521000b0320b56206502c20005040c060340c00c00c114100844082c2442d0081d40d485000180c10000401180e02c0d003101664407152041003001940084000e04480c204440e00e0840103c40c22542c1a0240d0f42c00f081606405002d901c541402540c2c1c1314400713060351480c24145503500c400303030b0308554001000035410f50280014004c050241c5205c8a1081d401000450100041e2405040c820b00c642101c4410000c2c1c2070120001540403103001c4c040c100c030a116095007007207020700100310101c405901134024200107042e680c41141686d46094165907016040d641a005c01c804650020304558402c0044800501943e440440c181d44907502500c111 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 801798561 1106 801797455 801797483
    0xd0e03031812062706090d0e13060303030f1b120e01141008120307080402012001090f020f01030e030708030601090f031415130f1e 58
    0x1503a090268008005005200c0702401104100000c51398640c5030010800c182c5800041e07074000610742004e000b4941395841000441800c182c0104481d8050541c82d00c500c044445581c000c802080e201c0b2100c8107448501d00c02c0548654007001007441c1e24004074402002c0000c8408000340043e540c40c52038216580940c050344400041d00d00010240c00c194168258010f07940c40384400a21442890061103051038040d84d0050740d507500e90461300e450b954015509021310101d5428030100100141c0c1c68404240101d036030310b6025800000545540b0f005009a42c000c01809605040c148102300480603400011240042d40040600b40c1703e0b21100c004958540880d0311000c00c81c0c6080e00040280030601451200c402280c4084643c141400300c8116076140040301c1c0002e020320719200000110f40d442c00c1d003000b01845920900380c0c0300603260b040c0405c41c544020980305141c9240d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 801618705 801798561 := by
  have h0 := BRFrame.cov_init 801618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 801618705 ≤ n) (h2 : n < 801798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
