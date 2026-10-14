-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1384
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:42:19.300675+00:00
-- url     : https://prove2.me/submissions/c6d3bb21-3bf8-49a5-a7fe-5bf7ccc70435

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 248741007 ≤ n < 248920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 248742257 1250 248741007 248741011
    0xf0d0605120114061905060d0e0f07090b06070f0f0602211b031e0703200c12040503070b072108100909080316030b060a0e040e0d051e040e01030b0f 65
    0xf80e8002e41c80c1d42501760030711405946441014011b10380000c5001c0702ca203483d00807004994844084400e10030f60b1070002a40c0744010712928200c0352501540681b2450100111290709070072140484a56040d0f4460100d40544004100c81c2d0560801c14200078111120803012030342c58141c0c2154a51030300b040f1801e1000b018028042060004204000d81e40001a1095034000006080c62010780d5034450150000d103496014100520203001000c10102e00c500020114403032f0030020f481d90006c0b90780d00355138503014600486605821440e801e001c8a8503a0000c0c00c1e402c0d014005201000100100034035000400201d002d0018440c5d00070800a2408806030303c00400c0c141d4802c00c00100d43d0f85855440740005444c400c0c030302d0382255500c0c01040c4aa0040c12181c10020290381c4c1e07400911a0142909030442c442c1401340d4200391107071440200110f0007050a17501078913000d1521801c800345401c0c5039041080c0d090b00340d03018800850310181c041c0d105030185100c0d580c454082c0c10a0304900d1007000700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 248743507 1250 248742257 248742259
    0x1a0909090706050a08070207030221010b100f0f020c0a0b040f06020a020a060c1a01080c030106060504140d02060408060a0c0e030109031e0c142803050f0d060512011406 74
    0x101c06010000307541e000d4101d4403102c105203010758440d00c80c04802c908110704c503031010390f22041c50310500c01842142c0c40d4030708400005900800400e200d0070244403014040c00034001c04500400307503032501c00340118004100740000d441500d0a036100c00000803200d080e180c0006441080218040c00510b11400000c0d01615103400204407001413030b0b0000741c0c81c0d40c250117a1020010b0a0030040b0401c00c0003e002c0881c2c1d000c0c0260300b030281d80c54607000396480c2c1807010007520942c02c103180006d481e80190100d5050300c2000b84948002c1c0010b0061013440107180b04101d800038000c000004001c10207000783c0303000c0e110a05010515200414000380301402d0400b01c540f0a074580b10700f0301300080d0030420002d45c000d14590301d1180309200c01c3e81034804082c40d58000d08440c62282c0500c42c481c00c0401c00e07075427558810400101915070314a020801306840b890040206e0300070808246007910303800c0580305205c0d01c09008107000e900d401c0400c02014030352f400b00040383c1d101c0f504c180703a03c014188400e500c00c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 248744757 1250 248743507 248743513
    0x303030c020732060d0903020106171005060f0604090609060b250611130806070305011514070606082116020904060609140a05010819020105131a090909 67
    0x801c0c0005440d01c041610000350804441d0f9011091038503000c611401d102c00c1c002c0c6032503203803107154600c030029040704401200194600000816003070b10741620507041482c010002c0090030748c11900200104030240c0703040c1c4d1103188040303110025a12070006002500b0920740104005162401560030745003242c21803964141d042c001400d02c0d400008582c0f11742410792150250b030081c1814013400804240c90035414403400001d50035601400d4090040c00c88114038100d0300f00d5510200304808980b02802a4078a90b40400d00c0395840c81e10440d0400d1140720301000c600d15141c401c0d9a010111040ca0b8003030001d503001003c1c4000d8040d0f50140101004500007009881d250465040c0c00c050040c1e80c0000f1300c5149074202260134404075921440c080e03c1c07081c1040144210070741c581d030000d170001c40d8000036042c100000440c2c01040442c02100405a6210350808142c0c9a401911140c1000200e200842d0788180c4c0043e500d0030f009000c821804580c003170156501d0240003804040c6200400c0b80e03010794 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 248746007 1250 248744757 248744759
    0xb060c0d03060603021813140c0403020a12210512271203130c090f09050607020c100f020102071205090f06033c0406050f090a1106031506040f0303030c0207 69
    0x8821b4110700c0b84000844105140da07112216500081201c030442480c801401c20402591f07907003c41c010801d0324001c951010540369580345a400d049021440100550401d50780e40d0f100c505003c1c60030344204260300b8802d0420880001d004500c003001c03108121709610b10501075002c405612b042c00100c60603031010b0030034000c0040514025101c06085854172180080280040c000c4040240b030141004400c284240d4130b00f4442d45024080460342507501c0c6c0a21404a00028000a940699220b010707011500300200b6174000d55207003248460060565408000c04000910300c40a450f1031483c10307403904c0b5103070429142440103100700c12400c240180d40410500a100700040e0a6003802614170b0388c10004034001840185c000c00c1c1d040068401142408144407c01c91a5007001d0700c039840900c1a00d80c0c641d40c0441481d5141c0328100d018050700030b0001c0d86501801c250006560042c01c49810840c64010100441c01c0d41c1e000381c0c001006030200400500800d0780c1405040d104031242d2004003e49 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 248747257 1250 248746007 248746027
    0x30b0f0a03080901182301110705090601050706050f01030519150506030106080a0b0a050c120f0a200306030106080c0a2112050306120708030f0d0b060c0d0306060302 73
    0xc0d01038000075003040c0c00840c544076182e02c50985038040702c90300c124050442d5901e041e410501c1d40b0366500e40c40300000c20746011019504c1660358580b103030702d004020400e00e4a0101032101b0318a001e00700301d04100e020852000816224061107006004000203403146600d14146030341448940803103586103540b01ca44c101c020500101d4100008042c180d800517150b1180c00000e80103044c25403120f0070a0044140c40000e221a0614141c0300c0c0b110401c00b40010b655003068030485110b50580f00b5515404034000c95811000e46440a0b84200a850000f0f00054022049100381005009400000c40c0000c1000210304080c054034004000c1d400060a0100c480e00000b624281e460190454203901500d401206040d90444248400e4102d03407000e82149046e14014080e90048500d43d00031a800004200d0409000900710304a0700300d40055420326039510411102c03030744071110000c0c071940c0704e1250324880e40c0c8110091080b08203d0009005070010f010002e0b003611500c2d4403110506105000341c07410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 248748507 1250 248747257 248747269
    0xc03030903280609080a0e030705130b01030b06030a3303080c03120c0304021f0801120501020d06081501080106031121060c0414090c180a09050f07030b0f 68
    0x70412034681030226081c2d181ca600320596544103409054541010155814818901d004100008060b40c9000d061100201030550303507121441010713009002000c0c81801d45c1841d5002403110f0005243c0420380d16628400038100d034100355a07160b0340981d1058814a0300c2902c00ba600341d5208003019041d5002d5612108204a03005440098000000005c401544080903c00c850785825000ba440c0f4403414141c0613070b01c00c1d03002142e01301c2c000c202043c440c0c0f844c0c21b55054070240101140c6d032600d100c1d030f08006810803405d50402e002c480d01d42d000e001c1e482c1020251300954000d803030043c00603c2c904400c0c2c0c0c0c0420910740180d02c0030807664982001400030031082004030000000a903119000400d0620045541c028114a0340030280243d005000c402450900208122000390385040d08500740d401c200300d0080b100740c1c0c84541c06a4100b0040e444d109031000380c001c4d482d00050080750710580e11a0f4903002e44504a070446000c0c40341c0b0040100b4283c051103031a6001100b03942403220b00314a8004254 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 248749757 1250 248748507 248748523
    0x1b010c0209060103051308030f07112109060f0f210c0315130e06071e05090f0a0503030f070606060507050a0b090708030403031e030510060c050a02061b0c03030903 72
    0xf04040d10b0344005400d44540c00441107080d43d212001039030324a0030450103001142d080c0d884000050740808508402000081e5200c060548be0962404811000c200040e043e4001f41d8603d42120081c84131181c00c81d828000781008002101941d03a07288000040281c05100900004000f8001041440417401d05035003602da128028540c2000c5c21062100014040c200e540352442d000342c00c4c032070302100b11000070544a0180d55a40c840b0303840c2a01c3c038844585685044201480007944c244540c039030300d00e030100707240c01440c00180c03000744055101c001280c11580810030301d051b42200090141c4c101f000d079200c0c5500070501c40c03508a0800c400c6030744081e00c2e90344103800a0182d500820108400b8081445170b00d00070901031003100da50320b540303140c090030703801030843d01e1410007101003031148100b07004c0c1c000c00307228581c201c1d410030360700382440070035210701424510035039041c4541410383d00180c0f1140c000704410171303442d00d41c0c81064100c440c0c510724113048041380c0f60090300107000c0c8541586000038048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 248751007 1250 248749757 248749759
    0x601030f020a0509041101030f021801121508030c0c040908040504020721030f0b041b05130f14100207050a170a06090f020102070b030601120b010c060e1b010c020906 73
    0x80c01004a80001003004080303800c56035003d50810280710811580b1600190300001c2a201401252014882a0308070f000d031340540b024028200c0070700900c542c4181d14108040610f00e800042182d40b003c207007804401e5030340080749103900c0050050f0140108000400c140c9808a03824015030703d082da01c0c409540520702c5000e0040c1d8010510008000c82c5400d40d080358100ca00c55000c030f20320403800044c00303081e01000d9001d580745440a80181410103010703100f04080c48a00500740350340380000803242540145044c1c1d103482100f40c8080b544290341009240184803244c84e0292034a0700e0b504016003004200e035154290b600c000400c01c85a02c49544000032205100380c403052a0781000c0002d4100003010360000c00c80740c50301c0007501c02c00c02c003030312000034a9000f07a08817003019494000c44000c0b844103892260209201014010824000d071f00058030484041c9410b005141c0260342d0031054825001c00403440c0c0e049101000e24030b141803244940c10300000d2800303004580c8a50082201c040010f040a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 248752257 1250 248751007 248751023
    0x18080f03120402030a02180703060b0c030906031305010c21290307050d06060e0c03090a0204181a01060201200f0313150c0806060c0d0f020c030a03020105090618060103 74
    0x1c00f99074042c0030408000d0340240c1031b0810a0300e5000141d05000d030131540c51011a10b441e60104101c035014050310480300c03511000714a064860000c014140c0c100901c107080c0b1420342505440010428080c02c0e01d803130000c2e140c41011b0089110b2000d070760800b0250600d00d8034604042480c4806424694801002c00c00280301c0c050038a40021905005c0309404c016041240b500380d0b4010090f090384581d0031159a107903109001e85491445240502c4150740c1230700c2c294003c50282c4003611b081e60028203510010004440d50422aa68140711011451088e00da0802420700401a080e020700ad1481c5115081da40550417603042052a0442e004100e0081d000c0000440000e00030544001c1491a4a41002c2c281760f0060030841c0140140072800c02500009001002183c840d04003242599101900040500401c200301c800072103111131029600310441c0300c2d403511500542c40c24040c03003a1881c06540080343c02e141a600452910700041d04100006a0b11283c8070304107480424482d056a40c0b01060f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 248753507 1250 248752257 248752261
    0x5010b09060414150402040801020408072421140910060905070c08030a02040803030405030706110301051e01090b0a0c050c0607050a030f0309080a090e18120d0207060c18080f0312 79
    0x215009001f2600001d40c95840024003041c2200005002d00465201400c40025229000c0540c81c032292680d0740d400106441001c8000e00d080d800010440400d15000c0019041440100086158400369440340c0943c001c04001f0000c20710301d0140c4005410007682c00d00c101d0600140c01021480e01a1010b000280e010010643c0d603c1150100d03402060312101710b035280c2c1040e092040c0c0302d0303001607811a24103107040003802200310458191b9040b06c0b802822003c0c80002800c0c44401c0b51001350107141000040c040c0440c2035640c090190003034010551b61540c4080140c41c0481c9001548140c25114042c02c0c0b10840c000343e00062441d141d0f81d850702d4444032466035400305030050055084020104440402c212500e0799214520404468001c0d0b881e88031900c400b440f05a5400861802410b2034004282c9503040407031500092a03c3c2c000a1401440c10a407900c84404032070382c54000030001101051170852040500075140c01400300880504480840925481d030b80c1d104038030950b0b6a214180340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 248754757 1250 248753507 248753509
    0x90705120c21060901060509190917090a050d08030402040c020708060c3a050603070915090c0f050a081306091a070905060909041e05010b0906041415 66
    0x40e030901003501600b554100107154020030000344658210348540d11900c00003a00c00c900501884040740e0010304000303401d460721068002600f980350061440c2c545c80d00c2848001a42480e0162441c241100d82152100200400c000350844c45034813017445a00039806040c0841c3c10369003200d8200340d04942c00503100010182c00d9007008555880362095001d02c000b0428030300c229038000d11141e540e0716426121a0021101b00c0320201460070b2001d1800112a181c011881e882d510803a0050700c003e08070b840303640e546d007038060544045211000744807460710f800b0055800700d4002c01004080034100714840c06a81c0600414030302505151800308028030f07010403002502d014560803859080310040c8010791050400c0200104110242c800c440c01c4c101c006041c2c148218002800c4e031382c0c0104038516120001041109251000d882034550742003451070003002c2104840c0510400c1c2c80b400011a151030203808100d06040c0090642d030040c2e003824884c60501500b441e28076403181080c0b0f690241914148 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 248756007 1250 248754757 248754763
    0x1050f0d020c0a050d0c0303060504060e0a150b0a0e09151f090b030a0c112d0705030a030809160f0b072a0503070b0a1e030f02040b07031709070512 65
    0x35070094154090101d4045d07200f6400880c401005010342c40901440d40c2d114140021250f10f8850050701c0c44019000c0342d110040c503040345100d103100004420090340c40c1c2c801c0700c03890b510019184020856144014101d4200f41314110760046400c0d0740000694842030102d2214034403110002000482000281d40c00da00800d000300142c0700100c01c0075180e14041040700001c080c0000fa120100340300c0503018441140024015615400c2040441003c0c03640f00d80c01c000d8200407000303204048c02403070004a00307a14200204000c480c00f03070707132403e4842c103195081c83e003010045c40510210700c214110501094140300101c8040ba2a03414825550311450b051240160b103640b014140d9400c00404140c00348859400d60609944044082c0c4260076641c035050503291113520f083d200170401b400b084801407926100b41598480d440d013000700f003100860302d0520072a40690049100043301198880074942d203d540e1106040c0c6085081c10780b41080074001d942c2d1641ca1103504e00c551842c00c82030025680c24 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 248757257 1250 248756007 248756023
    0xc0a0f23060f0a0309080a0806120d0e0d0f02030a0c0f140a061209061a030d05270102030705010e0601170c03120a090812030403030b03031602091b0a0f0e01050f0d020c 74
    0x1b48001c0d114190820b0007046144181e07540c0c2d2040250724811600b03904042003010000c0c400340c648050221050040c08802012400c0543d0181004440800540c6040c01483c0710f0300d11449a02e0181030514040c0080b02c401da4114003405c55540111802c0c585892114100340c8900d41801c40501d00302541d402c011b841070090003000f450812000056240030040340d00303d0404110141c440e00843c005003240d45001c0c0c40e2202c10400c1154520003101c59000701400c125031018416a494107185854240c25940c08442c070180c2c44d403003100100031409413455001c032141c2c03ca0001c2c2c5008010800066070700c1400c0c54042040910008403507118a014442c010020404082940c00b40c4c543c8050304a0705800c100d6056002c00d0420280300c010303280210458540c04505031401c41000718680910644401c000c00b21010940700c482d0400f5041010740161024480790f0b60b840c1c19000e41d85100a1008d40c00d44002410310100f802400c0d84603660805448114003401c40050712a0a1098078514120b04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 248758507 1250 248757257 248757263
    0x405031b070f3f05060a021201090b03190308073f0b04060b1c0212040b07051312110103050c0405060705150c030f011e050103090201020c0a0f23060f0a0309 69
    0x200100490f1018000c0704072220b1240688241d1715a0751b81e03086003400340d114141840f16442602001481302c500e00394000d1007414006400c40381c4001e5650507040d081c1c50704100980110b007086040141103548400120300d010a81d00b181c200307003a40343c590150200c891120908144865600120940c0302c0c036070000981550092040c407415a81d00e200c0d502d250301c0004912014100f41350340e5205011507008592640c41069554030355541e50342c1311910a21009007002c02000740810050360110f01b286101000303410161180748001c902c91070403156080c170340741c5028141420706040011200001c0203071021200c00341e4007266195030514200c1d00f80440100b460400522041c1401040000b0f00d014510480d4509056000350741c0390300b0880404910b0782d100003520103000d81c0520095101e0707040500f40074410b00480700e041031542d00103042d403013064010b181d0341841d03c1000c0040e82e40302d441599141e4410101504e12140410116410340700d181c802601c81000021848982c61280e40078031405a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 248759757 1250 248758507 248758589
    0x1303031e0e100902030c0d03030b040203150906090610030b15070303050907090908041406160b060f0904050a1101052205040c0f0801050909010b04050405031b070f 72
    0x20025100009121075006141c080c820200140c41c65a69445001500c1d9001001031030300101103001c221401580000031404c054036440034503079a8503a030002c1d600400c45060001014461481401110500200704610034500f080510030075132909441000c80c210585804980b005c002030216180030400422028000c000007011400e0680c10352101e07014850900944440f203942720051802e5440c0542d000d003074000f041100701f00d441d40c0c40c900c42e444a54064142401c040b122245145d00c201480300695812900d90104031040c41c00754a0144041c4040352009400e00b495181d00e541d0ba07030f00140080400d4062040300c000c5038002c1090b203c4404881102c1c04641d1003070400b01180c100c852040500460626200a05d228010843c9940020035560741522680c41c10b42008251000907000c0080c82d5a034002004440c0c0303030750040030f200394040d100030340d5107a400400d40085880e40700f058012a8006010600824407101080b0040302e20f0540d03100d103050b05205212020300415002403204c14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 248761007 1250 248759757 248759801
    0x50a0e0609060408100506040509030f0a0f0306081c0201110c070329010303031505270a0e0106030503130504050c030c030601030b220f050c070f060f05010b04030b070207060503130303 81
    0x10f00354200600c1950248c400384890740f51283c46d142d6901565001003050760041c01603410745480f440300031421519034900412040d03030700c04d0310f030f070606001550a4500520170010140c440703809000e0301110741e42c1d0742c480c546051207524800392601030350b020040101c0b086105101000b51700e4000741c1900b100701c1c1403010702540d49203400b42c000e20410001030400260b0000000f01c07490928461100c609100c0700180e01c2040e103010600c1d11400040043c0c0c5065a96080f002014109219100c05548281c0040d40c1d9200d5110003031000165a0f40904c0c4958184070400c5900c050300402e0340d17001000c81c0c0075143c070307500c0307010040c1c0240002a400e641c11254030b0b003208445d0318280302e082010801c050b600704050501024440159201143c10a0b918041080280300050308041c0070055540640c9000802802c0207500006a0380280d0050441d281d003c1418424405200220343c1c225403580002c00d0414034105000d0035078040142017a125002d000c11000516001c0d8101c805034800c00d81c4207403c1c11b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 248762257 1250 248761007 248761033
    0xd020411040e0f1005010e0a030c090f1d03070b0c091801061101050115120908030c0307021204050a0501110109120201020c1b0d060e070b03010b040510050a0e0609060408 75
    0xc0d0014403800311503014841c04a00c01c00f840f00c1e401030250300c141c01d03091441c03030170000107561402c0c000c25480d030821030031880040840c08480042e0050403a0040c04141c014903103a20500381e4803e90009041020000c0a44016890020444094692048800743e042c3d0340c00c5503201c1c0b00d0007110581074202400400c504440c56401c04214140e0754aa218007254040300352200d422603009005506501c02c4001345840d0180c0141342075140c1f820220004100100700755a50082034100350303500d100290300030041c000d1507501400f560400e00c3e14a9003850425241100196015015206440c148800d500c5041d01c911b00a401842a05802c150303151004031205c00000d001707600c007501d4000240503030340341902c034010381e102e41c0c1c00700700300080003424500011385840000b404262038032040c1e8460441c001845155403070240d4000c00103034817540d4507507150401740100541340d640b00b0300c01c00c0001c000200d201a008a58056044c40036580d45440d1050f0b040410303880e11554005501602c0f91005456003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 248763507 1250 248762257 248762291
    0x105130e0f1c030c0302070218060d0203100e150c09061b0d0c03030e0d02060406181e150b0105031303141308010c020f1e070f06020d030b091308090d0204 68
    0x1682e0101c0d542085440403a08080342240102c48000b54011000f0303404030540c0c41064040c43e0401801030042c00445040d9000038035060000100240050702c40c81c490400403410b00280c111030b041e81140700d5851034901c4805803144191032a962184101003288010000a121402d408010b05412200200e00d032003409010781154a07411030000727043c5007590f80083c001180404040c1d03050740007001341351156681c81002d000310041e01544050716030003070404100603482a41c45d000c407440181030300c00c080d810140000c52c4542c3d0b480301150f091040c50301050344d1000440e58000100d542c00903911200346012142c808090356016000c10000ca00c5200040000506100312145907000300080341d0f0000050b40c46103a5a158071000750400c2c0700400511902e49a030b07035580d601c004240c51280d2345030302d11411080120380104005034014032601c03043c01c0c0c05225820320848112001c200519100b000c0e20201d03001808000e21706031000c15440d10644881003c0c41d0341a078020400d0220720721402411034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 248764757 1250 248763507 248763553
    0x30709061409160f1d0409061a0f03030a050304060207050d1106130209010b0c0a06051f0f06020a0b04170a0809012f1b0102161b060509060714010e06060f090105130e0f 74
    0x41c200c0196071003001c0c14078200843d171102c0078010740510b00f0038580cdc02042da6550001402038603059020042000040c409011011807401d0b6500c654000341003480d5480d203400d200501036040d00c0200309500c80507030398100d040707030450300b9103500e2598807542181c62034240291a00001c203010b0030102840344003511003400440060301030307184411050f9900103091340d0200ba0b105000250b0081c45d20324021a24050542e4cd1160281c0f545c05100c0364481405070780755010071010800a0409014000e1034242800b400d0701c0e050414400842c3c00d090500c080459034030a030b05c1480010070000d8403401c22200c00300c2032080a52001c0085407140c0454448680442d100e035021946409105001414880340740a1181602d010350b8806040020081c00e01449501c1400705a4001c101c080040740035030000d01545084001c404080c2102c0d0600b0400c1c0000101e4601c1744a1042c000500140465140e0904048030207407480b07000324208003172144480c2001e001c43c00510050041e1030b640d60000e201814246 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 248766007 1250 248764757 248764781
    0x4050c0f0d0c060c0203150406090611031501030c0c0f1101080c0f04063e0d0207030b0c0702210a110a061d030709061409160f1d040906 60
    0x24000a80c004118501c0d481e500001c1805203100d509010783d40c03240d01c0f0004080e101608403021018030101e08803400004580840b02c2e152a00b096604006140c020702e100b489a07600c0e0a030171810301ca0041c420100d030350213003141050340e110f0b40f070301070648503074114011250010060341802881e402c003d00b40f50804012580400c1c101c90201d10320317020702003c07211281c421110040c02e06040640803920701c0092203600c0e4206080d5420544d02490300702400040380010429241c01d81440c0c18000e0400c0600c1008105640001208002107031250360981d40c0b168800115a51b81c00486c80022b50403c0d00b40d400141d50301d0381014030350380e5178030001700c130042d440c0206480c10b0051100300c1007218400c03150040b5000122040030070f14007140c1c01c01e02c0e0600280010140c800e0303907846d002c1580803140c01d68000200900c410321845028100407050a4000d0300c00c10340d004000035208806000014a41802d000b0000806e030f50300440240004442c20f0200003c2042c802c1c4809401c1507c00340c42041c01074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 248767257 1250 248766007 248766019
    0xe1311040f0605090f0403091403030d0204060302030a0b010509010207030209040807210908010614010c111e01030506060901080f10050d030305040b0f041502090307080304090207120309050703082104050c 90
    0x1700c1c2c41c00c0d9040703007554403a41d4035903622110503007085e010b82030107038203084c0c00c94141c4000c2c09405c18400541c00a84083c088aa90050f1640b81141408040d111104c8100c0d06001e8100309001c070599020074a1010b40b6015140d1a041d9142c5150662252150001c040d22541c000780d054040629a0103139004000c1c010f5a81d410b10544640702d0a00300c441d6031084401900707192004584a50290b0350030010140030742c13a203018902c041800300e6980d0400c0304207034900014800e9061065a014400c1980183d001d603105410003000703a0029107040c40c0604150981e01071a40040c103010000000a005483c002d89208400802032030090064541500c2c11202d0749031410000389101e0584118506c25600803085200300415003108000039441500000c2e058020150007040507a02003008100403c0f40d410016a80c6099060078135580c1d031240084410541004a801c011440014900055035013061141d0369039100409054401c9002003001000d00d0b40d490100000e0110204000145140507690 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 248768507 1250 248767257 248767261
    0x1060309210804060b01020f060411030d0e030a020409020307080d050409050109140c0a0201110f0a020706080403020a060203060433050402070209011a1e0406090b040e1311040f060509 81
    0x1d820440c000c1c00c50000303200800014007251868000440848040c01542d51480d4000c8425050860032035082c2c402c00b440708814581414104412864244c140c074041c55418059000603841c2e10708008064803442d1100d690710f0966805000d01c4004021542c11030f0500c502910001c0d0079604103224206009180c40c00000d0f0001c03060054044c05071900100094659031034045079219004400207008541d40d40c0d1880d21070400c0c0c0d000801c1601c0d0b49000c26a101d402d042c20013807501c070782504880100842d0400348000240c0004000c1c0c45a03521403070268072a030b201c90120b8010322240d03003214180d528030010300e00c1d50348250070102028034000300c14180554440080c4010f92003410002500302d51281e00400170307118040e981074511001003c03960b00e014050003c940541e280061225140640084c00300701142d00100d0080041403d24411824107250000c09030350140d0082c012604e119160085d01c08100c2003800494820f00001c000300083d40040c1c04842c0141498000c141c042d00321500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 248769757 1250 248768507 248768543
    0xd06031110170a0204050d0b0f07090312120f110a030b1507020402030603120f13060c0308010605090a1503140604020304170c031611091e011502070e01060309 70
    0x100300e1a00440d6529074084030741c002da0000e4250a802000d503210706a091002265640c0c41203400c040d1580190b012412509104e002240c03418805090b003410302072115000c1000948442c02c546107800f40b802d0128405289514400141000b0b03000010348602d0071001800e0300c00d1283c0545041c001c0b56500700300c0e013001d803014030080c00c500d04455200e800c01805500e00500d065001158030035400790954549000b1515140c01c290008035070852049030204505481501c01c10482006100501d071901c000790081c5c5000d404d1030018066502040f02c0050001e8a6440b1410048000e050100400c00021022100240180f2200d10b03816144da1110001c00c0140c070f494003d9901403038004800a40c007002e007105028443e030010b2440348813800203002c8004020250000003003410f01482850406880704400c1201d0514001d200b1510788807034842044030b10b501c03019000e041d2100079808512600c040c100503031602005910446000700c99070000b0812a6064003c20f224512884104820090b951 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 248771007 1250 248769757 248769769
    0x9060609170607050f0a050904020711090a0207021003091103100510091b0e03100504060b0109210605150a0305010204080c0a08030d180210170717010312050c030d060311 75
    0x1640f40400158180084043e940030b00006203100d0090b401d0244c40d010000c400f15090b0303085504140c507a45001e0740c504c02907003070028045900c540f00e8482145048074640c009004402d6051110701059070381d85000c010844004181c41d09190002c013102d200c0e00c0e1024048001d40811a00750860180d00e1790001005046405422903040340807030000044141c031041211204000c400d082c1d4544111813151002020070707c1283e000c0d601a400110310900c4440024204181c103511191006064401d0f6046400003e000c003514182d01900c00700d695200c03488514240f01d080400b282d44084c599400000700441540180103c7e5451815507942d50040c100300419042d0390301c00d40940341c10030402c0c985550055407045c081c400804050410b907106a0300404c0041d0514043d60001c2002c0d88040b00201441c0601c40d42e02600728586080714808801c20b0b4040d141c41844000c04885481402d010028000c4054905072400c05003101d0301c50f000324101e0800380c4194070042d600d0b10740115a01d10141880 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 248772257 1250 248771007 248771011
    0x902030d0f0c060c021f0605010215011202130e0d050304060501060503010501120b0109031703060109090e0d0c06090f031d01090e1f081b12060f0606070507090606091706 75
    0x1035240c694520b9440d8403000c01504d007002c3c01d1802c5000300080d840303020601d891400100c0302a1040010490300f4107001901e81076005628039244800743d80100a00200300803c4048194182d901d0300c890050801701c880500482c10707100440d8091441142c104c154400d01441c40f0394080d4601b402283d9031100159040d1000b8051240042c1c0150710900d0b40380313096001a0b07040031041c904101003941d0b0f5140d031120070f010200c090010000010a100f41c0390783c0052860060044500e08100141c40c0c40746850390380c1c5030f000d120700038000304001520910180303500c04480250095801c0e401618030745001001d0f007000c0740c00000c01007000003080d41954841c2d200703041135aa44d00c944442c251600f96101c0f9614030032802d00e114503d201c16003c40c401d9400d0107980303207030480c00398020002142181040348a1400051018055200b6030400145149080340301d0f8100e5420f0740c405645080e40c4c2001030814041e40c100401141c00d00d41c00268007a40810712030110340103c1200b81c00300c00c5403801c09486e030100f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 248773507 1250 248772257 248772287
    0x1e05030327060f030c0307020c0901090c120606050a11190c0609061701050f06071536020616060207030210050c16080a050403230115030302150a0f020d0902030d 71
    0x10071310000320b0038502c000046410080500468018401810020760080001d0b040b650f10551900c2d04041035a4020b1807800c85500c6864041c00b041e401e0400c000c0c590b0003080100010402c260b1406400c59006110f400c03001c21074025012480100c6082401001c0c0d4a07105880000ea0851400146c483c450002c03009482a403022100d8164600300401c800b0f500f44002e0554851000c22407030b00010011402880c6101040d403000c03074040e00403040025084210110018160205c00c2107941d600482c07003860b042c21703904552180d11444914005009501e02400040c01d41d4400910f41d424103400058041172414040e10074080c41d600d00b43c1000590044a18000c881c28021118200040d09031000d019040302d00c0c64454242607481d00c4100700091305444581400707040e00343c03102501000f0b000e880003e0200503001d00b041465030390000c2d5031314641c00801c01502c1031440890021109a040005a889000320943d210740d85000d4a07001032402d503500302c3c40b9220f6000c030108c01c0c0740511444048810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 248774757 1250 248773507 248773537
    0x901080a141506040f02090d0b0f162a0c1d0123040902130c031401050103020a020714031507260c09120c1c0c0815011e0503032706 58
    0x340c00c1e0610001e0140c05c0105640e1907001c2c010030f900f54440180200d0b0035401001020b50034104013080400140001e807006240700600400200000e422910500e02e07c6000c003654206034404110031464800215002000200c00c002c001824420001c5c00002c40e079038402070b041c1603983c1d03000c001b000500c404000d80c085135084403a0183c2450164404d620260000c1d0140103c1c1c681190714804907610104d201e40407982d90400d5500258540f100180541070a08003186403c1070210080e688101c42d10500180b024181301e1b0022988041c8410b5800800303450012040d8102142c0103031000d40342c166009140360910b24400d03004201c1c07004507405001608111031600c00c4c1c01d418008030340d68060b901c0b00188148034100350300b40c841c0c1415030034903841e0640380c03031610506103003108400c00140e1229030f0542c000301315510805030b82080b03541183c003507040412182c0d41b03040d843c041d066480c1c0c1c0001e41c5070101064144511070104c01641450400034003060001c050030003002440c0c011884c0ca0304000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 248776007 1250 248774757 248774761
    0x70807171009051e010b0d0b04660e0a09090f02030d03091a161b12120608071211031005041101030f0b090c030c090901080a1415 57
    0x1051550042d500700d070000b070100102c04011036030040241c50a86c030416041800090017600c2095030300c07030000448400c944c1030141010f5107654403c41081c42d080c001c1d40402d88880400902b09a00c0c1c0001c10304407140103060240702c3c106041013072100c060120644186490007506290f8840c000220820300c3c003c02c0c410455041c110094020540c10f1000c5030041e4000ea000380140e039003004060303542c1185540200c0e40704428034010309940000300031100800c40100520203030740c0600901c8000c68980c0d04d8140d243c0040d00b101c1c0d140301d449601025007a0350140c00014006a405102c0300c0d5545032280c01440a0b564908006a40e110701e445248a4004071450880c0011000c401c1d482c00c45000404540340c2013100b80105080b640281c600325180080b0304250700995806008000020300d100d00104290004040440c0084030000c01d00b07080341f180000044ca1049002082e81c600b060040c0100e403066131100310650f0b40d40400c110954001100e104104208000044e4089a10900c41103241e800d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 248777257 1250 248776007 248776019
    0xf01110604120c020d05010902010f081e06010302070218040203120c03120a11040608040605060904030e10030e0106030305030a241a070f0602030402040606050c0309120f060708071710 81
    0xc680d501d0b070303054100200c2c800d480300580d5038454450700c01c60044000041154107840090110341c00c0b07480c50802d01502d6000c110160003110080807413445001d1610380640c0c0c4481c0124001e22a0700070003503110790014180702003d180c0c3c0c850039100318400d408640c184008414129502c0c0118010079290340d01c10000b440b2040d00140000d60400609500462002e40c1c4036078544e81c54010b90003083c0000c01846c04c00040c0225801032070b0300148243c1e0300301c40360b00b003e45008150000030203d460003100b4848110305424840d40c800c402403c0032500800c6600d4a03458000c1c041e91043e00c814600da410a00d0040d642d0a008072528070074800c0c01e5144130320920388807100600c86042c0d490041614010f0107841d01003502580d0b645038103480782000503520310b01f910400003107411035004281001404e0101c80000c0d103000048a4400c0e50844000440318020f1a0f614030f4281e10000d0040c2d18090320081c09084e907000f403820f900401154a80000da481c00c2c44e600031103034004440011200600c13038405c000d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 248778507 1250 248777257 248777273
    0xe06090a1104140a05210d05040f0909030e0901141503010501020c0d08070c12031101060501050319090602040b1213031704030e030d0e03010c0305040206030a0c050705060c0403020f01110604 84
    0x8994081c15200c2c64a90781c1700003500022800d0405031511001c1591003a415000340604042c5148608200d8200707400c0228000850342c2c0760240a1050b42d40d09110014075000710700744e05030031500800d9555291b8558031007190559000708101d00952556401955036502601601d060f5007061303006007800d4020300204526044610000d130780c0414200300c143c005c41c44046010700584615002d600b40044a890f006004480444048505900d4142d040c4400da030300c941281d4100d04100c1f44132400c0303e4a40388400042080c0000149664030010b000202e0007560406401002600e10901c20a5942c0791160f0391010030000c002400242000c9890043c9000c0d82d1145030402d0007071030280104501c081c0402e2904904a251502003020144045503d01e0240501c040100b001e19080c072060800741e0129403c0c1c080640800300c100c0d2a80000d41c01a4820002d885110760480c1c01c80c1c44605080500c101c3c0755000340003d07406606002007020407940600c0901540d000510028a0746030358544413102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 248779757 1250 248778507 248778539
    0xc0f0109120b04241b020607080105040b03010212042a12061e0c0e0a080c0306010510030b0a030308010302041107030c0201080604180b0f010e0402180702010908040e06090a1104 78
    0x2040300e402e4450081070204c14035022482d080340e000c00a40111031450140000343c1228014045500040800c11004e0740017041e50b04481c4203440100d50f600e083d00c0028064010714611260300342c500d5007003000348104910448903501180000310004c80307a0110081440006000303070300f1403825180313400001940c507038001880c0306100342041c1ca444c0c0e444004103003038811500054000541c10182d290b810f1500d60708101c0140522030081884580840101e03454000520540f441250850b40100c8000d0003900280000000180300c2058507850703180107002a1070a010070780c001c6213444410010074100c50201c0d00e4194054985800714400759004540882c4000c001e01d80054607034440007030f0a449a4000041a885420128041e10305099050720b5054140c0c003a605010000041c0005a00d80d10044010604821510302c072070354910313406034090520f404004180003000180042d00745e03490b202c00c0b802200d044814041030782b20076501009450355a6007075809641c04000c2008030040ca011004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 248781007 1250 248779757 248779763
    0x5030402180106020f0f010e25030503040e041103030a080c0d0f0c0c0b060d020609011d0a090204030302010e070e010b1602130605180c0708030a1803020c0f0109120b04 74
    0x440d0090300904210301c40000382d00c0400564040c000034484071030103111880300d42803900b000b005204e541c811180e070342d4865216a40700003d040313074a02e102032100700405800b840d0031000300c96640d0f42d2000a600700144c1224155200300314004001300ba031402004840f00d00041ea81c0784101900c4400304501194804018200c2c1070b952001c410290b0712450240101c10341241c0ca07983c00301040e9003000516000001c2174103204120610080006a0380c01e020340b030700d0100c28a40901000880c02d000080a5080908981c0c440881c040c002015141d030b4004005803442a8000d1001c2007890048642d05d031454000c45650038074440051040311401300181c0020010040000005130258000c6615408003029150019494800c10b02c603a04101e038100b0380c155040c2000040c5841c0c01d11446945020700c0b41c00070460000000070540900c0d960700721a901103086003c0e105074030030300d25000c2e503500350010581d03010310400602c445036507004071008012101380f800400702e211440c0c0d5590000010043c421 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 248782257 1250 248781007 248781019
    0x10e010c0203012d0510090203040804350606090a180209040c050414040f03081503061006030b0d050307080f1c050a1a0120030418020d05090f070605030402 69
    0x41001da5001d010702c189135a0b01c0300c009050505403030761111200708002080b5403094204014403080d16051600300d8101c6c1c52244005840b62101d103400000c0b4400c84d440412071004814074038034500340000c15000103000d000d4101c48415158a2030710b84030101150701c50b901261000c00140f030000281c0040d0848811552080b600c01003030350000300704400a030340540c0d040c2034a41040c030403803c01e0701c00c00c080c07601442050246498699604c2d4250707075840c3c00040400c10600d01003118100300641c41c020911000b4107039100c40c5425000140040c44c13900c030b40d00000b810244540c3c0181032803e1003810aa4004000d90300e0808a41c4a0084030384c400460325440d400e0800030300c01909825480c40c0c10707280e00c0c11b50208507030400d54158070030b03071700a915940002844d01c4038207803007a070f0010300e1104080d512054203000c40c0006400681140201d40c008403114585000346c03010292154020690700340400c00030482070702e0300050f0340d980310040c1001000075444038038140481400741001d103074014801004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 248783507 1250 248782257 248782277
    0x40b2b05030409110c010617030313050a0b04050a1a060109230d080d05151810030803151f05031b0c0a140d030b03060106031d01050103050f150103030905010e01 71
    0x600d00c00c484105405001d141310100d03902443c2c040a0007198020040400707042d001c10350740201d40b516440090400d086000c0c1c4015410304101d001d0221240d510b4100c290b5410034942408d249440f0800c80c803080300c140e18031030345981102c100c02e446140079540680d02d034180d00b400c08c654902c041401101c408000d0300c00154502c400d40d685080303110041c0c0700c0c8518030b44030420481110140c4602501c0741c4907003038108410b556661101485010701e001c500d6180361080e1907140442c41c07c004a44c2000c2c113842c8000003004800c00300400780640112090703c8103040e2038a90042048940000e646550001e441000441c2c4c01c1e0514291010302244c0070584186800c444400051901b501c04200325072401c0740e2a0710388480d80c02800640c0300440541024018001c1400010b500d9010501606c0240751303980c4d503900e02d40d84803900d038440541e042c00020402544c40c0d050941d03640400d41358604540c412400f044404201581280d4101c99141e110380744c48a0078407006480c076001c5141325034104a20b500c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 248784757 1250 248783507 248783519
    0x6040305091003021210170613030324170705032404020118080d120b03071e0911030114120a02090c0c16060905030a0c09091407030c05040b2b050304 66
    0x9001d00480b20701c01b0700f2000307514282c040032421003141d0301902182c00c09020003890082c2d12001000c010b9040c98006948401e940b400b003821510b40c00302c889000349100c004200d0300d510000314200c00088000b00c842c0b0170340d00c0007056503444c5242d4200100c07090140c1040300049400c482950001d1050404a00c0c0484504811803401c0c41e0760721002081d032040c5407101c040394000e01c05032240c0c81140001d00038241d0a0012980d20a40da2040740415100b00d26000c0a90004008a0b006031181c07480074040d9410b80404000380780c00a0007400d00706005042c03804290720f442e070000306c0014a1003001d0114905190204501d5200c020111940000100710b8244031075028400d100c00c0c01c04440c42800506d007803480c0103110307d500b9008180654010100600840e941c0c1d0444401c40b0b489200101c1c8001961070002034021207990003100920504038084100300e06400c425040e110300351001c100541d510300400140c0c440004100c80301c0c210940e242082e10301072451710300000780910100ca150541d942 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 248786007 1250 248784757 248784787
    0x1002090d0f050307020916080f01030503160501150602150606071a040c0b160302010e060603071e0503010c080403020d031a090601180f03020a050405010312051308060a020d0e0604030509100302 85
    0x48454a400143c070080340305040d001401140c0009c00c078400f207000c0303604640e078043e601c6c8542c0900c803030020101104501044425000840707805003928000034000d075100f03400b031755580d0304001442d03400c100384000440e1814000255040d0076000b45a10741d0b800e17a942241152250050416210301041c07020225100e0300460080000c0c080c2501c851814214904009085a0034100307218071a030016001c0c0040380e600010f40c14261030340e03d07002885110040ba00d041801080768402e0390954284074901e0f83c06a000440c81e84190301079020f8424119020f80700301c2c207c5001008400c9213190042403041d140c203082141d5030744030b801810070024604605a410821121a0384003402c0b81060384800d00450400c11700800040c00c080d60203110b40d50459456088501060806e40100038022035a0f894840001121131b0040a900e4160350b003d04203100464040c0d8406040c1541d01c5003001c0100c1c0000600203900381c481c50709035880758103000f410810017001c0c4030361128541c1016001d11400340d9181d804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 248787257 1250 248786007 248786011
    0x70c050f03040303090e060301050402060a030c020c030d0207030309080102030403140708090a0b0a02010f020322052a0a05180705090d0c232e05040e0702070302031002090d0f0503070209 82
    0x6030b210b044c005c80c940036014941c0c060091406000b40d0410080c000180c641d0020b43d01310311807078100070550048081040349000d50240038240d062181540500010f03401007403a00543e406a5127550f1213076103440e810342c00d030f200603240280010850720a074a14201000c2c00350030028420540b03d440d00300c0d040000703141d8200c0ca4008510482c0006103c9000f1602403241c80c1e040d800c0c07143c065045140441c03441c10750501160180e02081d0640004104218080c000c0301321581c21100c0d004000b8180d051504000a58105502d019080d510004541441c1020000c840744c2c07004601c0d02620360761102c1c00c403240c1d001003403843c1d00145080301c42c81c001389400c0840d03000340c080c19070180d04400c0740918492488980031005400b80c0068080b0380d980b102e0418410a8003e01c0d401541030308441e0b03600032100f80c451540f001400322003034024000b03100e50101702c0504590080b0102d80824a8a4401c80100c0c41008540d5901c540103c10100c0090158842414514000c00c10340342440e401e5000b06c2c1881c0e5003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 248788507 1250 248787257 248787263
    0x2040503010c02070e011e09230f04030f110a111c03020c030705090c0a0318120c0218190b060c010204060f09080705010e0909071a2a06070c050f030403 67
    0x40440144000340c00d8941d11401010401c081501c40c050707010103012031f482240602441e85032034840d944045103c114142200106034041d501035490241803a85810f0700c2910b04030b002a04010180950903c510400d00005036040f015260181d800c0d5076800421801e450340c80c0d002007504c5030b1842122104420107941d01c3c0260090900815140101410000b150300510b20556144051113100568072090b103105084500b4001030503015203880144081900400806005900850174140c9a1040c1d034030b16598400d41c2c03102d0b0741520805a8000c10340003214851002025030344407084101250304031081e80c24021f0001440c103207803000c0c05402c0e13034065042000410900301c13600304250780c04841030000700001c0f4094014103090000003000c8201030348d9840c0c81400c01401045421000344003101c014010304090500031003500482810302d40003200d0340d40521940d1440e40d03607009540f80c4001c0088100300e015000079510300000b41e940190140080d10144680712207640170180c08c0009001440c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 248789757 1250 248788507 248788513
    0x300f030e030a091412030a050703050708030a1b0e0906103501060f0516080912010b0111010203010f1203110712060c020109030f032d050f070c050304031502040503010c02 75
    0x800d00d10448083d8130300c052040e000b000d0620300d50600703820200640741002902c2c5016655a807650a00712117a0081d840c003d40324100002c188100303020554054100040c20050305203945800440c1612040105c9004681043c0043c00141741858004100b01843d0444c2c00d00c40c10908d240c2080b80b13108800b810142c1c600c4000f68410401c10310a601440e80144202d1034011209083c01000034520702404076071880c0c9420101c142e0041041c45016204040c0000e0402015594601c04460103400038181307085c04101c0080c00850b4010060084a068518101c2c80a0b80c152500c2c0004210b0400f07404150200441c40550100d001414441140101280740c030901e00e400150507e0001c0ba1000c1000c2025a813400460310002900166a000fa004a82c20000340d1440d03c484070440c05039005424039500c443d04ca6112070794401c5940290300951181c03580d0f0303080340e40f54941034034406501d400150207540180410800542c041907001310301615901c0150134503a5070008682074804040084015030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 248791007 1250 248789757 248789759
    0x28180504050705030d090608180a0303050103020415030b0c16080d05060a05011d040c020c12300f030903070c0806160f0c06020d090506070903300f030e030a09 70
    0x120040068034080d010441c040c2c40017800410024000d0781c0300c0d1180d14144444d400000c1d103191141e040301610310101006540d4141d01924005008000c2400224440c0c0c0c90f040c4114035200000401d0030030b4a61103a05000d0603112001c40c000941c0112100c092520508500c1000042d11200501211b458001c0d000c1540d0619408200c104d4001c0d41004d41000b642801d5100c0490ba0700200c81c02e07250058070001100001524200d04200400500700d42110001e1003403520060000b0310080540c5d80071541001603030041e071200012105000b094079401c003041c8001440c2c0100440196002401e9004480c50480b540d910780000510350ba20290064001c0f00410994403c0328110b610394505a2a1440c0710040c2910041c0c12660400009040c1e90750110744a00e20024941c0101e003160f0700542221250326203090014010540340c04201d40300030003081e81507049003802d4010426001c1001c3e08050710445d0325021900168011500001c00d0788400d030a050124003800103018024141d03443e55695 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 248792257 1250 248791007 248791013
    0xe071a07060e0c0d02010e0a0e09101b081b16031e0c020a0b0c030c0102190f030e0a0305222619060c050c10020d060503030928180504 59
    0x211815001000c56401c41c03210303086503560b400180c07144d480d0309090074107045043c5408640e0060882d002002000c41200510602210002c1c840400b125a81c0c42884903282130342c0d1a15181c0e1081c100714011590f5140841d00001c60a1600c00740441200c1c000343c1003051000c212030f02ca060808040c0d02281c0d8903808450808280c601c44100b54074541081400884d43e5400300340460b00e144184a4038550214102121801c103004071840300b00200025500c403900700b0811210211010080d03400710300072541040c145401307401014440c00148010301510711040c2c5058901b54000c103103500744944c0d6980000044203106040310081c141001400c2042c40882e4883c102c0d071034106444c5465540110072100020040c7c905640006030300c244003007002c014200c0180c41c64041e640601025016202c0b5244100c07040d903014082c0c007071000c4018030500f84e803102450303280e108002216400080e400040294201d90074010764140d0711284d4100a8969901150340c50750603004013a00c0754503291010300c014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 248793507 1250 248792257 248792261
    0x9050a0b0c120f1c0e0601060305060f090f100f0e0a150315050f0c0708070f06090c1d070f120c050d06030311100b01050a080a060e0c03090105090c0f040e071a0706 72
    0x7400d1444040103007400f03140105941d41b005219400070152294000b580c25214079068040790540908600118102400d100f2000201118800c40c0d49600c0e8400050040051031100c0803101c42421101990725004c500030007030040748400030345020204000200103640c0c0f10411f04502d80e03045000815040c1603105401f6150701422503060322006100c92070101d40644111a03c2c580d014158a06c618102c0ca0300b680500304152014040900d09030000a0f0301c0516a840150200c40e032207143c6440d0f607070301010b813200d0300002801800903500680800c0400d03400d91100342602d8940c00c01c00d00700711030308041c0003e855841d041240081c8002c0980b0103103603010880c40c0080c0b4012b00c3c050020b120b8820009000c2e00401168004011a1502090a00e500d9030b2122001d02014980c0004915100c1d9989003540c0c0199a2580c1d15842c040000d9400c00c4085500500100d00403d040000204282000041c1c241c3c0c8180d41d0030b60065480c001800078544003004010001c107030f107540c0c59100754200402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 248794757 1250 248793507 248793547
    0xb040605070f0e010207090b15160302160e27011107020f03010507050f03130f0f0b0604050708070518130b01080903030106050d05131202071509050a0b0c120f 70
    0x5024005080c0c0c2070790317038000c100e04c815a030220000144003405c00d80001c01912684940c824082c40009060320744c443e4002030785001601035002c484200c403054031001ca17000b0303c52207180c05010714100424520811211440ca10556039003040a02601c8550810f085444140740c01d244440001083d4085040841d9140c003402c40c124002c10103441d0004000c1e0062292040c09000c2041c004001149c100220f080d880c2d034290402d81c000c507000024606020740040000c3e0941d006080600080c0443c45c01b40a564031604456a031140320303032980081903c0503007001e1801c9030414408602c58a89440d60016030381030000070007001c20341c0002240050000034000d0403418a540080006000c00c079008400c4400d845403504c000640c903650b080c4100d03001513008000a2911100750001004240e0010302c50b015035840c400c0e8280c022100c0c20059070940c03c944101600b0150400301081080307a11409081400c88103415203a801001f00741007116540314038040080e00e040400c2c1d48082c61803103011070b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 248796007 1250 248794757 248794787
    0x6032d09060106170c12040c0b19170403120b0d02040e0303010f0f0608070e0604030204231509040b07020a170a03050109110712030b0a180507050702130510030b04060507 75
    0x8503290405c107404400a116801d41000c821a040004c04c040003020100788009000e0048110740b5225108804848d03c0c41c031101110025074615011020700724513003205806554191610202c1c000c841b001c04d03010300f4481c80384503401700d00081c0c15400760700c40c0e0107540900140000134550300d60610074680c030407840b286c114040b6060b15001c02e000c5240c0003030b0450340000203400c102080742c22200008650b0710541c0c0000750424100190310000b040401c001d00484554054903050301c2da20741c0e14800c1e01c4010f005205a10942d00c40100d80802c00e03504e80d00350881c190f031040e9030b0b1039070454031603035036280b030000d51140301c80d100007003894401c1d906100e000c2c00340c801020140085014074011040d0b030f000e05000500121004d28081070014041e50020894001c0038003009052540ea1072112101d826044010444900700030014941138803800850324182d030700500c1c40c00540c0928440d82c1c01400020050710030344000c1f00010010862150071244520300c18100841c50345050742c001010807111000070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 248797257 1250 248796007 248796047
    0x5100603020121110c0303100e0c0f0d02070501050c030a1b0f18050a0f0501020f06070c1518150b010c0506150a05100801080d080606032d09060106 65
    0xd10050ba03004a51000465025008000e003e034200b0348500102450141080d103450001005518640040080d5100710351000900925030b80d030305029015250b003141c00380ca02d540200901280c840e040000b8080701c4420520040c02d100013588c81340d00b1902d050b204041d030240301100f0003642e012140038213814043c1228200444201640f4090180061800c2003003c1c452200078030342280007003e05c00310042100400345e664039942e80ca510021007031a4050301d401070081641d14528100005000b0380510103030340e0707071129a4455031036204c584811310186250703154580490103000c0088108102c40c442c00b400c040f07058121900743d410212840e81c0742c0c4505000e0300440c200081030300428600d510841d01400140254075640001d2000d0509402c2aa40400405460b40b41542d00500e142d0603108803101303d80400c500300d002a154180c045070445e40c0b0103c01c200003030090f20300d4412491050b07683c0711a8849111492810b40c81c483e01101c0c00302465102ea401005242e80c081e4186a00710a4540781c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 248798507 1250 248797257 248797259
    0xb01090b010801060e01030b0406180c0503060d030509030f030d02040509130b040b180601170610030c03170f0715060902280203090a090c030506040209060d0902060f0c0a051006 78
    0x280c8a02c0c014410b48041c019061880026a4040c1e006402195030052041040c00d4031078040d140058014800701c20303854a058400039009010b80102ca01620303006102d000075400550301165694442440d07281c060007000c000129005080016007504420610301584503404c01c01032100a000080c010580b004100550001060a00150035045a0032000031a21503884514254290764110700a520a1150030000140e032101b160a1440a160410a4910680300c0d0703001c1c54600c4c10343c5c0c040684004c0c1101e40402c0000c0f03a00b4070240288640c94062801d1147c40010b03240d2540020b141580c00c2022000d4141a1246620402c000b411204204608112241000750041042e03400c1e2801b0300d654062445241c14006c00a503940344900500c0d201d2402d8942c0da034000a010707403565410129043c58081103080c03526000f940c0d500c0d00c010b00081c2c102903034250300f02c01900722a401a40c01510802c1218400e031320010060000840440080484c00f0681ca0034034a403007010100d4a40c07151420030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 248799757 1250 248798507 248798509
    0x60709060201140c16060b0607031701060807140c070b04030f141f02070f05060c0d050105030604080703121b0512130b2d04032d05300103050601030b01090b 69
    0x10507143e01081c03503403a20f405c80400f1b2411074010002a084194090008180c8108041d40b009409000d1000c40c41d2482035a641c9000c03d5440d10415200d03000411720704412071016501841c050b100c0d41c00100c08a901082d03582003240d076158030940003910000389030040282070040440a05213064000ba0041001108100800701c40303658042590312003680001707480041c060002e01c0000c61a42042c01c3d5200c904080c00c0d0544aa800310b2561000107003000000242d51a0205985120725040010903152001a650440b884400420562186541c51001d0b25980003000d48082d20408242c0340c2d550ba4200703151f810042900d00800e0f40400c8080000400d00140e808420741d5005403100c248400c041403242c850322a00c524001c0880d610b0104801044141544551242004006610705d159070003000c0418080510b01d00170000040352041080b4044280401c000d03941e041e40d40310b01a11801011405510000070a03807050312145d01850040c4148003480c00c805005001c4d00d1410402030724640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 248801007 1250 248799757 248799781
    0x5040e010e041a0f061201110f0306030d110a020402090117090d1106160c020a03060228050c060402090702070e0a3204022202031303030c03020a091203030e06070906020114 76
    0x40c80c8a010306c44140f02c0c000e8001d003d400944d46103541c3c4104c10385842001c01411a15001110300612a01c145141d0f4090140034205840c04854030001400c0444066000d10010754046101241007042c08030714401c980500340e00d0540145420310280840d0119658000d000e084e0070042d40003a5000481403150742c3d071400744404004003550034560b0440b07000d0b00005150f00303115030000c2c05003030000402c00900f1321004105290340d02e041c0041c501807028803e08603080d0180b440103500c0750388030b43c000c180540740913114158420424411034003000e4884c0881d060145c41542c100705201e4030f07204102000100c000036000700021740740900441c00f65200803a02440d901a00107030180149001d100001807902c240900402c11a242c10366a034105880185440c2010190540019181100213a4000e10074003c071090441241d0f204044581000722238881110308080803810f00d5520060401400c405010007407181009403950110580b038800c000e03094035200d40301b4030961805c48080160307002c085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 248802257 1250 248801007 248801011
    0x21830120d0f02040e0711241801020f0f0c010513051b0102030d0c021605010e0a0303032304050a17030c18030a0c090902040b0405131205040e010e041a0f 68
    0x104401084140c07941c0c1000700207102c4c5800c0795001951510400c41c05d1500700c08a030b103842882004a40f030710755a40c40c1c00640500600248011442c9010228508412652050840b91001d0000625000e900800350b4115448040e00260428002c80d90a42e000030a10406911407800306110140c0049940da25494404141c0304071100d4092210b0b004059108106998001c0b079062400c20403054484006541c409203450300c610140c1c690480030989500c280c0144046441c00b615001c0c1d00c9007181e405901030200c40c0555040300080c0e00c039050716000324420042c0500d004030081c0400348610308041081c80091941c0c013204540c00c00c14021860b2520741103403e56200101040505851035000a091201090018007240007030400450b0020150703010a0043c2c0c801c440412010340c090041c881618801c88400d051050f4a0f4202c60208109984055038060700d0b1500610305030300c0e40c4c5105a03d420a802c050304400c80c0108220030045890003115200401040040180c82c114041d4a41c000700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 248803507 1250 248802257 248802277
    0x105031b061602180103110a030507060507030228030801150c060b0117040506151905010507150c03140703021911010f1d0111070803010902183012 65
    0xc0090769550b040c051036030101e03a140e401800c400f044480e018500200c12400e000a07601a030626424808510b8400300c0711003100d903c14040c00e0202d00d07051056590303820001040c1c00394040c00c00c0c44807071007100142081c00c01300442c0e580c0111202c00d040043c031030901600104e5950101420550201b50030044005009501c002c0c04140700d10840f00403252042c03911022807403204800c00f40f10800001160b903a214019030b100501d491150001007003800b0280348448040c11000040500c55544140001c2003454040e00400d5190400f580d9000200e501040701c8200086d510f40107500600000d0700d445d900702100303207019801e02201d01d415102e021b0000021005200000fa080d0311780103c207404c03204d46600c22a10400c94001007443c41d001c4000d80035802c0361a9440c0c0030548050391200d60503612402d8000c18914116803d05028900a6000115500e0031020006400341199146050b5030314140c2c003000c0d410268600d80b520003080c9408138880024541014002000034403031041038a81c0c1040c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 248804757 1250 248803507 248803519
    0xc090616020d050105070e010c0305030a0509010b0d030206040c1d1513090506010f0f0b030a0902010306050418020a09020307050a0507020d0c150f1704080a11030d0b0301050105031b 80
    0x1540810340000410500079001200319012106101040d4006442445161a031089880280300111a050701c0388000502140c0248003042181340d070703984229488958080001082829900081e001180c2010200c00592144041000b081018481d0000400c0c0030816503084080c0c4030240c00f00300d940144a01103d4505580700b003625910118503400501d48400304000c1c1116030708080380c581c0302c24010020065a1288001003004a105464003200c0390448070b141162100004d20000e4627100304181d0415481d0f03000403c00e50b940e4800c050f2024010800c10746248440d10500064809942c0400e01c0a80306008009519401c2800c07980d100d00103103480ba0b0b0341d11a51000a8004417201c40c05048207084900101d0180016004202c0380180b46e111070510a42c0745501b120381c0740481d00204424000c84010900107541130001d4400d55880b400d02c0e145000461500c1481c60f04203096104100380c41e40d1140707000c1d040c00e2195501402d0305802610340c031800c0c0044124103500c01c0780c6550080b6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 248806007 1250 248804757 248804767
    0x10031203181407030206030c0409060518040f081c06090e0a03020303060105220f0503060c0705150402180c040f170607050708070b130204181a0727030c0e0c0906 71
    0x82020b20800c009154006c01c82c50700d0341448503d482c2d40340c200c0c1c080d41c00c116181c00800b0030302d071600300d60180c50040004101600c6070b80325690881c28044201c0d00320740d141014800120700c08500740d900d460a0048a500280c164a0060440c09580c000c115004064000ea5101004a87d0200c00c80b544a1003e0803c00e648410030681000c500e40b159051250f024440d100208a1480e503551000803514128101c4400c2d44420511000314410514014500d40c800410700d20112840040c2d2a8444d0005214031940c1a04102d9002d80d01707400c983d44180c002e00058203008640c084560384001d0100381541140c088400c01c1c01c1a61450080c003110140040460801c080000c40c804440100e03504c024401d0b07107400c012000940d00e00c4200022803045040c00101c580802e201d0749510704c1c0da6000910145441c0c02400800d0090746c000c0c01c1c6408019007030b034850018204003019000040b0001a0845074070b49141082100c2419a4201e4030390000c0020034058080c0203a410ba90401d182128000d90300c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 248807257 1250 248806007 248806043
    0x70e1e010e161d0d1101020606150403020d0215031312030911040207060603050307050d120b0603060f030309041104091505031b0102011506050c01060e070c110d0206031003120318 79
    0xa0f80500342e50700c84440203c1c1000c02c03402c8240c21052030000c2c3c0817079000d5240d500810210340384130350108860344801e0004002615240074200031150000c0c0c160759040c030000300e6000721030303000b15a1b0b41a01c0102c505800e007009a5421101101c25052504002403100c4d5a290070146604001c01c2c0d00c526004a19030b41404540c0d440023004582c400e00716550382006292541c0c40e01c50541204021134481c040d62513410701c050158802013000144031f14030351f0395070400300000094105805a00342c44140864580c548881c400c6440c00f02034051001d84031450300d1001c0c0141e580401500500c041501d40801554400146209210f00c030540d40d0b20040e5000d01c0100e00401c07915120380486400d10324001405030b0808010440c240003000241f0140c0d407600001d00a0b25016a44940055000802d100205280307080c8070115010040520340702c02101d4000460f076800648a160001140071420801c203c0da0381f1246c0e00804c2141001d001c25440e2031001d000340c0c010241c0141010169030400d0030301c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 248808507 1250 248807257 248807297
    0x1602010e0f0a080d0206090a0b0f040309050301060b07060b190b0309100c03020d0c09060509040b1305090303180c0109030204050a0b030a0507090b04051b0705070e1e010e16 76
    0x807440002d032200c0e0050ba030300c0c00e0541d610740f203080c001340140c0114404142c0c031000102d1020790158102c4103042e690b48404070500342118000340140c0800c050008081002c0d5428041c0b032000301241090180c0390400707401c1c4882180d1589402c940306914004581103101c100655507000c4594044050382c80c2c0d83c0780c0b04460300b44080300c03600000241c40e00203030707844480d0158040c000f40d116001d030401c00c0000c8840241c400d411907008002c08903809028600041c90182c125191842c005030030b01818010512380107060f15810b841c1c401746900040100b1034828403a120010f1b50480380c500504004142c0c000281c00004e10f400064040c684540c0041c1880c44183c0040f0701510f409012070b941c040c0c05052864594101d40502584c080c201515981d15141034007c540c05982c001007000c42015041017012015032141d401103d5502540f0380c0080d4105114003040d102e0204c81d9010f801d00130415016900031072050700b000540ba2000005d01460031401010301c50301c05110f09101c074540c0315440314004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 248809757 1250 248808507 248808529
    0x30201080c0f0a0f1403040507090e0a0c09060e1b040e040f12020609010c020c031b0a0f0b03041e050a0b040201110d030207050705010903030f0318060f0905060901021602010e 77
    0xc0c2c0304038001486040d0643c13120441054031101d035640b80710300091070400136140c441510040d2480d03212500502c440c002640c0f0000340310843d1401c94a00c21896a43e0f82c8a029044e880076480703d507140f20802ca040b90a210044c0c0c00741c80d80b480d0825207509501485050300880c0181300100d0300010025041003a241111310b100d5420a2414048607000039000355a030108844900c3c207035003084044c1d11080d00024840144030401806070007548001d01c0f04907241c55132000020351015070200002140b40c400101c1034007403c80284411350328905030400c20a2101040c000c00b400c04481d55858001c10404640342280c198011010070140e100c43c00100d0300380001098415040c0110340c0b90140c2039400d80d0007071284070300c42c07415903015981d601d0040da00300c001840007801103030b100c98030218658420b511214032841042610a441001703525502c040754640b008440100c0d0303680c21500d080c41410000258480c1001c4020740c030705904591401140040200002d06000c1103408525842c1c0d102e00640b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 248811007 1250 248809757 248809777
    0x9020901030f0218100f0903260a080703110301030308040803060a080f0c130605010203120405030d1803120501181104080114010e0c03010b031915240306050a030201080c 75
    0x99140c1140c0c03031500c1342c900c1300000360358820403aa00d400c000380d40c01103001c80c200f14201c0e1039090301e5624540340c00e01e59200c1c20484151041c003a40010607400b410001070802d1415a03a2102c20918010380e0182c12a030011203003981c00301d03050004000090784203005950140d40018200d45a48504020175501c0700c00350040810b40c001d01000003152400003550140280b41240c12031254400740c80050300b00c520500900340103070820840020444c1c01c0d0a500c5401500c80c0d011a0b1611780b55648117002c0310802980070f01072000307040b01c0340145584282c4a0b00b800b03041e08000c21641d494070702d80d0138021080d02507144000740c03201814500c035840c100903070380105007400085c4464503d4014481400701d090081c1e4a402ca29503011805000644040d40e05880d50318001910f162034088030000343c401081d01c3c400b1400d442e81055082e803282007580c00000c1082d045010300c1c13214507004241d50b104076042036000701407030014100310f1070f07540b19603000440b40c0a08010364140c451000800040c4100e103806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 248812257 1250 248811007 248811011
    0x103031428050c0a031d04180b07020a050a0c0609150917030408060f010509130b0f060a030f030906080901151e03080f03011d131212140906010f050a09020901030f 72
    0x40c500b07246d0407104041070001807224600016021004000458000d18500617081c07100045480004000c002407a802428a004641404c008c990321a4580740354404111001020f44808018590300400d07284040c147e40f051203050010901002007009000c3c0c4603250103c80d00c1c0034070110301c2c581801118064100c034419240145810700102c041d945082c807c00340185c0c03009000030094401b00409014207980440e5018032616408407820560030090f15840c0c0c4800b03022030002c0003811141c50510124802e071682034410740380540181070602c00030040c100a074101004a2980000810184140d404001441040042254010178003600f603400c0105500300024000c80ea0701642409181240c81c0c502c880f64000c01040703288001d41c5000d41b0310000220070441d105000440485036180c02c8500c3e8500040d083c80c80061000c01d0715200034522403050039180911090030010b00000e805400c0030032101c1401850440400c0314904544a0802c985502040c10b4240b684a40c109030101c1d9103010301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 248813507 1250 248812257 248812273
    0x4080d141306050430061e0e060702060601020f0a030c0830060102010c051207030e060a0b03010506030313030813090c0305010501030b041a06070203030d0f050103031428050c 77
    0x2025000c4d9100d4024800300d01051803030340800d06040702003819030700c003001c0700d840340b020050740c91001074016503000b407100d00b0342225007418155080c0704005151a4490060805080c01b04000c1e0502c0c60151065045400c00301c41002006000078410b0450761b814038158500468905081f03009004151928415201025030b800d20f10180c202e420031195214030030b0000b00d07200c00006908903840c0a140b000850340500541107270a00140205500001a0401080c000003c03d2200e04000b0121504001a0754580811015007003d103c2d260380140b083e8002e51034802d040800c11407504e000d12008002042c00a401003812845104980040172510001c3c8103a00f040d00b00030f40988000d0090341d0029150814842c400e1405000b801c903030030440c4101c16100c05107072050190381d074071000043ea0144010403002e9080441c900c62101191b40403c00003480f9411031030000e0804101c08106c0104040522258424459550041041c00a01a084401d03460030100aa0f21809200c60030840c50041030301d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 248814757 1250 248813507 248813519
    0xd020c0601061e090f060e0303070501050421090e0606030403180303020312060d020a09020f07020d051605010507031b0c090c110c100e10030e07080705040b0604080d1413 75
    0x61620440d08815020503c0c90040010071581204281704603610510400340400ca454000c8124581035000035042d42d10b0300c20a602d5003401d55005581c100c48908491010000c001c0c80c150504410750007038582036180d00d02d80888408104c002424882c4112000408201018000c860700e243d1000c0c940b18800d103d95617820301030340700d07040340c0c8030038803110b4401c80080c0862900056000c1d600b40d0041c22401400c1c2441051030003900000240108054104032040140e903039900142c844503c140000c00b138040709030030b2070030030034a080d4004c9041c408148032050000c4d0300660280110a58032258801819407030400100500455002c1140075107040c000458040d407205402520258170811184041c9030b003410f108001d24003030380c0e140c006519008544464a000301381840c106605140100329507030540141820010a40d00501403980540c2c01003107541424000c4180c4860304551040c20289405549a1544c0d600d4034071a04001641380d140060303004240584104900c0100541c1c21700d61a00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 248816007 1250 248814757 248814767
    0xf09051012111e0d1410061403010e060613020a020109080a03020307030e07080a0318030507060f1b0b04030302031e130c0b040b04060f02210304030e0d020102030307050d020c060106 80
    0xb416580c0585560004400d50b82040c0e90b551a00b2074003e41003541a581a480f0352203c0e00d0310142e501040d004d585158902c5031014000e103005004d41a0306000d5640d0858100740c01c48244545011180d084032042006030340e502c042001900c00940b0002d69103550251f400c900500050100421904000c2101c202040d85a4040d500c0760740180c0741000500c2c03180c08440e55030041e40c0f00d011881ea05c180007450010303110701007807001942a001000017450700d0341d449a0800c0f210303800040010740140506c01d120f6511000e5026005e11109401d04c0c101e1550b25240d0003240010710103814190000017056401200c40700304001e03070740d03249182c0e840c41c100801c0705903080e000c0c1801554034403041000030515203001022541191440010311780307070a103040b4080e604136100e4180c030800e50003103040407d40b000389211030200e54030014034041d0340c03403500740381c09003590042c1d8494601580d40c00c4810300040c0d030000100c9802c00d2180c2815a15100c501a128011340320301d04103039409000311000002d48607000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 248817257 1250 248816007 248816033
    0x7031502040302040e15070c030c08030f0f0a0603080414310b03010b03071509030b010617070201020903150c040b1207030b031c08060105040806070801050102160f09051012 76
    0x4c07901406010140403000d5640c046d451582d100a00d4200042002c03180505142c0c2e50043c403038184504c40b076030315444d1412180c00864449524002e4002041032240e0b45900c0550300544c00076040150740e0460f15401c82502075030266462035015101c4040c110350714a500803122003000e1064608941c6807000312610f01c110080100c0002e800e2940c196114601801811030600c3c01030b00500c01c443c43c000d0110a420303841d50542040c0411440007101281d0355800c074501914140c0c854a4503501d03500e0710342050001c010b00c10811a4818464001d950b903010641183d10421400c0203c11a05d504080c03414511455004c0b20110030001069000c607100783c03042c14411b0140e074030304101d003d00c1c9100741901e5419804170740b100c001c8603c8402489034065011540c010006260080c1400e444401b010b19000090300c03082c0204005100400083d03038108007400a0b2200d03040100c0c041850103005c8200b031050f502a110440340c68800054414008815403402450142021a0301001d542081880d0281d9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 248818507 1250 248817257 248817259
    0x70909051302030601050a05130903110625050301180f0204050a03051f090b0f0405120406031401062105180a0f0c0e0c0406030c180b0901080108191407031502040302 73
    0x82c1300000201840e0400f130b24001c0b42c2c8040c102184244a1112100c024080c0340c1c1c0840030b1100e92200c0103800340c1c081003420312441d061481110000318600c070701245540415118400c0000400050080c0d8084e0110707441400009100807504110401204021b40170715088075802881c4010000103022000440c3c41401212041000c00c010081490038180c8202c400e024024011000124600d4595440c2d031130340c82070158041e600c1c0011102004010341d4015440040025200c080058040100742030440c014000c50922003c0c1c3c01da846401d1200300079500b04141126920710004040c5917950b000c0c00340c40d4840da0b0550b160001a4600181461381c00c1200344d60f40c00040308086030031840503821900a441200b007890400d460319000b24068040310082401f0800d842c200340080e10900529030b00074214113107103d0f0f00c0b80d0b054400100b40e403c0c140d10a0700381c0d07404410b5080e44c1c216800f40d8007182d0783e0030410724603551042d1440e044c07034070009500c028819150351443c01001195503000d08140c84c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 248819757 1250 248818507 248818513
    0xd091703160e090c0f1c020f030711060f01170309040203010b040626010905040206070c090203060118030f14030c070902070314030402010e01032d2a0507020907090905130203 77
    0x300c01400c0c445211403c46540440b448200480110a20090f000d1b1185920540c0d010502498203c40e100a070303004031800d140318903404411b000700c05801c002c611003510580001000189499020419540011322442c01c106e454804005c071814000d000700c445100000e08190f40e2035a541e1a5811203500612942e0001081d45c50011010b0380101c0d070380303030b9507a090031a0126264246a52075000700b001030000c03644210100800d90020b54910003442c02001001030042e00c80c80d00200142031240200b03400800000b4824050000486440c01c1049440c0c003c102e901031183c1c3c1000e107901c0c6129a415111062040210008000c02d550f002000d00030700c00d03a83c42440c0100319103041d02902059030000c3c082751600c00001e40c0d1354402d52020301c40c50070040103d02d4440c0390901205e900d0f0000c000b1140525154a181d800d120b10f0390784403403050b188865840c200340d0700980004215001e03400000f0300c2211124003082403070740700c0d40c0300c50040c00d90301c04104101e040c00d20002a4180101000302c0c0680 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 248821007 1250 248819757 248819777
    0x30702010608070617150d05100f06232106010311060a020c04050c040b0a0804060501170709020c03040e01080c031e0709020c0a0f0c0305100506060d09170316 70
    0x81004100354003100e04c81e0301c40690400861a40d005843c4000308440344a0f02e454511503041ea4030420711007041800707a00500410120300c414041900c50341c50201c10414100365013048051340208034000081c02492004220781b00003c0026140d00c02400d40030308440610f000541816000b180c0ca9040740c1c8111442c0204201d6803052224900031110365401581007520140d0950405800540d840350290b401c6614042d1503502d02501500804204e4002800e03d00420040205904c1414050700c00f00b02e403c14680d0206440a50321101402034058541d0017081207039088904000fa1000341c072012400c41d001d5030b16076181c19920040350301c1c0e0301e01c203205035103413281c1412a80e529070118000c0c200241140500702010103020350b000c05001100d901c40c2c00a08004115004400b402a0340304d404800c031402d1440c1022031605960f45084441c440c80c7c4400c1c0a595a2074504840b01c490070344001185c905402d0804021024103040c0c11400d080c00001000000d4060501a410211568480329842 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 248822257 1250 248821007 248821019
    0x809180f010801090b0a1508070b0a09090e07051926010506090f130f150c14091008090c030a032a0b0406020f0f0f071101030903120e0705090c0307020106 68
    0xb864043c0005072011740c2c04004a076002c51160461001040c501980702440c50799007582070300d0909194400310b11284046924280b966100020340300403d0f1107001480070445580015403141c01c0c80c8a01031240c510344400d00c0c0860780038800b0000400c0440e040240010110b414030183c85582d54401d070080d40b0703100006a051802c4118140110314400e682100d503600e1901e03500000c102040c00b035881914030640a00020700c500ca030301c0b13055036502c1004540e085000001400d02640100c51088244050000c01e84a440d07a403104050000b83e45441c40c074540380e10640c1820500e081c203002c0d8040c015969084141500041d1400c0e4440a001d030240c000312a11441e80d0402c0b144800052411041002260200e0010707006000c8003041060a14607284400d03d40b801103070b00503411141d04c01408100d41082c000d006003080880442801c0a00c48815182c1e0700901080d103440e01c1080e001c1e520200254002c604000303840143c3300240000d07905081400340c0003008d410440d0a20300540c2042c002143c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 248823507 1250 248822257 248822261
    0x305060a05180105060a02030c16080c0a1809021c030822051f02160506240906041508070315050c070b04030305151f020f0c03030a0c0809180f010801 66
    0x2e0301c1c84021049a071a402c000c10400107070b000d0240c0401b18402480140c099100074000e07041555000e0700800380d040e288c5010700d03050445d400f051600c01c44810004103c02c2c00d10010311002c03050711900c005404038551000070035004401404681803565120701d4420150095041030003074880509101da0710241c0c00f07220001401103003001342036800071044a00030b03114840c52405c0f1484036580160404164020012640864087c10b0b00d21758040310500c400110002c040320b0f00410003010351015408180c0c0403410f410400f801041c012640d0b100c0200700c4000120034a0017400c3c4801c15240d1680d92400c06d410320210044c1911000b5141c1b2000c1030954204a003218079090b0b00c4011909642e40e9624240d0080c040180040c0b522120450042007582d10f40d5180040c40315000302d451003600303400c44001c0c81c1040840c2141100c1d4010381107a4941d9030000305540c0000c1852401564400e414981420240900c10003d50011130800d03040ca00d0b200d48888491243d00c2c4800916101c0c1e07a80d588640c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 248824757 1250 248823507 248823529
    0x318010e0f070b130e190c03020910120f05090703031806020a02130209030303010905090c0f01120c030e030c0a02090c091305060d0506041235250305060a05 69
    0x7429485104100320b0305255030081d1541d400e07214203070b400d0a40d0352040848200c1c0304403142000e894040d4160380b062070303040c401c030f4060144616045041071103800108000140400d40c0105011040001a0700304071240c01c080030349031115109010f02c0c08d1424160341d6034200e9000440100d155100c44560000840c10158122007203540101080912602401034155000441c0c90313106030200440c0f01181c4080000b94002d1a8a1100007001e02d441c60743c940c2090380030b2981c8c92081c0907040040320140c1e070040280803034072030714540001d80c540006420340040c588942030748010300000ca180c04903250080b44035401c0e41c0c000c3c0e60801704d981c1c1d10400415288202d0421941c0701016440020100100d03500c500d9001202411000500032103845103803410310121002c985d06001c011207074a0886c0e10450950203841403071301500a8203d10300512200c01901104000d0000d040e50014802807200c060b04035102c5190f404c61241c06402d20307001009004202d070b4090242c00420400926810300d2944d40d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 248826007 1250 248824757 248824783
    0x1208070f030e060708100e04030f03112a0313030c050907180b1819150314150102011407020f010c0f0507020d0312020c060a0b030105042112020318010e 67
    0x40f0750340b00340b41038803650f90182050713030402c440c1d200c00b2984240307502e10a80501d000c2d840d500105142810010155040d407042c01404c01c0c020720007605c803c03400e01c104100c800788000345174800c103c0011005185002e04045000802c80342c802c000244640c08013041c0582c3c4d01502ca441185c0c0d41c1c1007080e50002d0341c0e0300c481109020402e00410034411910050f000c0d800801e003e00035030301d64100005080e64500301e00c0109528428a00b04540450540580c11417140360505001c2c0aa0040130601d038401e0051030050080f0301c84048807010381c070030742c00400c04040c1c106044486050164001356a1041d04070301e4802ca41c0b1300424191050b0013000d054104140e1795844529100440d824801c485001d0b000450922002108201c451350305030002c1c102110990300100301320301d003c03403002d41a22615101079000e42d02d41828800401c40d0f00140108003140a44480002200c0f000c080340e081e0143c1c04420304003880801882f003007401045000005800440082c00044501d140180d02da818140e17081d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 248827257 1250 248826007 248826013
    0x1020d140601020114070c080f030702060601020c09060d0201030e0c040603080a02010614060405040207030e031e0613020d3305150a0506031602070302040e0607091e060c0503071208070f030e 84
    0x7a001b900c140107180140f441041c000d07003400f4110030010140d0300f05030740702000360300070a00b00022541e0400030141140d8045880c40c105040800201b044014079501c0a4105900d602c001418842c3c200914110800058400c0008503600d00307220080741c008007490750042d4207007040002c0c0340600024100184070001c00407460706e032074882000020362006000700c06014009034490380c01d5409000e1102003207580110131142c1e9206111007801e1120003816210b502c0409030b0391101580b59a003401d00f0041d4001e40b014103116100b280418032a40c034030200f11110458806a440d44030f6240c0100f4000c1d601408800110721150341004034400e0345e4060355130803000038000610045d0100c4441805a42180140c54803a5165000b1806503400c88205000581c03180c8180503604d0f9010f03584400500c2c9910710113013a158018401900c01416214010411920240800a011050003210781301944105600c804513100000584009005c4502c400030400003955044224041d02540e900384503e6806 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 248828507 1250 248827257 248827261
    0x903030402060405040506010c051204080f070b040501050c0703063209120904063f03020309010309081b06010320010c0b101806050a050d0b04020409020f0301020d140601020114 78
    0x9005c010303c001082c3c241081000032400c404a5001d2020708803441c0422003466070f0b6070500001914220b104103120030148c0c0a603100700700e409000019103050b9102443c201c0d56a03500d010202d0b107491215040030300000d1502d40c4440d46200451030340110307141c2c1d24110407900300400303940c01c0d04001c1c00c860b07880e5580c10404049011507680001400d114a0041c80002c495460307400c9a54920303140440241188541c1206032480200748400d44400008005000c82c3e4450950303000f5180e0240851290525031990380b0041084044015205540c0442e54044511703980c0c002482d65840080c401501c00000d469100c3c1034010203880381d090140c006840302000c0d64142c4d690544d1041e80240b0305c0e1042d2600341c002003603d0030342080841c40ea88011201103590390611042011000796030f03100c0b43c45a03131080c480c2000174001e0f90b0019445074044600040c000c0460002c03d912003a51140f01c1ea1551002a01c0d19006020780c0c0301404880c94108803241d650748810041e4202c81001050402990b00100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 248829757 1250 248828507 248828509
    0x3080d0e030d0c14071e0519080d051303051c06180b0118050f15040305060705040f0609030213051f061110060b040312020102070501090c080f0604030f0509040e0f01050f0903030402060405 83
    0x4101d19142c4c4202d01711070290321440990115064a01003c68208c12700042c502812403141c01103a070441007900c091f02c021100d03942c0c084d08600c02d0300b4a02a0b030704105007501841c2100e540c0400b0040545a5441d905000240b0b41c807001032011081241c08284401030300a90061140c00210594102404d400785555104040040c00400d2101c9004800020040440065410f0001c1d500030803c5d5128503403254203150104203004500d4208008110940404002590381c40d0642c0316588040900003a80381c0301c425980c0300100002d400404136004400f40000d101c2d07440782c01281a0803a5200703541210344203a1001e002d440c0e051142c2da028290901080c0003080e40c0d181c094001030080d000062034000d00d42e075410300355911041c2c05e841400203018100004c4d10180080c003101c08110001e803085207030039039010386030382e004898020070414003182480e40f94580ea480883c500020600b114800520888410f01909040f2a0102e00c08144000704401c01030000617680503031350007441c0c142011b0600b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 248831007 1250 248829757 248829803
    0x703170c030a09020604050a1706070201020903032a0d090f060e0a0317121302040c18091a090a151d04120c0206070302010c08061903080d0e030d0c1407 67
    0xf082660f20850412002406555040040005140041810607041c520382240f07410500000c005130309690040103540301c1c41ea401701c100c5000c510789040900a10702040500f580480401410011a11038010417401c0701c0c4e000103004080f520500d10441c0820f4560808039102510030326003942141a03d001440000e0200500c0100b0030045002d81d42000d8082d001c161101d5002e692042101404407150310550400f4010401d10f0040c50400480c480e00d82000b0441080c6c0c42d108960600b5502c0c02c101d6582c0140c2c488502ca03250000300307410454100006540d000700a00c0c000020035038a10b01d40026401000c0d00e0380014031030705420703c4200d079880380c45904541803000220b40401840c50700303280046e92840b014100305400307503000040c605101000034100c1c2d01c000c0e0040c1d01c00c4c1c9054048000005105c0030341c10580f54400348040d156600c4581e202c020740a034402041c514040400c43c00a807c206030b2000e650345180d40c0e520f0202140c01d01c0c00c80e000e031041d104050140245c1c83c8980c09250825 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 248832257 1250 248831007 248831021
    0x504150e0708123402040609051312031b030509011b200709020c1506010e030a080708161b05010c12052b02070c1409010e1e07050703170c030a 63
    0x100315802003a0a00c84c5007050316004803411500342d15000403400013035042902c201005000e00c00030410840c109054014108030b110f20004004c1e2a10408404d042482038101c0205082c0e07101000d241d50b280504090080c1c8000c0320702c08869171902e14100c864045481c23000e0560300075902c50003000606000706101c8000340c9103d04c49284a0440c1c00900003045200400d04000c4a0014120035017604140350322003c00501454108a03000548107200e07a400301d040c25090380c1c09100d00c1d940714240d00c5c00c010380d4007070754485039100100342e402d0f1428800c4030303810b00524900114544281e141c40d90011f480d1409250005040c1881d00e40203845414007400040c82c1c40082c0c41c0c03440c14a0f0209900304044440320580794900282c000c41c0700ca08201c003150340340014105040100741d10018403004614403100511580444107440c03408900007108451020b034040303811450901c0c42c0d2510140240035030380030400c105c0005e04c5100b00d120011440f5011980108a081c2c0c2c450724517141c403074100003e0405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 248833507 1250 248832257 248832277
    0x1a03070903051002070b090106080d0e0f300f0a0605150d0309050112020705030a050310080f0102030609060409020a050f27011a041a0f0c010504150e070812 69
    0x42840400801d804108103a00d0f03d0500d000581d80c2d980900d0321004592014003450816030401e035041c40800401300e10001410080d1414a82107440030001410400702d172182141c00030601401050756014110b00d03e400c0e89080c115200c005200320308a5640d5a0b803920340c10300103800508001c0002080c94200c15081f030170b18030b0582c0003403010200180015000c2c0c1da04030007185800350100401e5800c0078039050045101e8200b1402c0c074400b51600340e02c9224404000c0c00700240040041d03814101000c807480640035040c202d6803446041d01c4014002d41c01aa14103104000350750004400349020302410b1280c1d40d01820b41e10260f0f10304020f00542d0303030310300744415403149180d511420300c130303054100b41500d000f5180c2224865524046c0054004500ca490086290a04000602060800b0340d20b40314000f2590031440c0d680d071102e142074034103400f0b0405c20841c19420001840240103010006481205000c101080403e107c0d42240307030f07038910511903a801c5070002c03c91800f1800030b000280c40c1e2990 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 248834757 1250 248833507 248833517
    0x30b060f031603020c100f0e2a03070807080a0209250e120f010b100201051e040201020102120a050708010b0301050d11130e030a09060219020f01030b06040902090f0306011a0307 78
    0x200c003007030386c00c02804400890165644103100850b12801c0d004610310201c0c0840030701600f900c2d070101100283d004027100071041d4072410380c8002d507071010851400202100000d80300d00c144c0f41e41d101a207421800505a20682c10b16011401d1250710f403541d083c2c819460462a0400000e00c00c060324130b80200d035000341d4880300446001a190724284002c803169000c103400040c0710301d10b035000c102040ca24a034074401168900710402400c85481c81c6003003512010840fa44a899546100403406840740784903014403200072605001c0c0e10780854000d140500807503240c0c0c506580c0c03203800883c220b01007440b0701c5030301c110b03891410f46c041007003101c015026500141c500384074110001107110507030f41864900075807540001240c90703c0c0c0303601042c1c400c0070b007041e4400782c01180701c10700750b000c0e006c2c40410019203e601290524203047c0e000c0d45c0514580540545443c1d203690741c0b44e00c00e40c02508129801da00074107005d4103c0302d151501040300d50580d00c55007031000010201a49040301604000c200405102c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 248836007 1250 248834757 248834767
    0x915032d110c030a080a0b09070c050a0507180c0f02060a1104030c0e06030d02150c03070c0c060f090b0319050603030c0102040806181501050118050405010f06030b060f03160302 78
    0x8500c0708010940b00000400555072002c1c1c100e4020f024800052074118400d10f440042001652001d0910340c00890324603100c07500d00124203086061511900004019104004c8001803009410081d441c180c400d50101304120520b0381e005540d50b250240d010f1005800032400039203241510791150200c1c509080d411030400d80c407603941c400200c0f0703030b40c20034000340307480b007040100300d14003000005681c2c0401e1001d0840403c44040103502c807800508006203451021000410b4248103511006010b5000b21584051079511030f0007500180d481e01101001840104000c9080c00c02030301228004c454045810610303440c440b600c10010940a012158140009c01c820b00c107010003400030300b0103000318801400700c0b81460400312180401c00c09000080d03810418266400320080f810b45030440c0c0c4282818903032034191050701c00d80d942040d0031913070307100d841c003c00403c81501c04c0c140d030b81c2512601e4808201c0f19051804201c03190040c0c3d9004100c8070b0003000015512600042c4912048065080c054108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 248837257 1250 248836007 248836031
    0x3020904020408010203060a1a0306040513080a080f070f020303010b03040807050f0105060405061c02040b0f190333021e0406080906070809030a0507050f0703030915032d 75
    0x703079101d0352081e242d5a4010062140c0d600d020088440201721903903e2505c021000e00d80c0072142e02000300300c1c074811540c540c0007070f030541c5001000751001d80d4041c50322a84c40144106c040c003080740c160b41c5224000b04250028400c0d80c01110300b0403042c40550002e5040d82e18001c0007205652004004459030702d0f0900101c0300041e41041809002003051001190501d8018184000c480000b800548114010022145840c00c0c640d42a0f00340b58040e60081760001e0507a0115000100c1400070350f4111a81d5500c001c920450204180140c2e4403846c984e40d080c00c83c8184607940c100c641318800040d590b684018114084140d4003c041d0241e060b10841c500e8041420021030300d400039400343c40452504410460510403c1c40403d07400f02075814116410704040c0b010755500d01030029403c083c000d00145500620108015091210134002c08407180769440c1d15004080200e00d00c11a090180c1c00200003003041d02a000b1520100b4584003030b100c0c0c4042161890300c0c01c40320a8115900103079600c0e890541 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 248838507 1250 248837257 248837261
    0x17462a05011401060f050f03060904020a03051207020418021819021303020f09010803041802040b04080a0b070806090402090403110d180902040f051011030a180519031203020904 78
    0x1160002c0300300c000440d0701d04080600f03842040f1107002e0420208020500182c001c0e60709482d00000166041c01003669940f0200f402c200c00c581025040b0321443c12018621f0400038010310f40d40f41300fa601030005203400d151a481d541d00c031502c025800001c280700704080450041910398050008005100d441d0390006034641241c0c8030800400301903607400400d1055061000e846550104261440c03001581341001c415100d0203280602c103004500b04c03602034140c2d8003a4043e07401620503a01c200c2e6886a41c0c4041c0c654412108208031128450784c00082c10107270151a144c3c0c0714100280908001d40c2d070f10f608000d044074000f442203081c440f6092034103c50400c200301c1a0b818003410b0300e842890342268080203083e801c183d80002740c03841c01048144010306007912040d046400030b0f6948000c4181d005002d40710f500030446000c1c0c0c5844080703614000b2651002604e2469400c509503412220386420a00c000280000c01c90728002041c00f40c200b0008a0300c00200041c219246001820b0000c3e080000342 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 248839757 1250 248838507 248838521
    0x1030605101b06180209280e0102040306060806011a04030f121e0809070f050102102d0b0a09020c0316050115060504150f0c17462a0501 60
    0xb403100c213200b5007004605148000a810030130041e445007000090314030040d8280422183c011041da00e50143c403c4411094064802640c5c1c001004d1104a44412419907101c00034031030b84180c034201010305801414110100c9060380d070004c2441170340b03803280c1d00c50031560075002285c00308110340c0c10840021901d100c200d003c404070341c41c1d07140b4140b13080140143e0300d050b2103500500396140d00b100c1c040105a8000600d074103686036010000c2000d40003050031000c03851408180178904030302d61568000c4400d030750380300c0101d114003110031080941d01e4401780780482c0642010500181e00400c07024488503050f245a00100748643c001089454031140d149030f488090b03901900120343c0c04201030000300c1c0b481c031400000b20b5083c80c15501403d0034050003842108034440103458100184400d90100c2149000c030f0741c402e8203529142c624515a40c29080500c2ca401101200300d01c5042d54810b68a640700001105101140c3d65110f0780110070b8030080c0c0b8580d00c00b00c5184e03240581c003801c500069400e0060bd9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 248841007 1250 248839757 248839781
    0x2090f090c0304060b09070f12090501020a0c06060e07120b0310020a0f02060a150e0c0c070f030b0f0106050d1104051009030507141008131a06030c01030605101b06 72
    0x542c507400c092402c602612400502c403032144420400f0400c4a961003019a003002d0218500010143c0303408822100070401c0100c003401550000403600f0200d0b4010740000c01c514410041041100e641e031505070032180e03064650384009101c1075142c1c0040051034002511211006041d075031010564a41a070881e8410380110000c50f6407618000c46044c1c061200550000c0c00c04800e1004880c205ea42504541d000d00a81119080000209407201e03078010075110400303c104203c0c1c40168079488102c100410b40c0c030080b10214580e5000030f0f80b1010481d00039048601d9a11200e04101d091007550002e80040e08100703003443c40c2400000b806940c3e1741c1c1c03040141000c0b500c03240100c42c1941009410404a80c00c520489040c04c00c2c52040d40d03c0358002e180c0040480e01c1e020303202d81c4500e6400d0010400f02d05024010740c03ca18040c131160010440c00e180140c00803801c0326005900b60f001034003652498410598001c501d0058a8800f43c05003c040217800c404200c001d400a0843d500c1800721500c604100b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 248842257 1250 248841007 248841031
    0x231908012013170a05010c1808010c020606040e0a0b0a020417120a2d17061c150b1f030b0105030903181906050309011a0d030302090f09 60
    0xc2109668a161000c00d0300c03491042441c00045110100d49000d440c850340c070709030030312484801100f6010700900d06207541c40b200074440e040c502c1c03d0052032501c1c0e013240c02146100903500015400f078144995402c00f40d49402074030700c0783d0355001080010030700c494101d0124050070720030900203011410740314840d044601006882c1d6041030210780b000b80c0f4a20512189500c6490f4030b0014801d04400da40d01c1300a549000c4c0f01a40401080a9000d48844003d42c0c1c4000041151710407142c201c0c02c40c0d0048594040c0088060f540c050410002d801245105084030644e0711442010440000c00e1041c06846d40001041200c0040042000c05003a40ca0109038003045440d248207596241c001c03145101c0091030300b5400e6080200070503440f8490301411022041e414810348103030352503418181000001000a950075a9500c0c00081c0c850380c000c036032a500d42d510702421f12419481d9921070070480700000d440400c20343c0e0240d0b0709500a5114030441ca41c4641003141002c00e0303660f01312450b48506110051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 248843507 1250 248842257 248842271
    0xa0224040915090606090b030405010605100c02040b010f120207170403030f03050f0103020a0b0d0f0f0905060f0c0403081c06030303020a20030a050f09040204030f02130623190801 79
    0xc0c02d04045020b400c0380d000300741000c00c10060b1507400113456047d540c0340038110f941c0761640e15101d801020142d0046401c4224402c80e0700e0441c0d0080442c0044500035501403042001c0707c801140c07080e011402d20408656402440c01410580c0c1c0c3c00303408003500c03d4003600000103201141940640040c0d2044000038500b441302e692543c0e150040e070780c01c590740c14000951541150300290414842c1d00942290950205198800500c02d40001c08410f0480d64100300fa41a10400c14020380071801043d03513103120f040701041c011054500442e100b41d1004052900701401c0d5504c4080d1a0302015031603103003041e00c00828080342190b01c60f207001140700740c8006940c0c410300c90000d441080c5200803007a51003201d4611481e1100c011045076a05545440c0c116a1981e6900d03000340d85009a9a0440d0082c3c404200881088041c0c0281c0b61400c3c02280c541e11171a50424444080e03403c0c9010361414001c1d52004040d885401d45800054400c000380510f00d42001c16200181d05029640101c2e5240e4441d25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 248844757 1250 248843507 248843531
    0x30501111b011b030e01150923040b0609090a140604060b03030a0c0303020a120213080106051203040e04030903150605041a030a0b040f12050705060c07050a02240409 73
    0x10080072001c1ca5000038800f000b0255000b03100103200c030850400345511403441740c0b0102029030040661204541012001581b1400b1180003000e400c0d0f10b01047d41401001a40088903d50f182072003168000c0303c031045a91070b60f0a10103000c1e00500000320511904d01200c0020b20b01c1c0d481d034601d0101c1c0c54000c100c42c0c44e090800d101920502c0c08102d009402c100540180c4541c050710206481380c240c100580e41c1c84810b4070454584901415104803d84080348040d41140744482134011030302e540307009201460b15802080072021040444120304e03441040704110b0380b90b008140f10f5001e406810140340c49641c03a00c03622903450042d008003801594540c001e020b02e207807500c01d03042500c40c0664490942c2c00302401207036581c1d01c0c0d002d000d40701e00c81410001d0200008112048600349d0320290f00c00741d1482c40700000d44141c100c11741c102c40b103000d404001422010000c060301c1c14290084000e115114280e002e00c0340034010b004076881d000d401c221030790200001c42402800180781140000510001005d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 248846007 1250 248844757 248844787
    0x1903080402180601050901031d030c07050f031504061806050c070b090601081e011d0601090609050c041202040f020a320f0c03070b0a0903030f2009010903050111 71
    0x214210080100041840f086036409025940c05d02d00038200020f1510f40a80341c3c1a12801417003a00c1c50b50b11001031201f41100c00842c010381142e001f5610040440c0a00d410142c07100710320f8030791145200410340040d0103e0360300c2c0c100800d15420060200d03111015902d4503803c3d1745040b43e0151181800080600030052000f02c0d02d60310101ca21301408084d4101a00c0a0716210690181c40400e030060400d45060b034402e62040c82400030000b002c05003d8000141c0b191540001d00c100748000c0d140480014030700c09240583e500c6180848882032400d030034200c05a8010300312003001e980066450390f500b084203020748000c041e06803194440301d44c0403006450f100c803a0030040849882d00540d624482c2c05440640342a92000d03038164541507190301c16008040d00d107000c3d1000c0a030800341c00030309002d19618560301503405140607039001c0c480c0385612409001501c0d03400c5600a41811003040d403100620341e04024044001051508080d07040d07491b19500d0a40714004110034000c840080c880b81051191 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 248847257 1250 248846007 248846029
    0x130c1508011403010c05181f02010504140c010e01030c0e12030c0106170a020f1f030b1003020a0c031808061602010516140918130c0506040b1b1903080402 68
    0x720002d10105103c1170004080d4051065440c5010082e03040600d01c580c0c941111030104c08414080b4a411011004001c0c0030340070544003541c0e00c0c002e012460f071103030001085030341d00960706031036013070301c0c1010900110018034120760b13036a040281d8840704030306903583c010501c1c622079542c800854895000300c2045007107400a50004150000100210000440c0070a1850b070300c0f50122144029407143c503012a0940b01000e40101c03003d0103602400c0901034065200d140c00c49020b032102c441800340c040055080b1f11a0211007008100003206200009205000110020490851403d905075a90407500e00d00701060f590f589060700794050082038a9030902ca40369018815402c0c08082da900341d80050103e0005001e00000100c002940d06156110f10340120301707038a100b045ca0703901803811002c2092424001c0f1012500c9a10070000007607145840340a41e81607810b1940014500481140c40d10092511451045201d0142c11120610b0b07201d0354070400360890103038136446520b140a104000b403031008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 248848507 1250 248847257 248847259
    0xb10050904142e0203040218040c03061401030312050a0222031b0f1205190b06010e150d020702190305100b030610030605040c05270c03010e130c15080114 68
    0x40d0b0224040c00d0f8020300240100034800c0f600c010b80c0ea4940d070022604628101c480c01a00014680c2440104501451090212801a001000712020203408440482428440a030001c1c00711120141103c801b540655006a841d040040c40c1c81d4400158014040301216181d0340340084120400c14800307140d00080204000c2006c910106090000c407c5108002d401840c412501c004001070030044100604045612100c0040502c20040d1034100c2010108a500c207001038001c034542c2104e810010448680c1446041c0036608000e080441040250415103040c3e0340175080440c0c8880c000d00052551004e0360190003c0d000010380000039070706540c0190640c1e4083e0b031101041107801d003080900f03a4141c0340c0c0400b01003199240c90502075920b4096802995201a0740700c00000f16281c00303111788081600440c1e08503065518074a070042280824440d018075800d1080000c0c0410410b60035207580c40d03114581508040e03444409034000902f80141ea0340114000000521180258024030305031104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 248849757 1250 248848507 248848543
    0x605040b0303250204020711010f0212090d0302030f0c011b020a12030c110d080a0e010e06040212070e09031309200904020903030708070b06120a0b1005090414 70
    0x580e50010a40d64420986064500c49516420f02007000d070700d03205080c0043e00203005544610860070f24038000806a0740303079404034005032a40d262560001c02c940300074600c01045142840c076030700c0a200c0280350f1300c04102c0071800200000725101d1422400751018030040c030f00019200003640c00480c5041c0d44032145906550040202a00151446440c210886150320300400d0816645200baa00301c032248200c0c120340d0003400080880c80303a01201d45441280401418410700070317002852405c0300e05480b680c0d40b031600f0400000c2d0150804042e2410b4840c4c1c10001c0700c19059131032801c0300400e10195503e0080780c00020b01d001009400c2902d030b40c05045140020010b51074060000301c140c3c507189030800100b0720046148032035a42c566068030000200a8292650703002d181c40c0c41c5c1d4040d0b00007002210400310b980041021070600700c11180d02821080018010911a0345034026122000cc1c00c5100751150188042a5511101d0200d400b40d4031405007a60030317100d5074800f03e041c800340003c056107a0b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 248851007 1250 248849757 248849771
    0x4060b040518032d0a021005010902130e07141b06010e09030a030e120d0209130213270e06060111010b010504062303010314060903311502010c03060504 67
    0x4000f100b111001c24140c5640161888001d148485a904a841c0c0d402d8000000c20b0500c4040e80105400219070580350341000301d60b03221529003089001d2800000c140742101e03d814091900395101d041c0e003001d91f82c1410484034200100f404513580c80001c0c0d0b00d107110604012207483c050100003603400342c030400c0b080444a20b0a185403640e01d0040f2000c400405843c1c281122804d501488010031600000c070341c036640e503941c8000c0c1201950042d5100383c01a4840312034000d00720300902c03c1d1203034821103004050046241150603102c0114070898a40741001c0102c1c40c40c81e85105206601c01402150042c00d82440d1100000d8607034070059030f103040980d041404030383c3c1c02c3ea4441e0480302920b4040c1009c0740300703000b11032080e643c90130342080b203883c107520000000c41808030403c884190000e40c0070403102c40782d681c026110b86078000c109844144544106c3c080c0004000b0310702d861206030700c400c09120000d5441200d80c1e4003180101c00300000d031755142000d502e00c59241c0100c4d4090304065901344244 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 248852257 1250 248851007 248851051
    0x3060b060a08130201093614010312030b040203041104050f010305120c030408060106020303010305160609030206090301020702041b0e0d020d12050f0403110a090507200c040504060b0405 82
    0x2a0003400307401ca0a45401d0f000301168041d10400001d041003002c850700c41804c07140e0013890348481c0700f009142c0788000c2c00781307440c01e141d41c0c020444450300603081c0119a034a9683c1d41003448900c400c601782855110340e4081880d455920103180302e14011000043e5140d2410244021508058880d0000c1410800180302195002031015400c4070180c03030007596443e17113034056030460049812101040c0951000020030aa000000c0c5058074000c005035141ba044c00040c541e8551141c3c402c1000cc980052000c00140c03510320060101003d01030005803600300680e000804407071200c5690f2094201002e8100314080c0e210b444468004411f4a1440c1d20381102c0c3c0004d100b480c241c0710010144144088042078091140c019600602c0b000c807005511185c50b841d01d004c0c400702c005000ca014210540000400b0075050003403a0080400751680d041002600e4030410490100c0c580c10007203445100b0800c101c03516507106061103540144400640302c0c2d0301c4000c00090380d50281809450244a806420f0b00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 248853507 1250 248852257 248852267
    0x130504020f15070b0a0603110a030b0105010f030212190e070605180604030f0c0302101b150b2106100501050d270b090607050c0307110f040905030403060b060a 70
    0x30804215082000e00701c1e030010120103807050f01401007511105205100c0c49a160740c1054090301d1244112002e029003200900c071402c1c00074400038283c2c0c61820010004d6500070204031090f4002450058134026881810b200c0d440010340b6040400c002c000030f07a12a0403414412581491144170280c45034030318200000b000703030054100c42c03505454041a801d0042d555072088600855108c07605040142d0107041450301460b0510050f801907811041d020191403007580e0040712000003288a001481240c0c907400d208800414004c40025a5070320b5052040c1d44003901c0c5111000c0000040c51040250005d43d4241074024025a80d82d90f6045020711075aa0004180e510449a440d070004200d2a0800269039010840301078500c06882c00c40c90006210001d862035200380d01443c201c0b01a40c079145ca08860606c260501a042a0401c0c03040c0070001d056110302034a02003000b0454000e0040440000d400c544594204131140e03880001e0400c100000340c0107a0a03c410200c0d50503040085459010302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 248854757 1250 248853507 248853529
    0x30b062b0e1b04021c06030803010e090a0209040f051203010b0406031109060f0d14040605070e0904020108011509231005030c0403080c0a050631020a060f0c050a030c0213050402 78
    0x1100d03035001704080c0c090701c0c00c40c041507940c8a0342c060240209962410084000da1007809581080d442640c0099407902c00041c600c2103041d030150004155030340703540b01d0700521104080102c400d4080c0b1032070b00e0311542e00c4a000e18040c103c02000309545a00d0600041d044690800c0d28000d010018403085070b680d42c0d80815244447d4650400c11f07650855072512500400718507145549054202040c8400d00a0543c4801c0c800e4642d52038982c0f0780c0740c0140800950b041c048070700130700040100f4010301c006042241040b59500040c208004802d44850010702109003035070501d07144800311b14005043c0e20f8603000e4003500310706e00e0404a14501f0842c10192080c421408050100c8078000344580d03400320300308003808074580c111041d80d055081c00b80200c0c05e2080c03181820040e0500d11107405154000301d0840a1803158024400d11030a45400025942c50541d0b0b04d214090204000c00301000c80c2c014080344c1c12661090303690130700d544603e104202100b11841e440481040c5002d081000588407090101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 248856007 1250 248854757 248854759
    0x503150a0903020a05030708090405060402030610120e1b09070f020a1704080115230f04150e131a06010210050415060b04030507090c0c03030b062b0e1b 67
    0x70885410030700b020703803802e01d82c2d0000030440c1c4030014102d01801381c031001074650314104450920081d2071b0142084280d00042d124640d015880c2c00e0002041c2e40619114500c0d00c03540c11000c42c3c0344000000244c1410030b8030309520400c4801191920441c50042c0260741e110440d418645200b0700e40c070800950310500c034180106400e841140c02506800d023a400d49006119180003032210030020b503140304421100740701e0b2540456000402d0803c400524800032000103029103440724130f02c00e5000b00805064108400c5410b641140c0021a1000480c2d11036442600d960180d0301c180c040310f10300b18140202c40200b0400d0329141c0e1041c0030b0700343e0b8007150911a40f60f0024020a154503142001b10200340040398850750245000300014a1080d544d0140080b6400760080d1440c4c15955161b40c1c00380c488002084002070940e503010b6001a00035403028082e5a0302404590804481542c14414000b900181a81c080b0101b0580b0705451721a004004810b92510040c4c03190310328445909a007c0d540e44407003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 248857257 1250 248856007 248856011
    0x30108060118150803090a0609061205040804030f14210f0705010e0d0e0415030f14010b060d0501030210090506030114040b19061d0607110d23070503150a 68
    0x3034605440c054000602c42a0146640c43c20a43e031030020941e654400300c103650145030340c00c01c0002d0442c014078500741102c4845d211090040c1c01c801880c0010070008204031200f81c414040400490040002000c480c0c0c03140408041d1450142c555900d0072280038038000500b90350002862010143c40142c4081c2d07010340c0181501c2c3c0006141480c0501010b06a80712148242104a0f008550140c40f5054040013902c04110205a560b500c001c40c0809020103011201001e0303140380090504050419604004400052f03c2c0410100045141d481500d2030481e47d51120014000d5207085003000364540c0b40c1d070400a000e5494080810403c2c00140b054040c18501111414100d0b1510382202c19003130300040404007215204c24004403000710354062040020086012004002c1d0b00c80d585007440c6000411882c107101c41d41c1d90b0f810740d40340c00c3d850268100101801c4000061140000000310070300447c030110618098112a40c507002d030503400300703109600100d20b07406046030925100390040051140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 248858507 1250 248857257 248857289
    0x10f03030302032703040f081203070c020d060c0e041b1d041508060405060603030a020703060b040603081314190909020118090609050c0a051204060e0f01020d0c050301080601 77
    0x80130145588528407540c4812541c44081c103a81c0200c000e006846060400c400403613244e1a810f07035603040341207408005000800c00b08200600a0643c011114401403055040c049903035298020b0328001101c80f0049803420407017480e14038060150144d04583c0b0040c03c0150300300d03a003005240e0000b001c03030544a0750b0318007003140e4940c90725008103600000d1049440041540c0e28170080e612601290180c505000e44800301d450762074040210781005c105503000b080e040342140c6500008150085200781c3c490f507914800000510311700083c05000007080c00078400540341c241040c0700c64086400842c07261481d13000043c4c0e404441d0313610b2415034404c020009001c08691005070795400c400c0804d2040403c00031303000680004150000ba0a40d02410300c02d012584408480c40c05a018004052020031400d100407148070a0818415030700c039001d4072000c0b603010914100c0b241015450700c500d50061750005800d075580f0a90707003d0345600f1141841c0482c0356614203090301d5151801809000300750440440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 248859757 1250 248858507 248858521
    0x20d020319030203030901150b0f0d0b0a0602030d0606030216150204030206030f011d07140a0207180b030c06030c07140c0627091b0a0c05030c0c120105010f0303030203 74
    0x41e14606181206102103400c00609002e5501d41044840c0102c5609001c001031050001c0d001c100221416001007038100305e000b1a42d8042c0e90081186a50400c2d5a18120480760391207042349002000250061640c40b1f0300c1e4401e900030b44001e50095002d02d0300420035040004503462070004e046421502a020b500e84c0b400302d1030041e115681c00a90f101001209000d402684812000e0481e2442151140081d6860b52200800003007242c000d0003240c1040c440c09841a51440100a00650740c03041c1d407420b40c0c40340c1c00100aa6486d0b01d01390045030765606900c14501301000b000e120741c4422112141107140101030f4034841d2040101c000c1c5503503044840305019041c02c10081001c0c140090400d5103918001d104009148445102c407a480040324007514890b01380b02c15449d0081c0d14417038402154031038450188406611600074481040b44108000d400325009201401b004903007036025210507400f2200308504040800c5440309182d241400402c11084024905022254503041c0582c803940c40700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 248861007 1250 248859757 248859763
    0x1201120b1513020708070f0602041e0303020309060903150403081e1005060a05130e0601030b0108060307091e020c0601080609030c030a200a06050402040c052a0a05100c02070e04020904020d0203 85
    0x8021f10f2a4210000c11007040019009401074900001d207282003006900090541040d00380300c041c001d0b0b08104000481410040000c0c1584480a401c65003060f070890f07203007a07002e40111001e40020385618213105400950070002c60042e4241d10391310002d4280480c541450403c1762040c98456040010b480c5800c5005070182c0308030710410017081c100d45035224401e02144104030760301400640b0703190001d0829801540d1076401000b002e80103041c400e050070081070080903001d03030424059506460740e40041001c0d000a011000020025010f10751421800d01d181840252940196070402d0120f4610903200009894200c40c09191442000525442c14030001c80c520b40035885030300401250a081c4032407500701da0702981c401ea80801c010500e543c01141d8a004040b21601910301c080700003110501000d0104001117008815180d9180c0941d0f1403034540740741603120540054403482c0b006803030780e01400014000c04007442c05049078545a070001301403c1000f00028482c24800500d6401e6403810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 248862257 1250 248861007 248861017
    0x203060c031f08010e06010b120a0c020c1201060f0602030a080f10050a0b07050d09050d03030e0322030309050117010603020c0a05030307050912010902090606070303021201120b1513020708 83
    0x8440b10510040d00c07000d02901801c6942d2520b00d207445010000100c000c2c2078421680c03500e80d180071096031515044842d9000c0c160784003d810440c49440306681c8951364804842c4100e01c1c0c400c0000405070314088464052850030f80c000005e642050203d00e024607080501c0d154444403013882d5242c2540d40113100c80294505401542c0c0100b0440008905040c00310014002180501c1c100d845800301c044c01290244098024a0380240000b0800710000e070098010304c1c0d80c0b480ba01e051f07a081c0b51010081c0303c040102401c1490714010604010014580c011403844090103003840d2440c0344203550301000101860601c81d050415600180d504803022040c403000080607801425070f030780c80c10040d03030040044e000851201c0c800c1c0c40d55143c002c00c4000500c00c0728280c586c050203601d0156285c400b0440f4641012409500349a000c000100e103599152441c24045c19501220480121403410301d014216001401125000c210b4008a502036582d22105840380c695a03601582d40c1e036041c03910008078011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 248863507 1250 248862257 248862301
    0xc0213090503040b0a17250203160807030f08090d1d0901080708010f021611120a0b01090b121b010306030501020d0902150301030305040308070c08100b0f0109030203060c03 76
    0x800f29000c04d407007004134020813040c5904d541c2c07a942d00c1491a2455903e0200f5614001c26003440d0380100d01044141c455044000c1d41070058a04113000380382c22501103210b24604441d907990014681c070415130400304004d505d000038500903200380350a15803a80d55207503030240c250900003501803c14104044040e031481c2c042010b000c141442d45d46804c1d070703542c850490003009203075424240a58a81c200d1803007610380c0c1405550601c024004152a40013400c1d0403002101d030001c8464840300d101003020008401c4061041c0c088000961501140c0d07400c135400c10a00c10300c00c0c1028142d55407290f900217200158504a4002e120085000000507402005941d1004200d5400401c030080d42e8466039004047c582d0003a1101c0000d00880c1603120b000344000d000050204405000c148003040390940608021441040b50407001521045c1403843d041c440342d506820701e17860306030803010f41c20405031400458000b0b0903c20842030035540060b0b140d140007000c80b00b0309000400041d11000d54101404000c00d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 248864757 1250 248863507 248863513
    0x60d0906050615070f1202032709131a150d290915130213090219050a0b1c23010e190f0f061e0803030105010c02130905 53
    0x4118603100000d468122100b41c42640303034450305211000110112000650300003001103003088182e881480503e801007544085104c140171015105c0d6130b41c0512031404411400700a094200c0c281003109440c0028410600e0007203101508000034100d902441e444640c5c500e600d007642e690303801002c000200e0710040321741c000125801d042c144120702190005145400c105e10700c2030b09080020207015641640e4540c085e0b0300c01c00b0280c08410500301c0702a040381c0d4207411124800c19680015080ca01d04030599902e2a540b084250210301e4904140d256054483c2518501546400c0005440707080503c00c5500b1600006055400b00c4034080c0030b801d012010b002e04000200c110461281e242414042c94008000114004a001d0701801091841442c400703659001c206050704091001c2d00c24041d891400c1c60300d0f00c1c1c0309005c504180c0910809000700c400768100e850010b42136104010700369405070599410400041c4080c1c1da100b41c40301b821a0b01560b500e00b020070515081c600810070244040c0c000c0c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 248866007 1250 248864757 248864771
    0x51b010c03031a150a0e030d080f0903090301020a210603020109052407081b0604051e1c02010c030c0509030d0e03150a050403031b02060412050d060b0a0807020601030b0c0702060d 79
    0x45449025043d41e1700d044e500d800d5002081c106040c0c0d54080709443da03001c10910000a800a4075a5490725800000c0d40b0540341020840030100742640c00441c814004100c2d590100a8603a00c210032000400d0529402400718920f150006085e840d541d000b907a0040d81c890602050018026204400b9207070801c6e00d00e507948030541041d1489410029040d45100085040080d042c0000503030540501d4002002c0c010590050030140551001d0082c0c2c03180d6030045ca00b510154418600004510000faa000401d4849800300c00030110b40e0007a80000c02d006060041d64120748000511012800450501291402c9050b00003450030014800300c9003018014020420050b1054110602441c445e88081c4104001803054010b404401c1c02000010b0307109000013030114a0042c540d14000452b42032440ca0b00940040300c20640399950401c5040540c0001c0f003081d1242d00c08807040e8002d4161015107910350550342c49014090000d00349014684000c00c00c4800d65859904032003058414070301c100022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 248867257 1250 248866007 248866039
    0x90105041a040e010605040819140102032809200f06030a060501031d0a0f081308160f0501080408090f090a0b030607030c0e06030405190f051b010c03031a 68
    0x10b074000d020341e14a60780c4000c0001403403402902642d06848403400600700c80034480d84042070b0720070210741c2617580307128060748112011801e2008600802c000b02c10441c19610503e1a01f1720355504582c00804540f0b0508a28007080d00c013184200300800348080b000d074441c4d11000042d084038030510b900e0341c06040042801034108255116108650003a207041c0007100443d28600b031000018561046d071070700199403400007e034842ca009003480d07100305140c0f420050125500b1510141542211066900c400d060785240c2c80481101001000c203200307100300050620340024902a400b4000034041c02d808200040d01e039950880103258003c0c080c112440d60314201c81124003900700050b11364020700945000c00d40f80303407003402000ca650505440744e080c210315501c18441960301c0100103450500035021510065402400741d00d289901179a607442003d8081d05100c0e05005090a01c18244180d80c074524000b43d0300103000801445e0182000240341428405100c0819034080016038081c00c5c40c0720f08120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 248868507 1250 248867257 248867309
    0x10806010e07020d05070f020a0f0b04090b0a03020d0807050a06020307030618060608071d04020c0604020307120b060d060f0903020706030b090613020304080408031c0b0f1509010504 80
    0x40381e808240c84003064440d408180d803621043d2454000040003009058003040e41c00595030076081c4003510303409082c1d59400315224102c12a800c81880f00d0000901040440750a005000c08070508880c3c84900d640345034006940c0151051005043c2c0c000400c07072000f40304e41406000416500310200f90740d24030f482c240043c004c2c021381c002c070301d00040b008598060071222841070074261002034480000c503454050042c0d50001c44100040c4d02d00c1c188800940c03031500c5a00203003007180560f00050003141814030406080002175045119100c103007881010104403d111300c2030f0042416141c010380005c075800c0640180010210b00c1c80103070700b002d0b1024105030b0f0000f000070840b01242d07020020102a807040118034201a82e010340e100703c111781000a070b031200394001c640051040e42010728007940c4a00c0300d801c5402000f4103820b40c08241c18642d00d007004a0003181c060440813240701101c0515000015110407140701964546000481d0005c00742c0d014130308841c0540039101d0581c10b40d0f6480c4048083c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 248869757 1250 248868507 248868509
    0x310150e070206090d03050910090501021e03070801050409030302121504061e03060216020a060c060518060403030903270819051209030a200a05033f0301080601 71
    0x4200c810000003410340784045401d034018045803015040f40c0b1300044045000c3c00d40501031100d1401175204901d18040c01e031082140300c6103e84009130301c854056000040c0f2407a40c04400c0b155010030010003101581c0a0081419640304503400140c0218504088009010700b10240d0030340320350309007440724195444010f00c1d08558104c0c0c0c1442400d840b115030400320130340900c0360740c0021210001400040c0c2c4a03009482c0c0c52a41c8101010f06c483e1540000c2c0000e80c0a6102102003082045003805000d810700a40754000c00c01d40720142504840501c2d135175034020085c000b5082580e0389469200b01441545040000041d160402c00c80c000b040c1485090281203100c0e0415070300c100305444c802440c940d50000c452640000c06080f102c14401d504400d00c1d486018043e5044c020015808006001d2452182c145041d0a040e1542075194106101c41c0300d206400c034a100754000a0b0b00c4144400010030703c10044a042d100e4003195118901c4601410350340015030942420100010410541c001b031564 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 248871007 1250 248869757 248869769
    0xc0a02030c030c0d020d05031e1b0a02090a091109010b13090b09070f050408011d010c0c080405040c090e070216060503101a0c0703110a091a040b031015 67
    0x9400740e0044010075603680700c0d122180350050f0700f0740f44030000352a042c0b034204005401441078a251010004280c400300000341034220315a44085601c034940300d1301941c20329400d51000010141c4103c00d80015030422002804100c12940b07920482e000c12007241d507908200c00015101140b1543c4642c007004030f82c0c1160ba0064045460b0010003d203220440c010f80b2070b401000b514031102070301d07005004c4625985c020385007410721504200004060f82c09104044040c07a072030583d038901c80e00c041b400c10b0a40e251054040c04201d503a10000011511100440e000c8807170403180010341c5900c8a0782550f145441c2c1d44484d403210429401c0142554000c924860100300200a10003802e807941d50686d500e01040e203505601c120030741e1080c00180707a0a924114000640c0d0b100c6c03030620340c000030018601482c54200701c48030034000a80e101141068140b00b00a001c48000a101400441252544c00c0b0b0030220150302c00c6444607513030300c80c0352030034071050f192010488402c2c0300d100300700e01d40c1041c0621284259 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 248872257 1250 248871007 248871013
    0x906090e0c091501090f0b0702130c09060f09080a08070204140106050304020f010903050616080a091106030624030709230f370b04030203070608040f080c0a0203 71
    0xd2111030308082900c8030311110041601400c0e072114400c00040e44801c0c0055414010420808030b01149815040001445890300d10b0b40c1e11001c80c41400441d100c140030b104141410712009609594000140f50203442107494004008a4400421503100d40d86501c41400c9000c0c50180388248141040100000350094070141310321450044002080c400074440c45000030700034404100140f42041211004aa052401628440d1682c0700c140c105141a501100b40340c0d641505005503a400490440d400031040c1810018122242c9551515060344003003184500c20010008100340c3c0c0e81e405460074114507200d490010011541c1084180c0c0c0107980840109034800000190b042002c100746d0644900700548210003650078040c0075144400b0854039611140c02c0141e140013071000100c2101d0311000320389082901a00703200c000120304a41d08a2811200e0030442031025807400074581d000c946007403400c140142c0d07440c10248100b002821000b41035110001e0720507064500040c00c00b44040c022019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 248873507 1250 248872257 248872271
    0x402061c09020f03060c0f030406060f3503040b030a0f020301120302010506220b0d080307020a1a0103080a050d0605030a0809180412110a050105010303020703030f02010203010f1403100501090609 86
    0xc06645d40c200701e54080a14004105610240c0388042c00355030003510807400402d40b69220000e1020f2540107400c00c2e0104a400518000440c1001100c1c00003c14241d056405600b02d08621075202c1c8198080e060010301c0003c0420900301c62980410b0421441c403108549a5031a401c990000e505010415401982840003090041c80c0c0148244c40700d006c80c1021048401c803443c1e1f01c2001c0c0c082c3d140d005902105101900000c42d103181c004500c00c400302e50242c10514814a4091808000103003441601110300740140300054040e42102c05000040c10315a4803101d000f02d04d1400f80240ba0003042d014000c4014180400c0b5a07000a04140ca90071209981d0a640d413070310416120b074007201c019040c2001c40008903980c502401d200701d00c01d002071003032300c40300c1000ea21101d0a4510a901c101c3c0141c1c0240000c100b03169020508148451081c4029880c65141c902e2482c0f40004502038266a201c3c2d020080c0042d81d41000310f1415004441018041c641c0d485208500034016403003415105414000c07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 248874757 1250 248873507 248873509
    0x70206160305090a170606010c1b030b011a0412140a0804031a1302030d1d090c1209031216050d0c0e0a1703030408030a02040e0c0702190602060f0402061c09020f 71
    0x102641700b034214900030302c0940c1e41c00004440315440c01c1415109121000c20301c14070310300c0445c14003000d140192a003041c0c9515091441002c5410350b0700d8040d4045041c00107118401011100c00e4643e6041004562013042c80386000382440703c01c100003020404001380001c100030180d14400c1d41e4440b00342200c0401e999040d00b1801c1c1c801b008200a41c103030044d0b000d0060090007000341954048001c0b101480601c00d10340844e55030b20040c0c07031140303043d81c5c0030440a183c2000314601990003038094014600b0704240c1f03030703011451600280115144e0049510315240c0c05200f1416142c0309074002d5000d001070b00d001040174000ca420410b8882c02170121040102d8a4a000001844000c00d8500198510b5480751207141c01c54201a25901c2e80359020840080c0d0400346681071806110f0130306145545003018410006403100d881004c04c0400c603410300411005402181569121200c00c60704d0115075118030004400c5c0c0310705c24240c618030440360041c0030703000e1182c0d1041d81103c0c4240c0f420791128a2142c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 248876007 1250 248874757 248874779
    0xc05150c0f0a15050c0d1a100504140411030114030a0b240319080f04150512060d0209010e1e1005030f0f0d05070f0203070b121501080a02070206160305090a 69
    0x142c0c10781e4864010001b0420000855000307541d17601b02d400c9011021002c805c001000e004c42c000c1c0c00b0000402c00302c3c090001a03162058106200c00c21513080113000040c40382c5013041c5c0814440c65820841802c4034201c5a103007404003407403c551284035503120f03240c00c200e00560047c4c0c081da162070000011715803e4480c100041c0b050400c8107142c4d000084e0070303242c2d0384a0100f80c2c811000101102c100744000151600e4050010b4a030f00320070f4440c0c0b5119503542d01e070041912002069648107000ccc7d5010343c0c0141e00c0b1007240300e06458840807805200d98071040348a80b01d5128142140300341c441c9004010041c1d20f802d5264040e10000c0341a41c1ca5589915980c81d80c6450349600b006540c0c10041640003411f0042000300240351203115042011401500004d0608200381c2c031180e1070b13100015001c01d03882001c0031000d40c0199070013444000c0403103403000200703030748401802004404d034001804001d6586020039110001c00507a81204142640c1c98000e00a41105d40401e020fa0101c2d0300219402d034450b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 248877257 1250 248876007 248876011
    0x90b0601020c1c02040605090a0c110a030c1203021204060b030d02062509080d05040906150e01030b150c010902010201050603210901030e030a03270c05150c0f0a1505 73
    0x1e00c02c90b401074004002200f1440401c200b26070065469000040d1a210350401901c1420841000900000102000b0341904002c004104142d00090001c0000039000001c2104817a00f04c0c8450700c0d88146040c094009100f400c1c0410120302e0341c0c1d0108410010103411440c0c40800960a680090004920503a0748250568070381816044c20009003803030b10851000c02c00b404546107400c0d09400e43c1d801201d41014542e54030440040c0c0006810f1003102001c4c003800004100722002e015001008238070040c0342a10708007090b41015155803007101c103a500c0312400c01c52001c0140440da0385140340048a402440c0000089025500f044e001502d1498041905101c010302d2848402c101c18042c804802c07180d0010380034505040e5143c1c00c86000307074404c2000d800c03003e2903520b0001c0c03040688201c03140b03011900401c034405008032800010014981e020751008a07401034500d42c0c1c0c4c904c0035210b4601103000b088200f1046100380110080000d030001841c940c401e0049141c41090070254011009541d01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 248878507 1250 248877257 248877259
    0xe010e0d0906090b0901031112060307060507050607030c110118060501090219080403050f030f040b0609090705011101020408061f0909120e011112040501030509010501050904030f02010b0310090b0601020c 90
    0x4514010000c44c1c003076200800c9039000c149400200c02d6000b42c0b01200d031340c008040205a105000d000c214090404102400c040c000505080d400d0035040e5880e1507230380750000c28a0017056201c40100c01c200d4002c034808200c080b0030100038003001025462051402051000503904503040c507000240c05005403007224081004046401078681c00c58500341e6a500d0701401c114100841007082da000c10346000d001d18001c0300044412003c504045c00d020841a002504c62846031400c0f1040c000600c41c0000c40320308550081c04c28104282c0403aa4203802401150300c9071504d0b0080008100111400440003644004140d030860149512026244100c59096000a240510042d080b0119030301600000e6040d8105140038003151101101c451b0070480f20000380d861101010409004568050003050741c0300c503984000708000e40c9018000303044c0d08000303000034050006246000000718800c1d00000d014003000740454108022071500c4c400200040c1302c0c245e0701c4203c07540125030030750300c0414040d2089034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 248879757 1250 248878507 248878517
    0x140d02061602120c070e15100e0913050718020903240f0a1503140f0a1208040201050f0c030d0f0b0d060b04060f08012a0c150b040e010e0d0906 63
    0xa043c0710000d409074072100f03421000d403061040c0001d160702d480f82d0092050240c034015141c907081810070b0140002c5203040e0070062100c50100c4c0c2e44252102107100358045081200741408500f507050203400d142150304500c2d5819524103034051f0840300c0d60018a02000c090341160388841441040c0061041002118802864500d0224a00e0502c40d1511500700032800e00005014001c1021000519410350040710b0141c8204a0819020f00500010303a00b1490b4401615140d4040d9a46480c0c1141e1504510144040440414190391160064600c2203003c0c540030399843c4204000296a81c128032495020385041c4180807840e03e400b80141025500e0160a00c00b1141090b03607100050714079601d14580003555603400007500320040721554001c05c21000005000317650307200c0320301114000008040440c51103841568140d130b40300b000e4501054214102c0c4510980020030007000d403024600143c1c1c001c0c1032410301c80024006602461b05040800304070307101c90000400c1510b5031501c8c0d103d000c0c00b00e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 248881007 1250 248879757 248879773
    0x9060903120302030a061212020705150f0d0e0601060809070b071101080604020d0c0909051515130905040524060310020c10020417010e151f03140d02061602 69
    0x1c0c003d40146400c0b0103002d5021910541b201c6907207500f0203101800380c4110000510544015806001d4000546030070f80b48040d228006038241e007468400c0d080038564070b841c00502c4c61030104a50f40000920083c0c6420740702c055039980001401c0301800d45101c626401031242c00079501450b0411211440d40c072441c640d00c0c4071000f0300195040c59001740219002030302048079858000c0d041c422041014403549640001c5800d00c0e070031000310b860040a50710a0f43c43d990608440f6034070000c0e20303040e200006d10a55a2807000040050750f944595006001840c20041070004015022a4480b00d844456200381010f0140e00d401d40700c81582030b2000b540680042015034000c0265800400580c07100404030380401058002c80012688964020307032440c900e090748500c69441c00c5c05245001c8003440020111420302c05d00441c401c100c0680f103000e00e0b00c08030019800104001d00040001c0d6044040501007803100704c19a6115800003000400500031340300003400d02c4118100c0b0b540c0c0000c00340e000301101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 248882257 1250 248881007 248881043
    0x7141305120708100e06011e0e280b131401060c050f030c1f020903030d090f06050a02030a0b01080f070f0917010204090b031515060c011b09060903 65
    0x6603000941c60784040c0500d041c0458590000c0110041c00c101c002d10008a00c10300d000a903060020603017142e8035201c500080304580511a20740c48064808112040d005078590303401e0781c003041c4140904800c412100d25400c1244c10a554803171012000c05581c3e03c00256500803415088030324455984881c0b005500050218901c180003a685032071041c0300302d41c01c060141010303d1070f40d009031124540351f500840d81c020252542641001d5100c01c0d483d401d5007000c144000003174881c020107021b00035050343c03440d4007001d0040b4290360300c00d40e682007802003009080400300c030000796004403583c0620307d0501d801056254400c1381058460001aa401a8030303031503600703040791628040ca1600041102407000824036503421103001012100140c001641d85140c00340c0d81c2c050725060300c402442074204c0400c8107500580d400c9025400400c00c0501c4024000550000d11140034901c3c000c1102e628022240b0058041441d640ea000c982d107407190803c40d03550382c000302c4481e40180801401501c02a5030803241c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 248883507 1250 248882257 248882269
    0x60f090b1b0c01090506250806040504080d1b1407020a031b050909070602120901021e160902030603210a0302030604090821010b0301050109050f04060b0403080307141305 75
    0x19181c000c103803241c9050400c800c0b10b400c4d21110682a68240c000005000643c0e0030b01d0080441d030002900303805450010708101074030711580181924021510b480002d0100110381c011101841c1207074a00301300142c442c10050b040e1980020001000c56240390007010304100a106403840954010300d140c02050655a400044514041944001840070000403c42d50340e126541480303180d03035030001c004451038008000c3c5084030500301d0315070f00c08041080c2c140b80e9038045100307000c55007400d0810395140f484202c07180c07900489680c0600030b4141240f0100740d200254001b54006c038412000ca230908500514030645240046501c5800c1071800c0190683c01400b0344c020710b510010040001550fa0b0326512207240c19400711444001212030940341503401c511041c0000d004d041c2c0c0503040c034115814000041c000403101c0c020284900c50004100e4101d90310383d00a0030240400c0c0c00c880d9102d5070b0b2460810040d403c203881601c04110440e01d09681240c104007907942c101c0c42c119011651910b8a014010b07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 248884757 1250 248883507 248883541
    0x415030f0606050d08180a0f050108060a090c0906030e0d02071e080604032d0806060708040f15140a091203120c090602010b01080603070611030c0d020a060f090b 71
    0x148242e1101d000080c10781d034102855060030b01504826036242144250145021000310100348035115140b0705210b43c040e6202c0c0309054800c03e092019a0b600c0e00d6000600414907640b18200003800c1085518180da4400f21840846056032014040d2005680701c8d03640307842040019000581c0b045000300442ca40070140388410b251b0010691008940b00d1145505101003180c1c00c0d00030034603040c3d0314600d02128016503420f0b25287c1d001a20110071301280203107203100281c80117101c0c0d4000b10300074090000720f01c1182d004104c0704034407050a5503200307100fa012811352401c1c6004100c07000300003003071410b20004603807075a43d0700d5039020455801d05131907800c006800310003601003001201e02003940103418411106400b2164560182a82ca8950000d0a44095044031810442e01105000b1252800220f03402035490b0343c00c0c02050451502c034800e00c0c1d03001c2c0d0300d403002d001e01c41c030310008a056401003900b981990017444140002d40102c420001503540110004000d46074020000da010710008805007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 248886007 1250 248884757 248884763
    0x406030b0705160b0406020307080a0504020f0f0307050a120203010c08070206280c08150303120c0a0315060903061808091203040512011b17130203070b040b0a0306050415030f 77
    0x12a0940194131002154002120100d8602c1c0c1e000040c410074541181c480703544030b21170030350500c01441c003980400d15803060481420701803c80821065103d90741800711201070070000e05030306441c41c1d54180041d942890800181d000b9403928208400480c46a60f190344150f10903001000c1036140d1800e858041c0c0c102c03840346454008203000e8800c020b40180900780c0007111030b9a0700340140c100041042499140e848845110340d004000060202040c0003c00303505c103118001070f5440c2d00c0141000e401828804041003800e07800c2c2000400e0182e00003010320b0907070380660010003250100164a0001900004c400b5029041c00d01c180703025483c11181591554407118140c900b07099403480401c4108000070100c40c2c4994641e807074026028818002074003109442d08e0112402e0020810800301c2500241c4100d00c501c40b40e0f1042d000759242001041c00405a101c180d543e20307a50346107d140310f5080f1060400000741010400503ca18242c010b00101c6400303042511a81031550b568001613403825403080b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 248887257 1250 248886007 248886037
    0x30601050f04091d0303130602030402030f03070f0c0e0103031b110306091506030111040e10050d030c021e09071b0602120403021603210215090c0f0406030b0705 71
    0x10100310710701c00c0504002c01e002c580214400c1001c12043c100c0b0112500704407416030003401000207800c4828500e40d042030300201d00585d20f44907400440d0a150200c07041d202d1910001403010f0402100600880740c40e8040c40310b04198507140c00100300722060a100207400513820802c0b10228142142d25145c0c0c99104542484a985e0268042400c20030110395030285a0030010605004001c03507032003a5400003045000f000802c808103444165400365024040701c0c48022000143c0910f505103400e805410002c08040d201c2d01c407464010000e00505900724065514605081145103442c440c0d1010b8110051182d1030380d13640c1c88004c46034440c1c2c1040003101c800320900d1000200700c05200500d071018040031240c080d403803d410048c2c0380000b02030100164981410003000031411070700480080b46102034400c0f10b500d010703100c00ca1905030403000d10f0360820f05520a011041c000003c01c0c403100c1505a52107030412a0010400c811107040348005007a11000300001401d0328820310080901089411070303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 248888507 1250 248887257 248887267
    0xc010f020a0219080d0203030105030703060b15030f0a0606020303090604290c040f0819081623060c0901120504030504030b010b091c26090409061d030a0801060503060105 75
    0x3e481c00d600f036030410044082500144100101407003e080700b00d80c1c2d40025403441d407410002c02d9941d0003a210160040b035443c4006442c969880c110302c00307107404000d02c0d661a03080031284161040f40c25603000500601c0d00800003001800802a40d201c2c04e00d24001d0b0483d40d4a0f034030b501c1c03184110704018a5007002014007004103800d0b5450030398040c4200042d600d80300c608020340c0f9082079640d1b0b000b00c4403075800500e00320203100d00c90300300c1280268050200340d151302e480280d01403002c2c1c24003401401a00e6800c00201808891402c3c0046000010b003100d4480d1141100c40070355104402909000a010325401c854100030754010607082031092078014a0190307662517040f0310000a070000310741c02d40005800205071510312442420b41524505484030700000f555901c0e940b031b5002c078603580240440a81400d0034648071060b03032030746080904240301040d001e03d4400000c01c05040d40070b800421402803880740c1d42c0008103640701d134501d035100c0310500d0b42840d20688140c0c100601c200e0402ca02046 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 248889757 1250 248888507 248888509
    0x507020307112d0306070c02130c0e090a0c0f0e0f270c180303031e191a01120902181b040303080f070305070509120f030c07031505090c010f020a02 65
    0x40c004501c0303054940040283ca00f102d08040c10a040900240300b00800007070081c0150303075100c1724a02e92404680c0009200a04040e0030350740b90341001d03805070b48250101e042000e03074416908501081c1c2050303501c81d44080c208001c15565880340a01c8613411030508080c5120310b0800500e42d1002c0310800c95200742c0060580b08001c0c162900300d40d908080300020a502c4005041d82c040040441d408501650861801030b0540200e41c00c0b110b515512050030502003603a481e4141c0307500f01c1c101c030000d41c00e02208a040900c103041d0402c201e0104c0c0010040714101c1c0d55800d81d0f214041986600034440691030b480605000d4160101819910b480f900302e020b10110b660a0700000c000039032080d110200c980c98200c3d0b41103503d140080c902c0e030034542404104900c05500c0390464160010480c0e020702801c400300c00d040e00d4010388104540c9076100004801115032800074140086a104040c4807843d9004600c0301001d96005440790386140d032002c50100316660003144031803039a0340d90707104a482000c5a60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 248891007 1250 248889757 248889799
    0x803041403150408040f080a030807050d1409010c141305060906040f0305070509090f072102031615020d09090209130513050111070f0b070903051203010f09050702030711 75
    0xf6800315601000000c0c20011402c03200c0b1030380c000702005400341108000b6910060005440101580108a030010b403070b40c00d0321515440350b1801d90214190b1046898801280741c001c0140382074080104203c030b20600700c1c00301c00e80c1c110741c2d4904441048083c1700d07250134140b100d150400a5003580c813103410320012642441d2208154019030160300140000e91410307050146482016003600ac1c0b540049400000c0100009402012124244154411421702640141002c80b814a0096060050761101182941d0506002c0103961111f0b4181018440c4001f06a07a1410100901e102040c0550401c00107071a40f0b601611810350040c2c107422a8501030b6298800300d07241120f01d025500c502822040134008240303d0213900104004085203060a16107550f022206803000c020131150a90000510b01d40c403402e00d08004507440821140c0b8844117640a006982003401200c0040c00c420034001401419030141600038100ea030095072030051107440382c0b20a81d0201000e1a00115004244191903003d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 248892257 1250 248891007 248891011
    0xe030f1c02010e0322050d02061b070504020a0207141f03051b07080a143c031612140a020304020307030c06020d030f09171c05040308010e090106080304140315 70
    0x200100310718642c518048404803034200b07d0040b0b0542000d240162079903400c403400105030103202b10182c400980b0461510929801058002c0e001203522145143c0008442060751200c1e416440e13034024120600485101c2c0d0342c8504401209288445001030080e44815007141c6011f000c40d220500e010b000020a5102034021031301444c2c00905459010751002c0720005c000e80c501d03038070703031801e6205c0e0500c412400b100211681d08940d45400c240f6442c012401e04e00030208003405042d2640751494603100040448a540408102d02a80040e828a40c621a0800001c01c1460404c00c0791a07144889000b5000100102d07094491141c012010800580c1c440000703243c9680200440031101c1c000400f5201214840e103205420300c80140000b4040c1880d42080f4102c0225154948240440562a90250001e00051289450706102c181a44850700354181c803605c0c41d07881c41c9174440d07141c40c03402c84049204e84c843c207410500040c400846e4001d854040307014001c00300c1e030102040300b6588081c4502 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 248893507 1250 248892257 248892277
    0x61409040209071b2916050d1808041d0606030f15041a0109092007030c06020c0109120804050a080f040e010b070c060206100b031803031302010e030f1c02010e03 71
    0x1005d403040c50410b0461440302481c5881d0001c058050034030700004050300200340d80032001d201c8041171070140110540d100003100d80c201e10044401694604080741c0b030b90f0150040c001802d110107082c103001119007100c240100b0019001c4c034a199500b04100c030710448044d192040c005615522468569154050380314400c446a11200607000c0000002d0f015280710360002cbc0f280707418441661010b030020010031110307103141001950340d01d4940c41d08603621030b48100c0091400703101040310801d0800541c0401d200503c01c1050b03400c0c20b01080010b540550b070803500242607030300c00782c0b0700d8001400700009005160390700f0687c03d04090f100c0e944203000c01402d8204101c012408503040c170900405c1d040050040440d400504081d081c0030004000804441c05029003103280040440d43c0070444460040701094a4401c2d02e03200c1c02e200b202800c2981030903400340d00041c002c04c443c1400d803070082880c03001030b00c403c4000c004915104a298000140c04000c200a55581c0d450042ca00c1c0c1c0c041c4010115961 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 248894757 1250 248893507 248893523
    0x40f080c030d06080c010c030c08130503030f0717030105130911120f12040608010608060102070906060f030b04020412060e0316080a080c090a12020a031e06061409040209071b 77
    0x1003020941880c00c0c1718107003140e041100042c4a0804290004c000210880e084441c0039601d900e804040002c0c900e460340120b030140700003d6580c040c0d100e00da014240c901c0c070404050300c41c3c41005d400d00312140800c3c09281c2c0c0c0840034809141c1c01402c15400240d616104d28901c1e90700d1014840004c02001c0701030001403460f0000e2002c901c4200c4140b150007080800c9486150a05040460042040c001402000140700e418004950268000c200400060a0422041c016a501e0f400001d00c0c2148070200c260100c1e00303111014600c0d1a00c0c1c001d4030b054901d05000381000741c08649500c800b030a101c0429103281c2c0130810400040d1103c2c21440c080c110300410845a94040c10140204614001801070648903000e0100400d9541c03880300290449081e1014250240c03468000071724104640d52004010a0f0b0743d40c007058103200c1c010b40203036015000303050400c902c550718201040c6041f2642655548044250002001407070840340942c1c00c540e0794035003c0841d110b41c1c00e0300640300410b00740a41c1c03042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 248896007 1250 248894757 248894759
    0x405130b090903180405090d08150303190e10120b04020c01060b03010312030b0307051002030d0c080709050d020901030209090304180b1f02151f17150708040f080c030d06 75
    0x55080710211244401c0e02c5c100b01c10700d8070150003520707071100f0034010080080700000326100a51140740c101c1c40040003020b07607a544084c0b241070411058180000300115114058034003440c0b408034110302986106403100e100c40b4600040c42002001e02508090f8007607802c3c4105140340000b449404007a080603c0815582e5041d0309090004000303480c81d0404250800c001e00700c00751404615002202c1d02a65044552442d502060781180a601304a542481c0703800c820a030041e80c005c0200340682c01d41e485500d600c40e112000c0c0201e81c0b410f040040c0d00301e10500010001410000c1c5081c0e440300407201900d007840d440b074440c2014011540c5c031040c81240c81d40000c444903d8842020000c24114840aa249012100b80a9203641040a060544611210000b0ba0140c2c1003a50b015610701e0381c281e81c8404a40350018042464105003103040b541c86030503d100c3c50117103ca0a0540031740c4441e00c5400c42e070340d00c540e203403080c0341c600050840340702400384010300b80c908c41000504024131035000085085 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 248897257 1250 248896007 248896027
    0x31b030c09091b0b0a0509210105010501080a06081b0a050a03111804031b0203030910080115030506030a1203151712031902090d0b0c04080c01080c0405130b090903 72
    0x450f0007424030001c0e600d03a0b20040019400420440324604d800e030500c2511480c1c0c0d8000500340c1034550300c800c10f030442d1040703210780850010b5010905075542602c03141801d0b11a04040003c90f905800f42510b03c1d845180d004003e205241c00704110745500900005511351660b0104840201e1a4005c40e010070720141c0554aa24210700080c006611188094405103002c1d02d0082240000c4407031008015011100d032000e64078240202d480c21039010f804c40702040c8460100504244092007100d17181c03050040360785901c91103802100c1c0203050003401040c2a01d20342d00c48503403250100701040e06242e601c11151400300da0001d0342034010503001240c9001c40e100000840e04240d04002c00c4509000d08008126110049012010720080039503070060321600b10001040700700144001c003402c103038295403c00c1094003402c00108141c81c1d211007900c91380741501d00190761009007903a0a480c221000d0000348914140748610b92b400024011010034a0080030021031301400080d02c2c0d0b045160000201b945d1a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 248898507 1250 248897257 248897273
    0x14041223030a080402040f061a0a030f090201021c020723101715030a0b0c0a1806080a020d1d0c0102070605030c0306040902122a030a0507031b030c0909 67
    0x60a1031080255180c0000181d006080c0d86008000a00c1141e075000078402da4015544048064003a01c81074140404180402c800a03411041c0c40d2000079082503c503e05c0c0d403c045c09088172043e410307002082c900044481400c1d600c2606c1d40e1010071481180d03400039020f054070351451040000c410320004200951001d2100b0489816050814400842181e805003045402c1507076009801070803900c12000ca440c006030030b1501142000c0d0249410000f8803e03219035082c02003681a01e1502c1c0c801400440403000310090803a4441c61000c12448030005080b5122500103103680021072a00017030020300d054803000581c84000b004071f5030381c2c0180900005940c041151802506080c20040d00b11720306103000040c0382c0700041641e4001c548464400045455030b501c40d0141070348003416038421200f04e140130a0b101104501200916120383c010126505010a59006098000c80500000707030448c2c494821069000c2c802050805182e2400000305810315801e0026140a41001ca8522070500300151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 248899757 1250 248898507 248898563
    0x70c2f0105030f0601080c0d09080306180c16030c060e1f020c190302030c060c18060a1d0a05030d02060405010506040e0304120305040b0309010c030c021c140412 71
    0x30500030100140014425490100c0b42c1c00b500900e890b04043d516100468143d001d02c1d04003e00c0107080040d9001004a40009144900d00585858004407007240f002d107107440c0290340400c0b42a504200000c008e1009055540c4460b00908200d50040c5081d903801c411582101e4142d05640c200403401c82c50800169545400142d48400c1075041220340b00c0b020351102e40e1704d0810a60014168580803c060080c415034490704881005e440c003924201c1c1e518a055403007000540343c0d55401800040480c5019001d99106820903582c2401202d10400142c01000c2d015400950060f43c80d0f40010340c1e55400c0150a000c00c45076405000e490806142650954401900b4607119900b0b00103540111580007043d10100ea240004c1098900c440742801e4a0900c502d4201c040140c0c4004100013035150150451407003c186a9007c110815811404a03100c0701960030880707420120803640d0340660b00c5410303003000b0010340c11174041c5059954010b4100d501c0342c0750800c4900c0102c00c1000003040341d60303248100d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 248901007 1250 248899757 248899759
    0xe0609031c05460b01020c1c17130f03030806010e040e030406030b0f120c010f0509030d0306080c0907090909050f0d0201150b03060a0e13020d030519090b04090203070c2f 75
    0x44002412640040e4031550b6201780240190b480e4105143d80c4041d28014085040d00074112190307089d200079004203142e101a00d500c0da400c441020028085c82c1c420454000c0b82d8065030b50900c180c076100011a03245002d4503e02d98055100c500d541c080b03100a0000b48001e20305074400095842c0c600741408500b42204003514442c000e41c0f03840d01008400820342d0340000c40d0904e42280084141d0600351036600070031202c0341e003600c2944580d01c2c50a41540c00801556041001c4500e00740d10b00b000c0100e1100111240400030b003860310100541c0080350440c0c004144103400f030b1038405181c030b802140703002082d1920100527911840c0503d01f4080c1100d600c00589200200a8a149418070100d103d030602441100041c0b4842000100d5080001c9014100164002c148020303600706420020604d80002d041d40321450b846070b25813440300f8001d41100040355120150382341007910b420800ca00940009100a05009000441d040020071808651240310f1114501c50071118007011280000e910200030300e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 248902257 1250 248901007 248901011
    0xa03060f0b0307050c07030f05100501080d0c110301090204020d05060f1e06091206040c0911090109030b270a15020304030c02120c060d0e0609031c0546 67
    0xe0214103401c0302207950002c020300b8030341c0da80c0d210814100d203003030041e174800b40c8113005a8001000300100411041030940082405201071f0741c03640c043c1c41d2a115048652404910181215400241003650700314074000c0c000d00004410040c0d40125050b070748400407801c181030340c400070040d692404085011b010b900544101403803211803c110f8004030a8101461711617400420301c16940da40d003c8400400e1a10002030b941c1d01d02b01490115088900c1e80106151542071540b5172015011143c00e46440880c140e44051311140345450b11103800700080c1c0010f00d40803d0108458058109042200c022102c100c01440580841d08183c282c0454620b1104445401002804017007a842a00c850350385030104c0700d4540d600e4050000750316108120002035004000416042400392079a8818014800c0b0032060741c9040d65030050540e1244214481c0e449000c25054440c12003500c2d030382c03115500c045115050702c80865906c0210b1091024006400b1001000e02c22001091317145042002001c900c950003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 248903507 1250 248902257 248902259
    0xc0f1412010e070e04020f040c05190f0f050c16060c060f06030b0c34020a0f0312051e0f071e0c05010e010c020402030a05010302011b120309030c02090c0a03060f 71
    0x210302d499542c50302c1482441410840400c056650b0407102c1c07000207030001c3c41027182d81800349000d0f0003600650600020515072100a02c002402000c070b00740713804200c0d514403000240345d01d230594041e04000c9124010b4840e07030801c1c0b80c0118603000c101000d441d41d5103541c115000d8a2400c1e4007074030001c44c40000c40c50f0500d14104001281c030b554554005040c80c1d0b042d912461690000e40d000442140303a500454803043c0f80410300c0740c1103050308039418000c0e42c811010546030a10148940c0f82840010302c031010840c01582564030070302c040e06110203034411920030084045419140c542100c9402030304140001608010001d200e901030310341e54105410740007084102d0300e8424001005206203418400101400e04081c0e200c3c0480e0300d4003d5000b40300710749031f04000e00410020042404128003007443e00d030241110803108880c184000e03510184a50148040080072000303041401021014020010101030059407010300c4a8841c4000c81c0102d5112021444014107803800c0340d0141070203c205c240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 248904757 1250 248903507 248903531
    0x3050c03060907140d031e03020309100501230d080a2a0507050f0102031b060106020c1801030201030b0f030a061a04020a12091e0305032d060108040c0f141201 70
    0x3094030580074007103d042da030200c5d06082c20345500001003000719901003200b41d126241901035001e1405140f40704120361864940c02d0646044400070b000b400d08a240880d4801d140e8181d10b501c0b13407201c401c09082000d81e240b0b10b6442030942c1e0403100e41400816441d082c0449080018080242101940070715160f0155031071301c40b00d484402c02d0041e00d0040c0e221500900c240d0b4020801c90303034000c4c403806007610395180c0c1200d090380713808003800390348014002c141503441c4500d842940c9501410426040200710703443e44d801500280008240580c02c0200010950f0b007554090003940b401c140141408035a0514101e0001030810034441d40c184034030700c14000320741043d80c030051609540f003c105c0c00241c10f414600b0400c0c13030600200b100300c803030f690412446410035600401460140080c0e024007500542201002640000541c8220000003510400694550310490106401c00c3c0036681011400780c60b00c1c8110407550141d0030800441c0302c00c40e110011340c140b04000184140e0074000030000391a08031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 248906007 1250 248904757 248904779
    0x30c14070308090708100204050a0e0606040902070c120f0201140313061d120d0c03050415020703410c0c0105070501020f1911070506160309090603050c03060907 71
    0x80c0001e010094003800091841108000c01e8015240c4101240c807074000502d8070001039070141c080c460080fa00e23001e0015211102e400078502038100200b690b420642090180c0009400810781590304441d18031000507882c42050390000c58501031001001c401005000140c5080c2c090004818401c8041040211b4144081311441b601c0d50311500c04558a4541001ca00c50710050703190000090188040350014080c9142c010b141c0d0940345802031000c905850380c00e0701100c0c0110741c050003a8100303441103a181d88140c3c0c01002e215109060250561049002030440c1781501c002507540701c0403448810081c02d84002d841410103080303075046480c214044a499440d030090a01c12070601c9800718140c0304202081d01034550514180120030b4441d000100c2c5040c030022550020004500408100440c2000115544081e10405022a460407212501018408800d26400d6080010b40000840e10880d20300075100118040c40083c0124030380c84c0d0405040400c0904207100b90341c41103208000e142c02e00303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 248907257 1250 248906007 248906017
    0x9270c110d0c0501060e0106050a080c0702030a1e0f050c010908030f0d0e100e0303010906061704030f030e0102040f030b070503040308011802040801050a15060201060302030309041a030609010b01030c14 89
    0x40d00d01001c2c1ca802519080b8094115500140030120703d0340d0001c07812950010140c0380c0d1065a80e12050140c48042e180681445041d8010750190004c0c0c084a01103903c10601c44c806010000303035818880f50075100c11941603c1d51508842541010880101560307104404602611080b0040d514080540d500401ca501c00c1d0f00c2c100004548801660075444824800c5803001e0320704203000c0c41210750f6240010b450342e0003405980541850200082400341c4510400b48242504243c48070f5103403201d45041c0d482da0540e030400810581c0310f40c071200b007034003080c0042c200510700e02c0c001f82c51245c250300d0690f4032404010130503c1000340900030040482da220b4141c60440303002c50700014042c1e00d182d0520000e44110303000200c01d0360038031701840540c01c00d6074803854980010014030b02240d0f03202c000490070384107540720180d03041d8400d100404c41032426610041442402c60170581c03d0329644400300b810312800303c8509041e130b503503a1842e60319560103020307094644c44c842c90001880e2200c6000c0100ba40a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 248908507 1250 248907257 248907283
    0x6051005011709030415020601050103150b0d050606041805010819020604060305060303070c03120e031b120f010504050d080f01050901060f0c0b0c040f15081609270c11 74
    0x211a0114096140030300c01c80740030f8070890142d03140c55001241b01960f00c4200f80700c0ca03400a881c0c4809444900210a40103064030440100b283c5011200b980b42e50241c0301c00b030b200d507502c03200030040012039096005641002414030480845d0961407d02d58504140076103444403114400c1160311f00044e601c503000c075400c1c1c0e010b60800244c25220381020130301c0c50007184070090845aa40c0e00103c1408030704c1c0600c5031041d1040d0340304004040c0602c1410303180c0503c0c194440111005a24a0074145440c00101000c14460001c07034040c880d03901541400d69900f9030381911540c000800302c01c10554051489644a1306200724054194548004110405014400c003403c02425100030b078038062041e1002850f0640042c1c040c1003c0c240413441519a600922840b410900103030030005c0c09604450b42d18001ca00b00f9110b0f03442507a160003a601e440c00d4441050820088030aa004c40c8010000c1c0010707110000340c68481a9940c600c407804030842d044284100c1c14040180a40c4c0903244000441c0034401e14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 248909757 1250 248908507 248908547
    0xa0905160f03110316171f061811040603090f080a05270a06050708090a0626040c05090414031614060411060d1104080303070801051c17190306030605100501 69
    0x18190742d820400302c41c0000130505021f81c145010116250080400d840f1141000586c210000c0010001c881c01410704003051003080c40308111543c000d51000c0d88050043c426580600b103550741e952281d5008100c0c810104902107402258500c00c0c80101c111070904080402c0014517040000d4000851707803091104010340041e4417410030070300106840031a1809801501c0e000d0703c503100501518422549211200600c41d07480c00c1465030b0b04030103070185402103111940d0030f05000520080c000c00800a40b500c6410400516525408100402d00c0002d01200103030818040c1c81c1602070308280061031416940540180408226002550007a16900f00c0346a0b41e04ca600c5030b03641002d4403a40582d0341c14080c010500050055000c80214403c54099480d44d01c941e07241d06c204908e0181c04c1c1c03920183c009008980301c0c0000c00042400c1030301810b10501500f4010002c1e10701e4012084800d02c0d00001c0d803030b2641001000701c40c3c052160805498580402014140000201284003213a09006001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 248911007 1250 248909757 248909789
    0xd14010f030b240d0b010e152d0d120e012d11070b07020a0b0a0f030504060207060504110102010501090c0f1809290103050c030a0905160f03110316 65
    0x740c208040c8080b1290b01a09130b44c01082c45041144510f1800d1052255030100d02000070305040c98414105040301c0300800900c40440140b0354440c03001500522070300c0207080b0198070708061b0b891103088401d4a205480c0201502c0384860020507580070001000d0607c00b10510541c1c501c00381517100b60240059400802c01054582e07030850301c0c0400c00404108600070307104042202c400e600c000745a258001d43e81183d20381d6444c21a11424403c066041c000149407003030301d41045109030003440c2c02034018040541001110340ba0f0030700f152400e40d0210f8102d4403648080040f0350f0207015490061085400400108010200141c020b00001200310104541c08140e41c0b482c5219005903400340012142c00c0001c03065a545071540c49103022030f8161b03100c0403c0e110101075071184c0599803080f030030080c0d400d080d6100d80f80d808001e0320700d40c60100e400b4010320449152002608104500620902c46001e000500d507051080c0d001c261107203201d01030341155520020441d0484c1d03488045501c00c0c02c200c0645 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 248912257 1250 248911007 248911051
    0x304210c02100201140108030702090402010507031116061116060e0a08010e03040305100204030f0f0602120408031006020c090402060a02030f0a020c0a0e06090105041509020d14010f030b 82
    0xc0c40800400079401030109038007181556056000c140071003145420b5400690700c80f8026652070141100086d032044030440010300551145018010a40c031a0030225002840c054402e0b003014000321055a007600380c1c0ca000c0181d6035001518030501d1240c80041c16040740014892016400d19010761400c0c080d0f01c01400c1e415441c2d21394200d0050030707004001c0002e01c404419882c0c41c3c2c1d000344015a601e01c5000c51400f440724083c8219011254800319164880409641c0c40d980000410700503100250b0a1004c1222240c0c100036042c4914420803501d682ca143c800032406c0081c40b00e0b08001d0440d48001602409604c1d00034140b034210760100c44d1141c5500c00107008a1443c031601c1a11200302c1c401265900d50540c0000709900240c0044421a81c0072703850300403160002c801111082e5110149100421090819500c045004881240503100c05629001040c090368000400842d07080d030786a03019911110301c1803a541c05858021030000c03009203940c55642c90010044c04032540030300107103505110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 248913507 1250 248912257 248912267
    0x10512070f050d06080715020d02071203030216050106030c1a09060d090c060908011d030d09110d0f020306070212030f060a0e0103030309051203010803040b030907050a12030e06030421 81
    0xa2000c404400c1c00b21540345c0c10019181c40c100e200300e0390b01840c40c41804024500105510560b05829030043c1901460005280a4081e01030b60940a2681c02c20088045000c034518800045026000100b0f83d6071840c503040140c01d08650200920000ca40d030724509004c10707002120391412044902300e4650b424411500000e1460440c01090b985041800180f80f6400c10310713520807204004000c001e40310ba120900f0301912241025800780750001c00c9080120701c03441c3d002c01c00f007a00480141da035000328540402d0320f0301c4041c401520313402400002d900c01c620f0f08100a5501411034806012032410f00c414440b00d602000d0700d030510f1420306078000b4a064880300302c400f00416100c0b402c01e140d540d44e4100034006048034202a0f61038080c800e00135a6607549803041b681254280001036182515207601041c07150400b40a05005d4081d403c00011035035500e14654001e0100d010840c01c9100035440e01902030008494034038002c08050003080045920b68208065581440080400e00700c004401226 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 248914757 1250 248913507 248913517
    0xf25031e020307020a060f02070309180615050904150b031801110d020309010b040b01080a021c09061506020706050f0c0c03060907080d0207030b040321020c0a02010806010512070f05 80
    0x103030984007008008540e50300203112119140a020100071b4100e00350f80030030592058a8020b0041414044101300c1d09004000c0c000146110702d200042c6140c4a40110b848007a4200c1203000045003c17a82c2085450175208044447c02000a140c00c854030305000c00c1d0150200410941e480304e00e041001800342d4082d0072180c0511100090a81d07500d125a4124000b034106903800d2006600e07182c84402c95041a11419041c0e460507124025203030344031902c0d40065444100410f2015135a03140e01b1410350350500505d001070b071240c00d010458890300c0341414104040340c1d0000301190300210042040c41d82082c2241c0c3c0305c02d515500599542e040354081c5140c5902102000e0f018402c4108200703090001142c10026101d041d0103131140507200c0c21040f41d440b045070102501c060784610200d00041e001d00320650000c0810510a00c3d119803600c41481240c020702d0000996400410980045681c000d81541e4042c2d000d091407424082402e142090740312006100d0820320402d11203201d811801003007074078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 248916007 1250 248914757 248914811
    0x31101020d050414031e090111060405070303022e0c03020f071a060a060e1e1002010614010503070e0103051902130302090109022814030106080f2503 66
    0x140d65801800c510304000c1c00200e8090f540c02600c100681c4c0b40c04d101204440c80e066414400146622013034212115680c0030206036814400205902c41c880e880c10311140313200310701030005041c02a2450031302a040c1000d15440780500d0840c02c903816400e248000603255005414a03000460440b000c1d4160002c0c8504480c10000003008109401003001c0388088114a8883c4601c0ca41107445120901c010b8413810302421002c07941101047c95141441070701c0c641d2403074000c0c40711400703a8103000101c3c20b0003110301c4210300140d44a4400380030350400080c01000d80700080c6082ca10350720304484002d25200c4842182070416881c0e00c041a4102010301c140c500d40e00481d4004c655881001400c0c003400c0d016480100d0040d4030743c00000514040320302c25901002180d003401ca510105640480d10200000c4180c0c40609c0f4a044d0865954040000550b01a020640b00c2620604215442036000c0b00020410000c2801040700c40d21164860600c0c00682c040340e050119041001040800100c21440242 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 248917257 1250 248916007 248916011
    0x1020d0c03200606040c03020306062b020408060a0e0a0b0402130f021b010b04020708030105100504180b03011a030d0302160f121202030928021f0e0a21031101 70
    0x84081010040f800c1401400c0841d13040185105441c0c0c2034090380000c8602c2035000e9010b010400003440103081c491108124281101610500501c03100d040741c1050b0040c1c50107038400c508000e21062203206440d041400c0c60700502412217160798121120341e0050000f0302410f17071240c03000385c0168140c000c0081c0f02a0104295101c0a11000613124100b00981d4a19158240401100d075410140f00319094941c0185d011886c5a00b80070a01003105000c0c092a07080100410001400640580c401c0300e61103100100030400b006442d04240c2500c6241c1c01c01c0c030900c0000e2600310f581d41d600013040055840035007009a140c1d10b03014030703002050603400c901500078018444203000304081564000c1109003151100401d21ba01d19032158104d010454104c500c3c1e034800c2c4a807010084040025030b0002c0040c2e00b044005c0f5a03654080740c2c2c42c1007042e140d2111040c112000c000000d400120b4411001c0080d1180741001d450300c074881c83c011102c00a082c82141402c040704091510540301300109211500003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 248918507 1250 248917257 248917307
    0xb06070b0c0a0914060a030e160906050a091a040c0c0510020307110d17060a05040f0e12070305030109110405090411030c150306011d0414041a010501020d0c03 70
    0x7a1000c55001069040c00911001404030b94410b00c10180410f9402c041e003001d0400e084240b09034024060701820484600c644000d034907001810b01c80f1240604426080416180d2500050040b1507a880d000141900d080c0b950188403031000e03290708100c092044030040b450014514058a01040e21000945180070f144010341c2d8070019078000f140540b1301c139910a40250400c80d00261104420340c00701c0000740707050150319001601c1003078494002100074040445a80d960000508440203581c0780020547c60300c2100180680601014100601c8159180c2c0303410300b981d5004001e403005004070990241d03601c49a8210520103c180d40240070050a01030480c241070800300c410400175504076100740716000c80348103c4d0810300070980401d082030882c07034156183d810043d01c021160700406110510802842c1c28641d489000d0342c50b260b11200030710802414903050031200960302500120180c178800004011a1341c0c0000e05001e00d090398030305403824051601d0111340f240d1031048510b141d0420300a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 248919757 1250 248918507 248918521
    0xc02030306044709011a0a050d0203040f020102070e060f040e0f01110d05010b070f030305090f030f090315010b0f0a0c0b16111c120f0f09020a1a0a030b06070b 70
    0x42405010390405080300080d0385043c20004a8035090107156256100c00305104442034100700a0711600403281041410400044902d608030b8008441c15910140900c0742c000c15541c06000000c040c0022049140781440d00307002044ca1420703440005805a6943c1c450388441c9402401601c1112072903500074898002c1c1910300c49002d400c14080146164640030000a00420f80c10841310400c0e0720541d413440075115514140d00500d00244859060b025105600b041d080c42800145010043e5a05c002d84492001051503c0c10070341500740010744c507010b00140041615401030f00e07040a4001d4506aa0b02d007001c00c1140c898000303010040c0fa1090101c144104d6000d00414064817004542e20030a409845180302503480c0b01040c040d401287e0754440030f0104501c83c00c0060303091805a0804250709140b044500219145001c98000301d070f9442c8610b90031460000c6024009018400c0880e101640024101b102c40c4101d03000034050554420480e103490710ba0b0000e554109401c5000480130380380c140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 248920863 1106 248919757 248919851
    0xb130e0a142412160801061202190e010e0f06040207121404050619020c0d05100507030603020301020c0708010e030408120d15060309030e040c0203030604 68
    0xa400c1c501074807000982c820190f40c02004143d000c18103241031100025581200030140d040502c03c01006490f0100e04910940464a80c40c4050b080b04020f00b4010095000300c94402d50040001201d11114444600c1060314010311260b940d504c0041104074800d10314014440140344011500140c0704205150840000c00000c0345482d4417440003a0203908a106003009021040001c0401c0903814130074030305c0c0c0341c1042c1c9510340070b285a56a043e480340300043c009140d5680d07400000303030810b00c42d8001c400115000b0380211f560741c00d035444079500d4a145c1c0c01141103030f6083c0300700169542000400c0324100c40019000d40200161581c1c0c89070030b94005000d00b0410340d01c550861401c85084407280d03009000c00d8800080f00c031000d2030b0282403124101040d43c4128030f050340e8800e2094010003241d900030360481d4001212007120f202c401546529400d030003407080760806140d290041217 = true := by decide +kernel

theorem cover : BRFrame.Cov 248741007 248920863 := by
  have h0 := BRFrame.cov_init 248741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 248741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 248741007 ≤ n) (h2 : n < 248920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
