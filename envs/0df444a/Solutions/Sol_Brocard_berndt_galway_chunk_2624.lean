-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2624
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:15:44.969211+00:00
-- url     : https://prove2.me/submissions/26d93ffd-8d72-47e9-8b4f-36ea9a613839

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 471762589 ≤ n < 471942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 471763839 1250 471762589 471762607
    0x16081f060e123009180a0605030703080301180f0e0f010506010e0d0f0807120e100504140f040e010603050106031103010b010f030c020a120e0901080105090d181d04051917 75
    0x204503105130800a000403035505021030780c451070340001e48540610900d024030004a509001c0303404030449410200d528150703840c140e03941c132580e603d495034071400c0c95a0b0018150105d40502c036540c40881e142c1c0040000d00c0c0060309160031110082c00e218180007901d640c2500c1c6a8808508650942c0c0c8400c9100003a4140e14002e6514015070000610300382d8900c2d01c0d000000d82c42601c6040c00d9400312105450b920000e5801d44140c816070040d004a00c50315550025642404018407a003400302500c0001c0140d0302c1d0310200d0031520a5003048030f03165101c3c00c041042c006c1c844448c0540c400701310000c001200f031800028050058081d0f00c81c041c943c1307400300b00702028020b00c8851642d03034100c8031040c1c15100401000b440001044c03940c0b8410380c1c0c2c4200100e09280144602486006808004c120b440c01e03000d4180d9050304015000c070803001c1c8012001c03414071f0702821100c01110150396882a1410a407420303030700b8003002102c6071410f0680d01422201040e00d0b070540b0b51b40f09a88080d0565039040030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 471765089 1250 471763839 471763933
    0x703110c0703320d080a09030503041b09060b1c06140d030302040f03030908060906060307061803061406010207090b090a02071e0308160816081f060e12 67
    0x1101600940d00f0b0740d1981034100c5440800c040007a102241e642580903030302e00154000719103c400014002440900002d400205600160060481c043d80480c1000d69551030391020b40308240c11a0561440c0460200d00a0045811000f1756005821042c01000e01344414841c2c403008414080c2e2003902c04182801c14503019504a4025110180c1d5102e030158503414040d28103445445103905e44d2062400180704506c0124a1078000d810040c00f03021101d280607030454450841d0005450300b26821440000028068443c100000c121151546910303e0640000b900302800c03a84000c0420303060880c0016582e4500103160342c0907100820050b01c425403410800b903460032041e50f6021180c10460302505140e0000c100a10690705050440c01c0029808000c0307620810517a110075001d41480000e4a0050041c13020903804003501c441d90144540e2031040040501c2c4d40d9001d40041450868058101d0510242420028901174014000c484001c2c1c0d81c0c003804001c50b00d05510321340b0381c1c0070b080c83c0380058 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 471766339 1250 471765089 471765143
    0x60e03060f100906030b010f0902031605090612010e010510093501020309060109110f0d0f090515040b010608070c12050d06030b18070812030405070e040b0703110c0703 74
    0x100f200d00708107043c2c580c0390401d00c80364280500a103c9008080015100b0111b000300d0f449466002c180301e959521105d004d0320030341c10a040280e030010f400d109126072a034070000414000c14040d0640c0885500d00320a012170300d40900c4100701080115501802088040b0b403c280100d00f04000b020300d00c1d0f01c0d41c00e884581881c2c03509542d4143d40000103209640f0300020318903044e80c1c9a204100030740c1c844201d003c4100c0c450310541006244080c00031078030340d000720b0344064000c01d02e168003c070f01100950748240c24103080e030181c02c000704160001d00007401440c4401d540507195a080c94070050604e124054400010303160010a06821608003100d054441c0066030030305250118240095922458050442441102c1030985e42a0009a401c04804005a040101d40c9030001903e0803014000b401c0c800c6510061080c0c43c180b058504c009800c132060300605225500a0002c8406070620782001400d0350045020107070407810a02040800200c04103031101281d174001400c14980d502456400c0c0c003141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 471767589 1250 471766339 471766349
    0x1060c082a010510050d06020702040e03030c04031101020d0912060617030a021005010b09090901020c030d0f0b03060402060405040e010b0604080106030b0906190209040902030f010b0a060e03060f10 87
    0x8000d415035071545451241500001c0300c00c020303c2640c0c0c41c0b01120201d0000c07440760350b41c0050300e0220000407601c294000c08215002500101d59445100344041c07a550083e20110182c401c0010100280f04d6844190709480209101910a0241402009000100c50701030540d459281980e110104090b59100d85e004ac05130b04045030790340c0a540c00d15a01e03a0014081c0320054002d034465502401030300d1003a40d043e507a0020700307039003041f08040030701444200081c50403145641c2002191300f10303503040000d000540035a60012428940320024070080e500c0f2400a20300179401101800016a03441042d1003d540c1c2c00d480003c2c1108140a591f400b4154a90049820040004011440803010340040c410349001c3c450f0b503c443e4940814403944d4070030450340752001d60540c89075035151010765001010300702c80007000400c020245030006806c10071660b210941c1e40e035480700150494189109003d00401041c02c0c00c2801d200208003103910b90310000e2418003d0020480040d0100a1406001010300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 471768839 1250 471767589 471767617
    0xf071b06052e1806030c060813050304030b0601090e161d1509150310060f0302090301021b011802060f07061b0309031b03300e061510050301060c08 65
    0x444030000030040d0030060181c110b11407011000541801d001d4044d44003200e500c001c5441c25a07141280407507400764041d2400744200094030050012440c1000038201542c0280d0076254607081280000d4420720300c550240e0751031541e40080000c42c00815659104904040c108011240350114900290322040400d581e0310040c1c3d2080e1030b0401e501e041c00390480c1601600c1d5454840c80d640303440e05242c04102d07205460b0399015081031207038038454a006066400c990402604107403071038000030b007680c00241600c00e0300c0541ca0309010909000740500b90700b190403801d404001e449241c0110b0000d2007049884000d0010002d0460100441356002800006041102c180c80d030000c004014040c08403102c00340d00260046ea29420107210249490f403400e580f648a407507884810517040303241c84000403003100c1e10840d61400e664001c0514000e8031100594600a03040030b00d13001d07030a200140c0c683c001c500c1c0241042c81c1c207082a83e422208590540b00c1a0401400040a503c0d204e042031050392003030f070805 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 471770089 1250 471768839 471768901
    0xc140a03020f0609010923010f050a0e0c01091203050708120103030c03080105012d022a031213181113030201080f0403090b1b01140f071b0605 63
    0x10560114560040141142c02e480340d030380760038159034241ca6941101606a4841c50103c1a1031003020107402000d224007400462902c1c0030410100881e01c040703451048103a290391807542c4124052010090318030003400c0904125003400e843c2041d50202450060a020340040e4042c10b0240c200241c8031108010903d01d0078560316841e008107011070841084011036407113400450150f021b61100c40d003001240e10034401410690142191883e003a403c0360055000c0c0140e0030307109000c01410309403030411020544804144034800c0c5031420344464103902c500c4e40c041c40350b442e0f8200650904022034502d500105c00b1581c0c145009401000115207400b142200060181e45491910898100b204e000f6212a8129966107a140044c07100495005000958000c03003486100a07801c05802e100d01c1802d03ca101c402071110000c0d0031900d0b039a44540e00c1600070f10400100f407070700c00705c403e511500c28a08050041c0e41c003003640803407050151009000756151000a0030041100008000c0010081121408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 471771339 1250 471770089 471770093
    0x10c03050627151903240b0f010c060f051005010f03050c09120f160e0106020a0506060423270a20010302220906090b130506031903030209090709150c140a 68
    0x6034011840d000c9011a140d04040150000305115080c0303001e1024068035818008c0800440c2c00c13a4103284210350782c681c1c40700f42e080c1802b00780c8034a906c15040c2c2c64094803081d0030f04002410312440002c0d60f01c205414141005599001d50003130302d031948400d940900c100604c140d01103003050030070b0003015a544140005085000300c4140e640044400c42c16503800140d80380c2c1c038200e807a503212540c0504550b10000c081061820f20390311841c007074500400c5007038860b071100440c3e14031808140d1385000e41006030f56201d60241040c05558005030310140c0205410801680c1e610409000320029158550034251068442c5c1d010741c0444201d0311001038a041c0041010001c8210420240200c0320950301d020400702d10074466100d02c10700d445008003003901d05c072600160800505001081103030140600800b202800c0585c13a04002d419120b0380700580c4640d50030082c42000c4900070a03180412803a00e008000c2201c5110f01528840701e10328040d00d80c0c80e030505021100341c0c090074410321a84114034607001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 471772589 1250 471771339 471771353
    0x7050613030e04020901051608040f0e0411040e0d030e1e01020c0601060e010905130605120601081203100e0a0902060f0409050a060e0621010c03050627151903 70
    0x85040c8a0b0712090803081401e02400124090040d001c6c1c0071440c10082c5420a001d400048050584900d01403447c05460384526904103d455000c412003c1c1407200b44820404007248400200750140c1701006060350006005aa5142400c00007080c103075070f400300400c0c000c1d06000c070a030803400340524514005140406103000794491500c4058601a40c000410464407904c00510035281c16552161001d080c20300b0007569460003100f88540032b5490100040035125582044110020500a4051076241c503504c14107041c002200e5068800c0c040040100c4407186210b22029180043c140342c18079034801191100411141c1c81c060350000c80805d04d10392a4041900510036648000301c1400740d42ca41c0000e40e41900c02d2070142c058007601c0307407000691a052840d10007003170b0406204940300244c440386c41242140d07100300d00b800020761207008015160802503007013480014800345100110600c44162440c500e4003030450400501c1d00c103240b00c0f0540c0c440c000403100b000c0000210035016940c1ca0440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 471773839 1250 471772589 471772621
    0x7031d0910030b090d05030c0f041d0405070b0a080c0304020301090b0109020a0908070503100c0912050c04140402031e0f030c070602070515030c070309080f06150a08070b0f070506 79
    0x25200320740200010240e00000c03517a045440c0560f202e090440c0c039a40010000d5801c031901c0c00300b0b0f001c401d003c002410106205001210160000c041071113003000c0c2400c40c10484c05030841645244100200040240e2110b00707203034001030246d40192261110703c0003d0142004e80300250180c80c0d4000041745c1c1100f9507004041c000e0941d141c0504c89a82c0b40714581e100c0c411480b51702d5240e001241c0c80d0601e08001d4010045403005450052215500c3c0d026806070071812584c2920554060307440503109051501c00d50119692650070502249403540c0042c1da1503201c081990b0f12150000c8461103154030810410380c0c11410241501c0c1c40b4040c92040c151340c0c0348130f441000c0051280c1100050f0a041c02004030103039070305100c030721451541c884c000540203612a4108030200314800900007601d1009200b01920340c8608000b412042c10310501035035500d150003922034890603000310104100b00780010400d085490800d0391030749075a000c43c040b4985024003000075040e0f0051901304801e0301d4040e0304007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 471775089 1250 471773839 471773843
    0x3050d030b010f020c0d0b1503030c0109060c0302040e0a27050a230604120903080f120a0b103510060203030c09190812090a050d020607031d091003 65
    0x20107442c4000c11041740d03145900d0444581154040482c040484d0001440692040700385009502000955020a15507030001e040d03c1c40995455082608015180c0602d05100c8000d03c1d0a505043c20545040d1400760080d00c003142055844480e641c4404202c54003c00801c03000b00000204003039424469280c501e4094210790030b102298415940380b001d542504801d9803480010b000c01e948682e184001e00491285070028403544d020b0020000380075000a007070b06445c09405940303998011480d000310240103000810018241804400729845060202d0b01e10070076450055044d007803009810504c0300b160342c0700c04100c0c43d20300c400003029083c0f0740c800c038041d0000a030107100c01940c03058100d0b140e000958034108140400c1080807682d240c420b0b510000c07161420000c1c28003903070701c0076050319065541034640040a00494a44c1681c075000340e8a00081500340c41c111302112072a4001411407282c40c0005081c80103c00081d0766000350b00003c11106040a400342205041507408400592410322003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 471776339 1250 471775089 471775097
    0xc0506220b03091c093b1b0d0f050a0902120309030a060c020f06090d090801090b0f07090f080102030a0c050702010827010203010b0405011b0f0b040c03050d030b01 72
    0x40000c0101050702103902c18201071025103800f6204455901c04c00140e0181c4100304a51102c0201e43d40c2124017818055942e00c0040d08101c06003000f400c1340c200e80c851810710f0980444000c0148190b42c100500382220481e84640d552030380302088001c003d141800140644a00c2c104c100070703440200d1f074003808a5500803074683c1c1d440d00c8040f85c01c5541788141c003041c0da0160010000a40094415000444009200c0c010b907044081c910102919161084401c000c055100c01030038400e480c2c000c12420f024080400091000d0001d5843d0000c0c4440040c014020111602c0700081c0c143d80303c3c0c140c5101a0a1001010003050b654058641c080c0d0400d5401800381450324004843c1117014400311001070f0303810b0b1201c1043c2e540340d4441121045110031361007440103418016401c9000f0a00c004c6018000002d0f441e51120b003840001403c4442c500c040b156003403d982000008500b102c000e62146641c000042c500580c1c40349400900320000c3c1d0b00c01845442850f6034a0013454164000c0d1941003800c0c5d907 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 471777589 1250 471776339 471776407
    0xa020a080c03040807080a09030f060917090d0b060d050d020d08061e040b01030f060f1703040810021c0204031208060a1508090a1b03060f06050603010902070c0506 72
    0x41c000450b0711003954000c102c90301c1085100001035200c8090103504800c0e00388014503694980301c10780703060780300b02003103540541e241e10703070b80c01c10200c1142d4032250350440c207145040c4412500824401c50305000b001d0160a148070001c0c00595401c040c138800664044151a90002c01c1180039503100164007101011506280001e0450b08180c40b0180c41c0c4401080c0c2030100c50a04002c1c400101181203801d41050340f980346810499019008420007060641c5c3c204094518240030a25943e808001000c80c82e0000c20040000c20000519611204104130b00141e5907483c043c030b40f41c20400410101050940042800810f1028120b880500d407101ea48805420b9600d1508100140006021320300d580800c41104040082c4124907456011911404441500f4082c0c0c40c1c145001566580c2d0740400e1602c02c10078000c02c48240544010308081603c14044541404002000342c001406078410f515400304400d0b080c0945550a80300405001c2d26040d583c91a60640f1402e0034813603075101085c805101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 471778839 1250 471777589 471777601
    0x3031205010b0f07020d050a080408030d050a02070809100e1302032202011b0f1406270a02060a02100515191211030f010e0d030b0904020d02190e0a020a08 68
    0x404552416102d54100da1030304c4429802c10070b0181208406031864418084a080012060f9001b4409084031200440e103407056030041c8400d41b1401403001c02441e0050044e5400603c0360400e507032606508540b00d513084481d1100072540c1c0d000a11010742e201410003480d50030350010364002c600400d02ea02c985c02019640a024021129214000034009030300321107156402c489003204103480358425a011546071200340c680002c0003150342c50a0074681c00c4907041c041c01c10040112500e40c403128002c040c0b24a50608465515011070320300181c09001e000401030140f61080c8204c1e030001e10000d6040220b0f0401849a4840321034618160b40180194202880d00311001c1d11079904803100c5945400084001c1d64404140c00003100100307405105076484000c1000c070130301501e000341520900510030903081110050a4070005001c00d03024415030000e01000da29089101241c1d0394058500b00074255402811107038404d0b00740d2081d424200f5010520111104d540c000700103000d07444d03449650644410b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 471780089 1250 471778839 471778859
    0x70807080114090121050a050609012906030402010509042c010e060a09020d0c030803040303150b0702041d010c02060414010e100f0b0d1103150105010e0405040203010b03070303120501 81
    0x10200c4030343c00840720b0010046003004a492002013500300c901c0802e060304a40e26207182c40c0c890042100c05411481c1044a200024455000d0303889050400c07007244c040e40d800d081c50f0407520030082401200000000713170a59000d10215003004c5006001004005032041c000d000091b100d40d110940c1c049086d41c5c18a0800050090b80c031b0600d0200060181d6485a070f90810051078819001c981005000f0707032610201d040d4500c43c00045004081081d41c82c07038540340080460340340b00766103800101480c00c01d216180408090f2000c181c1d040d03c002a441f43d116800700304d1080e150300342c2a100c1d800c14441c814120343c0466a00c2c0a01e1140c00980c02071a12105100d09880801b030501d40c60390320401d840c445503891500001c00c000b03090f6100140301c80c003401c0030414811a80100b030340c12241601940c1c460707050400040081110300c401d04032480d4181000202807a421810544c0305035242c0d000b080030355500f0b41c440749403a10010100c1e481c0581c0c3e407402501e54844021903261551030700c0c00014070707201c80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 471781339 1250 471780089 471780119
    0x7150e1015060806180426070b011509090203070e1207242c010e0102060424140411010206090f0a0807111207050411070b0103060914060708070801 65
    0x204850701440c5081410407184581c0042c802070340711824001c80c0d11a011017604143c003a501401c0d040004900807024400e003103464042e11090072004001e1075000c42d400301c14050550300083d86140d0000050102100c66100303540005102510010510510a42040705120140703c1034035060301017034ac1606c1198035a22548990308047c1001c11640c2a00004140d40c00030122050400d00d2450001000100d0b944034a070001040034466080402e0596070864000100d00d81300344014800351070310340c0e0b40b034054030b5040321206905003650140c1340d070f004201c0e049002801910003802c003491405050544400c8003084490b8050b00401c0045046080040b640c0703242158010300030800c02407903075a0704803150300c21071054804c0211091300140e15030b914180380305a400c98400508565081804210844444241c040008141082a040007070403020550341101e404c01d800240542c01c0e0b042c018590070020500181c40e000341b1003040303200c50b00151340e41e0041c2066a1a0b400fa0382e03c0321206064004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 471782589 1250 471781339 471781361
    0xb09010b0a0b04091d3003072607020c10031e0221010803031b070210020f010e030430050316050c090f0402120c0d05010614010905060f07020607150e10 67
    0x2215038000c04603401080d40c0d031a40d00201005000d55603801b010380d88581c0055400380001044111541012022604d6400c00d2000c90700d0304555030304020201968504086120f940114040414a01464041ea111f803182d6520201010350000d11160050025444150b4003154103c10002c101028690b004026040c0e0350384800451864035011041d070301d401c0201190646d56401088103400581724010302281d940050307002000220300c0501c91a0079580c0e500400441d6a00c240001c01000104080d0b29801c502a0342c43c3c181e4421140c6000d00e0f52a140d0180a8018800010b031032601c001ca461220520074000c406035000d580002e001c00c03c0349030041d5404414031800c8404100980b07000e8120710400b41e040d500700c800f0307030780904003280140c95a2031040e1583d0350b4401d0200003100080540703c45101c003d1038940038032404c000000380c10b40500d05c8030004448021850b00115120030f0704480c002a0000900350418841c2152500980042101c0002c240105060751800f181c0500485070052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 471783839 1250 471782589 471782593
    0x14010c0c0201090b0f1c0b09090334050f0a11010201140114030705040501091a0306041e05010f05010909030f3219030204170c010207030b09010b0a0b04091d 69
    0x180c94079134040c820b5040521590602c0104222041400300c800c440d0b500d0007285001c004c26000110760800899850050032602690820007400391401000312111001012100002250400001d44d0303490ba041c00c070794000c1c4944030b00615062040400540d20030180d201d0306a4640741d00003100128241d44440d1400d040c880048001400040542d00311020608005003c0355040c60ba1200010251182039011500e0789649507403034600309049282c003510b001001e4004141303504003507640340006003000e4584204403c000c003290013041001e4101002d071000b00d5105000550312101604003c003284103040340440e012041c480c82040c0650388240004c02540203e03040c41020069450443e20304811030903d81c00d0400c41d030600f03d40401c5050801d0002a41d00580341c6040100e48000035140c0402e801081d40300300b40c0303120580c4e8000b4a940580350301c400000c19075240c1701d4105003d0841041d41340c2e400b240708540414121440c4014004446404005001640542d41c0140000300c40d504000165 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 471785089 1250 471783839 471783857
    0x91e0a050610050a150815040e0706051c020708040e10080f0c1002060907090e0109060213050909060f04030f140d092a0909020a0b070b01090606030209010c0201080c130314010c0c0201 81
    0x1f0b9025583c8810350540040d1020906880c2d2218140c01c2100981240000c60400300d40032108030390070344144c1c0080e55204e00445c0303170648944419009006074410407010b0182000012240031003201003400a000b07210032290024003006040c1d4031030350a0003116004103140040e5000c7d043c400501a070140c040e08028200050500c401d0380098000e18140300e00c1c0390740710101b03100000e0440c030060050559000d00044035604010400086070800b500c2d80c11143d00c54018451120894030225422943c1b40c00c20500c01c403400c0c0c2040e0343e202429907000c5450440030440e0641e01426810820300540300c1c50320b08e0000300000b8004a031482040d40843c040c040c00344018000d5803219840100103a000604007201603948541e400100d40c004030741160042801e0300108044860360103170b100a4512410194140544200000c214113010300c0041d041040120208415010301400c4400142c03500b10040c2046440b410f007045c0d400109400f6a45940ca40b0b5404da400342e10400499540682c141e55040e06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 471786339 1250 471785089 471785101
    0xf0919061d0f152215080a12030c050f0304020301180b1e0709052701170111090f100c17040314160608070909061517091e0a050610050a1508 62
    0x250025104c1303000b50a58a030261001c40740708004520007401c0d44401442440f4944c500060030000240c440030505007030440412301c280d0000d040e152015918095035440350313607600000f800f5007070410030000c14001c0040e2907410311030701080503442205a40c040f014031114402d98000c001004a03111000500002014021868071004c990036030f50382c001110b01d120308000402d9803403401c02e07842a2508903d180110208500030702403000f1303030a4420355050a0440000100f070104405400c7c2c036109084c03000c107000c201401114500b841c80d030010050419070940e042c7e0400b090740b0602003074a40144000c858260045d00107104c5d50b400400700d0305403001a24205003a144120041e2180040c0407a800d400314000c0050320401000781204018291500750440e8060582070014003a1100c2502c90002c202c880240042c040c4c2c009000b2a41c6138a01c9500c4007102030070242e420703000030702a0098000380600b050b0038403101c13010380d04120b9245181300d0382c402240b49005c08041107071003c20342500014103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 471787589 1250 471786339 471786379
    0x15030706050901050405120303060916080a090303090609060209030c041e020c070b0703050a0908030a02150910150302180702070320060c16050f0919061d0f15 70
    0x1a0880107050035801c5c40d40302e02c0003580b01c52100ba5501500ea1012080041a160114a0a40110344000e01c1b2034030450441c00208000401400460700c6520303003008000305031296205e108030540010080050351540c1c03401e040654010645588640300340801076080340380c144110780584070780380340d400d2202505c0000d0b01d020307402c00381e0f5510031801f5120703002604510040003004e0891003940c038203130f46001040016000050a800c400d042d03600074842d014106400141280751400a40307481c0b0641c5d65544d80d89490940c0c48002e000c862810045005400c026031200d00003030f01c0c8210790901c91140ca440d000a01c204044403010016440000b040000c00c86403201c0c102103c10b904068a4080e5420740070912907407000c000642d290b4003150024100c1500005d185005c1c010485603c49031121040c00201a0300025103250150602c0380d201d006020303201d03030100006180a0b18180300400c4003500908010a045a80450303500507000090314106081050746043c036802002903145400710b140c1d40c0d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 471788839 1250 471787589 471787597
    0x15020c0f10020a17040503090303040e060a060f081314030f0409061a0301090c0c060c110c03060c0706020d020c01110a090b09150a0311130501091a0a1d0405041104051503070605 78
    0x181b494003080044081686083c130084c40a0285261003040c503007030039000c0c44000c40640e0700507020401d004803d07940c5c05512400d62504006522464000c0c00d0f4181840702c581400d03520f825182e80300001d0b4038944488581c0103802183e494881c02c000155035403180e01c00e240b201c4061f150f09140c0070401805007500e154401503040d4491300d0206400d0038255108400c03108190702c0140459a440e0060108400030000c00da085c00068000d000b107030901c3c5182c0070803400b41c450002c24a03078000c1105071004056034103031804c04288500038800e072001ca4240c45820382c8003100f21000900030310350110b505d080041c1150007011020b0110300a200c00b201404941d6041035008a0800d0380b160700c003031948490400a0240f1004005505c08181d01d030070009084050b07143c0c045c1d003c105110040c030306444401b0701924000003031341c2005c451135071a03451a41301d503203c5940e01c03a5009240009000038010b60442903a91190140c03000c100b552600050002d889017003c01c1650700d94031620041c80101c0c070800c090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 471790089 1250 471788839 471788843
    0x1f05060c0304030602040b070b070c02031e0c0604030303050f0c21040f0b0109231608070903080703181d1504180602190908150415020c0f10020a1704 66
    0x680d04243d20395403290203a9002e94850fa000032004100d4030244440084003c0c0c01a9440c20701c1d41d403244866011a4544c0c0454000d080303018944075841038410014401e15100a20051400740d881d40c4902c1c01034020181681c121028041c0c0c0703000641251006400c480240800d101c42141d202c035000cac00200100c1000704201d51003000111594001180079402134042c101515021440700c0d8091300c100c3c10740c842d8915100610141900344180034034411000c05601e400b514000c0c3d501d50b41c0302c80c00d0b90600c1c21035200030112000040c1c10014958003407210301c43c0c00d000f510b00b9020280d80b8003052141120003012000c3c081c80050210742c5950303000051010000b006880030072015030f141120440100503441c192101d6400103a02c41d460783c42c80c41138000072030f40350400d00003590800f9243c642d103660900c0140041c0e05440b02081c14042a51402017607030356100810f541d9078010550450316400c24041d660707100c0c42410300c15401803215000341d403201090ad65601ca17801d09000c0c031240100d42c0240003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 471791339 1250 471790089 471790093
    0x90a080f0d020d0c0306050111120702060f09090403020a03090e0405150a0b100305010302150f0318030f04030311101b0c1119141806130b271f05060c 66
    0x1610050015000d0130551180da0749000a43c0ca00c0c000001d4000d01c60b004a0010790317040002e1041c4000f4a04060b1111182c0656145444201c4c4001000080c4070f2880381c07540c031898050800007019800140361211a2082c0d6a80d1110f5681d80c440b100d040031b055800404a03040301460194514402c001c8552100d200c950124480140c500800c080c20900d10020b0700082e00e0308018010750a00310030b9801c8480c2501c01a604d42100c3c1c02045443c0d01000e000c08464100003260450380d01010010341d88211550f50156546035500d00d800703000308006100310b6089001c0c1400d410f4600f50719100b86000c18000c01021044030029a90454410140d603508445030b8645464241c0705e40c65948490f00c030750898104100700e0609003030103c800074107180b00084c45034041342846c5164a1015003c9a000042030710350502d10000d4000140241500608440d0004540d0042540981c0d400305440321030004850740c8001501c52030403800d90703d07914440785038140341c1050b010409400c08200928045000d441 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 471792589 1250 471791339 471791347
    0x20606130203130c0f0602011d030703140f12180a0308060d0201110105090607020f03090d020f01050903060c0406030e06060a0312140301120c050402130611010b0a030b0f090a080f0d02 81
    0x44da440903d4020b400c560064890718405118940c2c0901c140030101c10040480310300c45045001440c0c0d0b9219140009007006995403030b042114020350242c0b0807080c5200140e0703440baa030711251074000303400c200d03012407000c0401c070010b540106010503e15081e54141d41da80740075560305000c3c00008000340e00100d04102054006403995802803080754000d01c0070714082c14a0b0304159000070b140c041e4042180300c194000b00512040ca82e20f00d00b000c3d80c41581500c0c00707500301c01464010f0b40c09014880666405000c2c840c01c03c0000c0c030180d0014019981c95803003c11180d40314141041e03580d0b20885840e41c024003610800e00c040f42c14021380d010551139918014524400d07070314002c0c1c910f410a0b4060314840e10441c41403401c10140b0200800680000d940440c1480c007022803201400145205001c00d0054050304450a07800c01e4100c502804000351445010503500d103026680982c04075039030503103002100c0100b85c0d00c4a01180480c00307503420a11540c01e194420182785103d500c400c0c210070b00207600304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 471793839 1250 471792589 471792593
    0xa0e041e050405010506030139090815072303010b0c0f0a0605091e0c01030509010e0d0810121703061305011202030709020901053103080d06050102060613020313 71
    0x4001c051046210701c0002c215030418000341800c0da414610341040a83c52020105001d04440030b0000034500b56080100140700d80fa8003d1700c2c0c10a2640098081e80501083c1030340b10090384001c503000c0e0415540d03041141c1d1001445807036400d4140b10420810310b0030401040400030b508003900c04035804000b55990b10300c200d0b03190b903d4500303041801c035032850301e0300c007004804d43c0280303c0b07640128040143e01880e80145171089445064607070345035050560759404606a24401d510845c86001000201c99030b5010070034002e48113500440d80803089480000b0003249245104c0e8811000c95030140c0c00780040042ca0011001c1c5810082010f50080f050740c01d50700014a050250500030710b001c60503a107220b007490041c0740c145000f68001110182c010404a200c0380d13403000890351303184480d00003030040c0c80c6020600f2520f0440e000010301240420b0f100401800705d960000c0488040c1c400c810010180e0b100010386e19120101c3c3c41d5075020b602140c0112850906400955202e00c4c1e14403450303200c00d0f140d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 471795089 1250 471793839 471793841
    0x1912050f0c03151f03050a05010c05090f010c03110d200d050412140601060305090c330c010e062512020306030c04060905070201060906081c12090302030702150a0e041e 74
    0x5940159040d41c03007c0807280174000d0a00c55040c10740070724941145840a00d00200710709132062070b2044d041006400c1b14000b07041c03069094001c0100450180c41010482c1e0100602c0c05009860140980d801c50401100319000040c04106100158990300e0401e807415003401203212038940b00791100e000314807106203c40c1045c05803a02820701510002002d0400c48400d6203490090044903014844003000c4050300f5500d0314024661282d401084442c02c0d11041344400a405482c424185540c01c104009031862000b05909100e814144403150b0040d521040e800800381600305a0004a4100311728544043d00b61340043d503110001400311b0700c08a1505012400300c0e421a8048902182e550050114943d820f0241da8014803410405015280c20010b01e562070350240c8500600002c021030b9001202d5004038140310600031520420080c1003280e08020f512507220610403840340da4038840220300000780c14156001e8070490390f2118140d1030703500c00b07120080c204103034403800e0301e0550020003070a440c039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 471796339 1250 471795089 471795151
    0xb011d0a03060c1b200904020f13022808071d04150503100507140901080a090f0c0e070201060b0a0f0309060b041a12010612111912050f0c0315 63
    0xb08094030720400c00880c0c4001754210a0049a900c100050000d0002580e5407100407003002c1c1d001c0712009502a01409041d0080c829041c0c1c0c0d10707840041481e940c8454640c01d1081003181040e4441191540c2c1e284001c40d401548148501d220300028031000490341460fa0010881c0d18507080340c0c181e03c680f2180040d15001440c8c1d036110303500d51104104407601c0d91205461144403400303101c407400c0c01d9400e070001e880f400c002010034141998030040340d4140040080d0044c0250342102c80e07551116182d8240d40b4170407000300e48001c007541c04d0110000e4a8040e00301210b07a60910b43c1c0d00c031b1840c0caa44503800c9010340f034a0b1f4010740395144ca500c20308289a850b841440c0c00d04c114440c842b101a07043c0414000105000310416026900d0400c003004000c29002440020a81c03000620390f1301c1082000240d40c0400c070f1403210042c210208800309010303400449803803083d8007960868558030480714000e682c0303c2d04120a150942c01c41c0101030b1080c0910390180d50000b48640d00b089440b80c0d9018280d4000354 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 471797589 1250 471796339 471796343
    0xc0515040506070e0303040b040e0c040306020403050304080c0f01090b090d080a0f091502070608090f01181a01080309040207210504060801080102161101020c130b011d0a03060c1b 79
    0x40c1c802c1c07040942c0c000384a00200c4d4401d601840c1410714016001c0e6a0f80103a2003210003240c613000008070170260200407207018541c055400c43d1075a80f00e04085940f0b80240c084c010b240c1c818884549468038141c03861481c0d5407416903030450310609000700202150046001540c02281c3c50680f4400500802d010701160320303c0d07944582012403100d900400381409a4040609003944243c101400c55001c14124255030710790801c05095198034801c50310340905ca60008249510b032141030500754011140d03000046d40106010100c900c44a00010002c0da000e20400465038020000000942020707000380851900410b031060501c11200200d50741c1e51034051010000030b0380060103005413030700038070428054010380b8000c60a2840c001489844000d052002400740e030309400c061101c5178420041408001d1018000c10407001e02480100050325903ea4682d000c51101420100d0b03c1000080c4003075211f0004102e0030106265445080003820180450000c1081c00544100a03000403880076403014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 471798839 1250 471797589 471797593
    0x90f03110109201005040f15090806100509060609090103110d021c022d01050f0d0207030e09010824220b0109051b071220060114030102190c05150405 66
    0x1032219801c00492544884c1420144201440240807148040d4102c00070b0f40c0c284440500d14021108d02612500030f698440200c038882c100800c18050700102d40c820444a054841e49030540795441000064014030100c0f5405c4000e02004101003480054801c420490160505000100c5d54000c941d90700c0e04002e1a0b0f65030b090364542c80c01107060507140c4001807100034030803144907010a144182c840f2080001c01d0b040010114400d8002c0c000c910807107501000c241b4045585041601d0007070840450340c50550b104601d000300000e507903500403d10b84510039005a0680080314803190005a000340927207012407541c40700e001c41070b088080d00030b02c0072550f0241050b03000310b41c54440b000082d240010720088040c425194101e0100800c0400e449078141d102d8605600c0c80110101100d00c505082c003019404416100314005a84002c2041418ac070f100c0c0b409032050514840034075080c1c4c0b082e0580348807410342c44400401c84621414060515601c03400580d0b4070b002e81507100304e244c1101a1000d913016 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 471800089 1250 471798839 471798893
    0x30604030e13180203060a092001051216090b1804090c03050a0f0606090606050f0d2013090603020a03120c30020609060703110403140106060210090f03110109 70
    0x4d860208016540500b520200303010440782642c2c2c421001580e694000d01c000300c50308080000e0382c011313810f6415083d8081041000c61a01207101400400000c003e20046002c030348002c40c0c0c040b241411640380480c20104c07074a210801c102440010301100c0c6094400b0560440040001030080c00503410180c06404168120317820341c00c1001c1168070070703402200c0840c81d00904000254101081e0703099810740880751511844007000010141840c41c1c1020741c0300030140b0b403405400d8003550140980072440720ba0081100e0301d41c1400c204683c0729000296010305411010800a0708950100000441170300c0d03d443c032824266642c00c07400e0100c445503905040d83d4644007421440b0b407184003004c0c50480c801880c82d401c0c1030040d9612020007130301d058205502c1d84903003219030740346008460007154840c49200401d420250380c1802005503028590042c020341e0041603032413a0354041c0c0d407012900041012000c04166806840d40700540803545041d540340c261a401251100d1b142601c68a040700001d085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 471801339 1250 471800089 471800093
    0x16080304021201140604051909050319110a0624030305040e0a0b0112151d071715010e010e1c0b06010c05030d0e0c060307050406081005030604030e1318 67
    0x821039a80c8403400b0300ea250a0350030104003000d01d9a9504804155800a1291a0f4904907111b03104514076086440b0300300501101045070000080454040c02c070b410840f580010032084650030140c040321200c40d484001c903440810403682c09848145011141020100c2600307070482d659461301d6000340c011070b87c081002c200c00b10323100d04c0456214030945000c0001204da000003074002030000980c581550340c3e03070000520740801d24000d40050400c40b4066841c22601d8511041c010004480c1d850000303003030b07105401c0e109031326000490090021420b02203111107114011191441000303074023410030000c1c2400400320307252082000581c038210046010780c0c12840c1068502da03034000d05130504022034070140501041010050315203401100c20b000c2490f00f1904c0c151850510001c5030301d40e0000000040c840001e40081c000d00482c0d42c03e031103402c0c1c05d0f035034604202d90400c0f6910400e90140c101c1030000b4000303403041c01c01c4e403200d8100805449076184030012141c12921040003500c07415101e01407441c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 471802589 1250 471801339 471801349
    0xf1306150908100506240408011d070f06050d0e03040e0103050d020c03030a140d06031a0901060608010b0d0c02010e010608010c031a031e0a020d0c17160b0705031608030402 76
    0x2100781e141081407205041100c0440c0350406c1183d1040d0705c5c00054101c40c0c0340c07215120115001001c2400090210401b50003950f424910303054417002a0f446541c000042448900d42a081200d0050311440e0605c0040750b04c5402070f09017041070f0300440c0010000400d0120400840601940c007542c002d05000310040c03c0649414248003805100354010301002410603030180c403564401c00b428880e162501e2580c0e00000c00303880d603030b00300400401007010310445000003038a8007842800c00100038041507980380c4040d80c00110130f000d540f41082042048400e9204250001e02600f4118070000076285500c803c1c1508443c26504480101e94681c031400b102c5d140c0c14040c83e078601d8416003a41d1600510000000c0e603448a100c4400100040c0c21810103030450700b40a2422802d4028041100c3e080c160b02d880c0150900f00c0c043d41b0030315114041c0b1071420301b000068481e4504c004450764041681001141803040d00440801c40782c074801044411001d00c5407180b103d964a00c81c2c400ea81e101d090501c1080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 471803839 1250 471802589 471802603
    0x915050a030e06010509060d060603060501030605060306100b09101107080303180105062107030c03080a0f1b0209060d050a0c05010f021b01120b041b14090f1306150908 74
    0xb000742e00c800b00502465541c60b890603000442210179180d0880780d032620078081c22036584003405603450400004144060f079007000d88290f1086054540c69030760801c450340c100c4020300a440c0c1075503090024842a042c002100194a585c6090100c038051760303c0899031030820160402e4031140c2000c81800304401c3c07190003280034410301c60b009200d1403509901241c5121045810b00b03640d044a4640c001c2034003001e010310b50146800a900d241e8981d00c9007000402036002c4612100080c4103000c415913180d02c24816a1008000741381c108004491680812030341e008083c0000c0d81c030400c040c2820b000100c0c01c020b050355407031203541c043c00710501c2c0c030001501500b1b880e800c1f04c0540d00a6440b0011040b0740c1c0130600340b558000d007070401c0c0441d9044004002001d2007281250000d180500203103658064140300da0884e11144c0c0c5120a1281c8514008550b00a01c104160440440f2101c1074551500502c951882a811080001e0079680c9180e0404c80d1150b2448a030085001e0b10313030900c0000d000744429 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 471805089 1250 471803839 471803861
    0x3130501180b0a06050d020907031b05043b04050f010903020c030f031908130602040605090907031814030d090f0b06030601030c0611070f060909060e0c0f03070915050a03 75
    0x1c001c0c0514217000320300e05100c9080000d11903800100000c906034081c2d40101c40f0038480702030700507850350210b601030501d9006018828a928010a00c1e0700785a800307000c6280305444e00d41070740703500c1d100042d10003039100d4000d4070484490003005100340d680c1100b4810102a41e000781c0c01881d000a410043c90300784008803d008d005a001000380c60241080d403609070400040070324000e00d10b580c034050030380a01e03888000c000700f600b03000003400200d6580c058003420080500b00c80f00f01060f101c1c140c041e0100e0b0300100b0140e4042030b407105403401041d0200301c144007120300401500e25081080b0030600c2201c02e00340c0102c2e0260900d4111000348203401d20211342c4034100b900200813550660b112081900d00310311400b030802c01e089251141c520383c240010401008101a00c0000e240c4460009d001e1032440d00480c1c0701c85207001c0000031a0b030b2004c10010301035000b80800d2854541c5101c2918030b964001400d10003846414900000e40350401000244600030603903d0170b0b15001b5108004095030b0304d031984 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 471806339 1250 471805089 471805091
    0xf06170607050901110a021003060311040504170d0f0f090b07030203060d3f1b02060304030509060705030307030c0f05030402010906050c010e012c07080606010503130501180b0a 78
    0x4002649801800700e545001c42400e01c481800e0400c28642d06d40040c0c0d9000a40205c004080c44400540541095083d03a03c42c0d41d00280c40a088018407045520880b0098a039143c040180031100580400404154840120100d000e4610205c4401581d24615421401560300e07241c190a110084d501c5942000c0f6518043d407460030003000082031751b06034403000361504501041c80d4142c05a007402480203440501525400314101000036544100290000004600b80304106141c9580707000c0c000703140035030081a0600715100e9440031034107038008030b08042e00311100700242d001158080000d18840c041a980110303d042555000070040440e0b211038005100052007440010b03a00410b84506403140d81c1b524688851080d110f09000d0194802204200d52a00c1114640a621b81500c1c00d1543c0c2c040380b41d0942c82c0c0204c1c00c1d49079900c101d0710a480c11608450041501981300d80010b582060038071505c1c46100d0001d40b501821911425500c0e4222414208000100035007520055805041070034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 471807589 1250 471806339 471806341
    0x301081c1403060613050d05150c041208030a060b0c0d14072f040c030b030f0a0b01090f090b07020a02010305090309011b050106031403070606240e040e010f061706 72
    0x141e0041d0001030a0503110380e4010440548003850811804020700c4d0003044e04211502d00d003001a140c0ca9684400d0390b071340d4060400140c0024001c400c6070112012900c0b20072030b49a0a03150000340d07400281400b9107040e1a848005130007a40b6401800c8010b1005001e0f005004003048041c00d00300b00140c07001400b00040c0a848040713a29818400c241c020a0601c0c244c0460040b000d411307122440707102c0c40b6445468154501c203850307407690143c10710840aa0440f403010108200c01584c4030b00b1080020902e18107034005008590b0150041a01d40070a2140800c42105036a0348050000c0100c85640044e4400080f00045d580c0c1401900d41140710a03024610389000b8200080803184c01054065000e20716006c0103040080940c0880002c40d00054411407401d8000e41c06a00d03035211900982c0c8403418072101045c100d00920518030340313103031a4280c1400020a10415910085206840c5601580d074a1351069010428000c20a064881240c0010540d040210020304c00b0040340ea50301469120344 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 471808839 1250 471807589 471807617
    0x70f0b0301151803060e0a0c080d02060c030609131103070b0a030f0912050901050903010f1e0605030a0311031c0203091018081b0a0b06090a0e06070f050f0301081c 72
    0x383c1114141da400841c08509621040d2041d032400041e4500140001c444440002e0314120100705903520390820740c2a24150346030782142020b180400c3e80c0007680111384101040017a40100e4079090281e12030140d803840c16807c01300182c24044103030312640c80488002145a8003650511801c01c4101030120200410201a12040f03420807942c0442828850000340440b140ea02540a9820650009000b8040c011315036071400080e00300205460701d85540d155601c46005620701482c0c0544002038010140e822040d03d0440785200c0d4003455034014082008006620f000d5041d46030240448201d0243c1e49090080701280f902c14010a415141c42c0360801100960780c84051101800f5084900c054562a007408000580c0b02c0700300340d0000d2481103a00c5102000840080303103118090031100042c080c3d841d401d0020980c4c20350b041250580e0841d4001825039400b44400711500304031071520b0746c140170000441030300301da100381c01452455000707070303c5c8011098601030b2070210701d000c40c0f504500d0041c0c49 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 471810089 1250 471808839 471808877
    0x70606060908061b0c0f031c05010e090a06050a09021008040201020c03011a040b15030a15140105030f04030504120b0412030b06041217121e010b0a0c05070f0b030115 73
    0x4002c002c4da4100c00081d03981000d0800c01200f0403160308a0207803595031095009006510b500003010254550900d0000034002110003023080c800c3d44040040e050b41c0800f965003500070540204440d08a5075601e050001680700d003003100040460315155183c00381000d00019180168a11000d44207170f04044009074109400d01020407101320039540401e803600079000164018170803840c94241b04001000700324484049400c42c4d400c0c0d40c4c01180400c5441d8803000e8145111001c050b240c0c0c04503108001081d40d104403a004590721034007034a4103909041c1c60328101000b525040f9401c3d0341a5100070b09100600c628191021140c8110703040030450244074801140a6025500c109034071112000e00306014480d0041d00341c1901070b00b42c0500f81d80d9440e03218005508407003e5440745030399042c444811070001c401d1940d66041e2104289440c0c101291408100c940e460609801c80d442d01414100180c0e5501404100c4090420384000d00d44941c10580249240d4506041000410204180e11107070a695 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 471811339 1250 471810089 471810121
    0x12031e0f05151009030b1b220b090109030209060d02040606030b0909010504020904020907020f03030112030f0f020303010b0d0b0604080a140c1f0e12030406020f0604150b0a0b07060606090806 84
    0x201000603100c40d42c52060201000009401c210001200000c0c0c52803503403034200640544a00111031410f12380c0d20351409142c203008116900e40814611301c002e1000d4a13100a200703500440081c84040b84480b1a8003007410b4561750340c1324401083d143e000b940302c01e05e41110301c0c40d070069403100200554074140d00080c1c030541c0d000e40040d004407480c0c408656254402e000487e406105003003100d40c0c959442c07030802c840c2c2d040c2503020707000100082d5503040440c4c464098860b0746001c0354015421a402d010100400c0c1d8020185140385650b584840320302c0380c458001900051595a026111580c041d0034840d454980f643c00500498000304080d0019a89400c142c040c940840701c442c0011416001080e240c100d4201c0c06c403503000c01e00d000120001c900000003801940c00715403d882400c5001521640e450000b901d000748070810b50f4000110220a5920019400000800704000310350b0740c01e40540954004c1a00391841d607224241400504e410828490050070820300a05003840c15002e12010004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 471812589 1250 471811339 471811343
    0x6091107110904150524010203030708010b030720010c030509031e0a0504120b0103141203040609020a0e010e010e0c0406080a09022110110712031e0f0515100903 71
    0xb810030042001c0c0300006001c01e0144c00e85072010411400c040c405a6400349142c074040004120340c130038a080551002c000c0e02d001341d10a0b190180e16074240388051503d600001c1071030341005908140c8040d00341240b1105c10fa91000c101c00000c41c80b511410040695200819050700c1e948208620b80340d0f0019581540e006150410045403156003030713038040b100c5124a6200882c46045038803140240705910f100a4100c0340b1a05009603500425030031191101000c26101198182c01e00c0040c01003410764129140061000340301080b11504c1e030848030220a000e070000c1094480143c014090128208000390304040c550251034146171502d0030003840060020311101801345c9916a0300115140c10241d861054400c1c20490400103910b55225501c0071b10340144168281011510042102c45a0072910040d070050341090720385600d1002500038003d0541001c01049002903807580d244d0a03841400b2110503040b0740803c4a04100000b00c000106901860b4070440c1e541d01c84c0100180c004d413000c1c04682d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 471813839 1250 471812589 471812599
    0x4060b0a050a0f1701091a0316060c1a0903041e0506030a0902030c0907020307030201061707050d030e130b0f011715011b050a050d08240303090a0303030609110711 72
    0x1a0f0a28080f100400d15600501c0d0300903208001055812054100009000ca418007002101114508042d545e48655041030f1983d41c54450a02101d0300c02e858031580340d030080c031007107081e61001855169a80c1040380e0003103907900041070600c0600001102d00c0e00008011001d002e0640c02c1500040d1544000f429980c01c8680c0d40d00300e40b08540f414091910100c0300100400c1c2585012803001e0740304d9010140490055181c0080441e1b41000414280320f610300d618010032030b0b903082101307000d04100c3c0703480140e0601018001c0c043c07280d50740720228030a0201c20000802c6c0d80400f41c0600030300031039a911983c18004c0746082e4045200150301c04941c0701485100c0c1101d03c0803400c0068035039004411654851021207030074081800000610b01580621500c101c5001c209080c0c1d08071101039081d2140003220414803074140c1041d4400ea050150407070024240e91518400000003815071a09038000c5001c0380c3c5a501c20040d45515110320000701041c0382c01145000c003169644003100c5407190440b4454 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 471815089 1250 471813839 471813857
    0xf0905062101061d0d080d0e0313080a0b15030d1202040308030408031605160803060a1d0702070501020a02060f0f0403080706020306040b060a0203160516031104060b0a050a 76
    0x10000d000480907840425080c541e0301561110700c018203450404080e03590006800c042c1d1030701400c00880821405420900903030402d8040e5101d0f1000e84402031244000b03110a2144985c1d40d0780320140c81000f071181074000d00c6010710381d18150b4040c00c0000c2405168540030740600b0302c0c0b61004520320384000d0051511004c02c01c0c220102c00000c3c0515040039001c1c0c44080204420848400c008600079103141c0c104c84200d4040070800c48061182800000c002161004c00d5400180d01d00007454010364020300360340c0082c2d201e028400c0000018900780324400d21040c02d00107443d4060100c100544401c1c8060001e403026138010604038811107840740890312000941402c540300c01410384000c3c550240351242d0301c00103030600b00d004c0d40040c1d40641c071651030f10007001c0d00d5240ca101110340719000da0f0091410b00c40047d1001d0100d0b114210140d91034024190071407901c00c912448100513502c120000c001d0b00c4d41e000144402c0352500e4200c50701310301040080c0a25103170004d00751010311000745015500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 471816339 1250 471815089 471815107
    0x2040f02030f18240619060c080c2107140c0a12060b0a030311011802182a0403030306120803011a0408070e04030318080d02090424050901060f090506 66
    0x10344808941c00507080d4000741405450003801e113030414014a0100e940740303860003ca642034a04920b1034440c1d640400e14028161000031009805050000b0804059800c00c2c00340c40500c03405407005401c07460590f000000c0301c10801c0760001c3c98003044031082c0024986540c091300862003000007805400c1d4004401d9000d081004881e801079901000003900540c445035a0303103400740130300702e4050070010a03500700513981c0380031041480c40e40c003a590010210b141441e0b45101d62951450041e01c503a00950005030b2282c0a4810040c0c0c070000b41c096161b196035100d140d81001411990940c0000c05540280024880410050302c1500d054540f50003008401d0f034824200700100384150380c4048001c0c01f5801002406c0c41c05002114801c501940302440b82d5805180e6410152250f070704014100407090202401800950780136102181c4060400901101c1104801004001d41040e1810301401d201051059041010895004007002d0404000344940c03008003070000c0c2861300a140c040d450200ea1b10403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 471817589 1250 471816339 471816343
    0x1230702101e020c0303030a09050f0a0b150402030903030606210f01030314070203070e070504031a01030320030702091003081b07050f0a0b1308150402040f02030f18 73
    0x100103500405041110000c1a00948003150046074101d255001ca1a0b88510900200d40c0b01541c0400401035850350742e489907082d00500e000d00c800d54080c071800c1d800c1c82c0701c5201088811030a50152522065520381050782201d41c1c0f00040e01d9502a900610901189460010580341c004104840b10341c1c64210f105181841c03001c18001e01080c10600c5024020605114500394ac180d074040e943e141c00c0350a400303160341440e06c911a00250961b010305030402c152013001c0d01440e04400d0360703e000c5140070b41d2511041000b200d5a06034620400c50700004104044d000b210175100380c00e0120140d4484030860302c1f8503403240210390010b0f0240102c100018070004d1059407480c05950310480b4952110407400c40290340a9040d92804000d10400401150528281d800c503071202100400c2e2510751420b21410200640020b20b14076030320400014003040b00c0c48140101c240481000f0b80c00100d17440c150040100381c0310b521622052140c8100180070b000421095040c0d84400d003480c01d903503034841d284a41c034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 471818839 1250 471817589 471817597
    0x30711040b0607031223061201020f1314010918020c0a0b070c060c1e1404120b0702010f1103040b041403040909020f270a0207060c03050105040f06050123 68
    0x142d124a002074075408142d0804104400e4a4040400300100241040c1e00710980c2a1503e00d20b06100c40c08001a001d0719015080900410310b540000d030a081c2d00d06544107054014003031902c403000604009100440702c40f0580e03d00d03481c00b460b040c21200e1030200300e15500e8505500b64450a90001005042c002c8200305003180a5400f15421280d0700e07004100504403031840d80d044844506000850b101203219010440c5000322884004031000007210099940c4280f1a4080074016003d100028113000c04080651195000c1d051000307a5140c200c40007803c48000c11501d80d41c1c5c0e450803c0c2008948102802e803644194040700e90311494580d400c02414001002100004078440064003040c1c0310103031b4000c044450700c26507640444903480000c005e2042140010003005400408a80c00041940d11704990402c50100c401450445075071194410b607400039031681c3c0400c2c0c4941c01001242024400c1d10042d829032103041011034140700c0000d0000a001c000901c8248010700c1c0000141d240070212 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 471820089 1250 471818839 471818861
    0x12030c0305090d0b220201080a150b030103080a0f05180d0302190c1505120610120e15090d09050625050a050c0d052503050615120a0503071104 63
    0x10719640384549080c142c2e04d0000c450044180c2040b100302c0f001c50088010138052907905849154490703440c8070207500280021b49075503031901401c580014544a544000318065801202181d80e0744040381005025080c01c0e0700700b9000c10804000c03000011400f5001000c04c81c008880c204980c0500e030904a103000d440702c9000341c074040d580c00f88034204008054040225409040350b0400c1000c4003400340d45d5070044506440c400c3c1f400a0000b1740f82c0c41e203040311105280250030729940d400300ca104d90b20105c40300a050505241d1003c4a07280c4203c010b207082035800b20380c07080144080c0c41e20020040900940d446070500034800450008003400b403945a02d503001482ca112000024181d0030003683d20000482c0541d924041c0107805506801c1036040d000005030410020000400142d0081c01d5a500c4094501202e00220a001c40001d0050107080e000e003d8016111485221080c100500e092038192410304680c0700d5904800011408410740f200c6c540c0003201c201086002e8008200509040d202e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 471821339 1250 471820089 471820099
    0x8060a0e011a09040f0f0e07061e0908160602120921070902070b270715030209060415022e0b0a030228080c1e1201110703030e03030112030c030509 65
    0x1504e00130019a40506c04002000005004000f550200a91614031a02800d40040c401a161001e80910f410041c0c10b000e905140041c022566440361509000040070400480807000c2c40810049904005405c1c0194440c0810f51514403d5400245001c984001103046801880c10420386890140410350041250708015559510289403214000710110bc00024030300c004080c1501d0b04506004c60100e003c030950051280c10b003410f2540e25903190084080c0101902003003010f407251210000740c00103110310300d80c1181c071140c903041c040d040c0440a07621000e02c1e81080b8580c503507100c10811400050f4415040018400829400315458104903080a074001c0c0305c2504044511010380306801986408408080ca4107880340480c0d916002017161340e80d84000c0081c41000c1c55034104d100c199004c1d80040c800c510800740c4252440c29184500c0c80e201b5030200124003503052642600400c00415003090183d0300d190306250b2001c0d01c88070801030103810031440401000030940503501301d5041443c0181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 471822589 1250 471821339 471821351
    0x207151b0b090109170f070f08040b0d0e0c01032f0d050c0301171504150b0a03080309010b0d050d050a1101060f0512010b0102070612090c080a0308060a0e011a0904 72
    0x82d800d001c0c0c562450201c8409128900c01014004610140e8088004402c28145084400e4403070b000b80c0010480c0555000b1020040040c0345091140100503030140b00f4000b00310b00115482881c00d14003078604040c103050901c0f0400c3c1c03001d00402c030408000b0000b010318680313102c0071000340040c40c0100071460711170300d00d428184007010440390080c43c100c8009103640c80d084400311038000d441d8846841c4c450796a140600201e4001044840c454800d0111351000164807107504000a080510940c0107441d1081c001023480301c92240bc1c01454480c0000f5500301da5403088558555640b9880342e8524810441c0120366609564400c40303030b800020b424000240100d40d00c0740700841041c8800d10030307588600441c404111210305c06000b80d50031040140c01800829250450683da407092511840c05000d5440f0000c0c0001a084030101001e0044480200240d0b0828a0090241e110103081c0ca0701c190320303a40b0208a84c0130340e07011081c191201c4a070000807000440c102081d0f54082c0c40c0005d540181044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 471823839 1250 471822589 471822601
    0x2131401180e01091a16120b060c100b01090614120405010905070e09060f041a0603030906180906090f0106030e0a060518011109010c021e06070803160207151b0b 71
    0x100f002c040403005170910102c540740c902d040441c0d81c54080c0e4241c080f4075100742400c64019541d1060b111604080c103000d2401145241c40c5007440600401e2800d29561044c103207445592203285500034048070304010a000c1d503d800341010324090a500c0100171071810000a0400c032080d000880510f90220488407156203c504003550740c0e6044858564911840f030000d101d03605a040040c2c000da400c1108149132400b00f131601503a82000411151305072008010141031500e5240081064168259115034040025001c01c04080405800c0500c00c40c851410300c04c0b0401c505448504586250900003414040d4510361400c110407004058040d929003c00c10100d000c0e04c3c90f0a810300b14100c8000c0149040c00e40303500e016405000d0509000075801c00c169401801c04061902181c900f03240c034000c20f9100d11000407060b500503141211960404010b00206800c9e1607041e00042419001a1a1182c10b0034030041d017910819058200b04000d4543c4200d17410100d50144402c00d411800b0701c00149003103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 471825089 1250 471823839 471823853
    0x60203040f060b0d0b0402240318010f060609050d030905100801050112060e070f030e100209100201050c070809120f0d18030c062607030902131401180e0109 69
    0x11099424a00f01001180607281000030340107819484130303031011103460f55002c1c44251445e80100c0b46400f001d09502c0350380c0b042d4520245110310002d001580920310b04000b01420348a12940c40c8810a00b400d80c24000640c000032000b09075001950000000c01003820112898040340d480590048001c1850f44425544107404905a60302030721180880e002400c900c100f200d00030710444282001c1da1001ca003842d8402c0c040304d525440c95180202c9c1400c04066440e081c4030351010020f04c0d06c1c1c2e0000d00c14819050603203201c448a1040d0008006034a800010b54002d031080080041c6000000544e10070181e480075800f1a02007a80000c481ca4901e012440c1035803030041070840e0000c0f2f03c4481c490081c094034007103030100b6280d108040301b4003140307056415a00802903545a810350a0601010405030300186860341c41441d81d42d90100b601c2440b1700520002d0a0303075100c0714906500300030351001d130011284030040c1182d95004508482141090080c8002e041c2d2010000e91942000203030740600c203031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 471826339 1250 471825089 471825113
    0x3020304020906010c0f021002100e0a0210090806010509101205060103020906030102070309091d0f07050117070509120309060409060f050a06170702012a120b0114070f06020304 78
    0x4242c0d240401500c0d03a200545150b420000002c18a400e080504401030411250070f03900a0118012550011058810b680654402d07a0602d04a035000d4000202503141c10004c0c1c3d0344a901c9420b10301e205500b800001510b0b00c01c14003965008e10802c1d8042203180050304412001030034400c03400012009079150440c0c544000b840141e1081d0080f42c04a94140b406200700da00c520b9054944e600c01c107240034602d802401c16402c034242c2403461442d102a0b100c005011201c0c103030300b1490240c41d0700303800c1c0000075041c89a1040f0200c0c1040201c010801091780100484411003000c40d190002c54550300c6034146188101c200713403500301c0c00214001500c8030007504518151b40b000000001c2c280e07280e50500c1001070551060100160b0b08130042d0050603642a90150800c0c882e2001003a09081072402d180300d81d603001c1003126101003c1e0381c2c1d8001588c2c0070080104615407410b003800b1203c103807000200341074103075100341080d8907000911504000008811202a503071029040d5101c2c6401d0074200c0049013 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 471827589 1250 471826339 471826343
    0x304060203240f1c02030706170708060a0e04170a020a031101110f070501090b0c0a02010e0f07150519020307200a090e0a02090a061403060c120603070308040603020304 74
    0x80002400119030001035402000302005060140f80210000820440746000110101e140031344c48100005600d0a01a25001d4400b80d1030708000001fa00401c090712a000920803c100000d0409105c050b41d514000d0f441150013403d110301e49a200c0707081042000ba40c0b040302e00c005450011f16042160307004103818010034003e0700c0da0b210303061001c4103140c2621024201c1c0e0300c00d580308100d9001100c0500d005000018010000042c3e1740c42280e903005480401a211100b081401003044104103074240243c0829030b1052001c1d0a001c400c1b07000e899603c1c0d407903000790350f062503000318a81c0c003031072050058827072161003090074880c1d90781c3c8039070040c0d1a0b500181094601040c0b01d070144401102c1c409040c1030700b44015004604191800e0503070f81c010302110511450364040e5601d07000241c0e4130008020301410300f0000001d070305450088092540714400405900a42002c81044070b08540c01d01070f144066258402402640d0750080002c0c00e0054942008142e038201082c0401c4c6294540d000d90701c00c1d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 471828839 1250 471827589 471827611
    0x3090816030819110909040c0305120d0f1401030816020301050c0a020111040f1233061d04060b0312030f0708060607081c110408030309071205070e070e060304060203 73
    0xd00300983d403400c3d2061004540b04818040003c55401d00348044800c6d40075005000d1410200e450342c0c0c0300d5050404005441c014158046000102d08985100384c1c1c42c0700701171190070401d141c001401d00e281c0000501c40940404000b00380b0603d020f844082d40740006c0d42c020002c108034035100504d4030041d001031511000661030000c0350030b040c07030141d0121000c0e1b500200c440504940703081c103141420358803001d08603050407001101d080c000000188442c104481c1c8000c610a03102c060300108100d4a20380d01c02105903144503400c030f1035107803036441035078100b03400c00c80119071a0a0381d0080381c0381680d48480382908600c0042000742041e40c1d559042d0140e0380301e566401003038490004021041c01000c0010340590710400c107008002e034030800e6001c120304035001d010543c1d41c1009044810b9800c03c0d130001d100c5800000801881600501c6004098074040300410420402c40e22031a64031403e134020301c00b50040c0031011030f80031802011895072000005003440e1356898285081800b941041c1e60300700f02d413 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 471830089 1250 471828839 471828871
    0x61b0703060e06070c0b0a1e0b10030c0504050103110c0609061e0105090f1902041203030522021003021905040311090910021803010908070b070c08040303030908160308 74
    0x2940b00421858041c507a0f5580d0100080d03440c1c0c40c1c03021202c1c0081c1c0b03a0410560f0340e94130400f80c0d03034480c0000c1095210402d8001004c0300705009001590040d04100020189002d5010441d10303000002c1c1d0b82510802e2800003083c94800700c1078007180c850100c0c01c001c1d600c648000c000c2100c900040140c4900c08680031100c00181e9600fa010b4030744020302a10b80e105003450300065412603101045a44460305e00c05e94a882e201441d0340300200d81c004e80181100c00500300b40c00040c56058043c050b04600c10040c004110080c903825800c9010008030000d100b204812740b10002140300350142e944d0500044858035445081c51806059603019200403200320b07c002c05e550310a480c01c40800d910503501907000d0200395022400210013517010b02e03007075505c007515203507122101c4e2000d00c1403181041c4901c40d60b035602d0780c0508020701e11110082442081000701441c141c001525071007550b04036940340c100401c0e203040ca0324007400e03c0d010b4081c6060100702c2c10301c101c80c14140e104c1d040a002d021038104007490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 471831339 1250 471830089 471830111
    0xe0307053004030c0e04110d1b06052502030703060c05120108031c0f09050327060f07020105030c0f0d150605090303041502160801050f060a05010804030e061b070306 73
    0x294010b521000c0c0c510443c120080160f031144108145c2d01ca0721404040954000c0c1c540014402000082c00352096100c0b060012105032284980c00060180c0e070501da405c00c3d03020f5580b5281010220b4110310131781d45940810045443c00c01100000d1035004070103000d801c1d49824000c1450300055a51402840d1074000044d8411020080b83c1c0e08220129101e450315803ea01039901401a4070f10315034800b42e0342c3d43d030070340800c20a0010300700b80e06802c84d2019081c0d4555084103500341040c444184181c00401c0624003040081c000c44940aa0a0074480d450780e40340080118a07002d0181202026400042c070040005040c1e4400c3c83d9202440400e1203050b43c139240c00725518017445040a405600410042c0024204c02d40d400d41181c1c880d00c1103d5600a9203000d41000700059485002269142d90070b210b00302c108403014550090054444e0144107107032034002002e0540141002c0c0500200c00300703019445d141c10048a0000408500c043c0f5880300890b6195a0380c0001d00c0306460b9a442d120741004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 471832589 1250 471831339 471831433
    0x80a02100c0c02031e10091a07020d020d0c0c050a03060b01020709050105061e0c030a08010f0b070c09020310080f03120a05130b18010f09021c150e030705 68
    0xd50580140003445200150f902c0000306140011085d001d03407203481e0303c804101841e40250b601c071600c94800006200e02050742881c02080150409055400001c040742034641c0c00964640c4510103444c00d0070030401c035400d24115600c201d03000290405040d1401000703002d06a000f10401803001ea08445510782d0324280842100c50030b0113020b0b8070540800ca00c1c0301071444a200d1600078070741100301d1454282c042c5880d600c3c59100340e0200c4040307070424004200c02d56007910754400030220560304a00c0c020b01581c0d4890400900c1c01407621043d03001c0040f45400311660141d070050130749903003100e44101d645100955650095034a2024059400340010308e55074080c080e2034001c501244c81005400190707600d410122000a00c1c00040601004203103035056424010841d9018000c41c00060010544c010300c5108011003011b03503600709042042d1000208141c205003415081c101001511404cac4150340e6003103110ba070501400c613104a02c1500c2041800601102203c800400074031414440390549130 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 471833839 1250 471832589 471832607
    0xa03030801150810060e03010b0d030806130b1318051509010b01140a052506091709100e030709050c0306010225030809211c17060f010c080a02100c 65
    0x13603e0300000396800c0107880d0080c1080d60380d004000340081000740c640030103c0e10501161505500140c00d84050006509000030b4a400e50145c0010074001d09030540701151104c0111848058030a5a40107408840404a04241603450780b0406a80d00310110f604180d05180341034807203070029483c01070b01081542c0941202e031003884e0071401c0c1a0818a14142c03d42d52900459007083c5000c0b02c080d407082840915000304c1840500c03138100010303811402d061080540c00b603030072041000041000101190b03592005811401d00742031500c0750f8486102000b0a080080c1c550041d03800c0c0742440180034018280c41d018512481e400e80c2240c1c00071013862540d02c0c8105400b51340c403052214004040c004120a10000d0010b050701614030001c1030310390148003401d0787d415031100e5000c0d0002c0b00c07581c0d03180e041004903081401e00c071b291078100c44d200300d03620400c9054060441d52190030326022400d9280d003c1d103100060035800c0250107803a00e1261401940310448005402a202d2074a84c0c44440240508020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 471835089 1250 471833839 471833851
    0x70615050301090b04080c0309150a0206070c230c040e15070e090705030709030f030c0c06180e040609210e040507051603020709020406031d06040f0305180a030308011508 75
    0x22606925242ca41d090254400c080c8803d0f1800208039451b080e0311191648ae610640301804286c0e2038401d488000d0038168042c5c8150200176800220fa80828070f801c8290780c409007442c1c0f12010300010004458035000005140315042810300400c0007104001158080480102c0d21050075180d8521100700c90368070800e000194400c9480000c01c1075035203d0005180d01c070005007014a02c1a88985808005440c1854220b0001c1d0383da40310001000945402e40004221506200c0c0e24848040009400c0310058003e0716840240c920000d000c0c090660040000a900001100c55900c014042481d1112100e40d00d1030100f0f0036480022905c4c10f180c426180300300c10f5035460030b040107068071000d422070a1000c0290110301c41d004011460304981c0c030041005201d191000240b011006050320b0007200310140c0c1c402160045000c00c40855621840e603040190b25240040ea1741090307240740000030b0203003001c9507048044c0600108c02c0541204855052740c000f0b480b00c500d03102a902c0301310b031544011148 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 471836339 1250 471835089 471835103
    0x203060a1404030f0903150f1407140a090b0c010209120f3f030a060f08070302150408101d0307021005031e0903031008070b0f070f0807061505030109 66
    0x150211340310b506019507660b03c40ca130003203d2640d0307522403032000241e00b1503a045050741c030400401428220b00c540384941004071000555840c0c042405014155410015055000b000407562a024410801c00b005050410051510703201c0441505001703420103030b004c0d8042e444440c41d001403020005196407042c0340d00c00081c44800e00494110706030040101c03030207008110004078501581c0303000952081000154034400c1d01d074a058403a110980310075500049000c41c05142c14000d103c00801c240003503913010703180c0390381c1000d601300007404500c16030307006070b13a039010704000501c07001c5180c1c0214007081140b002040c2e41c1d40c02b82d07007030075103d03c2142c900a45c000c0803244c0c085089801400550f03440710381038002280180310804d0503141c40c40300f1115100903070400020850700e01101c006180150802800030000a0b085c610904601c2c4144800c0314501500803072040104a14a5004802c4984c003165a9885840500d07092000d40b40443c1060540c192444000c0399500b4140b0030201541d030401d034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 471837589 1250 471836339 471836341
    0x411190b070213020c15040303050601052115031f14061e011e1e0503040812040c1703030a0e010b01050702090a020d15060306060201140a0c120f090203060a14 70
    0x100708030072a803220403c2c0720680d400b400500d181480603c003a043d01d60300380540d07490500c0c0900d401021030b60001d009a05100052140d0710bc8030b44010408010303050032103183c180d41c0c2c85004800c10300d0030315092056030611404214101c401440003900c0300e0781600035003d12001c0c0d404820015003480c101c40fa50f800c034044030b07030212034035805103c1c8901464042c10520800c030081000d65040003804112540403c92500c813411a40341c140040c001004601d1400c00c0c150b050075131701c1481600c91700303078048a0054803e000c1810700001e070030700800402c9854502d64054100c42c40e0540c07203820898450469030b10f8440d901c910540107003d42014280c050b1b440c103113091110340c00c200004074080d0590241907428421030028060034840c00a00891341c1220302c20240c5030030002025510030380c105404590421414421070341941c0d2060350404003405d00071440fa0030030b030310443d0244044409184035900f02200112400903aa20401100307000360250b03159a03580b180c044041d500d0140c0a40588800a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 471838839 1250 471837589 471837593
    0x3041101031a0a0f06090905040201050318030906031008061003080d09060209060f0702030f010902031b2805100302120c0306120303011409010603090302120307050903060411190b07 80
    0x9440b002640384034007081c0490000d1071000c600041c075150400b4200b1201d85009102c0d16820038122401089008000e1266181a40c0020250301010300000d001c0a580b042814203280244250b40e62071002424158491800d000900741001d214483c404050003410081414003c22000070400c0c3c0340c1180341c5924003010003150500401c82400e055481130f609101e8900c41d962413100a1201030b51081e1941d40312226030041506017400c0e42c21005440c2e03d000103180060300c02143e02d8140c1d94454041c46400107291011035070200604001c0b656499443c9442219200341240b00c601b65070301555650341400c5040c030150228424500c2140100c0480c100088203203440b140259482407002d060f440081c01d00c4c0003030740c0ca0340c0c20030781200ba0b05080c0cca01400b510709080905c80c2c01440d091070103100d408025100a91100207440b560f85103c0000000102304d517001e03508a8a8214006e4100c940514250800c0b40340301000020355031040215242100c8101003404004c0c0544c0c83d0710154502d0001c240d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 471840089 1250 471838839 471838841
    0xe0102072001020a1214070c030c05120c090606090315040c0b040e01050d0c030c0801050f130803070e01031512020406060201110409091a070804110a080d030203040501060503031b10020304110103 86
    0x3c90305c14820030000c0c1401d4146120868003034942d05215400a0742054154503000c0d44089060b0041400350404014590310301d18001481520301c002541d00791100e0b121080456101e2103106090782e0140706501c2807040d10007401c0d200a02c980d000712107003008640c803550006601e118900c5898101400f00005014900c0e01180d00c00c04180719031880c044040d0340751342e026100358240d4082c0c2040d03507480d01044207443e484c200403517101c031004007560f43c4545107564402d02800098080d00410000c5009005030343d000b42e00c00841d440109500306641941d85d521200c5100082104030300403401c007034000840500501546410300007620080b8101410080510010898551305541101ca040700d164400c005442485010b00c90655594142c1c0c60300381842e185014030180a5400707440000f4040040c1c441c08038412000c154545405692926142401c0340505000c1d00440d5250100282d10030014201c408500c080c551890140c540003071121141c0e9049000885000d40745403800299402a9071103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 471841339 1250 471840089 471840113
    0x4062c01080f07031e060c080106030e01020a0c08030414011e1a09070c05031207050301080c09010501140f0f180909010614060a050c0604120315050d0f02060403060e0102072001020a 80
    0x2c0b0b01040c10301c0b840c450320386c0b00564245d110118003060001005100541d49409042204603150000358541103800100405681c4000c038007034a0740d60088003041c1000120008845c64000950007801074000c00b41500c4c10806400c801d044001d0700d0701c03050942c0c8100b2002c82102c1081c0041284440e507903400d10644005581e00001c503824001004a071044038010320b0030300d0250009685241c2c40750f042c41c000324541003e0841c020311840d800c200400103a039004800b40108241107072002c5d2180042d5140040390b0146824003030202402103003016000d81400c404d2201000300300c40700e103074541f01c205030103003202c029004180791f070180703060006442d0903d1300081281d50050725050707142c0301c2603e802900300309050718100c1d410a0a140d1079801c66501d4016807051001c08084008040c0c54240015010700044000504115010f0300700b60565851000b601d0007140c10240a01017004400e002034000d600964045031024840e02c0740b4030115400d00a00717040d080c01a00204481c0e0380980b034440320049 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 471842589 1250 471841339 471841373
    0x2406050705030c0601080a02011b11011d0a090c08060a030f0602070c05040e0f011b050306121f0501080d0c05031c060b0d0608061807030305030604062c01080f0703 72
    0x4010010f610103464100041c0d802044200054062808113200040c514031003000700c40c0074030003c0f804c003401260145101014000382420001d1b41c7c00e10f030a1485100c8042d03003c080c1c0e881480c8010008a245840d040150510a507565003031595840358104109000b1600000d48080c2043e40708400082495004001c244c2c0079a07070700c4111070781d00c03c00101580c4090251a0080e00000030a00040f1024040c9282007000e4003a062800e4490040090240c0401001103104145810312918903580c14800800d051b0244401d00342000000c2400ca00034020178452202c540c41000d1001c0e6100d07100300491180319a01402551500511981c0c2100501800f0144007107d696000300254000a0350010084a007840d5408218145882c03c01402d20301d00400884a06071542c4583d00007190110b040700a80b07905052150300c075101c1c800841d00404403900903000d15454400311881e82c030840c240410100c1c2c51001100b0f0b050384c89621058944000c801e14440503840b012080c400120b0b283d0120903114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 471843839 1250 471842589 471842593
    0x804030b0a02120114011101020406170a0906020c0f10091509050f01061e0e010e01032301020403030306080d03090308012303032d0408060a0b0f031f2406050705 71
    0x514950100f00e07840003a407050391040361a039505600b550300540f09000c00b81c80907008509151601d0005419064400751204080781c1c54400600c0c1c3c1002a846170b4100e5410403000c5440d07020b4984556500c0380f40700314401d07561080160901c1c04035003d0144086065100300000e10390341d260748504020700b00c041c000719140d002e40401d00c0d45145092113503500800e060140d40240c80c40300c91144203514400e408c050010700310b080061014884454400781101d500c5085841607524112030020340e255601c0e00c900c0c044d400050000107141d0705401c00e60680e46408107907100e40355540703000d40490f004403a0060118000d136004004510b280c800c008044101d0981c000e0380030310360500003811544a0b40f1222040d01d0888001c520100c801c2640c80340f565007481d1348038a02820800301e195152002442103602603154400f041594803045010302c4039910181c01c845440d01c551500e1002c0b0b02c001d1507807205541ca4801e12090b0840405480d42c904d6181d000d005080310305181040350b0079130009509460034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 471845089 1250 471843839 471843847
    0x71d01151d030d0806010905060c070509060105120408070c09200c10021b07080a051207060e150a05060402040303170408040515030108101b2f0f1002070804030b0a02 73
    0x2502d081c002c10b00c040e00c540c1e032000c2c081d103001e400240c03400605420450140e0410710440791601d80c0001c501c015a2000c507039010179a030340c080048a003403007115a50040b41d0014000e1004009036074003d0b004c0c941c4a1022609116140d0611a085508602c196030050303040400111060441030000c149060340c802c00e8451903002082514280c7c6d100ea41202d840b48002e610601c440c203010b0002c203000e405440050007005540742c840e503070750710403a0403110000c1c0c00c00110b10b4100140d0358440c0510702021020707a242c65001450045503404215030750403071103041c60000358440c60144200d42c01d482c0c0c1511804c00340c050039a41390a500300c0042007200c03004410400407409581e4400d405074281961101c684e90b0398117040a481c24002100e0000c0c40301410004100012000007040c540c0605651510308452004503040390066261000f0b1601054250f03c08280e00f03040115076840541c04820850f03d011610001d07007001c030701c103680001e080800c0a0105000103415408134917000303c0211000b41c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 471846339 1250 471845089 471845147
    0x60c1f0e010c050904140402220f110918222a090b0a03030c140109080a02010e0c0a151202220303030b12030906070203030d0509071d0115 61
    0x3103942c01c0d0110404a0000b01d400459031500b40030744c02d03200000306101000d906203580400e0018203150303e110124007000c1c238040d54401c540e0380111201c101c1c200083c0003010003600909001e5118032005809444815544040c0310410040c1d180240d030400c1c0311000400c03052085103810307000070b00b01716110f140a04032905080c402d80202d044d0400b03011031545196280c00441c108035035410055034010503581d181000400d801032008100e0343e400a00054280008500003401080d086c100180350305c2c0c0c0819110320300d0b641540411031200c0b011040310b460341051000c00c05054034901c102e05c922504089956810345c4070315020746158403810070150034143c642035640742c0c030351005050468500e0041e00c200f003450f501d07003d005810b42081c2d80350003000c50050b0191381c0b130b842035501c2c15001c0d90000440400f1502c042040380c0440d8408801008107082c09245161039041512030290b050303a101411841c040c540c6290141260b0451202d40c0110342402c90030b0350f41070b40e180708a4031800c110352080b81d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 471847589 1250 471846339 471846341
    0x20d05180a15081503210706050109020c070501030902100509010c050304080604120c0201230d1a03070608070804030c030512040c05011407030c021915030b030c060c1f0e01 76
    0x70190808408014500741955030041001c40010001c2d4101c0c2181030596401341c901040d1141414a82c501c1c030140c0151000304c03283c092040b000018039407031030700b00000b078000c000360b01820780d949004069501d026035520045040d915052800f035408040c400d2400c010034001c0d0000d042409040c103003d4103441c03942e100c0a0854200350710032191900305a042008012104215888000050500322841056a000280b903001000354004612020f20950300540030b02c01c056941c61a000c82c4140304002030541003068044000510034001d00c0b4045000c140386010f04d00c03892054205654100081d0b860751400c45400c022402300b0384c14170104001c00389203094030076002d034030590280b160407191070f14142c00141075038600890188800d0090151100080e40310440d40d86480c2c04641c0d030002d400003291f000b41402440d5100c00000418505454242605a0055003501a0840641b00d40e0000001440703503a22034075420304000e80158034071790950b0443e172445401801c02910001a0b030580e00720070038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 471848839 1250 471847589 471847609
    0x12010e060112050c0a0806131e03030f0b0d03080c070611030a0b1206091203060f03010606020d2606061e0d090507150e100c020d0303061e06020d0518 66
    0x220600c102ca041000703001c070401c55120382e02d209a071040b100526249440e611110b0240c020042e02e0780c1c0c913520605218034413503984c5a8502c451100d6000207002e00e03014004000a8440c0110b25060000d06030640c608032541e6283c940e015116149190768983c031b284641d07030000208480050f070f5100d55107600315200000e1403062411000005d0030000003810810f0401e5289080051940a1000c1080484012900c0a2050032406c4501c0d203e4542e83d0000381e003031b00c81551a50b0103618100380028030756030004201101c480c16403144000022080301f4018540441c10302444071425160103e4a94146030f002002400b0402e0f9410040314088803100c0160360000c84480106900c601414051150901c90440103001181699141d4486844080e0440300808a514499196020002d07807150092003035481e031340c0d801816803144504034038014008001c18002c1030300300c0c0c0c1e1902a02d1401507200f0a80401e90b1481e80080543c80c00510084907554007151f50f161031103030b402c91031690980300c2d85102c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 471850089 1250 471848839 471848849
    0x1902011103010b091305040816020a1208130f1a0d2301180e10090512040306050f0c0a0903120e04110c12030709031e140706030c0c05070512010e0601 66
    0x3c0307541c0c0c1c01d08208100c07022401610309154589000f060200240440045400285841f80d902c03440250b68000606200d074581d204410141e01504a9000c002070003000700032700044242407410283e02d03001c3c0441e802115001303842c00740c10401043d4584214207005400c03045050380000c90141003100007071a10404400200a0b4600004014854051218031100a295000d00100314484190120960b0ba2030b1903611511159030724062803060141c1889a40c10034801d81d40e00d50303511540c0303240c10030051104454030075401428401003003a51072004100d03442080c8555400c4081411915481d18003c3d03076020385814880126503030b6002d500d59011303c144038011200b1440d10b40104212040c101007180a00041c919010001c0000d4903400c91003060607a41c1114490009071001020320b0301181c44403102620480000314241007260300043c09a0540b041a501072013802200402500c0d00c0d2041e0740002d056400c000028051070070074503060021203285900200744038502c904004e052103020307000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 471851339 1250 471850089 471850109
    0x40801090311010507170a0207050a02031516090303081503030409060b0d15051807030908070f11040c050913110f03040b0606090d02040e0f0f0c01090801060605190201110301 77
    0x28102c0c0e0010a104055129500341403020445d5803224011520761802040507600d19408224402400420400c43c880e10380e0150460380c0e0070810301012120240c040320720703111416190074901c0c0c0480c4a1007070041100d0b41511540d20903110030b03000c9802c4010440320b90350107200c14040015881828062907000740102d0070800d81c0c800800e03080c501514036805040b41c6554840e541040f180d120003204100202c0b140304004059103950344101d000d40814200a0410302e004030701501400b1580d0342024841c2d114440791852070703081000344010b440d00362180d000420010300c49d80002e41020105100300c0c4c6450103000500340c000c140090055081200700c200807801c00700401c01040b2140346030f9600968200d4481e428000341c03500141c06c11500da02c0c028055525030070703121030401040094100c803c0c0910140c403004204856076590300d01500720f0060008008003c0040c0c840c0041c4644000e981066941d40e00c1c02c09440e07914074014000002c208c00b10340d42d0340d00310034801041a0280d4060503010030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 471852589 1250 471851339 471851357
    0x117040f080d0e100b10050a0306030605010b0a0e090c180303091002151e01050d1e0b06101e140408010606020601051e09011403010f050f040308090a0803010504110408010903 77
    0x4140c4c5001d520300850785180d86172180000c159079980140c030700c4000f007030f02d8081e540b001c135070408401620659000601050520001140300d0f01400082c0c200d80045e50340d5031150303000e603030100200e042081d2000c4c00506c008100009501c0b0181108200404004d003c580c079026207440820b11400c8199034550041e0400e600307041c1c07408400c1d02c24607013024002c070219521360042400d001484506100300d51040e007800a0f04810070010b400580d40c4200c3d0008060301c03000082c1080701c0031074001c460321031003440c0360b070b040300f00d503034000c52035101d039000110001c55003017520072030a0764108800f0203003800c400700501c03000404000c2401a4000790500d50301900c030780d51402d014407020a102180c80c16a01d0105541594140c5802d13011504540200050341d28030380c0c011001c00d0041c403290207106250b13400c110800082d460260754060207030b807090344c1d0100e85039035a010007611411005070050042e0802c000410180c80c00d6003100ba03079480400807162409a59660460840d802c240c821004600114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 471853839 1250 471852589 471852611
    0x3030910050f09070608060f04090303090204200403330615080412030c03060f030803060a050315070305480405060a0507050307050111030a0e03090117040f080d 71
    0x20107441d40120400d06160401d04204086a0b15000f882c05440c0401c408a40011079943c2c40b500c0d00218000041d00811007030f462810010050404054182c1c050750600d00740004c610000d80710281c0362800392006504043c1960303030f442c10304440d0000c400c40030040b0707424166000c0340c6044204040b003145000002d409160645e442060f6149060501c1404a104200004900c488041003200400c43c0380000b0380e4030600708242d0080155030800aa0018100e6002c010016004000c501800048507400c054542c3d83d420107039240310301d141d8480180c050001003031620303010340c2001d0b0700108042010025074000d20154030b404000450306000b103000c465248a4150308043ca1180300000d0044078074074045c10400400c010b485008403010812900145650034040180140c4810740da002d80203001d4085213540310b100d942c01c02e4641c0740c0410f00c0c03c1d5400c2c22200c40001100d0003460180c603914180d15000c0e14801c000000180300b5504941a840741c0e0b0009064800208021644a580041c03003841134 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 471855089 1250 471853839 471853841
    0x103030801140108280e070612020a1e05070204090f03030e0a02091b1c05010303020f070305100b0607050601062007051309080d050903190c0c0b0a03090503030910 72
    0x40e8800c0c52000c800041140e85a6132208569900040320410314820b041c6031040d0b9140d6480d2020681c4000d403410080005620000c22814101d0782d4507a150008060b01c05a010100c0c8558188030000c208290144003a01603100c1d03004519810508106045c000d02c0e8000c0b50941e070300c202013200c0c45100d0880c003204254061080c1c0c0c0000719000d000300043c140c0d03980030403403401015000300101c042c4d1400b8141400003100440c1d441442036001c00c00000884980f55001d03002c20301088016000d02c6075041d9550500145041c104c0e5008001842d070011038050b100014030500d00c03e942c0006081241d20041070741046503600070559544c8107108000c0842c0400d00403d00241141c80b540c1150504000c25a105192503000301e01121001400c082e25103410384080c4103d0442c261294100020040c0b4100007001415600300c24440c0c1d103124900e950303011501c281a006000384200c54201c5d0500a47c4040130152132040d0b15820005a180c869482c0e00303142d034000b226620300b41d5200e501e503d81c0500c15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 471856339 1250 471855089 471855091
    0x21040306020d02032d0a180203030c070f08060c0d0c12020a0c0201140a020601150e2806141b2503110a180b010216030807060501062102180402040e01030308 69
    0x1080c0741c072055013000c1482c178180e20345001d41107810940e210143d00007110150041c07100c2c20b85d801030807242e036a07200c500c0203502e85960388074942c02d05400010000390214046400c42c441d02c81005594500b04c444201c80e4000c109069000003000541214000e95021503c020045040140c0f22140450442e20004103100075911117840c000605220704002c203600001c40c6815111042541c20702030307403044806c95003001d400c100701354070462140070f0141a00010007c0c0c90700700d04010085404a8440600f0340d8031160708000c0001801003040800701e401045007000c0d08421401c016a110b05e402ea0b6844444100070400e05030204903d480c0030070401034486a02e0308440c0b003e403581c031215490100c421481140000200189541b01d0103c0c01c400d1380300f48200c2840e80107909183e01443c1c3c03203040ca1071168000e80c42c04c840c1c10b13103400c1c004144603000300300f0444050700308140c0600f14138805034844080e400c0000780050340522400c9840d01c0e9541e900107000500400c50a401496265080040217010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 471857589 1250 471856339 471856381
    0x603060c0c0703060906020d060b03010815011d04060906061401030f1107020d151d01200f0c1c0c02090106050708070803060d140c0a0803040821040306020d0203 71
    0xc04001580c800407010851000303c03500440700040799540350600c0c0010788910003005c1001803411341d001c20307000e401001860596610000312404900c01d02e00003801e1160030b0055240760b0164400003200031441070601d9078403510440000c40d2507032055840c0f006841280e00152550200843c4098040d61b140c03003100042111410148008a2080d0090380c90344503010019000301e4460b0300800500036030034804520204903010421050b0881d099540c00c07403448600c207d01d035500340301e0601ca00300030526442c05004800030f1200e1810007141106801580300c04080b4009006402140e440800c9007a400210307401c403a110312190b1980352040010540050b000001405010b002c0f8030045510802510000ca0b404200d0603601d40b070f042d001484440500d02c00400074642803400050300000440e0035071040209551001c409911140740e076803240640e0041340c00b6640a010312501c0e64690a2084200203109480b15140989989400e170583e4005981042801c1d000014000d403182081c0180364955 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 471858839 1250 471857589 471857611
    0x15080c0604030c050d05120a03050604060b21150d08030412090b070303090c031b090b010e010206061e0607080a0906260c22180e03121005100305060306 67
    0x1400c0d0f80d5100c055090354000c4602800c01100800c080090030403002542c81000c11445840f4107000f14014040c2100301c1310729000300d041240c001500c021038000d498868103825141803028440000082d0f500000400c80041e41540903031000b410344980a6250720640940322607a900d10b07050400c080446040301c607601c10480d454500700109005031090740c410329450320740412080d1260921040c004075175000030300024041045150168500b00022048442041050200018810054950b44c42080c00c1c14003680182d0001050381c6403036924145449a0240e052480903640c401041042d0000003045940c060002210305115030003440d4140140811302d032141450100c095500101d8441c600c048004804400c0400c5502c520401070314032580c281a450301c10080e4160300903104030a548144250441100c40d19a100700c805c0c042e0ba943d00d04640002c52802540c24184d0002e1800100a00480210403402040301c0d0340b0700c620074820701182e50b03010440e030400c401014101035000d0480c000380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 471860089 1250 471858839 471858847
    0x609120601091515050c070b0c0a0c170c011b06180309093c050901020702090a060e011802041d2512020d0f06090204030302150c0720030115080c06 65
    0x414500c40d805007144c407185041a200c41266201030f151980d540c00c110045000810038640f00500004d043c0c2d40c01703001d605645415075848502e5004050b1a41400382650040c03030043e1929408ac1181801c80480c0103d0248000e140381c4400080b15144c4541c1c6614440c1e8080c80f0701031560128006020705002201089008080c0310760740c40b5100f003002c4599640784015940100c3e2503407052800c800b180991014003681c90805001c038000d501c0150101d11901c44580850300b03196041c8141c0003581c60607103800c8016401c0201e05095160088080d2680d55020000440c0c00c00c4401e0041da08031103950f25818460a00b00003211941d0a00c0001c0c60070f9511140d10f11100b25070102d1526202c48185900503603d81880d5031880251060071043d010041c20643e000414900325401442207900036400c0e2801c510b4845a21180004c044e40d0011a041050001d80c0c0481c0c404441c00101b04289000e01600daa20400441d00b512944034007070580485401080004042c140290076043c0c1048482c90303d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 471861339 1250 471860089 471860099
    0xb010803220605030609070302120c1903110315030f0a0606050a0e040308070807030612080d0c0903030c02100c0f06050601090b09090a052a0a030c030209090a0b06091206010915 78
    0x4613000081040c0c1c0f16502e5031000c81c00d043c4c0a03074120355080c1001300d0701024038901140c170b412080d800749140c1c0e034002280d6020501e00038400d01c035000603941d000890a1a58846800c6111040000282117925000c3c1e28151907182000300701c0c20b0317180da10402010451034640702c200f02004107035600244291050000b00000282d02c404504c0e8051503d081120b0283c40b1480118000c2101d60851265a264000e41605010502026040d6000e0311041030100c040e170080221000130311440000c012a401c80c0c40d4400502e01030100c402401428034000e0100c9485455070045c0302a0031000340c0b0402c0d9581c0a1102659200320000060400707100500d19000d00c000202d100390600504d05e5400342e03a60f6021940c144501d11000c055000640c0d003c400c1c803105c182c00f03c886a8010303c2c4840100746000c00b60300c55203029000f61400d030140105280c00c01d61320304003148041c22084055030391003039003004507102035521064180e1f403400348580100700e1581400d00c0340701182e02c040c0e10045203140103581000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 471862589 1250 471861339 471861347
    0x901031203050a0b060a0c02030c1c030f030f0f0b09092415120d09050d030801060f09080d05090414161209020607110306060a0f090b0d0b0108032206 66
    0x50300d0940360010711a0f6910100100404502604980c00600003900302d610030b83c0154204403240c000c4043e00e035a6500c1e1410000c03205160104029040d1001c0c080e240428040c036601803143e000c070309001c0b80c10b481001e4220704984488041300e8079a961803071102c0e000d040041989902541ca4001040c0b111500103407111003404122110464080040001e0744000212a0041d05030f00003804900d0b05145e060036030f0761940700c008024000100c0c0d03510001203a1401e107401d1000180c05844281e043c1e405c0400454035881e40307922000c1804448500001c524008010781c8190900f1540d41c40e454520000800c03060b540c0c030807042740708043c0d1b0710240b2000c0200c1e50503040145095040ac04043c514604140001d08a10000a5030007078010500009200e0034070003009074041d040f01940c030260f441034100b0185440310700071108070041a00c0c042c0f0001c6180d601c01c1195000080c0720224070020f0350340d01e10250310260400f5049030004100004000c1064400c1100700c0081500c00101c1d509000c8010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 471863839 1250 471862589 471862613
    0x30604020901090801020708091c0b042003100501090c0c1a13060905150105040516030c020c04051602070b210c0408060901140a18020906060c030d1505090103 70
    0x520440d400500440640e0080042600400d0714400941d103510903820000c0160f04070908160103140c482400412031417448440c12011948800308110303507104e90300e07504000610118600041142d40c607118159560801c2458011025404049841d40c107203482030056800700080e800a202d80c03060041d000a0000e803007602c031003d0b8011600c0b140e0b520391540d080e000304002c4c03003d402c440c513003002c2200b44000880c2d0480318552040d503948031640e80f142800308542d42103821031105a100303a840d030351051080d005212813003114812125400a42c000042c00c0703a034103039040d54041102c107007104106901408608014882500c0f42410150842c2c0344008100e003200c0001c1c68140c1d40c03c00240c0304200719050350007400d85841114054030709180d01c18024600f401940b8080c00c00c8100086035000c950141c2003141c96031103903640043c10319600740241c4100107070841d5401881408004154001040501200901c095012800c802d55143c5048084120340000c0e00070340041c0d00600206140f02041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 471865089 1250 471863839 471863851
    0x50a020f01030e030d0203280e190b0a050c0d0c05040801060b0c030708090d06020a050a02101505060c0c042d0c080112021206100603060504050f180304091503060e010c0503 76
    0x1507603966a0030103429030402c42d021070292020341880102e2180023158416071240c1d2060044072074680c491548109201c120713410040000710110f0014200000707a8100301c3d0000480f900250801c841c810740351060b01c0c0403da0701c0300004c00c0840d00704101d00c0c09002d6100240a509101c41c0b500710300209240d00c81c8191103010300789000c0000c402e00542c035542601c0f10625000b01d021529040c0d4084020010303403040d00b800005102d205039007840c07400c80c1e204020201103814030803001146800107210b05a080400c54104a0103034032090700c44d80d11180108141c107103d481400b0a0300c1c040c1d8241030000660441102d0a413498480c850040d6038200d114141515010340f000303001c0080318800140206464040c0000c50b000f2101800720540a80e0308841c10740321507860074082c0e651035105120480304e041f20034a08100d025000b04901d011031a0a802100d900f90f000d0382d146c5a103c0d0b00c01d4081d1000007801e900c088907140000c1052007e18461100c3c2110000300a004010101c1d00040083c00b000e4a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 471866339 1250 471865089 471865091
    0xc0708070c03020603070f12110901030c02030f0d0902210c1203070204060e0901111801210e070608070c0c060e0d050f0d0e01090f030807020a09020304050a020f01030e030d 76
    0x40003080c010a18049401075034010103045c0d80e0703e46004010604400c0214103808608a03d8640741030100e5405018a401d00040109081c041c03840011400f070100c2e00d000350154002000010f0302404003000034401c402e0310040c0411400c0070340c41404001c3d22801c000c0702c10340c0281004409021408a404428484c0071590742510300355402c80e00f070070745c8182c80c0001d5200340752210016188044001003845003804400800284281c0810002d1520a03641c8030303e010141490140820360040304140d50318001814034400140c0c4400d920422101c0c5201c131815036610041041100c1c17a4003003c8613510821518102040070b9440d0781d201c010281a029040600c904c02c0d107099000e03250701003405041034018007107815003031945044030340742d01c0948012000a2024910b50003a540100da0800440e0b2002070351000c55499602c0d683c0540e000020100d81c0601d51050001d400700c0540050340c020341c06407025000c0c403041e41c41040000d800c40b0070128149414010010600c020110941e4440700844e10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 471867589 1250 471866339 471866347
    0x806010e06061c2306030a051e070305070b070b1005060a0f030e0304121401020415080a090b09010c0806030f07030b0a020c010504081b010204050d030518031014010e0c0708 76
    0x84180004100d00000b000d80d00d080720300980451001c4d030100700d6640c4010100c055407130b0030045c1501c92030141005400d96001610140200400e0f100b50448280ea80b416500920b0300e0b0340d626030a2007410340c095a515440841d40e641404201030a545c1c2210421400305c01487c900350208000b030144006600910161505668800c0e0007600300c0c201e64012201900d85e01d03612000c018400340b5890b60700f40e60561550b5000290640d0510848040e00c0c0d000c040d081540c0c11a49048800030001816815015150305203c8001a101400305004e07103140700c00403030b50041c402001000d541c40101800d100303602a01c1a040414070224202060b641c00c8140a10f032a5956555207001c0e101d400c0d601c1405602c2c10041000307103e01200035140c0724200142191040c18021140c034241d0089000f0503500000301015800064000e000402010300354003c00c0520150900009040c441d1352010000d81030348034910400c2d800e881030001805840c0c480000c007441c0c1030107000302c540303401600c41c0103100101c001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 471868839 1250 471867589 471867607
    0x605011d0a090e030a0201110703021c09080321061e06070807050709020301080d03050f070e012d110102070c050f0a0909030c060b031519060503010501030602040305070806010e0606 80
    0x241d03406000e800381d16410700c514903240003c1e542d0382d4000d000070401540303045840c0c2d6903a02882c0848034a2600b5a000380141c07480c60604160380d50a01034807909009034140300155901c01170010306190000119002d0090722000c100c190700800041c1800d2099421501000742054089509512180d050f146161142c0451522906612628802401902c902280011104a02d0b0001d50580faa500d0644050212200003079056600c15907045480510b40b1001620071841070541000b2190b052400410343d038104200d401c0c28400100709182c40e2100141000c00d80b58210450041000c0604021858841c0307a44a0100d400102e0064600c00d200180001c070305983c80c1007842025099141003084280311b02d00c1e014141000354801120540d00300f0711100c3c802c0c580441c5003094008150011170140c1d0f50f181c03044034885904182c640034540e64402c00b0038a520244140c90107144210f60040e40d943c2182000743c80d2092950100d459a80084014040c01d040c0c682c941d41c103d00250340b0580c50300440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 471870089 1250 471868839 471868849
    0x231806030a03111e010b042a0c0206220302030f0f100c032405150909040209180d050d14010b071212020d05040606060f02030a1b1407180605011d 64
    0x164007200803010212043c4c280d24410350201400020440c1c0c00c0003540d1305044c5102c0c410f9241c80290309031648800100f21000e000d0902c10311200e1005204615104000c2c0d011944500f401254103546151a82c0c24011828104080034401d80040000e100310322180d24882e0741c800c807140d1801c08054592249100c0c0c0c9009400080440650403828041e4900d00303c0802c4403e83c5034400d0354072071851b80c00b061080e29200422150f004c0c0028002907820354587e02400203213640608fc100c00703903110100010544034203004850100300c25599044e61006566240c80030349091511001006921100401c181e019010031542015404950300100c5085280c05840345503001c040c124416000154402181c0b0003075001a00c6503200f035108028103501c0344003c581c4000100a2070340036910410181941034000c6174000b8080341c1c0c403546030481402594861300201c407a0550b504640e40008802e018202ca44c00c034040020601c010200841440c0200080400c10041c52180b85404149440039003611b403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 471871339 1250 471870089 471870103
    0x1314060904060602060a0c03151e0302030d0906020f0d08041520091f020705010e030f0304080a0b13030504060804230304090605040915020a09231806030a0311 70
    0x28800c0210b01e550b0040a500c4600468950300c174903140c00c5121401c140644550084520f03600e540f10403850914001c1280400c1c0210344510440c25100001300580c4c08000c2d840e203140c1c2e2542c07201102850010040d14082c0100305030b9031982c00c94a0300d20095035015110319803168102c1894001ca1010381030181c002d200000d00315114420884601010340d4421000b40414070042d1101c5400b0800c0f08854403845883c011a04016040740100704560b44c800c401102d180707500142550300e0024400d007a40e01d551f102c0d6210429940240303e8a60034000994540c1d5840450794001101012a90760000c0c03403031096001c0e50303052100f600082030500541942040c104403d1061850a0b21221907406540340c006214841c4218102507003c511424140507041d88507910040c6118220410550f4101075089109600104801580006040100200c1c88036410076032802c4119009640c00c00c4c0450040f0284040c461100b0710001e2007407a0328009103940c0400d8042c50b004100055a21801d820110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 471872589 1250 471871339 471871357
    0x14040b0c090118140916020d03050603030405090406090c0b07030c06050720070f080c0a15030b060414090703020f030403030c09080a0308100e010305030a0503070306050409120e0105131406 83
    0x43c1d102400314080466040d5000302c490304480d42607440d603c1d900c2448241440c0300f20000141c20003001d140a150080e017000350000c400909490400d62a040400c5112104480c10b03120140c0700d0080ca814821007041c40c802a040c1d01074003038a411040c4d100a01403520010000b44502c2e90381c4d000031111446142c80c101043c0150488000c5140303445101503032400b03a4084d488605201100028850000054841c1d81e2078015160300903a51070551401d074034480c222201800d050721102e013407007590384142c0108060050000741102d0702c031044042c403d40d07841c001c00c46c6007494410098035502c1d035030b88800e1307990255151402040c65120100b084a180384264071170141481850841010503030000650b6100ea000f41581b440071641e52110440700810138840501690000c10014009912420003150310081074180800d2643d42d0342c0c042001c440003000145c1d249408914410b030030b5075106c640b00f00404d0003481d00d0360600d031102c01c031444009582d00c14103808610700c4035102003a0311414240e440102c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 471873839 1250 471872589 471872627
    0xf0809130f0e010509060702071703070519060b1503040b090c040f1413021c0614240a0515070515070207030302061f06050901050d06080d020114040b0c0901 69
    0xe0260400c4041c0c0002c0100c2001542000c0c0012014080020254819032040d8002c10360780b13181040345c1d010780c01844100c107558001009602e011030390401005600c87ca102100403400040c0c1e003040d00403200d908021070f103d440c1c0d80041680d202032602c2900d070840c2c1c11150713088150f25a41c0009290440140d49607402900303120100103840d01030740c0003043d005001c1507641019a02c0141c040c08032400c02078000d41c00b00504074010b4299a00545e041c0005100304800030340345000c0341c1e0b80c0c2c1801d2004ca80c0d81180012010203450141c0703124802c0070b0b00160a40c3c40042ca6820440000c0c2c0c060100d219101540401065072002e0110400030301491000c90750018016040c0705c0d200035142d00f0300d4001603000d481500c000c28111550451403521890700c4070341040d0b02c01e090003c1121a5440202c802d4100700b82403041d40049100742c1304000c010b002810003000944801e10019003524082c44100460200d40d00411010403248002c00b07034800c1e410700d5000c0ea522001c0005039032008110390010194 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 471875089 1250 471873839 471873851
    0x405060c0c030114101d0c07020a0e040f060f0b010e0123030f040c1a0d0c091806030b07020c03100f200301080601090b0d02011409100e09070c0f080913 67
    0x840724102255018058004c601640103071100000b0824983e8405014566000000001d1f03140038040007402001e44024111200c00761740324650f0070007100a8406a92400303a42d0700400800600307100d09200090011002c2c0100c001c12000a86030000350341e840c2e0706001c0c01c4008001c070003251507681010403420f021166164140020b0490301c6401c00c6a0880751039041000218401c03406004249900c100d4200031071402d44900312030409003c0360b82890080c07008000317000c698010041d04117107012100c0c8400103840d5285090801020501500900540d0480d4454001c640c801280a5020780f040c404086036125a24107a48000c0891096001c100d81c00c441564070503000c8040214101d594000c200e03445030f62904031074801c4408901aa42c7d000400550034001540100500d00c49065081c0c501c60800080d81d000c90003d000000a4000142e5145100000c5160940d03420b5044a45460109070620b1940d0b24064070b403442d4032014042c55400314140c2803541d20701c100008010b00d402800d000e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 471876339 1250 471875089 471875111
    0xc020f01021c090311031501031106160305030708180304051512160f0e0a180e010c2a17030903040b0714010c1404090905010e0604050f0609070b0405060c0c0301 71
    0xc81c021a02084804090317607a045020791030001108900e1078000200d5202c540d103544e48603840d601e0200c4042c1d800c1001030104403540c80e031010009081a000780c45650b03492078200e40003860180700a1000c03c8059452148074030911000041e241a50401c0c0c070600a80c09204070070780d240740644800e2000e01c0b242d80082189501070182140c0300071000d80c036442c94542401e0b0065561203600140c890700845003600030014040c2d02e41d0030b600d0110006070009122412038101609454003140e00c407020a080384141c00ca00d201c9080c80c0002c4042c4684180b1344189169614080034a082e200d012940e0004000720303000e03c400344101e40c014402d2241150361128186802401020900301561082d464804400621409140c9410480e408194458a8035041140800040410f104259003540d65a105240170800c20044140918010b0005081403803504c4546842c1c4200103242c0d140c180c002030740400c07101300d50009940566104441c21600c2c1c400c510025032414010100c142d5041d0b08007115110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 471877589 1250 471876339 471876347
    0xe0c100306081b09070905031002070f050105010303110d0e03030d02030601090803070f11010f0905060d0f0504150b011e0c17120a150609030f02010509030a05010209030115060c020f01021c 83
    0x7007141070316413004582e9126002c2e501d80d02c40d40306113905504061030103841100039038002c100f42481000603280365029501c94508486098100320003040c0c00c4c0384042c2104004000200b10b022151034121440ca402101094490082c662400c0101e074012012805980c018403002d8081c0c100d81d41100e4840782d0b01d00742a44444514041540d50b88040600808103520440c00705010202a80312840d080780342c401481b52a40c440d10f100b600e0190380d45003003a00f102c001d0140074000c0d4010030402c441c411070b81d1180703022030721030412580c180840c11a07a825200411100a03044130300e5410704c0c424102440c1010500e40000a078030f46106080022183c081000c040300c468000c025141d02042407245c40304000a0314405801408c0100d0007030703001000000d11300280c0c081464410314007541000610000301e4038143c40e40030308440303d9402040c50b0745113040921803e14505225214001428504031002d44504002000a0700841c01d0b10003c007100d90081101c2195980520a81a030090003184014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 471878839 1250 471877589 471877633
    0x90a0e0d020c0a12030206190f02040803090a050301020304021309030c080a03020c0714060d0f0209030316060c091a07230a03181512110a0c150e0c10030608 69
    0x2500c100750101004c034000c96072600c0401d01030f601d50000d00e003685070a05540c040004d521113008407591a020658612403050028000800e5044011501c80c800d00042003040c00c0c89402072406a8414405c0001582d10383c00036200c64400084000b03100080341c1803c5540e646005009000d09900003143d0400b6980350307008100d14803024060f111016111404041d50080c0080d1903130744994103001c401c020b10f03999444111b0910a003c0014685110746021174155007004008404500880d9088414410309008406c0800383c1840c003860950b042c180322000948201c118211a40c801080c80410410701e9044000340e180d290b003400150b0040c041c982075a903604207804400003501d040a043c4501003c40c903190903601d8130140c1d28210350300d403070040b900c03800b03010209520103031504003210102c200c2d50010030344940c0c60703600c10300402c42c58100940000e40400020400a1406400c000c50b5000850000c92543c005c0b10b800302c22203a0418114050f001c0350b00145404d000b0403202c1602d07640750709205 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 471880089 1250 471878839 471878863
    0x20604230a03050d0e06010605030612070f090606020f1609020f07170c120304120806030a0602040e01060806013002070501051501020f150f041a101e05030c090a0e0d02 74
    0x18005ca503a010340141d03d4040a105081c00300e0014004070740640342c1030401074403003075004080f00d21540d503c200300d281d8406164011050a036441c00180700c442e6051020449414001c8000c2c810700603423a00441030b0240c0c0348101c01d0b029502203950508000094116070b14a500500b01c0210040290640c0010740d100c6100c49820f0702c0340c1401586808002c0082c1d910a542201c0c11010000c0c1010007901d00c0c06004000a50501402d000741c000580e452020340003070141d11b01c04044640c10404054400000030b482d59041c03200780c40311003186403036420a0f03512400c40c5540514076800e546040a020b03014081008005509007401c01c02c102d000d0500107480c1d648240e08540200007400310881c2c540340000030707068031550135800280d000844140300c1600705124406c28007680112010001d90b50344241d400c4914524804010092102c4007400c074514003149402e450100b500d02000079035036240c0c003031200f401020500b0005900301c11550150400031801d400352243c0701d11004000703480305c80394195 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 471881339 1250 471880089 471880091
    0x70812100611070f0312050912070501020c0a05030303160207080a030302121819030c0804060807022e050c070215120c040312030209040e01060b04030303050c0a020604230a03050d 79
    0x4000000b481c005848000c403940e200300e01c0781c2c95095071181000d00031a42801020301c40c08014085040e1100f20000340380b07031640d40107004200d0401c40028140011900802e1050300d04070340c1841590f402108607500a40c6000700c00100146299043c1d041c0034a5038030512943c050b081c121418103801d0780046c0701c078400c1100c50503100d072b4540f060035041170300d00000c410003a4020b407100f5031880f0f43d01c0d410314031260003820704882e091055910405581d00c1038100c100014074680600034011380401150004c0c6103894003c212050094110700700d21103800c6040c01c0003545070f001061884c01407004641c810340d00074180d8440054064020000d9a00008140c140304081d440001e0030b841d002c109071001c1d43d5000c40c6103e507140441808a01a4109807505a4030503680d0b40180c030f052009105490040125548450315213155080203022204024005541514204090444d296011a82c00e41c0a03500a003541d08400726004105004038481c5d1030b158261050180000c00e0503040000b03408020301c0000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 471882589 1250 471881339 471881357
    0x106050d06090c0507021e090a1b0309110f0d05060906060a06020703030e0d03031518110c0c010f090e0f0105040605040c0e04020331020414090606060708121006 71
    0x4038040483e60b048641e240000c0341400540014541203000600c90b0300200304a22101d0400d900041c070402055803845126680c0c1e40506038030011210b1141860070007402c040006091503101c0303094844840c406244a16010030140034280c1d5600d40d4816015042170843d820391500c10300c1035030343d1a020340782a0301c0b86500c0d4100154091000898001380c99040e42c80c61020781a42051240e8010180380403800d140c0c46034035103820f410700d00301c0c414010400c10030700c10b0170904d800b20104116406c80c0301d01c0102c0b400410105440140005000801c28828600620300d8540004102d40d0320b01980c000b50068180c0d40140130184140c10019030580c1c00460b010000c02d1b0b6a1401c00044684002d00503000ca14401804002442c00342d020b9035228428690311816600f5024121041c0f243c4104846440031001d4822019410a88103c18002c0d100c500c40c0c4055082100d001c55480700003d101a100e1140025014100855441980c0d040060f181c80c1200c1c0f0305240603110a010020300a420018036162 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 471883839 1250 471882589 471882599
    0x6180f06040507061d030a0f0b0a11190c050703060e0d050408060a0504020a270b10080a090813120b0a0b010e0f0303071221050105060a0e010c0b0106050d06 69
    0x452914091030b4040001c100591030075070b082c1c0303115030046601c840c0481001a003010075103003440712901d8030b80b040c00180c80059580c601469104009400d28180718902120030b100c5039650740071104000140c04c18045484501d180c01c541c45018901c0c01050307405442d80020400c0b440b41c20090b01d4164175416070707403049468841102c0303034021403003540b96941c000e01c0400c0c0c0e101130320b6011503009400030303009000098440403051070b0038080d4030128003c030b01c2ca043c140015444c980308005c255003044503c05a100c00480004000c00d00190880d00d09540c1d81001404100070750081326801d01800c0602c00c041e5940d100d50b081145a0b0301c0d0240c418075104800181088110300c00c40300440c5050b1203104002d00c41000748207840621402050b011f2204229950206800b0244003880840607070314110700c0c00609001070311b90b00d0b05032005503075282800f005018903501d4070141c9034101140e29240c0280280100122801034640c00041d2108980000104521303a00030020240c8842900082c002995a6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 471885089 1250 471883839 471883843
    0x1031a1504031203020901080601030b0109030b160914030a15060306110408010b04062d1a04080d02030c0712080712030c030b0d020307060f141603030506030c0a03060f0e06180f 78
    0x2031286c1d400601d40380700040e242d41c000e5014400d03030003043c0751090318a5217903031310900000c40550307818680c0f03039104504440c51540044100c0203040d81a00c0b400c40104681c0100f0750703a4160040041519044151a042c40d0150b58004001560070000c1880b01603c0d515250352664058010700b09523500b007114001c2d481c1031500030310040718120002842d5040c01201c0d0b4226455006508030700b6004821000102c1c440003581c190020050b4544241e078803860301102619080300f964155056420a104941c000400810705a0403580006040c644100151400e06210710520074010210210181e8811000e0343c140d001402c8400d0075202009041584000c00141000040000758154400c10303085c44890300c1000c59101c0414141000b20b85c2c800c4511002c83c0e0343d04203006141c0554030070b091410500d9410b00807d50404001e030040c1002c0744d00c0001145041c4240d00003d400c1e0b64440c80e43c1900c24025070700c400b146014150940e0b06508181e4080b40c0a41d109480382c1d0800e10619004200d58280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 471886339 1250 471885089 471885097
    0x22020a540b0d26310303120506180405010f18080906090d05250906080a061505031009060b01030c051204030e0a0617090f0a0201031a150403120302 65
    0x100400158945905581e0307158041603800c0c0307004402c0a564191010300c3e54400190070000300c0e08540c00e01101e510f21900b29118400c02210003040c540607001c00c0800d0b082060040e03003140c9044080b8040d5241004604200300398525040d0200d896400c00040c0801075103c8202c00e01c41c60701c03d00c0701701754045080c0305075000d440028207032160400c125511443c0c04130013805105d0000d0700140c040403454a44500300300d18000c01c101201407180d00d20101c1c009070703c075134809007807a0801008030f541400c50303255440e00312400c0104100d9651800003019080024204000c1c40d000301103031058420100340c0005050740d03481c115200b03424614007401d83c2d03019000b10907100000d5a1501c0c1414025100b66145902c09402034082c41070759411101c01340c81d001c2020b000303003455854412525942681d100f43c02c0d9401800d50b4001e40013400144524240400d06a403000d409190100f1250802e01140c0603440c81c011520394400320308031022484500070000390007180e000722540d041621440d5803d9040e481 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 471887589 1250 471886339 471886361
    0x50109020c070b070c08070321021b01210c030903090b040509070513030218061207030c050d050705130903020f060408030f22060522020a54 62
    0x1002406205810308a406441a180076035a07040801d582c6e00751403410311885030000e44640e01015181c6140b00318a2010341800c0c8035500c018148d61924204240750450b04940d800d0400c403d010542401106c04070f40300300c070003162240401110108420241c020152130008802150341c1d12800901c5140e40301c1584c1c1100d03000380402c10342d5528043c08a0302c903480940003803001010290003001581728503207000c040040c464281d50a038107140f420050f40340030144d100011980500070510004011038844d2080350380545800307607004081d01d400c0b0701b07102d151740140e070300040c1c000c6003410030b02c0c0235800501c4200d01075025184c0c2040203010541e21800d0484001d40905401c101003040a00100762255002c00010604000d1005041d07240c0300074500075209a41954958061040c40b64030440d5941110103000220304540d4081e501244a5a407944101400c02d0b02180c4d40c01c0648851407a0701106401c078004010f50b8500602c0041200d03a405120291061401401700b080003026209081c6a51 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 471888839 1250 471887589 471887593
    0x60112110a030209030f010207110112052502010605030f031e0322060902041514010504380d0e010506040b01120e1e0a05010b010804211404060e0103050109020c 71
    0x1c003005040d03000c0d502902503144c140c4200056031545200a01c0980b4100703115610760603a80994800041c400f001005102d951685060184565120b001d200c8040010301e003610041403a540c501d05a0060141e40e1010341c00d4018020030b010001008402062042000300d2010b040d05650b0341d8000040c0411506500c000c071819101344000212040000500e520615000c0741c0440c89901140c241e44010010510011601c90184040103020686030350710390307081c60100d00301860640f444a01c462074440180342c00503004855070711042c403060940c40141d0303084501c541d03550100c0883c00003002c440041281551034000458120b1829024014230200160754203d120070707101182400520512620665611a4039030007414072604560954842d00400017904483c0c030b950520b6401d6420050125041244003410000040c4928a49a120070303294115509006080c04068404003c540e8469194900100d40003c07000da20441008018034280d800f4040f0b641e0f22100c601c268028160300701c40c50307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 471890089 1250 471888839 471888847
    0x5090109050619060b0a0804140d09050d060e03041d1302130c09050316063c020c0405040609030e090403140904090c03060504030f1110020a020c041406011211 70
    0x3070020f041c8034401203104800500669210603560403948152200d0700417406101c2000148010110070110050300380d0084c00b075100707040700c00800212940c0100d03442112464205403d000c000d40c814000d1894220459035184c0e203075544608250000e400c81c24168104034001400b40014602d0030070055409001c1c0281420440c00d440050001c64030441c0c10040361020014a66508000105c00d0944180d04e4100142c04c041006018403602040111011200700c00300c1c441c682c4401940c1000344200803224200c50002004904094140003103076841740c186002e11082c003105602000c0214031a0700c4203203507103444000303022071810308880c05404517803d42c0c041c40e15401c01200500d4000001400003851011550b62441c0c500902c0d04150782c0190303200200810035803c0514104113040508042c20b5030408080e8803a44d070465103002482e6540c02059850f50305008201c10b42160700c0082050000e0184421040000182240c0f4980050746800002650bd040ca1044a54060701071900701c0c60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 471891339 1250 471890089 471890101
    0x15270309030606101101110a02070906150c0201051c060e0f040506150d0b0a060801151212050f2206030c0c061116050705030d030b090403140405040606090801050901090506 76
    0xa10b4018140c603014009200d42058a07040c0a105159031f803079084008036201c1d0a0407400902c1c10301c0c250484a8000d152107418411448043c0c4184843c0281d4a0001e42924081c030049440740512480940f003061868143c0c00d40c3c19094010105440c8046070581c4241d81b500c03000024468113840103005c035000a000306401e9403019030480495400035025044121080c0d5440320700d03690840761840c545a6815050204180c00e00404c101c140c0c0c000306d10503c0c1c50402460601124001d00c00812010b00c1d40101072501c0c0c000c005031030f0154a050902515991858445407040c1c10740c0040c4034180306c24050218050f8028401c003000d5020944d1044e07403003c8281d0b1000014141e99050965041050003518004807040413071140c6d4900c02c4015194040c50a41070510381000300201809250401103e00e01c1c1d51112190b20341d1080d014038007034580301000c240742c440750f106603002241c0007402c11030b0100390180c01c0314202e0112000800200030b150b0b19606820b00f280e0580b600204107810600104034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 471892589 1250 471891339 471891349
    0x103150b090d08040f1d0105041b081902040b1e160f0c080609030d05061816120f0603020a0b03040b01180b0a1401121103070c030215270309030606 65
    0x806441186031524054079881800305d54a15a4000a000c241d280c003c400e4003c0c0e00703003105005040503601440300c50100002e081808200c0c3c02e04c0d074108400e18000550094480d030b6026010114220b00310750b20341d141d180303d11a99020203082822048040000e060303040c0d82804507401c5107001040900e200d102503844104204e041041503814003507010010800c20024480c031409804440f00a5680f00140342006007510b0300100821301c1080c08084d200a1110351442440d4421031015140a910f52202001e5881c0c00103039039030113001864100607881c0c0082caa8060000d0720f00031948261440d0740d5044240c56031004507401000c90a0400041200151105403584003841c0c184012840c45c0e03004010070f02c2004251f00416a403040d01c00e41a05c1c550b0848211602e4141e4108248040ea10559441d00c0034400500000104074502c10071b201854424046064002d09551800c203160614808600c2510304103501d01e4150100b07030394a10302d1030b500001250026035000d005009150b8880d02081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 471893839 1250 471892589 471892609
    0x3020123060d210923031b121501080c0f130b0303040314060a0c050a080601080c040504020d05161d0f13020c060f1303090b09010c1703060103150b09 66
    0x203580d5880c211801044104002c0390390103d01860303858036503c80c5402d1410000c1d903555074408003c0d002d50000c031001c0b038401040390341614401c00c2c0001030310000c00c0003040c5200d140c041c04415900400c0c00003032840c03501510721812207100a0466242c216000108081200c03025802507009500ba1a00c0500c01151b0304038101041008090300d003010359940b1540d8102600070071150440c0c2001c0200125549588180306120b041440d0490800032600c10150074118080c050b2410b204103400014454040c0c0000c4501908015000355181c1900205050150505403010002c0c19483d00d10350b11510b1080104a07918820140c11005003000c0f8020301000c0d011204256030030000c00c0020300031403603503030000b001039500a8005103107610307000d40b420b1001003010f0041c0e0104003038800d00e44042035000003c202a9004280c4050340c0b181d404006035190a50000d0043c0078410500d01c14801d0110748001d1440380c0c1c0281c90a0046412203243c0c41d448a00c03a02a00907100001c2c000ba000c103050220080c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 471895089 1250 471893839 471893843
    0xc0a090903090816030b070302030601050d0506150703120b0114070b070e1507020103061e050103051302030601060f080108150c030901060504021c060909050c01050c150f0403020123060d 82
    0x28000d03d0700c5254031410800307440030034020882c0ca00020810040b00c2c48419501480b54a4118258140140001e03c0c6202e880072120b100d544420100b589030b5610684554034051091042e5543d425900c0e010b45580740c2201c802080c5443e260741e01ca600d5000b03109200f060208400b0a61416021f680c50fa40180340c0907260340108a800c04400d44240c03242ca26103014009411301541e00c5074603e10006061307490507040382000e8001005001c0c40d0000c0540d006090b14000d09000c02c00d80e0341e4084000a20528600c0a075244c481c01d0000288141c011500d80f40311515541c0d480c1d2140e0301c40900b5546e48200c1c6081041c01c2c01e40500044501080348055a0011414000850b05581e90800501641c001148a004100e080303008441c0e54030b0980b1440c001015414000d2015010f69142c3c01e48840030250f1190601c00c0000b0300d044aa441030103c0f035404034120480c00e12038244040703509800201114110095031800c0501c0004030b1008407460020f0342400c03596442695103c0601141d10030003402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 471896339 1250 471895089 471895097
    0x3070903020d0804030510090507170c041103010806160509040908160506150d0f060c0c0c0801021209011517070803030f150a0e010b0304020a150e01030b01020c0a090903 75
    0x403005948580d00010014000c5901c181c0392811810034a0a00004200296031280750422910000c0c80101d600b030300f107e1807150016001c104401542e403c5c440c40f003000139440780c1741c0b40d140305c0d45821440140d4181c07200802211355958483c1c0030f070141ca81c210b0890310b012503c10300403000b03a403034a82c00c0b140901744218801c0781010070b841036400c20700342c0d0000c084401d60865030410011640340c111615040c2070481e10f075000c1051540390720918072500c0101070708441e1605d06070a0b40c01d020300c20121040d83c2c4000c0d014030480c2e07500c4041d4003d42141c041200d05841e20300201c0c1d07581c0014003030f050541c01c01e02030a00c006440d00000c0d00d8809003040040c2304a010b13640f00026030101c00c1c00610720403030030124014034500d45000588202410010081e1003282d0750802400080300d203d8016064548a2005544e00d0b161400018601e039010f620050221025440c281315080c1c0c8206651412a0300b80c03024060b40e4040740040e43c0b070389050f10b0710b41c3c2c0184103624200b06011494010081060081c20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 471897589 1250 471896339 471896357
    0x1150e06010825050d090c1e060503040605060d150c0905010504050f0906040f0c02010605030f0d0f0c0302071a0d14090a03030203100306090507170106050d02060c1f0e0c0301020903120307 83
    0x68905c1036070100203094541e01088402008400e011401e111001c24008064504507820305001400b01e00000c0e10240100c0c0e035400002d03600f9161450310142060b0455405410142003074180f030040c04c010002480003c8002c000010036501070707000d89003034420041c41440312000603000e10425040041c900f43c2e00603103803144002201e030742d0710034800d691300f496001052450405003414a410039604450004d1fa000300c0e5041071656100104001200c1945080f0b003551040d402c04a280c60340e643c11400600700c96010f040c000c0d181900050415007844c29091040d4010b412500107401000c44e00c04929401040b88034000910a6000b16400003010841801e03980d102d07292002140c50040742150a584007030b40034803043c403042d0070501c545084000244210703818600403410402c4020340080c0107030000b141c5c112000e103046c4a420310b40c030024101c6202500c82d400c080300140441f0f2a048110303000b0305683c8801c81c2010700803100103590280040c00da151280182c100075034001441c0301e0400460700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 471898839 1250 471897589 471897607
    0x12070813091503060614060313140706030c03200910090305100902150405030c0607021f03020a0f090e040f05190501020d1b0c02011d0301150e0601082505 68
    0x2100d10070350003442e03200c0c4215280c218940442100c0d400c1d08120542c20440007030003c140d4a0000304c0b0350051030342140d400b242c0803d24103246801180c0c0100402400b40410105405505900a11aa0405139014010f01c82c0c000d4182d400060800301110742d50200300f080003601d0422200e0680c1c101e0031460040b030304640e20b03104c803400c2c008540e00e4500307481d8960000c1000d40c6050760b0f8845046030003441c42d519003880d01c5d00103a91900518401c6008980101d0410f0555031201000c1020b016140a006040342032400014000c2d40314614031000706001000c0c00f00c14a114207020016034210084c1c544280d10365407900b40064140440444240c4a40307403540e100c1062480602040c140709100150701c86c0c3e180c0d80c0b200161010410050260694400d4201c6895400701030140000c4e020700308030f01c2c04104480c50200729200200040e4056081800040391100340a07030280854020030441c0e0419110a001181c0f15a4203807940b50300d509411a946128041000c406007502009080c9580390030002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 471900089 1250 471898839 471898841
    0x10212120708060a0e130206090414010f2709080408030703022a01050304031409031501170c06271c060501090203012d03170c0c031207081309 63
    0x1994124000d0030a040c0038900d41c001d401c1c0c941010048448044c05030400340c0070300ba0b40100602808400028445100541d01c40c1e034200e480098029009004400040061f80d1b0303007041c00e2040b185e8803011248009045003680b168003203082074483c0c030344c9202c00c42015030101030058003000340c0d01c15404000004541a08000034005603200340c003c3c201c180080d00c49403c9104011020101d40760591107807242c41e030307440001c40340d01c554182890000960810151230450061105280d01481034040844607250741c030903805e04032450070b07000d00c1911241c801c0c00ca4995481c440001e230449400d1141d4020f15000c2500c4404150390f40d40010302260a000014a44202c03841c26691581c0c14080800c007402814000c0d40d01400696109502c1d6500d4001c600f1407810003140141d0f100020140c1110380000b91114803001590041c810107010001c0c0c01d0750800e194400581c507009407244000081d01800c02003141c040c10f20000b00c90038104500e03601e441c189503120b450549645581c5420105415840d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 471901339 1250 471900089 471900097
    0x220c0801141501091d070e041508010f0b100809010912030e011b090612061211090106020106030f0204091e0501020903010f02030f0105120708030f0310061b11010212 73
    0x25000c2441e2480c01c000402108000100c2c12480c10048812018011110888a041c450b96581d038042d4803141d40d00107040711006050070300030b03034400c2c03c107800c035004812507900c151700b40e0350420b008002c0303c25000c401200721020031840540000d62500054031650003460305686c440941d900100300d080e22942c0e070744030341000d0320034880c0420b5440c1765084101c8c20034030030350311038108421003c11842d08e0303144060058000c501c00c3d1010810300e011200705080395900b00400400b070341036404005016920b0114602c4040180a40c014111013000003222031050181c14216904802d0030003003004240c003400003a044070756055500c8500030f00c0c407a21403e905c0000110b440d00a500040c2c842c0410400c150039140c407030b075144000354014000e01890b6404880c8160445601300c40e003215444400e81058200b4a5076804002a80004180340a088502d400294442c203020b01c0003080c041e4940d8029240e0001c1100300031101d803e48941100045c1072088040c800100500407641c600f9101e010100d1180e03c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 471902589 1250 471901339 471901361
    0xc0d141005011817161511030412081803160e090f0c040e070506040e100f080c210d03060801060605040510080c07021f1403220c0801 59
    0x119010400002880404000541001d203042407080911009030111603c0c2c1c0e0246509941805903140c0501404100590304c504100200c20305440e076a40481490101017250440481c042d0048220882804800c9800366001c0880031545d80015441d0f08445410040d1250702c5000070381000300c056a004c1204013041c958083d5207128072070a00c40014040c1601521461066000101310078400c100801c0d945c012590944000540b405103408080c40c2003500d030701c4a500254001004918555010007461007003c20f811080801c6544d82403812850806100380300494200030582001c5140103080103508140c181072444040c1340d02c034160303810601d40d044036402103540c511041103244003e000e03503c003c204d9800c00b242000c1c68035001c210311104101090080041c000006416030320700358243d44101c0d401030041101566020044002d41ea21958150f0102d184004183c0d40307541c0d06811640f00d60100302201c0001c840da80f001c1c50110401d590112007004000b580441e819070240300c3e12410316 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 471903839 1250 471902589 471902621
    0x4051306030b2d33100e0d06060b07060608070e040822090e0f0d09050d03110601151205220206070f1b080a05060c18031213050603010302030a0303050c0d 68
    0xc00300d40c001c070912014080d0801d80e9005003840c0101c07150303100c01c05c500d5038030910304140282000300f84c00200c200704003150040c80c55180410104181101001800285228040411015865041c8140d5507011842400a000580b000003000070340030001070211a141520a041c2e041841a01c01880a030b1940088010540c1c0720b01103801c511040200582191404020344030500b40020700418003002401114050040d0f0b0b00719000701841020b55000300416113050380d03110358480c8132508500002e614502e0000341054442c680c01e150500c65a80208500343c2c4078450700710302c8000420b5134411504140e0b4456814049100440c2c074505c8900300e4180701d145110b4501006c1e014000714142d19030481c141d598020301310078000440000b10950061f000120b65921500c0781d20140030800900b1448039054000c50070a495040100406404012280c0302c01c010504e403a2802e0080c01e0000f480f02a5255000e0341d1200c0220b402540003d4110540c48045481c1440c0d103e10b503030036114034110244400e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 471905089 1250 471903839 471903871
    0x150c0a030201022d030103060207021201110a03060e09060a1e1a180405061f170d030c05130512121210060809030d0e0705030a03030204051306030b2d 66
    0x40203807400c81086089114403942d03083c180c2e07031134800c260105010041800380e0029080c803c0d56a0b40600c142d800c06d0480c028440942a511038601603000301055001003403c00e8000f1403d0034114000510a141b10f01c0107280903911a1004005000503000700140302107001080400142c1a00600c07284108500d4464886000f000a002e0380310103540b882880702150100b404000362002ca402c0307821034403a41c503000d80c0e013000c0c010085130392486600184403c498a50500c42c04500814a10718024103a10100200c1c1440300007030391580701c0c1c1c060b1468a00c0711481c0904c4246000d841d0301844c2d092a208840305480310380d07100c000d45d90110301c0003480305103001d04004840c0700c2107000030301600542c640b003500c5041040c0c5582d40d83c011424040b03001521049160709508003003011800806c0700400311041500c01d4100030f4000c3d40070b4050280520000030501d51108818010141140c0d8040c00e813482d20780d01c200210f18200d42031050082c003440301c001d001500c3c5c0c0320703009200d0085440348150342e41c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 471906339 1250 471905089 471905107
    0x61e05130f140603040b1302130c020105041101090513110405041e060504020a0c113f030a09060503220c080c010306030510090201020f030313050d05030411150c0a03020102 76
    0x4004628101c1503c00d000810400001410f40e111441e04180000e550f102ca00c00107100040b2414110503007080454548200f0720050fa5054101c2d40c0264002d040c80c17281102c04100440b000e0355180296604000725041403100c00c0302691040b003128203010021810561100c0c00a000c1e40e46c21100d8001e150160020f1445528071031054000a00d01103c00f180303000446c10740a03200302200034020f800c600c11001c042030f40f900d4654110214003203041c01960342141da9001c094280c84214003c031243c0c1000948104c41005c0001100d54488050720703200e0038140f03844400c1b1595407000b04065402e200011100b808030107a0f50899808603c581500c00c9503e091000261404000c83c240718100350522100304042400403484451407614600041410241400141e282c4218895a444140b00000c200009141d007003a403803148500c01d0381900c2da03284d12550100c6460005540280c07400c5411441e80380c01d8600445105082c441741040281490042c50000d07080002071502500540d40015081e44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 471907589 1250 471906339 471906359
    0x24071e050607091410020a050a0b010906060e030c121603031d06070312020a140f090307081c0c1403071b0f0b2a030403060903140301061e05130f 64
    0x162118143c0b0301000380519080d0303414900c1e50405000350190700a62000324449109102801446400c542103415411300340c40c0480c440c200034403c080781a4a400c10101d14280308020000c03841d00010010101d00c01c60710200103003441602500000c0c0d02c99a4201e4200c0001c241418000318004e48401c504903070308042c6034203245481c9002510440c401c00c4140700003a081100480c140244580041e1a458004400e81d00e550080100c4016890f0114071082c1e9000e481c0c005018100303007a0140c1e500300d40c1c0e40b22a90399824070984003150000b501400080501e2058058408150192207a10501c03100036103020f082d58010442030340c2e00c00303800585030190000800c0c076070010020b289450710302d2403401001d12054052010304a501e524003410690b006c0b0b4900a14010a140b0001030b240d031503070b40f0301d0a8002042c084100710702292104020359070201903101a2812600941c984925030450b21601441f0280710228000a01ca0144058445a8124035074800034003440d401e1040380a0400d05603070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 471908839 1250 471907589 471907591
    0x3010b01080118050702010e16050a090b180402030c10021005070504180216022205070806060307030b031216020913050c0118120b010608060d0224071e0506 69
    0x180c1400110001003014007801031121042503001c0b8030009560312481c00c12400b600c40912070190038800c0242101503c0c10b040c280804903842281c0580d07005075500c02a03070940b10008040c80d0310205680c036025520a4956400da4080d2005050351180310b40c81d0000b44940054060b1100103a01410401900c14043c0c45201c4d00706880e403c10300d0a1616001e088914a03503d034140b82106600070445516a06110018000303144d0b001b040342e48842104d800b014580301c9000c4004480d82d04140105e085613000b2403883c1c3c02107901034459891541d81e030700181d000d031411034201da4051003078008662003e001d48024010100384d50142d0440e400340c034010070420190103044580025000140e00d8001400041c2c0c1c0b004110080c2040108100d400710118500d220031703072200c0d840342400e80c0c0101c05c003c0400c4025058030341c1d03a141d03212261603500512001c0c840e01280250000109000750301b2508800b2080e8101031005140f0600c1c02d80725070b4880b0325240601401c8807000311603912000c1040710500c852 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 471910089 1250 471908839 471908861
    0x1180c02120a03020901030603081b060f090a02092701020415110d08100905070e041b09090f0b060403050601030b33012d030605151803010b03060403030b0301 70
    0x304000d041160324100d0307a2160b41c41050a160b4001200a050390003504118000e50f00032150540f11081c101200c100030950040e64013280c0100c1001030507410306011418090701d111070050122020543c280b10b22000c0150400b0042c03da240040003078400030038050040540c44600140c0c503a403070045003103c0e40000e800c3e0001130154018407044134900000d00c0040b040301502c3c0c411101e8036a080352841c03284454108403c0d407400c103403c118449400c40034220001c0419102000820300039248101c0025040d24054005000c11604010001107500702900100084000080840b40309000030440d038030980c400ca41c075804c248010001c1c4107100c0f038604c0c5e210200e03003d69880149200802503030b0528120f2903040264a54014110691085100f1590a82110003552a0500300209034001491070149200002d042c44070110791030401c042080b010381488450942406d520b8030320b44012101e0300a04580640d0f8820206056070380400243e07008901948002610030040d000381400e6415155078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 471911339 1250 471910089 471910093
    0x50106050306100b120c160f120906080411040b13060810020c0304170c06071b050105041d061207032a031106070f02090907081501080c0d06090b01180c02 68
    0x81000810030610403204c0c01c0464010b8403005030386c1c02c4041d0321680161803c50b0f07280c030502c2c0d1160381000070003001c040c0b45501903420004481c250729002c4070200d5841c090103000591500200e000902d100c541d40d0488040280082180318204000c500300c03400800e9030340c40f041d844403410004243c0c01c1c00010041190124298030303200010003c01c2e901c1c4103034070409039841c601e110002c0030110180f01402002200600c2a582c804032814400d801075540d9044414880d040e180000b8250b005204450884041d16450010f4407032034a0b11200d04140240380541041042d5450903c981040c0503c0002e1880744845080c1000720030643c1d0031030b9a401c0d445400c1e2081051003440494440040040300181c2114100e5554041d49022180c0c1c12180a000750095461014000304020100e03040c0300790f88103181200c0e561078218900d081c001c0401e00c5600141e8000c2071003181c05050034000c0708000c90150001144400160703440030400b103400d9010649403000b54094a1400c42c190042d5082e009441c80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 471912589 1250 471911339 471911371
    0x1e07022404180501080f1c0c0503070501050727060827070b0a0e0d170c0708101e05090c011d0603040b0901150b0a032007050106050306 60
    0x102088100e00d08000495200c20400d0300103030145885412600680096540d00d012220500c4a560241c41c003802141180d00403d5004619108009403001c0640c0b01052070000320b20004800344c940e10400c160079200c90100b04420000b2503024054640140b0150f40d0724041c90348252031001c1469103482c0c062041080f00c1c2070170001360760301c00c0080e42c02002201072082682e01901903088855803540d12000c15009003d40000c00030b0100c0054020b510154480428012000082010001e0604001401c00c69500702070304860b4041805082d140700c2d01d100b10340f80c3c1c82c4c4a03403030180742036051606080d9a076160038400504080c480b500c00500405000140006c0c10480d00c01ea807120311060030f10f410440c54450007041c1103554482c040780000f02400c07495690506092111010600315203d60f440d40c28a040d140c00c82500c02c075044102c6001504030740c11f03c561300070100c02810302050f06440400545505010341010380006000c0184070350000184685040103060800000401c40c0c0250802c00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 471913839 1250 471912589 471912593
    0x6010e010e1f081009110411040b0903011508061501170711120f0301170a0f03080402181503010c0806060708300118020f070201082a1e07 61
    0x4507505800030000000000d01000d0180b840140c8100ca5000090f5407080c5416034500c004c0a0380689800c40c090000c07800f12400c0740080c0401e54283e1480f04400035402c0004000000d0b88001400043c03000a001040b01e00000d02082c05090320780c1c200174495004201031003041c60064808060303032380080c2410b42d00385101403856800640010811010301c0078040c4607100000c02400070450010b1001c034100c0c3c0310480391270004100d8100f400342c40c14000fa0800f50503041c410000340410b04550020355640103805940d421600b103840600120307040603034040d02c820385105814002e4498444400c11351820940f410416080d110000d140c082400554018010300c1d071200000c942e135154102129694480603024180240c9112001c0800004801c804035002c4c50384038000b4034100c0b0609500141d40f0001c0440c1f0404900c0389404108840b6400c10401006500640c996540561103c00568480d4000c604822884e60050340c400540c0c9030006420051000d0400341410601105110908124041e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 471915089 1250 471913839 471913859
    0xc060106021603061805010c05090109140303031f03050106030f020301050601030603020915031e1c05040806040b180715090e0c040911270f010309111002010b060c0604030206010e01 80
    0xb07030001401d40303905c401458a05501d81e442d40810a03074000020009a00340f00f400500942001d405540015802400001c200c90a180041ca40100c014081c41c690348656800744210120003130301d032403000110321001001c41d9081c400d17200150f0007045210f80021742d5104041c03c688009107214145880c084084c0f01503116070202d9607100940038030140c001d04251300000d1616560b00000c000709591041502d030761020218a0a41c3c0f1414030200c0c00c03504401136800c1e41c1c90b001d140640f00c0c0d2a0f01020001c1d001c21034000301607030440c03040c40c0101442c000f488016420625580c0040110b180a2191140119805070b01c04d40100184200070115003000d007107440c4688200c4c8074040702162540c440d9841d2200d2403040b41c0c807074091280844601c22007031070045e085040401f203d40c883c915040c03d5812075402170181003881036004000d031004801c100708020041c41150120021507503101d00c20f16441d00c070170000b045220b0000005212520f0310389002450580160050641140d45c000100106249 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 471916339 1250 471915089 471915133
    0x8010c031103042402070803150307120312050c040815060f030304030b0610110a0507030213050708060409060f090c0f06050403030507200a030609050c030f0d05030603030d05010b0c06010602 84
    0x24005004d440f0718580b1910800b81c051004040c0c102a80042405507510760034044900200d0164203642c04642c0c2c0307220041c0038081c14940070300814500f05420010304100d03405943d0041003141950f040c544c9039081503241c00c8500760812182c0c3e080c3c601340462490442c0c519406410100d00031880c3c54115644c034400d041024101c103000d0618043c80c2c4441c0c5004030a076844810740001101c101c1e444600704079a480c106440164000c5803020220745e21403039140a014880d1000351104030680e1200e9052000400141c942610078945e01c84421035100403d00446501e14004d59840b000581001c2c000e0701000401d501070700521004020410010f5003013400c0d10300c0150060141001118003070000c081d42544949101da200c030021101004001c000d900050006024808656400d01c00c88289965400b04161150107980a14040c01210784160015030784144040c0c181c2c0d0404a103521044281d900c01c1e00060504180458001181c072030400c0054010042d81c401402041500202c070600002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 471917589 1250 471916339 471916373
    0x10f0302160206030f0103060b040603030f210203090102041e0302010e1e0901090f15060e19091d0607050909150d050d1e050309031210080708010c03110304 69
    0x1030003140c88200e25440d508074494040e0060030b080d5481c80d0516611340d0151007400300f220464079000f500c0071682070600c28102a00c0d0b050300e84078200c80d078a1801b900c000d0880e04107688002d007012100c86400256002640c0602c1c042c60000d41c8641c10941034003c505041808240d48007080b2000300301507a0b000c0c441c82c0c800d40e0180c074410b41d058a01c800f441c4a240032010a290052070030400003529101a50201d802000c15110810405542001d20f55407610a071141400240940342d158070186440c40140c90707030141214850400e60313940d1816a00f42c42c420600c0220010b01d060082e9194401404840e40c802d602d8074045140111480004c0c510810160004102c80d01c4460724603441c1e00e44403851001540c02c502105c4005502440090010706001c0903560300c012400c040007034540c020020341e802019904059820189014141c40c3c0000004040010306041c200740014150000d00101000d420030200114100f204180c025086c1e6500c0406411100350400c10480800c60f52034017610002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 471918839 1250 471917589 471917591
    0x50304050316050304030c03110109081605101112030f1b0a03021602090a0f0f09050c1002070312050d14070e090405070902040e1b0c031e0f0304050f070503010b010f03 74
    0xb400c241401c51450241d60401402c042d024040401489018108604402005d0703031609259074607000c400d5207580c0864101440c80f400340c0001d20980c0b800c0720981b6401100c510306031140407001d001175403400d5607074681c425200c5000803d201400307004802443c1e00c2107005200303c000350300354404110395100700c21520003015804030702f26608000400c0e91040d91600203020082d64244400708200403c9038013401041146020746c40e0740500e1982c01110120f94006004d86100e012100c00e02c50b84000c450510000c501032078502000041003805044c0c5101c2c07160b580c0540380d00000d00b001d0107c1d60180c040c40854100c120402403d164421004080c00c0c0080d6210105900c0f45e00d0000d00d00802c5806c0000120700124000c0354489000caa240c0c418100e200d990040103807811901210f42c419034001c0e28603a001045a03102505030b030180c0d01e6081c0040c3d4017140c41c0140b000040d09550f04103447c201c4450700044d88954200d202000b1850180c2421802046460220b00002c0c00071020101104245 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 471920089 1250 471918839 471918877
    0x80f27120601170703080409051e06100e150406050307030b0d0c030f06060902040b0a08011401090308180405040812100b04210c06020d091a0403020d050c10020c100503040503 77
    0xa4075050161200950340010031307d880c0d0740c403500f10101421f021540389c180c070450a550034172096541e0404501840d0003900c400f00b0205064021500d014000080603000802c0c0315950114452600c010401060217954a6440e810820001002e07265043da48500c2880012854004242c2c143e51400882e9070100425207692384902c0c21030094032480c0d000b1a8418800301d00001c0e0305420200921502c0d1840e52002d178260f8a51504040310084800c2517400520902010310004080d44003c0815000780d0b0201d1403200ea18200040c281c8100712403c46000d00b010032440d510307403440300445802c1401c4142c0340303100d1410280d2034009801540b060450b2034140b2081d40c18084c0806020143d040c2e00f14145901660311a080a541c50340e201c1e58000000b1081400000c04c0c0c140300080c084044182c00703003a4507191a580070440483c0d44090140c1e01d500910f07017032450342c2d5190714140d840e000141c0c0242010520f1081004004c2141810701c005000c01001088001000801100c0e9455103003140c0800d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 471921339 1250 471920089 471920129
    0x20306042a03052a0910060908150109020708070609031e020c0d020f04110d0615050a021207032a0c09021201030b070e1011060a02190c080f27120601 66
    0x1c0150000c4400e41c1182000051040c942c0b00402e250065507c1c0d600e0300500c031965805400e13030340c14034204171070f01503a504001800207407880e0b0001e1100324022081b9600b8035640e83c42d20380441d182c81c181140031501c80801284d41c10340d10701f02c0801400c0d090016102d40b0b0310030408180c0700e020f00040288900300064400c10141d865a001502c201940c40031980c4410700d03404124000c14441c081c58588807450b44100b0140381c8a0000c58849240c01d5003d01000c420100040c41d26030004a400c50034482d81031256508102030381d100c100d02400b08c10100000900a003071540c1f2910050700182496401000210250329103051101e04603680034441044503902c440b81250104090a00b150f4040c544984000c4101c0e400140e2070401d6094000b40d4005450f0309910344101d100719850301580c0038460010402407409007500840c11030140011904d421401800c200c410b80c00508c0d10180f050030703086100125140c079450f007048080241c1c1d007495038020ba902d009a07121070510911401d00c0f0003032040702c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 471922589 1250 471921339 471921403
    0x3040f0605090f0f010f0b0f0a0317310501020321090109051e060601080103030f0f020c0406080a061103090c120309040f0b0910030305190903020306042a0305 70
    0x154032162105441050b8060301300980a4607040302d803c4a40707420060030500900c0c10307900b032482d02800100001c14480c9940d894448091419944a003850814018102e400300594660034503d102030500042d44a824a8221901781403904043c2c1154818007a50186800b082540404602c0e0840c620342c0756558554510302601c00084000d00c14010100149022501070902c10190100c3d88107aa4455868100444410300d092002800164450304c03207400d014041d0f065080c001083d80705030740303410b08034001180548100d0381c0000780c542e2041c90340300c06001041c41003801005165102500c1c50414000490303031002003100d154401d4a02c85130407203022000b082182c4c0040c0026100b8410070031112802d000070410301d18014000c03020980058030018540c1d0807039040e82c0e415142c203400c024801d01d00d44a16208500c42c00c003801020903020026940420080d0701c41d078420b500103800c0c01d034003400740c3c60b44070303002c55055044508410043c40003503000720759007402604203c48041c01005c1111900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 471923839 1250 471922589 471922603
    0xb0418020408300306060d0b040b0a0303020f010f0509150606120f07080105191a0409050a0209040c02160504020304020f09040c140f01090b0304020307150c0c0b03040f060509 77
    0x203a209990b050f100b0f0001c441640b40c4142038152280c1c5207001d121000c440103200c100e0301c0e85c2d4041010860703007800c03010b99884071041c1d0001400c000740300f00113100490581c0145420540142c0e2000448030740308842409000e1501c0b2110800344a07905141646543e10315084c0b08c555040ca8146000a145442d000306649a0003030801c00c1d0301c0c280c288076540d0452140c06440003000102c140e40082414246200842c4400e86140450b00c12240390074542c0b81e03c4111440403049070174080000082c411854040c0c64000c40300d4404c0140d8800030b81e01048201c8401a00c03010554020000510300d091180c000001200c20507a00542d4a0f81c8510018458000080c00244d20600d00c10500052204c0e80351000c003900c62003402c0c80b032000e050504000581c1d021500d650b0000b03c080300b0900c1000a0f8130b002d907420620280c103e481254440400c4826006034441480c0068071844464080c44070900d41000184409950b6a207503041c0740e1540c4131003491840e03019240545031030200d140c146c000c01c903070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 471925089 1250 471923839 471923849
    0x5090d08061e10030b010e18040609060b04090602030105180601021507090f030b1605090d0602070519120e09010608060d031202041211151219092301060b04180204 72
    0x24440304151090064024600201054001015108004001c1c14550054103239030458081c1504140c0d113030b50b01d0074040c0a5a10381100d607143c4806506460ba01c580c018900c81c1b9124440158496040405004503a4070b031104121802101000380515a40c020036261020041350f00000917680e9020425160800140e00c5504a4400300c00000305018401c41c10501078804400c50704101207052504035520f0189036007542d4000400165480054000d038014200d242c859410f60f21383c04050031010072034041402c0d080d10006414035402203115809200c4600340d10701160000380381c2d4105040100700744001400d4030b01891a448400f000d050183e0311821510507038a50175903441c1d407524a0f04011841d0700c601210400c55642c00e40302180341c1903030720403000c40c031060b0700c0e60819480c0000c08540c00d20250801c2d4044000ea080588102074602907207144502400320111207825280d444440e100c2c0030f00301840103034134110007486041e0341c400850f400c64000c019407654844218040f2002841103900c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 471926339 1250 471925089 471925099
    0x30608030423032805160e010e071106060405060d06050a0b0a050312091c06020c0309091609030209060a08010501090e011b02070605030a0219110105090d08061e 71
    0x400a02c5480107400490300c250b0300080040001d100000f0b06568407014a40071043c9180181c403041600d00e00030b04840c030a4000e07402c49455409001c404980200d403508a419201491401440200800e14400350443c15502d0700c000c034500a142c5150300c0b030720082c103e10f2066884c2e40200784c0e00e03595600b04415042e00300700200305604100940100a020a01c509402182003650000c1c00745004200c0607807000f05180c000e4581400081000116074040c11180c02c4801c48484413008039907244081c08030f090905d0300469403111020304101c0d000000510b04c11908501c0d00c201d080603a481908041107a84c1139a14100e10b848040c0001d98080054010a1181d8038140c0005000c000507003222410201010080111607000101c4604100341c015800d40940c0c8542c504010040c8510001c544c00003440d0780050820980741d1100700790754442d4411000094154040c4800ba140a119880c0c000b141c18008202c0708500c80009004050001c0403144201480030801e40d040c840b003200c4441c5280003d20b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 471927589 1250 471926339 471926347
    0x4031b05030f010b1207050a0317160507051905030d0807031e230705040b0f1908100f060f05090406050d0311012d18080a0c1103060f0c070303060803 66
    0xb000a0082c0b07031081d80e4502c1007440342d4001140c42004181a03064500190103d07404a003103403030386154480840e506072503241c8104014010b445505000c111114420005899903515100030404648151803202c0c40000401001300201d50703000a07449014138803030800ba000c50b541e1950580003024200d40070590010300e1100410000b079603510000d00680b40051000401040c01018440e84104a8000b008103408010600a510003800a4580440c1c603444d414500030280b40100500f58914020002052840e8103100410120314800005001213003d01c40407a0300d000d07030041c0b91002084582c000d00c00005001c00c01600e130ba420210103071401602002e0a0205441e00600d0032401e54048000da52a00e0507901104042c0d204080d4103050055900c000c2d400b01076080c00c028892522601e003400041e41c043c4001038030400142140f0202c1d40c030354450302102801c0103503444094034040c5105e508081c0412903400c0406440b02e400c0303040d003d00185c84004529041c0c00801c983e8200404510000c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 471928839 1250 471927589 471927613
    0x41401032f0c19020d0209041403040b0a030506010c02030c040207060e0d020c03150106090e0702150f190506130b060c070315060e0402090c0a0306050405090f0c100504031b0503 78
    0x100101080ca01d0a01158826080c07010034103200520f00380000d5010001d92031040141c0f41c402c0415420501904002c0443d007c0100c42a246074007660000c0608840440c40041c0380c0e826224640c0d10407020300f4503070a10511980040d80b01c0a420081c2e030700c140e60102d6504c0c24000e4950221021480d4407088820381e881d8540302a5031041c86074180351080c0f051000c1041c01589900d4540d04071151502c030740c0b00181c24503d052207245d000405020071071003807401002110702c512a14034051400e403030a62210341010005080c403030000c203100c507048900303181c240610382d2500b0340a10050048070600144d5200140b0000d980752294001c180060700c1142000301c140504070069501c80110703403d0402100c0c6d56040540d10404044402a5102d1203541c0090f0b1354103c08001001480c41510b40012103944403000a400c450003990150181d5121481403e41a181080b601c2060744080f142038840100401004190340b0481c0401458100340a14101c501a200c204034005003900806903200c412401d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 471930089 1250 471928839 471928931
    0x3070b0d0209060f12130807240c030e0c04020f0f030705070213060504320c04090905071802090904060b04060902040e090615011710150c0c0b04140103 67
    0x4891103104801306100466064030018104501d2142e00655590500310141c50742985140c0e94902c8480e00e20742c090b010301c03110149c1d125041e41040301c2d440004444a802420390b140124414141d07026030310402105180c4015a0182c88a17050091000d40c3d8030f5544030b00444850142e50002074200040d002040e0700c0b8159504400c00380c94040e01e04120038004000d0314501c030425880c1841202419800f800100d201040c0499030007181900e0803403038595100d50800444440420540f101e8006540600681650800100000c0406003003542400c280e64000390a042010300000c2c40e4540d20342100d00c0c0c8e5103564110800400c0100030440d120790751760305025220001142c000701c01340a10f1000801640c3d100c0900301c82e00030103940300040b0300080c131401c850f803140c080d020401c1442e1001c0d0000702c19042268540740103040b82d40341100c1d1040d03440c0103070070040e00c0d400811b500c00c81400244400919000700384018842481c2c041601c60401d00500e0320000070580c2000e14000c908240c2e000d05600e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 471931339 1250 471930089 471930097
    0x3030301080f010b010201060b0a1b1202011a040515121f0b0f04050c03010b090409020d0311060f0c0d0911030d09140330040e04050a030f050903070b0d0209060f 71
    0x442e20003845690703440c400481c01c80341c10740030307220301c4a00c14407815425600c03070995004100901500840b4031021512140309501d19100a000182c0d140c1c051b4113000d50354001d0005c50010141c9091140f07007407102c0b143d196607880c0c0c4003a50080307221b2840716220130804c02800d01c001c000040601c00b4544a00d05800140c101d104034240900840789104505090910882d803060450381c244505690814091002a9205403145075000762142c08507405665044440c40200d8801d443e8500c00d00101c0d40194103244000f807500e101c0741c40c103604201c20651030400f03d41c0400000100010312030b0b5140b03490458a0141e00d07219070184588003d003980a500150007400b03442c00c042c0318000c1c400c005000c0542ea8015a101ea1501e071526081d41c00b0790300006180921b901d40160b01213400c00707440d80c610810480c021a8203960b0340e8001248403040c181c112011060350403091820510f071a124001099848501d0310030314001210009207207448680130390699400960041c4510707515801c18580020300c0d04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 471932589 1250 471931339 471931363
    0x6060c0b01050108040507140301020c07090507091e0308090a12030806040e07050d060b060415030b0a05040507081819050f0c01031e1806020304060912030c0207050d020604050303030108 82
    0x5500030010400c1e41c001c200c004d10642d4000d000f070840b5401c00942170311a00250603001c1e007664081c8007882d2070400621228019080084000a1320325002c00c0007401c00c0040d81c8188442600a40e10701c541001040c80401540e03080317822607030b0351300206000c00c5a82a090b449680740307622445080d004c055201510600581d400c980510010b156050002d45691241c410f8507800030106000500050060b007000f1259940103010500705903030b03a40b0801d2034007045040031b800266521300201c040e00c1c0c0440202d02900c0c3c1503500700302c00c0c584500c01410490015000303400348000200486008442040500c090208400c04031018644502d0181d81d5200f426210324400e02901d481190346503c82d12540070448440c5a40c421018295103c01c0010220441403604c0584103815440100b05580000d50282d0310500c00003d100705141450420382c0620640c6408050620392071818944d0700140781401d07960129214032480107a480000c90360b106627401160103000c0400002696240800c040c0c00c1e0351 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 471933839 1250 471932589 471932603
    0x3030509040e1b090a0f0203010e0a0e0109020a03060e0a0c06120e0a03020c060703110a031e0c11040b060409090506060109141806010c17040f0e040b01050111030d06060c 75
    0x40c4600014070f0f01c0b0b180281c618100c1004204201805280c1300039100e070015070280d000500700200003a4403003a41e009030801d2045001d0003040c460a00281e1103440c40c180041070081101080a0380002c000700010b200140000c0d4650000d0b920200d401c1c80500720495001603540310303180da01c01019042500389003050850074038001e1450000300f03000c05c100041c564142e0160920b810200c0c204692500700740d4064040028440c894600d5144c10420889540d00a4032403080030340300348a100d85465140341d0f080c0704124100000400161402d000d002e000c240480e008152000340d20040741260080d984a20001d5007840702c020140000461420700a44083e611401c41d40d4442c2d014050200410351880d81281c0420441291414a819015000481403500c25030304602902c0302242207203003103200785090b000050104140c03503000c2c0c1c411004084411040c010b82c6095210450709003014030805040c80070407002507014102c24401c071442c541c180d01080000c1601c9800082581c5c0f05110101d41007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 471935089 1250 471933839 471933851
    0xe0f0c0a0504050606090103023103121b031d04090809090108061e070309020d03200d091502070e010e010810020c0a0f1104020d1e09031202030415060303050904 71
    0x2038185405011310031100a81054034240c0380c040110000d500100052042c40007204c02c0c1c2c0c0021400206d800745200e0120421004103081d81844070103044082d0404c0207120440060190f039481050b000c480c41501810101d8a14031f0241101380300e50203100c0180e03406072034200034204010081d405020100f1003507680d1000c5a0301d45031066601c030025a038852250300c1112480b41c4540d07040f1445548801d0038039000c24000480d9001c143c10710803c280c1200450700b101c2c0210000c5484140d0480002e110350010708411000d000043d20b0f070840c501035029500300e03164404503240e008001d280c0040c5500da80c460902d41e9682c1031013284030000c1c041c0003c64010b00319408034554050003a50b001420410240001d0079007507030385425004078074001303c65805410668841690352840030703140601c04501c02240c05a01023080c8142d00d4540c820140c2182d00d0046000c1c04aa440340040d070a0701c010420040e625292030509120b81081050001c5046082c80320100815034010040c01b640c0d03c09803028002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 471936339 1250 471935089 471935099
    0x12040602031305180f0c0f0403030809150601050f03100e161101050705030c0a230a0215070804260a030204081624030e06100503060903070503030610030e0f0c0a 71
    0x60540c4032803940340d071803c108005c14218440c0d24002d64000b90740300710303980c0b9203410162400b2140d0025171080d00070400410400580c440d00b0f000052418020750244442460300d2400640036006400403a00480030100014200d00f8002c803030a809026603806000c044d14113841074244a45501103100c0009400400c42d0051050500915002c0c142a4590074295a1140380c824101d80200042e0002c1182c502c418008921080303284000e100c021300d40a5540b40b0b5045402b91408980e00c0d00070541c2c1c030207501000300542c1d100c407410b07070440da119076011002000c0c400d02030000c83c51502049484d400006520760015050b50042c8110365494090780d0b51404040d0700f94400c0d0915104400e4000201607a0032100f42800980001a001d607003000148100302240e440d01d400f5040fa422130f4440c0d45a101841036280411196500180e40f00055241c071300303d5074910340c5030b0102904071400f4407200103c102c0c1450294000400480c0c02200700c1c0c02e0400c585403259079903202410424010700d076400c80030603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 471937589 1250 471936339 471936349
    0x415060812180a0e0108010e0a020d02060a21090b13110108060301150803030402040605060a2a0b15040506011403040807021c03020604030201112a12040602031305 72
    0x100c9180a015101140141540440c02d078000303100d42c0060a0240c420001903038070340d01503030301600c030b0a0901d21081d8107141201d0b0171100501903813582c0e41e100400c01310060750780e50860031a440e81507500903161503146406655800f032040700034516900c50400c0683d90341140d031000789480d000d40e4801c125500e86050440c85820700300000ba1004a10040400055000b144026000300f000750000820380b40703450008c4007a040641083e0341035003001040c4415440c050140c50013906c8202d5095103046450300c80601b01d01c5d807582e2021800d44201c04810645a1080c810003452a041880c5c602d40b80340906444803046445d1a50740c2c0300f1131400c00403510651051190040b050010a81540b81d42c8a9446d0616980c01002040b81d22a001e81040c96418800203405500c0522940007011542440c1c130f40a4250780c2c1e80307141852134902c140055040341d940d081003007041203841d940c40d6865076140c0380002e00b81407060390035106150340000e00045269000000b4203201107080c0b0300000c03480d00c03803081003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 471938839 1250 471937589 471937601
    0x410906040501050d0b041103070803070b010b0f0304060902061c021b070b04061202090d030f0e040908030109050612061e011a3f0711060c18010201060e010e0415 71
    0x1e5002801d05071350b030300000c58207001240c00c28054250324580710080400070f07242000c5500111441c0c0c1001c5019420000a01c61b01405048615543c2c2e00303011500f91811806c0c0001003026080c00d0f00c89030b081c0155181c100440b0000307498201400d48000c1154802d00280d0700040a1420503080b1404010b545103012030b0800c1581c0307103a0709140ca49450305208903050220800c9940b18144d00700901c10305680d0340401d03281c11501c40e4030b40310b030362203490130003d050420105a050f00450600101c5400110120300710307415a60035203800116500c0e80004581010311010170100ea61040a040c8030341c1035000442c49100315522a035140e501d0780c880798181a051801c000c541d01d400c84c144155200c2400c68188401290155003032900900c0d03440c3d00d404107001c5041c1d00c003104411606e090000456200d600c00c000e41d090000184a1401e140789800c005101c1d11b0000941c040c0c0010101c84140c2c400e4208e0401031040c039407058210351319907283c0309882c00300b07980c1111240400d5071401c021400300c0c0294 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 471940089 1250 471938839 471938849
    0x11b0c030c08060a20250b040311190f03120e030903010b0609030303040308040f0f0305030709061701050f0a030f080d0c1112030703021c0509010c02030f0301410906040501 76
    0x1c00c00e0300d40e54403c5d800ca504800f03480480b540303030211003101c516440c000c0d200181e0b0080e140c2c0d1016080a080203040107100c0c02503401075402c1810b80710042e9842e001101c0c0c0c45948161080b03c0f00c500c6081c200d0ba032010007050300705c0e80c0341401c14812400c0000000703071000c031000710002c0100681400402c841d61042005050301034001303100040119014600c04c4d41d102d0b0040711a2400c000741903440701c074030005111003107020403000f00a006c00c482c1d1050044010300980d0412821a2484401030380c00d00405110700d0f0310646104050820546036a000c140043d80d110f6023908040801d880d26049607040704201036141407030402200b62740d52089030b80080c6145040054041c0301c52909010300c07a984014283d5052580810a030042d0705601a10b00914000703010000590f42050000c1e039003561815040c100440d802400354000e08003044007200c2c1112082c4010f6800d10411056280460340d49010103144050340b10703040c03150000341030040103405500300c8000d4500d6880c40c08100840e1420301070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 471941339 1250 471940089 471940121
    0x30f020702090615090303030a020301030b0f0402030a11220501150825030b060c010c02070e190519060b041703030f0411011206061110020306030a02011b0c030c08060a 74
    0x1240c02410b112011380c0600031415202c42c6030218500c04039182d5803040d941c1c140100d80c004010414885d8100d80750303810400c2c1b002105290704003900042d42d2800c9540c005003c2e030b905074680c9209951f943c0752210032074298161094041e00382d02c0c0303264003d003024400c03000c081300c406001c02000d40c422280d0b28480c00000d142181304203041201030f59034425980da1b202c141542c500301c4400b070b50b0300d4101606142c54804000301c4d0001300d1440090801c007140c1d04c03c611080e6282d085c0020050b04804075078024a0a00b03001401d0380c0d45410806481d41d1851040c070070729123003020101c5d01410084c010405c2e22000d9020131550700c28600060703a070340300489112048000e00e4002c600010051100303004141d605141052181c0038221000d811035009a0100000c5520038912143c109002d01104a00e0702000c0710441c05c61034940c01080e22061090700081c100001d02c80e4110700350030710290340000581c000e008001290348a02e4210080740542c014010580310304000940c0300c1741c040c00740f5000b8ad590844 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 471942446 1107 471941339 471941341
    0x30603150408070c0f240e010318020d06020406080705070f060b01030f0c0206090f0601050d1b150207090e0a050d0806060412061a0102061b2a0d030f02070209 70
    0x800c4442500655000c400342d0b0000d40d8414522000e08020513518842d103c40414452405002335104507a15015810300905070f01030415a605034071400c0007070702c070f01000751040d02800310b0041898461840c042e00160f842d8105442d00003040c140441c0c9125070600b40003d58154006130781c0168410402c02150050030000410200402d9001e40039550419000ca40d05405600000d0040107401d90b01d5094401514282e10080c80c5c50345044541c0085100029100c5ca9280320b801c000341c1c1802800080801c02094840300c2c564400024000c000c0c5020302518101c8006041c2607005506010000d03ca5802000001a141c401c00d800141c2000507400c50b49010b941e0881c003411540940200160000743c0040300d05400100012561103140d29820385e0346020502c02001c0c00e0180c4400d0114000000080100302c40007191418040c64625110b01d008030b00078008084c1d480400741d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 471762589 471942446 := by
  have h0 := BRFrame.cov_init 471762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 471762589 ≤ n) (h2 : n < 471942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
