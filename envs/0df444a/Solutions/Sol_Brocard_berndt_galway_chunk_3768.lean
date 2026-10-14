-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3768
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:55.341273+00:00
-- url     : https://prove2.me/submissions/27037322-2323-4163-a610-e6b58a332418

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 677517985 ≤ n < 677697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 677519235 1250 677517985 677518001
    0x30903032714041401050109210c06080a0e03040f0b0c100c0f020c12061305010f0f020d050604141807081015060905060708091903031d040b030a0b07120906 69
    0x2ca1030030710080746100c40c40b04114186c42d0180c40b10b141c010302e030900146600410b4100b41212548103502c0000055203090380500501081e40c503446c45003040d01003041240e440c044103003596801000100b1552540102ea8011a001d00c0a02c41e2294082100b25042490109125000e507151080741002160001c4041200c040d559080710b40c8268000c0030710030011407501259219901240024425003034410000308058412400840d00d40104010701050f1984002000c00ca16000b02d2005400d500912849038059800c442c28424000b4105002000803006003890b0b040a065181c00504203408014000043c41d200d8110758081801c0f0a02c00002c2199113800c0401c0401100c0c00951a4402c0404134203445000300064604800381e56540102d81c00626040e4100c5110503815400d20015006200110302a0b1200003006008817540115a65104003641c0b049103044110300c2a920001800d80d80c00b580000c40c001c0907221198180c981454410440e8002401e1004400400c400ca400040b1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 677520485 1250 677519235 677519239
    0xb10020106060306090b0d020f2d01080a02031501110307021315050a060503150a1205060403030516050d0207020622050109060c11040522060204050f0607030903032714 74
    0x7080c0d10317204070600760f034014441c2a0f48104400450400752800d114440c00d410001054205030741e804160003080b044281564500031020b04400200a50300b06251a40c0003c0c1031008504d1403503da540ca404944882482c14100598058082c1c0d040400b00220b413040c9030014400c0e240c08500502080c082c0020f5517030720b8a211a840000a41e50400050006c150748032612078034156603559540040c2414486001a4080716000d07001401c9032504520040320b5000e080600410314040c02d0260035180b02a24030703c02c09000180c107400c0e540e40481a54141140400090b90307400322400000c00c14052030a4030f9059030b500c0400090241409040c2c0000c03030320280c0380e807010142c1e2200145c0e051805014003500d207828020281c9214a8141e0010b1b0340300110080180051000e2084c0e01c2070040701000c200e9000c1d500107001c0c0400c2c5001c5007103c05810048981c10b00d0881c40c0c1e64010403114492000906010006640300320b41caa0746915000085004c5111b840c240d40d88450310f40c018244c41502034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 677521735 1250 677520485 677520491
    0x60902040b130e071209150e0312010e0903040e1e01080a05150c03010918050d02030405120c280909080403031704051b01020f03030114090c03070816030b100201060603 74
    0x20b01c4198102c9007407281040307458045c914404050f041010b4500a03508481c50782a849518001341564401d07072031605c080390015a111038510b0040110404182c000c0840d26403003504010318030f540002210143c60012480143d0303500c5140a4503032400e1980044c40106810703c002080e00b102c001b4000c0b144d540030310212940d000854124500508041c0c800c013071040401c1005100301c00480e00f00d1303032a405540f034004582c034410740c564a09140c0d08580c0c840041c0c00016080006240401100c00600801c5014080311680100024100c0303052507019a99680f940402c03000d80e6032440c0c2c10f1360040070006d00c01e002c6c981c02e5241007001a882804110042001c00051120000700043d006100315809001801900100040c011908030b40000950441c400d240c100e000d012414405180203015203041e2504600c05081002840c1100800407a000802842080328265004004079040080c0354000400d81018400c218082c1001705001904107998407240d04610b0341c1540f0803030495026a07010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 677522985 1250 677521735 677521739
    0x1511160521090307030201050a020c090f012c070e150c06041a072010090f05010507110d1b02190501140903030f162f0f030a0b04020103060902040b13 66
    0x110790140030905501940541020b10055000740000d0201e45000d0048412200380c04002034890780d030454801241d01c00d504010041c90f00b540e4051203540701030042102911301c20900040540400410100800001041d1003405864809800c403d418001d6450b5588580c59a119580d5050544084414029074025080a07035245090b0354094a1640d451034180324400141e80402c10034030310018501d008550881c3e80b8044680b1402c91500c1c0b0410552020301000e040007802c40748000c0c121418082040341000140a0104240d00707641618240154440d586c10729524142c000c0c004002c0d00174a802e03c56080160401000310100c0d0000d13a03582446c1030101030018410302500300da15416038002e02c43e020b042c07019000034002d4070014075440d880e0081280c607400c03802c01300521010510500c0c0a0140c0102044a00c0d04803920030942e810107400c02180c022036980d01601901a000441100114045a20030b411000080050b4181503407256180c81c3d0000d02580800c45011401c6004240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 677524235 1250 677522985 677523043
    0x1308160c06030b030618010e070906080d0504181a0405070206090615062502060714070504050f0a0f09120306141503061e060a0801061b15111605 64
    0x2d42480f0080034000e0a0581c42e0020f04817019407001c81581465526180000d284000170000f110003488007500100356646446c031030904018400302d0b41c40c108401040306002c001400c11041c201da2411160010f0840181c02d500030385015407650b115841400c190600c01d41d80c0d40098158001c24001c1c080d2007580d283c000d511903015520300c0c401c0c5c0e0401d000384a13580d810806540729200081c881c0ca00b26581040541c0061030300d070301002044441d0140c90002c0da441c414101310380c9018000940e0104024240440c4070b0110501c001d01b6150b54984032943c020760400e0303640003161110b9000e405c0d080d9140d40e07510b016001c0c000758000c1401042035460414080c0c507081440146500f04000901c0c80c1d5214030040c4011014490b501c1c0300140108006400b940e00c0d80070050802860301d03034414903503504042c001484561115405802c8686000e200800300344880701840c150103c0c10400110b505115011005600460256803500030000e1800010b015020a64003491717020340142c9180d2032410300d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 677525485 1250 677524235 677524241
    0xa061103240f06090301091e15060f120201120603060507022b0c03090e0106030b090105100801230901030b0a0b030d02120703110105090f010b010203070203151308160c0603 76
    0xd0318a600c03480c2c50302011103074140940103140044000e40040750f155002d0b100e5a286e003040c2a21200011180303061a01440040502c07003506906410080c0540307440c04586400c04075050168204000c018407120085a01800d134051144440c01da0500400340e0340c4c01c02c1d100800044414038058047d202000c580c40000300d580d18a0000c0c141070b9084418044201110b00550394001103060185101012030200341c041c0d2018000d142c0e694003c61040c0480e03050004818060f40400e029600c1d440d811b1a2654100710f032541034038080c1d102000000d452410b0303504a420904200c40c1c00003000c00c001301c2030058008a00c2d00c20116070005001000b208002e0660302e0400110210040e00440020340c2064101c0380100111806494554000401e0f0140107003155015031301019035030701822901c8070218003801815280710003400650300741080c0b034000c280c0700d02e1038801c10303803485240350002428400c0c0841032220036034101c01180d459551906804546502c88030301aa03801c0d420403c00030311b0300d210340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 677526735 1250 677525485 677525551
    0x2180306070306051f12090215030a05090d050406020a031409190306272004061401020607051c1e05010305060f0c030402101b2a080c03060c0c0a061103 67
    0x1c0d031b03502e00308842c0e46448070041c140c5080c201d80c0141309100400d41a645034010394002c0324402d130300181906010311006c1ca06100b0780820300501134144010420541c001c03075050401d40d05801d14000c00451403500701b91074465002c030180d02c0350903034400340005000a8850001e40740b00360000c0221800c490485545500036081d20002c40030024205000100c400390320005031282d01c6000f04200300004001802e5412030b401003194001d60041c11a50741d0b90410170160480041e0810500c1c200100c2c1200d2894200e00305600f1410751181e8040d69640025103c44e03c0e1010501c00c204002e58503443c0543d190002a1814038580307803803401140c1c2450640c0704590150360b00601008041044880540303190134910402d4011402d08011031010552641c03188000881154100c00f40c062032418070015081907801c1080d0070f51005a0010300350300c0004240750030001d10000c841e00c1c4e0207240b401528055940b034008100306e0501c03661100c142c0300034025601449400000801c0b45130401c9510804203001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 677527985 1250 677526735 677526737
    0x1303031808090d0501020d0513022809090f02090108071a090d0f080d0c0201020d24171c02010903091401141e03090f010c021204050402180306070306051f 68
    0x2c0081c03804a00d000301400c12a41d10410002d0305000311002c2c0030b070466204561a00b14104500c800d41d0840c82e010510907240c0d1170284000150882000c0901211038480c001c0850a82e52040c0000038009044100c41141d54000c01140131980c58106107074503011207128182d120301e002130012003128120b40c15188140000b40ca86040c44460b034451001600d0b00c030b132007070340d040ca4200050341111120340600512482c13503030000b5984034500500c84003240c00c1144441d0349050401c1c3c650700c0489115a0303440c212106070406405058400005504054164143c000000f180c030a92802440d0190060a00103000c0c3e15100b007455941e9111a01e231024008949000898039050214820f1001c4040d00c00131441041c0313407408940c1001c040c0411b40c0140d0341050503502001407030050200034024034154480904c0500741850a03003480651500490040e144190740109007000580400f000c12083c42100400311000d40c109014003500821850251901400e000f0b80c01070000a06001e100a0860032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 677529235 1250 677527985 677527987
    0x24040f11150f0a0e01230a03060306140708060d020d021e10090503070510201c021006090b09130627060f020f0405041107050d11010608010b0105030601080405010908031303031808 79
    0x102c06c2c1d401407154021a07060091641d24a0f0101c003040301480350420150380d00400d1541410151001742031120004e040520400744140c160006854220005010550541c0d030341301001402c0c47c00b04a00e0320789919807600107200b000040c2490f42d05c8240c5038200c80c1c040d0190781c61540c4550a11904107071491700c23180403410500e408900c020855010100d00700f814000d90300040c1c1026805c40c2ca080400c0b40b0480164010720342c000e80301c5510300c1080e004100c4001d0421407010300d840071078189503004081c1502d0143d0480340b00c00307105440e040b004416500010807012445114060b100f0651040700c140e4140385006005a2240c0c0c052080350340107601072040324100b515100401c400341665001003848000240512000204104000c00c4601c8942d1100c4d44220803032141e403402c58000da481000240e040408004880e6005030803250041e00a00c0e000c1c64980e614280203026165100000304000c03800402c00c00c081704090040c2ca2074500c65902840407080c03150312540c0f4031441e8400541f4500c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 677530485 1250 677529235 677529287
    0xf060301020310140a03080a030e16140910120303050108010c1d0f010c05030d020a02150c0405091f0e06040608060903090118120524040f11150f0a0e01 67
    0x1035100b008844c88000c01c06440c0c0d03a165510401c02c0d4000c0035000740401d031580000c104c0303c001440341c04140540c20030480b8101c2c0c0741c00350811050301c01201c4c0600906190700840c40607500030304020083c0896040c103140c0c050852030010010a0244a0500d0301e501e08100b54207201e116640c50b49114600311b58400f4003030800000c0003201011185082c2c1449802c5240c070001620a001500c103050140c00c005803250300d0244040d0410038840c40111155608004005a041c441c0c07090341d0642d44117a4000c00e00d642d80d1803c0b4407110080030722003400c126140000041c49070350180900e02c540340990f002d01c680c6690b0f048459554a00340c3d00615680c00600c4a660654400c05006800d02203607550703075404950300d011141c4440309070b503c00d1b80c0e150000b030f2080c180801e005000f00000318410b84c2c1c0110340d2800d520f50a0010310500d1008219034103c00000710310b541d8160003201090200ca06840d80c586034105002401d92003171600350b000c10141d10b10406590f015442c00182c035000e024001c0070b454 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 677531735 1250 677530485 677530499
    0x6130203150402250b0106021509060c090d020301020d06051504030305090d02031e10060b04150c0c0b0d050f0105030303040f0b04051216030927020f0906120f060301020310 76
    0x140041d101004c003d20070442207074500318060803401256000b521040155410b180c07009082588a0000150158500d0184001c880300010029440341c401000340780c0f00c6001c1030000785060b01908010350700d903002040c80c0308801c07001c0c2c1c051403c03500e040b542002222600704112030340b800380d0321010300030401c00d20060b5190300f480800904803500c020140c1d4010054641900e1040b002c08034510560350001302003020201052141d02d018200002c21107040c01d2416560f40c504001d01c40c1c03540c0410035a00f900e90200200d481c4c140000c1e100800b1626241d529820141c0002c0c0404c1755003188084000b03000113500d06021003100e024031b0b00070020303200305502c50711402c0c914140944126420312550002108041c2c065028100010302880700024603001c038180200503103c50b8004110030689078001d215014014009403a001d8040302015864010f8160b09104034015807520b0783c0c03c1300c000500303a0f0090120448052041f9000714081590303866030002d1500b02d0004859220300014844d03000d11001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 677532985 1250 677531735 677531737
    0x405090f0c040b06071b0312031b051b011a19050603040314121801050717010603150e0c090306072a0f0f0b10080f03031f080d0806130203150402 64
    0x9043c01070501450b00071550b41d110488100e601c03500081c00411201442000150070700041900c00f01d1609014204001c44070340e40c103003440100f0400f804000202c41e05688400b03245c0c1c1c080602e40d03000070452001005500c01e151000010341500c60081c0c0c40d4441c1c80340d005002c1c3d401c207852001c1c00c02e500b15a16940e041c0c8140400309042c0d40050b40502144807171100070700c5003d1090604802001d41980b41082d000e094a0b400390520061282c042e02c807075221400d20003814111821807801080c02440c5811003500444180c002483c88071600e401c00420ba010349005040a007000e6041b1901035944140c112042c00000a15122301c0c03040501c0040b005c0c2840b840400d8240c081d0b0103045182c083e955480034107540c0315a04444150041d8100100241c0300000c1600900300000508581c110a102c821348a10008100d404014408e03a030340c3d5018200b1104120144c00ea44086949140f080c81d005481090f045800e540300e42d016442d65580a200342c000d481c01079070754514041d204100d500402c030107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 677534235 1250 677532985 677533001
    0xc0d05070903050607020d1e0f03050a090b180f070b09040207080d02070c0504060f060c06052d190b0d06050a23010f06030203090604060507090f0303020c0405090f0c04 74
    0x10003041640120215406020640c017580c03442e00186562a25444c3c007626003e0000e4121954042c5c12100c01105038011461440180543c500040e031980c1d4a81d0305c400503d80701c01b024151100034401c1210340c0c0380c04c020241010400c401265103d0b4541541070380c0c2c4509600400b4481c3d0302c14843c4178017900305a0080c111092003024521f0070a90245012412030300000c400f903480c014500e074108081c3c00c191007040080e242c2d1140c00300480c2e040a80140c1100c503e403200070192070703440700020700c88001120180d10b40402c40c0c9003000200b03003180301340154240644402c0d407039010410b581d29460382207200b40d01041001502000009809488140042000402544c00161600d40008000232002c0a0441130380920380521807030f5040070340842c2d02c200e01d50041e4082c944100244205041e0024400d68059404140801c1c15620490103c0d40c0007410391107002001d040040100405401181120f25842c003950100187d41d01c0030881c0d41d0f280700d0baa42c111560b41007031004800c141019004181 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 677535485 1250 677534235 677534237
    0x11030720060c150a0f0c031b080903120c07050304030b0a05070309240b1c0614040b0103170408010513030813200f0d08031605040321170702070f080102030c0d0507 72
    0x5820700c01640c40405941b1143d44050000f82d0f60744102082d00540f1060402400c414600b0441529155501c1d603928482c2010381011840014009510741242e4001c8405041e40030054035250b56580c0360095403200150781c082d14481c00c00001a6900380f091286031031141c2c114040140a5050032100c1c40c401009449280704151240d9002d8555107030601d000c0320f503488411402da540d10043c14004d0803207072150508003420118000707100209905408050540787c024010004603801141002618481c5a20009555080400b0454100d484641e1045005d0181c1c03184507403541e80c55482a503c000e03003c00100000c44009014269888415200602c032602814030b0a25416030300029001802148045070110800820450092010032200d2400c05580c00d00e0350805080d0b6860300d6108514461440540082e0711070152070b00e10940c00401a0342904070700e000d0f6410071207002900c03180c003801213162916081c000010158414030883c2d03c64444140400c4c1800303d914000c40c060640507240030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 677536735 1250 677535485 677535491
    0x11103040822030c061112030a0b1309150c030e0a0b060a0b030103060c090f0605090409030306050612010e0627040201020a05070905071b02060a0e0111030720060c150a 74
    0x3480102c2c9800c40c00b8090b41c0201070304843d00d498118014000d2101244640c0e25810035a61709139400040b800b0740c0d410000000e008070798900c40c00301288110003418962240c540c03c000b240c905000668002000c61464114188098019144140c09680c03607400d105089610a500a401041c042804150000c2000b007420459070b40da4900d11040ea042030b0410360f02c040d968910040f103030303030043d8480b0f00500ba01c490b80300c001e61804502404902800180760301542d21000d81d407003018426400720001e0324006141d01e8941c2403826180c0d030454401d003d504240401c21000c980b503454040032912252126150b441203180440503602e00d6200c025204a0640c4124185440060802d11018001c0c12950304002502c0c901044020428441d951030442c81440c0c4102c0000581c41d044201e50510f50301e41842403440380394800403a00004c038030038082d25500022520604100000d1015176000e4140c0d85003100141d006410080d00307200e030b8242440182c1c0603680300c100200e0b85290090303004840311400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 677537985 1250 677536735 677536777
    0x1a0c040503010c170105010e0306070302070606180906110f0d020d060b03040b04051209060415140a02030c0615030618010b04020442111f050601110111030408 70
    0xc40e003541c20003040d80300881c00d94003448041a213519440d900500c3c003441c0c03100e0703a0421503010a8484502602c03000c10035030000f03859024468641c101c1001400060b41e88040801010501401080c1102c0210380d00f505102401c0144a1107405031101d18241c492064a041c4140d41102c000354071041000d0505610358000186c58880c2401031071042e4061114100780385000d00d0301c1c504006400d1420715001ca4140311409481d02c42070705880554240d4114500a1400b444094840c0c02401903000d4151500003000c1942c0d40e13010000e0400c224200d0200c424940740c03070340529400d0295a1405070141d028030002108041c070080440e10b00d80740d480002403d600102e0100e001c1c0e80c859000816105038692800322b4003008071060005580340b46541001e402410b04070f2501d0490a181e030403040203038000c2c506040741c03000d000a810041d92542e440510b170b094040d009010f00b00c1120b816000c103040d014442110b11060007030740c81e000c0c022207900e45190b9540c1c1d07601d0500d401c0650300e006000700f00181307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 677539235 1250 677537985 677537989
    0xe040b0405010306051e04151a0a0f08010c11280c0b0310080105091b0117010305010b01030507050a020a020d081207020604050c121c270915031a0c0405 67
    0x116030107940144000300d6185440b80121024240d903001c40d000d800e90301807c010200e803144100c2140a2562500030482501e40e40900010407030034600c00380d0000e0703200c600184100d01004a20210750000000344440c1d03000c2c2a098440e000101014484c94000c811040e00c3e40e0240641032904008180d19171500305400d495811012505400100480000000307012400340c841404c40e00400c5c0300c0e80240218502290110b44500c092803011400c00c2d041504402540c2c0a03858a80f00032800c0100c60481d03680d01d0400034003034000d21401c1804245090b020440003803084040345d01d550f0454006150022803a070910201360080002522241018800312000c005c12070b4521340140700907401001e480c00c027414039030b08101c6003100507885446240035401c0c0c1c0e00c40200d040c022690180380401c0006a2040c0103541021601000f0000c480b4440d400f50741c1181d82800310026980a180d042091074428070725a00000356601014150445500124550081c80390481d64048003002142d4242981c0d000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 677540485 1250 677539235 677539241
    0x40e030c103606090206090d0821040302060106080a060f030f0201022e0e150f100806190207030e040614090f01030201091e0317040806070206010e01060e040b04 71
    0x914030714400d84509101d81d40000101e07110510310b00381460240b00110810b4541e410680c210001411942c46180840655a401082d00c044400250500d94560041d1510341c1c00d60b80102581038032400116440b807607818510140c50721840d415002404542d0070f1074006d8881c041d00818503115180c0740c10001c00c641e0810800c080c0214414002494800030b14400681001d00b50140410340768800f50b4041c9071810f11641940506001c001c00196511182c0b040c80e040118816011880c18007860174401740d407100100080c8518080c0ca4010303805074582c2502c035110705054407030f08030101d40d08104081d84046a8020300186200341060001203c160740400c084d21996440000f0400c000c000380340d02c0b820318641e05a4018000b0480d100f59605650018040f0701c0903000c1c0c250f01740314801006403100d150f03d4200b8050350300009105c050052041c41c01d40103501c01e00800040c1e01482002c2020507000107485416982032a10f030111580c2005000c8600b140c0307800790181d105448a04040482c2ca50344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 677541735 1250 677540485 677540503
    0x40606150504151e0e15030c0918070206070305070c0f110a06230a09091a1302130302090a02132903093c0609012306040e030c 56
    0x30710341c59201d43c60821502c145025032a2080b05200340a250360f00c2051200402c180035410303c1c107003c08214054800b1450340c0e00d0658200410003400420700181c2040800586510301b4104e42102a04e100400340100180069441d10056400310700414070041c001d400c0f055110f0388516018810b1615a200d00302d4000c81d03400300303444144442100034903c1c01c0955100c005046581403000411000302511149010300a0060701c3c0c50b40f010645540e05845502c45600400700320364140f04c4014200d03925818601e150480600c549010094400c3d5840ca900989020f6840d00c05181e01641c916028881c1c4010001c042e60204d9900b0010000400c03000d850017406000c140450200800c1e10700c0650400b0a042009580419000d00810003440c20015408150745640c0710020388140070941208140d400110384003580703280805140c07180710800100b00d846100d520000340840c820b0005190b00556000742c01c112000c0d884400201c541c00c0640008100d001484210381c648103540340224184a612 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 677542985 1250 677541735 677541737
    0x60b09070305062103030408160203030d050703060f0e0402100509100305011508010b191e081509010b09040b12060f010e090c06041401020c0306070c1e11010804060615 74
    0x507003c2c4049820010449815942c4280c0c5035038013031541813071190307503070000500041600c1400103903058019521402d000c8000c0d80070703040707030307201c52211880201502c021100c000029243c1180000d000b244114148104d4403000c3c0c540946484617002d200002e9900c1c5111f1003400010400c9212949800d0149507401110341d0300028a5410300403801c90b64003000d0558410405900f00501203c001c010441e45007005d02ba172203280c54400080180d422150494002030f03070b00390284640303442d1a0002e08071441000600b41a6422442d08410041615401e010780786540714203220054840c01c0561201c81c000c100184400103400c041c1214600c0c2410481e0010209616000100703c0758a02007d0740e034005803401c01602c07049440101040c040c0c003a5104031a10050811400c07900c0782d00078040510041c802605403606407828601c040d2103241a02c904a031800901071407020044801a141e900d0715900c41005440d02000f04011100290003410550724035503100400950a5200420444040c0d45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 677544235 1250 677542985 677542991
    0xf03030506280303030e0105100e100b040e07030b01090602062701050720030301060f050304020d0c0906140f060306062b09030f1106061003020d060801061505070803040f060b090703 80
    0x66150040646d160782020900b1681040e051103602600164010161915044000e4003a6150004c080340d07585c2642c032503204050000790201e04062005d03e060311603055034074180040d00b1143d0044444c45050f00c102401600304402080d89060902030001560b020882e00101803200000d881d0b0845805441c2100481c0c8040c00400000204d800068400200000550b0075907141207400381100c500c551140f000c2250000000c0c0455498214101c4900e402c030004503d032985030004940104914010a10317404401048691a4035003a0781012120401404c5142982c4480c4180040c1c0c1e0851000720003074900e44c828411181001d068cd0804000e040900428000007908003d1b000d1360b140258007041200c1c003941070014030000079a071900f101003910010032050050404400034011083e034000402d00701303040001c1e00c45054000b01c0954004000358458000a124107440306e22a8100c000c00c40e60090000402003071131107005440e0103000718070110341040d9a40005280708400c81e00340d404030303070303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 677545485 1250 677544235 677544239
    0x1707080f010c140c06061c08070309031103030403170a03200d0b18040f06060f1409090c0307150c0c0303050c1002030c0730051e03040f0303050628 65
    0x103442818501e40c2010242c480d40f50641300c0c602e0a4644400401c640c0c005c24031880000004455000040f81c0b01c1c0c0c00c160400e41b14502c901c0c0081092905200c04e82c1c42c101d400e00744814914020044404480d400b0503c141c40f072240141207079060b0041e4150106055036004024404030010204030070400039158019528081c4078450401c035100c1c000403600030044144201e0740b00c0d06030803149030000d421a0000180064924102d00030740900d82124407011000180080d01001014443ea801e89088500300da607070340d4503c00143d603244d0320048540e041d403081c2c0b01000b040703404003034410501d00240780500f124421622041e008580940c821000200005068006504180300700780766207200b0701040d032440c00c0034009050036024044000e0400b092060b480000900001506440000580c100407130080000501030110b411018003401d00c2c0b4048040d0410080c0c030f90040300c0c8502d5001500044065080d1012001032800400c0b89405c0721000c1c03086005d41641d07402035066550344001c44c080c414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 677546735 1250 677545485 677545487
    0xc0304090606090608061306050a060201061706070e1012052401020a03020705130b030601030b16020d0f030903050c2b1403040209090717030d0e15011707080f010c 72
    0x500942c0c0280c080003200074080c0300580e8089000c9800c04000c40b103081c15131800c60924801400c860307102d00e510400c1880b0000d1a19010342040080302c05000c00031104020b0450a591130f190700301c0d0300b400002e018a8113600780b480c01080ca01d0fa0b05400d8030302824106c40b000c0002d42181e2042e52803c08029011858200682c080d8040000b07440703003031015000f48681583d01960b6402d1a006151103510f01d000d80c03614595141e8014245d5100c000c003101c03441c0d6500c0c101443c104d6401d6074690b0003d250440017a081034000601c0c0000880d41c0d94544414920f04141200189007421044041100030420301da05008204001c2da00c1000c0b101da215241510545000100c03a1070000440502035003007404980200e0300c105481d03209405035410080c6683d0b10f520700d030030b01c226600b00c2a10100344107102408074200001a00d8081c0f8190410804020a0180581d0702c000070000401c442030b0003401400405224803030898403201e03400444d00100c5d181c0304482e08160008880c604c0aa54600401401c3d0f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 677547985 1250 677546735 677546741
    0x5030f22080a05060c031807120c05031204030206070c05120d020717253b060603391801030216031128030801050108060a030201030b0f04020c030409 66
    0x78a400c0e030003007850010683d60749440d100d00a103100b4000001000042482c020198200300e403a03001000e03261303400e03140c1ca480e00e4140407206095400d03807202c0300045024100050610010000c1c3c49609003414a1a1b00304800c6902c1030b101103c481002ca800002d05407502c910503000c54001001800c5408001070b402413505a403036002010040081828108002d0042b80707a10100c10780c607015100100044001c82c08040d0141d20001183c0b95040000c40051070000d0f02d0b2100111000c4070020850b80d0a040311580981980c4003648032070200003048101c80708664000b01d0703c0744940c84c0c6c0714000c2d000728505c00b0059800184254041c0001c3c40c3d40180181003080c0854400c03d007011810030703003181d204607000c1c002c03508005e09220240c401c20050300000c0048030319401c200c41d4242265407100740c034080744408140c0101e0100b0703d060000318903980140750703036032084001420011000780785800460150100c95441c0d50000880700c000700c03541d1501c1c001070401100c6640259521880e0407041d00071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 677549235 1250 677547985 677547989
    0x3070b0907051c0c0f080607020c0a06120b1503150a050a12080a091211040b030d050d020904140907080f1c03020d02091f0f08010f06050705030f22 65
    0xc1078020040034002652008040d0180104845603904841d4083c07404150040d150b4020700000c003c048000180c608000540074400e01007a42070f1611100b25078240f12170f44d0014003513000890325040301c3c001ea0091a61044150b041d000305481030070484042c0e582e0142c1c2c015030340c0308003442406030078034001d0902260b6040145402c0d500500e12503e000240c494144100d40700401c0c1c103c002070007441c4148074201110103040c1140040d984440d251410000f40000c080351980283d0920184a40f10711307001c0350300541100f407602e96603d00440800030800035400b001005510070b65882c6080a10421505001d2040f8408001080e45508000c101d80c42e104002142c02600c2e805403552105d000340d44840d040034100c40d0704016031105000070080300640942c06605411907520010782649200a01c80b89111070381030b4840640aa1060304202c501c58000d0103100c0c400b1341400000c0201078492801001742901680940b0700b084007100c00c4041d07591003042c4184e580b00031144010a500c0d964128000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 677550485 1250 677549235 677549251
    0x1415031218010903060513061419020a260604150b0a050702010c02090f0703060501020a0f080f09130b040b120c10230409060b0f0f030a11070503070b 66
    0x450003908201400c0e00388901d03000c080c0607460100701984503034003c000040103035a2000d001e00891400c000210365018104c4d5080d80c0700c50510342d405d022820500000707400342d0a40a02c11090100c0a10032070041d5000e040420700700030140070015060007500d0311350440d81c3c10f0b5140e000340e02d04004040006a40300c0091142c821842da19007088010882011030f401079aa80c1000da444128600040c0c414103000100a500003000d041000151651441254410039030381e10700300806903e42004a0380c6170380003000104003980048540010407810b0014100780d95200704440e150a0340e04000c140c1104601241d00c14458440c244101c043c0f606016001ca0b540040c1c13152010301c1d42428150b0340e02c006004046000300c2208410500140c810000325108400411f031590038024050b41d10001c3d41c1c0103115000b03400e803800130080345000000d011102c20403400081542080d0a580c0e1614240d4805030450079501d41d00d501d20503c0c514a1000341c8083e40c00788020b1501c880043c1413001000e030004000074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 677551735 1250 677550485 677550493
    0x203032110240c0606050406090209030607020d021e010e01060315050115050904050702430803030c0f090a09050603060f040503041701022503120e0303070e040906141503 75
    0x6070800e007208101111202c01c0c0b404041e400e10b5802c10000500700354200e1a085801c010010a801e00c20780c0050500f034401313400300d41941d0359503601241c9510304242c2e2080181c22904582c1c071f030310b6150990412840da56400004216080610260864001c4d030310807070701d000030740509041e94012071155900604c0443c690390340554800d1002000e03482040030080c402d1340e88002040d0030307034820801c0442161806102c01885d45214010700000c0c09941501c2c0340c9a407070580f1100e480e184041c442c50450308071030700071070443d1290300091149411400c01e00d00e07081400d000342070a07642e680590000924400500207405d0a11000b890704141d00102070030040003428040c0070018a0010890301241c5812940380b04003442410010302a200300c40781c1c40412100088942c1d180c81c41080c03c111194441d4036a9001e0061201d04a015500c0c0c00b0786d206a02e42041c40010103087c020001041009801000001c0c04500c3d030f41c9680480788101403044a004c00c11080142c0401d24400041290704110010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 677552985 1250 677551735 677551769
    0xf1b030604020d050a0209010e1009020c0a1e051510050d05100c030f09140c12060a050606190f020601140a2c0f06030615030d0c0203032110 62
    0x826036441010340020300906079600741c0c41c10701c4400d00c441498940d00400e480d03042d503517841001c0c100711000e450085803240c2d40840018085014800c5840d00c0342424050f1002401c20384464401d00c402d42c811130200c090221142000402c2804450000c40000c8105903460400350010780f00001c040d0400da010b1a110041040450700000e059a84400c0074580070809000d030321411070240507440100700c1200c0c204134451040000004181d80002c03804011542d0b103031500401c001c1c0071401da0700c031803900c3d40100004c105c6510503604515400103002d03003c10300c3d140400c0c07106070901c0c92201d028030024081e0100300c505903a040c080c0c50f005081504000c40b00c007900c0c000083c00d00c1054412042d031940444c04450245502061070a1061600e0118444526003990440b07401582165401d100b8000e40002806a46814152008030000a1b0040484200101051b43c0c4d40c0c15007002070f40c0c140302c00c0c420078121020252030520f01c02103060102549007000350440e104500d07107810040885031490320b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 677554235 1250 677552985 677552989
    0x3020a06180f150e030c0a050613020109092003130b01050108190b122e051509181009020a3609080304080711040903120f15080f1b 58
    0x45008156041007580352010784440c1200010b0220100c1315503140004a0a2002c020010070b06207840c4e402681a9401070740d0350700000c808030300d100c480240496008002440340942c1076102c02408500c05204100e584003147c519038282e0400c031041903039251000e981c07004003c241a1081d00515086c2441000d60074440040246801051969500b45903240a008603ea40312084512008000d038180c034a42d150311007d0444d41c001510511662006c168004280000703d8802c1522401c98100c894221a0301c2000b0022000c04c050030503036030920f58908070003002005001d040405c000d00000007440011500c10b02c48140b002d40d0000b014004c100040b640c0e070b0301c00c03148081e8a4044040840032010f00d803419410007071082035806415540701108100802078503400809110703014099041184200d0310030042900d04444004002412816403807880c1c030000e801550645d83c01b014041140c1d80c0342039206040ba440c0f54021607103a1702100410300e0f00c0c0410311040e44800c0300c1190f03084102400c500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 677555485 1250 677554235 677554253
    0x30c04140a020c0a0b07050a2007032009250e09010e0702030c0a03050901030e0102190e0a030203010f0f0507081e04021f030501050312130302090c040302060703020a0618 75
    0x80705518440c0c0014444410b01c506000007039800d030784480034224504000100800c00c0c0c11080448012400c840b0f0030722095469070145490045228000300300d003038119034650030120034625008071082400000f030910782e50352000c1e40384038403400320300541841080340f080060746406e00840b40a0084001103003840752a060700c407606440320200105810348600404920710320074210328000d24010f10340c1000805901400412401009907800e0200d20a8551210b00b00d01c1031150516000702d40f41f200740b000c10700030358000295100050216021980e240c010a081d900207007039006049950b03508408610076684200ca0300003003a460811181e00e04080c1102000304030b030348041c1210315820001802c40d03851100c0046028560402d0030f271348407105003019010380400e0107514420700a0b180c000d10300203203c030705a4000303200f120829a01e0034555001d1000e8a10041c0205c250407a04010200141c2c80e4040203088280c80b1781d0042c03000180b2070074030404440d218402d003c00740d59011422404142c801d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 677556735 1250 677555485 677555491
    0x3061125030f09031e05070e0f010e060a0e07032c0705091807032004060806070908011a0d05010e011b1418122b030609150b250c05030c0414 62
    0x10505c001060344a040042c0f13004040e80c003040e0951441010409c4549d000d402150403110031000c04103880d141d5400704102e10160340915005460110000703226540f113501b01b48000314000020020900426450b040350801c4940039081660090504001506060303018540c0089807086000741c4c00c1542607416141c0311984405000301c881c1d141540c80e00084980c01d00c810341001413040120503500c890b00b17512020102c5141001c50443e01e400100350707506019030b41c14009070310f01a6031031001c0042006001d100880382a0741030366030b444481003104024410782c866a4400284a0701c1960b00c480300070724002d049059041c60100c140682e400d06607080401340070351101183c0c040c060020000f43c1d20300c0e100c114801495280c90410b003032040345002c414641034031071303050f5000e1103071030380b80d0b00c510b02035a400100e006000300740e04070104001c543c01e2000d0304440181180c040c401c0001c080f4002c01c00103400380706442408982d4401c000500d42002410704405041d2014480e0305100d4407030a481050007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 677557985 1250 677556735 677556773
    0x50703050c010b18010608070e032e090b19061802070303090b071e050403050a02010e0303070b09060a0e01091119050a0b0307030c090305060103061125030f0903 71
    0x100c0d0141c403000083d004014030003005410f00001400f94404620307560028400c49011481440118242c40d22801c414198587c0240041c041200489404036048207030a1641040310141040d0081c07030700241c05402041800350054036072a0500d50004003001e0302000c0d180340d0b00c80c074000040050b204c4000c036400c061007a4502c0141c584646080c141c0240600d81c0004060443d407170100840c964001c50710038100015050341507040056601e00703039200d1040d800041c010390b121391042401980b00f01003a885085014065070304010710ba98440c0680d80040e1000d8505030086010015003031217611842c1c0c2c0c100d012100900c4402440d07180e0010104210741410702035400061244001305141f40004010580a00000a01640e50b0365154158000341c542d200040d0809951101ea140310703000440560f50042c000c0c1c80d0592135a0745040c01001c510308520386130481030144812138000341e50038245140800036448003180710740c940102807400070007820b0280521a1801e1010614441010b0712034081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 677559235 1250 677557985 677557987
    0x50121060506010e12070e15030303040b040501110d0c230d0b0f060d0605090108060106120c030b09040b0a05010e070f0e0409020a0f0e0606190806120609010e1002070305070305 78
    0x30300d400403125201412004e07a0441004141c01c02108000685581102e005490314141d689580c41900042c02c07a03003002e141d1548c420b10110340400c8050190340d800c144a6000001d15001504039412150440c9490305000390381c80d003015000640250507110b00103448805400c0c40c2680d00e42100312800b03081510201140d50380c1c168540c546600c40c608489030fa00030035103516410814080c0e006042180915402546080000590281d0015043e41070340c905031140e880c2148147e943c40c000348003c02c855020540c42d105801c0054892580e890300550003203c40c000c861070714000110948006070b02c81020418031000304142d41d07620101342105030800e07161000e1038005842c0060081c2c43c1c0d11401950001c01c0040009150a40503205011130300d4210580c1c0702d039641c100400815001d00030071410b2a14100003c0c3c400d05225014003a44440004c042420042c40b100304a89000c4080b500c1020681d5603501c021400034040220101030002048103600e4205250360080c8640521704c401424800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 677560485 1250 677559235 677559241
    0x91b0415091d03030114030c03030702030c0d03030204030f0b0106020d0207060e010e0604030c0b03071e050409020d020717031005030604020604050411040b1315031505060904020f07050109060501210605 89
    0x5186210b4405800c1003c8980ba940c4544010160010048081d4403034071400402c05640c1c10f0100a50364204e030018090541c1c101d840050021103080e03075100b01e08055080002000203100b49004040c400d000d804c01008544c14a007010745081040d40b22403042d5070010604200d41c0350f120345800e001140031b290040c0e40241d0000416114061904003c1031102102d20100c1c400343c00101440c454003440d070b00c0c0450300e040da640740c01070034005420820000d0340800c418081c5061940081c0381100b07031500014a01007481d2182000a444504002d842203000010320400101d202c040c0e02c041c080860140c07915003455400149a80700b584101405180c658001444104074002a1401000518021a0f98040c1100ca110214295000b00b903c3c12a441c600d5016584c030a10a14150707241d240c5031012007904000800c00036401c21045c169200350200019590f20b00c108000d082079520440000c107c4a016180c1401920416044490f50008055084002554000464070216000440042c07591 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 677561735 1250 677560485 677560511
    0x5061612090501050402030d0512010608040c050d06050a110a0e090c16050a0323160219090b0f010302030702190302070b0304080a090b090102250e091b041509 70
    0x40880d241004900c0d2491140901c181074008620031031080303098429104151105589a000c1c007105003800140c6200188086400f1f0100d098010303014400714081c1c60b40d6280010b050001410003128080e888600703010107100c660017a14a0600c4001030303c3e060038007480e0010003030508102c1c010712800003900464100194034044400742c1c40d02e40300000c000c02c5103080c120354640c001b03441100000c00349810010358800d131904c0742222802030000140790800c5601245041169260240d0380711007040014180c0312510340c2c60f10005c0c0101800803a4000e020303000c000b400300020384800d040c180100104000184c2c00b003032400e4081a10002c2003107244003070074200c0c9490700a420284c1c5c0490004140000d0199a402034a02002075507201c0f410191110342c2d0103220b018118580c3d016900c6031f40d00c82c1e5004010300c90400c0509074581c803a4561507855083c0c0800c02000d4440c6004ca402c500020954540418003000664805440030301c031403080030702820501c0380d041c400c1c00c6580c4e0f0307030380389800c046 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 677562985 1250 677561735 677561747
    0xf2d030c060d2403080a020c0405100608062206050103060e06011b0606090c03020306030c040c09121401060303091a04031a0903072f03070b0304080307121e05060607050616 76
    0x3e80c10401c0000d1610344900c2c00941983c480305541015100301c18180700c403860580506403013100c0c100d03889100c052500c0801d4800c4500a40120703480104e0308041103440408419003000b000550f00e0100c0d0013403506002400b1143c1c150020110f81079048200011030740c0100101c0c04034a1304a00038000701680d420908000e002e1508601030260800d2a8503440550640144d03014050850507106140d010504100413a5012110080032030340503282000208406464464110300035440c1c0c214144245594908603040307600100c0c0401d0200d40c00b44041002d5032610410050340302e14040c58070f421070712403070382c04440174000c00b8606021800060b80e1060030304c20b94110f00d43c4903184111070716a489500c2050b81100550075003c0c5030380300340354000d8900000c203801113a4201d1000e034519240d03512600180c0d0b0004002070240040e100300100102141e00c41c46040014014a081d081c0010107001c0054540142140b4800c81c424400e8002254020a000d60020110318420000b41c212080c00d07106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 677564235 1250 677562985 677563031
    0xd09181103062b051509010e10020906040905010b190504080304051c050d0c06110f032712070c05010e060904090c1809060e060408030a05060f2d030c060d 68
    0xb80d5603107002d0007810003d000544450080b41d0001c07070305040c6d8610017040d08030f03140c11420502541c0100403543c0c1609490f030040c00c003510050400c0b45025102c0c0e40110588200b13901429420307200140f0070303503541450303401c00c1501d0440d49480ca2801e8541400c03240d6034011800b17400e114491564610191007100c1088910a50740b000c00c0d60700e0309030304a0380601004020f940035500e0a05103441076914405103401c484010881c5040207046454001018640c0840c5000c507200f000d164010101c2048002c0244901030450003008a65500b65403815000417801540560305000d2400c000064942c1c032181a00c1c50040f0a460000302c28145003004400cc0c400c1c0d41c400ca40c1e8a1f04c50182c805166480e400c03a907e1503006c0d0340c00b4000900d019082594462040350045c11251051006c28040030058001c180c11450040419490211440009995140294001c0728050007001c090004460000c40c00305006822005068002400400704031213108803480001590b1b40d034080303c08880152100040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 677565485 1250 677564235 677564299
    0x507090618031e21020d11030d060e070e090601080f10170d03110406170703140c1917270d020313140a15110d0918110306 54
    0x3003820400c03200905030101081068849490003c1c030b40e030511351085442ca00e0042694010000601000070845450040c04043d00c0c0a020802c00104c107090107008100140c1301c210a02c803224201180d002d008092101f000d503008094400030800c407130382c01c1407216912401ca00b0411005a03902c9000c003218014030f4014515400b100180f045881c00005006461241c050301e04200802c00d1041c81001e501880c410710b40020381d07010b40d95902d802c1d00c400c0350390049800c1c20003140c0b4030f2450254a0790280d0440c3e203100b08100119803250014204003600700c8e05101c1e41091060200f8003075400c42114001400301240100312110b141d088d01a20410003c0c40c1d0001084d50703209042554000d4483c0d0201180c1d02e0b521050031004105480c64180030395600c40300070301c0d080404d0328007640c8015511810b06408140481c0e55944040392405101d042841c0c01701c0d9903181100d5052004100540800200112425140900c201404200bc10840e50089801c542c8194a00520166100d440d01c000120754 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 677566735 1250 677565485 677565503
    0xb12130506060d230705040c02010b03060406090f0803010b1e160b18061807050111250b120402011d0319020f13060f120b130311030408070503010b04050709061803 72
    0xc030900d2004203840007546c200b103d090202c0c03d8842001c038242c1301c02d40c0c101c59060301b101003ca000581d1980c00845000c0c8207020440c81040b80351140c11007500240c2c00715008060002e16041c2011008214214885001c26240d0502d00c26400d1441001c8509000038201c14860020500003009400c0300e900340306804e0129452850030b03214250301d243d481a41071b940c901c5907000c003049940c06241d0541030301c0c00300e0008191780f1004484e10800c1c1240707240c40c0c3d035902a540c80007103144c40a107002824448103041c0940520f00b450710004003290803860102d50404241c450810080d81c0c0031891440700780f00b00052815165480c000501180c04901c0aa5030040003076004916480c1950400e40c11917441104507a4a1b50340e603c01d22005000145000300019500c000040b6101040071507000018001c0c580311070014013900d0381a145502c0754028a0096202c0001004a860b0034020b501400c03800313840c14809801c00a602405183d100e0062405100000c9000356000d410f5904000003103411501c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 677567985 1250 677566735 677566793
    0x405040905150a061a0d0f060902090102072907060216050a030905060f040e0a0b0616020a0918031d090a05041505091009031403010b12130506060d 65
    0x2281e40300030501c400000756800d82d0009002c0d00b00c52107054102c41c1d0600960300c1004010760310148030390081c1904080941d03140121000784034144110000b07040c80c0200103980380800c02c000780c81c3c40b030a54411400d01450241c1000c40c0e240d419040f80101241103a5243c8491551410700082d010b0300e50201036840e80080d0aa0520600081ca110301c14040d84030244d40d680c48100740280c900c0740c0e0304408071202c01044200300c04110161040c0d40600000310010700b48440500085103a4070803000c03c0d00b08012001e480b01945000340c203d078014080c28030200b003035645000442503400300c100d00c0501400040b8101c1c0f21101c4c0118a00155070100130071414452800921840081200b0f0320280d5002e01c00c00a460340b8115144610f601405104004002000745108040050010120708404000c40aa001402a510600954047c020441c0c40e1070302c0d0029540301d80d8002e04000d15a084284980c0c00401c0400c030041843e03074100b402039940d40304c200440c2c2800f1502041c02024503034060000c0d050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 677569235 1250 677567985 677567993
    0xf010602190627020a090209090f07030b0d0c2d050f0316092306010206011a090603010e1f06050706020904180b06030d0e0f190305030c03030613020c0309010806030304050409 77
    0x8514043c6101321011413403136480e010184100e01513500001d40081d85440407881d00303400c041640d58002c1c0c01d498007040d4030f0344450110360400c094038400c0710003a400900038010340003828000d03411284840360000c00c1620308083c04c102400144506170244516803003000c055102802031031000403400803022022550703008030b40c0040100d40350742c1804440c0100740782d040c0501e140c200750148005070f004104503420a0442c42c83e01c20400c03d646080e8000308206c0315681c50307030070207107000f00038526156140345803603a0520f80c1c520380c10214600b00d200c403100a00009406c041650401d54002d0070050300c0726403107000318006020204040302c038240b131000b64004204812a0047c403460301a02030b20403a0790352400590304000250a00d0b68454179513045060309060410b219003004030542c001e48002070f56910b43c0c0e0f0440e4050f0800004035040081000f0050400840c081080c6140d0081140340440c4440956124001e98400c0c9040216900c04100e031541c04106460103008018002c02c9981c40c1464 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 677570485 1250 677569235 677569301
    0x19090305070b120610030b1203190507021005030705090d0f03020c0411041403032503080f270703080313061a010912150c09030b0f0106021906 63
    0x100403142445403a0000c41c4008480d4103607032082207055000c035161348840d010000440c00e2403d258041581d0362551011a640ea8510140150f00c1e00c1c010799504c502a10802c0690030501d22400d0500904000c0c0100680f075100001d448204d503490300c0c0d41c81381c58101084801c1e00c0f035520f072182d00c907508c0f400210500038101d19001e4140c0c860340890710540006402c1c001a00c00712405a40d90040a000400c118140389800e00404200107007928541011500107280840c8080342d150b94a1044005400826030401000c23034000e1b05414600c2064900b44040b1152208084042000c0d0b41c4d588400004e42c04007009a100a50b902c9000c50b0f89900c0d0940c40a200c0c101450025a4240e00f440740e501c4049114080c0b6500c1c2c40f42c103030744295040d8104140c410460b001c144d8209c641c4400740001c2d10012a2522034001541002c0c0e90701a0399500e541041062488003401c0c502050314000c004100140c0c002400d201000c2841d201d0403059243c42c00c120b402000c01d288a9039200c0d610b280c41883c0410904 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 677571735 1250 677570485 677570489
    0x7060305090c012a0f020a08010606020d110c0f03150415230f04020d080403150e15012612030a0c02060103151e140403030c022e021909 60
    0x300d030626807a800044540705030080c0c20a0351000e41e04030080c3ca090490895200c2c84c0d02814520f08060b403039a01003102d40465902144291b55108428451039605014400910309140b8004c8040140d142d0380da92940b00a100c001e110f5405200001401d031800c0c412403440c9186608010080d1805040c900309101b904503004400b9890010301c0c188103030020890545810703c000c1001803d641d48104440c14060140c420b80c0d01c83c8a900f001c0d000103034244014000b41d84600040450200c19480c00030540c1c07812519284230f6040030282c00c0d9160780601081d411107600000760040c200150401480c80721241440005900550782031020030100e5800441c0a000c05440401801007030b05000c0381c03035020030302000f0110170034030b2204402c40503d1381019407400c040400003030141082a2840c01252180480c1c214560b001400f08410306802d4031070b0791178410041c0050321480e04440400f82c40540074080c5200c080007000030980c025001742e41900c1844154041a02c0004840200035041710700034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 677572985 1250 677571735 677571751
    0xe25030c02010b03160e0703020705161811032e080f060f04260909040501050a0e0609070303080c19080a0509030a200f160302030c0307050319031107060305 69
    0x1102030700013824005a020349110038600d066084a04260a0070040070000d03098504244e000d00c40e2002040091025540103210254001040e5252051400703c1c100200f07880340200d03240011544400058004480d0b10a50420542c64400c040c088207043c04001542c41c21019188802c02154515001501c0210846581c00f00c0710540d0340c42007502c05034401110010040e402e0704240442407080c43e5000d003105207160300c82070300708240c01001c6140500211815500b981d120401d02010b1500c80c440d6010500d64100a4845031a01d03198550703a0340b0f00780c4401010080f1800c0000d0104170351b00c01f40c8481803404481006d4848903e00010304044003521f00b4030300d6900d490007088413040000120303030320240540c60b03503014481200c03080d4060b0a80c0c074980292034040c0c0921000e8a00051248550050070000300108060440c01854544100d00740c055000c0e52011006100c1a40c0000300308851141408603000048070a04e0111001040084440300c144100c00300407441e550550841c510440b80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 677574235 1250 677572985 677572991
    0x31b0904170d2009060901230d0615020a020906010e040b060f2703150403020f0d0906020f4204031d01031a09100e1302031203100e25030c0201 63
    0x71040b541843e82c401d1450302640480108440b00031540140e6100007190002c0c90030f220b403c0d01003030b0f0024165008908440c5040c2c0d59a40c140321549215219210100c81480240300070310850307010400741c0354058552810301500d4130310000b803644c03a6000f800b000c0f0400b0304141e4440380305074590102900507800020b0806c104001482034030701c0307062824072514002401428244a11400c4180090380908240c0441c02111034119004104000420004400c0ea0714816103034507024000381001001c0441c80e145400100031102c801c45241c0c0403071100280c9842001d51240701c0300f03506161411107461203a21850003c10031007896040021000071099515582062225081c01107046614011034a20b4100c0c40d00100012400c0029020b0741c020303903d100341b182d2280c0382ca05c2d0180d036000441d4411071640002c0c01c42c404500b01400300750319000f0f00c04406411410010800c040c014200d00030440d402e040700c400510410301503481005222920040c100f070380102001f008025000c0790050101540c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 677575485 1250 677574235 677574281
    0x60e030c071d06010e04020c030c15011505091005120406061d010b0715060f120c0602070509010b0f040302060a2c010f03020705160602100605031b0904170d 69
    0x3a002e000701d8014030390704410b44480e54803400152500d0071008912a045030f424044140b480780d0802c0141103003e45440200305561120054980860b81600a07080d4040d1070303100e060380320b60458180c560603002150f10b0a01425492411545401145204500c0000303803014802440450390060081e0340c014a030008040000e01e43c1400110320070f11400d01012000c016220116001148107041704610207808240c2030340d14141500001100d03000b8550745848115001d0401600841220050180340058101c0c0e91410001a540400500c2845400840001d001c215102d01c407040740e029640c000c100c0342e02c1d1840c56000800000300340e0400304201e2000d04802002c0c1c01c03083c1c034205d0709050581d100030001076140c204a001c2d40103000c00b12001e20400348100185040142881e0141c40158001c0010707105000e036801c25124150f0169009400c0f200007a10001e5101c1e0010441140035180e0b00c4035a11135103000010345a0b881445400c03141c01244400b14040c1941101d15082070390060b80311050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 677576735 1250 677575485 677575499
    0x2010b03010c0f0c02010e06030c210103122727090804060c140304032109120303050403020f160513151202030a060905100e03070201080406020c0703060e030c07 71
    0x542d5904a400209042280b5400f1036440313448207450f281e1040c582810050f100902041ca2a001540e942c0122000442d040315012480441031718055a41405c2070440d516540710100d5141c42594008100910307103198000300c1b82109883d201c00344103251000e1030326556100008212244041032036061841500385400d91806008200265810840d4039280624100b0140c1c1c02c2410b601084519035400c4131004a1200140050f10086009025a00c5803000ca003014004c802d004c01c1501c4180082c0c00c1081c055510451140080f00d0380c076050006003a19641020391038072445011450302d511070b5402c581052559004400b0441d481510108012400e9403000b00907510103e60400c81c2c0c0c0c10b5000704000e92505a841020142c0c009810b48968044c16124982070711241401500c45d40e1080c1060084114184600303c0040043c0d406907080840300d5000822004010700040c04464003c0741a407444941400f101c2c1c02140e1002e400c001c81003104004a40340d4012008144440c054410005400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 677577985 1250 677576735 677576741
    0x150806040c020c3304140d0f020411090907120c0201020a08040f0c0509070c02030c04020306090a09170a0918050603070e070e0d06050a1d0c220c080702010b0301 71
    0x19601c1d0080d0950300301c42010700011035000041e4043c0140002ea0f00801d9813207201c01150380c041d000070b21956803070412007a02c032007840141100f17004400149032400840e05d5154548443c50741220042505405440e44042c18010340e2030740340d0300c40e01c108280191182c10019151401100000900c50008900d405901300e0041340140d101081900c0002000103000c1594003184611604d01620425212000b05402010842d042008156032503c49025403500300011524042c2c00c9400350710b140380c0310303011039900038015001002c6203840b0501d040c100031450344d810000c0e07080300103002d849048402e402040c2c11490710900248800c07007410300c91040d4190207058803421000d00140300341e52801c0d11001000ea00207000c41c0401845080d18002c55813a60651600c0600400010984c0e0034102410f5086405400a0a80004880b072609000041c041802d250048084602c1502280700104000c1e12105100c4001c101914007440d000c00560800d454a0103414254020007031240003105142c22 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 677579235 1250 677577985 677578001
    0x20910080714060f0a0f11160506030a060812130e010b0a0f0e030d030f0507080402010e1e04090308070807080f010b03070507020d03120c031a24030115080604 70
    0x680081c1d60900440c64125504410600d010300210302c0c040c000901c80c1402d03000041d0510001d829541c10382061a03010300a00a000180c4c4050180031403010400c01c00d003581c510440740514004800206c0200c9182d000c403004100b52816660000307080c0b14407015a0344a5900580d07000d01183c0f0120b1807041001c505410307298080d1007e8642000f08006a0f0a00d005000000030030141e003001441c20b031020b01a00c1c0c40703034400d17440c00701380e480c0c40388003880030380740010444810081c6050800c00540e900a41040b8444c0d41038030780301d151140700319410441c40a4000381541203402c2c04024410107a0000342e0700c1c42110746541c2c00722692a180e104407040041038a1040720010984014411303500308100440e044189810224508a019804562480d2910b042980400c1704564440800c88035030080b60384480c5e051804025002041200c01d0f01004031146450007521084180f210a82d0480700c1e40c0c0205042140023900c940c1e591454511001107491030740c0000d81141c01051941c2001d000c0e04031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 677580485 1250 677579235 677579249
    0x8030c06060609060409090f12030c090513180b09070b03040b0402011b0f050a05010e160b03040f0c0b0a09060f0816050d09030320040f091e0e010207020910 69
    0x1056071509402c00245800020314640d1207101004006405140c6104080c4154032401c4c4070369103031071542801c101240101c1a903005160130f014918180c01e07030007500c002c1600c40484007462002007082041006203503554000c0c4c2080d89240c2e150301030081c6000380d140714200d10b00441c0e0200e03890b1008a6842e0000761401000c01000c140400d0045d0b000780300011901b1071000a110400c41152200c8440c0203000c00162500e800900056052003000c0c0100380e02504907100800d00c20300052040c1805000c1e13440740c8503022601001050402c403200c030034001e034103401200c11480c40d07844041920580d40302c4d015010104030441400070f0f0b103070301038041030810b620709817a00525690f40444034900042414401f00400a01700045c2c00f0a480d00c0c451038510900070307940068055002c2401801d00100c0e51210b4400a101744001c1011030900d510341000d5600101012070000b59448129869806074a50400720706e081078035032020740c00c055029280d01c3d030085a0180094484041295140032940a050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 677581735 1250 677580485 677580493
    0x714010203040911090904031e090b12180609100c0c02060301090e0a0b0915060a080a1202012009010e01080103050d030218030714010915050307200f1608030c 70
    0x34400a9104400141c135610410b031074580c02d007000850512045800f10082800340c000c1e80100c03061070000000c003201900b4481c003414100340310b40c81580a1540c10b003e0542d2890001907080001c654110309000300c840031140f140c14505421070710b6880c0380000308412440c10000c10038070740c40340c2c40004400c2d402501c0c2c0d83c42c50b400e10305424041d040410102c401880f0301440b03540014000d50344144120008405004860301c0c52101201d0008081c004610030300f811340c0d09108042c404140111181d03400040844858005032003a80074110301c079030103583c00d5107951306000584d5600300241406071090340c1d0301a55440450040d01c4200003804040c146034804041e4043c1c0038081c8d40208510010020a03403514402c44000a1074110340e80c06c80c1c06842030180c202109542c1003817014000e0320540418880c4100740e500024140d00000b0540d0081015907101005040311001212108800384400d589081a11064296a43e0383d02008400340e8031a010001070000340110584e50400400c0b40a8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 677582985 1250 677581735 677581739
    0xc0203090d03080f1015030e010b090f1006090b030a0c0c150c0e041806020c0309060408012f1204020a0914190902011e140c0c04050708091c110f01020408071401020304 74
    0x114000d01c882391100003250360f140c44020f40d55859051941c4248504503d00030070b860036441040c8801039070352040043c05590b400a00c40d036000c0a007540c3e4130009048002130300c120748030400c4625419408018209001d084c0105001d0f09098205001e0700341c50380c459110100300c18080c44211400001425640900c0b094a000003803440c2e002403500310013035000c5030f0030705072150005581640b00e5803040000d0b80d560510451100340784c030310081709009840341e2a40049981c1d031103d1003501c24001e5050304490700d040060304641da888000300103046840b10400c43e6032410501410322103002d0b9080110302100c2c0001ca10384031510301074010481e6060351781340c1c2c805e0b0019200201d4143c0c1d500304d09050041189030b555502c020103020700488a00d090003000000406001e02c004c40d040601464204101002008280c0d140014a900710f411045804902c24001980403225040b9031088682d890044e0050b600145005402500540c2c641406591a0360717550b4a4204541e407039400702501682081c402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 677584235 1250 677582985 677582987
    0x50108130308151e030105010b0702130f290405153012030411010804111309120e011413060c05070f180e0f0601090c0203090d03080f1015 61
    0x782c0c0d5007000005811011680e8000c1c000343e00040060030124461070710413040f03009860b090198034018901c140442d460824039030042038950088541a00f07841e5211040c0c913111a0682e840085540107401080c41007506e4084550200f400c051a03031031185081102003031070f0f0b800c0003880d051803050003001440780308944426402c2e0840000902140d504410414000d03090b800c0c481035442e9451028500e64a14052402a14110b4200306e801e0401000e6410000001c90154040c0d101200407a078460140c501000001d014108500e030080c1600d150f4030510301e4594200c403266042c81400d0700c550301d090600c1c4040289a006114045455010302802040400c0c010f00c101d102c900c0c02034060758419030319001e1500042846900c0103840c003040019100c504491841014008600318024241504004041a0740e8600c18011040d0303c50796001d02c103a1060080048174500356000d00b0002c40290203080140440b01c040301d5010b51509040001030351641d0f841d2034501541c00110240c500740000c068 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 677585485 1250 677584235 677584247
    0x10c03110d0b210304180903140705160f0504060801050603060609060102070f15030b041b27090608060603030721091d060307051909020705010209060f130501081303 73
    0x1010b40d403c1142588881001400f040809040355008001907968628292050082000c3d102c189000c003468406014002a404840b42041070328905003c1d4a5007030301d040050502c00f8249485a00c00d01201000034801100c00b110803c489084404010460355002080d00b651012140c060749078002a000a01d2031038440c03200307500f20304103204a49202c3d4607001d4144403449150402450b002c0e00e0f0300346654096050290074918407058809016403800401c00703108990158070903005102e120000071110401c01365204d030440203104614454180d48444043c0108200e0068001d503000e0800011004d060010031108100d900c00d81941c15980d03c0d65411402c210040d006404100c42c03520b00044001d0803500541c0c03000c4a0007102001c42c2010810140340485540c0b2007409206042c54500c2c00300500b01c1141c4c1100d18410300540e0720403080c6401c500a200e405010b0341e01c4200803401051910038540038156000c19607000050082d01d41c401907030012422500078000c08681701802000904c03c003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 677586735 1250 677585485 677585501
    0x11030c182427130b040303110f0a03020d23010612111b0d0305091f020409060303171f050d060b030708151510050a020f011409010c03110d 61
    0x1548a900e10a120740001d6061011610340b4201c120000d05951101468000c0c480c0c1c0003041100204081c120540d20300000d040e000300080d06150f914003001c0c510b0114101150090000903011595650701c13044041d0007500f207116002e044900d0a09000d42d0540d40c02d040605402800d480f603049a8a04041103a9603510f04400391500c50700c0d00c100c41805240e000c094845850500c4407000f07200440320041d860035582c0c1d66078204250902051000030200801c5244078400e0941d44144034030341620790040603200d15440f02860750b161500001c00d060741314040c800151030059078415035407510030f5604100440c5220f070640c10705016108000c1072415440ca40d03035403031080102244c0213051100081c10710700c55a2189200b50401c800c0b41161000d040c00d001d0717000388049856031809040c84080744e02c90005c040640c050090016560307200030b0081083d4409155180028841452030308003080307020b88142e891140703039030a006840d166603001c1d008504105403010000e6082c8030070490000017902c080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 677587985 1250 677586735 677586781
    0xb09010b18130609060b042d0b0a0302030a03020616050708120a0f05010f1403060412080402190f06090e0402010c021c02090c031f0b070308040305041211030c18 71
    0xb1010b810004003107000780440c0c203014884c00101040c241c81400265850b20001c07102615102a40119004541040c01d04450b0f202d5000140c2c14619001b1418600c00d54202070b605101d1680d55034109540082e9003481885461900405e050014006441e24064004000c0c8464000d01221100c0c4500039452944018070700c0001c503070058800440011140b007a0400d034410044480300b8013400d61041e0b21f80803c4542a8000c2046141c41d03183c142c0914644091881040742007004601903503500080c0d04400300c1c8611803a8043d680c0c400c0f00b04403001d503500c103c50214650010000c3c61007445400c0d07600c900d030182c58000c5010515809c11409002c8580407007103041c212003c220144e2560903034a48680c541d1950380d5a6400c10449510800104444102c100e0400d0311060003680c10340000c0d1002c031035150600c01c1e070b50349940c0b400b6111401250421030301e14568600c81c03000d10151404003c885241601a50900100c20041c00000d0903050850848060800041403115411a1440040c5689 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 677589235 1250 677587985 677588011
    0x3160f0903060c0206060114070206030c030402120318010905120c120304081504020f1f030203040224030711070f140f09100305010506040b0d060506012a0b09010b18 73
    0x1e03642d440003203421901e20000140d2201040120315600845440040d40782e0100b0103007801841d600154561100a02d403140014001c00854115141c0403040d6441d503042c182540d441c0c4c0c9003812041940c0e0301004002c0d00040c0c911600140303a09021404c44d074404220005415180010824003111030b50786003400000c0c0c4420400000c440708140001003500d411050204001d003041e004110f1050300c0341094601c190082d03040101f400351989070a0b0020042030030056220b54a900004514102c0c02c08403810101009881407044650040214801c0b00c2540300c0c0c100806291150700c1e582e140314040c10407110030100e0103008521594600d000b02e120000c09080071000c010340411995032040da0b00340781d100e070350002c28400c0250038003d56900070019a000c105105072800080c0c02404440070140c1007580d540e012420340d0348541d120001c58810050300260703034152114100c0c44004441d805903041c12030302010451400c018082c21500c0030000b0061220550000d14000304882d01502442100d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 677590485 1250 677589235 677589239
    0xb03070510030b01030509011103010e0c0408010f140a0603121101150611190305030c0f0c0f0f0d170f0709120f02130b13020306010207030206030f0a060b03160f09 72
    0xc0c80e0035041c08810403541e00442c400030300a0000d010b035880039140c00d000d40d0501040201403070035082528115182c3d03010201080d02c8041c0c025406e0312580c2c11440c644d50074281230f034001d040c2c6a0003a100c2c880d1040c1d00514240e481c050880c084809600009003584ca400d90041c0031581700f9950100c1d0603180313400005204100b5218054846000d9101102180328507112042d41a0140209030326034100fa15031a260b94040d98008085220060842c890708401051040314103010b0019a40d03d2011001156a041465144541e490400441450043c45814481c0304410300c10074980c900c503801e02d464100103407511010f9000f08078008000e0000c0148182000480c541c0981e80412072a000d0102000c04180d5030060040b00d483d5032100300c00350383c00e006d401d203010f480d940740d50288940b0360240140c4a44461004074101140c076070001e94044800b00c244015224460041402601100c2d1f0401c131080e0787d0400706142d400300319800f55200c1c0101800101d1035006245c0748034804003034500914901d17 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 677591735 1250 677590485 677590489
    0x120209220e0a05060601141e070305160f0213020a050403060e0313151202030f2703121e01060c0803071803211b0f0f0c0e0f06220b030705 61
    0x50300ca40b80c01e40f0590b00580500401d540c0050340207039a4205c00c0070382031034085128158103602601d098118660080010030341c06252040080e94060b20300384580024a03041424110707500d801d0350000b0b174454840c040612010043c42c0c401c5414000054413014105865600c0c3c0c0001820f4400d046030440c001001719404003801840c0140c040d1030740d121410740414098600070300c0340200207011000c062040042c4010601919240c0d1360201083e180f80c0c0581c0c1d490200810010f46260400324039200209616503a40050b000c1140700d052036681a10365406480c010703015500d820710840010410903070b50784011070714031401183d2090f22414884020389103201000a0100941d20903908081c030141d8550140c210781440a503034100c60715043c038080c2c00d21008074031b98904c042002800c90350078807045020000407100e0f1810346904507203125444d0707695269042c04110112040c0401d0f81d040c01c00101c0b00d10305101c1400c0800c50303480900594070040702c0b05070014900c69401550521540100003556 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 677592985 1250 677591735 677591743
    0x203061306030b0108060901020703090e041502030115030b0423040f0506040f1104050103051c0e100e0a08060705030402100509041104210f060c2607120209220e 71
    0x11803058410000f6507141440c03942c1024805400f00c4142e0f4010862800401d030301445000c187c440c0800c0d100d180391110700d450200155048c0d0a00d0030140040000200c208040c20880c1c8098044d48007840900510010001142d04248405490303030302c9034184071b90100e50240a41d90240c400c1e1034460301c1060395100e140c94203030100c0302111004140c00051081100742650b000c510075058800f4002941903030b81da251542e0342070400c3d0601e40b24050103120010311602000f03403003a1020341050480e17040d1500003061480c0c2d404d0396034022010502d001803090000146a441a4010782d207090031502c4a07030800100343c0c214041001000410300c8941415940c5200d207441a10401554079540c5d460080e803664040c5203e105466511611000000465a0000d00301011540400005045601a041910519082446010034084402c402041404c00d402014055071f0251a042a641d1005500e9800e91183d880c5d0107411241030002e00701c03e88105a100d2244d0300401c1c4000ca4100c2e1040e54103803074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 677594235 1250 677592985 677592989
    0x260f010e010203040606090c0e040f0b0d05070602160812130302090f041106070305070b0603012406090b0c1b0102010f150e1b03010311061306080901050109020414040203061306 78
    0x542d5000060108115051084030020120700d40d0034040c040c00d110024102208200f030060042e92508034110307030300c0402e9000300080403009110510901550600e079650380704c50701404025105190784000c2c024050a1200e00702c0b9010301c01442d9600c003281900009410048150100e10610320000c00107a403061a843d102e0f8111030b031000403911f000e090134440b01c0005000345004260401060000c2503000c8101c0f2aa40e800020b5400700f9100d2002103401006140300142c44071904020900310461052405401c030790365079559406240d115800c11000d40300346600444241c1c0551411500a941c61416802c9107a0500001464200c08120314083e903070b101090642404640c00140715030580c08464a80101e07130208a8044c07203184103c21b4413588011301000e00540010300c54000e241d40c03a201120702100c43c0000e0b04940c190fa644000d0720011040e6005200c55007080000310385110140709a40c02c8800c0c1030209191400c4620500c4000d40c0b01801044d00080741c100c1c0b9116100c4c080c003803000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 677595485 1250 677594235 677594261
    0x51608030106020610140d02150c01020c031b07120212011b020102130e0c03180c10030902120a080a0e0102010906180b150f0f0102010b040c09051504260f01 69
    0x20191401241505d409002c58000d0b0344000c40b030b0380100e0202e4072805000702140f175064541170010742109440d10051700420604501540c000940401c90000c084050709041103810440c1d0241d401002c2d0094440009000390004d03104090324a001501e81390f02c034182002c17803000c00080d4640e2480b803e101d080c0440140e4102503034001851108550f4103000010040000202d110418140405201083c1c800a0010140c1d1282158840180b8209000082c01b8603c000d00f0f01c02c0350040f00801030090700305118141d102e5400700800703a030060030205407400e400d039122594503d088003003031081d03d80e10b0b07800950504541da44ca0000d03000071514403840032042c613100f15902180c012840c0207010050014505641d42030401c0c0004044e844604660500c40012100642c0d001680b80040b8010301c0044055a071003130415030583ca059801074522001d03200284c4100c1c9106640c0b003591103230351043e0310681030310442600400181603404040c0185000d103600c161038803441603000850a44000d880c4505c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 677596735 1250 677595485 677595493
    0x15030207030c0f0b011d090a030e0619030b04050906060306190b0307170706050a092102130902040c180510020304030b0108030406021905060f0403030e150609131205160803010602 79
    0x40079000185280e0402c0c050001d0032150913240c061f041c1c030f88074092403000400f400007500c0e586134641c0d03807002036030030000089034000c0920480000c0103020f421050400e5010b41d24003008907104507000700d0700030300ca0340010b0014500b54541c2a1500209140c041d281c4080e5036031120900c80a607003d200b40c00041800e16607508490740940425801e25400350302020600c038040051090580c2c224046034122414008201c60504c4c90300c107991541c0a0750b01c0000d52254842c000f01c0003420081e0300c100e5120b4020307101040500601501680d8000052085480c45024400204802d1601c0008800c010b03070140b043d41d0402d541c9070b0761050352207000c0e04441c1d8079400c0443c4c10704c02c0030380c10072101c0312082a00c07200751305008258407035688a1901400d07480d07159559600040c1410300940014003000c051404075120090a9421011410015101c01c1d00c01c04000d00404c00c0c20038a400726140c5280c01c804001415101c030402030303499501000111042159a001c00e2005c10000d030302a500a00440d0090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 677597985 1250 677596735 677596739
    0x30a0c06050f0f07050705012d150b090d1104140108011b200c03120c010f091716121716050301140a121a1015030207030c0f0b01 57
    0xc0c00688000405a2400c28140010805910042050560401481c1c2005540d69401c0c2c03c140e4090094003442901031515904c0202c03402d400c80c0e080e00c241d8000214108103221a9044010360150184a20240c08500340403030700c60782c6818422402c00300c0c420600000100c520304040740030355460010030500c80b0441001007142c208280603460504c09e03c0441d92900d441504405825406850f1205680300401402184040400c220710801c0190040403200001044841100c0c1c030b5000c02c21a0b220303542854002140100303c1d010300d07510940c1c0501e900324808040c04481c0503d0304150140d1030f0010505440d240460041100c13107139005078981d5018032a4103190713000315040384003801c1c095490344031040d4105a15813110507a41500c4241035420740e440a468001000001c05070407d6082d550820f0344a0200040c80c481480c0c00703500b0380e0800007196106200845501d00a00c0380110f5881007111300c00301607100740c2c020074111780300b81000c421401541d25658000c814003601196606080307401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 677599235 1250 677597985 677597993
    0x30d05310e1315091a0c031803031e09031c0b1e0310110c1e0708070b03160306030f0f03140a090302060a03141003020a091107140c03030a0c 62
    0xca80c1c440c02e04121210029819500c0c0d400d420301c80c1d40801000f0740e46959070010401070348003034117102000040c000072904201c0d0740e0381091b50090f9059a0303480503400680c4003510000c42520700ca0003440809103002d482013a8604d02c0c2200080607403615020402690031515281c00e81600d04d20101103000a014081c1024003002c2c52400300118103040c2c1d440c0319001d49a07800107800601c50440300c004144200c0640c030603080d6000314480c03040c660150350081718680320048059900c69016801301e450107560780402c25121651070142c2c1c10305080801c00284184202c2c10700d0a0740400c00d02c1c1c0004c1c03280d0342e82c4400750780403464401141c2004105011000b4154005c0c15005a4140031102600d0105500350240110403144030082c000c0300003141c40c0062501950010f2049170030400c0300b554503c1c0c000c150060f00041c5000891169090000c00300d04420148509800c17580c00d0742070355203040301d152104000b010805004060b103200350284031149031801d00103044144e02a4a46804100d081d1074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 677600485 1250 677599235 677599259
    0x60206010509040803040611090d030c0203210f13090903080709060504120f05010e0a0f0506090a0b0a021602130929010e040f0b04080405090f0105030d0531 69
    0xc04180b04414450500c0007040b0b00c0c004882e005544590b00280c10031500103142600c1c000c0c0e280e40c55000c0c000401c0711b010700d0f8000c00100354240c405c9003551048910104400300003800303c000070395044400d00440c07110900c440d0003040403031048104030324025952813444064071107842d000c4000808940c28401c038150840b0030840500143c0c240141003900f0040d50300000300800c071010b001045900c50813030501c0303070030f40c07103080c1103004d10003900c0000d0b01c00d0410380341d130303400100045442e84945c20016500c1400818495005c507880b072000081500d904c41418080c1d04141d030b00c00d150720b00c412144001640c0d0550f019520706100c1c64007280503011410542c40c12100c20107405040062541780d034508010709072125047d205404441015a1a1414000360300c18120a004151030000e0701880140602200074008645c41185d0078203440c1d40d141d41d0085c1d0f80b00b0178440c89415520003031141020900440c05020306010b4bd0741d9440782c101000f0302500011540001d60142078403800424030155004d18 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 677601735 1250 677600485 677600489
    0x311010b01080714090612130309060203090a031212290609060712180b03010e0901020c060105090612010f05061017010329180105100501091a0f04030302010606020601 74
    0x402c1c02d5400c0e140200c0d01500d542080030400c5452807001a10850320b036111003e5410410070000410700501c0c0c250b100007002200342c0d20503400314074280030000700281f0000c1250080030001c3c181032034051440d903030258080840d01c01182071102c862030304c14100d4443d101e5000e451050f91110a4201c2c4298107024441c00f911410f24001c884c01c00000c00c568598004403902035600108074458070318040800c81b815a010303203410b41d1100b65003400086024800300958166001100754104546a09a8403800c07440303680ba1a00c11900503200400061034204180c507400305004d000713001d1142c400608103003100c152658144030180d0301c406108140c00c2462122180e8060780c03e08440d0110918003140340b43c0e00500c802820065640300c0d00125030040002c03015564031200300e80b1001c1c02d01000e80d812420404000a16540c6020000307001d0083c0305070032004855040e16503a25003824980040a020146445400c1e603010030003480b0500070100004100850082d0300001c2c49030709144009041000603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 677602985 1250 677601735 677601737
    0x1505090d020307080309030c0a11090604060302030604030c051e25032003070302090c0d0b19060c05070f030c08060702010209060f0a0908030406030608010f09050a1b030b01030311010b01 82
    0x8008400c40094001080780d96094110b04450713225640c1c946900c0c6180302d140c400c9111400344812102c10441c894400d001c0300b0a00f1940c1c10034a80d540014481210041d02c006581a8404404a00800c1c086c0240701182806242540d0000d50580000d02d024101c0c1c03004600141e016801e0781c010540c0c80451100f0005c0b0580072120b0284c51a11201e00d0705510070004c408001111000031682c2e6000c008003001564040e103146003c0ca000201150550050100128030302d045c000364600b91303e40840390011440d9841400b00005003044c001b11000040400c1c1100c882c40b540c0001306160011204440045100354946d403101c508040050f0708003107000d441442568018401c6a50035174548040e52200c2500000e0291240d00440044491603515407040c50a800300107808a4141c0e4160440b0041c0c0304008002d12a104085c41d010084540c480f001810720381100301c844002612460118a80c40900010b418040717846c4d4440c00c8a0341e100f0f070310031004140b1400004800010a0183c081e2040003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 677604235 1250 677602985 677602993
    0x9030f07151d15010b3f04060b100c0507090b04020f030a1b0306050108062806021006060903080a0c022d0f030606010e06030c04090603051e12090904140a150509 71
    0x540f40c0c00e070310041c030906c40e43c010940b803544d1400b09600d04056041c8441260503544296418603090071001804800d80060065070704000700c18509024109910040c0e5100006100c81407902c60a480180440c2c0d5800d54042c0d000c110b412494151100550f0064881d01400a01440009800c9480440480e550018076040a400300000c0e03070400c1d041a0b00004c142d441d0440c605040f600c4420b01196940040c510744900710700800c22650000e60301c0c2c407a00310103004101e500c3e1102c0d015502070710a4400103025079420866080303080e108103036850301c2c40d2008c0c0c1031100d180100b009541416035401c8000401c064a1401c1d40ca40349064800d03080c00c40020341c0a80080e00f02503000a1060034810821400340e00000b01041308004400100c030024501745408010310794030303403a0054803540c043d014862000d000701c20f01807244d07001041c11003100910f680602d00e841200020310051190080c006e89014003003440102080324184403c004451003805140350061007081d4801c01c07120050610701c02a40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 677605485 1250 677604235 677604247
    0x30f0f370623060315090a1b030207081815031303031a0112050601020c0a0308040f0f180903050702061210270b030c180405010509030f07151d15010b 66
    0xe090002d5a4640304103642190760703650780130200701d42038034003103c101d801c00c201c03108000625846610180803583d0000a01c0701c003608000c411405d80c090f03007070060700e1500100100600c038000c4229401c1009c101428180076240003507507a1340340b030300b0441e804040360143c19442e10405a0502c80c2c0f45241c1c40702259290103106940009119058400d2104140c0f80c0d20303000325030141c0c020003140d040810300404801c0215180c1ca8004060740140c81111522030000c000030413045442c650030710544264003076500701460007202120240140a0081e000d01c1010040c00000d80c8459005222441d5412203107142c41c00c0c650700310030510040e54005000103090407560b84041003074103803400300b400300c9840c0401da00c0036441c0040e051000b02030010b680311440b0340c00c840700510038118892046011380020415946d4503c100f54a03481026210301d540503080000000280341c0e80b10819107280e0314900051640c02302d00800d42150402c110a995035403103426002c2c5002074180c0c00a01401050b0b11540c1400c0f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 677606735 1250 677605485 677605529
    0xa090923091c05070b0c0307120c05040806180d0f0903060204090204060e011106060f121009141605040e01021209010614010302040b030406110c03030c07030f05030f0f3706 76
    0x104050801ca140c6c1c0070020200d40154490030026200103052107040080920450000c3c00c04d43c02442407107201c3c054200044e0300c1c500600181e90710420840040d104a409014045030b681e01e050a420381800075400c00070000c161303288041e00242c04540401a540c41c04c1c100c0c0500380d015011030550400400c1d0f01d2507000118003007040754100c0005e452039101d00c1107140006440c141802c12410062096034a120004031040d000741000d54041e032400500811500c2002d40c95503082044801d2461075200c04002d0390800d40e000d25100140c0b0000181071094035a80d0540341da2043d00d8031056a91200424031038003003120b444000e0340409080c1185814500746501e50180402440a0710b5140d5460504900000e141d04460500c0d00f450144c80e81da28289801c9209500452405c1c0d0004038101121604603004000300d901410310144410705543e40d01d400900c58070801408605041e10641d02c03840c4441841a500000c00c0004000741c18202d400c50600c2d00b112400e5002c1c08140b69100d2004a40c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 677607985 1250 677606735 677606753
    0x50316030c050a230d090b030604061a030105090c0a0e06090406170a03112d01060e041a070302030402010806041a13060e07080106051804151d07050a090923091c0507 73
    0x80d5007c24246450380d0b5005c0000e401800ca40c0e10041e184215607280c0c003c400700960056040c2c03001140c011006889141503a20540900d921752004266070b000000100d1400e50301400f92031400602c0400d01b01c0c0c40f030024440c6903c01004074842d0b98882c1c00900d08140d00003030183d222000c2d8000030a0403501c0b6182410400e00c2c840d0403001c5001480085d648540b8082d048840989090140400030b8285403a100e04400d00e900c07810030100d0a03d00100b05124802e0081324081c50b0142d564402036143d040402008055600e0007034140e490030400c0a0454840c840610b44800c448280000c0b0146031840c6a03814910040c80003040001600050000c00d4001085e944a20004c2c1440d14005203580003040040c280c00b0240c1406200e090800035a0410100383d0214800c1c519083e001a5200c0ca40262040d0091001c1d03200420000c50082c0a1000c440d1f010313a481420f00003a0804a2100c5a20300000040944040d00c1c250088030b43c188440340c07007641c0c509902c2c0007460842d180610340c0e1118601 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 677609235 1250 677607985 677607989
    0x1c0207140303041d091207080702040b0a0906180e01090c0b0c01060503030324010c0b0a09051207060204060825050c031903050115050304050316030c050a230d09 71
    0x455a040c203502106a1020001d039009803100c46011407030b201100c81080c0100b02c045a0b103104912840000c490b0400088080e60700d02a031040c5d5040c105040c2e582004090b0003800c100c640c0215030b40b20000380b07001c0c050043c40c00400010405146424914500300265407a66030ba12105a04006120000075a070300c5001c002c840058030305d41e4840040c2051240034110701c1e4082070b03040c80040280540d6550201540010180c8540d40110201c0101c0066903207122a04001e4002c01d03a006c00640e41403003e800804541c2c2c825001e5500300c001900340741040b03402038a0166001d0f42e000c9800d00400b40c0111032281c1000c034540c0c001c0411002086c01400828200b4400b80401c8801f24141116031020000e40720041489803450090804040c03009000345800d21580c102c64110001c0100b040340110101c23030296402c00082c5281061100c544e00d00ca41180c1c50840c204580721850a01081e0b0074443c20106911401401007100400c01d69001d1060781c0361141c1d655074001042005881e5082220001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 677610485 1250 677609235 677609249
    0xa0507091a120a02060a2d112e1808030402100c11060a0c02130c14180409031709030c010b090c0706050712090303021b03040b0d05040f060c111c0207 66
    0x81d584944210031100038a0b41d0b00803687c50242c148050340144080000c2c4c6c254100c1d42ea841400c0801c58580c031b20794070000840000c42a400f003081d078041030300c002071200d1480221241c02184503c0540511205014805c100351500100801444118608460309522000b402c0c0f40109640710680c603080007100d41445658440ca80001d81ca20343da50180c1102050036070003d000c1e021983d001c0f000c0030041c1190f100b01d84001006231820340051048441603c0c64261a01000d40d002d0620906000c010107203070790107070244004c1103040307591599100d031203078401c003005005951102c82c129180b03030070f4a540400b0300b031082c4c0c6110704101042c0d0380070054a03859504583c010074943c0320b03403005a49030410464410116414030301020107140e0940c005242d03515803585505c02c00c2c22071510b540d031203000d10701030308006500810a00441000c2030300080e80140c0038515094a0211540d500401c0348d120011075004114001d8103001405020300000c51448000803100140344e212000007502c03000d090013414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 677611735 1250 677610485 677610487
    0x1090806071d0907051b010c1b0804050d030906081303050f21180f07030515090c03100506040b0a0503030d020d3b160b0307020a0507091a120a0206 65
    0x15403000c6010120488a0340e010b0f000c0007071401c100344028425480440c5801c120050b01403031100300501440703a000c07400a5030b0345040c2442e03144003e42003421480081541e40d80c1040c00081210790790680050b02c018401c1d00e8440c1c400b403609002a2500c4402041c203c0c003240c4403050032022940000480700c0c65807420003042d0b40c1d500c0488407040c1c03040140071b512001c00074000400c04c56808401c1e401c0c403151200c408441c4001c03400c0804955a1f030761b5000042041c5c200740c58030304034058405091908640b00c201607070ba2a50004000c2894210044900e04189854000384580c0d800d16102e08032800381c064407511102ea0600000c04d42c0c038899001400485075000030b002d00800d400f03510141110b40d50b0315668040840038502002c20034201c1445000704181d005105502840008501c000500c40c2c000c1c40f4030082c500101c008054000500d2070303095000764010500007800034040c45000d400b1002000420070784c003c034408060f03541d0a1055018040c2c04d50f4810f01a40d0000f480c80c2c45e194122030032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 677612985 1250 677611735 677611757
    0x702030f041502101505041a030d111504031206050108040302120c030d090602180d030f0e1519020606011d0d030c0b0114040f05041a06060f040902070c050109080607 73
    0x104c4c68282401c01001e04a85002003100e060140d10a0000031100101c03400d120802c0907000d44100701c802002c0c42545039001c40c201050b045e0249080c00d960183c207000b65626000d0400380a9003a01046a0450004003840c103075509001c194070410014103c2803800e030031070785080e0740e02941c2e079000c03140340005011002ca41d40c14090780800c2110b00842640105201c100c8641c5007840281d0009900da00c01c2d8459060385070300c1420283d00040150345c0658400e800e806e1400f5040c0c03806030140c0e40322500000e0119101042c8403e100090941150700c000d040080400300c00028241030b00502072504112280405081c8009103020700f140c011005c6400180d070700c02e686415121420340c200c3c0200340e4030002c0d000246840300d6060f042044d85042e581408842d031038039141011104220b0f00200144200007202c4100c1d0281c0c000b9691140024000c24584810b01a00c650190001c1e0b01c442603840d000115803041202c01c49d4032134010070382800c003540340c541001400358840034024440703410044d400d601 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 677614235 1250 677612985 677612987
    0x1e0c0212070b040b09030d020105070909020a17091c110d1d040e1605060316052a0d0905040507051b01060302060a0c0615050303041203121104030b0702030f0415 71
    0x403002800818405a60f440c0c0c0c4410018164100e40516442801002800b210150042c040c00703118280c00d6070b64401c020306001d1a54008c2d0000d06e603003400c01c03100c000c1d240552900001c8150090580c14010801d0300002d00c03d10000024403441c042c00c100d800c405c88a44d05c00c0000e03800c09c0d218403d041641c41040c42020841c6441c10090b0410341c42800c005142d03050b600007162409807942c402d48842c80f401e40300d006006891005841854007104840b00f00600544920064030115074071442010300f840d0440d195100402045000d22400e40009258140c074030f4106c10141c0c0145825101441a0710b00880c020300070f4010124070252030214220301410300c4000390302400103180d00800040d02c5034000d80e0020a0340003500001c0395400d00e0501c1e00b120f0342400ba841401200d4005004603e401c2c1040301105d502c2070031030b400300e0500c50000041100c900c840c5c0115901e00030002c0d440b584482c07a6080129007004041c00d50000e540041041d9500070400701c003150190368030700751030041003407441d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 677615485 1250 677614235 677614243
    0xe060a0201230403080916061110050c0406030b0f18060d06020403060507030b1e01050f040f14010e0d1716060c08011509060509090603030714030a1e0c0212 69
    0xa50b40400418012040d501040101c014901440c000e0380c61030281d5840056003a070324400c1010303030701d0403010b00107040006611840e040301d0b808051b1000d45000d6a0101001d2017950030955070460129004070b070034000c40307502d0b2283c400d4192048a0342280842c0184c0865074051001c1407982480703815400051198a41551007842643e00140845d074441c0d90381005001043d0946210000030b0030440003a4883c5806c0c0c00d81c40400004520700760420380c070800195000d511100440c0d442840501c000150070301c102600c54010104a0030500b000d01802c400141054114110188030b07540440c03803c40814403040b00d1100701000d1600c4030799201842032141301c02c2542c0d420000c1c0054244081c10440b2640401694100c035000d05080b5029415900c040c0d0316100e1078090180090424480380c1041c4ca0035600c3c45030041c2d40a8162494140682c03901080c4003880707800480c0c00e41c400900042d4560b4400b50158003446000c10400c890310700c0c0e030700052055540d42c001a2141203a60340d42002c01e80180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 677616735 1250 677615485 677615501
    0xb040c05100f140405181005130603050c0603010e0705180901080109050c0405090c0105030a0b0a031208090d0c0605060307080f070e1806060105071e080d1b0e060a0201 74
    0x40641c480302407000340080506541642c0ca0000944550740c2d1200d181d1100b0548007a6031000b41286a1703220072002400f44050010400707001840103080001d000d07164641003c4107104004404580641181010392030a000054001d01440341000104001c4601d102041d400c5440c41ca482d0780c0d10301c42402d840320341c1c0b00d210746072660040320a000020b0708032055000b02a0644078400352551800e40900300011140c0488001c240c582000428820a610400041d58403041b0f0785800240041c551011440034050b0303030021102582203005110b200e9800c50584c644c8510a04010300c2c4040300214000e00642210100030039072915a804141c45680521a00d000703407136100101c0e003036018543d01d12aa0744256106500180c4100f50104100d00704aa03181400200c820700188907070388407000110f915520000c001d4580c0c4c400303802910002121104002801d600075001c40761110300c802003400071140200101c40c68902c2411032044515040907006076140800c60b8503070f4030b0b0041500306a0142c4016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 677617985 1250 677616735 677616739
    0x207020a09060501031808031810020a030e070b04050303090607060b040c031a06040f1e0905070e0f040c300509032a031e040b19020c0a0e040b040c05 66
    0x144004294018658030240c103c6400340c2c0d0510521a01d1114201882000c03000a090b5040410000c0c58090810008840b028404021110346403421140f14080741c020301440300000b44c840040070300d103440801040000c0c3c10080f00c0180741c03a18100001e03070307030348602d100d81802440e01242d140c0c107010240e400159003c00c00740040c4402c2500307101c000c4c002c0c03640303071204590600d01801c0700c0028240f0800761029108034100c03110019081810f48005400c482e10040d040c039081ca817006c2390100840c007419000c0c2c05241c079000780e0010144100821401c0c070840850180303103084910741480740d01825100302a81084981b8000d00e040b03031040400e510900407140d072494204030900c55100d40000040101070201d981d05100341c131034444180701d41840725a0795000c940c0b00b8061000d0f0869000040e48565000307003030300d030b162903640c0c8029030042d00107d11001c00001407002d0b0041064042c440b004e11814219034804050342801c00481149d68090000340071201620002803c0207203c03003403440039141c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 677619235 1250 677617985 677617999
    0x612020f0703020a150204030209040f08210f070804261605061b030915060301090c0806041b0b071103012003090d02071a03070306031b030618210201020702 69
    0x242406544e07001803140c100c1c0c07030b02c150030940180c00325548250750580ba4010441402e07503e880c0c41c0e40d83d001107441c00035140c03070001300240306c509500812403220300305201408402c2031030a40300b00590341800500301c1c410700010404000c00160402200c2d01c441460a1412242d044408401d41843c0222100d891051141d61241418841c000501a204105106900c80c2000e4075904c040144d000540e041e004d240e0220b2088140c51030580b00301580b1000117400002c1c0a80e094491507400e1183c1c0c1e01076480e9400c88400d001c28080700e100ca01c0c083d40d51240d200040c052600c00c094a05105c4e00802809144900600d104181e4083d04501c80c0c51031074a5907481204513500c101c000c20340c015101c0098500c82c8248000300d180c004110001150b191011307500034050003c40d405840d50004100404140d603910001c40080c0c5020030b45041d1440250b0600c01160a40c58400c00303d65820301b0303003680c9119040300440041d61400341c2a102d2407005c0c1a82514140d50103050b0b01900480070300a5110345 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 677620485 1250 677619235 677619247
    0x20901210b09030408010b1c12050d020703030203070e031501051003020c030309070810060b1e090306010e070207060c020a060f2307060501050405040f1205040801050c09091806010612020f 83
    0xc0b00001030301c10344107403a000700a140100400c101c44441c11510300f04407203803000c43e0500400c641d1440503850b00e4090802c07070320f00300320f0a042804aa00450044002ca07a011040c03040c010b82c03000d840d041030801038000341001681440b42d0400004d051040600c0761304c0c910103140c2d6440c03294040e141c01d007458400712500c03820200d02113a2126894000d16400d44144080c902c0c0c15010360003824100e910980e4001d14240902c076140422294080301e40700c071490f00b0445486680c82c100f040c0e130b000b010816641012414241c0c0001e0030880c180d4444000c200300801c2200c00341c0c0d100140013044940a003446c004c1e14940041c02c0e15280401c0c040c2848161030080d00c41029003c102c000c0000342d204500030400d91f0703200c0c810071007101d0f010750700a0030128400e1210030000f0b005000001c40c0054500b0010304266941c00301c2400c0d14030440312441d0311030340400c05035a03c0c2810452a60404aa1102400d00741a10950203949003014800d0200300032004005120ba1301442d812500d420322103030065582c0d50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 677621735 1250 677620485 677620501
    0x4050f01031208150409020109150905010315051e030705120a0312020324040609060f08011a060f070f0f030203120c210c0906120114030a020901210b 66
    0x90000d100030b4458044041a0045082c4960741d80ca100303203201c0d90401c22208048041c04002c086541d8200d05128a2010200302180202c0e004261000799660789480981407400060585052304444880d486210307400b03112542d0780304812503c008000000c030001c6404280041c0c5080e100d980031a400c200b0340074020b11503400104440ca5418045c2d1607010103004551040e008034071040711260308440301000c5459450800c01041d0000d000010400310b0825150320ada802191050380c0b14040900d49450104002c403028054446410545000e82012404c08404110b0910510400c020100340c006400310400c02c011211414076608a0650213990768036240c041d40e60741c4072448012842ca402000503c812061108850f00780524200c0180c20865081c0d404404140240c803ca851540600420882e41c42e04400b4101800900268130304d19450040100c1c040c0040c160402d01030380080c214000540c848540c01411182c805a101e218a00381c9982070101c03941c103800080c0a46460011703c9202c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 677622985 1250 677621735 677621761
    0x303040303151a030403110706091a071205070f1505040203210919050d030c1203020301060516050c0429220b060d180b06010c0b150f0405 61
    0x8500c2a2001c0020046440324007040d00114400c07529904600c0020060072102c40e8050358200c0e10a08210041e4032004078528203181c1d81e50841e000223403814a0810006040c3d0561522454003010b0312844c1aa0540b1a010184404903040041c070200051910400550032500300c0040c0e00b011010307400d146006180c00c06464251030503803082c45403030840c0e482080700640d501c0251034028100c51408240c08140700303003d160803441162000303041c1800152520344051303060b24136200341d032840c184901d0391401407000c039030341c4041400b01807050006001468101d412154600c1d078038038110243c071100e13191081c5490034084155400c107051503c05031420510b1544c00046402d00c40c42c040040142105006200c400c1101405110144014005034085198403101e850310001e40424a816201c002c41d0080c0c40000c02c0014000d00d008140030148030080ca1241d40000b024030b42030700c0e0480c0d00d407144c101916025114110715049600c4942c3d1321b942c0c000d4110b60310341029000303110030b00e8546403001312 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 677624235 1250 677622985 677622991
    0xe1305130605060306070804150e01061701110307020604033e010b040b061b0114011d0a020301050127170105010f1202031e070b03010b180f030703020112020f03090303 74
    0x800c42c10710700854610f1030046103207881101c095503010219661503e803d07840700c0b2002c4c1c4498009035920000315400100f8061100544126400d03205441c641c501c10394211100b00b1520b920030305044c810312408550115160350015094546441c07200591070f180002851420001000f162003040301200e1401035803004058964100c000300206540c08040c00155003509a0056001d0400c200c00743d0252204542d16450480140c00044c40e245841c3c82400720b21800e030003200c00c0c0c554401045007450070440b02d0503440580d00347c0a50865262400281040c4140e46104002c000d90006c2c41054090b444032030b50060624100c0c21040b510301040c0d241c000d180a00440700410b1200d600410201503041d81c5d03021250f405001030001820f0041c1101e009000a400350741503028512001400da2400c002031070190080d803200e10394032030030b50300d40720010000708014a01480440740041c6403a47c0114041080307036020b0a014140181039072803c002480351441c2c14070002c4012082c00040c81002000d10b00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 677625485 1250 677624235 677624243
    0x30a0b0a050a0f120609060509030304110a060801050d03030e01060b0903060a0c141804110a0e010806011409011103131503060503060a1a030601230607120e130513 72
    0x4507200c1c8284280400c890080910941c84010b040001c100c0c552003071000503008003c001881402940c4502c10b43d0819190f1810386c1d030012082c8414080600928640c030b050858042c030001c5e1904d00301401c1100705210f144c1c0b0403410300d19240d0074180281c100d0700e00c0f01070080007040402d03250a007004058121000346030087c4035400004a45880520503c80108125103030341840c1c1407411307030000056100020180d502a8078481c8400d05880701d004444444091503c070700e0310781c02d000c0f1009014101c00e541c480c2c10018840240001660010f0319211507240028406684540040041e0b940c0a106c04d1090b01078031002030281082c541c0c0c5042141aaa0505044001c66107140000c8081c0c0e11a07000e01030345070f0040804500980000e61080c145404a2004000c2010003a400a402c0880903407007104c00f04000480d4401b0917150003da00e0860b5001c03500300c0c1c1440e0b0340d030700c8100304401c08200f9030060050b160041c59165070b65400312100080031442c184954505074050f2400100c125034111 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 677626735 1250 677625485 677625499
    0x1c050a140706050405030c06131a0d23062b0501020307090b0307301a03100207050a020906061909090b060c0a060b0402040f090203180307050a1101050f030a0b 70
    0x82402ca1245040340c0440d10010000d1103003034100f10402409a0010b80301070845108480002002000010700103049044800350907110003040751035030180c800c0444c4e00d00042c4810503904072900010040150805c1082d5080d0300c03481014905d101744030900c081965008584c5038241c07030410505400a501c40c492664030320f0345003070761203584e018a4001510507001050140380f00e030180a100142c04088250b0790f80140c4a0a8140f090090864a1800c56804094014000c1d091642010404c03d03c0003000804114605820350712201c0c0c0b2050440390003441070100e440400c000c0da9440082e5140c202c1603c4030800e084036440d101510808140c450841e00c1414243d04d0304292078614162003180f071030b00b800341040126a42e5450000d1502e00c01203584280d09200106034012000000d80c007500354680016600d003440c4890304a0085d5201d905843c40d0303c1040180d0000d400481c3d5090f01d04d90080c15080c001900030010f031000c1c000d9036460740180c0c04c04020040c4100594000d01d40c841c405031448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 677627985 1250 677626735 677626739
    0x1a0301020f210f0c03041b090f060506180d020d061103070e0303040b0a030509010e010c020c0906120712050a060218010e040e190f0209130b0c0703020a021c050a1407 73
    0x1004407003408030380b1861203d03840c42c001480707201200c00a503801441046218040ca02c8014644401036180e044504102e0f034504040100c039000c3d02c5200c014040c12507106080c001e03500c01d070851301110038850a004c2c0c90000444c5045481b0072040e114550391110040c80901c600c038900401e01c2c2c0044900100055100c01040894100407085600380c80105102e64913080030329000b500034000c0034184062035981c403035031020450420f1041400d103c2842e0b0140000c40d0641042041065000e803100b889115803c4c0e1108084800140010441d030107103540c1c880c0f00105040c1141021013040014000c40e0000505c0340031030000e14001d80d42d040c002d881d403d00504082040c4000c42d18200e401c80d101358440c01c80f44040e443c120050034200d031301c980b1920040344079680c0410180d600c152088060341002d09208001c0001c80b510065100140d60303112410551300382c900a556a0085401038000c0f2210a01880031342c0655242c15101c9410100704d42041e292032401031004c4081c144001140d018540380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 677629235 1250 677627985 677628037
    0x60914100204140f1c0803150a081b06041707050a0b0304050a020f03120f09031908160f0206031608100302010c110103061a0306311a0301020f 63
    0x3a68281d500443c401c0710801602410300002c82040d9488a5103e070462480015020410380101040c5214a02d41034032804c114180c01c2814900c0641c0a200d000504418045c2000c000707a00c560061340382080300c0f400c404500115045120b56003250110003940c2c0c142c400d0801c4001082c504403203080d0303004074105696021014903030106590042c8103803c80c02c003075000741c80c0c6400809440f401c003d0958018045c1e111109050341e0060786419402c0102280c0305000d031030144030040d030081ca0b882c0c1555001c881a03941e04054456401607280c445449070000c0d0074010314a111036145540a4000f035a00d0030012070b021881403e18004100081c00b06001585e408076590b07545080304d506031a44103403200b40e640c9200d03441d1040c002c0c55040664901c40003030150741078031182221090782030002c0c0e50b80c1010f0003407100403001e6441c2804030042d40c6550800640c050304a00c1c810f514840d10028140c0e5400b0414034a81020110195041d8004213840202500c0807008001c0405020703a840480002000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 677630485 1250 677629235 677629237
    0xb090f0403050706050402011e08010f0510050a08070201020d110705010b120a06020f091011120712050d0939060903030f0908070f031a010e071107030609141002 71
    0x160041c0040d10910000c00040c580e50031494000703205041c1092110380d01c801c0213403d941c403001d8120000e1488401007207207801030704490001e04000d450000c000100400d000c3c02501c6082d180ca000c016445c0001032000b031013981556030840311240103129541100720403400c981c00500055640d54a00700300702c401d45c9070200184036118184406419294510303280e20000303400501012440c05420000a50340340e0701c104400c26151070341d45416454030200d88030980b500303c500051007429002000f41501250138a0613041c4031440d18039250383d90b01c03030340000c050280811400041442d10785c125104240704d841c81d51800018030403290806000a1040c003220940f0181c800c103404a1065417050012911078640c4aa1900b03840c1059000c0e039a4800c807131494000d10780c1c0b004880790b540103028000c00c480d5200582c5c42078044400001c055051030013041050f80050305d41300910051518103500c005040c0000401540c00010821400d80ca5003082502c0c1690340f26404d6860141c6080f2101c000038904c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 677631735 1250 677630485 677630491
    0x70804090e1b04111303051606031107021005070203070807060e010c020d11061b071805040c14030f010f0507090e0f010501031d0d020f06011a030c0307140406030b090f 74
    0x181c010070600080b014480200341a4800710b84190302001a104100383c030f40700d110002e42c4505c0060180300042c613000c070000c18140d00b00700c0400d400e01d070300d9130000b01060083c0c070300700c0c1c0c2c0450b07040c2d03c00000000240c03014410111300a400d03014410b400280300c0d1002c40c421080701c9031a1111003041c462a0011134184511800007580450320345006d0001c546e2900400d20703507176800b4080601d46070f80460034000c184800d4500320116400f500e01032060303103640c101c01c02100255607170a000606107681c80b00004001409605c40c0c0c5040c1e200e400c882c56030200005594940c000c4002c221038042c040c0c0801c06440c0c00c071000d4010a0f403c20000404503040f15200384200140040070130642d003482c004402821100c10b135903440041c1d49507140000c50bc04e20122002c03079080d400a1801c80101c91402d402d01d64160f00440820001401b040001900b403811280d1201500c4505992a03032600820313280c910507481c0d012040c00010401007100f07909940200d03150503084a210009070b076000e64802d580c040c11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 677632985 1250 677631735 677631763
    0x60103031b030c0b1f0806011a121803130f03020f013605130b041406030705010e0a080105070210240605090a0308160c1a030402190b070804090e 64
    0x988910700460f43e490038036904400105035180c0c5003088111085d0310808140c124505035041a4010403200714145000c0014800049040e41031900c625081c0b41444001801d0146440100e040105904000c1c0221080a2002800d0549140d25181d01c20224080741c0012406070120040036030300d542c0203c0c006016a05043354504290604d40080c04002e140d5141040c0583c50504021915545000d1418400c2070744020000314000303400100130503240b410280182036200340d804d01a1903100442e100c0140d4000707081030b41382e01c4507000206240301e49a038401d41495203440c0901001907800b20300b45507112882c01081c1f041e01c0e0a1a17251001c189800d1103900c5201c40300c0400c210f07035401007020b010f0344200140b0310b540071503a035100d901440d8083d42c014041c80d1403100c00708040000b040603010142c035521514642c0b6180b00c0c003050070f02c0c1c40080c001903c54040380080300d051000c10a80200640360941025444280510f007131002c0e50071600502640b103041190500001c2c4002501da1000110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 677634235 1250 677632985 677632997
    0x9020c0a02240a1b1505150111030a0e0604031a07020f0c01090302101e02010e1e0c01050705240a0b040c270504110901030c08010e04060507051209060103031b03 71
    0x82e440a54100907280821307200d03100b121002101080d8a0035018007000100d05000c901c0745404080c1400080d084800039061045e006182101c0f6032002060b075522941a007000840d1407017a0001800e039010340c2c0e100170004040140d1f0500381c040403840c800d000e0a4540c003110020710742c01e08902c1c0c5401c2c8644901d8001a065001003015181c298580103613198a4100170300e103034182c1c1102d8910044080750220160b9199603400c43e00042c00c00104a6244c0c400700440e5000440c5903e9940700c071072204002d410000003080e49001c1c4801030000b41c01e46290002c108a0840200c02190101c0c40112400d5180500d808a000d43d2410030b4010100b0070320f02651510300c24140d40d11780034003107240c0121200444180d404003140e41c0d100c0f841040840c5032080081c1d5110001c290004003619100c00b80e2004019204004100c40c00600c1e9440760069808400414160f5030391038210383d1801009040b0061600e46014042480d40100d8150706070f0b40039603180f8910b4641d2403001a030f9818014802400222 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 677635485 1250 677634235 677634247
    0x306062613200a0b07150203041103060f01152f15040528050606010f02160e041202010209061902031224010311091e060a08091504150209010909020c0a0224 69
    0x902031f4000e40d40144030300c041e85000c0b0841000309203010360031100c40321030010783c80050215208506140c100c40c503091400350503607034140c0c12558095070031480241d00020040010320143e2018482c03000e420340750f1080c0c44250301c7c05090030303945c68141c4000188401c42040b0098401c0d101310341386100c42d9800000501182d00c81c1001100c1941e18824400118000c038402e07401149050312030940200590316816401d81000d0401c18102000c0081f0001903a00c104210141500e585003a507281c80c16000c1d24194604e10001c00383d0540c8280902041e8100c515803c202031139a800c503505542402082200742050400c1e4010340895200c03462844900009120140d428500010300c00620318000001481c111200c0d808200c09402c2011502e010444000410044074810410b035150200b80406d03250141c02d044c1c03200c90408120704980101d80d50001584506a40641d01c00c100400503c08110341d20103041e190b0907200c4170b003e902244100b02000d0000d449030000ca400481d084c0003d42c2c41d41c9048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 677636735 1250 677635485 677635523
    0xc06090506041a07030c02041503050c06030603060414071d220b0a0e0f010c03020304050f12030408030a020c07181103010e0105040c020a06050a020a0306062613200a0b07 75
    0x307044007108508101c4082014001a166030264004127030f0501e21041445041d07151203401c20700c00f28442c5015150a00810900c0d540010f00260031541110441a030040300400c414207120160300000c9407405860003035003443c08000b11a0b482003040003041c4003050281c0710310700320200080b50301628144411021400300d240d0b561102c5244203a80d41210354103102c0749006401c2da0200c10168000caa40070080106004080c841c9000782d100341d0020301520f103c0948880d2240c0800386c00500401404800200040e030298100c079920301c4a4030403502e400f17990f02c13802c2e98005414907001d2101401c01e48204140c80c688001c0c1c83c1611075110b050031840c0e080000703000c01000380600c1402144103001c1c000380412070300e11038180221000040542c4d90754240d0006030985449510050401204043c66030510721009284060503203601c40c107510070384850100c0200359518203400741c4102c0320443c0a0240f1070040c0c080311420035007540c024801d070faa205052440ca00134a0320183c01d0002d01c0da950009c1d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 677637985 1250 677636735 677636737
    0x3072a0512030a02070204090609030305060303041211040e1501060201230112060603020904200906010e010c05011d0f0727050402010201020d1a42070f0c06090506041a 74
    0x3c480c40080043c100720f075640010302035585450b4180c0d500c0c0d9403480500141075040c0212544105c2c00d40055107010701c1c1c04160090841c0744003000d485180c84d0010b900665a4035001420901d0410080396000b1f00d6020088030410002e12910b00550319000d511380e040096449801e252016041500c500faa1902a00c0c28038118a040d0440e03e542c5d481c00c0100c0181d13281203070300c0d0140f409021000e501425110403608068509414248600300d90350800030300c0d80c0d2020000e4240c000a28100317003112002d150140c05028081c00101c0e000e0850b000c4c006103608005a0452801c05110449041942e212216101c0400c043c4110032001e21703a07448901441100d4100d990458810b100051401c150002c00340200d950380c1030030b915071086180f588803080c9030540000c0040304403162017131458416032000c180c1340303640f00301c81210001000c7d0500404c20014001d40d20340c10b40105139603d4428040c82c060286016501501c400705d503140c0b80100e03003400d18105441c15940056020500444140305090341 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 677639235 1250 677637985 677637991
    0x90a06080c091308160c0f0b251202010f0b09040302061303050c0618150c03060418050105090a0c29092808010c050f160f0803072a051203 61
    0x440702e08410f02d400103440c0703000400c9581c400305004805e08070a854000c0d07403d441584070301c0c0c204242c0740f01070124086400c01c90360781c0207020035654090442c62408401c401ca020740c005d08010321003101091104e4043d0400f2260a8503a1005c0010124002c108601c0c0340c4280d42c003030010782c842c030700080302c1091010000461900a00341507051a0740c168103d460b104046608211242070000c502401081c01c00900b0f001500e9115500b403c3d1802d0310b2118624080144058071540e19240f401614511b8602c90480740c54100c8000d000030302d0042141581c80c92100350807100d268100800050ba01c65004840754034000840c140721144190003036106040d08040b804c41ea004668541d01e840340414504100a840b04501104040038a01244142168442c00e02c4901384042084060f21509510703048403941d244620f0008004d820900703102d05003044119000300002400410f00c06602e401c820120f400e0b2074222000c8100c40b003014142900c06908200003481d562000030035030781c030150080140d54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 677640485 1250 677639235 677639251
    0xc0e270c0c01060303051209010e060402190e13022407020402090a050d030c05010e010603020a05060d110c0f0d11030a0c0203031e03062809050c0415020c090a06080c09 74
    0x418074030401240c6085500e035900480111b040007664044101040404a072300103e1040200f02505c4522000c5031101d01c01000241304648004100301d95a8500e0346210142c05d0b100580111403800f0101c2d8070f0041011002a8450642c8090001e07070380c4050101c0c0403101d00c141007a24101041682800b01130f410451415500281c0d05c080071400b500c480009a0303100d8080c3d9991140324600d41041401c40340920b00030980783c2d060101c14800b6032100d4100100302d400503100355507540b945080030720051004555403080c210b000641c050841000060400440e5806015108403c188100c180d03181011008200182e4100707114081965001e42e03444e040d42070015081c3c87c40e01c00300a094402e000101c0800186050011003480080d04002d0741d40c403444460820000c4400341c40c8164558244d60520405e01d4075902d440004902210300c00c1034900070070040385d0815000c1e91442c000303915510101c08190150004900260030b0340741038044d1400305c411090161107821582c1e02400070480000788200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 677641735 1250 677640485 677640487
    0x30308060a0e04150e0613080309070911040f06021f021806030a06060230031b1308010c0305100b2209150b041a0309100903030c0e270c 60
    0xc0c0b103844803070980b88103031300c5001c1811808030031501202c21140c1d16160b10f1101c2d07100a003008029240c56104001240e04446280d80341d41c0c680400c103184c2000d42e0810006103080107802d10580e203040c0f020700196202d910340c0900560b1a00c008070f03525401d0340c0364402c103504840b60ba000100041c2d0300070314401c1c1000d130503e00c1c07000141c80401c11a900654040c440030340d40d9202004410703810320000e03949900c00d00e0700040348003d0744105029550b50b0030203101e1141d00000410710072040d0000c0301c4050403440701442e0f180d080c008404c01e105a03403803003104920350074008a0364040d4820b00c02c8620a52098050207034143c180206290503030400d5216000100b42028020100c803540c8218000a0405000c046080c030102c8401c1c6640324005d07442001c3c200710911090080c6150035104c8000f00c5803802c00c0f19101d54402981500d000411040c0500883c60846103805140d4583c1009500034510b4480d014801c0c03401003402528a804040d88980744084074214502040780701200750403c1c2280030035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 677642985 1250 677641735 677641739
    0x31707020a0b030109141608130b010e0f0106052106061b0307050129010c0305040302100206160212070b060f032a0109030f0210110129030303040507030308060a 71
    0x441c80021035a000200000008801041498114042c4a4289154010300c0303509007400c1d6044454801000c800b5010b209410f000981c040ca40c40f00085462500701c142000603580d902881400c146003541e10704150b028580c000300303605000708100e5100c10014003541d0300d1854204c3e03142c100d9500103015a503100c94208180a10314181c0003d4902000e400c00c0655a80e407114070b015400c5480c0710303030741860300003900013a4080380c0780b084000720910000303080803003404010345401c448070712468000a40c446500c0707040030011580001e0740c900c610820401e150183d072440c44242c2e44c1d40b0340400c0c0d80300c040e203040101d000029000c1e02c941d40c101c030703019103101050030b0356800003400d107040640240e4484803030070001c2c0c0800b0004031150420010a0070990401802e607211700c51070124003140030b80100c502c076802c00d010520842c10001540c2c0307544020060944018040480e481c0340b03090fa40d1b130f8044003601d03440c154640801100d00581e800801804d0440c41c558056400500c0240080c0d841980d450380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 677644235 1250 677642985 677642989
    0x34b0207030908070e060105030f100513050a0e060108030703110f0a050604060b0406150c150c0309050c03011a010f03090c090c080f07120207110409050c13021303170702 75
    0x1900c800c900c60784a00740c03003600f0a6803082c0f401519501441e01c000c0b403441888042d0340c2010407030350840d880d40110206a6030b181c02048201000360f2101e5001078810040d1140c0ea00c165110501031000894280b040c0010149919603480c0c003800b4942090b0000c010105c0001d002d0300060403924006030076221007610600740c480c10901d0b00c20080e00d00781c001c00100420001e42c0e10a032400755004550400c09107050455425015401002880a110701c034060f050a00c6204035181605860b00c00c428002e43c0c01404000b00580714140c030840c0d0f94411808440800d140602594200082d50b90300030056003a4080111903509030550300c002415510507030700002c00d511004640c050100c0d080c1c0458030443d0720b030000b0b201c6040200380d803080c2c5e0005014070030043d910442007541221058400342e214041b40c10240000c2c0032503000c90303510070b152000c1c1d40104900425060b18208089076180703802c107840c440e000c040e881009002c2260010503001840004c0700001507046000b44200c0040c1000c0301580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 677645485 1250 677644235 677644237
    0x302060d1a060a0903230a0b070215160e01080402100e120102032404020903150c160c0603050601050703020703020d06090803190b0f130506031c080601034b02 70
    0x40e41c2c0000400d001400e000744599260070203007400f0503106c40207200d04101400b50f21184202c40013040355620070045001c042c4200182c20015003642d40c00062424030001d904044400002da0f280031429000c4516199801918258070580d0080c0c00c20219601220044078141e0501c070140340d000040141440c0c040e04c0901c041d6101d0104000301c02c24000d4202c410888000811a0315841a03004000741c0d401a14003103201100c100c0c3e4400407100b9511340480082c15402a0352815002141050746602401220701d500070444450380c4040210f030310781c4401100c551280c6c07a006009039000c20401c00050030800c4181090501944001a010b0600d55a4081581c8140c40701c11429a0f50903030419803498034420651901800c4400610304840400401d440d014072854008081ea2b4550000d0484c0d2401d019035911002580d4030780342c01070b4090134007508285c010b580740d600003494011000006000503004500c1c81c840344240c0702070320002c0e80e404ea2038035210b00000c001c140d41495400c1e070343c500300740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 677646735 1250 677645485 677645497
    0xc05040c1709010501030507050d120f030e01020c01140106110a031d040f090b0603031e1305180a0608010501030804180e011506080f06010e120111040f1502070302060d1a06 76
    0xb400108030365245080c818908070300d5030011751165042603e00350000c0c540c0c4500c40c000c1850f07401e04900400c07203250207400a201c81410000355500000308072401c0c01c010351180b102d0320402d00424070980d072520000c03100362410001c4815a070307000b0214007000c60301541926a0b01409240848494440480403c00b600d14600e00381042503215011a01044034107131031140d00c00c106800031810042040204601015080c1080c080e9510003d003100308504e048110101801000d031a0380300103e0f42c0344086000c14400c940e410702d010324140e000b082c148010b001e800e04172608098500c1c00c190804108200c000c000c010085081350790380005030358925003801a140744113600c000c1700d6400c80c984100907040020050108900c003641d071040200703603a00801d000301119002c3e915041c852a03841d4005005003c004042016a000401c00095452100d400f140aa580030708910030351003408001030b030f40c8070203070701000303620074000d00c1710340e01a13512540141090b212294a09010b0b1040740045192513120f6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 677647985 1250 677646735 677646751
    0x90b060f180a120614091c0c05060c0408060a0c050307081306060825030c1202061c020403021005070b041704050d140606011701031502120a0c08010906030c05040c17 73
    0x40c00203400d2041c644100f01c000010150350840c02c0c1b0b049680945c4803d04010116502e05c030310483e81481034031652002401e00c1d41301c42102d2490601c3c92580801d500103104113901885860300007111229076008002e25000140c85041c107648800206403080000205071400d15541405080049070485c00340c9001030107040d025000d280c055040c6194403020f0740c00189070b25141402d040000881a0b0725003402c41d40c8034070344404115030f144001a03580c81034050160325214100800700341c00166034000c104981c0300311420307a50040703072020681d020f02600c48003810b6411402c1c0040d0124000d00301694021080341101442c058403200000e5800c242d420040d070300340c2000048400da4180c100045604500c1c00d00304800c10381500c24129446040501000701108203215190f00c180c0300c2a015910a015040400085450602d074000002d0a90704074010016080c0b100000d9004464854030007920f42160404080904290600014003c0c4095050070400c0b5840101c001005041a0600131460 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 677649235 1250 677647985 677648009
    0x30a0f020103050c040b0304020d14031207081602030313020a080d02031e07052802040c050c01110307120b0f0a0f0905060402031501030e0c0901090e0106090b060f180a 74
    0x34000101101c00c010400500301c20b04120522004002c481581d600650441e00702c0036400b003514000248102e8a00d182c03585110100d85940d100c5203203103000c0c1c890745c1c003582c507588199200040b450404980070b8070342026800400c0401c00d444500c0c01d560a140d070024006400300c070b5881c00d2140c03401c40141406001a08041000e510a120742030040d4050a21078050394100400384d103c0b162a501d0035002084044e04401c03240c52010010b10070700112a0f0000c00401240c0fa101c84007404036400b145a592240d403a081030010300300d42100c2984d0140d6020707a2071303c3e44031450740d80602c000c4c0300700041950b0107080d4603041071681da641c004100c050880300b200c1c25041460720164905840019010a100f640103004000003102e80e4110b52040c0300c0c09280214485c10800d0007541000b480205080c0c00c01882c0c800440ca144503604040c20500340314000300031080e5220200d4084a0182c240306a00440810182c05511200f0018242d0110449110452540c14100080c10a40594050807044034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 677650485 1250 677649235 677649263
    0x40b091c0e01080a140601180f0f140103051519030606141507111309020414190501030c29070c060f05030f0604020318060f01241d01030b030a 63
    0x644210015080448200144420842c40a845102036030050002e81001620400d00440c5465104480e00501c40f0300d07040034442d50ac440c040d001020060080c2d1520800080c0309140c07651081c03103402e104045400001c4041c82c101003c000c03090040c1c410000118250340741c0030000c91098403c2c0b20013883c0c090311445603c07080c03070280031000c86100a1481100c0b414085c02010420800522510ba50101d035071481a082030049480140120000a9003107840c14850300300040d150794200740240d0b03d040b11024407407801d00744041071700e03004d00004101d228490420428201a210407900300f0380c0c02040340d0260110441c00c6c40c1e01da042000d0a07108011101000c101c0180c22201c0c0f0030320114035140291030b5260011410400c810041d14043c090f5031300200040900324000c0501940e5500e1070b042c0d030014140700b1640320313007070070207018030125805054400600c48001441100004e201525224607c2840e07981e4006072111000802e814036844da01052210b03034091000380110351140501c070300d03500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 677651735 1250 677650485 677650487
    0x1606020c030f0c060f1b0c0a081603060c0c020d050c1503160e0402160804080606010c120c02192303010209030a060e010212040510051509040b091c0e01 67
    0x15051a901079003003150300c402d041c0e00c0820303d00743c044015100a42c0da000b00c1000c13140d0718421000c90080c0025816210030b400880815050030107602203569941041e100c51003039440724050f020300204182c6100041001030b2440d0880302d81081541840c065180f0183c0110701c240d041007200f26281d03004101801034600e0712425020f0781d8030a10f400c1ca421458024140071100c2c0b0091410703c10f0091074444848181e035260121903100302e0051048101000034502214140c00502a8001034015180044ca055201d411008441600050f28611940c17144005440010324124142d811410300d940b6103512548840300c5030f000b05014000d040741c10036020000103003002080500c0e03110381d004000c50241c540d000194891015000312000901240c280b0710390b80244540210340d1040c47c070a804000a01c240441e842208080146087c405941c03030000035900359040c00001584800c60101150101c0d0892002c90750042d40c2900f00c0380c003000745120301d28140e0a19401c500001c2c3c0c05c000044015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 677652985 1250 677651735 677651743
    0x203220b04080304180b0918070b0d0f0e010b150706020c010203010b030a050610093005030a1202030f0c0702220c170c030a02090105071223120109020901030e160602 73
    0x6078170b080c5c0100002d103d07450010f16000000b4008400e04002c0b6000c0e011210024804c0000802020f030001d42c0e1802c080e003020010741a000d4204003250b2401400c00803100042c007030086120401417039810842c2c581007030358110b0342241d2403d0355041e509201c28003441c030003440154080d0400e000410745a00c1c10805c00001d480000701224040c1d01104003200409030403040a00555104184070070314010100c04000035100c1008600c1102e10405030b00006100010005006c402c100703650b00e04040200300886001e91109480c0282d20040b9040002e29002040c000b803e131240c03005111000100410820381e00800603502e0f24840d290791081255900c1350056050523089650f00740c544801d2500e044d01070a0b03804020101e0071025000181029507a105008441c1016070000380d801c0411070012000301b18500c4014449400300489440552843c41041500d0070076540444900e40307a030a148250f070103908039880e050705242d00c0740484031101f1401d000720a45111011030341111a858000024a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 677654235 1250 677652985 677653019
    0x909010506130b03190510080f06070e0105090d060207030801090f0c02030d0906061502210412020d0203071a0c10053304020703020f0c100203220b04080304 69
    0xc00c1d80100840300001d600e440640302210300c03484a85481703a954030103000d40c0c01c200009a2510900d0401080010030f0b420807035400340c074446402c4642c881c18451406558810942d03a4030085030f64944480c01640c0b00d02c0c0200103a034000342c2548a0500e16075200d20030b90304800c5c0100d011403d01c0d0018025a15244201d40c0016000003003401455100c640194491243c80c40101c0a151110518010701400e508250001c24004c542110010b0b49140b00a445410f004c207041c184d0041040c1070083c01801c003068a065884c50704900154034081e900f084a000d501d041d049030140924500007554002c00c10304a480005420f40035643d41000e07540136030803d4440c036083c804e09894a000c1c40051050394aa081c0000b58041118071020184080d2164141c5d40d901c68640c0607000289150400d540402c500c45480744800484100c0ca0b0100200f080c400035401c0c0101c01039000740075103545118900247e4114800032006503102070389400244116600580000001e5400040c0401c010425001601c0c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 677655485 1250 677654235 677654239
    0xc010603151b0e130906021905070302101104050909161503060b13030b0403170403091706010312050a1808160608010b0301030b0705120f01060f020a172b0209090105 73
    0x420604003000103001044e0071a150800107035500b46081c2001500c4d41200d22034826000f030900780e201040070090456211030400c400601452040124030341490081c00200c0a41e004034a04060030f00c0188140c8241c001c000e059a807103549034911620000407481001307400c44855070550302102e1100902500c0c01544040c00b80001040402c8100102c0f161001c10303a44d00450100b440e440d1420300b19510107040340440c40c0d00448a040c441010b80001e12001124034050b00d080c40001640903290711031509100c007400d820381120130803400030321800c014150000203081c5403142407075500c80c020204401e50400080c0380d1143c880d803648403d031800c481c0014517040c54038000c190b040588402d8140418800200004100404a440c1c0c43c0a01c050b141080f030a1501071003280707003101c1342800307280c1e0030b10400c0046070000c080e0b9a4903500c0410180360a0ba084140d00e00d401c40c1814200c0b001e58080e003880040030341d60141e064203000346000c01d00d1224440303680160701d07070030358038108403940703006170300080c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 677656735 1250 677655485 677655497
    0x2030a060c3e0c0a0501183308090a1101090b03190b0607080d021305060309010f23060d110d060605041d0c0d260c1b09010b0c010603151b 61
    0x7030b5080d03031501400b405445c000c3c603100b4030483e52026028220f0410b17410071401c00d24041328080240d4606400240500d100100d407818901d00c40b4002d40300d02c0c2c0c3c20303919540550051000e80012403e200c0e9984074000061500212155031620012510b801c02c1d038200c142c4140307503d54a058400340f4000c1410702c0038111500c2d85000b8079547d07003c0d0b15216140d20301000300d8000c107250396481e81d00220180140005804150382e0f10304000040d000f0400c94091692440c5031070416040098105000d00c0e0341010782c100c2c02c03156104d6104102c0704809000040341d08881543c880629615401514040035110310340129803107050070304010a4807000b480c003000e8213803505011000650000f03401e8400120542c0d490385400194201085080c08120040c1d20700b81d0f10800541221416038020b03d8074403810803d486400103213888609000b803070384880030343c0209107200500c214603500001b0006254182c00000d03440d40d880d5200782901c3c04100686186a540386925001c030b402414450140388882d240c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 677657985 1250 677656735 677656753
    0x1109090907050634230c0d0204050603030409020c030301140f130c020f0706180918021e030109060506030610030803012105030f0307140702030a060c3e 67
    0x4a40d55000d00c2d000710400d8080e025406034842d400c45100b00c0b030740c007107192144c2c86012582040395000c0d4007220b0581034504401003002c051000401e5845180e00c000f0450208001c4030340070032015060140c001c540c5404200400940143c0b10300c010450003a6910155880e5854902419048241044803901401c00d07100841825a02d007500c031300d030214001400040040c80182d08a19046e5010030425a07480b07005004142107800c0500000847c20b0049200c80c0c2d00d4440c1d640005546204107200007950310300d0071000040c903105a08050940442000c002c0b6420510000303803e648403840309481c0e00e41d44a05000050034103100007075103e80421801000c60b89144c0c3c4595061105101c0c640d440350341c090405110400c03844102003070f0f580101c08c076a101c041507500d1400756401640c1880104590178000c0c0d14900180c002c0e611f00036002405810700c0716813610741c04041c1c07103124558010050100000e44044800c00982d0150800040c80421110700e078080e000c242d100800b601c81d0040d8821052 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 677659235 1250 677657985 677657989
    0x20406020a2d140c0105160b0c12040c05040605060702030d0f02071d060a050d210302070204020c01060905090109020d0f030c0c0b030a06050607110d020a0801110909090705 76
    0x55a02401c1c2d0001c00c0440789801003003090262a800c45510094140302600324050020348042d10410802e45010f880c5641d4150300151150300c0303a0800c0c4050400c20001c0c44020400701801d143e4401c2c4503802140c54a5481a6400d0746d8040440d07048602144480c1c052005040501c510702c003900d01034a2003860451150000781d961080c2e4500401002224203680b00c1061080c06650001c002e051601441c650703000b0040304050004482c002d002c1d04580c84005000e207051403101c092641c001440c2400385c1040c180c0740264460451255003415000c0214100686840c4010212450382200020344241050820360584c0e102800c0b90110381c1c107003038100f005070b619813410014065022002040c007034001d1a00342d0b020202ca0348081d1104050400004000c1590b030b000714420030310250200012911034041002034040c60501402c0c0c5040f03140e1048060801010003042d650009001f00740c4569903480c82401d48201e0059075010220210340d40c90203052101c8010740104507800642501410040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 677660485 1250 677659235 677659243
    0x1903020c1c0f0816050a05011104060f050a020721170c030f090409050f0d26011202010207170d1206030209160e03191b27020415031d0102040602 64
    0x240280c900c4204800c1c000c2080301d043e040300d6020040c1220788a0041103420b06545400181e202900c89500340614280d46074511402c80e401d95029884100e103c00d6010801caa86801400030f02c1c05510501d5030204444103110401c43c24410500c508e00d05454042c604034020500488640d00c05d17810520801100c0100070080d24202d1504a8140303450b20706800016025106130340001d0064002e05152050105010511210030b040a4445c50a022040000c1c009a0151075106014071380050005114022511101c7d842d00b41c01441210001610340a40c0200300d12404105c180b00e80c001e44415407c2c2d80c100c40001400303181024104604c515580120704035001c01440071700c00c5100100d88510090040f00b9a0380342420242c01c0756070800d01205100300402d202c440c2983d1807460791500302c00b81d0016000c00005e40d8662220398078140001c0b940810030407c026841e02c00799800f404081040411030400c200c400006550200c0c404844e13807040d140c081b122010201050340100000d01900d42c00107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 677661735 1250 677660485 677660539
    0x100f0c0f0f12091a0c10060902030108120f0409090203160b03090c010e0906100909020c010504021f090e070207080f0318060f040e0433060815060d050f1903020c 71
    0x2141c15a441c10495017050400e01945425034403245080408900d00724a5806981a00c2000c8200c8803003500450000083e0300521070812010315082000b40041406c980148022a1026017150141e00705041c0c0324501e2810b9411520b50850088204140300e42e00b0040108500004c0c2800b01203a150080400d00514008240c2c03402003003001030360399a448c40f03004000000d00001d00304548070525200074902a080070707282607204450300d03081c2c244880c0ca4500c112a41080607100c08034000c0c03130000140803141c802032415041d0b005442e00081e10400034040d0300700040e00d00001c0c5a564011110600d100300c1c18851150080d0300a002034120220100211402d8803110781c2e2540140d500c0b81750101020b4000362a440b85004030801c003000040064460f1010361020318400d00c9415113650820f940e8000105141040c866880046040c03030030401203d00c18140218151100c4c40c1035030a400346004010b44018400f0403204036400d041c968144030360740c0050b00c1102c412401000d06504003420400384 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 677662985 1250 677661735 677661779
    0x90221062403030705071d06030a060504082505151902030a020405180a06170a030315090c0f3e1f02070203060108010b100f0c0f0f1209 60
    0x803070601c081e00c426040784840a8000808891351401145400e9803648402c0c801c424440f640c1c0500808192506003000b442414003600400f5010348944644025000c040c1c0141c0742c107602081b00c6c55001c0e0003101000342c201d01c181841600781800d407404c546400c2d201190341e40c02c800c90100340007519500d46100101500540409078407900d56010f030900071f1059500030741d88503641d26105032038101c0c551030a0f44614072008040103401e0b600c00700700c40440342708440d0f100d141c0c101c0881c10001131700035888081c68010090005040c01d4540510004403040400c050000c030704010031a12601360f2191403a070076100032042000440c0381c0013010b183c0c00c20f0b4540c5400c0d40c1c15020b480e440c03000401041652181281c042d4014495120104840000d50015406074004c3c052507001280c050014042c40d090764802a08001052105a90444140d143c0c80301e43c504002d486a1010080b4035840020007505001d050718601005091521418005542d00b103e414025200340411642a03040310700b15540d04a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 677664235 1250 677662985 677663011
    0xa23011d0f120708011e050a0b0f0d03030e0106030b0103050f0a051c03090c15110714091e010e150108060108010603020c1002031003030e1503011404020403050f0109022106 76
    0x82c228000e4203095540c2c000d02d80540c68036502d800708010301003400980840c4100308014035141c45c9640c90640d00144141900415140c080103918140b1803580b0329014080d1a000480f1840841000e0030355500340e005480d05034603c00140f0501005002c0f014003008100001d05200025039541ca84613034000000095421041021b8918140a90840443c03160b1010500c00600d0312041c02d540c03900741181080f03000403900614280c0c004d03130000f41801512a0380243c20350360342c420070420141440052220380042c0700144401d002c4000c4444446c00703000929940700c0c952401c1c91000b4512880320b00390781e040258400c244038082c0d1308002d009040d41d442e132a0142c0d648100a2029141560609a1201080c400000c01010107110b1a004060724030940c0c583c50383c1c030440c0c001c002ca110031000b007620b0a19020001000a43d5200c000042410760180004d030501d581d030340710b480c18558070400308400386c0d444161361011480c040d80e890390842e01e481c244682d0b5010030a103469540364014480c04050310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 677665485 1250 677664235 677664259
    0xc1e2a0d06020708070303150902040e060d0309030b0a02030601180b070f061d0c04050c0a08010b220303080f01230922030504081219030b0a23011d0f 66
    0x103601241c0107280c00c079418540c5c0302010314005005006440703030381d9000740f61440085801981d0303000300d40444244030090b06464a480040000301110796008806004025000100154440c460307070384180000c5900580340e203003510000d0503e03a1810108564000416001d204030701c844029100300d55045400c03c01c080303c89151010040080c5100f20088584204085801a8000540a20010081cac40034003454440b41d4041e0b445010f0101e03e240402c81200041c003145240a000d020241d206024080c000c2842c98500075408034a40c00079400100d02e0020480c000f5241c3e20400c0c014034144151703142d60610129400f510380b031005011441018004042401803100d4000740740d10030010840c0b8481c09480e072401401c0355100d481806000d0195511200c0d81c01c071800d041c1c61200500c01089180451504811401070241e404100c0e070140c0460070100302c202440301070014010b800302c842607017010307588009081015000842c50040030b0314105080540c0316241811700821003514600f140403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 677666735 1250 677665485 677665493
    0xa080a0c030908030a0204050111010b10050715020f04080c0a0b03070e03030403021804020102070e07050426120d0e0a020a151709060a140601140a03020c1e2a0d 71
    0x300826102401603c0301000b48005500581d00400854000340c885007010311101d002d04d42600c80c1072500951002e800d5101ca041c01d4011360044c044284542002c0164654054111040380c110f40c04411b0136074070100c1c003800200b00801c59502052307400c85e110b50596181c01c8482c036035440010101c0c0100700070009040b0f440d84082003514050f5a00500b9005d07640554024001c5540c021074099006108480c4001000e030709004449001303102581c0c421f4070346420000140b2140c0d07181020385a810400c08044890220107014a0000d180400381640d52051941d201000b601c0c44007100503507903088041400010ba81d80000314040f074400c003480c0c050390b80d06207005a03a41da20061100c92060840c03403c1184000700861054800c0861340020860758111038495010b0800445140d07010841c1c88000808081c221006890400c0e0913280240c078141402082900f080076101406850200800117010b11103002c5c01100049208981c170810416200c00c01e202c4448801c00700c1d540540c05144c8020180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 677667985 1250 677666735 677666741
    0x1030c03060f090209090c0301030b0708060a05030a050a030207172a1509100309030f11010608031b1504030c06051b2a061026010608061008030a080a0c03 68
    0x200140510505216561043c80700690300c03c0b40c2c054891080b040008017402100c009032030503260000e900e108290348404081c5d81c460005040e09922100e9104000340950341001091410740c0301e000504143c50039860040d00c0e02c0740c2c9401040000355000e130100850140000c800b02c09160070000140000050400c04c8a00c0c00c0c3c8100c06d54101040e924a00c85e107910348030040c8050341d0f0980b6079040d0541001c01c00c07401c0722000301c070040c0011454841c4e07000e214454910030705c0c0500c0391000040e0070355460544502d0b640c0485400c61b819241e20300d008039203100601802c110540858202d02e003e1030150b500408032051080000c081f507540c0c3c0085214003002458030440340100b49009680d808810600040007003404140804002c2e00d6140710712103d00120b4624040e8000c00c0445039828140702c004076000304d8035809410484105c0280c0c1030014401d001d054014012040035000504090049035004001030304400f900340d2080048003901d95001c00b41c50740c032410701c1800080a9000075800c80103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 677669235 1250 677667985 677667989
    0x331503040f050f1609050403050405010e15041502100504050a021027180b0f04021806030408040806010f0305030a030c1b0309140a050d030c14012307170601030c0306 73
    0x109203d20b5071038400300540020040d50101c441c0d103402000c59600d84660043c4ea80072500100020b5051100b0880c81d40035028250104074010708069101510000f0155190090b910800145003c1f42110704407035010300c80c4258030390052a090001d8a003c1d00d5007a0303911030b03401c4001d029400c0800500700480c0b20389050780380100e09080d100740101d030f0004200c4803100503000e00303010052003907403031041c50f0600d106005159001034004035510810304d04100094001d1041005d01824000c00031aa1703640d03010045100d1440b4003501030f04c80d801c03c03a03020f24202d4143c103e07802c0c41c402e80c2d200f400400d1000090b102000614a0302040900340c544041324560f1048443d0070010204e605a07208158000c0455000c2d03034020340552005684090800c201c8003014441c80303420034042001c2c000031030722079060200b07010700030360300c1c0d078413503002409124211103905440c444540d07040c5100c400c4904640c0d10460b007224091420a4a10a640201c10003a102c044e140a0501da030300e4002c40e891178061f82002d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 677670485 1250 677669235 677669243
    0x2a03030c01060b13060f021c021212040b0c0c0a02061605060405011a060a0917070f0314060601080603030d150513020d0b010c080a0804060b0405331503040f 69
    0x10360b694070f80a0030201d801541c184109803100600205041e0304c00c0c5180511800294010112081e00001c6030f600032020904404c110b006001c003004c511180e21000700307800840203c41480030b2904e42400140103801404403070750000b0030441e0907210311000454440d4290102c072895a2000301c0300700074001e071f107100300700134503500910b0104024410190f001c8100c40714441481c0d00e40d1030740d9500300282c0780314950075030010030f60f0200305011a0181818208507000340d081191541030703c810681c2c0100020b54402c03035810841000d808003290080c45403581000007030800c1162420070f070001030b86900440844200442da9416464144410300001100404000e4244400140c00d00c004c1c402279800032806c866854200035040c00c0d5540300724800440d00d40c0010201c1d0030402c801d1821181c480022b80251961030300da60528401d136842c2e00ca2350f401a4400351310742c2c0041600001407032001a00340f103c0301d1140c5030600741421076251442e0250b000c140764500c80b6540c5d50340c0e1078103034103003200041c02030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 677671735 1250 677670485 677670491
    0x6021f050105010819060306052401090b0a03050405010b0904051006090b210709020a0e15040e19110a050405040b0a150309230c0a08010e031204030c1b14032a03030c01 74
    0x400b20840e5010309c000103c00070701c134a2b078820384428015a105a460300c80d120158004010701180356200303a0019400c83d21031030011030078100590004134450010713101955242c10403055819002c20501c079100c000c00c2c03440740034024100c01034001007401d10b0f030700d1030040040192110216040800d001030700c0a0941400c0440d02d1705500c1000800c00faa100969a0041004024910302510100c0075a401c44549100c030b0b1940b50755031000100d04d0507452b05140401070711384103650782904551006e00340c1504150382e012b486614010420050300c5602000d240903000050040c0000b031050320180c80700c0c440600f0007040220103031609114003401e21b20a400c40a03c0400c8158440b400444d00b02c02044049407d541e000b9100c8441c40e0032a860349a40c9042035008000050f00c413820304000700d41c007034000d0803c1c2d104248540c940350103030100c00700c444004160070007040c00f0b003959948440508000136001400c0301c075a0b1a1b003040100715581d03c0b650702d000d85140980e901e03a60402c01c84401906940081c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 677672985 1250 677671735 677671741
    0x509060901110a08090a0e01120f05210a1403241306140102060c130909021f2c030a080d02041503140a2f0408030406021f05010501081906030605 64
    0x4000c5d0000141e031803042c1d9015100240561800303040710705039407280d6841c4081d07000c00e507200382013450f0b01001141c850060040400001d0340f1018540f04004041c42125580ea208a0005010841601200c0390000041c8180441070300c1d1800150008078004036060301d00f142c403000180100e20035844000940d403d00e4808551405410580740c0011800e030221442611a010308080728010f59400300043c40441c00100301c40c40071908104880e0b80043c1c0758080100030600f480c48140e00951000001c91000c0310820070710a4415240c0d6003105000100424035120301001948070121081c01924060000c01d25010310b41195044800601c4004048035641a4039200600540f0110900100281030140000c1000c503031402040f2003001d40c048610400d6211008001d94512821054084220203100102c0c10104c1040180080c24054000b40001c50090980d64040310030110b0300d521b0a0309001c0104810b076007000d10140c1020b0100300410100a50b20801c00007031011b0741c0007030142e50419041c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 677674235 1250 677672985 677672993
    0x120f120509060d020d0b01030c08130303060306050f040b010806011206050a06050319030f03020301050f21160f24080408160b180114070309050f0111040e010e06010509060901110a 79
    0x400d803140d01982c0c1401040c11b5000150704546c0281071031800b0403800c00024a012000042100740307180309040009025449448840840d441101c50303540c0d00501806000a2141d0320301e13514010a0301100900c8690b0500d02618a0f281c104000241401c1d00ea001251100100350001e00282802030100c541c40c0c18940602448180d014800f6004681542c182100f550304c20b0086074140c50001d0b104400c00e409200620040c4000c4400d5840303042040030035005a80403c1c840340b80321100100003505e40381d0800ca20220258196401840703008000c0700c04414510b0200ca4071195000302e81071584030355685080084040c03107007a2203071005201c010059010421580301c0b00340a610801100b0080300d4060300520f00721007003c000c418844034070070000f6940728804e80010840521400c190b8401e061030002c1a4296460101c01c0c224445d40841c0a0000c01c01100c00503004055240ea4510710f8282500060464811440154000c0318006011000359001e900980d44042e03c110441d4200019800c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 677675485 1250 677674235 677674237
    0x1b080c131b08180607140705150916141309020303040305030a021e150f063d05070b060d0f051507030e0a0213020c161401030501120f120509060d02 65
    0x800f007441600000c00e0212034180011502d10590040e150105074144119841286800c11002201ca0b489218080003c00000c1da68060040202c000244148085940800070f0000141c0154201d826501e509c90111741e5448250407a150645200045601e8140042411445140c00c054603903c40051890a043c1d40002c2490300f492043d40025000003100d40c3d071a844506030401050190007050204d011000100c04c07064004070000c020b0450500a0041f0a680526401d44041c17821001001081e100980c0c03903559590b000d603071400610700881c9503111007a440018001303e0040c1b00881011080120300003036041000d4100086448940400d01030552a0500700d402900003801e1401e0360025810004c0d80000036903000381900410780c480000c00c00207400032031112800780301c1c4089003c16904c8201049016080c0c40c1a0710070341009a00000d820b64034103910880c2c0a205001d0451301082c8a08043c204a82c0d010130001500300307030744100325814001c00c10038070f60140e80010148040d090a40c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 677676735 1250 677675485 677675491
    0x21320041a090310050c0d0903050304020a05120a12020a0c03050f0f0102030c0a210c0206040303050c0319021b01050705040602060f01060e150f070c031b080c131b08 73
    0x1c40d15040807016100c80407242c040c511000341c01d035115003185012004560841ca50040340c10141c0d50a00072031004820648420100940208400006000550403c48500d1001d03200a031003203040c0c11510b010403a41c501c204a0b015000e40301034440481c00600c00d1000c02011504101210007181d203a0900755294900003003069401e22440350140d5103042c040c001c3e28803501c8444481401c04000810540300002c4010070365855182c5400d401504c04020b11491950420950040c05030b03151915001d0102c070fa000e400d460001d403061037080b00c000c03c44610700741600d008140241c0c0f02d03060b0103802d101081e07640032000080d5007030804000701e495104c800f80c0102d540725422218551501c07001005c441c01e00f0301500c00028840080280d6034148880055114040e00700010306c0c1a10010303a5503003541004100b203411500b2103030100240301c003034514280d00304a8040c404803600c0c036150139660b980c80d01814031030051001403141580d40010740d00138020004c8001250403014a0501700038400c007000c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 677677985 1250 677676735 677676749
    0x31606021201240c020609040e0708060a06061d0d12051b011b090e041e06180201030c020c0d06051e0405150f01080304030803181b030c01030b01090302132004 70
    0x8031981c281d01d132003210030244490300a070407246840204018480900b0041701081c013644150900010b4880302003041e01e12a10a001e0700150150401e20014962081210211031888003002e541080380d442d0302c40142d8807036000e000b00c4190000395100766400e005502a1580b94000c1500340c030314080e4190000e20f081c00c848500f008501d803d07200c0c144e8084810380260001480206e001500049050203d5000100c0e900340c001d80e44030715a6140d005031003c040b40400510342015600e0110b5030940542d204155850018004001200010030750b0400640d5025002d10b455902141c0d070303034800016104640d01c40311002542c0f40f038a4206180d641280040c8004c49003000d6000813100e000c050600781c181e5013031402452500c1d2468403002d082e03400250410030030310141507104c0d843c04010840e1a00402000c0314207801d400300c1c00109030a050645034160b05040c140300b45d01416070b034003000c07220540c5d0741155400100c4003c61900001800d8002c12868000150711b500d0451583c001c01a00450703140d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 677679235 1250 677677985 677678039
    0xf060504090b062409061b070303091d0903090d03050c010c091404022a010b1e03060c04080705010c0c0905070507110a03030e270a0903030f020408031606021201 71
    0x340c0800c80c0042d85010340e240302450620a00d451780c50400b0040001c072001d03002900400544c144045e08200d40b82e0f0017140400c808003030400940c18803107512243e4100340c91070074801d440d0600c003c1d40c072445047c801c0c40c46201084000d00c1058048c0c002d40750412807400c000c0168442d1844050543d4400b400b4070203044005540030081450103000300c4d08100c43c00760301010141890300719003010001c040c8103401c0d035540b21a805c28841c0c50b00800c0d07444d590b14401c024440e01d0080014181003103c09000c442608808210a120420340014031000301c540a20b00104412010f041001240c3d540380c0000c2c60759801c00c1d00780041d10350b116000d800300d94064030304004040c05541c10011ba030f4046120042c023064203080041d50929080c56040004009000d003203110115014409000e00c00443d150440d40d0b070b6414407a418183d040c8103070107010403c3c0504600c0d09040c440070380e68034041c400d060701711401002c22680030001c882d011f80c1c0d90b81081184025032541c580d080542c55144003626000b02c0c044c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 677680485 1250 677679235 677679259
    0x3030f090e150406080d02190309120c06080609070e101404060503100608070c0b0402061e1b0106140405040519060219170604021b0a060e0f06040c06030f060504090b06 74
    0x85c0104114860410030703002000c16084000219617039140e40c800580070b102c0b100c940020f201c43d04e0b094412107148a0400201c0c0300342030403006072003100040d1045009055000820581580011508020720b00482c0c201488d800d03204003c440b8051140320203610400c01040c0011420303040740107903002e01c802c0c002c404001c5031164421100d0390f400702c0d040e40000b030003a01d0600100340b4400340503410038006030280c3d182940b4400c030441410b11403103039020714100020700d906200b46070500089440780048024040c1c1840c211b1102107a041441e40710340b0480d6100c1c04181084010080245c2d102403010100c09096024204030000303400002d103e4030204100201d0088403172240d0b10201d12440e12020326122a10382105020094002d01c450b4407550300110b49892034182d082110f03d003107034450240850040c204041c16400c10050000210b0180e0200091000080400c003800003620350600c0d00240d14006460542d000d010360358841b0350042d207041040418802c0392100c480c0314040a44000c040f40c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 677681735 1250 677680485 677680499
    0x902090f032a10020601060c0c05121608071d07050408060903030403030c0318110a21120504050306150102070312050d0c08010b0f030624121e0103030f090e150406 72
    0x16000148040160000d0005008640c0114200d403103507401550002c409c01c0c1c4580100f40e0002d0075694044459000214803840300d543d42c81041d0240203a2405418400d00d4811440c983c2180e0200f50802001142c001500d014400c006803802000c080d411180c1c141030a40042d40c681d0300a0318160002030800e41d20081c9103001e4020360f003001070054500c188144090310b4840390640da000b40719502003c2420005a070351807c82913442844581d001c00d00c84000c240c07521501d044034040341340c8240481804200310941e404180150700c01c140680c041180c4800b10f0040b400e042c01d5410080540d20060020f6800a42c01400ba140203504054204002d14550340c0507100701e1400d2046200c250301c01c00000c55a0344001c8040d68001e2001340020031101800c00000c41115120404517a4410000c00c04041c4c40c0344180407240c0202040380a8189031001d84402101d02205000141c03d1101900f05042c2540c4164010b400505022061030321a0801080c52584c0e4008890341a100d1800c02c00085102 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 677682985 1250 677681735 677681749
    0x2040f140d351201050f0301150f051912020108090a08040303031b03050603100c2c03060109061a0f070b041115032401020a050304081005130203070902090f032a 71
    0x203c85a5003880d50309a04c3c0a04001200042440051709075403a00604240ca4204510319005062002408045981020300340040d00200041c00300101c050440f08226406d6004c43c0c4281860302840c2404443d41d541c1300440c5080c0d4804e45c010702d101c50009e000420700d941a03010040d0b45c505400c1c1d824480f207078090210283c54090300c074641e05402c21301245480f95106d50180b800f41445051213070304805004400d0054115115850814289050b50441c0902c0c0511059001d0700344d100e402c2003c40c7c10455604595a8800f0a020078100c1c0040d80724030340300c0c000080c0c403010360340b2000524407440c0c0703441d2010a4a546500d403034000d41c0da8214001c100b48078541501d11070b620f40c820450341540c0302d07001e0381c0450700810740b1503040d805160b05600104505000400182c0b2100c0d00611581403844260b07800c41c0c0004055045103e1641072900069901145001c112084040c001d6120400340e4005441040740300c002030f038984a90f06100b25640303c21141e105181c12840d03d10a0040d0f01d0106200301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 677684235 1250 677682985 677682997
    0x409060509060910090c1718071a0a18030506070909060b091e150c07060906090617091f0f05220b0c070c0311030706020102040f140d35 60
    0x1500f880d0f070a0208036030580c41b100c5013042518000c51240c0d1002c2c04210089403e454400d400000f0024500c10803008008550013415400240c60203c1811002c1000038020940e0341001c000340d5144030031180003101c01c000065500901900e41600b0107044c050800a00e038421100b06074144603001600100010649860f844040c000e418558002601c0580649000000341c4c0d00612003594409041081005000c0444100004202c080d017040e00150204426078052820011846018401c09030700015905501401103d00d480c0c42d26508080d900b00241a01320300d62003942800b164403100d103182c000740d01800305840e04102c561110100c1d10711100768251944d0f0270046a555004c00150010841d0b94000d480403c0f8500b84005980c03080780490255205030b072200582d0100440130b180a10211004101d5030000714070705441d06450145e4000280301c2c0e80869000035408403159142c20f112040400d034040190129000e0fa035004412101038040c019608201841440c1c2c0d000c0f02c40000c40b60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 677685485 1250 677684235 677684251
    0x4110307061b0212060c0a0201140c0a050c010b1207140a260a051f0c080720010906020c070602160315090201020c19060e03010221100b04090605090609 67
    0x124059500781034540015042c500300d801001d41040b88500c08010310283c0e0140096401066845400c06002803e44281d0701114038901c2182080c0a01c080c0840112000c01d81d19003009030301c038008110b126004194151b84190080d074140c0341084500d00206850f03040d204009001c0c0010500340c001e000400c01140140540740d82c80100294441d480d400855030508405821140711101581d641401c0032918684014405000c0c081c0c0d1240070403500812500307116030701d090f440500e80305078014005203030300740142a00381542c1c4401030342d02400c0d000002c900d60090001e5594001292903580d0343e0b030032403003200018010b0101e101d50010203009290200e0f50840342007512021a010b100c0700074541040704030305620613961000250348030300030350200103c0c030003200400e0249002d80103040303003038042c1d09544a41d10401c00e40d00c184055010320002c140d00540103c8590355041c1580c940881c080d00145480100460b00040c003020301c0d00081d00f5540d0641b99240c1c140c031500217100000f81c1c10b1320816 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 677686735 1250 677685485 677685497
    0x30a0323040e1b04120605010e09010b090a020c0c1c110a03080d0c091d0402030c011b12050408070306240501050702011805060c060f0c091c03021f050411030706 71
    0x504103a20046a00f0712580c1042c414515256980da810a0140c0c00020102ca6440d00e81e00100b1071102261a03a40e40070328a04000c0c00b0041d0f5440020b500081c00918001005501040c1e00030000300800950103106400741c02402091405501405034200c40f1a088031042e848035034642107420420200c0048961200701c1c141000f040c1481d16014094038455074042200d0300c0c800248900f003252100f0350b0f40d180c41083d040a82000e0040c541840c4002d0840c0f41403012074003050740c01074a00480c013040142c1040054174664402c0e0301c119804d1190f071380580d210b485290700200c01c0c083c540c0d00402228802400c00034005422144502911041b0f2040300d0104c0d80910150300594000e216801d40c05041e84070102c082070b1241c002035402d41203c2c0c210001c50340079000700f00300f94030031608158009a42c4038845060404900020309809030034080345220704075151052080500800031040040c1c80d840c011340d140c51004110500074101110107844a21803a0038207941400c02091110a4640a903215 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 677687985 1250 677686735 677686741
    0xe0f0c100c0b010b070305190309061a06040b03040809031e07081606050306030718090501050124050c030f0403110f0a08070504110702122b081602010b030a0323040e 73
    0x1130005600440800d40034014204a099041080c505040c0701c00903850302c2c0042d1092040c00c000c81180c1c0c000040a45110007010113038580d80d911020350f0229012159143d07a299134929008540e40124403c4a4040c4125204601100071002d11207070002c900100702d84640d555140e0040d51044200c881d62000ca110f45414000c0d540328000460f4800c101070122001c01e548c40f501180403100c0d00c110a1066a6a442800d041120a00650b0f0050208410b07000d00c102d81c1b28040d01f091804404840c060140000310f001080130309005840c18086001409911140c1d02d041078455078450844aa1046800c040e0b410315904d0200c2050081e58100340051074a0b0342000d0502000f4004c8070580e000741e01007032103e4801a83c4030780713012402d4501c0344060551008680c5109113090188100c0180c81103100301500605540226402e170b1000024440480702181c40070309034010500c0003215030700350080e5600c00d410701d5003103006880500c2d103403101201e001d1040000e504d91030050740184654030b012203000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 677689235 1250 677687985 677687999
    0x613080304020f030d211a04090c0e04050606180f1b0409020711040b01050a14033c0604020426030c0f060a110406210e0f0c100c0b01 59
    0x1940c0d21601c00f03000041015000d400003407404050048100004403c5441c090030040186c00092018041101c18400160704980408050403104a058001e9507038031441e00034052050140360080020001c082c14034102414850f880e403004481240c00f90000034190f4015441e0066014801c0a0209000001c0d44601d0024420300724207031110601d4031811320020410034803038401820000c0c4034581e0701c40891411000d000c1500d4140e400f00b41030180502c000c1c15456000282e105d45000166901d554a64400c0c2c010a00c0b206050b80502040c028148804040141446440307020400100c2c0a0804c0c0d41c1c8070208420b9104a0142d611520450b92140720040b5400ca01d030707006a101d8809407401c02c4082052140b80600859940f8200e510200900444d0b045c1c512070a00340f4850002c0308c906e07180c102200540400a6444000600c03038916100780003d184a50000e04800e801606450040d9003050040b55501416245144555040c1b42005100c0740200d182411541c0c2c84040700189a10b403001e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 677690485 1250 677689235 677689237
    0xe0a050604020f0f0d05010f080a06110d0609021804060f03080706111201030c0506042d0b030a06030b09060906040b0a0b090c03010306150503031b0708030d05090d02061308 76
    0x20006400980a010f10480c00c00c600000e032000302e40c8468500e813220301c1c020240d01940c0301a0701c0003072030302e826003410f000c2c80e44045856014035800c900080341000800700382021900c0781d490b809a540d4548032003c25080700e1500107003040d0a406082c10300d180200d00401c0112611031203030380718103512890700700009900301c0e01429200f0701606000985c2440380609420079808003410480c2601c41034018002c00420009440203041c2c243c0714039045c142003004d51185141c42c030700b00000da50f0700041d103107200509902d124070103020b00c13011540d01c908140b1160b01c050042070208580c3d80c5000000a640c5040000e0801c1c451103113480144215100c40d10b9400c1c807081c01401000440c1d468100c01809615419041d500590485011a0b074961540c24032100315906010030b440c9408040904000310f6400006a940c220584010308800c003038110341c00d07440c02641d544484514000410960040d14003540300e41d1180303003500300355011400b40c1c3c04101d0b251346040b01c5014100c41e260b004080030a00c100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 677691735 1250 677690485 677690491
    0xa03060305060f07050a110c0d0b0601020f01020f0909060d021e030c01183309150318020f0604090501150f0203070818040f0f15060912060c1b051b09010e0a05 70
    0x4160303540d0710080c4000c58142040700004ad40d40c040340400303001c10340d41d041000820442100b80218108180c1c0f08441566114007140b580c03154a9910104d81ca5650b0101190a2694010200680b41980340d1514500e445400c030340521034001d580005425500032880a03800841c03000e4001891803e001404044a502d180400c114100902042d05a0115031007200c8aa0905171a8060040d00c2d010600006030f0038140140205030402a0003841038140c0003101800310741c100c8040c2001004400071400c1400b0b42d910401501d41464000565140d0152000c18000025902e04801002c0c04d03406a9072841030000060100408200411001c61500001d400e020070007000401d080b0a288242020f031a03d491211104584c1c0700c41d01d030240f43c023099003100200443d0030050815272400042c51200b400809016000940700d8010440041c450244040040040c880c0d03400030a100b03040072a550070140715040180884000c01d22480e141110b1224101c40d1841203407030301c0303070781e51441c0c00c001e85406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 677692985 1250 677691735 677691767
    0x1509030705030406020709110c0a0b060423190e1002030618040b070908060907170c040606110f03041406070501111c050c03070206070507170a03060305060f07050a 72
    0x5120300c0000071000d200400003004144d009000031800d0200b00700489040c0c00c07289510440400100350300e00e4000c5184004680c001c08003d500341c0da02808903015003003102c05004041c1600c01c807601d012006801c501c1c05800228124030828090360f0100044490524445015600c208551280402690011075110f41c01800c01d0110407030020b4400c0340a13905640407150312015008100740700307500842d40300c024040300004246a00b043c003815034565120740a00c1451300f03072112981c400c0d400208640e680d198000750041110555661009080810031052400070b401224038201181100009481c1940c9000305107420298001081118507846500101e4031952981c031400b4804045402400f5140d500c4c20460300c0011031300b0a00d000b198801000030202c03140510600c0140303940003c04a9100f40c450610554800c040c0c2803c0c4811854009001800325000601010456042d0440300450303203f21708480e00c0382c45d5140440442c0b24202c64440c0021010b0140603465881035801d000b0303480308 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 677694235 1250 677692985 677692987
    0x30e030f0a0b152716050f0706020405150403140304060f0e03150a1a0406030b1b120106030227010206041b0b030907030c0e0114040207030e03010e0a05011d150903 72
    0x2038400319512844014000c11074903003e00304d00c5000b0202c1ca0841c0d0340301c02400211841d6200c140300203099400b83e01210400e0100100d00b00d0104580d690446018280050400f403e20342c5420403c40e54be44030b03000885040340300d80310003a50035030004180c1e4145c80007502c8010300e96028440c2100d03065185100d2641c144a002901c4604502e01a050b0b80944010340c008100344088242011400070006002400341d031030035104001043d8148001904000d04481c45140b1039080818030f01d41c3d009104902c42e5280321600009440c54143d0b00030141080e110203000341c041d03a01c0c1d600303201c0b8522030340040e405604640700090000721840800c410b070794000b0021801581c1c46515200d12760300200c4403105240d00880b014404d01c075800700048014410b0148129640d0304003800c1d906080090803449025030f80103e01042010300400a044104030302400070440d030403418494a5a51b80070b41000da03038035461306907801100e0f9064010082d01c0c40c80707400103100140c00d101504041070001084943c1c6404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 677695485 1250 677694235 677694271
    0x18080406030218040f0e06010b071104050a1103090307110d02090708040204062601050a0204061b020f06031f0510051209120f0c010b0108160f02010f02030a0603030e030f0a0b 77
    0x5100c3c400c1700345c08102c42500180c0401d101d40b2840c54001c040e0460000550184100030000d51844401a400c150507140402d00f601ea46100e030029100409101d0108480442040094131000004d4004c1900440b504080e4981301303020300030a0401808044d410903204000134450900174605550414805000020302642e145e102c03000c00c1700c0717640c400018152400304c00300c0008002d024054008600c803004514061510902606c2d001d6240840c48407940001080d40655a07103070042d8003188406440240c1ea494500051030070341403025048585642083c01c081110f0514035091071410b403690300c3e0a894a400500b07400c6101000402c5520144210410030542c0c03100003010300711642440e41010f4890101985440c2555500c07028036041104180421103d94820042c84031900da050600d9800c512421074200e001d080c00d00c42c0811000e0000061040c00201d69102104481c080e58030720049a407041e04150300c0e003250f200006959805205110701040d0003c0341942c01c0700e03450034000c103041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 677696735 1250 677695485 677695489
    0x3241a09060d120527010c02090a02071203020d0e0735030c06090609060606030109020f0c06072003121b1b160e13110402160b01030618080406030218 66
    0x544032500f01c000104042002c0c0c501008204c0545000c10600f21401c900c5031801000030808812808040e10456100c40810602c008603411905869080318a400c2c100d5600c49015020f903100d000749071300300ea24002c541040740b0340104d50041075030400040d040e10347c00341b408104014000039030030b40001120708030485040d80040009201e12000c6502400030342c9042c40c0c0302801c000009022407440d4110701c08020b00c0e6030710002128191141800300603292100c8400c195014040c00240000ca0720404c0c1c00d02543c1c136041903500b1a420038035500f00c00c0040310b414615850b40030787d600c586040080b00d40461202480d20400d00e540e8040404954140303d451403600d50400e40001803552560400e90041909015a00c10703c0c000d403500c10000e007140d00f08840741c00300713413000717500e02071302c2c600d9000c0e030000096030380c0d8040340c0e80708041820013820b05907507003030030390400d1400c0c80304036903041c41c2131500032807601200d0f0912031051300840c480303040038a4140150080e502c041189828022400d014407825 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 677697841 1106 677696735 677696753
    0x604030f150e0a0309090e0d12020c0c100519080408030f2505030a0b0102070602030d091a0901020306030c060f0d0b060705030403241a09060d 63
    0x10074a0440c0c1c200003000010300d180030728010008550181944840000183ca80840c4200429820340440030340d2101c407940c0540115081400f05054456141d010f001c900314100150344103400c00200064000c0f14101181c40400d1000c00c07001c2e0010400490040c0031003003420090755908154840311400e0000401c1410347e515401d0000300a480000ac40c1511038440c02c410000f01f50441c2000f5059420480c0d00f80314180c90b012890440e07600c002640d84c22503460350082c40c6060210b4660b400174081010041d12100039090b00c02c0e241020004e01c20748980043c000068490030407404240c1814a5000c6645c0f14941c103000403025100c10500b2a250fa060400300000c9442c4604c0204406005003039006c0d01c1070002003800000c0c03150044640504a210401c50342401c030ba43c0ca01c2e08220707140e5007404030558043d0038016101d400c040b03004640040d00106660a680352660710f1043c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 677517985 677697841 := by
  have h0 := BRFrame.cov_init 677517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 677517985 ≤ n) (h2 : n < 677697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
