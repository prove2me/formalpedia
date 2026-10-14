-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3797
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:42:09.219991+00:00
-- url     : https://prove2.me/submissions/7018b266-2434-4897-b3c0-b2d6e50b00e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 682733812 ≤ n < 682913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 682735062 1250 682733812 682733827
    0x70f080a03030e0c040e250b1801020109020a091e110304020d080421120806060d090203071509080f151918050d1b1203200408010207110d1214 63
    0x2026038904074400d21480d0441c084150114141038480320180e41f074404c04181c1035180148581c1140708080c1100d41560061a6600350744c0d000750400d21680d940a091018001d60300c0802000403c00c2051041d05207200703c1d0340050010f024003c0c2801076400c0300d80d543c03450300c3d19805c10110319030301c4c1d8003140c502038140800181e415482c001025880c00f10440040090040d01e0030f00d01e4041403035480000c2c030403c142480a0358441900781d441d2440e0000001070744001c0c5000003840d00d01c0c168440086040c030106084007503940b00e91020110f0313100408031003c1290090311030f500c03030f06101900d4407180130b410300040510080e0b200c4010240c0c9441800543c000b102041c1310a07030b400d00142920643e10040340c5601c120b501a6807001c1c4620040140000c1103101e68401007802201e0088404050b161541032000f454940104c003004c032105107100d42d07515546d090341e5000c1d42080750b041e580c00740303442c1c3c1c0f07608203050044000040070b074803a09501c04100c12000641e1a5000e202446903c0c01c410322107032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 682736312 1250 682735062 682735069
    0x20d0b071d03150612030c010e280b070509120a0f02090601230a090503061e0105040c0e040903020708120318030f0406050f0d020a05030405070f080a03030e0c 70
    0x240200e0655445120100303100344881200c0303881c24040ca01a80c49110041030f003070701850095030868801c89580c03003c2c810940e4490702c2c60242001c05640ba5282c064044203580c00000c1d05c00c1040c0a007402a618108544000707a131101c582c48000c2c1c00800302d00d00003134845204100801c0071000040c00c9500d4001030613030052400b5443e480c1111980140c083c4002541750900b629a48180d0034a00342c4424040d50010000940200d03040c10700081010401407212070003201c00078003520002c0e00701d42c8286007084104034001606043c40d080d0422000001c269414280189141110b4039200c11300901d46a0040c00010510b4103010340441c0241503011945400500c1140382c05846c0d1010f40b41c4030709202040004d142c0340c45800300c0a644c001c03c090302d41045034a007600e04440b91410a2034603401c000003208600c2c8508038030f400d801440064440c403655003242c013641c05035010305c2c1120a03590f110701c001c0c0400181c9020300318071903000a56110020380f203500076810740400c900c00e4400401109020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 682737562 1250 682736312 682736333
    0x6030a08040e06090c130308070203070302030d05040e070801050109031506080d0c02030c1e0618090106050c011b2001060506160201020d080f04110f191418060409020d 74
    0x801e10700318002c2c0c1800100d00c0d1854050790402c42402c0458588615050b0100c0000014440140500c801169060540d80c1c1407104034021900501503825000e81c0d81c00040c450340c07290098120640c1c94002040c0d1941c46100b441d4140c80e01a1541804c407402c580354401100c5615120321189611004003107a4840c0034001e8000860054903001685115441018280102450880d02480a1240e0034490a081101412200e4000d50704180d6503280c00c2407420042c0c0f00c91070581d8009050800014810760720a004204090780140200441c1185118a00c404004c648030200011072a0076000c400717000030302a20040d41c0e694130001442580d00e20205a481e040141003480b440701b008001001c1d542c06101221418a59180c81700342c0c0e01e40364a0510280001500142c3300100350035510030640c880202000050400600c801000b28060700441781d06461801122068800500c1400c29814060340317084210000800c000141d03a03480051000803c8075040c03c1c0c1e4001c540041c944085a1001e42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 682738812 1250 682737562 682737569
    0x60e070602060702150621281406040f0b0907081e0607140412030507061e0b03031c020c01060317070606050a050315190e0f0606150a030506030a0804 66
    0x600311919103d41d01074100042c0c646035056440341d46040040d80d5035848001c0120341074a003a280820282180d0300da2804207407003400030b1480d001820b940b1004081c000c60001e410310443d180b41d802194052207035100c603030603180204204a5400a580054840c80106600480380c5003110000c2e540d503001350346006044c000701c2c02c4844000400c50000202400030a6014400d41440c514028034140d0b400114070a620403982d40841d420000d40402d84500102c03191030350040c1d4240404020301443d03000d061006c00e00d181c242440d003070f01100141804070585410454800d035440d880c44285941201a6001346900811550780c0c3c600030000868883c2c050040515410869803584e201e841c0c54003c0f240b040e00418403a500314942000540d40000c0c100e441115079665500243c0c440c00307000c1c8200888041807100450605121102040707000500c2121035918400b1280fa585816050180d204220f42c540c101e2000c0800c82c031003049020350859504a00007804446030030038103484c0c03200d183d00304e0b41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 682740062 1250 682738812 682738817
    0x1180c050916120c020705040501060305090705010201051e2a0a080108011104060f1815020105010b030c03130c03151b0f1e030204030c09020702090a09021c060e0706 73
    0x2200348254100031020030381c80044261044140091054090900000d000681e843c4075198092400184c0c428801746005040180050125585464001e00604411903ca05103031060b9580014198414010b00380645541091041410300d1a0098101420300805c0740681280505c0c6410015030a03250320103904c04d02c02c070b10a44404035247d0080a0b03d2060784101308a81c140740c90740140c034030b001c41190101c961504120b403896881c90403e41705541d0408021008060b0700303000240d0100040f4040302800e80540c002c03c09030ba01c440c05041140801e6850040003041400044d81e00d0401d12034500810b406000c0080d265566079403114901d12184950416203a200c0d840c988003403c158840080c0d001c001d04108190550398500201649409140340e280185402c8014503114002d504582c017864102d4442c0c0c241c41c1d21400400040c0d0303c221070490003102100e0000b01c17105601c0c0300c6c0407030281d4018244a00c0d03e80b21018240070710140801a6900c80ea0b401c000212100e0801141d0010708403034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 682741312 1250 682740062 682740083
    0xe062e050304020a090603050d050315030a140d090e01090518030a050a0f080f5703010b16030318050106140103020c0c120313030804051504081507020118 68
    0x61044c00704010071980110307403241c201b0205100140011903035203500040d13031500725140e90b102e00300040c143c644140202d41500030060040144000b400a055250003800211040d120341c809003100d241c0340c01c2c4150402c01d0a44401030081c000d40b03400003500701403840c241c11042000719a05605550002c2d0005010a000080c06050f043e0021403210348001a81014501442c15001c42901d55000070006941c505420080d004180d046e00543e501460446111030070030001605241c141d202810440c1620032011111414400744a1027200d05a6010302801d5003400c4181c5001c01d14401c0c010412030074542ca803452401003042503100101894090b1001113003040c5030003c01048500640b1f0a01c5c1018010002d5007000f800005100403000010b55882c451310303001e105954150700030503516900035420403c0010038080e07580040c0064500c2101c1c800382c00144806550741034031451203030950320f8210000c2204c590308140c0e50598029414000801e9040c500f1600c1b8440c1901d1180444505909 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 682742562 1250 682741312 682741321
    0x40b0f1302130e072f0703030c0b060d05191e0b06040608030a0e1207120c080c010203180d030e0a060c1109092806050a020c10060e062e0503 62
    0xd41ca82c1c1d20090180780300003450f80c1840d0b00010020f01701002c804403541d8a0b840c203910000040c1d140319200f08880415101980d4030f91400400608440034143c5601c501c00c800705116182c905c0980c045140e125004117a0800c8810030b0110b907045601081d02c0c482020700400e000b41480c08580c2c6046889155080641d14105007044102d6845400c8990241c0c4144180708089401100c501080c050464034600030610047e0001c0c134015040e00200d03c0545940701d08800c1044581d0b5a4042d03925150544003840303584801240c0c0da00654407103841500e100c20007140d6034282083c40c0c200c2c10380a4580f035003018a00d072000ca051803066034040c6000441c42d0b5003200500c564814242a0040d04480307059860070079420304c664030785c1c04200c1340c5900c0303c040b0f6100e05c8042101000c01c00e250b9024500344080d190020500000750803003020801217021751100e44034038940600c40c0c1025102821070150300b0b41c1303d80c010700910348100c110302001c00d40d5090035105480c2102c03140700043c26555807440d41d20f203030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 682743812 1250 682742562 682742587
    0x606050603191503080d0b030a05010e071d09060103031103090a0608101a03271510092306040612061a03160e060409140f0607021b040b0f1302 63
    0x1100f072090a0794240300400d2001519140850b4170001c501e21002c12400310907000a81019200c0c10002c3c060740c40d1500b09220130101007580e0086584194600040702c0e242c07400411480d0045485803c83d030090b200610009001d04080c1c14006010700840b824082c2040c086403032502c4680151020540c42410030a060031940c400a001c0c08e40044451890142041880180c0c000640100c41410940c80c0240040e41100304400c2010901d10458400101c2e18503415071014054845810348504440082000d080f5406034500549080c22684040d0900d03920303600e440c1001400d039a070310603110800011941040454004028060f2000040700034034030900d2030b030103504040c0581c00307500212628210ac0310032a07000d8084036040f07240d0840980c0d64800080080121002c000c01002c80b002035418820400a894100c4040003800ca658070340311400180d0740c50114148004025110418a080a00f025080090002c4001d05015925480f081c0051200d55944003142030740c2d9400704904040c4e42 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 682745062 1250 682743812 682743821
    0x120405010510050a030b07020a0c032d020d020f031e100b04061a0304020a090e010b03010c050426011d0303090106090b09010905280c090f05011b060605060319 70
    0x903000e8400203102d03160a022030604542d500c0064040d80c000c0000401c054024005803208640c4642107c1318a61039140008181600c2c002e00240480c81c41d9144440c010400c030b0b03c284141c1c000780400810340640e820481c027041c3c65561540c042c0503008101c54643d01d040d0720000e04200070b00250084180c6c0b0440c5900701e4103002d0855200340e041242c1040a01c1074403460521107496482100da0b203070b4890011072411403203a8800b0b80c1203441e14608081452066210001e105411402400940c1c4801411a080e01440c0111100780baa480d01184445083d05605555900148004200c2e940140100300408161004210230b0303400000c03c2140b144004e100e034401800d4000010814030303500501045014105000f1105042c2d960000325620450040300103100c2c2404464050318801e8156080c0c014041c1401002d0209041000110f205900c03940050180d03401a55011490031180e10300204002c0140c1007659110f503602008586074543e88000d600c5232044d0604400960b0382c40d43c50030100c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 682746312 1250 682745062 682745071
    0x9070b0a090603110304081b120a09030308070c08161b06030b10170a02030c0705010f1a0f150a0507060903020c0111011416090f090902090c040614031b1204050105 72
    0x4d030010410040051429025590110710001c0302500000d00c000405141c0b001018195100650201c8c8001c4002d500200b40d4080d01c0c866510907026444240060fa00d0407016040102002e101703024045140100d6042e404040340a0103502c4000c01c820a0005160b10142c1c00541c0041e4603020300030780e681010080b80980b40b01915150304690030720700d0301403203155016128510894000010584150005c001c0c0c1f01d000d40c0100c003c01400d04100a188010284034800d4040703140100c85034440751418417080041200e0103020444801d900e060b00d4442a404000c2c90b40500400f407011801141461044152851090700109500c1950300005440300350001814480d03a030508500034844507240d058282c00c00200700702c100703840281c800e059440c41e4075074100001c500d0070800c0000340a405c64104611507802a140c0d01c07440d1715400308510711482907019440c0400d5801c02013003103400003034000f980e1040901c1c04a291440c50b81c02d420100364860314441c00d030a00484240700c1401000e1003001d400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 682747562 1250 682746312 682746341
    0xd0606031b020c01140c03130503100c050313020402070c030b061804050d11010204090e0a11010e01091406120408030f0a201c090804060806060406080f09070b0a090603 74
    0x100c0d00300341002560350340d007954094100640518080c0c0030171100c4065505003040c45c8256900c6499149040d001012280310b124401c0c8680d00d40e030660544188030b10309402c2c4040c1e8031036156560342e00c00c0c004800030700c003001c980055082007440080390340c032119440030f14402c00a064440c2016810001100302d0940400003041040e000d000002e000040c1c1e10f030352440d8604001c040c2d5420305540728024041d50380000019400d00d14051800f4101061103211a480b411603c42080e0a01d001100d8014586060602240a040f01800ba490358211403242910004040714502901c410100c500d01805903005c407150000030081c0110030b81d10303019140d070001d450102000000c0c501c01c440d05041205c0c00c003003000c07010001030503008001c0301d808600d400c0d080c800f018040c098003464802807903841403080500140040e40441c60f070349440001c03a01240c9003552103400c5516900360216a03441e01030814282c612508100141c203483c0c9502a090054098031141103161400c1805400c2d2800c01d00040390 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 682748812 1250 682747562 682747601
    0x1b010c0801031a160e0414010f030c0b042607152c01140703020a1a090d03020f07020f04020904060605190921031b080a0306090203060a0e15060d060603 67
    0x200062500103050842032508095034170804012038000d000007110300105020100022074580da5078500f51084170301c030300c1d100784185030b962443c100310307001c2c5004442d0034901d04020303040c081941315140303400f0010ba070090b512240c1da01e038458503c41c2c4030034140300c020451141c0c0d070002c445e24281071841c0244080e03440d02c2c08125030b000002d24502103034900481c0c1d06404200401890302c200089a00d01c1d600c5422805a14660601609000001c98086c0d509210304540c855202d88079000351034041115042090500c840d540c00c00080c009425441a0450350912680d0807a41d110302a1100600140c0c840b03640d9a03616030901c4c1e18141516001c04113028480c01e003008015201c80345003501e5007000ea03e00c0000030175440e0440382e40407a4070071040c01ca0b010000c9081440102c0005045042c0580c50410400b0790720741481050780401ca4450f540300340d4a400811a9048181425602c4640030507480ca54010031070006485420003451300e40341c1541d80106100040e018491241c070200c00c4240400b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 682750062 1250 682748812 682748821
    0xe01030e0d0815062106270417120103020a060e030c091b041805060d0302062e090b03010b040513060c05071203090b0f19021b010c0801031a 62
    0x580e40e51940100034108a404000100f030240c90040c0b89920000040040341c1d04c42010b040e03802c0315070424586006102030721011800d1482c00001c3c42545c0b80e01102500341c401c103414442c894046000b0b0054a03003501150030241c008644400034038440501546c502c5003541103005001080c10705801110922050030515411558000f03421f55440200710f407000c600d503440b00c121404450701d01c801c0d2100c803840401c010592a101322100d48600a550000300702654800c01008603104445002801682115010407602480019501113241140e07401506001009920103034664a9070302c4600c1032559030117405202c0c84c00b8000c4132a244021101402141045807810703580e02c1e80401d00070700840d920b0411020307590141c0d050719003080d000885110a01501d10014001d80900c03101200d03040303401c0340000d40c0303900500d40c0e6501500d090254200560f620280d10b500a6101d90006034603200d00c00080d8012010901849510310303944d6640e54460b514507c2e03c401c0b845010010f42110001110400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 682751312 1250 682750062 682750091
    0xe01080702071e030507060f140a1b140f030a020f01020f1c20031e01140103150e130312020a0c02010c15090503091203030c0306040c0512070f0e0103 66
    0x850560b0f814021090303221a1070030901c85403e0281e40020400e020301100010800c0e040859203a00c0841a211102c1014200018000340c0c41100010340104e80e4004500c000e0035091494039004522401d4003d10984003900240e240025000685c001035100150003108142e050100c40b0b01400710720000d5092412a413200403460041c0d8507040c07296101da40344d110240210350400e503404440d05c090070b0f400d56034080702d410741c0794021076111800300b81d5200c0707052511791b448000350304031640c04d400c5480011800f40114007a2407807284d0082d180c416044c0124070a10700b0030080d800348a03d80141000c040306803078041d00720390f000010381c0c01b900e03c14000c50045541002d588001c0981c2480c0a04a000c0b51740340200601a80d000354030300d404d1400050004020001000b0041c0c1081100d003411030310340319076650381c0d60f10007240ca041c0e00803001d1021882d01d0500380c21401c1c03484171030304181b41407260241c89040d90704d9045451800184000c40441d10564004200c02d10082080c0f9060106c030802954a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 682752562 1250 682751312 682751323
    0x10b1903030e0a090c030204060f08090c092a070c12030c02150c030d0e07090911040902010e060a03090204050c090d111309060f140f010324090506070e01080702 71
    0x140520010806912190790b890f048000580136a40e401c202d85102070303c5c000c000f50414000d200c0400c3c0346500c51991030340103011452103011004010800c011451052207a07842000d841d181200e45032000f440320281d4422111070f0140300c420042074031504a41040042180c849c1c0c007088031210707100c01810200b070340250202403050301960310207101000d40e14800c0403841108912144c9000c00301d280e150040168001c003200007945011a0403c90311038001d4000c983c045a001800c8429100d01408d450405800205003e03005040c040351201c5044082a0254080c54030303240026a02c2c3c0c4640c0440c50a4440c0030f0300b0020840b503490416480034081035460032001800b50499804210120301036640d0523980c6030640443c0720034003800701c035490208083d20500b100d0940d55070070f00310034040003462010824032880d0741c0311580d0030f56480e544400e4100b201c403141d113086c00e584034800550b007201c0e28000c01c03126a20840c0202060700d01000e000f490390a002101504000713030300081c0040190700290 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 682753812 1250 682752562 682752569
    0x3040603020c03040302090c12152103040e0f040c08120f0315130e0f06070207060f02010236010e09220501060b03250f0305280e010b19 60
    0x8005903540c104102083c61801164002540310b0421000c003e070044082c130107044010118021000c96446400e8a481c82841109000360041e00c1c80ea4009208001c4c80c02c4554540c1514050700e01c0c1c40c0d115044403d586800310386114a00743c208080c80700301714074a88248020b014010180400340e40350001d00005200f00300c50040340d0751011000c00d018026518112802c800300610102c1007031042c042c2400542940d000350b4140d030181d0382d8210006203010a2042c8030308029805000d045007851000d40b500d5000078480e600b15942400304140402c09842986525280880c501a042c8004a01c10100104403000d007810800c030750210400c0350b00d90240c1d0f1a0441100c0c24551501003285254038141c0790b41c0d000c080c20640c200080001c8548290004601581c03103115100300f80040b13044030940c0c1074006158200080d014000310890180300e588950703003016100c081c041103250318510080c2d00701d801d07200344202c2d07aa907003040d4640440d0902c144042c0c4d900c19507048121428071945038108001134030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 682755062 1250 682753812 682753817
    0x1050103050304260703050c0a230d1a01060e0f0414010905090a050312040201090623130306293a020310091e150e010b2d0909030406 59
    0x130358400a00b48400081c0c8030034840303030003100d10f1aa6030307040c61381e500c054000c0c2c018000d03800c20034003045000103c080c00200301381302c9c84400039294240c2c083c8041341500b00c1c01624403000b1515040c4198102c401054000d100a03a540e00192000c8010048800051110680f04d10303c2d10b15502d00603028010141c1c11110180c1d00004d55a035210314031410070012110003406404000f0300f02d124400c50b40b44442c0118003c1e654140683c0c1c8030310043da12022105001d4002449040d003606c0e20204130b20046c00341080070903012011a540360354590036503c1d0002c151120054031291089001211005a59006d030111b0351041c0740c40f940f450011041318026185100c01c0d40807041c041c0c81950300440d10340e14079800341c111503408070701040100042040c1c9104a81c0008007492210781804150420600c4a4010403044000308541d51303128010b0942c00042060380d500c1c2d00d8a00b54943d102c02200103e004000741e103030303201803680720701e6050700d070b8801000b40c030039804001404188000002a20b05440190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 682756312 1250 682755062 682755089
    0x6062e020d032702011103040b040303050d060e0f0c03150d05100510050f010e0604030c0b13050114030117070317040e010f030c180e011d0607030c08130f0b07021e01050103050304 79
    0x6c059043c1544950b410820701032400150020030144d004c002072a404a0a000030400395884030043c1080e25421b40340080720113502404284481c1060300195001508140c1e0304035040768a001103602e03040ca4440585440c0c0110b079181c000104540502036020104143d46920f440c2080d0014100a00c0e00e55140d0400c000305241d031400c0e486800465024542200070b03076840701e07036903245901c15900c8540f1005001c14144070020b8654011005190004070030a5614150380c00e107071044840d1000c2445681c054890340c00008041101d0000780b00c8800d681110342544d9504161802c5d07007071103040e40440184031900700100301003201041140305032888050781c882d00c1450020940c0180400404580309541391a001e0340c160300460301444a4400068240c51403659001010745c100c8010a0044020075003003000640c82c005040d04041c0418400c406041e1040c00e6919480c15501048503000301603030001c1d032003510f070741c45002016040d40c0d264002409658159520a40c485c09544120358100300f030f4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 682757562 1250 682756312 682756337
    0x70f03090c090e030c0f151603021e04091104051005030705070c080706171e07110a120212040303050406050d02120f040309050f0306062e020d03270201 67
    0x7103400c0050a00c00002d20a001841c6082922030340410b41540310340c891140c50307502421001c1842c42c0707541040301c824000d41d510078002040d800b17a10350384541055420091204405542411005010344810b1803503115800c0280f404119000403880440310f5030b081c0020800b079565415080385514080c034000d0b480740c8038090241e80c0d034011082c000b040e80030fa000002c00e1035034002a010040b00e4491b591004582c141544001c0c0c009003e4406090990860b030342204041d6003541c015810a80d2480c0922000e07410303641c15401c000c80040e00f11203101641d060b1805041d810880040015000e1001914061440d50060058481c522840c0244480814000000505036040d500c01100c0d016500d101307440c0950318280c3c100c00449044000c1200c45001158504001c51060783c1010040c00620068481d0030400c1051000300070b104c1c0041513071004000450103005a050500c1501d0380003800041940351300a4140c42d080d1b2288500c425075142050f144d040801654110141c0a09202140544 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 682758812 1250 682757562 682757573
    0x6160501060617161701060203130b074101090b0106050a091e0b0f09040c11101a06040e151e09071403100306181211010e0d030c030b0405070f0309 65
    0x10441605c4a5541c402e80001519a402000602c08205030300300e081c404035124040c0304000e0141890203002c5450f1501d4904241405010000004454203031400d204459100002c08903212a0300c1d44201e65101e03002c200c10003905aa4880c090082820007606040301880002c1911800344611500c4941510704548a8021b82100c04041c1143e5890603964403410034460301503605c10301c49907002d64600f00603d500d4078400c3d40c14851161040740a014955846500240540b48444540c0d1200180e03418445013640c1d100c0050005203402e8504040714a40150500e00d500c94410f034481c0030b401956030703c0c07003040c0000c440000e42c2001101c40241540352070700c040b9038881c054101110004000420300851121075010070040b24400d000038800d004050542d41e0744004082d1008100796038114843c4001e900801002142182c010000960100c120302030900d00b810100c0340740d01080e907504085640c0d50b458022215035000540d0248418149560000d00040c2e940e000c3c0400c2644c0c40300c98030f04001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 682760062 1250 682758812 682758827
    0x90e0312060a0311100e0613050306060d260f0d0903120e0a06020f160507080c0d0530130f050d120f05040305150708071b02060f090616050106061716 66
    0x20030107009162140d5200d60000700940781270040034840c1c46404000303001444c03c0502c0660b482d41c0840109042d11020480140054403e103032072078402c00c10310000c41310030303d450007920101c0d41580c2c01141d02c8120b0306001d4855051b05210b0701183d41000f81418104100086006040d603012000581c3d035000310400070064042d10350944580c0c20482c650308140300000518405135441038042d24039a10800b410480e1501e1044401041a0014003505030640201da0a181507400d103500c5501041a00100601c2d17a44d1203e10b1003020741c000d1000500c90140807810080141030150360341070f5142071a4580030440354210516804005e40d01e029401550305c03c0f4152801107610000300c2d54107a07030030781e40980c014108071000b00000d4031410020355280d10401440052000c0420404207240080d000e01203d41c0c0200031a5000300342c2080448410f8031924000c1031502c0b00c034400b0003e1080c0d14605142501e0055200104000502c44251b016000020255411c049004401d0b11030b012070100544118 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 682761312 1250 682760062 682760087
    0xb330c031e0313020139050f0307050a02040c02070302030604050d2c0d02061905070b0601090608180106033e100305040c03121706010f09031407090e0312060a031110 73
    0x72880c2c1030f0b160016452520001c6c0003603c114241e4800b003220b00029035503800b45010261065202c1380c2d68101504207940841c0096285e0300c15a0032054594000c64074081d000d6500300d40541c060560351038211340c0640c40100d80321081800c491802c0021071901c40d68840010528071a0020a05013400c42d43e0300d4049513030b5020724000d0190302201c1c4010140c800e0704801015901d8480003000581590302c00c420306010f5400549030b40300319454142c00c5285503500300300000130540d0b80740c6011003c290414282c4509407a01004960802900301c420040400090003c500120210581c860a0b81ea5030002d00504070705480c00044560321341c109800c40c142603070b002130701c52001410528049603026140b4060b10001304130218550f22810300450780e00400324075210020384082000e000050540342c41c1115100c5143c1101c10050312607541004030764000118003615440000d00b03091100001d0129581301c50201c0d0080c0b0540d1550f103400012846050a0302d1113402510030100300c003070084405034580d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 682762562 1250 682761312 682761377
    0x70201090c0b040807050f030717031c0c020f060f0114010c060608030322020904060c180b041d0906060105130305031804050105040b330c031e03130201 67
    0x2019a5100c00702c925601900500300a070064040110f86070030102e1003560080c1014000346121071800064401c80350207041c0d41040c0780030800011002c2c0601194407401c46c0e14603000012080b020481c040d1a040b4410505210303600980100300c01e80c0b071403a41d80f074115140743c0d4940ca407004014004035980c0626510080c415460300e140468041000000340d407150010903a044400d44011001000900c0e480c60300a503c1440b6000040004015030450254101c41e400c210080818120750b41c5035407800c40d007040440d1100494100318141d000c550350440c00800200c07440f12400c0c6207003031030f0702c5082c0104030310f0501a00040d9a1303480d2004032402001180c01c041a20f0701c50703a4199224a0b501c100c01170241c850703410300c0004100d524040c13081c1809098024240d99504500c8510041c0700080a51a078800c0f9192545032a44215000c0040068200b040061030f641c4410702100c28a1901d000140d06102c4000e100f0018107042104810b40096024200b24008a16042c061090a070481c3c2403040d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 682763812 1250 682762562 682762583
    0x301020d0209041d12070809040e0c090a060302281a0309010b0402030c070f0206091003020309010c02010b030316081b100e12041a120f040506070801030b0f07020109 73
    0x551040c20390203010200d07011a0107000181207800038440d2003001003400007035034101012a45101c0c100310010811548180071076400c154034140000c084810301c210594039604030150284e06440d01120740340d80112684000c00102e8116004030700f01619501d0006010180f29031102d48402503101d503840280390f510300d0b511144800808420307a07a0030030344028002c1c0d07003061b41203412880d0034002d507132003034010a003402d042c050700f074640d41d00280e09002c0c140e130008403c11030b000c07042d103038009294882043d98801503a0780c20b0815050307084840703089083c021a494108902c680d66000300455180100190385111502074030301304102036208a2041886424202c1c0c00401d040300007003403d00c800340704507904004c4d00f1010391481d5224070b0607001d1850032140401041c1300300c50081e00000321136811201c20f0b608108148121081100c1c0030303074a03103465400f000200010001d041055503401403503803a04003038070b52440c1d4070010480c030068140c007000c403034000000300c2d818401d60160b820590801c0030001e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 682765062 1250 682763812 682763827
    0xf010b092107120b07020d1d0a0902040603091a010803071419241a060c0f1e07061b080918070914030109080d050402010c150203070f0e1815030102 65
    0x202a0b41200740481e600f130f5483d000a20010700100b0f00c5d07010403040361140d4009070100790b10150030928800c41141c1c00a03900d0b0001c40e0904040c80074101a02c0e1680300001c5041c02070a01d44101d54904907600134041c000d1006020486001c0305841c152588082c8500c02c007019004031500f017546010032510348450040020040c040401452440c3c0c042080825407140c0001000700d040ea040c0b081080100512800000d031241000c2006040c0c4510782c1099071070000c035003a442800e0038a90b0f414450f0700000034203502c0000d0000d01c5500010001400d101d01d44020b44d142444141c0b50428014140d40004201241103440d0119560945990182156100e05d4a40400703420998940105200010080c40d844d09a080c140701d4000c0e6030303410480e03481c14013078445103507405070000800032130400c54502c14000010b103041070201d05581b05e80c1c90140e26403a14440040c99008102070001c1003144281c000c509503150141010b4101d1413034004202a5a113507000450294286520250150320015140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 682766312 1250 682765062 682765079
    0x61d0d020105090604080a030c12020a03020619020d18020f060a0206060402180d1b1a0417010e0706021f09081e04050d0308040507051017071803050f060f010b092107 73
    0x83c10701072b03c00d0801801d0744e01000000c036510703003080e100180035920010204ea80c08141d1100409034519642d005890406400031660a1301e0800144400d2800c03021400000c52420242280c112201510928241104910001c5d5503002c0905024000c0303500040050b8a2080d004409807240000740c852070b4030f18400d142581650708072510101c03218414000204010351204080c4551801c07036200f25051074241805040f0010554114000a43d81c2e8810704100e14001e2010b03100a0080f5005407810f00d040e0080c044480c2401c0d4110300c0300a203800f8000001980e2482501c505619078901c0f502440504a85000a8401c03a08441c0e40182400310071020150300c15041e0307104034454405e46a9080d038440c20701021540529042010a800014a103c045007a020042c0c2c0480c091400d008584e504da50615800f000c250810f41c0e094210b500d07111a149400c01c110317504078a06000c40b02d400d6142451044081c0203c240c828803070303500503264030180b00912801c0340011018809a0388800d036180c406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 682767562 1250 682766312 682766327
    0x23150103050109020306060405061b150406050c13090906090b0a23010605091903080d02031501090303090603020c030909011410051306030513150501061d0d020105090604080a03 78
    0x1500080c01c20300080340361101030094900a40d400b07403415041c1400d210422515400020070311110328000c4d80d01e104d10100800241c00c00c0312104124407a50f04040c00c3c0300f0305030341008107620b00d400010000e05031600744502d5528100d5281d81400945812185800d4001e4507407000702604006410040c0014103c5984c8070307481941086000c041e00752195485007c59070402d100e200003003002400035414600b0240e1900e0b1406001c00c808070285c0e601c2c0d40d00c40321560007590811220a03404020441140c1a141250740c1e1480d00342050021a481c2da07900030441a6240920000c16401150400751100d00700240c80c50031000030000e501c150317115800d2840700500120007520404007404038180c114022411074140c03c54405040b000541030a40a40141001a101c003040300c40480144010070740b04202ca030402014004085119490b1110050041d183d5500740c00b010030312908000c120f03a82e001c101c0c0030f0303ca0f03080c01c1942d140c01403030000440714015a803265005010b040f40385820150320210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 682768812 1250 682767562 682767601
    0x260702061803070b07110f0f1506030a06020c03030601121a011808010509010e070f0605030a090807061a0a35030c0f030c06010609121709061305030f0a03090923 71
    0x219901410507c0a0390399940704185406c005400c011030043d8007401c8038610a9200501404440c000f40c46031742c900c800c1741e1094200c24140d13000402400790380e60b88400766501c030100c402d6042c0310310354040000d16100e554211043d41440b9031000340b01c4140d8003480c1401d00500c0c1c200000c110724035015402c0740c040c124000c66980c0a00030034501055400040601405883d0300d0743c0c0b56810759a030910840d006000b42175054134811001c0c02104000386060050707a00c2103032402c04280e43d0384030250510201d000036802604007040c118119040e109403000d5407124101c8003403500b018441c0070003403440c15881035260151031802440380d49400e024000009104000c01b40d022209107a03611102151709107901d0107003083c0e203442c80d00769802291141e5588808500c140c24100c0c600b5002000066683c0d002801c2111200300d500703801c100501c0d040c001501c62003c1c80010302032603a41d507a0000d00002e058050340b600c09554144c00300603000840b400a100102e0982c0e03090090620b03040e0709079100013140303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 682770062 1250 682768812 682768847
    0xc052404021f140d140106030912030b0d020d0c051503160e13020d11031008061b0a08100b0706140a09050c0f120607260702061803070b07 61
    0x102410441e081c40b800300d07103007110319620b19404650300c4807003031616440b4034040c6182d40d40725010202c0c00c4889001e290700804aa8a00140e185014900261007203266107131941894070b054030040c20343e1111811040800c0d41221144040300481c80c040c601c84591350012074201c01210341503e2001130386002180240307404018400409010841103908280c401c64054000c00d190fa80e64035001c40580240070804140b02c070202d9400140c035940910b9400c00c84030003a03808418403003000508002d018464000d02031160850804912585c0c00c0c110740300325040b400401900400040c024030798401d48802404447c410255550302c3d505083e0090315100f1924030f031601c240000700d044011548121038803254420003406074020400e04020f800003c0c6400c043c0c00104c1c08142125681081c029203100b0302640d21440d641000040001500040594400b2403140114040c040c1194000451a9005410480001c250903d01e40c060341980100c2c2c20040c82000030714107010401e034001203e01414030301d40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 682771312 1250 682770062 682770079
    0x61614060a0e060a090804060f1106040c06030e010203151005040b0c010c110c0306010b0901020c041e140c0f0313080c0607020f0d0504050906120609030904050c0a0f0c05240402 78
    0x2501c0c1324216582088010207520b810041080f0f400c2c029182c0701074034141030410b854101c04683d902d0381466001c542c00c5503e00c001c00300600100760144035201d48521100c008505509d0003515140c0c5102e000c940d030f144502c0c40f4008650825200300b003168007401660310300503128120880d4480c0a0034400b00124040342054407100303048031340000c401c0c2c54450001e0092000b40d190003240300f20b030b91009070614114010031140b1491034445000d0b234014000d072150f002e00b202003504121021034000280100d0420902f2090004503070b41c0f142a51000f558018403180c0c3d030b8455217094400341c1d031300c0744c002005058007040100d2031240218149100d0402074007a0355001c1600e01e003040d00c80300d2604e050382c0400c2041c44117200a007424064243c1c4040040c10200d0282035203041a0701d0108115000e07029903000003420102803c2a0082c1600942c91080e0241000c00a170005410008542e401c14108090740c40600f050003003c1080700f028100c503080040b038074460200041100401118207900840a8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 682772562 1250 682771312 682771321
    0x6080114060a050d0f0b06390d030b01030f1e0501062c27100605090108150a030209190e07240c0c0b0702030c0f061614060a0e06 57
    0x76804803942d40300c295079114070b07000304200341030000d20040d581076180da561054070313503e9915610024800b12044502205503040680281321070916503010b2452500441d4881d11111100058440300880035801c0c04907040c919400120f00a10440c1d081e40754981c00c00214420146c25800f0149100c00305407018840d5a0321860240d0789010188604131820080d5110180580344403550660011402094000d51412040f80c0124900e0705514000c080740d800c0081c414a00c4028106000030030590501c5814220510000390440e103000b0000150300c0055540d100280d07031095000405107500400205588c14001103400100030001071040341d00707140003020071018000048000455005818284001d40da41c00040032102204071703641d0034094021031083c00250709011260103071169603003d80d21403c4500415150002000c45c4c00d005000301000303881c44e070f16a02c0c115031398a441c45002c8a00108189062003034810f04010240c60307400b07070105001207080036400c40486011000200c600030b841c0e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 682773812 1250 682772562 682772569
    0x70b2e06031808030a0209210f24040b0910090303020a0e011103040308070f06060801050f06041a01110c030a230615010c02041d100c02070e060d02041506080114 71
    0xc2c12200a840d0aa0500000d141070840c0e4005241e4668090985c0c99a200c2111600d003100700504075403120340d0003244080c00902410003110315210038110f500c0702d011281c020395a1207680702910160908106000044a80c10b0401c0309022881050008100c01601c42c10010000d410070368502000909004004e620340d0300c40c13141c2410400340031000d945803502c5c41d07840070b999078890603044811040c441e0350070b40425200d100c0c0c5001441d0010001c81d061a04540c0800105c0008000741e00c2680303010a0980020041170589007088401e003480c05100043e0551701d86449254092280d05120b02840e810801101b62440300080039001030269030076540c1c4e007040343c6650046030384034800041418040c0c078540c444c1d64684d1260740050000a031107030075664240c0400070a890f5407846540000c51080070b01d0f0181c4140c10b2200a41e2010b0302190382044070a101a40016004a1081c46450b1001040d540c50b9800340c8072041d407100140341d08941c0c0c0c4602403e082d50910621481440104100500e4103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 682775062 1250 682773812 682773851
    0x90f0602030a1409010c1a151206160e28090b06070b070e04090b04120206241906020f0708070b0a080a0f020c0a14010908070b2e0603 59
    0x46050301c0f88034110124000381002a00300c0703040c1d42d0400104c400f82c007000c2510396409030491003030f07601c00c40300070f00c0c0c201810591002c0e0084100d008007200c070b101624205005c14402e8000d80507003000e40c996800000d08840c1d841c4403d00b020351000200e60412120210500d18122041020011140b2680d84aa100c400c488014841c1078004004100c0a40090702c19070301180d200d441c608140000100160100303007281d070440400c48244003074100f0300003482604064a0303045003652000300510b00e04940840031420121082d0800150820051900d035596446030b000300f2050038603940300d600d549800084d6107940500c2012801e01613510301284208001c540300c0155080c03080a507140148503102140d07110700c000c1c44000003943d41d5048a4081d502e500062500a2041c0010242c01e9600d04040182d08941580c005c916803610a40c0c900181d03440d4244c45500f50000583d60300745c0e8035a050f0036908422b080b54039003099405108103400d40000200d660584500d9a010050110f100141c501e041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 682776312 1250 682775062 682775077
    0x3090b06060c070b0d23010617010f120501020f1813091a0c09090415060902041505070f0b01080601170606240405061309050601051606020307030908030403090f060203 74
    0x60700000002c4c0300c001c594000400200000b07610001e40160110500500700c03a15643e5454882c40f2840100840c681c003484180862036079811040c180d503d02030344800021681d101d404800c034440190f48061108c2941030f5280181001c1c4495510306814030600507a0010b03140c502d01c00c4010f902e4180c13544403148101080749511000103c41d460811764509004180188802011401005050150348447c0501405607100c4d2102103038680001d9116010346250781c01000203244140010410390034241c084000030750503400c10f01c2d0703506502e091003034203a04100c1001c0d16200c003940c00080c5c40180000c00038102c0321003292086419004858941d1103030001d862803580644020043e1080702410592020620120440740745895662400301f0415001046c180e821008440f40030443c51140f8010194403c5091130b045140c1803c3d19503180c00841101c80150109034084001603486000782d11080340070f030f04400860744030703d054170307000f04001c141d0f01510000d40306484002070050300000a032484c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 682777562 1250 682776312 682776337
    0xe0a0803040209060f0415080606010c0f0b060a050a03080306031c0e01210608011d0105010b04060c0f14240118051b0c1614060f0310050303030703090b0606 69
    0x11501d46030204601c5080281032a5406061480f1a00d055130311442094030007184220b2546e1254030303007d8281c3c28080010400ca0600100c20071480001c0c42c0f0081584c01258017039010074030744c2c50740004900384500580049801007200b030300c00b1090003c0040514420041182120303112001e078a0b900c1c0800c40301d060718201069084814540a43c01000c45584520a00252544980d440c101e0003060341d04c2c039800a2016550340c46104c00a4680143c41000b0404050003030005500d41048140345114501c90722080004090300c03907003004034540355408030075044085c942c0d211849880c00350702c91444014203640005400410101070426000c00e60403160703441d00c0751384954602d0706028040d010007007800c1c103601c40c900700122001050002424200301c42030000e144640a11100081d0102e017034008810b8122100e90812003665600b085941210744010000e03107c0d150300148080341003658016550600001c4100700c82d85a0684c081e00e0356500803044458188c60b80c00c1440b000d807140103402c0f0302 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 682778812 1250 682777562 682777567
    0xf2a0510051b160f020301050a090c05030102031612060e1509370204050406060509090106110a020d05160303050d0c090521120309013c0c030204180209040e0a08 71
    0x82c0d40c03e440c02d9001c0c1c0034066542996103202075400642110000c507010005070380d50f118a0405d05c82c1041c501009070006800031482c500304600400350900d0406004010007042c19042400203929030884801400c41c01c2c00824241000e034602c42c40c0d01e0706038000ca4000c803008030028556200040c054615690071004c04008444103042d0310327615540000c16082c0c4a9001c02000603240c5440c850080140703c00d40d0b40d5602c91440341704010401c0c40c10380c030400030400c080119151140000c240c4402c0940d04651560602c00c06151a6040a8003081c0c070700e141d084843c000000740364115004050813900c81c80c00b040f5000c0c48210685515940c0d00030540c02030311001a07036a04840c4495802142c034007007000c031007a40c504071801e0111544100c821000790f94403540c0003516a0701d007180142e5581c468a04030001c010401400d5a1206044001e90b08102c0d1103403030002c010781c000d90441c3c000c1c2c002d904404080c00e81600d1150007a520490740e06000b107140c500705940c08038011079903000441e4400342c100d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 682780062 1250 682778812 682778827
    0x1d0106140909010c14130503031209010c0206010807050910030615150f0212031803031905151f030e0f0c0a150c12090506030702010504140705010f2a0510051b 70
    0x1015400100c644003080030006d0010800f03540030000303480402c480d244620020701d03050204509440454410348255800b500060064000201d46c1c20f09440d02520360f108940da454494948100c0c4690015026602d02040d8021a182c3d0390581410b035010183c0c0380c12049401801114507607804516400140c104030070980c68900040b0086400c000d8116000c401060201101d9055500589060080b010615496402051513004199101c0070782d0080c02d4404608801040290b0154503c5006a1354040d280141c0c0c24000ea1100c42004484012501070002c11600d0b80c1d595000320760101e2041d600c241c000240e44d22200a03100000f02c007951051540c02c2541d0300c4600c403003a140c400e074060040f103e601007566140d99003e544140c0d8103500110342400c0609011a1102c0c8086003111340d0b4111034424081030340c00080c4001603081a18101e014cc0d00000c0c0c1c144000c094006000b10040300042503c1d041c80400180500b80702c45140c420082038840341c0e4842d4014010003a51001c048041c4001c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 682781312 1250 682780062 682780097
    0x6060a1a16021f0206100504050403050901030507090305300406020c060706020904020703270e1801140406050403090609081e0a0f082511041d0106140909010c 70
    0x2841c5641c40545400452248002e6200d0079512007403461006070b10240401400b00381c4074400f0300041109035000c2100c0e00f06500c0042943c0328161401e41455140d2001c6640b292050003c8c030011034000e41a20380901800703450604a0558001040306180c1081c1d0001d022200c0904a03012240d554004081d40001a0180802034000c1c01050b20741c10350a00640e0740c80e4072540014503226110355504104001312140e40c50113010048031b416101c50300e84406002c0e0390794650145400011503007282c02101d0043c94581d02400c22140d00901104412050008110742070f084240141e01c40c1d20b1b1102c1440c1c07038a1080320365003624800c2c00401d17403004a0a100c01d86035821602d0b003240c1c54209031140c1c00d2107502c920498608400e4200c1e000100050442042c4030740780700c03074046c00c5030200d092054103220b0303107440341d841007070850b260f1185607a100ca14280d240202e40399180190524000c1c0400e03551115809008203401c0e0055000d00304000004050090611419103101d2042d02c0305040c0580c40b1040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 682782562 1250 682781312 682781347
    0x150e0103030e0604090e0106030c0b0705060403030f06080f0a020901212010170702030f0306060310030203190c17210f0f071109040b0408030601030f0c0206060a1a 72
    0x5400400030840818480d01c9400ba12032246c01d610000305050745146800100303400154026403101106012600004401280103a0050340601e0301041403015a04a0b070010505a07001c030314503200b001e040707030400e28020584110341c40c005c1f41c03140c0c626a0707600740a0981c01c2d030440ca1241e203503034803111302c00008000c000280c13114030801c1011100c21041801146040e034070001c1a8000c600c241d44000c405501c0c03815400e5101d50b440c4040c5007007080d90000000c1034040030740042c0c480c0d000800007904411981a0301d600541d0024111041c102d4422415105200c800f40240e400049400002c2500190b209801444040d0354009101d08407158503502d500510104a440f00c482c8108122168108410f028116903141000c2131a80c800280c545003103c0ea030100c1140780036642c40301c00c01011528040f4100d40c09500004803d50340d079a600d00407402000b480bc0c80700041842c000299400076030005559118040070386071212800d0700c540c140c41460340d414002d2045184204810661004034444 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 682783812 1250 682782562 682782587
    0xa0315020d09060903050309010c020c030a030e030a0203030a20070e0c0d0e060c0d0f0c020c01050d270b0714091e0d050606100302040302030622020919150e010303 72
    0x90006002c01c1c1560340d24252109840c05900040303021080c4402101c0a00c1220026038160000f4054940b100e0080307500e8081c10340340941484002e1074624100c1e101400003602d695401810780c0d40d01c00308000d01a0100f988145001148070904440c0e841c851400030700b40b000d48109440b031340025901c0c0c511030400381c1c2c0540a40c80da40c5480380799401040404100c80c0380150b010000c90358031030040f517200d48c00316540503124140c0700742040950031500c1c2c1c010818080100c402c1c81c041d13543e0070141001102400e0f801c0038070f161009012040303810301c540c0050302da00d0482c82039502c0020360720386a038102e1fa1507105124136000c4c480100401c5000785010401d800d9200400c4c0c0d10b81020704512000105070068422090b5096040102004000e141000841201c6422410110700b49802e54000c2a40c88800030050b940070081510009648148900c0c4580c1d41c660040c200d01c141c1c40c2c100e20b174050344006c05044900150900320703200021540c0703c0c980c0090701d001000e40c0381303d6840d40d10100c4003c7e0b045107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 682785062 1250 682783812 682783837
    0x20321130624180b0f0a060302030c160501061409042d0203010f0e0c060c07140a0302040c2f031206041b18050d0837031a0a031502 58
    0x321154504048a10400020000f9548110080e6150000402621100c101c2c1501c142d219800c80c0c0c40d25aa0424008251140340c1b03001a100c0d5a0f01c05418a14814080d42c2c840c00d400006503074040120542019096401e55031220040111803418032900c89001e0b1001042e00480c01316000840c1d2080194203407100a070401906003175100c1d00803c1c219592800241030740f9894031030710401004200811140703c4e0b029500c407440c0102c1c0321b40b00f64441c00d2030b005070740d508044182c0c0000e455440880c01c001440d0024401c000e0800d1124000d024030344905000005e4040203803d9003900c1c031104407102d000c2207107800518540a0b0405154691480080581c0c3d0302c155100c016001584040f0164481800251030700811840c0741f021a0303c2503656580514814452406024006407600041c1c400240f0391204900b6400440d05100b01e00c04502401c4422405403070030f04d06901903050300408a03255414a171200900d07681020300441416500003e001c510340003070340194142d520390040072207080c1361 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 682786312 1250 682785062 682785101
    0x140a05150403120b031f020f040b04140a0501020d0c0f02090f07080907050a120813080f10180308070c05030c1b0d020d020112060e040c0303110703050c01140f0a0203211306 76
    0x7808d80700103a04507820003520150b0202c0e003845070100d8820390000e8107004586040c441803400300001e42d40d00280d00e40900300444015501c0c10054584000d0340e28942c028940c540c40d1910346c1c2400c0142c8011110f4100207031144011901c100c0f40030428400340d030406400c144055051075410103022128050850b01040d0821184108002c4090944058050764000d81500740181019500e480b140781c043c0003d40b03150000000301120102c00c0d203010244e042c14a07101ca551501819140410b4540b009090b5010020b04104058800300b8002c41c0d020110440e0241c0c907000344241319494450b114000e40090b50010f0f803101545c001c5440d0b01c551004c070000170407015158485800d81c848107030b8046030742101540307080c8101a00011404010344142e801171410030b107507440360b0340e4408080c1101030500c0083e00124845a00305411281014808032100381c0c1d810004e44000d649522180c040c01800c812100e222144a6106c0181409191100d900d2440d541c00b0b44c41e110020b058900c180e0078600c0e0034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 682787562 1250 682786312 682786327
    0xc020f060702010e120313140c04140703060605070c26010204180609020304051f0f14011a0708120a020d0c0e120102070f140a05150403120b031f02 65
    0xc0140500c5058541d0004c11001c4030305141d240b030039240358465221120306004000d000071994220000c4036410580c261202505c1000c01420403003884003454100381482403c690344000b9131010390003902a55020844169150021225401003c070001c1c820044070904005040d40301d40544080e400140c07041c220502032408141c00c84e8840c0d0300c00004411058040c8940504c10701c1a40f00414807007d0075861071030b080d9255515100300d15401c07251009041c2c01d649101155500404044a0800c0104490304909180c017541c0c14091045861413604a06840d0358201e00509513204980c0c4000a03d080901d000d9801038000b20043c501c0255960034841e001ca41042c50081240802c0d641e04d661300da18180605001d0b40e01c0300807101c40800d80c010480c010000700703000c4641501c0d0741c000051134902d001810500e405c0c403103042e1004d01188075500c2c01c0f0303284081c04040385025511a0700c0d05009100c18a09400a96403070012040c0d01d40c01c080c0014000e00c4017450103c450441265006207840c18 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 682788812 1250 682787562 682787593
    0xc0603040606080c0609010e090703200319020f04060e010c06020f09041d0a030507020612240103230619180f0b030d1b05030a0f2304090c02 62
    0x800c5400351009a1200010416018280820f146602c0252041480d105801380040c200c2681586014042c0e0101c07000601030622990284800d003ea500e4103000c1e01251011016140d0001d079407101d20401da042840424a500e88202c3d400c5400340840142801d10305002503410340c881991450512404030b80782c900203041480200510002462650349405218091008840c50000c6443c44410110700106110100013000048141c1c14607150303076214502e1002c0f0b41c160040454101150f2404001d0246421145010940710300c09440b4010100703141c00011000e8822910301c503032060341d00c00c401000f0f82850500240e80301c00041c0100000141c44400c184580701c0517405500040b8010100440da800300d40100c000390000c011080c041c83d145071000a450b2424090b080c014841024414182042c0d19400c401c0d10301d40020649448581c00030019207501c071001e400c84000344090303114291141014000340c00c40044240031a0400b82055405802400032110b1002540305500c0001c2d0000f1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 682790062 1250 682788812 682788817
    0xc1e0e030a0605041407081e0109020a0611060f040209060f0d12030b01020c030a080d2004092c0a1407080a0507030b0c0a12020f04080d03050910020c0c09090c06 71
    0x10b1080100103090b1400b42050201101550300d02d260503040b268080028500001c0c0701c44070301c02c0880c2c0788000d8030140740806004100300000250070607001c6900080c0b450308170808080b480d001d101610000d94070784642e130a50000032200254001844008201030782801d9645d01480c4001401d0640310f00c2c02c5480c0c2c00f6040041c246071900098a0b1200d04c0c4c0d003540d040c8003040b141c041c00c2d001030014000303543c3c0d2500b1034051440000f0410f40d66020425400102d032504200070309040c0e125959941d00d41aa4038058414031138840554140349801c4604d074900005030900c070011003406070800a40694604403002d4104400b024140300710030700400c840c00e0130310564951910a0b4010400180b0b11b15041130001801000c4c01000c5100344000240560840c44140098000c1c100c01a551013032260400c17264004c94000600d148248209840c20981581c0101c1c040c960200454070320600c201c655074140d200f42186500b0b0f030381040c000f0541d9400e1030390340c180d0008954801d43d0301c0080c086000c158145c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 682791312 1250 682790062 682790083
    0x904060e0a05041115070609170a030e010501141f050408120301180902010f050a090e01080f010e0304061403100509040506160f09050607050c30010c1e0e03 69
    0x22a80c50341400300300b140040a10300100c4059440200c0c4640c048001c2017540690000a00041e845809100401a2101e10400d00c40900f0070002d45541a0560040c020103030039240307140542c030b00070020441404168442014860040281940c1108030001540c0c003044030105500388441484041890002403125104401c641080c4940b00e40c50f0100e0084070343c5440984101d603510b00702005000d40d9100c0d40100082004c0c0c2020f9960b50382c0b0b03181c00c49503080307141d2040b240100480f0000c0b4072a00c0c0407070345030000250a80280010040c0b2100d882d245d100e54899080800d142c0c03039100d444265100e000c0c552110111040205903a13840020401c09041100c045602e0b40002d03042111911242ea0055560300d034070b181c5207208108010010300304000900440388107120200e441d1003084001c01031203202007405000711484160041d848000c810281c0302803010381d0300a03004140844014805c0c2241c0d0003259071010103500042140601c01030302000e40104109032080000d5940d181044041d207003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 682792562 1250 682791312 682791331
    0x309080412061d03043f1b0e13080c030a0c0201140a090b07060e0715090e090712020607050129010c20030a0f060203010f05031906020904060e 63
    0x2105000d01e442002c035002d070f003800004090100403240b0b05120002c1aa001d03500c020a50442c807202c0444100e1507800d240d103030804e640440c5400c44c0b41d81c0c00c20700c40c0c03000900d1283c0c003049024426500744541c01401d500840484041c5040040c442c44018a141c503801802030742068509001c24022504503401022200085907444504400319680300c0820004041c1c811175081c185119034a00030103802e0796100303030407201c0d40c0032402d04244201c0ba44000c0c040e0408000310780c903080ea2901d4230744c10b6a441904c900040b54000000040048811501d28413a90880f00507011890034010b81d0b082160b01501c081e82c110310144140f0000400074410781512000d2445080c0c1c013000c4a00020750a910038170000b0f03040000050003140003500400c00c4a8544100c5c030300c1055000c8008010920305008902e01624602038240d51405002c4554001c2d8140c5645040b142500741e15032081c5951011140d0034401900740300303500070000c00d12a40c094421321000600c04260b07035560f111104056081640c0c100036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 682793812 1250 682792562 682792589
    0x21003050c1e092103120c090301050a0b100e1c050a150f0c0309050a0b090c1c020f030a08041518031103011a0a0e040611030f0115020606130c03090804 67
    0x14a2400000501e12440c20040203124131420001c0540c880c002c0d4141c43c1455201d010103d18008400c00544400720400340c020001d0740350941109000d0526044c07614059504c920700066003911820b4641c0030f401d0003402000c0031010a54008410045400d401e43c0d07107000709040c40700046e46402421103c0c0c0d1004e40d021800e046214a85c01c11901408008014140303800d64220004070046403a201140d00040e000d40c3c180d46022100d8104a0300390603060384410044075841d041c01d2054400d00c205070090300c1104ca030801c082c0a041c0c0d02d059004011b0722040050008000c0b00d040b21a126032400d03504e151043e080c0d402c1c803412070f034100380d150800c9079401c403221144546402c091180480c7c0038081e1071303010400e180340030100c0ca40411f140210026070346e0600020b000c1c4400c54200c072501c07204040540390f580c82c0c4804203098180081c01281c00102e1100800c10300e4503c005440d5008210041c504400329040d4940c40d001408640700001c203041d00d5a01010200703100401900007007150316401032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 682795062 1250 682793812 682793827
    0x1202061306090602060c2107020f030c07030b18070b07050709050408030a0f060609140a030b010b031803091c0204091212060803040308070b060616050a02010306050d021003050c1e 79
    0x20700b045e90040000000c010103006214425040403a014065402c0d0119003d00340c6070858101e08010321122100740c0c038407000036609000000065400200c03809015805200c0e220401c02804445040481c0c116a510480c402e000c0140313568010000c0601c2002101c1840e6980c20002c0141c0340210307001d4420141c04410421a0581405421003190342c8100801c812812b18602829010450003030002c801921042900c00343c1b00c0d40c41910280d50000351815a540c1d403211645003640c07048680e5142c642442c800f1640d401c00000c01e407600c08200819814854241c080241c10002540c0c3c000d0b40e020780c5036221900428001084890840402d50b034000341900b1424aa80540d4001d0340807030a941c0c810413042010070340c1c0c01300ba02e021a61041c00d03030004e61240d0700020b00500030211040c1e08408034107019010400006005c8500d28401e032018031400341d6600400c00e51000052020b90004420340c400041070344640e100716880741900c4012820034000000c140e072240040a071070010700300300083d0381c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 682796312 1250 682795062 682795067
    0x3080a0c1209330806010302280905010503041509060b0d2019090c030b090a0c02060f0601120905121c0621030311090d080304021008060a12020613060906 68
    0x440d0007072000f101c40d0180040790107000100c04110356814200b001110103d0745a070701ca90121a02088101100340d5140c803221107441d5503a442c3c140d65800b08000c0c9100088550261056030321030f0b030300040080030340c0405801c4900688020041203521030f64030386818040b030b40c42c03940c501030241c0200f00c2d401840d101003401040c0d49403019000c4d881420040048600c81c8030141000c7d0588143d441c0c0452100e001000a8001e040c441c030916a20241d0340080141144450740100582403640e4216070250b2201c0040320900b0310261215030000f4050401c203a07100b50300380c00000c1e02c0d6104108036031303028140314458440340e00620441c1c0e10b098224012502c1b4003003580940c07000f130850448110f01248101c02a016803c4032180018241a1544054038140848009580346d902001c1e003181c1d030304030040c40c00305150761085508034132a21004020224152040d0a024860080074185080c2c031420520782903040e040050049a111004101400c0400c1c45144120300900305515092240da04101c0c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 682797562 1250 682796312 682796339
    0x60302060a08191a1e09010e0709151b05100609020d1406010f0f11070603050a1a03030405010c242007020906040c11011b020d09080703080a0c1209 65
    0xb60030281418450307424101c100e800004d0f8014121862100c0041c0010f12085400141501076840658040001048a210110300344900610380e00c0c881110f03225004118078000c1c074510784000421400c3c0c2e80108100c026841c140c01d41c040c10071030f880c407407405440a00f5901540c000c040915004103408a000c07545001e41d45524070f840d148204140703802c0300020f12108091840c0010400d40c1020800c1d81400b400348524003003991802c0c1e800706500c508000e4060070040c0c822030070381440c11590785000304044407604203061000740618a01407405c801110b81100140b001c4d41c1201c0540a15402580f583c5d0708100e50b06490140400c222003040c3c90043c0016091001c40c8100c0c00c00c206040059940c500c406622480441c1c002a4a13845041e0850b58446400380708060ba40c42e01c03031001c0c2520501100110350100a5003241e040000d04c00c000c40300403015100c1c0281d1580498800d00c0000e1450020f04201106440c0203610004280c84520804854001d20340200e440e6400505c5400a103008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 682798812 1250 682797562 682797601
    0xb0a020f0a050d050f04180c09080d170901060e090714010f1b0c0306050a1406150322210311030c0a080a0b120f0c010828060302060a08 60
    0x540803100050302c501d0707181c0c0c002180520810000140c40d4405080034020788020300b05480f140602144c0783c4500c000113003220035020012807103002c0005112040051005900d00c1c0942c0c172910309202c1206034201030b84c3c02030032030203855407541c4c0041a010340200c5864030411001000b0561546407401d05441d82ea01030000904105e242c03003180942c0b580101752080d46031a8103400f4041e00c061070512a45136005a000242518206001d10540307144981008a8011070307946900099110341c010409402c401812004c06d42000f030000400d01c1500d2220581501c4600e00f20617190006980d9007078024040c1403074140041100d01102c002e242d814455010200d03c07000c121481d600f000c40d1641c216014051110f010403001200155182d00380d41c2020880c01009072182c4182d2810a020b681c6070032940c28943c04900c143c0c00e0401c010f6104580c00d5008080c90341100030304007180040044450f1100c40015640d5844410000040e140c03080105001a080d903568001420400361a10101c01c04a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 682800062 1250 682798812 682798843
    0x1e0e0702060f0118020403020a090b040b030321041b06090806060a03020d0b0603071a0705190b1b0f07121b020f010513090603050604020111070e01060807050c06010b0a02 75
    0x2085490350450b90300b9030558192030105100d5680504500e0040d10444d040203420001841c4001080100e98011488080f001c40302030120360503c0c0149540c0e80610094202c4e04c15215082d06900e401521700e20750044e0040b10280b202c80220440c1204c4003040d680880e00080005104000500f414012244c101400321072101d4218990303000a80003201601003c0c04134000100413680d956410003070000103019900c60206407203d03020509115402207002900c05015000240b4204080c56a90500c1c00b44e1050303e209146d180c90513401c404168110307810403003131810000a8956802c1001420205101e5540c803000c00c04804802000006050902143c1d40c0c0d1111002c00140d0342d032840030788a841c0a2803caa03c0d9150310301c1c803050800e90340d48a0702240345000d5000c000c0c00004503c03944141d000381c9034207048411140d60240d07910503500c2034240c0d1005181c010b100e150311400660b40c00c20107038a012800d10ba41c17603001718200242079000c3e040308000040d09200715038060001451002100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 682801312 1250 682800062 682800073
    0x50c070507171f0f110c0c030c0a0e070912051c0f020d030506040605060408150106170114010e030312101a0405091305030d0605090604050105030c090903041e0e0702 73
    0x5818490340c801843c11564031141c80e10001014440c0c0c030350301c42c40344c00c1154003040c44001e0904000c401ca40c0e00c024080c0b4030a0082d0607072648181800100807030b4001000d080c0984903031515084050b000d03805842e10301040b00200c2d000494144074443c1c801c2c06030054010780000103a01c09510f41030240010b00e24144010352107440e1600f03030042031004807a00d46040110b103640c0c0d1140010001c001c10307080240c0c802e8000c5000b10b214103002490100000c0c03001da000d0340c2ca036260742042d680a43c2ca420701c0c064080750007005105a100541240d034100c1d0043c1800210381030170000081c2160090840b40390b00078803407000c000c0140800c0c403004d401418412070141c09883d0640c3e007503075548602d008480c026030607840071078042c5103180c20302d2000503001801d81746c0f2003c801d110701000c1c14842c07203200c2c803c15051010903041d242c5841a2412540020700811060f81030074180310309103034000c0c040c1141c0d00041c000000d005c8590004040702480c5080020715080c1001c40000d4807410150a03d02150320a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 682802562 1250 682801312 682801349
    0x3090d0c0f0f0c1203050705060c04080d03020904060b030c07020f040b130b030f0706020303070f140403020409110306150316031e0c030818130c200709050c070507 72
    0xc9010080c0341078001240e250318000c0c03414a80c0061507a50f0010605010226400e1306145e402800b91219904c110251180d503100c40c864100ea600a500445071940c11181d140c0c0034150103a07004015200005d0804a00b0750b54459500e21980c004503025019400001510011890401009079400300c08880401240819801062103120618074016800759200c2d50380d41c5c1d6950400880c007081103404200c89603140c580d10004d440c0c3d0004c0e0307440c07004103601290f441400c40c000c8207110703031010b031100076903040510f560200009840346100039241000d00d04c0b0390002e2501c041c4401481040154917040b0f200380c5a07414113140284022030980124281c40051000880c5d18803c0d02c40700c506503032001c000d0000c0341040346612040d039000405022001580030031105003501404a0564125108800b510840c0d451400790f40d80c00302c0b0b44001030340c0c02c8192104c100d07000000000403e000e0003101c0c50749468407611411980700f600d14601140740030440030100a001c02c00703000600882c1145659500d034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 682803812 1250 682802562 682802573
    0x40c050a030b03061b0c030f030c090102070602060f04170c07030303230603210f0a090f0501030e100c030b0a090209041118010507110306100602060907321503090d0c 73
    0x720090680704040010140608281001038912303413005422581c2e40c85c00c0c9048924000e51000303c545015001304480050500e0001c607030300d8420345694134000d04c280d4490340c03013500c88800d4100868102c2c105001044040004210030401395100c1d403400207518260641440f02240b004d507d5000c3d40400c2c03010080591408580e820004c024110f000840780da024020540e1070050250780c01e0012804541c5c91411030340981c0d000100e81504030034188840d01d840044040c1c889124010800360f006650110040959a000405842448c038001540f450003034002102c00c08964040a02d1035004034200889180611501700d080d560120028a03001e0f02000200076022000310860501401191100520054a4a01e907440000a00b550968507240c540d900403818075026402c018406d00000a090000000300042550700300a901c401800300159010100c00035013441035074000a011a409060703e4091600450714400340c2e4242d02c2e03150042543c1e1a00c11081070305000c004002565001150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 682805062 1250 682803812 682803841
    0x40c18110405060a020c180a0b01052508090a06021006140a060f090f032003030a0225080114040317061507050f0706020a05010b030c091f05040c050a030b0306 70
    0x42050341e07426250020b00c8002c5e0304021030b018007203400c280984443c6505641021015100303042c002810452020700b5001110a40503440d1200b02c0c600e403264030355042c00c4640002200761446104910702d001d0b50341010903140e014540c010409039010000e120905107980c01258041c0500450201050303110701d00180380c6a1079840b45109000b09041c1d140c0e40ca9104210003400f8000b9000780c3c10703684e03940385004c2c1d092909103000590203d8020441c0384e20784c50080200c480c00340c0b5681c0200101c2d6001c00e40c001e01e607001c0340351082060b080e00c800020005403e000e20303442d00e043d05507059950300e01410060101c40d058800020004560010050305540c2c0004200c42c02006002080e140c10b914500903140c00c402101244252284110008110358006032071501c16201c8c10083c0240015041855500d03002c0c2c06225520220745800201d01141d402c020f10641c4044d000405521070380c0700080380803505c1c050b00c0d0b8000a400000c145a1460300b5001d0380340700e010b041c0c0c0140010f1401c03901c141e0400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 682806312 1250 682805062 682805069
    0x216140a03050f030a1b0c021306080601090b06221809120c0501020909010305061902070f02041107060e06100e07020c010e030a1a01080105010e01030f0b1e040c181104 74
    0x280004c8003280700b007190f40d030001030500303c0002c140c40304c080c00e280b0140891096041c101d101d1421300c1000c002c403411b240107200c00c94000c00003e0000380d00f0301c4845c01c00390582d081c00542102c000c0c0011038a58054407013041010440000c00e400c1c0074113140c0ca400504102403200d02d001d81c1004140000983d10511300800301e1346510b40074040055500c0c1003800780c41045c2c101644810f940b000030050080c040b842d40d018842600d41380b02841c5800f10b500d400c0c1d02031050302a0640d403100683c000507041c80d4000c4424100c0c0320318920702c5d000700c55440d401143d1a82000c2549503203c0c0c004c008002e022000004050b04680c41100180d05d40307444000c4d038900384413070068108000341a410020303440800c110751075258010000c4001841e10094884081d00900c036140e400d60a10b8000124007201c429403e05170780d00308410210201c0642c8616150003800b03880c0c1081c0c008030b0100040c0411a081102d40228441c0da016000c0c1ca02d020050611000203081480c20645007a0030781e00e50f040302101b00c5049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 682807562 1250 682806312 682806337
    0x281407030f08100801150905010f0f2603040b070203010507170720030408010b10050906270d1a0106141c2c0f0d080402040b040f0216140a0305 63
    0x2c0e640c0c01a0350b45189642c0c0d4008500c960030f0881645204410141c66003e41d07060050401182c4e03601c070008045080c45204804261450342c01c140071a42900d1440041c40440e401075040ea10700504d011880e5500c541c3c41060210000700d0a18210f280070b0103200d03008035062034203d0030064180c0ea13655001c40c1c05802d0f80244100e24250460f0141d10494000180c03060b0025a0340304c95560741072501a180e0440854401c5868410608031a400f0b01e086d82c2540314050040c3d804d0448035055100301030403420401c2001210704040a50a82e81c1d6102c0c442410303c5844200380c8002d40360f040440c007002c180c0000092184000d060600c1030066010349815000900d0403150518107007181000800ba6500d50b80c2802106292003101080e0141101c030110074607004403aa50000d5040ea5910749000301c40300d20008a200c80420b001d403a1a4000c03604030600100002454070000464100300d03072260b00711034a510800070810043c032608901180d038107040c0c0c00180c0401e0700140e900800c18402c000d00f0340d41c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 682808812 1250 682807562 682807577
    0x20901050d11090921070b0f100b0a0c0317070503060609130504030809070b03090627070609080c0901052817070f0504020a0905060a0302281407030f 66
    0x501504400c1c0220309880900f4100326401c000d40080d4441a200046203031141030b48038a44c04c2441c80c4d40484030341c0381e000160604907441d01d44100d0403101010300078069480c401030340030881c06004030080c0849111070711074103034a40843c40c0c058040b00203801c1d0002204e016030108403091360408101c076030202c412200c85036241c5820000500c41c00108a1854015203800100000c00d81c129141d40e000e546a84100c801150380c2c0e0748911818030048030301c1d2609400c0f6401003a01c0c03160200c2da8400c03080782051140c00d448207c00120303103000c0256104000048540c03800f0810305205014660842c1003d03181d2610660500021420f00321890f00c1c02201c0311020002c0d00b48404800284002074815007024010b81c059181e5015070f584620701403110003503483c00c1c000845141174030846101c600c02c0c3e200c110809180c01c0400000b900040454030a0540821940000d003503032030441840c0403101810742540c01c0f00408020104803071084008072184040010002182d0041d00006012000b45403401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 682810062 1250 682808812 682808839
    0x81f050c1b0102030103020108060a060c152406030c230c0a0b070804120e01020a020915040f090b0903040e0c0a030609050f0411010e10050c0f1f0f0902090105 70
    0x2241442034040c0030410790003040501280c1d1006400550490b4000d90340e00d0050f071900420001501d1441c858040810344502140380000c21200702010000031190001074021200e200d078070000402d1700b40c0c2441d1086100301c14442c442e014800c081700310b480e0340340c600b0040601002484000410311019002002c2c0402c83d80e0701401e0030000302c51901d501c042c0040342400c10b49800380c001101aa003c5503c0c00c0c4030310040c400f040c03142003550807104050740240703810045502031008880c00580ba111132010032410100b166251401101c000d50083c0b60300040740903060609200443c000b07003400c549500304010412002003011541c039041040300301c0265a5041a500540041040e5032103107811508020401084503000b41d507680c8141c0c0a802c64141805018004442d0421501c1d590fa81c441840c80d041c2c9291403242c0c000e807000c500d030340c01103810603801e8000c4246454100f104403400500350340800d04440b071090007001c0c003080e03010f6000c0c811601c5070f41c000341400c04140507a40c0503184440044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 682811312 1250 682810062 682810081
    0x40911011404140d05101e061a120a06081e01051005060403021309020306010909050c12030d0902010e030a0516090516030b030a15020301062304170304080106180501081f05 76
    0x1540094100d60100b00d081d500a404440ca0040b490340305036820703d44000002d00854021070103215010f8818820728140703201c0000ac404501c0900350018007542d501c0003040100003000000c448146245c2d88000b0300e0300740c6d850542960801070001d49007a280b42c1c01000346840708800d0700c1c1500d504494001600c0d11840c0403500410204c48060351510400000185a816071f90050400c24040d2090b2410740380a00c051225045160719140d0050707004110721403c03036036140d00c42489144145001e00b034800c51500003902d4000742e005c040e600e83d0004400905a035480101c80c10043c0440ba034103100038030b002c10046e90070700504130012041c503482e08189203003a5002d0002c460055888280d80c0e52004140009038002c1d04240608004114940d081103140302078484c850740350480c070384000c9103402e040808011072402203881c006800e200c05d2002068004c802c6c0201c2c2d001e81107480d9405071b41100d9014441c140c036010b0340700340c0d410f403c0314a02e175010344140502c403282e942c0b1801c40442c5036107544004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 682812562 1250 682811312 682811323
    0x80d08090f1204050f04020c1f06030212060901050708010303140a09090203130b060315040f0201050c030c010203090706110607082a04090f06052b02040911011404140d05 75
    0x250001e0141507244201c0c4000c02c8040c00c16030300c0544030000704542c940300340400c038032403141d51100c65400302680116036158112000f00040242001042c0d40d0750320350116400208800044045400a02c2040103648003449a5540602d407494041890351554402a00c10481800180818400020b1100c855405456148020001064215682d00c0c204450280c0700d4501c03042243c0c20401d840100c1d01c00d140020348120164210304003000c031501c55a03900c46c4408081d481c101d043c442c0602050742a03003c1840078204198510002694a01d000e1030501d0030000700d40c00400c184040c3c081c00000780358000403002d900201609000c0843d44603031513182d40211170080031040e94801189012030858070350020f0300450b0b00403032042c0f00c580038554103902629018003a298101c400000c0309006640c00341c2c10789010b244001540e21680b01c90340c001c07806580c0c0403d01a074804045607513038005035034458100c45201540c45616030804d41085894241115108070151140d5101e0201d07030280b01d0300b4401d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 682813812 1250 682812562 682812583
    0x105010912060b15030403020105010f053313030b0f01030f1416151709030a08070e0d210206370f0b090a06060f0f0c1209080d0207080d0809 62
    0x4e110450a480001064991003150102c006500305000010076030001203c440517130308010491000200c0012021468899610040004100c2c43c1c03904803da02034903000300220108002c46a8480f4154100084041c030043c1c40c01c004120108010000301d03071000c05421080f681702c500c0366046000c9843c42480c00b000c1000b01408500d03000f00000c0c011401d00d002198460309519070646408864074841440d860031101e0040390303001000090300702071213851110f500520505000c1c000e440450b010880e94450312404598a240c411044051201413109151040c00c0d0f0b84002c00c0240741c0000303820a45036101d083c44058420b103c030304032095101a80d000a1807048500200074011146030000007038006408920700a4015001048003181d060240c801501d00d6a10345150600c98a9030840300c0f4150581d8600812404e036882d84000740b482490f122032a00d07103030b0f10f40a04d0360420454900300303424001420f0656018002c10000e1080c08100c0d2001d41c0c026050407001580d5003100c25040100c19036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 682815062 1250 682813812 682813819
    0x3140a1709041e1e090c0504230108030703030501140120010b0409051e150f19020a020706140c0604060b0f03030304060c09060f081501050c100b12060105010912060b 73
    0xb295050307290b8079030700101c166140c128458504244c1c101158003101e0603584090800c803143d40e030a0019090a4000158050702112910b10540c810b45001130f6a82d03080c2c1100c0096040001c01c0701c20301d80d040c080c46002d003d00001d00301070031101f0300c0080c0410903034462001c4415400768100c555400290300503510764101401c240309080d441d280203629038400c0d07044034584100e025030358488000c00058514911f042045002c803076403183c1400e1000036100412807150610200041400302100e8006404d007131810f5001050264203200c0003405420103100603212444090003c80000b080c0082d8480d01300340c2060002500a4030ba101003020114260a8190035100020500003001079950180692040c3d0360f48004d10a81c80e504121415820200d940e80020450800714100c4429090502841d01d414146203180500c02c9089904020f83c2d190076090850360b031001c600c0c1506004101d0000c480300600078103038075818540040c1200c2442e00980c04080300440000c4104440da5120702032529008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 682816312 1250 682815062 682815101
    0xb010507230a11100e01020a0305030a060f06050c010f050c040b1c150f0905060a061b0b27190803130203070306020702030c04050402100507030909140103140a170904 73
    0x900b8042c4506010040284c000c00e8281d2001240c2c1c0d2040000108900051b4050306001d425510129143e420140511a80c60307951000090100f60300d8900000400d0746480380c03500e50100c2174150f821036104941078540b080c203043c00c02c090b09c1d03071480480302034814400e039540d2540e40724002c036514a040782803290710082c50500c21101001d40240650101e90505450f680c40341e4503000044203481e800d50720180c120b004000c06200e8140202000f01020a200c2152802009662182000b0440640e00c1d40b100212a152441c5102c000c10a00781e106a0454000c12044903407080c0c41e0f180d007064803c044d080c6c00010000c00d0031020448004000160028100e8240980303c2c1020b1000750701c0300790308034464826508520900d00b810b024a602c00e680040c4910840c003800d11040d20103502002d02201080254200403c40215510030f610544200108000711981035141c0300403081030403200c2c10b200d684014940d07070018600d02213000903410322009054582145c080454050324100441c0a180d02d000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 682817562 1250 682816312 682816333
    0xa0614040503160f0f0302010e0d0203030d1a0109050105040807030305030c0c011a3c01030e07120506060111030a1407050a050604200f0415032307090b01050723 71
    0xa00c035503c0c007034810f001c50740c2d200c04e40d81d110b030450b800a9501c0001d010802d011491240d601e481e0b8010f50005002809030391030300c580b0000d04000c840c0c140e01e1010301c04200c80903801842d42d2044111000c8c01081c03c10780e11303140c00d029001e075803110700344001000c2120000c0050741041c114410f580031124040020b204103500e568201d240e100407100003900885d424400107510790044041c40e148d0003d42880d0301c51018165036941000c19900042a060588904805120610401101000b458441141c00700000e00745025400d00c00301410700c3c1d0410400d200d1b240342101c8041300711241e040f070900342410340103000701601881c1d00400e007014106004101c0140103100010030000d200d2803144858540e6401030319280c0c0c4140340c01c24001a040300c4d101c80390040504041d400140c0d23041c0b0f00074942000c140d13266615030241d4090710000b43c00e1940c4040ea54640442004204068141050140240c0541d0170001b00103014407507000c0e0079410000c0780704064081121422111002d04070540380241c28 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 682818812 1250 682817562 682817593
    0xc0b030c1c0b0f040c03021b0109020f0306060901170c100206070e0102282d060b0406121112030414190b120a0b092809020a0614040503 60
    0x1c1540c214590000c52104039030010a5449111a21403008000c080800c1030041440300801c00403000b101030640c204081c035071000802c1c0420448403000b200218190690307106210090b515000781d140690700c80000d00c207103540c80c0740020b8151f0721410351035612280e00e1003005150481c00641b0540144062150381040c91f07000c03421511514050b10764a216880590049030782c0c018040c038107030583c2c800100200c280307050498840e0a40e030160015052190080b00c0c2004001d6802c00c3d40036008500144440800c9a00c1c020050642c500320b40410549140c824007a003205d1030320200914100202c200c5268680e20886401d1025125004072610b070f644a4140c0480180124800d510411005840034030a50040c0760560945903405200741c1806040710400c403400c01c019180041140d1a02029001a200c2e0084948260341c003407146c1d02d5007000803084046034042c443c100c0d18120700f814038600140e201d0010540490f645407030510794480325510022524001c5411032a0f0600981d0081e030322030700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 682820062 1250 682818812 682818817
    0x1a041d06010e10050d0e0a050304080c27060f01030e0d09180203090712030203041503020306090a02090d2004090f120f020c0618100306090f0e15040c0b030c 69
    0x410a03200c4825800303a20b4200050780f01c0709501080081c4c400c005000403d0031a4000442a0000004072802030b00c041d80e60a0035500582c0050031a0740c040c5145509501e40442c5d0600c0000c0d041e0b00703001204d40c02405201c1e4204000380400c1c028001c080c26071300c4a91181e403061201502ea241541d1103504204002080e84105128a16400541c0314100382840748910841c2d000343d142c03030010040d81d454a440c03000c071080941010b40560005003c001425510040d91079a01603141c1e0300141c0e00d19203002000305050028280d1840b0034414440400e517603e400c0d00f103002d2190000810035180300749190790b0300f80c100c0d00e498803a00541005402802c001e5a8001c8042d420700c11600b10383d4001b00100100c8041001080d8840160301c00d06610446007010300050540d1455010f4010500001001103907803540d544050400003683c0380020030a0752110b1050f400b400729028028020015402c0c5050355400c250300c2040e84800c0007002041c20000d003440c1c0000200603500f0382648910f00204150385d01e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 682821312 1250 682820062 682820071
    0x2090604030f0b0429061e0604030303140a0e0a1506080f0705090619060521011e150c03050921060a0b04200a110f1011070305041a041d 60
    0x82c03170000d544c0b6100102000c000c15405840d50f1455880004100d01d074010065030a00e203400020601c451511580b0040014501039100071440d15031040720406028002024000c2d09480c01170102080742e40800c0c040c507181e410540c041c00d505060156440100315075404015180300e80f4804409940380410100c08a070303800c4030103160590391182070001c424191130003c04411001d02c0140240303400b034800b610150803504411403441030f0301c030681c100140b400e0f08001e14803c0728101c000040c843e8100f20308058000c1c810502c05278040850013401d40c86010400070144800405c00800607220700b07401d84c8a2107071000c0050341148900904a0302d03000181e42400c012810f140c4648920b0a15010368045000ea1418a035003035400300d450341617990000c491000401040e05200e441c1590100300700c18040030720070041c082120b0310142001c00c4420300015a003020703005000c1100400d0b0048207407001c4454540401484042c0390070120114400d0750440003204414040d0109481005881107205 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 682822562 1250 682821312 682821323
    0x106060e04060b340c0303170a0c0e01030b0303070606031a10050d060f0b03070e270703021c0807081c0902031b03010608030313060c090b0d02090604030f0b04 70
    0xb00c40d200d01d0200001e110340c113804245000c80c0881c0e4040300d5003c2508145944012149402802140d40e880c40e154003d5841030f4001040554090240c00b88000e1090b00049a160104910b545400000d05410308a1000781e06040d652004a85262018800c4038201a8000380420a690f100d1410403c19803180003000f400b05040800594864900e03c2071350180d440090928101030352a580c0d22000d08400352a007442540c441610500c580c508018803406442903c80c01c500514083c40d88115585850034240700d05c6000c08000d1031109008500c1800f030301d806850f080b000c6104598802c031b0b410804070004007004070005040d42404080806401110000c584035440100d080d407400c1e007583c990002c003039030540000290301e00d03916240104074813034003014002041031355840d050340e4256041103454019440e0000042400c0141c10b22401d4880c9200e414200643d80c10220352400b40e024405c14040007540c001601220f668401098070015640319003003550010843c0703031044003044156001c0b200d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 682823812 1250 682822562 682822571
    0x609060e010c110c130603060c030b010305090a0b010e09030f0d0501031506080303130507080a0f0c090c09091509060347040c0302090c07030905150f1b0106060e04 72
    0x5691040f03402c00c18400014006041d4800140c0400c20031000321101068400d5440318000700250711805005040c00158500240d059648030015003138580080010610b41c0110100d071000601580000d0305407901e0f006126007503560064407a186101c0d108540484602c00300300c02903141c8075900140d060b6486a50a05681d256860b0340304159a09c5000d8070690f81c206000086c2041c0212103040c090301d0240781140c403480d596010007410090700c694103507800f07401c5400d904184440e85207104020a0b082004000e050b114400042c00001e031400303107140c07454854042c0d410b180000505040a8581d92104100342c07075491904010000340301507c2001510089540e60513001100081c840f480b40d59101c0150130003021101d0308032880010310407070300c40e000040c01002680710747c40724510a80008000541d00d001e58240602074000307a5001501c030f4080e038a5408001205641602d9602ca1820041d070345488081025500403c20040d040155604c2c003038001540300d502644011443d101070b41c0410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 682825062 1250 682823812 682823831
    0x70e0a24031401053309090a020f0906030d110a0203010507053a111303030c0515060f010c02040e120a030b040b06160c1a0301090b10020606120a0609060e01 69
    0x10709030ba404440c0c071812551152103154107000c800c400030928454401805c0000d034004000200f284c10b0a4441260951003c190902181021240310321001411141c42c0c05518000b40000d0f910740d104a005420403c0700d02ca00b460410041140c1aa05907009009201602d05148018040c2d042a4502d07a6a07041c000745807260110203881484503c80500726030700c0070844480041020300044010102600743c1002140d03034001a00ca61000514829500c2440305809030a01c030f40b809a03000050702c4484030301701c01c2c4003981d980c0d40301c1d130001c862003806d14420200603400018002e0000114a020902900c0342001542c0c41d40302c02841c5104284c0c03810403454031070500380012103946c5502070b90403241c1041105099005803281b0f49945200301c00c000d0030301d03880f0385c0c0601660000364074641668801000603c80000c581c0070b505440304081e202c03155100f0900c80000c0d40e40d50003610450042500e00e60303043c5000c0e001d00011518036000b100c18411004146401c8000300070564040196520303100849 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 682826312 1250 682825062 682825103
    0xb03041203050f04021504030b0c090a2304090f020402030f040b01060c26090a0f0312050906030a0f06090e0307060507020705090708070e15030603010617070e0a2403 73
    0x1030702800f00c0d1030002d8a10350743c5074280aa42e20301c45030703984444941440000001444200c000d40b1940480911039200c201c03010902050704400d0b049805003071a039414500c0d29000f102e9055040365421035000c200c245190402c041c0b90070b035448004c1c2d0814000801c11802e02000c41504d401030b44103411070509070707170b039144211041c0540200040c014802802902c4156100003c0181e20b900e203041d0482c64051808000f54003400e25501040009040713000410501101c4070325004507203010f08080346840743c1e03280000c3c0c041c4130050560289a60710f05640c003600700349500c0a8050103010800700030900c4400a840e03030381c3d00701c60402c8460b0b90800c800500c0c001d101050007000c840001e010302c50319480c3d0090075180060000d1500007000340d081000c611507545d0001c808403d22400c0000d0750703642010000e040c00c0d55540c1c0c2160b010b0302403900c0c03034102424001810340100c8103d21f410307581c9910340888040140084030340d10101900c0181950813000389818a19003140d11641c1410b540809840e0907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 682827562 1250 682826312 682826321
    0xa0c1412040603020306031510080f01050708041b180605040b060a14030a14040c23010210020703090b03011e1a0306100c0f050607020d0c020d1214040b03041203 71
    0x38401000511082181e54003c0c3c0256800000080903500c01854803100707076031181d10443ea060a03410032030508000d212000d1110781050740080d00240010328018202030800400640010154101a120b1009413241d18107250040c0401454082e910740141d0b00f07000142c28a8010075100c0c91070150418440e00d0714004942c284040b9480301c028031a000a4849a20b800c000c00811000f41c50300a00b103411951148032920a42c030504083c142a414032f42c00c0d144840000003240121400400c1d0388540703030307000141c10344580e4010703602590350b010300d00d01119000e034030f580044c05072240400041402e402c02e01c200490240118445550503999000d0726602c508040940700205c1c0040011036458181980458060109410301660854a03030741c070541e4400c05850f0a0301d5a800c600705011800d80e06000c400310100c40c40c640600001c2981d0000b8200d40320b040801040d04e00710741005550540942544c60348044001403007a02c0c0d80e9180d05440030307030344220b80c112480300050981700740340c2e40207104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 682828812 1250 682827562 682827583
    0x30d0c0206071d1e1816080114010c0b07021e010603032a020f0a0308030a0b0418020612070306080d0804031b1109060312040602011e05070828020a0c14 67
    0x10080c101d915501c01c80e010682c003018007900080d081012049080c03400020500031181001d5032091b81c611400300824046040e000f080d03c290000200a511b607030702c02c266074407142d040203a031a01c64a480006034606081810f001140680004041211501c19480230046030301030380307070b800380305820766090075030b6455031190003040d14180320560003d820701c10b1003441c8802002e801d0103080350b01c80c2c880a03140e8000302e03054900551904080c0241d0305060190304894811074420760007441c45980003510300d00a18008000d0b12200c20000b80e00140319400410007400481c040d0b80c080081d00c44010402d48044406a000c2071180381d661180c80401450072441ca40c0148403110400200b80c02c00c0070444000e03018580c14402e110009280c280604007c0006116036000040c020224800b01e140040108041e001060310b000d040227640d64008007004d42c070a08804554818124460396101550407480d00b802415201040f290f1a031900400800e4081c0c0c01002402b101401104242c1c2c0d59100350803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 682830062 1250 682828812 682828819
    0x1006060f0206180c06120612061306020d1506080a060e0618040c031e050f013606020d021c0c021b0f04020d0219020d02070302090702030d0c0206071d 66
    0x2c00180c1d040340d0010b0410340710306115041e16402d038401d90028605800c04070411022012210502030349250182d194a0241c2c140000390840349005003c41c2e80160b0001e002a101d43d4001504007410718807980079000488544520f0019141c64030740090510804440304032096103000800b040001c480701003507102d02001015a1134450001021103c11700380035000302e0b403564000f880070001900304403401d501e41d040f00718001c84d000040e05040d4076081071055124100c0c1d16115032111a000c8064045850356800c00747c1c246e104400d2030445441ea800c03180c0c0039000c144049001a0070001c04e8008180a81e41004011a08060060207c1c00c44800485c15000741c3e01111445a2402000310305200380c400c0100381c11043c00c0008082000e0740c2c815102c0c1c0298030343c001298a03110452042403c00c9424510052400d605055006544c8000700c0c080a031041030b0040000c3d22007131081007282d0b9228202c01c2c052284107a148800396442d202615204049100c840080442441c0e01500000784070005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 682831312 1250 682830062 682830073
    0x601050a090e1c020f0705012d12141602030306010215060d020a030c030b070c050c011b1a06030c01140904020d020705070b1c140a0b03010e010606021006060f02 71
    0x29a000040c49a2100600340d8090b80422010342d01c85a04003c1c0060340d00c1d0044d0a611201402c05800c250007034100a05014054400c0e015800340341c0032103400c089003a8544d001a01d25900f05a800e40f61041c0400d01242c104032040c41650441400b141c050242a0300c0e603401d235072100e4800c2e81c8a00048500b50300603400400300114841c1420304003a009000540702d24000f002540220310720220302c2d00f0968200011903401c0042080c00b140d0164880c10500d0900b003031149907501c2640318040c0307068081c1042161040d10720203030707aa01c81500310309078410003c02000c0211450406408001c4420713600c01d0003460380041482d4007440000200c0c40d500e6500c94a440d0729402000003d412110203880f11a60034498400000e40030041032002d4a04e082c40c1030307118240c80700d4641e998210340103c80411820800307040011092015842c1d04862006008600710043c207000c64010034004007030214941c24031f1400581c003034002c070308104401080300080c000a5103540f0b080d41c2ca20144480c080050340503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 682832562 1250 682831312 682831319
    0x307180f051c020406360608100506031f090308060103110412230718140c2b06050f0604060c2a15030b030a0506071d03060108010c09080601050a 64
    0x80b0b22441c1d00c5200a00c0090075075140c0d610403011000020020300b55110030030000540324184115103d00400049003440202d040101030303a1a13410079200312628941718000306078240da0521031a0102e111028a0700b00841d00c0303840f1000540381c400300079030114403000d02241c103951180c0a01318294405540d5680f5182c9050440140b0460340801a24517540303502da050840303d00500d01c0013000280500078000d85040c401002d21400c0c09100003900140340a0303d162604515810b41d591294111a50a840b04449086111440c04400c0f549841480c13103400581704400c0c0b0707404481503036000c1e503400d805900320006005440c8039600509010031105c0070b403c400200c500c02c000c0251440b00300302007016840014144640015504400a0700600c044034042c4c082c0d1502c41c22103507110032001051500034a0325030035100c04000d0241c1c810000b1102d0300f0b50303032044402d0805072141400307011150b00f5a51415100e00030041c41203243c0000d0208200040d9080d00000c40505031003004020701541e603c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 682833812 1250 682832562 682832599
    0x4050c0301180e0307030f08010605190e010c050706020105190e0a0f0201050f16020f18190b0603130c0506040602100506010c14060f07020d02060c09040905030307180f05 75
    0xd44440400b00d40da110b150202c04403900388041d01c0824481c0c2c46011161001440240c40030341e050b0408420000d00740a8010145080c1c805075144403294201840d114032a080102c0c0c0101050001401512442c0000074446605501076485a41501e500f0001400440c401c1000d445006c2607200c59684054054004581e0490401e40d010344141080c2d4602001d192151030a03420480300c20000c3e80d121401c075000d6040c0100a81c0c00040d040300c0e0610315401c2ca100340c0e0752003680948120941041c00b146240580f109500019011784010a46030712807a1109184a1059034103074100c9a080c1d41110000d401e0a195040c0c4043d5101a009004800b241c00c1c00e4500070480203081c40e0400c04030034491804503d80f007403580c0a94407114040c08288c6015407503c510200302814138021948200304806403161702080c125001001e043c1c07081d950740c00c900001409044089005401408000244050075400010030030103003c0340701c50344080687d107049401c0140c0c020300c01d1607044126204000f55020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 682835062 1250 682833812 682833839
    0x6010e0a0b0d0b0a0305161202060307030e0705040f0b0a050102030f03010b0a120c0201051e1b0f040306060b0414010306050a050f040f0509010c120e0309010c03110a2004050c0301 79
    0x600b0440010346000c07540000d4076001181e03000b41c4041d00710141c0461012074019104001d0403184165152030380255001c47c0084c8070051000e0101580d03040e5406200c402444010001e1200600c107100d10791407299104c0082c005a502c40c0d01c540b804820020f00c65002000b6074142d040c001104504580c6001c00c4400307994455a80d400c01c21070449805040c0301181d00c166120700c04654000500c1c1d151000304000f01c80c800340b034000c07a10400d403401c0041c03851440c80ca140c241e0038885a016152020303241c4080a9004030740005125030704010001c80c0e0480345034058030407030b0019010320a200c000280198100e80140c06181d82003101c04009015505103503211006040010b44001104000043c61500720b44003034807410b0705a51503e40c2406d90319449103921001c0e0f08042000c00c4248040e85170642e903445000c801078184840d0810341c1c000e0500414480000500d08402e03200301e8070b1076207000030112020b442911440001400c10380c807a401c1900c9614400e00c16001a6440c50f403d0496040842 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 682836312 1250 682835062 682835077
    0xd080403120902030114070806040605100f05210415270f050a0309051503131407150c140303101a040506070b040c0b03150402090f09090a0b06010e0a0b 67
    0x1c1d444045560050f1002d124001c06104c10803d40304803402c050000611554018140c2403040b03007012418003c030741c0c0b88a2246c1c020001418014940b100d207500c15100c5010f4034100134800a008078122150311509817100e4421032040c2c85815058000107100c07001c5030401000c242009146c804145038110200c440c804040d4000d0700c80f070f0301c2203405540f064540140d050007240090090b520030000341c10020403103d60001c40e0280706044d460a01c0900d8015103100030040c00c0141801180c55524000340b01603c041c3c1449150720611054030382000e05070f11031010048980c00d8445402600740000802544d02400c0800d807060305040c42c040d010590711455a0307254440590801c0000b0389075440c8002000c1c4030744142c0040099240c142000480310840b9841605102000c00400001c0c160806035500100f0044a0041c3c1f1207500070702207500c0140001100d034129800c58107014281900050386c01101c0d00c1000281d649a4039000115240c0b0b100c5405541c001d44c01c0a0140400d520746000b42841 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 682837562 1250 682836312 682836347
    0x723030402120f0715140d0e070f0303021203130b040302030c060f010e04020120010f0504020f010801080a080d021204060e0d090f050402031905130c0501020c010804080d0b0627030d080403 83
    0x1101c51407401c401b46600020044070700720384d624031600c6680c205000000042c185c044001d01c105245840207511070034002100525584000700040d5003c200c001002205504826800080d03d41450083d540341d01811040d40507118250008500040c000000e2b4180c0703e94901031002c03501e5079401901c04900c0e090031036014555907099010004070034850407410403e50356000c2041d062074018020140501c01c0128100100b180050028400001da040c3c9101c0d48203250300e54072200750301038100a00505045000a5240750180300034450680c0101114500c0a8240e8640c506440d5040c0e0b03940038507105084140080201c208602d1910b40d000e160b0055011848180b510511518102140ca00b220303000071640702010a00c06004a05c80701c400034101c2030004044906c1000c0010703010100003031000300146800600b103805464550440c401c500b0014200c1c54035201c0c0c110280c0c8281941112500700440c441130a00014a000148810f00403250340b034214840c0c41b61b4908a41c5800c0d401e401ca01c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 682838812 1250 682837562 682837577
    0x1404090f031206210201080a2a0908070311060c01021306051209010911150405100f0909060b03010b0c030c06180f03043b0405010203010603050702031306080723030402120f0715 78
    0x49c0007101140c01000000091a02098030b251194060426030b001c1d00480c404d60302c984028400540380300044002d0000444800381c0b1501c2c0da05000b80a80309480c0341044405200c200003400d1500f0201802c4c2c10b0000c035001d40680e1381c80d0b01415088611403100603001c244d40079581d079260b081c101140480480301040381c6261030744850208049480007009500051921801e041c03000c4e511102642c0900388001e001e00c0074501d01040c2c2c810b5030006000d1290304090010759180c0c4039074100200c403007914038003041e5030795071030281100c0c1004001541400d0b000d0160072445540c122010084800b9554200541e8040c2d030008000c2034044480b4200c411450a42090701d001c01c562401c03461403080d4454400075030760f5030403d42c000303081e6040540038409650060005000c040d140114103401d944c854503144515543c0c191040300d41c01002c1000c450481482000741987c40941c070300440c41107000380c3d160302100800880322aa214030002c15282540c008000a00907801c0e11001c65151800e035140840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 682840062 1250 682838812 682838831
    0x1501110d180305061510080f15040204080d0f180f12141e07060c02060a11031e0409111215150a0f03110903071404090f031206210201080a 61
    0x81c80c00c13005544200808a08070074107006071900001c0c04c1c128414a1a044c0100e003001a09092140ea02614507541540c03002440c10302a01c039075040d0741c000c00070b40340bc4640a1030521406040c0c205d0844c00303003000078484811062604041744080c2e00701c2d0b88106a101d03141b8585052035101c0014420115580b0301c1c0010904401103042000c01000e0003004040007002425a149615000c504d41c4800306000464000c4009603a5040c181c1e030519542d81440780c044e8101a42c96425482009251140720b03841c0d4401c0601c20607240b014005030741d00204200700003030b0324203040c0090f030085107580c41c003c0b071802000905d02504041c071320b0164203000c1e00340c001e60b0040e201c2d0b03180160400d41c0c0410008044c4034844541c4c2d50b040c041c1d84000707240c60701000e02d041c0c00c07000425154441401402a240b5035072483c030001da01c1d16442601031540000d5400008181403400030311a80403c2c6000c48840e0070f058010070040c0f0300200352201c0c228542c0f00c45500313501c83e50055a01c00b800903d800c000550311004032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 682841312 1250 682840062 682840073
    0x27011712090343030c14010e0a0b0c150c1b0703122604052508060c19020601060c060504030c02130c0210050c0a110f0d05031501110d1803 61
    0x50000c0ea0903455411030002c500000790b8540f0351002c1d44441d1540d0b040d41c00c0022422440c6140d09039040103407185408000c140040c1c400c2000001c110343c0020b034442001540049010150400071034a01c2035460b000c9941002c020190800d40303801c29002000c1140800d200140111020301400460640303100d25520303140e00c00702152640e06034011503040c46500005a4000da00d40100c88034007201541c0c141400d440d40c44e55125010301c004c3c82004400f080015404460280c10020111002280d401d4500040c40207855004040030350441c00126481c0c03103802d800030400700d041c0c84040d038642041a90f140c0b00c580241c0809031090701400000c1c1c04000150700e40781c03d01c910481666002141004849200038a0a19458907503a1081c0c0341030280200f2103c003038121480440d05250483c0c0740c105081c40c00313040101d1600b510704c603480f802c3c8880e11410741103000345210315210f9410b141e011490384019542480d15602c54062a04048020010140900300300400d286000b051515020340700d0f62030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 682842562 1250 682841312 682841353
    0xe0109121b0c0b13090507140c010b03061501020f0d02060f0a020d020a030608101104031104020c19170304031e020c0d0506010e0601090f03080711270117120903 71
    0x14040c420f80018070301c105a101003031440c0050400307410802c05817405050003020024406400d154480c400100d1004c400825003000c90300650090641e40c16003002c14030360070342070801420180035005840d010f07984858085103918104246402078a401c2d56000b100091f0760030010050b18084e80c2c00d1000000c688003d2010707224046494a0015000c0d0a282001d0315203500210080c850307d0820b11000e03040714030b14040c0c404407903001000e502c1d41d0180c100043c0103030140310420002403140d0303030000b0b000703c0402c07180c0c0c080140035040c60043d021a1300c82c242c240c1c0c40221005000b24104a05030f10309410498060403a140c50303441600c1440d603551001403185998480182c407079901c11001070040c0380ac801c8519400810908080340c000345000400542c0824510019010400105020040c00204c2082c1d24004800402c40b02081400380c800f030000101840070b88201c403820500118503000c0354403150755401c80c0c11004010084580f41c42c1d1002d03610000c0704940502030170340c2c44080040c4a880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 682843812 1250 682842562 682842569
    0xc0b0a120c020709090b07030f0e0d03020702040e01020f07110303040b071b0f08071d090d0f170a0c080a0506031b01122a0e010504060f1b0b07030e0109121b0c 70
    0x8a800c5508001d00000d060700d8270202513545251828810b50080000011610f0740c4600c103040241e103842036400010b0050030001d020360102d500000b00182c95120002c02131006910400d003140c00741c1d1021003810340c4c81c0118014088070303080c10003454000c01c00420440c004200b07050101c40043d92a654149880d41c2140d102c0b8945a002c0c04003130200141e54140b4805c1240120b510440794508400c045580e0100c1d56422428814501003406105108260500b8144000040c2d40c48a0a248041d0801810040940c50010b401780010074410f0341c2e10b000b8580209401401030101d40b2141100765600300c2d02d200701d5814420100007040911000f802154146985c075444041c895546001d000441c1d041c8000301010089507100410036070303811900380c405451181c504110041c1d03001100703070343c2550000d680f5410501e03142c108100700310104100911030705150342d050040645104ec650309883c41c080f4020903140070080b40382e414038800c41550030036062003041c10700c500c415601c500114488641 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 682845062 1250 682843812 682843823
    0x90c10031a01031b111203150f011b080c01020403020310020d110703080103061805030d0b1005161e0b090105162c0402040911070c0b0a120c02070909 66
    0x450401c401900403801e04110502801c0030300c50000c04007150a000d402e1220114240b1440444004038208100842e1807850460400e1350303030340d081c4a20034015040508a00a1040c2c1c45c00200741c030340b9403107011040c4900c6c01c2e52400050640040c1c1e65002a03401c5601c64820b9598207004c0000036a508108444410200c5000180c4d5011501c8015054441c010191002d02c2d40c100030400000e580106140d04680d003144c0000b50030502d02090f05050302e103165000c0c1c107910010841c2102c1e003001380e2014140c40011981c802548079041e0007642d1502524041ca65031050400c200000704a0395007070344006611042200700309101c0c0365500c88020034103890010550395980c00f00070185000d202240c0980c0c1312420301e41401444084007405000c0200c0000c45490b00100c907900f0540c8a2f0380507940a41000503080c44003008004000c1c9050700140760980b101040b8103070000702c00380c81000312a0052415610010b81d00b40710f51300000034280995051003184281c04c1c0014520386c00340700350407010b8401e0303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 682846312 1250 682845062 682845071
    0x4020903030a1d0f01020316020d21030b10050d20040f03202d03120c060a0212041e0501150e06090f06010c0302070914040213060807050603090c1003 66
    0x2400f000f080805400b00981c091400c8036507102c55680c0000a803a02c4611420004042c1c201c0da01c0030600301070741268000c20341c030015176558040b030700030100c0080b02c3e00e820f503000c110448002040058840e680301400021070001c000c400d6100b82d450300424859a0000c120507800c0902d40044070f1107510940c48110340304040301d024420480310523a558103c0b0070928030150584018000901054500684650445404202d2081114410709039a01c81c40005007030301c181015500c040c00560b480702441210300c0c01404000307442072a1901c02c0d52882400098540c0d015130b129075690300c08003034500d001703408280300c64003400000340c0c24010100003668840c1e07960852403625400002d101d40141415104021074400c20514036106180d881d4400740c00d191540301c60115090503400c04800c0e0304881c205d6401c12030324101043d05000c0e018000e0b072003910003880f0410f501d800c03c1c040321424058840d050b0084441081203281c42c8010319044040401500d108909a000246020b0344030f100050119803907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 682847562 1250 682846312 682846337
    0x18060309020a1e091d0a05060a18082a0304090204031104020712030209010e0a1508011a0313020604080316110a0b0301090c02011d1f06180b04020903030a 68
    0x81040c5800408103c0c40343c10203501070110b40e91942e04280122082c02d80d40e00d29040c0c031036006074140603810a14100707940d01d21540f400c00944070700c801c40d04c3c0a44181481401003c0c0f03207080c1d0405c02d0b004d401c06500c9040c441841c3c040c2c4070740c0140c1d0100070629101c000f00a03070792200900051009048002005031703220315514127502122610b040a40c0300fa0310500201e400715081052030392104590b40341c010790f1106d14200680e802d00076054903503003043d2440004903005980f919401e1140c001c41d281c20806d41c0c1d03910809400c4c0f030016072940b0b030b90758424008035210f04661518180a580f00030121070806407500ca149155400c041d1008100001400080c0700f40031000c441c030703070b00c0800036075501d00d07800d08004444041d844103104d01d40c01c0c10364070f000941c142d91003036206040c281c107c4801110b01001040c0c00b503a0355900c1042120400b580b400c0c1c4c40303588112610a0b2811200310111025682c0058200d9400910300e90040c039803c16000c1019030f000780d60900081c02c05140a171a006000c454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 682848812 1250 682847562 682847569
    0x609091103061003050615040b070507050312180604150e010e040b010e09040c03080c030c0c01090f170a0803181011040513110a030c0206061806101806030902 70
    0x3280c1200c0805610070030a0004035110403045901004144c1408500c40d12103078085001c0002d043e00741c2c501c512001c1000301e503000d410001000e00901031421201c113561940101a150740c11010422202c010420401000c84000c8404c0320801c08024055414240d460400e1804034058000040c00a50710800e03000e03140d80c001d0174641e01c440054504224180c80e07a0006090312450b14100c4c3d1107074590700700050800441881300c001840d8070a8201d0b8461408800c45513880d0080750200310ac0d8000c0c0c42d54540194843d030100e2044035020f2100802c86860f102c00d403060144507001000c1140101d4041c0400301e101ca00c001e5009024584113401c15400440c5401c3c00c029940000601072382c03d10140324203a41c6a80c090310252201182c02a8043c20031864000040404040c184901c5030f000c03800b504c0b0143c2660080d18051401d0f001c0c1ca01e16a181001c201c401010080a10000441c12010650509000c0410351013444941080411896275000c1d1104416071944200300182d00d50610380c04508 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 682850062 1250 682848812 682848821
    0xc0b0d0c020d0e2209020d0f150b090c0c0a05070e0610050415031d06010602010906060806160305070215090304051207060f0c082b0b0a03150e0a0c060909 68
    0x45591600c10407a8140030006a800031207089144007400141c60151001c41c096171000030f1043e070082117640420349918184009002e14a41540c40c410744520b001c0d100c041a000300051020000c2004403e0350b101c00d061703c42c2c1cad0000d01d2001414820040728000040c2c04100d401d0241c1012840c407a001c1c46c1682c2046403c401c004058030401c28180020401c80000c010703d954820014140864006071585070702c85141d9007036101e1000352240d00d000040c21a010340c0038450981c0548814045103486450560790b424041d1000041042c000311101d0159109038030980c1c12400610644403c0d0002d04680b040c1100140d40c1c1695582001804100500e00300c006d0f900e00c80c00060143c407800b40740c510040e144140122303c00051182c001d5060080029000c122916001032000c0350140784002404140f007622a00021001146000d4580a552804840ca102260390103602194890b0003000050302621516850300100c1c480c2001d803000281240d0790680c040e1009a8891041c0b5107802e40c0c6000741c0703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 682851312 1250 682850062 682850083
    0x60a06120302031e120a020408070b0901050d0c030204170c09090c0102150c28090911090d02030106080123010911030a1a0402030901060602070915050d0c0b0d0c02 72
    0x4a410365209400640c010007550714501c689401c41043c00e104a00d441950b1160340003040400c01c0c05810011502c2003035001d0020f980010b412101c003e520303012102c150b84209440140402c1060100c800c0c00102c5070040c0c10703609a545000f5040681d01c4201a030480a8031500132890380280901003031074100380c0c10107a4041d41000041035500d00c2480080e403540026420b41c6c690407a200c2c0003c4003610020110b51101c0070012519442e03590504500c5200d00c9014070304000a1a010000181c0d0041c0707004003001f900103100340351300c1d008298040080e15141d0040807601952181e2000840b42420311580142d040300c0410080301e481c080c10b4018481d081600100303941407070b003100801c0f401490070940e1b0b448240c1c02000100c1c00d510b1548140d503012000c0505900070b0000080001e4424190401000c9910741d03022200d035a82c554501c0d005403003401c8403120010750104004c2240b0720b480c049444449014000440307a42e5242c000c80509a407000d448191486e8aaa4810324903640c10000254403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 682852562 1250 682851312 682851329
    0xf06060910060f0c05060411030f070b04090e0118080304031e08040206090d050601030c2603180105370305040b0403030b030c0a0e0901151d1314060a06 67
    0x100c1c50001441007180c21540246800c001a211030301c03241034000e46010809540100460399035140c04c5ca404141003401c1c4030954002d0045802e01038070a000000d000c1c040c1d81c9541c3d1098140307800c0c640319000070b10818135a01000e64036208078001049500700c190310214018041d2642c1d81c9020b0801134554040f0008404e0400c08043e8a180e82d10340c0910a541c0282e4111091980c2e00d82c03070800217440406003080608180515400082000a03450303191046880d002d489048540501140d1001141e03411032109003038208100c0391021000750700c449411027205040c402d00301840040a0913412500070040d4000d140c800c0c40e008030000b0112404d5548030f0741450103002038030305071743c0e1002609070213007004080c10707141c01445807142ea0500c4007004003a00070b02101e510310350340c66010140301d1003900d01d00c140d540303400000c0f20702c2c00040c0e03245025a4800c810a00b066003100710380705040b040007030941e12070220b4080a4400145540440d0440c0c014031402441c4500700342c0c5243c41141d4143d13000019 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 682853812 1250 682852562 682852579
    0x21206011403160e060c100e03090a030f0218070c03020c150909060a090c030f1409520807050109051507050d08011a0a0503041101090312020f0606 65
    0x1284800c800c2100d90041d0041d0100c1102d1030310b110b06442e90b00e131214000707a0221003c05d0b400c01003440001c880d498030b0000d502c00e04c001e00c1080c205d15203d00c41c515050742c01106460060000c641d22074141c0701042d00c0039000c00b10010807020220a265170580d8907000284a1901060515a040110b4841c0120072a0f0b4200025283c290036005071290f680c0640c0070785050f50004181c0e82d12860540001e11225605214000000f00c0060003014400b0300000d4040c5442d000f01700c03a09503180c103244a999035400034644031040c0c042807005411050300f00740100d462206155030032400092034a030070001c02c021080b1840d1502940910301c441541121903182d20010701048181c1e40404c1e0035007105d10507141342007000c9a41c0401c1200e442001d20107016032203180d500b1081c080d0701400f001d0403949180600480b98181c40c160400f54880c04030b0b980300081c820310102b40445c41c201c400c2846d407001410030400056583e503a82d00c000050183c410701503044542086201070090113030940c07000c01280c4100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 682855062 1250 682853812 682853837
    0x3090e24130605090a0b01110c0108040b042f31020d0b090c030f09060601082d0c03010f08010b06041a0d1b03060501180e0910090602120601 62
    0x6603522203401940c4a40900c0020200c0544558041409010060008522481e01a1145024000345120303540081c140c8885001c0311031022605046054059503003036400c5e1180e8403603622161000e00b094803204100b01c20407000504502000d04e602422000c003000d0f00c8603940c104911159550f000c10840d94800e10038071803054030024084011100c1c8000180c0380c422036500070300142140e01540750440c512038107004ca901d1400c000703944035451000305031080c1d90790f409440392071f454141e4085010425480110389150400712500c9100b4022a58030a00ca03100c0f030b1020240c100d001d840c0301203036800000041c090100415025009012000f009211500b03018000c00c42510540c461108010782d5824030030b202c040110100c40d09940710344401d0100300c02c1c0c0845c200d03000c0050403001d40402c2c1760500014255024a036100010b05a1012184e40c1c02c0c40d003c04c48146500061407a0124001c82c01111003c807903504c901e424840c001d290060320340c206410840c04040c1e0260059050090480014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 682856312 1250 682855062 682855111
    0x60f09241232150909071a032d01140d210305070c020a0315061715060f09060f01050c010c09030203060108060c07030f050415030905010609020903030702041e0903090e 74
    0x800f80b400e000d50710010b450b5590440c017401c08909402c0002d541c0800400c1094454101010394000c1104c100500d01c0300f454120b100c000c03407500c03041042400541800410030305c041c04c140c89507075a0001c3c01c04044c9100d1540c6005824202e022460681c0115180c2d02d201c640d81885100da02201078142040701d1000c907000682807141c07510000348014442070343d09a0303952490300103500034003c21510100075031480401e29114940b90701c010590b0404400090040c1c0b9144000c0400e41101801c18411511040244820b03004100c0480f0b050040400020441e80024071031518891001d954541580382580304050900c0c906030320a81c03603980400244002c0201460880b482940d1509024a44001c042c4041e1114040c0d9800b40503000c400c6400c0410954140c0c100d4400680b01e40020008246c403102e840c4120b0241c420708540507801480300000609060f0b11224402c0c3c1038103102c40795410b110011000369541c9103c128001000310b242084401840c0034045e400c0401d10340e1180205045580c41d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 682857562 1250 682856312 682856341
    0xf19080f15040e010b10020607080f0f0a0c0c322409010905030417060604110d020c01020933211906090204060f09241232 54
    0x380740b246588500c60200c00d8001d50190710307102d1002c0c1100001100b90b00307002c1d40362442280c4603008540b40f9400903290807402c1d0142e500c1200f03d05504e041940b203510b81c5a00070696038610105000e54270480790003243d2540e8490743e0300000710b510a103034040240c910490010500e0382102160f0300000c401400000410070342c480280c40d0800440240c3d4a03000020302511540c8400b03000f038000002e0101d8206d440c80a10464070100d18120b0795240c45c3e0340288411a4440c11071210a030a05008164400f6038540080c070280640d000003500303141050740082c00098808201c02c00f070700d07865070060b00000070340800240b01c00414101a400c010803e41c8046035280645040350180b034110001a90502e0700b52070311201c50340060400c00070f80d501c95801c40700a60040c0680b00100311040040b64150348a40c5000f429151114401c85651007460880144943d800038030005100084240420003900c0c0e10540002c1c9070604031001c01e11000119407038040c10441c056082c0383d424035040011540f1031440d17 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 682858812 1250 682857562 682857601
    0x90901090513060204032f01141b07120605090a080306060708070f0b01060e0a0302061e0405030d05041805040206090906120a0605160c03020601060f02030f19080f 72
    0x80070075540d44040d203140c004881110010092480440c0120501c100c00582680200c4404d03550511142142d05081504910000f5a80000c4190081c028985d2001011b45030201900d0b07100c83c40e201c6041c00e00303030400003680c000c2c8414405800c0d010040c80346a02405030040c4009000e444c6204540d00c03034454910000b0116801500d0014441003040011421500007a40202d05d03180d80f40c10034a850a4242d00030b2040b4400121058005040d504c0c0c56801e0b03001312079000700a9454282c58000c0c81c1c010b05450120301c00f000740280700c0010f154400b4400c0f41004c1d140c5a84107650303181060143c01030084440400c0a4561400c010000182c071000c0441d0050441181e0444180d0356402c0010903111424005d21040c0c000c3e142c240d010007660380c210902402410021003111041040304459000d021100a00142c0c410340041080d64000c40c10655282c0c2c09105a03480c2071041a030303110032a80100d200d210180000c0d03104a400710780c8419019000b200d480c0906c0b031241420810b440c1201013802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 682860062 1250 682858812 682858829
    0xc06062c1f270603080909150f120106050d120201060b0304110909072c09010207081204080909011d06030a0203100b0112090b0105120a1e06091b1a090901 68
    0x425a001465600b1440194141040040c0101c50300d03440d140070340b40c002c105510701550100d00070586041e4215100741b142c0344040c240d0100c0800d00c00800524142039465510300795a210781c02b05240d21551419101c49000b65200c648080c80003c000b42115400c0d4048500d41c14144288000900301c0c0c1012051400c085450400644034075812a0030210142d01c004c1d000c01c80d600381304001c0c00d511803416420700050500d403106039545485483c00d0b882031740d20042c5680030401c000a44e414888000756000350051500380e0403d0040800f16411a600781c003e0b49059400d55030a1030540c1d1a480540e5012109601410660300c41c2d0340425550501c0a456214070f41e01d613501c15910764455042c07074981d600199010311003c829800c1c010346850f400c1c014540102c00d001d524000801000074958002c070f600c913a580c16101c50014140110b159944021a10251102c0240010444110b02e04e40c10841210303041c00c40e14507100402206d29480c80f1084800c010a03c2520070603665a588103045031600d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 682861312 1250 682860062 682860089
    0x1050a03020d1b030c110102131512090f0c0b190f030e030d0b0117090d031a0607061416050d051810020405010905060c0d0c06062c1f 59
    0x2012002c00340071601d8000c1d00c1d42c054552180c2140da415084030001c00c8543d00d0b001c64000b001c0503140d0031b034800d03144000e003030706501442004480040c2c1c400c0180d108252030711040d401064505c41c001e4841c400001d0354004100701540051050082c20b0100405400e6521461311911b01c007070313240343c0c00c4040a070424043c1408290710628000e42001c2031800202056030303a2604003901200062043c403424900040005900c5283d0b11070040010303000b001000001c001107202820202c010340f51045003030f1900c91007018481d00d1510303402c0281a100340b0459001c10110b6000710740b04044070b0001c5c101e45200380b1460200ca02180c102c012100d408096640200d1540d44a180b4085034103114040c40340391703100b80408544a0941a40580b050710001d9035078103141c0380c6e22020014280030f030b140d000409402c904801020980504080074203244286c10219450341c2c3e41440720030b0213a03484000300902e248035603144400c00404006590084403030038840c0c03082c070041d1071a10100d40300f405a030300c039a03528 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 682862562 1250 682861312 682861327
    0x91502090310090b0f06040605031e01050f060a1413050a0e060c0901050909360607090e06040513080301090b0f0d1106070305042102040c08010810021608030903130f0501050a0302 79
    0x640e00800c8c0940400741c00c0310303282d00d803c0c1c15103020104445607046055282101107600540d0354100d5500039000104041c0a440c00c0904420140d960340d20001d0340820055050075001c0b426004142c450741540c0c4001841c1004806102e00f0060f0050655038464400c11440351503032303082030560b040200d00341e40c1d40503903585107200120181d84540300300510b00650400d108180c8956142d50b24200381f40000d61704c150311101d20943d0040303102e00038000446081ca0008400b030810790303c030b654030841c03260300f12100c00099180ca200603071080c1c004240f400c0d01c4000491241c03c3c070300a40c13400c1d580140c2d05680002060f49400003241c000102c00307441250300186400505202c0d0043e98041d00218440a40240c1d841d22407003401c03d0a900c003280035508002220768101d004603041412030f2005009404102d04940c8910001d6001d0010001c402091f280840c001c101200040c1d440780000b000156622000000b01c08120f02c00d5510042920226032820301c20390341d101c4152141510a4100961206038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 682863812 1250 682862562 682862569
    0x42007060e010f020306120703030f0503090c0d080408070509010509010918061b09080303090c0402211303030b030a050d05030a0902100c12051204021201091502090310090b0f06 78
    0x212801070049560030a44080d444a807143d0046000d082c0c119210500f200440002d01e40b50704d9148006004108080c1600d2103031800749008640c0328188030156041c402d150700000c0d4111858407c2615580c8002c102480001000c006c4a005010304a0303800281c1c2d8507040005066000501500340780d2610ba1402e03103007412442d9549091154032802c103001680f030129545540c52900680303000001e4500b500051002c0c8007004883c02011000c01500c1c0c03c0080101340b101075440949183d403034080b8840d07050540400a00b60b1801590f041c0b04003500c282c00c07410f004080d02c080080b40385c0719400a45010001410000d0b40c85d80b400d1250030415182d40d1110941d000174000720390b0181d001000c0c846680b01e1b180d0300c61002081030384543d0750101d00001000040b40da5024ac404820705100006012a015287c600385588039102030400101d002c0811755210003503500b01c12221071207190040f40412040c84d041c0922468154410001c0200300f22549860f030006101404007503503072920b00c010cc2c12648 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 682865062 1250 682863812 682863821
    0xa0807020303130b0706060509070c0201110319120b010201020a0f0e04020d0c11010c0206060d26040807090b040b0904030804061d16140109053d080604200706 70
    0x81e9210710060358581d01c0501380880e0348540822120140b502001048a24003041040d00030b01c0380d075a030580b100d076060f0300644001040380d2281c00b540c1300030700855062492402400c4bc0c0700b101507030340c0205011101030060550b0790740c00d01e0f076055900501c1680559035002540070040b40391442e11002440719035001c24020b21038811401e4503182811214600c0c950002c800c40d03100400c100003040300640b4943c0c12030f19040c095600640c004031601c049800301d960241c220004c00104110341d840746d650041f031010954400e0307201140c5504001c108001090701441a40c48252041e1010721079548407800051419200800003800c1c007442c40040380511150f50f00032a95044081c01000c08a142c4a01d9a0b507125200600e45440381140440400d10b60210110444440c0307060b1590821103007040108159417500b40b6800c20181501d021400114585403003031f4070035100d4900c4940c090406400000e240702e000920403030041d810302240e080300444e0803414410810181307040c030707407100b105103041000390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 682866312 1250 682865062 682865077
    0x20106080c1f1b0303050910060e010b091507050a1b030803190b04060308040f0b095508010e0a0215070503030f1005010801030b0c03100506070b07031d0a0807020303 73
    0xd20b407000e44003013095003641c0100d010320188400c417501c0c901208024010748200b400f5401c86546440c1c010051642010003505003904000c2034030907084001c05a180480e0404902070ba140c0d80403c0064085c0024020481c04900286c03101c0340016045441c0e485480c840904882c1085200700c00c820624410b5901040074008018428818241c1d24245003042d070b0042d0003000d5901040d12000607491440c80b0444030f00050280440d5408146106800d00e51480658411450310349001058030103041020100d1150341100c54a0640030390301d4000c0e00c01d2404541150545170300d00070540324070b09400110394016580c1140d580294004955200c1001d00aa0380c3c000c0140c400031003403040b0381d0401d68800e803040100074003950b0956a1113004480c400340c00c0c030000d0a8010313880040303652416807100031603105001301c40e084140e9a80390040780300d5500a4400b0f0742c1d084100c000788113909505008a26014208482c5007000d100d17402001a12420048801800e036000003858504644003441030340c250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 682867562 1250 682866312 682866347
    0x201090320010201050907050102072c04050706021921030f1404050c030102030f0c16020d050c01080117032205090c040801111c02090a030210020d020106080c1f 71
    0x2120100701040461621121101d4050b500300b60006000d1100010400112001603005201c000d02e089103003405c203000448200508412594512461000f601b0460300540c8144001c01040b450140020306204121040d00f403213401d01088940071601c490b403000d40d5038034042e0342c0c01d0f170440c10301d00d05800901c0c01d454181d904d107042055034070b01e030144040a940b141c0e002e4001e030743d40351101c10f08040c200e2100702c0d0b480c402d42c504c0c2c00c0407a203030600351000380c03405040c0d90301024445105500090320107003204070100c5099100a03c903180ca960310050090040c14144c8000b40054019a0020b45a0040280076040d90300700b00213041e100707103400518400811014020f00c10b1170404411010159002d8004c0103210340c06c00108400242c1100102e41c050f01458090b4050741c1e030b0807803134540030354404003c10f42d10050000d000710143c0c1c1c5010211000042c5030f0000e200343d10300840080e00759040c0740c1c00140113820141001600707454110b03a40310f03550035148600c02d440c4600d4509a074000c103061341c0303401c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 682868812 1250 682867562 682867583
    0x6110f07060e090f011a0f090402070605040311060103030e0105090102070e09061b040b03160221090f01030209100c0c0e100303090e07021203090c1e1f081302010903 73
    0x1e500e0780103410100340c1e03401902c030303c00343d40d503080541201c0050030300c2104882c2d001c110069a2198595010303056616141c1d5900740341c03217007120009061340c100090540300d0075600e03000d1008054000450b0b160340500a800750015625648001c0c100b50032101c009030600200203402c001ca68428847e81020f80b8900701c12041c00d0800e1500a940d5100450b00d040c0c40812000e0002c4011120506031011900c00b02e01680c615501e9005050710403090b010344009504c10309015050041a60350403805285441860985031810001040070020005500605052041001c04a07a4485208050b8090007505004d5001851481d1100c035502c0250300907480485401c081c050001c85201d8660100c070300a5039500c2c1c1403034651049690301e1030252580300160380042d030300e0395803512000c0c05980e0046600c410ba0300e1258098022410380e14554850232502400c800d0741440e10721304600b8006442100c0c4084259203030000002a05261001c2c0080106070811a049011a84141021406103510804121 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 682870062 1250 682868812 682868819
    0x203150a0807030b07050c0d260a051f080606040e0309030d0c112e030f0e010f18031d210606040b011b1709030114041205030c0406110f07 61
    0x75212841070208136a005500b9021803980e81c403e0040d9901500d0f40d0703010b445403041c5c01c00c055440c0c0301c0c950b141c1d2840240e20098800400c11040c803244c0b15140b004800b0506250001c420382c899110303105107003804849078000f801000740000d0416488181500c0008001003440862451802038100703147e418480c02c41d039100030030361080b064048113104910700d050048000c4d0410110032446541c8603004600c50a0f007a070382845c81280149448103d080000e003130f2091031280c1e4152400e40c0c00307151f030f640c0d1550305242000c00c070391045907031011000180782e008032000d680050200409c5100401d0030329180000a025030b884101104420039084c0344030000e00c0007101282c0c1ca40204591580c8075501e05490310046500422410b0b0402440c13020000b6440000d5a0703500703084284c9070104004502c24050608a41c400744100740040001100700d200d945400e01d0030a200000c880e02c1441000b6040c818003901c3c4450a05032410740388203050030360004915100451400c3c0080140180c180304051000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 682871312 1250 682870062 682870079
    0x1030c12020c19230316120306080111040315110406050703110d12051501020c0105180310050f130309050d030507151a030105220c03061a011b0b0601030203150a 71
    0x4560983e4130352001203c0030f0005156070313140c2c0115401403078444400041c480008011001c1060111000e080000e003280d00d40c41710f542112400900c0e500c0c101c1c00003d013401804940034001e0785007041c901c42484910407101032030066008511581d028000040741c0c4000301030040359081050034000080b500003043c3ca05008115115a02425400c2c0345420042000c2501d480c0001003031082c183c0080c1000d00300f03e001100c5030b911001d5109a03d544640307440784599014480c2049440c104800403c83d070403c1c018003221a02d01402e02c1e001711000004141c0000c1c1c002e400f54003290000ca03941180e840560600751002d102e0404000c1c401907500e4502d0340f10394101d6008a007801103070743c400113004038114241800c80340180d070305400710780041c0c04d00d14013440d107001c4510315140300d03906082c216a940d64401060b00d090314024131050700041d0281009507401856507116010000c4c0d0301520811540301c2c5000000c010f06003504150700000040c0202c41030425800500c8009400c0403a09070343c030b4010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 682872562 1250 682871312 682871333
    0x4021c150e030322050706081012110f0108220314071506120816050a05120307030522060506041b050c07320415120c0501030c12020c19 60
    0x810000180001e400203040886903001065840b0009100d514105082565240802414809040c00444000c14ad90300c0c2d500c04070f11858400d10351410400202e07410080c0303d43c4902e00650400c0103030004c10540e40c90030031055088000303426581c0c41c811a181803c4035000703240c509d42c0848030f000182c040104003008000014045c41180c1c10001252541000607101e0315544000d00700034130a12001070656130005812680c1e170300c1042114002c031159030b122420b14010301e8100446c0c0e4004030802c20b103c2e40500a855109258043c000005414490000e0001c48100d4000c1d101c1a613036800210070ba20385600c408540101e0400450302c48035802d10003172640c2c0c0011840e80940c002e40400291601031001560b2901d0959000c00014912652001241d4003007041403c0c0d00a885400c1940101c07944801d24000d0300c4032150406004165003801c060020b02948120704140c40d00303140361285680041c4085c004070100c9070241e91843c007100941d0ad0003401c200b05e1603452091240c0c800401085004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 682873812 1250 682872562 682872571
    0x3031e0e150a06080307080d0225050111040b0340200f090403020102090a0b07050d1d0f0a1a0c06090a0807080319090308070210020304021c150e0303 66
    0x35259010ba0340c41d0540b00c01c0d01d034548a0403030303254000e000074000600b0f400041c2c8a8814600350050a01b424242804401d03005521030100900300706112209100f400c0c000d4105401d008403080d880c0c10724010b070104540c030004000c1004c0a001c0d4001c040e03e10b81c80d000e21b071490100d551214401c26944450341500c209007034421640c000301003092004404140c041d4100841c3d005002d140034810035028407148410082c4100c003155420011030001e940c07412504000340c550000c403c2d841e440344c1d183c81172408010074028424048a03415100b00310216a04042d0004030682d0b08102e03422850001c035140c00d546804c040b04220b000c0e440c000504002d88041c018840d070900c00c84000c2d0302e4010b440340d02c40242040242807038030108010408140344800540e00103100b00c90411900483c00e10300021245054030032000290504140701140d50704000c90414600c1c94441140381d03080541c0007800d000512441c0c0603440c40354101400034400a4000c001c0c1d01d5860400c20f00c0326000d4407480548a034401c40c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 682875062 1250 682873812 682873843
    0x30f0d09060201050c0a03270507052b02060d0608010f0b09180304061d04140f010f180e120403030201200307200c19030b01170a03031e0e 61
    0x160001d0300a01c140107543c0540d0014960901d401507110044024002d40000c880b613070108840d80c0e24260311484404081c46000e03101605807141001d081010070000201d108850060340f803544010402401c400400c0c91f641107030030a030359060681c1d40c00068041a0f00241940d4600411900401e070380d43c1202c404050300f203030001300550303d4003000301691340803a00081c1107500500040c003d0300e001e6541000f119050143c0c81446101150000d8140c0302042c803511480d04034a41402405000c5010490140420340500d041103410913140c042402500b510032180702c0c2d121141465100400e02007128100c0c0080c07016540c4940304d04002c1e001c1e2205982c80340d00e800c4240c030340750071040c0c803881981d010340300b50740e00e24205ea01d0140f14402240030001007007209024800203070206560748101d52418400c003031601c12019255050540d1000b80590081c0884c1c1044610031501071008031341c211429034075050025048030036002d66001d0035499002d500c1850320300b403119401000002441b41103200001d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 682876312 1250 682875062 682875077
    0xc22060501022a04110a120c0509060d15030b0c030403090b0a0804060e0c04290402040f05100c0203070906090e0c030d0e0d150507111902120c030f0d 66
    0x1031004a80e1020700071110310002100410307100620310315110944464400400204800f9000400ba004981c0541c584c0804180711038400d40f00e03c18503000b9a1510099401c2c090304000b0103070041011445420564200c080e51510044000503030758009001440d042459080c56240c0850039441a500c00c6e1416400700f03001c0e071400500b11400344103c0e4512100c5940d1814242c80d19a0384601824480899904a014440c9007400907152442001c00c0c00010000c040c0111413200c0e500c41681c0240c40d441e80c040d40c01048284195040d0300400021201706840f80c0c8440104034608488203599410020b6142c01040d5000481c0102a0002030564000c8081000350403000c203665981d8501322600c03160107400025904021f44d01072000008100c2000d003064182c3c4200307585000740f0b0b558410000c61665500c005208209074860405121008403c0080c0b0240d01c5030b0f4041c49249200540091245040403000300c080f03c0d0601110b0030221016040354000c000717000000b42c488050010110014002d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 682877562 1250 682876312 682876319
    0x1060f0314060a021e030403021f0218010206010503211e090109050402120f2827050c1c0605070c020f10050708070602070507080d03052401110c2206 66
    0x3d8401c032207061000316150000440e074008204030541000340244c040d400b0700c00b00c01d983c80e01540603e8005d900c06010060380e03030042050944050010300c0f81641190302c40b6006014903100010781c0442c03400d460f40792004e03252081e21500e00034880c80710a8100e4120108851110400b007402500600c4000d80b9501c43d4207440d00d00740702c00ca00441d031040c4030795070843c00030454502544090b560001c240d0020222009850100d41104542e00704001401c1c0340d490210030085400040484003101d51204040c40d0054591201c956650786554082d104e5030000e824450310b002440411040c956010340d05001615100001402c1204480340580c041c0c2e01030313090784c400303882d10303001003412840a80c40e818281680c9860b0440c003030704002c0c01101c4895003044041e02244080142400a01d4844001e010806075100020103072680034000c0f5080307030200b000203080e80000c0d07500b072620000300386010704c0f01401c08628141b400201c000c2d07054000c421a00160b51114815035140854440424240f12403640c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 682878812 1250 682877562 682877581
    0x90e0c0910030507030b0409080c0d030b01170702031306030f0e0c0d11062a12130506071b0b0d0e190b04081c0c030b03070303091701060f031406 64
    0x142104981d0702108000321611050300981c040394000545240002da060034207008102102d41401c819200c13200c2c08280344040d00c0c030800c41594003132a0791a0038049509024006072115011166860400d00088005000c41c0d01c03c2090f0740040441c103207285443d41d07482c28040c0051450400034038509040c031114942c4220000b880c0302c140074015028031fa415100e501d50710b2603144040c0600d607001c0001c2118132500080c01c002c5984000011030324000000071a18910315161000780d030b0001440c4203201159180c1038524041381100c200303582c015911141c900d045e415081d40030b41e2146c0018000d1340040303040c8a03a00054072a40c014001c04100305200000c4c0e85960750340001c094000007814130903001c0043d042e55006508a40705503a4542070070700244030074110101c0d200076408035507924069400c866a160144299510054000d041c9290564038000c05c41065030140044044035030905c0e114008007513201600400b09a2200781036282c5078546045900044010b07032440f8450380f80411050300c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 682880062 1250 682878812 682878817
    0x9030308010b0d06030804060e09130b0f061906030c020c041505010f020a050109110f060a02060c0906130e06011e020d120608190507080a0209040f0c080a03090e0c 72
    0xa4054a032000540e2078085141c031107600001481d40d0090b01d40b070000001503032080140028003800d4546440d50300d02d41040c4000c2040041000003000009005613020402a240c9190002c040004001e200d42e1400046034000303225403044400707685604400a1a654903170300c80340c04095541d003601c8007030039120300308030950700c5002c05200d00100c9080200301075030107142c20802c00360560041d907040703218a44440e130171103023100801d4800300005041d030486860070707006000e0344103401c40302c0394200010314000a546a4000b071061402060004030708540b59a00030070b0703420000340300148402c1d4a81318000c0000c548401e0300c03c0c50110f880182502c060303902c035900454500c5040e600508a51400c02c0c421908101c0b40d500b102c0c0307995924940420041024403000781e0740e2840103800d11802e04103281261a00a0320350182e450b54010300f0360040141c6d114500300e50050341001c0c41e00c1d100c242d581040c0c4010317003595000786014828105450201908003040303404844c0c142466511540c0c0705121989a031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 682881312 1250 682880062 682880069
    0xe060d06090b10051206011806050301090c0302042d0801091a06041b080a1425030605060702010513080304080d1b02010507030c150e0106030c1401050f0307230a0f09 73
    0x754080c00000041020780940710f81c01b03801450854111042d004510800201942210000643c0000140001e9815000d07140c4411664030313045280a24150581c911701e40d15010000d0b565034402c05c005c0000c0b8800700d00e800071f0490000208020310007454224a00c0c1030b9003026400c4182d5540014809140c54032500c581c04170030301c2d040c040940c06203508441d41c0d60010048040cbd01c5d900d1685215a40000303003014443c02d003c1d6440380f2841301c6a02c40800c10110603490104040c1440d81c1480240c41c2c00f000d44400980c282400303519500c4040c0300c0342c40580103420800403031001003000280004001031006020045858041c04650080c04121442440c604080e0119000700310380e40c0020320403440d401c401c601800c07044a001e202e10312818261f40544d1803440703c0c0ea448650a20910101800c034000400410f803030458107645050007c0c20074090601c1080c2180c0011001820440c040d420030700e00300d140220401071049444210503040c1d000300090000045001c0c00c0301c50054080c070b2540e400d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 682882562 1250 682881312 682881317
    0xb090d1b090506331603030e161505070303020408030703020c01080a0b0607030c02030109051b040c0305060a0620010c09090605060702010e210303010902071101080114100e060d06090b10 82
    0x114825010229140016424150503082c080044643c81741142c0c0c0640000352099902088000c02185001c3c80c0103002d49061111180701c13003080090003c589584800340320542080c540b07038807840c2801c1e0000c0c0100d0384090a0f40c040010b01004040d030103e03400c2c40d800c100740ca8808051715803a41542c100d6080e44503694002c10100030180101f4041c0c4010f500061009001241080c1300e0343d80d0500381408034501040c0c00241c129003101510f014014106201c2052a08000902d003050001e000c480c5984030b09814040031202004013140ca91544949031900180280712007004640d008000004a00c1070540640c90940c002c104d625100d41101ca18980503900ca000300d25002080141c060301d64910040d41c90414044a40c40b040c1c14000341d4000c01c280c0000588500407030400f0314114000004079810052601c0c018090102c140480c03000c001c40549082e041b04411407000e9911b100b00d081555803190300441c0940d0740c4040303900319200341c0e142c205080c0810700400050058044510b00d60102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 682883812 1250 682882562 682882609
    0x30503070206030a02071401050711030a0e10021614130207030c0b101502060603010e0c060a23072003060606120c2808100b03010b090d1b090506 64
    0x1600c0d02c00041c58101c82440d03001031403e00c031961042207400060162200c1c07030b5141c00c2000003d540107100300c0320002e140c002461a0420080c0f00074120305100201d1846040107542d1140543c0c0700700078492000c100b01ea62804240e8540c06d02c010380d81500301e1274611070070202c2c0e00c141030400a4003d4400c003d905071161010040c240e59a134140ea00700515090003143d102c0000114212543c20400300d0900c40c1d00540400e0400005050940f080702903407500c20340c0b100200c03103542e440703c1c000c4883e0401c0c140381c4503280ca41c2040707130783c820400b060310000c54031400841c011081c0259042c00d6668007a8038086036001c0440407080c1a00c4105c102d0b030850f409a014802403d003004a01e5020354440440c145152900c80e100031034502410b1500c12800b031011980c1c020014440e0401c800e150400310612030400450324140c1c1440b081d101c14040c6440ba03110200e540355240c0c42d101d00c100d490720f6002403142c60882020007081c100f0030041c03003410b0f041d45c1868003164260030440c16003014070110301810030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 682885062 1250 682883812 682883827
    0x1403030a09060e01020109020301050106120501231923010f180b071505041a09030316052101061206050a0f050910120602090108060f090103060510030b0103151104030503 75
    0x1070b0310455103070155045d03540700d604003c010303682813048030f010700001e813541c1040c511043c18540803910142c00117039910404001e541d94180b0341c514128070342c60045840c8188580d5445908070100c00070f9001d040c605100311401c01661a01c804844002102aa02c003860300403000401c849030001d880f07030350520340c0884a0038001c0404000c020440180200d5103902900d00048101044070380858041d1341a6174a041003a03110407000b503850b60042c042c10025415420011201c0900e5020445080103012000071000300399102d0200341241c80f04481e014004640e9140c0d4040c004030012340d0325807d243e240490103d204e00d44005c216064aaa40d0901e02403039050405004c0c81110141007030040200b540000500c2003041880340c4080d03440f0740802740e207600707208001600404000e0402031084107416212107060321010300785811a03811080200741516011088801c0160030341015200303070700e01e90005c0144042d14098440d0145420780410901c41d0b45070131f07201d03503010b24000181550820007010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 682886312 1250 682885062 682885067
    0x1106120408090102070e100614040b0a0e0f06030a09110312032403030307260f04060f021606063605070905100e01080f0c0a03050a1b091403030a0906 66
    0x7090050010300484203020780310a80f01440c6c0344104c0b006824101e900806004d11580108035022414401c0012400c00303007028204416400b41401141c100100808105681e545d24498070100803405400c1075520f0400242401c06405081303000d0b100c1050740c01c01c0e00d0740340c140007c84003140e4880791b00040c1991201c0010f0030007a02c0142c109c038610b9101110031105650709000450082c03a2075200c60b041c040048446903482c0740211a58110484004104050780500750607407540254449000500c00a00100744030081c041c4160402d1441c0d4542d00d03043c10410940e00c0380701660300d0101e103503840003c800701c4541c400c070b0002143e08140300c1c05022280c44103050340003144c00010034209118072075100c03400703e00c040c4911802c0758001200354015620a58204251300d400401d105004040c0b0700d016550964144910a88682059560800684002e00320303408440303400e28442d05000c6884404800030022100741c02030000300e51511102c01624580001290000da000d515a0702e00c880c6811801d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 682887562 1250 682886312 682886317
    0x80f060307150e060d1409070e0105010f03020715020f1201080d020a020d1a0403080f0a111602040906091b0803030f161205040c061b05100209130e03071106120408 72
    0xd168100d1020f00071408176600601072451407940a00c407441051428011461138000158407400a03960130700c0c010b00c65640c2c8004245101212400c0140c6c0e552040d140403842100c03480c0307910441920100d0b41c6480c0e5a00e50f0000c01c001c09a0b44c003041d0b40ca98850175481d80305c210b1002d4503c0581e000044000042c2030005e170002d9094001c1c2802020061000d010003e01072080760101e000032400c1c4104080701400d10074841d00641c1103081008490550248984580701c1d05140304a030b150b84a29100841d9190b4000300a01c45c0d211000703000d0298030f858034034800a03814913031220b50301c040302c0081140c03500082034901c1081402e5010349903407204001c18102c1c030b000000000411954a44006400c00c641c042d40c0d024520030455442002e140c017070010840500e00b070f20302c80800340322201e48021072070004007440440d011400040e624200c880003d020000305135038031710089040104403541c0103c08400b82c03a40300c0c01800f4003e01c41c824803082000c50301c15035464066401070702000c9404a20303803401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 682888812 1250 682887562 682887587
    0x40f140d11120d0f0f0c02150d0f0e01060f0506030705190507020303070f02030c0312270d0b07080709080a0605190212251713060903080f06030715 65
    0x915000d84204121aa091103040d0f030020300441c401c244441003080d0b0045c480c2054010070718000c4c4040c2119400520442c15140d845118000f010400c9661058039902108885102040c104080c508a41d41070b8041c05491013480b02c81108140d0000351420039030101c9114034119034400d1b01e809a0b03a00007825031802000020200701d014461280141c83c1000188031040c00b0755600385454481d8030401d880c0c9981c95110500940041c84490507402e04903003a02e1010089141e9080c44004045071541d00d000e816080c5540500c40c0c1c1555824003100c581c9c035500034012640d07104c120f5914107170180e4081c0303c44d2260141c0d0b42c0c13160600002049036075000e079400c01120500708008080c40c11009041c0c3c0c2180818600f20b1801e2014006411800e00c01003c6000c000380b1a66004004803802600140c804040300d20000300c6400014003803128035005003107a41d4048000c000c7c4541609008086803000c0309c144074001084008034000385000940304d030403102e03606440701d2000380608040f0f64001c5d4040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 682890062 1250 682888812 682888819
    0xb04051e03070f1b0b1c06140d06090209070c0606060e06040e0912031609050904050606150408160e090c13090201050f03012903041a0606070512040f140d11 69
    0x8003194130280d08011400d00604540a0710781e112042002401c08040f900501a201c1500c0c001c01040b1130704a40e083d00002c80012280402c1036071841c1081c201800c40c54800030340c403208800401004d250840f0319181c0d0503000e107008014880e1141425a045045d0141079680404103000402110061a00607a40501120306036200c95400c0700c00200700d50015a003a010040b60700142c2c0c0c9140e43d000604a0050108540c1960203043c2500e8882e00c03840c000d04810b006804140c000e00b0f80c0005901280c0003024a40c0c00c40d41814030346015152902e001c1d0080c010384211100110702c940d8030014074444807040c01480308507604080c0c580c42009041641040b4140003062001c0d00020000c4009140203040762039510707a44034000d009040b0000d00c80c0341801c450030340034402d001c081201000060080d0060711281c540c0ca403145000101140980040246544195183c014102c0c5440c00a08210780d00c86001d20303056a00e17100b800c00c110107072403051504202c160a031240856030f134101c40c04001d80090f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 682891312 1250 682890062 682890083
    0x20724110106030c05032103180304120821090d030b040f0e06090d05030108030313150e1507020f15060402090a0303050307170105130f060906030b04051e03070f 71
    0x100354142503a5081d80160b5400b90707049810030103414140800f40700602082c0c02419003500b410074402203030101404502c0c001e040b449a00c504050100100c801600c0c0b8242c29001c03d000519100f050750380454030001002000710341d0910b20160a1840d00d008001c10740150801e0020008114000c003444406140d200303440701e09848400885218030081d051284020341050300d00891058682255401d0350800c0040802c01000300000200a403504004040b005400d18002070416505030440d081d0800361680c43c22491440c00180050360101a10022840400d99503c20209980310440b03000040220341140e02a5180b4003941840e0680c40b20004000606103a0744101140e20600b140c1c0040740807803030003c1448001074110740d0071801004070200c130340c4003581001c01259015021b258920480c039102c41606601c03100741d410400140100344002c000b215620706001c0403a08040e00d003035501e40035009042242c8a00f00c2000310842c02500001c3d86132290b42e03a1003e40c002d400c0b04c420703038105625 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 682892562 1250 682891312 682891337
    0x3030f09012409060b07021503042603180609070311281404020a0c0609031e02030d0e010204080601030b2e05010f020d0e010c02040b0d0f050d020724 66
    0x546500540414407500b20420b21424a640ca80071607500b80c018400030301090100c0001603480c0c2c2c04580c2000e11040744942c981d20760b46085403030a40c030030441882c8091000140010644400044e6100310070300c0e20300b8044444c44105140d02d0707000c00d40e10760010ba000345c401407012500f60080100300308406810503000000c0040c0300722000075070300f484401c0750800705001c0110707401200402007410710849c0c0443c40d0210515014003420000d550051507203840c0c6414509150140111851900d00d032494401c001c0310000c030080d20f95202d819211a200e25252540032122814400d0764150b0b0100c000a00310780c0d080d500d403400000c60060100500c41d042c24001d6100d95212a241002400300c00861800c1c0e50400c00058024048080840d04644c41060340442c0302e50301c2400207803000c00070300303003e8102203a500103c0c000d0221039510b5500040086540e504000c0600740300300307440d40030740142da1303c0c0c03007220800700c2e121081c92080312a89603411090f1603000105108002c542c124a0401c030070003000c1e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 682893812 1250 682892562 682892591
    0x121505090a09150c1707020316150e0a081c05090a02010c080c03120106110f1b031e0706110a0c0b13230301050703020906190905030703060501031208060303030f0901 73
    0xd8082e4140d0002d0b03003640c00091401041d40105411441b14009582003c42c540b1f1485001c03514070f20050030b41300810700f142c8032100103507002906c442c0e03207042950760514907814405210713032140d0801d084e41c030000ca208401290b000c0c4a09801040d2500241c14038031056001194410f04031482981c0c0260108005003c54504100a140200034406040c68543c98031401402d10310701000c05843d65040b41c6181e884061022036451032144510554510100c00000400e242625242c031074072407070000b41302440d149440092484c0441e40a0740e60600d64417202045541c0b19021140c004202e074460003400d019150402c40034041d20480c112460b18160799582480190881040288428011066440342607060a024065005801d4103040d0700d0b0888036808100c0d6446031103010704c3c9010b5482a2403c0c3c2038030030020b22000388401011100ca2980740e041800c01041d0a100446450401c00c085003c0d0324060740d0103500c80c0c20010083d50039036131512030072000c810b8010030010316556120590420b141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 682895062 1250 682893812 682893821
    0x409080f040e06130e15100f0e10080d0f1407080f0903060a0b0109050105030c07240e0a02010503040807060905060a090312060f030206220303121505090a0915 70
    0x140150051402d00f001c1043c841080505185514580e082081e080310350f50000500e04403044244e84495010340e40c0801909903000c59402130211070050510000b003c0036500c01c0c942c0102d080902e070344040c5580728042650b40d141071591304003040e000500c2d12100b9000d0001034490300390400c100d61415415a452014951000740441c1483c0004544010b050804021483d4440d07205401082200403040010301240036510840d410006c00000050704003030800280c54016a1181c03250801d01c3e040704440510009609480c1c10552609002c3c480d11000002c8948c0625010f0b110145562100c4e221071035250700148080c1c40d8192200c0500300080c0080007598440d038540b1400044500031441c0090540910340304075084035007004414020200c071105a20101c0740c0c1100c041d0b5441c00390f4000c0300580c1a0f114580381d000505141c00006050b01b0500d030307020155000808219520000c0900808240e02d4020140c20940b1500068036200709503025180d01405404c250011032182040041500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 682896312 1250 682895062 682895069
    0x120a0b0a0e07060804151e020c0a02060307111903050d0c11070f0f080307020f060306010c060c0e0108010e0f15060408071e0503060106050d0c0e0907110c040e07050409080f04 77
    0x2050042040281320044403010203111041e01c040c006440c1d4162040b103500c1c9107c00d5040c07082c1e4001600c541d120820400e84d1451503014015030748a20b01544045c10308a165141c03c2d00e24040c0c0915034403264414100c13030050b80d0703041c0c5071103060200e0343c0044001444500c081c0c209103c1e0000c1c90540d45002000741d000108140d0842c665901d0400414483d103201c6a4480c0503242c0c01071121f40010f0f91031000f43d1020030001e483c1c840c2c0301d076140e0700100c3d2500429074014058520300207805040e503600042554880c04e080e04c43c9100340c0da0314002c1c03020200017101c0f20030784d015403000444c43d403054680311642d1004008194034203140e105c9100c24105030303040c1d116250300c40d46c103250140070942802c2448003c0c132044000e4103096141c09800b8001e4400c0443c01d12940780d0b03450038030940d10b02800500f19090000350480c40146420507024102c14030004a40c58584500c114048913482c042c029112a100380388007606000c1c0c5482c0c1880040c00d070450040361014000c0c4081c0b1905080c10002d48000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 682897562 1250 682896312 682896317
    0x40302090a05010504061409010e070c020913060b0901031a07020304092a050403050d0e030709020f2d04030623130614060616020307170102040602010b120a0b0a0e0706 74
    0x41d0b52600d0204000c41b1002c0e4482c0f40a0010b0441c02ea05e035070344218010b4112003a86508142d65540d444044034290105d00d0000d5000945409000c03050869812000609120714001c1101c84465003c01506550900c0010041110034000104100e405c0b1400d80c2c00a0082c0122804d00b03450320345039004d407070340300403a07040c80c800413032001000c03601c8070306048040b05141c108903141c2402c40c0c550949903004c00d0708103814404100d407040c1071514204040f400030655803504544170038006901c40300503400f400300c5880c881c42c0414203200c9c1100c14014010b450389001d0300c6510f001d2035555000b0141502841c082e0500c00c510035000151040300320024810071403803660044040c0d00b031070720b20704940422450405c41c080d14401c000b081e03142e90040360791003032400380000c0070440e8a00c0040d1404600f034100100340c003810b43d00b8440c1114150003030b20507509550001e03c12504c26a09018109171035200c00c0805911011404000c2112805959001711b11140045004c068107c1c445192058980c0710000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 682898812 1250 682897562 682897571
    0x507031a13030f1e0e13060f0506130b0f03180c01020d0e0a1203020c0102070e0c1e090409081812031206030f030a201614211c08040309090908040302090a 68
    0x5c90b1603e03500310104414588810040b560070040301081c44801402410b0040b1800945804002494401e000040c03c43c4520283d480038040a2441250004e0b20745103100848141814a01e1f040801e025549540690082550429000f0209e8010f442c031401c1e1074102c05410000704200b40101010b1900d540250010096105130320300081c500340d0503070300c24031800500380188030800800500300c44080052541e51300c00c500c0c190f0b06481c013074810780540c02d0341301d85880b46a10407c00850f018003090598070a8000601c0d01010511502c41003d1010700c0050b00104044c0b0b50300c0c003014403501e030003183c060304031003041144100c19072644d440f1010709000320b07140c05203510030601c0b009001c0042c1941c10000e0200d064420000070103c1140f40603282c60542d4051002055454001d1590185040359840c043d40055942006880d908030000030820503a01030340249007680600380c454042d03941030f503c1a0001e0f140215200c01080c40c07a10807115107008010010260390313000c51032070260029400018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 682900062 1250 682898812 682898837
    0x190e0f030f15070f0c11120f0703050f0109020904080c1c08090c041b030e03310f0608041101020307060207030201020a0e0f0a09020c010b030102070507031a13030f1e 73
    0x414000d000f80141d0810900d2501c10b07013565130003880c0d10000e079800401e5100e000d03405000200c41d4400a00c03c1c1d40b1511039143d40d1034269100080c0b01c0100c0c0e0007030050b00c005200c1610840e09813281184040c0d00001c4100c08a000600e00500802c07400303001c2415100401005802d811180881315110000070f0a00c0d010f10106940911110b0003411044030104946031000d180004090405051402810740d10300401d50001e03410700071140781451a140c2d03e105288112070343c04030f105003c06001a0250400004540e041c0300351038941c295140c41e100c1c4907156986503150009a0a814004d40c1180418080c42e80000c5250000d4110305103e03800150301c820740503400500a18080d20002e1013081c080074640c84503100d00103220107842040c0009680c4d120210b44041c0981288550b00b40c1641c40020804288400420948181c80c071030a6081000344911646200d00c200681e50038121381040c1010b00d0000f401800545c650b0940d40c1402c04000180050940280700d480c412540821300f4141410b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 682901312 1250 682900062 682900093
    0x803070b0901051504051f0b0d0e07080c120114010b1903050712150305030c1e120a050d0f1d152e030f0620190e0f030f 53
    0x6036404000a0002c0001d403405614054410100840c81802a07548802144a01100e40747c52078440703410003039554046039a800d40c1d010580c800c5a8010030325213490707915010404042078048c21152103100401d00c40401600304400401c3d0300001c06070b41c0d9a201e10309488070404000d078500034580d0742c0000e40c17205d140c520b0100c0300c9440050a4810507103400c041200035a0014100714406c00c440200090401603081c0460a1404541026141e8130010505600c40c2d40c000403420040000c2c07012f0a081000f06184040e43c840d107156030b6004d40711090040744070082c41900038090300c610426021400404140100085a07001050046004020a40d80200380c00c108110036040300e01c030700b07403c81924099000e10340c1640d541c00c880c002d080740b0301d803104610404640d04c0350155400200d0452509024541000100801c0a0508180317144903aa104183c1e401810390b0340591910102c00c100c04548201100c0768100918155407200d088010035010303803420020b07003508480d51001014210b041c04440d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 682902562 1250 682901312 682901333
    0x1a0f011b060608100c020f0d080c0706110c0c0102190204050c04120f050c0612011802120a15050a06050d0c180e060f0f030703060905011407081008060c12150406080307 74
    0x13900b00f5035224407015034105000103208c0312681013501d8005902d0300c420b54042203501c0380701c0001e0203040c00c0c005020064502c03400148401c2d24200c00310746619002500581e151000d680e40132030000d0004549801600b8030340c01a9038815000c2031443e1502d51a100c108854201010055a100007144401c4081140404c900b603151030702228040d041c1301441c0555408008140a04030b50840c04601040b59111a030701a180228503204503082c117441c00320141e2000304103402d80080c0780707800c1060000e59800c00c42130f01c4058410341d035503c07460f01c8000765480c4090240703141c7e071700104800440103424038040079101c00302902032108003c00904144040002c803d07808081284611030300d440080495a00050480c202c079032220001c222444141800b074014000f903500c2d04a1103030b000d81000007c56111110030301c1020390b2a540302040c1d841da0001d99030740c1d4040301c0e04031160004109215940b505410a240d00c5007003040400401100c00c00407909580c0c80e58000360b0150b0012031540c0c07c00491450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 682903812 1250 682902562 682902581
    0x3060603021c020d200c0c091b0901140a170a0b010207060809030d0501090b01021009020609010c1112031e09030a03031a040504151a0f011b06060810 66
    0xd003581004100007640141c02d1803100c404400d01d034002030a4880c610f45800c080000c1161250032140c030300700140b9103c007950040001d0b103482e00882c4001d41140c50810362041c080c1c070241c0c503086043c1c49220782941c0e0682c49110010f05200c9203225a20116400c8002401c04003029964443c4094413029018070705040504000c07200740c00c3c9007080000781d80c0084c2c01811640c04e0703d08203509448001005045104d42da90030519181002c0011492ba41140c01140d5012000e038229040c814103640101c0840d003000b10004c0d4003202c200100f035219849000b1031a5818091101c01d01d144501c0d1001516404c00715840210a40021800b6203a0103083d0b40b0745400c551240300c0103071074410b903500001e45614100c9c8004090503035508018005582d50b6166081495000d4000c00c49401c1c50309000d8440300c00c42404c00310f07090406040c500c04441d5010f0800401c10b010303200c038910090304001034400b1045560906040382d8030104020100f0101d0140f8002408600c002e08210402e6608070f0064410540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 682905062 1250 682903812 682903817
    0x906060b0c07061b03084302010504020d120905040207050607020c010c0c09020a1b140706090302030a02100339030c050315010e2701120804030b0915090d030606 71
    0x10324641341c0c2844101288401645864405025078400030352045003170700d485e60121185030a0040b00c002e407400044a02032002a081407204210002004a00342c8400b1039000b90400c0c01c803000800090500c0c0881030044845081031161640c6500204049800c040020380b9594894030502a01030f40610440310100e900380303846905440d40d602c4500d41c00c0010701c0340740440e035800107211040306d00c1219203c0701d8040404108001092905141c20540081a88002c0740d003d44000022030718014106601201d034041e0142800b104c05070200032161001850344e009141c0c41d010340c2c6110141803040c017940c00500007126042d1840385024801151409181c1d0400c1c50702d402d4200d03080300c1d000420b0781d5008114070072030781e50042c0c101c1c01290b41040550901e0381141500d000c8524011160031049000030b02c40704040226030341e556003a10302066580c4041c01a8008000920114520070251540501e0b8001200c1605040320030b2640d4201d0b0440b40c0d198242c010203c8422100c0d410f01a102c0104101d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 682906312 1250 682905062 682905077
    0x15031e330603010204230102011d0f0610060f0c0519080403030f1b0b13081801030515010e09070c0b0c040501020c011713021203030109050907090c080a0b040906060b0c0706 76
    0x10b074000d0800b406858a28140f03944d00c0b1044000c44c8e00c04d400031080084032408008040300301c8541e4680da06440c442e08183c1d40102e500060300810304040361411100316641e0305569036240d040903a040c525040b010b5456001d0742202c2107455150303210901c0811307c100070a5540d140341d81002004007020f910184200300741c005141c201ea4600e526010419038120f186081c25450320704030005801e120100040000c3e4002c18496041c01c1d0b0403142d8455020280c03020f02207507542c050b081140041105480b0b020507102c0e0201d010a0170f000500e56030249544c01d020700c10503d0790b200c0d01c0000808481c40c440041d00000c0074021542e041c40b645081130400e0804200700d40d1540300940008000070b1a1341ca00d010440f2101040d541c401e06564079514001c0d066070707503030758541e141d501c060213003142c4e060014450500005a5442c061082528010850f46c0e903034415102c1012400c041c0585c664440e6000e9156040100820010b03c103071b0300108210201c1980c1c03003699013034080c10841103a0041c014020700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 682907562 1250 682906312 682906319
    0xd0c020312160917010b0310050610080903070b0705070f120e18070e18090105070806060c1009080d02030f07180302060906030a140c030f15031e330603010204 70
    0x40300d542415644c03207044e40181d00000846280c010861111607690610402064136003000c1c660340b10390f004140503243d0310031b00307900c0f2035060765012000c6d2400090380e402040040c0100d501c02440540282c51460018038000b070310f884030410226040c07030580c1e01800c03002401c50115080000b040c14404242c0351002d0078440c0325200c18481000600c0c0b54184403c2c88400003d035034418050203890124202c6c29100b03410701d101c005000f010304503030580c04213240202103589403920000741e580c02e500b1040105255081503011401801c10804112a442c0d4140034400c40e80c042c0740061403090700e1001442a10785000000242945c2039030060f0144184143c00030710242e02c2d100d003100c42c860002e4448a5480d01c2d1412480000c1c00c982c0b13440c015000054007400122036062000310300800c000031602080392030b4460314814214080c5030803030b41b43e031148408040500d40403201680c0b1801c54015100c90045c4400c141c002c02c0e0486008150402c0c0d04401020704030f40032003995401030030550003182020700303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 682908812 1250 682907562 682907567
    0x80c070219050a031406070e0a1205150106120b120309091509090604050c0a05011e030e03130501020709020a0f08100815160f0801090903050d0c02031216 68
    0x52004080d001d1004104840142030408050900070b103000f4100f00d0b41c55a49041c010100000c511000780940580000300b03a5191150301119550b54000b804c14060500c1c00f00360804002e05060102d80358021004483e0917898071b0380d01d050082040e621114205030301000106c086070420540c0c2c0d4850300f0305007000c40f00e640000007502c1801c1c0042d900d60030140c81d40003060310502254443c045d4000b80602c1004100003010036600d0041d48500d04980000341620100601c00c101c2e0700505002a00c80d2034015404102600744140f8095582000035130480c0c4e94a0080c01d65100e07126041c82c00b618504100f0540d607041044c240180205074045041143d240c500406075a140d180380c0c4201300004000c105280301c6100030350300070001501146d45d843d100d0008540343c3d9030100d4000951020520b509103801c0c1c05076031920b5242a107580d03108030341d0f802c060b640300c020319105d202074041020600404012070003520a54400c0c0c0e80300d800854990040414000380044000e08190141901e0078002a01b540c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 682910062 1250 682908812 682908817
    0x5030c09072307060c0504050102120403240f060e100504020c030405090c13030501140c0306090103060519061e29091813050d09030b180703020d03081501080c 70
    0x24103015403078140311006900e42e0b402000310142c403d901c0c103100c4901c030360f03005402001110020780a64604070078860440310b45010364800504900345000c001031041410051101a031070003124002a8082091443c004851158012800d140c00b0402400700c9001e144044400601d42142c05614062560041d16160b00403889241e000d611100b01050765407196400b501c488200f0000744520716075681c146140640440700085040003200404103503210240b00c102c80c452074003d8400d5086910b190380e4480104401400304085c0c50070001d019030840443c0c0201c10040c60161004001800b15425500c1100c01d1903020380703c4454001e5031202d0380503000b161280340e10f800c01c034869200d204e80c1c0d01180d45070490702c1000d15040c40c60f000b044104030307001d140840e2a60282c2e00304d0f211300c4941c12043c0c0310110240000360241d407400001540d5021501a500c505030b403481c00740c0c3d611270b030340c0e6002c5440ca5641c040b08a0109000c074040100304503440c0d0305103911000904e00040c0d07a083c24894000e491 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 682911312 1250 682910062 682910087
    0x309011d0333100506190302090612011401020a0f11060403080a111c200a0c030b0708090a110904110a06030f050a2007240605030c0907 60
    0x1560004100036640c0c20311a800e4030504a9038101c81040201401d4042e820585a500d440702502501003403445205003000c505442000d04040c3c946009861117090351119010840200341d020000755855842e03e10280c6068001441c2400c000d5062820b100d504680701240c141c1154402e000276800b01e0000901443e08503003103225074400044140106042d40300b503400103000e480c130008031410f000741d01c2100d400d104200038054403840c400d03172000c1444000044096038001081a01810012288400c80100143e0f81ca030440c0c418100d180d5805042805950068584501c04000c001c0a250084000c99012001d0303000740c0110340c00340c3d0384c040b014110110b203607000d10501030002d8104210900c0507401c11034001c206151050382c4000003070160041d802200c6c02c4a00b8900072845c3e0074102d001c2ea1125440d6019900b03031103c241c80030307a03400f5040844c00f030390070300c40a1040e0300e0084500d83c0d09500f0b01c1c0101401295043c01c14091529103425102c1c69401064000100a2007690008a00f0480e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 682912562 1250 682911312 682911347
    0x31205090a08071103060403091511070b09010306170313090b01050301060c1509051f050c0f0f0d05010b1b060405120a090f080f01110711090601030f1b11030901 71
    0xf2501941403880e901010700d4010342c0c052003400140700c141904400303200120784a0304914811f4407a001c1c000c132220407030301d80c07940003da000c8002804104203010282441017418940001c10302e90719955401c03c4a224a0340380c039035400028200c42c0079000050240c0261400881c14000c044902000812a100522500c002c118158910004000d02d150038001002c04003c0188034005003030400a480e00340719558507840c15400380c44480b103000a8060544101c0c0362207025414548904440300705079100101c5c2c1d004000e02001001450b00e121b01c92203000c0c02c01c06486607122480890400e0320b9883d403102005003030707000c54100b0000a400003003076021281e480540c1503c4104401c0161020120f0380c0042d80234000420021070200400290b4610184c01c0c0d800078044408155003814403489211b01c040c0a84038100e6a07550340d400d01c85106604147c0601d80080d101c0c00707a000135800c44483d40030001140b0042a400c22480c0e51001010140e031071104042c5140100c41e20021700441e40080741c5140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 682913669 1107 682912562 682912567
    0x30708121c0f0e1507090e0c07061509060801180807110f040c0c02090f1b030702070e04110f06131e0b070506010f0b0715200d09031205090a08 63
    0x100e4000b2400c004c03140d08c8030190035410b48c2c00243c05232141a1079021005016100202c0240106003250700052428203281038282035844404002d0514000c0304078034404299200210340e20303140d00041c150524010580800c81c040d442e09a5942e125241c00d03003a0784001d07008071492198901c2181c0d5503881d40d90b07070100c5006124058941c800000090f2008050003040c560046400074841e00441d040030f540c0b0656070103450012502107540d0100d80180c00902c0c140740d02c00c8000c001080b40c25908210f1800c3c1250402c49003031144c0c4503090303020417100038184030000c00d000180412010856580c80541006a0f94040a200701100d5410880001448841c0b150a44000c50f034040d0306402c0030104001c20402400003141420b0000d494000300d0004004017000a000700b5a04050100301601780b4100900320201007410085154185020044e2400c3c0c0461900030b0594415810b58 = true := by decide +kernel

theorem cover : BRFrame.Cov 682733812 682913669 := by
  have h0 := BRFrame.cov_init 682733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 682733812 ≤ n) (h2 : n < 682913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
