-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3380
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:30:01.590328+00:00
-- url     : https://prove2.me/submissions/41001c32-56a9-46a1-ad79-2d016d407821

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 607733812 ≤ n < 607913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 607735062 1250 607733812 607733869
    0x30806091905040f02010f090e010509070507060f0c020d02070303080a020310050607031805122d010e010218061312020d120206150a0602030a030f1805160f0302 71
    0x7034450081e2800c903003006141400300010091104030101d200e40c000c0e82c40055400740300406481d1100140186003181c0301c100010041c03490856911580030429180403030422403142c0d1078409840440ca5007449094540c0c40c0c007592954100305c001c4420780144010121140344d0f8a000c0c5c440d62010346000314a50b0000005242c403070446d001c10004000c0a0001940d032481d5040040905c2c0e0402045100809207001c00035540c135002a8000c100040d95003c0d0507031078008140101545501d000100d00d00e00c0801c80c41303c810100b80b150705003c4010b2030001d85c2d540121240c0c5104401c403032803080e1061400b4000812000409913225040d28441c40742c480c00a2070900000f481681003070b4004112038424a01d0310080c66000c100e00e40101e2601c1c02d40b84a050300074003041b50f100400e008d020010b0740240308540d80e0320300c0b076003205022103070050002403900219010415001480881a5120b9203c04002ca00b000300c59142100201043c1c0300340741d491800c55000440f82089100d8099480164242c0300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 607736312 1250 607735062 607735081
    0x714030406230a050a02120a0e100608071d010f0b0c0106090c051b0a0203030d020a0c0b01030302010e0f0a02010509010e0103021b010b0f011e141e0301090c0c03080609 74
    0x7460b11900110904a0000d482850340d4a0341500312110042242810007007a80b1910302d000303803052510380c003601e01c181c2d60710300c0c1c20300e0000d00c2c015900034001d114014200d040e0940c94400e9001500d110000740c4491401d207217449544040a1030079840d440704032401040102e0040b5070740020360342908400c581d02d1110b101136a000d403443d604000203051074440b820a1641d04600141241c0004107080c040800d00c048081d900c41e070040d003010790142c104000d11103000d049940200703030a070040d042c01e07045d01e00551aa0806184c09800c01c5000d40e6403502401c06d607813420014074044280410041407a41c4065000034214050b850400e03050144e600d8804040342e010b50151041c100d20120341d100700d07148103610580070b00340c120740c4507010707079041c81042c10b4951242d1030100e9000c1300313406c50304020500d00d14111244d0212004206084900b07202d9400301400c540503454644492003041500d0754103280d0b0101c1101c0f01000884144030780304003c100081e400c041d00d1603003c0002c9a03030502c10b13a90b14254 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 607737562 1250 607736312 607736321
    0xf150206060922060509010b1003050f01061b0b041118070f180519061b08120705070b0c120c03160e1309030306080c010806030709050601020a0807030c030212030714030406 76
    0x201441c5c03e260410041140550284407140f900300c030307992074102040c0d9040c0c0c116101941e1000c00c580c1004018050f9901174003182403102c2d0f900541c07056402141c1c99007161400113550466080c45030f00084940f62902c2d00c4500c4030600503801d01c0c01c1500b030040015144a407201e80850600000481c04080c040354a4584001880c0c0504001486840c07c6500c2c41c041006028900200d109001c5080c4642c880300c0c0c20400c07240c1d10940382494000d10380d5108a01e5240200503604000c400c100000004441c08180e41c01603070440d242c9a11021007443c4106543d000600c50340361000306000b081810303005521000703001c045c1418104490b804c80c0000c82d12303400c28201e00c8a840c41c1421528010940c0c590300405c21030f0400700a0704c060905040044801d50710658149505038010300c82408562800da1140742c0202c0140102d44450402c2e03134131545160040d843c20b50205030540f480005241e014000a42c1202030181c0b001d146180071440170b00100f10400c0ec4807800d0f600400000d003001401d900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 607738812 1250 607737562 607737631
    0x2040b030a0f1514090a0c14070203012c28023a1112280209160f0201110d0e0304030c090507091a0a030c050d060f1502060609 56
    0x2412125101c1200074413039810700445602890880e03000030902c014510908850601c1d40c0d6403013403080681080160035400012050382e040d5623564005542d6490845158041004803210104000c90b0101c82030410035800030021000800e40046001c4040707000c00302d40442c0e41241d0078281140c004c2c514091000c241c1d15845d40000c242030f084041d181d01080c400800a1003000800d00410000e000d020900005098005450341300c0d01c4505400f040c851009250ba80c0d24040d40c20200d502ca800051074100281c1e0081d88410316140d06146c815031202c210403004000703000a010901011840211740c0c464841501d00440c1e03200003118088906204a80043d5000f04032a06441d4071004c03404c1c000d0005840d0b09012038480341c00000d0452450f42c1c001e00403514030120600f0800b03c3c14090b0003510040b038512041120401000344c2d818090711841000d0501d00c03203198170481c00c09049241c000380b0619403406640c480c1c401c01c103a6585543c5900d90104804807400c0c641481180840c40103000e401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 607740062 1250 607738812 607738841
    0x10c15021b010b030708010b0f280b0706050108161517041514040b010605090a170114070507080306150c190b070309080315030c0d150b0402040b030a0f 67
    0x1d56651028054000105000b000c40903a00c03415902d06400d070032240c50800d5141c1041300303090400750504e0914070b0411048003000300250001042c11580388034040c15000421040008203000c0d05001192240501628840c40184a0804995240342d0288401c0c0300384280e01d01d0560302e840b20f16200384c40c0900b40007504403518a090a203407a0100d074209c840340e4185001071070711780c0700c1c800c080e100c0383c3d1070f4041d9401103040c40ca2a401c0642c101da00b0360050314031540201104000103045c24000ea81c4000b0b4a6112000181540500503015004c030000f030700010030090140300001c080703141101225080304003240c05001c5400100c4c0503042038065201d03a480c2c14003c0a1550281014240e540a1446d1041141c0a00e503501c200c402c1d41100c11028015090142c140005524006800011000d144005044501c4903001e407000604006495000f11025850000442580495401001041c2404907020b504050512206904030b004c020071104903e40c481030303c004840310365031206a4900114 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 607741312 1250 607740062 607740097
    0x60e0f030f010c0c110f1e01020c12011d011b050921101103070f030513080a0905040b2403190203040326010302030c0d020307260d0c02010c1502 64
    0x3c610242808100b990159608010203440100c07910707200d2296846244024000031030011014642c0c883d43c0c000050550662052411003000d80d546c680140307003039015110000c505600180541601e002a20111840c1c9a040000796500c140302444986130440c61417602a0b203800d680300015030080301d00c1241c41c025205070005085424008143c8080e503100e8075006101c910740c54001c0c0c80d9148022100b20000642c00310018500920a4101d030b600210380001c140300f80c103215200d00f0100d9001d040d644004c11b4880c18104590300b45070040c5084003d04480c145010041000141c80390300d10103080220f01c11002001402210f43c0d01c6402c17030f800c001c0040454480c600b0746400b400100c4204c0102d03040c1d00007404c804003506c100c244098180c0364007401800700e8001d25014070000c0c0d01c280008a030f240c05802808640c0b1402030300c070f00140140b02030300d1620002c541c1c0155400c0001042c401d13230420203655074060250360802c0402110702d81c03100c41031544020702e460460003405141080a400d0155 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 607742562 1250 607741312 607741331
    0x303060905070c05070e04020d020915151306080402100e130603031206050409111c0f351606060e090d030b030d080f0c130b0d0f0501060e0f030f01 65
    0x1040310403080b5803050080317924550300e6910080f0130400840d00294402c914100130001030404001c1c2c4c640217218000d841c030440c81c000c400140e507100780d489000a14100030851180041c0040e1820b4010016400d16280c0b500702030300810010290401d0140a10540042c06102e035200c00c0740844061103401070803ca0140ca074580100703008440100303409442c0c145180807900c0e203454801c140003182c2c080c5880008171070308028000f102d00c11482b00c030b540b1003e1800900100d000707042181202803240300001c40f56401c232004203502407103440400ba00f1155461298610203070600407507200c01041001505250002d00d031100103804d01d908079448151500051146490f40010b8a0460f5007c0351420320000d8600d074145540c402c05619170b100011140004581c62301c445200c06a0080c42c20410f1a01d00034107003501030041a0280e00060740d80c0700008011000c50800e202d60452030294a00a200651500350024141c00e40f040030070b03102d0454242c0189680c2d07400c0203c10520a003070350091214689 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 607743812 1250 607742562 607742567
    0x27050307180b061c0c2003120a05060d2a06020309031011090402031012050708010513020f010e03070e010902041707030201050a05030a0f0501090b100f0912030306090507 75
    0x81c81500801c51900309010204185030800a84030403c40e004a020900414483c84602524900360141c0a10102c0c0c02d22400c0802516200511034549100079952040b4a5001c8260f040009003803a502071300e808284580c9660312031000200507007100280c500c15007842c1312380c0c40d290784070031104110354071000e0001b42250700813015202d9040f003101582c80a03030508e03d406c01900d01c0c6445104040c6030410001c0014507299000d1504803103004580720429031200c41c4100500d03903011054845910504007008050024003d1030f6212911191140305021a540441c6003102121107040c1400a4441c00c01034a0703c0c02c102450040c202008103074030035650f881d046c0000b54480c0c00b070040c8030080d240d00c55076542d00000f030940440c2c1e81030359400d2420889040455480d080601135441e501c2d107412a0070b01e004958000c00380030740303c0a00c000407103241d528204401684900c012409001000700c0d8907481c65049007a0f001190300c084602413101c1100c2c503080300140100d4004501403440c06080c081100d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 607745062 1250 607743812 607743839
    0x70b0d060e060d02092e0e160512160519110c06030c0a030203040212030a02070e0f100e070203040305070e0624040b070c0909110f0a03020127050307 66
    0x80e104112003510392942ca0902403d071500c0342002e0340295414001c10308146898450880da1102156440c2d41d041840c07440b114118080c1c1c1c04684410350b460300703200000e0200c8202000d100780a0410030700c8c010070402a01c02d0118010310300074083d800710026004840c0544121160714603401d4440342d001c8400d18010306440781200550000e4407405d00030309414180542220702072000c042d11b0b94100110003000324041c5d880100200d0b0060301411103141055803c0015004560b450b801a01c401070506501d010b800030020b2049625451300070600894549070408502907a115400440c165aa41070302a0326601c210751000b483c1e8850b401380022000031310b0480c24003400e0704869010040d000345d140204021105c8221168070b4030308200030013030380b05400010448135204d00e00141005a0b6224640100c0307090000c1a1020b40300030000003e18507184040303520701c1008a400b0b200740da0071900000c04107101240c083d20b030890b09203445038654801040000007400020219000c0b01d440f04800e81004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 607746312 1250 607745062 607745069
    0xa032a1407090e060a0908070506010f05042009091f030c0e37060b0a0302030601030f05132a0b0a020d02011a210106080f0f0c0120070b0d06 62
    0x1401402070204141019010f650025200400140b965484400c0d0101c010b01903a00126041c000420001c40050414091640200000e19076403424a2610050000ba41c0040950b1282d5644003404683c03d0f00a18040d528103d00c280c8890303000d60703206451141400071003c15900700c000758440001c10400035002c1e030f806558046181c0000c0303488030310700011200781004052500d50010850754600c803050303882c01c02858503880f070003040040d500d0790450642d601c51005140020b40000406c0f900f03503010f0003441c0050000c51820081e80c90000c400c02d003603030943c3e0390003083d004001402c081700054103d0360312140300044000360141556610b015030ac5a011803412000340c00360742d500d040118018031805008000303d5011030b464050a83c10481c0c002118080260201980c1003001c21041d003d20500b00602550300090101000f850020b520b4034441195000842d88000741015460740d11400c80b403641e481c1071607040d050001c0851014100b00d10303078001c4045008003060074016001d5540100f401c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 607747562 1250 607746312 607746353
    0x3121e1e0609110702100e040204060903050f0604030207050d02040f05091e0604020d0303050a0e0a0b1f0b0406140403060c0e120303040215090411040803031503030403050a032a 78
    0x3000c0d502c1c105401a1000312141120103035050004c1005400c106004e408008614a004044024284001022a0059000200058403250f82801008010440810400005401000326180c181d600a589012600030a4090003500c0c151804540b2150086440948460410b10061400320207581d0f0740e0100d590340b00c0000c0e41a010b030420448001c628180503607000f0f00103070b110602644064024000c05041c4005082d82c540c3c994407104001c0c420000d81d584030303255114640c01c00381480406400d514585c0122300b03448890030440030952404941c200c4103942408003010fa0080050b010a0255030b101074291428502c001c0805640128500d01070300b03049034050b00f6aa052400582d40f4001210001d402c00e1141400b03a02450511020344410a0700600100c2c1145405500c07a8054000b41e2214107a54804401d0107034200d040009080d08072400d400940c202451034a44d1030b641c041d5208042c0c1404a181d0710030070310186c501c0001182102d02c29060f40d80000170301c1c0c205207192052840100307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 607748812 1250 607747562 607747571
    0x402030115090518040f14060a091416052106160f0309050604020909010f090b2a03180c0607080a021204060c08030a0e1504050601050d03121e1e 64
    0x1c0318900a228544e8071100e4960094241d603483d03a80d14400b0303804071400e40e40c1c82c0700c0c2c1c00d042150b05006c02100c2d109a041c1d113030100311360388241341002d90480c989510744925000562030300e400b566240c06140c1101c9003100da16008110000c03000b0039810980d038100e800f600890042103220302000407214a11107850351660300e03031000350f04101c0481f01c98541c0100250071082c0414050320344082c5098110a0746000040c1c030002800d400300484400701000c49148094508214500010080e034500c0000d2151640004600600f8518001d210050018164201d0154040e95001e0104000c4514960140040c1e9444405080c056103a8000c04c0b41640144075543c5040901a628010354007107408940302c029403c0100da542d18003903080140607160981d654201c070084048108100002803601e20917010b01402c0034107229050000503001140608001e491210010354440626268035107846400901d0314032500801c1e0381d004942c00030041c05803d229a03083c1c0001481c0305a07000110b038410412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 607750062 1250 607748812 607748819
    0x80c070c1e050d030f030f0e0318130902090412020a02030105281a0609030a06020403260c0d050304020102010e0d0302031806061e060d0603062319150302040203011509 74
    0x10340f070120400300030005000304441c0b42000b40240c0108078059a14440401d0701c0d06080311143c510382049050500b049503003a003101081c1030155960840d002001e005008800464010803054040608014008854020f40d1043c491003480481d100c00d500030002e10150401d5881c0d881d400d105080e032001400480c80c00000015000d00c10414105443d9080040070a0400704000843c1c00080303540d078140c003410031070800007603841c0300500103540b01e1000e520702c1528000c043c105080030b00e001940d081d041004480307000d140000d00e8641241d6540b611315902d5480e440100e0141c0790782102104580308811b4000521901030b0003840c4a41a140f0350100c01c240707080700695a44100391607a60300300c642441c070b0740111030741c450b40004021000380469141060744500c440c00c44a81d91310568449554031072035640b950852865000390f038140030900105003403130007111100c1001c03001c880009a03510910b681a00c0c030b460b02030340c0c002c0d0b40080045440b9a51113a82c0d0203084807101d00100081e03420000407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 607751312 1250 607750062 607750069
    0xe0411130903080f07050705030f0a0201060e011409100e090f0624130e0a142a090402041d011a0a030804141f0c060c0509030a0201080c070c1e05 64
    0x1440d03007581558514040b500c583c0398194088002504600c1081810081c80740407410070001858070402c085121039489407030710402402c41e6001d030400b41c8516589401001844100c2301c18044150b400c4a12100c107842d140310303010340301c7c003aa40300031b84011004082009049001c03d04421402140c0243d402036a240701d0107284803141c89420710341c0b64106075105c4805060074255051040b8400400095075030181c2030803842c0101a400032590b07803203081c5200400070f000344001d49200301000034040b04007840b10140340c20b03409d841000501400140c00000d003550740b07640000360303680d00c9031800048030010020007601808154030b040e1440701d032140c280c8000e030602d88940d10460307400458581c1082d0230080c090401c860070400060b0f10022110842140b20100814140038070000e0321820701d18001442c00300700740c0d070080c060102030120030310020404c0d460104100074140d0b03091929118035610fa0524145a01034254060220744410001047d0305841d100700c90003125074503003001100765582040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 607752562 1250 607751312 607751321
    0x601090e0106051305040510060c050708011407031505060306121002131707081f060302060406030507020c010c0203100905070306050c0a02120c0d0e120f030a11030405090c130e041113 81
    0x3100d810503223400300700040c4900e6855050520032400d0b40c005d517540b0249282980c1c8448144010024442c040c411040e4162040b1303410402642a0a60554039100000d5001d000003010203014200045000e03007200b1040c0b00c07442003482c40d9602151038400c1c03e0b58110f0350403040e0150009020310310580d201034030b0000403060200c8100303000038800518128001e42e0307000c03909002c011090340c40b810044010390b20b010140018250f10703640002c0e07924203c40c00030710344261a41c119051200100a40003d61804107248081c03003c00c550205228800e860590b00c1c0c600d09070320140103181340c00c090200072103500005003404e40c41070307084407103409250285410754030035151020309039032200c400d000f00203001d41110001c203c4010005d82400c3c1c40c40c401641881503100058045401c0050a40c041d00d4110403080c095014140041d8142401c00c004078503461000350031041d4040012514505065100c0c1940c00130300490710200950303040900c2c0c4050f02d018124031461082c072100c071500d01448194400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 607753812 1250 607752562 607752571
    0x90c040e070f09020906040312030902041d060703051902031003020f0108151003020d1a032104140409051e120f090f0f0a030f051509060c030601090e01060513050405 73
    0x2086102c2d60310f401d141d54001d40c0900e02043e0000b0040c0400000b040e0754401550b0800c1c1113880110350b2420b24810403040b900210040d1802d40c101e00344002e400040011a03503070050040c10700254035290180c2c143c8040032a042c0205685000108001741400030482500459100b0344404d040490b185005607620307402110290903d100349a8021410714259600d90300c203039418140189040040c41d001015950182c01000031140c008400e0911410100303c642d95895203008201d000085501014525205600c980d9028076180b0300c45e00999a190740c00b4000e1194800f04a03000044a42e4030750383c03c02c070541c000b60745a000e0000b0002e0440c83c4070b400c541c85807003441e9042c0e103070560540420596060405400d90490042d8180b08101e88550a607000994000c40fa1100700e00b0984c508507140c030000c040881154020f0070144011120f0000b5556004054214078645a40e2440c00484402001e6805100400c41600c00010700e160098001c1803554152080c00d4141030f03d440c14442a14801d0301d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 607755062 1250 607753812 607753829
    0x3010506070f110637020c01030e190308070e04180206130f0b07200901030311030903010903050a11010b010f1d030a030f120c0c080703020a0b090c040e07 68
    0x428000051010704241e0b080b640705180c4250415901404030303d140d04400c001044071031070300d40220b440c110b26020340b449100840780c0002030100010f9000b500d03004e260003d2030500d6110540746040702c00600c101c805512000c988882c0c5a201407c0080890744140d4031040801d40003480d10080741441c0c05408402d44061200f14498003040e824000b803a40200c503040d250810128002c00d01c4e00e00103072004020141068016162502810900440c0842d5450b0040115010f500b056240d00c605101d503044a0300360922a50048030500c510381144101c0c90926415480e10b580030042513000406440b107400c81d9607035107030034041e612511400c0352780d503000040c00308481c1002c1c2e21610740f00300d5401142c228104952520f6103140c9020910f003140d641d400302c01084810f94607510303d40c2e11850200da0184191400e2140800050700075041c000d1a06001c0c020980001d07580043c14002c010000d542c0303030700c040c03110a9440c081300c2568461580311100b1344107a080440103c1a0712000034030344107031a41d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 607756312 1250 607755062 607755067
    0x170f03041e080301122a090c09030b061002030d020a090603060602190809010504050a030b04060b090f010b0a0c081908010510020705040c0905060c0102030106080606280306081207120503010506 85
    0xb62003070140107180f600849401d41406d56000140a40404080500f1078402c914002e0034180300242043d641c258005800b08440b00d102080441c0308100031581120040d2403050b001051880300700d0451280068800ca820300004050b100c41d84d200701d00d10704440e0b00e030740c8c20080a6250030b01241c45290f203500c500b02c14190b070200392021030318a000909801005040191410f60781d0408201d8100c06984141c885907813200401c800e10070203018803404a6421503000020340343c42c100e414881841802520300004010a150710b40d41d00511081001e2074004418649034414404102d102440c09454100001c44c0c040001880f420805149650510716401500c1110b040c074092100030030040445404014400711f00195a4441000415000c2000702c0056525814480003526801d00680050300804003001000d15254403551024000080014503400707050f06d1600440191916400444181c010740103001024100a03009009007031103036540310a040c50080c17066469010910405d500304c0c408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 607757562 1250 607756312 607756319
    0xd090b030f07021906020304050c01080907030b09031c0207050715020705221407020c03120306010e0f041d160302010915050f0d0501061d030316170f03041e080301 72
    0x1000481e540941603104546000410a000b154808610718040d03031902e5001051000b031210a014101c038a100a00700502a03003804a007890f5145210300c009825001c816011620b401c400340115100140c85010510000e16580208402944101422240c138482c40000090068000400440301c3c011500545807507442c040074041042c216045c00510191501c002a00141e820f100d240c00807801d12040c00c503646032510000e4501214010050b1195001c0012815100c8150381200c0e4001350a28291441e1a20350010840d048a40740c4030310351250504081500810500d60340c511900200c00498007210403860700c10f1030b00310701800060300041c188034041c4140f450758038a03070040c50400d2070000d01c0c1c40e5000300c00c0d05071608039880850300b07035072283c004201ca035600100d252040c900c04400c01400b10400b000099480c4140311440d44541181d466180a205881140c00790321501d1158680da00d1800e5004481c81b80d2040710f003207400340000444004519060b004402c2200e034009851865030f4203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 607758812 1250 607757562 607757581
    0x9150118030b1b0904330f18020712020c03070e060a030b2e0528180216050105010603050906090a080708072103050c090603060f1914030d090b03 64
    0x4412041d03c0110100f04441d0840b511544103000816203494804006a14403a90084204c081c591101c0c1c00302a60120070b0102003010500d4100721449050083c442404c0c0d10380c800040c0c002c1e8207005d00465090084090620b4003c2584020141c0803400d480700162240f4030a098460b086d038115070040360310341041c400900f5469500360000c20141c81c540d0100e9030050b00601d400e01ca244065200c6603a0a81000303903090140440b281d00380d010344001d40220f12554006000c2403144601e0200107482000b02c0c42542e40c950441c1d034544600075a90800c40d245d17003030460180c10300303110704c8001a05d4000011020b41300402c2c1c3c14000d00020000e425070700d00603180c200041d080135806840007641040400300044d82c2c441045200403420031f9010010554420180850300700410049442030300700208130791591080e0403291300c814111034010a408101010800003440240c40e010300c3c4c09a82c82c0482c4040f02c0250303024001004404a07410390754903003400c540000d6144148a0b1020341403010500000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 607760062 1250 607758812 607758841
    0xf12180f1504081501050d110d0206040807030b06191505030c09040203010602250620010e070807180b0d020418050105010605070311070e2409150118030b 68
    0xc8008040d45094440c404540ea52a071040d4004074a580c004c24a126010903c103241c1d038010181214110140f00d1242c40c0e09041180c02d14070944914000707408402195640420381d0b010748000b10072243c4042d240e203458408074a0682d2094803401c4405043d82c04d240d84841030400b622540d003140000e00c0c28071700c0c00740c5980c1c002400700c50340c3d940f05002d46442d68540b440914020036850740200000c0c2d2052060941250401c0103544c615110400c0910446800045200c01203c0c58807040c0c0d0708034062640e0380d00501405104141601507d480002d1107000041c0c1101a04c0480d0310401d400400440120101e0f18076100f01c64001c1608074400c1c0c01361400c2e5110b4000420308202d052000d80d00d40e039031542111403d8000d100442c401054110034541d2202c201199840241c0c014a1258103000000c0320000e0000d001c8030301b481c0c2e0455004407820070100d280c0c404070006483d50301541400d80402c040050f000a4841c0080c07030003510300707013827042c45a58901282c1c2c0040580c8050f89542300490600d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 607761312 1250 607760062 607760089
    0x120c0512040303140c1f02030f13080906160605010806010810052a190201051b040b04030b0c120c0702130c080114010201200c06010e011505070201090b0a020f1218 72
    0x303001c0d0524941c100307482c5040b400940315070740c46e00581e68034116103c0c0070a00c0020b0084404568043c034080000f49041d01207610b010400c54110b07803107001d030100c4000c1c040c2413004000c06403401c08000251045000580038140c40100050b00c1200038007418020480310201e68001980208070000b0460341d07404c44c1508001d0034050800c500c1d00a0080c00741e01004078448403031005070341da10304102070b000d4001c6485409030b80f44d489686c80c00e8500582c1c80c00340c6c001c1d0700028040c14600303008180b114419034104d8014000781248101d5a20b811000341c05140c00078102a4090000070002d0250b42075035116041e0164580d44503400c032039003000103840b015011300c44000d041d507599003a1a04510007504540780b04040883c2c1c02d42e9203054a842c0c06061041c1a171240c3c90481c05440140300f00c4495101e84001c0424502e0038549800c074600040b101800c0301d82c84043c1c00d110016601003090790100d40b08450b281c0c0c6408580300300d0000840d07008a4400c00161044004280d00e00350240e02d03118120b488030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 607762562 1250 607761312 607761337
    0x904080708030411010f021906050604022a060a0203090d081b16060605090f070c060209060414030706020615010809010f051e070f081909120c051204030314 69
    0x404600d03589400340c0c0d030300070790301555008040c181c008829a40708861041c81c41003480940003018400c0092400300d81c40510050a1545400001c0c40b55225507060b603c5103141d00240022074607003a014400d007855590240b900070702030140083d46000090085034013401e8002c1c0240420b0800d84012182c43c4000707440c1c1019010740c90502c40c043c09029010704007504030880710445c01380b0649000701c00c60fa1980d00c1140142c010404109441d80c0e4155242d902c1501030402c03171140c40091801d0340c001e00c904516954000301c04580411416020803049004e0b0304c0c1138040300c43d0301d0340304d01c03059949800403581603071442c4040302009025482440d03810f4212400c080082540b100c084c40400a0b03440488032888000a4070303460f070340003640503c1103d82215060a2000d42c0460040c8018040c2400a00e141c00e02080450300d8021034010b83c1c450603416401c44d0186a28221107040200a5000300c0f000703603098428890743c8203802c882c10f070841e1b0441c1da250301c5a089040c0b1100310500507400c86000d0000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 607763812 1250 607762562 607762567
    0x3020d0b030304090b0a080d020d27031109090703050c04020a05160b0601021002090f061b1605120c0603070c030207030b01031a0c070201120b030c0406081605030d090302090408 78
    0x4035840420203800580003902000c2032601002040c0032102c003150b404080258010303031000300c0054010600c0f9a4480051810a17498004800040001200d140300914031107140e81c5c0010070700000d000300710800102228603031903e807102525203649542d40d00024001e604069034402c440c0c134043e4000c0650038054103001d403c26030202507821b81b102e0302c4001510b0030304012080122940c2d040c05011440c200403c8114144200f0401040314203a040304a50f00544000031905d08050500386c451100841a07000c8401c419050070325858201c10601c901405404903111080b90b408010030001e600e0070002d40701c5400d5680d841380c02c641c101c000403c16003c1d400f9491011010441084105010b1801103d49803060910a881c3c00d03191040102400d4000c0014010800140ea2180344801500d086507004100748071624002802c0808201c070043d40300d0301d40207001802050100da41c2c1c0c4043e00c4501c0d20480c03184e54005040e00c81d0489502500020450781c000e000514001243e01e401c540101009070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 607765062 1250 607763812 607763831
    0x3070c0605010906060314100b1e13060e010908060f040804080f0d020c040b0f01080907090c0908010b0a0303140c030403080708031f0810020c010f02040e090d050909040303020d 78
    0x8648007a00002802904c6040034803c25030540190b401d0a40380c00078001c0c891900c0303102c050380b070307500c2d400b03410b8140600107403d41803020401481170f51064100441a83d40c241048100c10b50304062150402142060029444540c01495030b44200d400d480e014140355a09c034510848035885c014422035081406000100d450001000404240310100d40104444202641c029182c9032140030228492400c1c070500758101d403540b500d40da059180a00b480c00050f1940c1c800c45042c03074043d400060080349440000000c1b1a408040e41080ba008a0003c2114807420024490031b80103501024003c80c01d0111013801801c099001007960000d82e10949040c00d03203e0341c4441c21648959000e464090002c000d01401155908000c0340c52001020402c00ca00e01c1c005119844802d40700100f0841540400d03046510346007034229515910349003208540d00e40d00c40e8500045c0c0c40c4207031400440d52007a001c586881c14001c2c0100e81e129800201f2020240d130b11560220040c1d88480c01d13206030a901c1700c6000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 607766312 1250 607765062 607765073
    0xf03180a03060c09060306050901032102010f150603050c161202030906031005090907210204060302190f1703070605060301090b1005040b040510060e0105160c090c0c031403070c 78
    0x24030040c441592403044845c0380c40c50081c2605d5403500031038440d0700c10728010070000314850319948401c0d28207583c1002000c1c0481d0242e00400c003240c4140505400c0000412110245654102c1610039588040105450380c901c000703c40d0040503c2c0014140c0c0090b064408695203e48000c54142c0510403a4030740b584410103c1c00b107402c151260712040c0e2402e503050140b1326149a00d1544003010b40014803140d8075100b201d090201d0101404103440700c424a4540c1907481d5030b0403550155801415103544101050b600c0040590741d1301c2203042e040e000020101e840d0b007100780a110035803086001141020030301c0c0c07200c200400024149641c03540d43e0744220b50001e1440701103e480355006000d40740d0310360309e090103100c10b42d001e107030314284128a042c00b08103442562540c04d005070344084c074042e10380385102001a11140b00e0020800d80c0c074074103c42d58008000009030b001c0140d40c0060780501402c80450400e450762101490000c001c118810120f20005c5400005141d01032080d01c0c02c1092820b40e5100d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 607767562 1250 607766312 607766321
    0xf060c05100e010f110a0206040809060909010b030f2203120e010c0f0206070201180f020f12070501091401050d050c1b0a0215072006120f04140f03180a0306 69
    0x30499455419840654020740301d0345c81c040b690802d030503162102c2e4032002902c0304001800240714107004281117900d5224201aa40c800701c0140241603656140d4103c800550001c45034014000003040000e4142202454905d18200d40f64032510010400d079074040c0d507134107106900008010f5640c10f10781c00d885030901446104024680324403152500c12a4001e00300308000b4640401e40e810950f10500315401c04c0300301c0001c00d4100030300030110b11048c030008400c4c00090480e40d6001c10151601c13052803601040800444000740c035412417040d40e819404045000d050b0b21680412014130010000e130000c3d0b04078650000c580e4003500c4c038001e1003281904030f8084003600b0140a6100501c0c400440c01c14460101d600b220348400942404c1203541d9000380c0f20520025004a85000d0011403200e858400030781d2103002d891170914603189401060711000805c1210240ca41c86054462000c0078603020a041501c400482e001c0c40c0303070035000c00c50615a500314913a07498220350f02902c0000800c449105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 607768812 1250 607767562 607767581
    0x1020a060c120606080406060806100b07020414010609320618060d090b100317130e010e0f0a111602030c0d06050106090801060f030b0c13060809160f060c0510 70
    0x3103103600c5e8200341c20140102c85260704803102d00c0e4004420702009a0401c1206411a800c00c3d080b43e41c2c3d03d00c54804600980580b20380d004010250900201e0003a42102070398042c0c40340c0201440c540c0e00098503103903c60642001d00791034200c6d0320050480c81e04040c40100101c84482c00c04150352017a40d0040344490f8450450502c03a0b56072405800d040156280303c90f034210305107801c00e12010781940c441080c00181c042160720244070001d100740c922401028440024407411044124540e910202e0140000c0708030b820000f2090860001740a9074070a2041000b4950071a24050a04040c02018171440301c1c40b10040e6807510921211403210b6030b070b06511030f10b2a4402c0c08082a42e52408201411140842d00300e0282a4100b00301805041900e030802011a50170820306000768459417090007092240040103568400c4c60740c008686507801c0350340c01c0e004814440071035400c0b0402c400501083c0c0c02e03038005d8040128444208021151040110600c5140914155001515607905040031141c500340e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 607770062 1250 607768812 607768817
    0x1122a09020a11150115143f180102070503030c070201170108060a150504020d0903121503171902070302031507210f06060c0611070201020a060c120606 67
    0x615840c2c190f070214442a44107000c0740108070000e1014000c0340c440c8014018031aa00c102d60200c2c00d0500e00c140d880c02d030300b2440e0030000b5965150101e00d05510401146c00320100c0f4800100100b07000329240413681c50500d0303603d034803509030301c5d11071003281d4011f04c0d8442e01403507640074001500442d00900085000d0070811110340e0340c40c104c130b10024090041c0d070304a410821b01a00010044139802007080740c1e0103401c2200015003030300380e51001c20302e403812608420b8000d440800e40821521941e8041c0795480d00030b803201c1009c0d2140b00310319401e85030422000081c069075500108005030341c46981d03600341c011141019080c5003070f00e0018001ca80c0c0802100340103078821101001076060901240c0310800c801c0a008440d4540810094082d0b649161400a4840900d215800104441e8040c4c2d889a80d80c190510002c0e0351054000e00b41c1e1303170302102501c107a45009032400c000014001103903070465043c3c018000c002400d032101c5004007462807121082c0192a184031500d003800c1c0c883d0750050003ca4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 607771312 1250 607770062 607770067
    0x519060804030311130e31060b0406030b1e1503070311030a0b0c0d0507022b020a0222060506040f050d0c030c26010501081e01291801122a0902 63
    0xc606084602c002a40d11509007191410b42d01070303082c1c181d07c1c40c2d040e10b0300400080750000e4038034007140040c10a540090038903031b0304105100e40c0c0200d1b02c0c88050404da080340d045030152100807070040f0400300380208a034140d0142400b0070025100c001c00b410298001002d84601010617216070149850072030310721100d100d00042c01070301468244600c41d04103500d44008d049803603000e4064402221011100202500c00e5000c1641842c130804c00412072a030b0103000d0b15003d07119004018400c004294401240070306001e808103003400d046050b0380032a018440154052480c103410300031302d180d50308015180141035040200100d0400982c4e84000c0012a03e004441c0101d14604413041c048000c81c204180d04100042010240021354000c0d281d8a6680c4100f01d2a0500f1040340103080c107040090b941180b10410f82c0400d00c00d00102c22003c3c0f010b64240c445139030254024104d2050034001e075803519800700e030a1000300340c0d5010000b21482890207010b120f08074070101c800e407041c541d03407010101d903800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 607772562 1250 607771312 607771321
    0x2071712180a08010b21010b040c030e010606051c0b0d120e0a2106020d2414060c07090203070905030115090b030c1302180d0503040519060804030311130e 68
    0x4600d00ca001449010300805c02c418428000600c41c1ca468403251110300e0742c44810200c0c41e44c080d0300644100500802c100558265002d001e0b0190002c8c1000b000360303500c2e081e4009401c0c0e000c2c508550020410320780c0c190700c03502c0041c41140100000c640d8660858200391000c4001946c0300c100105980071a1141040c040e1044100108608560010141c4c0b0110100210592819041034030031640c0c001009078442d030706041d0f100c004010301201c403820381000e80345651010064095040a032861144e18a08000c002d0040c840b035407250401440079640101000c1007105015805140c01882d0740c6483c1490603603070070000c2d003940e000c2c4112640d41284a84d040160060912650042407026006080c1c1d01d0721280c0040c480407142080c1c009110b80010307040110083c080031960444c3e01c02045140d5004040c24107696070340080c02803500031050440100030321443d5005c1c080c1195002c2c1c1e52580b003680ca65070101d020741010780e0441c0e1920340c2030181c14240c80301385c0321082c00f03000c1800c00300c20107140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 607773812 1250 607772562 607772569
    0x901050601051c0504030e04020f0d0501060804120e031f0f270b0415051806060904020d12120501060f0e0a0617102714070207171218 59
    0x162800d81846000c01c900080e854070210b01c01c100d80b82015000070341d950707681020b8130401105007809a00078800a50001a4a24000500100c0b0450300c0c04000309da0700c2d40c0c3d007a21459400c0e03801412800c03102800e00b2070300d44182c0709004060300140603078181d041d00d9503403103101e940c0e1113040d00b40e6207441d16800400c102c040d10030040c081c034041d14a00c1d102500000d041000001e0a5400782502c100c0d1400a011b1040d0006564100b60801070104014131b40780f00025011048203011070183c0c001e072004641e0920380441050300454005020610100490751010703010850104d4032000d1003100d1000591000c3c0c02e100f254008c011903118000e40004050000349245981c4601c20700c5410a080c0030b1000552041ca103c4010044030594001500c1d00c11101e1490304403030340184102c84403240c0308480d042c5502030341c6500001c954014003002d960021419100d070400c40d07c810040e440843d040110359041c6180c1450400d01a0a4a070007503140040b000e041d078072001840b190900c070130000000c2800c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 607775062 1250 607773812 607773821
    0xc0f24060e100b3a05061c020604060c02120703111005070809010c170304060b090906090607051305040513050f030a121e0c0804060605040b18040c080d02060901 71
    0x4845030020b810345081031040f40c454000c50b0419401000c000030390b1604554044240c260400070007581c04c0c85aa0b80350f90f10f401410342110b05034003034080708401000b5000c00407200d00303002da40241001d09280c10400308480326104a081aa404010038149a902c00014400c0c040030718000c1c0c80e04503440310010244440401c0c24004401040005c02c90300c2c000c900600c0a0f01ea04180900c1d0030406050b0b642403101d410780c10458504240c44000061004211041d0f00c141a428011394072100c00f980c951482076240c240c01c4a8803140c0381c011100051000e446040200340d4106000c00e01410f40392180d0110b01181e800707d80c810510070000907401d0610004014440b1850303900b0000b185849083d07800100f4059600a0405556031590250300d940341464581c108407e904035402c001281d250f600040ca559030542c0e06440a514051000c129414640103401c5441c402811505000c003c00303040b082140c00042c0251440401010042030a90b07007404071201c641980e074010030707a0f410444069400c60303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 607776312 1250 607775062 607775071
    0xf060301051506041e080303150102010b0a0302060d1508071818020d0308071202030703090212071a0c03090d030503070207150e040e0708070b04030b09010209010c0f24060e 76
    0x4400162169890341c00b00d40c244c03048102001c10500fa58145617070001c002e84c001c0485404017104100c4408400c13161f900c03400718240d0003480084005c07028004420090300001e90404410841d9410b07060040d00044203004030b840a0400e0650b60710006402d01d241030b044401d0012924140c0680c420b40ca00508064100f010658070002055500081c0d0054034414001c007070105041c001070046000c3d071012441070040c0101595246481800203000341035008089114070700151081180c00d4000a100068800403081c0c03600c2c4803070025000c22280c12500942c1d160344810441041103454043c0c005131194441c0e00d51948a060210000c5d040c01400d4000c2000c0b41d00800e0480f41a0707520100400c6181d005031000103017140f4400200d81017420030740016a0030f00c102c1c1c100050108040001b4401c40e805020b9001c02512641001403c1c1d20030707007540600144020513042c000c40d01440c3c0c20880c5500c604201e0001e603540c0c40a1b80760740c600c90f60300b0b108041c0d580c1c14108a007000c05460154030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 607777562 1250 607776312 607776331
    0x30903020714092206060e01030b16020613020a0506040e0402130c02030a050a0201090204060806160203040e060118090f1a091b0c070806040501091725020a0e0f06030105 75
    0x203102c0390b000403424285008100ca03000716080b900c50410f80c07011100c01004641c000009001c1640c41c0c03650181c1c0250203100850b040c0300d06400150540758007010100a20312a0750180029481c0c05000640742c0d042d000703090381c0c0128a90000a40c55075030070014002810400c4d50043c4a1510380104a01c11b0819292451000c2c14003030221049940401164a0b1589500f8160344520318070404900500320108000d400074a488008244021f000404902c550210210201d10800000b000c9884c0c1c0914400d0f03480140302d13240400c086602031103445240782400c0780d0070b0400540c1e8654501c00d48424007181a082d9070748181045a0403e103115603c038041065a0841590400010307101180d030008202481d455400308642c0e4120314248840e40003032540307404958050a15040c0306000300031412089890b030404200e0340d039030304a82c4c2050300c00504000344003441c900a41102c80101040b0150200d034401c00f01303107010031500003100300503024030084c0b8900a00392030450107060840b000a03200390344 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 607778812 1250 607777562 607777589
    0x6061404080309040207081b0a290117030c0d0305010302010f09030308060405040204110406030218090c03070804030302271008100b0d090b130b06090c0421020604060309030207 78
    0x220107000000c03503c00140c00d07500141e881c2800e0130408920f000380084000d00034504506844580c4001600b4842c035405040c544031104e41d5040f528514201e04071154111424860042007548260b08984c5c50115101003900d16104a1088450a02c0001121500400d685500504c15941d018551348144040c0d0700b071482e642400e40d11b014155100c01041c980c4a580c0300d0001404544030b50300001000303401d09020300d450b01c0e01c607080039000e50042c0c2c0b005072200080c0048003c01d4900780c0e0030540038040c542051403035070703c03000300031950305400030401e406040d001c201c4000e08403481c0081c2c02e0700301d0421805459501640701001100340b52070503a4001c01a02c030b01440b00b81000140f10703c0460b8101003400b580c1e07082105010020700044440500543c41000400040381c01e240c80f14002d00703221f201e0a04071550764004128643d041a114090445d4080c441031240002c1744040c0c1410845100b50075004044a50014100c0c0c1e019070003840000c0d460310210030400d50108003600245c510740f87d1154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 607780062 1250 607778812 607778819
    0xa110606100818070f0f0923061c23060a0c0f2102030408070c080303190c0e031c020106090209060a030b0114070615061b0b2806061404 60
    0x90080001401d583e200c800703c5104105200340800c8024020520075941d501030f04e640340c0ea00c666243d0035105840400c0d00700345400c0710480442003010360107102100c92601c1c6840f01c00a21140004181c00069286078074038010000c0740c13590019496080400000010911000d484941030103c00340490715090708040c2c1c40201540c0001006114200b545003081e5050400d0070710b031485100740b040e0359880510000601051007500c2c00100038041c0030341ea892000cc0d03a2100015683c2c0b10465100450f4241100c8615210302c0d1500180f102c10b081d0300d0261626a40100040d043c20280c0c00d0101403c80070880365512180c0a000e20001003090301421400c002d01c05c00898400d11415954400301603a8003000707141d0b80c1c042e80c6582c003507110005810f80c503a115450982c00402c04e01c0d2a21052504a04000400c070b8410042808006100700c0c86841404255450401c1d40300060a05071085c2c00c00c101d00c0c10071001c0345d4020703c0c0c00040c2000224007103141500c00340000c031660342d0028604604000a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 607781312 1250 607780062 607780067
    0x114030f011404060b0d0b030c09040510020f0c0d0f0f030e0c060a031104030f061401030f0212010b03010e03030109112703011803020a0506070503090d1407080a11060610 75
    0x160440e80b803009040e00b401120340008008007540c0d000345018550115503942d500d440c0e0387c40305140241c16001c030f41d481901c107402c01141c0350003207070020540c1c0c0c0300c403005d0003043c40e41c1d030060109070b12407805c030780d00b441d070076100c0c2d6410300078520581d1001800700d01c40d50040705d60201c2c620b040d87e41d00e07007401c1200035035000d0f609403038038a03a1060500503840011000011407107544803042c9504000841034803541c5170701e0040b645c070010020a07250203050085460701041c52254503030403030b54000c0c485200a5043d40c2444450020f550400314113559070b115401340c80d142070284075500c4c216203002c1c5542c1d60419a1400c11200314000d0510704078018041d1034980070008065900c4040c0f000d41491070f00103a000060f0151042000d41c5410320f02d408854010103400094101121f8452000d60381680d0fa00d8001315130030b000448200c0c0d100d601180000e840a406000b8000300c40d03103c10f80161600ca440d031a9100ca55010300b4000d400a00000c0103590750344018000c498010204882503005d030350b07007180300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 607782562 1250 607781312 607781341
    0x150c1505010609060e0612090a050d0e06070615030204050a0f05011409040b1308040902030412030b03030a0c0c030f0f0507061107050909030903060c03010801180b0c070c030602030405010506011403 87
    0xb4003081c80316560341171100b40c1d5807000341d44502e0b00b1586a0107480c035003015001c2e142c21020a0840702c034807440701c885801da80581c600c500003000180080341854050744620001c2e10016001c0c1901c000c1700b140c0880582c480d402294441c184280022425a40d0b01d500b0004884050b4814078084960580c04003041c3d071542c00b41c0750040e80101e500c0190340c85001054103074800c83c80000300245d600050000c3c0c2c041c0c0d45c1d0003a600c02c03030042216500c541501301080d01964801103805916030002c0100b01d20480c02407036000903640c052189508500c1d00d80c1c0d078140458410400645102c5c03011494041048801c0000c180600307220726203804a00b884014840d07452100340643d1b481514100c0c00910a0401001038681c4030000408482c0182449111200d181d4070a0240e00100d500341103020015500042100241941c440034021283c2d507850340308445134002e40c07002c41b00c41c880c800c030000c0461814009035000d0341c0120000941401c012001400d01d105801c0a11402c400a108010b0381d491504030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 607783812 1250 607782562 607782569
    0x50601030201030b18070f080108010b090c210a0608070b130b092205040651060f1d0d1709030f0a020f0a15030c0207150c1505010609 59
    0x3c004c200f0000042c00900710510310280100086106001c0204a5600441200600946483d02011640c0b101c9180f802e8401c400d5206400c408140041090140e85100902080e1200085180b44551540440000c0071040d90409500354842900f400f00305424803125000b801075044051808991110560800c01103106d080301400c00840c41400c82c2e00c0302c041748080f1441005102d41100f0038245840c000380000e50701907901e07910f0074441030390b00000712807003c0100c0710140f483c2031041988803100741e903110903894036002c0c48400300700180307020121034059001d419a922501e501c20081c850003814483c01c0d4041120280d1107088800e010b88030f01c10903a0003690030007030415400310b00c0400403c080c0b0490703503182c0d0548034085a0032103180000c1803001080303100b15041001a0450410450016110f000c0d08442d800380220404440c2d0007540102d14031059401600d19403986c4800c4515686440c035030680104401040c10310802c55950400900700b905954108480e5060600c000c00071600e030f00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 607785062 1250 607783812 607783817
    0x130203012304090605041a090303010501021b150f07050c030303010303090915030c0b0d06170309091504020d0b0f120c060a090b040803190302180d020103020d150609080a050601030201 81
    0x22080c1400741c89a4028001003504100140420306151606001d400d5214a1f9504482d40c0350b07011482d061000b00c00c9a0480d10141c0c0140000310309910805c00c0383d110048580d0b4464801d40078410100c0c4824041d01e45046400d0b400d076140c1e801410001d041c4042c1208076403283d0810001400029045071b54401902c0e000b10000030340b035980d0107102005100b20303080944403110072a000610040800010940f4a903a800e040c403015640c0d4a083c100d0302c402d15080b0803190010700009501d41042d10301a540564a07488101e00300d03090401181c1207a0001c203070346c0c0800380c98a195410070304141c000c1c1010742c482540d02c03817280155048150348442c0c2034070081c0e228040001d040a111486a0084400350501d46d070140e994542c3c49902d01d950313034400c0400e40041d0111a861015a900a03c20f4681209204803d00c2e840811768003001180159180100e0600d0340c01e010400c0082e00c940b08003034800c0c00441301e84a88030304203034014246140c0c0d9401042d040d444038003030100049020903107a046aa0a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 607786312 1250 607785062 607785119
    0xb0a09020c010e01091113020711040504150504121706090109050a1104121112070b0d110a020f06090d0e060306010302040302060a0903021801061d0a09110913020301 73
    0x21603409003d0114084280c03100d40c00c00a011040c00240030400000c0d90301124404010001146210143c2c0104a03025008078620b90b8800018201a0040350303010b0b10651440c0c511104000e480c10445805450603911400600d544c1611765802c00d805402e011043c541c0c2c0545880d256001032907121050246200302a100c1000c202c12000540160941907541011140c6070740c1c4820380e0203140840340c40107580f0f6000600c400c906500302070f4142c40c50241d510002d0003c00d42411410f10395540208804000c0320380e503440300c902ea4030800c800350044080c136038058500300071085001440c103200a049074136140c0205094848207171300309200540c0100107598243e00c923030f13505006070000d00490380060b410200000b0714000d2581e0011110341a07900c00c903a9608a81d04001c0000e01c400e001f40515004a062500036005020300690300002c50003009007623248a1f9250025002600d8180464140081012a40c80011310f041c45004c07010341d092400460466142005100c1021040c51402c0f01e84a0707138 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 607787562 1250 607786312 607786327
    0x3120e0607110a120615050a1203050717040306020c120c0d1d100f08070c020a0501270b0a030b0d03020c010c080426240c0903010b0405040803070801090b0a0902 71
    0x50380c08443c0103202c000030106000ca00385c10b0100c0601000402c0030a0410609004141d40c9084250030042c2e42142500e04000c2c4c419a405a8155004080c15900300200741c010880c0700d884800100080c0d44100781c003503160302d0505241407034140402d5200030700380824002016012400519803404450519003480da1000031820701e03070520400b0070313240c2d08000c2c40d0740d01040341034021a10158959903543daa5880e030ba00e04d02c044826059480700258041140310040040c0d40c81030340702c401030703070400c2c2c0602c44907540c020040ca0440e111a802850740142c00b0a035190035640504c650b088203002503038031030800c8500385d07070003521418212030140c14402c101040f242440f03045400d40d006403014061001441c8500e0121101c201c1c0c01703580c0345c003141c8a0051080c03400240c0c0c80d08400350708401d18032404e0a0301c880c00110901e403c9041000d40640d030f5020071641c590780f1401518000da004d042699035a050422004020030300507040030340154200a0446581d44681d103d01c822184208001030300c5100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 607788812 1250 607787562 607787569
    0x8030a0207020d02030313081b0d080d0b1f020709060b0f03040f05010504050610090e0c01120e03030c03040c3f020d0b07081008070b090121050103120e060711 70
    0x140100282d0103100101e8407011f1034800c40e003900305981000040f104e00d40301a00d802c1025000c81c17110160020227a804890000744000080c000c01c0c0d00d4038401103a40303407035030000c40c005502004d1074150080702e130f008101c0420f806100d510060076941c5801d000240c03e2800c01101441400722001ea58200000050f080c001d811115040c20340e4031100138040c5041c1802c0160740c03072400751038000b214220f03030b48001445c111612131913902107402d0002d8080a40c1110043d02e020302046c1c2401858cc1e250311142816060600055100748000d452954490420303085c03009407602181c0080c0d9401c1d114128420044900780c460120301c8031219100e1070030f80c034480e404135003030340d090360000b0b4000141c5802c0e40100080f0001880c40b8603140d5603144142c3c0d407812017014414040d071081c0c40329600014070510802c05000c004001b4454181043e000c055408005100030899034001301050325551001071003040080d400f10b800c6142c0030301c1c100b41103005010002d0214454040002c2c020780e074140c2c27510320946 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 607790062 1250 607788812 607788829
    0x306161b11060c07090c1d1c0804090f0b0402070f12110d050c0d0c0807080f07060f0b0108161b0602040e0c0304030207080d17250e03060f010303140309031c0f0c03050408030a020702 80
    0x9d07404541207441c1c590307490001c0054122000c440c8101414040e8018050400c2c0c0b00741d40d00540c2240805051200d02c0d00d03010781c0c09058130b074000100702d080048481d000f0010040c0c0c1d0a20030742580c2e41c65551140481e2503040c000d80c14803d0b001c00103031070360200c08200b12509450100d9040700c00156560950040b62031240304207c0002d0ce011b0a20441803244070203a8003049070300a0a8032940c03059548e20040042035800400c51601141d1680840203075041082201c4070890300c182c5006103080c0d100c3c5d840d0500f000c2e0803030720b841a48000004000c200340e41400002c00820788480148100d0004001c00340040001d120600700103c0c8010000c4e00728010301e5584d074020b11500144162180c104031b0000c1c01d06180c500542c1c028031429010440050700611040d041b0b17500341d40c0392038030480d842512044950002c0e06003c1c041c84140200101078036115190300e400c000032000010000381d03d01c0403000381c6006081c0c91090600d00f40c01c100100d5951012a81c0c040c064000040e6192824800103007641e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 607791312 1250 607790062 607790119
    0x312051903020c060a092d020909010b030d020601031203020703170405010605010e06040e070e010203131d0108031804230a0b0306161b11060c07090c1d 67
    0xc191242602819099070060030206641c2040e035216a0b21481244217644000d00000c00ca50108500d030048001034600e1004081c145141d100c40100310746d00040e072070740b1043d102d800069560ba40300b8003940c030381080006000c0c8082d0000c1c00b115072458031f440b040c10101c502540c0034182c000402c08100b41c0300326036004200988a00e000014181341c00c1c080e00178849030090601098500c1050103081ca45001550300b25603402d90350900903913600e1000c83e0602100300c112410f5100900400e0f5414100c14080c201400c40810504000c0440012106a0f5841a40304030300540040003000e0717400c50346075110041e0b0070703050f40c01082d404116086164120140540313480002d403c10244040b0300165001031220040840c02c44a641e01d5640303520802403202c81e00b072404220b1900c810405c00203c070000554403070080304012900300b0464049942507000c481001102c1d00120b906200016043c8101c0ca002c0da03041c60003201c00752008440c0740301c40030312020700c6204501032500001c24085221541011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 607792562 1250 607791312 607791337
    0x409021c05070801231302120a0302010f05070804030e090603120c0a110405010612110702130c1d03300f0a0908010908030411010c02120d110c0604031205 68
    0x185002030800303507103880c0075018543c4a942001269500b03031002d684a500f040141c06603414140d00c035404031415110b15400201d070440310003002507407003102c14441107888034000e40010800c2c040360343c440011600020602c0d420b0102c400c0901010030381c42052015002c1341a00c100007592600c4000070328014039040ea40040b60700016070303003820406c041000e0903010700c2041d60514400c03400f000c100940b4001d025080005106240488001c3e80c43d0b0401248504c2c03842d29245400340d503401050303640031302103480d1320341644aa0100b100154800f204810641030b0740800e0160307030a07210000b40c4521083c8880040300508202c1500d010030007202c161540d01404925558806084c04c007109107401c01070034040403c40d030f20343c001006031040c09407100c2942c3c414050f0b4130350340da0f564402ca010450307400e829040000040c001030040e16030618640201980100921350000300200c0208080390104181d800e64220401806c12520380c0b00645058035400216020100d110318030442c0c981c041c20659011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 607793812 1250 607792562 607792609
    0xa0807060c08132a2c36060106050a080f072010091211010501060507020105071b0b0405040b0d0809040e25090f09020a03030e030712050f0c0915040902 67
    0x815900c901d500d142003400154150103d640c941d070108174600812592541404e8004900e045400c000c51941e084a040c120804406d0212001015144c880c00740c00c100c0100c0e10005080d01d41e941c10080c0c4c2c030382c04041120b15109d20300e01000c0052124030003450207184284035000e2070b00c1068007484541025180841c040000720124140780400c007060400c03801c00705c4c086149500351000180a400d0680d000b6440d030300d00c0d00480f54011241948103e070241c802c1c0030302c3c0c04031440d421502590800180942d00460f82c403079088c40100b104480308130094510030815200020300041f041c409540c1c1082080701c00040c25003548203028108000d09400f0006490011202401045070a01c554141c4001c000104a090a40b441d0078080341c40111010b913001340b902d20104002840344c0300b6070120308400380a403071000743d0300c5082049602642904442541200c0641d0b9001c1d581040280b06c49a0b0403521268113091600e04200307030716007031140355001c1c9480b0002e220030754079026400c48502d076000c1007145 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 607795062 1250 607793812 607793819
    0x101409010c05060903030a180b1612020c070303020c010203040807140604031e05010501090b060304060f0209060a0309050d0302030628030f152a030e0c030a0807060c08132a 76
    0x45d00ca80c0112540742e00c042c9001c049000310954440c010f41c400d58020050116911848030360300b007581c000b4286d0010021000d11512035a55280050040140079400610589085140181c10840001c04e207604560080c441084481307400a200c2d81100e003ca01d44c003104100d00000b0510503c140c1d00080d00a1040000504032400d03a902d09110701c42c00781e0700070800c60340c90740000340607152103803905944070900348081004a941d0381c0c024282010f40c1388005250050101c04a8895000800040301007540c0700c07071800c148030050201c1c4213102100e00d800c61851078130030300043c00c80b82d0000b03900d0320420515940c0a6450720211141c0c0255402c4502044a01020f24080040d20220010103a486050845030401c2d0031414111400581198205603400040c01804400400300412616030074491649031441a84041c00000c2c10240034281940d600c811301d003480da0070380e01e5000c40c01c0c003000b01b00c008004140117201d0803c540070f903200300401010507051001d030002e49000301c07100c6040328090b01e000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 607796312 1250 607795062 607795081
    0x3060c08010f051c06020310030c0602030706050a02040e13140703150c110606010e040b270c040302060f031906080c240318030c010203010305030d0506101409010c0506 74
    0x198129450b1482c20000903490b50240220494580a50351601a40385410b00006905030080c59010800301074408c507550380c9841b140f032580c003c1da0000c00540c000245031020321001d40540c6501000c1040f0552038a460800030342c00301c9000034020503644100141c134504010603050000c4aa4040c0c20455044640f281003185a0380540402c1e8400c0c68a0054407030241402800d4110040c202100a40519502d000040d1440500d00400681c026500c0e840c0003030030340c1d45802068008803a4406081c4c044010000c5650f0313580c1c00390501c83c889905120800040e5101c200300c450074000454a582c4035141d00c844000081000902400018103000b00031a0f00d072400118030118103411a01445000c150407207a040389070750358107061b540440410001382c06100000c0440740400e400303003c4900c0d1030302d0703221868221380081c1c008603009e4200165603001c02486008594119000302d41e8000f1107002d03d82e01402d6040d00903146006080d000c03400d400c081cae000d401a0180c3c1038100c020749580b4070300394402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 607797562 1250 607796312 607796327
    0x604081c050a0f0b040527150a0207110a030b06130b0324160e040506030c030a0f02100f0507060e030405150706140405030a08060d02061b0d1814040603060c 69
    0x42031a41803400000900c28a8180140c0d0700480300071f80c418507180340499070030306049402581c2501c541f0506807088104200b4080d41440b40c10344960040c0c80d41018900a940c040b40e03005402d1040f001c401c0c0a10114a141c2100c60304041c2c11114255081e03208c002c4000503000c20000345e6454000c80e4003001c80d9624000d24140300302c4100411815960318268003030890311400040c13000190060142c214641440d41c03042d074000c41c004086413081580180042d20b0041c1c0d0036021a1076080c0c40d1119421030402c01c8003c2c1c286900d80c240103105d504000801842030061250180c13613292a881058a004800d004542c060240502410028180341002c40d50036440403230300700c516030f00d400c0c0c0040c040400c5c1c035040e9000fa03600030059443d0504406048070840c038080c0665600000751600b443c0142c0c1c0b0000280000b20b050b09060f2007140060348410304142c03542d01c00400b0310121504e01044840c0000040c02520502c014070032054180001040040002d9040180550728013419031803503540200d175 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 607798812 1250 607797562 607797581
    0x190906180b0402040c0f0e0103090f0204061206050c09010503071b0503040803040e0f011d0415051302011209260c03030103030918060501050a050a030920041109030604081c050a 78
    0x8050014007050740c006c441c6511140e4065000810f200c1e4070120a6100342c025102d03050168508250207009500014101c0700c1d180d100c0000c2c01c00600c00b2400f08105401025403001c40309c51028109017054001a02510000f4034003820032800038180e46010102e01d290b04e0210360400201e031307102ca8548991580c2e236849030055180c00a0030000080c3e810750307c1c00c00c19040c0c130070018110303a03900e20110349a0508400684101d6100f8090000c0000b221041e01c01c081c0704101001c16504512950b00000d08a412030301020070b603184c02d1452607000f0800d000b00140c002c00b00e00040c42c280a0b5420181551401400850122030200100010525900580c41c006a8054120080042446003c0740040f11058411280031a05c14402140514001c00242c4000301c41420081000c070100d80d03905549200ca004100c45004040000c41918106423089102d8010100d28451801004000180d170b81c040c01400202090340000d51107100110008040300841e41e07842c0244003a040c90078840000e045401c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 607800062 1250 607798812 607798819
    0x3030e041b0824280b0d1506080618101a091512040803100314010e0637150e04020f011409090601140705070302040f05190906180b0402 60
    0x1005028214541000180d40c288010b0224680004c044407a0404c08a015807407074400a4a031000940c03058000e00424600c0800580041c0c0008115039240c07003103610f90482007c0001190410140341c458000e440b07218805115403807000c0c0e44800e86444c0c2031035150000000400400060071020902c50044c0142c007404a0f20341d940322507001c020303041b54045c0c213842541145030340c00480d01088080e4000c0d40c025555000100000d40c0700c2d00d034403040012207e240400c680d580c500b1600c3d01e240900c402604003118280c001d0000a406030380a98100c0040d000000c2d200070f4484a8084841c01c2d484030050100a41100840c81c0d540c0c550a800c0d450119402d900400700c081180c16650701c10b50300301000300e0340390070031a081103801c13003d0100100008225605200021500000b0381b080600030302400e500c158000c151043c11481444255440400389560341420803042c4031902112074521403440081190001d6020072a0a1020145c105c180210b10001003100c041da0034001c0080d6070703502c224002e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607801312 1250 607800062 607800091
    0x905060307052e020106030206030f150a050310050903040f030f031403040c0312200706021b0a05060703030207060906050106260c0703021c0c021c0c03030e041b08 72
    0x7801448614007100709201c641d40c021151071400361150110059030301c0f80ea440000780d102d4036a400300b1550342c0203445d80e11043c0b00700c008102c0f06060401c0700300a03012080d580b14030b50302c1c07030540405c2d0348007944020042d056440d02d0005200108c1081650024504041c84501e03081c0d882c2407408041651480617400540c1025510505040040442c1d000c2c85e40908006415455500e403920203078084840d1008026001040c0c441040d1110031108581240c440034000301ca1400344040d20b02400361800c2c02d00e410913090702d0003041c0e44540300c0ea000c5179030135900150b540b2a9803a0840003485152002442c3c14a044000703c180612980500c0c1620345689800302d80c0005448140d00c070b03a901d00402c0e00c401d01c002c40041c104080d600080c1c076003c1d1090045801941e2030360000d42480a1034010700d000518418022407d44c508045d06806220500800141e00049912490480c3c50b840c040a070900402c1b61030008141c40300d40c041500d03205900d0162814003c5046c00802c802415144850004c0c260b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 607802562 1250 607801312 607801319
    0x2070b211f08120301090f02120708060a0e010e0c16081305040b09040b011502030c0f0a030906050f04060c140f07060818030304020d030905090c0c010f0509030304110312040905060307 81
    0x504041001c0c0d10020703e40c01c3d0ba01c1c000d501c501411040060810880c1c086c06090141e980302c2901a0142c8001e4880640e1480d01009001c5000c129038003555036160340740b0040203040c0e5074800b180d4100040c09007480c1c1c1c8030061a0000804000440d008001c08000501d802807040c114604605071a012101070102845040400105100a40b000742c010010800100140c140d2003865060258442c0141d83c00c1600e84072040742440107810140c2995003059042000305944081090080d112504019003407000400700082c69008500038042409a0f1020f44401c0c0090003a071050303440102c40c112011040560710302610358140303200304130105421001107100e0880c1c1c0c25041000300082002541507560b95001c03c60702030400d44040d0706000001d10003003a6611100200d5102d1640f078800e0039501c03821a40002d08640400740180d0010707241000f4005095000f104503600907800ca91071103188400200042d00f8919100700d420060380d400900010348034103a4002ca8130030789084060b100349541c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 607803812 1250 607802562 607802579
    0xe0c0d0503030108100c021005040204060b0403150e031303260a02010e07140d020415170303041205270a090e010c1206080a02060304140703080306040507020d02070b211f 75
    0x10303005483c00584c100072169088d9010702e80c02503500500003030010602942c0c03940d03400743c50381c05600300b40c82e190b203c0900e01103008164094041a0f10382c2c803000310302e000d800003200b100741841d030f01000700340c491030104000c040c0d184218030303c40385042200420f81c4c1c5c170444440a03000b844100d0000101c0c1c0190340000600c051702c80155005644060040c0c880301907960708210042065000400d070746190000d0208210301100754000703512480b000103695030709190a00d00a003803500b01c3e4410410104001d4010380b08800182030f19101460038038003103d00240e030300103060640d168001810312440c003803080c1c84c20f0b1815001041040a59100c103142c00021040d582c0070b407803103030140c0686603000114490040c00c0080085074440d02030380001c040c0c5e00780740d0703207a82c10040540d0040c0c3e9401804418081030340341c580715458000b111800100341035100e400d0003030744442e61072049203610320b0301094000e40400c8d41071b061500305d50300d118a000c03580382c0002440b0b00e030440140607810a010041e0003044516 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 607805062 1250 607803812 607803821
    0x110904260d0b0a2304062303061b0d110913060f08030c03180307120b10081501030b220c060201052202060a09081501080c0a0b09040e0c0d050303010810 67
    0x340343d42c1e01000c0c4c405410006a04481e0129001030f0010350300e01d00001e00c42c407200c600413245041d25562404601c0320340100351404a02030703c0c6010007114603110b068102d01d03240450b8811005810041341c81d079201ca034030800c94040c030b22600b40c100c5d11034030b50103080702c0c02c940c000d0060b41c1c0c2808024100f02d8032044015134a0198100c5c184180d0300400000e21400c0880c1d4071204650740c0181100c5600d919040310300c080340e0010b0002c540c0d1980300000d10503e803031010900c80181190b0002462035200f0082d00600c004070610014203080202404181881e440e440b4140c11511000f04c0c0c1d50040704940384c44440c0d480380e485000010351920b0003059000941081d0946000031400340e07083d080300b43d5004c01c019135010800340410b12030386500029038048180500300502105240c1c0d0030242d850060b13150300f4a050405018490202014107000c580540416514455803d03540065030220f8490b40a10340384a28841d20b600500200740d00701044400002103046e01c0c16181680d0003014500c00309030a48 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 607806312 1250 607805062 607805069
    0x405090f070b070201081f03050307030306060e1f0c0312142d220b01120c0503120d09020d020402030108030705010b030a030f0c05070506030c180d110904260d0b0a 72
    0x6e001c030008544617a031100f0041d40304440101c4000240c0740d80c1d58542d880c5501c4400203c000c0b80d11000304000090300f12030000c4180340191440f05c04100080c101072080f402041103141440005030b00c0906043c8902c00c0c40c15880b41c1040100002491040440c151250488248a04400c1d0410142e00c2001001034100d00500ca41d40f4005030791244907125a50f40c650b4500040890b820503000c20215420b800c619000b40181110f00c0450611410031150003001c642080e4000e41c00000c0c003a03c141214003c491014501c0c0b40009004c41031071000464420100070702170340c428004400400c85c0280480241a058440c2000b0400c40c007604040c10303201c8485d0100500451502c8481008040c020304051039228840c1e0240c6da2070030788a000280d2141c10540c1c0304100c4010118291411a080701e00820b5042000c031203c0761201050354480c0d010301040c00c01d05004039800000300e81000401e10801803411000910141c0030803200030420a075811140d804a142410080342800900b4140c0079001035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 607807562 1250 607806312 607806317
    0x130203100b03010f0e1507020c0a260706080a0b180c091f02030f09180403020c10110304062601091b0507110103020318251a09010c0c03020405090f070b070201 70
    0x21b0300c1c4a40700c80b20310340102640c040d4002d010000c41c04d80e035034481000c068417100c40b900c0e20ba0301440895410100c070081400541c3c2d40070003402c2c0406500070300e0040c0c0c48402a0340c0404d85201c2400424040001c00b0340740402c441c03001007402740c0344415402800b1000c3e03040c2e48440d1445582c0c600310950740c010320103a0015802c100040c45400c01e4840050502180281c6150b140310141524030b0b0140344211030a80040e04200c0c00034005181039000c0b6a803c40d018588100010310100d0507503180d100e1440f401e8188216060054104821716039000655042c14191072455a07440150344044c000b05e00c04806800d41c5520000d241e1800313034050f201241d1f0410208a80403440d600190000d620151010844804c402e60512107500100080d095100c40109100031907085948140c031a00c004d030300840024180c14940c04050403840c404d49040d4a42403822030f500c040700703081c42c000258280d013001c1c0d0803030704040401c20300d481c0010b5a0b5590000c1103089440050b40c4021503003190040f588003e00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 607808812 1250 607807562 607807573
    0xf010c09031509020f12010e0c06042103030608070e06030c04050c031810180606051f0305041716020109060509010c0f0819091410080708130203100b03010f0e 70
    0x268450ba69000110052000d0b00c4100c00402d01000110f50700c07600710380002c50703030745461513a801e0b00810f002c8207414906c140d030b02c541041d060000300d04800d202c2e4040402c08a4100c0002800d140c42134101800900003076040c3c2e031405442e034030107041c1a5800c482c168002d2149041e04003007400c0c01e1080314030139080e001d0814215120303410100004000d803070707055004d40303e0011919214032162007502c401d46070b4034803648401451443c000090b200141d01031442985001450f18010b2144e4210071031880e50b600c0d0006450740c40e0300e0548440540107001180789180800c0c0c00f1640d010b80108010100c3c000d89961050545d946021280c81c0304032a107060010f03038000b038040001000f00e04400304c404e106810140c180005280c510049c07005030184140061201101001031003d00344014501c202c0c00c0d124244140c60121015240e40809442e840402c014000055144540b440b54180042c0e401802d4490382400c0c040c03a507014050010b2064803d5203402e00012101d5100c2c45a60f402e2000e4902504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 607810062 1250 607808812 607808843
    0x9270906161b021002010c140f0f0a050c1204090f0510090f110a0c0b0709030803070c0222020a090e040c05010e13060e010f081b09070c02120f010c0903 67
    0x341d03212014484240b0b1201501998401a900c4000d1540e13900542d0b07000199810340e0b00e000402544001104c840c401d80100200da140d102e0701c404031810041c0f0302041c3c0e5642c1414020413121417207018402da80c0e070302031480070311614500a0300078021141c00c01010310180c80c5e01c101c880d007180c009543c1c0340380d0b85918400801c0800401d03000892884092040059868440040031000b5884000341c900001c840b08003410800243c10304a64200c96149030413036145046a445840906c00a8141000e000d155600c0000719500d0b400f40c0c00301d50288840d80b82d039404200041c0000794100e1510301021401e01d160220f8a0122203040e244201e03006208040c5044c0381000650310410590300c01c82e001508826076986032441806210700821010300c01f40002d45c504083d4045409554000740c03410b4109441001a21003640c4003808410404c55540d0425222040c1c06c0c0d440c850002c01c004c1d00302220903c1030020540107c0c5140501c2100002030040c01f104403421600c82c03d907408020318000c038100c1c415 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 607811312 1250 607810062 607810067
    0x80402013f020418051e040c0603110d0c170912041205010b0d0c090b01050a0518041b020313080706090308030a020904020705030306191a0903030927090616 69
    0x1d415480c0c1d4070401880e0a03101c8130b0303004140c3c48004101d0f00081d180c40503c40380d44081c403900e0040c250b46103c406542e007045d94482c0541800381c42020109512813a01140c0c04c00e50004840d000640c2001c10007200c840c0650140c403059014145d04403d15034000020002e4001094480d005144068403e14281c1070401e2188c8514900d039094401e9036030383c0254230311516066064600c1c0742c003590311100c0840c034044485080d11800b9038030034100078090015a0320507800c4000e40b201c84109864200100340400042070080c111400d00745c4001a140c043c6182c0260003000621240c0400c040c2d0040c0e203601d03a0080c0382d42d900c89100b02030029421120810204904034091034001d900030602510b010700710300004041c1d8100d000305850070380000040c000c06107800042404200c0026200c60850740c500204070800842d2000080c0b040b1000091024582d40d00b402140c00507030780140901e12141e8420321007503d00b05403003225228922081c010a01e03656000501b203206084199001c5402c030340c202c004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 607812562 1250 607811312 607811417
    0x160303090606050306040b040501200724020313021809030f03100e042004050402030304140105072a060e030a060902010e090106050327150c1908040201 67
    0x35240755a8070079003c1070580e0248150350245004034a540d01d07034109420b00e00d003140c80205201c00f0804841a2286030040d2010950b0b100c590032442c40302c4001c03003804840e06201c074070055a150041c400400c116240d5002502503c8150080e00d06400c4e4060360b03007130000c0000007a65040450740c418448000064030740402913034080d411082082115554886035020303058295401c503217041c0f00d0403050390b4a0340441c80d05411044d0440342032009007051780200b40c90744200d000310106001903141c08078899025000b1214030690060181e0b40c58034202c29000c141c00c140108017503510440020001e0960700c038118440101c00020090500f904590303407400024145da8408a05205200d085003545540d007858090003003400d80c680702c2c0e40349014804200e006030b40031140895015400c0c60804103410000f400807d040107150030507141d4441c441d802c030030b601481840c11311880300b01d030b8180511580000314602482c400e032242210035145064200d0000c01007005e02d0204c010070b0008030314041c1c000b2107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 607813812 1250 607812562 607812581
    0x6070209180709050a051e010b0c010b1f0315320d030309050c1008010e0c0c03040311090a110a0e1c0c0311030303010b040612020d050703090611160303 67
    0x60a03000d151092001c0d5041c254582d10030061255101d0800c50041c40c030b409560703070000c240c50552000d50881145480c5400040c02000b4031517801144201041509621807140c00c20001e280d40390220710740c45407510815910b100c080000c1d080000985251620b681e00341c00f03648902d11800304081c003d64094400c3e4030803902c2e400b580910581d012486450305a00000010301940e0081400e0001d400c00515200d0040c25039400f60480480305214a03070320400e03aa065900c0900a031403a0346410140c0300c014022042060341e140000139000040100000362042c101205452000040e0340b142e22400c01c4034070605c006c49030410108092501039102e82000c41da0540002c0035074080005000800480c1c182200003140c00c58204001803007030041741c848034107617110200c008614543c1044202d0483e4000c9105442c00d201ca01d80010400b010242c040c0d072198082e00804200d245040f081c003c0c041c004218095420b54a0b200d4400040c50440c81150581d4001c0311501586800c207540440c003c005049 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 607815062 1250 607813812 607813831
    0xc0b0c0a0314130603020903150105010c080315120a060b010c11040902130f0e1002160215071a0f06030d1d0d05060403050702090a15141305012301080606070209 71
    0xe0849031a90f6007410001405881d40d00580740d441c881c1c24103141500303a0901c402d5a9120000400c41c40e84e000c4419603105034001c0728aa01c9440300311154003154507507600340d5404816100381215a460000d00e03490024041c210078401110350300c0054503910f4520301d020b000d040503890f400c1c52506003070708032055041c03010f017683c00d42200a00000046848040c00c0c03002c0c843d1141c40c04c4da07440b10104458130ba01e0718500d1003186010110010349804000d05a802809403003081c40006d034541ca010706949445411000d07a0b5840200207200701100304040315400305407014000071489a060004418158020316111400e401d181181c180c0006070355040e40d1988043c81c0e03840b803c0000e03000d102c101d00440c0f103070b10340584951807881084000f19005000d403403002d19041c0040340d0394403014413060407240011201000030041f400031645211041c602d06030042c1c2040c00029019548800020100400c016560014022003004442450003075071380e294015400d200c0c5101501d0301400030b0742c1107804203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 607816312 1250 607815062 607815067
    0x806010b210702010f0606030501050a1712191d030a14210c01110c070306050a14070903030e15192a06060b0c4201030c0b0c0a0314 58
    0x3654002005070302222840e00503511440c0540c1e8103a030501034031003d482e05040c00d008543c140004a1002201e5204440031000014940503000b10244201c40700c030641c038000f00da0354021619010242e01c100340382c803900042c5010210000000450100340b18010000e0280c00282d0321a1150303002c140403605075081e2805120a105488203e50116a005000d05143c840d101c80c1035201240c215401d01441c17a80d0800200017880b080900402c0351000d495100c280020180c5410500b60000c250104164407600c2126080c0036035150000c03400c00c103e92007540c915100708000801d20070002c809400c0c0b80d2104500f8080c0200b41c83d180c0001e01e81c0c0c180700d85400c170340c0203258010484000381c0640314250b800c5482070120090043c18000c04010b03110a8030154034044054a0255641f2540401d40c42d101c24103102c48000041c0100e40301c5101d00c2c00985840c4544402603040e41240d40a1108403a003029042c00010b01c96a01000d0b546c40c4602c5a019102c040980d440603500d4440701e09444100c803004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 607817562 1250 607816312 607816357
    0x80f070c080703300e0c0103050405030a120207080c0105160513030b13020424050f0a05190b0301090e0c18220b24090103110103180206040b03060a0f0806010b 70
    0x81110090612100c1310010901c44030b03620f10207080070340c0070084070304050400c4c1c1040081070b00003048917030043d0700e8a84070b218640034a030b64100901030b80200421000c000078410b40d403240150403e50203100590b4030503220301d0b20807000761401d1040b41c1d028400f180c3c0c0000108080f4011440a551140307295480c800034207040d500280446030480044400384400f088011191007205c06802c000c2c0030182c4402c5400042000000c034400360911500d4401c0c01065140816003245184900003050403000b4140c41e56100c14032070000e0b090b0700e00003580710b22452082d40402d2401107200051070ba03a80111054544451040345404003042c5030f040c600c0451840c4140000e841807260303611602450711a42c000d1514a440f00650b500200d420a1081c4000c80040c00031440d04030b411100c3c00c2d400d00f000034214010300781c40041c54000107006903001002050000c0c0c03011800d001148a41412030340480465190740d018500d10f5030130701030203000350710020060102c5040380b00100741511042c1c9064184140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 607818812 1250 607817562 607817627
    0x905030d0216051e1f020702040614040f06030f0303090314070606030b090f07090e0f01110a0e03030f120a1b12050121080f0408030307080f070c080703 67
    0x111001111102d007100126005201d402d00c2240241a0800505a01e1503004000c240d644c08501d04c03080c20038086148101200203d95049441403513000d00f00340501c85d96800c410840c0e080c682c0f80680102d040080081c42c0c4c82e503612171070050302d501840c0820850b8068a048004004101c4100e080c00b54038007220b45c258210102130440c40d4800c45010030a141540b0303040c0c5003007402804149481c0c1c40001406840b990100b90748040e109182c80010b05103255442d40f62070110341d001a030415518250316401c065280a00428402c005a214504040e0b00041410307640d20440d807a81d06408800d0001001da2090381040c0350300851402c2d004184418412245130301c1c0720030300c0221000b0036441080030400a01d03602030203004050215206a603104502c02400e0b00882c4210b00401d00d44001900d4a00d89050000341c0f8041d104040480351a4130b070984015005007416100b041d4601d62003000200424441c2d80b0303065075a513000f402c082c1081200c1d40e040c0d4841801e101604ca1010b505440e1800b50070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 607820062 1250 607818812 607818817
    0xf18060c122c0a05010503060d02041e060b0d15080a0f020a031203200301150806030724120c05160203010b060a021e0105040515041104020a0e10210905030d02 70
    0x52121181512403105003c1080304420b540c02241800f600b0700400c22155604004514195016540400e0389a5202141e41002e00d05121180b8611328010000c510703500e501000e0500052220410030800130b004c5681c490541c030a1160302500d81c4103414140020318440d554588203032000c4c12200820781c4a030f031100040f2000d1034080300000d03610302c0d0440c407080c0f00c40c0641c1da003440c2168425185504146218040c500150320040901c0440000f00b41b01d42c80811605c0002c0c81d00282181240240700c05940300c285140c2c035640c2c006042e004031119030710f40911820300c00b4a2251162442d100303050881003408180048140d07410b5583d0648075149446440c01003111109550281c0030000f008410100300643d200020031850703160008000000358006010850756006444010b680c0d540c42c5048000c08480c0b000035a002070000c141c800d0030035008044421075004c105d503240700000c4d44200866200d800000f144850707185103280038045103200d610031285980160260782c5007000907204102039a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 607821312 1250 607820062 607820117
    0x50c101406030d1103190507050a0506040210032306120106080709140c03010e1305010903170f2e03020a0e040507060914101e0f18060c12 61
    0x340c01031040244500e4140f00c6280d202c801420001a48821202201d03030301d0007030791844a4290300300e071611041c10f805002980ca086900c00b040303e0005946203081e6848941c181c8080340200400c54400195500900903100995001d80d0044c0d1458980b58217080d8000b030141c070300d86d0080b40e101450713601c820081c003586001d0002003000340382c014030b426a28811117407054a01a00401a007041c080d02c009880101c82c11101d104020b001c1d81d46030741401800c400c42807100140598a0050b10804054000000c280c0001c40001b00103155915036144070340d4050102c6110038409001035402c00208c105410404c2c850401610121480b5103e602003005901c454010003e140791060401c01049000c0150801511243c40e106c80030a02d800c40469418240d440203900c00d0b1940c44607002c00e41d118a519030782450844298103d4050500805410030034408000000134940c00e04469400440803e0401124002c0c0d441c102001c0580d212401c0044074414900c0401803201d100500454551000701004d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 607822562 1250 607821312 607821341
    0x5010c0e0315070e010c1a0f0604090f0b040228080610060e12010e07090204031104020a0c03080408090a090b0405090106060512090705121f14040605090705040e0c030115050d03050c10 81
    0x48c140102c8840c5014001000e5922803818500c00c100019441d6000f40356007940210346030401d845510004100041c42421000a10003081a4010282280100380d0481d6020742c140e80302900c41d000146503149041c05000e004c9a060714203400070b42400e400c0380c140c10111728000600f0492145d0418144142c0c2d0380300c1c82c40300380c02040038001e01980381003400c0d016000321030861034600d001c40060040e10920300003078107003e00d8000003020310002c2070032107400d90001401540a1a114103248005101c11030101c1d01407072401000030380448051080c0016035510f0344a442c103044404214074500c6400401c41c03c8280600300d07000419843e040e03140c07094030041102505002a194505460f10044589090340150500d050482002c0c002c800307a5411070740041c4041059612551a246000b00303641c00303550018908001111290b2000c00c1081150104030300a0000c1c1c442400581d40c60310b000e008003680b00c6c020800740000a8041c1008040b40419041034441e107841e40aa20382c01c588051010070003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 607823812 1250 607822562 607822613
    0x90c06020706021204080c27040b0118060501200f0609150a020301122d0b090c04020711040b19082d0a031206030c0305010c0e0315070e010c 62
    0x80c81d40c050040741c3e01a1003c8907014145441d00c14919507e003501819203020380e80340da00c1001030f21030300c0520400142034001d41e08040c1c2460f191030190403030700b485416090103600c05c0460301c82107203015020850b40141e4402e140d0700c2204444100d1100e03007011100a6110702400221000c2d01840098824a00c560240071040207504d02c520107500b000b4101450140304200501c2245800749051482c140c1002c044245860042c6c0e490440c079203414030085840c0322040045040040e00c09410344100030b40c405581003440c251091005a01410200400c00e004c01540c0002d02c0c205030348038541d1100000c0c0703580d048001204440150360080e400c034030345030740181e19502c060200c825200401e0120f03605c0000c00c00004e0045440c0c503003131810001030401c08160550214424a070304003402550700001002c0c0c0103540c80c80c040d0b0003040c900c050751000c102c0900c00008580b5000c1030040000005400030141c5a44041003121032201c803084640c180008a2000d4010542e200c400180446010048aa = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 607825062 1250 607823812 607823819
    0xa0b22061802030111160321020c07150c020a0b090f0d030c0507140d0b0c22290f03061512040308060f060706020f0c0f1b1e13090c060207 61
    0x600b5101002c1490607005c40401607050690f1540b10500c00094051a140c5212070b107620210405546a44064550324008240301160100c0400d444049480d9610705910a28800308203032029414108040d50010f48a282003040c196184d0040c154428014501d200445c609030010350940303c0548150700043c4c5004101301002020441c000191101c00704110040301408002a481805000010145030442010904010256013960b0b040400c20400e9064803414020100d1030b518079201e8040c204450720380c409e4045000d140c0504850700100c032074919200c40126150801d500c00360405030092000c40600110000240103400e15058003040440c00341045d0900520620f00a0805032045200058000c034990b50041190705069000b00c0258031102d504c0c107043c050303005440c50300740e4038000c0c02090700d482034022600000311000b1512144401103204144040b54013401056903003540c15071040707a11481c11514111000d4203180f00031803c2d826a9403514100d116681c48178015a012003000e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 607826312 1250 607825062 607825069
    0xc060a090e0a1104055b0207030f03050c1b0906030f100903030b09010b040f09050412140919050102011d0d0f0203161a090a0b22061802 60
    0x980001103040248004020043c1900c82403180c0d11407a0300c9011540c0010840c00414600d050041200c0c0b01d103611400001c544040d14400d0160071001c0e480c80c902544c03a108031010a15589142c0507030300034290b80e4255603413941c600d001c0e0034007074060001c11310030120216400c008589a0141001d40c000041141c4400d100701c010005d0aa01c1c8240c000380b405050000b00064405040182d42c4000f02e810b4030942800d50081c0341d0f11036480d80000c050000858242d9211004104031416414034010080c3ea85540c081180c0007590b00800388480d0046100250b03200c1e40e00b41d100345031454a158500102000014204ca0409800c1002403000d100100415a02031203299010940c0c112001520004021131a444030100b40304c64007403127a02c8c803145002c1ea00c00c0081e07e001501e441450448811f075400d142c42000c5071a60070b000c10a5246c000101c0c04817022416407082680500c4d034401a03107402c5c0350801411032a101200d800000c640e0640049110390281001c102c943c400f2a804022a50061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 607827562 1250 607826312 607826339
    0x40906050103060821031902071a180d030213050607050705011d0f04090303060509070504240c0b06030c03240105060715090303020706050a0b03060907180e0c060a09 73
    0x40c0c0c41940100502104101e480d034900b404429440142c0e958a6441d00c0c92601e03103040f032406c4a0314072440420076108002c0e02b500c003030300007051030410910666100000090f10003080b54145241d50004084001a00d0080d00640070300d101a040c1c00d05c1054442000c03132141d0700151020349060740003450030002541c00103280c480031292038654440c00c0e080140429030a207480e1494070301483d40c4044103400e1602c00da2080c00501001400c0050f0b40c1007100e40202035070064041d04a030344420b00c4203c11160041410802e00340d40c59260010032602a486901f10700c03000074101905400750003080420b1ba5401d2201e4222001c10b00c20221030480c1c030404581d001c0790160030850107560100602e902050405038040221501c03201e000c02c0e45003031864110003a004044000f4201e40c1460184803442e0900e4201800c084016411558181d4901c0400c42c0d442184d84102c1031909503560740440020051b030442e442c0100c2132011244014007100c04980740e0780c8803208803000184928820710005141c03400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 607828812 1250 607827562 607827569
    0x9050d120305150d0206090303040e040b040506010b1c02030604140702030a0905100c12030605040f020903210a030b0d0b0408040f0b040e010e070c020a09051e040b0103080a0507050304090605010306 87
    0x450065050032840420481c0700e131031801a11400001c01c103145166001c00855002d4010b080900c45642414500701c00409019a0211403c0c002c480000c644c0484000c00d840140350740c001c1800000006101d51030080d80082c25068119032a243c0c1c030000c3e525124000c40c05100680e0080d581d4040303480f402040c5904941100b8450842c4110008920794820910584d03141c0084100031b40c4015090b0a50081c8915405150001e040c0000ca030615030540e4080d001c45141036040d07880400000260301c1c0d01084405d43c90142010612005105070300c294480c410707040000e4410b0921500f56180c001c143c1200b00e40446842c00000b0701030204c6000749240d1001030103104034480c209804e180710072550300c4050140039111142c040003e03001c0c42c418002c80543e550081d044082d125122a100805401b044442c0007500d038440108106142850240510490704170140c1c210076400d5580e4410194041d640390810844144420804500c040c00140001e00a00700005001c920309000501603810aa0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 607830062 1250 607828812 607828831
    0x4050f01141603240f0e0601052a030403051902121f02030601090b0a02070303090501090e040b09150703060e01090903080f04080c0d0518040510031209050d120305 72
    0x1024410030320141c005010400c02c103401d0116400c60f5500c0d007030b04101e41501d0603480d40804094001040c21040b0350701c0003618210b03140c290fa2030392140300660f0b161203110003900a0120700100606200f403035003800c02441d02114103603071405640e9180c03180b070551a1085000c0b0b94280361108000c501e801120016030203441c801901c0c2c5281c1c400d0031500f20303031074a400c00440c4036000400070b56260300c214481405841343c844000d4035915000c8000356103004900044011808565000c21958002c10740790046070840002e101e11552541d4030149000c9002e0450342d00f911518224440c118850615103200340500e40d80082c0700752a22500b940309100691008000e903152107001c001090f800710005501034036220006409407a1403400c100d0714442d020070b0665600843c82400503096110b4002e08603020121400d1401061171030820040711002e880403407461403c141304000140911b280d01c01c15402a0500411032680c4e000400c4042e00681811100d10441c0300e06105640d4142c811181c00c0522031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 607831312 1250 607830062 607830101
    0x5060a1d0901121104110301030803040c090209030d1803060615021009020f0d11220e03040b0a120902031c1101090323040305160302011b020303120402120604050f01 73
    0x80308004111207203000030303051307080300f0403851415100c40d00306d14404903030b80c0002c0d81c0d40d40c0e490500c0195500151422108101c24010000d9100c1c0c0b14000d480c2907020040103803900350305624007034a42c0c0d80d079054664003500001c0720000104d40c45228840c002c0000f15140008020242d0009040c00140c804021200d0700e820072900c0580ca403510650454002500c0c8121205440c2c24180b000520350701e4165402551041c2c0710612000c910055004c030f0b45070200500044101d15445605d07401075000d840c038000020f1080e10341180c461990044c0000c140707100000e11320060f4010900f841390b5020810307180783c00035030310b0000981d102c2c0d003029070340905400801c20011160380007429038a80c0c500344039184c401907481004d01030301c140c02c84000303540c03050031a0094403100e1055240d0012620003039021076080c4c40c94070201281d0406055480f41c0c0180035500d00000f500710b101040350080d00030f9801000140f440301c048a4100000d9020300e000710300600b8440e07090164a800d40d040350390364044940e50f1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 607832562 1250 607831312 607831319
    0x1d131b17010e04030c05010f02210105060703031503060e0318011d040c120e0a0b010e191d0a061e091703040317071806030204060807110705060a1d0901 67
    0x4226a2030641d20050080c141ca40c850b404d04858079681c1300c401508075480e0a01e086510441c9074010010502d4644082d5540307070143c0340319940030000740b03c1c05d50401e104005110000340f19511510001c1c0d1001c10360b0b0150340c1c403600c1d8502110440e0021f08095400080d042165440064103290010000d10700701c07010f026a80c0190440c40030304400710b0b020b00e071107980c505511801040150003218580c202002560b46c092a210f82e80c80789a5015140e030350030500085084561580e0040c8541440d01c440398079054003001140040485142011103414007552103441d2950920019200b07030f0107140049100701250340d4514820200000c5103881500d441c000200052101494005024000810984aa5070350030140c034065420f0300b20405040c100b100300b000392034002c0c501c0d40200c4500070f02d503181e40e80c903100d0581c200d02c110b0190074003141d1840e0028400c039101c2c5010a442c40300c41c40a5610403691440403030642c0d0003400d200303008a0103144100100044044d50383d21310750011100c0b00760a525 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 607833812 1250 607832562 607832597
    0x219030f2a020d06110c070509010b0306060304110f121e190602250b011401020105070c020d020a0e0a09060b240d0e1519060f061d131b 60
    0x441d09000340183e54550108050102c1c0394081c82d90031808200c0f0b01d81d2103145400c10794a44080c2e0007154450801d0f1400420386810460030349104960282840b4a9038656480e046000004182c01c1fa038404002c1c011480e084d124600030100340c0003c00c004010003804083d4141401c1d143e5403002015034000f401303805a0158501344d548845410030170050361000d02ca0340c021200c0011250540e4901d0f500419203040004802015040741e000c0d1010750b05d00e4481b80012400d0712815501d590014182c3c0c1000009860046040c050341c920040040200c10740d02c1d080d07c142803504641e000c071807580d50b41c1000e0600c08280a0344c40034a00843d0205c5a400d00380d000100700318038203411500c04a101140b04030701070b10258068503440d40f00350200d9860040025480840c00421115150025080240038008180070f000701e805860101d90300d06c50083c10010100c1b803081c1c0b1a030750003580141403c6030805907199000001840d40714194042407400f03a480019201c0b08000a001c000c01601c580310000054 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 607835062 1250 607833812 607833887
    0x2a08070e01021c03060302040c05030712020408071a0c1b0a0f0f060f091a070c0b0a120b0109030606120210110604060b0406050603100807050a030b0f070219030f 71
    0x2482c503800c3c14148808903000c40c01006076400082d080380c9084015010b4030b40000141d84250388580e5401e6101680e644400141c0c0201c0c810b0094582c04000d0a004250840300450380012003060618140820380181a24000f0500c600306200c040b0b050702c0c0d50050800e111160058115001c2000b40185805401c5c01c0f05c002c14824102041600d0400c0c5160a104028401c028140c0d000b0804c4c00003c04402c0300d90b50342c080201101c8800c880c44c40042c2d100034607000c2c2d4041d030045440d040710920780d418040d4040c1151000d10350410210300c2011000800034803800006c0d11100c0020200659140306014242800702100414000e0f424880a0841d00004015030301645c088408610030414801140c00340c211600a654050404800c200071042000003d4049030301c1002200e11740c60791442800407030012800040c00080304440040c104c0c0d84c5820079550071070440c0c81110309025114818003011100d8010480000341c0031850310000951003054038240c0030100c81806100031800c9030078400720 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 607836312 1250 607835062 607835083
    0x1703130509070c080a02031206040c020c150412030207170a0c18110a02010507200d140c060106050a0e0405060d0b1b0d0608060c09090c0d2a08070e0102 67
    0xc41c0e41000081c51103204036440c0400f5a4040021905ea01814101079104d404c200040c03849210400006181c520b86409144503415180d000380290900f08001d00503440360302404070f40c080f80c00b0040080c0800e031401203918400d001e41c0c0585100d505280c64505a0f0840f0321188034a81d001e00401301c04600c0d042c20200c02c03500855035803044a0360b08590103010341421136001c84400e6010440d10445901034101c0b62103880d0954400c0b41e03071440500c0a044d40341c001d0710b140d5503952003480c1100825020712041810b0822404c00f40b4109080b4003203075450400700340c011a0004001117541d00e1500d800000504400b50104c2c2c0c00d005c07500d41080030505015000402400c10350603240400c04d0410400e0401207180e0fa842062652010080701c01030182042d4450090b0a00c00c01001401140c0c040040e034074040c1e03009101704290745030800d10a80300d400121300560003503a2800050720745203403208003861928205407030200210000102400144005280700144440c0304845070081e0703400714010000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 607837562 1250 607836312 607836319
    0x602100b1809120316082a070204020714030723060417070221150606071101050d020a172206020a0e0604080312010609030c06050703170f0117031305 66
    0x80c1d54902d40d04520301140c580030465a4100001842030100c40c92601600c4405942c03158011500c500d402c0c0084004040705600364118a42098600c0c0a098401841c03014002000981040c1c0310313884103940340b80758558128440d440000c3c2d070010020055044a00b08042c40c6112060034200f046e00f0f521910000c0005004018100361004039020400527685c240d90094182442000d0340f12803a00c890719a031084e41036034410810f00e0342d03850100843c0345200e064050305c40b904001c3d5035071b180c00c090095503425a06200003845000c0c040106807001e0044980d1950710007181c696200304d0034803200005890030b8140c20300180152995407400601d55a036607030050f40103035224070040e01254444140801150300c40000140065141c0c400170161401283c80d20784a56541d82c4e43e503094030320084610009001e9104c502003040303860300910207810054003a061241203034068508080c0088000c50b8202056003814005000074240c2180c207021008000e0021031420320003201544519a051240340d21 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 607838812 1250 607837562 607837609
    0x60e0a050f0109051e090c04140d020d05011e0f020915032a09100309031719090506040c0e10060810051513050303030712180515011505030103030504150e1003060602100b 75
    0x21900c030031833a8003110703402600803c02900806002c03030b02c4105071200c13038800c20b081c0107a00c0301c02c000501c00c440381d10b60010a6036036402180d80b03a09038240c00003000844100440c51524904036544200141c02c035041c81201c42d1754a411208002d006140c19000341c08051410304d901000a80001c980c0400074101c135110742240d901c10702c1ca48c844c0f40b107882d0559442410004800c04204c000943c0a004a10a0091811a40d10303045541644842233602000301c45551030304020309400303054140e40203040a156186101d4460300819850030f400ba048640300c1400107141c200b00204c0c880180040c2400301d01440c5907003000c80000b0040824082d41018044d0358003450702100d18080c1500c41e140d40d0080c1a210720b118417070080300c6540da00b4414880c1c940032400f100700c12248610102c0741071325456100e440c18a0700700720340303010414800c808400a100c0c8010400c1d5040d5528544d9000b10039581e9004148541000b00084c00c2c155507058040f14241004c907408850f85d40d9084440403407020146421 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 607840062 1250 607838812 607838839
    0x10501030f090602040b04050f09060a030b0406151d160807030b12100516030b0120190506101707050103021c0f0c0801060e0a050f0109051e090c0414 66
    0x5000b0008810300400c0d551000800013113040314000a041205c10494809072455100790900c4140070046940960202c1e0495041c0002119010b040d0b0b0014000d1030006495000311909500310b4400750010691501c0d00c0800400d00200710500541c00340714141194810014040041e014800280518040c1034407250504d0f502e0f03c6890241140c444880100d0b400700c0076180445006260549411103441c02d048218411280030f801000710241043c2e503220301c0312050740b18941d201085584035040c60700500c5e40144170000d9541008051078007450103070131281051003841144484070742c80a148100601c00900f0110b40104100741111803e00300517076603400d00d00d841280c128004900d0741650303240401540203000780f6031000c0000450fa855030440c42e601d541c01600c402401641c026800901440e0502090400c40501101c240d4181040030081b03458100040d400809400304c2c40d41b01c0d400c0c2c40b516516140c40b00407203400038800c00740b030703450030b82481100c3e14202206100c590203040c0350054031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 607841312 1250 607840062 607840091
    0x16030c1d010203130b0c010c17011a070605090c0415050d12090519090f0605090a0e030c0a21051c0c0905042909060607020d0203010b1c0c0f030b01050103 68
    0xc0741540d07144000b0340c00c19130301c884441c00310303403c0002c10b81b41c0756203415004901c6502440c00c1701c9402e80d140c03210010303503864900d00d40c0781c0e660098610b807080e04080c4180c0000810900a29018000c4003000c0c21403004000284011500c4090101c1304c101d00010042080391941c900030440c50380c01c4101d150301d107869903005507440e02c4070764002c1e60801c000440796000740c0180c60010083d00d044100620020460400d1002599154082ca5600c8070180000c518044600e40c04a0740d40740c0d00700700b80c038144101c881409041003494542a9541e0304440c00300d11107103070f0f512080c0385400000d00380035044c00b03148800264040901c135500503184ea907601070b070304040e0f000328a007000500c1c1c010810b010301203140c0120285007842090b503251140920307242c0507040c03402c481214070404020b0b2040741002083d03000c2000b1840c0042041c0d0f015561042c85e00d03244d0310307003070402d11400c09204007240d1040414035044980c4100f0744d000c1e409400724100c0130f000241c000000300741120b00918000c200300802c0030342c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 607842562 1250 607841312 607841317
    0x714040e030c06130c060f05090d0314031f090515120f07090903121e09021302030406150e040312050702150412030c0203090d030305100906080616030c1d010203 71
    0x10301e859441501c2c1009082801d650290304c43d5440b801d011600d03555501819074000c0c5580c035030600440d205110801e01c50400312240174149001380f40446070020400340e04c910a51081e2103842c425810480c910100c1400c402c00400104030f040780c100498a8080d0700e040e0130311001c821062145160740c2c01c0302c0710014200440400404080141c500c007543d9000380000070505044120081241300e0780400c1c880765907110300c206000508030240400b03041900400014440c042080741c0c0800c100c02520400541440074510031807003251300060184c115901402031604541c00030415166040130040000d60041c06920940e27680100403e80b5101d1100c281c0c18078250345000c0030000358503003c000501141450407071000d6134640b810020038001c8a01207841c0d1041400d0075400a280c0c1d81d0350000240701c0c0e805207078008174203140c115009441d1009402030342e5a0350b00540c065070202d02030025600e0b5420041d1104421410b08000600d141c881c01f82c810030704100d4069900c80044441c50b10b40c0d009008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 607843812 1250 607842562 607842577
    0x902031c0f0306080a12080711010911030c0603010605040e0c0d15030b0c0f03010b0c031e12070c050c300a12050f1e1c0b0f030714040e03 61
    0x38588a00308140003071000c02060207040020303080030300004807510081601201e254125901705015080c2c804150b6014001401b04001c00c00170308041c19800500303104103414140300300640c0c1c41440407042018681680440e00900c244010001008075582140466040b51828100a400da9580c903007003004500070009401005410030713900c183e0b10f01a02c0c281c68142d9101d0302d009585500d0712000100a801a001c880d171038000308000510002d507142028011003502002100d00c1c0200b064261481040440301c580300c03400000c0343c00417804c0108645543e01c000f851070f000c81520055202d05948010002d01240038403444207034070f5107110034854015100310910100004086030040e800d54bd40e10055070a50324400d242082c024070034419000c0b1040202e00d1b200450400c0789840301d4110010b28408143c2001c042042910500d40d070360300d004441a14200d50000d0044d000f4014021003c1c1000c1c071140c880d812440d420301503101031040710b0301510405d0360b0000d809244440c01d54654400d418 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 607845062 1250 607843812 607843843
    0xa0f05010917130801021603110a0804080601090b040507050d0504060b090c13140603340f0f02070501050a030b010c020315190504020d0b09010f0515030106061404030204090203 78
    0xc52264004545a000b02641001c1c0358090003d169140c1c0c5040c03c0703016000749502100803482a000c0440e2044910b900c664540320165085944259141c10096000364007102075a08848010010f0482c0e602c1260740940e800e0fa42400345180c585402006446404040002d0369a1030010605104103a403200ca55004c000d400a00a030030070803a55012508110480c0d0245d010110b00800d0901107840c0703501c044100030f0030315401c5d80c45021014003410480b50000c0840008007055503c46e070003165120843d4803058840c09418903107048010002c0402c2040c000642d4003044081000b664030000f02c13101e90702140b400040404510300100c031180717180341700a503252040b1000001a501d000301e00c1070194220180b802e2280400150400695030112400796000811070304032004601080f44082c0d1001d40840002120400d10118104594013036628155001d50300c082160142824441c81002d0f141a0408100010000986417650720941c0002401580c0350001d040071902c0030010901c0150200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 607846312 1250 607845062 607845083
    0x1e010c06020a11011119020703020906040908250b060d030c1103030c010e0c01080f0108060103082a30090f010309151a0a0513270f0501050c0a020a0f050109 69
    0x61560700c13046e04900366030200c2c600e401229400c111300001d001411207034041c00c0c8090741d941d50000c010080030004000c2e24040b004002c02410300c00700e464515044000040b291080c807149090089488400500c0180941a0404240c01103500f0849061865034403060324024520340001182c118000c111a2612560030407841c02452100828a40c145d100280c0c1d5141c916038540c083c041c0403175401e00c512000b9800020061021070500d80007040301c40e018142c1e504212900801c1408ac1040d500300c0e01340c1c1500701c0710b005424070f110000b850003080e080c0007580920070003800d21004980701d0f1403500c81c42208201740003c3c1c0d42c0d00982000121f540c10007031041045030f8148240e0090540300004901620711800c0d24a11403a120282c2d03010b031070024161801003042a0642d000814a00500041040501c4a1a0b5428280c00000c070040c80c899042244008070515003242540c4014042140c50042804440c441da6800a0422542038011408902c0f41047e81403c500400c540b41d40580500c549 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 607847562 1250 607846312 607846331
    0x14070c051b19030b0a0509010b0a1e1701020307110d0e0409140303090f10020a0c060b0a03050d0e01021e0a0803040309030c09051f060806040e1006080c1e010c06020a1101 75
    0x78400d1a84103421404041c0807950320000172600700c0e22284a4554080308510b4248001d0303001d90702f0907020322858a80d11048680f5402e0800d0200d65030301d903441f640d0307400204201d140c0740d00c019450240d201c110000c2103000003030303170014203010300041e10980100e5443c4020020b20201214614881e05c1d80d04c1929542d08060948603101e019042c3c3d518401d03c03445007040040c40991084502d4a00c0c50fa503083c540a41e140d0317a620180c00c1d0204419440710078600701001080080c0302c0c1003c001c1c82d0f03413541207081c0100700c0064107040c0c03841505a09020b204206200441001c9022440c190740600360681d00d03525450b003503a05103010740001d00000c1c00041c002c64040e00f20352195010b0300484001700da1507000b0010201110040d40604070021320640041140c500f0550070441c5c14940d12004e45001c440f10102400446080b5840f100040d848850b4504580c2030181d20756282c102c2d0702010303001c000c80001c0081d1211108080c024400c5078009050b0030340c02d204140800220320908020b22403250b8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 607848812 1250 607847562 607847573
    0x15052106030607080103050607031a031006090c0804082d03340f1803020301140121080901051b0a0f02030601080d0210091b0914070c051b1903 63
    0x6085403500c1c02842400d02094031940a1480c040c12640c1c0301d8014045a03442100840280500c1001281c0980d040c1c1820b008070b98050109035480d0183d040001005440d06481400362610b03025400148010b5106100c0414588030858440706522004000e04580d0320300412614160107108200703400001c42070044180600c2114004101610702ca00d5039641150034009844403014841404070700a0b42074440028001c403416500340401c0352401b030461350f9030f40101c0c0c21b50350b40c01001c07008400c101006010b01361145000ea054000c0c0b202940d404c55400f540c69072a984240c2511906000000c510724503482014180210a14542d20565114810034034095503861208001240700b8029580045209a000036904104100603801000c0d602e07580500980100400c86080e0f601d81e040e0000c000c5044000f01ca8800140901c280020302c50300760303014408082c0300c080c04031400c021134000018041103002a1240213101a902046100005800026900c0041040711140700a0300e110000c140b15 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 607850062 1250 607848812 607848877
    0x90304030b04060e0606010e010f031e0e0102190f02060109050a02040b0a0e210a170403060501240305040b0f10170309120d020a150e030412060e010b0a1505 69
    0x2a803130300440350240c40300001510b103c850b821034603001401d880c050360321f030b54440d80042da640414290314901130820084000161381298a542502e41c7d000241404403040500400c0d030380302c88911308403030340d040d401000944640741131058140e4070b0781750000b0070071400c82c6a04483c02008082c188030f0b620400d03048064180780c3c0d0140f40c4c80c440c80c0d020399214180d03030888900c1425980d144001d0301d6001342e03550b10594003221412030a0445e40c1c043c00040002402e62060034060849601d40c0c52508901c80b01400c40c00d095595014201400c10080c4000200005112034001602c0d200d004007582e9202d101c940d02d04030b140c1c01080e0000011250035620f46000c00100404001600c082c50364403402a00b159030341445007519801030707200031400c43c0414642105100001c400182c00300307610041803042c901e150072641090681c3c06101da21903081150a104681c20a6480310080c03090f1400040000c1209072540701d03c00c42d900c54418200e46191244048a608801c1d2014045034910314a00c0c502c560b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 607851312 1250 607850062 607850081
    0x609060c0a140703030b1c020a06140d050103030c141c0c0218191d070306020705030c060910061e170f0106031103010e06010e0c0a0e090405010507140a0207030b090304030b0406 78
    0x1501d40341c0482d0400c090084c7c0c0c8a1143e42c0103011882540d2070f0007011200322600c50400c0403601802d04c03c40715a821030303000d5540254043d40e0f841d1202d04903070400054102100494881651040c5107140403201c243d000c0c44000215405d114103031900500125070004820b10414403d214107004106400080e09004e0a0304c4000020401034000c1d14012183c2c4c0400c039050600007a800581c0400000d090f41e002046550322034000c0d6400c01002c0b0341100e103030100c10786007038a458203c00410000701101b441524018240c0c0b40c43e000607046e8818034000c2d603045602840551070f00d02e0704240d1080384204000d05510301d1900081000a07504e04029101240422210384654200100820074560026299060300c50307125500c3c0702030721080704290060340145848410700454254012040d81c0314840c5620030340c028400070480340350116004003251907030100c2c880c9060003849500800c5038006080c0c401d8036400311801140d0344400781d10340e145000e103a100a0841100d02c08200400c560764006c16140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 607852562 1250 607851312 607851319
    0x3021b06040915060f090303210204171f060e1522150920090d1e05011401080a0611190908010c030207020d0b040c08100b0306090609060c0a140703030b 67
    0x524600080c11a1b0020241c800a4009201e8000b10300000c0c43d0721240105445c03401c1c8005103481c0da51020a1207640c40c0c984210940d0308160242e010b0354030b030444c003110b6004003200d0800276a8208901d40c180420064982100419481060303220f64580c41c40e071070074404140d001c02d076071008200720030400707400b1750798410f0b891603800e90000a104019020b040c2041d00e1404000e040c03205840c41d1914142c101918050348003030040100d90100c4c0c1c0a8050052004209907020221078440c2001801d4031710b0030540ca95407403080130041140301c80c0400c041109941c0a0400310702040340c2c9004010602618111030f005010a40043c0d81c255000303002c0d0f80c101e9007100020711000c1c03c0c1c0d0b50b042d0100c0c041d202d40690060740303001002c0c0c000341d070b403818859000e841020503c4081c1c2c0c44e003801030310b004000c0d5450000d00350307140e203107034141d00c0c0811096030b01a10300030090030903190001910340c846101908032280ca0002080340100c150068103a04802c2e80450009c0d621641c480c20000c0241c00c1c04100c8900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 607853812 1250 607852562 607852577
    0x71d0306101707030309290406080604230703020c0a1e031101110a030c020a1a100f210c0e0916061b080c0a0204051608090a03021b0604091506 63
    0x550304400b03d9010102c03501521602e002c1890520f00071042c1650036600380d500c13200ca860300429070305c403480940050000c60359008c0c40c87c0303400300612003140d001020f01c41080c4611200c01c2c05814440b20500d038006030038070f80503032180f050b08034241c41d000788190000e0482c82c020103005000100c0010300302d203583c000e41e00d215000300310800c02401c8078041c600806400004101a9201c00d00075008124284000c2c41100c3c4c460145881c0c0b002000c11140041d42010028018480010b40c100c81104c0505443c030750003907015161505461100f80d500412200049144070740c6004c1c02100c103a11802414410032009051512642550321a989200c007043c042c2450f0001144003032040c0b022071203180808160b0000c4c4451900c1d0050035821804486030305226090b40b8100586840c0603003805488641e1070b00030007181100c1c1c003600c0c1c184001c201000ca54004403400c0c022980c001a2848541942c4e0a0107000310003076000320764503101d2904295030140c00d0044004a030f02c1c4100c1c2d40c00c12560750fa520030300d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 607855062 1250 607853812 607853849
    0x60a170a0c022b05090111030a11010c0e0f190f0b07020a091e0e1f09020f0105090d1e0204020a0503150f0a031b0305011b0305010e0f071d030610 64
    0x80c03281a9002d01180031420701502201d0703844c010b100802025005040ca104503500140066155910154412002494684003c0341042c000d02400c00158094107113442082c3d080b0001c41c50300c0f10818480da1240c1c2c45000400c505822040115001e0541c1005404045450b01c48103070480d40b210030f04901549028000098070b04042c400e10b41010991130000c08241c0008030500b000e0001a1607040481c09109004085c1d104410b06029400c00c0100c2c022a40c0070300c600402144082d40c01c400c5040c0901007080c00b0080e550780e0070072010541d11020780046075a9458108984040e181002508076100207a0040b05030b422001541c0b0411201103420100c600a41c280701000d94940001d9170400340241003400050000800798002032800034040380119900e4456030709441d00982d01880d0540c0300d840d000d00ea15454000c0038050050b94551514900b000c4001d42480c00c0c00810300c03001c100030608030050081c07558040e8804074400408036903141c1801030300109601035030312811a02001211890 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 607856312 1250 607855062 607855093
    0x71107060816030e06100906090209030d110a06090b06040c0e1507060921110327040f15080c040b091b07060e0601060824060a170a0c02 60
    0x2401580c1a03075440710040c1c1c40e00607054048412840405003032603191203c0100844d000c00071584600380201c0021501403418040c1000c0301d01d07070b0308a40c501600401c00050291070002d80c064030621140b800c41011a01841c440f4245403034440024281c07428141345509104004407901d024803801c45040080d1560040d0940f000c91404900d181c201c500e0b01e0446203069141e4010b013500342c2c00381d03001203820085666000b903540c1108420300e200311402c0d05014000340d4806040d04400003c00d00461600b8007003c00348104200c0d0042c00b001d665502e0b0000e1040c0d44441e0410010382c500d40310709001c2e80000c0c40c3c450074806d015000b03060440c1302d001c00d040003526050040481d01100680b414860751615905c111000304806c803240124001000301c40005180c42c03050a5102002d040588031550400c03200500014028040c8008070a40210009000002e84041580907008550141d91b800456409540d42c0900d62181050001004100480c00019402c00301500d586a401d443c145024003da9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 607857562 1250 607856312 607856323
    0x30a020d032405010e0f0301060b1206010207080c06030411060d060e0907030c03080a051c05091504051c031e09060b0d0b190912112a06300711 63
    0x40b0001e040c05034001c208039406030007660b0a03200e026041140e000030282c0840d01359101d9a000e400d403d5000a0113403080d1820000694000780b0920160908510700700100355603849203c0003910414000011804102110340c48100d060030240105480304007540020009211510809207200c0700b810000b4200d00011800740d041c0e0354407012071500d650960301d404d205034010b02a42024418204690400520700f50601c1c6030a099041010035585480314625050400c2c0f5110402e03c50b2200050200040740032541001c45241038200341d2a4152080d011000f500341000340a054507e110704c40703c9844100d4110300c1c01d56016072020f121115000040c810501b1284c1c0c400340080707003024042600705502004001040c90b1807240400e09030f0003500c440c0c00c002140b140d420b010500c00703075090114400074400129100c854542401c501e0380c400380c805a41b0402e005009110342400503910f0040980d01c03031803600500d21900000404030141d204589201010740c2c000e00400c0050200070703d880b100140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 607858812 1250 607857562 607857611
    0xd02120414040605042a030b061803010914011a030607050a0c03051c0e0607032f0409051005031204030201020a02150c0d02071d0609010302150705030a020d03 70
    0x40180c039061901101034221070054103a5a031058480c540020f003541e4500801031240c100c02480c083c02128001240c0c03416a0b10f000400034075080c10b4202e0010756940e010366000341d0940c05004e0038907030940c000a00414003840c00521205144a00380200e00056101801e183e2202440c05540d03d0a84201947d601d011038000002403010041030f250035210f481c0071880c03e84241070840c01c0042402c10060800c0f40811108015039540804000c00701d4200900307500301e209810100413811211740024203880e0309450981142280c010602c0c00c12850400300c4004007a000310801050510480103401200d96100da181b00e0b00c10b000c800d10840075820100c0702180d90580042003410466401c3c48202401101f2050081c24207100c5050345034030034003d1780840300c0584c0c064800c0a08060510211806105254481035000c034100816a03d6800c03020741507036011100b40c0103294500028000522440380b008096010200300c50300c1e0950001902d21168025032010f0004451204442003210540d1a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 607860062 1250 607858812 607858843
    0x180319050c270c0a1b0305090411160206160204141f2718110312070f2d0b0f06040504030806010e0103240911070201090306050601090909080a020d02 66
    0x10041030703d0280f024000c140141c0075080c500c20480c3d034144400304104500b80280d001c80c01c005895800351820b4451800b00401c0000e0042c248440b142e000880c1c140c010030700034000ca000051030340421800c3c040c0300f50307001e0f4010018004480c900540c13549440701075a83c1154503000128400e24500c1c2d2040d6102520304445a60300311424818110004451103503403c41c0942c2c0c1c900026101c0500a07040c0280a03002c0c81c5603200707201da0b000c00c1c50710303260300e0030b01d1f02d03140490a011650016a03850320610a551300000c00c11740c2d2005001d010030510351983d0031032007040c18102290f420003100a821b0f52040508140158103540c2d80800c1c00181da2040f500200020900000a1050341c041c40742c20b0240201031400181e8035420194080c484a044a40c0c4401e031600030104000ba0041801000182207110f80c450303080076400d40c0064400740c46400001e05090705c403400122147d124410001c014a00381400f072000358881c1c01d11001951140c00d03148018000c03000d4290f015400010080d41050300300c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 607861312 1250 607860062 607860139
    0xa02090a0213030c0303020a0b090102130b09060d05130501110f040905190507090e0901060b03010e0c0c010507030c0e0109051e1302030c03061e0303180319050c 71
    0x14680c00203500140940c800ea03110708501101051006200708043c512a070000d0000700f046080400c03151000070501718903a8010044070700341340c10017017024044070110310900e030f168909000000d4a90040d044080750003441d040c20011410701e003c0000741c10764000e030000c110211500601c0d030954400c2c00c400d2840351300200300400011206901035680400c030a468035190411103041c203400e85070241c0310b032000192510f1341072105009008229401c04840d2000300a510f18040350000240014410858144bc1020006004440100840300400741d400001c0000e840d0030240580240812220300d000900300d11120412540140209003d5440c002c01c1c0980c916900d044824030070018549603900408840785842da031443d580080c5004205540c2c9c015105d140680900202101c681151091090075456581c450340b400303c01c980e415401034081c01da1008603080403a10744051a20702d9075444c0141039050003400340100b00040030450484a40d240c154012280007403911b0902c0220414402a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 607862562 1250 607861312 607861321
    0x15020c0f09070302090d060e190215090d050d090e01060329040b030307050c10020d0905040506010507020d030305190605281502030c060106080114220204120c05030a0209 75
    0x259580c0780e03101c07050b80303405440e001035000445c9055142c031360111005600c0c1c001e01008030b10305010520051320480f884820190103900018405080d050f6480f030f140f4000a003220700c544038600d15410803a040001c4647c03400e24000c000f04281c1c494465031305010504c10000c26554828000c00c0b40503c2c4030b078121540500e118804070110050541e800307902c280c0d155960000d41e02c0034405062014084c201822200012009101462448403050000c41d0032420300c5241e0380b0303017000d01c40e8151201a90002420f075030b108016540c602c03030300001941c040321f4180608109541504072134454550010401da1902c0c8000c032840586849004040e0701600c003040551602001c040a01541d90704d80508280f1142ea03810800b01c4014400100340058000103007411088404102880c014034081c50105104d40c5070000d03808000c03080c04501482003601c5102c1041c1c13400108410b40080344004011982c480c0d0b241080c4007510303070f0550100c56040200c2c0e400901440d0104030b065149401401e000109d075034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 607863812 1250 607862562 607862569
    0x80111041d150a03080d0c030b18070c08071b0b090315061c0c0306110304241506020f07141c06020c03040308090915030c040f0b03011515020c0f 64
    0x1402040410440448031030600e8030350311488118004e5004200c0c441e40c4018000000d0242c0d58200d00150034141440110615511030060050701080b1842002080da26548001c80b06401c42d5180503001400110f48242482030070f00e0714a481d0846c1e03607071130442d00783d40f030440715490b006a03400d450f80364100340701015a0480c0e800d85d07290700c0b0130010f1000f0604440403034003004508e8184000c0e111200880c2c024010000e42c3d1180c0142c03a1401c281c0c3c207046d0b00c2c00341c0d2010114442e5010703092300030035004034003d803064580d0024400048007800b0001c0701e0b5144c102c020740d2450301e42c07581500c61154020014440200d14800580500003170b00c04040d0340740f0b600507500540c80c1940e0886245500b00142c41d02101c051024201542c030419900c1e60303030355141c81082440c110280c040050f02d50080700410643d0307000140102c02d55401e91b03000c101c00140403000c0000740b03121982d041d055400d140c00030383c03c10020055a0180c84403600d1801401c103030048102da42e0514068030701d8016180d60ba01100320328 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 607865062 1250 607863812 607863869
    0x3050f01061416080a0201050f0f190e011e0c140f03070c03020f0d0906031b1d0612040506040212070f03110a0801090c050307090b0102030706150b04060908011104 72
    0x7502d225190f80003200e94840080b82d0011a1010050355600c0074007031680b40700c0103d103800401030004140030707041c60340f00c2c2640b0a440103694a803180c0c0d940741c4d2002c120803c0d00034003051003036401141a26400c10404001070148109035200041c0382c0304075078820002241c161a00c41c024444124150b41d204901511180307030280040e4298071411400c512120400c10003400b074124680d40c0e1602c1a8130700304015054542c00c00181d01c074014110703510310800754031842203640c4900c5401d21100007a00e880100c1c40d680700c0c203000e1400009114041000f400b100007203c5009038403d45160740940313005180607845103414015402006036035901013020401000d02b48040320070080210b00f0543e80c614403a400c450580d102115003280300c00c1d0802c4245030510115004060710718003401400e2004000075124032030a08004e0000b55100d80300d010300a804241800a000c250740d00300c3e0f4a076166200640584040d1007002559802c1c900c1c1c83d00d45586000a40e02141c2d5011101c0c81d08802c2c01100b81c1065 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 607866312 1250 607865062 607865077
    0x4090b0105070210050c0705150d0f24031203060819170d1505040209010f050c010e0a0317070c11101101050a020403060509010c0e1e0d080a03050f010614 68
    0x10809020500c00f503603a805040030915095141e05d984c900000900c60f00301406e59000d5071280c00340075512000540c190003110100c4001c20b100249081d0124008001042c1c0e2204111411041501c41c0b0090259a222141034030301504c1d02000c0d8505510085041c2c0d461070142400d1604081d040000c00c41c08684c1e070303010317051181c1c805a0001d00c103140e6001c0c054003c40400201c40e40c556030f000d400c840d01a00340d031015242c140c0d0309501c0c10720f4090010700042004a044000c200b00000c218148210a40c0000501d01448084c3c40b90701c002d900300105030500640b000d00e44000351101040d0024003400002c0283d50303000081801d001424404c00ca200d4401041c1901400b0703514401d0105078000b8070895115801d0404016140d600b03504203c400c446004241840d168540300c0f18a0480e9001741255248400c2140c110042c0390301c100b420000590a44555600155440b22000c100140c840c00307821020042c9d901040305589a10424030005020b102d044003248007440e513800388600340070060150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 607867562 1250 607866312 607866317
    0x70f1214010905010f1a0a0605030c0a050d0f0203061c0c1205010b09091e0606090606071a07031b0206040201080a050915010e090f0f0c091302040f1a1504090b01 71
    0x12041c0940f1410b017510250105a01400d5888241c00c426540c1c00200e01421318040c1c64604260b07081c4034018089210181c2a002410030209000300d027244604221110100011001d10840111300403103c06500f00741c401034464254000d0f10640d65040310b051002007a081004801c00034a401c000801c500d070a035a06a801e9502c41d91340c04d416481d4645c805000f025100000c0c07080b41040300305040d00b108080764051880e04071409000c125901c80f10281d030000c1c01101c2075a5918110700d8a03a03202041d030340d00d079020440c3e5441000446500b545c44464011001f00703200340005a1650201c1e15a00106c8000b404035140c0301c085100c081c800e80c40282d00c06001402c4441b00100b401441d07810480992015101c0502c940801c00e000c0d134140140790000d40800b000384100d20100703040e030b502d40e09254140d038001e0384030f100003500c41c004400c07110303c2440d0042d10070400c10689200d1300018003800e00e501c4503200050030024045040950340309107103005502c1041c0c00d00c0e040182030070190501c0e0405604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 607868812 1250 607867562 607867571
    0xf05150901030b041407080103020301050c0a0c020f04090c0902031b04030b0a0509010b03011a120f0d030c02070e0726130f150c0f030501060c08030f06041b020c03070f121401 77
    0x26405c280001e900d02034400341d00c03010520340c9175104050a41e0001070203024481c2003400140b44954100800e5608150704480c00c03030401820341d022900600354a00c0c040c0646902c86000035410714036a0003940540e0300c904d0750581c1610300c040c903501c0340c0c4214440108010100c40001e00401103a502c02500001c44900105060b68014000b80c00c2d100305c0180505400f41c10040a0880d00d001c6005240f104c0400019101b0040d4002c07206440e92000700100e414152944110110756209015040c060a00d48415a8950411000003030102c10340300c2d00229410880700e01c400c0d0b41000e030560130744074000c1d030f41d09054920b8007613a504801200303505084506034003851030f40c0072030050707405020246c04140d6074481d045114284010192a4180d22041c1800404a1040c0225103000e040305d5100e009145038401a843e0003000c540107000034540b240b514800d5a80c0016000d5010034140c40c4100700720200e03030103591202c1d03030340346008524410403442403090a01040020380008211a140056200008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 607870062 1250 607868812 607868831
    0x5090307090204080304050a0e071b14120301060f08010b0405210303130c060504150309020d0c0b1b0f0d0e210c0103240608090c040f02040f05150901030b04 69
    0x2e9800603000381e542500046400c0c412030501100ca4001080740003040e2400d814035141c007034408400d04051114201109201400f8400c0d9102c1502414407010201c903040d0603180e5080c4141c0e0428000c14002a500c0d501e00401c29106102440c140c0d840120700314506442e0004108144105020022055810315454030004005001451080e41c4c0d80b504080c000031140780a6445092681100b41800014001409404001036000030002e8503400c000a11000b01c0c0002507178506a904014240190040c020404601d82c2001d48a401c9444440c004403a00054426455200ca0507200d01c403648910070284040d8451680802c46c0c450281005640058503104c0c0c85805030382010350b000540c40b4a42c03103292540e0601c1100002c2c00c00341c85400c900032026101e0303d00542d46101d543c041002c604040b8860302418000d0106400340200104620110040194065085031043c090400c115140c001000e0030100356030310360401e4400710f9901d400c103080c00540091450b0025141c1103980c0d03400b01e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 607871312 1250 607870062 607870079
    0x110702011e140c0a1a040b060d060612060f0c0f0203091011300405090609040c09140414030c03031918050f2104050402030406240e07030204060f05090307 68
    0x108280710550f006002c4042c0e03142490b40c418031201c140c1d031400d40c0c000030420021600300d0380995040b02c000c64550074500f0140c10901e000d411190403008513041807600b50410044039034002c10a84030b401c84140300b4040c1c02d4005481c0000d031075800700b002d03070070030086a0690724101807030600ca032007241010a074014004000c1e6241410003540c281d015515500d42a045440e800c8880107140f03a09a010b5141c14145008600c181001030495801103401c40046800c00c5090301142000d000340000c05c02807524180c140d100200f0301502e0036941d610744041c042002c0f46000c412206403c0100c0011403031501c540340c1d03c804044d00c0030b00c41e54100740d54400f24010390301c0d161442c9030310b240a0401007806100e00d404031400c0c4034000d4414000407030f505160703014084450064404a800c12a001a16070342c9908014001c0d085004002c40084c5030705145100265050303414a040d00c1710740c401c8403000c0d036410800b03804130f00c658000c03100861040c41038070110f2841500100140b035409025a80013940e0342111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 607872562 1250 607871312 607871317
    0x5130e0705030708091609020706061505070c05030d0c020111190804090513150906060b071b0e070504171608030a0e060909131b0612110702011e14 65
    0x1458005000042800f51040d88803a072143c004074400702078166542d03900d004070b00c607030210321500882c01c0e00454188140041d680c000360041c075503004e8004821903101d800400b140d20241c1b040703900485443d0046001e0a00040750700f1000c2240c5c5402e120f02056030019914007060120040f4607100e21071b44040e02584103d0100983c1d4441c000094941d410103c00900751000101641152000c10714110f01140c0104901da81c20318504a0008400c241130404e0f0001d01425003002030103000000c2c40c103040040d24020351007603402c41c0791004861500c1e48003110641c0002d44840c0d00103a0700f4003040c400f8105101c3c1100402c007240d800c8800c1010500701240c511350081c0d0152070039410100388401c4054001d000301101540841d4590710700301800000411032038002d44621410200789608000708150690103041c0789940644821000d544e501005002c0c00a001107a1074150401642d00e05081c41c2c03800f80d900507075058607051404c2410007241e00100e18243d40100030030011450168032540300740300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 607873812 1250 607872562 607872571
    0x10602011d0c0a29160309080c10050c0c030303040809040c020312220210020604120908031803070b0c060106030c090b07170f040f140108071d0303040b03010e06011101051003020105130e 82
    0xa45c0d11116142e0070b0181c000c12444d48841c1054000c441c000e01e5507074501011480049050401c140c85400744414586065643c403481c46d01403000000744424041182c001d0544c2030021102030001c5074600c217003203882e0300880c2120444560108003044001c40602c2910707100585400074030b83e0741403250f0009881110010f49410142c0c10140903c030a225030301110b40078007452814400a0700349000c0d0380c1562441121b0950b0910b034608511417030195410b0000b80001c0039690b848588a40090030402c1d2200402c0c412a400300e80b07400b07160341113980180b00c08001c41e014030032800d05209454954482c101e0040100c0e214610080280d580030700b6030600030344058400e060b14185058189030240c10340701c001d1180c01741442524010445115804207050020002d11014480e100303501c000480e2940c041c94018030007982d804400070076803184508440303104000980c1d825a0490590414500300e0f041590344052800403c407041c00594008d1008000744101c0e40502d092079a0780b0001c1c000d20013810355 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 607875062 1250 607873812 607873837
    0x9180a1104020f0409021305030c030a0308060409050703030504060210090210120f02031e06060f1b03270108070c0309140a090e0109200901031e0506010602011d0c0a29 74
    0x60300007180e107e032003035000241c1020b0f0001c0647e801030200007580c2e030791005c000900300032600e03000441d192243e4106a80190b401011500c0f152344030701d00540320360030a02030b920040c413403000c031901011035034099413241c0f5801405443c503a032042c1900b121031340ca00c2000080240e4551058132107512581c80118400c03c00203050042c4441210303040c00040760302400d028414001407008205001007242222040d403005408120240150781c215411402a44810305400284010381001260340405814044000b640c4543c219920440203a5a8000090014000401131007050081d507103c0c3d00f50720745400c4008c0002840e1555614481d0664001c4482c00d0001d0351074040301c00802284c5038620452650545d031814681c131174100429240d450520010300b034000000ca0f009440c000300340c0f4038001c00d6044400d0361540c0d0384510010340a8080c22408100002d072200010f80d140b000415800301c901c0c401028100d4291600c410b0240030b2000380410040380d07104408601601d80480c00810300d4100c00d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 607876312 1250 607875062 607875067
    0x80705161b0932160908150103030e0607050a060507020106170a0203060717040b070e030102131a0406080613181515150804051e0c09180a1104020f040902 68
    0x880440302200c21000d031070610a00400034500564992070f50030f50f1101e110380189003000070940c0100c480c1c88450340900c5d40d502618580101407402c400d21141680e0003529020740051000044c0913080c454540060402d802c1000280001052500626008809840007142e0291038405403c051811103201032001c1d80300000480071030800b8401660711080c44d0130051941480c40401c41c2d4444002000104500124000511014080c020301110024003800841d00c0750104c0201000e241010f000c0c0d4600c1c1480e5140307444404017103100316000d850040e0b4074514252a854123104800740c801d800340c81c5c1642c484445400e6280b01501003901c07035014441c1401401580d403401d00850f00541480501c01c00144424058403d0510301c1c0e88030b0400914107040710355628180360741004520610030840055006802400c0c10307000a1510f1004000c65030b44400740c0700c08040140d181c84030001710503035822103030140011032402c2d030322650b80301c2c3c0180c03000d032400d00442c16a40d0301c1d5216400035858107901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 607877562 1250 607876312 607876331
    0xb0a090f060f08100903020312151305070f26041b06090308190e0310020c0c0405060f090705120a05010305010e01060b0d0b0d020301020403120f080705161b09 70
    0x340120300090040310030071180e8900b8007602070307113503808107a407a92200c0e10741228101300351007003040715640460012104424103184103001d52030040101d409100e809c070f12107540c001030103034450280641d00c2c03a01c4428001014140030b6503034922158070402c00080c543e0348113804000c42021f95210324400d190004444010580203230b01e051060b0003000c100480e440007440014003100880c2c6448000440b180c4182c10b01c61022907000320000c14187e05070080341d4a0324020590368026041315060381c03013624019540c00d820b010448404403504c0340e0150706041031081c241080818aa04000c1d2450b195107040307807641108000074001d0b01d480600340d955800401c1032107002c1c42500740d443c0004009000683c90720710000014003030080e0f40300419955420a44a980d0703041200740050b58050000d44d1582c0d62401c005820300030703c0c4104c801003801c0d020b604038047d100b200140d20034402622030505120b0310394500e018249150500b10f420000101151080c000035090f1803000340b035840808036080c540f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 607878812 1250 607877562 607877591
    0xf0c06020d0504060c060b030c120705040f0b0a050108090f010905061905070f080604090f052401060f0c1109150312090108060f01180b1201061706040f0b0a09 70
    0x1c504208104114007400103102c015486030305405101e07000030020805100c001c00007170070140ba56410a0344540d161110003100d00c40132550300c04441040760308000d107002003000d04080d90420710003558042c02c0f40030280415809080758581186031801220b001180c0c0d81d0066007165007600040c4c41c154030130700802c103494820304801c0f80d60707003c21035050140c0c0c105518090881c9000681c020140400300c00002c0c41507c6951100c0d01031038100700c1201059480303091080e10351209645e00b80c2c0d00c5402d641c05010311000d00950074103c40032655591a500300e0303a030b0211156503140d101207411055100401080c1c1d515840068004d64664102c640c400720310404061030001c1c0800c84061406040c4508201070382c100c00780c10303400070081c3e0b001880b807482500126495152041a180c042e44110720220300b80b090f41d00506541c2c05001c041c0d030010790701d842050302c02e1690320b004032001501900005074181820340201d10006054a80481c1c0ca070948400030344808215000584c08503036909503806902e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 607880062 1250 607878812 607878823
    0xc1814010504020f0304120234050f1f030b0d1103010c110d0804170f030901060605130b090312030109020d05010f06081305250305150c040915030f0c0602 68
    0x34200d03403c5250621072140e854850000500241c58580e0308112003502c580240174003084d040811520f412400401081401da00c14184502c9204031074641c004100303414000800502070301c0003480b02101c6001024510706022401740c0d00b004040e00c42d1204e1449440308640320203014813070060034890103a05014507086800e4502c2c01001c2240320724a40c554850045030621401e0081d02e403c1040d640c460038a41c1d007200b400d071480840325a000400311106140d200145003c1da500400078081c040d40e84034211254010f43c41003020004039800c0402c2040300c1c82e40203064041c400303000c0d180620916000034a903900268848200e0700d8000846864062641c030816014016160498002a081c040003c2c900c00009150442519031a010281804010454070b0280a50022421a419000c0401010082c0c5a00c4100c400784a0343c0e0311aa03a4010001c0706510464848900604282c54610b041000e4201c240c4102d40c0d6519060b800300c041022044c00944150003040032451051400380000e2908 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 607881312 1250 607880062 607880069
    0x7030905031206030c0109140d02010507020916120212011701180b10050d050a02040216291e04060c0c080d050f0708090a06090606381c02070c181401 66
    0x140c00ba060158440d0640c04c8c1c0c0c0380c488103603141000000f841c4010707a00d61180990281d8454400c00c100065071095408007501541c1c6507551b01c0f903c0001c0765940041c1d00400303111100e640b60320401072000c1200740404901d45601c07007002150324080c0b5a00c00010000841050b90841010003c2044030701041c0c03e030f00001c1000703440340c03400404540c854035281e40401b24002d120720740003da22040c4040c018a500c449580003881c080d0144110074000303000c103100c0100c4d0904101c540e800150030036050401460181d4400d52040440c0e9a02d569401c0144a04101c0c542400100100350010171441c03400f9182241140800003458200b191030940c0d482c10003489003040060010401c00044400b140c1080303c01e900c4500850a04171314034052024040395005810069034952400740401c2d49844c440030f0002030131003000004401101820150f103e460f40040803090001007040040029500400d51940940455207105442d00040480241048031490380706031580005075092070b40c0992507005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 607882562 1250 607881312 607881317
    0x3062c07030b0a0b060405030715030c0806100809070902040603050105030f01110406080a090818100306050a0320220b01050403020a18060513022a031207030905031206030c01 77
    0x10074956a5002d64808005103094880ca0711814600e1668440c401510082c0c44018240d54080d80c491900d1034401a4080d0341d100024180080180c006000c1e40020b030080d5005480600b540311440700503691708401911540c02803084200000c2c81b01418406480030348000d5030045115407405080518090100c460109981d140246850201d10042c0894048404c2428604c05551f02c01242100030179500501074820140020100401c60381101500300e030309030442c0c07040100364031a00110300f287c5450007004d8121411200500100d620341c101050740d01e20407004100c00070351082c04039021000844203450f2403448c2c04203a03000140d0a00070340120503000e00e0064101481c680000e13288241c02d218456184150040303e9034011416008070002c0e150242c040140c1090b1514001c0c005e5000703402c2461108103564001e40f4010b009038510341d60607000070056091420700e5040c02c7d80002c010304920140369803034442000141080c80681151001c0200c44007903890000189420641c2e1603020604 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 607883812 1250 607882562 607882573
    0x2121020f120f0301180204030501150603230106110a1b15031503060902240c1018141903020a0b07020a020102101113121e03090e1003062c 61
    0x1410b0091409483c119001240300c010745500e08107100009104d280c0015145508001502051110309110541115110b030740421004100c4110888103140d440c8018252501110041265038410508a2000708818099650960711969001040f11f5007140d1a900c0305c1e100b110410080000d500800c1c410500c43c01c0c10b0007a4464001281010391031400024007180d981d000720420340d1030355045803000c6060038001808420103c004e403202e0717801c1190349121902c0380009114058440b40100e982102144400c484810000e5031001701c4101002c120421610032280383c003800d480360300d2511111078000d80141a0202e11420904c00703c95004000c8415944030141120040c0d070300003822140b01c540490009460302501000060030300c0b40c80c00000904200040c04505900300f0841304600707600c60705200c0c040b0060000c00707168019880c80c4c09800310711611070070440300780d100c8921a80001e0008000c5000c1c3d459550301000c48080d00305000034402011002203280e07a030341012500489850b4010035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 607885062 1250 607883812 607883827
    0xf04050d0c09180b06130621020a170a0204050a090503030a0504060c0804081902073309030206161109090d140f0a030b04060306020a1101060608012121020f12 70
    0x5008a5020b00384074000c41c6c41c00000c0749108101c2d40500041c0540f1040f40003e540444240240702c480341c441a441414692030000c0c1141011040400c0200600060b00565400d07808000080000502443d0040d1711000c2c540c0000e50300748011403140141610016250406082003021118003900d030006010081081c0030200342c107c8181d400e4411400000340c80740518040803414031049600424081040e04840d200c4094001410440f040d440c5200ea0300300e2451350012207000d4035034480650048402c2048151100c100324100c14100d01610b090390303624441102040304044211035201060304900180d9150307079800880303402d070b4144031010682030000940c40138615100742944030b070516640e008081820346913500b2007230065030440300454403000d028101804d100c0d00c1094000c115440c1507004503d040c081c81c8001d050701c014840c12900e26000f0034601c4103100304c0d0407040d201c1e80c00141b011491400702e0301007443c8000103a0b000c0c0000b031003104181c0d07242c4446840181c005110911599 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 607886312 1250 607885062 607885073
    0x403111203060f010e0406060c1b0e04140a0b07090806281814071703190f021501090c09140306041b0f090501051e150f04050d0c0918 59
    0xc0381c12440c2140d0103250a0810801031704e10034416a21190024104a00044c980c0d401035192103046015450190540481c003203c01c2e001600b40c064046010510400302e40403402040080700a90441c8040b030310641c4098480e218842e074126065800109035000912020b01c05011450300001c0c19000880c05043c41e00881503e200c2c6a1121150709941d02c141c00c2720020010544110503400c00c5040001d544600e0b202500c60505000e680304400184c1c02c0c641d40d009002044a0100310040821642916000c50480d25180304204580031845404140c07940e080b03082d83e655001304334482d0300140010742c00001074402040740e070100d0f0400701d041100c9012070b1404150150700503401000c1880303803e0701040003510710595400401510341c54050124240d0201d6020038182c41c422544520b014076001000c5034014504c401960708841140745920140700c4031005003100d2011b01040c10700341600d540229001d1120140c0680b54280d0f8240701b009132003100e200d5a094402800480b054140564860 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 607887562 1250 607886312 607886317
    0xb041a130902041d06060306010b0706020a1205100f090b0a14220507020c0609030a030305180d03090209010e010b0f0a0e04020414120d1202070503070210050304031112 74
    0x409000e1003440004050984955101c40c09041e8010070400c0b0800098940702c8160110800000d19440f0300700110310a0728002401c0e60480d0810b111007440d2002a40e1064007a41050740002c05100c201c01c036110075040580541403040a2106043e9035052400d1284a4483d206605c600c0c4032078030b080380c0a82d294484d003a500083e11014910388004255280201d10b08019901c0b00d0760000b2405070249910160580016003d0b41c84da600b1200c0c850107460070002d90b4414108400c0e8103500c566107150010380a034002aa00000c0c80b100711020703003c546051b508050311124420700083e40c404409003140341c10108a4050801e0349101801c5604080440715030380301d04035000c400e2250101d54540558170035140810a0300c005007055489643d1280342001c40071215204d10f205a0312031004085a140010b141d8081504940d180102c0400d010b584030004e6202d02010741d500d000400c4440050b840b1800078821078985540e07400d41d01e02c0c1a04004080d00c078000022031294002048102780908528103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 607888812 1250 607887562 607887611
    0x31203090d110c0301141602010b061605010e03040914091204030b0a020f270108090601050d050f0a05060906010b0a0c030503060414151008040b1501020a081c0b04 72
    0x1400ea0000300b4400041c0e203881c1c08102c0d441d6156003003c0d01000102861040c00d4050b2460044000b00c0a4542d10103900741e4914072102038214a00b40040c0c0301036009410001401c0e0701501c00042d1202c040c0c400503096a0098008192894540e107001210305610b50510b54444004030260005d07000000503200d541c4241d01c40684002a108085000400031380d0440d407012480c0303242e040da2200542d5681d510340c4031517404010000c090459111055020380f030007600c00c0c40c00d20041c0c00790781e00b010100200320060103810344203841000b0b082a00281c04200c10f42800d8040c4c0001c04a9107080c2d0081c510340441600004454a000d01c94080fa0980059001c80c440342e050810a03180d0ba90031004c034000300781c00384266014074503840c18420303103030384070040303e03021190548440a0102c201c0b031040d25416402e8400906000e030314000104c031070320009140b038055074051041d1000d407551921002e0190704288404410b100b02c000c0228141d2100348111040d41c00152014005001041c40408150b8075000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 607890062 1250 607888812 607888817
    0x30705011103190e0a0503030a09031410020715050c210705160b040302010f1806090f0b0106030510050d1104050a020f070605010f05090103230309040c080402031203090d 75
    0x1c0c00c0e40889441841a2201440c0c654100c200d001d9082100138501030040001034000d01079000d010030f85040120407940c50800c20340322120084d29607983c00d003510b0000c2054280b58018001000402800d500003403c080780540301d2940b241a408080340125080a4081c0070107900c03c20064000364550307005100912442c070040d01aa07030b01c50340d0640340da03c50700b03011031200120450840c0400c5440180c45000fa0301039030080141c0000d5251340b03002c5480c00d2403111084040c9503610800100d1540050b21560b1050b84018011802507454810503d0300b0380100c404a41c4820400c1002060f9041c500010071045a02140308911501d80791940010403100c0381c05a0740303444c00900d0659940e011100b1a011703000101f60307100d0890074580000e007000e000365202ea8105640010300c1d89850290340d4140e03a0801c2d221032200240e00441203481045072401758a600050100d4441581c562080280c0d102072602c1702c4100d49824030400d800c14255007070140000c0014028171031081c0c1c2c0043c85400c9404c050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 607891312 1250 607890062 607890077
    0x50f040807021503010b03040302070e07022e1103040b0604020f070204090c0e0117061f12032105040b0702010905120c070e0112140601050d0201051b060106110c0109030203070501 79
    0x600100300185660300404400103c0000002008a40240214860750282d07003595401030716400002c40c0c8a106981e8400140c1c491414207490740710326030a210030b1400110018240b000505900d0f81568050b070581c0580110100802c41400709041e8082c0d40700000f00c40031072400003851501d1080d03019104002c0c0c052903a8407822020000a02079403000741c03603c0c1080d2030b00c1d90303540d241d010420382c85407901e42c03958000d01c800310301c2c8a40510604041103503c4071031000324500384100d0b07000c14141800150204010035500440c0408604013400144940000c045101e103401d0030b1075807005401408040444e07141c0b1100d04080342010036000b00301030b0b01c42506950f0342c8139460001d24214070368000150750a1080000900403290642c0070200740d100300700400d1280800303459540c60744001d10640d5080b071640c43c203400040d84204014056940f11080b030001d034449009070309140c28400d802c20300c0480c00d0b0107110503d0b03801c00c005030614810300b40f0b000c1d240c86085030701080d1900030503c43c0e2030511052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 607892562 1250 607891312 607891327
    0xc09081023250c0b09060109060f0e0a020a0513030648030b091302030d050c0309270702061005030106061407032c1e0d02010e010302091507021201050f0408 69
    0x20044460b91681040d0b0b04202805d02c0444151201c40c00e10680c402546014070005800c010a40b44030101c8002c8c440448580da1105107160195000f001b41800b044000c002021a0b1400000c60201650081c480020f690890010100102c1d5101e029100080c040a09842c103003190313a1482c1c07101031100105100b801d4640602038000d05161004141d010311120200b20602404809018001e07008404844c032200b0001c0c0240c1d128800c0a00495454000700101c001504101800391450f4201e005d10324081113004824105103601a0341c0703000103802c85020301600d006858210000382400714000c00c01517150090107031014000071404014080c0104150042c14020600c000e4074966200318072250801280403036990314008070140e032080300b407440c40710030002448880a0410700e01400107141910b86800544032914020803045c10190204182400c80d21145004000303001c1c80c2041e0358403181c051040002c040120500c2c86000c0e03140208003c02c2c0b4007184201ca030010b401039a0b00e0340c0d8401c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 607893812 1250 607892562 607892567
    0x1101020c040614100f080406110909010b09040b03010b0604050103050a090c0b07060516081f1502010207140a0305040b1602090103030503090f0c030d030c0908102325 73
    0x141804a290300a00c0d042c800150805004542000c01c1011184491040e501081c1594600f1450411301c0009a5481c009400144254000010100d90b507103a6030414040100040324544260045c01c0304407400314584055041500401c541c03010201d0080c01080a4280400d80601580c27080d40e04064450000c9520a80c561b40810401504080c88403001615900500141e91100d10200c07a480c0c0b500000400c094021407044003607900301d03a508101d50300d6218540c00d80c00000d0350340d2808210303140c80005900c4c1a0b040d190004c40d42a4001688604140c10240b41c06c03409240e442646822000c02c180002cbe41c800c080310144c179210f22070540c0301c641141d01c03079401c61845080250090308450010040c1078015000c0d5105800a00c22500c07940c400c07070410341e00d0380003100030590540d0200b2082c0d40e000d4040c0e0880c8889c42c0700c0b0724205000d1640c0b0321901c1d00c4c0502c3e03002e49000c25607171940d94040901d000c1300b03142c0b0404580004040e00b401c20b05403c81c0b0481440c1c440e0702004c4c000c0090a95540e2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 607895062 1250 607893812 607893823
    0x1050108190e0a06140a0218010c140d03050106020f01140105100507050a0605040c0b09030606040b06090411120708070801060315080d082a07020607050115030c03030801060504030807110102 84
    0x2c8008450f6041900c1c540302009008061617420344040d601e0001d1208a828000c40c2d0762042500090741140c1546001910a114408000ca0300444941c010850000b4200400c1c070b00501a6075000c141d5525101c03019083c4101000d2401d0f4990500c00e0303440d00742e0b105444881c11110292207004e0724907c3d490f4211268016a40700400c60302680320420107000e1150040b1f03020f02d004080b000c1c8055510900d225491003110011a015000701c0001141460303d984224040e49020700b004d03207010500d200150445041d00b1031004038400100380810b000c0a01d0030000d0b030050803414210b00c1070505030303005040010144a40d030200b41c0c40311041900c0c41c00c51180c410040c030f41d050403503902800302c0740d0103028054112543c80e45035034000c004807134642100c40d004d200074001d05401803030141582c00744811031340322400940717041d074131040140089141c1c100c0380b00045001e2244002d04504608d0300030710188041e0700c4082007050030f00003400403c11150031500940ea21803030302014074001e0070040c0d0915 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 607896312 1250 607895062 607895081
    0x1020312060d17090112060e160306080307060615050a0c080f040b0301060203030a110922061502060703050f040b13151107030e0303030f012c040c080c090105010819 73
    0x40040042408020070201504138000240c0b1485000345000d00400200d4000303124000c4403400e00000701d1101e0042c0442d07558107075054600400c030640c0b43c40e441c5245910040080303420b140d035200d040000e0300f03541c42c0c80c940c4030119140903450941d180d00c0051600d003103440d0207000030340e000031800f41d40d1444404441c010f1000f034410903240d40e0741e5a030180d203d4100703c03000040701c0c5c01c0580c00001c400d80441260f661074001404541c80c2082440d4003580000710320440380b401035840c10003260600c0780c01c411011070005035000305814981098000d064403000760540414403114024040010060019698091003964244c001c08110303042c802c4558400f007100302042c3d81b400c000507004203c46001018800d02035182c0d0000f1089080516a507440100d52101203070940400500101448107070b00e511013181e032a054a101c4880304601c0701802c4050340d045641800c0768000f0405400c051048440c05030701187c44402d42d62401c0000b81c41d00c2001400c440c250340081c035030113529450300d074007040c1c21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 607897562 1250 607896312 607896323
    0x603090307050703030c020f040e0d030e071a040f081906090305070c0b090a0e010b090d050a0503040609140603160516050f07030302160609030209041a040609030f0c0201020312060d 80
    0x1390b0702e040180104c080e950701a030180240d56803400241c140350080240c0c0155000003090942d005501c21802803d42d41c829200d2402800c0d400240c00302880c0b044030080d00500f50440e5610300c1c00c100260119071030f41c420091500082220104040700c10f400300c01e1280c002c2400305146210380b80458140c415000010075601180754040b82c0c01c100310010309044207056a5403400300f034840c0300700c0c01000340034421308908180801048800341403132032011a4052042d011100134100b42e90311f0341d0960f00243c0120000504050003000303482004e03e000e120300d40c025119140b440c00c02801038904d1208900111040c4200000c1c000c0c0c0c2500190f07403050305140c000040d201c1c40c2d80d811041c152181c09503c02030700180706128900349030300803100c480001c503a05a00d0b001c210524513801d2244d04c210040c0141c0740b641100029412440d4000b20091180748507400005001042d031502030191040c402c0c0f084200503c0d0712034180181d03000012a400c5100300300b035400c42540c2d0300c40041c0d29080c404a00608 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 607898812 1250 607897562 607897573
    0xa1101140f0a02310b0c03070c0510020c010c02120d081e01060801031709100302070506010632090301090318210605091612061d0705060309030705 65
    0xc09901400d1809900655203a500d030351141c9103a481070703016008071a0b18a0652041c0201619103007910302c0c031041903441ca440c031031643c0c0304143d00050b0444180c10400b5000003581504000c0c07690100c50183c00212460100b00c040c800c8000d60780d61803a041e081c1800b1a6203405000c0d5558038201c0e03007101c2901c00486002c184a1040101140c0b41903501ea030543d030340c8020002d020b0b444045d80354141c40140c1c0c1c41c1007a5a181d52110906240b035003841000500040041c120b04c0d4803641c030205400343c89500c0250362150189030603464488142d00ca10100b0a01140e40d0070070310203a1340003c110040343d003030105402c0f0000035110f002e8420901d00d01d0741507182608240c201a084801c203041103500490f44001c031a92100d00445491011601c48519200c080744080014601e03405650090603040460349008000c428411902c0c40035040183c1e68038040601c5400c000540c0243c52100700844c5140d03950348003400e50356035212580d015072803140d28040009aaa9034080040c0d4401c0c3d60402c08944 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 607900062 1250 607898812 607898831
    0x80907090f020706110a0f2d0801051002010606120207060f020d060503060a020412030c050c0a06051306261f18180209060f0a12050618160b0a1101 65
    0x200250b2000400702d4525041510211106600f402038814102032501c07001d900391110300b42160b80d0210444071307148000f145605180098540a07528a4840c23807a141c4500c6075051100700700040e005d040c07244046a040040c04d02909034491100e0845540401d00582c944245140030b1029040400041a09a2005c10f038030b104451950032145c203c800550983d0596160b50920b5020382c8512301501c1384003284507803814001381c8a50340d00400c4c02e00420a641c0030500c41800110101e15580c401c5000901c0481c0500c82e01c041d0100404c0202800e09020018a030081c6a0b0720b0402254224000d443c620040000c41d80c50700d907140310500030810516500c00d1619071280c1c1024181c05032460301c02d03625081140f88600000050481d40d0303034004240d42d0b065a00c48041180c2211a8078043c2d8000c101400f000546030b40004018695510a101400c8a440c10700210b01020b0880101c469141d48080f800c5070206506c0354262003a94642c0d07034100c2c4d4401d6121000e640c1c0b8003c4800749a590b40c40c02000d0f5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 607901312 1250 607900062 607900091
    0x13030e040e0718020c19030e012a300e10021509070b070305040f1517060102010b12010504050f060c0a030507020c0d03050304060b0114040e090c1906020c0a0f0608090709 75
    0x603001141719495051000c15500d004552222003c0c26068582004100080352a0000030745001072910555515004040111001040d44010070031f581004c50080c61040c0d0301c8ce04805501c0c2e0b09007065540d1104000103040003540c501030b09801809084514020a80710901444184090481031841c1991010a0b14004100e540140320b250354901a03000b0108507509034203940c84103e20641d80f4405600c54201e04202180d00c0604014107541d6282c1c400d0125031600c59a050f814070350403000103624a0700703007071460a22441000e2902550804810811508a40f01c15038161089078500002d0a943d202c2060303140a10010001350b00c0780c0c60361580001c0583c03200041d031007284035440070700002e0300d054010b4500c4030307078000030030060901804140061035404610942c0f00401380e089507440441e50000c546580c408030303000340c0400c441c1c0b8414450306070100000c9102000903a4103004061910141c82100086405035504000310840482c05104d0104600070250000aa00700b0207521030310942c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 607902562 1250 607901312 607901353
    0x5130b12031c021318380a0501140307030b06030103061a01140904090f060e0304081507300c0806011d0603012c13030e040e0718020c 59
    0x2101504607451039000d03032549402620080c180030740b013090b14035041c441c1d0503010350400701801680750380d65a00d0781503134520402d2188941d450710600c000c280855000b81e600c640f03850303c1c696000f4407424200708620b0740e00c1721001c40424281c40d44140c1b02e8031076030411000f40007a072505592045003c0004814030420f035029000346250010160525603040c0015643c1900c20103800090003414000c1c84047d091540244c4103042c4034411000303440c0c043c2d41d201710440b52071007072022541e440890f052011103800c010242d0301c1e0300c01004201991904a0700184584201c000180f03098854031030a11401c1800c4159a2514500c440244035064014500615003802141d040307001450358544a2514001c8101800c099400a402c440c51a0f08190285001c4c24142d90b50003078030142e002c0712050003052a00d0a41c050610751031100450031242c1402860501c0080d1903920aa260403d0f000310600000749000450f003464100c0f41d2543c0164402d94024080c08000461600800680c902805441d070032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 607903812 1250 607902562 607902577
    0x1080c13140f0117040b15190e060136180504020307060c08040312050f120a0f050f04030c0201020f2d0f03121302060c01020904050901110405130b1203 67
    0x3002c40840c5440001183c012004039030745502c02e1040390214010841d1110216803069180c1158960b0154a0b40071941110072228148400da032090018800d4041c0c0800e40c582050302441c0003010915615a1402030300c481c02e021412840f84860800c0040000c140305000602c000581000f5910008804601030601114224030900581c6c00114440e40291004c0740d64036004802541428115920404e10740c11900580d0113001d020b00002000c90103110080041e91400582c1956600b0600040e5099510544603011081c5c206000c10007400c00840900390701c25050319065410325603900051b4106480c80000c90940c1c0220005078854009454180703000702e02c601d158480c500040c1c805140c582c5044107075031100b50800c2140c800d28074840e50b1740c2e682011601d0540310101d089a07000680c00c2e40110300b10102650041004413803490540300c1c45500c882e000b0028010751304030b05400e02141c400e0b13024444c4507031a04058150705161540c82524402006480704910200d00180d2175500e070025503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 607905062 1250 607903812 607903819
    0x50103061a0307080307140703050a03090f05010c02010509130b060310060e1203040608040c050a23120c061c050403050915040e0601110f1005070f0302130501080c1314 74
    0x90810751600b000a40d030320444280f00055418410180c3e82d9210700364142198021901c46c006c000b1010580c02d00c224011140309482c2c1d0380c922494001c1d1000c1c0105103501c80c905000c8109980c02c0940d801c00d08072644039504607905030580544080080040400300d034416044100403040101c6841c01e0308a1000342c4480b43c54074000164107200300f003c034411000c2848000d8200b07000400000340241c2c0a1600540706080d03044031703180c660022500c80c3c203560b4040204d000900c201c8078001007280303504034075141e030076030781d01040174010440c3d281d5071450348544601580c000100400707015034159940c281000c15241c03d0045080c00d08008041da08502d99252141c80694950741300050054111800c860350001820105c2e03803080010f56030921f6070b03031711100c0318094910403495851040c024503c0381c21122000080b41d007802107006003043c50045400b018944100020394410140c01d0a08046480c01d1804020a40e40c21514855038000c800c8040001103481c00007040e0b0160101a5040300b94054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 607906312 1250 607905062 607905101
    0x20f100603020d32010207020a05010c0209010e0c0403050a081338120f04120507080904090501090b0703060317030c0a0807020c150706060f052d0405010306 69
    0x9445050480303049100083d48002008003c10019203d0b50320f5058040802c0c0340100d403003090000c0c0c00c0c0c65140d01211303480581d5000070590114a4443c2c1c099014160a10700340c61540300d1580811b444030018041d07002ea0001d03c50000e85658004401c840185d544202035540014542c9004125a00840c441c04000c1c5000b40300070555100381440502d0070010307100000b00318100581007100440d0010301c0300351030301020410122007070944444540075040c0c080c030421161425003020b000307102c0305c03000c86010444204180700106a82d01d003518501c84080f900082e01d02c0c40342c03070b0080c01072188140080440100204004443e601740e80000c0480380503513078034034202c0c0360904c100416200c100c80b455007001041c407042d0010741c400c159096210400e801190484000c0ca00040c603e0b21460130300c0009802d00041d0403040000328003841e4024040101c0c014911414800010741e80380c5240c40f004104400b92040e50403894900002038440c1d903001d0b008000c1d42d40c480c01d200c4050400804a088940c03180c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 607907562 1250 607906312 607906333
    0xd02031b01020a0906030506030a0f150c0f02210904110a031a060307030b01140327240703020d05010e090d0c0816080f043002010f0c05010e0706020f 66
    0x103000b1a00e5081407540c5100c4e001c1e0401c0700640050002402c1c40750144101c515000000e0112a01491143d01903007206001c00b00034403450054840720200c0004101824070305003d05a00003620a038002400e5444044108045021200074000c82114580c0641018010f80b40360741c2780c40040c000c2d0b003c80da0301800301c150820658040c650f141303408035401c50010000100881d1282c0c0c44006202c03814544601500404004c0301a0b0f50401d0b02c1a0806400c40002e110140350240c0d42480c0002d03901c07002d451001d880840f4440080c1ca0381d103160404102580c000307040c2c0c511a0741140c0041721740755000c04c86540c48018603440d80c0802c0b2a00003483c0300b102110000b0500031881c000e5180c1c0e1060405140c1002c082d00155130f510031110458980c8410702c264509240f42002800c00380021b48070400b904295103106100040792103030341e10141c2c042c45c070344200980d80c000184420703c1c2982c102240f030358100d032801900602c2c8c07036220f500c424001d9480104110f603012030301c036801e503165070200c5181c12174 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 607908812 1250 607907562 607907617
    0x917070b07080c0708030604020c100c0f0305060d0807020d120c0b070c0b06010f05090607121e0903030323040f03090f05030c041d151f06080406050a0b030d0203 71
    0x2c2c151000c800741007040c80443d0009900000450340120094401750402d03c3e0080828a009201103004c4051922850186a01c562012100740f001040340b4040c403407820140040381ca580240302d00038140c5240044c2e250195185c0a030241131042e405010005140d0b840714000300400120070301212800121030100d072143e4854010304040c5900310481c41c819864090042d18004440081c500c01c0c0641270100010681e039020242000c1400b4080100c45445080d000800070901345402c2c42c511134208900c280c400d40d00036107800540e541800c0000e140d4081015066004140341c02c1080b40000d0300c0104807c02101d95541c0c03104c280700383ca800d407006440c0e45040343c21a00e18010b032070b0594000c20309a0968501500555282201c01031644404250a401c142c00c000f440f12a00810103182d00c00d0003000a0703a0359000103080c080b1035000381424240ad800030318824002d4406070100c2d403210003140d4000c00070341c0401441e100060448080400020f0080c0d05c9401c259117074000703000315003116400b016 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 607910062 1250 607908812 607908827
    0x60f05090105161e03030e10090305030f040201030b0d11041401082d030f0c0d020601051806030f07090f061401050f0c03090a1205010f0603110f01030917070b07 71
    0x1605844481c148220394a09001850f08040c050716210794014840200022441e00e0080e190700940d80410a01106d8500520708804035040c00b2000f4641008100031947c028241c90300203190090230407254540d4001207001d0086500c460b5071188a402e414000c01c4442a41e21244035800e8405016040f0500b0052a9146017485040c400d5000314110901c6c1100b080e240304070068580e980c10015100d002015807071030b000223003002d0b122540096120044101085143c05099091000384002e40c1400040b5151500000d4540010f006440c040340b695a014003030380358206560002c4030206641d8018460280441c681b01184c0d1525004011a4011001d08201c0703d642040c0c40c0c8610305810041c03d0304d015840740c00041ca29000074081c1000c6545c445050394028918000b00132807491044c20071071f00711a0444c1c00800a50314044042001840106014003c40030461b00c18244241c1c020058001d000c2d5048010b0501d10945884440d01c0303580030191150600030418181541d58210f02600d410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 607911312 1250 607910062 607910077
    0x90c1c0302160b0a0e010519020c0a0b0f18060c010903020106090b0301090503070215370f0207031509080301260703051506041d01140604090206041e05120601060f05 73
    0x1c0500f005603131852400703a83c024604600615041d440c20010010026050664910100040e004910b0200013807410040201c054400b00a003203151101110080741d451080e00060000c0343c1f4413070401a0f01d540d6041c15558011205d9000744207864a41c60b0090080010303015450303080d0b150844041203410f0500c0782281c0240d00100540c41c1002e19000c00040d0b49507140e40401d44402002600e03003604030340c0b440c456660742c4178103010307041403074402d00c0c4840001c2c00350710f2001c0210080c60403014a500041803000c803900440900d4111482c0703610b4201500d84420060002200007000141c0003410129202c101c6111242a54840108001150319800c40384005000b5a101d1f1049025401d0801a0150040c4009100007081144a1a01030507140350300c03142c1d40b0607550f4185c00001902c842c0940740c0e014804807401c00254005031700251482c0514003840c0c07480600c11000107a94107860f4045070160030001c0c0450184030960140e207a40c0c0342c2c2406024001100d40740d48031039140c06041a280384 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 607912562 1250 607911312 607911329
    0x201110405190b0706020304030314060916030f0c091a1903020d14070c02040c0f050f210c07140a03120203091c03140c03040302070608090c1c030216 66
    0x52034a080708200281e07800010b07071018402c1103140001c8803030502c001812154440c8a0258a03413a103410040d00b10340040f4030300302d0140301d0001008125964054000e501801100c4682030241c0390201c100c0040108400c080612441e05a034020156006408030049a0140c65503003001c07010711902d50b20b680903800c00fa0041c1c4030920380081126000b50003501c01100d0140c1d0010b000d0898400c0510380103415201400421034034125103040d410103028103190f240850902c482109110080280240318851074601707010004501c0803a40d01d0b20342e6064440400c030f0030542409081c00c03242c0590710b522401c02101c134100c03407400340510f800e804207100e404c1c41c7d016104c10301460200b05a81d4040d6200034290340489c0110080092000070300809580c100c4060b40e4006820a180e10108942d03030406080425843c00a10400001a600140140903642c0e94601500980c42c1c050a00749895424a0915480740c803600800c00c5240b21280740c42070442c026401c80303100d401011904402001c0d2402001c24 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 607913669 1107 607912562 607912567
    0x81204081e0307030e160b0c0705030a030e03071d060607060b030709020d06050f031009050a0c03050a0c0b03150f03070b040e01091d0706140d02030a1407020111 71
    0x51a400220700500301e0030b90004e091881d4545602c650480c1403000623140318040800d202940081902174104e40c600e8001e442c000e0041c00303201d8441400392041280c0020040741040c0405402000c5003c1c2c1c81c460345400044c004140d0000c0f00c2522001e0321031811030b60a1300c0401c07460004000f2203000607180c200003415441500c001e0703031105105040698420049540c0800c000241c40003145002442c05254501a400d00b581154080e044901d024000001e0000126400f00b44c1032149100010b00354441e10b058074075002c01d8541c80e50313000c0e02808091040c1049045145e145400404482e2555a101803400c11a805500700b0985440c21000421001845018501c01d81100070200c1c041c044003904581c1c2d4401c1c0714401d860821104102455460703c81c0e4040319181e8803a05400d540d24603188166902401c9a4201c140d0010302030700c0015603044c418807c031404004958003c51 = true := by decide +kernel

theorem cover : BRFrame.Cov 607733812 607913669 := by
  have h0 := BRFrame.cov_init 607733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 607733812 ≤ n) (h2 : n < 607913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
