-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4513
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:51:57.201613+00:00
-- url     : https://prove2.me/submissions/dabe2cd5-a046-4f65-8a32-b7f8a7256b28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 811510791 ≤ n < 811690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 811512041 1250 811510791 811510871
    0x8101113090c090b030c04060c03021002190801090e0705010e0f1e01180e010603090809040e100e031e0d060e1e0a050c0714010615020303011508062101 67
    0x500f61001800d4000e000d581035091000c3d8411003030203940248402e024014011005041c000c120054200809010030341d500c00c3c4c80030140c00351008642920b404038807030100224030702c000b5000740700301c0c251032000400810389000c00440c0c401c0060b262141e08508580344c00040c90320356a90907020204030a2581d421036151b02d0005260135403c00481d000200740c80002d00916088105d000e0440390759103030103d0205041e05103c0b0302da10402d22456030043c60038050f140c9480010400c8152801510010400c0040310b074103603034503031180e04190002851840803202e0560005400342c0711400c208000010159140c0d11521203404090f1590303040c054500503280c05030720700c441c81345604c01400076003401103041603024030499001300c05004082c802c240386c0e40d40412200354841c1c001001a0000301e4500780d000761019480c1c0e0300a001c0d04c800300051354550820140505410b502485001d81820100c424100e0348000d481610440725480b5500c1d0340684013036030342468201040c07403000c100d0500c642400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 811513291 1250 811512041 811512047
    0x206040b0d1401080c0907030f0b04050703050403020c01090807170f0d020f0f0d050304033e0c1203070803041103120415090501051803030405090c04060f050408101113090c 76
    0x8164002413843e4407000d0400103984848108503082212420042000c58100d5101c9014000c0c0912194000e880c20003003010f0315a05d0f802031402076000f6001d070381c8154101b100440d4076201d24002c001e46684000e10030002c070101000c501034400c51400503100d465001c82d4250b820305042d02903100050744650340004140f40e05000d01400004d6880080110b07006650029245000040c00601842680c0c2402500c1929034030300e910303100120130030b50242419405241034666440c440303e040e80d4452580e5142c9039040044030061041c038001c00840c1491115a0780720490303480100101c511802003c540070380303920200100700e13620b48000c08103031300c0da81021032018420074500c81c10010082c14210410061740c00a088651040c2040c800800c520250404245103100355032050750011038420403c4000041c00c000b6000313542d1981d603a10700b0040200c8080301c16010307074020282150020710381e01c0f650300e0242d4891540240300c0551305080c0040e50800b081255078550150b030480c0e444200501c92568 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 811514541 1250 811513291 811513331
    0x110a03030804051c021002031801380607020607050f0604030c061b080a0b010912081e0f1603090803311a07032709110705190206040b0d 60
    0x20081c00e40c0c4d14800e0050074000e55403c01c0e9074a180425038000301143c5c5001140c0480301c04941d494000b07010340c1101a12805200c08408142c500d001c15000442002010015641e0a1078038020701c0c80b03081071115001c00102e6440580300302c40300d2140e00003000350144180b000910840c0130b80c480041d500c840e800c0c0201690401c00c1203400d8165521840e1151540191b04140c112021030400200c150300140140c421184c0344c0c1000103070014940c0c8000400902800030040c05200010300601c14484407500c0e2414000c2c034448600018051184ac0c0d007046440b906010101d01a240106200755a90002401c42d44601c4e0010785012524080c602506049104026500941007a81112074509181210030180c0d9a1221240d10780000301c080034544071764045840d200300d03101502c1a02c0820b034804481281d00e449440c80c0c90341045040041844400c0c190340469030490003600e030040d8400310007000954402c00c00c0ba0310043c14000441d101d80c0341c20203400c09407400500016200d01068048030815 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 811515791 1250 811514541 811514563
    0x15041208190906080f1b0409020405040609090305030420040c0e0a080706020d0309320c0d0206030105040b0a030b0a06080105090a02031507020a0f11010e040603050d0c110a0303080405 81
    0x1100c00c0d8003c2080540c052482680440d13031004408041c0c0314a454102d003602000e01c03a510b034410100d00801c0c00100355000b4411648102c90402059654003d10030503904000d00c081c01054091002602103203003a0a92100c20b006092800d00201d5140c00060440e201414035070005544610b84500c18103240c0801340203066024014036080d40303001c00007556008423501e42c2040546590800d0100500260b035031001030140c0714441d00700d1141e1024824458080c0021f080c0d58810355203245074a0905118250009802600d0300340366a0a090502000d0719402e140c0c41d8021016503000000700303004401d00c80c041c40207603002044051521428509490f0080c26141d0f90350006034a5100580c2c0c0001e8041164041003081100359607113100c16802c01e8294038000e0041944045242d08004c0100e0003615001c100341c0b90420740002c07000910044a00034040180260b1002c6042d9020320f00480d030251105118190040851058a000c134410441581c801c4003c02c1c8514140000c002090041030104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 811517041 1250 811515791 811515797
    0xa0903080f09120109020901090b06041d0f1b03161b0309150e0906091e04030c06050901231012050c030d050c03091e030a1406070e0d021504120819 65
    0x605d0103800013044950306114401d94169601303e03000d102d032a00c00548005101041c40210303a030407280c008400c2d0000031503241143c0040d240c0000d0300c3c4c6010f02e59282c035038038640d040c603811507580b0140d01039001c08201d42030090160581c090074001c070b51107190b070b4503462081d501e9404980c03614172070b04c823132102812506041c010701c21044082900d425035102e81c403400c116421001034450b4084031b0707054009446032028030a01c070350030081495040821040ca840c0f10341b9081150790b903140c000340d0807201d0034080341c450301d40260044a18544021446900140055141c25540c1d589040c006009462880222030300c2d0031820980c2c1d21450300f4041d08a100440d03007822403510f900b082c4110745a20880800c2445900c19041c1040441000701404418000103411107000d03d4a0703003000c50900c2c00c039450308400f034445e01000a038080e100d040703070148500e0003a00242010307100f130307003081080d00f80405000b01e0781c502880001441046046066006402038a400c1d98424003408900e051000000c502014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 811518291 1250 811517041 811517051
    0x1120e030d050a0603050607020123061c0303020c030a0315080105070507200603070201021332040e070609031a0c03060d050a060218091015050a0903080f091201 71
    0x2100010046504200c02124005420342d103407a001d0000744407a1300080c1441c41400100f050050f01544100306400e15a4441d81d2001505030b80b000541a04a07a0150020354200d01000c4504e0416a2900c095100741809402c000b10404541e103140c0100414000217519a000100030801e00700148001d0184c0740003c0c0000d18080102030140c1c032030911300a115020780c1286d444080c003000c2e44c02000740401020030343d8030f081503c8001c4c081e401060324901ca00b404914001850704001d40902e031001c1c02c0901031400003004908000720601c507503d04580140e144c0c03051100101c1c041c001c0601a01044d180c00b41c1d900d06500b4402d010400d8008605642c1c800d0b281808803c0e80310000b031b20340c46072080340c10410303241d200d141c11804c2c60403698008003a5400170407060500d84910f0240001184103952403052559041100e841c2800c89204d9031a031408030410074a1070610582c01403080022506200e0101c9036070741c0c0c4090070790340a9030526507200c20115001540e0700d0041480c80081d0305107802444 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 811519541 1250 811518291 811518311
    0xb060d0b040e1207170301210314043b060103020a1103030a051f03020d110d06060902031602121801170702030a030c17010506160b04140f1605010f03091209050112 72
    0x1480301d0302d2340c1c80b01424000b154101003502c41e00c0b10000c40760000c050251100d50310500090008620840101807031407a1030008100c0b904c004202d00c40b50051191421a5181c0400640003584180c00f074004000350412a910098400c10056000b500280c0c800100c918011040c100304d844810501030700b0b00c042c0082080543c1e50102c1141800b03400403006c00d24641c0780c1000450b4600034020040c00241130440008503280c01d0350145102d070350010640300c01100003140c126103034400010445001c0c00c05200c480e406005040c0301d0a25070314107041c4100740388240362201c02010f1041301d20100607400081c030441065450300605241400e90b007881800092608040040c000050094038040c1c040070594512002401400207096500103840c122282014101081d4401e11000381a00a114100309003420401c00101c000000601040d20781b280e0781040011211500c8005011003090f40342e5600703401140343c1da2507001c2203601e2500c0300c0744c100e86040000740250076a0305100b16424a0301c0420300f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 811520791 1250 811519541 811519559
    0x1a250b061c0303110c01050a0c0305061801090b0f060313030201060b09130e1f050604061202060414040b1002010911010816030b120613150b060d0b040e1207170301 72
    0x401c410341c18100882c40e1504500c40c1007190240d90019041136084c0020300c00400c00b181c0c03224107071581d150360a0261350744a03130600c1046050f51007141c18030041034004001e0040d0780d606c040300c50a001082000080810700004110390001c0d200d94498903011450942015024840c0070300800a074800d01c1c0c186030840000030300c5510078250051507035071104a10141010240301070080f4111443c01002e0301c2e540c004d11440280802c440b002d0155181400100340c02201008800c4050760081440d840d050603e8501944501189038030782c5c0054541412042c40d68850708161030001c0d941c1c1c0000790000705424030700c000e00031041c50076050055840a200442e0b48103621034040070f00c01d04000c42c0180240000c520f440c1702c3c284d000703805402540280300002780250f1100720f13024002c1003e040041d9801403504100c842c08000d00e60300250400440101d09002c0c2c0084040d150000c01c00100c620446104900f0726811016813581e200c40042d40408208031000050600281001042e08640c1811400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 811522041 1250 811520791 811520839
    0x120109052409090a23070f0f03031818091a0f0703180b090f0d0203040501020316060e15190b0d1e0503040b04051e0a1a250b06 56
    0x1c039008040c0140095110002040394030310040d4000000d9030041c0031059070650003070099001154500480c080001e080480020381c506450b04000110301030f610710f075802c0d1100d030010320701e408030310310007880000310311013001042c41c80c600d03a0610110707403544180307040d014214401c4442010440300c00e040c043d4090300541515840f1903582000541402c9400000e040010508802406c3d101814100410314002003408096180308104890b080426420140e0300d9000d54003039680142d10511050300b49641e402c80300481c050048100080c0c000201d5081c50030146031001782100b02d0f85003014081c50000c1c5041e0260b0340400e5038020040a03141000141c3d4046500e4400f070300bc80d0b9000e002c00c50301d110320780d52585d880d54017004070f0384e880395544407420700c503002485014403510420110f5250121449050001c43d90b0003441d090083d804c2c034400d900071468072502001141002e01c030742c01d000c0b04101000d20303101e00c615410902c00c0c4220301d06892041030081205024031121800200004004480 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 811523291 1250 811522041 811522111
    0x80702010510030b070908061e06031c080a06050301021908070908060a0b150309010501143309030109080d0617120307022d060c04060509120c0612010905 68
    0x811807140c450480031206d1a0a43e000110300340164404d10444d000e00000e82407001c008a1044101503551104140c1c40f5444102d0740314681a0386041010040d200d801200d92014083e0343c000750a035110302c0400c1c02c90b040241c80c4042040c1035442d410340b19803c400010342c80220340c90b0005442d420050285e448800142c03010002540752000f01300241e907124440f10700c0038203e60076143c891520b40e42c01c90180000384a4400d03900d900c0c0c0083c2d810750421051001c104207611600d552203842100459405144803503105406a000707010600095070207010f00500c00d0b000e0007009440c0c50b0890101030481c0caa40c2d0000b00910680416810b00100118031202c130a900303946110344940d0b400a0623424070020b41d846860246d9200b0350130070780c1c10805c131003111103100003030840c4c020b83c2c2c079084144070314866409440003144081c088040540303484110708207940922000d50340910444c0002c03c103960030242c0745c80c94039203141005001041d0b00c2d1207910340c0044c00d4802da034400d140d0044245000e9072800a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 811524541 1250 811523291 811523303
    0x1103010e0c01051c050405060703050903090d1b0e09030a0909150b0d02073c02091602100e0f1603020d02010c0503090d110a0501451508070201051003 66
    0x58a40c00d45409100b0815401c139045800344120700c1d1034680151200c80894443c3c0100c1d25141c0858100d12000080e51007100c000f4110860070714903038645080c0910b0541c00c0582d0ba1411440100d26948000c088074040d20a00b002103481c0d0240840241050407180c1001e04214903000250381d2414050050360112040a041207998039102443c0070301030302c0340000140004002d418804600c9901d903005521020b05070b00e5447c05800c40c445a000b00d00451640a9404400c96011030f0a030031004000146d6401180100e640215244c0c4121095400d034000f149001e40000f14040102c000a208011320701d5840400c2d540a02d080d9170000d10344030721180010f81000707802e40c0f0450400c9002c00845949800092600c03a86d000140350441550703c004034014004d12841c3c2c000501c1d0b50180c050781c018444046402910000926408040100914105040a02ca9a04680c402c05c25044034a028007402d8001e14240e4410190240c405c21018041804580c03409040040b40c4402800f9407003a40c0d4405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 811525791 1250 811524541 811524547
    0x2803080907120305030103030f0c0507170a14060405071a031f080a260c1c090f0303090801201b0c18040b09010c140d140109091103010e0c0105 63
    0x690054584411034100e0119200700b0082c1c0c00605030014082e42c1201c1c030a82e038030901a0b14002d0200c1c0c0342000381100800c240c2c4003d800b4400e03030725910007100744904040e00301c401407060750315410b0b0328000a05d4201c182d60011014042404814445480600040c0d11000360903441c1031005000783c8001003a170382d5046680708008004c19a0468200000c024010840d6031101c20b9092018108040d00d4a002c1c4001114600b0109040024251070f25072100c1406032078001000b0350440f01c1c00170120400070800850b03210104070a008a4140c2000d10301076507030311051505141240b42190ba070100090041a801030110b5030240002d0111100c03d02c51458228454400a0410345030030b0070100c0040c1d1107070344441c00082c426a003200080c4654040c09400800d40c0341c07002c0080c2203c000b040c0c40400508030321000c0c2101041f80f8001c1000c19200031000400140e84096010b03194002c0e04103040050311082c40b8024415120ba0b91400b00700e0480080001286c0c0c040c0c055529503103c0030945c1804404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 811527041 1250 811525791 811525801
    0x141501050405100809060a0e0a030e130207030906031410140a090f0f06240503150301020a0c1b0e061201060906090603050f151b0c010e01020a02280308 67
    0x9882079400415000c0e01c04000b500380b03440302030301442085401000034401c00000512141c030030b0144041741d015003c00791004420a890465010302007402080c1c0200840141c02c89014444c402094214040d545100e12141007020003401e4070701c290501e4000160802c03d108000300d940403060121001140340c02c5041281320040703410000c1c140e000c2c580191500203075032410341d25500901e0052641c8041005510380300c00c024010480080070554400c0a00b15180088038020801140c01c0303401000807805034405030780002c0c2607a10010b040d4bc0042e00c62400c2d10204040350141c82e0500c40304100e00c0c00c0803401c04e82604200c3d0402005c0c0792250710740c00b8003055145000e611140c00f5040012062204036119010800038082920003101d0501c18540444c8141401280305400c03200c09001c1c8030140d884420000e8071b410040e40c1c130340c9001d10040110754070a4400340300d8070440f05480800945c80741900b020280c1001c64072401c0c41c0702102800040c00660f50549401d020031075050030805860340751 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 811528291 1250 811527041 811527047
    0x210209010c020a08010519091208071719060503011407080a06170601060f021f090c08061906060c020f0405090c10020327030c01030f020906041202030606010201141501 74
    0x11402010350001c0c840360010030012011b4000d148180401810030150700d4926050340c2c121000c0300000303004401d5400b19120018800c0c20a160004c105203807140d558018140e144820f4074043e40d902040240d004c0d40814260003a000d400010078040f0000c0109100020788041040f000070150020000808001400301c142d66100101030951144020a0000c07001e940e99a0b0300d0b02070280c04042125030412043c02c40c0300141038403100b0f030080d200b5454008007440001c085d25050900702c442c81c03580d40011500901c1080114422000c54a01c5c0030400e108a42030002c480311500407d0030041904285070168840d2002d030400700e001502c1c0014a0b540d08108141800341ea04011035020366540d9044c0c1e03040b80c0c008003804d100b4201c401c1da2884058884820b0607101d00b101103268240d00f00f2130580301c4560003a0310071211141080c40c058030b0032551200013812030740b2035000484560640c09a60301541020031030b890f442203082c002040f41c80c0f908000050034110080c0b800e40320308030380b5100d03003c0b5901c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 811529541 1250 811528291 811528307
    0xf100518060409150509060306040203150907090f05070f020c030a02150f04030b0907080a0c0306021b030309150f0c09060a05040905070323241203071406010621020901 74
    0xe43c640c1c007005650200100c400c1c940d02c00748200d03403041203210007041c0c0724070b80402c2803805154020018800e480d0b86280500b01d560b0014400c00d2070780904c4200265040003401042d5000a880e80000341d03900d454640905950044244a411075100e0849480144c4001030b05441ca42d8040f01d0403e0300c2c1c070342c21140c03803c2e03480f40c0c910510b50301c00041000000c2103003c1048034002c0f1190000d40340340342d88411a00b0b0703442d004240e003d8590070a82e40b040020800c154010886580e00c7d894809a0b040e400002501c0d691003920303100c1882c1c0c8a00c50141094030000d003010f40180906280c0d5041d401c00030a124214041c4100c402d00c074140001c0c9140d207150140003250300801c0110000d000600d04840060010206d07c156124510300109202c2268418040d00a00c20b5804d030403149122203800350f01c074401044440c06a90444680030070b50b0b9000d00c042018182e458400c0d01030158031724000307404030304100b0180e0141c001d1203801c608050640400b881440000038140000603240ca02090040b00e600c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 811530791 1250 811529541 811529549
    0x10f06030c0f1d0c160f24020f041509080a030e042f0903160305010f0b0d03021207111c03090503190f02220b0f1005180604 55
    0x186401000010010000d80325000c90300d0700722001e5401035844030206081040c6810f00128562000002410344516202800400d000d100103001e01d40216910324038030402d01c64056542c99180f5800303a50502491114000140c0c203000254101600518594000d020b9409040090486940d500e120184509240002400303544102c0d8070050341800e000d420321038480740c0b00c0e0040f07040c40790f0807404000c40c0c450807800c00540d180d11894403011082d8000903810080f48958180901e954880d1000880303071211000c0c500850000414030301019540d02100d40c4414410700805003c1420404645c010600d00403503001c1103105075856109140c0f88110406840c0c004d5801281c418851012407082492403c00d41d20070b46486003030303548520400daa40c83d80d41141580b14410041d02500148140040c0403a0f0f0b440540066940f46050021110220100384140c0d9526500c140c194654074000030281c82915040e100940c180000c80c000409611a40002c0080c0b070100701032420642c2c5960044400034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 811532041 1250 811530791 811530821
    0x2d100215010b1e0301060813061107030305150111060a0f0b0d08090406211e02120615010f09090e16090e01050c030c0405240307031418030d0e01 64
    0x59a1280b4000556401000302c443c041c409a8044012000401003201e040c4e50f0252144265940d540c02160b8a03600b46a208460f540d4446091007180344c6000040d04400744a81c401265a151000c2d01391014030306545028100001000004c5c030528011541c070342c02150303c07000460300740e0010394480040d04000311501c0e0010b034101c0e18042400681d0020707100d5039008942c14056250b03110001c0141d0800031030307181c1c4c51800f50440c0320b000070440540102200c00b0400e0010400003140c0014841c0704401e0a10180d5400c00020010301c52001c030990503138040c0900300350f00f5000305072070014040101402203d0025039075022400140808100017040902c1d14940502d0007038903114100040e1a0508102c4035540c203000c0071605080030001960f03c1041c00340da80e2402c00c0e203090200300e00714001004464102c40d880303c20000e0098100c0c0154815203450f10b011500a014022400548600400302140312100800c00b558508000c02120808801c0034404175420382c291502038018100e0300344c13030140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 811533291 1250 811532041 811532083
    0x63103030f02010c020601060e0111160326040b030408210a15091808130e0903030f13020d03031d03030406050a110a050706090c08030d06052d1002 65
    0x101a44503520960340d10301c950084c043c20b50025420781e503440e820b00440010450806060b03085502c82d04010350030b08004c07011a40d80b09014244220384e0b0070141c00640302c040c1140780782d902d03855040800d10503086403021010315040c07501c88070031040d01001c0c00040211000040700410a6080d15079020355080b40e0345da188090906064010081c0700c016050000001040e20000d100011440f40c121701d20b501d503001e011a01015030b6554061b903c15115100e0743c610308000450800030700003d15100c3c0c0000002542e403824117500b0b084c400300c0300400103a00010b0201980380140c070f910903d03d00e00741d030604010540c5000748000c030103c0c200380100c00d070003403001008100034003030f4a400040c0103800d40041082020482181800b00e441841e5003140406d80401c0080300280099000140860040c1201d90240352070b14003e9040d68441605103c6154441400b8001403a00f900900009200c10712100c180808804045143c100c81100b15446076004141002c0c105000f1322000c0d180d0f4040d0020410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 811534541 1250 811533291 811533293
    0x30f0b040f08030a0e010b0a0b09040203180a050705090c03130b09010e0a0605010f05010c03170901060f0303051c0e070e0a0b0303190207050a0f090b01030912050a030b03010209063103 81
    0x82413072417604681582402181c003901c0c2400e80c02082916440d80740607162598600c20700c0301035800601040c1007070b2000000c02100210920940703001a00c900c0250100901e020300f003054101001d070000464400410900820400c40c450b20780ca440e903c005955040c0d03503003050305401000c865071802a68081d4a42c001c04210456203c0c6050f2180007801072030150b100c20044584c019001c1d4000d000c200d6201c40703c00b0340990400c01e1759103c0039180011489035103501e000910000e003a801140495004525001c4000030451100509004003600f0000c0804036500b0594440451182807040d82000d00401c106e5141034110000551014040f26901c0c0c0700b52018412003003060513040018050900702107414a804005c0c04110b80c2900c09039207505090841030001001082c040343d0502d50b0791041d180008039100075082148c5441d8452644404003100007a054420355081248281d1040100680d20f0b51a00150f0b07038028405040c00004c034052489070710158907007900d000c0c038455407514000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 811535791 1250 811534541 811534561
    0x14010c0c030803070e12010e1207061b0f080a090804180b06120402011d010504050405130b010b0306040c1e050a0c0c080a060b03010506030c151c061e030f0b040f0803 73
    0x70205590a5030401300b480200500b040c02c0352054105080380d50089e100486030421018040c241d07241c09900c00094034001c80499440c403031024220100881c00c4607100181c095006025564031040d0b1a1701445107402036669914944558007490b60801c1500c0702d04103000c1107d501060a40074080e00141c0d6409240150950182e030850703040b80040d80c0200b5250000072510302d15038116006031034072404c1500745004c020103001c0040c02c04001c10030604000000c5568038201e0360080800b6440c10303030f50b804d03da02800243e4000b24040310521080e001c25000200101002c441d00000d6441c0c119103c4400c0c040c111000800e046010349040802140403078000d074040b5402c03050314458038040260080c900141403d0390700c00c031042030741500f010102d03110a0804410000460000e2600c251600411481b010700c40e040c0c11030b4004080350361f410b0600c403000600404a580a00101c0d071000d18501c3c5542d082c1154030b0b91207005100c03000d038402180130003181781d50810071240d2205003a500c0f0304d041007200c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 811537041 1250 811535791 811535807
    0x2060c03090a1e0b040e0f0408090303210c0406050f090316080f0d08060d060b04150e010509010b0c0d050f1608091f0f0311090d051c03050114010c0c03080307 70
    0xd0f8004240400e0001800b400c038900700ca0480314503100d040d581c3d075214080c5150303608009009076030803801048015110740c0e003840141000700201c4203100da05299039081c0307403010350024601d82c13044a0401c018841e00d900701e010f41d12800c1c4584415a692140b1a003c2820105d5410a041c98003448000104030341034080b0340c802000c02000201d40b148555150100c440110a43c0ca0640001c031001d140b4010176469008541a140d014101041d081c1121030b0952074560294045e25410003810014011440d082d1602401800b003240c4076818850301e003000341c1c1ca522284214105004002801c4e0080d102140151b6107104004000031200030300320700704900745a01c0001160b1054401040b200c9003e164001c01c0110780d241c0d6a01c444050750454402d400405a107460700066440c1031091004996401c103403004185d1160b405450607590110710400540054420710381890704000051001d80c001441d17800312640c0034071740b1060300b840342d0805002e5810f82d0f41010384280400001c205005402c004c40d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 811538291 1250 811537041 811537079
    0x307020f181806070e0a09051005060f040611030304110d05150a0605010f030606050d020d09231203160f0c0b0708090c0d0503040b090a0f0e0a141302060c03090a 71
    0x588506684d14182181e0000c500820700d580600303601030610482c031130799100e41d0340000c0c4955480a8030380c44100080040c1c1018144041c1c00c80009402e02650703501c85210710b800300103000110300358105036441c58081d1401c8010580520f078203c0e015802e00c03104101c001b80817078219070150002c4c280310600390041d052601910b80400c102206850055100c2d216400c00c603070b01c694480341403c454034a407402030350001b030601e560f003a120118813002c40c3c468501c24180e21082c8d0440c1c0d1030850300182050910514449085540205000700480301c09260700030b618016a510700804420100c4006949280959102402d2840f101007000000b0340c210140310300854002c021907412840e518200400f2101c41d480013000c0342c1042c0420444010503078003901d107071040148a190803075201e54404028484640c012104144100c0c1800118001442600c5201c1d013072005034182e901d00340c50f505000340310b0203600901401000503903800d8040700703000342c520701007004268201440c1e513280349064088507680 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 811539541 1250 811538291 811538293
    0x6030402031e0a0b0606090901170109020301020c01050604150305070315270302060a020f1218120a1d010509101803030225060804080c1006120c050604080307020f1818 74
    0x203d03c8038a4200185c1f40d03102001001c0400f680e09110380c4000306580b8100d400d04d15900d03100c40c6001650f00380091701116203907800000d1a0b280a1003040244c5010b0496600381d078a4048052012401c0030444005681c4c0003011200c0303421602150300c00070f002c80b41845c0c814207556075020800400e0351110a011074065801c0380c1180c2c0382c0e8000c0b90201c3c840c0d142d0400a440c001c0001104040c6410b40c00c0c4d0f44481c06c54404540444541010f030f040802414507044036480000d44200340c2900b281c400c03020b400301074900d148600100c20010b012403003103606192194011002440f0421711a00e00c440f408178003041d02c02c240d59524600079540e66003000e1601c2c00d00800360945222500318000030802c4032050b03520244140c03030329103c4500396404000c00c1403c90142000000151000d40290341c02031011080151202c4480d007440400c0d480707580c0002c0d114101c200010003089100006460b0901c1d0104c4030352606060000000301d245000c200040864552042005982004042d01c03662070303a0798130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 811540791 1250 811539541 811539563
    0xb0a050609030705240c0609100b01080f13020a080d03111303080c070e0f150d11011404210c0801090c030605090102130308090f0a1406030402031e0a 66
    0xa04000007402030600315a05580586820001840c08400c40c0301c0000418042000b24180200c1c14960b5a024042c003846560018007032002d282c02c200b207031003108042c020041290100020000780100c81c0039250200500d0400003103012400d01d10111054194001c00024940356501c0c1402d4640151200380c001081c038000d0080c1c407441c1c000b01101c0200441050452416007981da884e41d80c0c2d04000301400c42031103602c4012503d2094080d28500503410380700134108601c0e01114440c010704610002e607001d00b0310115040d00244040e0100e50801100342403100d480715241030b403640300e40156172240e5400800100c41581c54100c00344001b20307650050000c80c0e1416142d584140c241c03143e03400010b20704002080208042a0b032a40a035400001d084000362410300c20303060f101d0780304425400c03da4503141c0000702000b00f80740c04045c0b07580409040d2a0000a585094640d4024607072411030036009142c0000001d00315075041c40b10091442d44545001209a410001030b42c3d01e520313081040350001003803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 811542041 1250 811540791 811540799
    0x3031207121e1409100e0a050d0320280c0602070f0c0b03040c0501080a0f380a0902070503041d090c06180f0411340816050c130b0a 58
    0x4800b100e200b20720240c010200c02d480c0014400062000603081b00c0240203155031600022814000c1802c038000d00c1d50003040b01140c6100410040790608000b02ca010720412200304005440c01c501406203202207900100f24520311019202c504e1915001043c00e8400240f0604211040092180c40c03802051103901458443d101050b551005517005011950400000c220947c880c941c0740754041045d0002117242d03411100744109440c0203900c44c00c0000040212080c07284045110303003400c44890791051074803660242c0410f4442c407141c090707a81829000a060003e0010800440d0014292090345819070344051210151101c025994000103000f20340c0c0749101c40c609041901c01c80752035401a62094905c8500b00403503884880086604a0b8450300070881380c41c6140040c1214013503401c01581c40401c0c099030300a801c1d420003805c8025000e16085ea801007056030050700c032441000d0f10401500c3c0100d040103840c1050880459038058001403840d04044025000810140815152400d4070b80d26 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 811543291 1250 811542041 811542071
    0x102120702120d050406060302060d0902030d031b050f2206090801060b0909040c0e09030c01050f0f062206140f040504081e0c010e060601081503031207121e 69
    0x502c0040b24428041c420340c004041541e03c46a0414450390000174510703503940c0410200d410200c0c0070160107035a210329500b9400c040c07001d0300c0e0040a62600f0400f0301d680492035403003121410010301c1004404242859068541c80440700060102d5100e400100c515040ccd102209500340100c0c400240440c03000944900140174030000d6464030301d40c0d1420070140a052040c0000020810f0f107038000d00e1000001d4603989040c6050007819400007071070b500c680d10107030542542c0f005841e100c0010307201810080c040036044030880c1c100d1011540700b9122109071202070421100f49000c8101da85c0380800006003109050240320303040030706880c05515401c20008000c21110100e030085c3c00c10341c0801070000c0d0304d003a4012440c000703c45002601d003404c0012000c1e41c21103100100d0010360394800028000c15680113508a60b0098101046020010301c800100b42c5902035100d59520607031541c0c020035107040c001c092814400c29151020012523000b502d890526544581980c1c09072480c00100c05030140c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 811544541 1250 811543291 811543303
    0xf0209211507051c180c170a020d0602160605010f05040e01021c020901050418050f0c0a0c08091c060903110d020a08030a06051f082d090f010e0102120702 68
    0x7826114141044076080e0f455050a142544480150f41d441544110101104011170a024010325440c2d1010303062500f1400c00800124042c040d41c3d210808080c01640e40c0da085995150b4401c002503100c0e0b50345283d0031030801c60340304002d00090600c3d0000c601503590100c4d000490b036040394107000c2040500c10940c01c0344200d00920050148462980200800350740003041c1c140410725080781307010b50f01c2c0a208000089600b0720541e0700d445005010240d1100a481034204d541d02c915240b4181205801400070b1110000c0100510790100b844034140c0c0e900103010b1480301d0303035a0000c17410519520f42a0000c00f03207120100d002c20701141c00c82140103400603d401040140e900100703200784003034451102580006180c54003081d11882c002c5030b80e0b02c0e02810b81304542c0e20340d000b240303411032284406400400000e185440040080b481c2040c1c140c61001120480250150110b00780e407601111241841c1e141000422113608103610324a102405500801c0c6003013a00f0040022500d60140403030b00c0389 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 811545791 1250 811544541 811544551
    0xc060408061f1e0f0501030b030a030309080403060c0206040c0f12060504050c061306021005040b0402061e161b08030a200a061e050903030a0f02092115 67
    0x81e00400024480782c00001c448200b4030700060202c040b607541c0e00d10407100f001e10122105842c9036030940c01c024007440e81d8403e8000c0c1c00c0900b400e01042c540711010075035641c40c0101c05010183c460126806000082d402c0301d02031600310310180190784080001942d1620203542c202c400e4403c07264005034024480c514034064507180b4119090a443d1500d607034003d000e001d4029075803030042e5203045d00155035080040601002b11030181d010b8a01d000300180c240550380d110410001e0a1a04000005010401080c7d0066045411503140c1a04012000c070503460400c00c4101100000760440500c0c3c414250307074001d10710481c241c04804400703008408024080d84210311060f8030074400c0245250141c00d94110170100518040c030300701110481d0324607020315100242e842070341c0d80d0015143d00c00640d140300340e01c155266042c0414106622015030f40c1c40010030080941e540c541d640742c1d0181090b0101c60145200400704402032401070600001e50046421a80b02d074441c204006800f00079604985210b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 811547041 1250 811545791 811545793
    0x90c181e060a11011401050a06020c010203030a0f1e0b0f010504140d211205090a020f12070306090b090d0f0504050f310e120412111206090c060408 65
    0x4408140d0500c1007a411510101d4148124000c880341d524800344190348035030042c40e1074102c6a503d450144501002282c01590440d0402c11664000e43d800108598001041c4440002e5401200004c6001400c103c280000607a83c15600000f0b001c000b900107801301710b400c5501e0040665100300540b0319100e01d10a0703503070080c02075212800a00d0140c00c906002c50144028004102d160808105009041e0484602040655421240c840850301c01c499204403403a0041c00405990340008403e080d1110509200d440c00094100740a102804900000c42d0302403400e1100480e10310b40420701e50800c403a80400c43c440c1c0c484422502e4892102012101d10f142c40d06850310381458140700741c1980b02110181c00581014041e900e003110900f0700844554200c95402414203400d403d0015240d19601e40155076204604440c104417141c411101115406203940d00206420300d0101201421a03221700d42c40600d14550740c00440c00441d18a1140c4045400d13078201100d05010014180128095030030a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 811548291 1250 811547041 811547089
    0x20a030219030503190e0f03031209010216110909030307090b0d180602071703010f09021b031c050121060c020a05060115110d020309130605090c18 65
    0x9800c140c00c80420000210300c20090250b240d442e0a440d540c0302408a103046a44200f100d11030304d500031036138025200111f03076030004030000e000080c1da40d000c0c0c0f0364020301b0034036404041818500309604440070f001001c48040002607403418240d0914541200e494094200c0c08001752030100d012046921548443c0c4600d01d40c103051030b0207a801e6800903a01204101d554000106d4a00e03054940d901d01c00744039030300150307030392109241c07005400080e40c2c85e0300500082400148620340b1a5521a0103460740303c000141c0f50a01142c050640f078400390201d100e240000940380c01c0103200c000c00c003101c3c941020400c1c080b503642d440310841f44010581c1c0b20190803100031319250028915800c214804692841200c091294a0320740d40d080010a92102141c2c02c44002d200b081660084070720041c407034495014015035244000080d40700d20520007414805d241010b1100245021503201c4009081c01410001d02e074a058100c030001603010040444060031101c10b441c015103021008000844901391640392 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 811549541 1250 811548291 811548293
    0x3030301061101020408031c0b0103051b0706110c03120106090f2d15030b06130608040201090e07050a080c090a091d0604080a081f0b09060f0c060610030207020a03 72
    0x90202c4140ea030201995408110014010074104003512456002c0c440f1042107080d900c0307255040b1a5001000c9042c0f41c140740400c030040c2410a420000d025070f10504699503142464800001c28040c91601607006010030b4105400b5000006886051240c1d139081d00180d89417002662180d002d84904a4540c0c00f061041c0f19080144112410b24000d902d0480548022801c0b2001d80c005181c0005401d02400c40d075500710b0310f84c14094030343c0020301510400d2034905400c87c1c200ca200c00d03a0085000340024600418116441100c0702c0c002418208109003180c1010b07040180300f1340c40006004001858600030503034402c921402c0f20240b83c0018640a4680c0c607000825000d0205280c0d04202c607941e072003070030001303500512034103208501c141101c0f81d440c03c04071405003035030a002d403500f40300c4010243d500759000c076500c01031400c1d10505007900380c5544a68001411500c0349044110540101203090703000d419000595a00410703003212108484402544101e08034080c00344084e6129040d20b03000c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 811550791 1250 811549541 811549547
    0x9050c0901080f1902280c02010e100c1e1202010207260a0f02030405030102120406110403050a0f0510141e090c190302100203071103010b0901030b131b05041a0303030106 75
    0x119012500041308150b13141680c084d0400c00ca26506d0017404900505100c0e011581e1142005001d500700701c4401400c0407400400030000b0320a1070307008188800384400c40c6c60040d1084840500941c1c443d02041c5100c04070340f00207002c2d4010a030104c0c1c07034107241d4100656a07007000308000c03805a0154105802e10340000301c100c440c000114003034401c0d1b0004010114103034400780002c0010510600d2440b105041911b403100459100c2c0c1e00308200294244818400900d000c01c140f0704090300040d030408844024100708bc100602c03001c042c90100c1c5824080d00101003d4aa0280b003405030520042d03008640d036040d010000c004403280400f507080310380c070040d2525103e85424040155801162280b6860360f0204820b5440181e44102603480031526a00704100c51601c580b6020302540284003801804003c140c1f601d0040c00014440040e9200240000f4008045448881d401407070382500404102800f00041c210750041300c2c001c6080c502004a403000b01420045060350240080d03145a207800811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 811552041 1250 811550791 811550797
    0x412060c02120f180a1d061e09040c091a0f1009060c140303010f1a090d20151e03010e0103030c0503070c26010527030409050c0901080f1902 62
    0x11800e01e0564075007801240e119040b005c0b024225015140c03c0c11302c040d40d0f16000c5110001c0c40d1511910049034980040a581d10301072a41c43c0066a41044c65140c91a12560054064000a1040d807406a10141c3c4500140c03034200100c2c420355581440317114030340c2400840c810100a09011071401081000704d144a44d80010045000700820009080000e50040c00e43c6d10a0b40324510a412680040c45111202c00144061a0b11896000d14204801008c43c20030484490040d180a60701c0714680b0a4902c00c0361002c002c010002c0011003101c0c0d41ca41e8404003070f0400140c2603101c402032030801c00c0d0001e00340200e07410f035101d0030546062a841c40d41d0071110700155040444a900050059100140706003c02e007000e4084e40c0e8005464810f110b614802d40d50b40309403140400d030704000604c0a00f42c2600c1000400e40000700581c4401462403420f6851442540e00505269182c51308004409c111070f4090880440242d07190030440d29050101030b010305080c1c4081b41035110014840e01015020303401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 811553291 1250 811552041 811552057
    0x20a1110080c090406030501150f0501020f0706081302060a080f0a0207080f070203030f04031109100608180c1507060f09022d09040b0702010e010e0a030509040605060412060c02120f 80
    0x800c5c040d03125a540360946420301d125900708900034200b407044070001c0c0c016a010b42020b00c0200340611864807110f0396803e541c481d0100f40250349003c19416039411a0141304140c010340342a0350f03615140801045080301712083c20703c0232404004140003a810f4002c881102d50000c0e03c050404240b91989282ea41c402102240c6c1440100b160705000c0000078040c10040d40200400789155444109000d41400020b040d000c2c914031000c000c1c004940c002d43e44640002e8680000c1e00c204c0409550b2030301d408915188107074060801e900d101100300c3d850b00103040103440342c402404500e41d0002007500303807601c840000b9484009400100340c84410b10328031f081c4000300340b0119a29080d12102140305402c2c1550140d4611422401f0003107003d40900030010600c0c10600200300e00340310083e0180e214916024010208140000d8140050b075841e0001c20107410020825070342e560ba108040d40a03541611811580c05080c010200e403024004280062040e0220742128a07011280703075041000c3d441341316 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 811554541 1250 811553291 811553299
    0x6051807090503071a180414090f1204092018030f010b0f01050f070602070b01060813050d050c1011030105130b03030706050a09121814030c0613080d020a1110080c09 73
    0x101b0740301039035a640140c41440360801d01c2e42c540d50070002c43d140d00308103031500aa110b40d07102450310741c00c46441d402100c04480d411074000420000440300c540b04190342c0211107200540c042103c880703044840b403094030340040407412143e5041c0700c155142d09a40080d0032003544402c1d00703425100d8070350062004041b00c49c050402d162410709542c0d40c0c01d01f2a00068001d841500c00d0000500080da00202030307a800010101d01003140d00c00903540c059607440400b03d440108403000c60600d0b40000d0030071808030150300e03082e000d00c810500341000c0300040e04244100ea11600c4982d94916280074144540111907034041c028500d0038640b92030b118090a00507002d80c0d00035070355042440c04100988011100d00c507440d5100511103a2803c1c20a03190b02c46a00320034403282c0300354402034280d41d00256004007240281d4445455030004940d1050b0801c00382c1c031060b01d0b4061020091541d5502241c10b40342c11384900407484440c001c000c1400b1594000650304c901240d59038000c12440c0440314050000084020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 811555791 1250 811554541 811554577
    0x6120c06051b030a0302041401052704020c03211e070c03120507090608100815040515010b04030303050106090e1503031c0203010302030106140607110406051807090503071a 76
    0x1900043c55944400707107500c00294049024480040c900c01c000304840e00034a4820b040642c00d808071030034264071909602da0712a90001903515502d40e601030b41c40303d40c1c01500340e07a00d8001e4141581c030340c0c4a031004503481031600c410008070405801d50240c0b0070719040c6135030a442a0350743e034419201124044030540500c4074141101340d090285014040c482d110590701c106510f440d020014000c2e01d4040c007840e503030091312003081c00231800c002100b940c09a003a50040740261500d0400d00d04010304040e1040c540710803c400031454682c454024400c4034441da400f0008c0340e9031004125140d00351b5004d5411042d41c1803000c100d00490b030026464010030010700352481c004480c10a400c29543d01403280390070036008001001545020712813000249124861404201000c40000d011441100f000900c1c01300328401554858039182c0c81500988005022051451040c24204040d844200c4100001a4450001103041e00f00800c0410440301a45c06858000c00c0c107043d0003c0325000403440740c0c0c5680040d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 811557041 1250 811555791 811555837
    0x602040927122c09070e030a060203040809030105070804031707093c1a09061614010203191b020601060f0e0307091401060c0c090f1b050306030106120c0605 69
    0x203004000c1058071032400e101050340080040c0600340a0080c1701105001e40c0c51006415602d0100b406110590300a0380141d4030354903841c100c900c81c00355242441e0550301e444100402541c015030381a000354025150080745801c0d05140c00601d101c11283c03c0700040c801c42040003d0390020031098000741d000b0191040081800581c0500440c011800b408404500e800800806240786564000c4011640e00c0c1031410549001091080c892042d00344121300c00401360b4014022594a48000800490029556410b0510714011800c1344408441d4510b80f403c00302003411036003000c400001c0c0401e42c010344250fa2070410103661911940b1040c60520035100f100c1425070307500740300340c001400e074507140012420400101119100016040b031428041d0028801c07011079800c0c81e250b000c58141000c00710300300da82d1002c1c02c0c020b0488041407501391040035400705010340d0440c014621a900c02e070000c00000d0361b607981101e2030382980701e0098100070303a000045c04518880c40082201800d0300400700c42c40252 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 811558291 1250 811557041 811557077
    0x1015030611090d0506070e120601170717031b0c090c0310030606120629061b0a0c0305190b0606030604061d1005010e03030d09110d060204092712 64
    0x62030b0fa00300ca25400c00c40821000940100c1c1c00300c902c000036203002c01d0003c51507051a98481040c0039285d82004c180110410028080005102900070b0b4588101c540204801c02a17498000b240302c02030030107000c841d2a01d01c210009038824912801082c00400762510702e00c560080d40041d108440e404003515002c00452014006d01c401410030b078039115071f4a05c4a040130300403603480c4540c2c00788800c03a036146a8400d506844544424502c1220354568030111030043c003141070200d6400c0409402410400303000d020700f4081c00700c11030b4010825200c4000304100c41c003200c0204418001c04e1611840302084282c1084809503500c810007a20014280f61203205034400010140c00341d840f000d06010400032509842212403004000c00c0c20005100d240720000252a4085c0709a032100690351200e0403011721002482c0a419144090001c501000150400c4d4000c0c1d0b205000d90081141010304000b500422512180791000785011642c59499107a51440302941100b44000c0822102e840800b02c4010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 811559541 1250 811558291 811558309
    0x809040c05071401021306080a0917070201030e030913091109041b0501030b0a030f1a130b0105090c070f060f0c0c1a010812220611101503061109 64
    0x1060740c41d80c0c0c0c0c50780000d1403c05120345690300c4003011a401806034100030452445070380c007600e00c142003040d1140e544140401c0248254200a41840e0084006210b0003255600400119000b0b85e000d00c00c04140024039603a9118280905030401001e1524010440f9990300c80c114051181084040c030303c1040001440b6890261004d68101016032146402c11082c0d0b11884003c0c5820308040c003000e000d900025951a02500c0040c140807001e204540411890100089240014002d901e0303060520100501f20890060401c45012060100101c1c030392a040c0319244c480c07402602110710b44141580c2c0c0304000d603000c3e08226101500c990801d52441c0c20b070f01600300828072541d02c1196843d41414170400409480c03071381d400c071120303040014015004040b95801e020000100c10301e60303500c40b110350040c1c1100d5800d405e140c0d05d070314500c02050f01c0d90301004c1001601c0c03080044030100649502104110f416000150b4041f81c41034000304001440394001801290409842d40c1c2011032280220340821 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 811560791 1250 811559541 811559561
    0x3030114150d021b0606010807050d0b120607030c0e030c1504030803040b06040f050906181501030f05010606050a0e0910030b04050a0b090a0c26030c0706120c050d09080904 76
    0x70740105030260004403040e140c4c1075942c410710082c4810f0600c1700002e80342c6d00001d0a40010032900080300340705103010390080590301c80054101581d03c1c0c01c256600c3d454000c107503105000a410b101c01d440040d840703609a4400d031080140a09504a0b8001c104000203440d513404080682c41172000001244038400914490f5025510301500c0385002d00400007101c82681e101c07900f0320714000500c8003a6900003001030340203807a000000c2c40e10403102c95a034a00b0681c80596081402e00c0300000c0100195000c4024032640301d14001c1c40a25110035065540c1d00450784418001504044803c0c0f0750328000843c50382240403004c015040340d4403500c2e501c1e26103008890a5074560700c00c440600400240710480c13136115440501410050266603514029005a0711646684a000c2d80484002d041e04664401c0c0c01e031000390440741d5416481c500143c40300014490140413410040c3d5a1012944900600003000120381e1540e2902340000b820f02c00030500c1c00c80540e0b80340000d1100041680711481080410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 811562041 1250 811560791 811560817
    0x122704091703072a0b0613020403031e09180911130209090c160b250908070f0b070b070309060e0102041e050a050120060411130e0303011415 62
    0x79107001c0502900349000003e403e8156a00d845161a0020380d40c2e101605481c1d200f021711045481e100b0001e1900380000001050f894030006000042640041b909406544020b0200c0a04038911106882d02c034135130302c501c8540a40501c2080c03546015503015030307034892040b072213401410b01d20408180c1c0050b501c0c4540c010150300145554162400700103582e8450031010a40d031412100941e9580c4440e0361140092480c0da030007004c51140c41d00c4e060460710101c4118440b8080404102c4000d20340c130014031441c521801003500204154448505a2003500c1008940914203211903030348081c0840d004040300b04040e038900318103001030224026001c00000e044005611907080a424180d003407440c00481d5014507844104100c0c076141c084522044403401d0030700030b40d000004907803003448035a02c044400c00c038046c4100300000c021149611144400e003d07100341500c800024240d204407644003001000035030060004000d2509a4844540c94003c098003d00c1405d0582c00b01500d66080940c0700442 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 811563291 1250 811562041 811562047
    0x9010c1a071205180c042a0305061305040221150a0c030b01020f0a0f03090b1941040305151602070609180212040605091227040917 58
    0x2042401120b4100c88a50428a051013000d900700c1e540705091500c2900558544000340c8800d44c114100020b181840c00096001c0344000350020010041290042e1043c407444000c807005405510078580302d10380c0505074138a10f2032403c2069125800006d040c038000c0c4210344031203007800c8001d0780184c004c01c404a0085225202508003a003620b541c4100c640c1194055425607910300c00c0003482d00019500000b0311904008c1034281103a003107265412651104400040e800c5004040c03040d61b0782080d203a5500c0c410244000300642100d555000760404180407640c1c400c42d450310302c45906000315a502c40c000c03894280d503030f5105030074000f030302e0308650341d0789206402c201010404504a0864880c40e10243c038005040040280c183c48041c000c048006807103540d82c260425050741141d0501812007240245817500b460098050101200c044000740036098030f00300c005000c0c0054842c4055807100040c56a82e4044c1805144c05001c2c1480340e00907120028040841c44001c040e01006075100600ba039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 811564541 1250 811563291 811563317
    0x809061b012a0c03020c091e250311030f06030723120d0801180213080a110619110a0206190e0604030b060420030c040e0105040c020309010c1a07 64
    0x72032030b0480c014440c14000c00c1065000001e5020401113001c010864042150340c85004808100d01075420341405814041e00134482c80c02e24102c0f0341410b00c0c3c0c0310440d0800303030344103810101c0565900c0000c0c1c0c1d41084050020032a440412000e00c2e074428070181c115900140c5c2e07820a90201047c059a1143c3c8a4050554080604050b00c40c6841c940002000b410761088005c00242a4131052141402c40e2000b4520f007050b0100a4040b0b4400d6443c00c1c920070421307070321000c0440d1181460082115800c2106155120505028095031705108021042c0e010340304a0700c03000d5940780c007140044442c0f070061100e440300580c0d440c0302402404510f180c01c0304400040702c801514803030807042030740d104040030b02c001c100050601c41c00690042e0183e4010030108000c071200f42c0410503039040ca85075a03801108109201d0300040245c0300310707000c05800d501d01e82d82e68000c0c4001c07078502d135001c030005810030003046485500440082144500c07400c1006a103103991003c0c808850800d69000c40080c0c2c80500d0341c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 811565791 1250 811564541 811564601
    0x9060b04050a0609290d060e1027080904090204020409090503070b09150615070501060905071b05071a0403170304060506010519181a0c15040809061b01 67
    0x240c2e6114080303c080c02c1c52143c1d807404516080e4a40c8000d0700c604100070803802000490f811604000842104450127156480903020180002000c081c40c2c080c0c001e20f2003944104252105d5042507040f00b0081d162101c0d0905010250071780d404141d1300150200030021b43d0050034454012241c0c0228041c40c0c0714481854803040700345001d08810501c0c0d2101c504c02c040f9866a91807507406c80021180d11814050b0180c0300001d6001d4841c0161040d4604480080c0042c1c05030400c0c0d1040409665440a0a01840b5501c210303d40c1c601b4050440e0b80002814025668061001a403041544a009040980d2070759448a8012200f441400603500407050200f041a01d016140d0800e0b001d007450303820b04480d43c4c0c03401c0d82c0850008210040203181e81c3c6010605143ca1450805800c01c90505a50341d10807041070101648081d00749800d0740310700700984080b01822542c4078011940b0a000ca80fa000c0c0a8081004542218003d5080040700100301001c1c0482403140c106840051944440e030507001064503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 811567041 1250 811565791 811565801
    0x50a0e1216080307150f0f14010303110d050304140a0f06021806181e060a030b0a05041515050f0a0206040209180d080a06031713060504140409060b04050a0609 70
    0x40b800c5078424451080080d16800d501c0500c00801e00f00010b5502000c40294082e000c28072402e030949180c02c280703403000340c00300c40500e040e607029448003088501075811003540c4014100c500c9000840c02d001050028400d06446c0042c601140e04540c0d40c80007a03204c0190b04e8400d80d1048a49030f07400507800700b4801c940c100d0012200012520395041c02c20030780c0f581c520186e2200f0100d00c07170079011903003801c0c0c030201c890900c0030040046d04242c0ca400c82a003010740184000040b045c4245144640040e4a00e818020320f40e000b4010b0340d100000702e2508250a02c110034401e20882401030070710104000715403080c0030702001e0005500402042c10702d40148850404054003580c0302c4003c0088885140798001200d10030100f02d40750074000c660b144514030004060a0f0001403081e000c503010040c0b0080b89001034039880d480c200c44010110764035101030350148a10701c124025a100f00c9072141c642d280940c00240c180380030712400320707014100f00c00090031540200d503417240540d5244028000e600f0f061043e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 811568291 1250 811567041 811567049
    0x7030e150f0304030f0f05070f0501110409200c0304261002190e0a05061c0903021c03050403020a11060c07091d0105041e080c1b04051e07050a0e1216 66
    0x1031006e01803000c0c010164450340801511100c000b40780c3c1810054258032001c20b0003007200c0d03c41c1e15644c460610700040c0c03020100f600303c00c01c1d21007003880f039004900301203c80801c0400c005600d8a1324011407044c16002d04400701e810a10b038502e83d9561302c0c205001c84c400ca007281690040c1e845030044102c00100b14449030031002c010030390200c0c00298032060303c10301c00c0d954110f5180f5120130349039045c00307950300e040800c008082c0c0c10104d9500030150001880034103019030708902d10242c42090812421500120f802400690158080b0008921003c1424036681400740145181c04683e1041034078000440c0e0002c008581d65112424260103c280c0545801c08407000900103402c003915981c046094009486103e5000d0f0f84d00c840c00c00011501f103411202040b81500e01c17580c1d18014112420041c101c4140c015400e250000c0d85025804540c82882c4000c145000b07459110315404071425000395941030244007401c00c5210300ea90b26070b0b080256001c0394000515100b4030380d1402107d0498507500c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 811569541 1250 811568291 811568297
    0x5130f0309050109060e21011d070306051807050f0d120e010806100e0f0418030512010b0408030703032c0c031605090109021e0721021207030e150f0304030f 69
    0x1d1414503554421f18403d810742d40ca807844010001c00117138842d00406c44104001c00c0c0010100c0310300031107000407500038102e9001c0c40c0c0800c559502c0e00d0710b6214070041c0d0b2038420307030319040600c042c040340c6840714010603071007009020212036886540e01d41d1040d140920407100810100500c999031507911004072540260207546907004259140405403041c402050403611030031721300150b37402a40361940130841075642c14140f1310700e1004030305011303006601c0f4001405034513160300c00204803060000122812560742c0e0009500d0180340343c8003100100090384000c240c006001c1440008644441500c00580800d000030780003610540042511b0861000d4200841501d03400d000c000130359918600318110b07a980711015990389041c01c40c82d2104054a0b00100052401060786001c0c401c00307019a00d103801d04107003151818284060b050b680c5000382000f081c80d105081080400103403042140000c24940504a2030a9100102c8611103a801003d00b0705109040401080705050748001701c0407901089003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 811570791 1250 811569541 811569557
    0x6060301050a1b14090a0f0e0907060c080d060e0915100305070611012304051504080301090f020d0203160f110303180f060403090602280605130f030905010906 70
    0x20098128801d03202d070300300c004d00000c104400007001d0308a048690101c0010104074170b254460240030b461000310702912800204207800901d2803c80061000d09680150b141c06030403a25070f1f0ba80d56419030050403980c450b241c0350000003039070740c503400320250161400074050b10707140d4036444020f084200d00514000c100c100281c03007000030070030105101d000e0710003e10301401c002e5018071241d80075100f90307200c0841c541002511101983c281400342c40c00f4500c0348044c0c58050944c6512980151300999000e450f24000b00010030241c0469488124840605180941000242800c810803a0011a0154032010250030340340c00a80e885145400c11507a00d0500032022021201c0e559a02d00000b80b099601c0b0300700d00021300c010a820041d040a01341044100d400d80e2905207001896840300e0700c00c803005031040e490862449819808801c0d10300e02d82d9484ca1006046a4454002404025080b0802456144056008242e2184001451900a40303481505501d00000100400040d60007034040180d14 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 811572041 1250 811570791 811570811
    0x30809190e06091f090504031205040b070f030f05090a17040602060a090206091e120d0503150d0807030309120804051c0306080d020a0c06091a0307090b0c06060301050a 74
    0x300601a80142c01034a001c0b100e6540c0c00c007400b03804050310380085480d42d001c1d80006216030b01da40040f80301c0c0348680c0c1e64070307000b220004002c0240c5109590040280085100080486200780d00300404400a481c2c04215207407442c00a030100c1e4003d4070601002e030400c6034001d082c004045811401019400610740c070340740c80c002c0001e45400018003005501a150304801041d5510003007960001c0c0c00082070490ba04210703090050000c964081d180380540d00d141607800d809180414450781c400200d44035149140d80d4140c031075000f514140d200503803203404d040304000414403807000303400c2c074500c02c5d01d00203a08600d6040c030b00440307428107a001c80bc212181c01004006240444d1040317210424000c0c0100d401070092064016041c29004483d081c0f10300101880340700e41c00260700c1002401207003c89a01d43d1076030b008a035003101c00c1c018003c00c07824420004400e000c141c0e00545c0e0140303162402c0c80215465900c400c1c0940d00802e030100890b4480410700910346020300c80c0d10f4000398402e1080041c2c40315 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 811573291 1250 811572041 811572059
    0x711120a050307350d0b04150b091912112b1a240d03080105101e030e0f0a1511040e040b04050f0c09041502090a03080919 54
    0x1c016008200400344907502e01d4500c0c01101c40b403a007410340845002041e920b20400d804d070360003503020b101071355003400f6642140707060a2141c000c0c07032140d60391942d006031b013001c030f041da01544080070b02c64001020941000c0c5095955401c2e20140000f40d9503c0e45801c1c0e1418032081900fa42e03100c162240e900014480e0b02035010544c0c1c01e500d029201c1c00c00b1541c0c2e14508000c84980e2a600e402ca41041e500010480c0b5280075aa080c03c0461000e145862305030004c0c81442915043c0070001008151002e00502c107034504005162194a140d140121592201180c0030400440390341c11200400d032503038a1944006000d201c10f9a540480c01d000388203141d481d846012400900701e031607007400e41d55140c45007420070b40b0404440282c43e0324210070201e41890320300307115903850072101507032580500584030a901802041801c0a841e00824500d441c5d2180d40390340420740e400e001038100046c0c0c20005d50a01703171070702e280410040d0f001c0c1282e0358469808400b44040c00604101d82440c0c6c1207040e4090000d084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 811574541 1250 811573291 811573297
    0x402120106062114070207051207030213052d0105090f090703060f09020a0f030501050115020307150b18090c030f0a110d080c0304050a05010e01021c02030f0711120a0503 75
    0x43c04240522000c0003c2110300014890150031121304071481080218058001511804888064440808110500045603180c3d1081d020007544007401707408402842c1c0080e0401a0013009525030b5084a94124020321214280807071103050392004140100103600d419164a41d00a0500c5505c407105c0c503040017000d41314086408020441c0303a90300b010780d80c40115507001d489100e07805000785c00100d41f9000595207201551004a4096003070100103e2000300a03005810b40c0c3c1865001107050203419501ea0000c1d2903403020380a84244e072103c04161a82c0c4000380ca210508041c0480f41240c205100c1e2030703003082a071038041d5000e64410035007405d0148000420380c03030785c507003101201e110002c02c039000581c05800b180d00540380d6000800c110020800110040c021070307004940d424007080e5920300554004019880c2140503030030044070a4440802901c000400c2e9210f0700c156482d248031400000442c1c0c02040c029203d41400130b9100d07076642031951003100c030342212100501e5400b009030340702c9940b44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 811575791 1250 811574541 811574567
    0x20301150608060d0c0b280512010e0a110a050a120b03030a030e01140915010e0103110405040c031403040819020d03120b0a060816090506090411090414040212010606 73
    0x685010618045c004840301c508040c0c00c8800c0416030b540b01d4814003442c101c2410090300701940c1c56041030b00d1601d01507411951118400010030010780e01e04101c034140010000c002c508903d442d65012569031806a0080480500b9501c600ba150903400c0801031218007940e44080c40310f45001800c074441d0b50004155141d02c0d82a15003c200c00c40102d0350709000d4892501030b071010102000c14003140d820702055034000c285500744036400507079a6808e042c40481c07007840301070030942d44055000c2c202d0a041e0062a48140070703484040c1802d5407580e8020440303d401104a81ca81c10100d01070000d00030500581e51806e0050300e200410f00d6207600061001c03101000014107000004211820020303598001d4060070400818042205542e400060140e1000b101c44400302c10346d01600c00c0c03902d07001d43c042c00140c03072000d00a40d04100540090100800010542004c609001e124010b810b90702c0d4040c0100d004032900301b84070281030920501200000c000c41d012001c0e4101802404410781c400b50000041c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 811577041 1250 811575791 811575799
    0x18030105070917032205090a0c0f0c02030f06010905090114010b0d0c140703031401271e050103060e060108030304080306010813050109120e011416031b03030902030115060806 77
    0x1403103e8003035615503c100744040c24944030f050602c0e03003142411031040045980a0382d6480c40f81d520000000115200d070302101000c505511080c64010f84101d540520b0300d4400f80c125501d0103658078246103494001d0f4442d001042d100c03030800101c00c0c402e008500a10002c400303a00030550505c00100c8050042c008a2010309545058031350b02c00d48681c0c194080d80140000d159074403009420001c01801982402050124000c0c000042401d80e60b00060704030b43c0115a8420145000d8141c01d001e0440300c0001070980e820b0f803410402401d030501ca007034003c500c54040001c1100300c0c2c0e20351600f8007505900c00381c100d800c14002c03c8046207185c8201c0346c4c400c400740b03002500b955030307610088007020107000050410340c80c00713000b070041110741041401504000d0325007500c41d5003a0801110300306030042003031800c0300d1705004000118552102c001e0602e4400c2c20440427090080c007580c81540d19803503007600040e0301d44020b61b040d0306003840f4901c08522186a0f4944050034640007500840c0054075842c09 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 811578291 1250 811577041 811577069
    0x403020d11060f1903140f07030c1101111207020303251b05010c200703080c010b040c0206070e010311250b150307350709020f180301050709 62
    0x519500d610481e070025483c2d00c1d01c103440c0c1c2e50000600c40c403160403c568801203880d01031001d07036084980880a1242c031078036542d0b4000341e40d00d04040700500341401d8500213102c042080c07400101e500b800380c100b2850910881c20380320400300d0344045101201409010a5400030030074080c3c41d80a94510b0090841e109121171140303018010111500c83c0c05c040d640c002c04440a524030308115064210301003440c02a034400840d1402580d8082060928000151780341e48140d41c00c00001d42030201070010300c0c2c1044000034084509101150580315000e41c19801078100400b00442d40ea04000c841030810303400e2804000c92107a19406091074440c00b024050140500405003c0051540307800035a0641c0c00340800009023044c000010303841061100b100d2280c0120000480e507942050701481c403005a501501c0000040c41500300980304801e184403107680500340c80402e0340c000d0703030004082c00d8200c468803c1d9100340110a9542c881c90038601580b007039050006000110707501281c460305403180070b194028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 811579541 1250 811578291 811578323
    0x1030215070b0a0605040f0b3703081c0b03030d050a090c0f061106190c05040e072d0c0308070302090d080a030e030a020712060e031803010b060403020d 67
    0xc890090700d0005010040074010003150070402e4000800300d64050320148100c0201a000c002034503030841460ba0000052a1000d0b00c4840c1c80c1086601e00c4042504400f13228080b10442c81f60300e460740c1040d81e8803e00050002c05103c1d00760082d298581071400e00300a804013080019445e17104074040300300c810345c950010904206140e4444107071294004a202581e55546c0f810b2110841c440c40f0780d40c0032070481100090304200104083d807113031a00141c40d05450340c1c0c105200d001403c000c0f11050030800f0a01002c5803090218900030b000d01c85030b8603407800300d208a440b6640400c8022003500c04c400454400b1020094022400c0040c003541406d002400f0381c2d40701400c80003801540c03c91a480b43d260240d40062014450043c111410b00365001e10034080300c0c550343d079924400c02c0c404c41c00580c00340e401040700c4a041150595928860480840e56001301805549160030032000d0403001d001031a418090381c502442440d100d21002d990150506166400049800b042c82d58050034162010440d49 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 811580791 1250 811579541 811579579
    0x30a0507051b070905010b04180e1f060807050d0b0a0c030e0a061b0305090307032109060e1c020705041a03010501081609090b07031d120909011d010302 67
    0x100e122050316200c80d0b50310100c21501d5601c26041c800c40851a00d0f100001c03410510940c200c5055504c050707851079108e0f03180c1054100a14980c01842d460340a170488403840b0045101d600074000280c6900030950500381041c49043c040c081d03000900c984080100c09002440940c0c3c1c56030f00c240703807601c005004941003000381c0141107400040a03503800b0348140b5408010240e0b100040c180400e02d41c000c118a0654420f50032190280c4403c41c4c0d41e0710038000503002070310802c044486140b03075918412210407201c1a610560b5000c083c1203420540303444805424607000c02010402080b44404002c05462040c00a034580d011402018015a115440130091804500c01c8075443c02c00600208050360f581c0080c0358507026100150300c1c1401743e42c0f0f00000c80090500640c03d0440d045400b52143c0e03150500282c0062a802a003204c00350b218007065001480e0600640f42600111850699201c0301d480400003c40016080b42194407050020780050b161480e030150705490f41515080c2000e10460188 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 811582041 1250 811580791 811580797
    0x1527031d03030f12160e130f02040e01090f11091903120215010f0302010210050a150b09040c02010203040f02060901200d090e0906070305100509040605040b0108060c030a050705 78
    0x600c1c0c040c8400240a8850000301001304900343c2c16200240c101d03200d41a0b00d42030750503070010b55000a041407031a030b2080c0c603000e407580c1080d4251707440001740085d1000300c84c4140d03002036000b0481000c1100c0108005081c0d4000c4511000c0760380c0e010011910041403804681c00742001c0f10740103400c0144900c15801c0000e6020001d103030014140384852000da2402591081c420110f2000c0c0059040009921001e1094031419240d0580240181085580c0d40000508004040300c0741c19480c0c10600407510350a6010720b0240000300086652092500c090000780d80c0711640c400d085a00c100200800304207c8803040c011a981224034995400c8400012900202c85600c00e000114020b0094483e83d80000f5140051114948444544564079000907818900498072354500d50400c0b0009030b0202d201c2d034401d40e4010344150381c60313608039103402c0465460801200c0482d116680c6000f030006010a1a00681c014281c3c44001c0820f450441d0000041d4000680390001c0700e40c4600114807494042d1050f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 811583291 1250 811582041 811582097
    0x310030b0714070f030905090c04061409100905010219020d02090c1902010e0c010309030e090a15030303020301140907090b0906070209040308041502030130050604152703 75
    0x200a8032150103050104400340801300850129500e4240021103041c01d0707801d10302c240c40e86110b6509240c90904240c070710001410340d03020707900c01c10040300c0c1041e41c5441304801740785107a507520507005050000180c5004c2025050340f00301958050b8200040e614014078440031079041d04c01c1261a15180d10005140c042d80c1d50345d60320b07068103610b08000c55905520048540d003500342104c507180100790044d0101c5e0b034000c0001c0d000a6003580d080e50541000c9250307030f800000c03000c0c001481d581582402c40100340c0c00d400840019400100404c0016240f420b0740140b02d4085031800060b042c200d0b00503103551a144152403203210701180c0d80e2901d541c7c01040c4c1d00b1040d0098441c4074640703824036001b4440c031400c980c02c0704e03034060441d8018200c1e4260310a03070341a200d8003052050125085c3d0480c80c0154075882ca18107107403410220b24030010b9024071074030340124410511148580e80310f00e0f1240a440d121040c40444c00500108505150384661940a00b26014104000021075078000038070103490203c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 811584541 1250 811583291 811583327
    0x1211041b030b1804020d02010909050106021e3f03010f230f01050903030403151b03201803070e07110a0203070324060f0e0a020310030b07 61
    0x810402840456886100800031580c04201e102004401c2201001144108089000d0340100050040c01d0100076002c1032401410100c40c1c203a0b0b2800301900b969000d030405d200503000030790f000402c500759001405020b08501d0280220100c01d41454a03180c078121001322115050344411204c0040901a010902070705104440c0c0e2903840b481e07107000c4441d480c03040102103401034280142d4016a14504952054000c080e803280300007040045801d83c0000380860740c140010080040041c070899061104104038602c04104c00c81c00c075086192044c8540c05100505080c0300d42d00140400314001016042014640e003900c0c2da44035022034814210500e40181c2501c110000801c11403410400b1a12400d0541d82d03083d11140710069164595101c0303400203405602a500603c001011011194600d00c880300061803c9070b100a22001941c00d1513100c01d074103040d00340e000c1c4110740c001c45150340d208a20300001d41c60b42c00c080d540b440c13010400341300243c122042e032004919002d02c949245210078010030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 811585791 1250 811584541 811584551
    0x1213030c0e0613021801050a03141815040b0112030314040b010524161e080a14040e0a1104050d061a0d03050a0f0c0206161506050a121104 61
    0x1100960480005580303a500c038410040e0a50200e18043c021240d03e040c61000c45c18990302103400640d11a000012007009050302c800c1101d030030a104100d26840b880113401440348500c1c034185824202a60b820b00c1000d1481806c04110114140340c08550461708203200715013094801741021001001d08904848543c0721820501051111048110341a10803c8403010b2106002d03003c0d5600c566900030701c8801554060000096003003000c00380c20001400b070b900007030302d84615140c5012a1050402c08580d07241011607109021580300d41d200740303c4180d044180b4905130410450304500344004140c0c1c54506e03111004c0d1030300742d19000c0c00c1d42c0040c0405450402180424078000011340750500d03e1804028100ca89076942d0707d400d00c03182c08403640680303aa1b0314009401408490008141115000703000c0c254800c00016260312004240482e01823185e0103d22080e85000c400c40d6451000034000203060003018802d81d507070b5500d150110f4196210489034003206203007048802903025843c0358068581 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 811587041 1250 811585791 811585799
    0xf03020c010908030405130b0d0501150801320603071502070503010b041b08040809131b0906090b130806091e070608040b0603030714010e0106171213030c 68
    0x155803454200988980c00342503100d801d000d40d42d0107507128030355000e1030045070b000080c4c001c5e0f8000c02e60070b400681104e126843c213440c0d950070358203c84080c1242c2c0307103842c00c00c1001c21028841c1e0640c261807060b240c00441c1372100d600c0020001c4190311800c8104010200b0000d6404205810090130001c184101c5080c004c18080d45a0440380300c0c0038025401c001610b2404c0c5000e20a0ba2603400c8160a005070080885404494903000140111201d0030100f0a0031900d07a40c42c08030f0224040000701c041512000c0c1c0c0350381185025440201400c1c080b00e96018400130f90841d9644003900c8422041d1900c50109401014400e8010b5000c0c980c50f01652007804844400446c0c05104414203a1154004e044110700c40355031502280310740c800107146900401d0001d8552482d00e6000300d002170880c0e0406060b500c4006681d0741400d85180716a54401a02e00c03c100d0a001d000000c02581702e80c099072851020300183ca50303a102403003c18041d400200174080011401900000e150040c82c404042511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 811588291 1250 811587041 811587043
    0x907051c1113171e06071b0501050c070606081f0f090b0c0a090608131e12181a0904051b031003061404020117040201051e071109100608070c0f0302 65
    0x407a421a032050b000354074210f504610761480a02000100d10028401640c0346c4404907003045d100d00e0340c440c0a200c47c0000c0e1022038801d001d00d5004684030359820350ba4402e945070140031607003907a000c02d10781d811401100301e0400e50610f00d098511429480413540d1401101000300410724000001c00a4640c40180038012a0700f101803e0424820b480b4015142e80b10081a40c43c8941201e04450000d07094500b280058021903030f8005103655003800021740d00c25640d4105443d004014504001801038548104000f080c481940081c0341c03c40c1c50070104540c0340e1894a20f48078641402c0c1c0200d4581011407903403114051002c418038008403150780c8a007411003045400405905c01540c07940d04185400001a901074032290050394141c4800c1d45000740c2e0140ea200d103450082050741030140a0141c1c04c00c2480c020310598218002c000c1340d0b5600d440d2898800d10b1106514203d074080c910500030484900c05601e603107419615282404c460640c7c410404036140c40d5030081c002d0202c55002d40100815070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 811589541 1250 811588291 811588319
    0x1401031a061b15060d080d021e0a030c110c0616020409150b0405070c0f0c083310170304050d0f021806010f1d03010204140907051c1113 60
    0xd942c041d50020390400d0055904200d0594030140c3c80001c4100c49000942d1340c80003406c000328014405400d1844a0007000702c0d510750b45100781220354001802920040d81803203100c03080480703800c22440b655280d008069407000d408241034000c12001485603a909002d0f00030780b03841035008105210041007440d0140c12514006008801c441c100505160185820b0060ba40f00b6081680d421608903e5529001e41c2a01248000e480c00400b814010900b8201440b0007045c070100c2c0301907100c1c1840c4a01d080c124074144020340c0f160640c5400d040c08109003105540b802242c405c940c41902c94001014802d05500ca25840300b0360100da54400f400c10080c051420084150007103420b105081d10350700400300c5403030701100e80328006181c8000f1101d16a00540c852072403072840e045500d50740e40c40c4201080c01ca90040d0010700640410b1808246140361a03c0c8055108180c1d1038401d04041e46a401c100303440303d0b00780c0c004c00c038252210100140701d2940c4003a501850350000f850038404d942d80346c50709a992 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 811590791 1250 811589541 811589587
    0x10e2430030403140a02011211070606060905010207091404020f012a020909010203130b10030b01090509061b0729041a0106020a05030d050907080706031506091401031a06 75
    0x40307245015050013980c046800d0340e8068040e100c0702483d0121a01c00c60040141301e08643e110700085c8001000711b0b005114820240c4882e032210081d50341800006850118a6440f03170300142d0610074500c1800310000d9089800a5050710942d800d00080720040c2c540c4002c2268440000103592588007180180104600d14a03009072044800c503210134034034500343e1201301e0f241c41908000c0300010300050055031800390f02c0109240144c4140e0381302d230740710141020280e000252041e2601d0a010080300203004040c0c21108020094142000c81c2c0810300690180ca08041c246000d4107a1007040124085066005440c48095003813552400d0324056140b00c80c07002150f00045a0740001180507400020204080c0d0341000085082c0103619402c3e5010700801800f60303100d4041c030791001a080004110342405001c1689010490781a00141c1004000142d0300c42030810003410000c2120082545440f1030a000c00c0c44c0202d2010301007603045000d4881003103125000400040c003854020341902031040c1d98 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 811592041 1250 811590791 811590803
    0x6031605010e062a06012603031b0c1203150a1d0c1207051c11070f0f020409080c150705040e060118090f050c070b13050c090f010e2430030403 63
    0x510003451030a81260080d201f0f140300c40e807081010401100001840ac41064004403c50b441c029508201c01e003451010041140c1144000c01030080b40b288032000c0356929030040d01c00d40e00540c94110959008520176013124595035451010500b810000400c07070300b420032606000e200da030405c201d00170900e510000c0a852401038050b40141401e0903401400030584030000d000b0b0a040f61502e5540c102d00c0000c4d4101c401c03000c3c031034200e801600e0b030b03000390b0700514080c0306d01075107800e211981d560030000d40e4907070340340c00401c0c0b01c040151840e001019a010380c0e50780703070f41415070707580ba0001070301c0780005003001c0f00d0441c0542c0c600092991043d0402c0c580740d4883c5c0828040c41d1145e8480403202d0080b020028048000d000004203a41200510429070318001d17821a041a450500441c0c94228203903004115061484014841135074200048c5811400f8247d00c0180038036192402e8580c6540095000d100b6101d4214000c01803000309250200081d00d40d04400c140038903041403a80e030742c0c0300b84000c0b694 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 811593291 1250 811592041 811592069
    0x1a0307020609010501051f090911030f0a02071a1807150f020a021809070b040905180307030915121103060102070b0f042907030806031605010e062a0601 67
    0x50700b0103003e82412241c019060b4074104001042c02d041f00e2440032001010000b0000c00060203c407980254070309019000701c11942c90400d00741d4110040001480c02c07581c180100441c0c000a80c1c00f1480f5418009144601180c070b450359a164035841000068441c1d8078854203001140c201c0d000b6410051020964036100081c036011a8244d88504a8800c0654480400c2e220045084928460701c2d03444100c0d1820b484400e600d90303400c1001034209401454003070343d0710800c105a00d140c0c0d002d4481c0c848800700042d03051904c41e540c001d040e00468002c00350005400e0490328811402641d1164100c0101e80081c410f00000b080c4900d0241c1048510b18010720840c3c000144000040040b00c611000c0075080300d14141c1014110907480040c0038041e00094095019240100c0320a40500402c0388207a8522646051407001c142c503240c2e074030408490110101000300905e07070300002c00810350b21003034903c60707110b0f082e42e2400d841d40030704508400021310200c4039074181000d02041d0f01c1d068400d4285090300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 811594541 1250 811593291 811593301
    0xc0206092107060315170f03070501060306050112020d02130b0303120604141009050603030910050c01050c03010f0905151818010c050d0b0f1e01030506041803080c041a03070206 78
    0x109641742d18a404c50b5440c044d400130300a04170210070b46181d0b816003c003210100d80292001a14642c4540b078243e9169551340c20900401c00c15000d002d005042008040c04e0036003480e00001d03100c10011100038401e03d280e90070a041305209400c18240c0e00c2c0010f00340c0e902c2d46910000c509041c0c8046880c0d500c04d5203414680f039400f50380c030b025041c090090040c1820506003040149001400c01030002c40c0d06110920420f10f840c0c0c1c990141100e00341c0ac5560700d03506d41115500d01425110007802104101380b0600060098080c0056031004031404940c001c1161f4550030303d444209880720b943c29401031016008910841180c0c00c030280610003c0c000884228a0030911600325200b004d0b010002420400c400700300b1801039000950344000c010550b94403ca003090015100317154003541202c00440191b40d0b8041581c0600c112030384154150b50521000405020381030708900700310b07002000d0080d940c0200f824156080e0a441c0030f04041084005014080100888a074004503420f00041c0304d5080090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 811595791 1250 811594541 811594547
    0x1b030905030706113c0f070902120a0902011b0c18060609080102090a12020f090907180209240418060312030b0306070806030f030d06031101110606010c020609210706 73
    0x490352020171080700e55000460800c11215403180500101c44d80724540050100003824003c1c02d00400e0040001a0380754000e644401000c80c0c01014241e003d0f203441c60540150360882e12078051044903410060900c4020b2620035911012608900741d80c14915408004404090784041c0c103a59090716a140001da84000742800e034400d516a03150084000d107020040d00440c100d09461161009100004c518680030100342418030845100d14542c1c000001005050800c2c444506144007000040d850460400f010440301c00034229464010803a00b00b240114000180c2520301426a003400c40701d4900e1489048001b8080c07902003a5003078690070480c40d48440c000e108024541002402030101541c8039002520038042c020201d0360580644122100b0030a03080c401413260f507080100018040b4110308010301700c0e5040c4c0440c00d05010340f00d01501d022050014080798050801d191090500207184041346540c003449031541d802c400404444180032005100540740082011b08844238580c0da22070407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 811597041 1250 811595791 811595833
    0x9110d020c0313150c15290a05030c0303040e0c0f1803010f0e0c010c031e090f2c070c060609240501140d0b0319050106060201020a1b03090503070611 66
    0x204041088004401d0001d180c500254002e42c4100c800054414820000c44078103103011441d140240f4044603400200f13223003050085001e03017429001496803c0140303020a80c0c234452070007081032a01b9180005010303250b00c2c0b4100d8424180071100f41d40c80c0c9100c064901c07507404c001c00d0050f21950821440381d120a806220b0303520340040c0d401c020312a4161850064440d000d91090503420884c004400d1982c0049080b0000340071b45c000c1e81c0d040c40f11850a211034440e00d4040e0040d152a660b0907501c06003031034410f2000c0e0b9075a0680b01c00031619071140340c0241c0e100e8014107402400182450000540c2e9070380d035031221642c0c40d03110201c0640c869171941042c03198400c500640d0f0201f0b8091101c540d43e10200400380100d4511207000017140c5c441e10300081d1820301b60303008603842c0c05042c0302c1140400c1028022031000380b086000950600c0140100030305440c40180e040790030412258610000d00d4801d4080c10010078024081c0c1c0d81181e2100402040c032a004403913039a05200310324400c0007606800480f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 811598291 1250 811597041 811597079
    0xf05030616050a30050f04030522090c0f030e0a0b0112080c07172407080702100e070801060b160b0c0d0614010806120709110d020c0313 60
    0x44129211601205440303d0b0441d54280007004500040182010310a28540d5003484161031264001c03c600d0b8000404d554006002c502c030713141c0c0c000512000039048010740300102031703e03c01105280c0082e42904c61070440c03588248104e0b03003403600695906400901c0c88041c16020341d010b02071903905607007171983d58400f440700508120700c400040190745095030796103001d82d20410400345400c800d0a40035140044540040100c496080300ca103685900c20007080b401e41402100880c14403c0440000301600002003010080c4034990b00001d0606100380651800161001d130308001c480c00000400342e4a4a2a00555a4039860041c001c034098a16a040d02c0c090720300c06d00808400c401590b54001094805080310304100c7c0140300c590f0344030381e045c080c06000c1c0003a0030031005088510000101401c0300945090b004031011642c61004020208610041d220403420218506203010b0300d0310502d101d5202212511480850070000e04030011004003980101c032403010f88002d440740c0624000b03142c8110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 811599541 1250 811598291 811598311
    0x14030c0a090b070b0712021b030d050709080c0d020d050303040b16182108030a05040c0b09031e210409050106171812040b0c0618030a05090d0206130f050306 69
    0x1c000b0720b8040c440d00448450b1b03944903c000d4240030700780350708c00b011400800f034180c4990404204130035440e080b84240340d40085140340c45500c01d89440d40081d2070321005c0b50720354000d40040d4549000d540f00c4080310790410f0b41c041e044a980c0e140070f0901c05200340042d0760301140d02c02003135100942c0f00c0c41400d8104d459503e00421102052800a01540c1c803030306d10991606055005092034082074540e4003440c8a0350341e5550100d1540f825245c00e00c4044410b07040800706050034404142d954400103404041114040311240755003507020211072421022020f03402a41441d500074088241036980a00121340e0a020180b110342d0b00c13600203550200300f001407070408a2900000542d50700740112181900e09408080c0c8002082c52116050603174019003040c47c41810016200c100c1d100704012003079103c2402c4c1c50320680502040610f5890b4803030508020b00300040401c0300c945a56911a002d150325500800c003540d40c88440c000b000d070407030807031003401c0c101d1452600004050802040300307885103948032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 811600791 1250 811599541 811599563
    0x50307021b03100203040503040806060d0c180f0c0201060e0a0506030604080a142b200904020409050103050d0f0311040621060303030e010b0a051e0114030c0a090b07 73
    0x10008070101250070394010350510940541e2140302c0702038801035000d5401038015554590500014030715000000c0d1050380901800c4540d000071854035500401901c00c0520040c41d906d014901400c06417000c0240070b2203540c904298101c0e031540540c083d208480c003140040c00c0c0c40e0b07100c500c0c8404031f0300304882164050304608001000140d115000740544001428401d1051a440d2800142500b00d480a4492040b604030b10304050f05521400c10907003214018148603440380c481d5100030b0505140903a900000011604030403e540700c0d01034030f014020150080000350396904041b6502e071442c800b8040801d640c40d041220662090003000b500e41c080309059850310b8070301a41111001c940450380c48184241c6021126903034418040e0300b009500070b40e008250100c001c0d82c803d084480a04004c2d02c0781800c001708000c0d0b512000311541d09032038089038141c075845403030006a0348a0350f00420450908000000c00c0800c40d440c602a0590070080d0b620380e9200341c2c03501881c0440e4442c002024011080720 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 811602041 1250 811600791 811600813
    0x619230f18040201110312070e09040c0b0a0225051813020609011704030f08010b0a09090209030a05030f0711103e03031801050420010e0a09140705030702 68
    0x301c600395005032043c941044210284042d031404e50300441d420740303801c45155090041c032a03030000c0000e90140044a07a16201c1c28640c0d0764200a00c5244619000c0500c04589102814028003019151908803055045000c1640401255002da103014451292071350141c100d9809100403607840c03141e000281018804501341e02040415000907000c58100101054a200494024541c0743e0007948203441c0c56440c0f00c081030740507140c07220580258030b03884c40900440c1d0034150700140d4030045406041d4010382d905180b03000b00741064000d5002030b003548000580440c0700d44401004001d018010307103c040c1c44048010812101e5001c00c000e1000290f00c0b0840c0d00d03c2c40c24644000151034010511020703050000b010760f06101c1c5608084c29201c3e40000c400c20003401140340b00c0d00c5803100650000c02c4103290035650001d43c0c5036000100314990502d20f07a90002c45c4d0042c3d8149040d054000c240c006070540d586606005040927400185c0c0140707114000c00c900502400a4a024076659005041c000ca15 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811603291 1250 811602041 811602079
    0xa080a09080f0a02010c110c0f060706063506010302060901050c0709062d06020d140906161412160c1d040c0e010308120619230f 57
    0x1049030640e400d400801003011408242c0c0010001854581c0002c16040c406040142100f000c0d460030200741d030881321035040c170341d030303072840043c0c24407100b00e03509622a50740703040800045c0b1b0aa080881250000c50703800d980c000705900100161100300c02240385205a0384a070a40710602031000a402c02000c1c4140c284641c003900240c1038003c01030342200d00b40d607902c40b9200c080d209103070310000300d0400076203100d0f01d41a000800d0903415101c519940f190245480c00080d9240703040140d4604102c031260f1800e50140252007103802a9500030005511a0500c034201441d504180004448510104600c1c43c14181c0109110f401b00414401c0385080c108500303500c00795a02c2c8502c3c1120420104e00c40816542c0d07603c0007a00324104035003c0c9a0940c50140303091444030712560400354041e103000e401080018884000c940e20340b40c1c4a0b0002d02191a25004a004d1190500040a522440d800b01060300320640c800c1c0f0f00003031451640301c0c0c040210342050101402c0c0700b00e40150000180c415134018504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 811604541 1250 811603291 811603301
    0x519030e091602060c1c052a0309060103030c1a01142b031202040e0c0c0d1e030c17180106230607030c140706022b0815040905031e0a080a 61
    0x1113004481d96080380c6d1383d460302c00c0742e20445450300b071045140200c000c00421100c240500100c3e43e2a2545503081041c052980d0f0a414840181080f42c4030039414200420602303941e91001d03511407804a20b58542c100005605806040f060003a400e807052440035181d40d8282c49458800000f40c08840d940742d8800b11400400e0406070462240c08020001d1540e5124075014444d05081d14010b80320386082c41942c0c14004825000c030700f0026038410561031200424880c040b0351080b4100020140c207500801e039035040d600b031032498404d0b62510801c04242d5140700310706017869a9034002c000703040e140c00303c1d800002000c40041d4003141220040c4199414030744000c01015010703050101e46c1c0c0c1c880707941e0300325101d020500c911040d4000000401410f901008802242d900a034807510300d868400c20b00c0711306a1540e9820b070040054810206040c1c8c0301222a01c82180c8010b0400d020000160404a940b6804011041d11816207901c0c1c1d5007080007410705560b207801e030f0355031405041d0f16030460941c0545 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 811605791 1250 811604541 811604557
    0xa27030f051306020102040503070501050406020d11010605060a0c030201050105041505150d1b11120f0306040e120a021608060708150307030311011406060a0c0519030e091602060c 79
    0xc04200401d0b94007200b00111004103056400980c1e1282001d0a15041100300e40c49541805824401403080c140c0114041900c9100f40c540301d41d0540e03e020308107001d000740c0d1788080e0301300d5000a811010643d00c01c0140f12010f0007038009000702e90b6640c0030701040b50f00740d180c00c01108410b076005100510b41070351440704e6410a06940c070300b4502885002801c644c191001c00f4683c1c401e82180c02d988582001400311035400404c050138010840b90b00f207e0711841207250414100d040040010040da9442e442a0a103070380300c004440032110072402000c102d034001aa44000b40c0f00f4080110401d01c810300740d05060b121b80c00c000d84005c1c0c444040c00e80305100064442000410f645582d0311003902e04000480045d40256110f2502d0001c95942c0b500b101c01d51010380401221100c1000703115100e1004031410b00c00546000041e201d03942c18407a00300401d11007a20b01076071824150b0018564400007110b050501164603040319159060054250100c035626000541c102c200090302000540e00079000d81 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 811607041 1250 811605791 811605797
    0x2100f0e09090303180c030703021309050706030b0a090603120305040f0b0f0708010e1506090303040f120b070503040309031217091c030b09160e0303030a02030a27030f 74
    0x6080080000d900100220349a034115400407081109050041540d511705845640c090000b007140c5c80c01180d1502040d0001901844036828503201080040c0d10826078030b500a42504e80b159150030f0010007078480100424031034010400045184500c0d8071403c0212588510000558070b440d403801c1c0e002e844001c0c400c0c0d6035450b0499031701c4045004180d1482c03203492000c0c5020020310340168050134120f41a040030340c1a8100c20b0800c4040b44130070414158242e82100c000e9150084080020301c0c511458000030003040c1c3e1035100041c00645441d50038038140c0320711303045000c2d0740d104101128113000445026000503203c4801b003020481c14900c1d0013200e40c40e881c094000a10050840000c400165120740031795000303940007001c80d0b01180008160410307a00d8144140341110380010000c080c05040388008010320030b0402e412a001c1d15040910032805000d0302c4e120704c1c02d007200c40300940003200c00d40001030410003000c818110442040005101d00030b02021202185c0d141286e0000f4070b03a94170424 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 811608291 1250 811607041 811607057
    0x7060906090f03020d0f03140703111c0b0312090109170709180b0c040b040306022206170f01120f050f070906032a060c0f080304030302030a050f0402100f 68
    0x30910b240300d4661500e0007900100641240044020540300a10b002c8908161a1030103482d0710f69500d4076881c0c0c0112080c130f408520b114086058208612554903480d80001094681c020340120a82005041e2841201503417200c500c260f038441e02520800700007500240f040941802001a0342442c1c4d10708407020f4049441498940c81c40381c0071100d050000d00e0f0009007640902c007c012103400160351141055640b0b41c00c0c00e261072684440c50181e0702000305495000310f0140040d100710311001c0d0740b000905151080060350f034580944421564000785461138110780000b46004c8050003e07504072450381e0014440c00c05580c40d000ca403500c1c0d000c0103c0d074600400c0c903c3e420741441003002c203000e00340200000400e94954545110140720ba0204030390311124600015024002940448048681032305001200290358946006a006884402001d00f500841840181645640554894440c0720820452074482c0d010b030915200c2c0440b4029031111456000d40404c9109400c0394400c91600d0404c058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 811609541 1250 811608291 811608293
    0xc0206070305030f10050603070f11240a1e0b0402160c05100c050a0204090305040905040b060909010e250b030103051005060d0c0302061b010203150a09110706090609 73
    0x5856800031005900040d00403082c031180c0e860216080383c1095030304411540c55850b10022aa55000080682c0c4c18084090b9042c01c816020740d5207510710704030780700c01da03140340031071600e0780f5803030399100e071912808010044c00185034001030b10600c0c8000f1082014928034a400100319405495a4030029030041d0f024000d0400190007401c5803040b891180d00c074000414200000d000354038290b4903102c0100304000d14000003042c00411045042a019980414100d0440c00c0950302c0744501d6008520043c0340504200c1485801005540554021602046140c586950450a1740c2c81c840c07081c00a40c000411711f08502404a04007541580d03400422040b25a0310544410a600241e00a1b51543c0000c00d081072848440c0c890700d5449002103c03254240040f41d103500c0071b15900c0b40402401140002003081d4030742407800d0510490a0250020745d07480c40c0c000c0000c44080c1c90341d9655801041b411801081e40034540c0500074000e401e200782e86084c50560744545005c0d00342c8000c1a02c0c0c0d80d98461441c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 811610791 1250 811609541 811609549
    0xf0a0b07090b160311030a020c030d0c0209040b07090e07050a091508150a05031005100909150509010b06180310050114040b040e07030507030c1410030b01030e0d0909060b0c030403120c02 82
    0x47c145801404a060307000045c076007000c0c0d46101d010200301d800f40c054001680c0e10b000d66900700c0d030840d503030540d203554000094480c0520b68012180c03001c90401000841544000208811402c1da42c59a030398a64131080203810300c52480e860008104100c0000702080a9140e02c90b0b0000300007068105140c0e80c50300420300309455031061041701078076042001810343d2100700010040148040401c41ca400765207600781c0d803070b030250901ea284544a40101c1c0130244250031404003000001c00e0307507598480c141420725010700441c050f140071303000304107200c0054112846258121040c0301008004800c814041000502400c5040d550207035468001c0812084100110009544a04001c05615045003843c451114407a4040425825138041821040d02c07566940100c1c0055402e001c10700e0b010f06801078000e00095003a0080500c03600412400260344040c101d011101d080c5004c000d9540c40d681d4103e841d100300e00700c00e45260300c20401040011604400e8069043d40c525002d001124168009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 811612041 1250 811610791 811610797
    0x70c060b0a080f0106150e010f0504052e08040819020a06060303170a09020a0303080a0b2d0a030b070809030d1104060f0f02060105040e0f0f0a0b07090b16031103 71
    0x22802e035101d95101c180c4040248210700107081400034001b052921294014000e03050041c1d460b04021b4860f400f0b80310399010b070080d100078100041c000c2301403140aa455004011103c040d0b00e030210580d0104151322800340440c40e01a0360095600c914040701320507803006840c0e00c0d5542004511460840071301142c564401d0002451081c0e41310b030310b041c40102c001c01900704043c1c180111280317010205401030b50f42c244a1801c403a85410880c241c0d640e40e000040051200b010f60642000b96481c155180194004644004280031880058445c1040041c031141c400c85000040a03201104086040a4002c074070490703211500204a0345807041c3c070144841034a44504441417070400202c0e05018403900311a49066184861a2010080c2507240000f903407903070184500740c0a180c0c0d41141d80c00e00d10b424440c940d0315207000c000f140c031010344541c422582c600e19450240e681c0c070000c0f40800e82c00d510500004007100c0311030382c403141000c225107002110502021000c506004c10000d409110348418405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 811613291 1250 811612041 811612049
    0x903210601140c0a1e031e0801090b0d080a0e0a0b1602060309120403030c15020f03070e0f030d02060609090c010903080c0114010b071202010e0d122d0c050a08070c060b0a 75
    0xe04403c805d1181307009484800c003404006010214064040011030740030307106c01d0445002010100d0440340c401c0c081001d910030204060040000051010300c119003286441184560a0318441c0b40070b1743d00c81e01607103280180c541090b80c2c032600d468240003502e000006180c104a4200c25142c00104044e401402d5a000380d000700d0229001203030500c140100c11007a24100f01d41281d00b545003000d100245d084601c40141220107200181791003200341d8540061a214007000a421929400011640a0b540742402c4501c544200c1801000580069003c0b41031303440050107031581001c150441d501c1540c1d41d08241e0040c60151f5030340700241903550b641e00810380246034902010340e558605040071111402c40c061501d056a043c0809056801c00001d0b882074001094500010004400d01c00303035001d08a10030041055001240302c2d903208003c4034000012070704204100300200715070540e081e6400c0c052a81104c3c081040d40c400529528050480307064164400e12000692501910010b103401c0e005800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 811614541 1250 811613291 811613333
    0xc090424032114090118030b010815130c150c0f120305060108070206011509181b140d05040515010b0307020c01020f0c12070e0903210601140c0a 64
    0xd03086806068240e500c00d1461210b140200d43d005a402c400c1c102c40c03141c41840750400c030380382d4494514800440107070750203164000c51320b40071075950b4034100d40e50314441c0c031649045580700b001180351658030100c200349503076102000c8070140346800340b03031604640d083d8000344c10f0202c051a84000502c03080b06601000784a43c00c40303100410304030001001c03210000c1000e41800070761000e116140f41c00245040c112118020044109107030081c04842c82404c9500c08400d04074042e00f0076841e00500d8208864075104000069501c0c4441032086905185480170100801c2041009501b10002e82e0419980240910100e40c072b0074084000704041e42001343d22800c9002d401205104044e45e0501c014210300349c09200600729004840d980580300e000000c1d200d485108010340d41a201c42040c0003030002000f01c050035038880e18011002030307200d6208000202d2202200083d41c845540788030511405640d040e0f440d4100c052036507680207050703446100760041c1e51059000200c00a02c2c01400041e1942c103143c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 811615791 1250 811614541 811614563
    0xf07080a17120406020a03090206070501050f100e01091505030d0909050619140f0d0506011503020a0c0f06020f210a0204050607030f2a0c0e0c09042403 67
    0x3060000d2840241401d001501d2010018280d4481c5841d503000c1d08543c001100603607a944541c0c040d070040104d800025048480841c50105010042d40240d03c103c08144bd600e5090381e40040d40c1400309001e0240b0302c07400510f40b0041c040644103a104010001c0210700604010b9261070001e850000d0803540b000008542110501000c102030240c0e80d00154150f46040e4000080da0386006043c0481c058601a07450041c58454181c0e991184900300081c00340c1010360109041c00c20503140c1c07030f09000d102c800394078007038107015042d119100b200c0c3c520340f0969400b104000c4030703941d41080804032403082d41d40d140c00340302103650075011a0091501c40301c150310283c80c80c1040e01c011070b0703603c000411a01d5500c5c4184000c03c4603032a00402c941c206540340c903010385002c500010660b84a07280e90b0000d0041c07107800b540340d4085201800010000d03401620f1070040c0ea40d60b4444510700150898050380c40701801c0c4030840e101e0603d41c000504031040c000d8400300440d0403100e54482141d5030350058915031444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 811617041 1250 811615791 811615793
    0x40207050c190515070c03060204180c1b0b090f06090309040b030c03060c07050111030403320406050f1903061a090901050904022202090f010c21020f07080a 69
    0x10b42000c0c00c0c0c01c0200c0d08405551460a0700092040220125800140c40300280320b40820030626040c0020b9540000304640700d607105d551201c0350301c1007201c40724440740c40d084124003001d000d080e00560342e0500d04160031000607903603181e512036100a44203940130320404045440c40754081c01200d10401c4207000654699a400e000c01040d507041140040c0250807818100400b0b4030045001c0794004d400700c0815a8907640d51070241c2c010f00c010408003401e000040144030805a002d00d0036074214500b00d41200312034420600603209064030380490603e048040000308825800340000d02021101110348a040819803000204102d030003086440001c0d0751003606006400310941040e11008100041c1403d00307503020080346020344180150b41c07141c21810009402c40d95500c0c0401764029110403800b08214089d400ca501035000442c42c00d22801c007a02521485510030703411501250380051500c943d02c0c440c4014000d20072480d0804904500840c2c9507882040c81c1044450b0090100c040189040c0010f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 811618291 1250 811617041 811617049
    0x5120117030c151f080d030b01020313090911062a0f15010602010c050301080c0d0f0f030810170a020f040b150703020c010c031e02031b0303010e090a050a14030405040207050c 77
    0x1082020703980d0080131803050040f05000200510060800d0800003404116003005034611300820a81600d080142000890101e505401548069124211a1000003958010844140155201e0031442d03042441c0c001c5000c4680000100c4081041050340d0091100d07020090410000c080800180201d49004001c21a4240b0410426964500e4402d0640d41005506900c81e4603110029201d800180b1804c001d010448900c1040710b60b001c0624881c0140914016040c22411a0b140000c210308079000640990005c85c1c8100e0b401c0c03490f015110080041d8208081c195158401540150ba40c4d4200b0030b2030f4a070340310300c0390340f4019155080c1d4440c4001c1c68001d1400b01c10705d01290412980003880b400080d00401c240180580c058440d036a410401c6400b286140a044503140010020362440015214080025416524808003200b01d46e61040c2d00c1d1942e510001c080201150300440002022455180e10a400740c42e504040d207150507640c10000d4260b800c803503400e454507000300f52030034820b00d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 811619541 1250 811618291 811618321
    0xd050a0b030a03233a1b02010c020c130515062109150408030a0e030d0204140409262b0507020606090a0b06040b0403050105011505120117030c15 64
    0x10700d00080c01e00c0e0140c112400c0c60f0300001c10b0f200700d061090400c8041c0f02003090070041c03070300c80107000c05c00c02c50f2600f02111140301080349407141015501c1d0031450260301d031000c14070131002d40016281c4414800f42010741002014000c107076418400b4880152195070b40c8841c018034500c03681c80c810a0084508540e00c42d1466005002e29141e41c1c4070a803622217080b8400442603020360081c0c2800d0b141e580b800c640c5400b0703106602400b400c41c000007400401118207540508241d8001c5d5100c0101c00d03070090306000803291188005040c0b00c541c007000031941c0c8441701c05000c03408640c02c1c0d03260602d034044100401461200e0050303040c00d81030050406851145208555000e250307172004210a003840c8002c00c500320342c0600026070391511804108540d071518001c0703400504040808554076540e80c20f24600800307081c01800340c501c000361034600ca520300c118140da0490038480750b10f060b00e03440c00700080c10f80191141c1d950300710301040c050b0322001c0c1d81c144042004e211842070031036003900e460140040c200d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 811620791 1250 811619541 811619597
    0x6020c011211131707150813020405100603060b040819020a0b16060c0e0117130f0501060924210b0a0e0f1203010e091603051006090b060d050a0b030a03 67
    0x2e800f90a0070000c50640c070138800b0304246c10342881700356601c6000e1030324003200040e05d0182d0414100b0707080c0624820301c0c0700c40c1380032150301f17550400c8010384404107d486481540310300f044950000d10740128803e0216011851684011711400c1d0040d60780149040d01e40100302c140320b8041d0b07114880e90501c031081c0596082c081c4e0038a4200300610080d80042c0038054090039806070504218001140b001a10121085c51500b1201c1207034010a64a00940a00000d00a103c0c095080070104e80203450720054038020107a00031a5201807504000c0e00c00c090400180c0d1810f4a0310459644401064020b0202c5001d080c4d090348c041a40a041d000003498104071800d41d03041a4032807140d500c00c506440040d40c1c15a20f40300300c144996221841518500324030a0341190440ba50554004100200001c0341100d900803420280090390f41c8201d0082215044519550021000c004c3c00c58011016800710b54020041c10f00040c085442c4804685840b07038000d011800300b4805411070040040c403241c54664a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 811622041 1250 811620791 811620793
    0x30203010f060b030f093405010807020703030309150507020f12040b070b190230070f08060a0b0f07030314060612040f061b1806020c0112111317 64
    0x483c83e21403403d11070301c0018214000d60300e868021800c04c030402d000c180141c09200102101c040e0780c4020300c2d1940607407450300405441c1c564100040c294000e49200f032181105801620301c043c550b0700e080d00a0101d00804035480d59080b030281d031510101c0d2095502803480d0307a00801b408281240303032074580f03d4006070012000070103000801440b500350080764880c592110b001e02c02615152222403403108100c81c9400310f5030002c41e019065580128240409402203841c55054808102d4280355a0710706950380b000164a90307030040c400c280900b6a050700903c0150145889075507070542081d40da04807140284c0d078060006084024190b0600884a401204280d9580d0f18101800019400c0c4a180d40520041000800150034812403c1c03060982e40e400c0803080c4807956901e400c0c000407401c41e90300b0b00c000c0b50000f424018007007030200500c2d0540d007854004080c1c1e95054bc0054400d07100c403035840705d42305132101d5a0070007407080403024101c1aa01003898200090810040005003215411800d1803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 811623291 1250 811622041 811622051
    0x1050907060e04020f1612050f1204050f070b0310060801120609022b020a0e040b07031104030807060218031b220c020a120f090b161209030203010f 65
    0x50160003040c800221000c82c1401e552052800c4040b60181c06050074481200070080741941c00e082400c0a40709803548a091400c04184400c0003c1e113040c0a603009080c00808140704030304289920140b101c0d00240900126200320302c00d0725240b49000002c2d00030401c0d282001c414410b54083c1c4101d90400b900160518840c5581020f5044000c4054003501801d000d840d1560070042d500c5200c190341e0418410009400220300c3c12103410340b24904403200301d0003001c850038001480c00443c00d01500403030340304210800c02e48945000300c0207080d08144114500c4401c10000000820030002070625600c40c000150b2140b1138a0888800c010511401c24001d4000300c03242c90b04034040c0400340411381d01c100c820900f00d0f1000304002c83d0600403102c82d448200d02c3c0000524039203400140d80f0388068468210012500800e001c1203c20410003140701004c6107400400b44607143d0305801400381b01592145c06071590446440301300d401a030381428403001c5000fa1704244150704084c060004c51100b00d0a003488 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 811624541 1250 811623291 811623301
    0xd120605030c06070c1e081902060306040504060605031f050f0609160201020906120f0a1e0b041b1106060a030b07081504020c0d1205060d030507051501260105 70
    0x1880c0c00b0491110b074412680020340604004121014201918840d82140c0442c11001e0040303001c459640a0142d83d84940302200e90304002c28950f00c0c4031a1740c054185410b40c0c84400901014100140085500b1619850007054503107007007245130340561070111400c60072065880150215200500000202484c1c00c00300912901e0395601990041032540c01c86200b0310300688124028003d8404a0398040c100181a21000c0c00402559010f1300d824400c20b82c10b51a051421400c868440b030120a40710148540c034114a1203e41c07003080c01d045c000e0400b1420f615040d01494600c9024900d89020a803100142d4201c1541003205d15070150003501c1c0c0040540c15515101c0b100c0400421840c104a508400606c43c014602090f070204036000e40300f0b64481e0841c1d03040300c0d15020120491300014641c030b15620a03400c0103000341c601545024019240c5003009807000c48560b03200e803500392001d1041c00c00c0240081d861042582c002c0040c41040e44802007000305012041740d0781402c0034840d030304100504c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 811625791 1250 811624541 811624543
    0x12030f1a010212160803010f14120c0111070308190801120c05040b011107080304090b0f090402041d030a03020a1b020f240d020a020f0d0909180b090d12060503 70
    0x2511042803140504d80351385140090300f00c03012101c5070062420300017000016843d110401c401040c2c0741025022000501014103100b80b8010440801070320703500021011250f0350107500140c510304456016903004589030b8032038004551200030240c0d401d800300b41c1004281d40d40904000d014005051943c04954240c0c1c45c0c0182d1038080d4021a4484d50381d415501c00700303a0040c4400c00c0c20441d00e406850714556180c51603900c03508244504082a42000c56040d0240b800c3c4c94404108203004100301d1941d2100d400340002480940a8402045400a89100e00d0708042010340038040c1030303a42c0503a07101c8020200803e07140086c05410414030502c0940c0005a84a0401140515041c0d940c0b074955180c4d401c1c400480b0120320341d44880c4507400903000a40400c01d0f001811800219021951881808110f8036521881240d102002655801c41070260080075000703a0981000015000704440d0662107905005c80280c0f9440202d50182d071102c544550468040700000d40c07100c10400c0030501d048086 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 811627041 1250 811625791 811625803
    0x6030f011a0702120d0e0105091320040b04180902061b120c0f19051207020d021302070c08070b0405010509060c011d2e09050a12030f1a0102 62
    0x5501c014680010072010140039400e4400c0380350000c00c2d10f800100804042e540700d179807980c8040006502c0a14083e42540607804941c132022001d4507012552030100c00c08401841501c414066070750b80c2082d48034070704c81a040a08041c0018109040e6218641724100607100414500e0b410a0f40c20a502140565038440c01c1d1003030361900c60144048081d5810b082800c00f4140880f00301d1088011131013142c80c00c40000e643d001d44c1210340c101e030f2508008101044100046420081c0543d101c0681c0d45031500c1c0600260480a2000e8240110100742d50700152031302050103c814100359021444000f40310f106030034203005002100c0640382803400d00764420700a20903400780d1030510000188400c01500c4940840b441100100020895001c3d040b1880810600c074440c0c3c41807911505c0b00d01402005001d085401c0c2c0c1e9103282c2000c1103091420555009031000304020f84050055411080200302c0070032503020b0400e01542c001903400c06a500405c11582030b0900809807117800c2d00c0383c4030315036000298 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 811628291 1250 811627041 811627049
    0x605130e07090e0a09140c03190c15051215030d0306060503060415030507030609140309010c030c02030f010f1509020304020a050108060d2f09040b07081b041503060506030f01 77
    0x4070f05943d4032031410401a05041c00d00510b800082d0408190007140401d04c0a420b420171019241035141c0c030320481407940c07840b41002d411030307003408000c002101c01c0d001550002030881c01c01908282c1070721840000344034100e4603021040d142001100c0c00d8a801c0c8a54000f91405007001c01c502030410500801381d0000a2002d070085907900ba00c007062200aa07111001141d118084510032510303860058090010781d4411120504140b862601c000070110907602020410703580c040d6521041c0c1c504841f010801da00c04c1e0303051b010b4213a506030080028000c0e54001502402d02240b8841800110003d807100e581c0903090091040c0709100043c0c0e120358001045520901c0c03c0706040d103d0100059007105a964000c0072040b9104174203c0c1030880e041400492401c0c101d0001d02a1a000d0600c0710000d801c48008140000301e00001e85000e02481a075500030500e10a035000700d1085400701b42070b507446034020461300e9059001c81100a5894001d40d8050b0078140c8201c5d045007440300c02a0a4030b101802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 811629541 1250 811628291 811628309
    0x70305090705031e2a06090612091b120709020c1204060f1d0310050910060617010b0901050720210f0316200303040605130e0709 57
    0x40440c449800401a200203440010192211050100c0040c4607540000c1c1c1164000c0c043c0099020030784410341140324644d1018064407504508203030401070254084401c80b03070700107818064491040e140c07031041c034801d565540092000c2100e496a111524441c3c14480f44600507502c206900b001e004142d00003152401040540c49800341c5150310f00340311a10484419114000c100001c0080d0310520a040145090300c1d089401c24100c3c040c402600c0034404010b40582c081140d40040d403d40d648466031050040c0700395030711080e04c0610b01059a03583e0740107a00181070240031300e9000e00142e851a0041181210862400b095580040d1883c0280c841c0075280c1260801403000e401613000c031140d03c00c80c00916400d458080c841e06000386c400680c0a94416214198100302007403130000c211004411034044440c10388440b560b52241d041d40d100c0000310000200c5c0c0b1440d0081c0c40230806880648800c1d118a5100c0c144052b14125643c540d6000341d180543c902c0c18402010303006000001a200c0d094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 811630791 1250 811629541 811629551
    0x3140907030215070204150f050a0e0420060c0a06050c03040f03050a02070308040e041a1b090307080d020f0f0604030f050307050c100f0e060c04140102070b0a0816170703 75
    0x1440f140614054014041e42180c2000c01034150714450080000030395088810400e803954564042c805c3d0780403075002d01c0010402c48004540400c1c0e03401502d4441c3c980f000d2481800c07500100104025410044c110f222960144500400300320490194070740c002d50403480d00d800c5140540f24441030664110b00a401e0140005200c44aa442072200740e01841c0c100c0ca103d40e4a554840345818104e00444040e542c0c11446241d5a01e440528001c680c0543c1b040b0700c68486080c442e4041d854030780e201441c0701d070380761003541e50004203d8424070171101c0340f80e00340c3c01801320700414000307060405c240301e0ba05c0347c51504460200800039403c410700c0c001101c1e4500c2c000c3c3d126642d81c0400c2e15248241c100d101418865a5a002c60080d416007145010100c00c0320309004007000c11512542d82c40e01540c440c096100148000d0000e80c007a02c140da11002c005104407540d1990703070040031143e40e001d030040c2c0001810700300400080112401c40e1425501540c90414161421848a83d2a080c0f019150b041090b48030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 811632041 1250 811630791 811630819
    0x60c050a140f01050123010f02061b0403020d0b070e03071d070507140f0d020c01050d020904090c0f0e0105090603030a0c022205160203032503020721031409070302 72
    0x421962070b0000041e0001c10103942c544560002411080c4c002e215410a82020314409501c40d12241d64101103076002800710b40c4864266034a111001c000c1c14450300018440080941e55054000083d02c1c043d00e07400d0440e0030182c000405107644541c030303140645c0c8000c1c000c00c60110510201c2180c500903680c078641d540c4a00b0701c00c5405114205029003001c2e048074040071204c0020070100e41504042003141e0191200101c1613855000c1849220b021034010305c186420041d40360010320321220b0042c800101030100c0d65800308044592340243e40800000c450501085140010360390143c441111542814940f92000035581d110b14803101d005c01801100c0340742191104044401c0c1d1107c401214012952011001d0005190484d084402100380105041d400c5001200322802035500c04a4982c0c40405e00400205004500c010b5000301a03003041003070040f421800c00200e040218005558074003045034401020745110062246048081c01e0502c800c600f80000e13550200c0398156003000c0b5003044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 811633291 1250 811632041 811632043
    0x703030203040227070806012303190c02071502011503060e011b0507032319020f06070e0f0a0609150201110d092006070314070c0f060306060c050a14 66
    0x400d03481044d024221100304110b03100b0b0000038034800c2c0056030b65401c056030348000454100000103070031240c0104030541c038003034030082d0310055601004510900d00203643d5000c00341d08507001e04a0b14401600120000e104220041c1403118900c61284028070481403c801c0b403150102e49403000a0206940722140c4107030441c02e400820309103007599611010030303201c0ca001070000d41c081d94040700011122201c802d2074100c00221100700342c642c11081818000c29401c841044011400c044d01944501c40c040c24140c441001000d201c1c402c1c3e0b903245241c982c006014809a01c500d41081880703419940030900000f07a1007071a40085400b0b5400044c08603402c1c940c00d0740140380c0d80070445c02d000400903086003c5400c94101400300380c440d1b0303d0320b4400f561142c8c1030008541c8404503254000c1c0c040000c080803a2003440e103c030244003010076191812141da510710310040000d82c001158110000e07020846181c16228000c010025810208014845640d6154564400141c0103000f0f5508200c9000c00c500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 811634541 1250 811633291 811633309
    0xa0e0316030201230109061712030403050c07030c0e090d02121605062401080f04022b062009130f0612080c1b18041401020703121b0507030302030402 66
    0x20740244014a0001c4d2820002440c0c1c000b4056824498100900051402802001542c15082c510042c00c040e08071110454a503502c0a07100350708020080c040041c030400d00780302074001540705c0c1100040309460310031008410f1000820340700f1a40c02c40801c900301503401241e020244608008801e5540706d9000360340300c8040ea200f401506510825041056841c04000f9501080c0c00b01c0c0d0b072110f07041c54004011075009904440048441500700c01040060600d054007c100710002c4a1002038460510002000b02c1c1100340d0540d900d1b506d41401c40d101388a1250095641c0c508991402d01d0700c0c4002001c1450b010080024100c03040d50f17150902d00040c4e503988241c000d441c2d01c0c1103030a9640541c0c1408070306500010142d000900030a880c003c10108203c522640c40a0050318200c0c42000b10011074010031402001074640c901d07100c604504002080c4003c2c0703600e501ca52140442c02801458000444850030b0380018071010303a0700c103000401e4104d0181c50700503900d441c0169aa41e01e901c00b1920300700c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 811635791 1250 811634541 811634561
    0x6070804020402130b03091b0a03110301180b0f101d0a0b03010501062105103807030905060a140d0605061303060525050f1c140a0e0316030201 63
    0x310ba035080120b240c030041740055001d81c0401c02103030084c0c8004013085007000b110350003540e40b1045181040000135903603a100d03034600380020000140b80e1118003070038186508101048a8440e100c101708410280c001894980020076120300880301414143c14900da40d4480040266007982d100020724101c1c69a04031140005025000380220750313480030041c00b403002c0c201c000e8070410201c00b078444d82041c0c18441c06200703040601c4030600540c544400c00c06c0f0244d409003c41c450198100d082c0805160000b0f042da9440002146c196564403542401400b0703003002d03040b443c80f6000802035951825880500020466040711071035644080005401d0000c0041c5c0c0e1016401040c00305081d07106503d01b038104000c807801800d091103141d44101000c41f51324130440c000e940d0380c1c0310120a600d10a03c1040541001080031107018685121134800f00341c0e00c0004220b0f000c0740c07602c130030340b80c0310425a1400d56a0010350029051241980c0a031550340c880c0034819070890140e61303911000c8185413003504555610 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 811637041 1250 811635791 811635817
    0x509120a2d050717070b0313030509040f14011404052e0806010b04060e0d02010c03181706101a0301060e060409020c0c011b03020604060902040605090a09050d0f0206070804020402 79
    0x1554480204502070600300c031511311400ba81c030300000d080844004036880390030580c103910480c50709503405441603040084040e0f0003640d16054907014000c40d100d862141303103d594928a40c0c3d807400d500035040344070510201e40280d00300000d21480840c58498628000c0c111000303030790001f1407034503450152080c950110340d04e0310031140000340c09044903008000380c070b140d44d0300c030803243c07110038103006c640c2100580007400501c1880c100004680b041229801c0b2901d040d98010301c2356640d5400d18010b03403903540c204159800100602080042c007148220082c522014040d052510307080c0b01140c240414402d4109001d800c0444407903e903544000c41b0b000d000003c00864480c20300d00801c650714400440f9240c0894103d8022203818210366110b010042c0e4198011728040d6683d5407004050040703410101c1e045900d84034042000e550b01d0070602e1055440420010302110039050951034001c03150001014041c4102c04003482a60201d0f0565001003a03042c0548070f41c0359440468002c0c4241800843c803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 811638291 1250 811637041 811637053
    0x30801030f1a0c2a0c091017100b19090e0111030415050903040503070902131d09010f050f01030212120a03061d070917100c0509120a2d05 61
    0x10303021042c007820594803d10310040c004406014070304401c110142c1c0c80c03505584400104030f103600c0d080d8401c5070320420a00203120155918210003000b80282d5420925a402922400270003c206200c1d1a03803101e401c5030b490000d040b06100d40f08000c0f0150090480b0241c544854004031002500403909145012038020341e68a014280b9040b05110f051400620724101300c042105060700105503030640d44000e0203090002d01c1c00a180c0000c0d070180e1400e031180d585051380003594035a4001d24203840c004480c20350005252000460742118440d55640a40500c0d20342413104000100020f203043da0b41c10745d000709446511081841c03074482240f00b900d00704503000810303041c2e00745c2c540c0110040742c0da42c00402c00580b60b40c000520244904682600c001200312070b0410030700c6118114411003120300000d0303494415141c001c01c02920303490000c000c04240f001400c50b110f42048050303140100d030300b00c01071b00d05c900c0d0070b0765003080008041c5400041000d260a1441701340000f42c3c1086201c50b884804c07155 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 811639541 1250 811638291 811638301
    0x5040e0705040302031606050f092e120501060e1002100e010c03060503030c0a0605040c031202030316020a0c0501050d0b0405090606120f0d0f05040e0906041509030801030f1a 77
    0x3682e106000490203805214814100c1e07403030001d42c00d03081d80c0080c0c503554101400c4840d882d03410340040f1070380d5034400a183e60800414015642900c010740045189501545040c10301030a1152200f046821040c0b41000421000b030b486030502000100071075050f040c5030404c01c0d080b0310b084082040003c541e0321304582046601815405075014102c0d0740c409100325030b603c84c20161a4042c080c0241400c1d080798041500040302540039a50241c440e10000d030019032a5200c0c600710180752480320001d41d100000f84110942c038400c0346031026000b032005190a07074040e6541c1c001070700c60f84121418410041022558440c541d0000d00f14004090410802d42c548105102eaa460701551098026400e509003140002d4001c645840c4152000008001c00d42144d20102c45041d0100158000c105041c000820340c080c0b800c80c0b450207003482800520407800e140c144510340c000c09100000107603203403040d02c6e0002908016071a04494004d0810380542d491804c0070300c00051340c41142c0e0468001c09017000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 811640791 1250 811639541 811639547
    0x60b03030d0906060b070b010b0901020f0f0304210305180112150e060111070308070f0b1612020406020d0c1104090818030a03050d0f0e011b022b050a05040e07 70
    0xb001003802a2424401c0b2036650071003110341d11904001400d4945088018800105000c0041905d0141881200c0721051040695401c01650f40074500e1203804c0024200480c1c00000c18541d03402580c070400000140782903501400901c81c0da104041d820107080301c00320075a8012070034111300002200050000b0384c0c038490000840201801610104074880e008180c0c1e55100303900c0c510800191b04004d205c042e0454980100e1600052000c17140c02440760001c04c0080c01030920140500780a07500700a0f40d803140c0b80040d000c020540c000f01a407d10502041200640c0015442c0c4058854141001c6800c050700b4070041c00d0524031406500542030078401d000300260440140741030300d80d2101155145544104268a07a8601070014001540a2181d000c48204540c041c2c2c101c581d121100003034641c1d20007400341c25500c036180000004004030a141110603018801c1400c205d00b000e0344480030701856801045050614035007241048001f24107240c020f8061000c44000d026402140b13582d52500302401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 811642041 1250 811640791 811640801
    0x90109090b090a020f0d05010906060f03140d09060e01050412320a030e041e020c010c1806051605190303061e0b09130204092315010309060b03030d 65
    0x125180e00d07410380041c207803080c04100301888a60007840d019042050700c0c200600700e9024002a50f095603a6407074080001c10911030003008195986803024001d1640c10501c0340a105801180340c99005034024141c0c8550000380c3d801543c081d810260240011140101c849002d650807049107102030710800000d110761021040e04642c55120544c4160a603078490014503903e0002d00001e0364002c4804000085c000e03034081d0030304030002d040010180141815640010900c4030007011071540007405c00202c4500b8014220110020b00b044240e213500b805c00300401d42d02c135224507010001c0108100c410202c4ca00356100c0d0b0750340c201f0300303c0342040c0400740030660f03540c030b241d0040703021070301c0e0181c00100040d40440c140100741e075050034200c0d000e14083c8160f0b070540c0403002c982d610603032110b10b900522a480c03010b4000342c02c054800060000400b1500c0c00d1850011185500c01c42c5400b0801521041d0041b00d02501003080c40d020440a42629040d8068501400c50a17414040400c2c040d101000030f5001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 811643291 1250 811642041 811642043
    0x706020f040329070318020316050901090b0a15050f0a170f150108100503030a21050f0c090402041511070902031b13030c0608040c0b0405060d0e0a0209010909 70
    0x801012070300540c003c070f90300c00d030014200041000c0640004003158006c0d8050400c40f25650325980800440303900007410039a20300c000e148080c0704048140550304125003a180500301e80c240800200c00c1e007000040c007841f540c0c845ca500340d520301b407800c0c83d0040c0b05109850100300b45000701602c0c0c010720b4001401807008080c01600c2d110000b000142c14078a0b1400a50003150318541c3c2d0181d52a2030001103d902c00001c0c41040d81d51004500041d107600d040005203160f2038180d9884510758140480d0400c1103181010020405040900b401041614000826008070240f04042e544184260228020740550f9206054443e40400f2142c0f0803504502015200c1450405541c215500ca85940e01240820341c0d5291420042440f100c104544640080c5001032141da1f10300ca11075940c1d5a00130b4070403c00d4104000003180c1c10148410042d0222040000e86183e41c10107040134140004290a402404100f92546882e4003811525403028030481c0c1e001a00940882201e40e11175010401424080d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 811644541 1250 811643291 811643303
    0xf020402030c0a1e0c0f0512040902090a140108370207060e070f18020c01021602011803050c0609060d09060b0f0103110313080f041e050303090a0e09030706020f0403 73
    0x84c0c203600e0701104103080809101181c5070005081c050762140c40c000517050704200c81c0b6110744000103007883e001e00081c0c401400e42e054050f0b6901540000e100d4401c0a0b580070050800e03045c960b21907a40c0e041014554454800d01d21035112564207001c0140c60002001003541101000b01d085008040076001061030902441c0c0900c148040c49440b61383e5806244260745000546034070501c082a0f040400b910340310301c800030260070800e10282c1c0d2403c80e400894000110352560002404550704a00307113a01c2d44024985034441c2c546107446a540b2400081001740c0320320800140315030640d4504055400394001c0c040104a0241940703801c10040030304529407846071407000115412903109001e0b0f12003d80700f02e070b030941c215192106410744181d0285401c41d00404148141405a0384040c00b0348007c14009020043c1000c1c0200c84c111001c0d0550412800ba40081040305803030780f00d03942003a08076100c1203030361304066071044007450450088003001010a40002900351000034528090419240108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 811645791 1250 811644541 811644557
    0x30412080406200c0f1210061703030714070c091401090506120a110105120c0a0f03020f03040f030e030a08120708060117040203011103040f05100c09030605040f020402030c0a 77
    0x820601c580f003079003040c03e81c6520805100c9190706003211500e543c03140140a25101c140e0201c005400c1000d40ca907101141d96403001c04000100c85801000d800a120002035450344c1040c80e0f000b407854071805198a800d80d000500b220400030071016400051440d10806c001e501e00640c09403c10010a10502c2480c3d401c01021030b8091038069000c3d643e0607a0f6000414454a0658510300381042103904203041c40000e00003a40806050382c130180c41107001c4825282c4c3c0742303108080a002e111851304a081003601c103000f00203480302c4ac0f108403a0819080f20420071180e080e07141c200c8250110055482e0140540542c41c002c214902c400341c10034442d1440340c10715607030f0f40340f400b12600d0004842203030014402248000003601400042e0382c0050000d400810900900f890350107182d48151707421101442e9056003282030160900c00c40004d412410014803401081c0d180080078100c0600014000e541e4580200301006540d600c0b41c3c0340641e010700250340702e1a00b01d040d49425000b030405100482c0040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 811647041 1250 811645791 811645817
    0x8060708090d0504062304271a0d0c030804060e040f0902010c03081b03190f0c050a2d030e15011a180d060b1509150c030412080406 58
    0x1c9160700342e826081c0e0360942042c0ca4800110f0758035a1400402c000398a10412030840e500100b4024400f0f040d03180f1024118251030f000611582180c201013800c69441c0c04541c450725856802549510b10341240c0c000c8000302d482c01c10f560344944540c0001e0501100182c00180140c000e4040640800100c42c20058458110f42900c241c611550000b170003d031200f0011400207005e01c1070b503900082c600007007900454000a0110580e441900e07908000e08104c0b0305c00404182d03601070910b0011440009110800a10030054490b00900c1e10303001c180444881d0070b00c40141b03640c10000721400014005100c40e580b00c40064010000c00010b281030b4081c0c403503042d0030302004403075250407920814017481c0f2001010185102c543c0060180480c4041e2441d002d43d0301e55510801072000b940a204001032482d02e000812184405030300707080d070f40032400340680b140581d42c141c20550702080e4000525070b9426880c490905500c04da0f001104203081034000c2c0014042020701070310541d041078682c443c0d0700c13181c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 811648291 1250 811647041 811647043
    0x15300712020705030a031503120806040e03090f040b0117010b0403030f3b0d0b06032103040f03020f03040f06020c0405041112030409060b07051506180618010806070809 74
    0x103100b00160641d40200300c0104218481d5100707038140800121030900880e125602c00c00766140491450001500320024021585002d10504040b066080d0096281074207020200e940e1515801d042c07445140d031003a81d403a40e81d0182400890410000e2289240783d81c554603021110b40086c08280c000615400c110713035001c2e004881021141401c0c040c1654000804061b402d0106504030b0744050403048111405800e468882d11120690b1252070200954681641450f05d0000480400d100f86025503205800d0385015504070f980103078015615401440f00340c01e00764505203100340d6100c20341c0b02c00130b80019484a006880e0050f03842607429288038041410420090b2201a540078060014000702001d452038034058540f807160b0b0780d2040d07030306090366000510110340d01a0701034904888000388034020040c040c010b44000000d40303d40c81160341800d030045217003465190440300c0d5484500c00415080d40c2ca01c0a002e0303580703070003075110754103580c403000c10741d4442000340e900501050855010509140c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 811649541 1250 811648291 811648297
    0xc03120302040518040c0b0a08150f1c14060103050604030908011a1207090f02040810020a2001090203030304080a020c0906100f090510090e0f061530071202 69
    0x80205009100e0410360804d0101110151045482c490301c04000940e54a003070018000744502ca403240100c07858981b40422074400d580043c1c5100f14501c00c03c00c1a00e83d60031038800d0881c581c0e900105040c04803854055002c007880c0800700c50510450b8000020058001501d91007148030b0395a1000403561401340500b81c50440c0440c8049034241d40030070017541401000359141581000032201c040d541c07044c403441120000308118402d01d8000400f4410002c4c20814202c03030780054141140347c03d5490303000034108000c040885a0a0368900c0307205e41414800d4010b401d0860300103041d25968146072810742c85541c0301c81600c502601549505078850701e07159601ca0b1240d64040d2240701d0b110180402191000700c03000510050181000b000706c0c00e52101000584600002d89800c0446404d00602443e1032000401c00b00c2c0400c1c00408004281e1181d41c032160705555448091034071103910f5803d080e074403018848088100148041c81c00812401d00c04514001c420607107411212120010000d0103070303c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 811650791 1250 811649541 811649549
    0x51c2009030c040902040b100908010e0c03030307050a1205010618120b0c0a0306080f010609060e010b0702010810032405070c05070302091e01090e01060f03150c14070c0312030204 79
    0x500441450b99040c20240c0110b240a0310080c40020b0320010100004c1d07900010a1040c000913030803120078030a6501c00d108106815117040010208148088000b030783c2d070712005259000300540420398400f59400340c403d1540c40158249c00340040e41c1c503240020240400c5a42155010000400024802d190000d030000401d800103034220322503907002a4510b941e84269044400c0585c0d403400002c1758281480890040350300c4000204600d4030b068038403010780d4240d4100c5400e096810004010002e00c0504640345a50b0a080c42402960b4840984a0000b003551014003101d0a101c080000721140c441589920100301c00e040100d9104c640c0c013151600c42801008105601058041c800f500d0002080d66000b02c290f02046c131203c0110201c544054000ea001024480d11403a8544030044280600c1700a0704811003260009850340d1910710a02440741141e5101c1c2c0c0d0b40703007015401140b041c0d01c984103508000c004240e50f410b00385090300404c130740d610080d01c000c40481d0182e60158800c5c000c5904131 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 811652041 1250 811650791 811650793
    0x20c07090b130608210f0c011a010f05031f051f030e01062702040b07050f070b09010804110409080a1d06090d0b130f0606050f03070303020303011203051c200903 71
    0x10200404425440011412030060717405000e00c41002000d4100d4001d000410b00c1200107d0003030142c000b5003091030141161103040c40b0301c1e080ba540780385a0090a499201c81007103607102d03a00040c00c04400810900350000740c1c0001d074920010070341400180100c403580d144c41d90b0030440300100c1e002c210f0889580380503ca0401401d0116034000c0c00c60030111100c5006455801460140d0320750f83c2e44925807205204a81d90340100d1542a1419010301082c0700070003414021502e0030351040002010458010b00041000340d400400007680c0d141c0b03610491100d40c0c001e83c5599150408200582200003910500120340081f903545411410402d0681c0c0c041c7c0400b40610b0700351000c669075603a072400d0040840c1c0c00000e40880920105540070b5a04440500034a8001400c90400e0305100340c2402c620300070b81c0603500c41c582c02c20000741e0000850741115002c40182c98014494030b0112041d114030050b0506400e54541d030311040d0f0800b81c1c0300d45010b115000b000c82c298805c05a1444a6029410383e940c0d00d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 811653291 1250 811652041 811652053
    0x210603060c07030909412212020304080705030a110f010224060103050f04150e0a0209010906060810080c0d02060c060709050f03010e06010315020c07090b130608 71
    0x40341118000c1c02d0880d100382071075400151070b11032500072501c486018888110a4000c0302032003030601c54041c501d2181200155808010110203a55580300190510000c90880c03008041e43c0d0b50198102c101481e8410001a012604540000c0d5642c0103405280c607640502d4030005404d240c0008d400001ca98814101000d1005620070803104c041c502c81030700e066004428140b003a01d10b5000c02000800000400d210040c01c0400c0014115280200b034031a12042d88002d000205210f00740e000742c1030029000c0480c4c8001c0e142c80c01070501355015402500304800100215000040b60070071810b076180b558400100781e82e40e881030300c44c8842520950711030740c103d00200b041c00d00300400d10010b00740c0058110791815881814040c076003501154440006040401705012a1070298220103020008800034446558400020b5444040610000348a24008144c5201c0b098680d01540d11000281c415a0300f4030f6036842c1070402a003501245548a1804080303d00c01402c600d105580c1614210002170070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 811654541 1250 811653291 811653301
    0x90603030c0b0721021903060b070f060f0c09140105090d140a08040e0f0708060f13090204180b010b030c0a0804020307050a260d020a080a09081221060306 68
    0x70b84420050038110810903007810f0510038904000c00200d2050343e00600683c0c2d448007114004060050800741c20801d810310b442005040b100805491806402140c000380c12000307460131000600c00c58400440050801176840130300ba03003080a100c103e50311042c0340030758000c0b8100110740368400c4c04482a4041440034100d804030700403180d0244002440011a000c103d55500c3e40c0c003507038000b5400303014080613100800039900c24901d02185c02103054100040e1900340303400050310710782c04144050701821a007580c802010405401030b2110300d4000d041040720b680e02c6644030130000d28881e0260743c100004000081c05000c0d1008803841004a10501c0341094400102250701c3e84c0050b0050b640340c8101d41c8081030310366600d0f1a6100521844180d400d07420564000c3c0300c072100c902c0f500c0a2182d0031044401d0301040d00030030902c980c03941c0540c0b2180c0c0c03106541c0741902c3c00c81140e00045030070303c02c22204882c00302d201001040b00e01d080800070303c070711000d01d0004120f40c0d204903000c41c1c0581244000c14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 811655791 1250 811654541 811654553
    0x7050a05150a03140412030f05060114160803010e01030b010806060102030d0911031e070504151406121005090903070309030311120f040302012d200f0d020601090603030c 75
    0x2250101040c603000c80c400d600300711007084066040c5d40560300f011480084888440d014404c1d610040100382003403103180740101c000b0b004140f91440d0310742500000500708940391220700c4081038490b40410704503101d503140c0d003004061142c240422285200000004a20100000f4040340b080310140c2c000c605c0c101c81c03944054054010407804031411a401c000141c0c00399410b000c0d12924444000003802c1d40300714411010b03e4848a580024021860a1624244c4c10020300c1d413a07080e61240e0940030f40030a10440030400500c620100940d9024044080c401c00c1400d0884c0071089a100300ca6031b450f103132100d10724541c480c0304400d0700402054004a0400003e0700a241031070f9240b507020152204556064a4884154040c1c0c6024403200c000040510440d80c020601040b0315180314034000503601c02d502d400130810175180b412402d000741c4150601c896201c1810a41c244100c0e81d090301c040d8000d0761740340e90350341002481c00c20250140100201e251849440f40714200c0b90540d881542002e0075444038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 811657041 1250 811655791 811655797
    0x1f111c02012711010c1218052706060403050703030f120618050702030904020a0c02030f030a1d0a090608010203061206160c0807051618020f0d0e0a061a0307050a0515 73
    0x44d06020b090542840462010000201120f1440e100d9050003000420f40c1360080546411041c800e01154500c0c002a035030f00300d40c1c1400215040710700e41940c2c50703800000d14140260342c0000c140d0312800d500132080507440340e041d02d03e030305c00c0c0e8640942e0b8074910400725040d41c2080c018254402c4010110140300300c040e41103140c204690340140c038640281507010406a1b44050103d0700411030b0000107504505007009881c900d01009000b441c104295100e009042d80d1155035244030442420300b01c180c440d598020f40100400740700c01d0030052680e550b12414041c0d002194418402c0300c4890a400b18248080ba00038851200c12807801c001c144072380740c1950702c0e50a040c4280d9000360300740001000108d04011001510b034400f44030240b40c03031808152401c014140d03982020040e0041c003148513911a000141c9541543c500c0000c035041c42e0aa0348280750504000c00036110504207410039181000080c6c2d10415201d0680a4414454071103052080c07003842441442c0e044030b84a0b15035102e9582680c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 811658291 1250 811657041 811657073
    0xc290f0702040f110c070e070c03210501090f0c09030213150b0a03020304300503060117010e010f050114040b0304050a1514010e04021f111c020127 65
    0xc900b06102c07400803c560500c4c1c03e84950140000e00c9203440b1008210140040020001d5201d43c2e2a040200034860f806c0c0a0004050145402124140a01e01c16440806600c900e904010a43e5645014809400308000b0359604030320b010052024984619080b01c140c0390044e000d91101503030036260300001c068007680d600d03110440400c0403503140240002030401c1a00c5a40c003503264102800c120403449a0410303884c0d0391100301c1035915003210580c00d02d0b8003288501c8c1003058480c0d81e4040141d480b82c013548441a4004811000031540b0b41c400907a5605a075072111042208075210307001502c651040301401c04412a0500c020803694202c07800031030f407003840b0b003094030001c4407641c1e210181d0114645010f51980c2d2240d01c402c8848010b03c10f170380c2c0100011566444241080c1d0003140c0412911543d401c4069207031911803881500070105a90715243d03003001c035840c40c038280b005100d8010f85022004c0065003412500350248144011706810a90a50507003151040203a42d45401d52040d064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 811659541 1250 811658291 811658299
    0xa0c030b101d060a0b03010f030204020304060e0105070f0212042403090b01060801031e03170a021e0d06060206280b100e0301050603190204020d15030c290f0702 71
    0x21000c03401c0d0400207020740c0d410706101c460401500b0590f0070400000100d401c0029241810300040200c1c4d900746c24124102ca0b01a04c00507620744850a184000c0d01d02d0b41e4500d65150b00b09030511202c43c0e405241151440029802d0766481d40100c41120654070a5214800a14070036021904200c0d1140300c1b003003105a61400c0008100d0340300e40e280b45285401741c0c84000803035030700d2004005103c5810030703401c07092074840190745482c02a1390b00074011076085054041d0032062100000c0c0401131650444083d054031790507203001a031248400075281d80c8030116001c20305041c4800069110700010f500c1340901d0090482000c68031640c075400f050034114055442c582601c1d1140b20b60982c8a1846070b0303011148540d0f80105c2500913000b41400e584018205d40d000b50310102c030752440c007103103040c5003a480c9604460140e41c45600740c200d00090b1000c600c554504c0380c8884c1c000002c11500107101e004640d8101c00010000c003100b2040c070b1480702d60141c4824429410404103050701c1e07000c4018070149100030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 811660791 1250 811659541 811659571
    0x1d100e1905180105041203150509070806010903080d020a02010e060112170f04260a050712170a0e01020724050c010e060a061802090a0909030504080d021e0a0c030b 72
    0x2c694203003036590580d8240c40d59140603001d0300c801e540c98040c10020304136291903840010301c1c00703000c17500f084001098031003080054800b0540ca0781c0300f00e000b81c0040d41c1008500d5101c11000481200030b45c4a40880d501561801090344030b04000400c001e8101e495081c0c0d506410502500c0f1802140015540d503e255803041194074114900107010b40054100c0c1004100e0301d4120300704911010744515045240f507808554010002440000ca560503120101c0078102c005500f4070b0110082d11111000b00807104000c1640090340381e00200341d42c4862401d9084803c141e5440144030507010200e00c030030180c4403404d204c20300c0340c40c003410040510480300703000003413507030090b030b507607505192081d103d499995817140d404210140f240621907000c0745055004600e40041d420006601c149284545244135031292440011325001d481910024450300d8103030752182103806c10080d2518100b041048131100c3c040c0c28100442d60014880b11400e60081042108504584034100004070050801380c0b140880307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 811662041 1250 811660791 811660831
    0x20d080f0c010c0f121e0b060405030f0d0e060705060a020310050405040c150207050303160507051309050d050906031f080a08070506070201090f1403041d100e1905 72
    0x910030318440d0643c0d5079410001c80000038000f041c1210401c00111094204824910030f01c003000c000c21440752040d0800900c001c8147c001c81c10034011540704a5143c0202440c40c040d042000c83d51490b200130598411491420f00c2c000c200b103078081d900000d001c5a000f42c0000c0c0a80d500742d8020f54004c00e41c0154402c071182c1e113000150903a07404407001c4511110384d4030100a4049200d110410f00d138054000b605895084c140071a940e80104080c500061043c0d034611400c3c40403d001c110040c00024240b690300402c1d5803200340107841440411206803180d1311aa1441c070f0320030802d44042c090010407140ca9615490301e646502d81c070511007180d2070701c8a690005481c0404120101001d0321aa624036103030801800c0060908100424480545e41030004410001e50840d41e0081c181d17500512001002d00640019481d5002d181c00004040074041d03171049580c427083c41814442d410b0024240040380e29a681c11085020507581e10084100c3c1030f10345200e104071504542c1d880a0f0301c1b298401c0030114 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 811663291 1250 811662041 811662043
    0x3f0827090106020d030506060430050609031b031603080901151d0108070b0307080702120301090609050a1a0d02010c0f080703200a0b0c0913061d04020d080f0c 70
    0x70b03403001c00580c1c03206211001040e01800703803550003402243c0c1d0300c0c101464503004400c412505000384802598860301490003442c400360140c001500b200032583e00e442d0800b81c030743d40d030f074400f456060b02e8014481410000040000403103180401c8901000d44c0b800c101d40c1c041d988400080c2c02c3da03205540710005925014580ea105400800c8003030001c41402d02000f40756442c014042e00907401c160070800342400314455502c100e035041003007483c001c24a6900c10f842207090440c001b291079a074590010000070300104941045d400e4881c4c444007000b080d00c84c01d9a000495007007280d030610040c03042204980794903052140c0608c050040c1085860b021250f03540711a1040785401c00c13103c045000c034038801495401038a504000b0406400300900070004e804c0781c2d85d5000c40e080001c041010080018100b50550380c145c07945424081c04500c1981e003080c4030721001d0720391802075100e010070f00b03d00c400846501d200141d02031500500200d011a060b919a0140d82d800f400708141e400d142008480c1741600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 811664541 1250 811663291 811663309
    0x409052208030118060b161e0803100b03101806051302190c05031804061205010f0b010309020f06030a090b041406070507020609193f0827 61
    0x710a45034a56030b581016505580e035804520a410054940007051000c51b0b0960100d541041585403090005c0001c0e1801e0041d034440360000303e0b40400d060080c1810004524091360056084882d40411315842d84440607a81c0000c85440c0404e00341440701304280c2600ea07800443e6040844404502d03542c0f60004540344200b00c6424401040e1300091103420440030074501c4030403010b14030f015804481d09480b8140c3d01d008030003140c012080c15000705182a9116800400100300701c030f0340140b42201608103980202405907440d5112410304282c42d16540c8a403042128080d07009006e0319114141c40180300c556080204203c04030b0b5aa0364181c00410190031945114510a140d426500a07400000c0350400707002502c1c00051010030b000a00050b0b0f100e02c1510503510b416075804007910701850741907080070a01d60009000d0b0102c2444000b8181070903594403c1c0c100b851103100780780f2040c0300510000c1e00c1c4030030026103400420b220765910807580310041038954100c44502c024100d284400903072070305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 811665791 1250 811664541 811664543
    0x30513081b0102070807030b0606130902030a0e011116052803320c070915140306090619020906270109030c05040b01030e010615080a090804090522 65
    0x16002030821900784451600081c00303100203101401410740740900c095510102030200502144003c0005211615400309030f41d02d60b0074400d0701c1401e080d0386214075402584107580c1d0000d45410030116034403010050003000c83d81d6407026103903803a01c0d1001c601400c545280c00000c5680d4041c0c2c4400795002c0c021b502051071f414080ba0040300b5881d0040c07030054503c074410030000c20040140644441000701c0e03a800e40c01da4500c0c620070035a84400303e02c0744604003616500700c2d0840d14988604c5070721114850100b60192022000105413120440e4209662228104da04947c290312147c0000e00f0441c8010070164507114640d805030030003010800044076500802c100740300100c1e07000042c2103040380b1000710007404602170809000b020b00b540ca9203000c00390f50380119030295444541d070f000d46911a91050005503101e000802c2203944a806082d801c81e24020b1001c0058070700000300d41c13005010b00c01d12400b00d621002c0d0500c4c1c40e01e802d20402c003900000b00241c1e24008085014440b80208444540c116 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 811667041 1250 811665791 811665793
    0x19031209050d17060d060f0b090a020d0b01030b0d1b08060708040b1312050903070e0c091008070207030308040807052b020a080405211005011505030412080403051308 73
    0x354500c84024250340b0f038420141d41c04640310040c450381d1744541d515010440c0c1c020201003001022030034128080d00c00c80d0102038009010008000c0030342503550143c1140c9211000138081100c82c4c00044040e180d403140003e51180f003400300c1034009a840f00da22202d01c00c2c112800454241d0301d45245040500464400021030400300c100000c001c4003000701a400300d0010b000c044501c000d52a04101104101500c07401e00c00c2c0001e0124082c0d504104840050000d00c20301000c4e032504081c040c419070043c542c0705004040029500b41558050b00e911840f800890b130041144916544040f41d06501c080c0c0b050b90140802c0000364040360303003030051011200300e01c09184600e05e2582780010f40d030b048082c500720864104a800800180f40001110101c450454699259503403965403824141c2c0c040c0030740c801c039102d0300b40c00c1d54110546803c8141211000040d400c0e440010f604c0c1074441c1d100456000340003800190300ea03c195400380c03c02540050003450020b08201c491b154401082c03195030030034222 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 811668291 1250 811667041 811667053
    0x100e07150c022b06051b0a112107060b0d1a1b09060414030c040c08041506031121030307020c0a0b0f040501120f0c0e040516021903120905 61
    0x82d410a00b00e041410080c0c80c000da80004032150400442246442c0001c1010341c50b4004136800c0001c030007440000b035000640c555540d0410500c040c14403034020004a40728082c09081c1541403440c5103075222041c0c01845014540001540c48000415015031401e90049680c05070320040f481100b0b01d000e80708400c405640c8141050003900068032a440810780c0342034010000303900903440303010070390301111010070000b0100d84805000a007400814684160410325103101d150f6103c0d4811200381c01a8015072028a860010441c083c0075a100740c080030b4224140802000a035040184090101c2041d460384092044860051507046900640e03c0f0300050b40010900d40c42d0745000c01c101c000030a09a4142ea1410110412440d20b80c020740c0b003154140035006131602da20050507081a1444101381ca820440e03403171341e62000743c141d10894500754020762801000404603900d142000c0c0129500350001c0803400702112900382850000c03070b01101009030620030506801c05034025041c0c0c0911413030140c40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 811669541 1250 811668291 811668293
    0xd030909020a11010e06010510051806030a051b0304170703020a0b041407080c090a11070609150501120f02101205010e0403030b0d0308150d12020a0201020c03030408100e07150c 78
    0x42541c1890344040a990400c00040050350758507000810719000303506040b610b612494039402f100031152012107410a43c000200003c0d08c1d00742e800302d4800c00840c940991107610682d060540e50008807002400740c201c02c52503501e0420140041c00050303100c0c1c81240c07100510380c0c2c1e0301d1400120030744044900350100f03105070b60080c2d41804400050308041c401040d680880c000064006400a800105035039903618403c2c2c0820071110454140c0da400c840305210100c41c0c2d00c0d2028041c002d03505d400f031090345017200203e07446050078041107060742c10240b4004c010b002c41c1c0800c00c04446c0044180140600e14803503240401d41401014024800600e020055107498140a0301b51148003c8061088104819000c002600708080d43d81100c80303582c1407481d000350071000c59039070f00000c80050301e00c00100300f024040550014264800c00c0c400c0c1c0c01d035142e0701075030824165a40a58010741d00503800000e21600c42c24929400b41320145c4995080700c246550b074103060720700520600d103100b00052194240c84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 811670791 1250 811669541 811669543
    0x80d030515061c0e010212040204050403031410050a0f0302060315040b100c060f050f07080405011e150e09071a07020607030f1404050a06050304060b190611030a020703020d030909020a11 82
    0xf4040300b0138031000398503100342070100706000c41001304003d215555820100703062500c2540b042d842c009602c550b44000c0d00b0304c02150252000103226191140c036109a02099409070301c04014112680540181d045840e00400c0c0000c03440164417281d001a80c0c1d00e50346416565950b0b0140d4200c1d80754031078421800d5941002000d03110f00c001800a4981030038144044a50340e52242035002c803840c81d214800b601c4600e00680500040c40b080743d100a11840401c441815a620446100c40e500d42403003005030b40c9154280d81180300701c65980c0140c000c1d41c800c101440c031400518a0808850300c0b90b601d44510b03540015a16044004194002500104500d81d903541100110300c209a01603182d6090500d0200041c003019014025030b0b08010002c004601000b000307030001d401840000380f120301107404061440003c003640e0701c80c100c0002c0d01c034144844d034241c0100480d03044000c10781c00351818a040d80c00303001803100c0101046081003d0030500040e00c4a03684050b0070050100d035241c00c40e8400b03186800d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 811672041 1250 811670791 811670801
    0xa02010f0c090512011107240902090106030b010c02130e100612030c1509113316061e0b010f09030605181c0f09080d030515061c 57
    0x300c80c19450414005840741d00820b00100711034049903c5424000c900c1a02405481c80201498002c900030480c0c02c200030480058401460800500d0900a2014086041691000d00010b50850711200040c0002c80c481d8000107580c54040c10400318540865011990714a02101d210304882d42e162032140a4000500c920301c142e0b900a00c080c0042818103200300341d00d110401c401030900003119081010807500380051307802c1d000c0d040030401079440e044c01c2c07184044075000c0000d0320804500040841c440401d26460014658402d62030303840141da45c0d04c13645e85a205111841208800110000015110740560080c403501400541c5514119400f4035003550340c4101520305015180c11001d056950110b4242c007103c2c0c0006021900352245d07075441c1d20359172409200002ca0b018086517080c508a4030086220711106035039442c0358442a0300c008681d8800c03140201d0702d41d50001035200090038860b4001c0ca0304130001511450003080c250001441d10751005e0351001c40103641805c0c0c0d184814862080d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 811673291 1250 811672041 811672061
    0x50706081608221a09060a060b041403120406020f0706080f2e0605030411100f1409040903020f010f0614010309050312040804080c0d030507150902150a0201 69
    0x281c038032681803010207040060300801c60410280b55000c4907102c21900c042e04604690403420300c8028224110288201407800c540c00710051061001217140c0302000c2c8503030310484082c8060642424144280c2c0402c10f425800c40540c107100311080c5441703c6048600600041c045500180501d1041020642c18042c0561001701400044001c1165010324034007002da200040c2c0319510040107804640440c040071291100000c100400c9003ca5400e411000079406035014005104000f1254020810307085415035a20f0002000c14400a4045000d100c0001c0c0756841c0d4074400b4100050399000c00d00710b8000365020b6006a2004c0130311101070901388201041001850024001f460030480641c0300000d2034a10703541059a1100b2075400d120003481519080410218640b11a090a003028038a90700700f405071f055640100154450580707402e82c03810800581c1030b10784a08003041903ca0038503542c005110342c0382c103e0300ca100050040c1c0c0c48000541c0c8001c410000981c549040c91002400c66a806074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 811674541 1250 811673291 811673311
    0xf0e03130801141602210418060321030e010f020417010501051e12060f070f08090a1401020702040c031b080c0316051b0a121b080a0e060705070608 65
    0x100c0d04203600001da070709074060444030310f1200714114510100e00d0030745910503810660246e1540f004050b29407030000d00403100031f80904078062845000c00401c0751010701c0010b0400044c100c0c4d40080c0062010b40d1b000d402c1b520f060004d010b02c2807400160a448440e10b43d20451680081c0a01500210403440d29031620b100300200401c7d1f040201207403c030158110070741c5001035185500001941c0340141e100710040d10b6000e07503000e414251034500c24000150799580c00700701100c034043d00140c41116404e00c52403c0b0401402d00d008079803240c02c0c1d42102c1c01c01d03d800b00d5400f0003004015840da4042d02e0507941040d640051000300c4503407044108110740c2000000c126131079007801012801b0609603500802c40404103090300001c160183e0710740c8030380366400641c0049000f80344410f101c041801c0203c2406000c0d00d49404000040c112040300060303c0405e22144103445070000b04a4401c0980035440d80d6081c0a06c2401c082000100150010f07a030498499002e050103100c03d56020800b42d0304904406 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 811675791 1250 811674541 811674551
    0xe071a07020a1a21040309050d1518060504030f0912020919021b0c0a06110d030902010e03070e100806252a0b15031f0f0e03130801 58
    0x5030000700b612509100b20845224040c0f9103180501440085802c045412441c1a9244a0a080410101800b15410340100d002080b002a403400d243c5001100f00758418107100304004e41655110040c041c0711505891040891002d1002030003a2046078019802030b150103500c3c0a00540081802070244c000074800c01d585074040e00141ca0740d143c403580240e4504809101070004611210003805500c081c408071400d851f24440c0c03540808503034040040010748105d5440c6445420581d181d20107013110007110b9011074075032802c4500c03d50107201c1e810710524150200003a00000a864021290825004041540f00740160560500d454400070700085014001c1c43c540000b40414480030028040c4075881c0140700e85109030710503d5103410080302d084407480340c008011181000c085881d42c044503480030000100b040307202003603d040b4800b1801002000c2510300714040900c400c80030780010740340b03640302d5039103001c5410a40100c2040306c11020003192030701b00402d54070003a0300144d402914164502 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 811677041 1250 811675791 811675793
    0x203010b12070e181816140415120201020715030c03200f18030d0f0e03070503070b0f12070216090b010e040b060c0a0602030612120307080601020307060e071a07 71
    0x30500d00c2c542c046405601318142e0b81d0441c866100f603800480d10205005003041c1420010b0401d0310b490542d2400f030107034888a4243c10500049480068119240203a2038804103c1d103442c0d058440c000354810b10544403400c0c0c2d02c541ca6258000d011034800086a240e10031041050723418451190988107450074000c4003102400444e500c0d00c43c021850003540000038407038004001d9030400c500080d002400700ca06d5000d000301e0003800c80022910000000b510010348401d00c0c83e00080d41e805072031008018000c03861419085030080c0d4812280c000c8958000d001003401c0141041001e072084009402614107150424541d08146000e508010300d41e070300d000a0001182d0f448030603000b94503030940e000210b010b8007200041c4a80600d8000056038490b228502c0100005034000d540125025100c0144510f0384100e4030303885d6071840c1318502062000b4400155101d01c02c2030856003112041c01074919200164643c8400e0700c521003540c0c9507951101c9000c00000a000c00c48401c0340c50f02d4142d00c1e080c2412 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 811678291 1250 811677041 811677049
    0xc020c10050310151b0c05040e06070e0103020a02010e0f061806010e06010e040e03270a1212140c01050106090b1602040b03010b060c0a0209010b13060c0f060203010b12070e 76
    0x481c0c040c013082c0600040c41655041d010b4842d148100741d4110900c82200c042c0d10f00316a82c05814003130640503d0421003564142940050703070714090041904c03202010a15600114000d402c5918510115134030f800b0610208001400407840e01f040d0080078104034500440d0700b400d400400129584035500c0b0400405c004428400b81580102c0c0034038041d007895844c1400980900410a114803541c00f0028080d2883d21000d260300028107100340f00c002c4210482c0d41001038102c0f0500c50805800d100c46020740020781042921424003985003404011125000d54400b01c0307802400303009856039503070401400116001222031009080200c0750320701c0c04400c003050a801d807010030700080c0120741720700780b50f44966002c0d000348840040c0036100030b480b0390300c0c00324199030340d142100d00742d0180040500118142d4501001c4881441daa151054001f900d0002c040b01e11320031694003070341c1d51008140003100217221400214000d14151a10b0f503110705044c401b000f14401c0141000081c0b0401207440b01031521 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 811679541 1250 811678291 811678321
    0x306040b011221021b0307080a06020906070b090327010905010f031d030a0801090b0d0b070e0d1a100e0703020a0908073807150f0c020c100503 63
    0x41c02c16038084020740c10714000011000c0e01001c1a002c0c105034031500c40f015400501210210366207921480350340b0540c03041c0b54039400e42d4000d1250b1a00400d0840e00458221b40042035006405804240b62840549808050540903104540280c100080180382101c100308048480c04100c3c4c1c040b0f140824840001e0032281d0030f0f00c5070030306201d1141041402103000345d2080802d410b0714142c00114003120300603c3d459501c81446034021880c98030001c07800400611481c0030500f809002d5480c2e00040741c42d150030290009042c0c07000c0162810241c0c210380c540c0852800000d00c211f111034105000c002f4183e90052008000108110047c1801c200100c1108a189c0d08281c640c00c2c0141c0e1071074001d130111540d005a40012189104603040084d420001d290358004420820b0309a10004c100308200300d0400019005043d07090000703200080c041107007003424410344d07668040002026200300382800c0c2507500d0704142001503000b502c18681d10b0f0410314040c80d4090320070300d083c0e85145000c10300609252 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 811680791 1250 811679541 811679549
    0xf0105040b011704080c071d151912210f030e0f0601031202010b10021506061c14010b0c0604140c03070b04062c0f0f04060303030203090c0306040b01 66
    0x1512440780d907078164000d410018240d094500c2145981c070b49070808803134980c881a40b0728181c0c407c5a000048203140000340f079205680100b00d0b08059150706520940041c824561564084800c000c10044011011049001012820884011a451800c0c0150300c0c65034405110001001c80d52030328101a4030006004240d006801c0026049003d550001d2820307103c001142054442c080001c001e100c0885051041d000d0140d009002e1010800240854460401d0351580540d002c0100420680d00702c000c0164001d001400003810008042c2c14010250392501031a44596505d0a01d5940140407408031409403c1c0c1603015441c0841c8200c0c1e680e83c490340244007a000030344005104002e44424800f51981090007021288002e4032020f80b8141d81d44680300c1d203400304540182c2000141d021040c80d62030f140b000c0341c04c108110a080c0030700084800e00c08065030711045000d14400f03560345500c076450185000303a03801038903071500440d403500d0410010401842544014100300008284540d42e40c152 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 811682041 1250 811680791 811680799
    0x50105070b0907050d0b09010e010e060103150f0507113309070e040c06090515030c0a03110c010b0f04020c070501050c0307120c111237030f080a050f0105 68
    0x142d41d900000a040203029000560b21485691100b018441e07110380b02d038092400c0d07900030455148080b15003030072108854039141e0300b60420401003003c201410f5404043c0d8045410100381003449000c5841100d43c1120101d010500201555181d1003080042052480039003581d01020390100010a4100c5010f41d50800f640000e940081c00001c01401141300030701500307407000e2080c201031800c0c0230703020b180d030007441e0000f6024a0f000a4a00d03220403420030900589403410700e1511082001c60442e4020407145042c16140c9103003103015078284008020240c80c090000842da00050100b00280301201c030f406101e54018480d0304407002002c1001c9084481c00d0a210750349a100c0840641180070303c13070026042d616103041030401c03140c0051285004521402034482d50b80c441408101e01d43c002d0b9088020250722001d540c0e002142d81104500006102d083e0062002c040f030320010302824401141100000d040402d110b4031290040b10f8103401110042c0103201c245064000b44100300014405d2500c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 811683291 1250 811682041 811682063
    0x5061f0b0c07050301020d021b06012102220f0e0a020f0d1b0e010315090506070806011107091d0a030f1209120201141e0112060608030d0501080d0302030105010507 72
    0x4000704111010042001500940d11900540140381c02034000d135840035000190144461a030090114106041c2c3d0117404440303421684011144203c1001000202d0300440300e8240c101805560781414020700030301810101d140303e5007900071410b89024201e0402640c1c4040b19001c0103070f540b580020102c60b0107079900c0018814134280820200544880b0000f50142c2c6100410b19225103886030703058034007e61280c5108110310540b541100c0a004000d4080d4001f000850140c078030800c8010b0b0032900500d005201c0c0100e40741000e00700041c5a2201c03407460b41d078102c1c2184142d44400c003801000308943c00382c01007103101e450280c161000040003a080050064682e1280034540e031141d0000c581004c41c078185401c2c010000b0b030080c072820044101c0380340c0160004030545d0800003030441030421030121100b02d07403034044071a00070408140100c40d207640b42c05000c286040304201500c04a600980013051552415520342e003460079084540f0308141c0100010b1001c0c0c1d807c84101c5e004103500c9811040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 811684541 1250 811683291 811683307
    0x10c0c0203100c090b071109100308031602030d110408060f0609011815030609050714030c01030b0d0f0f0b061f050a0e0a060c030e03031608030403030e0111040305061f0b 75
    0x500c0c1344c403070300002c482503404038015003800141010301b07140020940b40201180c03214650309003190014400280108030070000980d241c0724144c8030b0440711089004032030818003070010910940e09900b0b038486554002050401064004000305030300403154100c0f0049074100180031410080301400b07089640d071098003d1880c450500d42c040d16404a019100c00c090300d8691038040060a40101e007901c140c03180240c0030542d6840d0300c40d144801c040c010000d08407840002c0064018010622800b5880901c200d40304012074100200000c1d554414001c1030034400b42d515019200c83d03c00f4108501903c5044a030700708203001c1114406c10188141003c54803519100c400310b0300791441c00340e240c0c0c102c11a007400040c42a00400700300b01c1144a500c038011a401d0b80e034137150341c1e030041841c048040603e8012100c08955044d00841c0c21500030b1401180000c8134011640c2034400803507000300d0b0740c00006400c006201c8284502c40d004003050700345611003035036030302052442c00751b0b80a003141080340012200b0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 811685791 1250 811684541 811684547
    0x1a130c05030c1308030703111b0105041202030a0c08030913050910090f12080604060603020f030606030c0c010501270c0c11040603051506100f120f020706050f09010c0c0203100c 78
    0x60004c01c070b000c0460ba90382030a841c00070450070200d92003808a101da020b140d0280320541c0080c2c4008001a943e02d410103103401c258801004446405a070140510004003010500740c61910f03000d070031039000455960009070280043c2190442c030f42d00b40c103881c0c2402d112803c00b002c10316030f409101007000440c0d620310701d04002070020701080c0001c294080c00420403114035000070f010742c45520b08440400c4410740d105000e030705901c152211210000d40c01c10004107149003c1c00590b0300450303900307040f80c14944510a85403c42e07500380c102088003040411130000a01401215524600d040941880321039201c000262401e12006001464010800041640d940b039941c0020011030308141101d52480ca200441c02801c1002c0d203a81d40283c0401d04120042c034025007020948100683c1c4d001c0d0500c41c3d134101000149100e1801e20901c540800103900410018050203000300e50700414a4082e09150705441c0c01c46120782d02003414010800801d41c05641c01040340c003045001c1940218100c442e07000c0131 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 811687041 1250 811685791 811685827
    0xb0111060f040b01051801350c0405010504140403080c1c090212070810050901140a020d1d031b0102040e01081c092303101a130c05030c 60
    0x10105208440c200700d04003420040003800346006145008942e40c0340c0c1e013800203901c00002d10000164002c00100a903640c140b07140012085107044400605900c00a116060140c1c116400300d10340c032500d03091901d40f800b4820140100011a82000300749401e00a990b00030200801c0502848413500000b5002e801031340480e00d59080301c0904d4030058012298080042030310510513030154002400145e92080001030311000e483c41c4600070488520364003000806060300502c000601d54075140e1010410964801e5980074410343c1d140562240422107003e8101c4042001c3c20071030700d4045400da140c0544c08001c50f240c1c200042d4025032010300707011245000e071040e940410a108a401d0002070840e60102c1e1252a142d00c90000d0218102002001c86034064580955040350450707040461081d00e07543c6200303265600103002e50340061076009407041120135080550a0070312036a44001c0e454a0510000925814020010000514071240007480780c040100b440440075000910b0b075140000329000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 811688291 1250 811687041 811687067
    0x80d0e1b0d11060c0a051506300a060516031a1c021207050126130f0c0e061c0b0f180703240902030a0213020f0304060b010f210b01 58
    0x929036131031504658059684000641c25642400740005409880c061120f40c01d000d07032001007107281070b541d403220001840703240c00c62000640c00c030803828042801c40a011000c01c0c540150703000200c52811211072b1842d04a203070b481f0b00802d407415024690400003041c20122026040e1030041140000340c4c00c003004102d400001a600000c840c2400b0350381070340002c401068550a0741c3e408510420312112640d0200540101d00503042d0a00000c0c3c07002d903c402c11a820340d4000d072150403d600e566228002a81e4080d003104030180c1e803803c20040c442c03d00c0d07000c86110420540400740241070545400700041d001402c0c4405e1104410003090203901d00755410001105400c050b24200c0d5a171b80342c4481c0c0000d201c001049002c10340240031203007580610a0081c4c483d00540900700200140d8200b050360b102e103042e01c0c2d08041d03090060750410440c40020350b1045114490001d924a449d4002400f000361103100700d810004087c0302c002c076a041c080359001400b0f950a40118000c040c0da001a6150b90070803413 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 811689541 1250 811688291 811688299
    0x50d030e0c04020d090c0518010b0306010e090708100b070b010b031b0f09010e060708071104021308031b0f3313060501050621180a080d0e1b0d11 64
    0x24000302c80040e540c00900031901c111030701165261f0781d8090124200012a0700c2c00c8464a403001004607460318401275070300000501d080100e403183d020001c1ca1450056550f58001075055041001d81d2883e04034020107450071816040c1070a00c0d0740e69815100e0014000c12211050210126060440500c1070101103840c0c002c419403101c60220080c025500410411030001b00e901c84a02190304082084481083d04004000c3c42d0072416101c0d1944100c1c0f51400c980c0040c1d081000005146510140030b000d041880090740e41c400c000002c0a10200c0200e5104480e03810840c00c0c50040c0b003000982e0404c4840d0b01162a41509440c0c012004607104803400030007a078400c208001e401d110146030199813034440c1cbc4081009903200c4041c48114040d1401000522441c2620441e8200f07400048542c0403040b480e040341004140000641031a0502508503402c80740460f1650464006000304400b0305a004010208517914980da003c40500a107155401a050014413400303000c048145116610300141c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 811690647 1106 811689541 811689547
    0x6070207060c0c051e150405030c0a14010c06150e090f0114010512030c0a0f1203091205030a0f0e0d02010e01061409070c050a0303090b01080a050d030e0c0402 70
    0x40c0c10300405c0c40c0b19504c0c180081d540d040582070810f4407661220744440c80d020601d0314040d82d2500300d80c800e919009081c8842002c01044201d85a401d2916804104803820000001c005245840c400308106204c04500345c0342c4e07030341414095205041110b103482c040746801d0707003242d01d801c84058003210004010080743c45d0041a088100004c0c000342c0c1e282240c40c0300c1440c60301d421104111400040350484000340002c031040c9004081c444e003070034060552280c1e6500038000c0364074024414480003001045005540d5072202000e0105d4400410020b20941c0c03440360303910540640380c0015801c00504400d03c1b40e0600074501110722903503d0362111131281040101880b0014880c1c42006107074014440881c0040140002990290710f0008884c00541080052184140c001c0c0083e540002e00300c60001d0000104a81c001c0c00901c0c001944008003c00c0504102104180992080c004 = true := by decide +kernel

theorem cover : BRFrame.Cov 811510791 811690647 := by
  have h0 := BRFrame.cov_init 811510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 811510791 ≤ n) (h2 : n < 811690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
