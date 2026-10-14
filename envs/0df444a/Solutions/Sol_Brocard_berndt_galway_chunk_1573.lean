-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1573
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:43:26.994914+00:00
-- url     : https://prove2.me/submissions/c8092167-b6a7-48b5-bc09-4ea8f6458ea7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 282733812 ≤ n < 282913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 282735062 1250 282733812 282733819
    0x14060f071d030a030e01080708090c0d030302070605010f031403090f090a1d010204150c021c02130f0b0103110a0f030e0a021e15040608060d08190903061a030601050906 74
    0x3a41d207003070340c1c909000081d4054080d6491441c0b034801240050410300d00600454104105030080254800f004103c440342000b0403103000082e202e090500310040c1c080c00e007014061500e8400006044416200303440212031240c0300f00561041c0b4001c43e60345a0041c151a0b5400a03038102d645102458880c001a6004866140c0020700c040907030b10600c130144d249060264079070340c009024062b501004c040e0107040001440c1010692420b40c0c0410400081c1406c00511509030041c00d10442d0f0301d0400300480ca20740d007a010441d00c801c110700301c00940100301074140800d28114601000d58150f83c120740840c03c541e1141640484860b1301200144400d440c0c52020b80503030b50030762005035694450b00d03c0c1800d2180c20a94030f41210010080e10500040441401a10802003040306981012a00d80d000310202d9541c46100c0d03040c04c205102e4400c00910140b02001401c00c000e030b40750001210710035280075490410a0095140b07401d505810414040d680c5680140c00400c0b26182546501d54400e4001d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 282736312 1250 282735062 282735107
    0x2060f0a18061a01031503051c050f1c0507050403110f0a090f0f050609040203120904060b0a111e0a1106190809120301030c0501030f09081614060f07 66
    0x240c0720300c82107804440d60030401e450000c040720710545c0d050040d04002c4034242c2c020b9500a00d15580c4039074441c11580070b40b8050414802c071500183c051015603611050b008409a0b0f80c91848003840855612079901c8500305140c4404501050b1180040c1c40c01d6952082002410f280070a04010102100442d00f0340e0180510401003400c80882c02600402255510081031820918000c401510b0004000074041c00b102000c100140e41c0010b44441d103118005500e5541e0003c00010402a001c5900300300e560380d000007222107103164070100a000074448002a20700b003195240101d030083c400c070185001d8030f07440b404107100490407410010798019001010341c0d140c0143ca00c140d00c0030503034612162020984040821481c10024011110b4040001c0421440d540c110b50701e6461003010380c0a100d0401d95143d0700c41001070b02c2517109100c00c40c0c010b00d045440c1c0d041130340c1030201d50b104090100e03a000c0e003901250200301c0c0f000841d1401041c46070f40c131240c903079101102283e006006500003611207000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 282737562 1250 282736312 282736361
    0x50a08030a110f03041b0302190503121809040f0c03121e050901050c0709050915070305130609050f070b1801050f04090b0d0b0f161e110f03180a0602060f0a 69
    0x159041d00c0040f805214016a500c0e00d000201401d0133042e801600d9401000c21142c06003d41401c84092464402c8a5612a60300c49082c85203c000c600e50008000d66072030b103008414400002e0900e6042181a80c5924809040c030203aa00f52403080c51110340840c1052007181c50a600420192071013211b2001100c0c2a140d40e04070220555030207450500c0140c02c24409210506011141c581d482515400c0034003090820b030706e100489108490024106c03a60750440e800400030280701c140403000040040710905078940503071000c40e074842908208105d1000c140c012095005d40180c3d9030000341a01042c1c1000e192080403c06040d2003190258080e14000000c0001280300300090700075070b4140c1d82c2440324600720100710280700560110382d007401049940460305070b9242c4003021300d80d04a032a04079148c84d6841e00142c548200146171210600002c100c1340000e28542512608000342290700710091a40c0d58401d0b62120740c02d603204041a185440080c0e8102c2068001c2003030000c3d140185820f2104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 282738812 1250 282737562 282737569
    0x60c0b0c1b070b0c01051e0103150608100e0613020d0602030601030209060f04090f050112062004090e06130b0115021903030f2a120207050a08030a110f03041b0302 72
    0x759070000510f005001c01e1800712007509108a5510000000c800c00b0449103284c0680903500c01484000d24a1a41d01c00c10100303501a07400613070040c400c4d03000f2180216080303103180d00500310411050110384525000160000418900b07180c1070364001d0410030b110300c2e4903100c401c0a0b40c4000d040505041d0204100b80103601c5640050461180100c0320503182d41c00d0003211000c0e101b189124460680c00c11005000d03a01c0d003030a05801c80fa5000c440043e403000c1c00803002500c41101f0071044000c4601103000608684190800c0f0405034161040c0d0b02550f072580d0980311048800480078000b0603142c1c00500c105503802c1400b01003200240111100d50b0031446081d1166440014206c0c0025200c41e544020300fa03582c05662010400c5100200108520480c00c07800c0018006c070103030400130703407240c0301034500169411903402e80d80100545103000703880d082110300d5078016075003400c02c0e078541444400c04a040c28191550070781d580716101d1642d11507451f10301c207070f114002c4c0440700103108030400401a41e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 282740062 1250 282738812 282738823
    0x1003230c0a0c1a010e040606050a0f120c170a15020a020d141218100605031009020d14010518070302030c0607020117070207060e0a08030702040509070e04080702040501060c0b0c1b 79
    0x895202400c0340d5150030314083c1f003540c20940c00355016203480401486006100c44404060f038120441c1c1c2d0b50352101c0760910ae944030600350701014010340070130703103202d030101011602d0700406010701044c5030800f0303258410000302d02c00c0701c00c24401a08402c14a030029840f031a4600c00d10542c1386e03222070801105201402540c10251001203001001a1008201c0c100a0003c80d203003603048a400c1000ca031502000ca0b464a11421300c0d2007880d503954020404566a42d90123201207a00302009054100c0c0c040c2d4494021f09041d41c1000610b0381c60100c01800400c0003800f2810380380e018015046482d160024460b00760400e180807418030200180e0a102d00c02c0d50307229584100403942c010400b540c54124050081c20bd848036031030245661450074002000000101e6980c0d0b40d0503600000d10b55500d0404506000300c6410140c2c105003454280700500c0191405000c40c28021035007000303241da0300c060681740524504401000d1101103400a1081012030014060890711418592404905d1140d6242040c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 282741312 1250 282740062 282740069
    0x12090a120c0303060501020a0f030806120106080604174303021509010921180905042108040f0809151207030204081b01020109021003230c0a0c1a01 65
    0x1d4079072520350041c160300d40a00001002c003030029211074051600e504043c1d40200c140501489207400101d01e0540314220240b001a600308000c1105544074201c841c4c94090a80303041d1081c40c0806507a031404880c0400311800340714400d90384140c0a204072207604286030050152503541000c5c0a0f401c1c40040400b04000e242d81c469800b03800285180d5140102140c400b5101d445180e150545610000c1e04c154400491155a10702c0041c0c407088248085401e91020101e1fa84100348080700002c4503001038001c2e40c01248030301c186190700d1003226403550003c4020304c01d50001402d0400032401003084109240480d6000f24039107131a00051001007103040d01411202c640e440070000780d070300b00004000300d200d8218102e0710b0300b0b40c0b9180c5052500c0d0790758a01010161a20741300c9004403040c0d60300075403150a0300356002c2c08440d1080300c4400060000c090740e04038810302c020034141b25020b15011401251081c0c80204c05541000101c45e021503003030308120300032203141403200046101043d6080645008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 282742562 1250 282741312 282741317
    0x14010201060506430b040203030c010c12060503010b010519111902090f15010f050d0507030203011508090709150503030c06041a01030302060f0901020d0e160f030812090a12 76
    0x40c81c0c206044c481010020000d4000581c00700c0000421054240c81014040d5042458894244c580d800028218400c0b40e11900d600d41c40d004a0b002d500c2e8100f01f19142c20003000f9810480035690701c05160070b03112071591381800150100010606140d14024481b244510780c6002004807407040440c03850100e612600d442c600c82c60600d40d404501c2c1c50b10000381d00c01c2c00c0307803800455800d0254684800c2034051640c00c0c10300505041110710b41c6d11400946440d4440400244042d003401900a0000e42c0300b0b00034814284071f010318a0704454020072855010f2800c880003031148034500020100141940c1c29601000149034000042c5590b080014184880855000d000d060906145c001040c041e00c285541001c81010010408684c020400719400f080600c2484100e5884110f070700e00a1140441d0b0070003251038600c42c00b101d4030700054203101114980011040c003d80b00c842e0744204142901c8000c100d20b2080085650320b80f54002c515411200c010111040350f0560780e03480b00c00780014080c4000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 282743812 1250 282742562 282742597
    0xc0b0901090c060806030709060f06080603190b060f030a0c09200301080d23041203090918061a0618040b150711090f1503070b0a05030109061502030414010201060506 73
    0x81751400744010700040c841000101303c8146000c0304601295480e100f098140964140040c020740c030180800d1017805410441e050459445117030000384d1107401d41d00540114503441c020342250800040b150031035034001d08440d00151804640c4c0d030140550b88020b001c038140c00c07880942c8244031140698080d15600700948074158694000625089820844c03c00c43d0900000c074a860307141d21f05c100c50036123988290350140000c0ea410180da185005500040c0700342d250070300034101102c4180c440e4141502c510410300044108103a031960b044a0601d2082c7e100c40100003185c00c0455100320042c2105000e840840d050b998400000c003200c0000c4441034041c540000e11008101605004011042e01180c020300b81341042c29240d01c001000400540d803040503140d241d6165507040010308010004000c80c075603180050381000b4060b4100380310307070300c0603c3c2014004a4007003141407400d0701d0320120394002c604040c500b01401c042c891f4080d6185056541c0c556010420740c84401c0107059080c0c507038000c8007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 282745062 1250 282743812 282743821
    0x504140318030f01150b070c0b0414010f3f06060801031103060f241002030703180e1612110a0f030b13020c0c060d0b09010e070c0b0901090c0608 64
    0x50800101c0c100c00300c0d0a0340b5060305d12407514106540b1009803441c04035426141d122600c0c00702c443c51410b8204002403200802d00140c0e1403000e84600b21450b000307030703515030b174501c40d9001c180d071300c141c80b0311301900420080d2184e040b00c5008450200541030803171040c4414084001d21110494106802c0103000540741c1c001403042c02601e01c222400ca00064008081d18541842c0618000e0784c05029200d078604481008484000c035180407040a100003098610b0003105680040d640354041407003200861101002c0c2260294840040811a52001e820719015900c0812040350240700e003124406020b42003407214000b1310320340700f0a00240e490114550740c0e62250000038142d416004985000c0500b000701d004a01d0302c0e03000c814580310100401c0940c9440c00140c80c2801c101403070345469042440818295542007007600b0400c86c240c007d892000c4c8503600c4030a1a80003141c02c6609d000815804400e28000030820110b10b9801108080000740000890faa40c1040030103c0e40841c0002d0914000e11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 282746312 1250 282745062 282745069
    0x50402090d2907050301030c0e0910050c040f050f030304050f0612011509080102030615091219061103160f110613030306060c02030715020127060501050d020906040504140318 77
    0x841d0003e00c941400c509542c910390b01e01c07001880600400328400006404148032020030000c8200710b220319403060200d481d2101044000d07070441e115100ca004aa038000156a080c1004450600070018025519090400c030a0006071000030346020781010082004040c0f4070301036000c1c0c9000e400c07040705880c000010820b000b0030203501d641080c4032591042044c811540e03143d581e041020500c0394152621842d010307000440030ba5200c002800c2900401140c5100c00013070118186101d845500d0402500e9415640288507020840308540003401c6103401d0a40d0700c0c040d03040d403d024400c40c60b082a0b841c00510b4144c1c100b090564501c4541c483e010708020030141c02d40620381c0074040c1450200ea03813450540005c0d075503410710310030340355041421041c40f64120310070b42040014a407022002c00c001850342005070802d000320901510070030328040001c2058501109004241500180340165588565041000614024200300c40d020a0520103001c402400c3c000351942c140c03116000e003510103c0c1c0050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 282747562 1250 282746312 282746393
    0x50c0d0224090604120504152006010e01060c0c0b0703030504060615050405061c09050706020c0d020901090203070c0506100504060503070b030f07030b0a0b091e0a050402090d 77
    0x1d4206071182002044a0400300158142c3e010342c000002000d0904040002d440f181b1403a004404d000c9500d50903201c0d11900200111640b440c00884801c20201c1c0024481d210807003801080004101040100901ca1041041640d01401000d072107801640d11800b680303050703104007021808261140100014403043d417203800000c040300101d2080c01ca401240007040d40c4074a0160505c911004a18200c80c0d900d28070f54010000c02400301000f82520390b0070083e0f030f10702d12441684010707c26990204020304200c01c0d55a0b17483e50140500d002a401e043d5500007130340000b03142104022110302503002081c01000000e000e84c0b00204203174010303403c240901060300d19070340045001c0d070b120f80d000b00502c19010301125400046607016031003980350494128050301c048680d00e41d01c02c5042c4404149003203800700414207a8400c50300d080c050040310500c88400083d0200c001d42c0425030f00c0f410001828103400030070344030390000d0500b50282c10941e2401081c0316a000320300c00d180c0c1c80d15190803031100710f0400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 282748812 1250 282747562 282747613
    0x2a090c030906050906070801150201020d05040c0e160e0607031806050d0b0102010e0a0305091f210c0f0809030702120705010207050111030703261806060d05070b0307050c0d02 77
    0x174040600c3d14550141400d401845500281c0081c14514003130345200b036050f10701d04070010b0424070660400e410700c500d80700c00c0e9010f0841000041804035212104c0b0147e614144503854880c400f0707585c02e260410005422a01d0150148020280080d004513112a0f141c009481c0a40707505499103049103510048811408000303055a00d000404800e1402c006504d10803594076180055850305002e0100d900c00710140740540000c01d00c960301e54100d0360401035540c84007400502d6200405498041d041c292880d401c0030b003000ca1a08400903075000e00c125000c82c1c1c00120302c0e08403440e1450075804528144420302070070b51305400c14407061015682c1030004000500c1e003481c0c0003c101c02c070721015544030310a04400609012440400f10480c10549400c0fa001446200e44240749290545503d00000c60501100104e1f00a410001d0a41d2a10120195070590894000c0c00642d0070141c64228561000c1c019405000060203080503600042000c924554001d80c00b40042d1a8208005254070f100300301c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 282750062 1250 282748812 282748831
    0x21303030e0f06030420060d0524010807030903140a02010e0706030b0a15090b0c031b0304081b060c07030f03080106170403120b03030d1a06072a090c03090605 70
    0x140d0980d010307a00c0301c00b605e401513040407880f031701e030030000a950024606400110381c0010000c070b101260103920790f100e50300c50703000d810b915508051080641010034008200b035902085040000c90607140c0b2a40c414400c4510030304040d038085400b0254401180c020f0498200141c1d140c0754401d440d0b01d01400581d008185a00b0103000070248c00c0b0010303031601039078040c01c22840369526540301c5891061030b03104000d04c0c2d1094144c0ea03800c1901006900c8e540050900304002d074000310103000c0720710000120750444d00600040c014a04507110348407080720402541650000d000c0c00001c96600091060b0340c002c510890081103554a82d02c0c0260210b14140c0c040810320000c000a54000010210285e170300c1941840c0050080d01154a20070082c41040105034141c07001180180c12600c150340301104c4507800103055000c180601c01003141512602c000180550070407810343c003031035211201040c11881070194182c0d80344e44410958084582c00b46086e80041d440d414a01e05206052185075008002030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 282751312 1250 282750062 282750079
    0x41706070c03050706061208041d0601050a05130b0a030203310311010f09050d020c040902031b010c0501020a050a0f11060606031308071a0c0c1b0d06021303030e 71
    0x300c0025106100c034003005000d03c1030002d00c12080000130b170300c5075018016004214002a20505043c14150001e016030380075805c500c00081928140c04043c0e51140905968440c600150018200d40c6034210b041040c2a64556603004904001508090084507615960040e264500902d400865104c0100d410380c50003a1324603a0482007c081200304001900342c201183d0304c030607803600c003401003501ca420000c00b14503005041040044c085666402444254200d803244617004c0300f08011118030480080d030680c444e000200c19408803051a020004050501d03880880c1e00392225400d80c1e0202001d04005440010b1440d0407030303044650240c00b11203138a400030010200e038402541e9104098040ca1141001000060480c94040b10101c9815070201d2100e445003607602e060171015030003005034818903020f40000b40714541048140c903400d0031171038020000080009840c5001d0b0740a802c4640d0002d6011500d200411414001040003030054000d007625145541401402880403265440c07003138259 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 282752562 1250 282751312 282751321
    0x3060f250e0108100506030414061f090b0d1a0702070e04150f020409140402040b06030c032d130b0601050f0d05090a0c031505090c010c06050a061703041706 69
    0x1000071104120802c0c00c200c4040c0d1101665a0351504480d0302645d40000000104070420201d2007100c690100508111541794980a0342c42c113400021801c3c0803244034220070108a40c18094000c11010740019140c4011600c25031103204492414014849008900a05000d2940e030b042055000501104910b000d090515503181d000000104c10074100c2c05840c0c0c20724078084010303541118000c11980703104104018960010611003c42243e00364800e03450112416800d0501d03e04403841826200c0c010341c1b950740c9500d0000d1802c00d40901082240d11609040000240000c0c1c009000780b03024080003c0c3e030300c6e00d8a000c080d1010010700d014104842400b80e18103a445080503245104d180d4240403c1542d52480b08928102240201414942c4003103400001e000e1031130310760640080404410b00040d619004407558444d80d4100c0c20740011109200d800118026500980d084104c42d0404524240d031200c544601032120207484550341c2002808008012075482003600c10984c550141c0114680b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 282753812 1250 282752562 282752567
    0x90926031308070606081c090e0702030a0c030c081201090f0b09150d02090a0506150708160305070b1006020c040e071a040b040f09180c0302011d03060f25 68
    0x40008000300322a1000c0f440d0004c10a094200d032028104502c00c8603010b190798880021403505880058011460a48001c544403041d42d0001c1d2180e20950011490070841c10421074070041c2c80c50054003009507440810000a41c400c008011810501c10a00680d50501e0081303c125000b2401141e01140f4085c19804c1640b00c40e041c40c1e51058103518012003103100c2101184d081209034000941c040f051004108515566920250080c04c0c00da4008114080d1942d03814114499001c014010360005d100441540c981c01c4d0703401948905c00e180c02414200c541e0f549481008060740c004071b10076001103051142c550f041000c600d0441044405100345504031031102c3d181c298600480500d140e0087c4980d415003445000c890040092800a580d150f80d00c40300c2c03004065181c02498401802d06080080f42c8c48240c80c190402604061485050303803031503005503030800e00c400008070070700309010140d00e003550706108940c0300b04080002400c1e51310300703a04002c05440300e945250b00641c5244054902213a03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 282755062 1250 282753812 282753841
    0x305011505010509012a0501090b0103050d08010e0f070c06150311060f0409050405010b060c060601080f280f0603110f0d05030f03070504050a03080a17090c06070c09092603 76
    0x521481e21440112005107614026505d40c0024112350b08101103181044a18102281268000c6041d143d03c42c1000304200d402490a10038000032100600c041005ca800c02d400f030310781015a9090aa81c1100280c0d0340000f594031500d844d1100a02c16042002070241c070301c10030884a0b008864503480d001040c43c908500e80030707500860f180c407030382c5d08006402c0000950084040702c4000b4001c58a920030000303450350f00c1a0850b88a07000500301c00c0032079400365016502c5402201451407000440602d0100818801944201e00c400d0548603000c03690180c100d8825a000385010340c0d2561069203040b400d0100460b02220424015882159040c0100c0c4020044ea0f007040051003c1560f02e840d2034000b100c1130f003d60340000f43e200d07030304407030000c101704094004003507104181e10340d6000c0108031444241400012201d001407500500c6003803040d450039000070704a0a1040c00084072861b2602c0b003450840e03085140c00c0f6000041c00b184442c04000350601c61010000000d2128510f103414128481480c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 282756312 1250 282755062 282755087
    0x151203090b16030302210f040302010f23060a090501090b010201050c1207120207020a2c01240203070615050312031e0402121c110f03030f09070f030501150501050901 73
    0x50303400314a80c07640251010f80021b2494401059034400d05042d0680050200c0980d811001b56107030140c0d8100381041400b81c4200a42d40c07140400100c19059501c048042c80103001a030710843c856401309800e501481140d0103440d400100044442100001a08480c0054800403e0200502580300c07c5003400c9171203648a0594644103039906d9a010390381d8064060014001e5003c5185c820100b0f803030181c601c0610008000740000381180d036442117402c40040080c003074203090866003001540e005032010f02000c80d1041c13a10403a460040580c035410100d40b40769810030300400d8038076810846440c1c20401c0c10079134000403084902d07500b000741500c40ca220407400310200a8140c1d0700042d055540718138481c01010760a0050703c0d50b5a84d21501da01980c2c54003101c6101141e00f0021919020b000068a0481800000000c610710746070710250a01d032540081240c2d80350f00c03501d04041040c03c230034601c917001180705100100f014281c424402920380d4a50b0040c0e070420070113104480082c0e0344a10560510f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 282757562 1250 282756312 282756317
    0x80c0916051e090109060314060f03030c060103060b01110622020105040518010f14010c0611091009091406030a020d081905091003060b120901151203090b1603 70
    0x96030300302603515008180c1c062030422003800e04203100340200c000070301602200340d9410b4a529181c01058040360b41243c8000070889215001941e24102070002510f0b401c00103080301c0c20504903021461030003809804c202c801d2034407a81000c4040d600070362814840c5401c840074058514003000d0300103c40102c0ca07042d0f0003003204100c0500035640540d04940c043e00c1e000e00707986060321040c0818000c0020a02c22045294908140001c58203101200308600c5917050b580d030418007000e03844210261194a0012101420821402900c2c2d600c121482001c00c0c080d1b01e80f80e8440e441e2078646001c40e01d03040f043d21001500311040119540c3d0100c0c54805240d4121078080780030503581400d10840c0200821401e0345d41d2118030000714036030000060a0402411140c60314034600c0a0030803400d42c2d129101d04280301d181440710103888540b1302040d9600c6090400005101010554085106c030300b036030f004807205000c82014600349588160f0400c06000f51480c41481c1c482500000712040700d240001608 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 282758812 1250 282757562 282757591
    0x31b020a0e010b1206040b1e1f17090606011b14010c0c020a050a1208071703041202010e010b012705060c0f06070c031e03090209070f0306080c09 64
    0x11940c0d56041003010341040031800c1403540c1c40d1103101c0802e621051046008040c882c0014040f0726042c0036500c4095070280100c403480e02008042c8a6030785010701013680c4409400010021440000d10007844002603030780710038101e038051500401d50711000c3d00224041d0070003403c01143d40d130028242c541c000c01220040301c03029500c1c24000c040940480e180c0440b5400c4c88090012540c1c0203014444042c021242c0c4102c41766110204500e8404601c11503a0000c6440440000b06299801030400c1c5400f40078800601405148010002e41c41210f0458410032501001c03010281d0903c80c4080040010008100301c519900010b05000301305031200300c40d03050200c602e1000c03480465010004000280c13966495140244e0116100c08644000200301d10601002588940c4900201c107112905900c1d030000101d004041d01c0c442e41c4000742c03038505054440c052000182c4603004540d02c40c030380550b221003040309402c500030143d03040c070350001e54290300203550719100e544e0704050542c02410440d000c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 282760062 1250 282758812 282758867
    0x30a03080c190f170405060708040201090b0706150b031504020d02220305010c05030f0c16020303070c08121809040f0218070306090e0c092701020c060604020703 71
    0x70340e5446901119880401030040c02d0103401d801c80800e8444603850b0716808051a880d44c04140500c4046901810030b0340b0001c0454201c078080e12616403c5401854a0b00c5103540315101c841e86a07000043c100c0d042559591214484000078854502800046082e01c3c075600b800e600c24649690180081c030304c4ac5600052002d241103590307044a031600704a54010004840f074000342120b400003440305a40035400c14041c00799152191045034480d100c0054012040d80710b10000080326008901900c446040c844c1c042d8026940400291071000d03c00e942450003a0306100400382811403280041c801e000d010320108400c80e60450400091180c1650211740c10340d1141013204e41c2004840e800303500082c0340003000d100003101401c43c500c503500d10b403820f1102c2ca503540d800a0840d00880d141c001690003000d00407000b40740454035140c025404042c581555603503865072b100c100102e100f110f11aa980015100842401030000700e512040c00c503402c5043c4801074502034051070003030244050504d502c05141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 282761312 1250 282760062 282760081
    0x60e040f0b0a060804061107030801170a0c0e091e0a080f090a080a0c1a1b0f03031303080901112a0a060902400b030f0129030a0308 58
    0x291001c2000700404100c0e9a1000003921181040d01c00359034103402d1000e029003251911080742c000d55410703581d04915a01e09001c0c50307031050300c401010710b45008207003e54000c41c0c0348010400140001441c005541d003402403059242902e00ca40b40d01c4401ca20090f0100b40c00000b04101d00c481e0f4000740f6140d034881000180b5a180e10507140e0b40c560003400c50001081e11400046c0703001c085032281401c00361458a0300c6060901192000d00303818113040c204003602030844c214075891543e02c0000206c0d540e010400b00c110303056800c200c99002c807000034500c4403c02c2c964890083c603000764205000300070101401150b60098428070181c404401412450354219004030214515400a25801d0b00d5078444c26140c098058440c06100b6440b075110342202000c0c0010000390f80c800b072030080060200e0880002d80e0070100356040c01c940c904540da59a0002060744042c005840002d222900001c0d61003021800a001c403d10b811842096060111202d5119117000808000f80390705800c1000040d80d0712a601e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 282762562 1250 282761312 282761321
    0x9070203040b071e240e072304050106080603070b0c0a110303040e04240b030d030b01030b0904050109053003060609040f0f0c0f08010302090601021501140f0109060e040f 75
    0x20700c016024004c81d0740510000816001c024001100000c000c0c0140ca00c03010142c9103520020501c503044100200b008089040042d800301c00110388000c142440400050100c40c402d92010700426a100d007040b80d2440c00341322000142c6500c0030514200120020900d41c0d4142c043d000034280e50b1030b98a880000da03420001c1d0342c0242404141d0700d00514152034202c2d54054030f204115110b4052032180e110703055480c06201d00c522005401030000d1609954210041c03d05d5044403418142d5404690405031030303c030002c52080d40610000300320b080703161030002d203800101c245a1110204180c001c0c0c54071000180310114520b40c05c040c043d00da40381c4030002185485050402a0f02c2450050b85000d0b0f8410358008848511030075004001d0070341e030024180c0b4012000d0345070000184403034006100501d00b030754140350407147c180b0480b4009100280d003401e49050a8000490000038032111566920b00a089504c10000c2840e00d820384901c0e040c800792058045100f80e5120b940c6500800d115400151310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 282763812 1250 282762562 282762593
    0x10030b030607410a031a0109060203310e150306060603070c05031201030311070e280b04050403051801020c010f030209010309021009050913020f0105070510020a0e0f09070203040b07 80
    0x384070396401c0040c2c4e0260041018005480e20b4000d084217450703403980208411001c0380d02a4010318079081030304450000f6914181440150194100300c1c48120002c8105800040d0082000400640c144544c0c05503000030b521200e01d10030f03400074081061684410080c1d9811031198186a140c0b46618940710b0f08600a41c1c0c03840042c82d414000010915520500d001c0e2940407410560303040544880b030618084000b02c81d0705c40d2035130340c10100a00f82c860744041d80c0a2b403115802d00051200300000020181e96040e54107800185010650022000c01c1d8004020141024001000f8001c108000a4042400402004103160b40828040380c641d009800c140c40c41c0740e00401003202c00030882c1016000b1412406001d000f0360500001541e00c9c124200f0341d542081c0c0082c40480040340c08001103138603034009101225203005280d0b01c080c41140600103080882c42c02d844100c10340c01401c3c1130010880703a2200e0300e4412a41e00080c03100503600417003154141d80c0840805541e0b07844501302042c070202e0b0f805 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 282765062 1250 282763812 282763937
    0x20d0b070306052710210602070209150a06020d020606040509010e0d021b1e040c050717090913020918031c020301090e0d2a0210030b030607 62
    0xc1c103030074004100260410712032035a1421125645c46806100004503058051502502204085e40600c0c0786d00c4d070100c00d485482258013502c2d10301c0070760214402c22425201021076100e266826071081c42d18040305405440e0b1071004000700d908125000350b0b51a0042c0840e4060b540c0d810104190083c29041402e00d0310345201280d40c0c6080c42c1500035581c030074581d0096500c241000b5501d64030301d04904900b882c001c24160754092252100200002000c4c200d0200c41485420880c040005a03a00201201d0400301c2e4421601e40307607180103000440100070309840311411010417680c01070b0b58140080e60000412403840c043c4240c980380701440c0d44035511010184c0c071a80010440014465001103050354001c680c01d00c1800f880f0000c1035652084003410300003065a01203101c0010380140144015111205005910001190042400c001c0803030000e4002a440d4000154076080410201da00440c951400b280408a00c0b00e445010b01c0382d0600c030500c107041403c00500c1e25615007020105011128 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 282766312 1250 282765062 282765079
    0x804020d1e1211120409151208040e0604022a01110c060105030f03090d08030a0921230703120b0301150f050a21020a0e07030c0306090504020d0b07030605 68
    0x90400940d004001d80b07580002411200082c4242e07103002c5940c1002501c1001400e0405040151000183c0200751410110316407440c0c0001e0b20701e42e20b40c01e0410350341c010062291f03594142000a500140300a04e2035001e10300420804c03046460070034000000e01103040740b07444501884003015024102c103c070010020140414601c802c1e03500030855a040300c6080301255000c00c03543d160a9103034024000103e41c40801100c104022500c444000c0d9407203042c40b00005800090f036640c00e03024035842c10442400b03201001801d900c95070405600003200501c3c55071440b00000b40001002c40d80700e900e200804018412601d40ea070100150080d24184070000d00034441c1881d05613200e41c0201c00c9114a09008801707400014090419106000540d45001c0840114504040100c80c81c10444001240c01c444501000542002c2c0d1b00c66450049100d6039000c140140881002015550141c21030351143d80f600c81400300503075071100c0444031a64405001038072940c83d00c205500030640c50f403250740c005000c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 282767562 1250 282766312 282766373
    0x1e0e030313050301050a0515060705010e1006060206090f030406030e070b0403060504051b010912030e030607080105040b0406081b01090b0c0d1103090109050f0321041a03070804020d 80
    0x100c041d1801501c400b80c1c000c1090380d440d000250140c84050703c406180907000b8407820468149030313004201c0130b800340b400401c0b00602c01008030b191901c8000462091660b03040b00b0302806505100c19504400f00b02c004042d0058140c040c1522442540b26080902d0b9558601021801003031016000411f52500f000e0303119030780c074242600980030840f02140c2c81d000c0c1d2035400b0081d2000300049a15000b042e51128415401d02070105401c4610328400d505101100d51100129607041100da88a51100c5d5038101d1654900420700c416103e8402d07030603215a00b020303014010603200040e00e1800450306170983c034016020000583c1c0d480c00d29000740c4101d00300018058204000007806c1c80a4076402d658041168500312405034030f9020340c2c8000c60000c0d10643d000c108a240080c1c100d91003c100409a60400d01102d11080e850b01c0403032040401c0b120042020041d040602035840500710703c1d20301441c0745180503c07008000710303c002c00082c81200103107100c00501000c401005821410a00304c1044d5456 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 282768812 1250 282767562 282767587
    0x120d1101060b28050406210b030607020a030f02030c060a020f070c060f090b071211011d06060f040606232502090a0c0c03320309010c020105071e0e0303 67
    0x204401c440100c080d00428041280c0d100c2c4e4100c03004c413001c56903a0800481c107120f0011031909000418094136888541e94806540c05100150081c52150000c0569105901d005011130070131200c8a82590803d100d05400410046501a80030396842030069a80301d01458020090003104800f403c0b5489200000c908540c1009000c0c040d0540e945450342c14540d00c078030040300f81c803030658000e0140070642d10000302140036001561442c0346001c004100d40703c06405002c11200c0c82d100c1102c01e540004103200c2d02d030070010b101d4034801c40107680c248442d608080b03019203132007402c0510310b50640a80440182c6460304209a1300b00845210300c403080c038880c4061f4000c0d4911000380a038031881c03040d004215440c401c0d22448201420b0341d1113010107051551030540307800d900503004d034803040000c0d19200201d40002c1c5080f400408005030450f240e0070310001c46070850b0312716840e2a042d6854401440203580d00422042009600c14041d441050000300c0d0840d110000c01d84500c1c2c01d4407000c00e88198146 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 282770062 1250 282768812 282768847
    0x121b06040309080c06030c0405010f02010b280504090c060804030c0c15080a060812071a0a050103050f03070309140103200c0c040b09010603021b060103081206120d1101060b 76
    0x10b10f8402101c000840e11410011540b0040e203540125200801041143c0c0d40a008503803020780107070000140031000007000c90351090790684081007807418050300c0403542c0d00c503008880182500740c80800c200503c42e619081f8117081401204140301240c40050105403050401c4144181e02c460306500481d80c5425580c51400d051110001213118040024043c502030301c51401102d006400920407a070250022104940c0074017419540940398645e01c108031801d40284074010b84114000003042d61460074400d007456015000c03e10305400412550020a50007c3d18034142c2c3e0182151250f56481d000060700105030310f4071825402410b4150010b0a02c8a44019240000e150015101c1420170780301040200c032040400590b02180c0c40005001c080d2095001d001125140ca1842c109030401c10f1200c0c0c5400b601764421561200002108584c0508501440d5040b10003683c024541c04030302155691181c40d0111803500300300c0c113031000c0d519000c400d403c10340060016003605951880007485425180c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 282771312 1250 282770062 282770069
    0xb01270c02030304170715050711011107020f12070509070309060e0a020f06040608010b0f0f0301180f05040201080604090201050d0c050c0607090503100b06040e15040c11121b06040309 81
    0x3014aa1098175403162020304441289178080d408490000c00720281d4002070001800f8502000304205070088110000d01c20302c103201c1d5004000d540c5681091040003580000b1081c0700380500540140700101c1a40050740e0030544404039600030041d0b4400f40101c0041c400b5110207882c4606003074145c03d0030309010551001550003a105880d80c440c0c1c00d4203200d964483c80c803030000021100c400401c440303c201d401030044050302030015880d111500040e8001da030000e0308441051006451040000407441c800d000c0c610401400131300144c5003940010380142d070018180c40c0101d07160314440c0116841740080f294503450b148400c0000e003010312002484c540081015132658440c8101080030f05e40103810940481714010700074002601c2c0c188049005e084d0102400e6044001404007040b8003511000692241201000c00701000e001d01003004152580b844034181844031402c01d6940d0f840307010440200141c5945111503480e0000b26025154601035251850075020300010300c401c259004d04140200d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 282772562 1250 282771312 282771323
    0x3030b0a14040506010e03030702090c0c0601060915170f1302100e03010506030724030f060e150a0303022503060c0206091006050d0b09030c061510020a0b01270c02030304 75
    0x681d650f10040d1091011006c219505510a1041c0b00c01484c02c2d074507a9920854505150b03040004941c1d40300e00d011000e80102010900c83c40701400301c6200961400551405440c1220038a80800103a81056401500c0f0324018032100000602e2448001c2c03000300c140f540980420100982480010003034105400664801e50800001c0b03032652038005001d00c06c2e02c07607000da1070042c54040c00035090f5060500814009050311000d0304c000d52421441030700000c0c600d40d0300c0468940f40005644195a246842c2c0500c100300c03564080c401b09a00086609030f0664010110039406c12514400c0b02e45100765100400313050510094a0010340e0101c0d105000308502e0046500c540c24503d850301c15180c030303401441d801c41d500000403000706078a628aa030f00116800266484d01e1001e200c118101003007102e01140c0c01c9002204280035045c8855942240004d0f032010303000614580c0e440d01140030041c03203448820858007229030311317010500382e01425046004070f00300074000c610b0030041e46907081120191613 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 282773812 1250 282772562 282772571
    0x30a0b07020d0c051507170f1e1509090a060f06140607030f0f120e0618070605030402040f0b100305190c05070209270106150c050709050403030b0a1404 67
    0x42d1030340554031140c001c80d4014040c10b94500c03a2101c00004540c0206a0402c0115400440c05d01000981001340a800f511200e1030070781c80c3c013000d002c0d0349001c86000c80c455060707a43c0070050898076190f084c26100200303c895151a885d1200c46038075141020501500084c505102d0345004c0485a0141d0700f1122440c1c044180c1082d46800c01c612402906006404140e05071000300d0304503c00c1e02a00a0700a00341800351120882d00030750307402ca401900760f00f0825480a418401b40010a1040061503090f10005140f82030030004003c046000c00303030000303010b0b40d2a242c5a48074400250407080030300740083d0000d01c010f88031a40040280200b6201e0702c500b043d9480184102c848140100c8406100c151a21703854619154240902040000c01180b1413060540456040c04001d4111001da00c00310000810040c0c14284180e44640032803d8a4007441042e0360f00a0000e40042501003c035803100c40d0003c0c4c20303510b60405030064285400d0081e40100e9007d0003140700110490766202031081502c0810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 282775062 1250 282773812 282773833
    0xe01050615090a031b0e1305010b0603090c2202030c040f080106030c0b090a09060b0c15130305030403090b040f060e040902130b0a0b0a05070201170105010f0f020309030a0b0702 78
    0x103240c85000556900586103060034404140307043c0a4211500a10341d41c001786581e1442c1c01c0b1820107040c3c0380c4a064040d203400310010f102c42406406e903820804c1f540d1a140d42407101d07540c0c1c1d60301200302c8210b0040c04840c108002e941000b8000030303404805504103654910b02440c1d008040d50207400b51200406005101096031340301441080252503004841101e6a07080c0845074100d034219018240d4400503000005c501d0100600401c0010720084407030327945400301e1040c502e003400d0f04030f201010320302141c034100500101a00e0a84082c10b416040a44c2c1c0c1e500d5904048070700c00d0f1207130400b18101c0d82c0002d000900b520760070039180445041c0e544800b4280c3c038100400065409001c0c010750721451031409248805101c0e8002c0c0c1d074000e4010310211040e1355800c0c00350f07901d800510340800030403008151b150a5503000303051800080e4090500035a0303581020700107801e102010626200300440380304000781c514000c00465600c1e4000070200c4002195614006400e07205c200c6544005000f241d0120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 282776312 1250 282775062 282775099
    0x60809070f18111e25081602010c0f051606021603080c1f091b180b040b060304060501080d05040b0f0d02040e090307050601120f030e01020f010e010506 67
    0x2900766110359190210001c5000040030241c50010030030382c50f10008001e00c091003da00702e50f0400da042c0f01c0004c03076100c1250030911800e0fa07880f0885541c000e590314654400040b1044111450b9000032080c0b401c0d1a61140012078003220100402000040020902428841d0000c0d41d541c2c0010a14014886035481d61000c80e11003040688003181d10801900501c0000d6142000c2d2240d000b0400460300280c400c0d8013201a21420070380d08004140c4d4520015082c1711803040e810041910f0881d003084001e1400c0916a0316803a01083c910f4038590f10f1040300000d03621608480b80103400282606e40720b080900303003038005002c2841195018800c3c101d9004625000e031080e1422540c8039030703d243c1010400382ca071200c1c0e5403040000d8150260308101c0400c1030480e480a607030003000a04001e43d121103641c81c2072894100c0681013400c072003d40304040c0300080d45034004000016854503090321301000d0003005034540207040405010369405c041c3e20700c250303040c1513000601c2090704565200c402001c08464 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 282777562 1250 282776312 282776339
    0x42307111903020c010e0301020d180203010c050408071208070605040303020d0b0301200708041214101a040207020a05030619180206030403080c0f0406050405010305070314061002150106080907 85
    0x4000d40c01004e0a49011742c01081d6804045a026002501d00b218100401c8111607010344480e100340d4080a012b81941800d05c580703802c4007000e050440c074140c2048051580c40190b48162400b1401c0204008c04108a40c400d64880715841902889075040c14a0702a02a42110007501c04c00f51400c00116150324050040140d41c000e2030503160f038680c9034008520010f50100f9000e6a003103904002c001400140754403c219001d0240c41001c0c001009441c0756400c0c1030020700f10720001030800782c10a441018424155600013411580165120b5042c800300e40c404000e41d1006605008a0013041502c4481300c034401d0b50001e0910042012004900e0300b2184003e6525020b50000c00074000540000d0003106801d41180d40c4c00a85410b0a0061000140c2940b041e0012000601e000c00c3c01c01240d40c140c0a01500301199003810300100c2e030740403484c241e042001810180704003052440301d210702d4024420400082501c2845100b25a16904080c01e60300090341d0800007841065000522007840b0000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 282778812 1250 282777562 282777613
    0x2071a04140a060e011214090307140106050619030b0a0b300609071b120801050603130602030c07020a090b01020616050301030f020105091002060105010e01020a0c030204230711 78
    0x140c1d414007031408801146d480b034440e13500e0307040d1950350300f180541a240c2d640035a104840020041d41d1f06d50139450300041070141c02202c820140e0408005100b51382d02e000541700180e50101c0040102c44092078100c0291286910f8140c00c900ea0200c00704854204000800d0081c2c11042000014003404c0b0036014040500e000c00ca40500b80d0380f002c00d900c0e10740340e604079401c418545070150407402d0b038010416407601d609200f202c040050680d800150b54110790101d0040c94201e034454254500154074050f560101400180400e50020005119a10380000d442c404d680140a0803a02e0340c8a0324464020080c0d403603054054410f80c0c00213001103001c1c0488000007221603482a095900c3e655403a841020840000c130305005061010b542c9507251001b664042d40ea683d8002c00003940342c81d00240c5901c004100c00c504540240440304080754882040d02c04480c3c0c10b40340016121509018200c0d205902a0f640341c0054040090000c0694089100e020402046003030b84c072810000c08105e00c1b040c10404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 282780062 1250 282778812 282778817
    0x20d0b19060c26040801151211010c0501020c0102070606090b0f01050f1309140609070504060906050c0c0a03080309010b0d11090712050a150f0803160302071a04140a06 74
    0x40c1e858005103101030f01d16804400d000074103004440485401400d908a5040015140e44d6010b00300c4c1e1440080e14020f0013000d400c44460015005601c0b00d01002c00c0104800c1d05000e1906100000c00000754100e070340048104008540364401460443d01400d034501c9401f1b541814903000030712901c1c02d5460654806c0050b1501032030031191001169640d006444010300400c004000094040e02030b00823070b4007a40081e002c101961510408001102e50040d1810040000034807007400650340081101040d0707142800c080d80c654981c0c0c00458030f05000350901c0341d0400588a000000c100d020700143d0300903203056000780201d00c078960501103090ba801001402c0044240d00d03c2c4c00d03a0520040361604030006140032500c240d58500300e00103903a402c1c0c501d40d000986d1510040161815149200060944401c07400326261130210034680d6401442c2401c0300388031405085808050081006000411207400007508008009c03010360600d0708144190b5821101141d6410414130704202420155144c5d40c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 282781312 1250 282780062 282780077
    0x311010e0c13141314010c0e0607050f240708060f0402070f0c0f060306050303030f0a0e031905030604050703020a121a0a090203090f070e01060e04060306020d0b1906 73
    0x18400c000641c080882c40020590391986030b44800c8a9010040d4441e443c48000501c20507800d14044c25420340030000d11a0b640d15250034401e0059000c18111030440c03040354490b40f00d02e03603418071a092140c800c40508540c1f042c40481c00400c80201d181c203c508010441d26803103a4ad560b98143c0b1250b604070b4086622103e5001e40c6a950310301030f400b8105a034040c083d054bd54200360350f10003a204c4e42540107025107460512040040030351500070f0070040e0078190059411402c1196105a01c05806081820300700d44903100c1c1441c4280c2041581c01c90a00312412000c8184010f80c0a00640e10603200203005a0030000000d90880c000e00860381020007e9440941500c1340080400c02407040401c0400c0d603460340c3c2840101030340c3e02124400642211900160369081080703d0600d00002018440b4003030b00025001c02c0303045080580c160444405040148100300e801d00082d009117070f140c000900491021601e01001d40c10ba178062403481d0300c141c60039a180b4513021400003020011740308480005050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 282782562 1250 282781312 282781333
    0xb030604020703030f1d010b060423041e0911060a02100e030913060905060d080403152702090a05090d0c0804030605131b0f0909020d0c0807030311010e 67
    0x1607000b0810030b4040e290002c5e280c10b0082200040c3d5014000311060608980100320406200703104a0302e8003441261002c0c5080d18200240c071a6400010700000c0a0b0004111031700c0c1e43d26990007040b640d0500045e00c031000000c51401c180280358820098544000c452400801d13070819108451131244140c0081051802907540d190140c00f00000302d007240d01041c07225070496160900341000e1518105030100f262400c0684800450340001c0140c0d104095611000e004034200904950949030404482d051040e2100043c0014118104c003189400b504044419520f14040b00d80505040c402ca0390440191142c02d8906c0580b5401e07a000ca0013500a0b84200b049140a01c5085c000a485089940d007020740e42d0b22a001111412240c2810416443c403901e020001c0d5012540726001013241e8003408207052103058011a4a030f4001c0040042d501c0f43c0102c01e41da075000700341004560100038681c05a0701c64101d583c480141c1d11044010412411400300820410700500304241e821f40e005004c403818 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 282783812 1250 282782562 282782569
    0x41109011a030411060a02010e0c190b0a1404090603020f0102060606250c0306050115050f0a0503360f28020117131a07020a0620120702070602070b0306 67
    0x40a042243c00301e144e0429a1304580342c5a014054000017a0000100c01140c2d9441904040005e01003d00c1030310090a8031444003001c0008005540b1414004c1ea2100704140d41541c10a60200700644010000f1800091201c907d402107000d507032080d100c0c408006100001aa80c40c9020b442055002c5801c0c825000f00880c0030f0343c4200481d0301c209054840c240b6a40711207411440c6500180c82540c0c40e4030052100e0145050000007011403403529501d8a0800410381442d801001041310821200002254098802c01c2010b1810388002e0251005580c5030680214480a014855034003801280a4030360071480c0464148076101d031180c28400c81e042c00c1d404145c540491024200e050188002c2500c0501c49071180071841541901c0e0001c4c00c0060740e06202144c2001038541c07a644c050440700304044c0580c0460207414a079480381e0080750365112041440c40700c0d02c07200700c811400a800b241d4038442451050341c50740517148540070f844105480d1002207881c0d03203107801402416101000440c940f4103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 282785062 1250 282783812 282783817
    0xd060902093c0d080c06010602070e07050436060303080604060f141c1115030103050c090726040b0112120e0609180702010f0e0a080918070503041109011a 68
    0x203000342460f15565066503085125000117142000580c80a030042c002c4540400001c0003030074000442114034540600d00510394070540c0568445885d16402c08140d100c2c140d29011039004100102203d1064a107088500900c420b1201f64000340c01785010850908007031240c1c0042d01c510310006200c0c00d0800b6aa0023803c0b403070111598000c2254202401088482d5076885e03032480c03040c039810100d120b2080401c44802003010045101c00b4040004000244000490b010f9034942600d02c1c521658031841d0965400110b00114031020b03000641410030456010600380c45144261007120103649c031207000c2e00d00c8a20b200d900628660f00e13040644d442c1e03030060b40796440002c4002c08662070085504003082d00003000d40e0742c141c1d00008200500c59816028050340b0342040704114100090302c0440420b990310b4a020b10301a000140005061185440d40078005d5000f000a1494004900b091394004080c4c1d401101c0a50b860100c0f084020494074040d1281c504984405641d40f08005506851091a9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 282786312 1250 282785062 282785179
    0x7030e0a20090f1503120301090c0c0503041d09030702010813060b0301060308030106200c330a02070807080307020108060f0915010323070c03050d06090209 69
    0x31900c4048450715030701c0b039400c40e11502a210003400c140c10040e811801c00c1c4043c140d40c611a4001c18491108044c004044d02e046905d01e000108050b84500c10955400032484000381c0340e804001750210b410f00b650401c4a1104280e1940c1150b19514840030340e4490040d02002400a01e10030042440c045030031440625007130081c0c0b400114001c1000001c0c0c2100c01a0348100c40000c070100040002ca9004031440c40001d10380685800c0c04da41840d14640c0303500d41d084070548640200f47d0340ca94005202c00e000005032548085003c490a40900c0b520780a8221004010051181d0480814030880209880303040320115001103080191690041d5041c290003003a8540010300108042550f99490f010a809041c18040c00d101201700e21000400b80c940d00305000b0113140c4000940b110f2407000c24101030b80413040c2e15110f41350020b02d03d0201c41304d1003200d07072995401d4209040818190300c154020724072002c0850b400344062550321940c048000304000d0400701c214403001e492a41404039418421803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 282787562 1250 282786312 282786353
    0x80319050c030d0c030501090c0507050a0305161e0519211403151908031204111002100f181214070c05030708030405090c090f060a0201021207030e0a 66
    0x10500382041c203c044440c400480703000039464400412134030800c0d100340d114400b04c51800f20b103880d0b07060320b50940d1200c03240d900070f01700710001509840000b015440f2850030340d800080007030300901d01010201d01551040054aa50050801300703c003100070256000f02c140c0d8401912021900308001a016003150007201c4000d2107021082134681c801d07414001c43c0726001e10340000701d06100400c01e000100300b940c850079400000c1e49005004411001042d02e00c02110034003240c80361340e61442d0040800e144c0b064401e40000c441c0084030320719038000ca0242c04844911b5020800e0546c0e90b0128001d80e414442c0d0861002d401e1401032002c941b811b0390318000e2004505003850941c0004942c240658881d1038241c48807080c100060005190501c048401070903103c0c001e41c280390900002480d540701c0503010707a003c49070000d0341c1320094a40c055900358001000b460710391a440d082d14043d000c2c6d80204400c00f09203040300c0000da0854003900c00d110a00c11030030000c00301d9a100d5504c44e581e48603180e80706c004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 282788812 1250 282787562 282787567
    0x9050a060b1f0f09080721060213030b0a0b03010c08010308070c030c09020c1204032a0f060c050c010c121202090a091d01022502061905090a080319050c03 68
    0x12841400351000b0140e0060b6104598904003d40003424802035800c40729198010580030803500342e40c0200021008060340a4422481082c90500000c2c03140002d01c66555100002c00414003100351441446080c0f501c1d010b202c4004440101030882d0700c0c8008642c08145000010b001040c090303030250200506c1168030810481e120345800c000a0030550102c02074540000320515420b00510003c0b00160085038214240303402c6588007004101100c0894000c50010440c4e881800b04040c40c140007004041e42040b226519070500030500740c2c0001c01603503644503516680f07406512403040400910780282c1e46400d101b400a07021680201851031034000a5000e000304400c41d84d0384d0300400300508106c400050840080700110602c480482c5451070281d1040c025040c9a03210350054190742100040a00808151440042c41d01d003d8134841d842c002c201104200b00e0307241c0100091901843c100c4100c8070040d0341d2000207a492050001c2040359281c6600b4560140e4000d2000d051440b41c100103507070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 282790062 1250 282788812 282788839
    0x10c020301050a051009060308090d0c150804030e030c01020d080a060515030402090f010e070f09120c0e090d0e10020106030b0a0911011e0c020a0b0c0a020a05030109050a060b 77
    0xd09482d4103039004004503035641c0a0180d5030041030b01e00402008490418001103240d0744450142e4003030203080b54010203a030a20304d020000c41e0800350003d04105644070410390306090004142d07480c01c881c210007189020001d00e849203000070700c1032000c42c4168010200c000d0359034011215002d0180072084651780320003010401d91744071203030b980d181c1500550442d04c0345004c0c010402c4002c80138004c011144441d40043c440340785604441036200095080500c1c495408442c103e0b80507034103501001003a001c03020014200487c402c4500d044400740040c140c02d82c1c45040611361103105142c4424085600d0a50040a9040c81084030020740c40f07500000407020b07035944420081800888088001c26a111400c004026446024844000d020320305491039203505c05000079088108501002030110003025481195103403034106001c2d10501140540b81e18030302d0343c40c0d0755418502030101d205405210000c1740904051083c020f00755007140c020a0f0a1100e034a03010010510b807803545800c43c406540d40c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 282791312 1250 282790062 282790069
    0x3030b04020a120c111b0105040f0b0c010b0307080a0209041a0c13090b0105073f020f010506060403021302040b1309050f061e01020109020406031a010605030c03040b0402010c02 78
    0x2c0406003050f40361410643d140d2418001103401c01002c1d0001d210840342644030744603000422083c24044081e660810300912030040e106405aa484042d035070000100c0400e81c152108060111400400003d1041840310000c15848070068003a076100395005050400c09461721504164100e8042d450b0b2131020402185c0b03020000070200d07158211514002540c41c954000840140e00816203500200f01040301c950008055200313a550107010000500400c015111003144050070404030904010661a0403003014406089400b0301000075004030303840408a000180140e03440b8500c000d108910702030a40d420000d800c0480745214441d550300b84404209c003001d02d4010161401c0d4030001c03508451824441d4000c1e90002094240203812070024802e594440e0181200300c100580c402403c15910800104d005000800c8003950040c00e12030004140015020020245601130b416160a41e07200e00003030b1103521054a003c02c1641082000901049424074129049441458004102200713034000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 282792562 1250 282791312 282791317
    0x7030b0d021f1206030221031303050f0f1501060c030513140a1409062803060617030403030c1502040b070c0504180c0e07110f0106051c12030903030b0402 68
    0x8041601c03240d4052420110f4100f259010002d072039200c2400818210703400f280074020540008082403e04002450240005000380c072a00944499243c940e0769032810708075030f83c003410900020385002e041c00b0f2003283e038404a00b4040c0d0000300842012540d18040f000c661180c1e4441c019420040300b03200b40303200c030340316100007130000c0021a140d4176003941c0c08010032018402c01d5204924580324410581c40c584ca9070018650f01c890216620761802c3e0f00da0070010314014a4920030841d00c00c18140120230025194012402d68004030303420b24805010303002079940e038800c901001e4003207100d02d1242d900103081100110f00041c0317080d1015041950b80c4035607100e42d82000e40e0444042101c0710080c0324605240c814100065004034413022140c0c42c688801844040f81c2c050340074551154400a6141c60003a0901c0902c01d2442007158120345200b8650342c0200baa5000b0b80340301700301c99001001034036084140d0b1241c040e0041840c14428000750419030040101c4c0004909060b2502c03a0980c955695101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 282793812 1250 282792562 282792589
    0x204060b0a05091503040302060f060418050102030406050108280809040509010e010b01180504050907030f03050a0201050f04020618030f0f0d0806060f1b01020c01230601090b0307030b0d02 83
    0x44442c0c80740784007010050240858280135640c01000d00070840829400200c003a000940d00d049622903440d400c01040142113450000d006002c500e8105804001e0150300841c80303103000d0b00d030410203a605c0308242e40e10f40f4151002600e06559205d01d00c15000340c0c2101c440080c0788600070882c6444140c40100701500c0b002c503a6000c942c4d5403145400510301d002e00a10740007040919107488154410355846007070764554000e860146036600001076542108008880c09160400a4121031106178a001001980003601c43c3e001542070001140c0300d000c9290380c05024580c01017030b0900340302d01d076403610200041015510b40c0c14440e207501d500e0144000d010603510340c801e00c000780c03001e20304501c00a4001c5c40e0140c00c29000d0282008503098106010054a120042c410222010400d0030100a80640503201c1502c561354600220b07450711440811140100c241110100d01c0103980303030700041d00c0091031407140c0020700a003040000c1c042440399000e290103850040c00c144c1c04030002c0c0c0205014520490 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 282795062 1250 282793812 282793817
    0x1404140c0a08060d121d040626060c030c07020d02030111090a060c081902160620071202090402061308071401050a0c03030b01113a020a0807021c0b0411040204030b060d0204060b0a 79
    0x14122710760815040d05800398426900100182e0a0001c3d161280b4800204910004040460703d9001c5540c2d601c0c2da480d03140e80050003803090000302e2003d02e040e0303402250b600d80701d80284180040c2031801585003d104503004580a801c01c0c08400c101e5021542860b01e91046000c0c4c1541140c0c0c49070021038100182c4410364409100c110440f011051000b103040c1081000d50009004006030b03140c10760010801941503400c000d141d00d403031000c03036107500446181004491030712001150000c1d00081c0101295400908400b10040c5ca000642d00c80c450001040d0024800d10305403008a4002e0300b00b200011818900010484100003150b07003800ca88040000c1c1003030109505106281440c42e80b009204512001d101e024010004047e544051411008020301008605d01c4250755401d42c0d0002c00b0300102e405c80303082015520b0482540300c8122422a03411070815001e10b00c5061a02c262420341c2d600011074000e03902c90300308000c9040801c00049a01c5070b00e6100105181c201500036082d80407903038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 282796312 1250 282795062 282795089
    0xd02071109180d0309151109030f010207060c08010e041101020c0d0c0801140106020a03081003080c0c0a090b18090f01060f170303040c1404140c0a08060d121d0406 72
    0x40c98050400f0100302d484030825060514080100d070f0302503810030038924401000901044c00a9498078030717008900c000d5170705010f42900010511810340061a010340303d400104100c000b1041d0a440400080c010407002a0301c034000a40007500c44110203440c01c0301401100c00c00105080003c0d90440840001c64450b501c41d003080014100034000c1741e01610185000c82220741c14180c00070741d41c1d000c041c4003400b0099400041940b441d14100800003070f6030000350035980c81c20f010401595907250488403a00a68180000180030a014030894100c504003c01400d0f4540d070b2640050300c01000505150f10b14007c0c2c00d000d049180092080070028180520000401481d10803c0401c20880040041803a00b0810070403000a609540060544045e101c024218460f6030303010600034491059500070791a4000b0606c0540d48092000d000070ba1203035512106103584100500041d4007403200001c4c000340d24002c014110a01466201c2c804102b10160b00340b9902010001a0039100c0fa5440001e2000c0f09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 282797562 1250 282796312 282796351
    0x10909020307030e1905151f031a090d0518040605090a0504031403071b0f0204051807170d030504140d05040302120a20120304091a0306010305030d02071109 69
    0xa0006841182c011070402c8401403c40c6c440c0c41c0c0f200700c03c591341040b21804030002507130441c5000c030b4040c0d0728070307050744880366543c9a242c4003039110103040000c03070400b48000015004140018006d02040c80fa80e0720107007002503a020404c642d902450b08031750310940300d240c04034213502c402c00010710440c448080415281420705000d000003220742c40011074028208208254250428011180c20b205004101c402204500300300b681c040718914000e40c443d04102c24030030ac1800c00010410704040c0303241075441ca103940302c035031005d030700d0620780440c13415002401d10031180e44c043e80c495580b180c010001c54420003840c1c0030080c1481c065840b0f0f1004624003040500039401c040c6d202c400d9030408c074002000761409680f20240c0d045184003c4001884050000b40079036144e030314041605045000413661a25203821800c0c0244c1a00700315218400e1505444151919001503058102d0f41c0043c0503510300045034a801003c1c1d401013a00f40c1c2d041900b02c05030319680d19046603480c8504040c40c2d070411081316 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 282798812 1250 282797562 282797591
    0x11107060b0108070c030c0816050303040b01080c18150f06123709110a0321020102041a030907050a0303030203060114043f03020f06090114011401090902030703 71
    0x2002c0c28001c100040240054000303504100c1f40310000780c1084070b4546a2381111002c3c50b42c05001c400040041c00088140070801150800352030503138200c081a80d80d0390b601e06090040e0295000c113982c8190401030301040040e40c117a0700c0f4850141000d008020440d480f500403c140d540722444440780b4040304800c200200709031003840c0d4490316a4445400703c0091110b001c10b00244000303d8804015901c0241c1420400c01c568031100f20200a410b0400c0d60b40d9904008514503814020032080004660685440c03030b10602c220381c25949070140010000c3c9901d1000300003030b0001401d4820510a11801003129542d6a0a80300114403030380e070240e50307442c21000040010030110b20110850009210501200525551a03400c10b8108000303262036a401203252a9000c2c130f510b40340f0240c22541e200c0c001c14160302296055001d104a81298901e0300e400e102e15003203d580080e0b060b0110320803c014480c2d0750034002070750b01e0468149040b0300500e46070905181203030320603103402010a035a20b0b030b000104034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 282800062 1250 282798812 282798827
    0xf0a0b180102060705070212010b190801061a1213021e12010908040504111903061a0316110a120f031107050a0204090203030412060507030b0f030c010809011107060b01 74
    0xc0c4043e2480d8101301e40c0c00307000c41c018484006d2140141141d0202011000d43c03050407240c4008100c1030145041d4000b1105580450107405c50035400c0540200304000f00b003103003003a0060500344040c9040000c0302d8074080c900d005814000341c06001030785d800150b51204140e24647c040844030019051b640c00402c40003240180410f542641450504404030340c1000a032003c4650a650100355802c05c54040c03c42441a2124008809040035140300d5683e80b41d44140e040c3e5001d400c5d40040d41145103501c41c500d00003101c1c1341307203910710150545418038452240c0d82d1030b50b2660b10444034448150b0343d400e010701c01d800030740d04001800e4031180c0119aa03d07001d518204014059120b03c1c01d0220b071102501c610354040064044c980f102c407001d0464404208540041241c5600c0d240540d03054905500503010540e82c0f8030010b03092054070340300382c5403c0280d003214040003002040c1940440740151038000e402022030740d55540e47c000020060b20000014541c6d60f1007204001a81d40000f0000760000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 282801312 1250 282800062 282800107
    0xc04032a12020907050a02030705120702030c091302011d063c04210b04060209090109060b0d0f0e010603051c0806010906230f1902120d0504020f0a0b 66
    0x181d5203000100942c4400b0007641d0000554a4000d5844224080c2079155100d04000100103104100124130709100d00e030050008580300300c003582c2d501c070500b000b0890305440c1a2500c44c20031a01070703001d00c0150702451503480e05022400000201007140d8000030855000141011040caa0404040c2c45104800c0705c0c5c810300c0d00d062102641d2580401402014038000c030f0141c4050b82c01c00c20102e4400600042c41e200304990b1282d54203c95180504c5c105c0b006c0d40001203558040c1207c100082412140e80c0601c0c400c0e00c01041307110b402c10f00c0d8a402000038000251912480c41d50341c50180740003071020301500740034602039001041d104000005210040e0f5288140000f005101024007610303a0f4440f04200441c0c440c0d203044804405000030100d440c2c10041b003408040040090707031501694451024099000c2e000c8100c291111068000303a8031031009044810503002c2c100842107000c1d070250312841d007050000d402c0c00c40001d98100130501012040c1c01500b0303103046c0454000c1f41d1006030b00c03a10404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 282802562 1250 282801312 282801329
    0xf070303061d250c1b15050408060603070518070c0b100501140306010c081c020a03050402031501030c12050c0d081903090c0905190510060f020102041d0c04032a 71
    0x10f0b100184801030034150301d64001013400c00e240301d000c80c2d5018000101c0014200c01c40b4100a250580300d00a001581b1500c42c0c54210b001320000180305240c0890300104980d00900700c995040d4004208148130107000b801c403c28401c000c0c6040020a5032071060602c00c0d072000d07499202d564280030015140d405041c036041c448540c10010407101e03903031003102e2011603503000e051162227140d0b04141c07034240890145080c90325440072a85010303c42d8541c01a9014500a80559003104020120301901020901002c3e0650030f0522003007158542ca00081000180200155404002c9001c0059010080420283c919041c00308000c20704403281c008000703680080313003020401c0c901503641c0e2043c00ea20074480c601006a80700001401c103103c4003403422240e1a540c1c4100070900e00b0a00e800103818072400fa0000081c1d240b007040c1000e60051080754203441000040801140350b0b250440009400103200e030201113014000000095012100440401c2040c02d503003601e46510340e1800c981200301e5002000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 282803812 1250 282802562 282802621
    0x1b090902031b0c0a050f1c020a11010f090504052a040807140609041508011521020316031514010605070308091c030f060b0a050f070303061d 62
    0x103042904812860000741c918082d507071034080c59a01c4074145002c000004e0083e00614403a2446418042582004140645c4075070845000b550f0041f6555299204000c0c1780102c81010441e0643c046e8031100ca0816140c9070103800e994598000c182070f01d1007079610003140c0b400100c03035441c5031450200d00e0400d048c000040303038105403410807840c0da01d8105200b01d11501446a003d1503990311424110703440d60030040e0081c03221143c40080011031090710300c142800d65180c40c0c0c0d05031030303214911715403000c07265070384841d20001c41e050540400310300718684100d17403502c104201e00300703840396000164004600408030003115152404400095981c3c1c0100005280c0001c80103001c110781100075241d4058141c41c00c800e159880d08030380c600c0c064800c58403d91402035001908902c40e4550400400a030b500791040c03200f9aa10000701e0701070300030303e030b0040080313002845044081e901700c4002e024150701907d03001c1a40b96440b074900001c5030f2892500f52008000b042001844000503068060548400580c42c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 282805062 1250 282803812 282803821
    0x90714092706030a03090311010c0b07080702060a06050d02010e0604030c06020f0d05040e012105072c04020a0608040309050a121e0b060607060b03030a200a05030f0c101b09090203 79
    0x340080947c1c00b0052a0a0071350b810109540d00c0b076407200000603070224200b220f130304200e10050103188045070480010700c1004009001c168941c0241011104d0203405004203103455801521507100380c01c0305a0300283c080c880040407440a10341f68000308041d4000c2d20100070507056080c180203100c0480c00c03d101c4204401c00050b00c00344541411101113024842c1401542e103a03010418484901c054a0340c800d40001160500361000003d183c1034402c4103d100315210001e26100a00003214081d5000f143e01c082000a03a000e00c030140d501511034504182c1103038581c40000d0950405030800004603802d44990707820415010408a105c5100c50b40c9019000700d03682d513113003140c0c400522207402010042a0141000748982050302c2e9050000c0917681ca8010411000b010b22040c030545036104d10580e0b41850134100302043c0c05102a8204020b035140003806800384105911030210040c0c00d01c610003200080500e10700c6001d11059282030500580f40079180020081c40f40d503048082554410001e20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 282806312 1250 282805062 282805067
    0x8010516032301090c090e04050a06090503120f01030b0c03190209031f0509070b0f030c16050a06060e0a0e07121e11011d090714092706030a03 63
    0x50004420351a0100300d211031800b0305002d00507006141032640d00308400100d80070805401555005071640d40d140b405a540760740c07410141030b080da0058003036000080ca840c0803a030341ea04007051302802a8202d81c40e0100c0c15205071801070045480c2178192172044010300c200b14a102a403500260903180141c214104108102420301540c000b644400d0b03800141100192010b20204118050b00c0715040a1a15002d04800c003428048901c0d8903e0300842001003032004024058560001d9020040e508582d107030440c41440764041ca07a400d400b40011680c0c1c0c00000d00c1000b42c071525074030901005c03480d50b1070702c1c1119626040203403c10042d64201401c014020000080c9541161106001c541074040342e1300308074904104052542050000300c4c0740b90824003e11045e8100e1134082070341c8a290300307000c00030202e101d0000380901ca540240c501c0c001c1441140306080c4402410306c00c070245450503501100207810b0181886116141400c0c407668420508003008505902500642c0034102072140359400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 282807562 1250 282806312 282806341
    0xc030204062f011d0f0a03080a020f07021c03030507020712020d080c010518070b12010509060a0e07020708070e06060406140c070f0306053711070308090601080105 72
    0x259040302402c0c90959a0034505104a10290481c600200310003a41c0525541d14000c800c0034201d490300c950304070014800800a01c0384d80320740d010765401010380c40b01c6003250040c1d0300107551100300d00024010000035a032030583d8047c0c0300c0c8111101c00c5201074946009420303a5001084003040d904400401c10440701e11010147e425503049411610503500d40c07428140c28056026002055840d0030201b09030050040514581d208090044503105503940e0b01c5012984554000c03d036541600340d004001b54201041003540240340204020921611019191104001243e02c0d20041e8000c980401103507505000840c094041051480907030302d0b211000c103040d4400c81c4a0042000840549a03403030110010588101c0907070f5a041e244050340c1e41e0898a5003a41d01c2c08103441032031600d00811801100b4001a0340c40981080207504041c1c41a084014180e09006088004a407a40b4041c00c0c8518440c004112151080d2515216410080c1000f07144c41416008051141e01d00310602c550740050125 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 282808812 1250 282807562 282807587
    0x10503060d080403060606170c0a020703060f18060213080105060f0d0f1403041401050309072318010f1d220807031d060f031b040305150a0c03020406 66
    0x821401d021024078045a0038451a0f01c060241481c001010a0340b5a0225115a10000c0c0e807100841980310161034511904c03410200c940923034082c8908000041913900111440c55505000242000e01c4404e54980311812040844540e680042c00803402c03100c0740f2980303010380b40d00b20003000304ac980280410b03c4810001001407150344944001000c110f241a80780d00107590003408803103200080c3d282555250010300841d00841ca4180194445500c6041624816840308004080940c1b4050304131100300d00c00c0303d9462400400c1014904503440380b881d0b20b401d1410304450580c80758900300100150824a4005180070281d103414195800701c0c0391034180d00800384640307500e0041d21208610b0700240e60002c009104000120360803040c1138008a650300b0208180d8010000e00d032810f420050345210300f03043e400e402c0d48240081140b031114a00440e08400004070301d9464035031281c0f2264601402c4040710380401c0010010440011320500441c01e2400082c00d0039410700d800c00c100a480100e9048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 282810062 1250 282808812 282808819
    0x21626030403120c0b011202030d0309030306080d0512071b0803060a17030c01140106020709110c1203040c0506040b030f04050109120c1103070e0106050f0d050a06050108060d0201050306 82
    0x11400204051040310015544507100245255880c0400742004401d80016200c403814000005203a003c140100003a00d079004004e0a480513800030305400074030b44482c056041550785c2d1070100c0c0d403035020408054007850ba40c503015152200c0344039621070180000c0500c0d08100c001081c1c48004410140c0e10030b000c03540720070742a032255507481c00b142c1601c0c490381c080d060038440c501c020541400044014203c81106500a00c081d040c07100807101080d0080c841d840c0142c0c0300b00000c0005080b2a40180b0b4200b10050f8554941035a801026103800d403525282d41c80d401c80002800100001050684000d02059400904080c5031103507041c0366000040c200b1510120072400035042203003e5100f0096141d0000b05000daa00304824001c1801b040d0f01e10489100c0320210584986103000640d920844100f510412026804c0400480e81c83e0019115108002ca06104610402d807103400303001d03c01c1d8412400051a00d240c81c000500740eaa015190a008450943d00c450260740d2000840b6440201907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 282811312 1250 282810062 282810119
    0x10f0e060103120c02030a060207120e011e0e06030c04081005070f0c020f280e090307020d0305071a10050d2012010908040905090f0606010807050d02190216 69
    0x3c8600356440c010124009500d0f004d002103c030100030840c1c4c0a051582d000e0715243d101c4010201c0207031540c1c41000310050109034184034060010344102d995020104052504901d9000ea4202084540d003054800c5503072080042020711148904002845510000c82c00c02e10843c20404006496030481c040280104010802c00700207649130151b84a1449401030449039503c100000395040d03640b0200c00c0c584c40c500c034010002a403800a588503030300038142e54016518002680e0308000c010007a84400f10148007050180002059605040d8070034030222100c070103018074068121030780258450700f1003441b40140c0c50200d404030302c2d807054083c0340c0d01e920880c1010014014001460445103181c40403007540c03e0003903071010000c021001c0c00c00c0b40c00e090014800398640c1c4071480c0d01e68500d4074040c18540e1043c80050034540c402e40c0125005a124140149030452030443d4074141d9000c214a400440f21202582a000358100007a1096000c0c0760507064070a820b01c6400750325500c0c00922000300c929107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 282812562 1250 282811312 282811343
    0x121704030c0f080c0a050a02010f02011a240a0c060605120d0e1f0207050f0d0206190509060403030206061f0905060711030102040f1a0301030f1211060117010f0e060103 74
    0x441044070b44c2500c04001300c640709841d501e005a41c4e01005007080b40001c110a050851941c01402418902c004441d07a44441c6d810b40c03002d100c48400915070721070400103503240e00101070105800030f1441e0800355840c030807928900c2c00c0c0079043d03ca07580d20903401000150b403559400c078800310b2052040320300c074a070091183d2610400180307043c001c2c0b801d140215407a04400748900b80c000071080304542c41139501000c44046e8200300411040c00440c069080f0a04001c00c105100b03d65520800d00c1d6220b0506600b042002d201081480c0c005400440140c0e01120912500d4580042c803045801c40c1d800c2c410000c0505200000c00c1441d280c8039140c080c941c0800c8013010000707100c2c0c16400c1c00002038000c40d152030340d03105907640200c0344c4d02c50086044411454440c1d030040ca403003224180c035000890210086800c1e6240d50140b207500a5800410915080320320802c01c090002c14028884011110f4580207443e0595084842c61611100f4240c0707010588042c0d0103021138190304483d004041e460640f81d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 282813812 1250 282812562 282812573
    0x3040305131802120c0f040b0d06030f060b09160509010c02280e01090c09060e06120a0b102303091c08040c0801021303060b0d02060403121704030c0f 66
    0x480d040b20300c07240030290040740103085aa003e00081c6040050001c4107481c0c540c86a0072510800c1079403902100c04100a02020b10800d0040000e0f684c60000058030640d40d0700d840c0c0c01c00086070411154961180c62007020f500d03180f5845600401c002103041031454a004018102c2d100e44040c8a0500c00e20140305410b55841c50f030465003003113a803041031010b0110b4109000b04169140211401c142034140082001c030030350b02c111500850640c64580d0a2803c0c0301e42600d405815003d680c0d403154082104a1748038010b0b0040c0340c000c24500101203019404c80b8100704035080041100310030400c42000b0713080c000c1c0e0803001c000c1c081e43c15003110f680d480c2c98083e16075007004c03083c1c607265944074503102e051500c4680c171100d01403085010740030480003d5100c071b454500746d100340c202c01468a0920241400400c8441e44103240355140200032a003102c85a9005c00c4441d0020780c0203450712a80c50004048640d0002e22569079041d80c0c0004030800e1400b507401034800640920301411289040304124100f01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 282815062 1250 282813812 282813847
    0x906020c0d0b18060a0e1204060909150909050a110f090c03090316050d0f0c11091812040f0915061d1c060c030621050c061b0c030c0603040305 63
    0x41d000f2080d99483d141401c002c00252100b0b50b490001449a49031520700d407401d01c805c1da001da4044c0d6a945404a00e0502c0b40e402600244c89145030509460703200180488152080818203803080c00540a0300013030f4105004840d12420845001e08807442010155548511000e90300100540081d9260380300ca06c00c0901c2c5000360308465020041d440258070a000000800380c07502c032699038a5500301c42080a049138502c1410fa0003e001d108001c402034010b01e00036880583c01803a0b0014600c8084954203581e01d4030308130060650108100007018401041410240e001038a5950000d20480151300308020009509110385401c20040d0240301c0006041d900e1a00380a19006051800c501d4240c88000742914007074404942040c03901d2100c0790f00c18028080d400484000c00300522001c02c40c0c02c0d641070707039144c0000d040310240201501d10800d0345ea00c50107440c1180030341403d008210301c0e0100b80c80c07508000314030580c400d5000600c3d810813039481d00d044951065051030029200c0b03100031010f10503403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 282816312 1250 282815062 282815101
    0x12071d0604060c061104080f070603140a0b010c21020c040c020a240515030f0715050a020a0501021201170f0706050c0a0204320c07060504051e030a0906020c0d0b 71
    0x103080006c0008a8903400120003101c0e4501c0d40079a214150344480c00d50490340c03a08801c0d4034400352000004c4207001c080c4d02441074001c043c1000b6481c4c0740d50b40e8860183c0a43d03a00443c0072040c0e002c00751400c1c40e0303040111074840074080d2410440c400042d000a5030740e2282c018000e0030070783c10701059882600ca00301c4610320819140418080c5003880440407150300a5070080a00910071000180945100040c250086070207221b0014034505014208845c0781c0d11103071106040d44580101c580002d030007440100842c09101ca99815194180f03540c00c40c003080408030004d907a5105451004502e100130030b944003201d00b14100280c1e0380c200c0302d035814180020040d0207944546001882e0240c981c1c6a541118041c507168403485100f4880741c403100301804140d40c02c00329200140000b50001c1c91a0b40141c0c0c00a016100725000c1c111500f4000c0c46a0403100f411740c81981000c249500c20395000b1103604041c180390f0000d04180340008000c2814224100c1c4040c00d02c1d41c0d140e01080e0740380d0320f090796000d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 282817562 1250 282816312 282816341
    0xc030720062233090c14010309020307080106170f03040e0a0e060406091e08030408090f09070f0215070e040b1302070318050a0501211112071d0604060c06 68
    0x166070110fa026401d0842e1280c1000d09040141034601451140e100300004580d02260301908103081426203000d0003010b00381c00d4141a640e144000241e9020480350b0014200c1d10004a01a82028a059000202010a41d003641c0c082c0c607a401d041a804815141502d000d4008444183c0d42c001c00d00024290080707000a040c0030b1902840140a001d03008030404034060301800444040710f6500501200c000240900016014000309000a600300020115508000c00200c00c1f0b9890790001016410190f4140021a6441c01128120350b01481801c00e1440e800c150359880b0f1030b2040003d031814582d440200c0c032482da114182c1c441542c030031414411601543c0300031900c2d850301d898040e21174482038400130307100307188a000020751b444d0080d07200f0161801a5200500c46142c07240e40c0c000400c5802c000f0f603900d40c032019401100c1c025a005002501d80c1c0c180d4500c29810002c101800303500d4040088110003c008403501190340b03e5400310780407101d251134003405c8003456007802d50003401100c0080c1203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 282818812 1250 282817562 282817583
    0x403020607141e072607030f0c030e0918070902210106021905010908030c030a05060a0501080711150a06050109080102070b04020d020301020d050c0307200622 70
    0x141540000d4403031284005407507540d1801c4060300c4518450003544410782c0008044032103418007409100103085035074032030301018601141d515030071002450b4110310343c980300d0000b068020a041d40080110361981050038080050b1141e40c50050507400c03d15001802140d010010501c500c450145425990003484191040107171100100c10280d0300c031420418604048101141d80da40c0800b02940c100c0c0d900e82c008103280c4011044800300b40d21001420366003956101041004606071f80c0041d40b0512082c0e11156503440c01c21b2440c030440e41d0103002280900c00111007801103076042903145030010b801d410141c40c1c1100c440e034a00d103001c7c0314129218109046000b072240c031405682040c000d584090302c030340500c5071715210554201d00a400c4041c20540c80c920204002d03061004040480500150002d8504482c41500300c0907144143d85c20150a50004200304003658465030000940e081c04551006800042d28030581d41c02010784410018075010704520700e421040d40080030704640c007401508 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 282820062 1250 282818812 282818821
    0x403021c0306051305010b09010f050f0a02150a05040b15030a06060b070203010c021915020d090b010302040c03021810020f15010807060c030c0b060616050309041a1f090905 76
    0x700600080d100302400340c050400b8480c12018a8000c203416554480c0c07940d420100c4c0480110369039501d0030700390414050100251159040108000d01800032150020190710048903904940034100074441c004281c0307014240310020700c05585075a00446010300c5029a501d590780024184641d0398400ac00042c6002c40008030305400102500009000b20020081205180c0b07003640c0342c4413003204445140e162012024000340c1071048580803040c07201c00050500300607000030030441704260b200707503003105800004000710b02d81809042010004c92409500306005984080042030309e54205a03c036140f1502c46d4070045208209504040c00c08800f184d003004003220510515803005c2c02292081c0c01501004201c142c05045400e8403194107070b9840b541c9505a403500245060b024000b00d0744881d0400448440402c912180c10040f4058005184d03280700071000c200c215002c91140c9107000488803220b03003617541d03028112551101010507800350403c1044080f969002180c0155039a1441c220900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 282821312 1250 282820062 282820067
    0xe040f060e0f150703020406091502010615020109050709060b0a080402060702150c150601080403050304050f0d02010e0c090c09102c040c0e0a09021308070e0402090f0609010605030403021c 83
    0x220b4001c0350079403c0408075220034600320141c5c41180101c4000c03448801c020010045481000d040c02e54161000040c06504c0d441001c40281c003d03c03024005070f46803c40181840020b000390002040419001c0203254030b0002042418010700404900344000c001c006020354035414200c43d20183d006005d0e240c00d03c01c13001110569001b42c2c0c80300c03100d0f229440d40b001240d1020541d04d40107180584410660740c1e16503a040b10b59920007482245d007405081184000c401040210145400d4a80c00115a402400030310a18100b040f1042512811561041c020008401c00460703e51150684144544542c5040180c0f9200300074440c03680c018100fa0500300d190341399a02e0700c1d103e40780100d5040c020405641c1c0100d138141009003606134040d0440c842003003019070960051a003031100001c4600002d60341c2c038079542021240d60290201c003414004020440c501192801d51220310b8045400c0c050615002003407407500140038010521400201040c10b041c020401191542d40009111041c00c0d4441c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 282822562 1250 282821312 282821323
    0x20313120c0e100905040201020321070f0801140607021903030c02040509030c10020a1b0f0501060b030408040603021e13080c030307050c190b0325090e040f060e0f 72
    0x35250500c40d41d2010400448031610a8098000c0c040700c1c01d850390400f851400140710182040f410b5101c00c1201210011920514409a0700c00311451902032030b248002030404109100c1c4d0f04200282603006011001c8911440c03040c5110139242e2945039040c501c082020309440da441100100251007000081640c000d5a20310703018402d4030300740119106c1c128219503038050f0180c0410b107500402d038401a54507042d030260544070303d546042c40e000001200b0300074030103802400a94500e00100b401006210003402804000c01234400c1c0c1610798034107901c0e1006940294043d4104054000480c0310121018160403e1012150714840c0d41d5130100c1658024070100e00d00c959069402180c108414030315000c000c1e1110950880098440c528a0104100500400d8560821070311164607011880c8404a07000c0c51041499002402041010409200c070641e10a14150700b044105001802015080c05a00341c0081d80220145051486403400102130034a100036841284280c1c1e81151120400081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 282823812 1250 282822562 282822599
    0x302120108010608010c1d0121060b090306100312050c100f1a0406060c0803100312020a030201140c1804110a0903030909230a0f14060916080109020a020313 69
    0x130040d0220780341c07082d601001f00c801050b00c0312031010041056940110801000c02c41c2c15000c1c81e001c0300039040c1620465103541c01c0b501d11030001041e045514101008042d40103800100d10040d201e1030750f40da005a600c102101c0e0b00c00c10001191003072040608000c0100000c007518400d1003803105204840c0c000f440280c95200b040400c1503040340150070b04d0b00c509400d0700c40b01d607111507080e04503840e00b4007941d001a0800c0a0000003a0000010a40c074812044540f440d0354060020400c80382030013404d6900f41504000308030b030341000340b0414014001c12038940804000039080310038401e0001030000c1413110b4140404900000d004520254003603490415a40300f621581c044685402c0100103e401000d82c0e4085a00b21101400c1d85001c04201903a116803000c2001c50509202d208480640d17400240c0121604c00803800e0128074a08034402c0d550014039030031070301c240c2d9141d04c4000700104010300c6840750159002405582e124030070b00849040740c1024400302c8605a0300c641443c0c40354840302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 282825062 1250 282823812 282823829
    0xc0f0f0218060a060e01120203011d0f130b150d061d0c0d170f0408010b09060105030709030303110403021809060601020a08041a0741120a03021201080106 68
    0x107081400c41814080384502a040280400011605000c015a00c01000c00d074254107019044039400100d51040c0000c41c082c0c111003280120140404c100d51010502c068000d151112402c1d0800603000d1900500c0b814003074004507030200700d440f07001303801403800822204150082c8261807c02c041c03010b1508180d0303c0841c85400c51018410000c66507131260710181e44144c2c800008803060021034400c40c1c03044101c80070780e0006841d003010b20644072095403180d48a4802d03230351580d03804001460134403892a070243e400e080a500c0d41c40c181c9001010101d040c04010145070352031031078090511041e82520040c66020b170a20124030458050b0707011800d02160200703454450000020569480465110b172100d9101b04010f09260928034101140c03018140081c060388000d01012000c070b06a5006600840000b80b10704409084080b42c1070840000100c41412000031181115180c410015101c40380142e40d502c5d403038075030310001c504a010740300303501d60344144c841003200116000030190700481c01c803034038403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 282826312 1250 282825062 282825079
    0x60f02190e090a2f2203060f11070605090c0d150513020108010311270613150506030406090b040507060f091505070c0503032a010b030606060a0c0f0f02 67
    0xc94021007591140e64050a144410803158007481031004c001e00f240b81d46000c60182403031041c00010766140781c103d004101d5240340420420900200d03110300c1d02400c0c8140818420000d0f603d4080c1c0841c4116071005155540e180005080e01c4414401111402d00080c101d03042d62003541010b040c100940e914101c01c091610011461040d0140c0401c00302d04d6041e19201e102d6803039070b2a03011030a48070618164000d00076409903265100858214005200c4103000c1c44924140801440010f0781c0340700e036013000c161500e0314241d01d5840300041d0008481d0121a07803a940c3d03581c1d180000140014141c01040c0c41014014802001000708002050304d841c1d542c5c0460070603d2031030444200c0b00c58030440154204850116205600c140c00500217180141c8011030312a541e44082455a4080c21112900e040456102913001550601208251700c070f0b14028040d00c0c071517000203034403010017030030852007010001810340d4a40d0080d445012070350380003d00800f000c1d041c2e013811455111000012031156090307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 282827562 1250 282826312 282826321
    0x150a0e13050411121513032007050d020d0b0108010221040804090c0e10020c030106171b010908010e0c0103051e0601050c03040b22120f060f02190e09 66
    0x5124440c0b04a4000728000d10000502040c00041200055034105074021212030360b52911031030001c280540010030200c525076115003402000e482ca5040002c10030201c250780460450000034010091350740c111a1070000030b81c1c1c0c4c400204150820b00004103c40c200c00c0c00060061010b502502120302c00707400c0d15400b411449071441054408960041060030148002e01030300c0182d500c091020030f414200403605041c200d00044c25010f18201c842c0069001140344a003604080c0240d1005001004040404400032011030303446502c0ca01e02d4206442e60000078040c5a0b01ca4150074005007441002000b01c04030035002036481e64480728807103011070b0404022405400020b107803401144e1401c0b9a5000c40d441d440700440c1c40e035024410700003582c801400041030121640e40142340d020080300358000a41c203921082081d050b401c0d4080e444521740c0b4030b201801306010340301c0306095980c044400511000c110040340b00a00840074650364070303110440b00e0a8080d402174801c41c6c1d000401c13240200e082da038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 282828812 1250 282827562 282827599
    0x7080a02180112061523011107051e010201110409060603061a12040302030f1803100504051009061b020d030b0a060f03020c0106030f0c1706070518150a0e 68
    0xe210f00380b5201d4007190700001141c643c1e440b02810350030005d00984032640e144001989400801c031080700d20100b070490000903682200010301d10950600c00b502e070f80e520b0b14001490100358214401c081140e00c04140007503a100307601000e800d02070750900d1510340303484180e0000140a07602460f00881d14220010035203501201e0f010510703490600d942882d00c26044250925094080c0089095110903c907040311546c01c003002c0c1084400c1c000700414401d07203041c2058984140311000810700b07440d14040c000403950120340e0042c111440100403070704003240c0c50030344001e10b000c44181c1c0000c21900090030000b03501080d0045451042c0e9010b01020001d07000300416040e031481a01d0200e00460105d8035001c1c0203030054070b10440c03850000182540c0d80e0701e6501c403601501d0000c5032040310f054424040090301d805d00341c400c2d0a4a0006040514180304d014180f44500c0311050306155084a501e00c1a599200f00342c031a0a4041d03140507110000e81d0b001818401d0340c3c11000344200621340000c3c4900030b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 282830062 1250 282828812 282828859
    0x60804030f02030f0a03020c1509031c1404020d0c05031e060a1119050c030d02030f07022116060f0203060a050105091c022106060a12020f13060807080a02 68
    0xc0801c10510b01e017a44078202a4029449440300b06980d00450401c800310201c400082c5100e00d05060285070344810341300d441104d0960ba80c207101c101c58030340204c400402c2045521542d2050b41600c10a034071403841e0902d090040b40301d42c4000e9040c4907c440e030074540c4142c00c5841c07009001180456955444542c1b150043d44d11483e0440c2c8008003d12400c0311100035500a02010055800e0440c80c00494200d15410344c1d20094001010345e40010600054101113807009602005604c050540b09680c0da100303e100136510301c1180c00c201808187c01c000c210030b492121203110f42c81901003003031156000c3c061004c0e4000b107450070b00c40c038040000011154050340480b0102180103000b845243c2c80008103280002a83c1000da8022500d0303c0f00c0d10313030701c8504210000020034080c020601c5180885c00c01200e40020382007282c0c1000140b13400001a10340045062000300300b116040080703038486000740b00911507940034001070700c90714400003211100850a007120300d00aa0300f00c11700c122280f03118108031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 282831312 1250 282830062 282830077
    0x405090a031e0c0812010e180706140909040b060f101403180307032114151f050405040e01060602030318030d0f0e15160e04060b04060804030f0203 65
    0x11488030114008410b50542102406007a0400400880203512034400a800c10f40d16101c5412400005114044c0407240c0943c1c4100f90291491003001d520600e10744480d111721a5109120f8500070800410030382605950342e888000e0301c0c0300890b2a00f030426049565064400e41d001e04421302a00c0312505001d41414100c401c1c0742c132202c10301107010740a00d4840d44010aa007802403051883d8200c849010300041440f140280e03911448c09011148141020028401c030f1a0b000c0d02d0318030714050204610a05039030102e88140b103200c0027a552000305403054002c944a50a18540240e9284001d4214002d0010380384141d80c10050780444801c40c2d4201c0f860350041c1400f5a20600009a42000640035042080d50700c0007903d00342100c0703a04400c2a9203141c21215a01c1d40c80e1103400242c40401c20540f042154205405549030810f051071032901a2480c0741d88040100d4094074440d16100c40c0c002c41c3c000c0c02c803180c102e030359103648150040038008103407001c400113851000000c2e08984004203490782c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 282832562 1250 282831312 282831317
    0x260c031b0d23070501050108071a041410090302060c01020703080c0403020a12050109150c0f02010908090409080403020d0303091209080d0f030b10030e0c0103060b04030809010c05100b0405090a03 86
    0x8041c1100000b9080c410520300c0d402c00c040400c10100014002c2c01118000c00030f01c00146039260400d105c129442070403000d80d80789051305000400c5081e030000c00c0018003103010344403c0240d9a0341d04044484800e0f68201941244d800a80141030b00015030052003510702980c0c44240507180c0c04804505407003203200c041d50005155106010030b260012200d14214810310000503045140e07924050076407906480b8201d01d6640e0111810003903045881c888a1603600c1c4001c01180407299100300482c00740c40d80b43d0b4082d40e070303070181c010800c2207841c1182e000d590014409150b4141d00e240040140450010456004001000a60755039001d950a4400d40302c000000d0314151403c00c20403106017868a60312000c140e141c1c501c64a080c0c03100c18520800203c25074001c50520720712940d4038900407100d148581054600340d010000c0b00f4090b03040d9000d803035218402540d1402103100486004905444c00b40290080c03c0c0c0d000343e000d107658001c852120f0f06440600183c0d80d074101890311000303c190040d01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 282833812 1250 282832562 282832577
    0xf12070b04080f13090c0e0414150103090501051501231608070f1505010b0405030c0d0f12050309070b04051008060411041e1a0403260c031b0d 63
    0x202c0ca5000341501800039002c43c0d0a02074801e8916400c1a80341d03000d1141e40355182c00200d14682c0c090300020b01844141c0c1c0070f100c1c10581c410083d0081000400c607404090500003d80c50301da1090304141841c80c0c00034028012801c0c0800f0b05080c606400d0740e064082142e2229040c006a0306140701116541b82801880c2405251480c0c005100c084101c11030341c40c1d200b0465030ac00900d21030f01305400710340614088490084881e645d0303400c44034180c0208038940b2050004009558000424180d82c00d0107403020300c14251140b900c3c013061103031103000901d08888440082c10346680000654495184001142c0c004c0da6182004030080c4a81e009880c4c01c0f074040f020002d2042d000714640d42d0001c4000e480010b401343c5451a002c4c2d01d4000350408544000d0581c1190741c505001000c0c4800b528901c6d000e041a400800701c0001d684c40b452000600b040b6807102c0354000c240c005864400e20f070386001e9807241e44105d012446a100c0e0b111858003081844806a00703e814440000c24002a20090b10340e1070b0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 282835062 1250 282833812 282833821
    0x110304090504020402040506030405010c1116050d0501060308032e030f111212070b0907050a1a090d11040e0619021803010f0204060906020a0507140609040c020f12070b 74
    0x41c001c002c009981242d020000081c0b107407644401103103e50301441c0000303004600380e50005c0150582ca10880040c1e44004c0d45400c1141c40b4240e40011036400302c070901d40749245031500c6030140486a002412580d03000c0100009281c0301d02d401031683c0f55070b820050f0540003111160383d1060480c00060000c0036113a00c5400020320003144032115200042190085041c03c5422510705040074070404d203aa003020500004016055000503040403030b50018025460511012409080803446803140001c0710400811480303100004481c80380d400030305032500045c0c0070b042200021502c500c0e514061440c040c0c100302d031103601042080c01400c1a0642200202c1040c988101a4000504001c01a290180d40c5140c5517400d1140d4500400c1c01c0001581303561400c0b8010b082c000003a40048150340100b01d03400b0010710080303885800d42e4082441000300b1842c2001103015405500c8034603030003030315044c0b560940c42d0b00050400c0040b4100002c031240b015503200d0740c1059008071480204040500c0006c40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 282836312 1250 282835062 282835079
    0x60304080702030a12030e010203060f010c0f0b01060c0308010602010c020607210515040501050108010605070206160506091b0111070e06010c1e020114070b07111e030c01060501110304 81
    0x4540150140c44410704140c01d940020b0b041454650b4200c400c040e1070400103c1d0203805010340c41c49411410021819072800c0300128518000c11138400381000b407292002c40c01c00440d860840c3d800c0f90010214030b040d41c0c5501001d07140305800203003900411502000040c0f00c51050045d003855080c40d80c00307000c440e00e41c2c0200b5601040c1e042c2e082410a5240d8190071003036815441100c0c17141c4402c4250201c0580b212060008488040e0095810801d9520061105a1304082182c058a60686110740e54651642c0036005040351100c00805501504040c0701895800142440c031090301e080010b001180c0034030041d81d40e004640b00e0190140c000c1203040041c2c40c890942c2941c448011f0405c0b481c507000d2540c2e10718081800e04c0c1d138402c403612008500310035560f10940d09030804440b26021803900703030a611544000c40c8020802401c00040075030300c840c18103081c4000620704414851046031043c420000d582c8981020b03600f00801c0d86400800901584180c11500d480304100b00070f10314103802c0c921075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 282837562 1250 282836312 282836317
    0x9050c09060a150305010512060709031103011e090605011e06030e010e0d0f0f030902010e09041a0a0221010b1b030408030a0e09071106072a0623010b0906 68
    0x205910486407a03000404080c14a03143c50303200c929943c00101e542c1003004100721114410040188d0342c1c4220300300400c41e03800c04001800e82c0d42020300040d40782c00004c00640500610100200d546800b6882c01c02d01c1041e0380c028046280c420f1500340314a030b0b20b031000500011350f1020b1500a10855500030082d45009900414260f42e241d0008180139a20741c111900d0110020b00d0315000491003400a01604d80c4000350040d80b03520307031400303201c0042c15400003401204e4210340a8421101000070604108119800034481c0400307501e800010700e07101d852400290041c245a10090502c80303090310360010020f0025050b00c80c03d80e1420300304245181d0182c2d001e203410203140304612080001040155081000e008041c41a58469040c0d80014007841250383c4054501d0040c480035071410340c1d910002081c0c1651105891801800ca030301d6444c040011000c1842d9000e1301c40b107500011070f090028603007241c00d4403446182c0b000d4032822210740b1030404050174414240665030600c602c0480b442c01600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 282838812 1250 282837562 282837571
    0x5090304180b030f070f06090b0708090102011b1d0d05150417040905070f050309070611010b0a0b04050f0d03021b180906060310021e0a03060b0414011209050c09 71
    0x40001c0380941d400110340f0384402d032810041c1e90b920040e02004100b515100c401d0180c01289040008c50b0300d40821200b071360284001c020700405000c1641070740c9900c04d60200000b0201c0c00c2804182c2c0340344100161007a401c1c0b40042d884080074030b04101d040d04100961903034032648031000301200c2011941c010b00384403014000b1102c4c410514542846561007101400c007800c42950006054100020701a05500c2c10358254028068103008004a03420040350702c0e011034100c0d090880c134001c3c294075000e00508070040c10940c00f809141c40440c81e4020740d0090029200207454180c1000103180401c03002c2c0c1c81c40100100184d120b405c00d14580c02c0c0403c219240c100010780114961001c5022610305d95804890041c2d1030351040b01000300c03518040040b100c14100d9450114901101c0700001201d42d0703517210b9496202d0300d00280d0340740e6007403007a400340005084a00043c1c0d00c9548840d0944101c80011440d41d00090510070020006c4840e03204090040e0362000080c0900e040400034802030960040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 282840062 1250 282838812 282838859
    0x151103120619090b0315041a0a0b0a06030e0f161203021002220e0115211509050609010e0402010e010e040501090606081f06080a09080a05090f0405090304 68
    0x5490300240c1140d84110b10141403107010100d1030316401024546858100740b0a82046004031043c000030404c1d03c8460540440094000100c2e56214903501d00a45918421141c00140500e0005480c643c1948000c40000491066030000e103a5084019a55400c0d41040c07091842c00f014208848011910310981151290040d0350035a240300d001e030022030b0006010740010700c11015240c401d00d9141401035002e0b210341e81540b4034070750410111203800046000142d040c884031510324005400000e0854021494030401071281904907600101c3e024140d101d00c0380c1e11030914002c10410f141c1280340301c0c1602e10404c103003009656076800446600c0a2015480d0501000c14213404464aa82c01043d000e02040c41c1c000c12458a0030700010050b1a009107140840c01101265081e03054082640300c0803180d051034403200e10f49134820240002c00007504020152900003e048135011f0704000030300f141e094100d51011204120000b40030035188100d0b4140f4031f64004000910241100020001d101401c20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 282841312 1250 282840062 282840079
    0x10060902190c2901140102120d090203070e090a050d0203031605160f0b07090801020906090f211501050d0c0302210a0609020906010908070303081e0a05011511031206 73
    0x400c0810343d480c0300481015030f0b048000700500495240c441d04880045080c4000c0011031082c0c91285958080c500031500c0b07030b80e2508460400e65408010f03d401800c4690130711547c0d0304200b40090f541d0044850100d0741c5000d84031200540c40e0011044d00e00c00c01a00c8000541c20900300e03c102d5407544580d150f0003c1c1041181c04d20041000343d030204e43c84a01c640d84d94075017420811800340000360603a00010300d586c01045a0503107916058182e40760102d060b40d540c03010f21031503800913003500744001988418014a1200100d08040001d51049178044540310701030340c0c0d0302c8500340071002041d000e01130300905001d80104010700b4000c00200c554503c50066500c50503501c40c500d414418ad078801600d10781c0d01c4000362420340c0b5010180b00d0708003400342801e045251500c03079010b44892403480041e05115050300050f04802912500c40f40480c0b004500b500079162443c0100020f140c20302501283c07004c40d16500c22102d000d40103800d01e4800500c0250f04280d00c201548a41d160004c007181d8001125 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 282842562 1250 282841312 282841343
    0xe060c0a080d36030c080c031903060807030206190c050a120801050f01081803161b060c0b07030e2b0e060414240304080a03050915010905070e030f10060902190c 71
    0x40c40171b020002c140079006030409c0819500241a50300c203400c0031400d5000140208010b90307900d01200c418403124081d070a4010314003032050798000c040c0031018256016200c01c24040121014030310940351019242d010071a62035500340860301300071004860100c1d902d00e020604040101d60b0840007c02c601c000c8928100c1880e01034600d4901c6040200d0782402000b2521144a0f08405408090b0150b4940446040b08607220202a4540a0300380c030141540c85544028500c020320503660b80b801c0b03180d05203e403d4000e2100181038090108034078009000308160300c4076031030314500316021206080d00300501510321a003000b0045903800211091003c2d180443c44100f1138100185200c0ca0103021802d80b94400203201038241d400040c40f03400d00750407880c00516806292090b4505503018034400107241ea0b41c400d8143c40c600c50760f41c0d42560601c40c100c4046e00b84d60000508441b031040503001404695a100c0d0f01c24180c0c0a5112908214840c16001c103000b075120740d6240c91240c2c01814656407001d071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 282843812 1250 282842562 282842587
    0x5010f12082802030a080a15060503040c050a23010305090c1009090905010606120e060703090839190212030418050a0c020606010e060c0a080d36030c08 67
    0x200c09050001d1380004c1941802c09030000543d80d4400340304038051107284038100050740d14141d5070081d602808800300100c0c2c00e10000c0f00c40035001c0c180241c20388074030300d858022a501116000c8040c585000d2a58406074840d4820700036580156002da0040154400f81700822000c04042110041085050b01c8002032441003809054403071801071000213051410480d004154a07680b84e080004103060480143c4c0c011000548180d000800746800107501e40b0300e1409503080d206090a1030550030025240b0301c0c40c00d136220403004240c281c84d0415800a040091126240c030010b03001155031071007114011001d420b001c488184054400c10583c0d25054481d090b003100c040300101121111070303541080150141461080305401e80315400181683e16140c80028040c950683c40680a05030224030091119010086030890592002c421a1503182058207400240184030540341100701c00180305525a1144caa140c100e010040030840404005480558001040e20400c5030a007104100f906039800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 282845062 1250 282843812 282843877
    0xa0605151318050a1a0c0304031e0507050a03020601060f17040b060d0c0f1401030522050102091302130504061206020a02070f03080705100e0c01030e010e0712050105010f1208 77
    0x600c03030a041c0754000300541740c180361070304001d0841c1902c40b400c10601c0b01190308045440e6910301651070300010f5040c1008120383d14022104010281d01c10b00b4018820581c001c94464180d880b2680c500740b2040e150b0600b20b901811280201e40192015800304012031203410f951940200054030000488801d59988000980c1c69402880d40129103c820b00c654244c14818418114091a00307000c0c42c18040c209805050104c1c0d803400600d2286580e0804001082d01030304c240c2c600c001e0000c001c040030f0b8401c0101941c031003118101d030204c0040000c540c03407a06200d19400c0d10750384005248810625038480000b0743c0811204802e40c891030f000015111501024040070318400c135240c0e61540303092300c0c00f40c0c501031054450540a50170600c0041e6000d00000b01e004808009290100c1c0030440b588040c5c0c0100710313032a4078038079a0240200114940e10b00107019501c65218400070003a50380d031100b84241445460017650f5002c400c03a4a240007042c4458090001780f00e62140c1c0c116460b101c44c40d20300d01d05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 282846312 1250 282845062 282845083
    0x90f0902190f0506130509040f0b0a020903010b0406080312040807020907050a021b0306070e12030a0903050d05190309020f100806120106032604090207050a060515131805 75
    0x41e104680c041c49228000803105004140580d40d09040149191402c01040701038010107000700c4003100040c040c030035007840d14590740d50001c5404407541410070b03210f0065400b0080c69402503080c20240c1d10b06c0e0030248140022108444007950610344200940d406206010384140c91424050049a0169030b03284581405929291a42c540d0350f1034002c006414940c0e803242d017034101d004040c00c8608903100422003e80c4003c4900d4001d00620b4504005070004200043c030304614840803a00031480d82c0c100c45100e09590040c8112040060300600403135041c0700320044860100c2911030b0401600e0f009070020024544001e2070702c02c403112610b0110b20380c2c0018400c210700042140e400c3c403c0a050200000040c1e6a41ca0001d228140c150344507403400c0c1003051282050a8004810a07100302080c00c203403400f80c401c82000799a20f1145041040d5035121216080e20903a14010105850001d01004c1080715100946900300d0410280500c0c4010580002d07681d18420107001d040001803405e1007600c040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 282847562 1250 282846312 282846349
    0x8071209090c0504050906010305060f100c0501052703071a0402040f0507020607081006080c0d0204030c0308030103060f05070e0d0c09020f07050c01080f13032a200a090f0902 77
    0x1228170308404c0001c00b95020b00b18a041c145800248010303511801b0070f032001c1780420340b01c13544110300e1442d048440c9203440d000074015510701414022407040c402c41e50f40c218420300b00c038280001d42510001c0d07206d1182c0000142403404400018012950700c45000758001e000900c0011410b1a101848082d40c000321247e0380180c101504105072103030042d081c2c540001c62030408078051414510080c00012018010000034100441c80c80803000150b0101d4001d51f40c0680b2406d82142c1e030340b0b41b1000a4200707000860b0168280b00ba0301f00f808511344181441101281e40303191190b05030308103020403034610041c00d43e05400300000200e00940c1500090030441200d81c0042d590fa0300f02d00346141400c100191841c10840120309000e03107403002c040c071580c100074141080300382940c0f503280c19100c44200110703510b800d4024946000703600c1d000204c080c00480c050545082070f0034100850208407242500d8040c0c1c07000e080e80c2c060108011943c00348006810207c03002421740801c0c0c0001c0d8011101900100d039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 282848812 1250 282847562 282847567
    0x120503090a0b0405010f08062e1704120f030e010c0216050306070203030718080703110301050603060610050f1e040612060311090705070b040c0602160308071209090c05 74
    0x1803904091205800030104004039904083c02c04c000203000b0110803106404014403400425000e90b5a001640d8520003002582d0002e07050712002000c0e03110984203030380081042010403840044501c1c8140b4806c0d27074007042d4080d01004010702a44e0103075843c0ca1030410150781d1000e56610741c03070911a00c08041910740003400300b04001c0550382080e540032b820080c003075004503081c000c03825000029650004807600f0100040448003002c9151154a9031141c100c0d841800c1c400028005003107100d022000c0240c00038016960303480b061644d03600c003d8606a4221030074034000340d00f591081c8041c2c80303100d580501183c03500e0400b04407041d03211034011600c4000c0300c00103010803510b41c00511101d103005030b00005001d5680707540ca54401803403800c0580350150f100a40003602140c407541c121480554880c4035004141400d06221400c00001c2c0104000761040c800260701c08640d480000d0100c030b6106104a1504540ba500ca560702c0070a94003036400c3c00891640415684103a018103202203549544854 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 282850062 1250 282848812 282848827
    0x11060f0c07020901270219030b061909090f050f070e0f0306041202060106140904020703033201090e1902040b0a031a0601032a050904061d010602010c1205040507120503 74
    0xc41500481351789510051040084610b800280d990322000c03d2514140080c0d41100c0101140c151310486030800b5880c1136106c00c0c84603041d003101440090b42c11004042000c0c0080c1403600007103c1003900e80b01c6800744080e00148100d071190400164070b0341b0140c9482c0c07480605401092030107170162805c40d02c01c06812024800a681002007500611542c905184072040307041c42c9000d50310842c40c0103406140c00081040605009400c03100341010500f02040640c0601c072003000b000701c101c00820724901c0018000261803452030003504d00c000b00e484060690401c3d5551110040310789120101d030441d071035401e042c042d95649040c150045004d80460414080840880e14090100401c00380c1490f142a440b030f4009000001c80000c001202ca1007590101d004034010794190040c0305416034801e0a1540100328580e000a0814411450000140860340c071004182d017038581480d540000a842c82401402221080d0003e42e001402041a2400141c8440003407000307484800040d102075200044a9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 282851312 1250 282850062 282850109
    0x516090c120b0a090f0515090709030807020a1802270a060e0d0b0c1c14040308040302070e0a0903090b0301030b0f0c163801090c02010e0f0601080d11060f0c07020901 73
    0x7004d102c4040b01c1051071890000d2740909058010f01001c6c25141012500500715207c401c40c42000d00b03074840f04040401c08083c4a10082d511090261504146808401c420250070850328681c00c0c1001304410201ea051100885038132014030403030781d0700c0040c0d4000300b004901d6030340a00e40a1000d0003104c550301c003d03212040032001e8100c0b03d1040071a140451101d00c3c02891002144c116030705103003d034040c2c0c03650f0030100c0c071b040e0740c580007844928080c800b8442e0106140d48079556442c400e4480f099100c0d035030342102a80c1d0100b480f018000410b440c000452014000c0901d50f401015200c0c0c80d402e101da0325041d1096846024801c444400c150300c18409100c6c00c0c500b1240c8101c03840c3c0301d00b8040d00ca141e5036170000c0000610030302400980b00c070704882c1814004c1d0440c50b070541240c002c07518642840c448466451000b840794010071b0140031020308540b4030640614100d422440d004003d1600e03407007000c0c0860341c4002c00b51801180140b02c0400141d40c0d404d00e480c000c00140b4103035a240d1803981c020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 282852562 1250 282851312 282851341
    0x606030b0f100603230c0301060f020303150409030c0f0303090212030304110915060c0a060e0712081c090507030236060f0d0516090c120b0a090f05 65
    0x21003054401c080108a1800c04041200d401d481d241d02e000300302080f000752844d480490000040301c003801319208100c400360035203020314121081552025101e2112040c140d807244000d5030034603110180d455030016581820340202c0003051003494200c40f80352554542c211489401c00341200004d403908003070030a40c9052040c12064000540255156040c00c1d600c541122002011140c040c20031b030400294204084022130140b01c001414035a950108150f100d170300c0c0e00304000c0445441c1d1030058040d04c00c82c0300060103400da40014800f0340310402c0c1c940301d0711718941102510f00302c0d8101004040d035441506000780c0540500c40c40081040b68118410410000c100100c80d01c0200081200350210741b6280c9055824080c0c4001440c40030784501d8040707181c18158004103500b00701d6190320302c42040310001d40c520540b1404401041c2e03c94890000c0350aaa0f9002081400144a40c1c1d010551500e6940202e200b500010304049019558120303001c2034400001b04200074680c1c0d003041040080781e0800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 282853812 1250 282852562 282852571
    0x1f03080a05040f0f080a15020408030711090a05091011090a0602010207030f03051003020d0f0819020c0604051809010e010f0903120b0d14030f0304060e0d0f121e02070606030b 77
    0x404042c011708040584c1c0e501c3c48044c0002e0800c4065518240e000d0310b0030380c1110060710480084e25039a00c20750078411681c4a280740024007032083da100064180d4501d100707480c05425444007070000c4c60041c01100380039003202710b0051510041006000c08a03901e13030180400800e0310790000350b03c80d4410705014181810307000c04641071505110070009129200c401d85c401f9660704031140c00d09006e0904024000a04522006080407000a0b4885d28040e40700369540d440b224a900310360348403034440c007440290b00072403156503007004540c030560343d03621480a01143d001c004e200000600fa80003c1116080d03590309038060001c1a074403480c000c1850f600100c41c1032146082c1f10148421104000031401c2040c1c0180f01502136410100360b880703114020300072145200903144009407281010704010340180394000a00c540f6205a05038065140d001e4400207948501c5030311620f8010300c1d4205441b018050f82480c0d05004100381d400c00c00182001e1000d840258098000012510f04610f00b21303034416030180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 282855062 1250 282853812 282853829
    0x15020105090c060405130603080a03021306111009050a0f031107140a050906010216030b01090e0115140a030206070812060d17070201030b0301020711030d09050102061f03080a05040f 80
    0x20b6103141601c03880d01300c0f0300b2120255030f0280e2000500120707000401c01a00010701c00d0780002005144a541034000d001094030758501205620b545500648142c80d81502164198200818500c00d001280d0b011000030760207801541c840d0710050b61303503192030061000203c01040340a2112292a1410841d6001400c50000703403078200754407100050b074084064454203120b1030700d100c0003138141d910a024001c2840d4814180f0158542c0f64984070408100900070741011502d0041c1041d10240305024403c0040349464408007040c0c03c0000c0d80401c02343b0080b03041e4205600c000004016141c0200900d100350194045607190355a14110014086024091031f115045182148001c20081001440701c10a1841069a140c046100503000f82c0b42c16004940e241d440442c0c200d0074422090320640024130224169888108030040c203491200060117680cac0141d00050000d0710180c040291000030701c240c0001c542206aa90b510303d8881d03401101040006400828100400038a9814041c050007114 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 282856312 1250 282855062 282855073
    0x1e08040f12020a03091205060a1a0306070c0506072c03030c12030109140405100c0c020418020102060c03010b09090402120d020f1507120218031c140307090303180f1502010509 77
    0x240c96407a03407600090803270129203555150703200c2c0c1912451007801d13a00c100034094030450316040c48054092503800c0415070780f501a60f400a1507044c030810088245000000c840c13046802c000c09440b03e04c00c244150542c044c44108852901d80c3c0e001c028265440800415196580d8104060790043c0c3c1d11201085441640d0581404000359004c220789506040c234072400641503a1140c02100ca100345014041c0d001490610f40481044d214620300c20910f0003a0203d80054460312019003480c03009101e21580c0d084248402c050918218011580240c0010101001c844600038004d0420560341400c1003d039001c0046d0422000d8240200d00001e82142010081d500d802c0b203020713003080700c61801007030196800a10812100d09001c0407902e41900a01120211403480199949418254080c0c0021480320422042010611000c591248070590354031106c141c1b95580582d480101000030050781855404003140d8071061029080c02801c2c0031020191007607002c035001e0f0071607501070219071054025 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 282857562 1250 282856312 282856349
    0x307050307080a0b0a0312020f07030302031606090b1e091c0e0120010509120403150504031412060108060d0506060114040b0301080a02040c1e08040f12020a0309 71
    0x44029240c0c0035001c0d08003004241d5481511600501c1104402c56000ca0503c1c004000c0c080c4110128a01740d01c030385c003292410420221380030754801041c800100140e0082148031000381c516079107806460301c500c1002c40c051a596650034100c2104030380d0841d404102d5a6804e02840300207c4076500090140090001a10701512150990031800c00780780034040f9024828000d030b48190340885a580c4084031a54bc40180b41c0f81f01406048250707141c84191050320424240c4a81d400112400c99070f21a0a80c90411000030f10030007d030400910546c01c0c050084155118450b04000406070b4100710589583d65241110025200b080090452402403101c7c503400300000c0e8002540b42d4014109081ca00c0d1040c1c1078502070300303081c445e070b4000c1c1c0c04030040030000054450300047e50200d29442120103202c105070118003202d011140c07107035840d400300400080514185c024642107800078000c0d0350380140c180300da0f01c0d907541481031503140c0c10040c1c0c82003070064140740d805071011010389880903034240030555 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 282858812 1250 282857562 282857567
    0x40c080f010e1306020d090209010f060c060b03240916361a0901150206010e1f06050306040f0b150c0a120c0302070e060108010b0a182303030307 64
    0x2414024001c0b02a04400443c8400300945540505240d101c00c003590f0700c000c0d02071010080e04545400300c0c018140f620010504c03402c2402c413079041d51202c0e504c45000b200b280d250b01000c0c012410b40d464040c003039002543c07440240090025100c074401c0640e40f069080501c2010320f0a056030a116001b0b1868030014054032008030048104c2d50701103140b0004101010110a148101808044150601c1c28250982500031400a202210400c481245440e030366180600c42640121086400503003020b1700500c050b807901c0c1c4041d500040005480b5513901c0011007000000c2d80107410482c0450340200410006186c103001c0e082c07010090700c0e0103025807819480401c00800038842e800c050308501064509107a80c0412180202c1a04410b2041815044444c094002c80c4e50041c00c0c0d005010340040400c82120398110540201c2060f9501c0040d030307181811005003074006990500401404018407900200c0f000003040c09048054000102090030b02003401265071000d9425002e60000e20401c403d464 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 282860062 1250 282858812 282858841
    0x50c210a080603010b0621060d02030c010807050403021306084c020d0b120c0a0e06010507050f0c01020f01060b04050111070306020d150e161d03010501080309040c08 73
    0x116a007824080341c0c881d000000c1c0905405000d00303802a40c0852950121070618480421070f0000441c941c030b0503152681400611410804041e400d5130162000c4900ba502c80e1074032651050840c540701c1d090a4072a030001d10b44201c104120f008007504c0304402e00c1180c10501ca08901d41405403801881c0000f00542d0700c04072181480c6d0100b03140340c1321a503100d01500c105810281001d003941c04650b5042c040718190024958200564010020a01c40c00300c102d1b03000070070044030400240200c01c0d8a140000c80c2c26488001400181040811f100f98070022b0400c02400909041000c0540415450440024030b400d42e0600d00c00100c0c0e06108041207003152131021141035030802e1900d80c0300c04d50012a001d240143c20f600040c400d620004442c1d1105650f9404104014002c042d401c1820380c0da006a002a03c1e010744000000c086081c2240440e14041d0450812007101c403000a2841e510080c006400c50b00309a1280406820000b101c40340340c902403192040d0f000e01c5003004049410301011262542 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 282861312 1250 282860062 282860077
    0x60c0f1e0c110a080a05010f1508030405040c1e020d1101060317070c051206040b0a050103030f1101200d0606030e0604060e0118110a080f1009060e0607050c21 70
    0x8480b26207103071201d4880481d0f0802070403100b01110118500c03403409a0080c10700072641e204030b070b01c8c0811610b10160101c2c070310401c50304441c000718141800c0000f000000e1241d24115018040c0500b2803000381000d2169002c60841e8a8000d40a45a61400007400f10151031024111907403501c1010f000090f0070074019100300420400d50380d25000e580c034201508410381e80045030b10004c481e814a000e041c0c00619607101e10b1043c40c049001e5120865a00f003507903000e001c010045403000e02c1440c0e40174130800c4001e900c505c0b641c00220310500341c0c1d4405124890101e600c100502000102c01900c0c00c054090040200441d107002c205240005022546510001d0b00c000c100d40e072034140805580000b500807001001c042c9040c3c04022040f46030441c1d1418140c03c2c058000d030b040b10f00001c1d2200000c24040c43ca10742c0e80010f440c41c1440c9400d51401041080c10031941d40da90b070914103c140f01c00700030b00e074800e031519260203039103518655016142000d400b0003960100d807000d4290b20b001c4d0035034042d21a103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 282862562 1250 282861312 282861323
    0x309030706150305010615030f0209010e06030a0609020c0c09100302030a02120322060e041104120c0b0d14010f0308072301051006090918021903060c0f1e0c 69
    0x10b81c203810400c040d400d2015031002e42158202580862412640081500302079040e03181040916645000310080e8000d03a00540e012404900c0826078508015004541c041d036602d0380011a503444201880803600003420010160344280440411801c0101d6115001140c08070088282d500d5507000039620460001c0089c00b40700c54502d60a001d8200304203540d1142980c010b840c613410b0040d40b6001c4105c01600c0b501d0005006458503100a00300b41c0300e81d03041c008041d5841445e0034202a106403200c14070103c00c440800c203018002440d00c00040140080b44c92500004c10001c1b41107942402c1c0001c1030f00201e1005c0e42c1c2c1d10040000a40c01d504407070b1b0440d48204107500c400140e05001c581c210b508021041c0d02e5081108201802c10041d8201046d41d0650701c4a00c082501d443c0c40ca000c4502991203003481d50740c160304081c098070f0036000040c2d07a110303c01828414280c99907545810b40c0d101482e4040401c0115010740034aa4200c2070501c04c643c00071840c45549076000348003c008200c090b001525 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 282863812 1250 282862562 282862571
    0x14010e100e0d0f020a140d090b0a021209060c19020f060310030618061a0907050c0309040209040b150408010c210b031204060210060e011d0a090f20060309030706 71
    0x1807103402409105ca040b40c00c0b03c903544000010b1409a6150801004a5400244441e60118502d02100309581c0e042c403896000b03082c1054802e1800c5101e50080074203651144041c055101c1040040045c03d420941030300c020080c10384d1910500c8030148400b409a4860101801000281e00e1601d02c0703003080300e07017283e0042025031034221041ca00d00d00711100030713041c035082c5982066004503e01c45c01403014000e07600f00b40142d0725400211f80d140100c80c12000550020002d420ba41d1900b5000340c808024014000110382443c000081c002d9003013024203829200c03010800300400c040c28400d418101c02c00c1d0420309490b2507150000c5d5045180410901040b690701d501c0480f26403000c01c20040040c0020040913a500c1d180d000203503840390507540c0300c0d4807a8104074010484280e0040800d0494841512007005d0810702c002c11720310230800614190300241d8907004200419403965819035030302d00851286a0341030f010740707200d90825203040b503407401240104184000e0320000011640b000d0f4102d4030004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 282865062 1250 282863812 282863837
    0x10615020d050f090f090405010b010807050310030b2e031502040e06040e0a0203030f120907050603062101020301030c090c090608160c05030a17070e090406050a0914010e100e0d 78
    0x21180d030314880d0036507001b01460040000304034055000200b248000d0f210718545941d5900201e4031440300325a90000300d076490800304001280c0d40800e9070425003284620300881540c3c000c01031a80180b020039001e041032034a040042c000c80c89801d0140c2c014014095181c941440c0c1255880308010301824001c2d03644031b05c0b03401c421f4018469075050a600030192544c03441074900380c100c213030010940742c40c0b401000c501050380103600207540c1003103803400303810301c1d0640d619042007080400001410200914024404d11001c203428402103018600c148160300c411800c005d2100121440b0821f40014010322010910440d40c0041485601008899401c515607106480407a0580c5415400a140c1d02c4040b031410030381d40d006803818903500a4420b031103240d545d07071080c00c03524403113107070445900300481c000802d011801e660056a40428036804c0410842255070f03411228102c44003103c016655114840d00d84550203009440400350340d12028885803807440c0140da104d600c001054070034090b8080441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 282866312 1250 282865062 282865069
    0x910060816030207050a111504080a08030903040e0c04031403030f0a0e0c060304060203060f31060b030a050103050c1210150b03010f080d0305071e1101020c010615020d050f09 77
    0x41d142d1301e03400b07400d4510084403850212616001c0c0c0c0e03c450301c01c0c03c40203003000c861403079002901e08484a0070024201d5039415102c4a100e6032000c0c24281180c00100300214540c140703010190300450300c200036a55a285941005003019200110036400360b08100144406409802d841b03c2c0c0140e002c1d070000450b0a116038440f0302d440383c4403030001c1e0071501c0841000140001c0f0b9000d144a040c1c1030b1810203081d00d51108010500354905010101b24480302e0514250a01c114044040e1100b4444000741458840d4042c55044d0400c030b42d0f81c6000ca03181c20042c01049418080d401c118542694418032032030003e030516413103c17002c0d4801c8084658074904903100c0c2103c0d9004c48001e0034210b1249903070356114071040c1c6059105001d40910782c030811420b048a14424816184240620303994603080c0b001060489d20390007003070b4000302c0030403029070000c8986440030703c003c1ca4041c158000001c0e40510b4007040003038200341180340c101035410950718864840c3e08041111402140f000600e50388400b41c0700003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 282867562 1250 282866312 282866317
    0xf03181203020d0f0203010503010b0a03080a03051504060909110a120f111009030b01050d030503010b0904090203100603020f190b0a09080a0305040501081f1a0d020307080609100608160302 83
    0x6a80903503007084c40c041009246a801541a03580640082c0901c03607482c1d0038031021514034400142100300c10030401010781c4c429440795810410921410074030310340000016041c0e60550304107440b0b955441d0703d040100b10807001e107940c030860246d071400a460702d04208040310011004d0040c1180312001001020004c110001000d11a401406007045854141c0c0040003030f10180021034090081c2800405c0502d0b001d50700e236203100c1d03150350340d6441c40e070a1148500484d0810b00c0d075907400c251210507100040e0340510841c014401c3c2c07000005180b03461801004031a04002c0a039074020b54107001c06841003640e440c0d105043c0d400c1502410307512940268120346500c940e5200140c40c0c02500360031f000705544400104100d68099a03002c4064031000c20358001c11048088011f10b0f00c0f4440030401c030641d0160f907440c1c640600c04030414104600950810260b81c401c981140000341d014040002506d00381c143d1310741025012660718101410158043d011150141c11151a44110341c10100001d209404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 282868812 1250 282867562 282867577
    0xc030c02090c0310140904020d0f0611090420250b0103050d0e040c0f03200c070503012003060d0f0813090e010902010c02060904060e07050a0f0318120302 68
    0x4503451502d840c2c0030080440d003066850240d8040c40e1036001802000c032001c02c0301071500003864000c0645641c0c0c20084080215501140c4203d0f00f4110000450004d208199018848128040e52118082d0400c4110f030404001620101c2c810b491489a0700c0301841501d015172241c038100940000743c0045425460400740c001010b07040054008001c009003c01c40041085a03038030340122404929007040155104610107600040640b4090b80c0c100e8800c9d0000251080b001c0b54100350318080004410045d4444005111640e120140821183c01c3c01d2060041059005800c5140c00031004201e80c0c0910000d403282d4032998040c000e04c01480101c0c0b181410895100e1704070b681c0c50030340103a03d00c2d103c9028070a01c032005141c42c400311200e000c18050390181d1036050351956000b0a40750308000e50b40c2c10900003541c00994800f0003150b0744181010325401041c0584030251a9903151711f00400c03a1700d6011000080505002c980c0c20803521141c2480040359120000745040c480c1d085046000713004418 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 282870062 1250 282868812 282868819
    0x5070b070f0519020406050f100c0804050418021309080f0a050d090b07020615060a120b0a060210060b18010e0102150a06080c0d050c120106050310051f050108070c030c02 75
    0x301000303010f00f086400140c1c4292401d0142c80e5032081040610414010540d40002208400c201c0d174510503041c5540080c420b0240504085d210350104046643c1c1540b00300001c005040313000198500b500544030700740129902400490b030150b86031202c030f024070780c1d8a181c0c0320380210b801001503004105072403042c03001c40e2003040910b4290400041083c0c05807241c901500902c004288000800c15086114030000707803100d440d150702d03490300f02c9500390f1844040b02c0c05035460350407076000d0751102c0d4031000400d000e03802001c0700462200103400310b0f11264070a6416500810106115030f00b0151000d541140074204043d800c004600181d003030011000030500303039880070420806007001a1f4000d40039a0642c204075002d40340c128017403100c500002600500298441a0301100610b0a100740e0b25000498200216400b0358174004030303240804445850300c010382c6400030031410642420f140f0020030b040d942c80e14000fa04d810000b03808524050048001c112004030b1950034180510502082c0700d0303002c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 282871312 1250 282870062 282870073
    0xb091201020d0f14070f08150f1f09080303060a090b0402090d0606080d080c030a050907030f03170c0909041e05070308280212030703110d0c0306050d05070b070f05 72
    0x9483c8010016815003a000008a401140c07480340700340402a18103113540c03120078594681080072002481f5858070107a20541c04440d003c0c0d03c1d11072a2000000c01035409100c01d485d400088083c0150006421400f160b61042c4100400c0c4d60314010000101c5102030b50010722160f6140124020344507180e10280c000712101c54003410801641e001d00d0032074105101391030000102c0034003118094020b6035007514070007042c001302d0500109544283d4018000408407000d0a60769601d51950303c4030158281c004c10340c00ca400043d640000d0001d243c2c8646094485071500c0f40c2c1d580000c500040140c0068183c0802c80c100400468541118282c41da80003400c803004960b4900c0e02101c1a4021014a6040da0280d4120440c2030116916410050815000b901121011401d10442c40d08028504801c042d01c2c0c40b80c4180d00c1e082480105040381c007000001c645c15000c03e0000d01682c0300307580001d0050601400200110f40c0128805c1c00f030f59000300d0320b07030f40d40d0f03078581440800700c50054406403990003a03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 282872562 1250 282871312 282871331
    0x1202010f1106010303051e0a0e09130f060e0c1e0103060b040806070f110304182003010e13020907080402010e03071514040b0c03030415050c07150e06010b040f09060b091201020d 78
    0x94501c1c0c048a02b00d680350350603918000d00040011401c0f4000780048141c44102001031f031240c00c0072140c54911411034404440e0302c40010802e1950803445060104810003030002940c1c1405010090700b800c0001500e01880c2ca1203003035864000070309040800c03d000d01501c00d023512a41141c0000304030030080302e403604d031603808140d810035007489009101c5191103084c0301c00130941040e090003403100420131415a0720b018400304804000426406a680c0b036000c2c0800141c1d42d11000038094410b0f80d481c10020710340303440050250700c40c2c040105e119a1042c0e404020303140300500390a030075208500c1d140e200f0420310341c1d40c40607030300540d00232140340807000c901c401000c0e0002028500c0b55001e428035101c83c000401000c000c0300c03010344040e0001d0400f04408008a4101412403500110741d4200003071000c0502401c5003800020f0304412044000090100150303040703101070f4000750040d602e04112491810b503c0115510407039803844c2c0500400865500800c40c29030507604030310001e40c000e00c01d01e5407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 282873812 1250 282872562 282872567
    0x106050406020609061302062d04061719110c0a030f0807111b2701141906141b1c0c030f050903010e01061202010f1106010303051e0a 59
    0x129001d118018402c20000a1501a0006000d03008072040380945c040721826800703200f110760014650452891946011084d04000740d16811103c1e03105081c0191200d003020300060070040340400903101c80031100d0500405d54400002810402c04101c00051107289841c10340e0304500460032982000c0c00780407070103818580c10845020a090460b82c038281140d840400584091003040d541010551203035050031921981e0284452800000611032207101080541c000501101000d80020041d014001000001306071025100499401c07a80c180410a00042044101ea500d1142a0400c1040c3c00d82410030075601086800d4210b45d03000007081e036200707410300c0c59880c1540d490302035002c03d03082e8480c101c00e481410001200c9a05913503071003103050000307400c1700c040d044041c90640c59503031001c6440b1002801d105d1040113155440c6001201d0043d400090095181c080b10a8144505034450311220400450144d0540341e0500b800e0303499944214010750191603580040c85004c3c000600705080c582c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 282875062 1250 282873812 282873817
    0x204020c010606081008030a120902040c0903050c011d1e0904030306031211030307200a150e030c10020f1b16080316030c02061306080a150315090218010605 69
    0x10f03842d80314070032a0303140c6001e0022100d42c070340b144444640090080d8111248146c54501c41080d00e1507000c030b12040306400140c11660040940e5000c24a0804100f003008010302c1400c0f00d107902402d01900380902c00340154501041041782520400b040720010100303412441e0304881c5440b001d0507a10702840e0500e400340051402d400181e81a80ca1100b0304141301c3c0c0300b403211940e5000441c02850968503681e0b01070326141c403002a0f012000d500c0003021620f401040044403080360181c02c401c0300300031281104000312003500824484582081020254600e00081c9800e00343e00360000040e030f02c1c40000800300080c00307242d010284e02e06442c50414110702c8001000d074401001002042140d903622124240d07280714652019000d0300001c00c1079070200b401079440d01495400940381c02e02c2d000020b46184c001c40c0194101030081210316040c808580028400c004200382c4040c007190445007503490790254200c070701c052080e40c19100e0b00c18200710744400c955064840044029070303165503103551018000388c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 282876312 1250 282875062 282875069
    0x515070b0f040c050d03090329090c040506041a15041503022a120702010306090204171507020a0b060402090a03030201020919030c17030412050c040e0d08060f04090204020c0106 78
    0xf41d00641c000c5000e1410000c490041c5070f25480344811180b66036249940d840c1406407216201d007804d241103200041c40315450f80301300c41d52800b600708218001d00300400c0b0703240a04064056444c001c2c094583c0c200541c0c03000c01c0100c086500d902c0c1a6081c070601482417082e40c01c259510125948003c52081d0190042d0441304181a940265090003051606036111a08160803165000030320390400442e440c4000d11546006240100b05c1c6a15556100103a030b200c1c1e07000804c41500180201c0b000e003001d01c009034440c07001c003480f942c207420142c2009544003030341e80028000303401490102e0300a66440c2c4c129500c0200142c05a0079066690801a00070b41040301c541c0c0c01410982420b1112000701e044c80c8003642d41c020a00d0382c0d22130034004866150402c5800114283c0300c00c000c080f4104810302042603026108000400d150900e080a00081e94501c00c048071542c0e000700c1c0c7d074a40303981d00054000d500c1071054035190444044140010013400020300c0c040c1d0480d200140190001d5810340080064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 282877562 1250 282876312 282876323
    0x16110a0501030b0d03031e0905060402102c04020c15070e040c05120405030403020a17010f05070818070f030614071b0b04060603080301091a030d090515070b0f04 71
    0xa956034000540590700790076015030303010544030003070340009009621103600702d4030924004803103015020f002070880702090401d07900c5a015074100002c500c5d2081803150031004610700f6154a5058001011100b011038881d0321048814a034800000d031590350642340b080c10301204880380c071600c4101d081c04a0000707039604000540c802c00727032001c0b6043c1070142c424800c10f2603845074602100f000d00341140c282c0140088400340010000000561303038401c02000a40f44040c0d65040d1025842e5071a42140c3c00859400c5055042c40c0411404c035400101041d880740300b12200248031542030040342d0a112154011250400203d8008000e12000d540103140c1190041840c4889444603a41902c10aa84040d5080000c26180c0c15200103110b4071001c41d001403241c038000c14542d8682d07589001f9604260000a04159940507204813070030628450040c0240903800307000c54010100c8000c02c00e00043c0a0700d4058000101c000b9000e0000fa03007114a101d401011545ca141400684071506a1b82503034140c42 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 282878812 1250 282877562 282877579
    0x608071409060703051b011415010305060108070f030e0708250b0318070504020721033803010501030807031202040501081501020a05250b0309031e1611 67
    0x49152403641181d4107450000c00007030400d00e81d40e6040350242d04c05461650240048101c1d072141440c240550116030240c0e010010151801940d10051a1031b45002c441c1014140750600145903040301c0300580000e40c600e001c0740c0b8620411003da02500308000d06132030a11a115001038200c2c0301281c1045201400c5c40c00c0480c0c04900c2056030b02201c040d001d104d800306030400c08a0440c14207041041c1c40c440752a02501c0b601ca13660800241280c110500035100001d11520f00760b0b410080404018402c25a07050402c00b0580c000041d4103045403210300121307401d0030761008807140c1003c482d82038410706004000380004d60710717458800c95503086001c0403000f040101e1006c200c10500750099070305807041a540e41c2c078941d03144001030030051050381c1118198050301c02c040e40400e100740074000646100c0c43c810b8866030b2400c2880c48030903540c0e80c0035403084074050040c01200080401258038aa8900814060803c10441040c0140c400d1507200454041c98a8000b010000c040150710a2800d0403620707500e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 282880062 1250 282878812 282878837
    0x270f0c09060f0801060e0612240f0a0509060a05060a12260c1b0a0506130f17031207020f0d02101503030509090c04051504080c010c0305040911070c060807 68
    0x70300782d805c0d500503003611a00c0c103c00600c8030b040c81d040803034000c1504800c4891350010500c408420300c1105004c981e0785019801001340e15203002c614290803005c0288104130b140b070150b5981d501e034000070340454011500c400103c0d4441c1c1e41d04000c031001d04141c50b040d114480c400c0c9889001d0388260400304000c1282201c2d404d9100d001e040c01c1e03400e00c12031503010300030800004000f840065081d48549500c45103a040102c3d01d40c407050054842c6155114031001a141001b1a003040c0c05556071194071401d01c3d00e03024040544010050301d40747d030ba808940420640b6815030503410020001c444440c01c0c4551080b0520b05980010862605611920208400401480300310900a41c5000c0600429410001070905080040007964026412051079040c0b607181c50000d111104142c155041c041400f14040c0940c00084c00010740f602402d00340070005074981e540203040d90040d48a410b0090303544503c03481c1c41c59503402c121079031035a00c0002d0311101d64031744e90054542e860031f036049400520401d0003030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 282881312 1250 282880062 282880079
    0xf03030d060527040b06060d050f070306080f0304060c020307090c020d0f0c02090c0c010e010c0215010902160807060b10110118050318061303030f12270f0c09060f 72
    0x82030b5450301101e510f51140c0c2d80340c0711074841031409044950041d00411004001151920996014100c0301080552600b00030ba80102502c0b81600006003582000c442c0e80709251000003182c2c1280d1260400010900c1c65000082c10142c5a074403141001381010751002c03003e230740410203102182c00c580310080300d2800000201c501440b0220000d411045950201d042020450083c2c0f6060000c60000f150055010701541d003502d14020038207001d64445481c0c1e41c01500e100040a01511110400f10b0030300d0160501e40801800c001d0001e003140301d0009001042c80280e42102d801011b000d41740e20851780051708024400940394000303a00fa9440c00340720800d100c05490500a900b90060001e40c00c054154100518048481c14002e500850421086250340c22030510840214080d0720b4000f0101d0780200042c0851406a180000161806d076143c480550743c0c61000300704150810a2503440107452800540740407400d0006000740c0c240b403030001082c8175641c00000c1600d03040030f110039800380d640a12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 282882562 1250 282881312 282881359
    0x304021309030206010501140d060821183318030607021c0908070b130b040303050a0305060d140d0905030c0603040f020102150c0a03111204110f03030d0605 69
    0x40060300003c0c010041903125108c84501c3c1d0410f03c03c500d207464503840c26442129a02d50140318135811107404191507042200da03189c80b4220100c9180c0c5040e102c4500d1500f03034210f580a5501c204040c00d0380c0c00312030303032a201304540810342102c9444814280389a01c1c29140c002c086250840c0c59002558030321400c0118000d805544190003c002a11b0007042c940e82c15070a94000f0070800105200009941404112000007071942201c0190380b4111646220003032081600203402c01c540411042002030341c07050403650303200410720b4005400e442d50306c00074010100500300645900c6583c1c3e50205058000b240030580c0c58890345805d040240c0ea07105160700c0e20403c47c561070f4440b00610010b0081081d800c0714000003441481a2003c0800c2512150200f1506580784000b0510125950300099094070401c03c110f8500090603081c0158251954031022008100901442020f604040c0d192205000201d45c7c06004054948450440041000801d0244551031007400222100d00d181d0444500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 282883812 1250 282882562 282882581
    0xc030608030901030504080d02070b040b06010c0b0c2101030615090b01050403060e030d020c060405190f0303020901091a210907030f031209030c0516230d1703040213 73
    0x34500b80346032000158010000200145d520750b004005000c031050184c4028000701d881f031140120305040c54180a1400d80c00140080e0502003010201d8020504040301ca40d44a88600038543e0380b1038240100c4030310403001009680710748402400100c200f003256003292031880f140040c075140b0f880d03a03851806c0075600c3d8103002901040f810401480401c1d0aa08046c4240c102c0740c0443e0304c5d11202a0a020890b442000b41174003941055080c402044002e00a58080c092003580c0380c0300300d04954580b0105c3c20f400344030081c180741e4009602c0c405c2d81d02aa10040041c901741030400003050505a41034041e0340058190f80d4001d41d82800c140da13200b0071222903401002400010400203003581d80f50340340f0390460b540c00d40910140310340300300c1a030040e40034110409220340d032941038003102c518005150103206146400440d28000d010f00c164080d00c20904200f00c0100d50700040b00038075070081482904030043c040d103a907440740d450a007585150700003503004c1d510a40364810a240040c450104803180305a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 282885062 1250 282883812 282883829
    0x503010c02011b05070219120b010801090308072d0503010807080303100603020c120c0a020a061106040618080c15091501030b0c090d06050a0e03071707080c0613060c0306 75
    0x501035070f0054803400140c40c90610150201c50b4980c0e110740030f2001e450041d404a511100d00002c120100041d01c2d0300c0d24010314020000b8000c0414690f006001100000e1004c0b00300514100344174400010351128244810074400705405640b421240189994402d024501051040d10400140960004102e074402c00081141c541998100300d0228040d506c000244e050740e00c00c810701040d1800304a0014400341c50285c0042102c170740944140240f49140340d000d00140b240103205640908400316006910603804180019841070001c240601000c2510000d0134420000c101000302c5400041c0038400011303040d071400d00310f0f80c0344001c0c43e0391286c0d4009508507030048040100005626881d20603005084000e009042040354030101e03c1c0c0d20348525041e200141c4420134005c02c1c6007248034450100312010055441c10010381c8a010600c412420402518000007883d1018000608190395507011943d0903200c0605021110801f41c0702481800c2c0c84d00e034507156800021030300034840c9404844201c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 282886312 1250 282885062 282885101
    0x10b0d0b060405100f0621050103110d05030d0c12060e060102031210030807050318060405030c0607060b040204060903050606031c082502032101120b04050a1b0503010c0201 76
    0x70310900001c1e220180c8560850448100301144800301025050040c007a240c0d10340041a40c0741414500b04480e0050951200b403401b0010b0012907144000c40081c04029034800d0724010243c0380c42407540c4212501086003a1410008121b419031003c0c1c0d84d00070b0700311024140030752a1554a102a0300c04181c1d1500d000d68030410840341d008210580f030580c003a141828424119950f45c65030b0701c03281c1c04000112845e070800982c140880004138207a002d50031041c0c400c94140b605001c086540c1e041803505c01441244086103600420105030448071707242d24003502c20b640382d0741d40c0c1c0e402030f291a1140c04212054014040080c12500740040c1075000051011000482d200c225281034440c1e041c080c1603a0003031241d45c80ca000c105a5810340c10b07890004598010740c0d1300da0035900413880094a40c132196064040010040103035118441d010071000341c101e000c000d00d50b00e503890000e01c1c240100c280144021155600d00c020519900324040860b82d041e802804021144c004c200c1c04c889a504064040c0e8050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 282887562 1250 282886312 282886321
    0x1050106050909102105010c080105100e150403050f060c090109051531050307080a080a050403060507051e120f09010f0e010b030d05040605181804110102010b0d0b 72
    0x1650f03901c2d401541c0e680d061440c8a85070322083e82c0d8644640c81408041141c1062071080080900c81d6840180d00351500e1100340d410000080c6400c0d404400c00c204100010b00150425640d84c00f45654145903900029903407030340c9140c80d81d1100506658480c2d18040c03440001c0301401c84100f01c1308080c00c141d454880d0203040c00d04024845881d658804000c01d414000c100b01c0c00210b40b100d10491000c1201d01410010030030714100e03e04041e0b04020b01a810001003001032040001d0720a0420303074003107007460711825142000c1710580a0760748050a068284024420b0558001c4021300d4801e450801c80000055604440c60041c4200f520803440c50380317244001182c80c3c4018401e150403004d00c00010414145418051b000d0314071890a1121a955070687c500c15403034100b250329101401400e01500f031914014000d421801744050014107688d00c190181c05a82e80c40c041c03003c1410243e81030000e282060f00f404415030070b0b0b988841d40590328020705022207242100301c2c103445035880710080c0c10598a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 282888812 1250 282887562 282887569
    0xe01050d0f06020a030e07060f0804060e0f19030f0e100f020c04020a031a120304060f1e02060703050c0301270e0d0206040b1e0a02070c030204020a051308010501060509 74
    0x12254151000c07118000c01c140007030241d0004061080c1c0ca6070f030109206c251644443d007400955032000702440140b200c640d0043c1e4020310b5495116801900001d14800308001103400c15480d924200c205005000b0611407078000c0301e1804007101d0080d500d00d91542140e55003558090b490107a407aa102d8004200a031003030f0700c0361302079503401c1c52280705070740c1c20036001c00c00300d0300b640c104442401c042030311880a18001000c2c503924101e488400c4651100c80c01c1903004c201d86902c11806480c0030400d52520001c0c9075402694800881485a141552041c1d0701e03980082d2144011ba501e580000d0418010a01501460054a040e03d017074030b03202c2c5200d01c00c4080000302c2c46c041c400340d11703d03d0f922144540710001c0c1c01c4c40039031100092900940130a10f05480d0031448103000070084101581210100c8a80f0030400010560100d44401c0040c0d90f0384c81c81c00e00c0c8000038415400207501500000b26600625031100107014201c00ea501c0b000513142d1510011402c1c0d80007401030400080c01400300c21030928 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 282890062 1250 282888812 282888829
    0xc0f05010b0a0b09040509060f0112030c080423100e01030c09051906020d081b0904020c0708010b04060918060b0604210b010602010902010801090e0c09040f030206070203040e0105 79
    0x24490400060084418000309100b186036030301040e16035401203588801c6080034042c50f070740944960080d18241c50701d16040700320341c130060240d12545001005210105409000060300c07468000306076070303101d1303580d6031068903402e1555550341c6103601d0200716503030a0305200c5242076a014032034885824248605004600074441e944030001000451140001c0c3d60711510541400340821141440c040303410804003a240503903804064080200b0201003000480285100351038501c08060b030b66a807180b03500d00140c06030003443c0144240780100100050079545c15448441d01ca94261012b1041ca40d6607080802103074444104000c2a018031900a8005441540200c4a04000070002030400b0b448094100007100300142100c18150104221018001c008102a00408551000b4400840d0650000304a032006200364900d05456240c0300d41e0360700e4240f0010b01606c0c1e0107011001c45141070b04209102d50007100068001d030041c540070444003440442114107407910400021500d07480d000074060200c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 282891312 1250 282890062 282890093
    0x321b151318060506120f0601210203130b180c10050306062802030703030f18062c0309210a1b030b0403080405011d1e010b030717010510060c 62
    0x980c1d84000c00308aa13560b00e03001d00030031703443c5c2d817100f03402071425050001300003c011b0b1240d410b12a4403c0705881d00032500000d0b41401640306000350706c0e030711140d072000400d80c1c0d480001001010140100105001002411070440e8520011511040d0401c0207010344c2600325502c1e1030024070104005075550510900409401c60301c07040c400440b408a0307951803261681d402c1d401006800000d003003030078107a150045c490341452405041109001041d0341010912421304001c00d0141c581c100760080e064445510741e100c450812501c0c5009142c443c0b001e449170300c243c0411b441641040e0301e641c480c042d90010020071080050040100e04602e840e000d2400d04103802c86d480e04c44038804044001102c464410b030040f40301c1c0e103c80303501d0f04092800c10300751010900203070543d03400490031142181c800201d0356516003400810120364000056818003400d1460a455007511680400242d54030b00c0c104c01c10b0000111030002c00c0b503900c0b01c81c80c03a240880c05214105c00600001d40c5400440c00115150014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 282892562 1250 282891312 282891359
    0xf0f020706110f120418060e0103030e13020f04030308150d0b10030507090902030d0201050907060e03010e01020a050306030f0c0d290109020405030f0703321b1513 72
    0x15580181c12600e4051316041004100002003420030248251640a000c1300711261002d202903401c01441052210f41480040c0c100b11a00010300003540315020030410b00c42c4840c0065654070079006105216500030310045000901180015003488403101801003264030060580950391000d03181c1c26241c400140070007000d00c811010000008008200c200d00030f09074450042109a07036801003506050320340d101c040559050004010756180c011990344140da900d4108030303001c60303030410100b801822083e00c010495807000404240c03403a0808060340c0300e08011000ca4085440080c130503074642202242058210b000c0d40b150100080140e02c0c040d003040300d03000600380d01c5400aa010b00c04c441c070a9220f042119400103050080741003e01c40c410000c00c080c00181070341499580c40c0c100c2100c43c002144901e009010800134901c90111140d4602d43e5000304071220207500118400000018418461151a0094941c42461110f0054428400380d02030801011480c000c14041d60f40005c11040b80c0c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 282893812 1250 282892562 282892573
    0x4080d0501060924020607180503010f021b0f0705060d090605100320010e06070302010b0603010b0c0717190501062d050102010b1309052404030f0f02070611 69
    0x5a411144030359030080c45659150110180b406816800d00c00b207030741c0000c05410088900300060358002542a40040151600f5028024415603110321039000740c00c1036526501340040d0b1a00380c1e40c2c036000b9000c102c0c4410043d00750384e604041d51a58134000c00501100d00d404c4604108401c0c500000a4962514004008921b4600a54840d411102c08881040380c40b400c0800500c2440320644441403946c219102c0229018000c2c000039140c2c1e50411146407140710000f5017031003010f00c01e401070f100c07007000030301510b0312541c44030524841d542052201c50030b148159800000d02c10066080c1c5418410b00c0d43c094500028564540255201207000580e95592501e800241840f291406100087c1b403003402c1c2d620103c58406007010740c0800350320150441e07040c00404070f10b0755210709100f8814540f4180c00141c140e030b10f25141d0f040070344d0300b880c44042e19182d80d40c401308203201c14005841184240d680c0e400e45c0000a9043d20300400b014203000040c1d11014090020724003c1c0c5048070140407040c11101d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 282895062 1250 282893812 282893827
    0x80f04030e040603060917090f190b0c030304060b0a060504060302090d0212010c080f01030506010e041506030305091002120f09060408100209030f150403030209120106030602040f0e01120305030408 87
    0x905403102e44d4030803180c0a9441100c10240140d00707030640311020081c070045250155500000b80900380c0d28204030b100e29603591021032000048000c200062501c00da54a81b54a10744c5016a181d8000301c509443c11402c00091401d40d2a1144110082e9012a210365003010306000c0228001d421814515821950b442c070084050f07607600c00e8084000551200102d182c10f0070f07a000802003440540b0418480a0079001407002800124085056030303407840e44044c040da59410314200b00c40810740244407980c507004010003495405801000390400a44844031744100d094402c9a071035942580c45452032006204c01c86046421800528007000014071031400c00303031501c0c8040e01340211000100d20700c6a0010b8013602c0c5046c24403044121459050103850816032944c90705544140040c00202015030004201202c3d03901c664000440c195418000c0100548030310300400203520038003500340400311042002403040340b10f44c04c0506032802c09085800314803450760150b400380c20140c01122102d84c14031030a2b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 282896312 1250 282895062 282895069
    0x6031805070e01063005040320070302010906050c06150103090c12050d17040308060a17060403080a1a06070204061208210c0703080c04050409140d02030901080f04030e 74
    0xc1d104001c5081d425514090000d0000e06005d41040561009440c0342d8004010207210320b041c1d4000390001055659461070700300c401d500d04c2142c860f40000e0140d03000c1180c490000e04002aa0701c00e80f54594420b4698800b40c1c2c29005481c00e00c5002e5105600050610342040d02c0001d13142c5040c10003086e4100c803a654000c000c0220380240802d4040411248103003c82007040020611044c101684201600300129040e0b000080c0080d0030301641001003032007600c0303014201e001420f0742540000c068100b40c00c5952903540c06c0c3e80550009440201081000c0103e01c514038410000e220311840c00f2913a4414460320350001842664482d0356070000150702c56040c400300d5034003803040d04140d07a5280c41131400c040780c61040d182e4801c521800e400b00f080c5614214103d4017801e40504003010640d6801c002018284100c0d000150064240750482003000f004e040c00ca88031205000507038130032904043c01280d8034060254050300081c060000f140d148010f0030031607074200c0c0c000e1030310700d05040422020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 282897562 1250 282896312 282896323
    0x230304030305180a4401020706140609070e06090a0b0a120c0e0d1419061a060d090f2001020f060708010b0a05040b040e07020c0901030803220507080d0816050406031805 74
    0x345c2c01a650000342070300800920b0b101d403030700e891000e41c3e042110b400c20801123840c01c100142540140441c5844500300c50751860241e8001101c01420242e0154483c1c0c1d40781c0c000e13044a484400030406920310040b0003000c9015066462206e41d440061084017013081086105004c0800d6465038208803002840a1302400a2442d0f0201183c040c0b0b0916043d26102c0b00f1038031900b9000080f101c6100c150f4056542d5042100d14418501d0790225481e40e2a092244088030040c1c001060801c03450b0182c245a039041c0c03250040e4100903025510350724509005d07103840e041c04407084400141200014020499500c01601080384203181c090309040e100d1200c61081d5000d0381200140c0c1080b907080007030f0301d80d04004014084000355101c80095240d41d0314031455000140510303d140070b5054100c158000f07090031005205800c40100e0303030762503a00e60039141c84600111012000449120004103007103850301e900342079600b4556800e840c1c20702c0d140c8110001c0001c1103045810450480600e804180104170 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 282898812 1250 282897562 282897689
    0x40905010602061609060c020d11040504150b0f0609120715090315021e030924011a031909080d0903090519080a230304030305180a 58
    0x10442800c001a920a5a80e0f091400400300620441d080c020551f00061100007168191050000c0844501d05441ca010580c4540303500a494541044184003480504101304250400b00f00000741d4a0710074490290044103074107802010420080c0c919092a440101e10342601d4016906504e40741e01e56443c01112811070680081c2003444244240481001c1103411100c1c804001c40c41c0c01594035072055030140c42e039101c12801801000140da40b00c4240072410418200192464070020500c200107031100d82030041141c85001c90401080c440e0009003100e01030004040000c2c040c156010050380a8141c2c079104485080c803e004118070140b80e40516101c8900c41e1310741c40c2c0300c2c5040c08144581d103456136441561503d84001c0811000c4008190742c0c04042d000900d4422003000701c44030030b40c41440881901900d00c40014000103140d4440041c2c1017028100e82c08042c102c151408001e01c8104a0140409601c401c1401c0c0c1440d80c42d0b40030710500c810010303007010016002101400b12400200e00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 282900062 1250 282898812 282898817
    0x11b0f06151401080a06050d030309060209120f100903050d15030803040b0402040b011b110a03050a050a0506060916050309011d07051216060c1103070330020c10050409050106 77
    0x90b41244903681200425500c90404c100400c50306290a00003a5030340d0304224080c0905035102c1a0200b40000e0790100c495503403002c0c01101c5000c5001c0d051580d81c0c505408213400340d003d0380f5201000f544075401174a04954140d0b0743e10741010300ca81450030040502400d1880740e844d1107500000020781410145125030b0013524409414505401444166004a00c102e4104202142800e1080058031600301c1843c0d00948a0044006080003280d5117101541000d85184102502a4104800010762120580c0b00e181a1303601c684851052000502081c1e50034144030301d0001136003004512590103507611900000000c201001386007080c0d400d045c0c513460803501079013022500f4455410f002e0580c01140020100034640c000546c07880514100190003036204201c441c0704a407090162030700e03203100806002010366001c5580ca1038850002c1e40341c01200d003101496000240c8000f00150940f4140c44500c0c2c0143c80ca1140c0032081050700101e1440c40e5050003400d001c00700701d0b46100d101d01c0380641002d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 282901312 1250 282900062 282900089
    0x20d0c0302091011030a0f020c030303092104030c0b09040906090b090106120c05010c05150a0b12010b0d060f1103040627031e05070b15040b011b0f0615 67
    0x14001d01100084440402040c880c4c821841c03440680c00100300da500c11082d241ca0001082101c0089051031000e0701241d070305100c0442440790340e02c0c1c003203102c03081b9041700340700303c1034404400c8586a00da00440c4805400f842042c0010010350844038010b08031290010400548840e855695000b00ea80e10501a04c101038510300700914101c1c03d1040381c01502c50b62440201813441582c0344c020b000450b00442c1d0400081c0881c0c041007160810002e420b46010000c0b0000c00d10b89084a60010000703c540948100d500300da80e0707a0038000c1032281c890180006013030750740390350440d489030310140810726641e0750700f240c1d07a00e640315040903040040c5010b50f1056501140000c04a80d41d0100703042c001c0102c03400f141540f01501d00103600500d80240543e400311400d500600201400d980c01c3c080e04902800c038070107200400060b403803d180d0090080b10100c03410048098a0801100d01c80780d41c10071208404a06803002011610050220b00c002d44100703c0810030200c1303041c41650b100e00f183c3c810702181410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 282902562 1250 282901312 282901327
    0x1504061d0705073912170c0f0d080402100c0201020a0605070e0d0309080111040f060c02030109080d0504050601081c0804080706060b0421020607020402090f10120e0f1f020d0c0302 79
    0x1040c80e14401040d00d01707914003c00303010740ca0b01c40380e107200004050761200d0006070441007181c0501c0a120210543e40554a44030b20030741c4042c3c02d010040314100c0c826000380d60500010350181404c12041901a4000e000d2008180c1d031319001000054036000c05d000800303a205c1c0b001d558503000702444a20a642d04120300749000703601030940e071404c144008034a0050100303010300b0310004181d0f0125a450310b000007180040d8000b0070300501070200050300303a8100140a00e00d1142c10b4001c0c81c0650310410031624540c1c0c1c0c1e81101500c410005001a0a84155103a00408584aa545640c00038040c6408901c2d244550f582c0a007100c01640c07104a8075840803508112403035400d02200f04010308481218400c0b0b209074000354442c0b180e1710000344070329070205a582e1b083e15040c100024099014044622040402d107000d0003500080e4400800700b030501c450068140130114448020b500194010a0036203038800486e103031442e03a040445000c683c00e01c00c44038861150302451115606035100185d40700e01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 282903812 1250 282902562 282902663
    0x12090114090a0506010f1d04080702060712080f070806190b0406021606030e0304052b050609010b0418020120030307050a0314100b0c030408061504061d070507 70
    0x505a11520481105000c10840c4504140c0302c1f92080580310050340301540c4034540000c0074080c2c200013a40100f0040b0302d010420036126400e0002038400d480f104040d40d1140b01445034040c00f180c0f002c0c00208281302240840c01c0c001000c208900b0382c46100c200c415150071106080c4e07003082c0e11000050b0b200031418160b00d003010354807401030201780c5010310030720380c4158130199248914410b26008112030484004d10b05100c2112104040311761200c5c4501c580079041c082da41d110181d071070181c15460910300c0035140c6054414044081d120051045911146030010742c0d5044a00030070309940d1152800004d4500700510007075100e10100d032115a260f900e0903500900325540e48a11252141c50342062000061350385484130200c0b00c1504030b080e80c503020860502e0550003154000300c4503100703100500c48013424548400001d42415141080103903940c05003101d52002102025510025500104554522a1006046180c0501108002480d043c0145603251840050301130351040d40c2900c010442d007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 282905062 1250 282903812 282903823
    0xb04050c0103240b03060604080109060903121404060c0c050312010807060807020303060f060d0204141c0c031e0b0f04020103050903090a09023018070b12090114090a05 74
    0x48210040700c107900580b80b403185881070f0780c01152540b0f50003000090032643c2d043c048078003400c0c0c0e01c0000d000c10320440c0303040c80c0030701404c02c011404100204102e024102040c0301c1c0d40091708402881caa4280c135507454107001005a11942030800201d1492030010034030420041103c8924007910411561406212a09001494025104102e82034040c05020f0ba4004280ea410840450300ba0801e00b5121001480602c1020f031410031060012400040300e4000e104410802e91701a146076044e40d4000481c0d46016000c035500174800d50002030140081a4813402c0110304070b4a03441410011101d070707103810100000407140c075803c9041c08020802156403501800750040d910350021410240c1e907000103200420720f40244111340b03034042070203200c1440c06401d070f21140b0045400001084c01021400300100c4080391f481c03a008100103840ca03a140c00009072401101c2a0282d00f6040681c00b4078890382ea0200503000718565929114049a41d60f509105940154400b100800c0d2600c80c600d41142402c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 282906312 1250 282905062 282905081
    0x11070e01230d031d0d120504050411090d0312020d0504060605040e0c09070e061b0d2304030201030f0b03010c080603070617010e0c1b0706080a0b1503130b04050c0103 73
    0x4003500042140040e0b00018a0500c4c0e1280314608040d515010b0040b408082404030301134001c1911007407200c08650800002d0095400686080c085511855120300643c0b042003055504200c05544500201e441451389442e01c0d161040e000d490100c54840000a1b03880655061f10850b98424007000b43c3d1a191041c9070303d00c03c10a0240903007190b550002610004000c1c03c10080c4980804103140a1342e4110446103002070b00a0012000d40a41000681e1a110113a400022503007001c1c20020180614501681070041c0c90b00c424a01402c0d03a00460140080c00420b42c01140c82d08400c8005503003e0181107079402d665541d000c100e00e010001c06150180c02d6008005000c01c030001c810088400b0304040c1d0550740058480360050b07c90004040c60381c13080840d000345c00c120b10508403112242c0800e80e002241c0441e61403050030346030900c4400880e5505c411042c1c1c003501c001d040301c2c046e04180010350360140491110340e40c2e01c81079480e0402c40352000c56080700da0750000401c0b0180380da0140b1030300882 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 282907562 1250 282906312 282906319
    0xc05130602030406090603231314060915010b090f1804050d030516120c02070302030d110114070f0f0221040f060311030c0702030a02060a0c151b11070e0123 69
    0x108001d07080c2c810074000d6664400445c204c4100002100c1841d002d40801c01c007640420314400110892020503251132f42920f140c90507010b0068400c421400140a80d81a16507541c0c0091520800d9010441280c002ca0318454000d401e140d00866814110300385184284c1c001d902804075046650780c000e003101c000820703525030b542c22050740002480c1c0c85500c0ca00b064902c200002401101c200d0180d14022150344029894840d41000701c0705907170701420010711000340000901c000040c5400702088c450045585000048404911883d0140b0421688400785403600658400d8a0012550340104070908012800c950000608000c1510050301050003004a860300b0082e0381081c1004481c41c1c44050401284084042405002c0d960b00380507001c80142c0c0141010b5490038242009040641c40c400d081d03a140741a103000b69a0301c55907000360980400d403041810011654040c040e2541c1c152540141e84601c00c031003001c604542d50300e08450280c01c1c0303e2070302590414511440d074402c0b503200204502 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 282908812 1250 282907562 282907571
    0x6160507080d0603080c070e10030b190e0102041203020f010b0f090415020d050f130308060d053a030204031a06180a0b100e0d060c05130602030406090603 68
    0x10154010199008907900101c100c0c2d0780c41c0c4102d00d02000d460b5940010b080304c203002035040d803000000100c00080786c3e0b000038035902c0f82c2d540140c0e07040c1c41ca0b56880b010f40b048041c00c0000d0000c1c5c283c240301d200c4800c81c0400005544101d00319071801c98200703030025400d8994986402d003d1680411000c203175802000000e000c038509070303c049070313a24010300b0301d00b4060107003203000c6401c10a030000c404542a010b010b0031916600d0b22001e29020340000d0361020780594520011400c812180c184108500741c15450307543c4192204010720150b80c400034030682d4240990140102c007100825100003149200d2042c1003290550040c0e44c4003030050a0580f68241407042004100082e4095502d60719400703000204a16540ca07c00407550107800c924408180b0400c0104010030855aa40b00c01200300042c0c65580004d01d4a03002070b500110f0542d00185d001d03494103d40d00c0001c040da0440c0580c030b106440c015080c00c0035600c8800039244a50070980c00343e0004542840740e160b100f0340e400010941407800b4003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 282910062 1250 282908812 282908851
    0xf0b0f0910090921080103030809060603070308031f0f030b1612020d14100f0b090906060a0309080408010504150908092b06021b0a05060f06010e041d06 67
    0x600c6028419260702e80c2e181c800d82c0050001101010340e1a454103076442c01911603c0c44002c181040902040300403c240001062400030001031481c421007000e8010410710b410354036003045a40008020001c40856510a00c078403041000c2076034000c0884030b0050064a05610b801c5c1402d460040208000c0f096080d004032006900c1482c06070307058849480143d50301810203144003d00000c04114001a48000c24007441c0d4403070f842080111070001d081800c049490b282d4001c014880c4014056010302c00320040380b030600c1c01000601c052031180c18000303410032999603a01305035000742d0b000b070400f070350b61b001000240003030f1950041480408042c10001808107a48480031800380f9044a800b5030300000c0c0050000100300c15107030156090310000003035070640b460208003a6100741c02c1c00014241c00300c031300c511904001402c002d909078800c014028690f141105900418070091049040265100f01003040340c40300d01c14010703122070b6002184103c5c0c2000396107516000024041c20a4040c9a64000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 282911312 1250 282910062 282910081
    0x6060603060d150213080c040f06060e0910080105040f030905030a081909050603010b0a03140c0405060a021203070302030a14010f0918120509010906030e060a09050307060f0b0f09 79
    0x302d540903030000c2d403a45581460780540c0002d0140d4074000d2440d0306100700110380b110300041c1514000104643c03e001c4026045103c0e016180f2911412020401c80e6207074995500e0002d00c0180e0003a0442d28022840c0d40e034901d4030742561003e5405650010001c2d599206140d07011070010f010b000190000d110b9496166500c40e400d00c075910a45c1d090700d40a10741c800c8020b01c1801210700a2800400d0741e81c61b561200b11070651035100b001c0c0000401d252078201b04103001e480c803143e8401c1d60f4203400d4500349842d01b4103014469110701d41000443c0941c496100402051602440c0a201103a0703006880c0e240a0115208503000500c4c0303d4600344107600104584a05040c440d420b660380303484082100011114081d10684103658010102e5025506040c0403a500802505c40d502003680c07000421950f07560140c0442e500c140d90b102440d0000d80001c1e1405a1039000441d40911a2044903d84082c945401d03088411a1000f0210140c5842e01c43d5501d00d4400700c1d8402449007103580f54441d06190101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 282912562 1250 282911312 282911329
    0x403061d0f0d0c08070204050c191403040224030c183f0703080307090e0103110906280503010c030c020a0f0c0b0d06080105070f0c1115040b09030606060306 69
    0xa41d010000f10808030810005a079085d00d0340e8a901800c20311130f41c1414a00141190404038040340c000d000d900c1071a1100f4425240c07000e4420142c170790180746450b15000d00030181d00000b1040450020a811496030b0304540005510420048105688580c0c40145400c0b0840031503490603c540d85076031000028048200460030054840040d4800e40098112a184100890120f258650050715030010502880b20029441180d2555442407a50389071490a0000f036000c0c000a440302000460b00d0245003060000c06821002c000c0840010384044950400c6030b4199100c0d446002c421608100410b040034041d0300044182c60a06000d06035000e03100950700c0071348080c09048d0320a411a1f0b4024031035607030752050180014045403951407114940c00009040e80b403148003101e40c680320010754060b01c900609030648009070740d035020840c466100d1492480b4030920b61540548030b4000040e4503881c0074020001401038182071a10391030b0000c10181017031b40081c42c07a80600820020003103203a0314540c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 282913669 1107 282912562 282912583
    0x8030f10050604032901061b03020705060a1d03010209010e0904020a03020306160f05040f150306054c0503192c1b04020a020a05030403061d0f 63
    0x20170b210064003d124240018450030b05900c03a01080c0d0414024542c042e204031601585c0310000105036510195140020a6203100711401100e0000144190301108030021820070b0010301c0003915003a03864110310310a00f0500001001c6548460400018680240858001e8076210309078810090b1200c007802e0225450820040145100390119000ea800c44401002c16a14004424010726000000d00041c55205d4001040d40d0300d440003007003415040380c100d003080301560341100100d030b0781001112107040c284080603820b62402d800d600a88100a441d1240e9617036614422980c2d29103011a24031800c50804410701c4802c1880c20710071031508103090008002050b030f02c0c140c55442c200c0001c14032040c401c1000e030540314a01a070281200c200c1d1401030b01d0000c4000c0e075405065900070340088440995030fa001d8114000980500b0300c64460340402440302c8000f4a0660703549000001 = true := by decide +kernel

theorem cover : BRFrame.Cov 282733812 282913669 := by
  have h0 := BRFrame.cov_init 282733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 282733812 ≤ n) (h2 : n < 282913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
