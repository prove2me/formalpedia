-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3937
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:06:44.428997+00:00
-- url     : https://prove2.me/submissions/1531461a-1893-43b3-9de9-c30611bb55d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 707913669 ≤ n < 708093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 707914919 1250 707913669 707913673
    0x7080a03050d0204170d02010c05070f02130207080d090c051e0d11060406020a0b070807170403030f0905031308031309050c211608010e0f130b270f060c0309 69
    0x170340320003484000b030b180035002c170385140e014039034003085c0f03039028018140044190b00b8214104001601ea100600f25a40b1000784610702880504403480460341c1500e0700b03035801c40a42512a00c2c44000307031f00203080d101e0b001d5600b04806000007600c2e00d442c9a05034003c002c000d140c00740a480003014070055103004103080341d00744c15144048016031070300340c00780c0010845c0758014507044810342070000e5000c0018060784d013040308000400c24420f070010390000108085540c40c503920358450500310014624007604007191400e0200035024000004081c05d81d15114801e00e604190356584081e80e40d2141e00fa0a070a03840601c2d004000d42c1c64a030348015070116058021620f07040d0814005c10a447d02c070700b540352110780c00405024002c1c0560104912402580c14a108103506000031162003800c020a00140781072007000141d00031003100d4a51440300d0307125600d03031a6820074120310655481c000b4400c0440741c9855490064580c00081c9203c89510000050306003502c60703004d15480c0d50700c0203041d40918 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 707916169 1250 707914919 707914927
    0x31b030c1101091e09060e1029030c040503010f09200102070f0b0a0f08010609050d050312010f14010302091011030c0604050d030b0f031c03090609080405011107080a03050d02 77
    0x120400c4c2c0c582d2080514084c80c24052600346008001210b006e82c0041070802050810090401ca580f42da1009451482e91b01000c029035502580606402c2c0d00c0c0d0b9654041c10100510124002400140003560001c0f0000c2c8a100c8981100300201c8481e420058000882c449075403208a56a00d40b003a00c180341032064413003480e1600408442103030658000400c0d1540018420000c560120050710703c0d070800c1c41c0001c0c065240c90310061119545003c0c00303100705403081c500c80804c03800300100e13031041e104012003031240c1d81d603040243c003070103641e11500c0d2696a011104401030361113442110a00300004007500b01101c1580000c669602355010184002d12040003540c0f001541000001e1249102d01c00812100507003042c02816580720304044c500800c010015a02e140c3d5011900020241ca12075404074a14107051088004c3c180702c80c4050100c510b003600c01c0062080317502c002d00940b81c080c3c9442c11344985100007596944484d20a1a081c0e40000c00040300081c130841c010009010210000350070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 707917419 1250 707916169 707916179
    0x6031b18030f0307110907050f130e070903050118030503010e06120a1b14100f0203090a0f0503070f03050703060c02030d0203010815090327150a0804031b030c110109 73
    0x42c00d800ca4200111a50002c102c010400458014034840c180050720b0010f00d5040248024115001d05180ca89105602160980e005001070352424002c02d1200103540712411f19030030140081460b400b0560b255405c2c440500100c0040c412400c0007503601d9510f0916503840c00d01c2425040e0720251600703512041d12110000b60103005c0060405031070040718564801c0032074000c000030b150352660010180e55840d0741d13203600d150b0354072000300031000050804070315000c91218224290f201e07800c0860341c4a03025213004a0f40c400c01391101419104260101c504154444a07000d6012030180310040180e40207080c2407002883d0783d040710500350058011a0708010341101081c0681e0026040840b05622444004504000d00c20525401c04a580e0181d8078082000e02000712498035203400c101404501c00520f034442c0c4a01d02d6624003e00c620320055100c00001100a00030441501c0a5002401c0040100e0b40704882000803812254940c458602c4441c1966900c515a03082e04006411f2088050000030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 707918669 1250 707917419 707917423
    0x30711040e120d06050405070c1b030221060a090503040605161e1a040302030405040e070e0703060e0903040602060105220c08011d0f040b06031f0f0b06031b1803 71
    0x103200c140303900464480c1240b07081c02081302c000e80c0c00103100b41c2c18201408407150704100b40307072107183d0424680d40305000c0344005a1210b000641c0001d400c0400305101900ca4901924081d44c0c49150300c06403842601c1c0c007028003094424100380680160002c100410446002d00300030b09590391510000703c2943e0040e26074405031910003080045070b9898100c010100000c42210041c030064001410000f814561002596401a4028280580c1da125444505603100304001c000504130100c62840c0c0d8505900010060182c0e885200d42c0ca01003080403c6c08140d01000b81e509890740c6074018000d6a203000d00300414038118100303000d0350103140250110a400f80380540741c40400d541c0c41e581141d514000841c000d0ac41201720442261040009025070115403115a0707800580055900d55107807100c1c00002d013041e05155080e580c641d90315060149015003500191601c400050041118003401024000c052004543c0160188010300003503409800181c080c0c0066001c800300a10300d01c80d07800100b4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 707919919 1250 707918669 707918683
    0x70b0304140118060f09030905040b0d050a0f02041107150218061813020f030a2304210f0807110309040e0304240c03030e0a020915010f0201050603030711040e 70
    0x4585414180403000500c5502d014058172011070020402600480381c03801850f4402c40d00a65200d15201d400c58407660791440e160428103600f005c03d41b4189070042c606015003010b40c41d8101c0c06a410944103c24207040e40060750001900520001503400e00e0b405118000e501c128403407040e8014441070314600384c8401d0050603942d400005d510341400e03203003000c10031f54044101140807058010069902d6041200e000d80360401807103070021034a02103400d0000c07034901d81c4000407029104154208020701500d002000c1c0340c9a15824604101442c1884c01c81c2c1034001d41d54403c0c08030f0744800c0800c0c0741a01c01d00301c80e20200610700035207080007480400101a1075039420403400b00e034404501032251041c80c40040682100d0709088000e40313030307440324050505216840050b05042e980e840d00e01c82201d0138400300700803a0b0b006190001d00c2c0707055544440540e45c0040081d00080c107000d03030700140500502c5482d002c1c80d0010011410032580f42c0e260001c0d1501148515006619609600c0190400308602 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 707921169 1250 707919919 707919941
    0x31b0c03030708060a210228061403130b06150a05130b04050a0317070605040326070e0f01121401150e0f0105220608100f0503070b03041401 62
    0x91541c030700340700100800082e4090b082901c64105000c0c104100c81305603035506c41100400102d0b540f106421b00001e01005451f041200045500b00d011b90106035080142200740d8407181c031840544850b140140c180d0b03020444444414141c080e50341404110305030346c00c9501c40401003c100705400000b0104005401060000380820b0300820b1405940203080510b101a00f80781e08914101868100002c0c00540c1d18400980103040c0340703003010791824041040b90f1551350400b4050006051524004001180143c20103084820204048050340414603a0074020440c9903075417a43d000701f0504010b0018040d0400c40c0c14000220b0b0b014801100f80e01400340c0c0c24021041a198541c90b1002074442882c0000180c010401e0f4910481242d940e01828040314210a10f059503c4620041c801c0c50810b04005c00c120008bc41c40d00b0004a040c1d00078601071040346690035000c4c80365074803551007021500350301600343d06801c62901441062007410245034010b000b404180c100c030b0307072402c18942181d400e40350f2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 707922419 1250 707921169 707921173
    0x160501091a09070e04080f1b010207052d07180b13050f07080f0c0d0902031006031407030203122805090315090a0210021f020d11031b031b0c 62
    0x204210414188a00001001030901d00c038160b14161b990f00501d813244d814480e041d13801c0400e040c5060703046102d50700b51040031113000710754690140c02c00680c0c51b404c01c7d1b011003201d6102504008019072110140000ca2100c000900843d400c0c80f0352445003d0749d5121030031225a0303071302c145580f555801650b940040188003000134107040403007298800c5403008040344140060304041c4800104155000c99010b03512442b000e03115071039101035402030627101c00041e5052069500001e1003000c140c1c044000c482c86800064130503102c02c0e0301d40e51110a5031102a6141d0001c070180e03141c40c40c052000b00341444c0181094070714951a0180860b401d00e054098600040c80421059a142400c101280750100c2c610001d00c0300340742c1226900d50b14080e00070020b000c2e40d0702e007840181703c90003080140428803d44c01c0100d0a01070a191000c0290010624400b105003011f4a4152802c15035085074010b0681c007408006c08590301c2a0340c543d0b90700c0989018804090081c501d481c1400c1c41b006400c03042403600c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 707923669 1250 707922419 707922421
    0x609162421021308010506090f07020a060903170919110d06020403030c110102010204030209070c0317012306031302060f04030c0b1909081f0b030607030c1101050c160501091a 77
    0x600030380c2c03c08181d000405644c1c5420309104c2907a84042100d80e00c803030603584801840c1e031619412802d01c070324840002d102500341414401003503007100c0f403800c03000d00e00c081c2d00782180d0b01c80040540c1c9007200034600307047c03901003001007001c5084000b94280034000500b40c148c040410781c4c0c45c04102d030b002d98400d800090352400a42d040015007404051068004d00c029424542140c001407000d20020b4100c5041c402c0803102d00c0100743c0207040d1606180d41c1c400d0265110343c0d681c61403601005111150422502c181c0358002440d11303250040c0c030b0041484603016a5840020f42c01d01076554419960a4940d4400784800400200700307440410181600302c00e4070b504d4040189000c003c502c00100c81c0b600b8400185414014030038002a14405442411241e641900407c0b80481c01811802d441d181c050140070304200c0403e82603041030904081307943d2a04800c40030518240d003264019035940c0103900c0100325070307032030f691700c3c4076007944070703038000d80000030115880d03030340c0382140782c1590042d110524540c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 707924919 1250 707923669 707923687
    0x21e1902060a1407030f1820040203090d051b071401120b03060c09210c010801060219030f050f0a030501170a050a06020705011d060916242102 63
    0x200401d07410100c010030901448040107062900e12000900c508200760342d550304615041101c1d0840441900070020121580d03a00e414550b6045005a64100c0d10558104500710780d42001d00c216441a4100000761404012514046906500801010103410100c2c140c00813210b02c184140e00007420000560200c21f0304080015042040e030b02100b459961410300492020344020480540c4101501c0016a03100300c50b400040c3c0c0c500d04000c540c000c02601c2644500640740c00550f00001036402d0303c2e40c400c44e032303645c11307089a803841c5001c00c003260b412907602d902c400a8000c200742002c0d400c1074100f203402d1807440b100201c41e40d00005460340c0001d40355030040008413106108252000c4418010b0410340c0815140c1d640c1e114078a59004000715800914901400801c0d442110018080030501c41c00700d41d07e0344080d40d590b40680d0180c1c601d01411250582c071486464014045600c0344c070305003401d82946402c0c00101d0011411079010b100b440d01904950600721180602840b104000050b1104001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 707926169 1250 707924919 707924923
    0x308120a050c040b09011229030c0402160f0303060b0c030d0b030c15030408041511070603141602010f020f07031416021005160f05150613021e1902 65
    0x50080c8a400500f04000e0011010b44000c840307101c2e400b07080509010320701079046401011601512040f01043c10306170420300109200c196106a8100e01f00c0d0a520084400c00040744507041c524807141050410380d400080f40074041c2034555000e410f00180d1580d4504e1030009682c44060101c01c5900300040b807114028884c803964103110010f0300105400c95204010070003550601300041e20b042008000901040040740441c0e0140040301c9100d0415500d184000d043c171604400711104034015002e020034024030910409075524403501510041e521106441e049680300000a04110754a52486204000c002d00003495824080090683d41d0916400d0003449800c6400f00c4e520f00c6032082015103a18401e1800714020641c044480408192081c0301c2a1840e1203921171001110080b10555421711040000580880b4020400e45000104402d01000d03482400c4a13031540c0040244000300000d5201e40c058042e41c4445c0405030220030a1204000356a00400d040c85100300321480c4241f500741e41 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 707927419 1250 707926169 707926171
    0xc060703051f0807050607020a03020d050102040e1b070b0601030f0501080618160b0a3e0f060c030a150e040606080f0a2d060605010e2b03090308120a05 67
    0xe10140040c0e5075050125450b04d9414510801b0710401021a004095560b1050100001c6074010003500201c0600d18045010390080c2c81481c007d07020340f0f00058490580f1654003d12000c5601100b0310340036499485d0342e055500502000d04255541c648003000240c10b22942c1e018144001c010450f0b48bd0882d100c446614000f84a84140d0b00072142ca10b003500c41150b0103905450b80020510344030a24640100c1c0c41c5120005100742451041d03019415480e800007000c004192001804c0c0010720b0584c0284e031351140c4008804210343c0c0158006904840c5960145400881384000030a8007010385035505d00d0040c0702d402148894120704140800c00507680b00f07010003030010102030f203414800d80c80f04a450b03940c5010f000d403034590060f01a040328614070340e500c04901458408065903c1d0142452401040d550284a0100b00d00481c0307540285001049242800d4015103188200c42d810002c22042010b01c01c400c90501204910110020340314502a01200620011400f014030305043e0100503150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 707928669 1250 707927419 707927461
    0xb01030215070302191716060b1c0f0c0503010e01050a050601020d050423040e1e01051504020d0b04051e010506090604060f2a020307140a060c06020c06070305 70
    0x7070108003400002e0380206014911241c540801c09000d01036080c14102480550102d40f0001e20003c2c4000c00b0341040c0b540c03d040c99001c2c0c4010040c80008805100c00411102d1240a682d40d041035010001010503240c4e1004d203200380e030707280e007160790300d4010a080d504e0703409d40d0001d0750f511041080101d40a074403a443c2e21100074402444144200d1302c01074040d10403409544094080da400c501742820f0319005840e0599030203001000420311041140382c03110b40d18072381c020b40800700906c0307a40e41c200305000703183c0207104080d2a0350304c00c481c003410080294007142c0071080f0191030f4140c0c420603079620b1203610b11490400c0d03039001420b031a0411020003090144c02492280c4024480341c8090b4441c00261410741e01d690819011034840100c040e10050160300100d902820064008074003a00f01e02030f40407000e072003501121a43e5495098000794910b8030521316400c03148611042013010312550b034805020b4011b8800614241c048107181d424030030112003407404651640240300310301d0900058020b00c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 707929919 1250 707928669 707928709
    0x90506010f090b091519081509010c0906080a0c17070503060a08070803030601051b060c0d0c050309030d05060d3c0f060c12020d06091d0d0305100806040b010302 71
    0x11500d1012800d84640c00117285001c1c8509402d90702d0400700b04c2c56208041c01030402100e508103050820b001c036004044074100a15420b100596480c01e000359060f070107440141d100e000566a841e5800c40c01415584210010001603190000c03c2100d603094590180c07a0355514542d50b4a8028107004001c45203038000a01603000c82e0042096520200507660040024179145070307a5001e040d41261048403580005400e4002c407814400c0b00d052100003030000d034003003400a101141602c0010b40745030100302c41b600d640d0703002000b87c40b552651a070303c03e5a1000e401400c0c0745c8010130585030020303c0801248130800b0059818140ac00400c100c1c240c00044060f07010012040c6132869541c8400040c3c07083c4005c080700d8961003056801405030044030100689983c086403240c00800c8518098032003440f5982042d8070f40440b6428520b00080e031a400a0420301c003c1003100c10b110002c41c024a401410205c0f0707015072020214404600f07000450245028054049a03035045004218181c03140480da0b0101d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 707931169 1250 707929919 707929921
    0x302150405190f02060d0f1808070609170309030406090b03270705060c010203040c050a0b18060405040609020c101a0d06140106110d1d1003090506010f090b09 70
    0xa240060500d485007002c802140088009207010444055003620095022001280d2405a402c1a40c000c0b801c0c0c65116034140484d05140703103000701b0104003200140503440300f0001702c004500c5680001084d40d215802554048154641c50380302c50b001a94a0301090300300040400130039610070a010302406044550500d54200190b0310a000300c40510404548000c011034190056418014030f801001c01038183d0307a0310360300862801d000750b101710f45c105c4040034650b20200c0c5a05161243c20195800e00c4d02c1c01d8600200301d00d10340080d245003514140e000808210105468803507004a4000b0500200096210291409400d00340300802000500e2149000c414041c280e03400050302159400560b4240b91403501030500c2c5010b0014280301180320f034640f0300001440c5a01c5040105503c4400040c4c2e0101c100b9074500300da211500708070790205840c00f011485840d1800b148041c0d0201800c0c100003480c0700c1c050380c0e8282000b00c241d216503540e8010f00741c10084000365000701c0301e400100321040d100c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 707932419 1250 707931169 707931173
    0x2090106091805061f0e090703020d050c120f181c1209030f052a0a02030d110309040e0a0c0b0a02010c03140a0510090207082a060105150d0e01060303021504 69
    0x611240142c10801901c00400803a1550b405a41415203121021f05407403140e2403d50b02c00f801a6006803007010110346450005484508503406554401100b06204443c130303101c2c4d0902d800c5c20381d4060490103903501c40d100d40d0f101e88030040209503520030110810b41683c80503d03e018185120000c520400d00d1f040030400d5001a503c02d9000820a20508003591550381e80c00811041014207804a40290340c0c8645407030f6408800960b02106610031000c40e07000d8240d86d0802c6a030300c02d481c54000f806034424004994946025004400108c1d0603000700d8022400985640c840010641d020104440c8000703a9480b401c2e034207020b03044020b40c06040a20000454100c0b43d080d58100070200d000c0903503500045101001c00790014401030258440c1075489000b01d05000d1101e501c404c0c80b04100e44880d010008070130b00c0c071800340c42401060001030005030b132030081032002d09000e01718000c0340c1060810980c10f0084070342c400c01e201d001c90383d00001505403c51a01a2410644408034641d0807626410400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 707933669 1250 707932419 707932429
    0xc01050115030b0f09060402030915010308090a050a0e01050d0f051006230901090509030f270117040605040302010b191d0f310f03090b0a050708160209010609180506 73
    0x6e0070000c10344005a0f2540d0311400c2c0c82c20610075000c240c0410315490000008c1c8429070000e002c1d41d1508a41040c2c241e5610700400a00c18601c1c4108040d00d06001f004102524042c545041d03004d0080301c81c100080d0305680c81c0c60402c0c1702c901d401d24002e544d80f2030a0040c0300540f00e1004901a06a021820ba049144005145107c052040400594903138000625070041802030b2032034521a4481c1507140d0714011014500c10380b003001107014060700120114031941c412066802503079015a444c020341d4445032101005400020403d40644d900c8001d00030282d03c4070600c4070340a1003403444c100440d40c00c04688100c3e00304800d019094140e0501c05208801421042480c3c11120700c1501e189800949841c0c0119000c0c1c43c6401680c9a0108907100280000c0b2510f04401c1b03031196035141005a00d8003001342039030041d99010000688140804000112000c3c0103160116115900364450f118a50029440507000d070454400100340349803c100054814180c1c62400f0300c036003010b00043ca46080814 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 707934919 1250 707933669 707933671
    0x10b0f091201060b03010608040b060307030c030b060102120c030706140405030a0813080a030f2406120f090503120702010c14090103091506050102120405240c01050115030b0f09 78
    0x41c480c80c10320025080c0d1076000d40c0014000d14116030042d4503036135113020103000070100300d500391014801200042c2c032500c1c001c1480380c1503d034060034220861f415620b8002001d0030050126040d4410402c0c840001d1140a020345040c1007044010341d610b42c40e5140600584070046400d000307988a0509000006402100752029001c00d440d10010300c0d5038080442042c03003200c50000d01507090009540c40500d50640095841290344036060041681080c1c034440390904201300e46901c072007219070078021a132190a1054030b000d4403c2003c50a00550f1050104a030150481181c640e4030000358012844441000264041c26900080040010b50030001e89444c03040f400c2184104000a0402d0481e030007070740603400c01c039002600d0b0100080c4190f2004010a010301a0a001d03110b02210382001003145411a000d0310400f0b0040c40040d1141a80d41500076072003200740f04207400522101d400f0746000d00c01c1038001d00c9014024600b008103a00c001c3c007100c0b1129441c07802080c0b080030298403522901304007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 707936169 1250 707934919 707934937
    0x6060501020c031b0907140a180e07091e0504021b160e010e06040e010f05090c03030f18010c08070b0f060901030807020118120c03050f150a0b04020f03010e0f010b0f 73
    0x401081c0d902d200382219410044149002c0b08240802e8040e00700b60b01c1203a13070f01000b90804d105842079441d0012ba40300007c2c1100d8040018129080034030041d480e550030f001070560310841020782c00c2d844200250aa0f000701c9442c091001c82c0c0141f4015114040111562031450305201800303540c02c000c40a503020b001402201e180c044000c002c980746495652140303520250080080151285250006d0007030603007603072520624814807028120f2440d0110840307030041c417440502d130720305040c6600407850062501403540c14040c00f04000c10101d103103070307000305001481200c0008081c038103102c4010410744040c0c0745c40d0050841d9001800000c040208440e80c0b2502420030030540c10070101402016121034000c98441c04120300b200c0208403080c101c1605482c450001c2d540902040c5114030740c0c81c4545607240c1844803580010901859042d4030640c18058040d01c003503c0c2045c410b5119000f030b8800c0e40007424004c1010200180075040716525070140181080c09868041141e0314000140035003010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 707937419 1250 707936169 707936179
    0x4051b01051605070306090f05010b04021804110c06040516230402220603020a03110c0a02150408030315010f020c0306011a04080613140f120a0201020909010306060501020c031b 78
    0x2464103015040292138000e40c0d016034140900300703440c035040c003840a5480301191258240110b500092401e8001d079071748080a000100c0c03036901c3d00310411024001803c070070200418100190b0040711005d201c4a4881da00403001030000c9e11000d644c140d080025540404825002d001081071110102d2040f03294403c0210740142e19a681603058010440403401d00e014112118040001c2c015055006840d01c0e0071a5101001694110356a0400a03c83c00461003419040365103000010301e0310410006030301c01042d84090a0503100d20006113103920503034050303030700001ca801d0880d02c3d90b901105260240c0054400f8100c50540c40010a50301e1b0703010b0140180d00f4045406d80d2880180c8107003620000c0c044101291903d00b0014000c0022600c411000d540580b945646580c0c013070340014184110100d5030001b481c00400402d1030705010381000d0100000c654080060071902d03510700c041c86019500514000070000d1600c0300291809200040c4113009401c407c604043d0340c0940d0120754000d40d0281c030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 707938669 1250 707937419 707937457
    0x3060612060f040c030c031808070605091006060822260903060109200a02030a0f051902150a2a090e1326070f170403030804051b0105 59
    0x9000101007518040d0002e19000311042c07411780c55003207210304081c1500c08100590700013000c5094000c0b0754034040e0005208002000c00910560311055100e9640d00954940009801680003aa8600c1d888400090240410312003842e064480c0701c0b03c1c0807000c4040003040015561000707070352003d2003408010324001d20081d02c01a0042401c8070010403000f82601d620b5078440d040c000003088190f4a140401c038080b200884c51400d40400c8581c0303074480340c0007182000520141100c482c00803550034010484144241c04010120302d0350030391080702e20340203004400103154208000000040250122a0504031140780c0040d40754082410328800d81034404820a800e0000d9800c030100d0b030300c040030b5000405d04104040e80c18201441c0d50070b01c6007440040b20b24101e050442401c940c0c802200e11030404000c01000100d0911302c2c40c00340c40c4144e040810b890780e82c1e4407806594000b0b6105030042403c20041008210042c000050141941074803184440ba541c40000c2c140e019404403429a126a94 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 707939919 1250 707938669 707938681
    0xa1505090624281403030f090d0609111f0c020d1b060203030414030909010e090a0606080102090315040803010e152d04090305190c0b040506160503060612 68
    0x1d0221802c0d0b40c0301a280050000d4442d082d41e04100000e0706668002d50b200781c01080142c0e00a00c14500684000c00460030301384011101d8850380d00c091169a402051181c502000810038090520094082c1e00c0d03000100c0800c03000d10030a01050030400054910310880c0001d6642c0140c044a04a0b40542d001d44240f500341c42c103030b40c030014000038022007000d01c401c4c00108030740d00000a602c075510a1504807500c0340100005135413402840b2940b640494484018091403019900051f484030000341200c2e501c2080307031a108201c13070760743d00110b42c5650001b544498034182001160a000340c450150065480d184d21050b8407030206002c3d1450807821a4042042c074000010704002502d4000c2449082c1c0407245c0c0d0031080c94401403141d1080c5407107860260201e02c0c1c0780c818442c9494160300c1d041d28210000f40e28140070928180c1100511520008002c00308440317610319441244110b009054a0070003c503680c002c0024240a40c003003010030401c014242d1249015648031149200c41e0100ca9103800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 707941169 1250 707939919 707939971
    0x2d0206190309060614100f0806090406021603080a0b0306130f0305040f0b040302042421050303010b070515070c020103090c15090314030f090d020a0e090a15050906 72
    0x344024001c1410102e0104206100740c810020244003191008000c1100610581d11840d5200c103d8002c40c48c0e8000044d064100118240c0e8401d200300030041c80d0000414021191552210041c1e0000e004201000841201c0344200002d24004400500c46407519560140c3d0000750820024a40c0418405c000100750050301a01c02030501c6a05800070240c0310031410b4440d41152005901c0744d03040c035800c0c54440c50b1a44092043c1405980758044460804241e9003401d0f00000307071050929051051000418070900c003850103420400343c1c06035510440c1c01e01900d40a0b003000d0b00e80341003140c42e0074000c501c1c1e045070401c42080c1d42820041081480d50502014010341a0f016211440c04044034070310312640b0429900c260f911501c003c0b0041c08898060581e40e01440041c600700c490100007103860341c503054a81414051005005032651500c810118540190070b031400c2c0c0181c0c2c00424840c041000c03910a5202101e210740c420031040c030f4110703002556514040c001d04118402c00b8010301c00d203c18 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 707942419 1250 707941169 707941181
    0xd020a050c0d23030d14010617100f06091410050703140d09060507080a0b01090b220b04090c050306060f070302010902041a1206011203110a0f2d02061903 68
    0x20024000c0c0c59929440280f580300e5200c400c21074401840d10b01c40300941c80c2505031301030581c0d00ca9a100c06103200601c204000c880405031420100880070a4006868108100e80306d018042e16602c1e210400e14010400c1e90426100d103003648100303240443c03249a40d43c0001951a0f450705032420f561b45044101400c0e15a2149044042100b07041610a1091208036086103010303400c16640c104484d41c13001800811982c01168050001d904448204926412180549030f83d601e2248001c0108a00116003d10890310340d1000342d0050000c03038100805641e500c00c18401c820310f824a5485c502e8480001109442125800640da40001c5045001c0c036201b54030900241b036028100b0449144180e100300600301100c14440e2244140c0c8020811184021407a54122200b407066079000400c142e0301590a00b2405049102510a544040f00400c0f0301c03102034201c0c1401190786c40b6450305084034640b000c803c51425903c0d400b940404c4040142c40707030421603821001082000da070400d1440011405400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 707943669 1250 707942419 707942453
    0x51e090c04081207020f0321090612011203120b01090303050708090d08040807060c0218040302160603020d24030204020c0109080c0106090b030a12032d0e0d020a050c0d 74
    0xc204109030f01282815801030038468021104001c02c4a180f00c00c0650304d4009001000722020031040d420344000c1403101070708180c1c000801080c1000d00b00c01020000101c2607012810400500e4240000c1c1504070701d505500c000c4808082c80a560b010001030801e40061100504110000680d0024043d103401500c0d00c44c03400a00d00c840d05101410509040d410034012840340b1701417080000b0b00c0350f02a0032440d80043c0c1c042c0283c0305140d1109007138000004020415029409011603103000c0c40e1010341e03500f018054980b00140c459400c1040c18003290201ca151410300440034900e034080c0301c1384000381c03811281c4c12100541c0e241811002103000d480c400c0c10080008030041603201e10042c1c19003260095035800350041006c10314240415035682c24509015205516160382802258402d410110008103400f180d03441c0302c0a5003c15100200824541c40031380341c3c1c1c0c0e208107a081c0a051040c590b8210303070351005001c0149030380c8030319481d03a801c01900c0740320b0032080700b1003801c025607a007443e5401e81c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 707944919 1250 707943669 707943673
    0x830190608100c0908010c21200307090f0e18120a0e1e06031b04050d230d020d1b0203010608070603060902040b0703030e0c0402031003030801051e090c0408 69
    0x1924000b0340607111401c54100895960a804100a401485076010500e090307591901d031100c121282c00c624039492301c1f5141075103442c2e00d51849460740aa040d0740d00d81c2c208401169030380c58120401054865540c0104001c042c13000c00c1042401100545a03405c225082c00389072001c11208852440c100941e4a0101c00070000b08600000030f4001c410314179001402e4a107800390361070301c01c50560041c05000b04544d22150034404913004825000d204880400d440d0300d401d00e4107884400140388041d000e0b0007104c042d9160354031710403441401c2c826019144c0444000f8440c500901d14080e4171690007201030800c201a9100328003090125480d84000d01c0c0c3c01800811009454000f0340382c60b402070340034001c0400d06083c4000f46004451080303c08a61010710002e0a0068070f0350100d0140c48194039281c16440f80c0284c0c21048d035154801035004001c03004c58a11b5180c036526015001a005a000c1442201107445482e0103844e030301e015442d5a0400c8420038650307501d42c003007140280601c2d00005264 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 707946169 1250 707944919 707944933
    0x901051303050309101e05010806070906110c0406091e05150415150522060c060b01051308030903071409070f12020f030f010b090a0620010203040830190608 69
    0xc0709001c1207560392000000070f0000342c9e214400f107550f4480035960380c00020004141040101d21a001c041c401e803000b1002d40e80040c4d480c000003000c2c0c900703030340007400d03820354480000d03122885002032004c19000500c0d00348400d00d8400c08103d0a08181c4040900030303a00c0e0b42d8420039080000e40c0c040083c0450700c5105181102c00b1000900b9a00503000b5140311800300c0542d001e00920592000007262229a079a03c0800030325640e031009000031848180c14040103004804906402100106c00350030950001e644a0b060703003003010301e450060381c004412007940c102027030fa054682d0b0390039550003407680c108101e030404a00c004070341c001741580c990303000a4804150700020507030f40b8000754050000701d180d03080d069881d0361841004e40b140f9a42644d000303800306c20410400d401880908155144040b02039064818011541e099074001c507030485205a002071415003c10100304030405503a0000001a01001008901d100e0160301034100c0c0e92010b6800b588420602c4207410003000303440054151040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 707947419 1250 707946169 707946191
    0x219140a0b25081513020c1b030123130302030c0a030c11092e080304090e0106090b060706020315100c031719050603030f03090601030b090105130305030910 69
    0x281603108012000c02c02e522200c41c652030b440769441501a111109140e000e51843c00f0400c950b14004c10000d11840340c00f84156034218509001c07110300840d42e5074101045030a240201806c4581001d0350703840b100300500ca54440c80310440c001c0c590040e41c1c1d00d0744540c081d1341760805925500a48480300e00307501c07941801d2020161701980d161089441204808030070920360b410088440411107954551034544060700f5218248140c070700d62110300700754036450a00d48622005080d07602503002401c2994460780c086610040034400d0b100100044181001080104000100c0c1c501c079400000c2c10392500813000c40d10b42d41926500841d450802092800200060301c03024101c0d0420714005c1d0080713000401d620300c0c1c05003c941844d12605a1007040c140c80c001c0e20450710014000a0314480d0503100910540345061481d0000390b000c1c420040c0101032942c503510300060f0600c0010302903d5164104028008000c0d8400e8102c03680c0b991504001e622541c2d4030300601d242640c11000205201d0504c104141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 707948669 1250 707947419 707947441
    0x109060c1106092a0d02100315090603030c080a0509061c0f05070504090c0905040212010f0f05090604020306010302091e040c02010204031205070503041a0315010219140a0b 76
    0x8010701a510780303958100485854072882200f00c0da040600303040a26909038010b22043d40080020031100722084c142e000b054800240c5110600801d035540e1002950144c0d04002c0070041501c02428010141107650040000130b0381c05009000c03080200d58030091038024016500b00c070720003404881d281c040c80a0320f400c11000b54a103040b100b0385808602c80c41d42c00c0030b0040a01c602c1440c0ca8841c80c0a14040f0000004d08000e280c0904000d00c11001003031982c0c90380000e12041c1c502c0074171280d0f030754100002c85950400640c0013118100307500200300142d03160b9811441e84841e08030b03801a05ca5903080010b81c064403076210900e034800c5042c0480e1141800c0741300d084410140c20341c0c08024141c0ca80000341d00300e204600024102800c1c10135690115407107880100351b00c620030000e80e030500b030b6140141c4a02114604000c85000400f0080117111499032441c60b010781c03824801401c62a080102c00e0403500c1e80d00e113024112042c02007510b00030315420094a94101e620100c04803040c50004a012 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 707949919 1250 707948669 707948687
    0x80f0d2a030c03080f071409030a060207080d05070f02060403182105010c0e060f07050c120607080a1a01030c110a110f090130020a0308090a06080106020c0409050109060c 75
    0x6012130a450042450340340e00c0043c003403050b0303407a484040d409a040742d8007501c107402100590380d1500c1040004d20004545001603d0b0852240f141681c40b15010b084107010360300000c203600c041004426050500c3c40c0e002030865040b54142c2842c24465081005001c524820740e00200c1780150424412540c11301c01c28183d01c40310f80113500801496140000c100c50307080740c064205610110510440f82c3c3c64030b2880040001500c9203040310400720303a1402150708100c9025492940b074004800b00308519800c10b902a91003c0803520030008400060307924840c414404081e58101595481030012240c0180d090342151009001110403042036803130300f0580c60191615070307400380e044103845030082c1c1040301545050ba80c03c0c0c400c8500d030030358001041e5448400f000e403601d07240b44061405005a00d4440c0104003842c0030301c80340c2d80c3c0c9200d110148034441000350300440400818a004100107030b0301069400b44c0c04403c94020032079402038107009015180000c0081e0405d031500c2c17096005190081548 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 707951169 1250 707949919 707949923
    0xa231b0106060503010803041710150f120f1b0b041e0503010605031f1407030903030c0c03020c0112111603090602030712080402040f090506060a080f0d2a030c 70
    0xc0c4407490311071104990b507000a11a0020300d91050100f489061095142c98070418100011507000d090221b094500340e400c0b4102441204120040901c1a0544102c4450280c526110a410031590a6568000c0b1551501002c2c14100801680e540d4064400c41d90000829a425000b42c4070ba0301c40b0b400e01000400300d011442480120036000401e0b017410b0003908100c610060140c5140301c14051b9158496a500c4100381c0d10340c2c3c0c0e8282c050030141ca6600101e00a40da1130790001118809860050112000c0c52540400d01c02c61040a00c0040c2e80051030703800c920f00038a0a140c0300092411044054a00320b0714910596101041d480d8034640c00d03800c2d90070700f035000b42d45940d0141e54619003a0303101d1140401c05005a41311a420001c50b0b40941e2440c0d411620107031000503200304e40081041101c40840080316039400080512032285044500d840142c0160401741c4403141d1060300365581d802c2c04403010030900080514800c0c840744914500d100c0d4083d982d501c0c001c3c61200c1d150003003040d0a07441003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 707952419 1250 707951169 707951171
    0x60d0b010e18060f0a0e07030b030f0d050a0306060c020d020f0111060a0b01080c070c09020f160507030606140901090504080702031234060f0b0a030c1a0304020102030a231b01 77
    0x107580460314007088980e0461310b07400c46c810203585494030100c0c0a0605441c3c2d4035010312594001c0e110450082000b00030034000f42c1e88203619a01101b80080039504190f00c00350400040341e07420000340e0368000044064547c1210500701c4442d00c0001030303030100c1e4240304407000d60048104008403007950343c21051100000740e0f03401c001c03a07580d4042803003603002e006409841c0b01c0d45484180041e800c241d0081ca5031240a6124504110b00103125881c90703010f49100700c0701d9410182003041005821300035480507280c0030440e00c0c0511040700120700c0d04c07001442040001a15900810180038584040b0b5503555000340c151400c10341003008244c481c0e4080100e03c0700c5032286c401505480d0551140c04c9035840403429694922a141f034030b440c000340c02c183c4404a41d0300e0741d410310b0f901c0564541e41c119000f58443d41e11070700c2c03692604030407090481003e015148038031000c0082000507a40842142c07200c4805082c850740200d1844141c02080040e0100d242c44000009415880324500320b048403142903079000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 707953669 1250 707952419 707952439
    0x607152007080c07060f020703110102120c01020a111908091c080319150b0703111c1101060302030c130908070827132a0903031805060d0b010e1806 65
    0x40121084106c008041006800c910018400070361583c82801e82900c0510480340190800d102811440d4000c0f2407190907a90300040c0001210f400c4102d141e0200e446138090100081440ca414002c145e41c010001c050690011380c0d1861561003011608034202117a0140710040c4051418070a00e50003600d001d040d407200e10344a001025100c2c05105100b160707004010310a589000140c8149410039582102808605004401e030b846081184220461907886440f909510080b805040d41a2084500900340d0603c102800541c60006008131401400c1d070b14500000000c529001c01004030341401000310400040440900c00c2100180a010350041d030010140b040403642c200e12a2604d44c0303039607000025004200c28803801c59104054a00b01101d40b041c5032040840408014040d074008180030800160003842071541c0183b25001888443c0c4448040509001c0061510700915104110039038540c612000107911504c0740e010402c4001e0030400c60b98680a05241202d12704881c2c03d400340350125 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 707954919 1250 707953669 707953679
    0xe0114010e0f06061b0a02121608011109102307020f0d0b060405092821081902090310050a0c020a030e060d14041505060607152007080c07 61
    0x2941103000703840040800b4508500c2e00701d80306501e44c1d80c5c0d2140c603060061695140158030b03030880c00e0842003810005809001380980d050b00403200c2c1d41e0030803003c0703a242802e40243c0e040c10304101d6020500840d01c1003508070041070100c1d0403007040942e41110040d601c650480542440c0c01800c207140c42150310200035281c420501c24001c062160140c10601501c3c04180c0030b0415a002c241c0003130a070f0099031191181d6003e118264804604000c24501201400708140310000a403490740f8001c40b201d040754080c18400040081c0360282a8000003440003112020a01150781140d102c030300041e050342d080d6440c0c1c0c03403920002c01c411201c0c03130b000d1810481d0650340d00b0310101d406008503a2503101c03524070894a00910040345c020100090041d40d959601c081088201040f80303114a1080d12038003401c1c0d9056061406907100540703840c1c05482c0130304c100c6001540c0c04244c00f9010210a00010300c10003048202c2c81c3c50050580d50220000000030140148501000100801d120341012942c0c040c2c0d80e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 707956169 1250 707954919 707954941
    0x20606120303040b070504120f0506130201021e0703141606050406091e09050108100b010e0609090a060b03090a0201180e130809100e1f1d040e0114010e 67
    0x3216503129503030400c00015002a100c1c03100c0c1500308500340751080c241600d480a81a81484c41102902e000c0c0030f04d040e980c20800108812035201c1c0401820500240701580040e50b01c1c03c0e0314000e40c0054500e4840701f10800b004001105c019604401e4603908955400641e81d107507188009807034600c0801202c0030800e54080c108550444071140c0e11701009500d4807041d81c004003580b103121105e40554103c00601e14032135010b241d02804075480985612020442d01c0310456400407080340c140101c9260a504503034031841035481760201a10a07805580d621490b400080c003903504540da0702d1001005020300e540f000604005514401c0e207803013031b600c102c40c900e038480c22441d442401b800c900c0740700c0020314502444a201c0f0241e48030748003482c10300008070000345242c1200c0318030030700184118044040c580360400400c0c1c02c0580810701e5120000703200c48002c0103c1140c001d400e00c0d990340c40c454088141c449a01800d5800100d10080003840b5032034203c50410070080c414210b4641029010030292100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 707957419 1250 707956169 707956189
    0x1206011e020d0c021c050607091d0103080706090b070207060207081504020d02030703060212100b070b0a02030717040602040611030307051206060403140d081305210f04060906020606 80
    0x200d0340050041c10142d0804440780151a10304a8001915990043e54069000804140e10b841134000e40801c0c0381480c0001c14001441d44003601041019000c03010912040c07110505681c0c000f140c1d03a03a0303142da0342055006018400c0e802403504c0610000c2010319907010409009481540e03003911982daa84040b15550741100e20891001801c428000c2001031500000c0c2e068100d102030203407410540c0d03d40760b01049070044d010101c007100b840000c000c1450090304800c4090552140c40e1402c00c1c0581d1100800301c40001c3c001407034240d00101250300075010f00040414030030301d0310282d1032519103854054041e400c64490200031a060505d428408072000c42501d11410710740d80d6007820640c1c1c80c1c0d400400004040d00d4550411410000800412031207140d10507800e5000e801004042c840e0300004000140c010300c0d1058080c00da190743d10001e100490003198204e620303483d001c0a080391f402c0d405100d204080c1c83c5246280005000a400e1360444520421203c4035000c0d48c400d0780d110801c0c81380c0d541e0307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 707958669 1250 707957419 707957477
    0x60c0c090723030406090c0e061318060b03030f0d0e0106050a0e040f1e110f1c02040203090c1906020d170408030703060302031e0106050f06040b0703030e03120601 72
    0x40401c40b03a041c24095000a140d02c60700030040414215840d0b2600500c4048581200150903102800c1141d41c0c10103007040340000e01009000c010b030312980d0582c0903035000280c0c0300078041134941d2182c44081d074080042c0c440d04003080c4091942ea0308580344000c014520001107131115400d00000140501d04503443d00c003212078415020300709959507a034042e0690040042140e095804c964610030000d00280c0c0035810a10030385c4a030306902c0c049401c001d00c40c1d054040e91442080080c40d140f20120003110b805690726810f50300942c40307450317070030580c0d042003d00c010098000250300c8210214030140703007001080783d13015003c0d10100964000100c40c04040c0343da201220b00c1421010034006031110000790f034071008929001482a441e9800a41404c80450b0405200e0303203ca15100100c8600384079200080108448442c1c0e611030b17007000300c4c546014038420420054400702e01c50082c58000c0d000f12180c4903100342a60344e60082c0380307445500c8807c2903452600192a5803080c3c030304c0d80b50786129071034038003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 707959919 1250 707958669 707958707
    0xa0807080d0f0504030b0f010302010815010207170c0d0813090204030210080604141017010203090703030e0319121103070b01052b0803180a11061305060c0c0907 71
    0x1800500c07007500c0006141003000200007007003000001003844402014040c038118103801250303515600005201d12400340800e14040c4601007403145581e00014004116030345401e00101c45501103042d00c2c01d201c00b120440740c10104215a10080242250081007200e414104035502ca80d1600c900b1402c90045e800002d4100360700c00c80b40e0711118050503220f031780240c0043c008220108119032404003c1010340303080e00a1400d01106021485000600384d1070319030b0b130b14021401c600d041e012160351400c5500c40034050040c0700d0314003000790f20140007a810340c4001d268004403002091034000c800c40d0100c46544002a0802c21104500300048111001310303401221900030b5900341001c01041c0b1002160042c9100380300c014141651600c60b40424110740a01c0d070047e01c0c4e240105458a00c10041040e40090350090f04070440010300080c11035100180c19030300c1c0341d100c1544118445458030641c01065021101084014010900045010000c60151403010b0f6980302c1c420f0580e1506c0b80315081d0b030b07206 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 707961169 1250 707959919 707959933
    0xf071b030905040b120318040e010902061e0c030414030105011d061225080111030601080406050702190b092104091a12070e070212120a060b040906050a080708 70
    0xd107020b030044c504042c0c0c014090310800c0d80303000c281440c662100801a0f08513a1901c0301700801e2400744034902c2499440c100030f00c08000c25030b0000d140e500c07801c0503aa10a28552441d400040b0940701500c0d8000b1690040b0307699140c4a900a48680d0000040240310b0740c280070012806010081003203603400c100c1881c94089848401c200040c001d0703210b0341c90180c0d1190b422a41a8101c50000320002d200c00ba0100c1660b09080c20401429950811401c00c420b100c01c1040c070034207991240159a101d42c000341c1c0090a900c48a0040b428803820300e2501c18031041056050701484520354090780280d1928007165100c4c20450000480b018503401800e80c0340c00144801c110407170b05500b185031569203091400c6e41c40341d03000002905201160a1001c1280d10034041030040c000d20f10040c2d50400307640d000802408040301c00000c007510400b00c99501c04102c16000c20140181904100e014000c00074045484030386a4010400070030aa1041520402600b14002203050700403400d4000d49044201038540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 707962419 1250 707961169 707961179
    0x501060602100e011b1b0b1314060103030c26120a0b0a0614090402130f061d1e180414011503050d0e0117010602010b0120070e060102150f071b0309 65
    0x105070781e0031b2510340d1000481640100000c80d008407180c480d2a00502c80840265542050319040030141a02c50f041c1d0b01000052011a070040172400955030310002402c0328100b03e0301d120f21041e0f840b9006d96a0395801080100d2140464000940302d2004107208100d441d00c118100403424005102e100d0100320031004540b03640000d0001403408003c064005441c21800542803001c0c1c2c1810fa014241c07003040340d8810304c0071a038007803c80381c071521000c0c00c0d841e00070802c0c0e00000e900409981c00100c4607500a40c41d4001c03901c0d031842e611600d289081e03041080d8034043c202030390345100300c501840d07541d4644240d000211080c00308a0007501e80000c010650101c034844c0a488002c248555981400070100ba4180c400203034103c182d028241603400420001d244000141c240c180040100000480804d05407605120002e4260100d91038502c6006107500da48006074240000c2c01c1072201c02480034004c00c004207514160450050b104c941e01c022080500364054180003114401c000d000894490381049 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 707963669 1250 707962419 707962427
    0xc04090612030e0d03092d03110a05220b0a08010203070206011715151207060e040f020412031d06072405091504170d0b010909050c160602070501060602100e011b 71
    0x181e00c08103d05100c50300e01ca04e01f4540170b00e10301d94800c5407840e503032550342500d07070400100c450000c003010f03201c00c000c45103100642034070340300660100c03100d959880038488e02c0e5503100d0700e10300000c280410085580f03042401d0000c1d100e000034010b01102d52403807000f00000301000261030743c03010084400c140b605d45540301755003d0305060510403a4404506200051602c40a00150006000d1511544103800a00092005850f01c0b610040300b003c5c03042c042006001c0403080c4141800343d1502c0c0c40050710066800e4000045024900755400c001d01080746010030040d14501072030091501801006460b1030f52512082d918112620801a00001140c400030401512070351b80040c440c810f184501426000300c00711070b41140c10000c1003103407105150204c55030030a50010103800d40c240207001d1482c0c86401c1c22500e10032504d0364100002e62403201c6061140740c0e81500c0e1050341c02002031041540e40c01c1e00955a4401141440c440740c503062444009240510a0034040c244401902035141c10a10f002d80e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 707964919 1250 707963669 707963699
    0x105060f0310090f23070806040210050a0c0b0c120f04080406110c0603070923090c0901030b100e12010b01090e131403130b030c0d050c04090612030e0d0309 69
    0x2d81458240c60303004d00054180c20498010745002103805608481d502a030380c0392480c9a4480c02454014005000c0581c645242c0741311910161b042441c6d0721844414211400c41f80c10a0140030240e242d028800512144002030940c5028032441856644980c2e640182044060381c00404c0340c442000100310a41c0200301600c03d003074650099840202d95980441d40c20792084615400165406005001460120788001c2882c03101c40c28000000e218a008a0300710341300540030b8580c450b004102584070303038403d0300003030003001000d4880f40c890b40c006040030f0190201c140b4050f100749072000284911460510a42176800d00596030000c002e4030704001d407042c1890240c01440141d80c2d4075182c20110b920b43e11030103800d4580b60000e56880e26442d031020300d200402c0d004907032a10420000e00500e40b1203d025100c49103600078000a0a03117910185948070310650384241c12240c204800090f10340441001110740d54082d488580c10483e040c810003031014622a402404209a04404c2c8181180c43d0500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 707966169 1250 707964919 707964923
    0x30a031112011e150504030c0602030a14130906170105130506041112060412090b040308041509030209010b04180506011704020109090e0a05010c0e10050703030f06170105060f031009 80
    0x40c100b41922a80000d40d0650130404050104100240800170002c140040390f0040c4080e10146003031a01c000001440990f00408515091102203031040f0154003040b5100c0080810100400c0865601d8021059000c000e607800c01d03c9518080002e14603022010b00064080e0740000541615039a0703075a04036a003000303403800ca60040e0f501009814115000c1241c240074034051002d44569031465080285400101e400030b80ca4804148030400000c6c4001040e02d0075250f000c0882143c03134401000465880d485680042e5010b900b1800000c0d001c1d0030003005000f40e44500d141189581082c04924003030b07490541d1000c3c00101c406070000f21119124107810f4116105240904086a442c400401514841401138070300c1e4100078040d2080007030901c1f914101c1c0c906814241c8100d40308000140c11440000e09203428070400040b02c03000c02d44690312400c030003104138104212035074961100c1c480001481000344040c1d031800300401c030340345010b0b004600d201000400400c0284034460054000c0c105c01481 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 707967419 1250 707966169 707966219
    0x50108041203092d0212010b1e061909080c010207030210031e050c04050108060f15070c0f0905040501230c07060b120d1d010c080a021c02030a03111201 67
    0x441a03008502882030544103080c9120852890480c0100904211361b007040d01c8047c0c0c908942040d07140c484910100b16065484038200500e0b10070800304a2a203c0c411030010703401250100c442c4100d4201c1c140ba410346a2140854109030783d9507005a90710f200601010b5407200e0b03d00100c848281c400e82001d0040c030101244420301c6010801e1510035070b20705072581100c184012500f8400c03564080100e07540040b044512600140030314012608020981f030501c10a454001102e00900581428090040104022081034150340d581c10740001d02003664111034950a08084d2007030047c040802995210322500d10001c142c94007055442c0a90102808503800c580341c24003080c0a9640c1e504200454003c1006400703801c2030000c00034442ca9031500c2400e00c0c4500c0c42007203d4142d0b4042d215212284d40644410f070354040c0310b001a4074000c110341c1d605211350031014044c06001c0d80800504054800d5803802c3c001041c1024039041c41d40104160a084c00f4030302c0c0010407086001005694508680c090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 707968669 1250 707967419 707967443
    0x60c083106020a1b150b04110307051b0601060e0f0303070b01091d0102040e1e041106090112052509141c0503070c080615010e04050a06082505010804120309 69
    0x80155820942d20051343e103080f05c4601e400d045041402003e0300d0340000c850410000c80c5445218000313010203040e4104120003c91070b411840c0c02c04a4035695201c03030208851045d03a49010081030f59841c1d551aa000b0b00c16000440f0040c1000000da81d141c6c0da01150050050b0b003811400002030030381c5000c20016400c0c1c0c2c03414941911003840204090700543c030121301c1c07514000c1d040000ca20304000088400d08100400c01000c90403104c0e8008076003504840056840100c0c6004941c942c1d50b081e0641d80c228504014040b4480d155000e07112a00307a107200c2c003120031182c0c24080d0f5400040344201c0c91003402d154601c80079440c2c5118040440040074618818140050311210f2450f0802e080880350f601c002142880036150401a903680050351000c800428451400002c0069a030415034600603078450002c10007066241d042103000d0800030044551400c2e090b0380c45546180a0421856280c0300c0020124595100303103803d61003150405000050a031415100b1802000d4040d000d0759030b6101a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 707969919 1250 707968669 707968697
    0x10090504020c0c040e0316170d0c020105070e030d0f080a20030a060b0f0a180504022101050409050c0d080d020f04090c0305041e0807060c083106020a 66
    0x4400b408501c05104001c00e002810315061004075039036101c11503c203900a102d008800701e014041d01c9030391a44140e4030320341105104401d914a0241e0010498064100070713005401c41d80c1580000e205d0701c42a5107420840c02c200080c1509d95824100d441c0c0003400407408810410701070490030303402c5a00d130b400024549442c41c40400200600c2280292000b2000080c010003801601680c03001c0c100a1032140d203484504c16101c6610300c580c149507410b11031007484180e04804106098001004040d00c00d540d5010a03241e14002a4405400356a1255100c00041400c0c1031901c12440c1e001d07440001440c03148440001c02450008000e41292942e404101c801011103007070025105800f0b600d0040da45440c02d0179000c0003070301c1e0004489020946842c0802010034000d98500c04500868189001c803a0300703506126649206808000d401107003025101e00000c1e502c0504184200c90800c00c06041e61819401c03003a03180c1c000d000b1455400c03100102032020460541c010400903015060041c80c0300303c24 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 707971169 1250 707969919 707969921
    0x30d0204091d06010b03070c050a0605010803041712090d080403240e0f1e030708160b01080d080601030c1e020a12111c0e090f010510080405030910090504 68
    0x2540014101c0368554041c8440c0354035440c21a041e8841150103401c0c10b41c107007802c0d05014000140b4090400c20741c5041e0000b800340501404a085404c40000d20496851740c10190ba0380d03005101d60f00e0305440c079898854207540046040e69100d4170f00c4c2c10151800150300d0400c204290140320079565a401000300200244098182140030380f6242011032103500881054021101c0146030521035411900c146480d000c40032840703c0015a28640c2c03032040e0400c46d0f5025185004584004105401c00541880e003122417500855400b0310813550b401440e0303290300080ea26101524101404030798058049551903010750400d0380760740202d25040011000c42c400e0120312110601409007d41c01c180500418000080080b803410190390505140703d680c65240d05d951142c5170303055071020100301c00d52114018400d2082207504140207001e0341060038841d415820400003841200d00c030f500060031090015015240c154401da03001006141403403014000e1142c100350034862041080b074074060106655940f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 707972419 1250 707971169 707971177
    0x1090b01140a03050114040911190f06030209030f0c090f041e0b040614090709090c12201504090902040e1b0a0b1201061103090d03030903023c030d02 66
    0x40d81d000c200b651500b01100a501b01c160803090165041009410120b90561a1450300242c01d84a880030440b010024025110994001d1080c00b20221400140c00d80e06802600307081c40110f003a114000c0c0520401d41d81c42915480b40e07a040509140020f0a40140c5904103902500540782c03620240d140844500c0c050100b00c604940f8807008e107003403006102131032184500740001007070020002e080c500300c50340d502c115611403101400d440d180340c501040f440d000c11400070607101420707a802801a15080148105800038010200449454400b007482c00c5c2035881d1150301c081c070f80189491304052001c409022042000ea030802d03102d24194050f0b01040202080c50941504041c030022010707810400c080203568840d40d00107405100c01c041c03880c031a080071030442d803040c107000402c460301c90080c60440c050031942990001c46841c103482455055001101c845d4480d82c280c0b00042441517800030184003040c20415074121041912040351003086510803980360380000c4a003040c0d450b240c2181640c1c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 707973669 1250 707972419 707972437
    0x1b050102040906060305090a0b060d1109010303020c01110c060426060a05011802090619090305030307020601090501050405042001210209010806030f0a0f031202210703020a0801090b0114 82
    0x1960f21010000198103118040c0c21112443c0544601d4405446554003450040c0509101c1c02081102e00308011052007402d030f0000c800340242c0c0752036a4900b03010352110714542026000c1140e40d0903102d0122800b040d00644900c00500031806c0a04005a40d43e00700a00c128141201d030419003600150b000030401903218540d00640402c0070342c1801080b644c001382180d8a06811801842001c0c13455680c1d40c159000e42e03e80b015081d804140602044488603440d91014201b0f010010900c440603034003013000c41c141d0700324040620bc90399803102408101c840444024104089104c00303402002c00031070500180d02014909847e01c840f441c2d42c0f031114517118038084180b07950700286418140d60090380c650352002d000c50140c0207400440f5980c07a00c410303018400a0490070520385ca60200340c000c030001e0030255080c00f0215215040c00c00f24140b81c801c203503189a103408800d00002d408510a00803a000403600740d80e800e02d00e074038181220001e000d421580505009c01043c3c0303003003039040c0c120103400014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 707974919 1250 707973669 707973671
    0x4030c03232a041109090c1303060e0601061419020313171606081f030605070c02090117071e03050d051c150605160506090c031002191b0501020409 65
    0x48401454101203100580740b0078021800d04803d510030070340e08030a03111008429586618603030342d5440c160402c0c0c41441b034080382040c480080070051160f194030885100d108841118016602d9007415202d82d41d00c441e000b04c40210400945540030380d060307800300511989004a9091100c00303569145410ba242c1c005440c0540440b00480104c40204165034140160200300881c03030703040c107100412540005041d0040b6000c1024850400b628900c2100c0042d50802c408001e20f0500c1c210007007134482d4003a4145c0c400d400034000030450300480c80003451242c8030038000700115031402118290300c0c00103030300e20468508500000008600240241c81c000d858a50b1844c3e0741380031529101c82c48110412003480a00e2034003c00c400c004c1d002c0c807411000d0750302a0070015110a10203841200302200303107400034124081c01003400581c5000046800e04104202c09461814140303010050880c011078445106202c00e01450345445409a68414a4001028050442d8030165140d86003640d005500c00d69100d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 707976169 1250 707974919 707974963
    0x702060c0a11030a17070c27060b0c03041e1805012606070c02010201090209090102130b0c03040b0d09141c02030306090103020d1505240d030e06090a1e091104030c0323 74
    0x304680f80328420103800385062b03a034144414020b001d07a8078062401000351407010402e80b4071604149642c140001c0410300c1c4c04801110380c55a00700060076081c07040c135900d0000d12043e130442c4031091105400c0317100e00100411040d5100601242c2118000400b80e040d0b550343d488a80c0035881e0030f103d040c46a04100300143e9103c0f06010350880044d416848544000d02c01d000006928202000b21011035511050b41500c0d184540780d608010b150455000780004403240944413400f030041000b0f0314078001d04d002301040204001040ea01c07440211680303540015104014001890910700075801c20340154034030505001070000041c1104d10545180301c070301c00c08101030064505d000180c281154020340d0702d20228000e07541d01a281a11a02205e03220302c03404540540151210684040100b18a0076544040050211052800205801a0303810340b41010b101e040403044100c12a0704403580f04184034080340c5140c517100340043d07944401c65500f5504201d012001541001500c10351070500004c0d0803c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 707977419 1250 707976169 707976239
    0x203010b0316090b070609030e041a0a090605010507080a02010e0a0f02150a0c12030209060f090f010305040507090e010f1b12060b0a0509060702060c0a11030a17070c 73
    0x8107042c442104082000e00d4109102e0a1502d2090341c0d82d65030b202c01c010802071040c0c90142e6800c0305d00310007103030448c2c9012414070216007000002082690706031090b030302c810345802600f0191007040c0103082c0450b1f03080080a00060004000b817100505c1c1d88000241c201c40d100f18103041c10092903041d1344076010b01ca080029442c21010080007140300d0316150349400d4805102811441503001d020f40b1418070241c0d0300c840507000b40c040b00c1e40420300404451340c0d48401d0f01c0c90030544c1c000881e004d0041e440200c030100ba030350081c404d41d030217240c00c00010080145007441e80400380010010850b095508c540018002e641180103695403058409240540707a285480014200c00300054412100741c10000304110170150070040315180c0101d0700c0c1c52540c0d400a4004510381c2d11881d40d0080d000703400069034010142003c50005000c51258050402600d1001c2c201541c802c518030300684a28860200740000395034a000900300c051007495614601c030780d1610351021074100c0d15119001c1c004100c4100c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 707978669 1250 707977419 707977441
    0xf12010509040f03050307020a02100f12062d09020f0307021014070c02120d02030c0609010c120b0f04052401260601110102040f0609150c0204021b010203010b03 71
    0x201400d0140c0320014580741c1620743c804039030034804014050007000008104207600c01e024030700c04140c0180444004404060005015003404503140300019003500030440e014649008003412159440c1402a40080b01e00c20b940f014000b0130a00921102e88141c0021220700340d001400d420366010f8115900c070314110002904001000e0b502d001d0003450014021081140c104980d0b402072810324040c4506411440411a140d2800c10188100d100d840203c403d91607000006007038450205061312041d440e80b80d074190a0700d070020250000320b170640c0d014036800400c5501101020400801404210700054042022160b0603070741440c000905d801c40390b070307800030541544800000a2820381c01900400410008284c22241500b50303a4145002094041c0c2c400c0351341103035100c0e51a00071035541c0c5e134031480c00c548058540704140101c2c242c440c0c000f03a00404030000302440700707450300c4415901030640d00700402540180d000e40103004030480080e04100e000d2000c3d6000c1c007003d01802c0da883c1018001c0310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 707979919 1250 707978669 707978671
    0x10b090a0b130c020c060f0c0d09081b1f030f11130302060d1e0603050c010f120504080c030403030309060f15090b0d020904120807020106141201060b0f12 68
    0x803000742020855100c5480d08101d4850711440c6100020340106100c03c12401c012040c4071850340006c01050800501d150a002418095400d2044031074000380c0b1501500c4c1d40c02e062280c90f0880c2c216244e0107a49204c0941740020040004021440e07003110310581072881c44004072140300095980b81650366404032482181c4041030281801410005a1003c010b000c075114040240642d00c080b40454103485182c00801e80c42d4408a03159040301c0760f8000c00801081207100a54042c0f044031b00000040d4000c00741c1030019856542c0c0d088c031549424207240090132001d4002c0b0740409040141d0200203900b400600040d40c030a070b90120703003829141080d4040d42e082e02c80140e03102c0d1400d07070b1010101c075160488004075041c0b0360307001c1007241108002603d16a60310101070341000001d8200000c004541516080d580745603212200340303496600040f0300326001405801018111201d4800c0035241c58200c0070700c100b20400012460343c0d02c611040c0c00c960050040303000031a5001c2100c00030710b01796140381 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 707981169 1250 707979919 707979931
    0x503070308150607080d02070b040506042a051009081f05010f060912170d02030403030e06041e0804090204090c090905060f0d15090b09012304170409050405010b09 72
    0x81e45802c002d00190062040307910040c0f86000001c4c0d120061500360301503400e060b41101413544079240c03508181d51125400c40f02258018504511281c0c40c0282c5025500443c00c030380126035115092400b0b02445c0301603e403c980a00c44502c9000501450800079080790b040003410700f801a0007800c0d0060240e44c0187c110762110107001714184441548010b07858103c2c0d030003124403608000d01d401c0c5441c19040c07103c12a108400d00242565840d0132680095024170f220f540c1c20462000c401c0040c40c0c4544c0150b4008100b29200b4007001a5198400c0c4800e14043c00b230440c203841e05940d00e03503a000702d0388260b111900d41601c40030080c00642c1c1000240000b0400b028050081c0d2500c200090884010200c8a070310506030070001c10180100040b440007e0045c000302000000c607941410400000b080ba212200da40c00c1c0403221140104e17564803910188110b5021900a44a1b07036251810301c633100c000d09580450512001411003540d00415000301e01540000414540641c00e10550403002891 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 707982419 1250 707981169 707981191
    0x40b04050c1f17251b0813061b020112240509061f1b05150117070e042d0b091216030309060b04140a0f0b01020604032a0503070308 58
    0x3049004001341c015640a0f48041c10f402080004001c0f0584292000f140d2880800b0f51303d10815080080004c0107001c2d06c0700b48040c40020701e9031001d049031003001d8903034603800c2108a455087c0065005640070040740d25035803070100704641006c01904081d101803001c3c0c0a0340002800401032801c0c00065150440416622a8018911320f91035010244d4005111420406c462580000e12075021500480781580310069940242000c240700c4200b400a0044030092904c000d52160036a0000034000119412604040312a545684843c0032940c0100800c112410450407900e842d0148a28500d43c0640700d100e80591501700318008a29080b20521442ca8030a070400869014031145901e0009459062074081841041071900c00c0c060910304488642050a1119030a00c0740307060702c003061180300400b004100b4032040391145030594031050f038400d000d40c0002e4089000700b44500086416105e003441c07503192240b03088030f03400303808210480d0942e83c03070f000811424100b6070b02030101600003085401c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 707983669 1250 707982419 707982421
    0x1e110a14091b04050a29090f010c06090804060203070b0c090d110301110f0d11031501140f07080d0507140d150807080a140a0803040b04050c1f17 64
    0x31075007090010300300d408038400011031a40303102207040898015003400b900281d400343d5075480130414031000809004400144000c0c43c1102c035146401e641c403055000b001c00b50350040d00e900643c4c081c00d01d40401d680094644118601080e00c1400070300040c501ea81c000d61b61200319042c089890718003d803500c000524100324400965070303000c0601e02d0454008488100701d0740c040c00000c0c01030000c0c000ca925842d0002c52207100250f000000f414040c020558140f10144107002c01c00c0c220f20084031003415100d0f610a070078116511490142100c3c07148003251514060302c0416060340358000400031561980005841c04070503280340600c49c3c000245c2d05280200c58170010003082ca41c0120000f100840d03549442d251511024100c0c50002000d404050381d0b8119100d00074242c80b9510310b20151103140b140e0031900500980011003d070394540002090b41180c032142e8a04100c80740280c4181c40c84c1c459000c8603145da41d00c0014015098040d010f102c00c0840c20241e01414240f80c0c020004582c0f40318030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 707984919 1250 707983669 707983709
    0x10302100c0b0f0612010603122622051005041505090d08060f090103050d09150503160905100c141f090c0b03040302010e1002190c1e110a 61
    0x4140b40d0485800440c400c240e40e1034402145240c1e0086054454030b41c01c005000052040d840b441c500e85a050341e482d00b00b40640003480c55219100740301d04940000460002a00c5420b4112018682403d8280d402000800b075803116031074034004501d00d140d110790b140103010800262021081c2d084081d001c080c8400d00d800341a164a0720010000308041c8100b0f1000545165502d040b24224480000e0085a49503164100300d5030307030060b0fa40200c000c141030020200d10740c1d40700710b030882e80240266221491540da1007800c035105001d15204009000310344201041c01d99985400240441d501d41d5428854900c0f8180b0007200300d9140e801015540144600b95040340d6401e07041d2400c044284004a00c0e2496450700748402c1606501850b56041c000c0180300c201541034001001c102d14200445264081c030051541c124030070b6001050200008000e00300c0500d0082d482202828000d041480258008182c140510b00c0d045000b16442002505410502c4c50544400006462081c040f044030990341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 707986169 1250 707984919 707984933
    0x40c0f0c020d031103040b04030b07030608210f0a020c0f0a0810200c0607030b0906060301060305090c13060303021203010f050616060c0305070e1002030f0d0f0e06010302100c 77
    0x1480042d00400e101d02c4020245400744052440d03001c042c204490781d9a07503035103281d4819001800101c07604000d120114003264800c1c00340784103a42d5484050030305400548148141c000382800080310080040c0402c00c0e8214650019160350000d40c0c000d08000d06040c010043d00ca6103503d072261041400c1c59060255820025003c620f818110900141803601000003245041d01918600c0750500c0019401ca50100701281c0c0c02d0280d000b03500c0a120240c0390354100400f00c54201ca8842d0401401e100411105109800040e0401980e03400d4039a086080700100d05030303050a0302004040d5858040c20000c156040003000751214038082e000b401c1d941401d641c42da40311420302c2030b58403401d000f041c440e4403d007480b580c2e805840e40c030401c2000341d102c1f0401c024002e042c04a40070b002007072103a0602c0c005424213103840c168112140e8050341c5002044245410681c00580f19401c010380e403030301034000b842030038481c84040b80d0202d00205640d601d544100040d958030640060100a824020f0034001a44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 707987419 1250 707986169 707986187
    0xa151e0c110d0b010513020919061d06070609140a081b0102030105060702010c0203030f0301121203020a27031406090c01090f03060207022206050a1401080406050717090c040c0f 78
    0x41281c0702d0004c0c01c5802c1806c00a4020005442d40c4480e6002c1c03185140ba00e01031180c0c04540760340d1540340c04804443c1e02d0b40c03195140510b6a54028008114110001d405a840040084d1044001d010854600c1c070000d03180042c181803c0300c21400c000344021041c200d0708899a030303a100440080d0f14540c10407010680c1b81c051514000d041c07000e000860000c650f000c0c030a50701e50913004a006a100d694580d151107001d0000300301030f0340311030040c1180303044030303220303000715100c040d000c0d196544441031902070904e040e202c1011041e00b00b803000c0c00210004841068601c0c0822501c00113005a09008040600380540642542e0500031400c20400802c0a600011030031290400d10043e10b03441c59001241000d4115904800b421040b149100c60070319260380510195103003a40c0415a05407101c0700709034103480800016002c150031200040004200e9003040e90300c0344062074000c03c0310100c003959103030344501031300c02e202e954000503014071450503d842962845121031404042c20526100081d000c410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 707988669 1250 707987419 707987429
    0xb031207170f07080d0603030f03140711030c07090b03070e040215070318030311390409020907050307080709061e030b130b0109090207020a151e0c110d0b01 69
    0x54007081d407040900b804000e407603040d43c100c4880b503516044101068000c01c41408224041800c00c210510b40074443d200d0880300d03140701e107802d6401d0b4550342c4041e01d00141d0301210000e11300c0100b2844540c00002d0202c3c1e00100303007107200460b00c0d0240c907040500f030003a03540040500c041c20a040001682d1103403001c200d0040e4200c2400d45e40c103e00c1c20211400d03914039100e0381c8180f241c0702d0f00100b0150700001d051518160740b000e0b981d40c1030070300605a0342002100880100811540240241000c14031015101c001c8024000520018258003007a03100d00d04840000c0032500220410194680001e1000d0f0312a155142c00d031000307400c0510182510620800c0034110744440000c0106684c001d0f440701584c00c800030400c04c41c054030214008040d040c03a07000d6900007030b540003000440c180b0380d0080e20306450b4000d15002e0f07064100003900320600403c020342c00030014510904058800c451000261a10480e655400c500c0a83d0505001d444184281d05016142c61005e410100d60413001c007a054031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 707989919 1250 707988669 707988713
    0x40b0a2c10060807181401080a0b010f030e010605040501030b040b0108120f09041e0f0617102013031a07080f0c040b0c06010e1014101e030b031207 65
    0x180b01e00b54219407111728000d42194020181c180810031000394144070750f2100c4240d031a42c102d90369064501d81560042446a4046421440145c0313040b4001d800000303d080c3d440c00001000c0d0740da0310014041e42c00a84c4261036107400202408103002c01209850b02400014000b082e0003001c4003828001d40c451007549402c8014040b0766030300f690b9216000700a58618844200203201003241042e4010f00c04210030314007148c50301000091082207071241e00d02c81920f6002504100240e0440000500b40b030342600400556041208100045004040c05012031000c090f50141c1f0300f54904500001186c4800b00d40d11010340080120403503008034807540c026001086070105407908154032165001e0340e00494102903001c514034900250015030241200c6440c00520100d0b201c1182c0020701415500410740044100020a01d040c1401e107800d800c000c03040c0c45d20f442c400b849028091a0030504114000020f51030320508a528a0104040c80c12154401e000c545051119a51035140b1081e010f81d01d0303003803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 707991169 1250 707989919 707989921
    0x3070e060d0902090702011a030c011b0303020f070c030b011a09210f100c080402150a0207030c08010903120b0f0103110702180f010905010b030f0402040b0a2c100608 73
    0x400155080b507511250f0280c413610792410403d60107030180101c0c444090a408941e80c0340d40940c54001000e11400c401a10740c0c0341d80d0000c10800c0f09045003003420076002d15030200030060003182043c0c000c090f1075004441160f0801d06602e8800c00e07005041e0b101e01034000340843e24030801e844d0745044a042800c11100122820140341094417034100d98580d02049020f803030800b03105000701080102540443c540c0070400a02180300c00e440510741598003a40128140306e4446201c80340f0001052800801d0040302c1c1d0850340c980e280c1c521742405400441040e51200b04400406401401d4a401c2c0f01c01e40100303115281c40b980c04101c10040ca90351f42410903458400c1d40d500307440040200c54240740c0291a0300005111898607646d802010707124007601043c00740001402103010b200d91410703030303030005480d600c0d585820581051015000e0f0003030b64015580c840d0380a09a88840b05c107070044c9010000c0d950342020152050703031a0341c00400c44101d0074960804220040e034032000d01c00103803a841e0a0412003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 707992419 1250 707991169 707991187
    0x1208010f180b191404150b0901050c070509040c030b0601031e0c170103050102030f150604031205270424050607210234060509040f14090706020303070e06 68
    0x14550700004000c0960b184490110b04c0411041600100e100181d0f801c3c40000c0c00c80c0c400420040d5030b44180b2143c100300b0301500030300e58482c0000b89607100e100c004465409880d2000181c0304541920121640b81214504000300300c001c10000d039007c0c0090904028842c18070300b440e81010184505c3c10314440ea259009584a401000032012000c150f1071806825038582c5041e5000b540140c6401c00e01b80900000100882d40c1070458100901d4003804440c1010704e15559242d101c49003000b01c500f0301509000d241003180b0444005048104480d405c1d440d1000700006000466a04004446005480c808804145005508080e040301d1007940e6050350b46003e070616929100e000004101c200b00c0d4002101c07031541d400103401082984c4034000070b5a404c001526480382144180c0c0109084021450401545025001806260340050f2011a40000030311040d81203d204420b000b10300103450043c000040002c004803006041e05000031441c50804650141c00d00100240701413169100107400320f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 707993669 1250 707992419 707992429
    0x2060c01240f0806280204050d030201090303060503150f10210b0601030204050d020f03030d020a11070602030a0909020d1d0d080c0319050c07020d1208010f180b 71
    0x50031840d110340140048001c0071204484411449030107004056800081407220740032074218004d41840110102c21848400c00542c1c8261111040e208a41e0070700000845850b07849408100c1803080d400003aa074011403902508888103504618041c0c1d1003001000f0440011001042d000a12000046081d56419241040c2c51210f6080440c0304070745401c004c02000002d0380c0030342c2040e101d0a01e44100b43c3e80c81004408a0166125040c0d01108212101e805800d24441d903a011100180c182c9240150010488003a030344048903540c0004c2c180711562541c50424040a0044d025600c042c515000f000c4000a01c2081c841c00303102451a80025140ca55100951162031040901c4055002e0340068001603501c1d0106080310b070002c076a80c0c4002a00300e4a072881103a100d0108818007a40f41c8010f60114001018010074038a2081400c11007440582c0d03030001c4030a40680706d0700d4103803820352403008020300c480c0060303015a004103642e4509005007c801206003c001c00c480800244840701d4600080c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 707994919 1250 707993669 707993681
    0x13060b130b3907120c060201050c040510140301120c0504140105090c0705070608090105060f0321120408041d0714070609060e0616020a050703110307091b26010302060c01 75
    0x8051044050020f99000007012001c4c0950242c618210f109503680820ba0980d10219402d10b203243d01080140510700c4c010140485608903071511005420440300d4080903039100fa00700828000c180c00d01503041080600c40c44025180a540600c10700c00707440041c40d100d08060245901c540903140000d00d0021031103044e118000e03040000c07142941c0d039504019003100d0050381d50b2903403942408001175050415000e18a005c40c4082c005040e416022a0204150500405604045107081004420300d00242c1c0d00240200c5c018400d455440e4a4451001120301210392807601d0180020108809681c001c59030400308140d80c3d41403581c521407843c00384020414410000e00f02881c0c00f009034001100019868460072050a403402600b10702c1c001a6591481c407400149a680040d80600002e030044c0f031000083c0c14040c0072940d0154842c0c071070a040e01c80c182c040340c6684400b16940e80101d940b14000c03429002440f906500d84095400150700c100b501404060b01541000482c00b0900c90b09601032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 707996169 1250 707994919 707995027
    0x120106030b060d26070210080708240d060b0108100812070221010b090a1103010b0c190503120f070806090601021c02030301030b1803030a0b13060b130b 67
    0x1030400c8400c2584d18450b40201005a014400581081a019000d00500c9005551a4036814025031340c50780c501411031441e10500c48a180c4003102c9080d5500c4540340012000c0c4113001c003003031f14051540010004c1c0c01c02003100c001a601110204500b200100740320081040125000e6501e0f4190f00124840309200705880d40000001f56010347ca088040d07204174840c41c001c540702101511400149416946c80035480c8881400400040011010344001407180c040e0000685011840304903c00c00d101100c1c000544460304005102414503138603403210b641c4181014a01e02641c140488011700c01040141030500500850003c100340d43c1c001c220790903a4003003000103510007900702c0100a403682c00a10084032404110f9010a0b6540030360800d1618202041008600b150746074088840a464001540c0790803140070000a000c100c56800fa03000a041490840341d601c190026251824403101d51069109510600840307070440c124480c081608440350a100c1c08284c02111145140742c000041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 707997419 1250 707996169 707996213
    0x60304080a0e0415060e030a0b16022b03021b0d020745060810061805060f0f030304051c020102060f06100f170a0b120106030b060d 58
    0x10082005034031401411a040355030b48092404a1040a10054a00410b03804a01c414040720034000540310310707080c3e40c2c0004010210745108078161240200c1010540e03084242c0310070300301001c031003d40401c0310800c111a8048c500304085205104070725801b40e4141c00300c3c1015000510019503510f2881c0ca82d00b000031050542d28010b40e118406551003c0c548201c00016480c0e098070001d10720045001e203450b04005403d0644655400001e12403138140c815890a030035656600855506400c2008502c0e00d0812400041c1940c00e00034425000300c40c550114030802d09004c2041556218441c1802d03803000160365411088002d81c0c0002c0c214003a5810868000540c07140340c3d160201030a1514074000c1c000e800b46e60141d1108100a40c2c500710032604207400c02100410b00015520601011400810310319110407410300003c00c02c40240c5007915180c40c400e40b182c00b80b91481c070340701c091034082440b4070008004061a5a0b030b00380001e030004004d01d201d10b1292442c8010320042810310394081101e481 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 707998669 1250 707997419 707997421
    0x3170406140a1e030b040c08040b0f190204081506032a1c062414090a18301e0504181b050403051b030c060a0507051605060a081003020603 61
    0x3d004000745441c2032510f10036400c007460070008a000d1b40c0380900540c1c10801d404c071103a480300036180204c0b502602044401c1c0030340004500000b80f41c40944042c200960160a0403400401c10044800e001703080984030303401550701c00e224283c03120f01095407410314450326003419001740006594500d450700c8580301c0c040c0d000c41c0c4104014540e0311445a4004da6003045d1800003074207a03000c01585e0980280400700e0b090f1000c011152400c02401c80c3c0c00083e0001c00b28000d010100c454a86d80c1540508980415144141202080240300789040d000780c014013003106900982401064031442d009851030014281c44483c3c3c0a84c441c43c112000360108000010b4170213110010302c0014802009900c0c02e800c1d040c03410540a5118401b00e90440f07420030010500c04080220850762480e0038258a5071512901031010b10549801c4041d1500701010303203625807038031280e040141c101111044088010301c074452003440503540700000d03140e01445a107011440b070b695100d5116440c1119400103980848040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 707999919 1250 707998669 707998727
    0x1509050a09050109110a2c0402070308090f010207030516020d0206070f0b07050a02071205030409290103110904021c0612020109050f0a0b21011419031e02041b080103170406140a 78
    0x259014dda603180480d01c05100708a101c500302c1c00b520900a00142c0200070b1001d0401e003c110100401c2d00007401801e102d00030390700003886580180c40848114a048001c10f00b80700070100d41c55845641810b00f24034020340b04c04e009455402a000c1c140c9100500b42e050802d0000800c03e440151801410410061502408050440103c00c005148800e80b0040003031403948a40111509000c0d1180d44a0500c0f070200100030180d00701120510300301c5002842a4007c804501856005082e02510585c0b02c0f40a4000144000c601c0c1c2c01c0103000e4000f0302880c07002c40c0c460100d400101c8282e880d0301a2502c0060706a52032998a1020000707a100303c580020032030940302810490a00c82c00c035186890f42c51169036541c9102d00c54440035148900d040420118101000703000585244018800110f60310788003104c601007010aa1302500049544006204109841d81c0040e00319001181e5941032503d82403009180803904103100700e07031840100c0e080403c80e0041c1c0c111006104408008058a0741c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 708001169 1250 707999919 707999927
    0x1c020d0608120406020c04181a0709050a030c0e09031e0d050f280b091003020907020f100c09030209180610030c1509050a09050109110a2c04020703 65
    0x2034021500c00b0700404103401240007040c4100c600322020b42d00503102e050b5001c0d0070030005040d0100c40c0d220042c0180000800592100d5080c1340c140c1108410716203604108200600448680d04803078010451070000340302044207500f0020845107040d800b1002c039036030321001ca070440c0074041001c00c62071640d82003c1601104032004d4035601e18600320411555980362280355946205451800d810381c205071084072040c164001401c16404400c8010407036a01c0e0101081a500046541c07585150035050107008518000099507040700e12440103105082011540340e490703034030100c1140078403070341c990300300504d640109680c0c4000d640003001514240b030552100c10001c2980d50181c400e82c01104002424407003a54050426a42c2144140c40224249948140b040a600d00b0726824880444400101540d039258140c1c040d042000c1e01040d1945002020010f40318100f0000003026024404140003591103242006000000c3c100c00c8600091b0414803050250a80780550b00b0500008882040c1504 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 708002419 1250 708001169 708001181
    0x20f0714010f0b040c17040201021c0201051b04060504120203010b090103050a021008011202060319150303230d05150301110406021b010807050d0b0604030b151807051c020d 76
    0x1240c10503c046201c800800048030010000c2401003020b0222502c1001c1401941903409841801210504035810801c0850004041034000c0140c0d199020030581c4002d203914890039840d60501749003054105003002e0158040d074007031801100180e40b0b4000c00d44d502504090b4180320b0250110289517180e08250f501c0d00c0c0c0c0c0307400c20b03030155a41d2140d5031022441450070504868568042c0003c1d60815820409568805000e40e0081075000082040c9101a480303409003070010342c02c01d550254594a000703000b02c071550f0101403403407a04101a40401e29040d0840f88481046500002c940c0c0c5da4140034004c070403030320a02030f80540c80c005910003c5804c140040043d105207408880c03402228011440d03450340c0085000b400180b991000c1002640501e001d06510031382d01d4008504074482c040070a8240c2c1080d030040d104c0ba0501030a1040852311007000440b0540c040c2d030046840441401c000071014408ee0400042010001d4080d08140b5035220b480c0c00701c0d440a609540d2480703034020120251130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 708003669 1250 708002419 708002441
    0x409110d051602060c09030f0601080c0102100c050306060c0336030715030207020307030f030507150506011706061606061716050423040c18090f06020f071401 70
    0x11074500070030041d80c0081001c1e40200b000b58014245a40c031130301c14180e02e03040600d90540503c41ca00c40702003241418052140a0841e40009141c04002400024505150351130305040300c1d86410301001041c7c0e07201d03046942c00b0301c0036144c0d00e079540c41e14400d041c5588034081d8004e0601c06c494418130005102140b141c00c1e541c469400010310407000004140e1100002d00c141c9500030038594500001c14001c0d0042d01d0002e0004042e0768450b9a01e842d940c45290709c2c01030071000200c000400360b042204248401c3c0009034896002c01880c0380a200181546207460241c260069003480004c2d07030780d03460710116400701c3c0c5060042d4403418154038140c030103808103000d03180420b49540741a101031140041d92900300c1c40c2c4050f102c4c44513842c000520000346002c40490105000350002091181c101c1e00f056800b5034801c046400310b81d851700d2071081c00000c55000f010005401c2000b50404240300780c84404000303801c4100181da48c81034842c60480c40c81201402010f10000340030440c840316065001000982c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 708004919 1250 708003669 708003671
    0x1a0f07090504060e01030609290f01150c0b0c0d0c0504090e06060604031e080f070204051b0f0f210403090504090b0a021b0316030908030a140304080409110d 69
    0xa40310780401c01501c0c1e4038015003000c01100c9004001061881d0080340c001400b031280325442d4000404821400c03030741c80520030030f0180780009003c3d80c0b08205003d6801007085207005046041103100081c00c0d2501d8580c0035000030300700400301d01e15101d180308940600081c030313004208090b568000907042e80c105202d20a440d51a08034081c0190b000454520312403040108094501030a5944940c10b03106084040740c0103d8482a04100080414008011510350005541d40300d40140c4100000e441c0024842914864000303d6081150783c48002c0c3c0d0720440b503220840307448690040f0aa0b40901030403d038203004982c0364210145800041c21828066800307036580741c0401c0e84680a10040d5071184500809202d40d10000600007103499001d44003640340c0740c2c000e281a200c000941740c519000b480e459013950250112600806800c204403070700414000b000395081010803480900031400540d941d19440300e00000140c100304c002c01c2250090b0246100801010120352100c2c0786d2034002c0000407101d6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 708006169 1250 708004919 708004937
    0x12a021011070807080408010207030324030210030f092118050a4202010e0f060609040317010b0a09050618190302150309010b100212071a0f07 63
    0x85040c0340544100d10450216062802c0c41036942d18095034001070042e07a4443c0c06200109058400303000510206001c3d42d4003040140040b2019000d0458039110315140f040d0040c002c00050302c80b444040da1810060800051447c65404d41c940989076400c00180b00100001c0f401c2c21141e140301d0b80c420001d00341e5840fa03c02da000e003082c44418003000c0c01400e07880781480804200d43c510707100d806d4080c000000d010203440b4401d600e500c0b40020059581c03481002564544261040e82441568001014032008001e0035584241050b15002c0c041d1a075402007440400080074140201510004c50750b005140c42d09541c7d41d00e440c0c05403138004080040000342c600c60005001d16064081e41c2c0c540d407807600241c00700c8c030784082084841c0c85400b00304c01c1d491498100c000050380d209400050141128031100c2d44d2860500c004a0848580300c1c03086200d10090005280625800500c0f16026420748110590f20409030818244201ca070000c501c2c80c40e54150200700042d000809278600070340d0b107074856801e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 708007419 1250 708006169 708006193
    0xc150306120804030b2e0302121f0b040207080f04081501050916120f0207021302030405060f090325030809030301080c0919020307081008010b060a080603012a02 71
    0x14810706280081c244000502041c80807500c0004000d0f080720442c803103142440603420229008040b9903110058030700544900b001582400d080a40300922000040c241003036142d100b1101e0b00200e18101040241c1d5028809066101ca034111240a42c103c0394440d02c914050380240724590160090303590900924101a524455050300607059a800814a03659070b91295064841d00d580700044c80c0c20002c405a181540c0c02243c03249052801c920000960780b4001401440030b9842c010500a4042d803040040002040c0049080354011035003c84810040d11a064144d02d10b000d00d485001c0f100360201140050012043e6001405510075240e40301c4a80c0d81c02c4520761a40024400d40c0d0130b9401051101c4a10725000100a034000300010906407030a584523b090100d8008a0b22940414221028800208a101c250750010303c82d5130000e000300900240840d0007030050304245d40c00c0c01413400106a4980d401e40011891892400403110075088081c51052919060b050b100058000d1140301d580d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 708008669 1250 708007419 708007439
    0x1090e0114070c020f0a120b0c0910320a021504080301061125050901091104030303050c12091e010e07030314250c0803090102120310030c150306 64
    0x1200d072491269401242d40340a010345154141e62001ca900c03540f44a03522007265241001c10000c0c200880110400a28a1400480108000d464480409400c1c0414542582d8015140380c248c4d04528011b240c1c0c03610010301c0385240040f4596280c104244010f40d1650760070102c050145420b0036070854a202001d5040b41140c400261009461071030b0400041c40340c40c0c060804207143c8119a42119401500c0e00d03095602a8282c40e0250103c82e0940000c110a00c0c00a008902402c10481d04101c10b0401d81d84180c2c903849913120003408d16448a0004031020f02402c2500d0308417182c03110907012407410040072901c400b28401580d0040c020008150802c3c1e00500c14019000b4803080100340c280e046482c10780c0c0640c101d0300306c07030704440341002009010705019044c48640443c40c0ca07485050000743c81c0686014105801008040d0310034071100c20345a84c0015400c04d00110b984841c1d40d2900c60911031300d06802c1e1a0400342010000300c60008101c0785101c2002d00102e40c0d65000c000698a600c550a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 708009919 1250 708008669 708008681
    0x8130311100e1810080102030a0504141c0e0409060e1612080403020f03120712021002180111010b120307060b040e0307060c032304060f05072304051801090e01 70
    0x65082900f000703180148203000108150442590540c0e6210310b5a200641c40c00c2e80d004980e00c42100d600d6106110030480001429220341030800d002d041060341c2c541200b898103d0f000451400c0004000c0745124945070340d40031122803030304050306000d0708541c4d40546560710344556800c0d5000800f90300c00030b07107aa4942c0320344003526840032103149403518580810046600c500040c5e549030103001226511300c0381020040400510410791885c220211302d10180c18079400700d9403550554010006513001003900d4100b00f030146000d0802e401c8292030443c403680105003400c1590341106155000780d100c0a400005444041e00c58141404604c1c5450117000585e40052600181580b00348000b03400107501e0b4014400d0f4110798500013c845140340988140380340c0207586000700160010601c0107100b004d020b00d04054844d580207008509040400802d294401140c1d01d04c06548206880082e41c0300d80304403801020028904080445010300c5010005070030710a0103092460030418004801041c0244 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 708011169 1250 708009919 708009947
    0x3030507110c150304050c090414070b13030201260a14061c172503020c03070e01170a170c0f07060509060c100606030b011101060e130813031110 64
    0x3c405481c1600f100e000340c00241c42100c550040c2010700d02c1c0758845002e0340e8403590103a28006001d8a0151800b401c090403034002d00316a101c10840700031031140300d008070400c41c0e03420b103801511092500c5e10418410860203850b5103a0b032a0300c083c0045001a40c1002d1110030214018501944400003000b0761004c000222800154040c102500810600310301c00c1260601c0b4405185040c5003a040c42218440f4141d411070500b142e103c01209250341041804c000c108198010260306040c02c030b00355204041403251080501b00b414901c15004410300003407014607481a410310b10810680b02044503a0098841d014143c46518a100c0008030002191000c803002901c17070303500d41840c00080c42a141d04c10b42d80a10184507507211000015200c2c4601c0005000c81d81c0d0005940008800041480d0000040a0126030600809001e082e8500b400d45800800c80e14900c0f450109900d441c24403400381000190080b0050711000091102940c120030031450221a0281f40141a00050362020061141c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 708012419 1250 708011169 708011179
    0x6050f03070b0f04081f0f02070203060402060a110a0609021518010c14031303060515060324090f091608031b0712200901050907080403180303030507110c 68
    0x40102c8010040208040640710b40c0c2c0a10307240d1241e000500e0a24104134588480c10300e40d50003a4244014880c16072000d1240c00c1c15403606805800096a84001500c06482000c0000e400082e940c01014008400c40021042d107000004500301301c00240814003041c1e02030410008a05101500c110844144180309440c007054080034200454004c0243e060440701c42c1c07800301054a50243c10405450403400021608004501303514000317059800240c10401d4401070252140700c6030b5210310a4a40c404540301c000141e0342d901040124210904041c400d80050140f01401080c00d80c0383c03c001d1081010404032900c1c1140204042100c00013071003212200c3e001440072181d020810032072200000c0e4000100c4080540f6212409005110000c044445200d241c80341c00105261a82da403890940840d4440e046615290110b840c148004007243e08101c618130006007014001c43d803800b54100d02c44000c03000c040d2607241c007030020f040135200170010500c4484051034418000030602d40282c40500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 708013669 1250 708012419 708012433
    0x6060309100504110d0b0709060f0f0e0a031433010e090f03030a021809090d05030903070f2a03080405120106090e0c10050a0c08070602070605070305010906050f03 72
    0x440d010040c42c0161080700c0d902164421029645d0f0b824480e40303c450301845903548642402d09010f03044c1601d035800354003481090744105447e02d8110303203040c1c024102401c00c180c2d000c05550000c2d5100007260030040692261201596541c48002407811003a00e0200c2c02d02c4603418406103e45070040c540444001800040006001c0c000304001303407070f4012010108071501c071030b6244180d50039600112900c8030920b6012481080300c9000c280203a04086007954101d10f24103000c80c029071140b880c00801c40038030000001154010300208112091f145d0050b110301041800da19008075200950341c0f805407640f0100c1e0201030804c1c6004006400c99502a82a900d400c4c688401e20090541007010030720f85560306d041c0064881c0484c01203102e010b000b80042c10b0920803540401402e02c1100440300304004003801090846034100007528103207a000f210144d11202246000c2000c2c0c0f01d10903005019a0804013404061034043c1c1002e81a10f000e20028050503803500306203c1e80e445082219589540099 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 708014919 1250 708013669 708013693
    0x15020306030604110103090b040b07090504090b07050309031215090903091f0e150306100f0c031b0f0b090613080906130b070507030c09020403051c05040504090b090606060309 77
    0x2400400440d00e046c100850a09510303156030010200484003651181d17250800c03c110315074040d01c407401501e42240d04010003c20360304c856007030602c000c20040900c0710000120380c4c80b107002c0042c0d07184828a44000095458175a1181805606400c481801160020301203458844d0200550395140f0303018087d03519150107105c260304e21088244866040c0040c0284115007903e51324101d040e450010551240da80c00c0c05000d0000d05548607001e60b0812800c0460082c0d00d940c0640306c01900c603010b02d013809031070407034905081c20780b0240e440042950000c1e1b00318404220383c444407a0b118852240c144d80550b5070700c0f41ca10403007461000d001843c0c1c0d81e0070800c4031068500709018003520200384140048a0b83c0740c5561715202c1d88154001d03503d0390b1040c64108200482c0c10a01001381010000641c00c040c595a40c56a444500e403007114204510754440c640071605c59800c0d90010b0100034030a00c150003d50400c070b004000c0a03115109540070342c500264040c180310040320300540c2058010a1114060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 708016169 1250 708014919 708014933
    0x203070f06060f030305071a07140f040b1b0d02060702030a0c06141f090c080a0c020f1212010b040303091203030e06070806240a03020903071e0315020306030604 71
    0xc0071500155641c0c0c1c00f00f4400b0030300c1c43d960040c40c401c2d11107941d50410b500b00701502c07040c0c1328000b05114210400f000660780d80801030031003010424484a031a4412030680d030106004540184040070b0000c030f0070700c1161b0180c0380c540c00c120485c10291003509010807000c9803290411980d210143e8010000702940510034203d14034110301a1600040e20b603884070100b00000300a48646404840c500740d201d18135500e45e02c280b401015088002c11548001c600f01800d64240104022071440d910100b8501c00d900900c40a80302124443c20b440c94020141c000306299000a40381d00c03245182140046180c04c211002c40b07080d240c054442040304c514240d1001104084590200c003050740307503203841c00c1c0c4900401045001d10b00c6c81d150a9018500030b01840b40852102c44903a10000c0c0d07846912071a0101c0e03400f111200002d6181c0541d54501c1c0d48042032811486034011807000986032105e07141c84842c4000d503025a446141da80103d201c0020701d0105900040c2d80c5164144c0050010030009128 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 708017419 1250 708016169 708016193
    0x30c11030d08180a020901032a050904151b080108070603020c0a080a170403080f0f0f220c09020309070509070e0108130f0c411507060209030715020307 67
    0x4011a042420560301003051280281d0040f12005012501d072040c0d102c80c4030100710000e0162003249c411620708000142264006403014000d41c05c0c06200380d4040d002500040110b8141401d4012044920303070000700840004d01c500761913400742881c0414401d01c40d000304c5001070807010040c07102e01030310f0b284d5074000d41c001c0c5006002d0241d08100041c41400c452041c51169000380ca801a00c2d103090807601046900080c40034a26802460410243c0088025000c1e00311800444250791900c12580c08440c00726030113800340400410b4139000a410750107400a51003170a100c825204642c3d960f03802d10408820960303021020489042c4200c026510860003940d02440285014410001d96113a000d4247c03070300030080d5424941ca0600b40240f1201c480c80d4907c0c4020610700c030000500c1401042880c1c1040000c2e80400500c8516404403136441110703040ae040c0854003140e941e5001864050000c1d031001c88124040d000d81403000800101d141d803541052a415000342d490f055441d9078412050301c0e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 708018669 1250 708017419 708017461
    0x6010b0a05070b0108011e1b140405031005060a091b0807020316080903010b030601061413050910030c050a050a0605090d06022d090a12140a030c11030d08 68
    0x418440d24012802c940d03c030314000c014031000005c405c44400060040c07806810181c100d030710f0500319600440301450000702071004192900301e01c0c2c105440800030f41e0780300e0b50340b00513854481c5001c00f40810159601050042d10100d0f0782002c190740e6240580247c9581c496003100d00440b551142c01514098180207500047c5841900c2c9402c04c507104a012134502c80005580300640810503909074103092150342c040304400c8005150540c50410000e207a281c001c8040c6101c0040405d10781d40034000030b8065005440000c014146601e800c0c90315103400f0b0342c9440140c80c02000300c00d0000312400c1800e0107100b03607000174000c10185d41c2021400d65541d03111241d40c0e504101d0240380714000c13881d288050686c5028103030078142000b154018a00913819640090200c00404103e59001c80d5150b00d490001c80301e450a0b020b107101c0071418107080c0582200005113083c01b85410003420194000000500184102030381e0f04040c6504042c5903441d090460402e011031780400103e82425802d8001d880c410b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 708019919 1250 708018669 708018677
    0xe090606060d0905070e061e030c06070204060b0f190e0f011d031e0c0103020f070201030c1202040e1603090506150d0c0807080d0c0302030403061a0405090c0906011106010b0a 77
    0x203000744e40341c0b450004240d01ca502030383c0d403031030901009240400f443ca40440038001c1040d03070340c25000002030b1602c1c0e2109500b80302d40130016203070046444070b070030410040c0840144d030340d1165008072244140c1e0f030083d5191007a494420001d07101c158058070140c43d5507000501000725425403080191000750241101d613580c1b00c10041116841da40801080701d803c00510f501d80c107400001540e8910700244d4607060760502d40140501c12000d00c942c3c0617035442940920300401d50070380405e0181c943d40008800e82840600024000c00c8042d025111207001b5200e0440c4182c04181c8a282101203903482e84009055801c608040b920548054440180325540103050304403008480d500c0e44044000781c2d101c0807298010b00400c10075842c00384051650b0100c507041c107441302200c2e070750000e480748103d000c014002540e59681040c031103440e003400a13090001600411540c282101c40d11b83d141d415a8440c0d1251602c240000d000d948a800c80c1d4100c0034035a4010101642082c3e210308031038200340780c50300401c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 708021169 1250 708019919 708019931
    0x7080a0209041b031512052104080a0f110901120605040618050f010606020705090103351c060b0a140c1509120304150b01110106060201020d060e090606060d 69
    0x40c0c610954590b00d00c02c1d02d000544404014529402d81080d5002c1b540700c1c0c44502c40780001c00c03c04107003145095001410117461541c441102d00e5240220b40100b540c52044103100000c003c24988520325071802454101e070000b600f24100410540c0034000c1048819580d02d030540000c20941040b50001c0c4282c0d00418076421a661210740440c03040170949035a4001c00b4207000e194020b100320340c0603004510161900d1420500403e61580c01032000601285031000d0003942c103507101703402c0c0b100c44095800c803144c40d1810104c0e0b80c0482e0840050f034103c4610350520500116240d110707803801c403000c4150311418410702c0f000c1030703810181e00350b101c02e16500e041041d610303119000c7c080040c03c403074940a14a45414850742c914a812100284165541000c009120209145e00d0014180642d00300c4041500c11007a401200d1207500d60103810003035800d00b100844d81e00c0e01134001c0c0c040f011034004e041100c03560703440c3c3c9408603000c19902d00f81d05402910203c0c019082980c01040d100c001c0040108034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 708022419 1250 708021169 708021191
    0x80907051c0323181806091e0709060305060907020d0e030a0206071407080d0519020c030604060b0102123c070606092306060307030e031c110307080a020904 69
    0x701d82c00e002180070f4000d000180c09004241e820740102550380300761a140301d011040b407030303940c2c405001130990751264805000183c0c0d0500b4040d100c107904a0188804002801c100001801d140054003583e004642010002401c0f424000c00b61442268070b80c2c010036910104102c00e8489541d2164105e8060085098100160311340c0030091080b0340c070448402404100b00f814450518405400921071341c1c00044812144075485000d46a20340001030711744150250060301a45881c1e0b00d00a06a014080d0341704100600c0300560018800380400c2c1c090712852403d1182c001c48900c12000d00340090302a4020801188050074042842805943c0c5803400081d10090300041c07039007100201b1184075845800502c40107095000c3e903c1120300314110843c0c402d40318000c0c6010480d0080405014140100000710254030039003000092030fa0340007d03603603142c0c8010031380c40c010782e104480c01210310708015a60515412240c00c90b84100419503661000d80c4407801c0c40d0000e03600c0140c000c0da10644600c21080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 708023669 1250 708022419 708022457
    0x180e100b0f1306050a090e0a0b09090c01030b06120a02090f06040b0a120905100504080d06140a06020a05190503071a060406050604050604030f060212090d080907051c03 74
    0x207080d400003040700307490300c02c18108510000700c19005082040740c244102c5030382c2a04070154200396503d1101600c0030390b44604141d0010002e0b200040e90100d20718041c810079001c04a0024000c1c4800c0e40c00b40811980c0e8024800c0510800504a208040850008000402590281951010007070204140024050000d0740f03a420a4201441340d070800541c005c1407a0b08003040c00ca840b0200741080c0074000f802e840341c0c2e40307642005452080c00c40d210700c000b0b0204600320301220074010501e2410000e8948070118120f4400b03c129247e8054608900d0115401303000086410741c2a5020300100301c4d20780301c40c03079442c80600d554130111994401400703000d0014013400940a031040d03018080c6220f034a090820802030b41c110760310a6005160400040c403090f21000c0c02c036019a40c0210100289130801d1520030000d220740700250300d4450986041c041c04200200d080c5440d01c0880d60b86111580b40c4000061300c4130000c0c410a0b81c02582240008403424416505244990190804020046449480d12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 708024919 1250 708023669 708023677
    0xe0603130b010e07082802070201140c030a02072414040503060408250b1506090405070809160509041101120507020105091b03030702090c0f0a08040c06180e100b 71
    0x41c444441020800000f181d100c4441c540c0203e402c40766811b01c8229440460301081b919607088212070b000141b500940e40070b0200144619803507641250381f120030004968403900100c1c0000d00600406000103200303c0d90000032ba40800d4075000b01c20410580d1101960100ca922481041c110030a00000034a542d0511003240700c0c0740103000080e5100c0a5006a10303403441c0300c2c1c447c0c451220f4004416030124000c44e15699210080080d00901d80350905e00065041c080da030120f683c000c1c2001d0400c407009034030140701402060040300300c8003401201d6218218040450007141d030002542c00021303010400030010160754107010304010019911030810754080e03c100b2569140543e444030144401c00c1d204000202c0b42c21010450041c0b4100d001c00060703102d100d0000081e00c907500c25004544021140001c90309803507448100703560b4038640780c5c10103450040304850648002c10500000540240603110300e015203c500c003680b2044500708000c110502d0409404103d90b41400407010480300c0415000b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 708026169 1250 708024919 708024929
    0x6160c17030d051807030308280608010506120a020609010c0f0302010614100203030a05100f0305160510050a0819110d110f0d0b1503040f0614070e0603130b01 70
    0x1859807070042d4507400007a01c4000e03210042441c401034980c1414080403400009582c0d1626040c0b1582e1104610310703103203100380140d01511446d8540c419040800c7c035803000d411101c1850090110ba03a03503000308039480c0c128225000003a044038034840d0042c5080e4008100b181014108051403180c50b403110181660310500c21000750790b460800f40060004101d210042410031180c0c034041410040b8002d40303e00002d07000c1d4420984880210340600d0108a0240290011038940686542c4d00c4c18074568801858100945a05420030003048509016060700912040b40c0c072910f00d0b0580c044421074405000404108a110f078110301d0b1800b40c20756014014000e407900c40c401362100f00c0c4c15060000c581c410001c5407100001080307054aa481d420040c4d5201d80d09400c400161804440c021410490095413410021803000041004002469407005001402440104201c0c100040200c01d1901e081e03d400e03000c900ca036a003107062480c1810080da13009068401c005541d201c41d50704d08001c0c032030a800c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 708027419 1250 708026169 708026173
    0x6160912060f09110a2114070306050f100b04030305090910091b1b02031f090b07051b01060302300303090f0d08041101080703141510020a0206160c17 66
    0x6101d015141090f00c20010b45415015100c401402e002c2c10714052045c0d90000b0403060136001403481407c0b080c00580000c6400280900c090b1030400c04400040404030303010300505404110100c2c4040842081d102920303455111140b41012034420081c24407070041c085032040ca0365100209100e0032500502400d422154001d4003403e14201000d0415202aa069000740c0600d134100c0c00540e40008487d541403203005820210401440f02c0d02d00174110103400a0002c0041c031007030003a00782e84007000700801c901c035104103a09603c40303003505801c3e01c03040d11020f540b14000d4088a10825202d410b22429852140c0c45146180251381d0358178195081120191080c2d007101c0b030520144d54090003450784c0d6042900d0220560310340f654600d5000c6081200c0070303042011400001d84490f0003039000c00a418040d0010300340b07525040c03500c00c0a0701104803199005e08045280a0b000500000d0300c00035441c3e00601d40d5050501505070888241000c6809480d088040c02d40003900504585600440d6524140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 708028669 1250 708027419 708027443
    0x9040f140a0b010c050709022503090f0815070e06041701140903030f0a02070c2303100e0718180c090c0c0803040201030b0120070806160912060f09 65
    0xa424400c03141c449103468180000c2500304c50001e140450781c601560004c030760040e107440844840e02007400c40707014202c00c0101099014000d0582005c00b00040302c40c484028081c40741c0714186503440d407260040300030400c401c40d804520350600400280101d00e4001c0c110f103080550315640400700004c41030095a55964840340c3c2d4140c9140d544010754030440901c001c0d440d604041280c403c0c404001041c034480154007280707030000c200840010b04005d01041c0e03c461a0b2107041c04c000c4446c816403030907036403282c4170b40c419801c103042d214001e00040700810405070070f40924001004c2600060120000e461990340e200e002020340c10303801c4034280c060244034000c0c201401c1a080b5822136070255003d80038402c10303240d1000000e00c071004481d4800d50a29002c28540c17480001665a044003204203800502c4003d003112135140e001903c80110340e40d2000701c1d041515405620b40600c150386402400081001c08180b00b6048090827842545103c1c0d0302c001a507281040c400000ca80074551300302c0321004100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 708029919 1250 708028669 708028681
    0x9050105040b15040306110d060611010f05060a050108061318030f021203040f14060c0c0c0f060a0c030e031f0516050d15151e050a1409040f14 63
    0x8810340a0b000c0041d02c9059564084040e404110b001d140700c000c110980700d41d90032008680d800305941e604a0071000030700005e40c4400001e40f0044904180288540c0303840d41d80c58940c4c206018060103940090b103128070360341c2441c00440f01d1103401041540c02c0700d1062011640e1480300c0c498480070000b00d07090b49111b894145001400b5034107492102c4219480002901401c90700081180c0d00194095004888024030785803502035985e04080c401028091034042000881c1c1c1c100003826180070003800e0f181001c00b80002c2014026014041a4111005122000c089405000446016130080c00d1800c0c40841103000a440e02414081e1010710a00c14003035005000301c24090f01f504000070301741d03901e2003032040100144640602c0503010f440c0c5480e240d00e0488025454091409040040784010703550000301000f0f80000000c3c1c4030049a0940c4400b4140501c2c815000e441c20354010740e544420303640c4600f0301440540c2050304941d03440f5940e61683c0e08240f64a101f0385401464030020060b07985010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 708031169 1250 708029919 708029921
    0x7020a12020105010b0a0c05010b0d03091a031603050612010908090a170a031b02130e0706020f03030c09120f1c020705210106030c1d010b0c0a0f1b0905010504 70
    0xe428098107682c1400d0050202c02064021785151041900c0d0a41244c0000d0810501504043c00d41c242c000e240424034a061690000d0a0401e45030f00300d014110464440f42524010f00c0110380902018044511035400c1c07520a030815034210000030821003802c0c24003051a421580005c2c01240c0000000603c1c038100d0400250040040000143c1d5a4080e0700490a16469060802d4000c041045403d00c000c1c803801d1501c641002320b80c0191404210f20060500300c0024206e000b44840d0603c114040003810a01c0010b59501581521015609503202e40031200d503141c0121703900301c2c2d0020408000c203011100420840c2d114100f00350080038000005902001201144c03d0400c04540240740103100e1b5881d0020003e40c58075040464492903614000307454018425a00002c0409a5512000811158484a202940026014507042a41da40e0300200d041e114010303118145030445d405113804141c410f80400c1e01180506480c1071a1107108940c440660300700d07008652416a1140180954201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 708032419 1250 708031169 708031193
    0x703050a0608250b040602030d0b0a0501090303050f0f0c01050f010e060a03080d0b030a081306020a1109090f060a0917070b180703020a17060a060302060301140d080307020a 76
    0x1000001c0200c503007009007003501d880b0040c24140082c1c1c807182e44507684040300740141004051640410742c480c0e4132824000d4403030b4402050081c40c0d174200b030b0000d800c81c5402c0880c8400c843c0140c4070188078518598040e01c81d90042c2e40a403890040c24800d800240e410301000300340d00110f00000190a140194210804e900180c100f80145030300ea10410032180c480a42d26000d5070781007519140c49014940c4007001828403070310210340501480560100708150070000d00809a804180500342c42e4031100200d07580c4604c4000035048001c1035651310401d00b40390318100c3c1c0100d400e8040c0d4011050850500789410400d42e00788190315591200d06091001000d010202c02406c140b24070b01c0c1c1076803034481282d03481e000350910750b08000014447c1c00d00301003007180a00440d8040e101035491a40e5003085040100701e980c000b1094021500006c1e1450301c1807091038241d80d4002c04282c156400c0c03035400d941611800c1c6490342c000003003020400108904070055441210360354001c106102ca9071070207040c1002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 708033669 1250 708032419 708032431
    0xc06051e0604020d02090a4e0206073008151c0f0501020414040527030706060b04030c0608130b1005060c070e010819020d030c05060a05070305 63
    0x5914a10542849100300035a0441c40445002d610750b05415094030080c03085900d9617510208081c000a0a00302d5415034600b01000716101b085c480d00c44070f0318018040c034a0302000c120300705140e002c040300c1100003c09040c814000b030b02c5181400d41a0352018002d40300181c10320110211241c4000c101014161140e145d160285806951428903007419100c110414441601c50b1040d00c40d5003080810020943d210795411a0803505201d0303e60130054000c0d805401580011b8007004009030741818180142d03030240f0541001c900050000300144003555502614110960208211510204d00c0c2405404083e001c4112084e54640c65460900f40302d0300d1540c0500c0c00d10440c1000c1140d06650f8000c41025142c01000c00c3c00c241d42c80654007246500307245c00007a4440408620748402d402e0000d02c00c4165898411103c40702d0740c0b6251080ea46c0e10051202c590a900745107075080c01070910f03007140040303503200e810015104641527941da400c01d00121000600c0540c1c0e10b003007050003030341401156017202c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 708034919 1250 708033669 708033691
    0x13050d0504050120010e0d08061305010617100b2b0b060414030307141e120703120902040207050a060c14160201210605030705060c0304062303070c0605 67
    0x303240c0320001e040c0e0118244201c034040c4c1112001d101c500d00a410143c03400c0b01840c10740c1c101d062144400391143c18203403107290103a810301107039015441d040d00c1814143c9580d03440b100b0810181d020f90075145c0768000c200035030300300040600180700040c440140c441646014000a04c03440c403100241101104500030074006801d10580e510541c03140c0301242e098801105a4194810010000c60720314030400c40c0081400e0000c2d0102c00003000f000c1100c1c00f0800321303188460501284d0440f090b60ba0207a042080b01da40b00c00704400c40000b4041e4a00c18541b1960140c00301c0c4450b40c640000d412608900340a66003030b00300155200030050315200c0c40c416003203503080c0805a03e14100c0c41c00c5080c010048a0b00c082e1130040307098000c2d2780c0989165810106501d4241e07083c180d80b6100c2601414291290b14028441d1602c00304152400200ba2001b07296210010350506140040c11a100f0080b20020308075408031185108003440309030001c43c461031007616151450842d620b007800445034000c0c8560311038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 708036169 1250 708034919 708034927
    0x3060307050a18240303050c030f0304030c0212120d02070318030b100803210406020909160e060909060d1b0303020309150a350a09170313170f0313050d05 68
    0x1071504d0f1543c8010790750580b800c00e4490380d00032891403441c0300314800000c001001208010405600c000f0300f001a5209851a88201070207501450781d810205080401a15051000403043c20b03003035002e03003080750292601c0d00d0807810268124082481d26002600c04004001c10002200c00c1403050380300801d20b403402276140c0180d01188011282e0105011020580b00101140034080c007a0181c810740080240341c0f07a441d050183c541c00517501144071004c0468440ca080c111540b4114040d6100b075200900895182d9807148208150034582401c01c4500708403060110094600014018000e148250011540c4408290400903519a16120010715107020000c00b02d002c2d40c00700c284131540d04107224850074024058001c00e4900820210034560944020070040140b0ba16000304240038054a640f18519406180d0750003d44802c40b101a104039203403280200081e84108103104210368420020b013028400007645095a000f80c030800c407581602c0300c4071002c0c8241448026102250303820a2860 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 708037419 1250 708036169 708036221
    0x5010b010c0b0f040305250606080321070201060317070b010b03010501050715060b0c060f06180f040302030d02121501030203010812030c0d0c09030303060e0c0f03060307050a18 78
    0x28194004201d02d6003c1503100108080600034000d5500c0810910100414101800e042030b0390b03d041036005482c001c0c00c0500c0003800d1600881112200b0854541600c40c038001f802782000c10305000350504046659500d0000003141d018842650008410034150f592850305060844841e40181c125032000181003004010036a00182100c50840e440b200b040301806403021480018600303a4808104404001102d190402c3e0118009104424101c6208880e4071040c06010850703880031001b90079014814049498242c10182841c0e01510910440b440c1c84606600724007681c01030b440c025000c41d030503030034003800314441c4250914100c020710301141107614044100c0c0d0b407540c010b0010340110400102041e511000841200c0118001d070005000006803100010304281407480300707400091510401085400d048981075000741040c00c4194105600b0044000321940702030452b603814072403e8400606c82c4c940004900050004003210040030054480548c02e60740801d00d1352000101000800d41c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 708038669 1250 708037419 708037433
    0xd081902090d020d0c0b1902300d27050c01080402060a0f1e11160f061d150903251509030503030a0f0b0d030828051305010b010c 57
    0x10f0380455000f0a00941c40c03c00c1e14007980d40b17401040d015000090031701c8004010345040000400f180d0308980c0c51451003440c5c2d402c200400421a00c081d0500b64948002a1440001c1c003d02200b0900c00135107080c25014040c0c0b03980382d001c0c025038100304070790b8200244101400303140300b110801c1c20300c0c80d00e6103480e81c002802485502d006ca014046240d0110401e00d01c0341c404a1006080a00310355241c42c44800041c0c1140001c1000c50840e11807800403602a0350503107420300459000c0c2035903031103250a00206550019a06003104d100703450403403a02e011590350810a0035004041c000c0c3c1503503484a1000d050600102c6c00342400f452088003005401079010003031600442d15810310030161401821411103452249500c0502144404000e100c480c41c2d0503400300002e000340c650104203502004007401200c6110901c0680443c550380c1c0080d603284480f9107c0b01c00191120b881490708004043c403807040318000d481400c00c1d081d4410b81001007103001d1144001c1c130102400c0488a40c41d090351841d07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 708039919 1250 708038669 708038689
    0x41112011503120c080d0b03192d020301090c0e07050403110f01050c0f24240f0d030504051e09071101020405041a0307090e0a140c030d08190209 64
    0x3c0903000c0003500a90410b12903514020155804240640c0e078010500360f0102511029120350b200e80610b802d03501c2407004500c441d54140380e002010b10580912404043d41890002070003d070003040401c001801a0b8080c402ca4400e90b12660302d90f001c6a017064801400000f00405003414414104070510101d0300b0380514807814041142c44000100b844001240c05c3d01178200c6900d20340c03040801ca038407190b00200c0c0509220001311100b03104040907003036040c2124020b441101c500408070700c60440400182000688642c40a40348a100d500f441c004600000800c02e41500043c030f001c18240003a1505140d0350002541c6e42440c4001e4500800004851a01c0503201c01c080c0010001d907204244002c1d016280200001041000040710841a09031180ca940d0340d11440b070300640d040868845c6061090302d003060391100040507060b8042d40c800800c4100c482c03e41e40c040c40303001a0550165010059030b90490704991301c50740142010380314180c0845160396003202c1c1900500c20610540c45040c041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 708041169 1250 708039919 708039923
    0xf01050910091a090a060c0e0a1e03050d02070e060402040605250c1418091c0201060f060c03110f0a0308061c051b03060903031617041112011503 64
    0x51400b950b28100c5031a94441807150144250a41001000709000c601300f0852400f0782014040e90220a0045a011a005000c2e0368420088401030100c404030b0b641440c41c5200040c0e00c0700a440e103035200c16180c40311588280300183c0c04401d040c000f003c0d10401040d0000003c0d81e05600701414000054898080d01815800f400750080304000c1e096140320406a41642050760b4006840d1a0349421400c4400c188002d1f000c2c08501c80707c00c010b440b010928503c90645071010b00b140498503a0f102400c00d82c0004001d0031507490360320100320b4081001c10100144690303104c4000998441c90007919005078941007040b1070b003103078100700c02400d40454003030300d86503152400005990700e00d800030301c0403a80700b060304203a0085440305000308100020544000c100348902e80000c003842c4020582c2e1a94200e5524940c0d420510200c0e400d0280c0700d80d050302a181a0070b0040034018041c26403621404d045906844010300d00c00480c1c4c4c2270404190003440001c04000a01c0312051010f200b1364000d80034400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 708042419 1250 708041169 708041171
    0x10b031908090d12080114090f0402060f070c0f080f0a05250b0304030e1306141c050d0c02090a0c050702010c080c011e06060809061f0f0303030903020f01050910 71
    0x4607000355482d00f440b5500310303a1083c2c2d4400e0a1400f0b200080642c0003d00510b4a00348500c0c0360360196217042c20314141b00c1d651720384010615565907802d02540307030001c690380700b12000c042c0919070009a00205000150070408900005a803610720118030748108100c908400740c00c0340024202045000c2520719200c1100d402d42e188200314541107540a11690740300704c84822340441400109a881416062503107422610b14010f24224103444c8119602ca116900c0179024000b415021810500c98905480d007a0600f50714403510244c0320b841c201855126003a00262000d01c8103000c6241030003090340c01c041c002000704181440148042e0441c4603100c4041d040c07080c064048030410110108481d1102c3e2006d009001003030400c00321800411002000d001501d003071041c0401c1480c41034144a02c41c050002c010441d03912031840c107810440c03600c2e4451020401142011510506210049000718801e03900002e00c020641802400c2c00140c40e481101b40c0d061400f40280c44500040103010307010350f140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 708043669 1250 708042419 708042427
    0x6010303030c05131502100b0307060c0812070f080a18030806030115060c14060610210c0e030105061906031e05010902040e0f01030b01170309030a050f010b031908 72
    0x2c815202401074092100000d04105400b2400b140110501d6001402c150215820500054180015500c912103019016800034008100c0030384217507455000d2034000c0546501d426131900420a64000407240c0c000803800c415103000f01207920280031540408410401c200b549040c443d843d07120031f121400a0b040110001c04265903035400c1d0f0000e2128100803190f030030400e98541000e803801e20072010a03960074664010b180500040402d00710303c038a10041c071480d00d8003110305041da030002c80503041140280c41c5d00205003415220303202daa00048034a454400c0460201c82c02c05096840080005001e02e4580c128540000d990030a25819140c1c01e040c00308101c00014989500c2c80c003240c0c20300103c2030404000040c1c80c0d495500800680e20f100941c1100c0303642c1c914400f42500c40a21005003510000b800420801c80200c9106081c55090026680b40c542039000291401040d01010348854010500100c1c400d6400d219200c2c030346400390081d10008100244540d0040700c0720002030f08201e4001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 708044919 1250 708043669 708043691
    0x2041e1d04060f1409070509040b010504020a092d15020601060503150307120c06020f06040f020105070602070c14040903050f0903150708040501050601110307061e0911150c0601030303 81
    0x904003d18400d00d030001002940605120300070700c00000d9507200104d009801010500d41050f0072010321580d0403c0c031071490b59113050305000081d0b00400c00304040000d260000705e20003004401c5403c4a2880410605c0008002d0a0351944c01c40b00b40e21621101622a00b245c4403550040341403411208541400ea4481d0340d10700200c044040c08540103035140c0590200811b00c50a01c0f015101c001e8000d11484005544944069030b48800d0400b4164003035102c40300040c0010100c20104840503c18988541040da09640d2007050360000c0808480d00315030f01e4070500c011048030b26006080f600882d8180040903503230f240a00700348203100780f0b41000da10005003505a42c03410084101214460342d000c4172a454400707001440e4040503034007140d403075007000c0100d04250707c00c4000d4102d07000c10002a610340300c0c1e03a98a0303400030030344c5480025070102c59030180c8262054910074905498013600c0040046c0261604205070725036400101d81001e0340c188510640f400d80000c1d054192641410300180c1001c04e2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 708046169 1250 708044919 708044921
    0x90b10080604150914070c0308011a0415030506041103010f090e1e0d0305100501080a0c030f050109090c0e0411060c030d0c090302040b09072705031002041e1d0406 72
    0x80c080c2e00f09810f0310094001402032659020080e01074800355003a0050302c95580403504610702d80c030f016000825000051040900c200a070900d84400144080e16041c0e80710350b49140c0d00c20550303000d030110780d5807410407040381840e000e00700c6034100d0700c10141d166605260f0581401500c80c02042d20665075202c103146883e40420405001c4001540d1043c0d0900c802c10f5160380d1580303900c1242c4002801d11010520001514883d482911016180d4110faa926221040000c01003841032404040d250303081030014040d82e10690b406003440d140c02084041407414166424001680138800b020980400c01c404a502e06a035089034102c02c40710309a48400380101d491540c000c80300c440c5409840d2402c0710f15096002050702c4101c0e8800c0d101440504010301c100010740004a840344041403400d4611000d040310041458075002220303079280c01d01ca84450200e440e080d000383c081c20011340d000505101c2659280b4003283d0005078503400b40d100034140078004110020102d0a0107250320000f020400700460303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 708047419 1250 708046169 708046181
    0x50a0e06090301181518060209030307060c0e010f050c1908190c020f1c0b06010c08370504050603040602121009112d070c080c030106090b10080604 65
    0x40140203104001800101c0b03640701ea10400103d0390314103114900107400703d0728007030301c06c0500f42075800401504594039000c02030f511802140d0f615000c1042141c00142262145484540b210360381c480701141c0c1c003000501012001070701001405824003d1003040040000c84000007a65000300300c024843c1032030625194000d07610707554103140340c1c503000b041120780c040c10341c41e140c80c021100c0158403500c420034806480303000303980c914504540c905c0c02d4000c0ba0710b0030002c5030407620614160200c01e05941714040301e40c00c80400c00e03084488480700400041601c0b0687d00e41c0d070401280182c0c402100d07540140140c8198810b2070b00500c1d0110024050010550680b1841007903000314030940d240c00000020109450300071103c800346440103003140d104044065030429010000c844440c1740b800180c500c041d1125145c1c0c00d0710f0f200b0400090700011030100c1c400c0000c207d004002c01c54528802d04260035112281c000709c0c9030501c2c0005500007a940c0e100c0200c115841401c00401035207076580402c01400c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 708048669 1250 708047419 708047437
    0xc06060d02032b0311040509070c020a09020d0b0f040e2a040603080c2e090809031f05070819050601030e01020c0309190e04021c0b0f1501030c050a0e06 67
    0x2110402d620300748a0080780d0101400740d0f42d03a0401c206030365010740d0916800740d40910380c3c004500b60001000103009400300b029890000b854089410366034410751080c2d038800b28032441c080707495900d04d00143c2408116101c035500c08031000d100a004480065035640c2c60b141a554041d281184003c50440780720418000311440035006018494030b900b030409071580840300502140c410010b1106811100711040c803900300301c440980385010701202c42d0760003400b144030b015910b600d010050901150782c100000820308170005110030164426041070021114020502d0341404124002c1041d0b40207002c90004181e038418400080c80c0d1140001200101035044002c0e81540c40081c1400d03100c1c00000203000303500400c030790800072180142c0140e840e02c03040344540c484008151001c28018079104100060403440c4107118401c071269030b103c850b190031040c0ea184081082c00c3c400d00c0441100c01a0028086100b03080501104103440b00081152040010074402c000a18081080355620041140c66804e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 708049919 1250 708048669 708048703
    0x1003090605150310110f2b050412020307050a030305090f0703050f1605130509030d1103250210050601121a0f1c0609030c0818040506060c06060d0203 66
    0x2c80c0801c0e051000e071040005030340c070038426001600741c070002e98040c02c09030070100c24a00e4203020200c00c0564483d00405600c01400d045040c0380780d0140c5142510212440111002040390704041c280340003001e523515205400c540080003410082000022030384111549460009140d5640c00561420403400d541e8200c1d19001d40d1000005102c00010b0701e1031008000c40980e0142d19544074038107500c194500c91180c001005855007506580290321003544107680c081500d2605100c40d000c401140c1480344c28206504000c0140311646881c0b2071078212004038041c1841e003958200700080d54070840039110282003921400000c0c0164407440160382907441c441018040407900e0300c1080d41e01d0400c12403150090f103135851490558503001050108003120b0000700600b60390b13aa00c40c80c000d402c800c00250b05015407640300700c0000d01c2100c010420a281c2c00d1691100d007460304104401d071103000c0d007a81d2140c042401050300c00b40010035011b400c52400c4903810340203010b510102c0d00300f4017114003804003e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 708051169 1250 708049919 708049921
    0x1e06050924300f07030201020712080f0a05190e1c03110a1109090c01090b0a05090a27021e031503070f030b090d0f03051e070f0801150804021003090605 67
    0x3960002c03034059154103002082e2125070030f40300f04456035801c2c80c1c48041c0c0141d014580411048484001651034507000300c7d0658a0002d0707845840708540c3c8032403456000034500089a501a05100301540010300d581d1400e040070281500025940100e10905601c486017001c000c3e034101801103ca0302c0c0a07207040720540e519140c0d079081c080c078503084500c0cc00740100c005034002400c02902244010071090161500d010540c1000000500c64101c0c40b03100c1e00b801001c008040d07035503860040001c024800c403a110101b0405d144502e8800850803480c000b200c1f8014480c1045150740c02042c28540010100c0150301da035641e01400727144241d203100468042c000e01074049480c01e0183c40a80075280598032403032160314dc000020380d40d0640244414000740c520311000325428482e4002c0c0760084041c2d01b0f43c07009a661580c41603040d15058541d500892103c0142c00c181c80d4200101600400303c2c40e0b6011441d802404000d42aa100240000c0c45000400d0500c02141d000754070030319549401002c10421 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 708052419 1250 708051169 708051229
    0x302270703230103082a06040803071106061c170c2407121a120606040c0306051305040c08030f0307030b100e100309061e06050924 58
    0x144002c2400a40e00740c54100c032010425041c1c1c2010b41260b50101030180751007a078420309000c24802552030750034000c02c1e10468062400401200740140c3c000d0241a0745c0e0308088001903c8400707514512103844d0098800c00c21107036203488100c0020488d0766481407000300e143c130388031131030102103215640c14210214030101c0100700091158000310302c0910f103044142000203118051001120b8a41c0000c3c07102c0c03000c40b110b07a05a0001643c0ca502400d200061400440001e204424000d40c100ca4550080d010040580303058010b4008d041c007a07007800c02c5000d08000105488080000f120300207551171f28041410002d11a003d200140040400d60b91204a468801107260788150b40c500002800d101680c1018548110500001070307040c3c940095403050401071280544860340d400b8149079481030a08080b0b80d442c00b40103000c45013005201c92501c010841d50045a01c145c120038003a0324141d04010740e4111100c04d4650300102c124182010f0281d0500098805007981d0302c501101c400e81e00c081003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 708053669 1250 708052419 708052421
    0x10203011212020615060906120a0905071d010312020708070b07021816200d0c1e050304090b0d060204140901080c0f1201093305060a0302270703 64
    0x6074591048034108030411018070100da03200300640e511900740028120202c101e24000000f002d2400003d4021790070300c440c494101c554950f013198403403680c2c4d072542a00c3c0104001400303842e000d0190500003000190310f811300003034220414040106446003030902d420f8010300801c260030080c070403d003c83c1c07001521013406103140e4010400c03c81c0103c40083c1d01d01541c4964607d642c0c800c0c2d4800382504c86000304480f08171140b5035420454503c8402015454280010900c42c0001c801c1640d25001c5501ca410301e425000003e0101400c80103007102a2968009000442100c1c11512100300202d202c0720f07920300144822110040050100e44000303400034190302c01c10f24030321b9054021075190146031307038a692142d184d428071a141580900d0308440c0781007d1800e280121404200d400000807001c00564410b440c26010020098001900c03407582030080b007500907001143c1000504c01e00030b504010300400d0703255505000091040c1600020f0f45076802445419035000080c840c0a140c0720f04100c24054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 708054919 1250 708053669 708053699
    0x70f080c15060114070303180b0a090c080a2a0b1b1b060405151201060509121c0c2f0102010c0512070c0804090501180c020a03021e03040801020301 65
    0x20440200e0400129698007404869044c0030400c03c145141030070031783c0d0440042100303110b00307841c0c00c0030003101002140e600b80b48188039000040c3c00140d41030160800151404d501e03441711034a6802410041d0016050801640c10640b2119140c00001c840344115480c50201c1e0304440c4000310081010b1109081c8040144480c2c1310120039200b040d400528084a4170404600301608110f040100704254180f400c080e05401c1201c2d0f6410b81020f0a0905070a036080f82a80500001035005c1760300c00152403c0c0714010008d101c0400100100f160081c0130041000080c5800010b000d6000c00c008148071650181d0b14004100031500350f00307130042c5811003020300004603d0600640c030b401ca04000c2240500102c4858143e5944880e2075079441600403102211074180445140c10103200015010705207007d400c0c040c00c10309014118081c294400c5804881c0300c45131050440d8861054072003c00e0300803500c40f4038011402d00e45c0b044000514007207840d42c400e95101520f5907100100000d5041002001c2d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 708056169 1250 708054919 708054943
    0x1080901023a2a02150c250c15030209030a050c0301050f04150b0d05010f05010f080106030302122203060b1504031a0601090f0303080610090b0d1808041205070905070c08070f080c 79
    0xd40004070300c4403882c081c1c03120907c0c4020038007500c040b014410b140b41440c1c03c1c03d0b030307580b40d18004d0300d00700d03d0310042410584400012252907100c104003114600c0e00303005490348070a280081030500c0c5095110b0007403400d20072041c04542540c440745550180c894041c0641c42c103410100030703c802d940c441040c400808091040030300d40310b00300c0c8001c507842c001805200c04403034265008043d51414003015030160380c49802e0b8020502194601e03007099005110131040210b004540000700854041d0900c10009900c0c8000c40714404104420300000b105a2a03058111000401c0201c0c95030703488005a841c20180c3e048240340d8428000d0010401d0f90290046215000544046e101c500c1d99850586001805d4001c0389000b280038484142103110a0340300802c1d1f042c00306103080c481c0b1819190700354564010381208482e103100d0251030048c44410002680106400f0300304009a1a0420000300100c1580100808084c2c0000c0c0c3c0e18103029a16031500e00403604042c000ba501e146845403280c0d600668440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 708057419 1250 708056169 708056197
    0xc020a0b13050f0d1d13060f1707051c0303110d020a0e0915090406060f0f030317070e1210140610020a030e01080901023a2a02150c 58
    0x74860402001292502010585450f1700540c20a9804800501d2002203116038003c0700300316105004000501401c801002e60300c80c02446242810b00c8201c6002d101c503400d8005601001c02040790340c40b591a40b1806d076680350300c00401c400741460110054605035152484501c004240c10b40c2c0301e51240d008001a4849442c4d5144024200c0c0610506003400c8032900304800e08260707030513003500300515032540c0648665400130b40c180e11a2007688542260b0b4200c1000807181d003000380304164000e0b1380b03d100c4484900c52450ba503e04001c00503c0f29041213041401064820021007804c0e4040103240240304000d10700340300c3c2030000c2d01120380030041103809510900c95552410b60340390010a070603014a4041d0340e040ca00e94142c00056401c100e01400340358140d9420070106c116000074408080921407142d17049503c1251a81d103c002c214403100b10014182c1c80c140b0007400030780c1c464041c0c44915080d04441641e440c00b0071400d80c180107424807038405d960200f404200413050908010414103c0641c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 708058669 1250 708057419 708057433
    0xa0309050406090519110c0613020f04020c07051003020f0d090b1b0a0c03091205150c0c071206200405030106060302191d030d031406010503040203100c020a0b1305 72
    0x12081c080c4d582c10ba640b981028203499401c1c0d5144c4403900320007070560340154041d203442d444030803162030048121103c48860401d42007510861412402c84074610404a80643c14038144800c0ca03900c03061544075440c854242c151003110140d0090b01581c03210000e101390742e81c8803804a0f08181c09048852011540b1980603000640c9191002012500c00c6d1207140110307003803594820301540c2c2d50185100a50a0001ea118002096510f000b00c00040ca41b0403805084004460303507106070444000b810101c2e104000307104031039500d1400903d00382180c20505442171150300c5424004000c20101c18071188905001d050f5043c26000c020041084410a030003c0121554588040b0308074003402d00c003560054141c001c4076409510404600011500d8103000c0c24078014118002407030840c0002030035012030340b904004501150604100b0794446028206180f45291a60019072161490342c101c07480e081d505d4038888000d87c403c000f18003455901184119041c01c00410640c501c81c1c24100445240c41a88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 708059919 1250 708058669 708058679
    0xc051606020c040525080a09140a0506150f01051b030f0c0c01030902090a0924150f0605090d0614010306021207180522050705041e06050409050c07050a0309050406 72
    0x140041200b4100c200e4041c5c404009840c12150420060110005d450700c800041c00802c10480810051410400c0248055086464800d0403c20001c00b154290420610300050b103031205240c45421200900c0d041e507407a9544c070800a0070b51410030405519110110720101c0f0005800c1c000c03c40d03207000b5802c03503c441100c000110280c8010101c020b401c500402c3c08034070f0440c1e1541081415601c168113034543c3c0702e0711401d0002c0000d030100d00510400d032140904000c102c80c0d044070300060304405542c603202c141003241c05840c0d48241440a4041c50350340c84002c0078000f16030721120b010307010313403000000559490611001035009039800741d0107140d005011860031030043e8420a40b102c5900344141700145024100310442c1942c0421b0a01c01b400c41c4484031110200d4400c1512509054540b643c07107c1c00d041140c1c030b4900060800020700c030500039040c409650041d0503a02101c04a02c0e005ca115540c4681c05c1d05503016508000704517120301402c85041613000000d10b001c2c0e801c26201000080d035a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 708061169 1250 708059919 708059941
    0x7020118031113200a0e1306060306050d05031b070e0c030a0c170a0b06090423060604030b0c090a050d03030c11160b0307051606020a02100c0e010c051606020c0405 72
    0x310b016040307000083c0540d180300383c000101403e12680c060a01c403070600c4c0c651002c01d1f0642c40040c0d5911020380ea40c0018090f55030548640c00c0900410781c0e15400c04110355640075901d208291014849188441005411043c00c205074005444214540640c6082100d085001c0341c2081c1d46110313085082c4071f0b00522052054003110108421044545071139116812075100404064445a810000421030350b1070300d03159400340d038610401a9402d0b08140008446041c40041c000c0c2840e407082d1805c00040000c202503240c42034015020040040d0b80d0141c0f83c001a44105042d030080d500101c1c009612410f254040d404810001060388031143c0e40d04008402a803102c00061070b1500300b602e501014072940c44100d014683c40241801c091740f400302c42c03140e070840c115080e15046130314039000031b1600b072116418000c0c585c10b02102c1d00140007041d18488040d000c410020320042c10070112481c10f00500c60100001c0302d1100080f001c2240d1740d6142e81c4000d484841c0001800d00840c10b040c080384262000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 708062419 1250 708061169 708061181
    0x9050106030c17060108070212040605030108010b0307030f0803101703070c080639040b0c0c040c090905090c100207091103010503340605180a0b0d0207020118031113 73
    0x5641c01e0f51410369600b0015160a500900031904510600300c50700030364081d0380010000f80a4544420351030b50702d03065101e82514075806446020740c10000007000020040c0880c1a807403a408001580c49940315001054968190f500421076101d00c6c1c181007103200c1c3d000c001081200d000d5016808920340700c800e8565218015500d100302241e160307101183d40600d1151075102c0d0030140340c0110105864010802c2030b13800c0b6802c00c070f184a40003d071030b0000303a6007000000785c981c4054030184418555000017501d460124816120702c2c0e911600003c07030b410b2050103044111940101443c02c901072180000750342e50300798040c6101203454034060b80f0b1124980340990b4101e400c010f0040c001880c03418900b4005950001c00381591840d81e0b411941c1d2414905824000380580b0350701c4de921140d8114507182c03071411591010340601c041d41e5090001d000c0b00300403038410101d4006c0142c0d80f681c1d14401211030184020100244060001010041002c100c8941480080880e00e400242ca01309103807400f00c0741c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 708063669 1250 708062419 708062447
    0x3050a0e070b041a0714030c16050303030610111509070e060d020d05070812030f010b1c021c0e03090307170a020d02010e1314070509090109200409050106030c 70
    0x41070000b0844011078840c03806000284c6801642001d4641e071b100c00503510100810402c0741c03c0480e1410848070100f014041c0d046e00c050042c48100d1500010984910000c3c00e603c3c01190103074035145180340034659030043d42a0708011581860121032009852410035181c00c0041e000e05840002c402035410951406010001c1c10010540d06e030340d08001815549902c125400e0141850000d13001900f400005c1c0c05081c044140c1d5940d103841410039062900581025000150601030300a034940000c076081040c2c0044540103075038440343d02c04c0808107000d01d415074030020f042a241c50074010021020340303121340c5d05908844a031038580042c04055031782c81002c580181c1c024583c5101510300f05410a0401e40181802ea41101000001c035a9104405200c0b08456840c0c0300328421451046041d0b0350f102c00e9501d490350134000803400003010600107100d1000e010ba01d031104042e01b0000703801c5001c41210b001d040f80383e490f82d03100480c10241c2824802e0202003441c03c1c030b203064103500402c40035001795 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 708064919 1250 708063669 708063689
    0x6061e05040b090406150215071d0409080904020d060806090d1b15090807050714010914120712060f0911060c010e012d0207030e1005070b040303050a0e07 68
    0x50500c089002d00c0e8010324450f640c000d0710741000041c00903c60300d64480c91000360340a000441c1c0b024150f4181c40300090010700400030004918541c0318604240030200180890340410300c032409041c01c0b401030103184804c41c0e00c584000383d0541c080c0d000781c0c0540201c40c0b00a0641d08550b80b50b8840c15101c507500c18011001c140341d0103821095404a1508101d2140301e003809208841d12222200100c0c1d081140c00c4032007550010391041402400c0004000610403441e04500c8031140710002082c01d076142c46054111078140b0540651035440d0010107044e00302040880394481d130349000c8028525070b004020b8074024980160041000818043d42c0790792604588000c4441c4144420304c101c80e44594000741081d5130f10740d005050400d0a0040d40000104100b0322506a0750b0200c4803c0c100c403000d4152040184100040300020340c01c000c00307500c48601160300d11507000c41410151107a205800f00180b62030445000c100070107806600540c00307200b07140e10810504024003891030b40d40c08640100320f000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 708066169 1250 708064919 708064927
    0x60c0e03160e0c07030306030c03080903010e0706050a0f0e031914190206090d0b040c05040b0303070b041e0510142d100302060c100e161202040e1006061e05 69
    0x3c03424100901441d4401c1c5400500c4907035a840e1000c80c81d44c160000c41b040d140009400340c0e103207001d0082c1d07030400d100100a000c500d03140c0315001c5c00703030b00c2040022001e101d154603c0c29072190003172080d18031324100034081ea9400d10190a001c1c80302c143d10b1504803070700c00e451540c000d405080020140c140c45a51803044541031980c1d0200403054000c0c082c401d40c4002684075460009208258403400303144120300f03c150003070814082200b6241c54200b0f50340207a00a001c5400030403401000c45800070303001500d10501400c44141c02405c0401040060b10030f1050311011010110654001c070308c40c5000c100c503040c168607040b022604080780010b100c2051f007000350012a03994030301c1e00e00e2600304000f16401c1c240345a40e42e000c44c145420042c0c3c62040ca801000c0c2d40001c410b4680070711400c03000d00c01d024044443c13411110000c181114090045000c0880b00e880301151580d500039107003416540111130740d200d4494103960241031326010b5080041e0b40c032100001424164000584102d01d144c44190030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 708067419 1250 708066169 708066181
    0x70305071e0309140a030f02010f0c090b0d180c06180e40110405010e1302130204032907050f0f040308030403080109060b071e0f060c0e03160e 63
    0xc0c1c9000d5000b0740e0f541031300d10014040c1e0346080000c0022140720b40c440c441c8411a4a0010342165590440500c041d0f051083c4c800540d030f407008403182070742c0f00300c030b0100e458840c142c170408000d25000510301c7e000070b02d900740c000910440c401042c0c00c45a039540c07001001c00c0701c0d500240800b070341c030311800d424550480c2c0454101c100d12075225551900a8902d40300d80e00c18407001d08091440300700344481808016510342c1c03d020480c95000c44100c0b040d034081c80f481d4500400c0c400032200003404a0b182d2001860100119600c002a6031017544102e00c003513440d15141d040000c51031091501c244000c6010709140f41c80c59156080c0d40348108025100c1c0c2c1e040050314407107544281e2058100c115450000c000c080002403410f4051400b0b24066030342c500751981092451000c54075150007100d2041c02c01e1000d5000980d030710020701241088118884201285441c050300309010604006000a0400010401095202051080046c4118200d51003051010080001103c560184e400080484800680 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 708068669 1250 708067419 708067421
    0x90a0206030f0702010e070f0602070b03091509070308040f1706060a17070302030105011d0a0207050a0809220203090d0507110d020d05010213050a081c1d030f06070305071e03 77
    0x352080044c00085140002c080d2079a0400805801500440c0002c440502c44143d040008501920785400c009140d8100004015510104540c1d030b00c20749615031001542215050000c5401503a0025600c0d80781d588503442c3c01189a1103000c2c3c3c50300d84409900c0040c6801c00020080c0c0a5000030303004064007420f200c0990340140030a0b840401c02d12403c44004010b0303c2c00d11802d8000c00b0b030210031404d00e001e036985020301c100c0090075606005005000c1000404c00c0800c0650209a00507246642c55102a0205403407a0490754506250388000c11110102d9400350000d6114a1030310080e6a070070803040c94155158099814040c2850241c07151340f00a60902462118a07940004c1640001c840241e40d01d03803d91307100b120b10300da031900b06400c00c1005040c00c100c44000350050300d0180c081901e080345031111407007070700e0040e40c100125141101d4800c8604030034208405d1015095070002c00703650302031507510300d0309aa121000914260000781218410f9210300ca681110f40c503521085c04000b08100c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 708069919 1250 708068669 708068671
    0x408040e0108030a12140f07030b220e03030c0f1b10091b03080d050406023f090c01121104080a14030f04060e0112050f16030b01090504110408030310030b090a0206030f 74
    0x501416500d0b0b840c500e04bd038070011241c03480b10220401908120340f07610041c0a40d5203c0010885660062050180c0d00c000c040c290f4100360740d8144419101c1c03403000c40107606140000c0c1214094002c2d00107040da0300c6813980003030a201d0b000d1080c000c420301321515072a80300c407464840546441c1d801c2c0b08e040750560542d0006c9802a0060b03001505012500c181c3e4003c00360079407040c01d003a145e40c03a50310510901c03204a071060010300266480942c0380031500c031a1a56068407201c1e040003402140c0e680306585e15400f0700e1008102100003601c40303880708101a075440c60004150f4014411241e03081c480e200000c101c3c0c110019550701203052074a0700c00309a51000c0480c134114140311905950101d48680e85c8201880344040b894030707505504101101c0240014510344550030107081401001690f6000912441155400d6800003543d1407151101052800b698204540c2030100001b406071040c0310940720380c10742e802108210703007949401060741d60f150030110009410820500020300c02201c1134541c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 708071169 1250 708069919 708069931
    0xf1c0e131b0908060c03010306090c0e0a0605010e0301060302010906080411090a0204091b020c100903080c07051309020310020705011b02031c0603020906090408040e0108030a12140f 80
    0x612100005032040c8000d8a540204003566500d2021203410401e5000c0c08200043c40c0c2c98000c0e100c2d0782468100e0307410703030301c8140000745c141c1351034021020820104035001001031000746206402c0b820640c01c0d003000380ca001e10031140042c40903503e05410f40740602c6804201c1e035050311146142031600f01c05860b02407004009071084506172406110581303460000303038862105d041d40140d640e4203018064046914050b2a15248115419413003061500043c0c28240840100c0b1801d100c00b4294600300c946140c1c03508001d020000210340d414408000141100039250700312103503000c00303d035440302d10b0480b1a440b5003e5410b130b000300c0150f00040d030254010700000340a44c002107800c0b048100091440c07200c03240c007140140d20006510002040d07071404881100141ca00900c1102d00c3c50300042c4640c6d030003a00c8640300304c4c40b00001c90104034220f0126802004003030b003c02e001d5a51490841e440b500401038040120f50540c26204200d070070343c8120444502d43c4450080c494451012601c6902030003001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 708072419 1250 708071169 708071179
    0x809030c0307030801030b0a0516030e0a021e03060c0c031c06080a0b01030c140105030a020906040e0708010501170601050d0c0210020d09060608072709020d03050c0f1c0e 75
    0x604039400c44203100600300345000c0d8951101c9945940b030100385a1000401c9548840e2806040c420b081d0088424030900309110f14020a40042400d0107504000da0101e00943c09450a18412060941400448201c1d0000c40c2614501d646a18110400344034409038050079420811804402480e105d5110300401c04001c030015496444a150364a804034102090312409420f4004008008074135880801400e52131485c4011103d840e0006000ea01000d00708007a0517070049605001d9031900c50940e0010041400d034640c45040c4070f00c02605d656020b01370940020061100305620300d8040f8845400340b141a03482515040350150400000c103e0b101d00e4804502980e042c2d40303600032190020b44a00444a2070000f41603503140790007000c4600c07561040300341d600006410044c12900314104003051514040c0c5840d800716560100000f071151003402944500c0010340c18062590142c05011b207001e094084498035040b000340203959049000c0448240440350707200b01790280c07180d44011418200540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 708073669 1250 708072419 708072427
    0x32010090e0c1207031e110708091c1406090610032a0b0414040e03040e0a06090504030503061e030c04020705010e0f0a0c09020a1b08070218091e0d080903 68
    0x72489a84405440c00c0d00000d80300d0304086da19065808401000b010000c20030044034000804001040c0100f400c081e18085022171940070329102c4003910440c80f003034400d00314100c0c0443d103400d41d4842d0480000c138096100301d80024100034400a0b81c0b6000d40380c0310700500c0500f0320b181c0e1103220311070201000c100b0031001110662090954604400080c10360341607a80d80300e50400401800d40310151074421b00c01e40c142105107244007000f00880e01503c8120070045140d0b5991706001c406000c640c1e01c800185071901c000c01082c140d001e005503019400860311182602c01404900113901e80f0568416810f400c4000529168a040e5005182c0b980c0310b0000131404000c6020102d00780a0520300c1d030b80710713070300080042c10030004641c529502034a50035204508164207600d0082000039040d580c000e202c011803e101c03082c0461117065a8065900402146007072000b01807030100340b1800c0d11b80104510407a81c407402c282070440b1441c040c5d030100702c00074214140a107104580c800e0001d4200030385800100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 708074919 1250 708073669 708073687
    0x1302040b03010c27150e0d05070603150902070309300503040302090906090705010318080d150503070b033402030a0e0108010602031e090406032010090e0c 68
    0x30155480715030303042c0c030360500c002d501074a903001c00b0005a103110b8441e18000d04c2800220303201c40309030321040420301d801006811030380040b50b040400003201400c00d00c14110005a03507513054100054010603000b5110302d0641d0b80c03040009034018035034010041614130360705100d000c0292018007002c80456030035654802e000c8280040041c0c11183c240c603250000941441942400502075410050f190014a00c51034a0401c1d04d0301c4803e140a03481c10141c40e555521807000c5413000b05a66107400c511000c0d9991001c1c2d49503402070084400302600e5440281e00041d240c44c0208081c1d08a0303480102280c0b81da51451051014126001c04154045000a00740307180d200c0d540400c80e0401c0340301d030011641c603c5010700140a440c400722805040020b910018042585e020040c0c42600390f10066501a05040000703200d00e500450156540007807400100100b40101c280300c1c9011103541c0c1ea1410f049c001c0000030712178420803541403076010404c10642001083d030b04e046202d40c04601074980f28200000b00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 708076169 1250 708074919 708074921
    0x90201090519031a0402030d0c03020102041503090302010b01051603140c010c020f010f0c120f06051306030b01050d08190c0f060212060a0f06030b0103060504021b120405091302040b0301 82
    0x707050100d0a082642c003042c000c100000031441c01c4050615155065440d0603800659a0102c440c0218108003042210703104050003501a5005000800c0351050090500c1c4001401400032010a0700150b00b088400d001a50203842210b8a51427500400c203110400c075141500e411a072a1400215200108030040340624280b050050340c1026a002e409080c9104400900b96441850980801031614030407051241d0001441d02051817280804a440300510311824003c06641d8080e54028522400901c5000d030598800d00c10340744500000780c0f059894006010140c901c000005001c000100043c600301d21a04008015001062038160142034150ba206503800d2035560044484503008a0042100700c0350160541c1d00c208146c986e4031813540740008d09465003007544214814560b03036020620040e40700e904013101500b0041d005566039000d0071358054a0031440007103c103007070140000803441300b620310301214105d031801045880d81d625941803603040e0300380090007282d00c207a4a082d4141181c4003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 708077419 1250 708076169 708076189
    0xb0a0c02060409090b0f070c0609050118030e0a090b0f061b030703030f05070e010e060d15030813050907090e0705090d0b071416060e0f100c0e010c020907030902010905 74
    0x9210b40441d41004e11324105030300c440090f00d410043c28101c4200310425078403400315558240c00c40303004140004141003450050100e07565881008a00840179014160048920001410107481c076803215a560794801e0200d40d500544950f020342041110030080c981500600114565014a107184c084103004261440d0300400c000c4010035103e108030302c59401c00f072182a9128209060104512158000007014002c050003464400c1501140b028080e96041d030041e03a98041c0c0300c2d103003079925440b810500d40c20342250f03070030031800310b9520700105407400c0c01c1032a00e014240310344600090314140180f030310000d0300042907102003040034094a140c0e641c4031201100c00901440381d040b003508000d00000c042480106d20130440303203002c01c21541300074520501e114443c3c0d00003c1c009164400001441c1c10000450305a65482c820020010240d400a0b40b006030035190a488814810b00040b00540c1c00038503480c3c02030b40c4840c5e035400103500f003800b075046890490320500d44401c5660322500040e0354252 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 708078669 1250 708077419 708077429
    0xf02101806031a09061003050a020c0a060b091003170c0325060507020d0c080304050724030b0108010312110703080406120b0a0311210a1a070311040b0a0c020604 71
    0x40c0303c01c038144034158011030000e000380c000d5485001c1458040007082d6400302c2121800d0405917500000f80d07021880d54140d8140c6440f40c000d8800150039810100e000d0208458a40d109101c400040740041890040400c100c0340e000c11480c80310103075030300c542035a40c001a80710341c02e9000400001050300301081131345001e8072007403140311f4414805040210440313200800f500255401919410002d42e0130a161424503031784444055903d9030340e4617040d4246062a0b1051440c04038a0030010591176601101b9555844103a42c1080010030000044807181000c2c40302400c0d2241c5104480742c201e2140241f9a5500142d0f402c03250102d40d207a40d4041e260380135500402c001010802c2542801505008e0842c4000044440f015001c0c103645030540c80302c8102c2c0180380f050780084105c0c02c00c0c10b19001500c0380d5104400969070380b2030860410220354411945500a21148000000c0c00240244135031248a00c4030b00e8414100303400c01448448641c800c04045060041c40b0a25900503070f1800003c7c40601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 708079919 1250 708078669 708078671
    0x507020c011e082e0b1b0105060f040906140a140c0a050304020423270109051507021e1606020d08070305060f030a120f14030a050a020c060a061707030f0210180603 72
    0x5103052210101c0c090306d50003006035030f41480c0a0090b65030b0354020001d4044012a000159a4850f01e0b205001349800225000301c1d0f83c81608010019016900141d80041c401d19000e0036944c500744038210034030500382a04040765083c804a00541403c1d802110817071860030280c0301c003422aa0580070382d5101104c07041a0003254888010044040c001911a1204188000c0c408000310780c0d12642c40303140f405420803005100400040c49035208002c2820174030b0b880810119540600003410303444001140311900c0c801203280000480500c0000c41d00705d110303926503c5141e103407180078003240540005018603900564510b0f0074910790b036080c030400131500d1084115030003800032454090113403414409a031041c8220411000c022811420483e40d110000c020b0004180c0c0d205480a0001d00900a070784103144940740400034410441d07485441500d840081402600002e8600301d43d540896000060130039000a800c0c400605214103c0000540307181410003401d542d41c214554101d206d0340c040e900103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 708081169 1250 708079919 708079927
    0x50d0e060a051008070506120a18060603170304081207091a090306071106010b0a030612050102091806220e0328020a080f0711040507020c011e082e0b 66
    0xc0c03d8003448000b0940e0002070001a864000062003501030719a4906034002d0400005e62011550f41c00000f940c01300e0904050401250309259005000300d0108582001d0320310000c0c1f1096281c0d00c1900e1040382d021150502d0228003450300e20310318030081d083d00140100d2100c00304d5070540c103c480c0d4280808083c0380c19201e140040805180c404040e11400912204030300daa00302d108003064071f5056404102f0340301d230f17910051141140141042d502c150f0f202c02c50703071009904005043d002054181400c0350554016000482c412840a8003590495030011603411120741c590503072806103100103034480d00000c41d60001400d0a055a003c44a56145110f00b50b1545000500500b880e800c0341d48548001c282c1d40606507a40210351182103407400a402d40420482c0400c62484800c0c8102d0708040c105015500f86250040d40d601b4400c0711183c0801c884032030205036030380c02001501c3c0561385d55a0341000c030348800000f8000116490079940b45603281c1300c01c1901d07240c0c410582d0070080c00f180c4282c690b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708082419 1250 708081169 708081181
    0x70303060e0c12010b071109041419033c050708030405030408060a020a05070201080c0705011e06081908090d1407060f03020c2104030b090f0d0203130303050d0e060a05 74
    0x651605170003036000c040042c0070120204d90381100308250200252000e01c0c041e00d81e802d0440701020300704035600341c0340704007840001041940300310007880c184251180000c81207407040d50a0100072450403001c0030558004041010b0020900340b80160681b410803502d094443d4542074402d5000300e80941e00b0b540009001c210b981800c00c01c599004050a20460410a03806401805845202d501034100003100010440000d03030f020498000d02d601100800020512000c44003444403688441c0307244e145016400905004042030300c106c2c007031424981d01d42c0c0344c40640e00c42c4003a410006406800409084026001599180729803444000e140d005100c80d81c5000c0b0024216260200141308160041c40070141740040047d100d00084007210101940403130f4280001d103940155440981a401b10070180315008070045004a44440c621080e1035074042c4200d016030307480c0301d01c00800b05840295034007040800d201c0c402a00070f447c030042000c5411804801d003207250200030345480c14020780d90014429 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 708083669 1250 708082419 708082447
    0x6170c060a14032d1b1305040905010902010305062e02030702030d0503041203110306012016031214180301020405060319060f051806030114091c0314060105070303060e0c 75
    0x40c1000550445030741c2c5d2400840b0702d00c58803400404c200402001050701d07102c05541004085c003508018104000518480c2001d43c0a41405a01603010914040100b051800d0a0065500c0c2c040030f102170303041c85161136840c8070300c00d50540c0100c41140401d00c2f401d40103960600070208854281e5a80d55241d003230900f46903100d10200140355080c54a400302c05045d42c3c1c01c610599921032000d007041203002c140806c000302c250070522010300041c003030660100006c055040c11001070b00d0040098490400b0680d4055850700790074104000255001e00c442d1169a22134a6243e00c0080068000b5007095992400705001e60400c0d20302d5543c0300ca10000003078101c90107118500050007070b076410346005494030010403040c500a4980d02c6454442d80d001031040d403425001100581c184040703080310b904e8050040d50316620130401030001d46c000f030486285410f200c0d00902401404c20b0108441985510005549542c4040812001c0c5921408001421421240b22603c01c406540300366644617030074402c2030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 708084919 1250 708083669 708083731
    0x6040b06161b060c02061e0c030414090603070510050d0c090e1018020a14070803061507030212070201300b040e07030204110c0604060c0306170c060a1403 68
    0x7111800c90ba01040f419a00c010f0803c0300c00e8055541d44d83d10401d01d1f039104140070005408000c00d00e8002281c1c7c01c44c0754000020b1003100d01e0307201c004124403c40310420070000401e45440340e01d0340c02500103000e11319060080b5040f40c0e665040ca6854800004802c409407203e0307002140200307003016820002c0c0c904043c80d03a03500c0070a4235283c0c0b40c441c0c241252410381000480d0030110f1241c0c0800c4044915000300d0b0b4210803802d1482d5240d4580882d81381440c071301e60080701c0e071a00a0036550f0344c80e0060680d6200341c030300103689500501b150030202e041004050f001800140e04101411a4404140007180c41450701e83c19040c119942e607505c05036a0005a071802c030702c03c178050341c074280b20010414404505801a258111801b00b01c074420225840010300030032001c00d4041c00b0345000d1104106450344200c0c24890241c43c00d004107a82d0303403940c050302c8040401281c403541100c0c07212801803410344002c082c00109410544034100b8805d0303001c1816082194180420100d504032300c800350b041c1e01010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 708086169 1250 708084919 708084953
    0x303110a1502030c0d0912030c050c0a1518030309050c06040f150507021206010e060609010503040b10080a050708011d03070305071e0f06110a02120306040b0616 71
    0xa008404480d80c890241103240050100e500360b02002290134681d0400450b400c810018000303101c415101e00f0000c0d400c400c8540f5040103c2d1070440d070925013a0041090b14511903004020740140f1031903484011501ca0745496209045a130362441000356070814400c8a0154069540052001600e192051618802c0c40b249849060244020402c2c800c6440c19038084d1003440c9081d40021600c1070080e0341501600c80029030044e00c900501060700070004070345040740c2c1d40303100940300740d298481804078910801e20ba260020300d08100180c0481c0d00d6107031700f98010101402074200c495881e807229040c040c000c041214030703801c01181000a030009000e0301036494943c0709280c074028048500c0580d24898034100905003e0b021400000303000358a012803800e00c90815003000080c071185000c4900501040d0110303640340c03801420503050b01013142a10000750741a0000c058500d07c03105902e0854000512541e403040d1a0b40c444035842d00d03900041d0858030140094440005900e2034400600c1c000704100d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 708087419 1250 708086169 708086173
    0xf030b1005031227030f060709060f140a090e090a1a10051201020c19060e010509060601110a0503070501020a08011208072307030305040f0e0112120c1b030311 70
    0x10b2002c0d03e4a1181c21110450310450380d0a08840b920fa15440c401c92070609050f526005400c18840001c4010968610a80312643d40307602e2141c54560982e48140c1d4620000c001446140c00c6c1890121440024000130545041c00210141c1e40e504510800f68120781010f01c1d03403c8200c0c1c0c102001036856180381c030080e012000c0d882c1403901c0c18801d100050303681f08071485000b00c4030f1003001022003036044411019044003030b540540440c0e200b44201d001c072003030100c50b142d185c40318940601030180306841c0680d103800d000d412507445000045070000301e00002c08400d805000024000030b4820801042d070180303e14005030710ba01e0200000307042d022050344130340035460407510643c000860680c110741c940b5038071407900c1c001c0da110f80700200301c509559016015a817041500100925410501034000c80d0f000280c1a0401a114882510345a00030b1145041000703001c402a000a400550030b80250100341c64031080003802c46d16080450a88400d0403003011580c40410310a0551004101c9501204440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 708088669 1250 708087419 708087433
    0x203221d04020d170d020d060e06011d040506122410120303020703091d0a060b040602101109132009100810121410060303020a06090204060f030b100503 67
    0x304154804508006102c0c82c031300d03035144142e0324000c0240e40303a601460100310b440d208400140c60042405004400302082c41c0f03000952a503100e4070a05d41d03002d43d8040e015501341c4035a01808081c04020340a10b9010700250304542c1c41c40001c00204101c00711880b5100c82003032620b203425040140180601c52071498000041c008603802d425a080850f6262400603030300c4056040c1180d01400b181c00c6407507800d4904144050042c41d24003614003c0000d104100070041d41d032445488148168032404d8007580002c1000c03102080c1d1170307000d038168200c10021945084d1085000841901d120154406d01e00d649400c4280d0700717012000c1d2006801d14100000d07182100102c0020040805000314104001202c4001040c522092207010028006160203014a4806144c442440380c07111680c5001881350381c042620540150080301d041301d4158016040303110342c4d42c6410002c1c10049001340d80041d20742c400020030500281a00c8000e60040b01c0d00307130490030140520041d10403070303134007003403203540468 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 708089919 1250 708088669 708088673
    0x5070f051204030314070c0203010b030d020d0e0301111626090609030f58031e020d0e0615040207020a05060703020d0801060804030203030109020a0203221d04 70
    0x464541d03660015070090305a8031494120041d04104800c000400a00c106100d501500400d214605030f100310020f0050160031424140e480d46001c0d02400181d1080250304c00441c09885890414a0003030008a13007a04426a00c050a520200b8031603e1906245210011310041054296001c500c0d2040790ba40c030502828403400d43d020b401d4005102c0c2c000010005034a503030800440c0c2da05040401135900451002c03011035a850803540c04003800400e0000e001d0b00e80011403441281c4a20001110030070030807241006111b0902d91100c1105041e603c0200b03003110081d840552140c450f403000d026940700d5000007400299012026010b019611920601001c850460410303114064250750060f1207524500001c0c42c01311103030340142e13000780c0c00160b00c2050640c045004280c40b07407540c44240700e90b40e03528030480c0e4010301102c015006030414401801a500c580d0014192001684100d9060860301154811802900c02c82c00140e01032554040107138954844000c4200031341c0c1c0004030103902d440e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 708091169 1250 708089919 708089927
    0x40c060503190c0509090108210310060503220c030303271202150f0a05010b04030f1e08030f0901060803042105150a021309090203100b06040909060f05070f 69
    0x1465805642d43e8644140483c22880b4109403020742c28010424125540c2d03500c00540c81e0040704040b00d09800c10b00e820b80310020074605c101c80c011100031600910742c0f0b203403060441d080e0300091302080c2030007401813510903046415007040c03005030701030b520002e2003924515000e411500d9100094100000301c00181c29681510170791080c110342c1180100d110460400c20890030311281c0140e24245d07a880809100040140090701e07481082801802c01c0b5a90700e40c3c15a2207240540e21004040721040c183c02c0001407102c10907174412041c2c8081340b80401080d641d40e0091030b0400c5400c01d01044c0d00301c007000407100382400341c60010008100035501e85410880301c103040240c3c12008114030b50b6188201410464108442d80740c05c0c00e0700340751400728100712200714003941c00034540c0c0300780d10b007000404035004c2c04502c1100d662641c000c009004841c811078211018043c400360704c2d640040c06002c0003400144030702454441e1482040c00040e002c02540a1008030341021b8286002c01400c240002001500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 708092419 1250 708091169 708091201
    0xd1202031c180b0403120c0e1008010b040911070b010b12010f0f030201140c0a0c0305060105011d0f012001020c210717040801090b09012306060a1101050f040c060503 73
    0xc83d00c41c030032a9035581410b0750158064291a1515441c014500030400d0313000580f407203050b908448079962030345145802c9070420b0080c001c011034600c04001c00c02403035140b070340700e1803021a0344250b80782890380c0e5441e030100d800b200342d20440b5092000a02a01940e581c1d1103190301610400707800b812070505102c9a4043c0d401140002410703c987c02005000700f01c603032800e03107440b074448004a40500c1700b0b9140001051080303100484041c420a07002107400c0d030141c206200c21000002c0c5a030344a2505904128201040c03210150510084500300440ca0040003074040410503c81d001684d00c401e64500da500d8820f80c0c2c000440c2c0b4503a64141054814031003000c546a03e90006a1300c01c01c0052204a50000d1107142e001c0e80c140e40c41d15600c00204040303a08414851459000204440c107903a00301040c0340e40c2c03003658084c80d80301d18200280700f9241c81005041c2c1c10700b81d0714203500c01c502d000b051079084132030175140707518100159000c220800119132480c00c05001c9034908036085050a080004000342 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 708093525 1106 708092419 708092423
    0xc050112020a0503070c02300d0804050303130218010f06090611070522020f070507050607030c020f1309030908071409010e060d1202031c18 62
    0x20607109440001950b52200b80c51561140c1086858294500f0f0407a44511030340c120164440704580142074118480e010f584102c90120035440c58101074904070740c10041040100b00010b1400300030307280c0010804400014200040c40001e86404a50120245940522000282c520039544829045410704d848115140e030b16140c0485003180207e000d0780342684004420001428009003008034a007120003c2c101c1101840399800c141c0c0d101c448881d60b824404541c00041c0501401560b004101c1107500c0e510b454484e81c0c003e0040d091a0710080d1180c200c2c055000e0494a0f984061029428920800c0208030214034015000000701d000c0c0301d43c140705030034001c11422841b5408004d04c4000508503842e0b0f0780f820364295020680200215001724401244d0000200c400828804084050f0003847c1c40300d40b00700b414400605016a108002400c0020034454918545905481c107a = true := by decide +kernel

theorem cover : BRFrame.Cov 707913669 708093525 := by
  have h0 := BRFrame.cov_init 707913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 707913669 ≤ n) (h2 : n < 708093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
