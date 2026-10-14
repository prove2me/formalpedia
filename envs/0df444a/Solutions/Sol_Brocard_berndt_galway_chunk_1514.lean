-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1514
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:20:58.787224+00:00
-- url     : https://prove2.me/submissions/9f033b94-17e0-4a32-a442-b2017e1dd914

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 272122302 ≤ n < 272302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 272123552 1250 272122302 272122321
    0xf0302091c1202070f2603130303170a022b060e0702070f080c0d03050a0212041202030c01030506010203091005070f060209030d090b0405060a261b0918 67
    0x7050864140404900021410b0541001e07034030382c0511000d80702e681c1c00029101c01d000e103000304807290074880e91030b04c4c401083d0301110314410811070021032006110015580001002042c000c500c20f88641e045c40b40c3c0210003c0758000b0090020345514030500454003616408006043d00d5a01218104090503c801052008101c0303908801c800741d0121003040300a6400103504025a40c100b03100c0d01c0a40da40c2c0880c1a170740c4400d43e0700280c1058a0000c2100002d000b40c1c00303010140341900507502c2c00041c102c1e0100380c40e0003da200c810202141c1903428290f04062245c02818407084c40d0500880c0b406800203983c1e84608030205005000d0800c121313030140e1140c4140c03452039a0081861032082c41a00700b60005e504807090051103070040341c0c1262103150140c11031404842d281d2003681e00b03082c502002c01015401030200300007842801e00c0803200c09419941211041090107540c40c016090a41e0041c041f401d9043d00e44100110400c89a600c0d540c4072954282201d20300c0c0500c0b425030b50b561038070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 272124802 1250 272123552 272123569
    0x702060c071710051009020a110307030207060f0c0b04110d0512070b0906040b01090f06030807050105151905100e090403080912030f0601032c06040c050604060f030209 74
    0x480c80e40240030300410303101d08680c10300402d00705040c00c403001007502e44140350481d04152640440d01a100004000301c401c95005401a2095801c00401035000d2203081410365000b12401c80060b0012001404020341290044600801514010107140150b903500f900408025001400c0d6410b43c860350000d0f5502c0b80016840c480e80007069030290060078802540c0d580005604481d403088040000f0002e00c00040c80f20320880d0000031040c4540d1034041004010700645140380300054843e05d011010034085030050450a2146000282da40740c40400408a5401442550700c01c2141c4403008056515115040c2c003980d070200d8680d511641481d07400c2d1080421403e0280e0043d40c8101048245a00444003034450b10785001550400350404200c000540700440b110283d0141c0500803421551082e13000c0c0c1440d200800cc9010340c103400c0416081c0c02c00325440d5814503644060308000400004811410003440256003135401c0c203040c0400a00f140300c1c4442c0700c104060b0f02160350445552052030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 272126052 1250 272124802 272124817
    0x50f0313080f0703110609060402130504060603332009040626010b01030212150d140c0312040506071205090d060c02010b0a061b020a0305060f0103050d0320070206 72
    0x10007690f141c000f0714010b0108042d100c02c40000d40101d00000300204000700d48640710340c0c3d000308004940c0d16030810000041401030015110a6503c60f001300001d41c81504030800d001041e07504000c0d1581c0c108484500304180700e041500ca40c14425025101c0780d01550b09180c1c51101181280c5502d803010205004020300e40c0700c1c0e0070f5117010b20101300f01100400b074140d00d00e07131b201c0c8000d101404030903006409a00c5070f58889078400c0170078000101002c04840340d0a113528001004821100059250071458404070440348400b504a0b60702c0e0341c01e07440d0400c02c0600d810359002540b070900d490300c000200306d402850700280c000311600d42d0300d42e0f480348220112003500303800070042d0101040701c0c02d04000400c40005008090342c0784c1031140c0003920707010a000b02202c031690350700c8168503800104d85c1e141004c2e1580c00c0303812102d80340300400021014459244114204024803283d5850f500b130036440c245400c1e600b2802e0526282000c1c1c8281103082001508207c0800d50a03501c0c20f0324808030350135206800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 272127302 1250 272126052 272126077
    0x20d0309170301140108010911090928020307020c01020c060406030b0a03080a0c0c0e1b180405090d080f0c0a0c1406090a060e07181503050d020c03010c050f031308 72
    0x1c000b03e100d00c1c03c402e544249a201b80e842c542141c4e25003000300111054103c801c0c4420b0010701207503209241c081e01030340d0301881100e00d80c00315884800030000541001d0620304002a0044200598140d04209100503094244018034000c2050004541a807095001702010544c40e00035890307450321036402da0030086501244140e44d482012070010a005541402124503525410000400c80c01450f191401412008030380c00b440c0c16070a403190f181c2d45c02809100140b0405003041615036a4611840e4030440031034010300700444842c5001454404010592a0000f0810b0284120004650252400e000150504000b0000030b402c2111043c1c074400101c509500c00c0340c0402c10b0b20080860140c6e9098030488050012070050042c00303448140740c5c000c4a4045c41c004050510749101c5400080512400030342c01c0f404140ca94681505000302070b215100964820701024801c2e0400348150708515800b0b10341541042c40088450220b84000b0745002c28840342d0003082e20501600742d045860300d080c1030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 272128552 1250 272127302 272127307
    0x606040605030c130b0d060303020d081e0601033201062d021f0b01020706020304051503130c2c0402180601030e01060f031e2a32030a0201020d030917 66
    0x11b41042c001d41502d00044005000c3c09005100d50f502608407280500c03807498001401c044850a18003000800904103070406403500302ea10102140c200780001c800c0d0740c84509015840d6040114016400e06034400f000308003c0a80e1040101c8208100035241c25051103110501a0883c0c070480c0740030950144503850309264000000d80d1551076003c500030341c100f0380954503c96a204802d98130381c080c0384a910780203488698101c40203007007580103540c03195804501c28a42c500a841d40d0812040c50342004031001c40d408822488960b4400788094400c05400c0191114039081c4d010490000304140c0d001054110980820714076802900101c0c10400c0e084020070045596584085981d0f0381d51000f61070305818440c46030000c1c000c120b45244159002402c500013003d040282a40303411015115030394240f9003030f6002c5420041c1d80b14400c50800902c011000700221f04084058403501c50501900c640e101582400050342c012a85144240b114100042e400801d801d0400c5403405900c20309100c80c500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 272129802 1250 272128552 272128567
    0xb1804050c0a110f10020a12090f0b1b0f0304020418051e06010305031b0304030510050717040b060907020a02190806181009080403050a060905060606040605030c130b 73
    0x1850003400289000d80d0711100700302a07100900d900c50a0720410140160840f007060401090a40c004185101f0b0926001700d0800c00740402d00111800441c0495081c0f40c15600b42050005050340c0e26000f10b9002e10696070320380202c2d18820741780b00d011824540348001000082c25940c484d40140310718002d407103802004243e00d05d0065205e40b0703420036442c0a440041524040d50740c0008a681c181c1e64030500442c07500c01e007500d1043c0080e080c0e81a80d07406100400012001490038000d0503803002035540c0205040c100100b0180008455441864a4a103640d0800c0042110707868041e401c0117054650705407a48a250049050214501010350041418240c105c170104400d94128101d40400041c3c5031903880d0038196680741c5001564890700c5a019035104018107142d603100150702d900c00e40120740762035502c2c0d50b91b5090a2280c04181c41729995143e02c101400380c140003181c0c1c45042183d03020703d01400c1044c05011404080c1044811b0200411100508006c2140060260a99910050700d0b42c0c007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 272131052 1250 272129802 272129821
    0x90601181512060902011d0a05041109100306080618030a080a11040f180e0d0e04090b0c0702040c030c05070312020403210f08070504050907021006080109031e090b180405 75
    0x45140300724000780c82c1d1741c00c07412107a100e0b6003d8401c0c1f00006040c80070b254501001c100c05030010311031016803860304101d0103009030f0303600c603449502040585021a0061821000d04e0510200410914085201c031032182460392001c03003102d001044505104e41d964075000c090100810482209074000c8a000030f000c03a501100c120b5140840e003041d01c00042c011a80103181060760360803140301d48590711100c18a0700d624061840390250510242c07002640300c00c5030b140d0300084a41a203411b840210002818819820306000d0803c05000c1410700b40a0500d4241005125202e0030380007408000507207008110400654044500954000c0180030304a8020004100101044410400450860510040002c2c002c004480c400c021545a80381007600d40001c2c0f01a180d0014102400c50142e0500c40720506018440c80014148101c0001114230341480d000d0420b50a01000c5c42640b080c1801c1d20101d1644034020406490700480070540340c0a40301c0341515060400112258024206010000f2005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 272132302 1250 272131052 272131061
    0x118110c070e1b04060f210603030813050c01180302040f02030601230901080603010b040c05030601200c060c100603030320092b0507030c0e09060118151206 69
    0x1038040c052289035807907040c10f052500800b10540841d00c0e005100800c1224040d0102c051041030604200d2030003100340c10100209801843ca4424003556400d062003450740c44070019a0040c2019841c40c560400740c0c503101e50310003003004120b04101410759034240070000c2c8a102d00003907034090310511007598442c03032441c040d4104807031039070008403500c44e00c0c4d004406005c0031040e80c140c182241460700281c0b10044603400c2c0f000340601c0c0c041d903c400000c405600e031881080e8001d2400c0d0b48868603410044001002031031104a070805600c070000f00d08801080100c1d4803ca0b5004c100c0340e0304c0d510178602d0720060030001d065000300741591603c0d074000103050701900585c241941450559214141a060685050080450040d040003980380807200d4148191241c800307180c2e43c074a031400c6102da150794140c07a04600f170f001106c40490310442003007080b0030944015003009030301e00501000e604180c07142d00d101c01c2140000b0141e80e1504a82043c1c001d02d00c4210340070300303c12640d980c08094503050010107007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 272133552 1250 272132302 272132309
    0x1003060e031905070314090607200415030b0c07050a120518100206150604080a1b080601050303070f0813060f0206060609010504140402160302070602150408030118110c07 75
    0x510a0045a10b1144200125000075a00d5100c4000c2c41c904041480c20342e800602d046500044108070580c0410891036207650801745065002c4041444039040c00262a142c2600c92280a40040c003400003445180d403040c2c0c4815a01d0030360b40c645805041191908118040c00360030400000418651150b1040040c00301440d030080c1e00380c0400c801014082c8006682e041e440068219402103003508865142c1058060401055107052589402c40b039400d0000a140031a52903c5211410000e40e0b030a80440001707005440140100d98901400700707440b4450b42e0801001d0100c0082550b00b042801d03400e59280080510364136000e2520b66001030421035541c0018005031080e040060030a180980864211501c1a5100c0742041e00c0c00382404030021983e0705481d48a502845100b80ea800a00c40c0f0304081c42c081e034000e16030035203003820203800d00070221200041c29043d801000013049500045038111400080150901c1d034500303000500415102400604421b0002148101c0c0e0f00d0005440066 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 272134802 1250 272133552 272133577
    0x8090307140f07050d17220906180507020d11070e040308091e070501030b28030210020a020102030304230a0b01080d05040503100c120203091c0201051302091003060e03 74
    0x22180c8940030041e0501070720100078506c2003d2440714505034001009844190f0480c0c04075240c2d4080c0f403d652255404503003289140560f10b08080041c1320800d540c1a408245c001420025404c1842000b501c92603a411300034280320540030210b0144504028000c010030240307040e8802810145402844090259504d030b00d103105400e40d8803183d1202c60380180003500c1880052882a04e00001500501020a851a4400ba005440c1c6403606034031441c441a000d02e01020400c03460030741c410000c042c1008040c00c1c08560100340c00c2001030f41c00008894006805c600c002c0d402c810700c0d04007054240c1c0b40ca280c0e00390310701408010b94200a1018080d42c142c0700190140c41d159001c00b84112918065446065450751004039400c401d8903050703205010800303103440d08405204645400c80d060364016668068194801d05042607141003920340d01d1030001c040e200070b022a0a00d50b01151030340f00c80c444040d1148001c0b4011503003043d80d503000700004540c8447d050200440c640ea1082c0c4a42108041450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 272136052 1250 272134802 272134813
    0x6030507110d0e0607140a0c21060b040b0d1a0714030606031b07030f0905010309032c0d08120f01050d0803071b06020a090906140108090307140f 64
    0xc0322801190301e480480d10540007404502d031018401c4034018010260395400034020084000810040540d01e811110074000405d0611150720b091541490f19034008400405140f070f03104a001c0382081101c1406400c094049914580d4000240027084ea50305030651100c010f04c601c0d01000101075504001040300d40a903540c658442000740c0b154408003c0300b03881a04204001421494642d01560f00188040c1c3e06092581000140e6503c035808a00c045e40410409848850362940c80440744025090a103414000c00005540242045614400360100340904400010018003803580510014000400c04c04078111941010101c80d4400c0040b030000c103c174100041c10300365075500c4090483d040904082d01a03409900c40240b1900064055401c2101d1800c40c0700503c1148850480d00034002c040042ea03500103042e01400e6002c0b00d034014200a0700306241040107285001664007003400a0801a405540780c00006003107200b561001820491050111001048001603004082007910308944 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 272137302 1250 272136052 272136061
    0x52436010806010b251211010e010605090a0f0905010c0903050c09060303120709050a06170f1b0a02120c072d05150c0d05030702070f0806010905060a09020f04060305 73
    0x2e031504024081c40c0000c1200304110312054103002c0d140528100200040c039a08402c0e5a02c018034601200321000001c0c0220300b1910300880b003842041c0280902d00001c015280c540740109000000050a14004640e500c60303881c1071401540281c11516030100c000c0000308068800544060081d0005841c20321aa1031360000d2418071400c01c038040d0308010000d6042a0308021103450805c001480d45041020005000074030351500e2868001400140c1c4400c0a003030041c40410240310b0004200402011000003805501e4841c0750703120610300d03443c0881c1c0d940d42c5080f02040e8985a1308030002003003d0070004d42481002804038144041c2e41c0d070f0703980e594100e1740608010b942900b0140a010300c11003981c0e10820030391801c0240407090301c1a248100d070401128100d05030070280411a5407002c42c0000040000159042c840c0b40c0c007511030107911844250415020a42e00c2005014481c0800e0380c40340071520300e40e202c0500b80001c1c800780e5020740d594002e043c0d02c52a50b401c18130030031011038100000704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 272138552 1250 272137302 272137319
    0x30f0c08070905030a2d080a0c0b09061308032205010912020a1502070c09090c0801150602151008030408030a120e030304030804060b03011a03070905243601 69
    0xc0449030005461b6105640c0c80001c0c85d80c0c07610311820408440f08000b404000116054040d1039482a10348492488500504012580903401841081990000c7d400c020030b901449041000103a00000b44036103076500e2004c400b6031048018402c000200001c0e1050042050541000400134070440d980300302c0c000308003026079446a031608010043c0d450502184100c0c0c0703090703001c5e00c9054010100e400e003451f41d400000c0d08a81c0a101c040e034140304030501c00e0150007000d02601408812442011b01c4251401c0c070000e480356911055201d4910f089400328418070f1400311110050700105081e04d80e1550340700c0d04640c1d05d520003c940c0002c501804042e2010380702c584943c0381809403481c0610f1035076840342e600710340c0540010400c50345555130f00030002c007940302446000300c412045007107001d554060600309845c100841c0d1003209032904200400c00800405090b4108c202400c26030742e080c804039480041c6a0510203203c400f84001c0300405600d4062014200140e0324081c1000162030340d8035442076 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 272139802 1250 272138552 272138563
    0x2120f1c050301060801090902010903060f0e1b0d02010c1b060903060b060307050a030c03090b090109060609020924040302090406020924190e090106020d020d02060708070f030f0c0807090503 84
    0x3180b002c00c0c065001049582c11f1504980c60b114030501d42240c81c2e546036920603044995020000c402d40b95a1f69500500380810803441d20030307000c108540d40c075039104400003c0058204660003410041c00c0b0f0f0741e0508100d81901020031003681e009212031001d03190384e401070600d00d0303030301c020340e03255003400d440360f51504201044900130161690792610f44440c45105034080c107101d0f4008030425540d0903d0102259400050a010b10102000800d03a84083c0c00c2682c1500d84a4100010651040203000115074600c0c03113400c3e03c0d45003182ca000785942d0f101803403a41130082e588082d400103070400402c0108102640101a010811901c04e21001200c061412000e00e44a0b100c402c80d0100308801240039070520501004600ca84c60001d40c000900d90114098110a900c10030141c2c0c0800d590054440c0c0501810001c1e030f10b244010002440c1c2280700800380140600200140101c00c01c1d00075201e807203034022001e80783c40240e0502140080080040c030010b800c6030000005001c07424085907600d8082603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 272141052 1250 272139802 272139809
    0x306061d0711061303050c010f021306020102160f02010207081506040e160b0f09040609050714190807050702060a020a020a0801020708030a0510030c0b1312050d0c02120f1c050301 79
    0x2c0c14680e54824500001904d04201682400340600c400620b5034024051350b0119001d00303102580b03c5046a001c0d180c00a01e60300703c0c109590060056035401800103c0d541066a0030142400c0016400c3c00181e083c0600c80c0c000401d5400707694601d506810355003040d5401346200f5201040b4100c184180e050302c07240c101a000134544141402040151440320240501016540080d441c241406000400303c958983c09802c4054558003000320858021a186408403a07400c0010300d00001c41d1603080344086009180c4051003152030100740b00c90711030f200341c800c259805000c666450624040c060741c1e8181104040b4410b0001e2000031804140600a0300c803440d40c040c10f1203040d5110b1201150140030024110711041d01410b000101240b40010040700030980581d01c1d0307030b607680c1c1400d80c94042c03051a00010b105510201001c40095000195030070000881d00d000009007003284002607002442d69801c01007885025110305a026000c03429114092281d0004d820315180c850082d41c0d180406d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 272142302 1250 272141052 272141087
    0x311010504031a18030705010e12090a0306090f02040e0f0606010f021e03120f0a110406080601120902060c010c020105100e0615040305011409100b060f090a0306061d07 74
    0x49040f440008200086074004001c4102681e001c8075040c1c0113481e5400c0450240c559a454000d031201700340c003c2c001c50b1500c440e017a02c99403502400c00003207803943c641440020300381965410070714240315110396240341d00c9a00134001d101e556440c014680d07441c52040d10768900b80c012880880d0040d030141d12916138040158000e4118041080d1b02040b00903503650042d080c600080000d0705071070074540364070761151444403000451401d00116040c11600000103420b05130704100010312000e40c105941070f038407220905e4280500c2410310b209034081d100e80d010080d007010021400c1403061106411101c0b007081a5402000103507519143c103102e40e051446501c1c40d000c01032000c10141d0a0081d0401c21aa19198100f881c03e82e4a036541800c68501e0881c0500e49503910b001d1240d10034080c01400042c48a030701e0148680d482e41030021b62648900d00c0181c0c1c10000004500340070307441d1041c50000458020b9020050181d0700c184222a12a03100d03094401ea85080001452050044900260107001304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 272143552 1250 272142302 272142323
    0x1012061b0e090c0702061e0406020d090308030f0601021c052d0a03051b0a0e090601030219080601020c0306130b01230d06090b131202070803092413031101050403 71
    0x741c40601c0f60f4441d18040e0380091007004040105001c52024401e1200081141c80d921450844e00a0412800031400c8042002110b000c002080c480c20640c1e40200900c00344181e20348034000140d180852b603849645104140304202c018668108001c0d10016095a18282603034000183c070f086208071040d4801071300345062002c0c1900521a603c01d0340e200302020074018030b1000450041c03149401c00c1c21440005107480401e00502d0400c0200c0b036401c14805e00b0290b0510746040301910445000c13418082c108242c000004899a10811401d44003000c040c040d150700e802d100341880e00c8421945404d480c010070030000004c000d0480300440a000780c0c0c010b0315680d103400807000c10107161603106095a4140d101c2a181d07020600d01400c071401507842e240d07281f5240c03031907180900c0d9034060041c1640c295005007000300802d44000c000c0310038142d4100c030141d04d160041030316000440001d0b82d607544103d0000c551848055880140101500e00580f03505090b86640001150580706500000f4002c2501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 272144802 1250 272143552 272143561
    0x23022050709020306010509120c0307050907020a141002040303090503071d04110103110412050607050322080c03160309090b18040c05040e0a06051510081012061b0e09 74
    0x242c2c041c4d0380085051410f240f5144a290004c0c841040140004070190480e82d855a03240c03030100241d80042c070b42600c00201501d0400b001035102c001c88a00548192241d00c2b421500c1a02441a8000811405000c5407525240d04004100f50b0311409a14000c1c40b076030b50041144102d0b102104642e00078528024201d664581e552801241d50051045c14184c03684a1841c20a152401602c0903200340c540d0b4503820300150500f81d2400300091300040134000100140086102d00052020108118004144402041d80341402083c414605441214040442d0407500c4402d18905d101da8280a41c0c4c80808007521480403400300d9541032b280310780c44524000072010240601d0030b6107038001c1c01a0a034031b090595402c046030aa44582240b44401d801040040080142c0ca100700ca4000010020740e04c2d031006103402041c2680daa111000d02800b0942d400540031505180d00b0801600075200c400e8010ba0b0700345000300184c400008200b83c0c82e64000c120144280c42a985d04490360341c014070070801e40e101d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 272146052 1250 272144802 272144819
    0x21b03030a050a11010c0c052b030b060d06090b03070e01150f0e0d05010b0a12170c0a0f12140310270914120703080403030230220507 59
    0x1c80401800d201140d1110080703804d0a00c603403039000c072160b2180c02c10201689402130400680c08052011b40c88101c0b041d01c841401d44040544030305460a0000303041901f0700c0041d406009070380d024012a400c100c000320b07003641e842c2c20030100c0103001d034101e601c0b045d00c0f142d0400c0a40c10034003d9050b05401c406114000910440c40850345143c541040c1d41120032010104404200d45041940d50b43c0d10340e01084085c0c288400c0c0740b00102044d1081e6540070700030395180c684114508100c1c003240e10011079218440c0758103019140305540e00c4054146180080c0c940388404e2180016280042500c240307a0000c0301c9141c3e82101d100d640346e0500042e40c203040162070429844c520459400307100c0200305605880f612841201c4099019200c600d0101c0c7e0740741205403614a4809200d1404c0c00c043c01071500107900240e030660420341c10b044c0581c0b595500040800d0340d40c1b00a0782040c1404201e1090200c55204400090054104420806411041c18060280d030110003000428642c000c0c1d000300080c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 272147302 1250 272146052 272146057
    0x615070b0403050705100621030806040903090f0e01030b1302100c0c09020d150f0305030d020d02090402161a1605070501060816080f0105040804140a03051903021b03030a05 76
    0x42c800d04106050851603101e142c90aa1130b0305182c500e141e551101401008a003c0d03e2441040303041000da19080d039513640003041800003502c4a4002e517201c0c03841c40c04040c00782d844100a00740040f07035030f00216034841c1c24000081003880141c48540c0c0910110305d50100c40d181110b4101e80180501c40c0d05201d0800880e41480b04250640e40c601700a100410100c69a000901e40450250310101c2c0c180c0c48800500c0c0ca4170a41c0c4d1000c0303480202e03103004000040020080d40c880610030b103001030b100c41004040c94080e208511190b58403910004115407000c0381104001c00c918081c4508000c6240d03030104070071102c1403d82e40048860942c0c41c01d0b03c40244a030700203103080391040c800070500c02d42d125986403a00d80c0c5010000c06101060a0900007101c041100540402c400402800305042c40e03100c0e0040c512440c005d01d42c12a41800102c0c0313250700c4d0070a6003402541d02200315045484c0c050384010900c210000704800500550b00035034200b01c17441c014a0030a0200a014629000c50b4a0301542c2c0b5a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 272148552 1250 272147302 272147311
    0x2060903010f0c0306050315090c0603070e090109090b1e15030f06040503090907022805150f1006050403080316090f091506020a030f1d0a03050d080615070b 69
    0x10741d220a0000031011041c020548060584e48001c11000c3c20310301090308295500080700ca4030f0346244104030454100103078028222030300703a58440d502d45840d041114459043c0003100e40001d81c82d000058035185542c4080e030024021202489242c43e0303024110020141d0f544e0400c101c01d00e0034080f41090742c1c180749041200000404848880f40d80301101c1d4100307041110305a07250341000c600030700d4505103418920350010382e0b8405020700e40300c19860700c0301800702c0101544055009006082c100001000817501d0070309090000c07070051811005502c450030702258000c981d985035800c0016881c2c0580c3c1982c040e03d5201c4003081c00c2d0f580340200c1c2c070700300903155514004000960100044860860700f02c4800303013115032400714910f0300c0d8070b0440340c00c0c0c2c1190340800210741c402c0c581c0c0d40109501c14001c4010741d4242c58107400c506c45040d213403080c24003c5d02c906c5a010030328020010811000140c00f20413000180c41c4c514055591004102c0360002c0e0b0786500c041e40004000b0070000449401045600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 272149802 1250 272148552 272148559
    0x25030506090d08250e0a0905010b030103020114040807060f120213030309050a03110402090d080c06060102070f0b0922020406120b010216030f020d1a06030105090f101107140303011e030f020609 85
    0x16503c000807c180e5000f039124050b204030010040c4255603009160000080d40c400c0d21918151800318255901c40d414031600c3c0401c1100c0342038a0f0450300c02c1d91070b00c0c02c020304074400703540f1242e0a151021044c4104c0c44100c000c24840c100c001440d0a0a4203c1c00441e07800c00e07100408004050140f00103980001000c0341d2101e60346500b10005042c91001d44060320309180101345d14035001e00060300d44a07098020305101051440d041280301c22400448020340029180911a2042c5031030240c6030000c50100c0c404082d00101c0c0118805500c12054036260920b00c0040c0000d0a680006a0f10f07045500280741c0080240141880800c0c40000c4400345248060211000243d503622560030003070074040d9415901105005110b828602409901e4002d1103a0002c0c00000d240104200c1d92401c403102c4000c4029107402d01c0d22640c02c8240700355004a40c0201018481850b100c950640380d03802401118103042d00803070800d00c445640c008100949500c0342d0400c03800d25168082240a41020080a90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 272151052 1250 272149802 272149819
    0x6130507051e12160e0d020d0206090a05030f0a03031401050d020607050304094106010c060b090702060108120910030e0a0f11030d050c25030506090d08250e 69
    0x1d085002918640f20b400010080c0d589000e8401c80181152241c0c801c8602c141b01400060026980b42d100154440b40d04860079542c0d03103403070343c0401c03011041580f1940d454042c00c080034800d03030004503110703240d103109035410040c101003e50001c2c0700f080c0a00503150442e203602d0220005041c420020100a409402200d08065544000009071041d10a440c84940100482c0d8007441c0034140c0d00c4410400c80d040d1a43c03050044036101c50740680010165070401c48920b002e0000e002d03251b409918908000b81c6600801c1ca4107a002030f541320000c4c4508080d620850180c03e2a002c1080142c0340b070b02e08001d003200049600c070340c0101c01420300161440c42c0360090f110444001382e0342c1203064481c80d20a0907230460200c0f26508150500c01c211520106000c800c0000001c41040420303d40c503039010209507a42e800d03264494814042c1000e4200414500c9600c09010030303618006500ca2070300c281a0303174440e02d91740c1d20680310801120801c207000c02c0e1154501202e164074021101003404440103460050f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 272152302 1250 272151052 272151067
    0x30f0212120c03130b0c0415050a0c030e21010e07080d050a080c04090c0e0312090d020405040323090a0b090306151f0c05010f0501030206040e060402160b06130507051e 74
    0x4804000c06d4500315448680001c2c00c03c01000d942e400100e10034298200355041164511010f004007001402c010200320051011280c9591040401822602000e42072181030313914600c428020144141c0f00c2e030300c80c45040070000720003c0024202806144a5460b54103181c4941e9043c2c51110000d80f1411800d0700500020401c240c03a07114201080381165696603641001200745402c1c415000d00a401440d0100450b03003140c1c41d010740440003160305680010362aa41c904048030480c5039003808080356490419a43c448402c0c40010b4142d804007159a9943d1540e40d5010701013034071030650500d401d13810110008241d03d0003e506010411005088040d07044030856805502000343d10540c001700f8000f114240600009114072803102007101d0701003055504540006030940158407a450300111170703c001411584030390b0140c0d040d59140400c481d050107034900e8174040d00d52084403207d0241c200740c1010b502c0000c0d180120760140e6003d0b00c0b01854410480d01003142d000d034000ca08504075a0400141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 272153552 1250 272152302 272152313
    0x5090d0b04111003020315191a07060c0306121112031b070e04020109120f08030103080901021c2309060d0b19080303060607021903030f0212120c0313 66
    0x6078411841110050406a0040c003000b0000501d10364481c10184113004221980301c20201468401900f1160144088800d0710240c0481450703801402403504040803190403006044050b01d4018402d100510401040f080218201e170702521803c035584041800080100b80320003d400d9501c000608500d803900c1108003654071f1a031294242c042405c00e52180e40d40481c00070b00041c1b026024030f04500b4068185900020003d40d200c0c00f07194a46c22001913420100308405281204056004e02c0241c2c17a980d40741844849500301030301c50b0f80075000b60400c0d0010b807520b4104003039250829485c4c10040010032000103564131881103c0311007104040000d803216030382d1072000e04507070b001d10180829108200400d201c0c00c18204190030341111030b81c2e801030000e03031004020740703034409021b0b00c456444901c1c600000b80c003146254040b4002021182d804000d0607400f441d008120300250302112042198103040805034890b100c40112140140004500e4041c0c1d410000c642201204000d8121480e20f0f4454 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 272154802 1250 272153552 272153573
    0x130509071802070507300203060a02030c13060f08010603020703080f070e090405010b10050c0a080a031d060126060604050c0903031314090f0a0507030f15090b0603011505090d 77
    0x51707040030300c03140210186c5026140031050b00c0074050031640b440003102d0b80829a5040050095040c0640100c00221044840019240e82400411510310180da03540005072500c50306001a20014981c80004990316000380221080d896140c2c1c2e034001c1a90b644610b0031140304c070180095081204000c0b05502c1c0b99a40c145083c02035000f04000140300540000300070040c40e885506034184142805503000d00c000102e8221400c41d046481e065841c40f102d18228014a000e5243d0b0714002c618840441041d400014102d05031600d02d8603912040c03882c85c00711034401d00340031440380f403030f0b8000350000d8940d044c641c000507003050306101c150741002594800242581c110428a040d0f2030200403003002001b41408403801c483c0c009039038903450790411461000c20b021000b0200d03200c40b034071540032400443c40fa91125400004400007002021079041ca00b841d0b8208501c0b5005006040c419165020315040c01100e04071004c0f400c5001e81c1b803181340c0054400b60001c4001d04d620008030402031002c41c102210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 272156052 1250 272154802 272154809
    0x110a11060c07030b15011403180c090403050a030c030204050d1b030605010b191b0b04140303180705040b0f130e010c0302250c12050106030c0b09130509071802070507 73
    0xb0100b10314030701411424040c3c1e4299011034100a0510764020400703147e02c045942142440601c540409001c0503120f1405c3c034040313401901b00b209a0104024036920101416880100e030380e06000000e0601c03005c405a000d94002c01c2c1e4400380200700e00d00050003101240072141c40c0e20984100c02c0d170341ca445400460720241d210300e11241d8001204c110004000421042d041c41c58106400300154a0383d00c050031900204006100c0ca5000e00801d0034010b509002d284031034003500451355281707801c1004030441e80714000e00c44858418150040741c0f40c503081c00752203001c44001d41800c19403141c203820850741c0f03440c98030306c07051041d5501c02900c000c2c3c1c000c0c041c1118440540d10094ad4450f980c100c41c81030800400440e2000380c040d805014000350201143c0401c480d2604a010300192240c00c0803801000e20b5800101401a103080c001181690b0350050280c400045501c1101d000c182600c400580c2e004490f11006508002e5050221000d0354922140040c6c5000d0010b007480400e94600c5c0c0380140380d41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 272157302 1250 272156052 272156063
    0xf060a2105130201180605120a02160302010b030c03030319050601051603030209181b0f0d02070b040b010f0602061b09100e1203090a05042406110607110a11060c0703 73
    0x35182d00544d41c00a0350401d403200010200d010003450180001c00a00030400b4015046040707001007600e50020f5010707180c2c541034a0a490240a04628006c7d000300501c892280c02809200c0c242402484d0100c156481080e184650b240e1010815101c00010b01004040c0e9051003800c0c88046030980e40c10260400ca03078400c0d1001030b0b07940d511000304090712501440e1911441d01110401c80c520284d06516125400c0000c44952540c80c1074602d80028080c00c004292120320200d02d03002882095003100e401140030340b41e201210b9880307101d21700d18142c040c00380c032016034403400100314880703d03840e07918010060414500c0e003051001c0c00005d1200c03060700c11120002d003090107041c1003450499240110b8200050065207000d2082010482c120480c0c0300d401d115507541c00084c0194407401d02e0400307a100d201186c0c0740352681c030380318060a41c1e94604645d12031031289000003640303940100c1c800000c0c00803400013041807070041d0384c0340c10003c1180c0c0da20325040f50b070500c0444684041080b100b8003551144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 272158552 1250 272157302 272157331
    0x140f03070b0c100b040207032705040207060213060206060612130f1a061c02150409050c04090b03150432030d0e0118140a050d0302030f060f060a2105 66
    0x250f628005075000441c4c0c142c4154410011a000a900714100c90f482c81d49000c100c0e50421011503205d11103500a40c803540c0c019000140c0b05040041e01d03402062000860034240b041c2c540c03640f508030b907100720886d586600104100100d000d4540d140b400f15520000803a0507100c0c0700404e0f9207440d5440444902250004c2548078115005a6403500107030b40440103841c101070709000002c40c460100303107596010b070044101c201e0f80e135054429901260082c1900344001c6c007a80c141740c880c400d241d504c0f42c418011b0062501416030000c1c6001300d400b10084241d850224500e480f59100d841da006900b20241e8682c148208061001286000981c12a040502d0103103840711541500c00c01600c1074202004010b902d8500300a150003901522200700c0303900314a290007000e07003d10310f103450078241c0c1c40b0141c038078441d1856000c01c0951540041d440b0700842c0c010228107482e184c0074404034100a44040c3da00560601002032406e100389244071600c50f40560b50011402c44101000071140161480750040084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 272159802 1250 272158552 272158573
    0x50d0804050c030d0801090c02030705070b190509031f02070c091b03063602030103060203040201122a0302040f0f03050106061b0f170307080916140f03070b0c 70
    0x501040303202c004294040c02c00000400d6000b00810300500404178a60b5032810031619003417081041da518a0350040887d50703c0c07515285500159003101e10b012485413810307061025518400d8042da1520b14020b00104040321034151150010341721180e808805580c00c2c00218082900005103030b00600040c04e00107100e19a40ba2b8608d8110301c05a2010140360600380c6c00c0001880480c0840281107007110891500352615640c03100d803030345041c000340c9034900200000c828040c1690085000b14801d072a00c1400041d0b040c0048103031428a4402041000c1132a9840f40480602c200300d0856201c03858014a0151141154100c000c000d0308078000d07200b07000c01c051007001024403c0c400900020704080c0701c4407824201d04040b1030030343d200041007502913445010411010050348080804102c0c8007544038a4040c00080c0250300c1120440124440d6076050040300142107c51400c2c2e4070001c3c03d920280d40d480c01070114414924a070b50303030944101d140029030b03490264044c0000071940ea015001b080c0b81c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 272161052 1250 272159802 272159813
    0x206070b0906090f0a02040c0212040902090108070f17040809060c0c03121e0c0102130b07060c080c0409091502070308040b010e06010f08040516080309012303180703050d0804 77
    0x1443d00490354000c030f200e03054409002400150b92a4116400301b0301c8801c00400324145049090f20040210340800c011452680c60f4000d8a42400d0070780c0d4a207415600d400d400c9131030030b03201e400c450301203030319000082d4107221811000b42e80305003d00c0384145061701000200d442907200c100b242d441604034051300d41e8203150900500500070000c090942c1422244021002c018070f810000c13059144000818101c200b10a4050b10035210242000004442e558a50040715a00550003141c0c000e103421007440780f041c01030b040140605a500659801c081c281099500140394004007a1680020b00c0c485410250640c00200007091080c1e0301d4203050300b01803410000781c2a040e007000c4a0109000c0030083c07541d90107041600024250710b0101c0c01a1518103019080403400b500040c040b110a000c0441c0500000008207402e24081c0e035601c44c040c03459400c9000d0614042d00f80c54131803900b04082440c4c40c48555510640700040420b4510b0303140d503695401c3c50006008074101c08100032000700424000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 272162302 1250 272161052 272161063
    0x30c080c130203040503191e0e011101060f0504020703050409152103020d0c030e1918050f0433060e0708072028060b0303040621090206070b09 63
    0x2207080401d6045080039a030f95501c0c1d0040802c031840441d416080c880703000744142c4016203240d4102d90034200010900c0c4005209c00950306865021800e80301c1e410800c010305201300001ca42d038001051079a2400e140801c0080e620031242a01081024000807940400c1842155041c030701c1203050301c0e040c80c54000902d0391603200f421220390340700441d140304000c642c01141c1c64800e540c1c145003031072a03059503107400d03a0b56620303403022030790402c031604c01512080741c00889020540700002888039901d03000312003100070350341c041f50700100010b100f10214000414452078001262004802d0000003103801005010885a121081503150b880da00200101c2d4290070020b41c004220b441d06224600c3c01c00307006402c80c542842e62003072140c00c00e084200f045806102030706070007901d40c1c03264800c003880d00c0f0140050020b852096078002d184c4101c20b83c85250000485003110281c2e2900c40fa002110b00341a08003104201e01c42034270a440c2c101c25001a80c3c1e603401804150b205041e50346890510030101c92601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 272163552 1250 272162302 272162329
    0x30708070e2505031305240901060617180d0305062e081b16020a1202090f0c04210308010f0522090605041a07090e0103030810030c080c 60
    0x103550560042404100b0441d00344118052401c00c6562900d0341e405e1546580d5001c04041c0c03082c012005a419100b04c0d5100070303504180e0b020001c140c10744680c3c40032422204c440c45000b000c41c5028a140318082c40c0e0b0240142e03c01c01258550a000030410303a41420850030341c04080001c2da4070750402c4054501031440d2103500e035104040b1545030210b200010b40300c0051048a0081c000c0d014001941082e41442041e400c3c404001d88a48450b9030010030310f1aa9642007040748507408014005c12150283e03503100000070340081548540d500c030300010a41c210310241003c0303008031301000301044100f49000ca4040c0e00615841507400700313a590500418148041c1c211001a8080010801490b5506001000310811101d880009089041000e100a0103034260083c50700742040100014020248807112550145c0044107050740d445100454402c6124012401c0c400081c03070050001c640f16141641e80086141d54501e04541c8984800c0385503a059480820700b54001d201d0f105490608640d0038511 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 272164802 1250 272163552 272163571
    0x1104061205071d07030b030a0510150b07080306131b200c09012d12020a060201091a2d010f05010e0303090d081201090209100206070807110a02030708070e 68
    0x20700c00040c01082c00320b0b001400130740030161100c00700c048550701070060741c0704189d01c41d048545080c500489030014115820303107a603429200980c0020a155070808513607509610120343d070301d99600c4600b00a01400c6a181c903100c2c56a1300c956400f040c8030b0f101c60707000015000351201d00c0c42102604000a03241899000c0b4100740d000386181e0201038984221090550303044074440c01a076902603a01800803c00c017074420703c206980e84c00010f040590b07088502c110b60f0007a9022081551508003d900f41e407404080103200380240301100715224040d00300950403000b42c2c1a2941000c0040e82075011400c3c40c42c5030309003d021005d004209440030390900e14014402070034040e0103400417400103030322401142c25aa00481300700380c13001304018035501291880b00c0318510a2a42e56110048240207401850b002c60045018500c01c02d41e0300e00000720b1a02c110500e0790b81c0a0306659164040303444c41004048402548924050b94005a4007803000c88003400317000c001060301500d00178425000807405000100c2d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 272166052 1250 272164802 272164829
    0x60806280b09130204090c171501052503080603160506030408070323040602070e01051309032604051b0d1103030409020c061906051309110406120507 66
    0x450040d040c0154210345100e040c035900d40e901c001c0400c80d24002803070b12a50b29440068085500d030240d5001c2c041c00b405036541c0962043e0200f101080c280c10135258502e101c14441010a8950311400c0103000211002c201c00c0300814442c0390303081c60300d10802801c60200b0060070400803241000c00008440c12040c481240c1251703d042e02040c05440080c00203006024000361240c00d250080c954450301e803a802080344c0c51111007410043d1950058000c0e50f0050123117604c00240e003040030208078180c9034010000a0349450003020356000300000b410440a020016440b20001d42e14501222900e03a1000288009894030f0f05d419070a2000f071f1141407160441151800445407145e81c1e18400d415031000009200c20b88140c0001c0c914043ca070b001d003901900000311265889404102d503800351060004451449004c66905400e0325100c0c082d40d81c0044119123454591001508080701c0d850149030356003a03924581012a040d104603402102e00d00b8103007840c1c0030070840100602c00050144064440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 272167302 1250 272166052 272166109
    0x30329011409030f0a030306142b020310020711060732060705041d090c010302130306050a021201060f0c020111031918080c0a1e030606060806 63
    0x40080a80441460410100d4030a4204585801c011640c990800030212000d03d4541c0204540c3d4a44030f080881c000790401c0c0002641c043c07180c0c0c141f070f00038400400c1c641c0010a484112804110406c181816080309034102e840035031014408040004000000136030b6039030f5581000c1210303010b0b0b5075a10303002c0c202c00c1101e18046469420300c0300c260f00c000501c1c1100481021900a0044c901d400c20200e940101c03401e10040c40c1d0048000d108a801840400c06070041840b0000f450388000c1f280c855982d005102d040020350b100780c0c01816140003051520320311a03100d464204c1104c004032110700402e540000d003010581c80f00d011160041405282c841810411f030040103008803c1120300034180080030b200c1002c1a9414403d0b01c2c2c2c0c0b000b0080700018440840400244021110002420655a03607800403440b4000420b017083c0081003c1e203d0f4030268034010003034040c10111051052900000d100110001700c140c01140002d1510340d4601d0340360b0510008200c680320006400e401803440c00480700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 272168552 1250 272167302 272167361
    0x11b051509012c0316050f03031e0603010902030705220f0c080c16020904060204080102190306050a0506040b030c07020a0e040204050a090b0a0504050f0a0b090c19090906060b040b070303 82
    0x1158042911710684400207a2881c0c854540102408400c0c3e40d0f00002c0700700008081aa203481c9400e0510126500850710b81c9001c2c1401c0702d096900281d010380000c1ca0601543c00d0900240544601c0e807102542101c1d0034001600480312080000e0042175200c80078817401c60b40c40303800a0f0b0030100700d000062903c2d031520b150450403010140000c0c01260b20702c000070148230391035059900a2400200a41d514600d51082021180300da207481804285401c10210f00350900d42c0680d800d988010b0413040c030745820820241c06c0c81e0801002c0355103103c1d0802590b801070b207559240900802090704001c4007805c06104200913a08000c0c4800c2940c1d107022a0b04001c0b0307d02940d0580c114130220320002d0301e5119405c1032804c0c07404550b84606103106a0480e032042101c00c0c7c02c058860040e240645a903968840c0801001c01c8402c004500192140b11080c4140f9a0550020707161920442d4006074203503549100802039081a4802d9003c1000403a10200341074150190702c008a0f0540d5041c0140110341894 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 272169802 1250 272168552 272168557
    0x20c03061f0e01090203090709050105030c04020d0b030a0b01060815100e01120e0c0a0801020a052b14061c0308070f0e04060f0512030306011b051509012c03 69
    0xc9001078846030400301200c01d992150080584009002d001540d07842d040000080e5005840750751042c17160f4500024a041c1512519058480c0200a04603042e800000c10000e074000c400003001031903488202940c01c0c1d400300a00040345110f20442e075444d6140c0b240c080c00c210b00090917822019018461040c0944c1d40c1e031405913034607402d410525010031481c00101e509104012180e0409403800306d0018031100c00140e42180e404c03040b00d0004003940c64001d220b003030740035481444000c14414000c0100343c00f8440300d00c180341040100261b0300e140015031500280d6a90a41d200700c03800d01e00050007801e061541500f900c0103201c012410000c1c816075401000c0010042511040000580340d400300e5034498405c042403c0b400600510078181c40e0b81d088204a001f511906220b003540c410035918040c800320135681316110503181c407485002861661003111802500c1250140240307500360f072a2480070300415014822203000010904480c0b8201c6641d200c03001e40940c8840d0219500c0a9001e000008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 272171052 1250 272169802 272169811
    0x3080409020f22050a120c050d02060f0f0702011b030c08090307050d1103010b01170601080601121401050306091b0f030a02121513080a080601110d020708060106020c0306 75
    0x40050382c9a6040081189034080d40c000c0007440d260350314003502e000c1d410f107000206441040303a030790414079584c50b4640761450b600e1b10b004200394401a8104082e00e00765140c590841d0029003a140381c07081102d190080303940094614220308101044031000d5590050400c402c44070740f0356440c001400251005040040ea0000c0100b91082c009581005c0d40c809100072002000d0150981039038180c10b24040041c90144c4203514002e40c6450608080341d07124940022403401200c019405545075500110783c1040020200e0b07041c0202003c80d4144403605209103c034484c0d0451094105504101c205401c000c80034000c0412580120840100d4045488034840305a074100c5070a002040d000c0040b90901000e5000a9400801181c41944101010890443e202a8406044070940e07400540a032801d654540203003100c4020310000c07000c030780140740342c03a0007040506001260b000e00c90080d61809020307021800c0103801420041100e11002c0010f02e0240219002800103a2107841c0403170303501c80c0c0040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 272172302 1250 272171052 272171069
    0x20319090c0f03050718050115052101090203041202030901120e07090c050a020c010203040b1213080406050406020606040e06130c0f1215050f06010e04110d1506020601030804 77
    0x540d1004110704101e901c0001c007401d040b0181031942d2810295295941d030310070083c46004403090041c0011052040d64144d443e42214100e248c15908021125904031003105508015281044040018845000390083c421000c02682e603282614003400040a1804200c0c00e5600c03c0c070007069640e07008040c0c0807400c00380c1000081c090508003019403820882c0d92105d004145271000941e4000d60041c0140202650f41c1c0885441a040344012a070740d01c20fa22074129030b91000d00c80354000c507a1408015810100c0d44090101d050519159a0703919031140e80300202040c0c00007000c014498040c040d4947c484412101007002010262034a503c442004206060158581c001d000c10448203508007805410703044201001c803034854500c2c100d003c01001c42a0341c81d00e1444140d444032162801403920a1090301f04542c102e8580d04010740d0b100b00040301c8154099110244e511007145048054035050616000100b10b10140c1c100e0310031012403a401c4081103401c100700600210746081d0844046a9641 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 272173552 1250 272172302 272172311
    0x6150b040504020a09030f080301030515010b0711131416090e010306090503130e19020304170c15040807021f1d0105121306060b0c072603030c03010801060504020319 73
    0x202e021030f0082c4441e0002000005456014400d200302340307003d0740c1030368414400c031001c040359021000346400c401d02c034264a0503020040d84001070703003c2c4ca0400ea0500090407041d586d400507003610301a00c07100c40b0f81c240380c04002402c1200c02410f0b6803510b403402846040100c0341034102500c03e000510140006400c8644812402c01040010022204600384c4032480b42c0b992511001260b100704c0003070b2207042c111581caa44181e26204907108413406282c1c802000301040c41e65400414454002d12030b007c040d401a0150798000c03101e41b42c0c603184200e104600c042d685a1180c070401c105400c6519a014042407080c61400307825400c11242031484940000340c4042062140c0101d8003172040d42912000c030a0301405100441143d0055001034522072003040c442c49848945000b03243c0100400c01c810395211003000c01480010b45440c0030180400d40199210070280c0402d149190b00a548a000928001004014141003031040201425040700c0651440c101000e54101441640940e00c0000d50384 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 272174802 1250 272173552 272173567
    0xb0f061603090f17010b0f03100e100905060108010e030a02060c07061d1e010c0e13061e080c03150a0b03160909030318020a0308030a1e060306150b04050402 69
    0x5800c0e800040050300803c0003c01c0e01c9114808503044102c1d0495440c0d800c01c0041209450002000e584400000d401800d10307604105148001d003044400c1c0b00725074042d5020316581d8021b14001e0b01e4001703004900030001d5501d003401325801c640c41c06c443c00d0342d250018009650b065501150f00d5402040c0a4103140d03c03490700d418000c2c01403000040c9111400c817080425401e0041c0441e4681402400705184680703054a034401ca82643c1502501d880000c2d0300384400903d915106078600d83c1070b9007800002441c01e8039980c0901c0c0850040e004c0800100f0019410080000100604c07610207100b0743c00341c4808042004c10740c099120142900044c151601c0d4025083d031001c1001d40c064901c0e0180c403059071551020000003c000305441507002900b001c00c40116081c0c034440c071503600c59010b0b1003291401d1550310b9a0015410182c00d8022545d10754450081d194058030405441c18001c2c2000100607145180c2a400c030781d50140e9051343c002902d4030410581c1c15031800e48003241e0098502503030310000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 272176052 1250 272174802 272174807
    0xa0807030c060f121b1209211107030f021f050405060702010c050607050a110114010608090307050a031808060f04120201090206030c040f1d0406150803070b0a0b0f061603 75
    0x10800c1011002e5190040784607548203a41d1104170221180d80f6001e0094100d2228001590072480c4003a0210580303031958000380403240020250b0b00000e1910070203418800c41c42d582003c03e540d0003a100614060540000e510304034180c0c424528070211842001c0081000240541c051481998460303070740884e4940c103590180503800c9480da80803094680074a010040036203039801c00081000046c20060000c182d0b8001441004a0b01c2d824210303203001c680c40c009045600410090410501740024088440003c00400a6050091185d00c03008200c00281c418003c0010b940d920004442c1d000101340700940c0f24400300c0640040c3c000031842640030a00340c00f80c0c0500943c00000b500102e0004c10002c1455a50024005403024000101742d0035a6500980d030703180b5900381c2446080101e41010070005401903000c0c91016039000c1d0880102a960340c00d031400c54000b40c006079105800c0804100c0081030b03a1040720b00c2408101c070204001d00d0031801142c02401a4040c00d070301610600c031068103150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 272177302 1250 272176052 272176067
    0xa050408040b1b0f070303080609180a120806180411061c060305010b010305010602100207170304050c030105010e090304030f0c0503030a23030f0402040b120313050a0807030c060f 79
    0x10580d81a070f0350b10307410711090076012420000140400e020304640038240100c00301d841d07001c49415580c0c0e003c807511164104482e03000c021b00321603441310609400d08582c010074090b0890f450301456001c10140842c2a025203000e00080425210f51440c040c00c901c1c002407035582581041d000105c8059102c00040410854401c0a25811a4400c19590303c18456041d40000c5e00303a034800d00081c028000340c2c00041d0f0980e5800e0080380c0158101001d0b40400c8103107a4040e2129900482d040040000a00300007802a80706540507030301c9811140590042d0708013401124018180e80050082d5450f0060519440c0d004034040200716291008061090050044d80e040191200400b502d0f40e40312141c0001c0d24803030114008080e06003600180c03140840f05003040e6071041c3c203d00302d030707420740c1e55560b0800005107143d603c01540305081c2001082e4401c1c080020b004410004240c410032141000c04200c840480f5901011556100050a07c0003d8101840c802101d1242c2030080100d21210403e4030043c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 272178552 1250 272177302 272177309
    0x60916020109081b100516080a02040308040303080105040b0a050f012d0f020609070e0a020d020d0c05030108070e160e030a0f050318060a020c010e0f130504021f080a05040804 77
    0x100300224102c4103250200c90210904c0011500f214065405910024241c0307400f25013504044129400325540503009030314a5501203070180c00185000d440e130b582c02207960015041a00012000e80050001d42404d21a020709420121070300484c16140038000391450500541040c10007040c2d0483e421444c80300c074004050701c40d50310003951440c8009907004200c4079080041100511800000c1010b140c00401c1c51415183e18a0600c05c09586050a400180d44101207582e9000ea08000307030240d40100b807051081c1d013135407552010303075a5150a031443c0c070b4603040b0b400100400000d002401441071780b502040ca540300c01f074145100b0825040c40020305003017203688068404003068450000300003010004144c2c000302ca80190381c02400b142c00b40a00d900502c510400075034420300c0f400b40c0640c007408003403411721700040c801d025090500f404605040013640d03c28503901d4446060200b1490502c42582e440060803428a4a51601013030080034a038014046841050303895004c0f5042c40f40c40c00480300907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 272179802 1250 272178552 272178563
    0x1603060905040f111f0503131b0503120a021011040302060f0909010603090302030306011d100203130506070206160606150c06050702060c1b0c040e030c010b0405060916020109 77
    0x19140a0030421400c4414100440c1c0702244502e040b540d40c645010201708400107000b510011a54a00003541d05034006860750381103d040c0401000000d180071401081e80e000d0300520005d062500c4141450500c03000c00f407022078101400302400490340003c49644013011408089860400216450600c5c800c2c1d420183d0824000500900940203440c001d103d90324060b1145403880e03030390b00070440440c1d503003201c0100141c10820110340707203602c1400c0d45003a10328420400c00140a041c000103580083c4d0412000142e0404606107080c3c50084980b9402001f050b00d299140130820360015103180309032920090b01032140d50343c240078005203512210180a109002e019191403440025020591060b002c035038860501c0c0000c0c10540c40402c0c083d00851003062142e091000c541c9094501c20300200140b42d16109103000b0358540e0350b45000d5028443c085030060366030303402a103003a9800d403100c50306414052401d08082c040e16842d684250b80d8443e4540210080300000d4981c104e015000f080f01c00b400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 272181052 1250 272179802 272179811
    0x1b01050a170408160c060e06030f18160f0302040501080102090303190203070b040803190905191403040e0f070f091202010314090705030706020c090f06030f1c090602031216030609 79
    0xc000c3c030f02002c170781510f165840d0040030104081c100070307441c0700495584184020301d20204620380311101c0304405164402d41501c00c4d107441070000625001c2980d00840d41640c3c600410030a6040510a25014040c400025072034150f00d00b020a581340300b8100c015540c80082c01c1c003442201d200740152002c0d907030b001010300c08a0030b260501640c40e810555039500c800c902003400c2c1e28180c0705407098100aa1744140680700d400c01d0b295060b04498aa0305068950341801e00000b0801e440920040019040002d00014541460701624101c0c1800070080d0050051118100001c0c82d040040c900880e402100b03069428500c0e44012000f4140104100c4d640450070f1090003031000d00858101c007a120f05608450040c0d6549204030f9407000c1007949107401820b03d2000c10412441c8099079940008003030203e61061840061440c9840c40810811100c20992a022000542e1012000c001001c0a100450600b110440d0303000245d4030151140071030b041c2100300c0134035842c0a901300d0700050803008001c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 272182302 1250 272181052 272181097
    0x314030c0303150406140a0608090c131a0108040308010e07030209043909030b04140a0302030d060b03071205091903030b09060402030c04032d051b01050a170408 71
    0x3c6249400c14903030740c030440c00c00c5c202280d030b034046a0142c04d084100030401038000d40b400030103490155000d400301c0464015101c80c2c1c02540c40b003107102400204660000035041040c804920300c001c100e510001c0c10003e6480521000c240d00c045454150340c1d0b6620581801c3d119110264028440e000016401a00b000807040403140b13602c07010294810f0f00720358035040b0302e0b1048600e2310b961345080000b00842c10070001800421072011080e58410b105a28050002414603045450040036400c22001039100150a0010706100d0180400418108040c1c034154105140d000c1c025600700380200705101c2d07031040003031041c01040041c44c030766900f40402d201010f005c40c20000c1c064051210401d02601c0ca0801080c440d060074030131a4403a0311404010380c1064207641c3da07007041000b20400d8200400c04a800b50f00e9015403000000181c0d0702c148002c0054400780c00141c0b403c54996001a4103100c02030040720121307500301758004912800b1640400e8255100d19144065006140d00c0d00640d00d203240441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 272183552 1250 272182302 272182321
    0x603061103071229040906060323010207110915060a180e13021002121c0b0910150207090609060e090d0512040f060504290108070314030c0303 63
    0x303502482c1640d07a0040000c811142e503809844582c1e802c2c0300155081c1160001608008580e0301c4a00d00c000c20100f1040b48540b15441501e03101c2d0400d444000030045404400588491061403503080718000f5810403d19448e005a0514210115401404a17000082c000701d4456500440c41c00000c02094855480540042c03040d0980320002c0e00c295103030717038012a01d06000f402403403007810241c45003845a0303055401d200310300c03030359860000c1940300d801049411500e01c1e0000c1d050064504a000184007019001001952141c0b1200d50244422a092101d14081c0e184680181ca400313200028480c0f422410403454024a640500c08440c540034000c1200261a004207089640c59034844002d40c8424030340589030655030300490045413003041213116003400500c00705e40c090301506045003030180c03584a040a41d8800c460494080f980005040300608203880100500350307070184040b07a02e40c10480c0c80307a5280c01034000a01444c6a0a00c0c000c00a00b040045980c9405c444040d41c0e00c900300510030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 272184802 1250 272183552 272183557
    0x602030a0c020111040306090503040806010909060b041404061e020309030705120a0801030b10090c2106080c0609030c060d050105090106050703020c0f0102071a09041401030f1506030611 82
    0x32010320340d04011114540d40d205000e207444090714802568542031940e590200103000c0031408441170f0205100c0064000014071485e4001d168520300864128160f00d06541100c18190041d4850b91812020b0340714400146051a4002ea00210011f0300d5004240540000040b00c08101605400041080103000c80480a40f034490310441c100c88401c0c9104034484440c0c021420b61400103610540100041580e000b05150003410414100e0011a207840c48082942c00c9180f1410203d102d90029290b141803407401d00a205800381b80c1001081d0070309440c55190010101024461078001c2981010b0b0f560a10032100f0b841c0d4010061651040c0809821303010789024483c00c0d00c60310f00300c0000141940074100310f80c48658154041c1c41520584001c000001140c509103c0c110700c00c0380000306211030b40c66405030609503518407054a035038044c1d04200980f00ba50181080f064111f41c010800240c21045140610b039200312002030307070a8864110030041000d580003500c8642025031082d11503014000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 272186052 1250 272184802 272184811
    0x1809021311030408030406090b0a1b2303041b0e01090b060a0c03030c020c030105070909062102010807110303010b0702040b0a0f0521030c0c1e011403060d020d060203 73
    0x318000d454001442600480e00081d807500c0c501d450800000d000580082e00035035015208400025407803455485101c80302500729011005a0313900c4203c20124a1850607000302c01500d0300d0718041d50002c60050a0780d0b5142032219a510f07140100101d8100040510200d15500c94626241d00300303036403400b60b088000300a200d40c10102e0703d8007601000e03a0078210b08130f038800301107a140c140e00c0b8a042d0f07a0413002480400c40400841c0034034440701805590a001c3c00b401001c0c25608c10003081e0400e201c5804951080e4070a000322030105402640148042006a00fa5602401c1101071a96500c006441d002e41d1804480701c0d03400000300124003840c2090241c0714a40c001e07031307041094855a006100659002d40138444c5800700c1d00d03c040182d442d1081c1d049450070080450498816810300c1c410b0700e1908001c0c1800300380e41010340b14210030300301000b494528100c000484005800c183c80080c2041501b50401c244c90880000040d0302e54603070303400040040e035000d4044081808242070000c029001070380e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 272187302 1250 272186052 272186059
    0x10e010f0b10080c1902010b030d030b0103112d040f03050703060606050c0616050918070f0f08060402030601030b1305041103032704060f0e1e01151404180902 70
    0x10100b40181c45210300c10711a08041c0f80091a101d10b41c5106800381090040e41011507483c2c204801490318144132000c0e458002c2e4078081212007a000025082d1019460405450101882103c0c0c601008034102102c030ba1803005100c850300008a4560020f2060303400409001d0b603854000420401c001903441e00b1680200010410b51341c41d00e004607001d2003540c5500301154040d101159005141c181259449511414900d01c0c201115001c01d01c00b44179294580c0c0d0b0101c02c00f04010700150407400c640c1542c5154a0b156070600c45014001d8103111001e407815004a6000c0002003043e40694040408454000c01450001300302c814408081c04003200d045920b0f040c1d001e0000c0c4181000000e43d105445210380345460098660004010030014104555000d030322088001102d00b080d181301400380140843c210a0340c507202120091401c0005400f0744089010700c010440c02c2c010207140c48004040d03280c10001611070030403100c0a40101d80081131803101d6190028003050090344242c41292094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 272188552 1250 272187302 272187319
    0x70504030510060b070201030e011d0304031401090302031602010c0204050c09010f050a0e010c0807020a0e04060540120302071a01030b0c0c030408120c21040b0c010e010f0b 76
    0xc00c0b40000e4a4441c40f805490550078002ea01c0190301a400151307140c0c200c02c00000302103d44665015240181e4501e6100c1a08001020300520501000c5681942e01c1c5000034041c61403a0f80c0c00039a284114aa0310599008031070030b24085a2241a800003003070b030024018409800d02e5481c00046611121806012407000b060f80c801c80c500410580e40c40b0350190312030501d55007128005450001400004071074840040100c1e00060303490251007406891040c103c041d0038900741c50140300300c0303034040c0400c0d00b10b00442029040c0d000003c49821410408010b40011602c0c400c05c418102c5002d980004121307484070800a80c0c0305034103a000e020401c1c082c0d83d00d9240360a90b200d0042c10280203000141c03c018441001601441140c8001c000901c04041142d2600380d4031a1010708040308013080b800c1140002401c0700e4103060410042c5030103401c040c0700300f150140c54109400c1504c554032a16010140101d40840141c07001e5210040500b03680e0000d221540c840741c0460b00400f010b013107403482038465 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 272189802 1250 272188552 272188573
    0x160503060d060e0340170c12070602100b0609010309031716020d1404060c050f030a0e0f060a09030b0705040302030703080c060f1012061107060608010b010e181e0705040305 76
    0x5c0c000038070f108101c0254001165403e100d014911a00c0c4012a00101d108201d403207400c90300c0c0c014820b2108240500036142d01406c2290003030070039908100d01da640700d0030140c00305582e03500c020817980340ba40c0908000651510528bc19108902002958400840400108a007440310f110903290744c4101c1e03600340c1d007034045040802d5594452a04000c120f50310f0a0205102c0180039900015072103000b8012110340d10803100c40e0620b0340d0302c02c0c1c2e00b1400080c0d07400c580e105076040646151641c0c04040311075600f003000f0740c04010080b4039103110240c60190910f001c40c0d2403030b000300202e401458018003562120342e00d900344982c4941c003020511420381308820000c0c611814446185000d02002c00341c0d82e845600d449030796402950014419981c4550b40d11502d40c00400311001418881c1c4a980082201403a1004060841d0014007806040c05040e500303980300396031080f0107120242c0f24104440855214829043d0b0002020718207203075141520300a000c4900c1d0490042c01c1180d11a40c221480e0b07421 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 272191052 1250 272189802 272189887
    0xa060e060d0c090c020a02060d14011d150a05030d0c0b130521040b0c060714030c1605010605040c0804060c02010903120509151005010305160503060d060e03 69
    0x8000d080035242c0140c2d41c0060010f03000707503080101c6408407403040314000202c540004045501c400c129151440c3e5a800070001d0340b000072007480c01010168007003c0a100f4800701078081c1c0000606402c0540c6041d00c2e80c481715503840c8032000103000098116000c150b10000064001103803848142c64200c5c101c4001040710501004410036598010042d000b050031110824091388140c44100c03504031300600c80801c00c90740040241002c080058028821410a10710242c012500c0800300c8008000403c00c11080601480032186040b03c5181d9060041c8400c2c01d180f401441c440d0056035020381401c1c2603180340b0f60f002c08660b01441c040c080802108014660aa080307840d01c00700100807651f0a801ca00c0b5022041d44566444949031080d94440c5c40319890ba030104c00f000711002190742d00425818800303540d1500c11140d2220b1084100340340b0b40c0c0c4c0000c01030100e020041203684642e03000c060a00c20001107420a10000f4902c00840e919503512008043c94520130841040100743d10441241c0c1144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 272192302 1250 272191052 272191069
    0x102190206060d11010c0f06050f010519030c2d030b060111210702030f010c05030921040308090d060f050627070e03071206020a08010f0f051c0b0a060e06 68
    0x2c0e4130490304101d41400d1001580c1e690300c11107041d61403844441c808070200d401401541c0c0305080328620405598141000c00940241401060140212280041c4002411081224180c60001108080350b41c050110100c104d20300208404901c000301a00000f081320000c0c01038011402600c50f00d041341c03440442c40d540c44101c10300e80445250544005544484030310010000907002809481c4c801d1490041070742900c0004181c00b000403000010492040000e005055105410340c1d0142214610034880e00307201c0c0110f000107000c00c90001001d2156507030300c1c0f04a0001c164480010322007610324407030603402000c0c11105a80a41d40e1000200f00307641c1c654203403c051990f510a80181da88980c0c2040302d08900c0060103680611503298089190506079299900c7e2500c620300160b0307079080c5040018010801079000290f461080032090040100f0814000103507001034030441d0662603414144011020050400342c080441c45080c1b005141c00c0740c204070151600001e80101725100c0c04107002200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 272193552 1250 272192302 272192329
    0x10b0f100815130509070915060c110103020403050d020c030d08041a04050102040f08031305010314010303050d02120103110a06050f16050a060c0f180605040303051b010219020606 79
    0x5034141c00254000140031841101401c0207841e1200b14200d00124004803034058501d907034154412039040203d813001e030040b04c1003000c0b0902040d00151400703102410720b036102c0d0401003001e16040c00d20341041e40b0039410f03140155006001c83c1d03070030500c02e18042c1d1240b105102d224028083c00107080700c1d181c05400d000780a6503001075500000c0300101048103207208044c1c41101c095400300310010b0382c0f04440e0444405400c0400c05195140c0044145580c803100d582d02c464103160910300c8205510035002405170459070941041a80da001c807270000f170000e03c5252440740300f8071030f04000401803091070714240d60038080641e0070b83c810584a100a403a24094581c80794244c810400030080341128119040504078800c100721804603c0c41d58500003a60380344090800010b00345804030340500d40c40b404054041d0300555400380c80c54142a401015849240006800d100d40095111000302c0e203807401988010042008546800c104182844507910074007038200181f00e8080410843d290100845e10354 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 272194802 1250 272193552 272193557
    0x601170f06040b0f040f02030303100e010504050126030405210607020714060901031e140c07031715030706110d02010b031c090911030f160215090304080708010b0f10 73
    0xf140e44102c120b28000780000c004840700029508a100161000c0000c0d40c0220302c03912030180c1450034509280c0140c0416441188181d040c100100308003903a00c1041c591090607100c04081c001d4000d05901d207184666400260400c1e16003c0d46498032844529180201311200196052529295800c903a180102d003e4079a110f88038031025141c5140c150000c042c006c03010304003c501503800f4660700c0da50b40010140f10040a4541c1b02c081348001e42d90880c240e0054011401a080501544009200715801c0701c0d2103104062030070200700c80151800300001d0070714008045580e010b40307681000f440c0004080120825200c0d60305020781c40f60060191019661000e4024071504490105103200468030110140501c0302c1c82c0700100f000c2e2402d02400701c64585044456a407800e1454508030000002000c65051509404103a40400d60100390701044e00c01400c111007140d00d80040d51800c0d8803039680080050320410000041e4044103401c03d60301601d0845290000001d15014480c40001d0646403000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 272196052 1250 272194802 272194823
    0x3150b0f1b030702011d0414090307060b0105130501030b04021b0f06090a0305030a11040b04030f05121204060e1e010e0111030103020a03060f0b1e0a05010504050604170f0601170f0604 81
    0x2c1c0e07444028428151840c0103001044445501705960105002609c0c255215080060301000b840071902901c400c03203100380307006441c100c1d89802c03502d6071001d940201410181c8540183d1900d90740e54068611516401d40b40030417140344803442e1079880e2440c1428102038002e10000600030b840104108800c190152256442e50345c2d600c885034002e040e003615a15000000344004950058035030050701c05544911440c1010700403c0c140689400008078484010000811041928400394050b0717540081c0d00900114103841d55003255401c05985250a92040c0c5140311b0b44400c00c64150014196500742c0f000800007007090345c4600000d80310034080079410048145c1d0420006002d50b01594503000c4c0840700064000d0428000b4001200c003d5040d26966100740d1a003038070745041d40fa100010310f02402c2040c80c251410002c60420b000740e1003032041c1c4468480201c0b00307480e02032101c10300541400c0d05031103044d0b03161072200d030100150608003117030340c411a4180e00922800240ba50f0041e0f801c2360038040e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 272197302 1250 272196052 272196077
    0x120a1109040504050a05060c130902040f05060c0a02060d02130e1314070509160e01020708100b0a0308070c0303020715091406090901080601080c0d1203150b0f1b03070201 75
    0x1001d010b010304225440d225401110000c2401400000d0240740700c4032025588440d0000d8081220321582c000b001c20b2031040004200c045900c0c0061400c4a20035104030b07482e41d4441c4040d03030a0030228240690030140000f80c510030028240e0050468170100c1c240052501d48401126000315130850303002c10b4004690745070101040401a4062400c9408411030f40a182c0f0360340450301106081c1d41020340f140d03945c40302d01a9550000810310303150900f8030042c0f060034540f061880e501c0d074148400c00e02e641d0340d5000303141d01500c070a02044d01454001620f5542c130b4000d8981400c40d800e04d031000307400502400070045008004810042c0000d40300f40d0f03403104018280342207003000c00a5001996400b00c4100f041614a4842d1a01c09009203814801703444590b04d801140740c100000c13004d80c02e03c10b0003011000c50008002c03042e80e4845040310f00d00000c88503841103060120102c03d821240e84030802060143c2c552107124020680c0014011020414030303801d26034030b9503900034608002d0200300c2c800d0408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 272198552 1250 272197302 272197309
    0x1805060303040b0c0a02090105040c1707110604081908010311190801050405010e1204051e1903050105160e0612060f060706150e090303010b0307030b1005120a1109 72
    0x454000500509480c640b59941d0030f01591680031450108041c0c2041036143c0542c617160109a00518058905115983c0240801082a280204220703e40b041c10404947e411340301d160402801c0e80994202d5200742002c7c00d00491580040c02d0301c2854003400c41301d00c8002c82c8030f0903040c2c0c100c80d07000058000b041909001c201e503140c0b011301c0704540c0403042e180c00108441c09029060080d070280e0000038003010f10b030484e02d0a04c605040c5c4284254405c00c010015601c48007514410907018030ba0300e40250041c00300050007aa080081512219400328000c01840019031000d8010400005c0951000a50b0241520181480303404554080c0d01030080040d400c185240700c40d407210008102883e4120f201c00081c0450300014001e643d801d0b9201d102080c607610849050000d4030514001c440c440c60101026940c0f8841405102c041d40000300200b40f03100c1c0640c124101c41c140040a091007911500001049038010002d454004000c13103003c0384c401c0c1414450351881c4418145002d16005614060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 272199802 1250 272198552 272198561
    0x207060e010e0d08030f0106030203061008040507150f1107270b060d06030506091c0f020a060f0c030b1203040506070807050708060403080709080a032601150f030618 73
    0xa81404480104400a0303030350050292581c91248034007584904203d281c6c07041880d01600803105251040040c01616601c40c11004624070700791034180d925540e02d03d02241000c0305a0f1040505101d01c182d59000035070030a0803003001c0c003942d0303562024620210070042d99030506482031800c88110944050007692a2100b28107850b0441000820510410710208445901605140301c02d1a030b030b41d83c140200202440200c3d0404102401403203041d414201d85401074585144003400c0c04140520724600d14005c0c084010030300d0300500200034038507050048001078a4449820300020385030001030400c51510445900030300341810019800c007414032050000d035500004003651200340520002d000640e04220321006080071001030003a50900d86409403030320b000a0305460612500941c1800075034000140e403d81907425103441c081c1203001d01040c00c005170000d003001e41d000504500210320819846450138082c00c6076562a0006480d0990490403500d141c0156071340e510020000811148041d040f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 272201052 1250 272199802 272199827
    0xb04050409140d0e03010c02070302090a0507022104050f060a0207030305220f090b0604030b060409030e040203040c030c05011106060415081902130506010804061a0d0b0105030f01020901020706 85
    0x2505054800c000e20a01d103805401c0d0f007040c001850501c3e08180c103040a004200c1a1103142c00145621811980003424400d00100081e0107280c2e11400900f0340c81c4200030307a100f016030f045800e80440c00080e51205044d0310a026207030148841c144096181d040000484800740701d00e501520030b05003985c2e42141c1c00e91080110301c05025407819000740c0041485007500003010322902c1c000685217400c18030415554000a100d10510b001d10082000c00c1801200300d5000307000311070010702112035190640700507400c00400742d00709102104120402015084100942c0d0150b111200e4080c2d40318011201c1d00402c1c0c03200c4a0790b420160114a060410f5000f060020704800502d5103031075142ca440e54607265207903609944820959441a06600340125440c28020002c0c0041c44145043c80010b002c000014000400040d80d9412051082c145000904140d06004010104418990800c2482070000b8001c140c030a000f81c00402c4035200e41482180c0b0b1100b01030f005410458a040c500340c809840400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 272202302 1250 272201052 272201063
    0x714070b0a151d091f05060a0905090c1e0a27050403090e060109030f081804020d020c01110c060720010203161b260c07080618070b04050409 62
    0x400c4018001040b10001900c070510070030400054102d18184000800f411049403074102d00008070100c03400708900c174900301ca488008600358a41002066401407540c3c00011614500300500070300c51000300e903412a041c01280d5000c804403905103201400c2d054106800c1d400506014104031203658052031314000507040b95081b070000c06a895130701c10b03240120344c2140081c14503042401b02072032822480c1c2d00310381c0c01c1c81c282c04900d00b541e45401c00c02640440152080c640400c035440c0613001800c0e042243d50001d041903448844444050307001c1e404c611036404495080c1080c0c801b0315075030b10055a003120300c80c0001f03003180d4850000545506425400c0480e001c101407075902440d4000340000c6025900054044001c412100402071a000b420b400740c008107031f25a149540800c001c141e0380c0b80841e1800503404440240c001e0a144188141c1958401c540181e050004114602103580c0707100356907005130703240c040c0480c64105490718103a000381d40039248240014401e509055002040342d500c5103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 272203552 1250 272202302 272202311
    0x1203020111070308010e07020f030d0e010e070b0d060504020c070509041509030206040b06060304032f0a050102040e060a0e040b040c1e0f0603140a090507030221060714070b0a 77
    0x20440d101e280d000301010ba004c2842c0c0001013100d00c10381c070113660b4014002c1c400303030034020a044141c0d6100e2003480315079800d2a45480c44034001369400e61140500d0f2020004035806940d40d901d400805da007120f4846401a8a0300380c0c0080d00341428021200079038244000303442807a06000400050b02d0000d0300989d11440d90311176900e90307103086d0f01c500015a80a500180024501407500c0d203441003005061601851062041c880003079040904021001030303094046000c100c929086451040000300720300383d2071090686290a211040d402401600e12503030b00b00b0030035942d0800b440342d07010f114800c60010348880c03400030300440c5034001d80d0b0350450704c5114941c01041e40c640c19075028070003035442c200c0074a8081c1c1c0104042c504100c1000c005003000d040a101002c1d41c00d03c0c84460702d0000300f00c400e0035038a4a01c1402000002e2042c030b00a554000d25021412054450300000680124140d680600c5410080340d80c0314000c041414042040c1e10350b42d881c2513080d584400c0141009050b030007903507485 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 272204802 1250 272203552 272203571
    0x31c0c0512010306050a06060c1a07020f0106030b01170d0f0309110a03060b10020c0307180e03131d010f030f0f0b0c07051b0a050108151f020c01030c050412030201 72
    0x16014002d0086004010110352414254400b00480740e07682d1112007070203001211240004c1c0144122101e000401406841c25517a12000b642052162414000c140d46888004020000d00801407416a45002c40c550441248400038a560b07120245d58070011800b5110b0301041103200f40c010721441e6200d016400c45150180703003c40c079a068603800866055444429219036410802561054030101d44010900c1c16512000720b0340b03a5086016411140d1030864111030a24401e4100b00c0c0355214040c00c0700c1e0340341c0c44440924400c0d003180c0200c0310410311101612044202c180d00d800e050ba00070940485002e840e550b5102003a02042e201200d4a8110004803030128002d4400c082c410020010343c00ea807412240f40c81d908200740c410b0034688442d1491501c00e6039843c0c2c41c02d500152442030a2820140d00c030780d0b0900d407444445051995110000c00740044040d0481d12440b407968a00e40c00710741c00d10743c00100543c01d8072400503828001279014842023003a0780c540f055540401e8068000094640303227 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 272206052 1250 272204802 272204827
    0x6091a090a060c03030b040b060a030216020a1e061d100309050f011508150606090d061a0a0e15060a090e011d0c070503070f11210f031c0c05 62
    0x660342c40710001c141180f00103014190140251607507811300b100c040003848481400110329000d45103c0d44100340d80840c2c002c400341e080d104030181d042e40082c00c024106d82d441c030b00c803112000c45850081c44294204170004089004001503000c24508031541c44901400f1410b01404802001d01d4100301074481881c800822800c2c0100c03404440341000100f2a018003401c003801103c075507481102d41d40d0200c401c031080050315070006070b0041000c4881954603007c400021303403c00310640c8060503031f40c80c0c9414424095540c80c60203040800590b00c010a880e034910030580c0d00c1c0300403600b8890110104512071200d250201c0144500081e900740034207099107444400e110030009810070901c0e80300075104010110400410240e0080a18100707600d00301469545680364025020000d140c80400ba1041d82000558140c1da00120317800750034401c071a07140d040d043ca8410070b03100d200311042c01030119810b02810044211032045c0c0c2d01c01c00c0381c0d07507041c034808802d40104005201c1c0410040c0a02080701006c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 272207302 1250 272206052 272206069
    0xf0e1e04080d09140d0e060304060f0b1e090705070b0402010f03020418020c0c0a0b0f030a230601031416050309030d0e0708070503070e1503010b1201060807050a06091a09 75
    0x18041d10090801c4519002601d15018540307017424244040606e02040e03a070340d07440440c1d5100380d01000206030b0b9041f0595540140150f150030381e51040c001058018002011109200c400e00101c49100032034a503c0b0044e50144070b500340150150750402c0c000b40165000303005804c050815031800500c1c003581c1e002c0462199008034852005603800040c03401c0710309410480240e00c41c00440305440480d25259a4035018420700703085001e004e001000107110a0515400b55a6516808070713440c801c0022203c2040d204201120440e02007440e040341d1844091030525603600c079100c009044c0480d141468400d403080d4200400c02c20851100b0081c891440c00e807401083c0301e400a400040510074103198000e4100041074004c10300a50099804020242a00007143e0f0403a0324036109004d55082400400e02514145625641040000c4420a480c401c1540f01c0c008403182d1905480d40e0b5030b200c00c20005513940d14494071000520120007800008656001e04100c41e01070b400c030f185824820008601d41c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 272208552 1250 272207302 272207321
    0x70312051e01050406060207180b1917010c050d11071407030210030b0906040c0203120c04150309020f060a0c21090b0319050a1103100f0e1e04080d 65
    0x480c89480d070903646020380441c850140000715014085d079801c10034005c3d40c1c1d480f54401c0061400b10300000081040056002c0c0304140c070003400720b40585181200740d44048400d03216012031f20800fa007901140503c107116860010150303540b01481c200c0d100480002500b54a5036005414008000100004001024282680b00d1010280c900d1034590300402c0054403260195100f4036062901220040c2d65890005a12040881c1e000443e4148003204130728601410752854074440e110b5040c4000342500001600403030301040e040700c020202a1104405483e000d0314000c1d00080c2d0b0f40280c90007450103802400b0144400d15029180086030b4031003d04a65400d94010b14020b07580a44035111548089448054848154035034518209240c881c014418034456030103056507183c0119010010303a40001d0807011100700ca054032803e103003402d51800c00031480390f1100c2040c071103000954001030140361440740101070120a006044010b1040c00017000034822a105034003041400e450654500c5102c1c81e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 272209802 1250 272208552 272208571
    0x3050c04050a080d110d020c0108041a090105061905061b0a0f0b0f0703090213051008010603140c030a0312020f09210c060c0a03050c0109050d1e0503060d0807031205 73
    0x100700444c40702800204182103072a0490304003600c00200340b6000505401c8500c4203107030140c807590710341c102403200c81d00641e052104c048180091042c41441508070502865086840c036207110511001c143d404004c5114080c2c0000060110000c2d1030f09480d03900555401320400d4079250300710395a8440c00c0c45826075046880c030100d603061041c850340300500c050344000c06007410024614141c00080d18010044500e03018140c4800025510300c03420f5449030000c14403813000707021450b02c0340342107054010184460311080c850320545003028900041c1500302e803501034542c00b51000541120707802952003142c00c012040c0040000705620346a07045aa0208030490a080e5005205080550309026040f078105101d600c003880b81040740b800208081d0b042d9640750400d10741c0c1c0c12031401081e0146c1040a40a066400344a00340a0705c2794101c500140c2c124090410a0501d0034061000d40b0b4a0100307448164000c0480c4c4550800602040010803409010f8200011800403107000203080e43c0c1c0c116005000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 272211052 1250 272209802 272209813
    0x5040308100509010506070204090302010b0307080a05010e010212070516020901090608060609150409030e0a0603020c060901020309120307270f050108090a12050c030a1d0d1203050c04050a08 84
    0x22107404840107080504003c0741c84402039450f020001e400780c01100400f910071951240f84004150003544114000304000e001e0f86e50860342d808802c0e458180682090b1655400c1c11a10700c400c040c18822240c41d8000d000c00384c0d5a41d21000400c4400f80c10000e0075104003942410304102503a12144071301e0003424229400710700e807401d01e0b55250070410042c240500407000d51044c005441c600c0d08485510035826100010200c030a800c00710741c000c10114070241c1001c10401d000c030301154503070018040c25680c0e00499159461f0798241e2400c03807108450880081e000300d00c01c96002d030b17050001140c01204a10346080d0803c850b6031100e044a101e01001d04070b6040a134410030041954440402c01403109080820b8503140000318151036003003510700106048040403850440741d0060055401c103440c1c41003100c0c0c6410400e0340185c5148003d000d2595072a004084040507031400710880b048069000004280b0540501c01c01d40183c8409404800300060610002c01e176902c0b201e40440037405490010503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 272212302 1250 272211052 272211061
    0x80d0f170a020d11190810030218060102010e06010f090f02090603150f01020102041802070303060e0f040309050603071e0e06180a1406070807020315010602011401060801080d0309060f05040308 85
    0x404030703400308101512004c0c05100c0c50086851000301051000c000342400c06550361460145440d040c40380e00000d510600e01b40a01ca20b030030181040d10310558003a0000c20005040e440c00c3c40e40c541092181403100b500202e000d200b076820300d03040903c100d000150017500b800c0c031010008500d90411078400010b07420340d00c201320789031900140051442000380000c41c80d141c1003003c02040c0ba0400d00d45a100c1079000205441090710980c0700200601c01c141c429403640c1001594190280c0c82524283c0005840c1200810310f413a043d8102e80c040c90303880d100c0e2a815080050503c00f1425400c0000052000c1a054401240c0f20180109002c12801291440490403002086000346407904808101190b4490b14443da0b29180708542103603070840b242a4582100d480020b1030701c4940d0481411104000d00001100e0340c054000380341c0c5043d00c01c0071111680e01c0d00b808880b81d4000348550401c6920006001c03a9181c080d51080b80b4060003010003250090b0a503103042c3c1551019101100054480e00401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 272213552 1250 272212302 272212327
    0x60305060703060b13090207050f0a0803040b070516020f030f070b0a17010501020c090910090b09010509010915110409020a08010501091e060305180f030c100204080d0f170a02 77
    0x400546101310005003010101c450316a1603032154001c07608001c2d4001054814440b003005841c0c003400008003210494050307840d00c0d00e2903400680d0102ca00110300c2002c10100ba0103001a42d16644100081210940c401e800300b0110a9038420b407960180562104444205004c0c4000340240a030003103803075940c0040b11001054980c61038180c1c02030000000c0180500da9002c01da54000172000c071148941078641d420464202400c105480201c0d510b0071000c08108101c0110040c422040b5034020009582d0300441705080c0c8008190080481d0004040490210101e622211048220504007402d15444500c00701c200c0c3c2c00100c84401207448907004000750760b070100c0e03200003134284501d640544100a2400000b841102e00400c810b043e00d5200003489a01e41d50211645400310b14226403200380907680140e00e03075104059045843c042e03510a04d004281d580200c60454002d81300400b07402e41d0182c0e040740c610454480034401c014641d0031079000440c00e40c001da401002d240c40e0041c0c0d15414601403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272214802 1250 272213552 272213561
    0x3507020c0406080a121103130603050a0513060513060e0304051f050726210106051c1a0a090501060206070804080a08060102030405060708030406110301270f060305060703 75
    0x2910322541c00c054007807001203c0424070003046544590407a00851244100796030503455403900b021244004a407841c0085030b50000e0104860041d10104496141c00700305009440044540402c2124000208000a840c40d4000c2d50b001e09500904400c0018030f44c2c400301501c48403503012202d503202041c14042440e00089810780810707800b0395896001031f04400604030340503011020b00940260b12120001c0e00c4811100c00050a80c14415550b0320300c4140b94590141280650010040c00d1000206400b03014038201d5410082040d801d065200811900310060040d0400601c00707009840968149074856102140c0070305403030200481d4a42c1803410085c94044000d042c1c5081001036418400882d84500c222800c0c7c20161508900680d50000140d00d1442941d0040340c111000146039000d0103044005140100e1003900e0511800b1703090480702905000c00c0c002e01c05065000c016100b00c1d401880042d0039006140000407901e1098070340c00c0001c4561a61055800c0e410050411401d0780c0d25104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 272216052 1250 272214802 272214823
    0x2090316030314070c0302060304062a020304120c050a180b06120109090c05030d031d03070317040c030803040c08060601020a031d040f05150a0e0106020d350702 71
    0x14140840d49151802000c900c000004110a03400000b204004c1c0814281060065600501080d5030f90905203485030040400c44141c0c1e051030180b030101e08040c82448445440c1140da6401142410b0420850090922308000203d4400080c4200010f8980301c1c450b0345002040742440c1d4500745070240031100159000c13200224461402003120340d62400446407d54196004440d000420751454642050440010740180d98103100b1050743e0804d46070b05420085184000c04002032100c401c015a060756030140c2d000090120304110000d10f1225420696194441e0040010241056894989070700035882921300f5205640250400d00c1003003810404680c00c039000380f00401d0b40e01d000b524001c06441c90344208280b20b8040580800c0e80f69220f400c41c07015040c1d20001000742e42805907089204050b550303052400343d01a03000000f542501080464100d0303140b40c0141034007004040301211244454124107800311141c202101090484010080d400d14100140320003c0c01e0445000c9e02d0032003103d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 272217302 1250 272216052 272216083
    0x606030c060905090408031911030615040518060d060609021305010c052e05010f030b060a0305030313020d0605040b1902090d020402090a12030e09070f05160602040803040603020903 80
    0x4004200f50380303854400381da2154000e04415269211300c07024441c081c2400d401c0f410401d0802d640d0340d0b00c249200008600071807040b144c090080081d4001c20f03595000d2407060b20f42c000d680c2d002000894406004403540081c0003020307158400c810756504001c46401d60081c0d01101c0e80400e43c4000c50305400b04180281c503007403c2c00500131685035607580c1c0d60ba0509000341104003c00314105c01c0421010b02c0c1c0034000f81d4442040c4080d68580070540a500c07034a200c01c4e9116a22000400c85600f4080e48032810340380c001014500c2c6940f103c0c0d03000302c15205010102d80185088441c100480c09030310a0780d0145d0f00c00d00880d2594241021080c0320a001e41c0402e0089510420000040d036071a460b144c0c3d4102d50560300541c031806c641707002940c4007025501c036006500180014004250340544282c021210403604000c403a00d034520121090b03802400d8100102c1c0040117020302a00b41c2c001600324441c42044090301d450b803510015803e5400035401580400e4000c1070b50700c010f00d004c0c49000700814415 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 272218552 1250 272217302 272217317
    0x1060306150b0d0c121415092208040b030703023103061104030c15080702010b0a12020d12200f0d0513050301140603010b040b150a030f090606030c06 66
    0x1042c10348544180c0e1004542250713207040f0020002d0107044002c4820040d80410000091442d54949020004071070101494001d244054458500301d02c0d203a008031107601070000026022000d1543d9084411010f8410000c1800000b0344020541f0065100391030b20f550140e22440c840e02244601500b03000414271403603590100070f086464240f800c03000c4a811407c003082280d2100341146a51003a0340001d001c2075401d190104000108080d094100d200542e207000b21f0740d842c241c089013241c842484c1d417035101c040f0b04c0007004011445610180d11031b000820001040c0204c1e950301003010401c204803404144441008500d100104449403180c0d060207010f0700c0c581d00b244001e2a10340c100c0a001d41c081c44000b10380c9580c01c10821046a0242c000a0000c101584201400b03581d000011200c1500c0380d8244201c501c01402c040c09460b01c060781c05090303c0000c0f0814881e140007904809210020982c0d5003c4c410b091580714081c80351064012640061568210700380b224030000c1e250491420710444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 272219802 1250 272218552 272218559
    0x15022503031d01021f02210f0a05040b01060f0201181202070617220b0109090b06221a15071703090709090602071a0108012304021003090506090106030615 68
    0x2c034406480254680782000440c5074071151100034010310f00400c2c02c8410a007141600750603103511f90360141c1001c0402880c1940d408031640180c0b00c1c2160010310303820300440100191030107100e101d0b1122600e40000704041e0014000007c5c0f043c1041c2040d92001d07008070203801c00940500030503010740694684920813410340740c3c42c0c0403117140280c07041c0c04428280c1810040031540110001505a01c14540051940d603481c494000c0c051000c3c05030740842c890801709109103000c40d00c02c000c2c1d4020440b8160b0b6144c032601920000d20900020442c84490b900c0520700c5583c07103011175034501c1c095161203a00c801140c20150684c0310410942c1c85880001c20904c0741141e0b00007500c03021100004008205000300b4034200340a8014140d00900c142c50380a030103000511080071550607210240c000300189407012200c115135459100b85031300100401c4000c10301506188149011070205401d02142000c2181d49140c40c0007021500c000d26655a0b05050040100038090200300065180e1220f02d180d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 272221052 1250 272219802 272219807
    0x8070b0a050c07200a0807080f011a2227060506030d0c0b060102100c0806030f03160f05030c0a03120f11121f0605040602070b04030c15022503031d01 66
    0x210f40c4a00700e00001203044d403050640e03c1c9031145018050780c4050398206940d448002340d4584000004420035400c081d41981041d1022000c8000d81c1c038014615010000301080340052100b42605ea8031200d80c58103402400c9912030340364000042c14080750b01c00300d6415400d03c80210342001c2c3c8403034441d40049448160040d40000807694030768000703c000c042a01c50200503441c01c07400718015503440e4180509175074605d4000340a00d2040b0300540c1510280d0010b1150240c03a803080441d40e802c1140d40d400c0030400300e000801c244030700501c607004a80ca0f104041c1c9901c0d1a008a8000441c00a0104448419a030005000b02c10b0302040d50042488905494240c40c03456001c2d105c2d01d1400c40c00000d0014201c0412900c501a201c0d030701040108810b42c0301e0f1030007441e41c0d02078010791003d4480d0305c00002e0a407410314200c80440b5004415100e00c242000481d1105118018450046200e007030102d0018050b10310091508040b18011100480d00c2c43c5009020708082906103807843c00c20710646102a40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 272222302 1250 272221052 272221073
    0x507050a12020108130b0103060605130905100c030605040e0105180d020c12190507091a1c020a090c05070c06031e180506100305150405030702060d0908070b0a050c07 73
    0x7a03090910700c07907984c0c0d501e008401503040e51703402130035018085c07000000f405002c0c0d021070280c40c4152843d460f0424510380510969403c207000401541c40f10016001802044d40175100d4a101d42c0f4000c40e10a69500014090703c202c0e0300c140040d6590b0b6800e1040b4800b0748140c06d59841d0115000d051010420360001e511101d85401c3c6034003815030b40f111803a01e5481070051840c90604083c0291400030315080841d0b8800c0340780240307070640781b40c0301360915481c03482c2002400500000b01074100b1381c0b2810202c00e1054032000d001300c3e0030541401001c203130005c42d802400c40001d819594540c0328111400c0600a41d003a550250050600d030800341d440080d04004801c08000300004003190611010310720f642d074190003c20140060090109102c9004140c10300d030002c40e40118121001c0d0101d54110900c081000c0c0da008019910070003a040043c1010b10141c5600300fa840d500140d8420a41caa542880e806144210303a40070110080044440744d0748039850300030312040e80300750800e0381c203543d0201d00c5c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 272223552 1250 272222302 272222339
    0x90b071b0b0c13090203040b1503010905060118110406030b03010605120309041d10141b0a120b060f0a080106090b040e060a091404031d060f0c010f020c0a0507050a 72
    0x20b0000180840c00c0b502258414001007001c1c0104565a20703103400c060402d5181960a0507400000c1e89400341580390500489003520340050180c0000e91900380c008419620b482c0301180d425446d0303141c0d62555042d00300648018201c1c8d807404101aa00d010816084540d15000a441001012070b15a40900c0000c1580d075045410f442c002150200350100703044618010880b00c8003481840805896880b0711382101c101085084515101c81e02c442000307445084203050003500c0c00205100c4084420721528030383c100d040490034001a040f4004000c504039920503480d40c04160400510301c680550b1015105006201d2031400003c96400c0940328040c034843e81c03003030711411262031005c81c40300d81d21030600400402c1803180c2046220424502581140d204032000c0d0045a080803101c4c42c00d0998015000d00c1220050a00340b90203c0b6000403402074100710344010166684000a00229a181c402408800c9038500145600a4a49030891804103590000d6008400b0400200a614003040c03500221 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 272224802 1250 272223552 272223571
    0x50304030f0c05010f020313020109080f0d08100509040c030308240609150301090506090f040314072102100606090b07110607170d0b03010c020606010819090b071b0b 73
    0xe00c0382d02e040c0386015185061031500628800400d0098400c1c2d00c19007484154402c1e00c07440300c42a66081c2c5152198508034426850360003c04480101d2846140700560046074595410200b5484002142030208200e40403608814402402c4c41490307084940030781d00c1071490600d42c04050040344484a958024600140100b802007031204903035442040c80e1481c0602038111a44030360b5602c403c20060310041d5070301d07405a103400e00418900705c00c03a050503110790f03010348802d10f2607901c0c0e080740c045c6644400d5003541c10588000c201206020304808841c4540f22035401002d0070f07010780405004403201c0d6445a01031054144041003c00e0088054902540d00309070390107000c0003c100418400d220302040244400300e504860481c452086014008110741100204401000d03c1c041c5400c8502658100d40542c3c41100060115841240c01991008954030121060100e44074000161440050225450030b202c0b000c104866920820025080003d04d075180104425a26080340d00c80b4081c050313046 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 272226052 1250 272224802 272224817
    0x31403070201060e15041107081204080f030a090605060d0519030e030f1b01030b09060d02010201060801020a0507020405060114180103200c010b06030108070e040204090c0e090706050304030f 84
    0x100d4000c0d8845402840c0940e4211603615041462048101c40180400d1089103480545040b6043c200d0588582c07543c80010380349003444511100c000034500030300440350081c0c10000c0100126641c0040c60045440500200f540d6015242500981d0002001c0f54015020100f00202098001690181d501805d505049281c5440e0030100c0e80c20103d21110380c0c140c880c00d98241007151000480342903070104c10000001441c4001e00440a442c14001c22962040e154000705220380782035000980b60f1441400002001d1359234000e120f0998000160450100364080762000035070810b40180e07a031200d4240303848102c1d6054101e00030100d0103078000c8100301e001030010700d4645034000c6e030000c4d941014542095000280160341d140d05544425003070100d80d407c0c48421f1100c3d0522401340e90584602070082c001540c01c00b8060300850000810907644291118807031408074420102d502c1c01b034070b02940c5854403842c00b03441c07851800400354002802c1050400420010030780c407800102d0900410b21346040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 272227302 1250 272226052 272226061
    0x11710030f08040e01060903031103040e01210507060e0a05040902211207060e0114010302030d030e10061706010e070509100c060608010e010b030f0c0d02010504030b04230a031403 79
    0x242e05005580000e80000748190004c40c8440d00b0070040e008a9201e56140f1200140c814005510390040344039413070080c04401d0044c080800190765040e00200406889032250440e602c03000d2510b8280e5000c600461041c84030140325007002d4038603502400081d2004d210300c828a9001c15443e10072f4104d4400808900c080004400b0030500c000c0c1d005404102c0305030740320f040c82c1c00c10a00401e0b5540584a088d840e190b0710a1103e83c0070344200d4101c07500100504405080210140c024002642000e1054018614021101d196500c246005015124130050b5003000401c4118503048040e04480c214401007401c01486603845000c0710804c48080d0b9a0710700170007207404160307012040180c00800441c18810080b6040070150f1100214001c020000d01010682809240d03d898a01d0510000364120340110f40741c9051444030b80040a10600d00503143c1a9070b42c460303071030080054400320761400c8295540007104d00505154072002e002100544419501c641d00640105c00507803000000d5800440001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 272228552 1250 272227302 272227313
    0x1060519091d06010603051005040c0c02120304080102040909062f0901140c0a020301051302010207150509120604032d03090203010e070608061002031c0b030c100509011710030f 78
    0x2a0940310030b403001c9403165612840013502500c0110b132080005071811000241c1403800e40140da080c102c083e00c501c4a40c6595400b40b1031484100b15105c0d0180c40100700020780c08400340b009000503c2e040c08006080e4100d40360150556007501d05688441280d0071030710300c03d4031090034681c10b02c0303d10b40001a51400385900594078010500e0320040042c10100b00b01c01b03034541c007003100500640300305c0082101d0b513035080000214194000000e40141d102400c2031104001c9040d00550040507410309034240b05084000928062103040300c22350b59000a02807004140c3c0009003160071591094220901802c41c41c07080104008040e400d40030140c0b0384038182c06540307003980042c0314505500d0650710480c2e00c420b0017404551098503818010038452200d410b407103101006a48440206103410441c3c1c01c002d42e19032001e0b1003c200070b20741c0340c014059143c0c030f03659850f200441002e00e02d131902c0d511144d540300050300051074203140682e0215030b1070420250000d803151741401c0d6a030085a20781d00d0229400c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 272229802 1250 272228552 272228591
    0x30c0a0903080d05100b0c03160521221203120f1815050c070f15051915061b080705030a020618010608070b091305070f020106051909 59
    0x20780800d40006409603440000c1c0c04ca28851080a4556034520b03a403208490030034440c60710348181d1900240881102070b4190b01c0c0d1004000d001e6004c90f0555503100a910300d1802403003460000852000030341d481c02c4000140d07200310791450007501000081c50100c140c0703081c003000c1c1f80c02401c101405082d241110065807103500036074116501007010700000c1c1040312040f040380c5000d81d004e58030145002c41410660245034890445a525103060849039030300d55592b11400300c000c4a4810a0b1400c4800a0f20035201d840c3c802c400040074651103024542e049422111710040c07003440000b060380f007802956084460b8400c00b90b15954100c900760028140413005001e0403070018043d000020f5003140180d40028050f00641e049440e0b202d50307120003c1c080c0c2c01c070390140c440d5802e0303900410340c100100c9030094007400c0d643d513014240c90300d95201030b00c1000c1107403000c4a801000c40c408841d01c0000507824441d140c050041502d19204a51080307800d05c20387d007a00d20542d0002a2900c0082c80c400052601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 272231052 1250 272229802 272229809
    0x1e0708011416110f07051318060905120c100605010c0b010308030603030403051027050c0609180702070e1b0f030405010216110414060612060418140d0206010605030c0a09 75
    0xe85549104210029894466034800c02d80304240001c0c0c141f411a01070702c620100581a20034150701c0d500641e0300d4401a210b030071000e0342c1900401c42c15000300801d540040802d518244040d041131070140300050300710b481903089241045104404000007401454005040d243c018a00700d03265a90318001038a54070944d00010900d0040d00e00c3c1e0011040c0356040070301c2c007030b5000e0a601c1e01c0300c0803950040700c09045041c0c00740c110b6001c0f2000e4003580c10400c004081a500140802240e0300b080000424211400d41e01e11006174400e1800704650b824440100d60403640311148204103600c02e0607041c0c40f80c02800b4440d19040000004682045025411254030b002c410f5a14541d58800b410402220156451140d008508000b4410304504c840031105100381402050039080c1500c607402d980040030003d00d10341d0495a5024000c110741c241c0c200d040d03882d034811200c103044c07600390329200c505050110b000700d0b0540d8801c8005000301174004007039036400480c03407150548482c00d030102184c02010303660 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 272232302 1250 272231052 272231087
    0x10051c0219080a050705100f0507020a030b0906040311061905060a05031203150a0605121503071403010b06092b12031a0f060307050903030702031e0708011416 70
    0x40002402c8540450702000c40341c091000c0c1e410f61507442080c800e10310011404038000410340503802c000341c2d004002405140c1c0c00600340c80b00307440d00c9540d08070f032940003580c42c4609548604108020161b10144400403400041c020b4101030030000442d51041d490604450702c150b44550015680c0d407505a0100000c00c0024212040c01da01c82c1040e0034182d0007690a003c50f602c15400c602600e040c041c800000f00c5030165511480d0010003560955581c0c00030340b8118900110101d050100d6408000c2003029020690080b4a0310b0742610405003100c1c201e00e1400d0046a05000c07940c615038404164080010b081c0255851701c204100c1c4691441c42e200a0040c01d17402103c038107100e0581e01d980104c1042040c59203c0b0001c1481d8810483e650002e4881564804c00400026002e10f100381c01503d003008014044a090040e40d60000c0e08003242d02c0c8562042c0802caa141e09440d45d000c00c400c0d0002c1580070b000b00158801c4281a02403500c0c024560010b02680d03164000c0340314410020f030350840d003020303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 272233552 1250 272232302 272232349
    0xa021c030201270c140a03150e1027020a060f020a060e0718201c0207060c2c01050a0e1c0606090612110609061c0510051c02 55
    0x2d001d24200340c10f03000c000f601c1100f000100401c0103100d003190030041d03c0740100304125a070f1560740c40c0040e66000f00c00380c2a00544643d01805c941c0c400b0041f01c815820a04008140001e402c3d5205546042a10b070795480503a0640c884000b6032204180141540c0c0a441d1140b941061840705a1501210b00e100518041c50401941034184011921074142d89204419005880302c5000c00010342e05080010541540251900001d01b00f4440051003251807111801c12080152140c060833a008480c0c26108681c8a03035032001304940c07040407003003102c0c03401c0307045411024000d00d0414003000c407600803410300c2000104e0091940c040d40c28080300790030051018010f4000780726002c01009000030100c800c40d003001400f0400c80720501805040d0350b00495002e00c414410303120444508071034100140c0011081041030410b80b41d060040c9460040c0320800f000e02c52120700b0750b1085442c020b00c2000c507481c07090410f009507950300c40300218040c5e8044e00c2040350071803400002c07040d180c5040140041c0d00003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 272234802 1250 272233552 272233601
    0x30c08041706010509040803060409031e08010e0610120f0f020711040c0f0e060d020c0609030403051005160806180106020c1c020303030103021504090f1b020a021c030201 75
    0x1080c1c030780681d440c010701501d071075907603940500c600d401c4162030007454002c040c00065070070308040d8011036060f80603241181100781c10384140d024008903140032200140d040130051152102100850750041c805441000d241584170b0b5009041c540303e0754000385100d40b520010050015540c000b0044038010f01021555040c0c641790001201d40b4100c0b0f914000c9042420b074100c2c980c011281038240700a10780b500c170702a048400810080c3e500008140886070390034000d0304004c0ea010001c040c4074803001002035a4a82c214248075240481c4100350310f80d01410300040211a2005038002c1009014900700903400f40c403143c000031080d062881d41c00300440260300000400d10703800248080490300071368034203c204061115003011001c40e0400690954410001080141410081c1d103e050b0b0000c05c006013001d85945524040c0e4100d5180b919205850f010029045038100c0351007036400601303000902d480d108540c04540b118000c6101044024550500101418003c0d0090b030605810f4a210a000000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 272236052 1250 272234802 272234819
    0x41b1503050103021008060f0d0219120b0a0e030a081e0403081518070c05031608070209090c01120b0402120a0f0501170c09060d0f0b010326070b04030c0804 69
    0x900f44401d82c400c0014107410035035075004409442c02004d02816075041255040e051103030b20188010102c0e040380710795614940d2041d40060300001b03454408240e004100080c100072a0624018058420b1146414121104a040081140c22429043c100003800756500f0941d80203680c3c021400b05100400e410400081541c0090030324880e450869030209001400002d0140d40d80c41d0080413040c00b600d810200b034001c2c0c000c40544200e680700328102d03032a040850150310a100324010303046803c114040344440031443c011450641c8203514000404083c07020400003440c0349450b00ca441a003a40c1d444501110391101e070125018009480c20740915401c22764054401004903102500c200e074030741400030817020030b0743c4d0018940c213a81000404000c00c005040081c810406040b090380f01500101c440001480b103c1034030480c90007002407407000e62450605500324100c07100500752a20340001d2603128802032500f91002c654204c084c00c40306030b54604d0262001c060302c69020b4408a00881d0024a242 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 272237302 1250 272236052 272236061
    0x609060b0307060c03090506090a08121905090306040b1b0406022b020601090e0106090501060e030f1f152103090e0c0301180609150e0f0c03041b1503 66
    0x400c1941121009550f92500326800c1041a13002030000e0500f02c01040645004c5001e041d842600400f0203203035503038881c041450304060a5a5a0b440c0ba0042070082c0f89218100007102e00070031505120b40f4050f50703200000e03100c040082c40100520511030115207a4450130509408180c8118440b42d5104d45401e4041c0d40c40300c0e205801c80d680c0d2114411461003044020056182901c180c004003c143d0812082802908000d1001107082d1340e10b0100003240100790080500804c0a038031030b4100000084140f50804c1005454130319164003803801221060003842d01d00104250202000400b40072005c540440c1c02030300d510804481d150000300b40380101c282c64482540a20039110300c60031036510440d141030503034103c541250400060004100eaa5010070140c0f084038443c2e400000c005840b44d0300c150031100e1245c400301054416507414404803100085d9990801545400c08035a4507041c032a04419200081008248210002030305c0301c81038032080890702500f800347d04542481c1981e0703401402030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 272238552 1250 272237302 272237321
    0x411060d0f061d0109140711030f0a05280509060901091d0f0a0b0112020906090d0b060310060509070f020703080c0d17130803070903020909011a06030f04060504020a03060906 77
    0x5101c0800024070107115120740042d101401c80c11b12115611140141c801d04e80286a018260000700b10b8204070315065401400300d03042030780300d0301d4560501d0480c1c21814110141c1c02b0310313180b20018840350025044001e075144c0740380c1104c0300d80d44c1d0081500104c80b448141e6200c810788501c9024203114103c5d500d01c1c00380c81002c80b08403124041e5140300103d000d40350608211030203c0d45102e01140c80d18400c2c1c00415030194064034640c07400302e1000206403500300581342a51034160350414013142c0e10b414013500440c092445014044281481c000440491001c0c02c00c00500c030310f035018030227450b001348048002550010801600ea10400c84842c0d100c0038441030040000380c000c00100c001c000c070304010303602910b1114040159986c107a510465203030300242005051007141d410000040c1e844104091142c01640c001280c0054450881c202c040c4105000500c980e80600400c091606503c50840c0d20642221021a107a2a5400400c0801803241c10103850941005140c4c02070150980000c00750 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 272239802 1250 272238552 272238599
    0x709050a050601170105090a06080f0607020706031103010b0d0b0a03060b01120606020a0311030c030711031b0d15091502070c060905010f03050c04080d08070305010501080411060d0f06 81
    0x1590342e14011164510b140d114604180d251100602072410050b80300c83d0b01100806001070180d40340c2c2d913028580080092010855481001002212070341404000d00034a60f90800f440402d00c080d01d1000f0318001405510140840824042c080041036005111551800740890804503100d0418001521900007400c0c0070610040c0702d989901da591040000300d54499000d0600c1c440d007581c044961b48c4404504034202c4c8000e200b00e000d071690034401000c40c40d00c1501d600d030794458203d09240c00d0001c580d800003032240543d0a054031588406884c0345006a000740081d030b001c40541c180800510518001826501c500e24072400b640c0842d5000f044094007402061016a5603038034100e441c600c2c81c2c0542800681440100f004590003600410381103030004569504094131412301e00d2824031104c0005000442080c2481040ca4052103000d01420081c64000f90910b420b8466070794a860076400d2502482c03000070a52001a0950b0040b111061561414480142d0745da09074072000d19410b490810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 272241052 1250 272239802 272239811
    0x30611070c05060f030105040b0307150521090718090503040603020306031606021c09171f0902150a030b0d200d050a110a0b04030606150507050703060f0902030709050a 74
    0x18540f4008081d01e5030503140208075480c40c0e00f05401c3c0400751815440d01134240c85070000104030f02c9881d40c01181040d40e540d4031030391200030b4000844541f080c428416800441c242c0d0501120203008950042520f114213074000b044800400c074100200000d1a0140c4140400b00f004102568160025401100c00b00d04499115a15200641c980106803055901603404400103600071186071301030824413201d0b41070034203405680c1c141d81c2040440c0403940750071075040081c2e403401d200002c18440e2281c000c20301e020070078051030b030740403c0064071403001405d8284004200c00000501c80e03000103101c0c0e0030103007404200702e144e0b10704006421241000000c0c5070050703500710000ca060440c515100b07680c00c4401803840006a0b200d41c910075000030344498000f8103500c00412082c2d460720042008505c9007e000901918101d8108039901d40c2914407810402c040040310045003000a44100341c075004034001802c0e8902c145040000c0c80c29100003509405203d100250b040f0207a4000741c03041012450910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 272242302 1250 272241052 272241059
    0x203060a0501022a15070809031c0504060825020106060e10050414010c120203070b07080402091816030c0302030c060c07270e0f0c04060b04140a030611070c 69
    0xa80320148690341c400660f1180d516280036842c0304021169800005d0034808050003488038a445a034071043c0141c0d0003190000700311001d81003c0102c0c0c05041c0c54201c42c182da8090608004029110307500c00c4e102001b000c48086220103803000c0101030000c08220200c1c00e070011058000e03019085621a40000c41e40340380101e65142407280504884d00801c0d80c401d460300e030a041180402400e2480007070304201044a4450000700240c009d4103880304107400035031711554103140c182244180100900100001041800300607240e40c0c0245070450002480c010107600c800c047e0918081c415440036a5103200110000240311001c0d1010043e2802030b0143c4608556150034841c49200b8805405500d42c481d90702000f14025440d50942d0b0300134000c032100d000701000764007141600c00b0b16658040c1600301c0340313030b1003c005002c200c040021481950180900d500c0c01d20440300501440c811010070002c03070700c80088940d81e200142005980e004200b04008111040035050a40001d0412910381d0705e14503012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 272243552 1250 272242302 272242307
    0x80a17090607020105071a010b040e0105102001140a1401120503041205030906030a06062010090f050a1a07030212190e01110c100605030d180906090203060a0501 71
    0xc95500d40094070032440d040c00d6500449480d8000d1b8402e9804014252452203070198501c001402041c601c4211500c480c00c1030038208911a042c2e00c135501c00e000c0c414944c0c1996030400c48807044000e070780e503031001180d8102d80d00c20302619602103560741c092030340070030044014100da0104000300d80c4641442126070b200e0040c0010240c020320042c0c403e90041c00108110101c0d521600c110903c110152030600c00c6803c0494200d81060b0f03100304000c4d03100c20090103090350244100b00720719901c103141c80d10028100c0665450f06800c5081042450316181c03080d081c403510840540e8007690190403284000700c0b904080e403610030003195012400e003030203001c49e00c00ea100e402907580603040c1e048900f500340c5a2204c5915a03114000c0860341c4075460300040d61650034207201e8410840c40008207030380c1d1455a0076006042035234000c01e040c0074900d02401409541c4001881c0c124525044c14100c03006c0c0e5000c00740303001c0078070680d110405080c180040851740030b480b90040d600800d02075a10024036625030380107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 272244802 1250 272243552 272243557
    0x30203160801030b0a0e16030c090c03020a080f06010e0d06020309120a140d0605060c060a0507140f090402090904050a030923012a05030301180c05180415080a17 71
    0x180c41e00d00c3c0000031845d000c905a20103207002800700101c4020241c10b404c1110010f115510903540075624180c20030090905014959a511107841c04516001414401612040015000b802e0a918540000e461079018109817401d80300300421030703145015546016400381d4001c981280d03d41c000c031201450020902c0c02600d500d0074071030306c5440c0d035100503804040c403c1d0010480010b1b015150b180000e01612400001e00030411128040d040d5481c1c13188200c0c0070748501418a6041048154241005041031002c0c1c5d40030b41c00640c0c1f2140d6516500f000100a401007070441c507400321a10042c0010080c0c0021b00550162090325103007445551188408a0f000700100c46081c5c25105011a062541c81080414a041106500c21103291458008540021112401150103510000051009190028003024120341ca140280300300c00c0040780003402d0f8080c1c081441c210000640071240107a0350354100360800c074140218a6480e60340d5603083c1d541c0d040041d50a940c280c51024480c00d240c4000b804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 272246052 1250 272244802 272244809
    0x61d0601060507261614070602070905090307081c0501080303040309050f0d080a0f020106170a08070309051c0317060a120213050c0301030320060a020c031306030203160801 76
    0x11564100742894036050720003207044041c106034a480102e04c800b6181d586020f80a6500d80c151a841c02110f1868800400d0a12241801c1107034040041009808c0e400114007096500c220340105045d2100c0840030f1030340c0a0001c00030310211001c00c05818101800d40001030a9103011414072250366200101d0707440c0d1109903805000907000341070070301840c28840c0d4942c4020501401501801e025a1246012600200b020100007850035982e141255030900031080540b0b4040b104035200c4001d00b8025540303008424009000e00b60100d2100d0502d40600c00e044000c14010741844801c494148900c110829404c008030042104115030162011014038101d1080704d0240450207034908011a44051a00d03d00049901c200d001c0c0d00c0e98020111401514020904051b03440c2d125419450081e0084901c00440c0800808030030008c500e4020000c1e8060704041412001a41e800322015501d04500c21015228141c5d1aa02d00010b000c96051f40114811440284125040310013981c007100d01a20a20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 272247302 1250 272246052 272246057
    0x30a0c0302161a090303160804140306010e0a0e2401030c060302071112120c011d1b0108040602070506070207030b06030712060c1b0b010617240a0b07061d060106 71
    0xc1e5108070008210f00810030303c10002c2c12203081c0144144144401d1807101022a01c41002007020801041061400740b075080c0e0840c06404158140407080c0701c0028001c00c4a07038803d07161850080051024000c000f00003024564130341c0e8040764085002110760b4203200407175070518140c0d000101544607200f0340701540d0f40445d000041c0404c40e410002c2540c0010a2500790f400307868902e902e10005000100312110202c4008a440c100c1609026107441500d064028150458a03100001c0850741c1c603160341c2c5840c2402c0118542c1ca650500e50020301074000c0c001c0036413250000344214a50002581c0d0110380c0300340c0c0300c07003401d5403000d0516880d01840c3c0700d41d080303110041d15200c0001e030907070304114100d83c2186002091f0010003c0b0007101c10380c101c00306480c81024500103100c1c03070b50f002c02c0c0e94041d0141e102010807036080c84020441d9000028000302802e0644041c00c0c1030345d60740d4030001e41c018640100c04c9034582c242c030300b40000101080c06c4004c454123803041300300c1c120b0030010410740d04840f2030b45c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 272248552 1250 272247302 272247329
    0x50c16081509030d0608010e060105090402010207060c0503040522061505040311040209040c110607050703080105090a1104090213090908120a060e0c09040b01080103120c030e03030a0c030216 84
    0x94004604424003500b5000d481c0414003034190052080e2040c0c00007018042e00102d660082c2250090030a001070700418065680541004003513600041c2c3d460454145240c40701d05c204060400a0660103240c1201307038002a1489000d2948042d01d401d2144980380b01c00030480c10786d540300c660100201003880710000c10340c01c0c0010001300d98540c0c0c1011074400090030140ca801d060100060031980f0070600d050200754012190740304018100302035030380b05896040162400010307850140c20a101482010700c14035901001891044c201d030060842d0600c01074915031107980300c2903044065002115415216064820700040c049464022030005c0d94015010514100200d400002da210000300748900d001c1e16550006444100c46400074403078941e240c0f40310b0b00c400c3c0e80000c01094941ca4411641004404001803002c55a80180900c40c01180d0600c2c0316190b40354501030b5500c2c40344c04483c59150001142140c51150415410700c800c52080d401c0d01d40342440502c103103d91201500a0386805d0078603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 272249802 1250 272248552 272248573
    0x16060f0c170c161703070207140d02130209040e010501050f06120c0307111504020a240302090d061a011103040b0d1d1006080c030106060c02060d0b060406050c1608 72
    0x11000108800194180b4803c18000282c443d180c1c00d20945081000495000007048034082c0e052100001800c2460511051040c603c1c00240f1910410344001c0c0c0304020030500641c0300d1210b43c0c100d8001c803a02030024044c917200000541d000782403d204140c00b800c1000074a044174a000d2088401c0034400c0190301074551218445048140c00080000050010810610f28204002c008001141035a499100303034034a41031041c01900d82082c0d1000080079056402000000140c0082000d520880e02d00140c40381c40c0e0b00000313a0113009400d00900b00c2840c04604580540d103642d41d1201c200700030f0325500140084840d0240d541d2156120b054181c5005001180c9040b00580040c140759815040000d00b048600040364200310608109616a59884030f0422441a0a014401d0904400c40c0200000d903d01b007801f900000300b50100900c144000a88185104850351003a140108060300c21600d40341c4428000c5d00940c0a40e000c3d00c1c0501c21510681311039003070352028805881c480c4000d400c80066 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 272251052 1250 272249802 272249821
    0x102030a022109060c060a0605010c0203060a11040f0801020904150e160216080a150c050702040506131103040302010608060112030c03021510090b030706170c16060f0c17 75
    0x200c2c0e000480310110801441000d603403220b0141082004090203000c860030840034140480380305600090620505d0040e0501503034002c1801d42e40111308207000708036644122310225403032060350440000d506001d800882e5110b03055000d80011103040da004c0021140c2c100241c0307c490384c14803803004040c104030009150701003402142004000c80d80100c2e40314103608100c00300c40d680c00381c02c907440c25809645a0300a000c0044001012000c0d80035040121200900004116219081001c3c0c011a12480401c40c0d07522030201201004c000d4110400681d0b00010745481142d10a030750a030015820924089412400403070502d0407a0422000456440360b00c5d90305480742e805008040e000e50040b94102c03100d2400084145c2d118038084021001e4581c01c0000d41021984409040c5000368020441407200e80d8100c662044128855641010b0381c2e41d408012504034030440240c0341b4070702c000c80484004c000c8a40c002000b5044207800c1405507142c2c01070215020901c1a50506da2001020041003403183c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 272252302 1250 272251052 272251093
    0x608012f04052e03090201121509180b0403090509100e07111006141302090603010506090d06091505090606090705030703090b0f07021203011202040f0605090901060f050102030a02 79
    0x501016000282d200c3c0c09140c0e00e5441c06030603052001c40d0b110b541e00e004642e03101c0303000300340a4401c84003000a8220020415a04c403503d024003080d0740da441002c100d403000003040c1c160001d40d008801030344924051800906501031403040d24050500c0201050701456240d25040c140c5031170502100d440d9480c01d40c00c50750b0608001403000107005808401c0380220460250101401e03188c03603d00702c55421541409020086d8200d40801e1510610035040caaa981500300c0341110000c403100d50710b4a80b410005802903403042d0300105001c1c5000007810410020034508600e1f81444141000300355030300e01003a601d49108441207503000c07007100001002c00340150701a6030400074625001440304070559515010b00d0007660780040c8402c01c0000c0054480d4100800004201800c405504551400a80080819820500910607070700e807125800b0380c1c0c029520000052000909030780e11743c1850020140204010f00900510b84000440820154000021502c98800590007000303c5500030000ca000030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 272253552 1250 272252302 272252329
    0xe030c0d020f032208030a020f24040206071703160318050a0212190f050c030d080a09060213091d06010623090423101508070c05010608012f0405 64
    0x440404d84089050340c0d0410250003c0e03440c0e60002c12038542c54030a01854500303d990f6031610040b83d00100034040442040d516045075050301d00701c0d1984918503100c419445651b00c002500800403040140f02c2d5000c001d22019060300340c40410406003905030394013812000d844e0103001036004158a60060602c1ca60a1404a034001c09550f8044210303041070f6070150b8038a400340c5186071140c80c01030500038203100e084883d81c4100c000b800c0d0441e808502500c1c80e94020050701384981c0d03c01002080c030185404503400010700386403200016444113100001012084000d501e42c101c02092441c1549001400505072007a80d02e408074042d902e0703400c03d1030108102900301071003517041c803800006d91141e028903010001c03070304032149071101c0a03e401200580c0050683d100141c19803020416680304005444040c0500c0c5050140c0b40c0d501c4000f43d0391001c0798600141550301c0c00c070001a48120660002d205261004c82040d101e8547c80041c40f00d055a802d50881d00740343c1040200200d01e0303d030b102d58044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 272254802 1250 272253552 272253607
    0x10b09060313050f010605011b170703020a0203060c0a230d0e03120c031f060806010f2006011409040c061b0b04050109020108061e040c050d0e030c0d020f03 69
    0x60441c1d543c0e615090070306258038a00340303139145c4500307101a44c0c0000000481d0105201ca40811004a4407240d82400ca6500040c510910000e40181454400c0c00710000343c54014085501e107041410356010345511414a60001482d4582d90740b8a40d1030500c91f80342c01250712065981800b401114190080590380d81900442c03008101604280d4014072026100c0c003c60841140c883c80c01e80041e04c003188000f10a43ca144660590501c0095041002d00740c01100a1a0005003501e640d10191020310050080b0b800408141c080303183d0040000030510b0503100305240d000da000300e082040c071102c03081c1030b5030061290511441c00c0c801c5c2c2c3e125444607451000580d0f05071001c0801e688400030580020381d41550703540d450b101c40005650f0003402d2a41c100d9000d4030304d05800c400050180c4070b0541f0040c00d0300e205503140c50f0440749081c0b06da03007510a00b07070b60701004101c1c200b20020519070360341c0f03d41120041c2c1d00a410f42e141c800350001c00c1c0174041c0d4003c00051031900c54696010742001d00c00142c900003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 272256052 1250 272254802 272254831
    0x7090b13031a010501170108060f19090b06120f1f1404050a2108060904020f03030d020702030d1b241b080f01050d291609080303010b090603 62
    0x7007525500c81d0040c0c440b044021200c00d5042c00d00062120010f0500300384455400c1004011180000420715401801104000001c1d02d0302d640d581d060134036420b0ba00d1001e03410030f000d540900c0340080f6007e000d030000310788074420744003e90b011a84544040d44c0c12040b03600b000381e80d85421034011090b21307144101d064000859146103504050802e900303075420b940c55404152400c042142000912080003a0b50907084200095040014030281c001064039000340180c02c0400d085445031641910b403a0002000d8035180c0c281180310a0080d041007109070320a110b08a44090302d0750245142c000c07c1c3d965141c0c003200c00001c60310f0311404e00c2039411140c1c1554004e01c00f0030050003014070402c910ba4a414100051181001400a000000140600d5641c9060800402c00d503901c0000c01d510f420340c00380c034420f50014250380ba0b0110030220020075907420520000c01510a1142e040040704d0b0b00e0a0311020150703030b2030396441c0c0e5a070700003400350a5142034204002c0d551071030060091680041c00390070060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 272257302 1250 272256052 272256059
    0x105150c0109120c0506100506030703200313050705090f16141317011517010204050904121119031409040e01020301060210140619080703080403060509010507090b13 73
    0xa1902c0e208400900084c0642c40c00c004101003402810342059201c07001c0030201d800d02c80011028070024004c04113059039000c00e900c0441340300380302101011a103006d0545034070703020806000c0344011950844850140c40c0000c545071802039140c600440d1103540d45c14a0380e8540c2c2646804207005100300b0305000805540e100c00040c0e010040c40f004081c4201c0903007480c9820340401103004051079554069061140d802c0d284100314001d50215a01043d12400030203030203003075a00911403134201581013440c080c208030501008101110000000d07503075075034115107115031840d114110b01e0450061395a9070100301d00032900c1807540544901200c06098031707010407200042c0c1142d4081c08800460b9401000401c005501404880100d03050441c0a00c14a0311000704446039000c004d0043c4d1007212030f81c400840250564217003d0161420004888442d40c40741083e8129400c0ba100807503815003003070700180c030b4520180100350245600c0c0e00d0b1452514201481c402c404c0c1c20030040003821852014001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 272258552 1250 272257302 272257313
    0x81902120303160f0f080c0d0b090907050a0608010308040b0f0409090302060405060601020c03120a02010e0a0b0f15030d3009050f0715030c02031207050d0f050105150c0109 76
    0x254000c0d61400301c0c030f940c004480c507400740c0f081200503004403d01469007903032048103402003001e581c0809148055951805400d10560081c00e1014115420400423002c104900c0310009011041e9007003201c07800790300d42e5500c5040758940802d0000414001092004010700c8500d44040c1c421410016501418a5111709201c003c070342c04040f055006900041c00c2c0803e100046c400d80d5000582071000d0940303003c500010a0fa546450f1440c0c3d2480080003a103540c0052003075215400f034080501c1650000510380c10306102c4030074107035240002000b294001c200805100d904000d036052001d0080c01501400700c0d829141000c0c643d2504940d083c01a503c807201ca01034689c1c00c0944007100c7c40004442c0c0c2c3d141411481c202d01602144415400400e040c08241840d4016244800c0340e443d0106509841c3d80d012030441c0a00f0140008107202c4005201800da0000041c4c02541d10000d02000485a0003080c601071b9502880344540045ca45698185000c000800401152000d01700105080000d640c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 272259802 1250 272258552 272258557
    0xe030405130b040509010c0f05090307030210020a05010e1f020705100e0307030206131a09210a18050a050d030309080c01060e0c121617012d0819021203 67
    0x400441e5a86458801c9140b416200322034101804400070020441026006040038520880e03ca06001001c190902d06070380400c40303600910750117007503407101c811000406540d440359180c00b140c40754200a0384003440000091104080d1455070004084540d01f000d80340d0080d44018010399040c0a407004107c211821401200b5503584044e004544d01c03609810300070309000303010708800c401400c0c9100070707008100c610f072030800d140c044444010040d0f22601d00741d03031500754112520980700382e1144c403c2d0465040764000e81180c4900307423a00144a030542d80c2c03001e148c00d8940501640180130440c1800f03942021000ba00203d4843d0030009510112a210321049070000a41c100150391a41ea06001c002036042c85150001c0b145090306040080c55403122500150040c03602c01104905020941d442c1d00c2088520711000394515100050352311036040044241054400d007282500504601c02c3d5141d03904816412240b200014181440381004a0f030500c03a5158800d03a844a58010001d0004406100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 272261052 1250 272259802 272259829
    0xc06180c050102010c03061208030c0712020c040608030a080c090a03050a141212070f1e081005060705030d020703030b030706080103061109011706012a020a0e0c07060e030405 77
    0x10400c501900e018002401c0d913860481c400105810400b040100daa985482400019400b00c009502c990716100412017501030340c84043d05d000c6501c517802d00440d4000c54507012001c0199010b024264803612810b660b481400c00502c001050074000070350110401010384400c1c00028854003031b0aa40e40c5400303240400b2a8400d80b540a0516000061000b0400c000000940034910030307414203800401005201e0001400030003400150056500c2451050040c001c2d544040188140700000010008281c940704a034400140d03040041c3c04280c52516109071400b07598460010348c03a2907030307107400500a90040c8000b01d0502d0b0b20781100c25803540d01403000202030044d50b5a00b0744c19614504200050721600c502c40f0122007005c1096100a9902070641178140701c040882e00323220744405004a8621000380390b1500b8008650510128001e00c0090a508050007194503040647c3c8a030034240e0401415295007001850411080b0000f8056801c88451501110152410580c2d0341000c41c001c1c041141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 272262302 1250 272261052 272261063
    0x20409050307081204120f02061501091e1806440307020a0e0907091d0604030f0f050a0822020901170c120c0d03020a0b0a0b040c030b010203090609040b120f070905090606010c0618 79
    0x371007400490308200303269803901011507050002d14600404001c41068403c41d054100b0100390059507121054000c03001405c01d40c2d81189600d5030b812032005e48075080b02104034402d050030030700010201c0010460601441800380a49010303403500c1b801500800c0d4189592070315014071082d0491902c424070605100b10700981312038210f0708131410007d00140b4014000c40511038180405820315074440c0d240391384108620140440d924142c076111100c0c08000c40022340c40340000780003040080e0001e070a03000074007102040714900c0f8028820421460410000f001c04c1d80c1c0a500d41000760702d082d0203800d80250080c010381d9000e2245855503124501c080300d6841403039803100000000d1f0b042500c90b24948240c1880d04202007052180000d40340c1c880e11199502c604408250f007001a40c40e640003d82e9403c0061180140c020400081c603201c040011150001c0e00a00d1400a101c25140c000c00703129030000b0001e4a41582c4000040d910b5503200c14054860968030300101481882c401c180001060160303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 272263552 1250 272262302 272262359
    0x3020a05120a02060c040f031e06151509030b040602031807030f021309150e0c060d050114060a09030204050705120906010f1d0103020409050307081204120f0206150109 74
    0x1454040d1402d003000d005c09a04820030030040041e42d20001070141a01c3d840f01030469505e070b030450841c0203c040030a001d4416481d00280c68203000051300c40c10201d42404200d40e400f40c4912400b0703545d850980c80040c140641302c02c0060001402c81e4000c581c41948100e054640c03009a00314a413400704943c0048a80c6804088c500703083d454004044850300507031000600603000c49903142a4000001803020f514241c03103107460518000180042000c92002508542d140e28905a03000080c01d000c0c0b03d5202042d02c1810070400c80e0810404850307901a1a03210188014515401d000044c10b00502a404100c1e090100030510741c6007002e03290160540100810b21355041610b8004140910740c0700348032a03518088800803402a1141450449404603000030f119901c07424098114461a08000c04c19200011101a01040880040d01480c0179078656502d84540d0042980c08500e0800001c0150384428002000102510f015801021040c5840052240c3e44e503024009403803c031000c483d01042c80c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 272264802 1250 272263552 272263567
    0x4090507031407020c0d080c0307150b0d0f08090d0b010605070b2a130e1317090612040204091e0209090d05040302060703020124060e0f1c03020a0512 66
    0x14002c0701e450803840040d0403190b05041d04040c1d59882000c4545004180400001060000400035505004594002c1d40d9480c0003a250846e03409000c8a075003142c4030b16005042c0c40ea404c0c10389218171425400308040a4203011502c500a4070780201c0c881c55400300004a10400061040c0a000e000b001d2540764580c442c0c440d4684031490050003840111000400d104540d41d80041d242101d00441c600c08a641d41c8050800c11702050700040e40040d003c440c600400d2105c5400c1240d40085130502501078580a0b0700c0440010015203d02142c1640c080030621221051018906616410030310090000130b40d10700303940e9030080c1e19200420300c134418000e034116241541040190a83e01c003520b0005000c1c040c0f12500302a060b030043c0d0001900411011a80c1c10825000b50701c5900c0440c50b1005c0413044800440c820000040039000e10030000342c1c444c01001160400010b00941d0500c000e105c480030901200103850b000903c940103401b180304405049022031020301c0802cac658900a40c103155100e40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 272266052 1250 272264802 272264807
    0x801051003090c2607031212020a0905060901020c1302031b12041e05010e030307030e0d020d1d0d081207080103051009020a0308280f02070306020a0c0804090507 71
    0x3200e500380c5040c10308080350740000800020880003a189160382e50003a140300307107103062a0700c0d4501038140b01d02d104070300010060100b4104074440071400c507031765085840b1506907040147c0c00341c52842800300d440810240300e03501e01040603080011041c0f044540d00400000068280d0141c1d00792000d91503400414001c0b21001c140c09980003006180501e850000307007000b607500c060710003080038001001c3d0415101d00704803005036811390349030044003d0000902070401d040c0c69078000e88002c00403a10700034a07800c0300400170500b0441c21041d80c000c1e00c0b1000362140180c808048444e400b40c41c121440054982556500e032104009070700071a035440e21407440c03501c1008580000390010050001120042000130000110500588403149000c600a074141c40400c101c10b001e034200501d208400300c0d0400d1902c9400120000450340341621200c2030640b48020303100f185021290b1030040c1c0045901313001055054000f0105403610b4a001030000c50651078103500740d00710303400c030b03404542c0c885c4180f219065 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 272267302 1250 272266052 272266069
    0x2202151c0e07080c010c020906060c06010305030a020c0d0b15060c010608060103020a050d0507170a0c060503091e15190c020304090c0219110d0b0702010606080f0103050607050d0219080105 83
    0x50540c0c024135014250400103000183c803e00c0080c0708610900c00144551245019640c110551070101c0b000395843e4501603480b600a194500010310030300c6002c684074500286007021042d003201004205480d0b41c0c00c4c0c074a0a080300601550818020003000c0190842441400c0003070190380054030655065104000004c00542c1c40b01c2d206070360300c24000000c0303000411141d0886507508600c50078555007421082c14202840000340a03030800307003000a2641d0308100110320803602c0e4804c1d204403003000342d40001c4908510b02d8549840d40401002201081c2074100340350031080c0511291010300601144000740c410120340000140c03c08507041140c50018020450010300a0010304001d411031415840800148000900401000d00c40396080761078803d00c80040c00e4012001150620f44003070003038085c02c0c0c03030300c18030000540510000e24100ea000d41e116041c1c980c804050040780d214400103c4d4035030000710b180c03040942c2c20413040307002280d40032001882c80100d4892046941c5060104400340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 272268552 1250 272267302 272267309
    0x90204090506150925110f010f0218040608030405010e03030c0d05120c030c030601120e01050c0c0d02030f0d090c08070f030606090e0715051309020c01052202151c0e07 74
    0x8141d480d0350a08850303003d14880e507606542d450588006c035080701101d0b02d04012850900c009510f03086100b02c1c807002d150014034500f0002d40d00e0b55031009840c414802228a03070310508805030400d1009112542c0706e80300345c4400f0040141100d0a04d4010050740d810041203a9000021600008102251650346241143d02413a0540c041d401e600d00a0f840012601c402031130300d410810064222454101071703a0280c1002548103008010620380203820800e03683c00340c0e0381c0022900c604200003424502c0002212102d0070710b1003255090500c00c44000b000703005880d10071038400105410114860b182000000024200040e106240e031786141085421540c458001c2a201c60509490780402c90000500c003040310030605507003403c00041001190580900b8192400000a030040080c081c0004d401416400d18440000c00990b250b4403c3c0390301500090300703050250003110076514054a441070400c148113403c0c444070340c40c02c0d42c84540d04000030301940c0d00b0458195100aa603448140c1000048045c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 272269802 1250 272268552 272268571
    0x1406090d1e1a010e0f011a031801022d0403170304020312071b0e060603040312060902160b0a022706040b0a0c0c140303120a0e0109080408101802040902040905061509 73
    0xc46d4100b18801d00b648907002100b007a91030740000882c0b4401200d400341c0c1c940e803542c04c00854492000400418500144101c5480b000340040c07015500c80140c04100d504a0b580011140040c0307105094200f42a0030007001a6414010410708600100c0d5403c028496a03128142900800b5050076024038810007541044860028550030400140c403800b0031a034006416082c07040c100100b015900000d00010382100c0142400860001c040d68001440822002c1c404d9202c440c15135111803402040b0b0240c100c202c100f040e4030100450074071150007404c0641705400780919250549904480e59a54000000c040c0020142412300050100130350020001e448140b01d4822000c0d500b0300007075aa0b008a501c529043c00c1c02c800403e4050fa019442100d1500300d601c024403410105080808940d001441448124002c0300c5c01c0066500140c801c1aa488051817141c1d02616460307001d00000700309900003260440d54a44919010860030007000e031040b29a070103440300c9400c0c00703401e000b111200641680c0c071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 272271052 1250 272269802 272269831
    0xc030909020427150b0703080c28050c0a0809040b090105060306040e0715050a11010507020a0b062206080c090903180d0c0b041406090d1e1a010e 64
    0xc0580d10351600701084010030140d80d582031100030100240800c040b200c4d02603418100000d981200600641000f9010361180191561003168200e100d00c6109a8078030a1024212101820580e10304226001d1480d0b10300b1906000710b000d421440c003402014250b030300d100c0101d00b030805440d06014840c030081080e0782c101c6440d45441e012030314500015040ba4441c40d00c51004080b600810403401c0000c0c00b0055202442203e50f036401381882d400640c016002488900300300620707000501626010712001c0d8024581c880c0140c1701c0301510507026007810307445142c5141c0701107211100b0a0082003091044d00c00103509203010086890300e0345400310680034100e507900308185800084169015035030340c44480d40c24940c402d000240e0390720208400814240000102040d801580d40281c820b95034000340004207010504104021401005a100c0d4011040382902000904000c0c071203a81c00c246442180030143d01d50755207460042440a0700300aa400e000040004000d848012600b2036083c10182c1c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 272272302 1250 272271052 272271059
    0x30a02030d140d02030406051503061902071109090f0f010b0a0909060204120809030615031b0a05030d020f01050604180f0201170f040213110d0b04060801020301060c0309090204 78
    0x94580405045007000d200403044080c80030b8a02100700d42032507440110031907072883e16203050030080005541c1e00b5911204031090a03890f041c0090418000c5580c4154902540000007203400070f035002d0941111000340c0361a2072805600c0e1120840c0c095119a006002d130041400000b51400721100346081d00e0342e0500301d07425455192404c154082c2c440105e404078810110b41450000303880303240d02120781900b2204014092000036030103000e0080c811010b5841584505110b0317500d03191a5040e8650503044001780c840e07140e4a010041c8a540c00c0a1700c0c0b0b0046a558100083c00c0154191503440940c0140d07040901402c0300b03100b841d510510854042200e0301c5034400780702e5035065004000701440c580700300c0c28007076a00a0b040d545d00703800143d141115501e890314050910000c01e031000c80c058081c0d4000c01c9459166400381804984003d850242001030a118802c0506400c28066070000c1d80d0304030105603505c00b8001903001e0211078450007c0b00c5142d1500a0020201d0380c4002c61203441444140b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 272273552 1250 272272302 272272309
    0x30a050a0e0d08041214010605010e041824060506072a0e010f05120c1f11030a080f011203080a02180910050102010c08100605031f080a020f030a02 65
    0x1100e12403000e281c070300d004102640128640b40c8404802524005011400040300011082070465407403007036a400041c01c164484940c02d0b21070900825020400c04152000503051503444406440d03480c80c142540d05040340c480c0b000d210300b5945409d8000c007003181c41c041c4550a90295100914055420525241240c0c50f10b0100c40c00c036640c0ba415141202c05410505920f0404483c05000847c0340c184103565190020b0380e4001c500c2c407030580070301c4428441c03c040c0300780482d801440c0c0f00041c1040c1801102860343d401d00e500302a005406220380000b1402d40710701d08002601c0074522136154500c680c142401400d00c0c180050344441440702641c402000002d50060281341c200107010800358842180c00c0e5080940d40c40d540029400800e41d10400c058030210304503c0048803400c0e0004c1064602c4442d04a65440b4201e4030f1228042e0002407c1000f24814802554080d1200d020b80b00e4003803001c049680540768560000c14658020384040d4154178109a000801003401c4005180704416076010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 272274802 1250 272273552 272273557
    0x21608190609080c100b011202070c0b09060c0118030216030f03080601030b0616020103060911041202030c060406080f0f090d0e0307091e1104030308011202060706050106050304060c02030a05 84
    0x28030700c640380c5000c00704100e8464252a40c40707004100fa0b03022400d960480c1c1c002490aa40034500007022180001c402c1280b6100300c40881d50030400241415042000144040c1e000160550b041401045000706000081c858142c81700440c4803020403030036250900074030308940000f60441010050f001080024a6000f95152480d071500b06101c490341d80b280160010031002019035084440001c0d050010460032185402292003600c01b0081c85448050840807101150300356404508104410721400740d01506038841540700030116502c007104ac001007030782a007003648040081103d220600510005001e606948404d5120004c911032805450700b5aa98502243d101c1c00d104640156103e1501c060141401910003a01c0a120700e081c518801c13400034911020201410b490001038084e0b044080084600b201e8044c1e40710320140c1d00f03007a5481450441d280c0200c0e40900204a540c00203a09400b480b8020310054407416204c0c60a4107100d0183c5014086500454104002551129820406 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 272276052 1250 272274802 272274853
    0x702030f0c031f1103070c03080108071203110c06040e0703180b060f0f0405270a0c032d0b15040605152a0c10020102090d0b0606090a06021608 63
    0x1180b48690350001c1c800070003002407a003130030040000170824456040564508090300c00c1c3c1d59115a6a40c90307056940311390301402950f0b03080c8003540807400440d00c0340702145115440394003554181c3c40d0300000a262a07000303030b02c9051044040d00030440900d40502c1042040000802481c0041c0c2c090303582d00d60000d8006090078403c10040500ca0b04680f41e142c500c2e111894068002c02c02e80c1000d070b1413121200c0c1c28172034041041050030142078848102103080803410381d0150b03d150f00340d41541e59016041202c401902d0741d03000d03070082d82e52803100e2485034100b07094010500c4409505214000c100c0c928404801c0a004900300136040007503880d5400180c50b4900381c14a26512050050700246a00329840d1440c0301c5442e042c885800400c0004c250f403442100d00715118814013403070303600a9007030f0f014107407d8952004840e17a0001c0810171244915030b00c070f030008002a15001c1d00304006542d401c0ba9400850041c0d2102e681d0303808003000d0a00980250580030010801c0c41115030075144100190b01c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 272277302 1250 272276052 272276083
    0x603130501140f01140a0803120910060b03070f210506060c240610080112082809121e0c05030a110102071703090d0213020a050702030f0c03 62
    0x280512900703500c41903040d81c4002c4801d14038200003c52040444003801103081400c01a030500f40c03075240044480048502004c091820700c0c43e803c140c4505428010f240060b24016a0074142d54841544140310141200380c113032903103d04000301c3c0280740031400d000c841e00b841030070008400c00d10980d402e6103030800101c0b54040307803d50782c10000c14440c1c01118018007075846120181241c040c0072209400c007044455615501950721071040080355000c8004041c041008030300180000c00d02380071414a41170042c24107030318040d101341d607222042a40141520340c142c2e10f8650041c21a82c00421000184502d14210b0701a01c03482d22034000144a40d10019411441d04003807600300040c44202c4401020300a00365060500181032025a05407044070b101c0c010300903080045266003c4c40c403c54009500c050044d401d001d54603040c00500544803d00740e034420914101d1828202c080d0004050202c000d50300c050b1a00f48520600d071800d40d04080380c0070302d40c0104e8200800c1d92000503085207503a9000c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 272278552 1250 272277302 272277331
    0x403021f06050d0b07031d0703140105060d110f0a06030506150408070608150402030702030315061306050a030f02042d060807050f0d0603080703081003080301061d03062d060603 78
    0x245c00754020642802d0204900740140c407500600b80003c500171080b24014080440c2c1c3e0740130909458200d4108585040d4000440105039020904203802c11008190180c02513440694103c001010000545e025000080c0c640c410132440d03040041c4004001407602e54124209030500c901c5030303211079280c0036000030895079800181860580e2081d0685008010b0401c550764102140029143d0340101c0d41203400c0e000b0386000c051a4181041291407400a0030b80403240681840004c4980d50701443d260010141c848007440e51011451004100418110303450f50711411184642d00d80500404410a10b4081c1901d402c1180503001b098244e40526685840c1c1d0355405182d0360b0032441d0240b00500e80c0c0e078910b0a0000700c10803406400500c28203004c2c1d100d0707040c00d940d0014602c00c1010f0a000041070401b084c801005290300604070b4800a0412032800282c0c01030503000710b0b01d4044211103d0211542e41c80501c20110541d01044030083c401c54100c3c422441c000e0041522844054920305010314003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 272279802 1250 272278552 272278561
    0x90c212413020c03030403090609030b06040203090f0601171501030b060f13060906060801090203040c1a0d1506230a0c06020c1f0c05120c0d06030503030403021f06050d0b 75
    0x31010322280401c5403500c110344510300304480c0da50fa50002c4030228013041d020440030405900a01c0c2e613104590f400b10011405554600a03c4082d401c080c001d160307a8070440c81c06120a01c42440558041c0c40e0505000141010001210389002c815500404401c48160014004250710310861035102c0b2080e1100c0c90350070850f0001c40c442d000025090f10341c1918040b004504005240c001c142140c5450741c4104c0542d8031145000300320310050700c008004032074034541002084080101d051495a94130740550070f0055903e05d04050b95030001c07400e078048483c05400e000c0190004d50300d80240203da41e81c240341007042e0440d41c55070301c40c00090f481805a1880650100003450f01110b42058805060710881041203811890200350300e011402200c0c03c00c25a0082c4a1181082d00c092450b0300c07600c030b035550722040c8c0820b030039a00c03070300180b03151940703031003011021580420095010703520035801004070214520800d62000c80400710f4003071090811100704010ba50301c0103000c3e081070b04054003d0341e03520b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 272281052 1250 272279802 272279809
    0x1701120f0f12020d14030609190f0e120903060408030910020d0b031b0a09150305070308030a0f0c0507120908070b0d14040c12030c02090c2124 63
    0xc44050041115200e8405002000040c4140c181003120a408545403000307410b1054607607010030440350302207880920000d240c0703180c905031050300098208084501d01032544280300950b10108205038015072500c0c2083e126001c00c00c1000d41031020130410301d04062103000002c3d100c11001d4070240c40004048081124141c00740400c0c00d0300c43d07a40300c1c110340c1c0b14080c01500001d09907000c0600d201c0e02038000d44032140d0f40f10302651f41d2075640c02080c4462817402c1c419000000c240706c2d12a0600c100d040c40e00840068810005200070b54003450301c10ba140e00d04856401c2c1962a80c2c802442c40c14113000c40010b01a4105050300c1100303500103e03110007425040d0301100c0e10045640000307410300c44e5950000300e0080580c000c05442106640600400c01c290702c1b0020f1961090f00c000780364245510007080007843c06003e44401c140b0a00e4440900380e2542c00161031494156580a200c2c6030005042107280303000b03105180740c02409115a00c0070b151080240020150046001e010b07002d009109104655 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 272282302 1250 272281052 272281073
    0x503030a08091603030903030809060919050a08160b16020c040b01120c0e010f030e0309040b0310020f030f07230a17090604030212032809021e03070501170112 70
    0x1482100303010941556400d00a05400751b41c401500447c2c0c800010480c070b058003144036441004000010031620100c00d140c3c44070000c44120640d110302814044500240070781008000030b46000c2c420005104082c00d100c003018130041d1150100101102c0e4090b0000d402082c420b0003a2070844000a02240d10401603c49070001c8040f580c5d454505640010b009030008114215580d00380e0712a0b540041c005016000c4418940d001c041a9005112080d0103141c036411241c0e200b1006400d5410700c4014910b01070580c3c110900b0103040100100400501c10b4804030990b600203000e2520240500c90140c011811046032a000c00040307400240d19044a80564072040312100074801c0031b201707403a2a494041e01d58078140d4084005010f01c0e01c0c0103a07500701003800d50b40645200e03d0308054545140038040103445420361032514083d10350003040b026940d05c1110116556a544204581d0f80c4650205400c08404e504081d042c800401c0740008024050b46079141502da54a001004140b6142029607a50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 272283552 1250 272282302 272282323
    0x402010903051f0c03060e040f0615060f021219141e0d0f0504030f1d0406030f030e09011802070c080607231c0f0b04020a0c0510060503030a0809 64
    0x140f203110048500070501c64100d0042080d403242c01c02848905100480c03c0d161188101c2100b505031f5000304010070040703076054010314403910f4009640c05415a80c54400409503108401085900021504094041c0f0041051000089000b03262201c090841c0c131075032089002074802c008041907040e040440c44d41c100c480724480c1016281d0100c0a4100c0560305a0100b10581080b5041c50750703031041c0c0206400b809000e103a05864502d4209102d42c02120f851081e40000c591008032903000e220341e41c448d882014061401800359940e82c0c403050601600000100c0310303150081016000411000c01210b101d6841e105441c1c07000340e65403e090030305080f90007140d003000d40349004010a2103103050b0420f4580c41d111490364040ca84110194200d0f0344070b4095106499061440c0c04120341020203998031a070b10040055030002021100b0f01d0209013241c11400c0740d0300c080f607032000c009018040100080f040c0b1030545101031090714207180100f03450740200e410480a005822001c182d500e2010310840010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 272284802 1250 272283552 272283563
    0xa02090301110d0f0f05011406030709050a060f08090d0212090f06030705070507140f010521010801150503010510050415030f0f021005091f050705060405070603060803180105030402010903 83
    0xd074088000c0d000d00030700c100b80a82980c1c501d40b00c0200174184181c042d05040f0391100c5c6000c2d4100f070400c81800310703c1c0d01c01069101002040d1801160940d9840b148034003920380765540d43c10490340408003615241d406810344d44560b001540d035080c200e50005203100c2c0804450b003c162038580d408040340581c410204140d610403004401c0011060f4000040d2807001d0245040307803056070740c817480d200b2155125140d50b070b04a00f0314100322a1950044004142080303071404c8140b5100a180c80e084420113007a0040342c40ca0b5102c1c2004200b4090400b00400500011402084541085060002241c01521805008544a40352905c41000d032a9002000710781020000c80c0c4550340d8900303c42d044902480882c46106000122240d40d4072030070030380703140d403e029041140701c15003010b10314000c044a00a4904104013000010002003007444600d0180c0e116a00402450f820070b5000b0b000d039045904051070075442409400584180f41a2024682c039081c2421079590305c90f070004a03030000d000e8002619 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 272286052 1250 272284802 272284807
    0x20f06040b0d020c01060f1818050105090109060c02072402010b12160b16020d080405040f020702040c1b080904060504021215061303061e0504050d08010506040e0a0209030111 77
    0x40b00c0390350b5001083c0d0700c4c1a08000300300e1103865a0340301140750914002c030124240400d0340d03904640031560241030383d5810005409440e6403039585460075500100d41d901c107140d44483c0d001f020808240906440c0b650107002070620309003448400c1894558860440c2c01468080054114481c000e5026051005001d442030b41e00014494400f580c1c2d0018240c4d8901c403031a0f41d0400142545854180c48000f065035100018040c00d923020031600001e08942a91202420480003960b03640e00e04c20407101c1440b0540150325280c09004020441c0e140c83e10b540144000e03154030010095450600840441d841412151200045004203004160a0b00300e035030803d10014044000301d00c450002071043c0c005000c82500c09000006000460103040010080d6031400d01e0305000084240d0454591840d0311030084c9110b078407611042d02900c1c41554155190340001182841440c0c3c001c00d064050001950100c0c41c1034a081041140c55000401000d2041d41c0811103041caa9020f410003e54000c20280701034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 272287302 1250 272286052 272286067
    0x60d02030a0e0a0302070e0702060c0405010e1f030e070e010308031306110d06170109020105040504020717030f060112050f150607020a0902030612010912030207330e030c060103020f06040b 83
    0x946d40c04050041000540305d1070f0001300040d10000310b85100d0b540718040e55003018a003000640740c0c3c075800e604840d071040380110107615603140341c18060704004190b940440c0b101a40340d595070600000e504030b21000d68143c401800880e04000440360009401e0b454003c1c04c2c600c605040d0028041003507807140c1c3c02c000244508600d44950010020f840c107082c66a000320038080c1c202800c07601203840080c041001440b08110b6882d10390301a00d07541d03015850a04800d08c0d074040303150725030303000b100c0ca0b4448140010920480303580c00001906003180501c404c0001c0e0400c400d982c8110310005107180302141c04a0190440307070f11110f081d11002d91b8043c04840d0040c1c4c646203441c3c0650421250640200c072622075180349114140901c50000360805080750900140d1b00302100651720840042c1c40c031156982d004c291001009005044005c0026610a50031314850200381c1030310000c041601c040e500500c00486504000700e02103045940c1205c24004000c0c0f0b0001254550081d940300a81080c404519031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 272288552 1250 272287302 272287307
    0x603060506090105180a1d030c0d08060315060f130c030c030c0e090103080d0b0a14010201061703030f0603011806060311040603240b04090807020f040b060d02030a0e0a03 75
    0x441c020a400c4840c4102c0d40e80f204117105c405800103002200102e0110081413120400d5406202100c2551740002d8134120300300c100700d14661005464410540c0290b403000e420a91000e000c0790003990490181001e5489840e04099030031000e0019881005411100c01d0250f0314042d07003806d46003503814184039500c00f492010300209116101c10000c641410340c08a41c07140720390100b01a0420040c80141941d0130368490404d250052404554529580c45000e60242d07504c3c405a0010022481c0c040c07945104074000a0950750345600c40000c01e0500c1000c00d0201002000343e96000c04074070308070070b1640d440c240040c1c0940308061124481845564000007485919000340d01664000c441e48d51a141261050108403002444040c0c00032800b00d6011a810301100c50505181800000114062488400003170850b174001c401101c0c0d068002410400314103044040100c40301007201d04110045a442c041445c6110b14468211002d41c000000340a03150b0f9540010380390204042241d11440032451302 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 272289802 1250 272288552 272288561
    0x3030213181a03010c0c0f02240408010b010203040506040e100f080a111002060412090506030a0b10030b0303250501091a100f030b071e051e040e01030209040510060306 74
    0x3400380c269818442c4186003030501400100400603656044d042070b0a8a40344e40d80807002004907401840c0c82800d18038034804004c1c1e081260390b01142e5607510b9103414481d2b42103a0601200710705541062008200c156500c0c03090301d080301e030200103103030f1aa940d51a610000300c0c03540d048000480c001840c00315500d00c0c0001c4902c5003900c40d40c500840568020204820420f28a11180c016400030b40043d001407080b00c01801d04480034101289500c0e02d03a400078005410441e004d03607205540301a4000b442c640101d4140070030300d450408001d202d01401c0403a8580c0b103020790b0b403500c000c880302103c4d21a42000340801485508400200403d5059180242808801da074180d85001c5801d1b010803060208400001d04035020302c5607d80440b4655034421382c0303c00e002010b1906202c0032004218400780301c10321980101c0f2042e0398031030703490307840c096104c0b01c111a4841d43e0300c0620080c4010300c440d52001440c107045d250100d0b0341c80c4076946d0724034010b0715203d411100c1c3e80320603040440c000100000c1d50003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 272291052 1250 272289802 272289821
    0xb040b040501021306031e020708030103020d02031e0132070f0c020d1401050106090e1605070204020d060503160e0a09050c150406080c0304030f111908030a06090c05070303021318 79
    0x4580c1c0300c0b11100b41d000703070503400344c400017800d42b09080004000520f011416201b044d4405805d4480060ba0801c0d1088200d0911140b05216510b070326406803103865083c01403075005000201d001072030400c0d0205140d030140c0180030001380b090b046030302d10030a4026151540b545900030140b011480640c0380c0030300002c5600b04488565800c200c000716009024246079020395030f81e0525400306580740001318040010440c00c02003480810807600000d616580001c00c2c22064062000c16014644010b04d40b0f4541c0c40100740c0ca084494500603c000c22001d44040d40101a0240c0451041a14289141000780e91a03000c0d52151651120030b000c0401200540f044850b0382d140c204007075903503421458142c4401c40c0d0013070001760860704080b08140140b040d100359100400032074683d141014002980000803900680f040a408400c0044401545c000d50700542107403241485944088540907126000710b0340002c0c01e15030045903143c1c08880c08601c210080440b649100c04044050a40c040109051788 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 272292302 1250 272291052 272291081
    0x4030602040906080c0319230105100801020a05070b04080904060e09060919020402033c06030309090601050706150b0901030b0d02090a1104030b070203130f030b040b04050102130603 80
    0xb40d002521310b00224400c00821740c0a00504105d8a03001084009000300704012660302e140c2c2034084203800480340e41014011400000001e072828600682031402c1042c1e40031080980c010880210806c4d40041582d5a040e44800560055100c518141c15a4000e00c410207402c5407804400089402d01005014028680342e4142c44198031003034a402d07102c1045020810038110001980401410507034002c55002c5e0700c100e0080324a04410802d242130781942103410142c116102c00d00351070000010780b03045d04000214015441c000404011038001e04000f4030160501c40003140610070702030741e60002112003c90029168602d901d0306a1b0001541080142c5030010f8503210f2150204c4c10310000740e410068004040e102d10f591111050300c00340045040d0390100510070f12002000601000400303009542d2170b00519220768010905505040d107507404082076040e150030030000b159100c882d86030400c1e00640d2000c2c20741d842c1e050981c0039215140019100c3d05040f040040c42d40c0e0f01d03511031450079a940 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 272293552 1250 272292302 272292311
    0xb030907030c0807051f18080f0c0402090307030f0311010903020a1505040c090e011104262803051b070602060106020f1c02120a0c050d030c050d20040306020409 71
    0x30314030360350380c2c031050301801c0c0d002a03021b601c0d413001300756100420b003000c42103241400103072005096400b0180030aa210021503071154480440d210024004c0034100001602d00f14188400040041c0e034400303c602c80a031500511070101001e02d44203841d41102018000003d0203c20401c4c64000e6464550346010380d030048980d0314001c0c40b440b46015850146400c10a042c40342d40c1880c40c41c0300104034100d036000866503281103a910407e030a0011700024a00b4402e09400401c01191920b414442401c00d4111a00315010480907503400780314081c082184040c8090012802d840c05444a102c1c03808101010b882c00b000a103142e0741c0000d8501c0540c0c2c127640c00c0c1c590b1640d992806030381c0c80100c07500d041000d400842524010010004a1b90001c015901c11920320580382c8241004640c00182400006007002e5944014031008016071601081c0a00d010001c6450080340141140146502c4160241d1660300d400c4074003101d041c2030603551041500895a840d40c07454004004d42c014480da092041c00c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 272294802 1250 272293552 272293559
    0x3110301030f0209070c050c15091003150911030c0d14010b03071e1b020a0e07050307020118032705040501121a090706180806131a060f190b030907030c 67
    0xd40c008886c2554000000c0205010010800000c0c0c260241d1200044c00c00b4800000741d65035503200190000b555440000f844000e148009a120070290800030126080c00002900da12001c01241c0c0d2101000c800d541d1181062071661000d400703004c50627030400808000100f07100c191000158080c40c05911540e0074600e210400040900c4c134942d100001c0703102c02c1000003030120355260481c5100e04c001d101c2e5841035115060954028070585100e00000d03808010812929024464210542420707500b2407046040d5540081907454141c10007a016000b0548040070b9981d1040360002416000348240308640e11106000480c064284065640300034280d1240303c0141c0c514103e44c00f505640000d0140181414020380703c4011b55162084c00d01031800c000101c5020610001d0300401250340a10410b025509003a001e20a50b000c409075803054502c00d0111641e40c3c041c0394024003c0580724403c103042c48040f81e01d14002d03e035000e441905000800c00c00601c074042950030980348034103004128140c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 272296052 1250 272294802 272294807
    0x2030c120c3a1205070e1206040c170316200a0320010c1212051f0501030b22050f09060714030a110d06060206180312060103110301030f020907 63
    0x1260102081261001040410301d00c000b0640b14110700a035041c0301d01c10141105a00c0c2c11200100c4203280051101c600020f200d00c0c0100f4068244000034000741075604254681d00d00710450351250a01281c065200b20708103103801d200f07840c200040e42594200040d46424810500b90664802528280140c50b9426140c9031039080001580d801c01001c4800d80050102540e82da0700340c21016060000c0310320300354002044401050030400003a50707924041c0043c0d070420403d4410290061032400d40340e2000b000a180d502500ca02114407d1a010600b648460049a480000404102840c003003025a90504121a410840c000c11a452040c000d43d0349280d03100c5e4a410b000d644900000d04103e09031440300d415000a980c02108080d00020380f8482d804039101d90707034020405990030740c0e10741c0d00800a258043c081ca5501118400000c0220f89611356956141e1184940f00d0400f0030204c000301d041079101c0d6104e14035000707140303ca0507543c0d41c413410091581707100414100e10030203280c030000e0002031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 272297302 1250 272296052 272296093
    0x70f140c030d020901030b060c07140906090402010c020a2d060207030f061119020c03010e0609070b1c020f0c0d0212030406020a020a1e0201140f1902030c120c 70
    0x30400c03000e141007840402c9078038042c1d4000c2c5021410180c451000888550350f80f001401c0000d01003005003403103460700c4102c1c2c01d48250003124500c11043d4108001d49074403404c400315446942407070541080c400e40c1c400515606070702d40100f00b1240c8049440540d1958259208920100908803105803e907900c0040b0303030700e103010f0000400740380a007005080011040e41000308580005079007035081c54501c00391900c01d01c03d0784c5010001603005080100c8241005e1044a07401410b0b84050300441c542158061b80d030f4040e502c1610381c10034000520300c0100302c0280d080d030200c60103840f065540e91410703e143d90940d00030003842e01041c01000040c4544900005200140392424034840e4103507a159200c3c10029000f03064508103501560000300c0c0000d4810300b0100701081c10b60341c140b6070154107000060044004603c844d218070401c00c0080c00030441e05069400c410030104041c0c01c1919140070032402d40c044c0103c10801381c4030300c0c1000202c01d154040505a131540c45000c03110010b46103210a980e41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 272298552 1250 272297302 272297317
    0x10c080907031101050c10020f030403110a1e0f0f0803090d0305161101020705060a050a0f0605030309122b0806010503040f060209010309140106030606120305031f0302030303070f14 80
    0x480151400f0215401030000d4080c1c40c9024041d17500e49052403c03424141d9109000034a81c0140c004200420913070040c0100b1000b10080005140e4021a541c865803090a541f40842e07100000300088070410141504a00c2c14a910802c1e400412200d40740c25100750f0803c0c0c0c3d0005042c09078201e00c58500d842441094071030000001003103103034020000242c60700015255014265502005820046141080301074040c1c0414440012685024005401110f002810300440325003002d208000603617001040d600e001d10119403140c0403900749100903141944641112440f0b05401203d00d80600d40c403041c904d106c0125495108080d03840000450340c80c80111001850304821000800c045111a4040e00e0940c03018140002c880c100c1c0c3d1600500034800c080d90078151f079141c1400780100059402910014000303105445154020356034003801e0350100601c900c450070010362a01d8407240c01075412400560f0042d054940c4c90400445c0280540e02107907162011801a0141c004605501822911074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 272299802 1250 272298552 272298563
    0x1a100302010806010c06180302160b0912010b0901090e06130f030309110604030c0f090203011a030c0403021e01030e06010602030d050c09100915030902060304260408010c08090703 79
    0x542940d00541d542d14000d000d007030421046030400000580e0741d1003010302100031000e091268280516000740740c60440034407252003921910041080042000030340e0b0240310111282d0382c1c0c4000e0204858014080510415406000c010001904c0045a8403081c40f0780d01c0c040036130b4000d03694800741c05d4900e21200c20041460710030f0724449010078840c2e40f2a140151258221102c00301c90200081c009401a40003511584105c0c4030800122071018942002060407450a50441d0301d03040e40340018409020040600080010014130200e8103002118095540244161219500c0d050351001c52082103800501191030182010b0001000203000d40c100d800e258011450700d070100150b01301800c805840c20888110074000180243c1d240440140d05d0145680c0d10342c3c15a2034943c541c060b080845000206040c034240341c24003d6100c2c041125817140e0841c401c41c0d04041c14107034000d40c4040e03090203074264220204000c074031500c041d0000a004407441d500c10442c0d88601d642c00c0c0c1c4502042c03000501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 272301052 1250 272299802 272299831
    0x605030a020c160803120a060e040f0f0204060b09100e030d0c020f1005070b0f0412030c1209052d0601060e0109081209011202090904110a080f0601031a 67
    0x428029001420b2080c64102a0346854512607050b0003262540e0300080043d800100e010079060940c011801d60002108405120451418180080d1443d0107000940b4103500c010345082071000b401c2c030340c190041d8003a1040055594035410f011440d00201c440520450b030b60b00c18918003603c41d907410000104010094400108a607000b511110b1034100d00b01d8014447c0114092956220200040d080d582c0c0e0706e5240d41c2c0c00c041e00e40705a0303c140c0140080320080b10017051002003050105446003691250400040341e0380007a03402c0c1c50811400e0848140d080c1804440d034200240461642501100346a45040c50f0210034004842c1c48000301071440d003544460010800c0a1090082d002180810306288500c40d45503000c1c42d0030011110300352000740d10000b0f4210f5055902001c2c0740030f0302c7c1030680110f003445001070006484080141002e8200040104d060348603641c1c400840b07004000240c100c984180020f080381d522550300b4441035450f0011002d07811009070085c0ca510b88110100c69150300c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 272302158 1106 272301052 272301061
    0x151809120c080702060d18030e09090c0112020f0903030a03061e0617250201050108120f04031415091b061e07140303040c06090906060503 61
    0x2040004040040020800c004240c0f0000fa40c12501e16a0740e12041c00c101021b404801a500b00041c441c07a81401007540003600c071311810006940d501c22950799012001e44401c030a12005020401c5694070102d070801c15401002c42444c0031542a0601140f503000c00c0c91a0440b130100c07404a81e854005210074899402070708221000d51449c115041d0500400815040b11468220080c14544021960b10340c0c0d22400b15150582000750f003003c11440e5003009020300020311a0003a680181c2041502d184075030012070700c1300381080110b145040c0c61a40d50b103005804c00300d008462402240d143c0c9010344e0a4440c00c1d401817600c08000d02e0448580139640f8940107059000e2032103554104030b1b1030041e500464507241110036210b012912000607003403051b4520f000150b0802540000001c00c03003082900b60000040e500580e54a10078262202c04d618100c0d9481d00903900070039010f10018 = true := by decide +kernel

theorem cover : BRFrame.Cov 272122302 272302158 := by
  have h0 := BRFrame.cov_init 272122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 272122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 272122302 ≤ n) (h2 : n < 272302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
