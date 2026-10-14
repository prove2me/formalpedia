-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0758
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:37:14.635987+00:00
-- url     : https://prove2.me/submissions/90218a2b-77a3-47a7-a54d-3e328647852c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 136151079 ≤ n < 136330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 136152329 1250 136151079 136151087
    0x3250807180306060902090307090b010c020405040204090206040303090303120b10050309070b0c070306110f1b01060509010e040201180501081f05040e0706020d022406010c06051f0522020a 83
    0x2644010703c003505085000c16008035603005001c040d04c1c240d04803281591187c3d4113a05a4461096150006111042280161829401154105002074000a031004c80c58003c541198060340040d0041024200b00b00101540701e50210004500c1c000100251101140020350462220007110f041090100104a00e09024041c000052006c65401a0b5a9660381922a1070307402d5440103a80c503030300d41500200b8050307041d02283d21101a4001d010320382410001c241e20400f4901541000360340d43c4a00120309c94a03010400780c00b03482c401070074200a1a0503c0010007640c80c03040044003182000e4000c11060b43c00c1100d46401445403c3c1441c0b01ca0600ca0700da00c0314801030762040754070509010b465007446402040078416035410707074243c45005c1a14007050345c0d641065504190f04031001c42d800340310b076071141d60300c1500314005140c000d03001e4030662070b24801da9000f5039404101200084400304040409001e01c03009050a0710201d0031485155241c4002e420219283d0b00c000d50000f5040405500c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 136153579 1250 136152329 136152377
    0x1605060415180608070207050a0f0603020a090f060e150703140d090c0e01150908030405060d02120f0f01081b0f041508010e0607031b030b030c0607050303250807 71
    0x21180c0805500d5407440001e1405100b17031410710142c0103c02010030a414004c40440030788203200d2004051a18050003100250f210036036903401c019410601140110b80d0000c154010304103130760b445108070000400c000034150b84075007003081a6020041040043d8201410200d10800040002d440d900703501203850291284110091226680100101d414850000e026040e10a00c0700c5580c064000440d055680701d8850140303641c2035005200411061902600400076004860400f4ac01c04082c5125030301d813844103640f040c45c422050010444018640e000050041444034020020f2045205a4518802962004a00445804c040c1780c0711911584c2082070305054582014144580e240d81c694005c06208050b100300e030043c3e20101e48000d11031700480c0540f80c0b410110b0030008110020603801000d185082c940c050203128502c4855584a2001e0202c160140000d1941e0f454103003100280c1c0c603065130101c561a41c40e40001070070281e00200c0c00e80d1000031801c2c129410010200c00a00d40300c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 136154829 1250 136153579 136153607
    0x50d11041e060e060324041704060203090f01051303060504050703020d0b16170601030914120d06050d110907030e01020a030b0906030a02090a020a1b0b0403021605060415 75
    0x314a141d0300c0d104650303a001c2c40440300c0d1000600c007562151000c05803207000ca004080030042c0041500303458074140350f024540062082940c0f14400103040500e0f005504560312120258202107861609030904044604207040c003407074540e2901c40208007030300b5a0842e900028089030364800000302007003000c100d800081c5170001c0c90450401c03803c1c540342500d1141201c015903a103620740b401c00f258500510046003140420381109580b030340c03003000450091031000c0045d1504061084840d131104801d00c0074542e00d030611031706a556460940c0540381521490741c01240504007417482e4602164086103400300000e0111006e80041c1c480800032805460040210003055100080c400290f40d0182e1143d01c074000240c844400c00c5d55620304040e164103107400c000e9001030310540010f0700d0082d20340c001d000400d81e130300700341044844d1910024803091403201c00300c8415001e14103000a0640410165440e00e80707aa0710150f08500301400720307a541c0204d11454107102807802e40e540c901070040901c070300b14030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 136156079 1250 136154829 136154861
    0x30a20071511030301060c0f050114090f010c0504080a02060a1701090207020f0306090607080a061e0602070e01081b150c0c0a06110a14070b0309010e1006050d1104 72
    0x5516400d01014041601c9180004542c1d0b03410246038411011013528100d800980b81d808884034642c0320b80d280c884154104540035541da004840b804040c40300001c0c02800450000c09102140300c7d1094212150f4000c0c01e004e10105210030000000b0004007005c0072541902d0a6403540c00703030042500c8415040c01c07403108002402c0c00110389060340e6805082031178001c4a00034a509103681c18182c440c0300175624000b19802c24000036802a00480070310741c10041c04c0000044040d50b4518071200d028040444010720801c01400700801c90307040005c00042c00c0b2551600026509d007a4907545d8034200124100703d00e100d21480e05601d03554064100c1c0744400c4086d102e5071307030741c102070b8546072500000c0380b03c3e620030311191310007142035407284490310702040883c4c004042c001029101c1030b47c0c09591b484d61400c50b104800f03010654440c2840035602404550001142d28941c60640a04100c088030070160841c3c0380210400c03c0355031318041c482c0156080714405d8845005c440c0400c004c2c061043c2060804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 136157329 1250 136156079 136156093
    0x30c060c0705071a0a0c1403040801020705150f010e040305090a080c10021605220905030703030506010e060301091d03040f0609050a05030303010e09250302030c09040302030a20 78
    0x8030482400920a03030b4480c1060b100050348426103142c2c1000b00c40381c1d000042d00b0a0103c03070b003c6400380d541040300500604181d00071422142d001da1a56016402616160350042465000c02204022265400030b404000000b035141101e10140c00c90814418000102c402e81c010a0505000b401221640e6001512502040d5158110255680503400788180036171111b03001c00c24442e00c0410601104001c249202051601e00030400650740b407010510001c0b59011546440d0140c20351050b070310700e50f1240c0051034440c42c0c242005011982c0090546046c0100712504100720b96940d030803030303054a6200000080144a0408885c000139080100018601c030000d000702e8105400c44c3c040c0111185d41e40e418060b5511102844030503909803140c60303055403041c001032149035100700e812680545200304503005100c007150004200c9240b140c1802c8064200101442036080903c060800c40f14240c840c2c441c1400e055034003d5482c411038401c04100116010700d54542c48244650703a0003a04044111020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 136158579 1250 136157329 136157341
    0xb03061003150c0e010f02100203070e1302041802030403020a050601031b050f031009021c060c081f06030e070306020403060e06071103070602130504020a020106060206090a050a021002030c06 84
    0x5810600003611034620802d036a81c102c00d0580103d07402c0c0f1529540f0040801c0b0b030a0010b440d8000e9060481e42580900512080f030b601d080d2001e10710800003907940719000000202840307008500c203030902e4031040c0104000d1000ca10b000006c407890a10504006a69070b03101d00b012420949410320040c02c900454000100744282d241d024020b10188003c54100c0b507070307180300b0444041a141e0403240c25800140c9400aa0b4044e40e0098003d03074000b4040000d1851020b000d1100144415802c82d0f205654048858405500030009075000c490400180d00940070405403280c1441d05110351400c16884d21100f03401c41e541840907030700541d8010001d40d1604e8481c46c0070f00141541260b0400d1603c0b0f55000111490710514038020701c90701613030255140c81081c0c0c684d40e000e580400901050462040d80c0014292118030091074240700607400000e2075030401d00300909101000d0404080b81d4001040000842e801140c903012140c0c1c12206800380385400c0c04240d0441c05140c0861107a0b0042c0020801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 136159829 1250 136158579 136158601
    0x60507142a0f130f02120106020123060603040b04150c0c1109130b0703090c080c0a060e03070603050a1404050d14040b090105070c030206030c070b150916030b0306 72
    0x103101204401401c06100300c00340910400100b02e000c1e4070060205810303000c0240c0c0e900000b20b0210350140549480501240328100d070030203901100050390748508462401c1d6030701c1c0000c0c07130402c5400460708803030901000242c2c05000250016000c2c0e03520304007050410501c0d07021200d000c0c010500a1103003150090016012122000059405860700040c942c00743c036260b082c1502c521890481140491a5622811b54074440200108103043d500c090b45408a0350204901c03000b805420020000c40000c6418800c200c00b082e8042c030280710b000341079100941d4000c10101c0a0300d10500c0e0001d00f541c0d0303030003000d400303028541c1300300c2c5036034210205006c01c1c072401190386040e0702c2040c3c075040100644a0740c1810644034a1284425000040c05903045540c400ca000b804880d004040c07902c44030340c982d0000340709944191030518a204000421100b00004649690350007012005410f07034800429012032100d41c0c005146901914605500402050003503002803100200a02100c189242101c10340e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 136161079 1250 136159829 136159873
    0xf090c0d06171c14031303020c0d0201050405060d1509050402151204030309050a061401050111010911040203100b04030f02010e0402070c0e06010c05060c030103030f080c0406050714 80
    0x45035081c1034010030004000c03200e00014490107001031440300044041511218a540c1d294020016207a81d140c18414028010f58060b803c01400c140381c1006618003e850488691412401400400301820141c0e81100551701100c109650184c1c1c0c4802044a100c005d00e0600e11611400c541c134140410710303505c0c3da8441d0313224510a40d81d40341100c6022445ca5091b001d14140d8400f101c40b00e10000d000a807080c0c010071240c500c524100c03501401d42c1c1d1303602810345510468140c55179a008c030041140b0740e032000700c844181c44088000c21160806d61960070a0041008407107000f00e40000c04940c0d6264440c501d00b000b80a08100c10740c4442e128a0010303c681c5030700409034001101814a2074031881c0520031581000d500c131219016240c03401c6c5050403107542c010050760600100c640c0a5010440074419036100e8032401c80c0e05a5250305501d030251845d44000ba800040000110400c203140144000f164282c601e1030401d00d4a840d80c1d8a0501342e429229541000c82d030041c452400803c184502d852 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 136162329 1250 136161079 136161097
    0xf070e061809070504030c050f01200a060b06090603040605070509030318031014040209041509210305070207060c020a150c020f030115090b040f060609081507050a0e0f090c 76
    0x1000243c0300d01c4030480c2c150086000c007030107143d000070701000145815103481560740018184038840140510141e05c50410320034003e10550045840c040c2004103912800003405400c0300e00c3d50600c40f2135400301e00d040c04024401009a503035800411500390050782510140c02c0000e0440c0d584134110416500c0784903040781814080d1241101c6403522441c0c50085249122a0b03d07200c00460740c46400300041d821001d8026241030f040340c40410038025840c000c4405250084a26a43c80c0c08101c0e000e020030141e000081c0d08040c642818465896804162001116070500d0031001038030392400081e00c070307008591103072403030703000701c80310000c5aa800c107402210081c022101c0b604405035060601d0700341d403040c1d11400e08103600340000740550031a5500846050f48040c000007100036444a003003044400c19002100441c204540c01c20441004001817030030400c4680c8691041c0c100554050580e0083c54040001e125655108040b0782e101c5030581404030f00010000d00b40c07801d03c440501030981c029004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 136163579 1250 136162329 136162339
    0xa020111070f12050d08010b091003150f0302030705040908030105010c03020709051005130e250503010207050105090f1b1c12030509010b09041a25050d0e0d080f070e0618 75
    0x2410402401840c40f181288d5038648040d1030314a01100308209105c40111500601d40d9404903c1d81d040c134283d1824004d0451710702d40648050460040604c5c0482c036610151003a07040c0156400091036010070740b4111802070811314078401462806909200036a002400401d20703007001c00640300c0840358400304403002510842c2e60b0303191480d500c005031a2062407034109503000d500803c1c4000d0b00d6601e01d10f290b084100224140c0e584800000342a64448041a1a141e448000380156040d041c80700c09000c00d8110020038200d0450300c0c10700b0f185951103032440d215600d1001500681180b02400300b11655000400c150505c1642401a000701400d44183d54031758a4130865041605054807814000c94109103541c20101060110f44001080100352849443c1c126003611140340900c030529001d03105c180c48003525000c1e11801c4000301c43d0132060ba03d040754004c0c441c1070781254001c1c84064200501100c04001550b60841c00c0d524609840c2c00c580d00000b0010301c1c6d00e0002d06103800701c2d040c5041107038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 136164829 1250 136163579 136163593
    0x10905010e0a06050c07050d050d0212160206070f080d060305120a0e040b030703020a080d18120303090231050a02030115121e0b0307090204080a020111070f1205 71
    0x1004440d8041009640750704a02207000c00d1201d140070308050700d1503045140440d82d8258480c0045403c02c040e00310b00b12059030042404511a07a0140040e1a000b001128528100005003403030826482c02502d01a00500300001d0381c8003071090b8941100000703504030441c2aa114440e000080042c6038600c001d032054042c0c0070503148407100f20001c44840c080c069030744441d00411101000001e00940c49c440e985131099110020060704c0b648014001070a095020307041642e00c00740c0290002080b01d804d51680e000f1060240145d984d00c80b42d0307402d481c2c0c02d031a00003180403181c40802d82d01c2400f0f8812460401c1140a40404000c100d00c0d07140745525040c1741880191900c050030b0307007a80402e0152884600d031000c5210440e1b40300751180c80d140744ca50140414100059412552007561141180c0182600e80c0c10107025802c041200300c0080c2200d2100314502803500d07031300c0c41d10f800060500030304012030f003c07e41d20100801c11401c0b01611008201c0c02d09030b55a0f00403034290786052a4103c03480d0141d10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 136166079 1250 136164829 136164839
    0x605030c121806091b04050606040305151008011404060b040608010203160e03190308091002030a0605120c0a140a0b0d020a020d11030708072a0f14060711030a0b0406020403020109 79
    0x403d001c1114401c80c1030744408403030300c44200405810008d06040c1c100780e05010000100390104045101c034900c00088181d5414400000d90000000c2d0300440d00c04d0b81400001094590141100303a0b00c10340000340052409014400100a005d0642c4842071540c0080188841038100c2c81d03c1ca620343c1d050b5108c850301d4a110000b4141c60319101c600190442c0007a11504001c680a0703400b299000030410192200b04a4904101049800c1a207210021f1543c0d520140024105142c034003480300345850080a07084400000519404603034020104884801d4440541d00d44940b07503c90040c103101c0c0401c540b101349640180e0003e4200b00c10510051041d400812407481c01203150852074000c3c10041c502c0c000098aa20005034801d0f20129400d086081c10100c203607c0c07a850080060b8411428490f5051822503110000c03000d503000b2682e00f8000c1400002603a1340c03001211901a8052400e081d20a4810300180c01c1c40d2840601800a4190358101b000b000100e03030062003602d200b6201c40b2095501d0f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 136167329 1250 136166079 136166083
    0x40b04060806010b030601020a0503160c050915040b010207050a080604020f0612010e060a030605040b010e180309190302060d0203040c0b120a0b041b0c050111130605030c12180609 79
    0x540306003402900000014045131401c071004550080c01030040340c0f24645940d440518540c0203414028012070504600b03000c1081c02d0044500800c01145e1102650a0150744540c40041080c0228420390340c4e01422541a4020b203c07500045c10000c2008002c0b9584041403a100c540480d0120322400b6030002d620401d1070040192507082c106121100900d80c03c2c4407041ca103000f00a40b100307500c1060385000100141c0c06000710381c031603403240e03070340c6030391549013190541d001403010300044905080940340242041c40002600c0000e00c085a10026030b031500410b00311408000d030030182d0092030000c0d0b1848001802d4001310b000b14851144480d5095a90402050b180201100b901d00100c8100120320b20309919040811100401040040d419188c004402c500c5a1089490004940e070428003906000f4284144151420a2941c3e41d00c1c110401401c4606284280104000d100c4040081820b5200070000e40d9040c0c0010020080d19040150b00702e48102d072180b180d103071180300310000a1091540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 136168579 1250 136167329 136167341
    0x90106080a0c0b1602040504140d0203030106231209160e0105010e090a15080c01030506100f08070e03070b04090c17060618040507030c0818101802180105040b04 71
    0x1200b0510034042c10259080300a501040e80c07078074250b03404140d090250707840b48640c0b4090303445101c21824003c4029110350400070342500c0101590001e000400c80ca07038000f030140c5190300344400900602080030074800f603280164030b40307000c02c03081c5078080003051710002442c000d40c0400d10035048010f42e5144c501c002c4002c0c09020702030001d559802c14504a042071640582c000d10f6100e004954107030019010b4408812035407040f006070744601054100e550309440750542001056803401c03c503482e80701000e005a44141c01040820145000091480e80300c2c1e1040c2c1c90552006099942c401d5032a08a20095000f500403540c8403894444010442c9000f58260340d0030303240c1c1d42c4010305941d60b094104034954104001111322010300c143c0c005201d030345a2081500c04c404a440006100c1c160701001401040001d01240020344a810035240070840082c0704816106501804a010419403911580080d04200003d400180a01c0349850a200c0882154143d40050724100b003c010840104419036003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 136169829 1250 136168579 136168583
    0x10b1e040305010b210d080a0216080d0b1203031308041d010513050f06040b010207181517030304020d030e0607030801030b0916050906010203090a030c030c0b0a120507110a0506090106080a 83
    0x700801e180249540522101075112803950308c014148039017031090215125103000c08031410b0308000307404c1d54152070b0307445113489030b68060f29091918842c15961b2603a030720002c6d0881c2d42400d034404d0a8000c022030481144d010b41641c1032010140600c11010040044080c00f415100b61040282074030f0b00e01320303403094605c5000c06000e83c00450326844140030040c20035555850450040d81e03000b20303400c041d00b01c140426000380b800018007160341103003004941c41d254002c1542032032031a940d10791500000060341d41194040307401c1c07820104036107401c2da003260f02040390320b0300038102150050074503402070b4185049038041e034100607150b0ba940d041c0da501d403030300c00d403d06595030708800c800d10090910480d45030384840b040c0126403424206030300140300084150300807209010080024010840502c100c000140304070a515400c0c103082c3e9102501009500c01403101280d62400002d0540380308524851002900301c0556180030340e1810700c151180c07000c8030000717070755828844005584440010780011481d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 136171079 1250 136169829 136169833
    0x23071502120c0921011b020a050d0e0102030a03180f1a1602030a14090d1b060504050108010b0d0f0e0c0114030702030a1107080106060f180e010b1e040305010b21 71
    0x5101c08100d00313240c0d0900c00c94419907035400107a0314041811200ca03a041455001030600100340d2034014a805425017840080090f0b103110103145903000400e4804801075410042070b90000341c0c0d11103188030507510019080d048004071040c28032001e00030030f030158541c200c1c003400c45640d04451600004000700c043c100691040000207001031241182c03092149202402d24902041140054900c0d510800283c41f45442c01c10300b0a050300b05d140101004140304d040042c182460000040c115240501c1503003074080001503511008a8203601811014007000001c1007042061000140d40340443c1c680e85004c9003440c241c00b81044c0044060300d11034159507000b10311704040c0502c103c078044810080c0644611409801107400a028043c0d0b0010342a40c0c0c0e59100c00f503141d042c00a01c030301c90320036841c143c80788200d02c03d0240c03101c44569141500c1d07480031a6a580d8001d044090400c01c58a2007070f554034040420040200311043d00320400a0200f11101800c1c0c03030441ca1140800541070318598115 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 136172329 1250 136171079 136171099
    0x1150e04111602060c0607020705180c030412110703060204090b04091502070c080304060507061409120c100203090303060102012706150b0d0605120d23071502120c09 73
    0x407224141d0241c00c184040c4c101401c00d8190900300e443c110064640a015800420050100b414a07080d49423190340e81e608520b0090a0240440c0c0c25840003400c0034020384854020f03d90907a00800303640075401d450008407410b03e030340d80c01d05000941090050310116820403500d00708900d00340c010030f141160041c42415002e07a00240b071030020340c45640c003140c601840500016400800b84003030002050113444d0207036500c00c5850700000300c418105001240e010408140324170030754001580c21603000d03565601030340e41340c010f141d2900e44602803801c206818000410428410008005140140b0081c1c00900c00f12010700c0c50b0880781c845a04280141048001c1c20601040b80c0d034010003010394861850f090041d848002040007a0300900305e4046554440c0c0081010342807010315404001d4169024100f04031010500404188070241548200d24040900002c0210898200c802c5150b0005400002003108080d030f10281d000a8010f861140c0d4800c0051103056112049901c920b078000e00708286 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 136173579 1250 136172329 136172347
    0x30601090203060a050d03030506030c12060a0c020c0415030510050705030a0b01090b0c0d0f09050607030e0f041b0207050f09060d060902040e0a0524010b0c0a050601150e0411 77
    0x2c1d000206459444100d003040081c07291030703660401c03119600941e808285454103609044c6040c8920005a01444080d200568034000201c5c4507500421950404600d0800030300d0200c0c90a00c6180400358414585591403680f440c112641a0849100d04103490039010840015411034030221660740c0803513070030030005d2420050b660103019842c0c3d0504100d1b808075159440176400740c02607510410190b000740a00258a50010f019071207600e654a002c0003010b0422001c10341c0380c06414001028440612240c00d403c0c1d5444c42c4042099001920412844290f20041e100781514820140054003076000086024102210000c1c00000003428161045c2c031403005200d4071141c41031044e141d041c1d9840c0c0050040e5520f0040c8560303440031000502030001a82087d40c2003040f079080b26001c2040d0007c3c03024007040162409030459002410030390f11900c41410403800d0004000c401031150143c800089181c403080c07001c0b5143d02d000340da20400041e003442c05100898130b2586040241c4841030040d504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 136174829 1250 136173579 136173581
    0x9030c03070f05070801060605071e03050f090a030209042301060b04060503131709030c0405040b0604050402060d0504050709050604020715111308010b03010e0304120201050a0327020102011a03060109 88
    0x150148200e0844d8441566621468211420b07500002c0000d940043c10105000117004a01007107907154200e0245042c980c0d0f809081440760340b501144039080030840010540e501d8101400858001c0c108810918007454028210442d00740b00304421010304c0120030090005100daa0b007076070690703100c0e181f401d07040c0a001c3d180f0380c10040041500c00002442c50b400140d100d542e2020308900e09207000e80310104c00c0e08060403e070124200d0760141d0b140c0410000420b22002c0100d80101c401d0310700103503e03195800451840e1044070002c62071a414502804100a4001401412103042042c00c1010362a820100026441210f0014241c0c0010407c8560302c2d0006078891140d80c2e0b0074102c0185491a640b51380458481240d1140300603035035603150190036040038015240200800f101540c6820309120705411002d24014000c2c1c104000412a4600140664001c0129190300b0b9041035000300310031840401c004000108a0043d400c00c000c210103c4202e180c15820104002c0150a180e804c1070b800c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 136176079 1250 136174829 136174853
    0x6090a0c030204051902070f03030c0318060c090305030a020609060f0903031b090a06081f180509030f0301080d0906050310120203100203070801030605090a080d05180f0a020909030c0307 82
    0x18611780019021035003014600c01400715500c200740040f1036104505001c0d04070b43d4500344000034941049a1101154500c1c81040b03059a402040001c102003203010448064a06402c0200680310015003610900d8000441134403400c400c0c07003102d0315682e60b40702e1555281c0060f01c0603003040d8001e02c046001c014400d010110038541c82e021003400e2002c500c002498060b03032130340301c080030904920900c800318940241248000c000032001589091070204145110030494008400c00707550742000c11034090b801e0084801c00000002803603100d5840d01600b40c0c95005c111400800304c2c900130070008015000350152445001c045003103541041c501804400c541d018000c049905010303000110003028128030145006030307116070303440300c8540c10341c5000c038111070000c0c20040e031941c0600320b0780002550b040300301c440c0387c0d030886c1000c515501da10450307450383e2b1402401051180a00b21034170200345e10000b0480030050084a04141e2601c400a94070786904c030700780180fa402d800030803200010038182c02d409 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 136177329 1250 136176079 136176091
    0x10605010c03120e1207060f021305130902130c020d1e0309030905040603210c0809010c0204090203010f050a0b0a050906010e0a0317030709091404060b040b040e010e06090a0c03020405 81
    0x800c0d400f081c2d4110171308020740726580010131000854500d06000241c811883d1601c2c419504500e4900041000b0380403400512410740f00e4000d4480c80525031980307802c4170391015030192040c80c40301e10960001000e4140508010010b00c15010002201842900444017a50100c50038880b5804510012405442961005d0f802d20000700e800190b203445520404004502403006034034400100e0001000e04000454400100074a18114030013107034440c3d0460700190b8003401c009003605013600c041005049120000b071350552178808002c610001640100d0300c90316840d0320802000c80c182e010000101014083c1a4001c215007001500c0b41d400307001e050048400c020000555075540750b13102d070240d0051105020021002009128a0a40000307410014046000041c884001301403075a00380d2420050003c4c205030340310740420b0310a850315070001c4000c40c0e01400602c014010000a14007070040050742402c58403810001500c4000003091840e4400d90050013090071034990380800019140103012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 136178579 1250 136177329 136177331
    0x5060d0b0a110912011a010203132709030201090308060109030515090a0f030e010e0a060806100504090c030203060a14010207030609110a12020301110901050d09081303081308010605010c0312 84
    0x403c2e0765440002c411001d0404000105403414400102c1c004070f1b4031001c50364103550080c42046503140c02d20b00880160b451040e1088060118400101014400034102083d05842d15488406040e03040d00000740050103611940d10b02e4581000440b0420181e00c0017510b0343e04030b40c01e440c00c04041c400702030782c0000c000000c03a40c8044907510b612044502c0041e040b4082004085103071003550b00300e040c01c03040000440c3c4105040f440e006024040c0384008040b02d10031820035880d4200f10740100240e50140a0304001002441001c80000d030080d401902c1041c071440b4810741c0020300b0382c0b24072425901010180c0c0901152031840e928100900b14200d42105d030b0074140080700540e03403075010a80c4000e0825200500d158090340c018542150b007012002050b08008110304030459070088100c6410344581c800014955100c2e0030001d103c3d0096080c00705c01507550100010a000c4680040c09858500031400d07a000e56494441d40d007242c0c40c07882000d02144858840c03c020034001d41004e80d02c5004920 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 136179829 1250 136178579 136178587
    0x7020112090b090a0302010501050301140a0e07030b07020706080a0615050a1e09210512090303120a06030507060906020703020105090414010603050703150f030605090312100905060d0b0a11 83
    0xb0311201d0000c011900e00e04280c2c13000c038821060507424000c417401000107400030081202610103485194000400000745951943c80c26003408104101c1c000c01560000d0180d00c0ba4109008001d44908040c49140c0010301000080345501d442481a0021200514220054040008002d07595904a4070101c01802055a10300c42c0049404824000301070f01a178810345200d0400560b5000c2d00812125003449210800381c0e04009200016145c0e00c56410101d195200c149840009285205031b07025090019a4281403010000c4507810807025039110341300741d40b8840d8a90740d040f40c0020345131140700e0060340038501c10805540604005c1003180c0001d400800c4450903e4042d04107013400303070302910010b69101c04000d05160f0600c80d035000050390064078480f15103080b0120240801601020b1300300f50750341010586600301041140c004440300058103c8500d042500d05400c00361071f104040003141003000007406807400074002c002203584000c24001170b484546480e00240031900d040409010200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 136181079 1250 136179829 136179833
    0x30604110112090b01051e09040201080a09020a1202030c010c080f18040903080a0609091104051302120307020a0603021213050c190906050301050106021b0103090c0602030307080c09060702011209 86
    0x10140410f814028410f000895141c82c0034050090060b102c101480c0641160214590742c035a07002c01e422640918104840d0b031140381c40d110083c40101c070001e40c058000e110000d0311070341d0380c1c007500c0c0170b103000b01c054810310801c0700019a00c3c3c0e10703c0780d00180003081c07c00031940c81c4500b410150100c0140300701f800e91000c4030400861300311280402c052340071030110010404007140500a00014100a00e81440408050303030b1030001c00803506944510450b12200001c2e016072044400ca04a6600285105a07090021203102d849501804050b4021200403a000c68840c0c0240201e0b4000065010112481d903a001c1e000e07240c41c0b4006c5012503081c042d14040a0b01076079181e08600c40c4508900750f0244c086d15040d0058200c40301c1c0d80c01136000782d0424004114598000c00c02c41034400c0d400669507404040c5c01c0c012401000c66520040ca41c280c20040802c3d1140e000000d10310031012501d900c1c510307854044801a2a00841c80d5440d0f004108110000042d44116000381d003807214002c011808242039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 136182329 1250 136181079 136181081
    0x60c06040f0f1a090705041802040b1302040b210420030a060f0f0b0306041a04060207120302030f100f06050a0221090a09050f01050d0819030204051e030604110112 72
    0x416034400300d00c3d81e14002c1c040c8130881404050010f0404440400500145070a0681d51346040c440107842513031307030740c003001031540301c900c640313148401d83c8001196500c3d100d140d481400d41225004c030324251703200440c030301c103100f9000780c4a4005c0380c100c0c0f891020003022042c9041c0b58003050b44000d400d8081d007040781c0002075880c000d000105901030401b003240e40411140750111081d4405480c400da201c1c80c24000450400515248165510540c00c851035032541091800b92041d008001c146009541d004010030b075141d0301030350045511010f02c1e0444e84071402c08102c000c8690060000c1861014400c00446016600030080b09002e8010390790140c88800220325101c00401616080842c0000d0030040c03450483e042c04040c1c0700f02c0000304200e0070905e910a410102c140162806000b220003901c00b030040d04002d85000708401c101012031208407841c001c010303401520a00340100d2001c060034000245c02038541010040140003026283d0315910303082d00b031050050032070741401500d00d0102446046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 136183579 1250 136182329 136182353
    0x418020c0114070e040603080a111509010204050909010203100e27030409060e01060f050d0e0a150506040207080d09020406030c0611060c0a0c020112020904061e05060c06040f0f 78
    0x185200720943e14001c0b9026041d0180220340d0307841030380303400024000030b0303c0c070b0f0107a52040c806440c1440501c81c203e00100c1c41c0003982009000080b1b000000c001503c441500100150b490035601d10b0256100d2400711401c0c1d02040d18801c0b100180035606100900c0000ca2556001c8c28000c00c003a0a0100350009080414141e07802c0401e80d0400141400701c2c08540c01248014499140c40212940c94458020072200e628401601003100c000f40105060300e40c3e420120441025800b07490f2130150500d0088800d020346c0801003440d83c00d1400084461401c5d100380e826103a0440b041d646401c0c01240e2241c020070b60000202d90040e1307240700101c04219030020420250402d91900083c080b51810340a2030190010120f4407940386c03c101591070070307a118101c0c6043ea513081c00c1044810012000d0720010340114400290064070380a400070741c41070801c15030745022905c00300020060351907009100044c81b0300c4500c1103555211502240000d84200b1801d01c1c403c0c0100880e608850090b9a1000c1080d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 136184829 1250 136183579 136183601
    0x61938130f150509010e0601051b06071101110906210106020a0c0e1306051008031602040b041a220c050405092520030705032106060418020c01 63
    0x2a68001e801e06405203441924400d02c4042d8206803a0b42c03910001580b40b190502441070041411001308400e0b07402070054034402c60420342170381c0180c032807409500da480d0303011100c1e0b01c0000c9025040050081c0c0621600400d9001040d4085c607200401041c01400c1e030200c8200d081840340d0030506083e00004c2d0140502810b045d40c060901b140e1141400860140395402078550000500c051080c540d504400040c81d00c0e90101000ca2190303500b081c2c640300c009040d40245400d000000300d520b42915a40d1603c2c1c1d015200712001c108410000c018003080300e19078120030b40c1c0c0380c0c100008030005141506034003541d0b104a503050030b09025600200c409480070840041e02041011a080c4407a1906100541d4800021034070204031105244043c1405000c1241900c1400b426a5000e99070803a50308a0855407044603007103e554944a20300030f07950340c1c0004513640074407070f010840756850024000d03914014200241890f0a10303040c4000f900306a01001c0341024229820095451001c80a0085001c142 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 136186079 1250 136184829 136184831
    0x90804080604051e0303100905130c030c06092418030501090303060e06010c030c03050c0c0909030703020c0306070c02041a040f050f010503010905060f072006193813 73
    0x9070210103104444511145aa01365400600400802c8503810403814100c0700d01c90f1001c103d40d118400100442003611001408400a40f5408070038010a8226070048401555407901c03015a00e1a401803d81d02c01001c016650342c03540d031011034182c4039810006000041c10b00c0c0b482426500e54960382180d10740a012000300e61140c004001c040a6150002d500075820300301180244002e54008050781c2240e18002c090180c0414000f158280810003110512009080721495040540089076a41c115510403030051013590443c2509041c04903859004044903141c1c40c41049465003000b01a0698001e01070140004074200510340e600d0f4050003050120003040004e40303081441071a40c1104c81600258000d0703040042d0b20700080c0000840c954019148450400b00361640c80080b90440703451a6410030382c4d00004044c20040300007003440d5000d07041152038590000e145500301003c1d14a180c00d00c0c1100c0c0300303400800d600e160f180c58a5650003040543c000c41c1c914240000659208a2002401402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 136187329 1250 136186079 136186093
    0x12010e0711150417131505070b041b0b0c010f060503070f030312270302010b06031509040f02270610080c09010e1003090c090b0a050d1103010203180c0405010b040909080408060405 79
    0x1510a1b001d0408900064a400341c40e09801e9201c4e40c105984c040d20007807007204c58025540304880529000c10113004141109a0303200180c8103014080c003086103502c1f400615010000400d4580014041c1c00c580b01c4409514216255450550301c0441c011445c0d10920f4480f03c00301118503042c80303084c80711042d644011404000c1810b009007103440980007103005a8040090208040311200307101d642d500112020451a40c0300d15007d000c050f204000250007880d0000f12805851803185c04c0c8441102c4410030300c40558840c0c0811041d10072101d2400081039191011500d034a110340d00078038901e04181804105110b162011403180f21030610a0800240d071a14500704101c054a54103004000300034091290880c0480000c56003603452082603c10158414070700100910702c280c200d20350742c4c020000c544901d4580c0f085041c04144038000b0000c2d018103100c042a0345014440c55050321400c0007400e041500f4101070800503c00901705130b5074107000740800a58850100f15452040344240701038604 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 136188579 1250 136187329 136187339
    0x1906080a0e06010b0a0206390c0102070602220515030a0905061602010c020714240c01050613052e050603010306020405010e06041401030c0c02040212010e071115041713 74
    0x4242c2c010f0030304111031290301c41100f40c4003034050343c0d00080113042300302c50403080b8010503500082c440c091034200954000b10311081031125a82c0501154115950303c49005d48142941c030310b480560307000c0d2640c040c508514140980c003850000e507070701a40040002500c04c11036150f05241500495441401040c90340e014001d0b03943c207002e40c07a080840c50000f040ca040c1810040410064001c2040707000d4090200c3d0400580041880828a0032131020007030f5564910700074a9028110803145140203d41c0142501818042d0340f09140c4071b80e412002110302422480d07007803400c038034110b40d480c0054409414080307a29a40c690041d4001c1d40300d130b000142e4a900c0c090000d0814048804d4080c421142804100b25050945050036010b000034a80007400c01d100900646440c6003e04001c0e412501c0030030b07007007181e0141c4800c00d07050303482c62824001e0540d503116045444800a000b050519001900d0407814078041804080c0c015100d5200d03403800c4001d101d12032416800065400e4600e04002c2e070100a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 136189829 1250 136188579 136188583
    0x90303072406060c060906060e0403030b030607080423030c030c0303010e06180103080f19030209042d110706090b04030807050a050306010509031213030209061906080a0e06010b0a02 80
    0x30103440d50320103202c070b240360034805010403010501c040d12040d1210b100200700030282d0b01c240050308040d0482c4d001e0b4146810000c00806452100f903010b071013410302280819002c2c030b8803e44295030189110104010007412481ca400d18000d0b103620034030040c403500350070319418805843c00203e01d000541c0c91791b02d04011816001006045180201c2c0c07a070382002c3c880d001101d110b0b0f054a0b002050380745c2d10b040b001622601c600c1010078a01c00d5a2120780030383c203001d82c560010321074084115010b2109262051a111161840004138614105d65401d000d08503042c941000850051001c0d21324100300705925448245c42013400119036007489a4100800c00d5000215580c00106514095040075999140030b801d51201038809414480c01207900c4085603020412a48000f5011002c5a140c094103414103444048500013280b2070000f110004100d030610f000012100700c50580036203141880d0000c1138414643c041c060404150f102c11a15a0218082004034001c010f102d1802c0d64400d50140300038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 136191079 1250 136189829 136189883
    0xc032c07030606270204150815060310030605100501051e070b0109050702120901080406050c160309080706030e03090d0201090b0310050103050f10030809010507140a0302010c050a021002030a0209030307 89
    0xc80b01c17407061006001c00da4003250b00c0300c403543d84d42c08e040b030250300c8059004c4c411814841d12035a02c000000f0404c0140308104a1140440b4440c400602c0103855041403242c048850b4003070076000440512912400044644034031411700c00a0050700d02d00803054a9941c9821000d0b00b052403019241c0b0203018040c0d030b0401440e12100e1006024a00348802600020441c0001400c0541015160300105811640317107000c407440c082c0114219103501c0514580948880c210f441141d00c24099180006400c0c0c1c06402054140c1c1c41c06005185004650307410015611400d2a0984c100140c81d00045100c921040043d406850480300c116402450400018140c0710010005801060400103102c80f0a801001d501e080d00e07801b0740c0c1152a0b00d44100101c805000e89800071b0003001028410a8001d100810000c16242c041d034024000781507030740f03029a02032141d070070030ba0011b84c8001c00d001d0681080d0f40c050b43c0c01003240c03400540f8101581000034555001070b882940c885805520f5190103c5440840d1703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 136192329 1250 136191079 136191149
    0x60302010f02030f030126160509090d020307230f0a020a090207021305071421010b04240c150203180105010b0702041a09090604060c032c07030606 65
    0x4510708400c21400b143c01c3d00040c4074140c0c10066900310100d400104c0307420701c194140c40034100c1d03402d0032300103444002c55180b61103454015800301d80400c0d160300021403c001c440140313800940c5000c40c0d943c0c500f14040d02c0c402d1101c1c3c01c0080f0b46240d0000240506c121584110903000904840d0907500402040303030b10f564024684184100075040c0140c481ba0100100e0300c0803480300051564864000f030302c12200340c4a010048280001c0c42034a0078586000c01c10b554002c19a0668a81e030301c90080c2c507100e00c114058500c3c002003810700b08500126584c80d00d4170b107442d07910300011000800d540c0e0340c9640b0080006c50030319603004030400a182c038450400c0300312034024800a01003545400d00b81c030f01a104542c800303800303151a500c8145180440710405180c0c60000f80c0403c10390324005150903207800e0103035800c0fa40c1303a04040505d80420711a0040901e1803400e00e40303e40080d01c0c181468929030040d003401649500440000101080c00c074440d40c2c000b804100d41002c510075015180203e8071401d4100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 136193579 1250 136192329 136192333
    0xa15090602060613020a020c1c1403030606160503040b0406080108010c0c0c180b0d2a030314091908010204140103021c0908280305070219150b040f060302010f02 71
    0x400030b250380ca40003011503001c1107580060782c0e20501341c402c0341001c40e5000c180e0f8002724110703007944a000c0c0b43c00205649c41c0c003805003a059001c00e800c201c0d80b40d10080d00d245a011105101d1940b030301364010543c011240c4524200d914084e031380e403890301940d00170354055004100c0c524010402100207000b0324015003080e103030103400d1100640d0707403030741035411070250944880110550300700a84007540004000b140051210142c50420300c0d00301c0303051102c00f60201f140c11224040202c806003007019032042d00ea0540322080300036002c528030340b500e401c00b03106581c1c0000200804407030002c0c1d000084028000e908000740e81e4a007070014000402481c0d10409040520400c102d446564881801050b01c00c8296070102c3c84035202d081100c50f40c0a5690010300311075131002c1150780000303038407406602101952030901070b541c0e40031000c0c3d844006114007049080c02d00140200000c45107160b61041186415002071244050804581241e8031500c02e0104550b440c0f4050040d5078000d1040820f800036440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 136194829 1250 136193579 136193581
    0x20105042003071a0d0213060e010507080a030f02070b0a0507110f030919170307030e04050601020604030e06221706060607060c0e0d060b090c0307140903010b0a1509060206 76
    0x1c83d07581c910922607031912580c0400c40690496079142100d4100501070170540d103a02d5140e607040d02500c0c03184182008100c401001d01c209500501c10780c0e4046400850a505111000c00c095025003107682944030896400c010850001d800c4244140c000c452086001070300e171901e0140507110302c03190f08001d603c9a0103400c40c520f514030000214ac00300042580c042c2c0440b6182e41105054051319080f001c64050300340303910303001c000c0b00001410303005009030b0b24928014041e20500040790026151207005810080c0090086030245248000018001d4081d0b880c2c4600c8410b070481144482d1480c500003c04110200413984100e420b080030300e001c200c054401c41c1071103000a04548540c403401008103840b5a00184858021080a102005e018090402da51034030301c5c0100081c003071004490710915128011400316034920064911a01550722a04010014000601025081494001e03815900ca40d81c103030041d100e00e6811001050803201852224100c0e49001d0448601600000c04560000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 136196079 1250 136194829 136194893
    0x5030d09060e12270312040b0d0c0302070201050a05160b010b070209090114010509090a050706120c08070f050705071205030c0d0f2c09090c03010e06040c1517040302010504 76
    0x400c20380b0700c031580300c644e004015100002080c00d120b0200e45003050108042800500c0e045110001d140070241c6000170081c456400340e0a408a0140580c003030700080c003d01080040d507004400030400840700c086c00b000d9010582d9034503810301c9002d0300950902003003c9002411401d11030901742e04032204000030b02090b4444070181e01044030512500d440b42c090103000c0f8044c20418026101825004400d69103e25218200a0160200c0c0b110381c0641c2440c0441c6601241d00c079529840c000d04031503441c0068807101c01800c99007600811000c1d10b06000320040020484440441c4100d020f00c644061a06c400110781c0b1103092080400100c03040c001030092021900e503014512010441d03a80c203240b5151040303449041e80d007902454500d90801070305030a216042000040402009000310000d0001200d664056900c45506460042c10300041541c03e12080c181444616070010076071503c840c40040e4050000001e80003a41e054000d40d40d540140001d10504084640740b081000d5084a1410402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 136197329 1250 136196079 136196107
    0x60111010c0908011a0916051c0b090c07050c0907030f050f01050108010b180103020d06080a2105120a090201021c0c0c0509070e1e060403030315050301050c0409050405030d09060e12 80
    0x101f01100707c5040c001c902961600803c02d840258180480c5a101c08282c0c4070312200908071f80204034400d264120008034054280012501c1540d4003c0c040c1100b0404901404805c0314050b2526040c540c4902d00c40744030b0744070752040034452810010b088850b945401c0c0058051001a00640c0702594104244c218050a01e50a0401202c003840e0041e950045454400000c10440d00b00c40020b026014480c4c040c49a01e0540d80e00c1140e11074031500c0741c0e03102c824081e2458800c5030700d01c903494452040050111001c0d54040c40c0606c0c01070041e00d40b40d10356032048141d0280e440180c1c201142800301c0c00b81c284020412400e01401040c6d61082a5041012002e49100f05101c2d40038456800b029808140b440300300d10061011401618031521075131280ba029019001761812140712330041c00340040d036880c2c14060740d0300801016a14524040c14038145030b01603c4028000c3c1c8044c40100040c00000d8014410340c113805005030300c0000c2190081c00c0c51800c190030701d250b104147c0801c0c008400e40c0814 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 136198579 1250 136197329 136197331
    0x10c02160501020304030c0b0f070f080901030b0604062007080d091d01380313140a0803010312020309210c090402090105040b13051501110708060f060111010c0908011a09 75
    0x1c210307409c1d2030341e00c0c5c4048890a44034090004090300c0c003917a511400c0142d04000f416045c1c900340c0f02485442d0801003803200c0c6010b18403c070000145251042c800c84552201181d07180c024201c02c0d1003042d519600040e280c04c10765500e00c000950071003420400301040122500f42040ca0005522955140000d1341d405201c041442600c00141c44060034809803075210380080a000c03460030700e6164a00110710044101ca0303188207030f65111300d4003207006c2c2c60503010544a140c694000b0324141942d0a54545407108e402229000003580703c20464101c4a40c2c07224009800f000580145141206002106500313240790258002e001d83e035650309000040e0b440c05180c0381590300513603000070183d5508001600308405021070074006460903061201d511280000d00c41c01220030780b2401d1070204ea101401d981c0c0c11103441495566000b10010035900005000355940000052406100b049104001e080c00c42c0c0d540c14034800456000b01007000440000c1c0a2a5404550307c1842c500403040d0f04c01048000d20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 136199829 1250 136198579 136198589
    0xd11060411010807200105011707050a03060905071a0a0f0e0310020a12090c03050f0a03021203060109080d030510050105072114040e0109050c030c1204050f010c02160501020304030c 80
    0x1a000002d003045100f10006074002c1c1c0117048006001a11001660081c07000307004070300b0125195002400346000025010342100c01c0a040420807d1035600c81e40f0042107080700c211514061b0800004500384c0c02c0320341e0b80340600b00300d86a035901c150a40c4060300c9024082d502070306000e03000001d1a031940d000f0031078141d1007042c0d10016a54141819007120b04128500310001498941a01141480708075a48a404d9030300c25000c45150480781400c150307a48540400080042e0b000004070520030004c0d401441d013022046c14a00003454444812034203041145c03082000180e0f8400800480326208414003004200a0030030519140f05500d03022244c1503a5a4510111446d13100c0f240f5800307104400418821754840380c425156074460b04201c00102c028030941c80314a0030320020071102070072a42100d024a01c80c0715035610345161400040d40308ca8004000303030740780c0c002e0482c4255407100a0207011601c01503540640010f444402e0308004100312034001c2c81c11580140024400141001e89440c1952 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 136201079 1250 136199829 136199837
    0x10b030d1b240e011e0b0310090206040506070f0303200a03020c0304080105070f030b0603060607021e030d032a020604031d040603060b010201140f07120b120d1106041101 75
    0x60b01d1080c6008102e003450b00980b901d15000c0302500b0710406521503079030300440d40c4c003e141a4a4104005007139030082c101142d030640040c07582203107031011075000780d01c0d152000c1c3c206401c103030360340c000120786404c101c00a5401074605040142055030500c00c410400041c0340707030312507190f0700005a0391003405842d50000a06500044210710000100305a40c000c00b40e61009006514081c2d0313004041160140c034000103e0700785201d01829103011419a413180304c1c0507004609002041d020010381d200040440e0304001000e15050503141c400740120740d01070039551400b10b50440039a913035004082e070107a480c0c00c46000c020003800042c1d902150b4140c1164140ca040e440c560300006414480e10019951194054a0111300004001d01a00151001b01c026002044031040c0f091101900030b4080310a8500d10310f210001400700740c0560140c040400301d602000401c1350051001c160740c00340c2c3c03050041c200d9106100724220550f000c26610701c03460007000a80b40d40c2c00c140e03440e00c0003416225011410f00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 136202329 1250 136201079 136201103
    0x180507021b03011404110a06230f070b04080c0c0301020403023703050601140d02010c03050a0c08040b030a0b01140423060d05010806010b0a050405040f020c030705010b030d1b 77
    0x80da501350002e4040300e55005500802e800d26151140c040121100b4150094160f001c0c0050302500801d55400030072500048040d44221070b04858120340d0042000080c0e83d00f080c401440440c84010202d8483c511403040540e46003000220680390154900b242d901c02e038010803081c4011303141c49014403658003850402408604030700702210380c1210642c4070b030400707507101117400401c0c000c000501c1812108114080380501203400300b440303c0340e987c500d80a07010a00084444000038814401030000703401a19003003081010581c0c808003598003076800711206480c0030040c46403038107551046254010090a20031003111500e6038002d018026449010070901343d5090228a06400c03c240514030b0718000e152a50f6154103d009400803c42030103a0074052044000104200a85504450154940e521038500301481c0c4410400984802c1060303002c2327140c00b4032410002400410140000718441c2001241c04520351052500d400d0b0003911030410441c3c07140d0310340e06048402d450005040e410010142034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 136203579 1250 136202329 136202383
    0x15070c051c11040911102709360c0302040504050319050c0304090506030304080d08191404030e040b060c070f0b21100f0303030618050702 61
    0x11040440d405140c101a11030907845440ca900c205550031039224112103100c0b11850003d000c2280d0703000c04028441103502503d1000c038540180c000020070441c4c60040d0142164410200f213030000d48402c100c59035a8888140524000c0303000302e000380100f4000354a400e068050002c1c1680c01481c12900800550080349005e02c5043d090410281d46c01800c01d11050502e0b00e440c03a9207a105245ca404e1811280c2141c03081c89220707100300c0e11000c092070011401c0904000d100e00080101524880e8544410400041c03216014407100e03115a8941e01d40b00c0e00d030701e032502404988400c0d100301400c25a00e06100c0d0761544c00c5809206400a8044c908441d03100540e00118000b01242c0708015800f1001080d1580c94081c001105001e4070304c039001281c8015600d101101d024001c0c481e441078a190400c503000d203c1d00f51403035002e50001103400654a010307502e40c048031104046400c19400203484031801d02c16228031068400f5405650a41005a46440c01000791508d50130010880c0040c0c242e41d840e95 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 136204829 1250 136203579 136203593
    0x501060e0f180a02040515040e071a09030a0b01081c05090a090905031218070905130201080c0706050a0204090614030a0b0a0e0102030907060e06040e01060f14120601020c0406051507 80
    0x21071580c080e1082150f030a001000300c07d140c400485c0780d0300c2355090965407440710700c0100f950701c21607803442d4580007004101c100c1c81e40c030b40d0420b00726a0b4040c4100d03200c81c000b2400003c0d4a50080c8180000362100480109082c0490140d49465400340702703040005000a8a4440400382101c50001000907480070b1460602e045104600041202c1e09602c018002c40c004415200700503080ea00045400840c0d468031901e042e141c088580f09468240c41c0700700005540945446d0b5440301c0801e01c0d084c42c00001750303201d88c2154001d4805480995001c83c05011641480c800c1c603001e00700c45520001c2811400b8002030f555501a80c0042200c0d06200201d0385079122504032115400920300255100e190000d140d968130002c034402c440020714080351244032400d09070101c8065071501c00750411541c2c200f903000e650b00d28400980754200200c00c0b0202039076031580c00242c2784c01701040a4141d180d044c024002460502c210a0380d82c4140d01d0598100001da46540442e000c02e2000c5031016142c00031410051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 136206079 1250 136204829 136204843
    0x9070801030b3c01090902011d03010617031312150f0b06070b190e03032a0a0f200c010e042004030b0c12060415090c05070501060e0f18 60
    0x50448030190040703071511042c0b001c4070064035a070380722025010b80c0da5210350800d582078204041d010070202c085001c0309c4210003144142901c5c0c060008a41c0c1961003020400a0100d805d0b409229000491079400900004080c1401071096001c051054119034551141c560000c00941300d510365035080842156400f03070044400c1940051416803070b14510305120241500031500e0b20f804015017071f6044920112403060040f0703c014240254113694a480b03462500c10100005d039a0360742c400c003282c440d5400c111b00040107171044940e01c071400744041d020050481d2010f00d003030029500812458410031540003a10154041c001d19010004902080c04103000345500061080300100d04120400030304070b030701c00034003c4a1084100c8281c9a4072940002c43e0780c014000580042c510700e0000c070b8020310f0329030010b6400f5540b45034101005c940e03c4c40315100311240207040a000c5000810701c0c0342800001e10074000140f60307040705e48030a840c0c004080020120001c0c1054680141035040d800e98040800142c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 136207329 1250 136206079 136206121
    0x1407350a0903090806070905060d090f151404150b0f0a06080f1003080313020f0405010312260c0c1005090c211209030a02030a0609060b09070801030b 66
    0x1520300304505440040c01c01c0e03000990210b011070800040560000403100c3c03040d615592910180f9041404100282c0e01c884030340303d00f11303499000c00340100d0700854410401038030400131480209103c0315004150f600c0039140103c1720f10700b81d080002060b01d4410a29008010700c0e0000f56103923000b00001c14841c03c010303109812101d869070120704240c00890f210301400918a082140f55604050300000070101d0200a1507480c060012030300c46004c580e4540e401900c02020200e11040d000081003c54409910507a103c10300c86c1c20f000801a0807081d011901040c6a00900c0260620b00c80c000d58148080c2c0404020500042c0c2d03131090502c14044000c4011544100b4070040c2011021140c0c1c0d000002c154510a0b000340f442a540e100900c1c800c1c0c003044000c034001e051002ca49040c4840a03030005000c564040c011624490010780d428031001501a201305400600380d06681005000c0302c0038803400500030070801d000d1003007260700300880d14110b030350013110402e0300c2d501c2041e00c505c10f244450031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 136208579 1250 136207329 136207427
    0x5606100c05120c011821030e0a0507050901051e0904210207083d0b0d0c0311040e0307060e03070209041a07020624060c030406050408011407 62
    0x1520702d070358920402440f5444640d0000d002203118041a5810702c104040000c001c10424814060360303602000103809040c05a00300026030000c2840214206817500200701c5594000f084140100d192160010b4050901651184c4825055012807203e0144000c000c0c1d00c00e00e40c46000408210004800031a000b0740790300464514281a031019556045c02e0141e44020b019400780501e0301c201a0014000c05112000745015042555041007800300c0d410840d069030f00c1d1100d0b000099525602082001e881c440c424204819207581815099000b00c148901c1c4503505019542c144c11000009036064141c010794002005c4074181c3c001e0b46188079400000b901305c55003008010500069104588608650400540103581d0300380c4201d8482004503114500035040d0b2046094020501003150380c006009400c0ba4034040000061902d50740151b03100303c0010b40c0014061010582c00e000d00f0750041410081c00703040f8141590003410700c49510042d13000000201c00c1450351944112840303002ca480c8950 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 136209829 1250 136208579 136208593
    0x1513030f08030a0b181303020c061c050a0603030f0f0912030c0303180c120c080102030c19030203041a0c120106050927060603045606100c05 62
    0x30741442150021124403103480d2400d00070400900f03005c000d5041d111176090a1500c291313260074400c0c0088040c52000c1d4114410940500ba541e1100c50041160f85250107441507110140d10b40c88055403030040085502d541824810400260410007a03080e148007030a12200742c400141044030a503041d5484400c8480c01d02c5d00e0103051503080607110760320a0107035a0602204110804040140b90b680d9002404586880404c01061241220700d0110602c0303444000e5840d80d0f1025000c0c2640c1003a208280150800601c1110102c4900b48581000000b401c042d411440d068841d8100590040380402c8525048800901d04890210450320001d00206c01c18169503103944006003d0b802c131400c1640588030398009400303c05610103009000320b014130503103011a42e80e00306000301500040d00495a4280d5502d1508100c6420559a43c000144604c461011451010348041c0d4102900d009542c1d01c507502c100900c001c9020400c1c40d4010340c1510584450001a241251b144002120180184c02209 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 136211079 1250 136209829 136209833
    0x1206030605010509012403020306011107090605030c0d08040504050c09030d0f03110f030c07030203071a0601200a1b050402120a060b0a050d0b0102010603080301270b1513030f 77
    0x340c030003416204151548244d580c0c0315501034811865000a800010380b0046408071464480c1d001164860300625080c68200c0075581044d103001c0c2543c00c281a900d4a0f54001d10050a0801140840c220100c640b041105000d072a00d020520481c000c003030145849500091032002d50300111091580c0141c111000950241c4008004e40100a0362100003810300000c1060380000c002905c181104a00001c7d15545900444000d50342c81004104c081d400140030350f001065184189582d212800c0d00c1c10011031400400043c0010000c80f0300903c80000d03025150000c2a0000304840d00c90303449031276144c120381c100920340c181c19802d0707001c1e6521500014905400528104683d4040c2034405001d1001c281c6172070112904e400307200c1846000230390601c40264500f010303400c41291030301e041c000040d205440780c580b01459402600082680400b01c1e2503449484000b07070101030000380111040021820040c0007419425808aa5208024000c500c0300000b0b0028250600215408910560b2160300d134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 136212329 1250 136211079 136211081
    0x120e0312090c010f0504080723031c020c04091211100f090212030c03030705030a0e240a060803030c0d020c0304090920011b06090210110705010c08040b030712060306 73
    0xb40c4035074001140300c2c92030300119010b40150741c141c600b07400140c042203041603140c658445120b04640b014100903008600292014485001e00d01180110f44602008000010303207006101c08400b80210b180064500101300c018180d1100d90006141103c085000f10791035625040100c1410540035240144c200025030300c82c0c1c0030031109072003920b40031035501a0308080c079140c0c02484900d100d1500300b0000502c20f50f108900640d4046031105002605004000e410351400d18040c4518026009440850000c05004403405600c80da081c44240821400d00c0c2b403144d1a800003504116161102049030f420200d055010341d035846052600302c94071140da0341c0e04403025100350002903c0c1a555540d02c069007010783c5030800700e00c02c1d06840c1c014050800396801007a0111203103094034825a601d600c800141e5a035002c8450340d00150b03a44145011900306210704160b11644124188802c5e0000000090062401d440860b207100b0301032912980d40d01d405540c8480da1230140d014161402e00040104051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 136213579 1250 136212329 136212343
    0x5090a05160609120503030a090311010606080a05130201020705040b060408060c0307090b16030f090e040f060c05040302090c03060d0b04080408010b1002100c030204050409080d0e0a03120e031209 86
    0x910f944100042d40c0d24401c445280c80039040150284d0010000502008000d070000c0000c184645850748992a038210300070308588442d00003400192000c1e06000181007140541d07a0805030f590030741c8104404642c0040e6a030708003449028011500d8001b81c155950f07440d03040d10700604880c0c0a5511502e040290841203a0040f00c4c0000804c060f1300d00810843c400c0c105466400d601700040322100030250724240c80c1082c1580a1a081000d06200883c400034802c910501403846131120f003252807400d18080c2c042d916a5138011082290038402000560703034a40509420001c02d0155035a42d40350400803c0606280388000703042214901c043c0001c200c1280000c10484501740b0080040e200e0f100100243d48842000c0c3d1401a40515443d004401c03e0b90b200c2c100c0c290b85805c0040c6440d0ba200040303426103014143c15142d15001060007050625217000e24684000240090415125282c0c2c029180b0300b050081808419940d04c1403011201c402c104481603908118048481031801100040e13031566 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 136214829 1250 136213579 136213589
    0x1d10050a180f02100f02070308031b1c0e0d020703110d060507021e0c0a050103050703240305010b040c27030b0c0304140628091401020307081302100305090a0516 71
    0x2a425070025031340c840c01000358403807295805858014511f40300e0640d82e4001070210381c042d0902e5240201d1403a4441c1c0140144d803031900380c01d4181f003405001c44c802c4a100c170030007054582114503800c0c103841d17000c600801900d5000d21107400c96011000491034106038110700500940c42c01c402e1060b0581c00088050b64070ba5110340d54903140305461081768445e10218140390304540003a409202e01c3d0b0103504225401201031500282c1d009011440f00000c2c4075006802145510718001031045c01402e024080766000240c0307080c868054417180c001c00007002100100410500d0540d409844d00d00f401e48480110b4210f841d01c1c0305400d000c00c92022590003614111052a281480030f0055100400d940307109801d02c1c03900c94018214074519602d0f0282c850100c640c01e81d078076602d00e40060241c4000c40d803180c20203000181c491410342805811280041d1003050041e030303801b624a0044e954284200c00041c80f601e000315058840302a06d0f0b02d080480c2000600d80d0041821313200e0f02c0c24003201e01604450b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 136216079 1250 136214829 136214839
    0x5070e01090b011b0312050f0703230604090f08130f06030509250b0c01020706060f15030f0b060d15061106010e100b0301030302101d10050a180f02 65
    0x66a21141d003800c88581800c610b001c20790703da1060034a110040c1e400319000d0b0003400c1407014088000b107900304645084525042d0300e24001c3c280900f81c0c4d0301d0b00c02c54440600303800700300c0018600041010004503000780340030b00c5661100d0107002000500094540c2990f400909203444440c01c10f1005034000b841d000c0d001800303004030b030002880d030b11034058680280303007010103032850701c900306441840d42030803441d11520402224000143ca030170000c02014540410307000141c4820381441e10f8415541d1980c400c10900407400f80501889051a090014003201410006152084401d540c40541125055203070b0000c00410030b20180e99071904115070040c003d00c1d180701030903183c1c9829145000703e00c40035140d40d402a4010300c410011402070b26046800c203142d4040b516540c120b642017550090700103c0042e0804141b0f101110b25a0103071481e01c1e011483c03c0d41c014011006c1099079031185040c44021991100040360946809901800420405100c011107120182c2020340c608185404102c0c014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 136217329 1250 136216079 136216081
    0x302010b0d02090615160503071202010509061906151101050703060609030209043008010b0a14030601091701091a0402090c1c0204230a0e0109090602040305060405070e 74
    0x6072604110300c1001e2540101801a180c4921051086a0035101e00c5403a907080c0400c44003421080100483e05a54814001969190040d2500c02401c0302420080c0056a06100c2801300c41080400c003194080305040701c981e04910b42c1d0b025140a004990312500a01c1030000202c0d162940c8010410800301da440024002c0e030b1941035086080701e0051245500280c40c40c1010320046ca020f40c5402d40080c0a5543d0011084100c01c04103140d4640c20982c0501c1140c1c40700000c80070303820081082c014440741480504100c1d520300302800202813250540c1003000000009001c80c0e00600094001e0000c0280b0403003014804400c1600804180c501664031488078603200d0303481c0c29050030680c4aa40d007c4d040a880380c070780000204007130300b0260002e91040501154041c01201520240c80240380d034040c80620342c0741c498000b410b601c10f0450414050042030b0414400300d4509120181169500c94001444a52a081c440024000da401c010f006026080c00d0106022001030543d099611000b00c060071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 136218579 1250 136217329 136217351
    0x140d020c030309010c0606030204050a0624020a0201080414060403090f0e04020a060c0314121b13050915130c02160303020601030303020a0509030d0c0506070c02090414070b030108030403030201 85
    0x18480c0c0100c80280d150784100003100b81c0b5485510101061131042c500880c50f6612a40040c080d1442240c10300c080f559541c904014135004019050400c00c00801098424035070688000d44601d80300c10081d0501c1b088101190030069503034003140035001010192000c5090500d8000c00303991040c4a45103030701292000100e5100110313032a483c01954003d20540350f2500e420410364800c41c07400c50917014040d05034204405e81c0030200050548400741c03c070850503890040b00c10010b1b81c000d8411050400803c1c85002190b10300c0b02080c0c03007611000c403800d080d503503a0440217898210401548580041441c01c038018480503e400c5402c450416400381c1c0c402e94009080120001c0c0944000b13001a0f20100c0100007181c06540240404106494a01d14080040d00840c0c40c00980c01d2410b40050394214486090000070700c00d02c0d80140c2c2c1c918000e9107a409940000d110032101400240400d0415403051540c0031080040400a0070000d00c1c0740d49942c0d40e1486540c6a411a11054015509249078181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 136219829 1250 136218579 136218583
    0xa030903030e0d0207050d08131404050c040b1b0c030f060a05010602061303051e04080a0302070906080c010e040207050105040b01080d030920030106030206190e09011d07020309090103140d02 84
    0x4203204071380d005003c06071415042081b082d4100340141e907000c001b0003240200c80e4032200d46001a0100004e030300840042e030000e01040361001403039400e000070240000e0000070b0071013040325070780701c04251300308003040a01e0440782c204807285805c45c1d03161284485031002800041030702849001c0031001000f03241c0c1e039281d0070703612240d048441e210b011018500000010380142e0160403840c140c02c41014004042c190742c100340b9030064000703d000d64030420302c20303040550410100001e004d4400e014440286403940ca550344203425547c0c10b050111600d068202a11942e040c0c80c400340d0044000c0c051401c4c82e00300700c1312420081c082e000c1e00380280408062910b000b0b000c2c100245038092a1080002c4800d00c10f82031500c2c50926050f0f142d500d940000015036510070280481d07081501d0403a000c05d04030354010f0100740c0000881030140800c0c0004000c0f40c0d83c078002401c03001805c1034078280242d0780e4140c1203003907100e240022584400c1002c004002d01c88040401020a41200c048501200c4600e0b010390b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 136221079 1250 136219829 136219843
    0x6111905030304020108101d0433020901020307080304060e071406040510110106030503131a16020604030501110a0f0e030a02061308010501080a1a01030b01090518030a030903030e 79
    0x203031103540100007283c01541310385141c6500249074800c6e401c2d010388907504180b418402c01c40c0040102010010f01060080d2044604a00e5200c21a5030140751501040302a544208007020300c1d0b115408a2980c0c044e900920413500600e41c80241d075566490103281280040819140c107011034428204041880c010325001070040036030041c2454100381c50310f01000403440d0740b1560b550801883c003174242c3e035141c0e00b4042c41028500c500d010355284c0007003800b0054540e00d00e1b0300c101c0700c0b4500100f51300084010081100c07800c6405800e034020303264042c00481d2940c800c1d030b4001403040d880c100300c500001c481200a0280d00c00380b555900c180c9110340d0f5048aa0402d100172613580b43e0000c000000c0145001c5001384000c03140b100414081558a00741c05085038000d911411194104009500421a195002c0c1581442207800c1c00002d50541d202d11203070780300500070502c000750354802040c1c220360100c0c140c201c0c06440500f02c076510320032100c006014040302941280030a040451502e00c0d10004910307a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 136222329 1250 136221079 136221083
    0x2010605061201140a05090708070e01050a2124090c05030402031c0e060408160506121501020a0c060c020a2403051305013207091e050a061119 63
    0x14180503403e20084c01522201c502059030f03c9010020006950b0312030040d42071044000d030300e400c1100c5c42c2c580304c06403041800081150410400700940340c3c0c010b8010741079190064054103104800c198902401006220180700510300d03202c40c00402c030281c0700d10075010b4160390bd4280148091406036005480074081510001c2d4942c2180020040c00301c034552652000e40801d03e000f440c105800404294a5480341e002100c0e5904101400a80500404c0450300285025502c0c5481c0400d510840521a04050301103041340ca848030143e01168420402044036035001198503403444c3d500c0b0300160803c00e20070003c0340603000c10b00c8002107a01c0020000f03101522620182704210886140407002040000c0c0f003c00901c1c015000c06000c00e03003d01c14249007085400b1241c4009065095040c050301d20110345800701401181086426a8094000011909813101245000220755145480762010f078002c41e400c43c1304000000741a0b64004684e20f105401c090075110007800c0a1964480b001d00c0301d40c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 136223579 1250 136222329 136222357
    0x803040b0904020a140f090f12030a0f230d0b03010606020309010507020d0b0a020405130603230a06052d01030804031b030b04030201020307030605030f0601050907031404120201060506 81
    0x11640d081c1070f002001e200c5040c2c039050320041c8160b0180301c101e803c103407410002500040fa8012031403c00c22082c03407038220200c80f26400102c3c1152000c0d52840303186508410401400c2d000000280502d086000c07071303407621030204191540c800d40b001140d0855840c0300a500e0a10254011506040c8200420b85083e640035500d4102a18015102c40c0e004640880c1c101c000300740c03c6c0e00410030000286001c0d4140c10405680c0d64904010080050018132104680c6403501004000003010320400400d42c0c460f00340c0981c45c40d0b4000c604a0306011616502820302401c250070011905200445045820281c071a4554010000c508203070030780d0424080105407920030070041c000705610307443c20160300c00c04030482c0410075181d0342c4030340502500351030072000f6039004414491181d401d0b00544015110540040c00c180d00d0018200b80c0d6900103110f03440c024030112000c0740202d0305c0ba4010121041598131269564200740c07511125115041e02450010751070984046194905803040b19440340d10340c070f4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 136224829 1250 136223579 136223587
    0x305130308010e09070f08060105010201110f03190212090609100c090512010603080c15060411031b0c010905070e100b270d0b160305090d080a0e1c03060803040b 71
    0x51590f040c100141035141103200f2228002214241c151200024107501009016607501d003a00280c29228030b01d241c40d06000d0240405592a458003090704d500912b0000c450450134101a06c103402445050400030301060030004001d081c1000050302c1d03025800e03140c06c032400c43c40d079011040101c41d4859010300c001580c405080007145071104184140703c228074000650b20341d9941d5130003180c0d0f205000181160300460b0102c00c048480401103030303005a0903101801000710b42d03501205940f00082c0b0042032129050b50304032000888000707480d100084030380200001e224034104603039652a207100d0030358503030942000180c85085294411088a130100c0310181018405030401d100d0808090280040d05961a0b50320002d41c2d03041220b0f400e90380540044005410410711540403080f030040060305250401040c0b20074031000103049248400c80b454134800c2502d0f05903403107010308502c4601e030807a4803d0310744045600001006c5d04243d108036841c00c005a540d01c0180316200d01407072040c20b80b0524280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 136226079 1250 136224829 136224839
    0x807081509041a0420031501030b0a0635030712110a080f0408010c031509090c05030105090c0a12150218041b03060506130b07030c060c050a030513030801 68
    0x20341150800e200d0125041d5400b0f108802d00d01d8424101c4041d58600b0455107401c0701100c0c00408080060402e40150415454080104201e0036040c8802800c802000300064600c01d5158842006080d4141b100746a900507081c0d811415583c286190b0614144582c290451440c0001201c441560002408007000d56606007aa2607100c89041c031590390080800000011703105400034038007003186201440d2514100f03036541e821904886200d10605151018440d420225850010b04840c40b5000100f07040241d4502111103003101c1d88103a8040d820803050001501c40490b19411102c1c2c140c50321350549030358980d01c00c0d0300030305842c0182000000008a04100b51107070013b041d0010240d480c64021040c140204d404c40d008425000c5000309213540003482c3d2941401154000c200858001342050350f44444600d489003d84075110414900180000805000d000724100c0d143d0880c42c20401c1458600c000b0307180d03501201d01c110002c1e00d000c000406039641d2562000d110350301951506503580c244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 136227329 1250 136226079 136226089
    0x7020f1f14221b0801140109020a020715110304080a061404031418030d090501080a0209010e0f03010603080d060e0105151b010b03030406030905010e0c010c0605040609020d060b0108070815 83
    0x1903005032000000a4482009800081c160070f0007030101d07400004d00d4070800c091604c070101041e0000042c640c010000c1e90206640051154240c41c0318021001c65034a464101365060042d01024000030b00002ca4000740b2400046801c004590144c5410300c45102130909030369010304101c2c0d0007000310300421030f600091b01c4004080c200c1100303001c940c00441c20b0100c0000c1d1510070100810340c0020b452003800c0c82217580c0201480d4010103040b4003513013056510780018003290380f0b0b05c208074040da00c03210101403159002d4218400071034200010554038100420140f002c4d0035903028a1710b10b0344140000041c0780c2400c416091401c00c0000d0784030f06001c15000078054a1088058260340b0b59243c081131011a50203200600080c01079840001e000c0175680780141c01d45424018880c80ca03040050303011141d913003203c0865811a03100d04005002e540c1c1d46840f0004041c000400780d008007901c0240000c00c100340d480900c2d4120241c03030701c19244d5508a422611103030100d0f102c00f280207130b01442000342e040c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 136228579 1250 136227329 136227391
    0x8060f0a0b1503040204020904090602090f03030a09060c0c0e0c0a0e030d0c03030b0409170c07080c010509010809030d0603030314060901030c0b070305120f160c02100807020f1f14 79
    0x1001b0b002500c2c0034a454006000c3d02c0500c1c8060303400a50000d00a04180f40068548003015001e402841c01e00c1c032046800f504605c035603c200b405003d48660381c0400c02440441c0c220142040548070700f49170822841c0e40f405904a05009804074401c404407440314038002030341000c0400d2594584819011565084028000100c019508507403604c840f01c0003c0c038002c080e05821311581c21820b8480c668401b0b010f140807150b60018000c0d07000036240d8071b0240d03032100032580500000e00741242e1a40f2201c01c0c0c20316612a080e42ca1603141e00e0300201104043d410303080041404030001c0c0a000c05d03200d19003001485402884024590100c030001049011040e5026004250003810a142040c0d102c04010f40a01c00882d189800b00d080d90082041c0d00020205071030003280f0314a024040000c060780402c0c1c2240c00c03c0140403d0200900000d1304603403003040001d1840345940243c4068028406500041040f8441c01c901c03080c0c00d245c0d0020901000c040f03802c0c400c445e50006009000607180c00c5c4007214417 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 136229829 1250 136228579 136228583
    0x31303021009030f120501081c0207030c06090501090e161b0812060301061505031504240807060c0c0306020d02130f1a030702100515030708060f0a0b150304 69
    0x2412005100d025010701c00c80d901940252105404c407040b6104c028000748000c22040308079881c2100600040c40e000842240b000310186640d40c6217445854107030700d0500260f000600c1403120490100e406030b882000030080306d0080e03d0350501c03180c980d0202400100c0c102c0300c81c89402009000064018031829102c035003042010320800a40c509501d41c00384a034003402c035140d504022032007484010f007002d1141800500382108a5103080381c000100404a210142643c810340000300307e000350316581d581c04130445004003031070702c40b4a80e501c040000a0b000c181c41940c2d610700070300100080d414010140d041003194025511420700d42035544510084d00140e052248040e401d0280c2881d410304940340d50050420075149240040ca0102070080309850100200d0b40e1b004180144014070350001084900c880701c5410108059659261418805260005041e030500c0b403040005030016012030024025a4080c10246482d40c0f190300d000c0c142c2e1001501d081d00030164218484450410001550300700d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 136231079 1250 136229829 136229833
    0x1110a030819020409021308070515030a0f020d0c11010b0310110f070503040f080a02130c020a0209131415042409080301090c080906070f1101150e1b03130302 70
    0x1074007000c15404907013054100c015095800100080c03482c02481012000302603400040507214148408911190310120030403011160100109100c0c03025a0000c540c10354500c20119112149907c03c0b001524542c00c1c15004644041d04d40e840c020818010300c90060741c060f0040c0040400368030050000e040040d28140e040000303008142c44a46030a0060008030300580c01140c0325400d080c4109886041c2c0e90040a0950150b111800180c40ba01420640c407014440c1c00520a00024001d9040620071a0000c1d48032000d01c1c04c0042940035003c0380348a20b07001c0e041500901c0d0584502e0307036440451403041c9246036511000500090304914010b4031204400891403017061724005004161603250303034210380c0d4036400300051110070602c0c0701d081290f951034908030f1560b007844e404042e19004060300000c2000301c0300d00f040042c0e90003800504070300e01c0010020090001100c0c02152404620701034600c070442450082140c2c081d6413a23007040c560300c001080c60f10b15142c2d104004500040f00e5412010341c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 136232329 1250 136231079 136231111
    0x120a031407050307120503070215010509040809030a020a0b1801030e0634020601060e030a020a090e0c090108010f0506030318040b13020a080906061c0809010c0b070509040b01110a0308 81
    0x1901c5120582581d0300c05d40c0326141c9904202070068140b4800c415003401a03262140100496940c6041c03ca82040c1c00c80402c69a484202d4080380c02c002c0500e0010b908030f00e03816030006000003002c0c000e10028401c03100c0210b4611181d00110142c988054400e10140d000c02c0c00f140c0020010300c100708241781c0c108000c4203c1d000740b50382ca03038203e0180d490300805a086600100312094001120f428581011006040c0500d000c3d40040c6001c0181e00454000582d20341556461f07031400c02a03014250070040c0300c400a9a5280d403800c1c087c10a40e812002d0060904010a5146c1800015601d8484008528010700002c0806010040c49407801c155408640507a0300345003d98188001c210803011a03803145598a86000c58629014010700390714001ca800200701e180d640191000306500d590701c82c0c3c100d55600d00300c100407214113500000252a00080348180301c51160403100410448005907030500000307600e072005641c01668105041d0070ba8218442d0760001a02c506040c2e9070000c1101911404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 136233579 1250 136232329 136232333
    0x14060c150a0903020712031e09050d20060403170c030f0d0b0f06030601140f09031903030f1103064b1f12060513020306120a031407050307 61
    0x40c0d920554004075041d681d80e024900f41a8144451005082111080c80b01c90059642c01040000f0b89031116405507000c1c0442c03201140701d01085001070600810030800421681441240244107c92032400e600b00c6c8036040b503960610300c059504a86d0001d0300e44140d9410101200340c0d55200e81100b50b80b41c0001c110806e808820580075115400350701e040085d00c0e040440a0090b007469074011148103040600800840f82e9110780b0200d00450307002c12082e113072484c00c1101c405074022074052960600582451020040003c001007008a01035030701802081c1c2070240342c00455005500089454100304005200c9007010600000b030040d88205403114181c521810100ca2982890f1980605c0c0480444044820a40b4282048050110303a40203100425804480080c10286c19100500195000c1c100d1030302030716485980213160103048140300c0c180c500c4c1400000d500c1100c01600c240403c3d11036405160f0000b5920749401e40c5515494804052550b03076140e40d4106500c1110b40384010401000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 136234829 1250 136233579 136233613
    0x903050706112b0c02010e030d0201020307080f0402060a050c100e030306041406131806020304030210110a0e090a0e0106030b040302010c02030c190609082205060414060c 75
    0x14195a40c0b2514505061100d081c100f003000700512121200042900c2002c1d4940d8120101d01651400c14049403007141c80141c0344024500c10203a03042c083c0c046094603458040d001188034040d0340c0e540040c070342e403515a41c119000007550041c2d0403410a0020180942c0290004c280d110704ea1003c0311101c0f2040380901d802d13261756541c103881c45e030800b001f03110140c181070040c07a14075450307203003500305a241441c04100c3e810b006000d24192079031903028401c00c2c48001086100c0e001d0f00b08009540c2e0745090b060180d901c02841d680d010b035035031504440300c5c000e007000d1055880c1d0040a9a810080075807000800075001c001a000364881e60365400400740713032102403040d4070081d80b140e60031303500038902402e0103421a00840c0c031090a5401c00c00200c100d05e0008125101c0101000c0520b41542445040c403a00030b1901440c01000450000b03030210340d103213803107800e80d0b0007100304582c6642540c0c54a052203a01d00582c420f14070421500c520030031141c0f609402922185030908125640e1801c0e00d06551 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 136236079 1250 136234829 136234843
    0xa050709050a141519060c0f060b0d0302070f0b07080d0e0c030a0b0402151c02071104060e270c010e03120429041401050904140c130e010503030712090305 68
    0x1842d1358100f00c04591a6040c0300090950301d8089404240d10985804406400005000e40091101e286511036004104031903100074025113001c0c150001d0300505103006584c03801c4c01d01a505c0d500701c00402c001070028060703007141d012a500c0f400241c20701c1e101519480c09001c5821294050b030081d100a400b440e10700700050300c00c841c0112407628150601d030040c01903c3e07007040c1000745840402c01c20745210b1a135a803940078840c0e8049400596074511801c00503020f4880a0460782e000741014000240c66140c4e8541303034010340c000c1400c0590b009615610382c00700f5003038044070105904000780b00c0c0059030003810002c00c0c044000d025a000e2100d0010420740c030f035206421502800c03045010041c000c00b00882541c211483c400d04103840c190a101650b032754100c41911560400000007050811521950090040403606003a036070303010301300b03424030000b150401c0d40c03c010700701d42c02c0c000007803400030080ca10381c100c0344003402940c58041c49403550000a0204030071081400100c903c000000f4070100625 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 136237329 1250 136236079 136236091
    0x10603150e0c03061608010b03040c18060902030a050103050c040507090501230a09061b02030c0f0105090a030c05010f02010204050915210a1101030c080106031d01060905090f0a050709050a14 84
    0x15003800b004505c0c061300002c01a0420b084841c41403042000160505a9131000c0c2d03541d64140020254100e184903024000e690000301070395001000307200c0740350383c60b030011411780c1d10400c140d034075288404040c00304540c01181d0302400950018070401480d40602c00e600d00c0b40305003220010a00148402d03420060303010428440000f819584100015503100541c180d1002000e485101c5182d030316000280d4408000c0e980501c500d00e0103904200c42c2e801441210707212503010340005c402a5690134106401c1d1030303d1040701c0c00b1400304000542c4880c410b1080301e040c0c4130001c104882d103440e032420940000e8110b0807419041100342030a0349a0607054207681850320b40500007044c40c48804c1c9402d41542c460040e181d4103060030200080125900903811a06440c0103240000e403204182d42103940c0c1c3c20240311070610f194a05100031462040b5600450710031030340c8204940410b179019490640d9007550b148040d01c1a04000028050741042d5001791b034004001100116000d06000c00c4080c000c0429505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 136238579 1250 136237329 136237351
    0x30609050a1119150e0d0303050108010606030e0303130201031805062a0a2a0b1e09070905040c090606020d02010e0309150d020c01090f05060603010603150e0c0306 72
    0x450000c02101280030524840709540f840b40c411120340740d1920403c4207000f6058500c13085000544454818401070b02000801030003034004001604020300180b03002c0c02000d005508140d404242540079009813000c0c4640e4500841c41d40e42d41020600140110410481c109900c03400040b06038900c00b40c0d122250f9000c2c001070300041c105144040c4108404c00c400c600200c0c0340d524000c40725580003066a9442d040e604110342010171041a0a040e40070070160814450032156071a024003211803501407144030240340a0341d0b60703040d00d4500200c007002200c0040f681c0d404040180b2140e00c0e1074114540040c81042c00746202501c4400300002d440c140d400c2840107a0240c290b080c11a40e0902404500c41d901401461401e000c90021500f494800e54441904009c00244400010300319030484800300d9041001b001991118503190042c2e50300710303e041d200c921485011070750078607061148030200d83c1e201590030f180149044550002d01141007809103680140801e11601d52000c1c0003c500c1090310300c0d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 136239829 1250 136238579 136238593
    0x20702090c0d051b0901030905070f06020106050108060303250f05011406040b0a03030f05070201020307141c03020307080f0c13090e010c0c02060702240a121a090c0a03020403060905 80
    0x1c0900b00311007004101011101c03080e41d4810aa102075022102030040a10780410212840e0038840d2070502e03981d0200d400c0da00c3c00340d0b0000d90b07640d044d40142d0175514241c1c2c1c1d20300341d030710780f00b007010344d070b4003e15800b441c034400b0351420201507444804040c695144900c00016154005031a15802c503620310500701d41c50b0140d80200281e904e4640300e44609070104035800422181192401410244e00c0c00040044c0000052104290382c003c006480b806a40500103180300d034a800744854640d200450410301e65080d40c1424211107000740280d91040407103a540702803923950201410b41200015110f40c0d100300d01002480f01000c4e126070070801800c0c07960f80100349043c12001590031201c00d04480010400803151000043e40d074542204d00c0fa40e01218101c00858150f008a1441d031a0320090828450300010703020001500045441c080482e031805c10803c0c10aa081c40c1400c8060710f10000c0d5209003010001040602d266024203461849841d005050541700d50741c92013120030001d0244d40b540c0c4188 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 136241079 1250 136239829 136239847
    0x406020a060c03050405120a05160c05100f120b060408031303030801090204030c121406040b0709240c050f1006050a050109050d1401181202060f060f0d0501020702090c 74
    0x3004036002c1d0101ea20703080007145000d4541d9603c6030760141003500c00b4480020b82c0f0616a00c00c200b40e03030600d0010a940f01c140e0046160410219002d0702c41c1a0203031890550400b030342400f803010508461a0f54a509400582940e40d0700001c10201c20080d5000c17800b4000802c0401041000c0c000c4a6141c1107032803802030441c140074044030b005034003d0407030384d004000900010704950150011a01d2105100c580d405440c80c4c060258078905401c500c1622a8174100020302803112481e60045540740c95015079151100355403244561800343c03c6420200074058104e0280c45500c504e8800c500640903142c3d132115001180c0e003840308590062001c0c5407604000d11117450244250340040c5001d00380a00000e181402045800380c5070007008c0d1007050710340695000100300b07420403103440c1076000c2040400000d81ca0300240f070781d450003000310040c45014001828144588540c2e80038890083c0f1483c100314202c0308110009090810450380b0755024409800182c6030322007424010320316207140d1921a4040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 136242329 1250 136241079 136241081
    0x90c090b0c0d050913020a05180a0e041b3609050a0209040c05041131050d05120a03020702030d0206012111030d03060524030a0c140406020a06 63
    0x2a420004900034200304490503041d0015440000c2649800c0c107946900b10380340012907103003901804a40c0d050002a600d11456440707002815120f4400c0e403054103001e090382c01d0106a141364003170400d1001c540c0011a0104540a80010590039030480a200c07843d240d400048841010206040880703200d00499003003a07051800492010144000401c9114070030380b11140d8480d48020b02900602c0359101240a00c209240c54801400c000313070050044040c2c00104a05641c032a0609501d2000c90100704402038803101094454011030110302d40c01c45042800700180d0750135102c000c50302c40c86052404501c0d6920000035041001032070320016141c40090050505001d0154600c004540106005224142411040001404515403c540d0b00001ea02e0248024414414459810310910074a499069890303044401035440035501c848807100e0596403419184044400184014420320009804805680c4444081d0050303242503800201c03031014495850b0b201e50040320060b08442c2a810603c10a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 136243579 1250 136242329 136242347
    0x50105010f0602011a0105090111030f0405010801121a060102161707060816050f070b180f0309060909130c060c030314090a0308040222050420090f04020307030b01090c 74
    0x590000f402580e0307010417480400c000d2803a80f1030510101003481d180c0e603449820000080149034003140c0e903985565880030041e4001e4400c050004111030004940c0c1620301c122100501d0b40007075140c15510442c4113801c0140001007181c2d045214050103183c8a010403045000105088000c003502000000010790a29201e40c2000090185990070700072240c014031981c5815090398601039460340b81803e0741040c03c0c0702da1140035260000e00002d0119070b954651f9880000d6032880f00302c8100d1404907100b66100c2c0540060309500c00710500000c0231324181021415401307103032080102205046030b51200014105500030800043c0c0310103100f8101901441609200305a00c001e204003440d00140c01c40e542c15410000400b081002004981152952441c403503e521049425041200c0008520b60003014201e4054603040110030131400d081040700b200c3c240c40d113004ac240340e0266039900440b0506840151040340c041c07050b400d0000104000f08800e5001c0c1c52382e148081110403441d8402005000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 136244829 1250 136243579 136243589
    0x4080d020706020d080a0204030c271a040e01150b07030905150405040c03060e01060215060405100e040c03050316060507110607030c1e020705091510050f07020a03050105010f 77
    0x71118100344212034000440c1030303210b82e051402e500e15039a50700035000070f4000c5a1004040170f5001102160130300002002503c500c01c0c001c40420084a402000429515600e07040340c0b0300c04090ba12500c01c0e09080d0010f688a0341200e00102e500252040550f00c40f9500e070f400b40b007465002094400815511000800040c2402c4030850440044401c8405140c802c6104051140b969001d651308414040e4010200902c03030103046901315a0b4503034019458048480701802c001c1c00303620010300a40350500c1458000d4110781d090751a000e00b0003594030340d40540540152130302401400000001001003004210402e0340401c4141584c1c0b40d45010025264081e14150030b10000c14402c240d00100081d00c0340e8850064078000c07504a041c40307425142c0282c0e454502c040d001603885072503441c40d000110402221801d40d56882503654100c1c210042e00201e1082d55840b400c8110711a00c00f91040b009800006000c0760100e02c1c0c15901c0e13000914500a41e48101c1d000d944036001000307048003642002d0001c3c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 136246079 1250 136244829 136244833
    0x21206090604022d060913090503030105210a06020c0304080a03030b0a06020607020a080a0e0303160506010f0b1e09090a0501051309051e0715050c100905030d050604020c030f04080d02 81
    0x607135040b2502070780b403040c400003d010b4400451480090b54514191110320014500c00700440741440c20110b840341c0c42402094014a2a07640c4100c4100c1e000311340d5904e01100c40b000d1318801741d0b40e6032020060350189018010b00c0c80288004126070a09221400340c2c030303209840003c1e21030310100903c006d10b241ca900c044195001001004640c41e004103240e0b82807544444c4060f039910500e20203039010107a451041d509484003145001070019100d1503003c0150149040700d040d680e03100440e020000d5140100e01d504141409102d1118124103409060000001c0b0030b40d0401d8060004203047e480c0c112402d10ba06515000100f01c3d60501e00c007141081e0481c1481031007403141d00e41350a0382e02ca040101811407030010520707103400001e0501c220b0b03000d0b0000c1c041c0b40d0806405241d00408542040c40002084d006592144510311107078880c03404500da000c00554180445400c00000400b03000b400c85070055000c0013034800364013082c402003009483c49010103444030305285683d8030304524511424159 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 136247329 1250 136246079 136246129
    0xc120309020f040b060a0305270a0209130f290a14060301050c07080d020d090b04031b030903030815040608070e0c030c0304080309010e011a0117010b090d02120609060402 75
    0x9845920444461200313a0070003264548035010b041d200c1c4049c402e030040308950941c2da03442d0600c0c03000c500300300032500071103451041e5140d02148028006034107500130071410b488220200052501b001c3c2d1181d8064110400c6a17580c04001040c0b069441250780d000d07460b03035442d0102c3c0d20950660300c040e0851802d500070000d0340b42c0720782c031080b941c851244041d04046c00450b811083c1d030503a40403220007001c644010b008d0300f084c0c0d1908101c0018213840441c0490548414a010a100a0900c080300e50b0942e560114039459a203050765100009000762600d00002d40401442d502c85015200040c40c1e4140103050307180ca00011072416400250155003584420410702c031100c000314083d0b9400c00d402c011103075941d44400c0c01e1280106091044078025500f40b400496844201c441c00baa003040e004c2e00c030020790101c83c19108105240c24060415445014402140d581c140500311407920f83c03000d4880f001b00c82001400a00e080d004540030f803006e90004c0100021401c1c034440b89a90901003150050003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 136248579 1250 136247329 136247351
    0x9070b030105040b0609031b10081902071a0403090612020304050c060306030a150606030605010509012c2e02190215040b0309070e070207030f0b06010c120309020f04 73
    0x100e20041c8900c51007151115185100b5560b20b0044030901d00c002021103140d500c3d82e0084081c582c80c030503091032003880340307080401006010702d080c0d0b40b0a501e03044c0f005ca1003003480e80c0b07420001d4111751425160103035590400360304c009a80860708e001d10300a07110700c0c0181e482c0c407074020542d003030b01d402000d0464010300501000520005180000d080c0407140740d9200c3d9140000300707240842010014110b1422141d004c903079441c0a900002c140d4032195030601c002600c071001568588502040940000c09140a0b802d20150ba207a0480841c070b116020540340c14400d00028050f64007030f819041c1c1000c40c021a1400f040b200c0d20382c0f907090040b5800501203604e5401c1320003843c01c4070401d01034042c9140104094004580b5011a4068050b024441d601c03820100100c0d603817003075540206100c2c41c5d21007012851040c0002900011264005d00c0070f20360080d03603550b2280440018100c035040c801501c43e154001036661590108003032176a900010f440d08039004108aa00742031040c1780c000c81c40e01e095814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 136249829 1250 136248579 136248599
    0x124050103090c03061a1003020903010c09031e0602041a0d060f06021b010c1a150a050f0609040b100206040c0e0705090f0111030309070e090c01020715030603050109080304020102060907 82
    0x2003241d1704020b0000b2940c12020055040516201c251a4081400403c0420f584d4040c0d0291000340342c16002003100501c106416510346000d80806414544010021455516100380042c0d131030348030303c0026041035035070140302034940008500310b00708201c08205003c1280d824403e910081421811811000d8900b810294a1301d4105c42c6400d00148003c46013070300b07a4041c2c10150f401c9680710345045414119803586581040c001d5803000e09040d20898200d442e840d00e0710a40c800e952006040c2802c080e1910100581c543c071180c01c054200361a121042000e6484102c40104001e413038014104034605440e14610f07080c03071600040b0600c0e07034100610000c01c0d0300c00261b41d19200300f42e481d4540c40803180c00503035400d800034072003011a1100000f00f0958a0021803040126400c2007408402925212112130700e503d040074415005034000e42007003043c003010360480032002c006414005422900d0351107190a441855205480e6184000b06000031540d0401c8196804100440500321550070000390310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 136251079 1250 136249829 136249853
    0x306030b0c0f1b0a05030f0706200a03020c070302130e0f060408040509060f030a06020a021b06090f01050f0408030316050c07060e12010f0507090b18150c012405010309 74
    0x251071004100c030b140f002014208015440f558001c001ca0b40c55520542c181c0700310743d1100c0801c880050030403800c501c02819a15600c034030740203d280e92070b04041c00380700214000e410124402c1071510a0402c0040982c580e6082000242c111910110380c0003601c407000c40c030b814406400c8e1000c81d8816400c0101160f65a03040e1020750344c0440d0b041c031b602d444806c001010a49008540ca03454000e602d00c03d010805c21707a0091044682d10f809641c00d450300111051030449043e0405508038100b0070180b2090b01c1d0001041c8800300c0141881ca0070481600769102054009811140d2180d10020920410400340b0f82c461913400260f240c103601c0c3c42d844003450b645602451141c10180316198076440aa9540c5030b4000003082d034404001c01404111402d000e016000c04c0c5c8802c008141c1c07076900841d00020210489405555911000c0400c0b85103409200c444205410400100390041c44a07010351b010a000d03201045440d50425400c111411109501c059880d51007a414185002c0c0745000040e5907801c0a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 136252329 1250 136251079 136251097
    0xd0503150f040e0f0706050703090e130c0801021c02030105031e24100806073906020a030b120a03141201120c060807080604150302100306030b0c0f 65
    0x64406554103010aa5a680300901c0a51007400c248040601a20025803034448022110481c0c40c20703a80c07644181e4052280042c05800682c60080600c105000700891942124075a9281040808a038484076580703c09508508043e9400040c841e810102c00708221411315042c2e02e04615551408000903603441021400c0ea04050019100c680d941c00244107070001c0101c090f40b0b004040e11650b400249000003102d884040c18803844010500080009074248600d42035210704034038074062141e034402c04152099041301d128242c0001e03840002850b404c04070082c820403015840342419174018060381c0d180550340c1c0c0070f03000c0d0140100c40c0f8600001c030100250340600303090480d54090301044040d4803420040310704180d051400000d5180240001c2000c2d00e00580680b980303940c07203040031500750406448103400181d13004041069072600307a100e80c4c9402c0e0380e2169000d80b690b07268049800074500110300d0002c265074020801c1404100b000d003d500250350000c4500c1d090a0580001590113500c4070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 136253579 1250 136252329 136252351
    0x12405120c04020415120c0f1b0f030504060806031c141209060103051c0207030b07051b030a110a0c090e0a050f0c040605040905060604050a0618020a110d0503 70
    0x45814140e418460700640d800090019540c1c0e9868010303080039945040d40c14000508854240c0c2c06004c800d00c90340f40c182025907134061440b004d550084a4400c00440ca0b001c906540b110814001400c50607242c40e568403035110261914a0a04098100c41c4000c0c4158042e401a445100d4581d01e40c0b00c24540d2003045007040581c140c0440904841c5004140311100481c2440b4244000468002580742c12640304d0000c940030802c0c0c0104d940249480d091443c3c0242c0e000c03c6003840007400303030712003287d0150241c90018149040440300c2d01c1d511f46403448588254000284548030240c0c000d240f403c1850209004028820040d55080000281840340500e040d42e5540146881076050040c0e0342880d400004444940311181881603e030b0040c0e06505100d03900d80b8100058074200f07030041d401360310340000241c0800d6072032100340406004018041c242080e600c020200b01e01c5451580c007004591808001070300c034400c1504c043d226480303c4044000c0b507406a690405126400740459502181c1602c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 136254829 1250 136253579 136253599
    0x703060f110706060305061b0306011409040216050706020f06010e04020f060a0201060f1a07030f0e0312040f0605040506070602071a040f0b0c04061d0d05030406050408012405 77
    0x420600240703688000c0d008011000107001c801d006140c3c1081082e28003a000b5518640c850b13800010340251340104002d110780c8240005200e5600405601304009020986c46203849992000103080ba030107501b0b82d491503180301e04088140b0004110b250f020700b06600052100780002895541e8407901481780100c0700c86403000107070031034440e89210223100d00040c0c00d00e0340b1003070560b40181c080c00340c0303010740c2004810881002924581e100a10617115200c102d41d281340011a850444010200c003d9107000c2c407048444030000c41d2400c008a810b0410100314070350b1610308204400740542c0721036016104201c014001848150354080807612425401a00103030341c1e2000d45003855159410000d800301c14036a40b82003000b48180502149419131007640b28080e99920582d0541440c011405a2400140050740c510b0098000e40050007030054001c020068608030380e500c4600d50745c0a40c00080c00608080b404005804007400303400004403c81e0310ba0b0203400300d0051840c0e5081141c1c0f0a80d0b00c641c03a511 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 136256079 1250 136254829 136254851
    0xa12090503120106090905070212180d0209070f0e030a0b0609040f0827010309150207060b060426060402090406020d0f09050115091107020d1a0a09060b030609070306 73
    0x40b604020602c0080210669441c000500101154810811154103100001d00b001d44042548142124048070300750410071071a00741c2c0c10320082d10381d42c2a084040c0201c01c00c0965103074116070380b08031420b55425070342c000035180040080070b40500d21802a440a04017000045042e060302c0e600c400245c03801c088695440c10009c516811000018005540005171045204408118407891802d17a00800c03911042d10401181181c002040241032040d03004c0100888030020740090003418003c13240810a0303029140003c41aa11590160039038850300c4210085c0816100345c1c0520060060000d82028a480c1d004145c8121000340000c044590000e5410b0703140c580d070380c8010b40c08150b00300d08001075102c4d0702c1c01070700a1403040c1c3e1241d0110460a40012201d5150007912800e51980c00024107180b0513509001c4080c4046408482c020a0b100070020b0508110003200d02c140714240022501e8005403c0c11f4044030001601c81e802a0845410411038075400140030040702d91050700025241214 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 136257329 1250 136256079 136256083
    0x602010c050403020a2714042109050f03070902191e0906030207150e0f011104050a090b0402041206050a0b0409021e030f0a030c0b090a0f060b04090b0906100b0a120905 74
    0x381c1892001c5034549600504c2d0000000d4046104030320030800c030009e5492400301d458840e0166408400012420482070181d4101001c9070411590003070101c803015a01c45420100740e80140c194034100c1180c045090302d03140d500807020709006480021603000340404120003400b55003d4001e020501d50001007030380402000c5a16a042c408403180104226400308040d1601c60864000380c0320f8a6090450982d100440d0301d0844d0f04840c401032905c0c0020f4a00071814000d40f40c04503583c0d0b0722079824840000c100d541c5500524041d80314202c000354a282c03030300d9000300700c5803030302c40040c0640d00c0c200390752005171550358203541d0b070403581541809001c042c8030010745000008844044103001d6070300d00104264200740c460704000d00c20440d01d0303000d5981d5030b8000e80d01e401003400907200c03d090788000d10104007580d001c45601078010f03201090a25060b00c03040130300001590b000c40558002d0b810041e619191101c0b180c00b4000d040805854003441c007000400c3c0040011102c41c00b141d44128202c200682 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 136258579 1250 136257329 136257389
    0x109020a12050a02070302010c02070f21050610030507140a1403010603081b0c040b150d15030c05120d0e0f03240702061005030a031223010602010c050403020a 70
    0x1000707400e001928000401c00007940100c40210095801c2c941c1c4022290300100d91101a0703601200220101441c0158071000300038400034504a45030408142d40c04a0404d1012a12584407405440c028620754070b8020305d4620158003681c1c0c2041903120801140d52080780700ca00301c07008007250f000c001603100d0003c0d00600c0d003640001d00f820310001d440c0d00314072070f42c0078038403616410107041d1900c0202c546c0a1006403001000300d903a104420400711030040700d4030006444084445c1d40001180100d000152200c04c00c0758000351820103c100c7c040203070346081203e4900300501c82020b00702140c801136003d400c7c0655422058841d040240c40c03242a0744080050b052144014614481c8084a404038109880c0f820b4890000600940d000100449400002c99080b00d0028004040e480007a031000c80b224404900a1100191103598244811022150855200000010481007545804c0f00a800c581c07600322540148103003404200090380d15110310100315240607144410100603510391903c480c40f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 136259829 1250 136258579 136258607
    0x3120604020904050910060504060b04090c0215010b131d160c05060a1a030d0503150d150c0e010c0812040305130e04020f1c060c090803040311040b010e06030109020a 73
    0x21502080010a06002841b0303030303a41a101a04001423134407002408140e600500580c3d01424080000304045130250b8000f1100d0325180c03054900071004660395000081080c1e2000320070140105140002070610000b6070001c0101119070f1a0f00c045032882420042001004241040d00c1d440c1e0540c2d9490050608080c032580c401c0654110b80703411051070006140a80155101c8440d01c281a209402c001a044003100610b03110030741180c1d1004c284540340e1894032032240d00810301e541c40740c0000e100c24401c101d904154140c0450502130010000306540c941d020000e04000c421810740000c07600d1031044410020320510b502c1b88a68071810196110302c41c004a02c10b00b001c0c40e0400140c414405c00764603003e184215405200f0800120800c280c84551049950304440800d017160f00040351a80714241c8450355061002500340d84444050641c1c10540c4195480080700381d103042709182c03901c911a1500d03424200390920000c444c0100d02e0500050264132281680010740b411070314026540b003042d540f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 136261079 1250 136259829 136259831
    0x61b14030a030509190201080103060504020402091c200a03060e1e030703020d140d0207020307091109040509060f07080c040317040302030606040614010324030309030201020607020601060203120604020904 90
    0x10703980c0e4800500410040b036075042640903840e400700c800051000b0311060f56070142d450b41c0d1142d01b941c907084000d100141c01240e20a9080088003071a46841e0b06070100c4003c3e440c0c011780754412506210700c00e20040a003840c80d020300091104000e5941032006810340c0c2c0c105d400003403003c00b07a40090707190587c0124801e071182c00b08008080c108400000038405644243c0c259228181e001500342d82c01c0b903606010401800f418408201110b601da13001d412424002000c0700d00c1f840e0350b4840e000444101028886607a600052156024181405403d070400107000081000c0d291035401035000c0e60000d00301004200404022415400c8514207030b60141d60800e09443c4181d1800e00342d6882a406848200d01a000d55800981145094810442294201c2c413503440c900d410030004500030074100440e83e10f140501c0011800414550065401030340c4251a00202682540006890014000c000c0400c6600c0380005118595001c01600c0002c445800344050b1503c6401c0014040e008150400307403c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 136262329 1250 136261079 136261087
    0xc0c0a0f110a08011407030903170c0315060304050309040905070e0702060a0b0306040f120201110705070e160903060b0609030a0308070801060314011412150103020102010f0204061b1403 82
    0x110014008500502004492080c2003655903d012402e9803034540220304100040c900250310980aa00154006031003131900341c103200f01140c3c00a003540300031f80d9112a6414080308020800e60310b154012030b0000700300c0c1d006045140c41e41c0c6842c0e492051040f01405140c55135000410864100b00c443c02a0000124503a8540380105000395075480031901d041c0f041e81018a0344016040100e00c09009580210900100c0b00e415242c40340014032a203462030071513580c0e0700188204044c601c090112984641e01030310701c103031070b001400400b918060445c1035480d803180340b0042015004241241100d030f1045012600000d5400010110b0091500003501030249054100805034001000d9100700c0090300c0e480c035070782d880e4107084084801075080c203032a49000b40018442c400c541031500e90358440c01080c030107480400040c03441c24414030355500300d4506034541c0140b0031980c082c094010003040249046040928100008054500f442d0040e07046280030140314040c00f40820401480108160440e580e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 136263579 1250 136262329 136262333
    0x102090d0212011b050a020c0108040210081b0f070c05010306050d14100509010c080c03010b27060a02100506041a04051302040501060e030c0a08060c0310031a070e0906090c0c0a0f 79
    0x1c0340c0e000c6e9104800600481c55001d5956005038040c45c091500588101d220000d00f50741681e0b03990014001d20841c3c0041401c204642904900900c080280c1c00c40191b111046490000810402c1d40c00590515041040500291715161f070a41300c19034204540800b403090581006d810b001880c000108c01e13608101c100034000c035054006205040307481e55401d10660701c0741c03607001382400203015104495108008e03640384500482d00c020401d00d48000200342031601c02c80002c11a41c407160517100560405107040c071040c0014410280c1c800350076030f000e020810b4840c50089a0301c21426417144104c1d52103021401241c07902582604d100da000d0010095561188000380c003941c442c2c080c2511170f214102000780b071810305e01c0d40c2130304840469006240c103440d10014000980c00040c030210240408410020114801c00c2402c001441348208501c4981800e0074010500012809154041d288030340910540d51100407225a000c401c0410098079500510310060030314410324009069403225001c4142 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 136264829 1250 136263579 136263587
    0x50d0e030409051f03030e0f01020f030c06100b0406020c01120209180a060b070b18031e0301150c0c0308160605041109180a02090a0f1811030102090d0212011b 70
    0x102a14220248003500f60301e044e946414030340e1030300000b00004d038141e0403880c0c5400c020306409a0600140103a4030b2500824009901c7c40d00039540c01d1400fa4041c1c0700380106d04161001c007901500320514094a810f06126029640c0d0258140c1c0a0420291a02e00c06101d0300314ad05540201000400c560488400020242090b030810744100c080b2074035040c00050400a43c000b101c1307250394405e161440543da220785280030300081d04c002415a0004004052144036041c0110300607407884040d180d01c07941440c1d10505c89240001d0b03402c00348102270f00c081c0040790f403407a50f01003100ea000d000507603124210281071140c16134100c00200708a050006020400c08101c014203e00381c0d0503608804a96201000c0d80c1844ca1b0b0b1881e0480c03540c2001c14001d0250074140d0495070310030b40041d000320b4100d500d0b58104045400d00d03405141c808042e44030300341c00c0080d000783c0700301078440440c001c1d4200000c10b800200444460100203200d040d4a400c8523178209429002048640c510580039401014680c03c054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 136266079 1250 136264829 136264831
    0x140306060a030e1f05010f1a03040203012d18080d0e010608030a03050a0c031b080703090f031706040e10420504020a0906051b0609070501080109020f0703050d0e03040905 75
    0x5030100e00b0800040384181260303000301c003100c0000d800824236920981d0480901d80c00a0401d81c0c042d501d8400201c600c080307415101c000e0002806040c01c9003c030039002041100d9411001d81007041c2500e6401c0d020400090561b60124968400042e56031a4186003900400d990b6100300c0b01c0f8080803449210700b0380c059008070300c1414940001c2c0180c07100004d045040303d84048180034000039200350603045a01c280042548801181400119282c0b01c4d115021244d002c41e40c01c400103020440d0303040e84800022042900306400343ea00740800d1140070211611010f050205801d81035680c10101e80009005803010fa02c2c0034000002c2c100c1013070707041d41e0008140c10145400c1341a1000440021b141c100303442212055266070ba03401c0c02e16400c110044441d540818101c04d030610003490b07200041201032000d01e005140e03d0300103008052a200000d4140c0c0c80584c0200c05451043c44030118004881c0d046622860345494129078a13803013213084d60018a04004201b1551202040101e2800106c0e4041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 136267329 1250 136266079 136266133
    0xe09070305060112080715060902070b0117011116020105041203050424050702060904020909010e0108250e3d08030304020307090b040207080705030702040b01140306060a030e 77
    0x34540036030301d0388600718032130600c0607000302580d0003000751a001c10f00a100c00008250031040c04150140d032404042d09a80006000b560b0110100004100d00c4085045d0351039665500c4009010140200d000c1e43c045004191b881020110403011180840e031064040350302410405a0a1681550b00d0600400c0e5420900440030244080f0056100c900b10030b16010000300a40e036581e9103418543da00703014650b00448115a00180c0078001341c0c00c15607445c99014040c14003d07404080c02d624000045140840c1c1c003a2280390040703107491151401c00001003440a90f40840b1070843c864070780d84180013548a800c50750640849a5803101222080b900240580000c19022081045c5440d9034980ea01d0b072109a0b8001e5050b0310240042080d406641c120308581d0400400041c00c2c180e01c1d8407030760065440b1000403038580e0400581f820840c82c152080500b0700000703290131080d4091301101072000d8400981640d1017844040b50281002744203802c041074900c2c40c44107a40140c81440b021039443c0c5050404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 136268579 1250 136267329 136267333
    0xc010804060e010908030f010501230d1e090f06050a110f07110d0b070e10080a0902060c1006030c08010501030b01090b2d0a060f020d0c0804050d03110d0503010302150309070e09070305 81
    0x88a9103072f001540c2041403c110071075200c0c2c540746d403404e040e40c0103064004080c2c1c2100c0c2d000590a80d803041521400d40668018000401d03550881d00d000d104950300144004041454601151121003082007a1250001084503855540b01f040c104a200340400702e620551125690303e0050030007010b82e040b28002c260035199048900100d40402154030f030400303000350000310844001425110b594101c1c02c0803d001a007100d11f0504104052801c0000003000c0a07111a00c0e000e01704200a04a50007000821012000300000d50440d5078006040c0018402c201e080d80e00c1d1000e03044a0b541d0307050841900500040c0b0f6007001a040c104040322412a1003125208040792000002d02500848501c088031105d80d026015030f40204100341d030b10740003440b000d444181092201252036218180c10102160107134440410800c51010388078907144c1c82c40c203a1400c0010600042006841d26100301080f000780301801ca4403642c41d20000b518011a9901c0092044200814019911004076482040c1d038001c2003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 136269829 1250 136268579 136268597
    0x90c081608010c050d1d0f0304080c03070e1308040506040306060510030e0712050f0303072f100b061603030c020d030b06040504051e16110c010804060e010908030f010501 75
    0x240781c1c00c03680101195004508100055001d1082540c48a08100007480c1070202c4003007561202c41c6028070592000c0c00c82c1c1e100185c180041e0908000310401d84800314014050b240c10030390717a6201400041c2829041c54000d1605404014083c0d050302c0280c40060075064030b0f9a560b04090740078201301e100705801036844a0340c1d090040d1080c000e21010301441402803907110b2030b059450700c8c041c2c007101040d10781d40901d013100041d02d0020b0004501880540d9100c20f0040c04130a04c1d0023089542d040c00c00940700103060003610900d0b010400000441d140c1000180076101040481c1e05403095202d440d10408101c0c003441c04041d0103a00c07e0003510080d60895103413408202c404c0e0300729280680106d5005600b44020011440d1a4001c0d66124810f840f10b9241300003221110103400c1e9007a6030641c220348110100c8480640d20210340c014800c54840200440c002034400a080b0180c040c0016058940b240c03081c0d041d1a41c00d4101d4600f9581c0086101d94900e0f02d07012051490350f0a00038a400210301c21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 136271079 1250 136269829 136269839
    0xc0f0308072007180209120733140c0a03021e0c09060904030507020a06270e060f0604151101060603020c0d121803030903020606100c0204050604090c0816 68
    0x410b2109440144500070b02c15107003460490a40c4c00c031a0505a601e064003004542050784442e191840c809a4480051604a0602c50900c010444171408107101c0440c411407000031003600310501039083c4040c200b031034000780c010314401218814415141081d1080484800415a0002e0700744000285004c00c001c6d403d060800312515040b00a901c5907000b0b071800b01250503860301417281c81d00148281000b924040460703010480380246a400315000c00e0041c411281045004059404401a12043c0f180c0b42d9042a00400d040d142c0508050700403440960450381d02d84843d01210041c189a40755050400444c42008105040182d200c0d80c241d400c0c41c00c00940203010740261103070302c003005c2d01230500000034200454084c4414142c0c1003e117a1510505241007640054820020340240d80c0459600f1f03590401034646400a8801ea00076401001c040035416800f1050150060b41103801080a8a501c00058040d2800c42e41c09464120b4015001036043c2c4001454003280100040c02c1c10341603580c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 136272329 1250 136271079 136271117
    0x5070203090a14042403142107020409050316050f010507020703030c060209060d0c080603060105090c0a05090a0803070218060f0603071e020d110a0f0b070c0f030807 73
    0x890105900007141c102c0038440607070402c104500229014000041c0000c0700c014088029107100102c1140607041201807050009142254000c01d140c0d2004042140d98140514007110030040000d04017031020460604541c2c5030340082c050250454112a1140021b5182d03100340300e01030b01c040b01c40744030308800340c02c41510600a075407040c4a01d401a01c0c0040c0f0795201034842c25101c41044400302d03400c002e60705481c5e0f140700161027040303009200001c01098501e40030300400720250040340b281d40560010081660b61030141a8050303007220b0016203965000c9030a84035800754400c80c550080b0b07509004a0081400005044200e000319109080c0112000920403034080a0300e1a0b0340101d040150a0348900b03020006540240c0c142c0b51031014001c06c0e802141180d1050002c5400503000241d40c85070040d4040314040108211074060f03d961a510b560300c00b20098414070042891400074001070039903008010030a8895004440e900b440500c6140041c03400302c00702c0300701011070030b2407809104110382 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 136273579 1250 136272329 136272337
    0x105010f090519020f0714010209031c260603120a020a02010c0312050f0103020901151b11030709020c010f02030405100506131a091503100c05040f060e010305070203 73
    0x80a414124040c1c1032408990180600a100400340b0f030420070341501d1022a48028241c8a1000c1c0e034084d110342e031625040b0024405c00c01c20701c2103a07006001c0710b5081d542c00b0507d09141c5140e2001c1500142011005503a411141545c400000d030282c103001710110840c609540c03140c84102e060b40c40c81401055128101e02801c1d0305000183c2c0014104001075011301d00358500349009040c220414179000080205407041184c110203d07140781c0d801007045003040303070030130780903054921890707007010020203004000c0c20004076032258540451100760280511000c40d94841200601071310b2500c0c0d112891040a9800000c010f4842d40c40c28807240780f92401d902c01d680c001c3e40d1010103030020040b140030800151101502a903801b031400100d01c213035402248242e50820100100e0f06a41c00c19080400403c440020105003131010072489403069940c0110b00b45103901902407001a02c5043c2582c1254107000e40c1e04004201142440c011481c1900980000e02c980404d036424401c5a072400012a00da0203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 136274829 1250 136273579 136273589
    0x61e030203390105040e0a0b040b040204080d0806060906070b0906090a0803060103051902040f08070905100b0705151008011a090106050a02010e0a030f0206150603011202030a0c08011a03010501 85
    0x2d4041d10541461000c045180c084052500030300b0300f40c6501400220010036100650000d07030720380c040e428500b0940665034451208480842c2854034002e8895105e100840306841006403944c0058171580d00c06c41503400416018000e181c590809150448991b0019a4901d150f0711480300041c0d0001e600144003001c40d5031100016066031503180040d80500400b80940ca5041c0c4200c840c10a594007500c0a00b000b00b03582441c6400a07860404510305007070080c0c0000c49003504100c1000700ea000c14550000841e2540c0e10b0f0301d07a455407141411740c1091651451408042d05d51401c0c003510f076070340500d8541544c0384c03c802000240c0031144902c4207104884840798001011200401c101d5002300c0103810b040086000200c2e0000b5010741c41800c10011003422070101e039007003588221860b41000481c0c2d000340c140701c038a03c0e05a01c500001e071450105102d0034205421808800007151000d00000c0500e641c8980b01c071010b261a201003602070010301c11040300b9810a071010041c00d1405020300c50482d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 136276079 1250 136274829 136274893
    0x1809020306130e100509160602010e0604030e030f1f0c020613080307090e13030801050303030108070e10090e0f0c100c020909030f0403240207030e0f0103061e030203 73
    0xd11401d016010f00107410b000b04443c090050055442c20882c080c1610a040d4203000d40b484107401109160010b0341b40d00071070116854518550340380702000602580090b0141060758088038410f000900d0800e20030700c0c244941c0241060f00040002002801a01c9902c052092200340c8541d50100c2e91160101c40769181d8140c8841c030100490302031401941c004503140f620b00b40442c0c0b00c00d142e02c400300c4103442c9640c11141443d280d03001c0c1030b84460b00c030340502400c034085c510b5540341c4000940e41d4602d0b4001c403458080440c0108041201d0b40c07c4450090445036428030400e404418525180c80c40f0f540b9090307850040305101c0c84603151001d01c0d040040c1c0641c4412000035440d40a111140078005d206c20554481080700316114400b15001d00000c0d88100d580344800b0075084080d00701740340017007a22000b5900500c060320009030001c406d4440b090041d656080020f480a0048000d4261540041c186891043c10031003800101349003e0283c9000f90111050001c10155455010540480280b844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 136277329 1250 136276079 136276099
    0x10f05030702032b09082709041b050904060c0f080c040b16020405090f070b040302100305070909020d0c03112803020702210c010801180c020307050105071809020306 73
    0x1401c10f60044059010070150008012400d0084c80c0c0101c8040d0f000c00c1d42c0950300850303006022008010000c400000010b650303d09000d942000c103d0044014100030700c07600350791400c002840c0800200380000d0030000c180200b1400c0606103407009020014003074000440d919010341609000c0e0612600070352046a6061501d0b1412030070011035080340e0b00703600303580c00d0050310341e0302690703075405541d006100b10306c085d0480b9400ca00c15145028065030040d04200002c2c132007003000da0744070482c030b601041c0340c1c1c00d002c81c81d40e442c19821604d07102282c002400052012504081d01100d0740d01c0550158901c3e00e007000030328202c1042d001580610241810801f400c802c0b403544448411040205c1034400c5c3c02c1c00f41c2440308907800034012100744030b00c4d1103040001c081642c00502c4100487c81caa104207080016265040c0000c15040c0d001003003548103082c1d00d030030f0700350b440354400c10854250360b8116008021a04040000501c0f0030340900044810010001c002304d03056200e48212805100c0007040800c40b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 136278579 1250 136277329 136277347
    0x90906100902070219030305040e13050c0906010e10080921070206071e0f020f01170105090c070b0f07020706021605040902010c05160e10060c02060702030304031502030105010f0503070203 83
    0x1a6001c03e0f001c98000d0201c03a072400c6560003018083e405107103e522a01e48071410300c07061007603131b40c001440d0a0305008401d8801021800c00700e2059000c141c156245501c0b0758501c001641c0b80c00441c0900d981080e0b0003c4640800c03580310340440e000d40222402ea60a081d0042c414a8442d180301103451000041000020014a0114024020548504200450451280200d0488035a4801c2c16a80c80c805004110210b00c1d0210100c25900340c00d0800c195602c0d0464602981743c001405014020345100c00401c4044a40c2d50640e42d0a42c0c0c41801c8075910325201800340e01101003510680301501c44c0650202c2d180d400460b00342c0c5541070112500c4a01483d060802c0050054070341c041c4c0c1884a507141003400300f8411b21913811034800c8840920b6413545440c40d0003018010080c503069032002031480922505501c050341ca00000d80460722a603c0b00d0050002a081d40301d1540000c082980c0300c2008141002a034014504a41e826264031a015050481c1526030348000c54148006030010445410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 136279829 1250 136278579 136278581
    0x803071107090b1309300905060f0712051b070e071407060507050f0c0a020a050f0f09062e08010609030c05130b0303040f031b0302150a02032203020909061009 70
    0x76009000b20b6580c440206d0400a03903030100b420418240048048100c08004940c001e80e40c0300040800b90b0310213240c0200e0060040080c0140c8800800750826038402c0c1d941d003441a800d80d03148108540c85840424070600100e565003c10707105160400c01c00c540059a164041c020740d86011018048040c5400311640e9613000400d0700410030001e002c2d0038000c41c03040044520140c400199900010f00001460b4010841b01c0942544840d2240c420340c481c11400351680b90500c10800c00580f91031040381c4402001440f8000c2044040040741416480c1d18441900100307000c03103e00d010b40368070259903291201103035951101c0c000900295007108003040345043c1940407041000020fa00068030101c1180024210791090380501803140e0b4082083c428800c894082006200d48038902040252443d070200c1c004d440400d0300406002e1001c184403070542d00030f01c01c807025500640b058480000000d80c8016820415000c10703406a494800080c20304000010300c94010358800072400000b07490070541c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 136281079 1250 136279829 136279841
    0x11120304240e030d0f0f05040c140f130203040c120507030f0212060408040602070603140106030228050a080601020a0201081614030903041508010e060415030803071107090b13 77
    0x4541e1504a0030b0000e6040c0050580c8211008011600610000115040d54074400c541000f0b80e14200030b100001d0164000c0c44120f81002c480749682c001da080c0020340f0a99031440003600314022040b180308541040d4002d61090b0700c01c00c43c0b0718900e51264021004660a02801805940011340c280080350102403c07202d000c1c0300501d107006c21200e003540e0508110041e5002c0307402c0b4401090074000c080c0c0601081028140030700d010801d070302c0f1094441881c00010310502c014154006002d0b40080e0070199212410000070001c0d18101c1c01400000b0215031041001000054109021031410762010a10302811601659110741e41c1d2551210124010b080030b001a0511081c0401848003800090256214605800140d600c403482c20780c42811062500c004401040035140060110a00f00162250800005c1e00c0c0010701c480b0350082ea2250304e405401c040e2444001100f044045503000384001d5200c0145e1040e21005030b40d0344035071403c0c3c0b19094080d40d440f107600349880b01c01c0e208551107a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 136282329 1250 136281079 136281143
    0x10b0a18181a060a09030201020120030f070306150f020c04020c03090906060c01151d010e0f0c0906070605100f08070905100306050103081b0606090705161211120304 73
    0x998036402600703000414580c852801a1301240b9060760030825581c0a03c035040211400302c100404845070b00002405030b101c010144c0c0d148420041c04034030010302c00e40c060310203002000240c4480d861141c0010b40700d00310b042d8109005100c0c8051469031403c3c14000e4031001a81c201c01035041400c01e02c10004080b900400c4503070030000910514142a009000c9d814482c4031301c000016040b0b040800da284040040703003005024009410040100340040d2030081c2c4d018124003400321280e100d24084115504c04d050f05140d1140000c6581d1050103010781c40140116031044450110503611044c0f007106100f10700c140411600324100030040d0848a400c40c0b076203c035909155030503954417a80c80c5021100c0c284c1040d9001a0049207225a40789010014070820b80824001c00962402d000060300f0000d0003000e020411801260844026110000300a85141d00c005403040800b040b1600514040180e16404030300e120f1a00809100140041180c1c021074002d1410042c400e02e2401d20380c41c141200c0d1003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 136283579 1250 136282329 136282361
    0x2061c0e0a02060403350406091703030105090c04270b030f030f0d090204050106050c060906090a08090d20040c03050c0414031903030504022e0f0203040e010b0a1818 73
    0x80c42c0046105120104c0e81c1040e06d0030007900d035407c0000040c0001c40302d0704504491428900310425030800003066904494040390056205c0d5a06180101c290045901c11022180c1011400700f061007000000d010b03613001000c00b00302c2000e610301010b43d1000850340d07000040d0020442c594134040e040c801803082e905c2c0c4d6000880c05010b65408901102c2c003d80c800d40028402150035180c0c1d140c180500b54001120400a02c11824418004e64940c03500450007070281000040d00074194892915540d00542c0000d40b41c0d07040c019440e030521301280382501e101d02c1103140070f4400000600a204440c0641e0300070003424100381c1030100c05c00304180078201c4513901d413003030b0007a130380d40307074281d801031110180c882d5801040b00e00301031042c0a820000f00b00d08001c5101c41140001c034407c000304409580c2542c600e003122920391008802e030b007103104540003181c001040d90300104520001c44c1c02410b444800355107221091840b18000464901203003d104405c000850384001d5101d1a508007150702890808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 136284829 1250 136283579 136283633
    0x302030a0b03030408060a0c111c0c080d060f0602030a09050f03150a020706050c03060f040b0f0a030c050a1707171005070e040c030209101b02061c0e0a02060403 71
    0x10000f45160420740c0070307040a900031420031121510a0141101212a030300b041004104209900341c0c0700e2070800302a0f0075455404124031403985c4a908610000e540000c1e081d940c031403510f8000e40141c50280100f00f800c54410304006800c5100004032000304c40e0541d544000d240c00c000c100107001a2151206600d4814510501803010030342c00e0a84c001d049152005a0f40e880520f0200d096800050510868410520070483c403034443c80000c0c0f5480104450014001b28800002602241c201c015160080b0388581c000c001c01c6200d8490324107880040b01c0205003150b40e000040c0c41d030150030003803405da900815400c1000c0705641000342da82802c0881544c803070345211a00801100c204458410010f89402c2c3d089203142068070078901595950302d019440c11144402180d0307501074924810040000b040340590130408481850b0a110368002e009580c6c400304030b043d64010441707c00341542c2c414900008140d090000040c0400e03841e0303003e4283cae800c2500d1900c070088100c294030480718100660b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 136286079 1250 136284829 136284851
    0x603060f0405100e070207061d0d030c03120213170706090506031312050a1b0b180c030d0503040b090a0308071409090a0606020f0307020604090c0918050f250302030a 73
    0x8013030030b0711030005580140892454030700014020703a65503c80c108002402d074943d05081d218940040800764050800c07001c00080b5140448000d20b40d803070100c5039a0301c0410035036010964503e41c0411640d000844004000c01a01701c0c03510f41c0d0680c411000800c0d90b01c4002c0129040070805954401c4041110044042594691004003168519000300044000130300b1150f980d001503d807621800c03032215280031040d55035110f010048004d8509402c0d0940305400100d60340080180c042c1d0349030090142c40000004c9400071b0701940044c0c0d000c64900040c00d0000300520340018112084641503900c1620703a4070f90b90400e0b42c2c030040594010042c400100111034046d00c0305c00d540c0c0c0c0642c10300a40013509a140003002804c00301c1d403d51400060f01300304400c2c80541d594505490030344441c883c0018868002178020788100d03802d94841100d080d00a5002d8003c14000e81c07000f407107403d170194101070702e5035040b51141540c3d0078820b030008090504002c0b400d00c5c0b4400e901035980521502d0000990341610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 136287329 1250 136286079 136286099
    0x601140f03010905040308072f0705130501030b060d120e0a1509050a060e030a14010b100e18190c0311040e0405010e0c150a09050d080a030b0603060f040510 69
    0x3d822003880381e62036500340410190321464031a4070841d24684080010440c3c4211155010342080244038034070703040c08596070f00c0c006000f1080100002841c480b5100035801550300a44001d200580d1b0310382481000441d241041c0d401e20b070303503260b03c021011992080a141600c2c0035460003a150b821901d60080401c0140c050440b460740e1085e0382c3c40f07440919150101f00403100c0c1d0709800020412180e41003418032600c00003404c044e110740c4002214403800251249500404528010580c409240158810125005001c03510800c00503184c0340c90f45c01c21401003c420410598180c9815074200b6070403540070700103500c0781000100518000c214100a2040c0943d56003141e0480714120a080b4180800c01409108180d800203c0340e0151030543c1301840000c45148410a075040413500009200c50301c148500d43c0c01001e807600034614881e2440b1800d298440341c010381d04050100746084080c0340245041000e03644650303001000040020380c4034040c0700207040d000d01011031402e800d0320040b030f2040760 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 136288579 1250 136287329 136287331
    0x81b070f06090b07030e120c01021201060521070518041b0e030f07031101121107030f020d020a0b0a0b0d081204020a0e010303080109020c190302030409060605120601140f03 76
    0x20100481c11510b6818082e00e030b64400740030301040c9441e2199170680d01c1d80106151048001001c411030321000001c000310702920541c0c00300c6502c4803d610010501c2174001000d4036540d02401c000c3c501d03101500b500034820100644003503020410500c0098500c0031411030b4005541000341001c01c084611500990150556102c000046641003406d4556070904000c074640303242e00f1200900c1e240f0700e107072280b5180c0c0b41520384660401079111944403400c022504510300c3c2d1114034003510358440c0541001072005092105980c014000c144034144218400100300b03c9464000c070b00680262600c003103100050004402c0b851300604007101c1c80c404240418003030180e1028160340017245281501c1003000704080b6400c08000c04264a0050010a5010704582d064030130102d00103179140c103000c40d1545040c0341c18a81100006403000e514003016030201c050411102c0e2210207225043d200d80c01035403140103070006078400141f801c1c009140303588184a003803255031401c1303039440c500b180b2b80c42c1202d01c07540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 136289829 1250 136288579 136288583
    0x30a06050c0a0e04051005090402120a030e15030603061501030e01020f0c0712030f0503060109050d1407050607030e04090323090f011e0c020a0b07060501090c03090201081b070f 78
    0x60218a6642080d00301c01c1c40f6280000c100c80810551510840d2025030300c20038050503001e429407800107000c545490081c007d004149030103d5180e610b00d0f1500400e0b5800c82400745008242c0c41101c1038940c0d80010690b8003c2200501a1509a6a030844011000d0081c00054101521030810b0341d62000c082c03004040310f091034603046940e513200c061136074904900c99000c0c00907110b202c00801701090b88a00292602601c51524554944138240102c800c21580d42106038800c4c40c000400013003012a02402c0010741c3c17104152000240d941003001303100d01a80300040c0110348174424040045c5865801010014030904080c001e420f002158500c00346000019a2400400001d007200580391100000300d0741d40d003d10f481003e0041d002844450301e00f01e07428050600006001c0201195500c80c41c42015100c6100c82c81d0301c0d14040c0c105103015000a21920f4002490814840341e1a0305c68014460242e030103071140846a01c1e001842d0300744200390803517620000c10500c24031000810068021414034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 136291079 1250 136289829 136289851
    0x10f05041d01170604080a050f0f04080102090901080f10021c1d010b0d02011718060a0914030304080a050d0f0c110c0a081009061b03090515070914030a0605 69
    0x240c106200c04030f0300c102101400da0903034131907400c100006480c501160300c50a0f0b43e1500c9900d0311040b0820007418007034404080803940e4041030100703201c2c0055000c1c0400d0070080362400060b0341d850140c42c0d154600e48203410703143d400101e45203189244a400a0080ca018410a005480c54840400b42114500140000030a03403060b0314037100791007406a408038100413544200381856560018021244503245041a043c0e440005201020390900c1c14004d15400826160140707080543c0b000240f00c400b00440300124051000c440a203000025603218581c0f0500d80c03442c002c1400300507a0350760415121090354586a2002d01d5110b07000d406aa8652040d940760924845a3b038600c0c91f04101c24800900c1c05902038207010030000d0400550107c5681e00b481001528210034185400035140450340307448640810002220040d9241d404003811a02940540d40c00d1408034854009503c410b641201c002146100180403d80c019002c1400c003010080480304030482d10b0b030704c61040e07410480700380f8844 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 136292329 1250 136291079 136291081
    0x2160b07020a140106122d11100804110405090a08070804140103020306030a0308060102150118140403020a031d0d1109090109021e0406180b100c030806010f05041d 72
    0x22900f004488902c81c08100244045400c1c030310700341c1c6502c00082c1d014040c00c3d03401100840019005012032036030004480c0b45c8040719400c0c140400c113000c46c1c403181c1d0302032180750315641403081c80f482c06035005507807142d0f1814040208070108800740102500707052a60241c0c81031031000403208030050523111b02c20b020705625a071034030107a801041c044049083c10315004104200301581e0100d05510119418200308040703440309070040745450703411240940754191100010419040f501c95000b180752140da824011000e075101c1131b03841d0000945005016901901c48940001c3c00b61005000e40380f8003c1c0a00410200d000c0000c03900441c40c2c0b03040e82c00681f162110f48480c00d04c1d0191a0344004203e0083c8501c1699034082035001c4803454184100441a522080296596070007040062240c040001103903120b001156004122140d5502d1042da55076054003002401030a41e02903058040e11840540e594100054540f22404d04a0004103e020000030582010100001241c0848007040341c0352 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 136293579 1250 136292329 136292333
    0x1503050d0e010e010206040f0501020c01060306020d05070c0f110f090a09020103050f010501020d0509060c0307050723090402090a090c060c03110106080c0d0507051c11150d02160b07020a 82
    0x14441c1c90700303035241c100b2036604141d034450303600020001d400070760100a114801c030003411f2140c0207021780005103c40e5401d00000009200c0c8540145c080e10400c20010001038880050039110085102c100801294203a4012070200319041150242240b002d064104040e07940f00004060702012100595002e13a00d0306060103550f03040c481c81d42d100c00c8501220146506120010303558944448540c030400000040e1050f554590b8025101800203080890340c48940070b24007592035522034082d200c0c2602400b02c4100b030303412161000c44541c4501030410142500c640d0240068403100a080101094a40308031b0b42c00500340c800110024601507a607990000d15919004100113540e40c10f029a903814030409100c00302c0049104083c50508803184403a81c082494002e0130455203038002c6d03500003081c103135100c0302c81c1580603540c001610501112410701b44180400407045180b0105000d40181800a4048040154020b12001e90000030605030b14001c1d6442010382482100c04031b005030065406042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 136294829 1250 136293579 136293587
    0xd020c0a0c090f0c0e1003090b04030807020d050712031a090a0c0f02060f070315031205031602030a08061009120507081221060d0501180309060302090d080702041503050d 75
    0x103140f21001c03e040c040201380450003860649031200c0e1070f205003007101c50514541e00a500c1081c0310f607406402061185003e05018008640450307101000d03008019070740301954032403c01c588540b94807403900304070910f44138000c80041c002c00d003100441d02013140706d0960742c1c0c0d96180100e02c154006800481c6000360940300800c4070a0b800f1541042d03620010038002d0101002c4038841c1d106045180025195110300030b50446000564000b07031008035511034103149140d011005501c507807815a8002049a0814000ca03030343e11850b410900000c510f9401700d6441d190090b1509070301481d81c9040d074501c0ea15001409042811204100d500da8030000080200134070600c410380040d0104c0381264109040003130708103041e86460000c1482d010300400040c66507640e807500c02e0061a0000020082180c1d500c03455100303043d040c003069011030407110b40007440c00c2c400e000300c90b144180503000d00000c0c03109035500e109541110384100d138041c5e12802c0d1441000001a90040150701850040c9032040103400c010b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 136296079 1250 136294829 136294841
    0xb1504051513090308010905060301090b090106030507060e03062e0b07110103060b030106031808070302010504050c09010b04060810030203031218010c0c0f0203070302150d0e1902060d020c0a0c09 86
    0x900c0b1030341040c0ca0071000c03d422801c400e045805920003c2920307070320580007900400d09007174000d1003024480c043c03042c41c810541c0b160060340d10034800c4907842c03911703030000703941994000c030b0301c554158000c0c00090111000303014a00c400700018070035040c6038156040d0300c0c8004010303500312426008020613081c061107144800a1a907075800e00b41000311500b00000c107006440b050256105241e207400f4640091140c610400c001d80d80c201228984400807440c00074060402900c040e501403161034841481490104010b504a80d80d10703020b9443c050ad00700d000d41e0b81c050010614002c4004c0e4007c00005a1000c2c4020701074051b65140c5034055141c00505100380c07a90443d42d070340c041c0e071501328000407403500202000c00300354108100c440090000d200092620b0607a0300002c0d0800c000c4801c45c1640f1009130054410a8010141448038013461009590764a400c0c0f40c210f0380c0980001c1410002d0b0a00c5401404400c42a907005807811030700c0049079140212040c82104c409036859020042d008c03140c1324075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 136297329 1250 136296079 136296109
    0x1503021c111f0804080f19020615060910020c0a03030504060f0309020a050906041d100e03030609010b0702031002181c030f05030c07140a0b010f0609030b15040515 72
    0x11000b09090046008195000c011094050040386008641030040e0304041c1c84518402e40c0d0b089a07143c029400040c1c6484400c000304001d0310454003c6004a4190103481e4030510002d0a442d041036920000c02103550800300c0c54800b94000e01441508503115400501e02560090b01c803242e55600d0100b004001d0120403000c1c0003010310740341d400e00c0140d0391500180d080f15400c40b40403145440c0d1000003030080c551494105036000303500c00c8501c2c0040d00400c040d2151039503104204401d100000c031013501e07840211121940030030b0040042c8010a07100020704001070020301103480c02000072007404100c0c0c1c0003503e044d404500004040109117801190240d074020382d40c40c1140060165071700501402e44172181802400008030024607074540d00b100343c03503646401c41d584240188007150364580747c4048140c141d910183c0700c4000719420003207640302d4003280c0e101d0f99000900342c99901d60450081c0013070301c1038010b0b804200b42c0c01200c0c3d0b0380740507142c016414014006401c900d40020444116260050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 136298579 1250 136297329 136297339
    0x507020d08040b0a02090f06120a061d180f060708100f0e0610111002030114180403050c010204090e03030703140108031b01060b0f030118140a1503021c11 68
    0x4110003d02080901c0303030407000205015031907030b6058001815960488220680010020501403880b08907452218054042001704008076500c3c1c0e0b46c500401100d01040d143c04180c83c60100702001c924070303c1455182c14280a0715041d1501c0c51301681840300036a02c07007000403a46414001d50140c0f12681100411909412056003468120b0402461000401d154840e098010111904500804542e0300c40403543c020360384030300b1401c035880c030007500280200810352207d44031900c0c0c00e060a11070481da1010030180c5035460b50703680c2e07001c03621b9a010b021032401c50354082c0400141c4039110300600d8000c1603180091612031078104401001c545141400313a400850720001001030400100c00c440045000c4194140d9030004000340e1400b40500781c1c09010801000a200d4000c00744550145040c0c1d400c40000b01c043c1c81c1d442e81c4800c1520600d00c510744658a1030b0380800e81e2544154042441c2d507070a42420740010742d0b030390001401104803403026900e1400d000192020030241d10420104c04104480c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 136299829 1250 136298579 136298581
    0x1209060f080f0415151e0807031e0c0609030b06040b15090d1209170a0803060d1b0602100b090c04030807080c0d05092d0618030a05010507020d08 64
    0xd80141041d402034615020070191202240502c415070304000e040413402d5400f40110380b10794001010102c0c0b14424104c0c100703414002014484d0407a003281040f103181c2002410f20a055450300700103100400310958544c08001903207000642c501c140d5800515054444852461444c100005011001018688620303d0031407809a140d40f801d200c4505c0c103040481c9152100c2191000c509628040741001d458011403035510841c03036078042c0c00d54080e64110715001c08108091503600e41c2c2c41900c1c035001050540c0030300c00100c49051080400342040d0041c03056902c040f140306c0d810b480d2002c0d203400c400d0068000d00044072074188140140c9801c010f041d5a8041c442c030b099600607034103010f50b004c000e0a82000180c107d017400304600507120246000b44c16964050002a4050075580c4403124880c000c444030004c4400d8191f03850714007031004062004210b03101a12600b00940d6a00030362443c0200e03003150b40c2c1c54071039460410884160520803000002e8a04001e48040e20304044c40d2544420050700c58 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 136301079 1250 136299829 136299857
    0x1c05040b01180b0a0306060321080c07030c12090501110a0b060402070602041a0903061b090d05030c010f020304021c031e0e060c0d0905030102090a12050712120906 72
    0xc04001c0c1110110303800010b0958500984001520401103059401582c000000c014407419502490480b4480d400140b20340215080c0c1100003000c0c401d488000c134941ea000550303840036042c001c0050b01d100749440302c1c138500c3c1d56039001d1031500781d1201c0380e000401002d401e00c950758010f959290340403914030081c286e4070226602d41c0065600101103901a68005c115001040080d4054602414165a40c1c0e048428407503004010745d003042c40c550f4860f110700c40100e109818a080c003000202c0f00c468040789814803010a01460640d8100100c400c1c0c0301c2005a02c070010350a02ca011a45190780d8005039980c1814010002d0742201c2006501d4404141e0782c040002940043c1880d40c00401c41810b4084515000003c0d02e01d6041c3c2e000803500240000340d030900c25100851019140e442c20b403560107046880c0c0013410300300d01500003465040141c82c90180a814007000030302d03070801c0c800c0c03040711109900c80c500c0110508035104229650700641d40c00f186c6c2507801003c0600502038900c0c1900c4286d04071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 136302329 1250 136301079 136301093
    0x903040f030f15052a0a09140120010b030114062110060e0402041506020c04091e23031201030809011101050f15030601050901031202031605031c0504 66
    0x151100030500348122203810b04000000d045034a401c01c00c41400c00080c50950702d207810b21464002400c04035000360603259444540711043d41c074543e400d0780e120412941441ea42010401c10101510306106032440c1c484262208070300c5020340340304440004904040084141803c2d074800403d480c0505000074104111521050b44010800403401c4501884000034440c440c108102903070490a010306101c804106072071031654490007103200b41c2d020000340b07040d8080381080c0202d80c091100140c1141c841c083c414907143d00406e0b03400f4002c500100e5502500d6101d82c20540c145081142c10001c080c0d220004c0340004008400d41c2e0301c3d69000340d864801c08240301280d1070b0301400000d04140d408a40c102803a4403500c042900c61110400130000c1d410603d006050840b0308440007600102d0009005000e810f01041d041c1c103c40e07002d40240460b07403d55440040c00f1800b44194421031005100c10582c0614010100c02904e0041000c0c5a0301d801041030b01581000d681c0c007400e036980c2050103020004540b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 136303579 1250 136302329 136302359
    0xa0902180103090309120602040e0903071227120308090f03161104021204120f0e0609010309050709050f070e0f1306230306130503031302030a0b0f0f090304 69
    0x2007440c00140c80043c514041c0d0780ea03111500000701642046030070a0402501d54007c1042e03540d0b1044811881e40d9114007150349203d400401401c101c080c00020b070090b0f006070303488400340b5004070300e030300350305010105040803940c45520046694614508180c18983c21003800740e001890301014015103e41001034640c0da12410441042900000716801c0c14400065540c082c0590010400e540e44d500d480480d00985400b52010b6421040078546214100e001d030201c007101142d103460380c2c1d803121201d10030440e003a0816074043d0305240e00c450300d01c400200140554030241500c0b403000207442c1400d541010550388010103030024003082c4801e030219581d0f0030510012040c8110b0f00c2c01034414900c02c0c1d680203445a6404800c0b1040b5070600c0307844203034240400245041c002c1c0c04545155551502095103824a100c0150180e08104040f0702c038115040180c8a1140c0050304071030a015a95584a001d04411114903150418a60a02048128501c07005811001210045080504103040c84154940d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 136304829 1250 136303579 136303627
    0x30c070e04151b0906030b130207060605060c030a081608010b0a03060807080c0102010b0609010e090a0e10060602061003170d0e070f051804050d030509011805010b0a0902 75
    0x1800034001010400d007440200c0c404542a48140b000c4801d0561041020069843c0180881c41d0b41d00c010840d90b1091188500701c1900800b030440c3c0207800c00c040b80084d40180420b407402030b1200d034040b5090315140c005000601c80f26000310303620080a8001040c1401c09841304a44030444c80240c1c19241d801511181594038211045580f040803050a0f40145400d0340401180d028000000031140b40111f2130280d40c840a800074090a180c94080180b280710700341159001c141c010018001d5401c166500585c8825584030005240d050808003d25000010034110b1a180d200c05041c403041360305201c025048150000d0924140b0f04559990090610680c0309000e01800491500c001c4c2c0b0302900000d441040f1803040d1210a9261005445002c0e020f002d10360196a01206a5841c0c2002803036403441150464007800c0100754041c2c0071409410081c0260605648840c19941141204c031101c1980c284100c2c000a001c250440600081c54410f6200140c154418401102c0c080e22820401007000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 136306079 1250 136304829 136304849
    0x10504031112010507110d0305010503071509030507030f020f060306010819090c0b0a030b030d1205070c06290139170d05010b0c19060b06161202030c07 67
    0x244007100031075125200c40d00703014801e6080005011021790442814101072000c40b041d03580310025803006078180c0c1c80a00c03e0640650281c4c408010030b04c2c0080d0345151141013454038100c45a43d1351074044ca09400ca030019240c9000302c02c10b00301103250400c00b51580881c10780d006401e51500c0310000e004104010000c4e0000010520485044429276000c016640c1e0300048802c11a0740700d0140008030340004c03640c00302081c0b6041410080b03240024030032030740184ca80e82d08030b010b0006040c0c0b035010b8000642014207000e0b0b9a40d00038000340550240c0c54005108582c00b070742c00652544107c6022a90307845441c1444400020031102c0c00c0100840c0060f440d5181030550084e40c050580c110801900002038459032200e8800c6031441444002040203907203201c03091103580d80365221292644100d00c295412076005d02c110344d001c03400c090501c0424500a00000601d412140003080095210b1031002c41070b04a80b0f034420302080414030f070300a001a003500c02141082c1d00594000e50b00c090138001c5110700303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 136307329 1250 136306079 136306103
    0x6091202100c05031b100b040902060d0f0609060303020c0a0e13020d0807060c11010c0504120b09010f1803031d030403230102211e06010c0203010b0a03030c150b01050403 75
    0x4014200221040318a81c1c021004803072204401446d1a240d414100003c6503040c45599011460310b8002c81d03501640080c80c40345410769146248004101c6840e0302000c0a03116500021071401521984004602a170040d081d0302c1a104100b010341445504601400111001401851015400901c60240d415a1009071400d80d43c00c040e0320340d0066450080007182021900268070390300001d0540c0c00e11540f0000e200d00c01400c3e00c161030a0007170b03014a41c0b0440e00180b0440c0403c903003048940d04101a6000003885e44981090602070b1620200c2c80c40d68840e40d0f40c409410141d00d84164200e4018400281d5140440c10880648a200c0c902c8042c16586542807a0807000d03980d908000f2591840f00d008544c0c40308821000380c01c44400d0310620700310070300c50030016110b510076a0020499990800295020b99142c500540d000e946c603400a030380540d80d540300d40c00181c840442c8a0083d501039202c3c2c0c000c9031010b15241907103504445400d5001402c080c400840c80e600a0155015240e1183c0d1074184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 136308579 1250 136307329 136307333
    0x140d020f12012709150902042c120315040203040203031210060801150c060e07082d0a0b04020d02150a0905120307020a0e07030e060a050106091202100c 67
    0x2400766071001008050080c00014001450881101801000e502d00300c429030b91000650040fa02e80c01130180815616003004078a41610303030b000b052114402800000e180c03820000600500f64003ca00c0e2414005100c481c14946030100f01d040c10400d40305175414a5441c123a00308030104c40300055040d003d1034000c03010804650382070007614145200000c14240d035180034280e82c2c0c0f00d25000e1041501140d0325800109800144001889010103d92640c00e61200c0503550710000b00b41d001c150304c2c0c03640116103003c07075481024841030b04d83c48484244c440c41140722a40040c0071a00c1148400390942c41400782c0c0000407500c3c0c8416601a4040b075200d0300607003c40c008590303000007007203000d09854800504150344940007030403201a22803d556008107031840800c015a248682100694003a506000030030404002028460740100289008a05014013808a42c03403c40141c1d405422151910010722003a640824084010b283c08a40d4892003506a00400c04600c09241e0bd9001c0003012404001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 136309829 1250 136308579 136308607
    0x1020712170f041205030712050301031e0201030b030109030509120303070f0e0d020d0b040303051b070b1905010e18010203011a0a02010605100203090103050604050402010807050304060b041e0c140d02 88
    0x13040000c2c1810b0f20706800f803a10b2520fa920420303041782c900105030380103466184143e00b03482c149c036440441101d0f0039149941059040e24042d404a04150301d03032060401d240c90a00074014907502c682c0b50151105003500030480004490861002d1503441403003005040b07a4483d0342e010303541d511030a00461001405000c1a050301100c00040c0d0480001040e01040081140f44144602d000e503504021a486007402c40007c1258541001e903406030078040f00010034000300800d40c121034401e1210000c0c1e40d41c01b81030400d896090b4026401030a409040104100308520212340901008000b10f16541c103150a0040145203d040034920000201d143c045041c001d50056000c0c2c030004101010803c0702c03d0000b907803580703c007030946e00190900e000720301079041c90f0050700d0255030705840342402e541e10002d044405030001001540c14944400803c034581d107840c8102c0400c0508403240c110300c125408950402d541c2150300013000c10540d00b2a540d400b4140e41c0544106200c01c000160ba581d15800b1051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 136311079 1250 136309829 136309837
    0x1020d1805060708040303200706050c01090b040c080615060712110f010b10170106030903180e0406050f1501050903010f050108010f0c02030f040504021606020d0b01020712170f 78
    0x150042d60005812040c0300019000e03100701c0303200b41e440e404540c0e00d040719840f00407c18000d00d130881c2d11122081c42124003800181026000607400042c180100c1e40318078403503040a40d010f07640b21740500d03010b000c00c181c10b0050340d83c0f0185841101003070594441c041001da00c10b0441c0945030607825114805160301c141284101008988120b81c2046155000745009209254000e4404c6008442d501e0085025102440100c415034074001d142c4e82c40e15a054000e851900011000c010011084545e03551075228542e0240c80078240341c000c00e00d4145008811244054600010f41c082e01e4200151801d4901c0815116082840c003951103040c6000403d015180007060240842d04100c0041900b000542c40420102125802488201d18407002642c0b0382c486e004807500724260402042c44241440d400501c4606078442c00b201f02c01c003031a2503a600300d070845410402501c0c0c50304400303851581d04020712009800b030030407140040c1c01a561038801503102850f0392152010042842074642000030162 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 136312329 1250 136311079 136311089
    0x5030c1305030f060a150605041e0b04091e020f1b030f0a020a0209060103020408060f06030c090103050331210507060207060f0201050f06040b0301110a03060e010503010b01020d18 79
    0x90300803000c2042200c4d1100401c80781c0b0130342685880d001e01c3c1c135013101380c01920803115581c030b61b20f1909040c042c80010708140500d045400310b40c440c400180000800005100400e0410000a1031402114283c8900b50048080c864901d00502c155034880c411001115964000c0340028403032820004034050842c00b50801d40140300c400030580c404c401c0c1d0041807a4040910840f8141070360760b5000010f400f00e004d50f000380c8400c3d62200c80055401841c2c200c005804ca040201110881010000001c11084098200702c0381c540000c900c0d002001c03803071910100004544c806460032030040c40030018a01d4001d102d40d0211417100e84985080c1402c0069081c00c0326004000d03030303001c19111a00650754801620030703500000c04110010300d10343c0c418802c0c84e026500c21005021241c40c1c110400c0082c00820403440e515540e20300440c13107128824001405081c0c0183c1700032030468a000c0c2c1200706d0217016400795002e0b0341000d881185aa0b0b000c1118a000040342c102120321120003d009131000d000c83e000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 136313579 1250 136312329 136312333
    0x41d06012d02060109140f0c090d080c1608060714090301020301030c170109020f0d051006090b04110903030f0f0c1203040c08150604050c160f05060c070305030c130503 74
    0xa600810a00041a030441c81c094088075083d0740e0fa52204400c54001d01c452400902042010800d40c030740e05211550003946208000b420304c240300002408503401c0130b204688010002445d20170104080c41164144080421808501e62800180300d4680d80300600700c500b0403000300546110001700806071034000401070003c548941c0c6034a000703032050080c3e004020322068200b415012118050142e0003000740d010f01100c501c00707400010f028201008110844041c040d0500789000c01500d40b242200414090f40c000c40c5080340002408215240d40b42d000740c1c00102001904184e490000454030750100390041c441c2c0e981c0c4074502070703c8140100317014910715001d50002c41032007050700000755004074011003031014065603074809140e80b00004008652285007840000b0310f1480c06a01159001944194a501c3c201c3d228280ca10718084a040c12600003041e640b103203092103000c00c00180d00030000b400452070b1000a4901600a0000900c0c04241d403d000661002c18511008254018103010701 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 136314829 1250 136313579 136313627
    0x3010608010f0506210312070302250b060117190222060305010b0909040b1f030f0c0f3b04030302071101030b010509040207170304050f070b041d0601 66
    0x40020b0241005407503a6100d07440e03494104102ea0880300c5401c0b45124050011031928820702d4044a803035100070207100a0590901200c03007810000310071080048031920620780c0000192500a04450018015504114841c01c10250b564031880419400180444503a54003050403580403029105500c04102d80200300707a80662280c542d116100280d070291b48042c8456030321400401c0b480d00400c48003d90003d0700d01c2c04039010405980241d41c0100900900c030b03e2205e03008160b0ba00c824010352080301c0d8045c0e02d19800044c080e0307123040fa0015000040100900d5440d04503004091410785900c070305d01c0c1c1000141a2100c107010503440c2e0411010388101c255524242c140600290450712040c1d40050001d441d4144070340c482c0c8591f0720000416100e05007012061401d001c00dd404c0b4541c22200d8481c5200c410301040840303002307144564030a40081040e1a038101c6c20a040641e141d20850f80044140000e0100380c82002001c1035004d400f4004030050744e42c1c0c1004851b4402d00c0c480103015110150327 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 136316079 1250 136314829 136314851
    0xd1406300d0f141c0216021c030e0f0d03141306050a0e01020a083a0507021005040b010b0a020c0a14030d140d0903090b120a050105010f0903110301060801 68
    0x104a40b11564940c807401c851160714041480d061252545060343c0e141c010b15840c02d050444d9024280c4c1010101c41c0400030721066020a1260410240c07012558207150000020194803110460a546064900d0b0703a140317200c04003003100c003407100340000c0500040680c40c64540440005480c181e01d20f120503410f110381c0e6540054001d60103020000e0002706121000207155000080110015510203031481c82c0100111340800c0c80111040c8c083c298011595400d949828a07440200102d121003000003000e04201001038a040e441c0310011f5021410036003004041405003440c1411100491800c551f074020042c1d00b2400d1000700c20101c2c0d88801050401700b0414440c9074040d10300c1e00c0c00e4048903000c10350608140c1d1511440103030382c00c262200b00104640c0c50f115070802d2103103a01c01c0c10301802c840d40303e41100404c0d8002c0500c0e00d6801c40c85008000c2c05210038019540181400e0070400c04004c10203400402048450001600d00600c90058001540b000d6101d1801030081d44001c0201031040c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 136317329 1250 136316079 136316087
    0x90103080c03072a05030319030e030408030301080105010e06100806040c03060e0411030d030b0f04020a0509090f090106090b18040507050604081b01050c1902010302070f0501020d1406300d 83
    0xc002510f03100d100130f040030525080000840e00029005d42c0e0004142c00142422000f42c00452890803450105010000381740c00b041000e980030744903840001c039642d814002200e100c45401082148941e80588845401a0b004407016400c1340c1d0541d804140c5000440c000e6015201c1d651203040c0c000c48650421040c031071601e05408980302c046041d16a070702c1c3c422408405480381d1301c5401d13501401603038400a1a282130f600030640c1221900340170342000c801100003404510111200100c078810754080051400c020f208520190500d02c40c10010035212a000c80c001d0421402d207400410a1840403405101c070400c034000091900800d590798882e100d844840d211944221140c0303040c42c0c58043e9a0f1a0740c00f0340e05507094228108001c2050f106400080c44081154240680c10b050b401c01c1403001103400b182c01c241046001e1000540d4170411040e00004a403524200038a0240c003c50900031107580e6058081c40d134241440a0b8251400d010f43c504200450071145440c861140200d6001190b0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 136318579 1250 136317329 136317383
    0xb090406090201030b0f0307050609041419060807060f1110050106051308060601020c090417030c040501080a0618090302010e0f1c02060702030712020a0c0b0c1b090103080c0307 78
    0xb0030707a010320820a1002c140403034800d542da0300d154150006507050141d130034658081c14900d0fa000704040b0350301ca50f140100b82c4402c403d44100803687d0035040a2200c44a16008210041c81441e0041ca02d41c0d25140000b0600340c20030019200300030182d003540c101078204001c90b6100c2c41504070200078950b5100400380940d40640d51091201140d44030000d050070300855100d200b0481a00509908810801080040d00c4018000c0340d0046450656410384011440510b104060204001c0e03943d600b02400507100b0000203005202c03072420306800f1f110040a80003403078616240c2c0e6001040940e201e16090b405440d031892049036a00c42e00d6010016408001281114000b0204c0700510ad440c407c80101d850f908101c40d0040964401c105440c0082d03054080c0c1e4492101030b10640d8a0620740741e441c10030724119640031070790144012520169190051009648204503030f50080400022000401c945000510020300400070115005004400c1072088941c442e910002001e00b424100100c10340c001c103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 136319829 1250 136318579 136318583
    0x5070f060e090412080403050c01060b04090e030910030f02070206032a0c0a0f020a05210f0a02030a0b041e05070e01060c11100509060a050910032d0b09040609 70
    0x10780058418074104042c0081c0902e402c10300e80c070314007a0041401d03201000050710031000c1203003c10a203034a01c1c40c2842400c01902d0340402e4107940b2882d0003065030070340f2100f80500070142c104111039011680e031207800d1914070841c0d080108a01440d80e16101c000e0265002c007039044130002040246081c00300005a1010705039461840420750218481401409410354071055640510b00c2c004c040391411910070f00b083d100a02c8924641c3d19003011840d407044240800b0140b690302902102609014089100070b1100c6030010311600201c0d800080e583c1c10131040280040c00c1d100089014044003c1e601a4400301c00506401c24113090b140c125921441072003502c0b45648141f001040403032240c3e240b000c0d000c0c2c002d1906090b8003540c030104985030481c0a01e0f4420b0200c00c10045c0c40507200c4202400005003252105925110120705001c1c2000b2000c503400105403500000161140982d1144a03001c03690105025a480800780610010092306d0111a8881c013400100310030848242c1110f90094 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 136321079 1250 136319829 136319837
    0x271e010f1a0112090203011b0804050f190213020d05090708060702071202090a090204050c041a0702090118020d41060111010f060608060a0b0c0303190905070f06 71
    0x7040c0000650340d04500070a0300044150400f070100c292690030540603d4001800002c100156001d44800450840507041c0440c150b0745c00c0001340a401e1060407600b00c1e1a002404100c110040c1140d0300c00c114100080c4a100a003400342007a181070703410703103a0718a40b0715400c01840c1000d188056403007010f881464128850100091407041c40460340404881103805460b014112075400c010750188001c3c80d200c442541da0310000c0250382c80713004090265007681600f0b507036142040354440140c40c02400310500d010b4100407240060701d9041d081d50444038403400c41346080c25892112406032180120300c00b0001c3c1403545030a090301c07840b180490409030380a40b0786603148104244043c102110061070320081003540006480e5400b9901c1441000c1d1000000a00002e81d00002c20403607655802c03140015011104000300740c1031828082c4060140a400b49041680d0b100d043e964034070000701545032048000c0485c00ca545800e41100b01c0b603680c0300d0183d40030261511080243d800075403107004009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 136322329 1250 136321079 136321091
    0x9151104230108180a05070e1506160609030c0b07030f051f09110409060b0c0601060215040618061d161d0c090d030503070f0503271e010f 61
    0x80360307840980121140603162080561303604000c81c1c10b5240f007540130ba0712501070102605d002450038800c840141031007440403c02030030302d101d298400b01c1c041e22045001d2442008100b450303242c800001110903a10450109850440d881d04488941c1c4003032008082c0c40f814010b10002c0e54054201d8110054140001c0100396a000c07105000d004082054100305000c146061160750340941000307021101001882c1e141c10754030b1080d403080f1341d2903500410581e072000c224040080010311101d401031207288010813048803515030510100d2005270009003000d5a0b01c0c9880c40e18140f00c15400d0200760020001c002000304040c001c1b40d070103910812100e460250b13406401d0200d40440c895019901d09010100802030808544101a00b000d881144201000c0c00106842e41e02d84064000030351090780c9040e00c80c100400b000d000880381d54400c0341030180910030094800200b18103d4611200b0654202cad00d030b2603000d40c131410090b8266101da002c40d0381c09028120140c054002e0009061080010496 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 136323579 1250 136322329 136322369
    0x20108071b062d06031101210504050a0209090a02040501060f050a12020f0712090b071205070311060112050c030106151206081603020103140c0301060309151104 71
    0x60004810742030700403480301401400403600355804003041c41c44500240101052620381000080210301190300e000f51260340a0040041c00400c40100b0f0a080c02c0c0b603410403428110492151501c0c82c001d651113681c940026080c008100900710100e40c01418682c0b0f58180700f5011910b840300e140040e80107504103400028258842e01201302d40540340e41e102818040d05140803107500750214512034211f50240040d440100c044001000c4040c8102400542640c0d01c66000d171003141305500982c1000030511062004c580d001e00c00ca0302c49005450715541e181c04c545010749280d6001056230045100b007600110b1581d02c0c52005a05040c0201c0c1200c015440d00d904060130b8800600640b004920002808201e4900440d0345900d81000c03014086400b0b13450f00382c7c403880c2035004606d00d0000c0c80200c00410940d43c16200351649000c5604000d011440c1c8100c00f424a0301c4184196010540d0382c0c1d5401d41884084a0502044a103d11051040c100303a4000c00c00700760068001d02160602c09112a24 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 136324829 1250 136323579 136323587
    0x5010e07080c03070318020a06080f10060504050402070501090606030501020409060803090a05090c1908060906040c1e0507050f07140604080c0f060f0c0f01110f0405130e060103050a02010807 84
    0x11050407100c800030f15542d07420004402a14059442444010320b00000301c0060342c40d07100ca90007801281d40c500b42546450a44d00d040242c0c0588a103000480d0b41e5020f02480d98840e0444040d81c00580c0c02599032400d130305c1c0c91801098032036006404545003c0012003040010740051003180e00100080c000961580d1109807a0301c034203140710f81e0190b600f24040099043c02c1c41c4995101c0c4010400c02e0900102c12403881c0040d410070702c0c2400140808007001300f140b6007244520781100c0160740c01c020f46c1c40704110141030300d4400400281c0c0c500606070001c003d0340c0b01c1c800b01c0321416408001d958140350a011255543d5000e8007860f4a956690a80c82c030072420510166030482e07101e2001000b00c0c4000344180b204101c0c4a08800740c0014080041d04001b051580040038071000007801001c10270f60051446085844a0045174502c4800b08100004910008185d90a0386c0003120041320542c07156000038002c00c40c9070401015801420000014410007080380d900d02030003030721056043c6d6031300c20040b5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 136326079 1250 136324829 136324831
    0x3030e0c1309060e030708040303090b0f07060b0411041701050601030905030708030408270a050102010c020c0105031f060801060314040c0608070c0c0803040603150f05010c0516060305010e0708 85
    0x55001030340a240695040403903004030038501c0c00b41c000000c00b139019007500d0741140c1c070108040d148904002810410941e102402e000103002c8440800d0070550041703480d8400344141c1c1e20160447c1d84441c584501603485034800300303c06846a02d03099507250364000c42c001e042004200c480d0b6135440c240008160f540640075040d40d00d0381c0900038500d04241070b036407443c241d040a80241c4081c0360621201e440c1c18015480110a000601007500c050603640080002000d6140c000c181107904082d40300034501d40000d522840000242031550701c1390382c2d403054091129882d10300841031400f5041c00040498000350031505840b002c0d502030040356407011341203410010a039001070181b105080d00b008402c1c4074000c142c1d005912860481505075031511980b4072032415400100194200003020400c1c45c0d0103105801c0300700031200c00d510350325180800e1065107071060301c9035a06105c802d502c24010000240f00d074802030001911284485a101d10000380100b10034042c03d140300c0d95000100b55000d024000781 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 136327329 1250 136326079 136326103
    0xe030f0f10090c0e0406110f090f040908090f010e041a031903021c03140403050d0b030106030f0b100b03090705010e09040507170114191b0219110909070303030e 71
    0xf041080c0e103007075044860380d1030041054403d0b0340d07036440003d0541c0c1940024101088205032aa44490740c44c0c00f004403440980b0010382c440d51806076a100050300000c29282c0007030707003140c031810b900c40d41b60016100b0085002105900614081083d1820350040c0d008480104069084580c4034084000500710015040800741c0960322680200c0c00300c2c000300d1040151030b070540c03602040b480984030130360071041e40540d003c030042040810410a442030f20700c1074501e0203c04800038401d035803850b00d071000c103032103902e038060a20318112001880c0e042544100030020304200c075040350742b40b420622007501c1e02100c2c02040d000a07000031089246103003283c00e103406160014041c00c81140b0301500512042d58011054102e5500d038064500c64240e40b030081886103410012034000b607082c030001113044941c0ca070100e450620700b00440c2214aa0b0019139a003120003d00c401d2048102d190034460031042c0400050b59102d00c514082160040d804a040f83c01c80384179860922135038084a00c51074903041284c01d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 136328579 1250 136327329 136327343
    0x30408030408090d081303110402270319030807020c0612060d020319050304032a17031306020d0f1e0c060e0102070807170301050f010507030e030f0f1009 68
    0x401c0100d19200010100d41c40c005001980300c1d1825078407171a0a800c50840504d0402d0f810900b00b0034070801c2040300c0880001140c0c114900412620102500c00d28501030f40d07501ca00e07a00c1200ca4640713040103080420a00d42221045124551400824031801103036610010f004005003d11a0300308142514410320058814100c941c1c0c3e08414041e1aa60600b000e0b40e06100c0c070b6002c0c0c2d21403c802d01981c10b009019401031a615425410060b030464a0520450030184680e44042074a286618203101a2000c2a244400982080320b40c540346000748852480807491418002400c650002520555007503d621481480c070340301d520a40c0d203030150704c5080d0441400140c3c810310f514403510401758603d201d00f1001500e080040425400c903001103004036490351000615005003d40c1e050052002d400c00d4419614540c10140450101b043c1104a94107000c0c02107420001c060184000090515020301100c005001a06c540c5585101620356541c0d1405581c420101c01f4045d402540d800710740081c1c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 136329829 1250 136328579 136328581
    0x4020a060e13020c0f0106081204030803040606050a1409070e030d05070203030408060703060f08160e0606071709180408071b080a0f02040509030315040209120105040807061103040803 81
    0x6098900301e0880c40d0740d0b940050065000450b803429480500300c11a42c48005200d07114003050309608690346900032500079404004915420b80105e8115030660b80d01100c007075101c0d01c4a20300240600031a400565200140b03000104000440b040150a01f40040760140b4164907082c0d13050740c0484010a5058254000c0c0340558080c0d40150001c0641034405402c5a26165849400d68145401a41c51078000381d01d0303281c00c020445411810002421849024000a51001790f150f2020211845080c134240740500c005482640e840c4180d42c4011b800441c0241c40c80d0304903841203032540c00f8a03044c80c82107003210302c14484109003a911a10503079004428074608481503c54454001114040d203e64055549001c1f40b01e07901417000303110491280402c0884170f9100d10402041c1c801c01410303484e00ea0300610400201034079402a0543d40304083c0c9006a842c1800800300704080c0c2c100300c0301680c0c0d600b48002d12040007030010013001d240e030041c20200051700741d100c090701c058401503901514080b8144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 136330935 1106 136329829 136329839
    0x6100605030705040608070e04020315040608031608250302070503011b1b03020f01020703080a14061807020115180606180909050109021906021504020a 67
    0x300349103080d803422aa004000d0300880c840c0c60104540749002c1585207000744161043c030f280c00b510540d540d01c0c0220010a000e6108544280290320b03100780052004c07408000c2d910303055500601527846c000107489507807094010b101e125209519901d02100190804100760540c2c9120342c01516842c1e213060100b60840e080d01071405124519030756288103d41e401510945003007148450380010300283c0c1004c038900040300000300f0f4190b1001a0344414160454102d501c2010b10303c0d41071280ca1070001c000b40c03c540056403c51b03048658a551150103803032a04d1002c1c2d00c40d0203407000181800004e8103c1100c43c0541e8000e50104188001e440f4403401940a0003003e000303c2d04040c0c58032411b406281360180482e03c00c1c0c2d0007150792440030008200f802c0d0407403580300740c004003000703003107032036000b4a010b452082c0c0318010140c415240501c400b03031400500745200f60b03001411001c8481c605 = true := by decide +kernel

theorem cover : BRFrame.Cov 136151079 136330935 := by
  have h0 := BRFrame.cov_init 136151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 136151079 ≤ n) (h2 : n < 136330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
