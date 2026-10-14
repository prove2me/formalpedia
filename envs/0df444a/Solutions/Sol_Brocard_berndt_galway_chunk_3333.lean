-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:33.089187+00:00
-- url     : https://prove2.me/submissions/69b6aefc-f5d2-4028-be21-a524f9a6c3f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 599280575 ≤ n < 599460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 599281825 1250 599280575 599280587
    0x230702012307030c020f060a08090705100914130203191107050307080c010b040c0e011707140f0c0106030b10060804080a0503150a0b0c010b09091e1e0c01 68
    0x1003000a812031203075004200c05041c6401030100081c103019580804100359900c04181c4124001d00405090381c8170403a000081c01030b841650700484078411280045200d01d00766801020702e10349030390395240c458585180b042080e041410385640100f0000e919a1a0007100d000445c410040304030300400100911441c0e130200d0b54900004403035580240260f00004902000b1200900d400091041e124118801404d00412850032a59401407520a031419404d41000c12600840001d0300c3e0403d02c0c03001c010040940200c11900b090000e89040c520030302382910b1401605400e0b0b0030810b81410304012060050031103000c1c1c0c00659201a200d8104940070103e142c0050181c18a0b25004800e400c05558489090040e40310810a008000c000200b52881d01c0781081d548107c010980408545e403a2984801a44820011000b41d4244103240a6a082c00c90b00349001b40300c95001440b072646d20505400c030400b042641c483c602c1c05414a40c141d001b03404000e06c1e05012001000d8011050310000240c90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 599283075 1250 599281825 599281847
    0x11160b0709060c020607060b060c160e07020a021f0320070203010e0d050304030804061b0809071502033016021005040809040b03010216200105070203060106050a23070201 75
    0x200324140400e000161904002d590b0011f40c03040d00452a40c1070b4a0003c7c08500401030802603900c2032000588518281001020466a02e100344c1c000c035031100c0f14120f0b102c20007a80042d4020f011380c201100010010222104942a5460b0000705c5404034200d000958110805001c2c8040c03000c27840c01c0c10b514007071040003029a20140103008020f420700c0050301078040140301805000c50b60300002d0910649070802c0c2a40012010020f0195501c600c02a00025040c1c9003208170b480350710000b0030088580a00781d00c81c10f001c7e400850400c140440a040b8400310b0000200c280c10b289103c0300000c11050000a006402007095803a02c00c40080c00280741107814861014028208420f102c0815441e0301180c8080b5819940440d90508a00c0800d000e48581101c10140e58a44440c500910403450040307020007440c980c10044450107540110740b07a01950001943c540c002800400055010300001c240440241c00e000c00c001440e42c03085840072100703400d42e42c0c0819001409004640e070003000c20203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 599284325 1250 599283075 599283077
    0x203060f0904082a062a07050a06050c0d050603031e0d02041d1f0506030a0b030c1315141804050c030604120f0801060504090c0201150f0609080109030203030a11160b070906 76
    0x886c0400e81d180c500e00080d00d04451802640c0c001441340c1c03d2000500000c00000e03000ba01c28042c0d070074070340c0c0e000d44958030030003c071803a8901d408080b8006140220841c0e17100f0321a21884106900ba0540048442e40158555888581d0070032002908600420703a004005040c500c0c804250f1030420080070300803002c489a0518000850024801c5a840f0400e403a0070400400300000c1c0480e00c0004289001d4074000d0340c40d40040e001d560318825440311381180001c20f841c10030345100756a030f404c40214101c01508109601c04c2d03098961680705c07081101c1080d4006e0044003218030780d6507218003003404d048040e28151018281c040d4481d5501782c112451565103c4035240112a545c9800780050560140d0b0040b420301d107803100c1e26040740520035080701150950030341400c01e8050752a18100080340c403603c10240821003141c40061411818824485115010717006140b46230f0341c80d0040c00007003181c0d255540000301c042c000813005403800c091002e00789104441a403000c0c18004d8004e0492052680144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 599285575 1250 599284325 599284351
    0xe1002090d0f3009060e01020a0b0c03070f0201050603070302060c0313061205070c0f060509030903070f0509010b030c040e04030903080d0b120c1e12030c0703060b040203060f0904082a06 82
    0x440d0560080e0342200f02c8002c0e242c00383d1b41181d281d00407402d221540c40007829801110b424081c800c841d600c0114042d0b6101c0c0c80d9485034074581407082c2e0a0b203504480050b4560880305c0c0400140c10202c000744261601d072010307a0f02d8050030a184541c1d00205402c241d000902c00d80c0070403c40211442015040011424502174280290783c0344041006100310007480b00da21040032987c920420030688404100042c16900410f44406000340406c440c0d100c1d01d4403030801c0303000018405e40120b0859000c1c265024800f49064204400d00c9404980500100c5c00c00c00360b098004086001c2c8000f40c4101c0500c0c0c0340c0401c0d02b0407500100120007040740a0340c022034101070710180d01641c55042011544021440300d1510072403030800504155085040c010103400001a1510000004500340d0706403485003034104420410b00d005e10003240411039109411440461054009280404c07082e64080d00c44c0a000745841025010bc60700301d44480f03600440700f0002c8907641075400041c40711950016600000c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 599286825 1250 599285575 599285663
    0x603020109051c030c030909140613060b04140102120304060504060e0f0a060f090b1003050615010c030509030c040f020c01050c0a020c09040c09050106050a11010e1002090d0f 77
    0x3c5005002061070040910601035201e1040500408a050052488480410880d048401e84054000c0d04403404c4d8841c9609203210354030320001d407081405488400031900c3c203041c18219500524102549010305601c504041460388004410040d440741d80301e80004030f100d05152516500b51905421410345130340104440703070103140d000950541c61070340254010410744001110b800040c405e03080d024080d545214204086440b81803c5481140e00c65001c071800340d034460704103d4004210b0819680028550703130318040400c1c42031025002d07000b8014140c4d825072141301c00083c1150400e000001c0360b5a00403c09103001c1c5030a104d01d0f42e002d907031442c80700e1901621210081d120b00c8580d8060344503880c1403001c44d0501c03403000e9141c0b002e441144410410f5507102d5038082c00d103412444403d400207509082ca545460300601a03082051510030041c038031400310242c02c0e030194014003105500711200b01510004110f6942d0001750850080b203180803403600c0c4650707014450f01400b81410482c4411040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 599288075 1250 599286825 599286859
    0x1506031b0e010302130305011404031205010b0904020304110924060403080304081605010c120506120a0308090a0f0b10050117040303021602031e0618030301140102010b13060302010905 81
    0x2900784600d80c2440c0c0165103200c10013840c1d003014807030740020740598130f0f1007101e0310b9007040801600d009134080e0315a4403081203a114004182c80090051810180003403101240b035080c40d4014641080c40384410700c041032110780c00304602400440da2a502d00c0701c50b41610004d080c0e084415100414262007051070306056803240c000512001d000204070580009882000c0188402c1060106510900074071100c200304200400510548030441d003944c0c80e002c0030501619000820f8800b00e21050003820076a4050303102030340c088900421540f07150040035042000585884c2400a1961140c0c02208017401c00403004404071100c0d0b08018140440044000c4403218441c6d200c6a01681c54079003da61050201c165660147c018031009416105850540c1c0341001c6580039402807051840842d100c035039895540c814100302080c1482640d401c100010710104a501484400b000e6040c0004a003030369044000c01c1c0c0b01c0d840082d50043c620ba0b1000180304642e8096200802080115010301c17104c264002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 599289325 1250 599288075 599288087
    0x63a110405060313020303041203030203061009050d0210110d11060f0717040c0302090117011a010c02010c17030f180d0e060a0c12020c01110f120f0d1506031b 70
    0x10070301900c13aa0f240e051004664080003100c01400d00b001600b0456078981c50041c010350008d4030701d43c0c40303240140405610f50b88102c861004450004000780a160041d80070322882503020403942040141801d4a0020003808001e800c041d0811a0380314121000c11650b114140b400c041c0ca4140410642d40078020001c1e0710903818a112000034840507682c1e2a18a001c40507080560301c02900079640d00f000080d078460b40052425850508030091111181c0c020070b00d8010b0324410b02d0320380401c3d10ba40000015502c902003400355603114a08010030040581007000c141d030821110700c18407800d1241046050340c0702054140c0086025001400e00e0129500c02404d0f0701c403440f250500407a00890400c451a00c214805040d070368001c2c1c4e0080342400c4c101130003511031060101003800f07d0700351480c180303c0c0c0000045407010302410340c02622183c0034909600209a20070b0000114100051144404200c0203200d1340c440c06031042150741031289031900c040c2c1130760103550681d50681d1000b824090842d800c02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 599290575 1250 599289325 599289331
    0x50105030d090b130f06111c050415050903010f0e0d0c08070b070e0a060809150609040b071107080619050f0a151205010207020f100e063a1104050603 66
    0x303803001c4d00d880b61000381a40340322042e4400c840030500410005203841d0808603600c1401a104165504485610100741e40c0b074800303844401c00200200805c11007425403056400e0104d02030710b01503141c45c071807100207802e5401c4211760320700c46070741e50310420100101080381e40c1010035141010540350b03507a9101e0800c0c6000e0350343c01810007442107000808851248040079404040104814405502d510004100e400d0884801c07440348511208060a007840060f154403800b80240110000d55840d43c07000c144c0300000d010341d07040c001c2c0788142c146080014400600a00094001800c880c984030305541b00401c028441103120342d141038284001d05d110754080c298020f01c0c180300032510501c0c0c1500d2400c1e8a02c1c0c0d9002255641b480320303c550402406400400c01c0d0342c002c860303404680040008000e0300161a0700c094000c110300130325800032410100094501c1240401d03080d00f88910300001200040c00034092072a04038004603e400000b803251254403d4041ca2001c0141014100008203036544401303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 599291825 1250 599290575 599290589
    0x1806020316080132030a060c0f0203070c0909050307021c03020d0305040302030306150f0d1401140904170702090702030c0f2a0d05120406090504140a02160b0910050105030d09 77
    0x2d0f03c200b100803100000b0508065002034121000781b941800e0510050908602c1030001412007600d00700020700c00420b0700c2e04a504614000201842c2c140440c3c01003050b001b040743d09000078402c5d1000350750784400300115900c00e03500c0e103041e066051a009082100300120001454030380030500001c6036000003a80d031b00580070788a403009420102c1c416140c034090f9000c00101240c00003600080c0300740a411102c0c070303400500000c03486a6220303070380e0340a600d0307811020790381040d0401b000030040b4030712044803a6080c05501c40c0901e010170980109400c2070003224080050b03480058042c00440c01000300164400004000d480150b401410449401200300981c81b54800700072007034640d80d039481800040c03140c0d00000b113518842c0e5040401e0460740042c8906408180145c00c0002c0905142c0a441404203c40d120003005549410600b802900700c18520340f1440891520000003031800c843c241d0244801c00b00500f10390300699045801d6550581140b80680c01c40c0c0100e00045411003905d0041d2490 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 599293075 1250 599291825 599291879
    0x6070206011a07032321161b1a011e0810020a0311070609150c020d080403030207020405040501150b09060304032a0c15020102130b0d18060203160801 66
    0x15080c2144c60f0001100500b43e00c0070581e6000c075502d41880010071031b4a1444000c98260b10408651455240089800c024110034204240b00024130545000c0c0c08503035142c0100c1c0d00c001c2e0302d4480c0b29520541c0e01c404500c00703000c0c00040c40036a6403071520210205402c040303581c0490514039203549400940a8080945402161020105000340c00c00307040c80059181d510b440f07072018107102000d0060000103039420840c4d004a0358002c0d00d0750040704020380c0f0b15002042814410441102c039064024016803c0650a01c07102006a84502a8501075401a0300124420481c0c1c0d006891910856000c500040c1c0c3c1000240b00e02c6e00d0303080640354070a4043c01c00110744a05226088013076800100c00c010250500140c1004018407030b140c2c802910700c191604c0c440100c80c3e031020f908034403410020b000c840d079036002d003004040c0c41030004003030848410310081340c0a03680c2c511803100420384000c00c8a0f115004020014440c1400304c03940004107482c178103003402d540740c220510107100b41c49002940c0009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 599294325 1250 599293075 599293087
    0x610060809150a060e2203080402012d030b0102031806090d020a09020d1103010815072c03010c09030308010b21150406050307050604090e0709090c0806070206011a 72
    0x81d040c4004401024520624082460200000c40c01040203004201300140d1210128650384850141010200c1c2090000700a6191075113051b0b03503c0350010812030400484040070318102b11541075140000c1c80d546c0c03800f52001505003014055404048105046503c140883c00402c6081d10248030a500181c46281d03403888900d004c10b0422202000294004901140000780c4c10314030b0780208036010941c4010005400d180300b1524030f510081c41200320039030001000c0c901108881900680004e2b40b4100003500c202180914039520100501c00d4228480d01040d100743c0d82004e02403051101068941702c0d80250071603601609400060149811130640812031556214203040c1d00c6c1464900001d40209500e000928040b1080b00f02c10f015005a0070004000744030f040016103082a6003000b03042504203810000c031240101440766506103a44149140000c048000d8032403040d2712409401240c60301801d00c03691624211001c5c01a904550191004014150180c00401010300c4107260255940c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 599295575 1250 599294325 599294341
    0xf1403061e0a0503030f0a0801060e06030103023c0a0b0a02030f0304110316031e02030d050c0a0b0f100f080a0602160b0c03090706030e150405070e0901050a0e06100608 74
    0x95080303d5051321000030400d181c402e8103009002e2641032503a400c00740c0c3c0c2c0c8480c412914100540801d58000340d0500044c401858440d0401401c4826004248103000122100c1c04510000340b103a8030b8844d4038a8501c20702410100000ca000c0c1a017608003600c3c01c0d8000f2030007580c07886001841e00f4205008170100741000f10300d0717070b41c035800e102c3c004d080311090b442d2903041c413000921074401210b010030300e10684008002e29410440b40903800402404c100181d85909a03116807003000c0c2882c1134041c1c0206a80007130150400d00d0b024001510070348070700e0300c0d010220b2211500d1f55004a0400c440040302049004400113615403c20351041001d6200c5651003420700102000000080100140c0ca040011418614025521a00407141210203c642d588402c0e0122510120410301e9034120200d02511181d0800d0904d420a100f0381c11101541e0355003842e50081c040540e5084070a94440c82880701951440c080c21b0181c4114030050155401c0141074858000d04920910b03040c0f0075a800060300e24 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 599296825 1250 599295575 599295589
    0x10b06032a0403050703030201050f130f060c0e040513110613030312060e0f100b0c1e120c010b100908061b0417010f0522061a060a0f1403061e 63
    0x41d0751280172a014241c6030f14029020304402ca0b080c81120000388005101c520142d4a04a2201d41140b00100308245944894002e0442912039400303100c403a03044c590041e2264451280f0641d080a0a9042142d0f289031041a0903200807403548101004d02002080411028100c401c90364141000348020391254050000b030610780d0703c0410400280400c010026921225091040869038440419aa00c40402a0280c01030707014142056114800000c001c2e108203010070207003a1018202c071840c2480101210440e0b128545000341da946400b100406d50420300e8111006c081541014000c007030030004066607803000140507044025904003124080c50004007105c0c09000359040400da104a40080107000c0c0001c0001581310502c1c140020b101c90141440e1005102d213048552644465942c07a0140a000c12503440c402003108000041c60980d280300046c8481d8140d0380b1a07141e10005034201030401d41504050704100e800030010089183d43d060724000d01403a96408200d49018004089403074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 599298075 1250 599296825 599296829
    0x1103030f19050403080702060609010b0a180803030c040317030c0a030203071e021f0c081308040b042d06021009170a09170c010e011209060908030702010b06032a04 72
    0x8038510307100c180014117a0140c0e00c184103503619000c0702d82d25100c00742801a514003d10480900b14428401d15072400d2107481200454001d040080301c0e450b8507449a0750542e442511a15181ea9000404204100501017600c4510305d0700941c83d819032400c40c03135030324a600c20307140c07031000301a8004009421035000b200c80b003150390402c060f004006450144065651a82e942ca110b07003185002072507080c65400c2d030007a660004d200d43c2d00c4901c141c1b503980b08140c1c180c1c20800211281d2a0a1101061001880001d0b10040c41540d8403015850300c1189108400314220091001c0026000014000c1e0741d000207411001452004d0001108901418a4059210310550300641441e0004620b5844c030f90040c00d010071b40380b207142003400240842203c542da940c1c6000907180898050070441d800c88d806460f40c54481a40d0040110b000c007003075a034440841d44040c00c2141c6240010003444405603092007806d8410905803a80c0f0300d07508107030021010b001c0e019940c0c00c070001000e542010382d0350394110943d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 599299325 1250 599298075 599298121
    0x9130e0604121202031618031a04022805060f04030213020703110a05060601050a2a03020c0616020f010212030a06210201052d0a09030b071103030f 65
    0xa0604042c50440b040c80c0345a946007000400011895800d03000c1c1c1c0c401c481c041c99200250010030541814242d40e8000e9003099155404208040000854140044401c40e048183e502480501e0603104004600410420045c0c0074038640b241017015800103415803040d14401c40f2115161040305130604810301c2560402900490f01c1580d4640300700b1039401600400b446616581d111409220700316036510280000940b00e40d01510103d40f443d4000c0009201d40b29003860070b07403204002601c0385445629100012030f403522003811407030140756050001070100c0504507216850107500b960a904461035041010b40b090040380725a41c02a8001c001001403135030351000854403490a001901c0091403d8429642541c8146188080703000c8a00b0032058407640c140c40f05410300344208001071154100308802d000c0e21400c0c4151903804005180604004071031a038401440905501e441c01c49240094649030034440709114022150382d0100070360f036010f56611403070344060340d5024065484c00707491036500da = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 599300575 1250 599299325 599299333
    0x3051e010213090603151b0c0f02040911120105070f05090a091404050d0504060f08130c0b070c05030111220e010306061d191d030307030e070605090609130e 69
    0xf03c000d480d81211301103d016041c483e14081480401906032002c03444002040784c5220103070034085008401401609004032a158031401155001c1002c072400001c0a4445e60b4000031210308034986803401060b900c0c0180002e0001d1300380720394050081c00b044110f840a00c403020445603803a40743ca2410200030301d01034030103001c90b103a00100c1c001c0b11001903a040d9494066000000035180c02941241c040b54055076075200d103648000301c11034030700c0009405217000d95984020308000c01d0013070402c00c02038005d500d40c0b01ea84051601d8415444141503100300d0080c0d0510096000c1c2c00c803004c0c00e0f5066084103058400464880c0d0300010a1115590011a4040100300011091100ca07074840301c103031488106c01c5007010042c6050100342d240121030100981103e021095140380d419004a0199040a00d014405106191216086401c100e81d80f500081d6130b8500c0c00100081000303013400078681820940e04d4150089e010517454480c02030701c5070003828503c0e4280000754150703000800444180080d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 599301825 1250 599300575 599300579
    0x302120f04030c06080606030a09060e0a050309011709100509120307090e0105061201090b0d020619020d08042111030d0603050c01140412030509102703051e010213 72
    0x3006003504280030989844003607500104240340546041405240010003081c150fa0303914030001c018003000b074402c82d40c040e1103180050f041d0034100146c1c0f2030944910061525034448200041010749001924100f840046044c0041c126000ca070700c40d0f0480c610000440c0aa0311080f10303610f403440c5a84400a011400810803429550048030788003614081100c02002c0d9030303039000300055070003a40c0c188640d038140c102c010807000016911550410f0005001d240320301420303130002602c1d5080910468140c0051101d180c001c02e0b4180700801303a00c3d40500b003000d580c1c00d0a4075500d00c102c05022a8266004015901c102924050b250340d0408030314200450707545558502030b038006080703e0701c0115020721030800202c28660042c1d104c24002503403010f05a040c1498410560440c4240c101c0580502004104c01c81c040e450380b0520700c03014485c2c1c0d1a643c0729a1a00c1e083d00300a030380604006040c02503102d00031702c000b8001195401c480580d10030015200311031001d14500900c03440034403000900401e540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 599303075 1250 599301825 599301847
    0x403110a110411030c0d0c030f02040b04090501080703031b020301060e04050307030e061e0f2505100504030905041a03070f080105060312070210030204030c0b030f07020a021c030212 80
    0x60300240800582c0c050040380610440c1451a004c10345e100c1c4024581400301e480540007503407101020003a1b030b107030105016030000d101c00c0481c0d200d5001784d98400000501808183e805000780ca00402d4440e0043c0086451078500400100c2d10b00c030203420305007206442d0819594250400005420200c070803180c14181494440e40d00e9014045c201c1c04a20b04c600d80003c0342c03420900f82c50354064001c401c80c00c44501c0164801c031581c440e031100c1110403000d00c41c100e2144524032210304c603030010b00d60764070020f4258244180b9001c40381a04108260030b0504100002e0b611103406d0007142c0307041c0c9002c140c282c0003030f01d100441580041102c3e0588603042c0000380841c0304c12101c800f15091039000308401c0e01c0314014552100d91400242031548000c200c4080181040c01058641c0001c51400600b49030302c960383c1405510a9501c011781d200c002100b8803248035984c8080a030044182e0008002c150402c2d80031481d80340c102035541e05480b41105a050034103000b800000034802421036066966982a50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 599304325 1250 599303075 599303093
    0x1180e0a0504140601051f050f181311190507051f0b010216030b0c04031403040e0f041226091b0d031d04020d05040b06010e0a0b040e0403110a 63
    0x9403d40d844803040440805030720010403214143c4002070300c684490103041c40d403001e56003003010a000802408001d10301c0340e4007542010304a04140c0c80101d844488a1034200070904440c0004610341c1071424208100c46121941104d2070070403880700510100300c400303105884d00e0103229400380007400b45600ca1039412004200c01c0c0f480d20004e07d000c0108400d080012079503038500705806400c0c00d28520040c004984003003811755010081800082c07400d40c495540203103400f0303240480d0050b41e00108041c0031800300c4000032507005a44207082c40c20b80c94203489810781d00b851140f04005011302c0d2070100d00b40900d41c07038582440034031003000948913051041c0d1319a904e0f00e140c0e68a000d001e40c80301c080f548070720740300d10801562601943e8208440d10580c045011251511061542c410360070815060892801e000385481280109580103161030b040c4000340207502034201052245018030002e00803d1504c206031020340390202d6140080b0740d80c9140070740b104540700040e01d90611900d0b40600402010301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 599305575 1250 599304325 599304331
    0x40216020415050102120706060f120c0509070c260c0f0c040506091b0d09061e0606090303080c0c0f0f1009030e13060f0b09150901050901180e0a05 65
    0x241d000c00940d8514000d442010b0100d00440340141c20000101c80d40c1034160307018107041d5000782d40c0010b00d1582c51130701e0b10000401c1c2d07002a00480359130000c0c0c030030f02c009007040d11300521003610100c402d0720b0102d10040c610380384d81e02e0081032280516900c0c9000d0f00031001d03007904202c0203480039551788078503140390f41d80d002d01100210191082038140055030405010f9180940d60140660000740c403107458000d0360014055400c803020005000418451185010740d0742803500a00e00001d4108444025400742ca030300312071140600d81888010070031681d1200306003044940624002d945c1d520f90040d241c50341c0c4600c2c0340b040540e124072a030038240850086241a000079155040380e1081e40800c0b2540c066500d000406404070706071504102c0c09043c003030030407040044041313000070360f03503840365180b410362112a0005100c4640110750f80445050400780c0110092040030810305011580000810b50300c541c625050402000b000040040030030103c2d0b24000d070150040000b07851520b10813400045c1411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 599306825 1250 599305575 599305579
    0xf0e01090c09090809090c090402031e0f1006110331090b06090105031807081e072d09050c07060b0607051005070c0b0c031b03010e04021009030204021602 68
    0x109000060b40006880b501c064150f11600c001e060401c40e40401c010000018080401ea840802c8002031541d100c1c0300440c801c902c404120240c0040c680ca284144ca10018040303840b0070042018801600c1011001e641112505e103003001501c2d02c2c40103840d007580a807540c440d0100c141100e00d40d04581c181e0070380f040794900d00d01040787d1295884040b402680c1c001c54002d40c1100c020810900c0f203501c24801560b201d00b4442e05e0003404d4400684e410726110b0117610459060300a248880d400c4481310308803032540c0392010020110142441910a030102458140103103000754001c1c1d10b04da070301403030709190f0050000c0e6200b0403861901c200c50560030b5000c00022a1514504554900c40e03192036000e541d18150400d00405880d090500120020000600f511051260144061001400e2141840e00c20540d00c0034513070304c1c0d04100c500302862150000d95082800800c2c0010310200070040011030340103404503402c002c0c140c1c1084003540c8801080d017000c2d410900014101040c40c219004c0c0c0c01806200b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 599308075 1250 599306825 599306843
    0x18060901030b060706020a0e01020d2102160f031103180f0d0b0108060f0c0a0f03050a02091003020d050603010504050615010c06060b0306150f0f071e15150b0a050309010f0e0109 78
    0xa4023004988900405040c1008107801e50503a41150b602106140320400c001107005141005140341c880c115410020221502c603445480e003003c240c0d021346140f920b640d410005500341900031003c0b40c2030716a00902d0074011000d00030032001039582e0b0320700304681d00d4101e260b4100039619069011b44030402240c1da80101d8072604003180452552034200d54200e0741e1940d601e046d51b24209001c03805000051300d1400d98075001d00c212807040c0d49502c0004a64039054500507901c640009002090310340c0200001c0c0310341d01d080108404144c01141081c0d00401c9020200004ca141c2001600c4104c0c0490010305102d1a051001c9807450000e4025409071408407411316188941e8480040c152060840c0c0301804a818418052070050281c0600981403081941285180010f6694503540c03090110554030300b01c0c0c038007400450890301c1c41041441d0070826503034020203040010461061141d00001d400f0002c00100203010b2681c2948007070304081796080306001081c07070302361024060000c2620980c1d108103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 599309325 1250 599308075 599308097
    0x1e13080d09050117151906080a090b0117010908040608070206060a0807061110090503030601080a0b10050d140405072303063c0f0a0218060901030b060706020a 70
    0x200600448045402c1603551150244440780680b160a40262080900500a0200c103c072556000e0054502d80003460318141c4991410500424090001d49481c00781468041c8110103d00c1c040000e40c10b640410007500856001e408a40c0d0042c803071518058401c00010402207281e42d804614103006002c00c2d03003110702540300cad0350801c01d050565100e061019405a141001614060603140c4c00c0e05103500245c5000b0740100c602a000c1d01c41d2074100300c907290800000c0018540c0c000c02c02d29040800c001c400c2010055840c0401d000f00c155492103c14003034003080300d410494564104200c86032580080354098142481c0c0380c0d59508450051011440c4425400c43c1c0c04943c410441c887c40b50002c0050000c1e8481000c0c4c40304904000b0410750312050401c45a01100361031485444031490301c0440c2d91158038182d1482c80b40f040010b4080414140100207100c0711620f064402038280404442441c2c0da402d010005034014107601e500141c201402084003801d000701075003e48a6200c241d02c825610003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 599310575 1250 599309325 599309327
    0x6030201120213060e180a152102040f061e031110020613080c060106050a0f0f020a0b060316030609051005060a230603190b01140409021e13080d 64
    0x8000c1900c1d019901c0f40a0b6400c00880b8480d4a086958200250801c5510412603040406501c01102c3d401c141903160a030300d20702c2e0413a1454010050401000180f40100c5010f80e03403003640c142d1000684a55200c8100c205503190540c4910300610014071108500100b0b8031001c80701844902c02a10103200020708111a81040a589025400320341d01803c21075950481580315042c400d101034500a0050058100709681040100c2c0a451182c95560315451440700040280000703003940d5042040c1f123354075015a4001403040c07059540003002070015035070540803a00d0940c40500300403400000b08000018056070354030003901c040c0100107691207000da5403a0740701901e0099a40e01d030051070241c006c0041121680c101c101e2001e0240c074900d50400b081c0005001c41d0820784101e10503145080440b0304540f5207105a40e00c030507080c20204206004107020204a000740c1c45070014540d00040d000c15100390f804c07072000409990b0255951584414030a001c0540030b107002d008078038454a4071207002d503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 599311825 1250 599310575 599310577
    0x4050d030807020d0513060503090a020418150603170d14070903061a1c061401060e090f0c04121704060503010f170c0607110a27090203030f0c070306050109060302011202 75
    0x200000d10455110185800c808948d136a0005041c940319002c0d01c0703011001a9602c0c007074800100c10f20b034001120003180c0d08010200c00c400350000760000b40740a10800018014408400c0d12040b00b0302500e84420016031040d020f0048440208000c3c4940020841d0990304446010140c901031801040030b6483c41c0c82c1d00076000d040c000c01039800045800c420020300341007258409194880d0a0110780701d2040d0000d000c4d410001c2c0c01c4400130600d441c240b2900340c1082441076611120080c400003140c1000c00d8107510700d110358010240305034410301a04090210006080081c01c503444181c50351642e94850040c01c6d40c000380516039079120060340010f080100407403d1124244200060a00b00b04404100b141b036074481101159000010303800503825039518012180140004011412210042c101d00748c5400410786800f10709500d4501070340056100001555101c40022601396175440c0030450303152800d091f80d80010000c504040001c10652002d80012080301d1007070700c405070041481c82180080e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 599313075 1250 599311825 599311837
    0xb030114061213080d060308030f06011e081e0907210503031914070309150e030304150209030a030f0801230d08040503010213031115030109020307030204050d030807020d05 76
    0x550710700b0401040c0b420031004a09100244241101c07840c040300c961429054a240b03a105032024080401000100e980e040000b9900c41c90910341051209015455441e481541b00842420044224000342c0c3e880c80381c0004681700c042c1c0c3c501044892034100c95003035480c500c6005620555007000e03030705c0020600946009460542c0301001c0e50a555950400d00c40181910a1480086484e004c110108109103032007140121401e55020030202104c0c24a060382c030600d070880c5001d192402c1d1b0040651400881641e410961020001c100f00c50682d202070040d0144040b26035160203240c241d082015084450520071402589488080c0e0307907030300240c015002a03140740c4001070314480c816011624009141e000c455101c1c1c1106d504040d190400703c0d0890f0080804001481e500741414010b0141d003416418803060b040fa41c616042002d1510302c00c5a01040c81441d1003141c000c00030646807406038050f038000d080080c2407502d6003c103e040050005809440900140c020010303040302d501c1c484c000f1a08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 599314325 1250 599313075 599313097
    0x818100b15190e0303040308040e0a11040b1e0706050702070806220f021503010b13150c0807140d0f03050a060305070510092c01090b090604240b03011406 68
    0x102402c01020203841d2001414400c40e41030008000c040006401100504082c11000302c91400500d817031404c02040f290110080c20481ca414482001501c030780750304480b1886200e0101c0f04a2051070f04411480b0f02600100400080c10501000541640042e01c1d07803c641e00e0a007124402d4466a2007a080d02040e070b80c022003481c01c12401c00011840010103090282d10280006043d03400c4042d403440182c00c00c0e0054480c886c80000c0c648403000380ca1004030098029504116503200d4103402c064030400031860000d00c0d1000c00300746041031001542d031100c400b1a800c0c0903642059044040284a80680302c46070002c2031810002c00d941c000c842c0314100540e980705004005241c10300d020803594a00c6a8050410000d01c0a4040b4031220031000d44215800c242900681b159140c0c0315580c000708050300302c001d5181c6000102107042d40c1c0d4080468002d141900c0c0011031041003158100c0450400c0e0381e14031070904240c00003501081c13681c011412149090407000000c00c5000810542e44a82c1030010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 599315575 1250 599314325 599314357
    0x61633020306031207050a050d090602010b01030e0615060c010204060521040f060f020c07090608011415090c0d0e070e151522060201021c0513030818100b15 69
    0x100c0310713556140092000700d02990484135054029a2401c1c54a41d1a0940c40d000803052101013000c0da40902581c05800c4003424140601c1c1c12501000d075840000030540685910a0340071041241c8640b401c030746000b44110001c6d5aa59260800079040e42d214041d40301c030410340030b1151101500c0040010707000b191b01c012011098515916540302900c0080d2400815680c01c1182e040c07409030400280004100d00300307000c6013051400882608548100004002910a100400810310519605643c24100458031207460b5110480d010805010345d9502c4500d040c030f42242543d080100264540c101e13003520151500300e03994141c02c03032180390035054020f404c180ca21001225021650015280548560819421440c0d008201c04072000640c0e01c0240940d60000b48031190f1000c016040601042d182801e0080342410804d042c03200081d044042c041001c50780104401c8410b02c5100e03203580c80b40200b00c5034501c0c0d1400d214001050b24a02d500d204180016443c401510f000d402e0302c440d54520b00e6a2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 599316825 1250 599315575 599315593
    0x92705060a0b0109170f011b050d110d2301050618040f110f03070831031404090204090513030e15040317090102010c0e090606163302030603 62
    0x140050094a40e10506200c0e1142020030034440445c004d681025030500102040c03031a45080908590704200b4a00da0406040f00718100c01e03412804564010002000010342c600d02207404051078060034048100080c1030101007007524004541803001950341500c0000540d9031502080464460406528158103078002d030000c840c6000c1d0710840150a802401003000d00000c86019046d910421086248884c00700034004040e6001101c9648400702140c1e5059008c030b1840004d107200d5100c010000c1010240700e17008109882104c61405460b0b007012a180c6654032408031501a402500410b0703e83e0786414002034045105030f102441142c0c05481c0c810714034070000148a65602c5611000d4403100c0100800400100c04140a140d2000c81c5101c0f103440d00320900009007526864540700c4200854090120050b96500c0c1ea500c0e00458210b400e00e41c0d078806540504044480c905c409001e00c0c4910700c14110070142e0708600d12000c03000802001c100449481c614040780030580321150154000560 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 599318075 1250 599316825 599316841
    0xf1b030501020d063f051903030c2601030807110d06060524040e0618040302010507170402220908070c0305060f040809100c061b020d03090b160c020a09270506 70
    0x1070214620b002d18166252a404035000c41071030070511402318002555551001c040542c04810480c4042410000f0071818001c1500704082800c18003001d09211400038031982003021581c80005170050203841c900314540780b030a0010042c8041d104041c09a07034500c0c1041946461001c0d0882e10740801c0380c0380b43c141818240745114408000f00f0310ba0700000000342012000b000071a581784200d00c80d600110702d1386461350005000401070600180301175401c00503c001a90740c500d18428006240c00103200f0426510302c1741010b07044004000d050400001910807d000740c68420300240c1c0d004900306e0741d007a200c00015041000c3c040394082d00c5650240103034400703813400790604111565940f80c03100034065240c81d500103c548880c428007490a4411f24031546c80d4050040c42d20480c4942800c101921640e21042d0b4078060007030040410802003001104141e0142141c4945903801070114182030762104606d00042c0b443d611a0500056030440c200220210407060072482c03940800506216215011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 599319325 1250 599318075 599318189
    0x9070e0d0609030e060f040f1a0d0c02070b07030810060c15020702010203040b031602010605010f05071410090302030c0106230621090312130f1b030501020d06 70
    0x8011810400c0e113480c42c00752a03644401401c07414040708100e9554a02d08a910100807600e5442034408003000b802c002000260b4100361070741c400c580380001c518160460812070501c030494100010031a804280b1600349544108a18442c8601d201c48440700303a110003080d14800090f01d0003e11980c0c4800c1200307240c2c400c80e0050481d151040c01141c0c142070701c5854500d401c0e0011a039000319a40c12040201410f9424000e0000510082c20b002d08940d0b50044020210300c82c0050180c207680e0b403240c810340b03024820802d001812420140c100001c2903c0d1a00a4803640100703140c41d600d6081007000304030045149002c42c0001c018843c000282d500c94800d122030b035000415662550718210300c01c00c0812207260038181c4105035078006196200501c83c03200307020440c0603007103103803040c44001c10744009121000c41d680c401d40c10110103040f0010608070b428002186420051255001164008030941c0320b0300f000c01500c05030750243d00b01090b020110000004134091030855142e0005075a503030590b9480c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 599320575 1250 599319325 599319341
    0x80c0f01050a020705060417060a051524030c0a020f0d050301060f03020903070b130902042102030a0f0b040309150e040b0a050603010b04170a030c20040c0e09070e0d06 74
    0x401604c100369562400a9020303002079115007082e0b00111080c2004006c03d0000700d42c84000e003242041241800c016003401740001c046290b02854910082212448604420503103241130304295940c2ca2500082481190300842c0c854030140c89013180b0340102071404100000e146441c2d580b6141543c0c0b81800032030f03203160921800028150300300b01034511624140f0240380907281c0c400b0655a290828110100301d4100f43c0d0112544a1051209210240c030305104c0b03109004001151074a410b01e6800081d04000d4050130042052100b01910410400804010b0340f149019403105000a581d8903481d803000c0503c0c8406e00005541e0802a1055190030b51003e00413500240c01e4508d02502c41011900c242e00c01e0f000f00350148004a4204402400780d0441d0640ca10048081c05400740c0c55940130740454441c8000030b000082c00c09900e00c0180c10350429014088d4002d01c28800b040108902800410f40000c0c4139000c0c809440c000b40702c00e8001c0721004100600580810041149611004010b0101c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 599321825 1250 599320575 599320577
    0x412030513020d0308010315060b0f181f02010f05090312100f0803040905010801020a0504031e21080f01050d030c0503070605010e160c0803070507020f0310020a0207080c0f01050a 79
    0x601c841d8000d0303140d00d003044080900c079895a881e40c3d4110f091403528181c07030410f0502d10034103004092052005a40c2640c0201c10060001078450004603242801c00b1100001d407500500c1c05034844900380060f48501040c0c25181d0000c20454442400710000d5440454031258664001c1040e4141031201e0026251700c1200c401d0302901c01a290700700400c00101c1640004690b0344041800c1c84003410900ca201e0042101030000c503d0000ca030039018100f40200d1001400c044d40d03901928440d98080c203050544998011004022440d07140e241244500c00d4102410000340d0383c40000720045c01c2218810b050301d100900d4000b0783c00842d03070100c2c0c822011600c200ca480c001408014009180d9014a5020308900311240302c5510700240305c50103c003078071050807041020140810010a160404681c1c20880c989031181e03640e0024004500165402c212064152250f84d403002c41c03200d01e0380c0c050b02510a880e070941f800142d41c2c40c1000c1d56810040c00d44c642c8810000030b018141c1d80210f00509a00e003003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 599323075 1250 599321825 599321851
    0x1506030313051c02060f0702040605180f09030405060a0f030b151b16030308090d020a08180d0b0c040f0e012301170108070905070503070212090f0303040314070e04120305 75
    0x7250f000c1001c0c0e42046c0005125500049034140440c6060300804000c1c05080e01c20703990344088030310420b84100014045c0007518140c400483d909030000c1c41220080c10000e8125941c1d0050310500600002c0c0d58506c41002074a03111440c0414a0407818001c9034200100c40503082c00d5503465425070007425421091810301c03070413480c110b042140070900d000860013500c03403d44a141c042c14184c100f44181890500b150040000c510004500d401552210724500b170b0b10304403000c84000410ba500b00780d144041c049090792002c0002c95003403000100242c40d01e22a4115266903901800042d8080a006604421442503c501e07245004d08100300c40e00b94052420304c2035040340901650140c4003c3e00242001c3d084075409021000c1d0328000d15401180c40c0c50018514603111038001d450340c44d040038200d005007001034a510303030fa920003811010022004042d690b07220799038540038941c441448401140c1c2d0040c0c080008245003021003140c416138000103480c1e01040c0c81d441c120024200204074a82c400c503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 599324325 1250 599323075 599323129
    0x9050c18040c03230105010233061c21030204030206040b0304020a0317090312180904061506020f0d080609070503100b03040f200a0512150702150603031305 69
    0x894100000781000880045082c4d03541014002801d00202d8812451030b0400300492170444080d035140c0031403825042402c00a65190040050211b1031302c1c4001e80006500e0070520b2040c0300030418648a4080b02203040704504039001d8040e0241d020340e1201960082003404200134400c441d5005560041c802844900e089032240d4403401307011001034807030781181c0d4042030855084c1020040c20303900c000d01f03c4800d410283c080203042c0c1441d050f60702c41c600035040800820708201c21070700000c030f5070306034800c01a07040790b280c10b4000e68560000d00301115601c1030000c0002d1190040c00d02030b00403900548103c02e20303943e02d1003c0c5e400341d1018010102c440403501e000580d41030361001550055110f110151403210440c1405a030280c0341c41ca0400074004030902c0c05190b955a80c03880801c80c1e106a070f00c4031201c09201c4129080804100c4c61b06003e80070401000035507640442d8101354080a03080c140c00c151130328401e2555a0040c1448213400280c1d1030814401c911b02210b05e01d032030010141441a00b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 599325575 1250 599324325 599324351
    0xc090806090d0509130c0206010602070f05090601110f030c0d090b0c060c0a0203041d0114040e060123041814010e0604030516050723030105090a02010e01020f06040c09050c18040c03 80
    0x510407a807410040c8c0001c1c0c014451329605000c408001c2c826004044840c50a140005039112030240089050000c1c40c00e4a0304115000d0160710800d4628405607a1161070845000da100e503140804000041c0c2c01000100e8148014000e5900744c01244004140c25a41c0d841d240c1c205602840b255800d52005100016180c2d000422040d20403100e0015652207500d080fa040c00807103145407615104ad810004502031a2000081d40c504540782201800d5043e000d8460460a01c92070300d070703060b8105082c03800040004424003100455103129120b40d65141c403000100600700c82c440b014414442e0082d1001c900030921800150441001c402c4000e0007040f01e903952540b800e00305502c5032450740302c04007440f00b040194240710b40744800f00307800030720941c90070305e0049850b6440104002d040c0702c1400460f00341c5034070811052804501314011909107040c0303400c003d88808550b10544c0c0b0703106d00304000940c1406004041d140074110042d001201ca42000307007003101070400c0e41103601c10955550031810600d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 599326825 1250 599325575 599325581
    0x301050420031e070e0108070e1804050c03150405060402010c02040f05090a110103061d091212040b06040b061209030d0603060e06010f120b041a07030c090806090d050913 75
    0x1031038111441d6240f800d02c000003804500780042030b190600c8880a0b843e5450703600050150381c04416480c248080301c86000000d030901030000141b0180f4141c00081200708500054000b00610342142180d0009920400c0c8011040c800c440c020140c0c1c00480108005500680c02090242d20003400030030103c40900d20401100c400b1220309070316030b0261100c5000e01c481e00c010841a40d10030b107070a02c01d10741043c11601300310103d510f9200d09044240c0c00500c0305030080c00012040400c41e0100ea0340d801e06060800541601614155000c0302140e006c6480c5150500c00d030600c1c40000740036241818500c400e0000a030300010100c401c2c81c00b00300a006003604181c4070f40300c06103101f04000520b280c07c140c00181380c904145c011140c1d6014015043c00034031410f50514000c0740d40141050865544e601d02160909000114005250b031410700740304c1183e415030480c007140f02c21642c85c051241c1d1751f654402e6a0740803e036241203068112a03c030002c0c081c484c400401010501824006455040007403823011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 599328075 1250 599326825 599326831
    0xa090c0608091e15060a1505030411120d030e010c0c020108100305070b130e06150f131202040b0f0f010c061b090e070201060513020d1d060712020f030105042003 71
    0x10540145684c00c200320002620f268000e0360560b20f8002503800c0c841826080341c14180280148040803000034100000c01030400300801c0050880120401154444d913a110b02071a00b0b900420300301080090080c2052040c0c8401410660300d01c2903507070b881c0c0c005441c604c0000c3c00100c5c01032206500030000c100208040d00c001c0c0a48022182d44040500c28955200342a4100d903811a44000030301ca0150745040c0710b00c040d6000003022903510101c42d0b82c495022700c07c1b10541d00100c07580b40b0001681500c60b1001552940c001d50302444400d5500d010403032611440101d1a41c42210300c041e20341702d54820b0706084c084600c00d8030005140b41c0c03040c842005002c2010700410004606100c01d0000701203628885030060070900080c8203850601c0001035650700050100509941d0200c0c1c000309002c25908800f004d800080e0388461480c1c22694620b03180c40045980d0b001180718585103400c01201ca208541191500070a1581540d080100708000b40c0840c1a66407541081c01030083c480c40c80702d40040d80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 599329325 1250 599328075 599328133
    0x901260702030a020c030c0d0b07051902010c09051009030b150312030403110607080c03040804050d03090603050603030403030c0807081b060a110a0503070807030609020a0e090a090c060809 83
    0x14030f03220403020091902c4d1140202c03038040c0d0400550000076885010079120041c2d842020450642d5541c1000c8417180103c40d120656030f0f42c482d028900b00c0c1e8040d4400c501c0e03032400b03640d079241154a0f0001d108a5410094204000942804d42000462140380210b034018281d2035010f4a0004c4150010340b4000c0803892500450400005010400d508412031880c00040130340a09050b00d0101c6010385060300040041f0301549002000034204141441110050b000c014071000c80000b150500415981103401000d001c48c1ca4032000c1201031a0010a0b241280c2c1c1c181c0d16600c0c50100c954504d080d90f0018101198100c2080c0404075041c584548284024104400180885d00c0d2a40581c0165004418030300381c0140208a80814258080204c91307008401c1d0411110940320840c080713004044681c05100f00910114503840c0d1158002d840000c0311104961000c05510303414120b9080301e5081e100180301852603141000003d00441c0002c1c1d00807200d0701600c9240d07180c5800340006a1003201845 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 599330575 1250 599329325 599329327
    0x1602040b1302030a0f0c0206190906050c0706060f0f060e060705031b010506040b060a05090a050306090106030302010b0609031c0207030b040f05100506011b170f120a0908090126070203 81
    0x840301303011a10031101140d88000061040c9403007540082c1d1640b42c040d1400034400c084c20003110300940650021001190b202c03608000c189407070742c8105c0582d0059001191b505040c01c00024005142c6216038060f101b900d00c130b50407070a00d4504207581b00c0c1c130140c4000303811410912940e00401c4050001d45480c85403100450b0f600c9691501711400c40c0d1000f001684550315000500005440b14030a490b42980941481e60b80c6006c60000584400b120b075011b15858072411080242080c410741000c4210303482500240304c0f404100c010002c940c015810705ca50964800d2801c080c5030311400d1003940d4181c1c1580140e03462507860f07868818282a0440d8243ca048140e51480420040208458290031074a07110400c5981007050000b8030800200a1f904960045500c100e014480284046c5510810b0291116a503512500071242a5041034103c2c0450740c10190026010640e80e0140c0e116041d40400100c0c6448400c40055400d0311085400c1c540b4070100b102c0c08622000007800e614050801030f0011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 599331825 1250 599330575 599330581
    0xd031a06210109320103030e120714030c0a08060f100f090b1e0904120e0319060501060206010605030c0a050403050d030e0c01111903050903160e0106090b1602040b130203 75
    0x2000d6000201a000c0600d840714030344e1000307450904c40505496041c0341c1000c516a0b503600140144408540c0c0c0c2d1842d020b00c441c0021100c0c8a114001666201601902e107000b59041c1000a030f0074007031144100070703080780000651380a0b00702e51466011988424010f95651292020300d82d444840e0000500960f41d00c040021915001e03009101021074550b214200440c03c0340400e4507018040c00080c65110451003d0100d64041c0a1f0003100c802d024003110924520248400c03081a03032880180c0d6464a00b90000c50054070100b88103040c2c0788181c0b1803900d5511070760309601c0242d11507542c0e41d0401c03400f8400400003642c24046c0c034218410f00e5034041250110551b5980c240180528560305210440611410b560000f06070b4820504d40300d04440a0b8001c20b0400352420301c10340c200e05506020302000007030100301c401c0704d01e001d07141d1003083c0001607030b02c0385016203a40fa55800f40b1a00700300b041c80120450001e40b2140c210b8540b0140011031012004e4021402031320804811001040e004020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 599333075 1250 599331825 599331851
    0x60105041511060f060d0f05011107061d03030103020306160c08120f0c09010f050d0b0a030b010602060906190504030e1f080901060509010b070f0f06060302030d031a06210109 77
    0x3c941c009140070268581c03810b001c000200c3c08420410005c058820030030044050080c290301800c10780c0f07603220000b0b560b0038051030480003c240f000900009440580001100b480000003924140ca50240c01418030b0303101c0154074910300c800c088881c0708004034030704034000040800e400f6290211010f088112541000c60906900020017009404500700c18810781d1501d82e032082920a00440500b0501e549040402c039440c00303805161105500045444400010041c407256140c3c101e0f06164259803c5440300c01940b91180e44c00da9611000040f4100035016114a55009940003846030404004801c50b410100d00b0300e18440070300300c41c0402d100011b00c0341c141d0801e09441c0e0042c0c01d20b000704001418000060036860047c048c4c8040307508045030b2082000911400c401c0550340002103220004c54502c0e100010b0802804100d0090060b41c810302d00f013038081d0007910101c22400c04003040e0f0003181c40c00e0100b15006404040314840c00111220440380d42080f80501074080384101007900304407920 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 599334325 1250 599333075 599333083
    0xe04020f030a051c031508071d06010905040b04200a0908030712080c07050115051003140f0712180b250302071403030f010302151c05060105041511 65
    0x500c09019401c2407090100080c40824070030b510f90903006085141141c2c1c41400c80c0204156588010071006c4800d0204964100140354400c0b91601484500e030381d069000090103043d01030710b40078045002c0640030b0000d8500b40c0c20850240c400900005001c180c81401101c4d450320003e06401101d1000500b1501aa4014100c1020b080702c20004e520b85130440e44d41e41155891a4840000c11002c000440e08021401c012122140d420a00070b06c0089001d02d09103844285a2044910482c1140d25003446035020340200900318410000c40300c5c160744e482c44108005480141a10100038005508081d82422072144c0000d400503500c8601121485150043c03110350b01812a5002d00394400001c0500756004220344228000e900d000741c0c484060349414501360721600d000021074000441004029400141018104d9000b111225852090b401c0c5e034007040d100e03190207001c10300a40e03242018100c3d6641c02c540e170041410701d805454a5600da90303001c4040310030b020100000d03010b80703108000603038104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 599335575 1250 599334325 599334349
    0xb0f01050c1f09050604050114010e0423190b04060f020913180803041a0a0b030d1803050d17070801050d0b0a141006030e01050108060705130902040e0402 68
    0x8200980351141c0a5a00c0b540d80b40040c01096070259001401030025001e40c01030001c5640c0071084604a0a04c1c0c5801c0d03029104400009030180e01000c00082c0f0040000702d503034016030b0007240c0000c0745040e4078500e80300b142d0402034007141e43c812031188125080e50b40d000c010185000f0884a60941024602041901d8010100841d1030340103000702c0c0841d54030724000080807101402c0c0010360080010410741460200140984000b10120400c8280f040100510085081420308882c20f660395040d13100c2100e10344880e00d40c250780403003106560240501360b00d0041051941c11020140ea80360740f1782c1e01e4032002002c0350000408900e54055561b0f4000041c540201c071a082043d6598145404a802c10b003806401518000f03004010402042c0f0960140c2035a4500c4c1c24240d0b904c2c50040345007124030301644141c00c00a86442450a0b0084061140c98181c1c3d00c140c01034003c6403140e140484840c0c1058030071200c1c00342040400107003200584010002403100001c441e01d10f107090700400004030958 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 599336825 1250 599335575 599335577
    0x3032316020f041416020a02040507030204060e09070f120b040c0216240804060207060905011d0102030f0105010309020a090e0a0c080d0e041104090501180c0504140f040b130b0f01 79
    0xd81d5030311007034050340d0701164860640000c205020300811700403440c0050030000a50450314080a10985980c9600200b0a5600644034094001c41c89420f00c10400760407140f840000310800c0f181940c0c0361052203c50a8144908008100e220102000504548041c590700c4003590196403002d170000b50141c603401c01044010760903142290b080b0900240240112009030410200b800007c04000d480c1c1d05803030078150460010042c020062422030300900d00100c8134407141481d100303c2034582005000316881000c11350380c1c80b6103c1c0d01e000c00560140c01710303840880e4003448050002c546210b240c401c140384d5842042c010300c19a0707400c0c1801c80d11106aa0440340040e0800421000e0f500d0b00452a0080d203078003074900251300744400c200d00b052405190000c60105050500016115445420300c81c0204945c410801c19046188130946443c840c5200d151410f5441071000029440c02200e140762030788000c3d001290400081c8005043d408401c0d0341090b105503914a0130441e41070200c0c2d8140801d1013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 599338075 1250 599336825 599336831
    0xd120905193206030703020f030405060f0105030c01021e07050d06151a0702010e01140a02010911061611011707081005040e0703060b0607210201050a0b0a03032316020f04 75
    0x4800c942c049100702062003401030100001154480d4403c0d07044800c4900400141a1030b41420303d8141e446120944240c1143c1c2c0030200041244e180228101c414000144c0051000641860242d42010f40c05a10717100d580c000c10b20b0025040e12800680701015208100006444070989443d14400b00079810031036410200e0650500f913071402c182107400140e02400d01d001e50601c80e000480344410341c00c00000348118041001001590150050009980316405a0f0806101c1c0c00501815000710784424241c04442120780d000700b611104882c40705041850200d41c0201d51884204030440c05840b0400050101006c01041b01404000760021b000116810702c9200104520555180ba4078080603191981e00c428500781a0341e41e1080340ca080391300008002510000c21011411010700801c641c0140d402c200008801c8003243c40f59071651700d0010588813400b170442d10112840070808807102d0400e440d1501c0501a030001402400c1004d0522042e500e0409140c0305204101d605145041d0003141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 599339325 1250 599338075 599338139
    0xa1a01030b04060506190b0a030506040e0a1205070f0b070210050f0a0b030a0209010e040218090a03050904091b1a040e070c050703060204061d09060d12090519 70
    0x10080c00740381e00190022400f01c0e01c0e49400e170004130410306007a200030b60300481200000f2408400d0010701440c142507103007080035a941c0387c00c0c442a2900c040341181e140d00910407010000c0d81c607220000f104905c0d07240860a005055540c00031840303031001d00b580c000c6002d8040000040d41000342c0c100401d1008424865070500c0e00ea6881503000150032041000c0e19803400e240561410054800f51940050088130385503514158110440802c0d50141d00030054903144d034032044c0c60301c0310182c01685180003e00d03c0403120b4404031440d80140240c160303c680c072085c2e4070012640c0c40c03400c20b0308500d00c40030b5411107500d40240440c100444d80c80707440140009000421424020007000c40c1d00184a041844011f1000d10b442403d0a5103038000034011440428003007800c0e13501000454000d0003100b180b100c298410410021481402c81e1404c0d885403551024000150585900e000c4003840c500f014008551210000303481e984401e4010040380c2064001001807000010780280080c5000ca00e11105413 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 599340575 1250 599339325 599339333
    0xa0204050925030b0f090406050f0606070c0303080c0408010c080106031a0102120d2004150c230f0a0308100509060603130c09060914071805040b0604170a1a0103 71
    0x40588080c061560318841d40e0915103548080003d03150001b00042c00c40d20b03044c03400800130311003503d40750112190700e000100f05040080c219113155400480c2c0c120f03442e1840c1d504803812200201440c510510500001900030300074002d8030b100381c1361519460a1507042c90380003403c54501001100092102e6160140581d0f0046001c0e500f200c4091031141c0d8034011012200050034901d44200340f014902d6001000380c108000182041e42c50a8000500c080050003086848213030030200135040c0c52282110101003000301c0446140c02050308192513072040c80c20007840c01c00404500c160301241120080141000328482448040d0000325a42c036038a0401001003112400020003040560b600c034100c207030500c04081c00e0500200070741501804050f8031440c0c0c20303016280c1c4074080020401248041074005000d5201100c1d003004501c8040e00c0d0a10b48010070010340000032005070031440810002c110000500b0750f03042d00100510041ca1650228502130030040f0f010f440042e0031100e400c006100203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 599341825 1250 599340575 599340631
    0x10b060406020d2a0f060b090106180501032319020c0a0201080f04170a0309170702040e0d08060f06090402040e100e090a02091e0406060807060503090a06090c030b0a02040509 77
    0x1880c5c0040c00448500c685185c50001455960b0640e540300c0b0754100006250b40d0f00c8142c20901c1440c007030007981025910710064059480c0f22041c07181d00301c43c0c3c0c00d03d010340b8503e00f4056a401400921307240300700b6400d0b1100c40300302c0e4400c3c1c00015254100c01a050250350704114003275003082c2c40c4502c00003945055222041e0140045850309840040003941c00280381c03003908030030100b40c0c001446001000b44054030017190351010208034000e500b450f1499030f0030100400c00420a83c0341d42c07541d06076503885508116021507101c0c1c4050380000e09106203801901c882c07003e44060602c910000c0017a0800b41703100d401c0401140d200c1c40a0307030405070411002c3c01c80881d41e4012140e040d200b08907a5201c90641420f06104123000c42d41c4115018100400d001207900503001300e45600041e18829a2a00000c842610049483e40546c0d8807400250000484591103141320900801c0c40c4c4400544990724615840800d5501c41c58207a0085001e00040c90300080e126005040000c81c1c01d000b403010300b204004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 599343075 1250 599341825 599341907
    0x204110a0e150301210b0a09030305090f0606060d06030c0803090f0a18113108390a0311030118111003021b280309031202010b060406020d 61
    0x92008801c2c03249041700002a1080d066540300b0300802880c0381141c0100001c22400a041d00001d05000c0030a041e101c0c00f051407142034100c1405041c05075205001d0001c240c0c40a4000950141d4404c000404906030121480140070b000d005103a680e0720810410550210030041180700b15041241004034880104000c0b201e82c026210116211201c0003c40026005204484074503c1000d0000041d003020007021600c80c0f86410410f8031800c5c1c581070241d0741c1d04a10915000f8800800035032907012110b05101302108150b10f040d94009800050102d0a0001150b2080350030030324510310380030149028000c0c40400c1c80c03011100c85580c2000e8540d110040071351240d50f070183d034140c203049181d07030320a80445200103005861541ca89101500141d41d503648161940e0600e012800600204040310300e480e4203054142d03039154806800e503140d02c41042418915107007599600c003040516500c440d40030303000811164001d0224001c0903100609000d05240c001c545110300c103206203030ad5100d525480340c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 599344325 1250 599343075 599343089
    0x3031213020109030b0103080702120102090307030609060e0a150e030909011205010e01060b1b07060f180e011203021b030712080706181e031209020303070204110a0e150301 76
    0x49085034a00042c1c410161580010f03008154020000c818403130010002c02d420742c4240d910b030f02001780c6060418200d0113401f107100d070715070481c00042000c1015034002c5a12030b0701a9400140a002c0f41c90450300c1c08000003070445507103c1044003041320b101d041c455546860450405189407d0416001449a04c4140200904807046092040a0000951141281e103001340b00820005840d8001c6218503003001545443e89401141d9088042ea00801c011080741e0082e140d901403a038007030106555801940d0020400c048085800181880803107a40070700800c984010b40104c0c10032828024100052921501c044a164007542e83c8140c03000501c100442d41c0c0100d15102c000483c0c680701001d882081d5010708007a082284005894000c40f1005030428401c940c010003060b00d906ca00040f044a0840240106201c58070340c070041d24060b00030288140c401410762b45040602d50004003110b5024203002203200300031541160440e00b00020b415000741c100c1d0341c15840381d242c40c9001118401405814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 599345575 1250 599344325 599344351
    0xf0d03051006210c030e010b06090a0306110c0307030507060b0108040201140c01150b0a0906020a0f120c05030d06053102090f060c01020a1d03030304260d0911030312 73
    0x200e0100c00403c0041c020b1500c60006100c04040c40703600601030010410344146951070480c44030310300d140030300464501110103446000c00d07071b2a64607a40002d1000000c201446841000030b90f400c05000c0c00202100741c801d0311031607140c00403030901c0c41c125002441c0c0c850501091100303110140c0e800c045030707904021702d072031840c0e83e0f4919404120380508072008030b154003003072603110109071f03458000050001004150f50700c520283c0e482104a07a103d0b1044405000d41c0c0a4003810004242d501ca03c003045c010302e506245001c000c484c1e480310703d15442040c507a4016943d8600502081c40c2600340016911000700b100810040d5034201c81c0c16640c4849180705243d6400a0070318216100d91230172802d003800051070507031100740d075031680c4d40130751300400a10300000c000711031a942d03420f46c0084a15018401500035800d641d61540c1c0c1c0070504642030440c90b5000750010b14100c100e00504004c0140c0e0080c0100032820b0385240c50081c0c1d50200c641a4a03100f0f170002d1080c52489031084c51326507070000410102c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 599346825 1250 599345575 599345597
    0xf11180d0203070807060c14010c0516050a1a09010b010206010b091c12090905090a080a0806010201060f32010516150501030822060f120f06080f0d03051006 69
    0xe031908100c1d6003c650316001c0c0410016415401c011050001c2303020308240e0030034040010f4424221401d8000c00c2010401c00d20880780c00c0c5400103c0c0182c50761080b412994090083e0700c83d1044e900c02c00b104405512054020444030500038001c0f250300d4007080c0018000fa50420b802c52039980240d8008030302610500c050150058040803c40d110190401040072100921682c01004003100f4000c0100040c10300380032504a0500041103101c1303d4002c01081d0500046100031560007002900c528115074890402051180010507024000c1501c0f10900381c500c001543c40110070907100101c1d008903255064050190f0b40c000e07007251032440c2c0e03c0c2d1020f48540c0c080d10300002242c0c0c070491602021131503e0004010400240003d012041c0209588100c044408404a44080c4907000c6e8000090403154803005050080500303d8003045900d501188080e5040602d000320760302039014400f0f41d4428100d9000c0054144940d24240e525858140b04900c1d044200e2841004070707110382c2e020440c0518132 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 599348075 1250 599346825 599346829
    0x905010609020c0f0d0c08030105010c2f040b06030f0c031e0403180503030702010207061101063c0b12070e03030a0201051506040303080c07050316060f11180d02 71
    0x22405807500d55030864980c4210064141e4a14101441c80c10502c00d0a04c603010041c018800c1200195021804d94596801c1c480111180304090108071500c0b0300350401d40320600401c4d02d000e500c0701c601d034014500361a2a1420482a524001002ca00a0340b0400500c42814400c24003294042d081d0025a0346d039484044540c42c00300722003030941151107241e00030f1200f0981d0045544011080d8114000301072515801055100d120b20705c03000b80982d008250410800c3c0c0241c4410744801480000020800e64414a0340d039150300118034014840c100031540c901c000c0350f5000c001a902181440020f0640c03e040506c123261058182c90040300c00c0000c0020740c0c843c4036417a0b403108400c0140640fa1501824080030740600829a81803282070f060000080c407504103c0165001c8035019550300c511070300e0340c101c01e8541da03201140664450001300965a64103402210784202ca9110354000182e18190102200c120b85090f0100b00402c5010050113180c0c6c003d918050604060480d0307140c081050f9440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 599349325 1250 599348075 599348081
    0xf14030312070509190605071203150b0c010e07030510090804092901020609032502030303011503050a02040308030c090a23041a01081303121104031415010603090501 73
    0x8071072520081680420108a034840e01030800c465081d00d989501c0ca5030180318031200c8415010711000104207000043c0070540c40e0b51082c65903081401c0000b0300750460b030800d40c0180300c00d800c00c0508541c000f814110b8118244210201b10400c40007a0100c1419503030f80c20f44600d14000403d030083d40300c1144905101850044900400b08648100300360502e215041d503504c00e896401580f41841070300711651035400411618030610322031004c5e510b03000b641c2c40c40b000c20303040c0d40b9022540f6803050380c08c0c040184c40400045000c0c0402134000e100b42640604002d064503001007800c04072600501c0100000341c078007415603800684600100380c46042c0c18002c642c00f1510340c0d101071440e40100b031101d000b22011a0040030021000da030140710b52503004180c40c02180b04c0000880c0056260b0300040c454140c65605500d105100386400740840c80032100c160160b070300c40f541050703040702d00040800400c0b02c000d0b540148038054001425a000b114941c03848640e505216203030525803100c600b0420888298 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 599350575 1250 599349325 599349337
    0x2041103010b090f101e120f0605010e04140c070510020d0603050601080d0203040303050c160e07030c03090804060c05120c16171b0a0e010308180909030d15050d1115040f140303 78
    0x1b10080000502340e5404001034403951003002c0c04204d41c8403030a400c0e420035000386554100210014803083c0c440340c02c04442075115010550740390190014420100819000400752021303841e070003152060450400c01e05280c01a03101c046150702a0012500694010041e103040f81d8143c1070643d140d460068509082c001070304940041e0300280360b4041440280c6021450040005680420001006010039401c5540c9643d0140040b201030004200b40c40c1b003003810300b4109101e6010323075072207515624200040340c1000d81206032130742141d4100d40200314000c03d1000100924112800c17440ea250304415101d400010301e002401c0c400c4881440300e512201c05600007404280401421036a403820b1564032074100546023455400c540b07220103018648403080c117000b030030a0400b0f1858040d43d84e01c000001c04154504004503410600c000616644248500a10740c2c0070f0701c840345040d1550310400c0752505a074900e150000d04184014081c103501c501c087c0d010b035907107a4040541035645100181c9503014070707 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 599351825 1250 599350575 599350607
    0x15040f060f0f0c030e10030c0305130c050d08070b04140c010302030f040f0c1214010501060504080601150c0f0f060b0619141e130f180902041103010b090f101e 70
    0x6d07600c1c901005a0550001e18100b040b9502001a03444004540c00710b4269003001030030342c41d507411050103036107021850004500d00c03940038640b034a4500d540d51588800d003101c007519210080301c0551800c8606020202d0414000d2030304500d5807520a0325090b8812001e04040e002038003e0070840d040100a00da560701070503c5e0084046811a05d11300000c0300001102c000e4865402d10b000042c103540910140c5086e01d40c614041c1101c3e81c24800c3c45408041d000c58000304004030041c0c0000400c000821032551180110204526040241051401e42e08000303400c50281408011010106c42854045034031018641340002e40d1030003110012110b0300840321820341420381a042004050000e100503c0000700c4150415039059131850001490580303441038180c0b0082000d84404820800c0c2d01c5610050308c01840003c0e001c41c95002460650826008452440c000241c542c80c1860210904041c44d1701c102c40c0c040d003105140c9401003526241000c40b0041142c00400c500c810350140d0031160100400d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 599353075 1250 599351825 599351839
    0x12130c09151a0c0106210b0a090c0b0901030c11030f18040509060712020705030d0f1404030305061e03032a1504020a080303072003040515040f060f0f0c030e 69
    0x52100c451019a103c0142000250703c1d0030310016449020309800d940d001110744102c48140d070340f51102c1d03030036150080030484502e0b034807122071000031800f5070508050006070074221f844000c00302c00034003101c030700c010b181050050103240d0f00b0200b00c00008030746455214420107911603400d0002010001102c8000d10741c0142450100700242c01c000841c0c1d44241405d0790b40800300c040050900e4120704c10603001070300e282c0003042200450340007034100603090440c0b81400202c3d0041e849000905000948003140080e80b81c2040c0081458006400c002004002c81581d280712461000a0f03503e2141c64506907088c4070112190842d1030180b4071041000d110703030043d281c4100301000c41803500710080780d00301c1c800d6400303071004140b8041c0041643d100341010388801d400c0400e0103c01076420341042c0d40003590740c801000041060f454070001d500502a41038039091702e4504000a044184640760810420045440d20ba820b01c1a40640324039241c0c5040d0a24140411203424111916400703240240e801c494 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 599354325 1250 599353075 599353109
    0x10020706050a1803020c1c0b041208060f010e09072106152f031306020c03010c02010e0a03030b0d080f03040b010f050a03080c030c010e0312130c0915 66
    0x1c0c1c00441c420000440c0030420350b4542e20034200301458081c0043c005034000e550034019810a440c03440c0004481244000f44c41002c0d56800b503844404890440d180c10030314002c80001c1d504141e946401c641c085070b0b0070301c0d001e03ca507000810314854031450314441c0d6541404103050b18085c49081c04028500402030300c0d0f215001042e44040c000380c0c403421403140e805142c50b0341414894a1302070349064884050f111800084100015214034284650005010400006144008c0080c401c801041c03150040c00080e06900200360031900d15950000030359041c22003201c07400740080b9516800c0b42d803500300040c0480e86640480c2c00c03010085030040c12240000744164080c1204000781d44142e1141804003481d0303803100300500580c50726214954001c1e086039002d0000546180151018910b0380003221300300b8a0a2022900350f800e1b20030f0f0a40c50f50000205914680841d0004560014011170f0500009607983c1e40c900103802e40f8450211041d17079405c440340c0c1220400e10020018281c1607800d41c1e23100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 599355575 1250 599354325 599354333
    0x5090f03030c250e060409061b1805060304030905100201090f1a0a09020f10050702030a0c050102100203130609021801090614090906040605040c0e010f09050f1b0c100207 75
    0x1409900750625422200c6101e21a640351507282c07000382c0b1a26200d0351a45d0300d4020622024280c07a040c01c4502c03d0301d8201d64441e0002402c81021114119a94440d401d01d04c2c29400c218030708160000d41c001c2504004100200b90400284030443e803083d1800e18405021407412030041c00e81c060010001ca2130020b050062000364590000d41401075004000302e40c4580e850941140c4982030025004203075440c1d001801d103031403580b101c03007681c0c0d5082c9030346001403541c0000d0802803141030480b048000082e007440b055a04100807601008017600c11842c5041403961000400b100c524002c090684410041085459141c546a60540425038412555031124460b00180049000d0104841c43c1d8400c1d1300c56600d01085410b000390700710ac014083c540c6a0741c03201c201900340100309640403042c0d500005044014000100d000304807540c0e18400d030a003014146825500080c00035036440680206101c0c102148515004000d81c1d800001942d6410b0b2200003030420b6000d241349140c06102180710403c2c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 599356825 1250 599355575 599355583
    0xf0114070c0f06020f0703110f060301090203151806060706021b101136060a030c020d0c030509040c1809020403060b01090317030a270b0108060105010f05090f03030c 73
    0x6542c4080100100d01d442d000100da5441d0f2459611089500c426820008156444200c03803080310064501a0306803512004100507520031fa105c00d4100f0360001c00c201151216492165144904441c8580d141c41c00c0409581e08003005000c40d0b1144070300003408020044507034101c03080121201168982805901c86480d10303610b98444009049041122140d02141280101c1e128038510301480341d80078848006001094040d07103c103030390036a80c214184000b13554103805450030101c03903036000c03400030000d00c8024100b0791401e000c1e030b083c00743c00c8500c407000039000819520341d400190b400080743e1001c10400c640041d4a0040d40744840c810100c0440c4184040d001007040d42e000b1001801601900d40044801c5212488042c00f003040740940d207685080301c0001503410421035030012900c005100d2003050b01c030503080001282c80c1d5075181c28108000c0c40101090050802c3782c007802d82d43d850400003902c80c0c40100000c03800c00c08001528540ca45e5905400c540700080a03040783d0300e80c140e00c18050b550b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 599358075 1250 599356825 599356829
    0x1104140f160201061508090709060b1e190509040b040515030f030901080106120b04140618010605030a090f0b072c060904020d0b131a01020a0b060f0114070c 69
    0x200c0301d002000d101d0750328014043c080850391484520080c603401c0c207400302c0302143e0241001d9454040e001c0005603035421409070f0400f0f0100c40d840e00d540e5809058441c810303d0640d03009605070341428061a00360340700b0034049442011260030003d44c1c60054a0005000f4201000c0c52540b080c40c02040c4148800c11060154030000141c049601d041003d0888560302e02540c06880c2c00543d5400050108521420311012001c44901001ca22100300304006410344240700319801e41c0030070310f90800c18035107007507010340401c810740000280480d4102100101684002440c0e164840e407110144010482d520701c07505001500080155064104044000d2904001b901c007075141d1001c49100c41320a6051050600201c2030003050b582c5024410802d100103500004180f010312a504d0b1512011130302c454040d071060760b942e5130001459005600201e18007850300d41c0141d04550007404a81e0020380302503481c42d0040f4040b10404001c000040040340c0c24050f081071040f0b04000407618404000240b010501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 599359325 1250 599358075 599358091
    0x504090b090f0402011b051902040c08040c05040e030c0708010509060906160f11011a1e18060616030906020c100503040b0912040303020c09011202030a1104140f 71
    0x40301012a00c1002494841a0307001d001c04103461001c240190b0103002581070b400c0d42c07100c03201c00ca040c954441d1410f048003400c3d20280c00201c0c44000c0c0c11441e25104d8500406440e08218515091984689440219074000c89000e55a2038002c1001c08508000380e03000c806000080321220750b16524400d001e8081904c3d40452407149002140d074540c0d01046d11480b4101501c1808c808161010045400510580b9444103002030080c125204e25401e0190700c141f4150400102204110a000e00c0b114000349200d44040c50440d600003c5969540b02914150300259005007425807104c10000e144c610406000303035004405882d0450802d90056030702e10440f1f04139001c2c2c68072241c0300000c2c0125400b00250800000707038204009000100481c6e407030342c0c1010001003113840c06041c10080d40025403043c0c20a50241c3c1c402902c291062030102c89813070162400d41c03440380048140703030b001ca983ca6509440c010300d055003c0c25800101d0b2920b920040580e4070020400d40b56040441d00b0029140081d903100f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 599360575 1250 599359325 599359331
    0x80a0e030d0204140906101e051b0607020706030b060703050918070903060f061d040501060f09061815060503073c0c03080a110c010e060711150c0304110d03050409 72
    0x1a0440c0b5101040715404c0001e510f41230004078240ba14a403400c1d01c44100c00d000c0c0f0005000308200c070210f183c66640c49200640042c1148d0070044006841c102da07541c410700c20903040c465945007d842e018141d0350000c0d07243c00d01c02e032254116000250b12103542112500c4400200d810001001d078007083c400100d9004580c20002481401d04007803e0b02c4003401420140d010030310014070524404001550b220303014a00001c1c1c00d41d294101c3c4a0307203044075404405102d842e0f034010300c0034000303500829a9241010070200007460701c9a1240d8030b4594540300700b0b403d0110210004604070301814019901c00c0c40284100d44046060001642c05071101f480841c4140b00f60800d8003e1900030703004080354170380548a480c0c8583d603400c15480a084c2150380c1c0d40c0704003400d01405103085007d020391802e5401034000b400b0245004280240f04442150384440f16a1002e0801034441203e000301d20381041c100e06005549076242c0c10708112003545868041d030008645a500000d01d64808e01900640f200d5074824 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 599361825 1250 599360575 599360581
    0x91e0c0605090d02010804060b040f0e0d0207080c1002100213030b0705070b0109051305030c0709050f01180b010302160605190e1b01110709060305120703080a0e030d02041409 77
    0x1101e150040071803658100c5110440d1601660180400c1c0d0b13032085c806c12002c29400c00f1240850b09440f40441100d44807521750280b035941903c28445009141500d100502c0020b01e050413056032070300c95481c914021114400300405082c800e0000b200d0352000280c056540c1c1c400a10b100d030881d0380350702c0140e5451070103001140030315104a02301c030900c9810192000b00c60342040d071008020f000203414018003116101317092001503418405066840007100180000301d161005000640d04c00070720b440b02e0f903a00394006000c0449250f8003c107068107400800030304c4d00c800c000140c00902c24a0090382d00b003011714a5070401c000c03558202e50712031011061851045034507200c201080e294000000d10341034100000b01046110b105080c00103c0e60f0525218510f100003c0c155810544960000c9803101c4e00c501091003401420040044114100581c15191084039100200040130181458420304d403601e4100c0b6158000708181c901d0042c1d25001103560369641c0c03c1c04c00103501d08e03d144d44d00402c100400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 599363075 1250 599361825 599361827
    0x3060927060709150806131b080f09060906070f020a170a11190303110f040e16050304033c0905030c0402210709090911030606030f1906091e0c06 64
    0x3c51419130001d48031103141c1c1d21280d04110500701d0341503141c468550707201c1458080060700011905101680d03265500d640c208400b040ca0700f100010030801580e403000c070600c8803890000501c2030380851740f89021031004484140032400c040609802a10f4110440e58440354000c5c000020001140e090f11517410034500e01201c5a1522105519101220130f00c45018010074002d0300100c0c8140702002c1c209281621424100c020b541113500a461488000010808010300c2400c00031448156400d000b8150301e080e03980240f00321008010800700c00030010f0118180f0307088480c1c078005095215400030ba58109840024030900c2c107072240d01c1c4a4450091400c000741007034401c0328000c8404020300c2c9030071440780d4a502c14000000d0301d2001005154840001d80901c28440c0341100c5100c0da6051120208050400d0b1400502402d400e00c40e400c07591031520b88400015100c800c1000051190000c10035605160008113544980a0580c01000f5113129403c45402000c00c41c1500c592552120f041d25440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 599364325 1250 599363075 599363099
    0x608160201140c130e070203070308090313090c1b110a050f0307090b0a170313090b0a032d0c0e010b0f090118090f1406060c0303060927060709 63
    0x41200d801c1070400c4045403000c10f05100401c00642e081a2264a0360b60315448280350400c2200d240005810102d118000c0552015451707410040358001141020444000a03480000c039204040720255580140d46806000348900e8002d19000095400c18003520300300b845100100c00e0080348284094000400d1510b8586680b510346400a40248201ca00340803048d0000c0c02c580c9240c59010403006400922004801200c0892640340c00107561507070380c800c26040c1d114a65421001c032460514594000135190140201c049940100944443d0002c0081ca41e4104600440f9920584040500e540a0200503128078040354200301d40681c0c184e036a8404140c06005140a03564682c00030091071520358071400d050b413850000c000d140d1500e01d6480c4400401c0f00c0b841d00c00c41840c40e88a039004c4881300700b19050306500c10b40a44119183c00c0002c070040380c580c0f0000b80800d2081d095500450542242800102100090070360001003001440769450303604d48040703400d038000505051002c075804002ca1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 599365575 1250 599364325 599364341
    0x20030c01170a1a21010b0d050c0f010504260c060703090e0912221e03020423070908100c0f05070f080a03020705010e0a0b0615040f0608160201 63
    0x11807007a580d622403070001c001400703803041c0510412141215054465585800d900301801c0c80c0c0c01c003c0da0102c044001c0c1425100c400c0c2e10944134003240c00d011000300e03002080404e4000b0084406800c41c2d1140001602c1e940915041518500b00d000500b5030340b0408179085030710800f801400c03a540800800c0c2004600d114a140007000074494440410000d4881d2101c030741c002e0094802d4070740d030b104008103110301a0010400c0307075400ba0406440a00340f010041c1100d02500343c05600e10f03510801401c40d4400350300300740f200038001c0d96142c0504041e003d210b00210241001140c1c1c82c801400c0103000285030762850300030909207001e03544540b03070242e0261203034a00c00301c0f040d00c8000d10398007450f07010356242d045102c0c20b5a0300d444010f4410002135803400248172403c81ca40f00180c682102e804c1650071100580460b80490740251b804001107066040c03456444801150304824503100241048018000c0c0c0e400709a01c603070400340c0450202e40240c01ca80c0315400c0003048158408101d002207081e07554030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 599366825 1250 599365575 599365607
    0xa050708070326070b10090e070303140a0201020702120604020a120b2d250216050f01090306050106090303081f170a051f060b030f0604020a090320030c01 68
    0x40f8140f04800302441501c0c404011841801d80e0400c591500c8070120003030200c4003010302d40072031113081c0410545445100880f6035144014443c890540e84c014000101140c00030b03450040200f4201111803003501116251607010307007104d202c10f112170340655841ca402d0318121711032801c254002c10315020800f0301c0f03081e00390049845101c0391201ca2100c0c141c81d602c191010407401c01e10b5860101181c0c1a800a8015281c580c1c00b80c40d035804040c10643c2176140c1860000c11034011f10304140c44004180a10420b03100100c0d8590207500300a001610000309950008007607504280c000a5040d030042c003c02c044a000c2e8540d400e1313561f41d40c055000c002161a044100040980c102800000507006095103200b0111084401e04042d0380c8a0510300014022240e4070401080e02c3c814542c6424000d4400408444d0f01082c15400e1019100b0013004008202900640e4007040c1584024072400710140216041181c400e000c1c4500714104410706c1c03005018500034407600c078108004d5441003102c0c50f040610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 599368075 1250 599366825 599366843
    0x1603031407170310051207080d020318190f0b12100308071b170a020f0409030c030806040914100b010806060a03090219180e010902060f071b080a0507080703 69
    0x45240c40259600040d01c0d050408116604c00300c0d503502c64503c05411000e241000f003a5aa1078034443c1441c2c0240001160300310340052110b01c94060307800c0041c1c00002c00444504d0138840c3c141c6006404102558400240442c14580000b10580305400030100c070040380560035082e030f84488140d50141000d100040440d4001c00130003001c201c41841c038071507158400030b01c4566103030360703802810b03003825030340700d2100150001c1c200036046103407114406500c02800c1d1b505100400007034901070a000c1c14464040d040c4140603000a029036103c1d807000100941c0680e80b40c0c00c858010303140c00d03a603440280c5000e8075a403820401c00300b158098032840344151001840d482c0781448104044002d0085e4480032a04100c0324a001c10100c0081c038074120250103000800344d246450030250006841e0007201c640d41503458001740740c02585604044840500980001c00ea031604286800b688103001107040309085501c441000c2002e1201043c950b03140390041089612050b26800080d0302c0d41043d11004181c418 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 599369325 1250 599368075 599368103
    0x503032e03150b03070812130e0c07080c010b0d2904050d030b01050c1902090a0c0c06050c0c06040506071106061e12010501030602040e01090207030f051b1603031407 73
    0x1c1c2600541c3d003001d809400c0c0c035242070342d6220f210719000c05001312004814011500b0385090500425540040c48070540d15142420a00707200c0c0070783d12a50030080c0441000050b80d10031640d09400505030558044e02a103214030090805001c0c00300c1d003a40074002040c0000048001c115581c5588e40519004400341c0311b00d5111400540c010308030720b1500e030305002d230510030400c923030b4801d1010703041c0703802c20002c608040c10461041151101d0000c0410b034281c0d1a298801001d030394032105080c0b540358042c0d000202174448010a4089000f030240c1101b66105840c1003008010000c51214014a0384d9201c40500e02000c40344a503c44804842c010341003108112000da54800320088109070800150484400b000384e450000c0c00c0d10002d81081e1a629000501080386082c0103001c0c9004100507501182440f4050b900107006040d01c4441e1310410801250410005104050100b680141501103801e1031808141c1c101c081c01c803030f01c8150b001c91850044d9060905143d03040710301c1c107903003d080f0015140f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 599370575 1250 599369325 599369363
    0x7020a1a2a1b03070f0308250302060105130605030a0f050d030c0e10200a02010e040b010806120115120b0f1003081c1e0605060901050913090503032e03 67
    0x7402e011010740c0c50f01c903d003400984411056510009940104400d07580d924004101603214134060f40368140568603400243c012035030100d05941918000c80d614503030120800d08403009481e054002580c1405507a40040c10004a0304070030004601c1075059812140e11001d06030708603003603424420041008401a0022807400c20569842d699860502c141c6100002f18020007060001104503015404507030900207540c0c0100014080300703000c17541408030004d580b000a00c50080a403000d409a4841e00c4078900c511800e4000c0703215079240751081c011440d03944004800010345004103450407105d0901060240071481031a61284610364110b148107459944d03201c0b8181c0c80242d05c5074884600703903d03004140c0c103203000d1085406c03140308441481240e02e4800c081111210f078007540c03185908002141c07059800c0400e80b030811300111240708918002c00480fa000d010350b504014211300000003005442248151810324107a125106000b000303003002a10650f00c0424000901003e40d01c4081055103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 599371825 1250 599370575 599370613
    0x405060f070203010e150405071e0b0a020f013602010e01080405030403060507090302120714040c1106012601140604020307021e061f050607060207020a1a2a 69
    0x840c8083e00000d0181d000020f29414005c65070008041c03c10301c2d4040c0800c0c00341c100464005403140b00f4000750150440f55007408010a988202448070b6004115010f4640c001e102880036902a04001e11030389014031044c8648a6861814480106544800041d1602203074400425079030306071030b140d05c0b400b03036a001900d40d600014401c80d480c1c48104400b0000600c240101c0e070050110b03494119191342140f04102651080824041441d402500108490801c92074070400e4140c003034400080c2da00105230111124085c1c00401c08041c171030b110001400300c0061030140c20700d440108400040c0000307000c00c1d900340c858080d0705c6034031200c180010a91918081d8000c607044040f0740111482d0004112460742c1e0142c0d01d281d261142e4019004010284d01c007880d55a5071181c007072456a00f240c2c00c00e000038001e030152003806403071144d002c1070601c115200e0718500006030412004218a11204804601c181e60206441c03448484144408804150720000684001780800b00680601142d8003908104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 599373075 1250 599371825 599371837
    0x3130b0a110f0703020d0c09020a02100b0402090307150201060915090b0105121b04050916090503010e03031803040e040f02041422030306090905071e030c030303200c010b0306010b0405060f 83
    0x114907d850001310340d015480201103482d510f03006855807451002806088880801075240600d004215568441c1c1d8041411425141c1c010803041c1900c1040400700e005210a8012a40e80d030f140c50f000072081d01e6408080300483c0c255545c11720540900100451ba80d004005103400d9914802011400d20f590960082040d642c65401250900d43c4c0c41c400200c07450070507078a01c1401d40c0481d0803800c2c119480250007025080070740c024032680c68141c0d0904d0ba240710040c00400304000c1440320804c0303031000344100c0d401080300f5501101c080c10541010704000b002c4500c00ca100314905000d402112061241c03051040c4c0042c0b4507071008846419508864103103084049081607645c80c804680c10503144a007003c054003860003008254204800400c2c43e2000e8400c01e0302d020a10181040001c501107152801c3d83c0c0d1501d40443c3c20001c498038584044111403590461500c003090012041d071055010300b0035004100e0483c0c0c000e0b640c602d2030320150f2066002c0e0b00d4105c24108405c0100041440c0203140b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 599374325 1250 599373075 599373083
    0xe0d1115130c0b0d05010b040803090f030703020907081602060c0d0b010e030d0504080c0625030e03030f030a0c0801051c1707050a03120507050a03090503130b0a110f0703020d 77
    0x20050340c0c569410154500c5a00251000b0f400031501c0030009006100309405040043d0b00d0a1615080180701d42da01e0090324510b0307101d0044a59000301a0720f0912002c8004c0d507001e001c880081c00c04690180146030200e4a04522080340c00034001c90350b1002a8690182041c01050f030719110040d1211400307000301c594440d0501610425444454071300f0407400109440c00e5a94945943c1400c83c4c0d10b0520b20100102d52007003c05128200d00e000d82402801c5a54001184e0444400031500c2c0036a030589202e0f030b4107541400080740d40000c0610030070055114482400040100303003044001900e07203507000c2c051103800900800c8062680c14a02149107541c41c056100160b0141c28100301c030600d038ac80010211030b07640000d1081420150131a8600c18111403101d0140b2251a0408009200b0f02880541e00c00305902c645007001445003c0c022901c0ca00056043c02006a40755044902558018061100094443c1c641c031000c550000c180c0035810f08694000d40b0b1114a15020000622400300d0151 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 599375575 1250 599374325 599374351
    0xf15040e06010f0612060e0609100f0605091c0f021005092d030a080717120405280f12050c070e0105091e040201081906090e0d1115 58
    0x100210310400001d402042d1a0494048050901d0401000d03100304141151219050003000e0050ba908881465407000c030940340c1c05141c0e80c0d0310145504584540d0320a032480e1415080118404e98880c2c000c0c0f445a006440060049282201903583c0c0035003800040c080c0042111194010b02d000c0b050800000b081d86080f40c20100000700083e01031a01c0e40d0104c2540042c040130b20083c1d8412540030000c207000710050a0000c07241e03102d81030f4138415040001c1001207070131240c6200e40b40950944400642174141c0881900d000d2504981d540c090004426100b0041c0c0b202c8034804071411411000c80c1d44c4074080c9071038030090f9a5400700300c1c01620b038010240311051003915111541000102d00911400145006035450003040c0b04403c0000380252108104280070102c038134412101c1d0940040d07080c68a01e00310b07a40c9004180c15000c5880341c00300c0c100c1c200580000c2d15140f542103220650801000e58201120406041d5540c2c0245c00200720f0301e80040010300401200c890103240e00c40007000d01a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 599376825 1250 599375575 599375591
    0xa03120b031f060f0f03060e1911180c09040e07080d0906080c0f0f031e090706021905070512100501030b0a0c0903150b0a0f1202180f1504 61
    0x6402c1c480078038841500002c032000701a01a00c524001c0600508041295080080c203000d10114481d5141c0000741005071100d40f035401d851020000c010080d16440d2490988003210f10f8003141020b01c81681511404184d4580d00c100e40c0d141d0b2966001c1c3c004801101d00d03046004c000c0c0030140080311140c490b540180c80002851540610260500021640d111900a4140f0f100900640000b1b043c544030f054051001030421036620f400c94040d08009140c0076120340d85c4a8400303d1104003c0400040e01d411141448040100040c800007901c0b03064090303500e107488100d010f0022081c2d42d20041e0013540b003928100000c0c00c0417420b03058030040c88002e0b980c0322901401104203940b401e03401100d0221021080000c6052244103c6424102c10300c2c1542c00c141c070350744a0400030654200d040602d243d445800d00815512455090000c01c42c8081c4009540e80d00d07001000902d020355801e900920f0b1240c02c9280405403000e125200313451522070100c0c00c0e11034568048180c01000401500603940c0c0303100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 599378075 1250 599376825 599376829
    0x4090f090203060a1413030503010603021804060632120709080f03030402010905030f1b0d020418030306061103030c0d020d090b09070801060e060609010201060506040f1d090a03120b 80
    0x1089104c1d6210210115150b00c035140c0c102c1000000030710b80180b83d20131103a98000250b00078201c9044034440d00d000350322180301c00a8803523034011038440c20f5481442c001c00003400940104d20302031411103400031507a640581c0d40003079046400307000303c0380d45120042051052010030456040e0b000283c519005d1740c6503444281ea50324020400a40c09481d5101004000466a004200801815003580541400301031403119a0381c0b020040c034240075454020141180c1c81c1c440c4520601d115400600503c004d040010881841d42040c10041d40040d09101d00440d1040c00381d2420091403100800961071aa0303050301060384d0340c0083da04100040c0e000c005504034800a8081c0c01c2d01d01c0cac010075514042d4144080b40030b1412a10b03901c40b031507603414080c04020b02800010420362103901500e01540d10b441080040b401410540c0005502080214005c58121b00400c1c0120580702a610401040c4140701e0042d0647c80d000ca039a56035507032080a1000000380316903420340307048548103030110b0701c80c20030300c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 599379325 1250 599378075 599378083
    0x21b0601030c091b0f120b06120f130f080a0c020d060203060f03191b091b1b0f020409020a05040518120a02060606220b090f09010b04090f090203 64
    0x4420394220091840500014034640300d038099804c6540007507188203d10140142421540003015001c0c800c400ca0750b141001429000400380030001403815545880148044802c90700607964000a01800350001d0304811414075400030312a04440021040405503071491403130340c4449031240400c2049601400141ca900400410070b0b4402d400268403407800d17800b80009202e50030345451195201c6000b940003688104d42c1d0b4110260060040001440c41500c882404440b0340d0101145a01cdd03c981c008800c0b0340900c400d0403218190792256a050700d07852030400c2d41200003a0181040007a5140140185401d521154140d44040c00c80c0f10708543c2d460014044480480b8a41803014201860801d00755052008208100205c0001410a508520001d68601000700300500410000078030404c2c84402c0c080c4188290005c6103825500c5850b040c460030a5000321844502890551103900742030302c2c000b2a024143c40305a68613509191514011001030076400a134a0140d0340c0d20051000940c03000c3c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 599380575 1250 599379325 599379329
    0xe012d090203100302120706140c1f02040e070206070801090c0c061410061b0206070510230108031c111201080d260c09060903061602060a110706021b0601 68
    0x20903043c294a9401030040c89a03002e4001e8010781c01030760040c005180c205045041300d44000180c9a11420580e01d454036001c00c401403119524181e130059100c1e445180c0091003640ca00320928441d90321380c698140d0346d403501502c40002213030b103031001400002c40d158003030f809100d600c0c0351440342400e4030b031602401c03500703aaa8421070305468101000020222a4103000040045d0720785080540592903000f2922900c145009116000c0000c985082c8601002002c508902c2c5040400800c4041510a03110380c943d00701e4a00c6070302002000040b140d2003c01691507420f0388040c8244c05e0340c46010204010800c1c58103442e001e003410b00418800420403401c040c06807011700010030a0303c40d0403001400c03100706980e098800c00c03182c603500310303000d40340601103608030380b56000c038580b02c0d800d440010301c15000790b11881e0303050700c201000c00c00340302600c0100e40c20540c1d8540984031943c0701c0c0304c21b4509036042411940c102c140200100e02c0002d80c1a802401c801804038420300704164000c45040c2018400e0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 599381825 1250 599380575 599380591
    0xb0304030801031e02061e12100812120430210209010f050d090f08070210020105100e0c040305010c0503100e0709050607060e01020f130e012d090203 66
    0x200600400604e2000302d0450003460803c0107140c0e41c1c950001b07885125851900078400c000c4506050944000016a664012081500c490602e051080140348501500c2200c42520500c0e844d490180c4c6000c04031110a802904a0081650f0325102c90300040100c200341c000e40a160071403c028480c420410101074005542c82c491343d0380c0b4034404c81d06503080c1c0c1d0140c1c800681c8100040000350303801544942c41354156081c16030300c0b016841004030007007801c250041e01d0b103081034042c04104640d11000b848030301d00c2101c04584030040b810040342261002c5600107124400b42a0510024840004003680140768220f85460a074480d9036071400e540a884043d0301240c004400d0140307440310607506201506030018900b81c0c502d4010030040001040b440741c41d028600009010b41448560780100c0121504803000f555034060038a0700a565900c5a40d03020703080c8001803008100d2484a00c9081d04070748660440d2421201042607040e03a54285d090341c1003400b40740c0c0400280d404401d0024500ca40c0031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 599383075 1250 599381825 599381837
    0x1140f0a031b021510051e01030c2c210a0b0a050c1602040906060303050d060e0c091c050118150b0a0303030e0a0b0414010b06070b0a020901090b030403 67
    0x200324030107000d4940340c1402080064190b144400015800102c26060f041010465621501ca00900106003c0260400303900302500402041c4006407000c000e4031310083c2079a04000d04a4161000c68451701450600c07900624052030320b01500c02e421140750301c0584c000f8149010b1554551075181c0c0d500302c084050306550000801d01c01801000e81003c1d13070020003c84203000c1850500113882240c400c2c40003800c0c03c0e860307004080d015500c0701d90000010703990010302000116181d00340038040e070b0402024440d009007404800700c2c2140203141c0d414059100703109403034144405203041005425208022042d00c183d51140100416002d00980180900d02c058031007145144e81407001e1540c40c0c10802d440214200031010056840c2da050a4080300e81501c1c000032040860404281041d495444c050302911044051009105900d9081d034440c002c101c000b0880c20148005200d11809141c0000d0300c031a9040d0f00007941100b154005040c0301070145010320419483d464107254982051701c0650020b24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 599384325 1250 599383075 599383087
    0x103030201060503060c121815160903031d0d0b01290901021b0103021c0b0307050901030f030311070f030e010f142d190f0e0d060b01140f 61
    0x40c0a21908000d80020b802810803031800400090b5a445102107848071001d150000400f20f11100040100020b2541d0a9a803400e4103010410000c1800380ca00b514503ca4646440140c1400340c441d0074203e0b6890740359500310f00e0510490800d021a8190140d80002d0110210300002e61060101c6000c0c1c0344403100c1324201c00705441c00760380740c02621104050800003042400da05a80005210301060801001180007103642c0004a02a01404021152461001a00000c0c071304250b0448035071282d040e800c80b519181e6500800c0b404907000c0c0302c00740c04802a5845c0c200820300c42e4228000c03002c1c80300702c2c0394641921540d0340180042d80030720035000514910301c4000c0c2980c1c0028490441001c916280d5202180480c00f00d11130b2107542c17a5040e0002c184803000007a00106240200c1078801c2055040c0c80d14203a03411001c240f030003d021100041c0940010000d41405038481482c1c54801070020080f00040d599450b004000781070130203041c040c00104004003082283c00601c3d0300010303207602a440c1d03c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 599385575 1250 599384325 599384327
    0x20c0706020c0f0a0e0601020109150603050c091e0703181505161e0216080319020f070311010e040c1107090522020a030803070224040309171002040e010303 69
    0x8154900b00500c03602002031007a00d6566200321020a5034030001e4150045d40301e29005030b00401150b1030042822701d0001259111007200c1c1c1c056400c0b02d006400351114180007504026041c4000c40d0400703603d004070100400340743e6100c1245588010745040c00240fa07543e4260040d64150b001800f01d8008aa5a40c2d5401c008464000c3e560056040c01076014038812590003e07004ac009595203900315403000348c044841034402c00c10b8126004840079502807082d02e40c80499102e6200440d000c40030400492041c4119100003064214101020040c000c414290340d580781080c032015000d03604100d0300300b00f000d11582d03a40c80b07811001149510f0741c038026690030389054100314042c0c1c0400840c0e03240000700104203080b01d003d0b801900e1280c00c440160b003005c0c400180b480149401c080c000550200400659540010300c1d41034002c4680c0e8524004048182d226003428011680200062000b01040084400301d0403481c0b0060009001d03601b01140d80b2007284103d8025500407203011005030300401c141 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 599386825 1250 599385575 599385583
    0x5061203091302130b0301140427080703050409021b0f0d090b0c1203010b3604050a060b0706061703041a090d12030f05070e03150a0b04020c070602 65
    0x181250018605103955040055503118010604407001500003c0400b801c0c42d07002d00c4a400780400c606003544a58507400b08441ca0800000514091485e04025002420100030b82e000312030103085e10140007034116a14044140c0100b0300c210240b10003808041444101d90010301400206d203d502c0340c04460072040c1c0340ca000465082c040c46900b1441c22000060b0340183c0c0c0f1310030750b0380e40a8072903a03a800b60119030f032a001204003111248140800040b540d030308004000c102e2160600c5000d0b0348004941c141030f0440d40c0c0d4131406081c007110070001d10081d042640040e130340051110000640303155580c4034484681c0c424201141e20650f108003d01c0190683c4884c085c64a008400070341c240b43c01d20003060410f0840038005c2000030320103c2c00200710341d030321040d244a0781ea0094a070100b02164210260213041204501302c4824103040000d61071074450109120308074401801031404409120380c3e00340c09040907080304145612801f074002c41da250f0b40000c00c51510303d0070041884501d000c8009082c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 599388075 1250 599386825 599386849
    0x2030112031202040f0501140903010608070e160f08070315080a03031401050105071403070203030a0519020c0306060f030c0607030f0807020a02100f051b010b01090504050f0109050c0f07060506 85
    0xb405206010031300400c0d4426031000155402803c2c42500301d40300b8070100c18076004800080f171741513003007110105180c007020501204560954070005501d4941c0e10540500729608409135002a006042c8030300068401d054040d00901c1c0d508001511002028001d800c06546800520055100889100070598140b03c2d0000007442c0ca18220815418000020580e204180020380b5a40c07040c6d0b46c0120b00c603000d01c00c44070f00a034010222032399941200d801070156007246001d055001d01e0480c4903030009001145805030a980100901160303507485040003c0c0c0d40605401c5509849201c208801c1900d6410081c8050b500980310780702003030124900140786480003080390f4219013103402c0090040e10b070512010181c1d1200c1c1440c03c102c5480140c01c031144d000721001c0c0862087c940300820138a1b0b8042d8417040da0708000380d80c2c0605068540d03003440140c0d0001e039500501c00080c48010800204154401c50300b1030f000c2810940790401c2209002c209070404801a20310a40d03500c2032184034034010100e604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 599389325 1250 599388075 599388107
    0x1006140118060c020a0f080d0e1009210f06450611070c03060f0b0105030123090705030601031506021e0f0304031406070507020901180f0203011203 65
    0x1080049072418002450014824031081c0b1006005080842da55104c0b000050704000102c010316580d5080d8a6954426402c48400850042542c2c10030600340b841e0481c6d014110303600c6807041c0a203024400d4001001c600c04001ba4006068074040c0000c86d40c10114504a00a80703000c10700d00c090311a15140c203802c2c142d111074554911060701d00c0d1039030b0000c0c2c11a400c810180110001c0e0001c1d051920103007030901c0c13483c50064030000d000d10030004c07180c0f040d40a590203588104024800c200b500022036071001c1c0841d0100d5014001005100426008104032246105103141004103c50104250001c01d589950104034007100b0850306582c54803900400d0072440648000303140c40c0081c040c2d100d203144d1198008030244800d901904242c04c00144500c4409401181d5581e507403030508200d00d00e01d07001d04422030300814011410b403500c04c070141d0340d81c10b800601040e11a480c003603030350345408142602060010784a02545040f503444e0b03c0654000d050b014481c02090625103002040340d181d042c0410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 599390575 1250 599389325 599389337
    0x91406060904030c03050909190c02191e0f0c03170a05071407050a1203020f0c100c030e0613090b09100501030e070305030a0f0207061713021210061401 67
    0x1410359107540e05076070040c1d00350800c1e543c44400c50504880038810b12500d0b980180083c0c041c08044550280c150b00803441c041410068115080b004a0b11407188600952804051080391008036410f0301034409040c1c102400701060041555840c180d40814105c162040e844580e82001404510722454503c81005071505242907620f0b007004e80903001d040000751040c8085a4170403038488017000340d07202400c00149544e0312681e88194181e448011800c040380180105260030b00544d00000c0da01020b030400400c5028070204658003181c0c2010030303079025410003007481d4020a05844440c0102601840c0c020b06202c2107040a24610696440003100c602a03818002004000c010f41003130a41507070801d190109564103005c44c440d280440507080030f40707607000c00940000c0c0d0641003049030781c00203051b40075210b24594440d0148c4014074a2840003086200e10800150320000c800b501654451001342100640c00c4c1d0f03400c1329450060000210302c0c40c1c59440300b0a0101070381300d400f014003d03402403801d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 599391825 1250 599390575 599390581
    0x1a091b0913060905010f020a090501020106030206120c12010602030a141215060d0f020d060b0c0a060b120f011e06180e03070f0f030f0914010e040e030d091406 70
    0x1042003090000d05840c9070300d2030301564000300714950300850003554000009025100ba00d40001c4021741c846042040401c0e00000001441e50040c00380b41d0459800401541c20100005461500c5080051805c54100c20800150031024100344416011380260360065494040c520000b4100200e6801586103124040c859544511507140c034090307100400c1d076055082901311002044040c0074041d110f690607401d2a80b4040707944c5040d4043c1004000181050008075620154281c051250016072500d58200c0c0203084041441030f0401d8180100c042c000d8000c001782501c0c0542071198000230040f459440d490704c200a0003400366400241d0115107000c000c01441c142500c00c0c400028049009003079122031f01040008824400e403076280e50490b0f182020500640f41458000315940021004620610001c0499a102d4a1518180c40b15069041050307000003005480c0343c00c03103013089036100d0344540510705461070034009400d03405240303d00841c05486516100720341040681c10240c2c3da600c040e0030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 599393075 1250 599391825 599391829
    0x306070302032502070f090209040f020406080c07050c2808010204060c0615171501090908030103020103090507090c02010209030105150108010e0a020f0304150c020604200307031a091b 81
    0x595021020410a403c445004044140d06241490f4004420b100c0300c0e181c0050705501b641c00402c0410001c072000c01c039040340c0140500807030255001c1c0070f0002d546600040d144d48040001072000034090021100c000c01c80000244110a020400d0544029409540c4150402c008220409000315500075402c2604081c0010071441814a001e850790b81c5441515141d086010f10000c09040c102c01c0280c1e0a00312904101d540c4e20b008290000f50741c60340300c000a292200c0348503401c06d00303070720007040761459280d070300114050054520240d80d58021b104c00010300c0001c82c45080901441c0d60005a1140369590416007150001004050b441e198410321300480d0380e12860107410366220120030903203501d500841c00d00902400c510307840000000400d000522035144e04001c1c0c00d0000c42c80502990308600412602c50100703481c0208422141d1028900d280201032041d46450b60250803201003d41c0e9465060004c1c55a904000626402d0340034420641014058485c2a204912801c4000101000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 599394325 1250 599393075 599393101
    0xc01050a200a030b120102070507270506010224220f140a05120301030c0b070c0302010509030c0315160801150f030b030a031715090a0c030e0a050c030607030203 71
    0x402400400050b200102500a41c4454a0044041e02903060303201407501541c000c0d40481400d45580c0f05401000481c101c07aa4888070f292031008182c000c14000004c141c50142034050b01c00f5056001e03030013110303900890100b03081b0000c155103072050503107060800b12815200c00c45058059601c407244501d202090107007544401d51940a07944222004a2244050038070141d00401001030140005540108006034043c5050328000d0262001c2240d840040c0141c0e031188200081000c0000c41c4200301541c041d40c058049000f010301540d01d0109110300013800c0100410b84e09806a0142080c040c080b235040740520300250b440c0c00c1480c2e203541440901850070743c19007014000c02118521101d5038074441c0d08035000007000a0100c5001c03005038500900389080c5107907055581104440000d090001d40340c10080441c002500b00b4500d40c0320368003510042c080059042003810b41b600702101c07050404001402101e07000f0070103008804011810142048000351aa20401d4014800d11440540e041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 599395575 1250 599394325 599394371
    0x203011a0a06030c0c0f03170705030403090504020405010e0d020a17030705011803170c0904020a05030f06040605010f050d0908040807030b131106130f12140106060503180c090c0c01050a 82
    0x44042c806c1030916103011150452003040c81e500301d800c0c140c10b20180c2500310010358003851082c2c68200c0840d403218140301c2240207501c10700d4005540340d502d40300c0500f44400003c07001c500217000f0101135501c0382d044061403003003444900e031698400101c000a01c8030030320420740d500f0790390604e454030070026840003800421071000c0c1c60300c444420004500510f030f00c1c404032940740001030029919200101e0001d00710b03070401c5803011000c08180000500d02d04c1c06120382d6080d204140c40f2002008000b6001b100c194002d540084c800c03d68074074003c000309265070050700003003000c40001d115545c21464080c3d400c40700070f0100c030002c400c082c10000c00030b003020310b0801c2c0c0c5d0130040d11000e80b40e106030903c907490204030b0303440700d00c1c0f040c00d4210100b082d456120750240781d9805202001d0f00c0d0354121030b4031401c8480324130030800040d10500100e80e10b120912414001c001000045030488600000016000c800540e039448841c0f200007030000b100031003070003025031042070030f4410011912a1030031500541001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 599396825 1250 599395575 599395583
    0x303010509010b1c0c03060501020c0a0b0a0509060412080304230a0201050c19120f180603020a0c050d08071b153201081c0219020a030203011a0a06030c0c 68
    0x49103041c0e60b003840e4520703c50711071360941040c030600d1010100070b402410f46002ea1801401681c05010241c240784422000311381650118a1a1001c000001c55007a0401d5003900d0b8850380030400000c130910941c0a45500c140940c0c1242d507a418685000300300e007850b2160402591102d90b1089040c02400b0908841c800e40a00748a0313a1500ca0040c050b08054006405004140c000300040042c80000307514040c1088564550f1a403800c0310b01003c1d2415080e0060402c0600c404500a1140701e01c00e070082d0925124600301007080c11426994181040402d190000025100c0004c0049080c0d00003603000c0d400c03005441c1d0107101401a1110003032003001e1013040b1940782e116940182040a0760300f40748480c00e942d001c0308100300d0031004500034a84081c41482d80f035110300042011003810004003481c102c0304d95002080e0405580045c01180d441c05071059900c0b601039040003015840078081d1550500d001140102448000030410682d0901c0303030895800c1614000d4441051034011003411101c80e04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 599398075 1250 599396825 599396827
    0x90c04050601350c070807140312010801020c0c0a0602150c0c0706030506120c090f0717070819110a0e150403150b030a0b04020909011d100b030303010509010b 70
    0x5440040e0f699070100c103c04404001980303404140502496414040104411040961a142c14507000f095001c0c80304054140201003200c080041c280300303482010a0030f03c5c800d0b00d04209082d11a680c21071801d91007ea0680d40000e40d603503034004e0900004074054812952031082c00e013401b400079a01c000c0d2807074658210889100bc9035104600c070098842440e070302c06c215202c0a4480300014040c10050f0b840d10b00480f496456420164030105a0110701c00d0301030008011340d502c0c208010301031030000d000341082c003082c08440c41d81694440c070715603c6030f8502d031165a4a401c0c074900113500b04c042c41840140300e40c075182c002704903140083c00302c0c1d001011a14020070b203010802e00180b000c3c144142210009100024000100506c0754a6641900050241006001125414144c43d0348119030010708185056001400514006000d580c200e0b200c0350000a0703a5514444604100b500f2520180c01070b8814031011001015070300038104540000c2c0c000d58219490040417400341e030018000c071440110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 599399325 1250 599398075 599398081
    0x60f0112060b03070b0a023a0c1106030f062805040f020c03030906100b071205030c0c070602060109150b0d0b012102070204050609040f020f010e090c21090c0405 71
    0x140400500c0c0c040c00d010b982940d6203042c040130203541c40c0620911001e40c23800f518451180894010445403000c0d50760305200c85002102c5008172542d02007000304441041880030200c200e521004040c600c134000403513901085003808010040b009001c584441141c20200d0f50710764602d4190889003003203d4041c0d0740481c2d004040e401790701c003074080d0440d58680742c800132040006452000031201e0003a50513511082d14283c807203020503140c0c03062030b801400030000e401c01c1c3ca007910f2181c0000d50344198004800b03800c000e030f03c0a5207410403006a01020041c0e10110061000e6007040c416410000000e0b40c141901c1803900309000450f00900034001700c029038403100403015074004c00340c00706906c4113141c20007003206041010100035008108185d00403480d02c400140c46081015145004a40043d102d4013180540c0d400c101380040d0ba44001d40c100054a58100c110b52100e0079503030b005d0f130041100789480f0b00071224100341d503e000030107403c0f4070152142407104060020641d40d1900d0401c1c2d8000c60665 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 599400575 1250 599399325 599399329
    0x23100b030f030730050301120204020408010903080f090d020703020d02120601080706021006052d0402040909050c0d02010f180e010b0909070905060d050a0b061b060f0112060b 77
    0xc0580181c203000380000100e14003003181c044000710b000c00710030f4041032204502050320440c01c1103a0f281c40c1c011820401c01402054600d110502403035100400162402e0384941b031040c01e48242c09130072004945042d007402420640d2400340c581c09111140108401d090703210000307658403410311001e4017802e0040d00700815911000008003080b1050300c201c54441d40d50303503102681d46000e4414040180a080c0a5810b8042075009020440e20f005103841c20707890b4120750742e417520320044410406a15910002c3c00264070b581c0081e2006250f1024009048480d50820b24184080380d1002407161000c0075041c00180c1c1c000b080d0111008041c13900700801e0500342c20380381680756150080256a00546d00000c0d01501c0c0500420007100e0542e0302007200e485007101030b50894410702400d90301850900400e006080b00d5802070380d001f200c6950208640000002294440d40b00d40b00f0703110401089100500308040c20032405802031203022030302c40c0f01e600d0102000740001c210000101004d8903408107403616 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 599401825 1250 599400575 599400583
    0xa020105162906150d05072709140f01170a061a180105010f0e0d08030103030801050a060e030303040209040f02280b070f0b0426030423100b03 63
    0x1d01d42c0714514007400ca16009810b04040c20754100c0144441140000822a0911919421062504513420390502680ea40b114003e0f04000700003408201941c0c01c1c2104202003d01c10354040e80340c44a00002040c1844103a0301a07400340c040482491082106004072081c001105904640e940160100f100305041c0440d401c0280301d100c0506039a007843c1070100b19021488505c0300032441201d41c0300c0d03100709010010180d10003d04c030385808512000b441d040c3d40c9000707041c20030800b00002d0109480009a0381c540c4001d410030381040d0002014103006200301d0411500c900007520150a00c405059207801c006941da1000500081c0503194100c086002c0142c07d030002c0310510307401031032042e0a80c0c0c4a5840b8400001c0c0b655145280352a007440000c602801c0011140c15607080200f0401a272482d80b11318844400103481224590b411028140e0502941c80c013801e00900941802c660b68205403d040101c04d1000003441d1500c061006040d210060002e41715250004a000c04545440700c0d0000a083c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 599403075 1250 599401825 599401867
    0x15090b130b062223010207030b130506090106150908070506070c09180303050703060806040602070c05061303060c0305010e1f09140a0c140f0f1606051501110a020105 73
    0x5034004980c201118011401a00320540b20407080a065095421513002111080031401c02e0140e0426071051000c40d800d00e0300241d000303013a060722108000060341c0d96458000300700c039124100d9640d034074140650b2400c1d005200c80807110785048810300c0e0400411949441c40b61088a100d5640050320008000400d0041001064a02005c029003109942110596005100120002450440003c40440c001c0c0310b03c006a540303403c0105002e98a607584c180080d846800140e410019041c80010590f803403030010b109041102d1034020b50381d803451178139000340d03152400c060b823705040c14014000b0038180a5407607030090320340444640000c4000034108d034098498014a00160502030420311143c100441c2c0c60050b42020b0080180401c80c4d40e0840354030aa184500505030400c101e80718424070301c4000780c811209001203040c0b5000c48002c282c0c0340c0000340e03c07080700e160740c8940420140006903c850000c0c95002e08080320728211200d039850326800c50545c02030510401094904107441c8003820180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 599404325 1250 599403075 599403097
    0x31e0c050603090a0605181b04020c06070c05120306010e1c020406090204050906040e0c0607050c0a0323010615050d060509150a0803211e0a15090b130b06 68
    0x290340d040c035680301511074000d1304061340c005040c61302086007000d80c0095000b241000002602e03485810800d041c840c6004039610951098082c41012001202404035602407002c540311640c0c1c106071468540e007813200c4280d64410981c818010418144d03044120700034511011500c12210340c04d8440a0a20610350300e901079005807801d0008600ca080310b50041050300c404482a68150341e0ba18100030655210200995060f005884905043d0a003480074041682c400c03004d850088079003601240038419903500540704400130107202003440c1d88004000083c2421fa80088c000c1c0f900340b0144c4110f081078142d06008111000a0310505043d1943c806009860010200e11540c1040700342c00140600c903810b0b0078822900721000080d040e400000315001301d42441e2070034802200342c1a0341c4040c4000280003c01441054108844042144840a2041141e2403000610031203401e1691035601181c0c0014500910303014102403280e5030351001031500142008045580080000421480d02030020016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 599405575 1250 599404325 599404327
    0x60c0915030406420b0a0e1f0f091203230c16090c1d040b040209030d11010b06040e0115020109020d06140a050402102709090c050a031e0c0506 63
    0x14505072804800c50841404d0700c0310f185100110b101800705200514494650511820402075219a01404003c50faa000003801c0c1c1010340f04451703854100080030180100003c80c021004208150448e801d0000387c19881d02200714041c6a6a024100310314158072038001c500074201d21070007020182c08490302080c1c0c0c5e209070740d50b40ca42d045400300000c140d8000c007900c003030a15010a40e001c3c800e00134042504040d22080124641c00b00512006000001010f50010340802041410341c80400c49503107100603035501c5040c1c5450002c011801c4070320040300326224050401c0200010b440512041d030554003012080d0700c2140800a041c0d00404c01144000d40004250310160305000c2d80303912861101c2500d030701607405c99407006061070466200300c0c4d000f90322804810700080582d11a44400e5282848400118030b0f088644444a030b0100f9503a203c1d40c18541c0b9074110100304088046010000c00c8180d854030100350555aa220100044035080b50b0920a00a43c10090210f9405070000601e030241a02e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 599406825 1250 599405575 599405621
    0x1180503040314011e0c0203070b0f151005091c0c03030503070305090d090303080415062c15101701090e0c0a080303060103180b010f08060c0915030406 67
    0x19440e07030028031007620a540c070308802d0320711604107006018845214020754031401101d205000c0c02032041083c1102148000d0041c500003c41c07107000603004072070281c0305054500d8020340d214a41c0c0031000506014941c100240b9110765081429038266480803541601e4596503049824031540c0381e407202030810201d0700c41c00014950000011405204160f03424005a0750b03c14066503a400040701110001d20605c5003040840d01ca1020035422910495140c407039682143d000000b03131b500c40c0d00040c08501005900801e0404035920b0226050034104040201c1d00d00102e1802040c800d4001180c000e10000c1d010003010340c070464008400d0010326512044030f584030075215004044c9507446c0969440380080f80005e03494100d02220448103084000c41c510740c3e4403001140a8000c030001045600503080e04030b07000500f200382184c0038159801c82604040e140907800c0e841c084014000300071601040010b00d0312a2518007000d09800319030202c841c1e81ea03e452425000034091000400d2424031b01d6494 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 599408075 1250 599406825 599406833
    0x2040b0904030e031b0310020705031c0e010b0109050a05040216060e160b090a0311011407060516090f030209041109130506060a080304170a2001090f03020603180118 73
    0x46540030035000c031170801e200d0034071800c01c103030100e5101903140c1c1c8035220036000300501d80c0060024030701c540c041c2d0341040040a840f5045c020046816442e040d16404d8001e86110244a4000d51042c02d03e007a0385082e00e08400f04880c6801801486d01541e00082e00340d2540c2240d0503003800556100f4020400000d10881440d202e48026000c6001c03003540c6680080c2540e020310031313100c0201000740030a000ea4590b82d10064540300c02000d4505004101d42c5201044c03004102401c04540191008035691908030041c1c00c204800c800d00500b40a44070406006000311441d0703840c01e0307d0b41a40e40036841d0315075007000e9080c0317482c02000aa01ca11107408000d0b003d03410380340c0c3d905094403031412140c0766116801001042d0540d0302640105900a000800414100c10111580c0c00700303941c1900c2c1000c140740c80b5003141c0c500e044000100d00401d480c544495503407010140b0000d00440720000340c81400d5a000031110320000c0e051642403c41c00c3d0524201f80c034203600030425244d200d5941c002510035450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 599409325 1250 599408075 599408087
    0x8190e0a080c010f0905030a0f20031801020607090b0703140c010c030609020a1719020a0504080d032307110303070906080906070206040f06060e1302030d0f0207050d02040b090403 79
    0x20481d10b15400c0100081c070200c45402032110051b0f01070090b509244410700202c940e81da00010107010400c047e40d901c42e1001030181c1d41100011940007450780d413100c240c94490030101c40003943e411940a64201700da40c0ba44049440d06880c89008881c0d50340d4828102240c06044010b8803180040d000941180440b6055200b01c0c1144040c0d2020320181d961240804201d0141c481f20401081016040003280c0350601800c0c0d9024241e500700c5419092819905002c98003c8a48200407990024044c412000c0421443c580840c0501d000c1c000d1078442d01204201800c0d4628021a8a00e818042440c3c64021040308a1040b040c1003100d4481c034104100034203070145441a00d021807a5840860b860702c1004ca01640701ba0000e80061155850781e9480c0074415003102c40035106103565240103e84c401000188500440480700350315202001401010b0521030b80c0d041220900038100380b4000c0164001c40c202d0222007044a4000d090301c03407400428090300c035552803a940030301850104010960001d07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 599410575 1250 599409325 599409337
    0x30a06180c08070f080a0b220506180c04180209040e06061801140f0315010306060e0c13050909010b03060915010b04060210050a0b0d110111030a08190e0a08 69
    0x2590701607480d211280300342d8034001c0c103072031220005d9010320004d242c0f49100c4e000000758a0000e4041204042010b1710303200590582440c4a15258680d4180803681c0b0308400b00200c2c2e6001c0c0540a079490400e204852042d11407403180c40c0c10a000903040614607410365060340d4540b4005403003480520000740384207850700350848420780710388550003071054180b80d02d0710500e058030802c15402c442c00046d03038100b0056004480825074144078102c00400004252442c0030f000358802d080204041e800e05088841444000709208603800d014007810075000240541001151415500341c4e04d03039151024a139001d03189040c0020780501c501c0c0e041c4030400c0c000040e9001600f01620030b0b6840340c0d17211400011244120311504006a0100070800b200d5032040d032203581c0040450500041c041803480202d0b0030100e900d0b00c00c3c2ca000e082503401c41d8070303540c1000170720000c0c900001c095840c2007030800006d811004090604440700303504c400401d40c082c8040c0d01080f409001d01044469048903889c2c140e40c0340c0d00c50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 599411825 1250 599410575 599410577
    0xb060406170109031407080f03040c050d08180607150515040c0e1005121506070b09010221160c02131b030b04090b0a05100f080307020301140103080f030a06180c 71
    0xc030145c0840009400b520100b0f80c0c40192149050451031a91031039404c080c10650350b40b81034500005441e85d60300000409103100f501846e44601c0d440320311021490400321034901a1404111080004821400b06040907200d0b84c800981c5407680e400c1e81c807050f82d5414001d6001464040071a5040b40c200e01c01e600740c40c10840d030352074001c0041d0101f19414024900703100c0d0010003400c0403400c800704a4182862284020f0181c600307021289e250010040e5041c1c51041036030b580000c00c0380010410015002841d82c0003410241581480400403022503800d1a80c035041001514641c001c554601c4d060400020040c41d040c40300208101e4502d22a01d80c0c03440001c0880d20304415103032542001d01454140e00c0e0410305030b0038155205038030b40c006844001c105203021403200a01141c4c0c001c21a180b1409001002c2c0295211422481030500719160414084002c41000c0010800241542c003100e8200d075083e2000c944030348902103142c02819494200c0c5416000301e0b03814003030107901c5512070a4500c400f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 599413075 1250 599411825 599411837
    0x11060a2c0a0503070807170f03070c05030c04090b0a090203100203010906061205091c0e030105010b13050f03060402040902061605031c0b0312390106060f05070b06040617010903 78
    0x80c41c403c2643d15603603807140c801c00f40c001000410080e8600d52100d00200c4003042900c0c1c980c00d001401c0750a40d80300005c02c84406070701c079509100a0400700300c2da9881010569040204400940717449219543c010403865000d5148e449001c11518240107000c107210480f003003035489507161448200506040c1c06408006182860f00450341d50301c500459000d03201d281d0203090f1a0000b2001e1040c0700341c07461154400e008080c0d0743d2507005d4400f44945030082044455a6850784c581229280b01c04482d548140d118252100e9405402e0350701144660700700c3e504850019110f1074900c0859078900031802d24400a030494240d0000f80301340070000b40082c0100c1034900ca02d00c3c1c0702c44902022155100000f03605580404802c00c4c0781e40c0f4000051203035001ca0708500c07800718610742042c1d405801001043e0705054441e40c500d20294024040c140207000c2c03038100a408001d13080001007050103801c0b00a00341c5960340c00410383c141c40c4d95208501410391039440a4090b41100d040a020b00441341d0b04400243c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 599414325 1250 599413075 599413079
    0x905010b030a1208060f09091c031a09060d050d080402030607030911090402121213150203030708190501081e060105062208010c020a030f090311060a2c0a 68
    0x6404503088502c2540f15071890015001c1803411070300c62800406540c0c100301c1002684040c1e03a180f680303091050f0380c2d02000380030000c1e581c040c04a40c000c2c5801c4070018103003050420142d20b0345250007005c0c50103003a284204a0740e20400002d400405a020141c06405102001040c10750300107150751190340207600302d0380907445100701203003100c0303103900c000e811090001205160b0345011304850340c120340010141c0c0c03a035035a52280e039070a000100318904110940014000300c041c1d19032900c1c80040061696241c58070818040c0a52244001440700042010728400600811048402c0c0765541c8010a810420340da101c0040d0344da5505254004401d0310048000702c0300610000400e0342c142c5002804003800c0c100070400d94900e5070f0180305910400c8698140124000c0400d118400036010030f50300400c0300403014180544680702d0110204208402c001c014404101e40000340e050b03003042038902a40d51042000d0449020f864039801a9804081507010420303402c0b170403207650710302c03104a0752403070819 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 599415575 1250 599414325 599414329
    0x317010f0506040b090f06031006171006081b03101e051c030e040e07060809030405010c080c0c0a031b0819030503040314190306090e0a0212030403150905010b 70
    0x6018410aa4882c10401060042904c00c0000c0d014200d4050201100d09400e075000668a4008440b074545c040c0340c491082240310391140002c140418071482c1e0b03805c40e051000400f403012400b800b660050240c24404030345c10700c480705840d0a44100c03040500741c41742411000303680c002c2c1c0c031332145000c54400e00045110070110181d40c0022190014105903465580f500d4201a002401905400744a000d1b00c94901c1901d4074010b01e413800403a600901806030400001070480100506020b02c968810710081c0500d0f600907900c1d410f20364008801a031034142403144c9a207000b0f9600b0059801c00d0450000104000b0070340d0540018506034103241c080345403104160303942d505210381c504100300c1e43d1040c1800070034010303002160010301a01c1c00508241c1c5080b10351003d68003011121070004244091190015418807e400c050144144140400da80e12800d00707983e2120745001a11400b0040c0880030740724820021a401990701a81d403e5603a484110220000e0a410300b0a943c03550030003011511074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 599416825 1250 599415575 599415599
    0x10e091f0f06061b0b070309050102120601140421080f0a110c060c100f1415041413021012060b04150c030512070207050909010e070803190318020d031701 68
    0x2036450000810001686501c0e203406171a070103414075043c190f40307070b0f00031011503402e0008103050500301c01000e6090514400051503600c2e100c101040381c510a0005100038418045084c0308041886d2007008010410f04100a1900c146038106400e0b00001070031101140d003200070001030b03195010654180700c5004040c01154481c0c030031520101e400042c8510400c0b14181c0c442446d5082c10b1034001040000c0226840c00c0044c1a0b900820f4601410600c42c00c501c1c2a0144900744c08280e41c0c41030395400e041e0824005c4004040c0700030321499a854404020740d10810030507207030005c0341c0001d2160a9996003030006550150007803004005220310a0042d140c00f41c8445410154540e40d414138010750600c11825000c2d000e840101103024095001840382e46120340d19025041e402c2c00001c3e000c00d24513400d85030241a0380100c1c09034001b0710400c05207502002c02481d08811900303000c40c640e0307103260207050100310208000b0b40c415202c45d00364050540c0401d40030792040722029010410707600c0d08d40c0b070504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 599418075 1250 599416825 599416847
    0x30904020c1c0306180203190513172703010b0916080115081909050303280621030c1505040b0a0204030f030c05100e0303101d010e091f0f0606 63
    0x5d003041108580c000380c1c1407070f4029540400401c01458140d41580c001d0b5042d1803007522228a01c03165a01040c0520508401c94005040740080c140c1c40c0c90040721035a41d8007800c40e00400c441c08151030140b61140c0b800c0d0400740312501c009000705441d160178000c0e50a08408050160005600e010003c03500f03035840030f02c04034100f40907150600c859503803840040e42c40c02c59502c0291700580341c500c81800a5010000340d40078845154994510f52030552040d9111f040e082c444070320060400720100b0140081510a0f07406980c0b12907070304003c030b03d07904017540d1589090340014403134541070100143e16206a800a4025849880e01d81e640382c6808548800368000c0303010150100f400d20012000181c0100245034403144206c1c281d50f40e60042e0b50595007100d240c0551104035410000c10003403503500c2b0580d0303d80601420b803224455400c0318119000c0c001e205018140740040c4c1000801c032442010840002d03c021003100242d0b0000807225a000070300300e00400c0007825410802d0200d261400345100b1300f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 599419325 1250 599418075 599418089
    0x50607020f0c030618030f0c10110331020307080a020907020f060a09031e0c0303050108010218120102040b0a09050f0111060406050604110a020303040c0f0e18030904020c1c0306 78
    0x1c41d4980d902152034194034260030b12000c1c4401c001f074001c0103a4540181107010301607400750050415454496003521071901c03019004400c10420000941f55082c8003403d51140f0241d402c5400c0d0302070951910603880d040c0065414881d140740042c6403140010340c03a0441d4030903101d40703240f9111a103090307940d500c5a4170311300d0f1207800480000c0c9860b0000e40c02500344d10300900d00300410b900c2201c0c05d416148020200b040c0010442e201c0c0d1024103070103000f03490040c0155002185800c0544a0650000b498081d801e40f103401d00c1c0740e0410300c000094058501410300415940d40d11184941c024204510302e00c02c140c004c40201c40f07949803540c01341c035404186c4050140038244913500caa940710020301004105603802a070701c0c0880c81d00e0082050140031502544e400850f581e080505210401510710f074032a9400f01803070501402051440c2c860540c1007154a40d05c110a1159040e1450450044100e40c640040c030105003008500c4c1c00048045000c14090401c42c1908a807050441c2590601c0c05085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 599420575 1250 599419325 599419333
    0x41a0909070c1e0f02030120180f19080106060201020708030a021b0601180f0203041a0901110f0301060e0f010503011e0302041b0206220b04030507020d050607020f0c03 74
    0x401140c00b500d54120b007188584012502201d08020406181c20208819612008104c0402086007000d2090441d0f00a0001082e81840135190814400d44170f4190000001103003652910396540f02c854070600c011100400c202040030740400f90442d184154443d0029030f600781040084c07038038010b108130f1f160203410042503895940e07020a03d41c042d60141801d0903c00b90b5891140a0009040c00018080d00003140941d2110f1902070084091f91814070409031752031300c104240000a00e11401140d0358901000d043d0100303542d128241401040c0d603208559655100041c03454000222100941c107031074240c0c4840041c00303101d0003807001c210000180d49010403c01c00c010301600549180340000403158002420b92141c6990105040d200504400da50038842e03c0341c1d8803c41501400059031042991881808981c0142d6001d0404d41e440b41020340458008400f080c107061081c000c4070744140d00940300255500d418609a0740e0b58501b01d84403030040c041e0a1021425403000300d40301e161000010024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 599421825 1250 599420575 599420581
    0x7111c03150e0912031302041812110114010b070f03090e010f30110406170307060b180a020f25050c01170c031312022409061605040504060b041a0909 66
    0x1002c0280074007104802115000740001e0b00103542c4500c0c11305c42d0001541c400c0c0520bc1c0c0c8444a50a5403500054001b82136007203030041c81092034200a5860341d43d0003508865010705a0308095a8000b03c076009800203814400c000709401052000700c0c011106000200e51005040d07212051803080801a0705070001e480c1c00154022540109810606840080c00001c81c10340d25680b6503102d01150070b82c0800ca400124890f024410544200b140c180010f60b21311903041003c680400c0c00340b000038801c5020310390115001740d0b6901c1c5a02030307442043c14550300c8030100d03080ea03070702e040b070541d20810407a0399108800b001100e65204019101c0410402d148107885520750340100320030358000403c800348040d03c17140c0200125002c5482d103a055081a0045e041a40c0007401d005540e0b4000401c1148001214092012a000001361140e1145000400c0e1090310450802102c1700e100d660b010a52140c20302e00c020545002981c010011034419180f4495264603100c24000180550304150340d00c08024400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 599423075 1250 599421825 599421829
    0x20c0307020d02061c0b040b0303090603070305071e050c010b0f030a0f0f020a0e01031e0b04030e03070f090209040608070f060c060f0c1707111c03150e0912031302 72
    0x2410041d54801001d0341e0800d207151180f1100076080c0c14407400506d807102420301c114140343c4147d1640388000e4000d58a0002d030400032805902c00500b03101c00b0150703190001202c0b2441908413242c5000202003080704c0c0607040f0001082508800d0720080c19510b085400d52562515000388c0d204a00007501410303112000d40c664191405e8810029658240c5461103d80143d0303e10314038602403c6c0b80d04c54002c1c1541141098512000b50103001842c00c01c0513880000840e092030b01c2c0b00c1e80a640340c0f503c59098845003000c01e040c01da46500c0b00015860000d40887c070303a40140c0180409200aa50411243e956100000d503032307003005e1203150005901000b007404002c0c4114655092203005140c04614211110a107204898181c40401e0000d04101c4450312050030307030b803601030f04032180d0b1a0400070024000c0c04992030700001148900194201011440203d000b0340200a015840c44080617109664903070300200050100c07400c107114010f0301d00b4189000d0b1804250703805020f1341034848070318412540c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 599424325 1250 599423075 599423089
    0x20a121109090c010324030c0e0a110906030a0e0111031e040b1501090314010507030b06071a07020a05190201080c04030809040203060609040f060501080109421e09020c030702 77
    0xa030408020160080350201b000c076101000045210700b02c065503040c5820718607404210f024102d042218202030852640c02c0c142001d907034980104032516580c0e501c0b03484d00000100401a5182c00315401c0501b500d00e0307111120b014512854400004458805510f04018407580d8101d400815200484001c40c2d101202c45c004015242010305180248030317200d0710b807201404c10f41c0d40d0040fa0350b912503040008840d40f50042152010007503540d1410001641d4462000c1d0011030204d0501260716000218207510801c0040061a000400d84000034541c00c84221281c403400b8003640490401000b0410078010035044400300c80c0c11161182c01c0021110400001e980f004d855540e20042c103020755080b40d40c0d507214075910080c0400c0c0c005400d5107020000b5100301380507488500c51500d0440f0311015032041c00c11500700d01d440c0440c4916488188280c20f9020107401c8170603c85800c00c000701150a00341010584a0406401c1c82081815600c00d100f40c141c2c41940000c100f95001030000da001410116 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 599425575 1250 599424325 599424341
    0x50c070f08181f0315150c23011a060a0f03092f0907020c0102071404020f0c0615031b0f01020a1e11120703031b020a121109090c0103 59
    0x41940c0e6650b201a00000c0d00f8844608407211964219800d542c000d50301440b410403480d40108241901520748208451b216088a0701078060000710108101044181a4280024060030001c1111b5101d070351182070081904804400b41030300b07010b0220040340781034410303514204015a50a180750440030022000780c010142d0845245001c41c0d005004204200300802d1703504400ba00c884051070300e10081050511016182c807065410060815107a6617002c598601965103401144c1c80e000b00c8800841d00900c210814815482000f0611024071103000c111170340104462116889031208030780800d81c44244414a801e00640d2250300e1104504109031a4072a2070014015110074680a40b07803550310010040e000403091000d120600c040064008503103c15440540d0315010030080c1c1003c899070f8031a5408083d0030300280c082142640301e1b92001010542d80e02a01c0490440d0340c03a41c0c0e201c181a00064212900311304103522003801d040c030000b160310071900c403801031005030803400040d07009150741 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 599426825 1250 599425575 599425597
    0x5040804180e0d030504060c18140f03030a0201050601120b0315070c020a080c0a1a030c0306060c16090f181104091e02120d09090c050c0d030609050c070f08 69
    0x1158490388200083c40584034443c503684001c50356103841d05d0280d00303d40fa05401c810a022140c0e0000c84201401c00261050311040080c145811a580c0300144a00810441e255418880000c555401c10f90640150740200c9007038036001c800e8100d0035001429901030000c810303055489080c0f010030b0030345200c110982003219414103400465140d0040b03940b41c400345d004108994000c081300540d1782804101c0d5070050911002c46032000700c140c0c00c0b00e1030901c4003500503440703a00c0c044082407503981c6643c00c455003210900704440240414a00e200c4d1000400d00c10202043c0ca002154a541442801400c1ca03028025440c030744d082c22195944480703525404c1565801954581640c40090380c510300e181030130000d104103441455202e02c100b0560803440f05404456400c5000f0030240550807950002c1642d94043c0040b8050717409150840c2c07680544011a002841164032803040700390103a206d031068400ea07030009d00c496904d11402d00310030300c180c1c00000c00c512242014000498100030192503c07a1038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 599428075 1250 599426825 599426831
    0xf090c09150423070e03070509060105160c0e010b0a3009080c010c02030702150306040207150203061005180904060b04050115081003020d141203010b1201090504080418 74
    0x1052010400320b420707510700554849000d0f03040301011500940a2503000c00c00d4503002407800150030101e41c440b807903441603a010341e4001002c200540c1c014001d445000303110f040c0700000c805032411b040e6111070043c400e010f040035150b000481d18458003012104101020b40b0317154405415030a4600306181201003012a942014071102c0c240c1060303001d95503505004442158560b00e50780402c47c05c440600e042d0000350740c800c02a102c010303191100300360124500c0c00b2070151696114070229010303101e140c1d001001044104201450107950342d000c0c0d80180d030b065605038518001084241d680b845200e60740e0340880a40380c1c0d8031400340342816409030b002d40714800204416040c1d6010400ba2402030b00b0140b0406e0040c862210120742c00000f45e5441400c01c28881c48080c40c2d40c001c1000211404009445014a03128440c082c000400c42e0314500408814140d669603074038200c8007000e400c24020004100c481d10000200b4000780e0244500854001d01000d1910707203001009200a41906001d045880e2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 599429325 1250 599428075 599428111
    0x1b0613031808100e19170706090f0f110a0e0a0b030c0310020a1106070804080f070f140d05040f061107090609020304020406050d0b0403050d11070c0e0f090c09 70
    0x30b082c40008490b944280c0040f07405407009090509001207203a07000c4100d0801000b18010940d0018a600b8141c11512500e40da01c0450504030054025000e0103852910303100c00c1d880420020030843d012160089110710302c01c144040410800840911810079a0140940820014006039000300c1c080740c40207040340c0c4156100307004282040409809000c0c0c0e10340c046100c40c806a004061100c0300301e02200540a18030b002d580142038004068000b6000440100c1c0d80700800c0552001c541071a6085030f841e8824000b14607207004031000c1d20740c91072a14014640c0301d070a0b960240c4151016100d032011311051103410880c00300c85800280c0d0b03800c0070710304c204500098a00c8aa01ca80360190104007009a6280303490b00500050b02d08a9000c0c03030040192004600c08a04500100d40e002a03140c03604503030710b0400501c1c03030000d04010094840980030002d18141044803a98424040701c84410990205541d41052075032364120444110213540c02070316030040d0628004415540c400c401c0840f081c42c1c50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 599430575 1250 599429325 599429339
    0xf01140706050c12060d080a0c02010e090a0507020f0703031e0504150c0204060e190e0f0f100c081314070e162322050402030c1b06130318 61
    0x40c0096400343c58803440001e6005101c8010b24899901010507921071840d2043d9641e43c00c414464a00c0c03540c10000104d2000b411603104e40c031080c0c4007103801458810182804508040200303000e440301e40261040c1c07200440302120100e0384904403030301511041c0088191024480325011800c6009081000170000440d0195040c0e0640310003a07225541e40340700030f40c0ca1060100316002d9030040e8a5009842e4104111960340d003941c5411200d0440c004907080040c4030a03e4a04621f03215401c64500034417203006010f002c0020f140d400d04035003800500011011010985911505803440030301d640990f020900401c40050103090a00b42103821100011b0755402000300c01c40c4180c030034001c00601589249031003a80000d55080c010140401d0000181350b0f008807030b8662045c01580352202540440030f19004083c1c60440004041c068015942c03486c000050042541c410a003822040c42480f0060242050000d4024807510704c0c01450942c2d441d1741d803000e541d21441d0365490901c3c80c10804021506d031f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 599431825 1250 599430575 599430581
    0x330501030f02072f030109150209040608120711040c0804020603070203072112060b0301061116060513061d0f27160c020a06052208160e04020f01140706 67
    0x803031030030a6070200b050035880724134131148503611810710aa04244200011890308110312110040031100141c2d6560791340080703000b511583d403041141340604d480c2c8804000ca9003008150f29441050398100b140080d20402080360141c101c1400010b0114002a006080540003560007890600489090610907a66980041c00880c048052006203c03208100c0c40e42114248901d0f11668106000c030604294200d07440303001c14850081003082c040311a046007602841080c480c44820030807a8216a00c501000c1d1035076200444148000500a000003045445441c00e1004142d0b4400c0c06d40f0b10503480b104104561a4805007280e01110139503840c910300901e003001d072000c1d03104102d0506852414884800600d604503c4400c1400445001800182e44560302c0005440b841c0c203060351580810300c00760009504050bc0c0c07400041034120080b501d010300080100c0340380491031800700d416071941a5041c400d4000d84009401206c40190b00c1290741c0243c24030120882020081030402d4480d40b200016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 599433075 1250 599431825 599431853
    0xc06090c170109050c06032e05010f0f0c080f0c0d08060108010906031703100503070303021f0603151109030a03030b030c060c030f0f04090e01330501030f0207 70
    0xc40c8040c9820480408441c64003491000100000c001280a036103039035455006100c403c07840380740008005000b000001624491400000d41c0c4405000144405402007000364007a0324040341c7d12100c000740701c91260030b07001041c0d00c10780d4a0f10410030740da641311031954000b142e00801010080c45010480352081018000c07030b11440c0d4800d4114100764001401145040e0085a080c6060a00034004124225420013410b6551089241d036550307010350802001c02c2326040142c0c9801159400010b240d4001511551240c41030a03642c590840c060016046414a220084c900810103903d5a4906265480b01070004d5224039000c0c40e01003034400203401c1c821001c804801007030356404110f04600b0100b200c03000d204801e4820030f24005000115540c0d80c080c0b20200190302d5400103210b184d5114801c152802486000000d10890400450460107400400460342084aa480e42e500c80c031085c0c03000181110500d074508221203420000110b02500c0f294694182e42d40d020006c1c00c002885407004005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 599434325 1250 599433075 599433083
    0x616080403050d24090e1b03010905070b03011a090d08130305030a0c0b0a02040806220b18010e0a260417010c0207060203360d11012601050906010c0609 67
    0x6404c40ca0b010030398020760300c640040d03141030320b81880742084210001d501c01e41980351240d0b1015603410600082d000d0041054010114041e850700018803480c01000745059546c10300305580e2400b242552648180112113400d076000740c02c09050301c0030440301401401e100007100e0300c204003c0e8403612410f02d50b40c0050911000581e5842031281440b05800d44c0c0d80c0c10081c2d07220194901883c3c0031aa607038800001d404400791341d40300c401c0c10128121842c0078103101d80e13200c1c040d0005850040c1003104c903034072031203400e046030350a000b01a0741c11580405d440c03070b0700c6a00c81e00356400408502480e03200c1c01c6007140170401d0500c1c01c0001085520150b4a2840d0341c000d402d00100340c09007402030090402e0502d5200c80c003558010300801c030741c03d020008101200400e1000364040004600c0710b07202d15211011100f90030800c180c0b95002406010300ba850319145c07007030300c074090103414070511051034581c44c4000e15907003507002d80103002900d051600c1c60b401c0721052500940084058540c40c0440b00d0310380c0211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 599435575 1250 599434325 599434361
    0x506150a0605210c0c0709020403082b1406090601020c01091710020f04030219231305090105100824090708030f0c1005150904140f0601170616080403050d 68
    0x410102006c006600c0a406406801d46c1054071315500d10b000c501429421103e00c0001c449040b481d103400e103074101100c440b004018082000a48205080d824040e41c0d404d000f1106040054119400000c001c00182c2c2e069540d24501443e2400c49a454034881c681411036015543d00c189030f0181d81e001428600c02c5078035030241e4807031a51041090031501084800d2000303e070b4510801c0989078900b1000403081c003c0d4a000201d41fa03003800a0200710701d00c50f140b06070f54600400e100320360005500980c446c009080801c08030a48400303115035030307450a14156100300d01e5a951b19051041040040da00030074820304640e0f0013500ca0b090f01d415600001c1400c0701129010035807401d802d400300061300b565481d2035410852801c060400c0380c1c485e410555054012000348011408110b034030180145542e0303031002521031501c4414116074641d01d080c80b440d12140d0039211840100000072403401c2c015600f480b41000c10748581c14080c0c401210092058061103420b001c181c80e00e4a15005400d41c00c1d080401f14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 599436825 1250 599435575 599435587
    0x60304171b072c150307030c0e09010b15070f02030f0609033103020f130f0b01090902030705091009050d12180b0306010c02060403020d050a0506150a0605210c 70
    0x614818554020110741070f0aa0751445100c54140555811100d542140c0803078910040200340340c0700007a48018001c210810002a440000400542c0540f0a1b1f800904c035640d210000c02440c40d11031030700c0c440245410001c0000041c5c000400f515000d00c0030b0292164a400740d90250f003032003003c6580c000180c10024052a0700802400c0003e1a10b040c00d00350482c240880d4080201000305000c024003070040d4505002441c1c2d200400000c100d4a1342000348095402c1c680301d14081d1120246075404200050404643d40c2003c0c02a00d1165113141e681a09120184003004905014000c0d0503080c09031800e0081125100c25000b010701d41e00a01030702c448500c070030303400400510752804d10100380c03443c0da80188840d00c940003c42c0e801100c01d190044100c4424000100306220344da000035400455010940100017001c1a407154641c0a4801e42e9420b41e5032803100b181c032048030766442e03501c44440d5400703020b4203000c2c4c000303804c04403214a00301044650301c441c0560000c400341e428072a00c0c40042a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 599438075 1250 599436825 599436839
    0x22d0a03110d090f06050c010b030a2904150c0507050f010203010e0f0f0411012607091d06090a140406090b01060c0803060409020102030f0313110f060304171b07 71
    0x1298045410514005050614202c19801e0a101300d0042500f0068001480f06114009401500440c980281911600c84142c030b4059103101d0070404140300020904912604c04d05980300c4d00e0700c030701c1d081018800342c540203184040041114444110a2000510011000c124100000106c9121581c00107030b4070b50400c0c0d0160507486c0018038001ca44e0780c415040200c0c60045a04080c0c1203039100450b06810a50f010040c1c520020380101d4241d024005001c0f6801900e109100c20b004a00316129085601d4860039403480c1d0703000c0040708108011109003c603105041003000e440e030043c036800300015080c416030080c1c0b1114034282c134103035000c94407864104103018207107070240e00414490600880c131107403c1c2e480710640c0c000206886c0c45a40c0c0d49c00c130401035900030300890300028905449140d0300e241c01800c44204003005801031300c003004616480b0b00a4209403001d44000f040040071035007540d80b40d036280718400440304d0448000c142d06000c01081c00200242410310b590250740a402941d0516003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 599439325 1250 599438075 599438083
    0xe0a050a0f1b0b12090c0613170705031f09080f070201120b0307060810030206040e0901150b0d0c141305040f0902100c0f0b150f03010507022d0a0311 66
    0x1068aa40300c442d0104100c095a8040b42c110115201d441000d80c0d8075000c0c403d0501d00c80f8000036803c07650001e0403102c0c54802207a14400d03100c29803284444100c00381c1000365903400b10300550b034055010814003804d8003070042103428901d0f10703d5400305141c04aa0784044d03068000c41076800300c0c000003042010456802080741d040090754443c08211905d40c0b100003da4412a40c8a0130040c031030300c00081254000c10030b000001940d00540800e036540ea64031042490440100c401520a519008005c0381d60549000c00d20300b1183c0305441c103401c00345800c40810003803564440c1c41c07003882071040540d032142c88900040c104029000c940500c100749000c0910040d103200303118820140e1b02d400d031000e005a0754000c01d1062040c5600d000c41d100700d045e207401d58240300281805050002008100840d151400004640c0d00328140c41200540c0454070915013a41d60039120000560002420390b0310104861110307180c058100400180501c0040ba50203040ca0700f204401d90004150900542d4600d900700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 599440575 1250 599439325 599439353
    0x4110925030204030308060405060616050f1e071707030303020a030209150c010612120309081b07050111030a090902030a02090a0e071b030e0402031305010e0c1219060e0a050a0f 78
    0xc4d23818031551a2020010f4002c2c443d18600b24000c0d40500d88aa052280400c80d10360b110700a074003214031284441281100309140d28007070b02140d104101001c00c810301050000001c0c00c24001c01065400d0840d070701500650020a080390805600348070005560791170725144603207045c001000a82c0d41c12000c00960940703285401c200c204031070102126000408280741c0d15130b03e40c0280b4000403065a54540421184902148004911500144410000d5010410204840c0240c03602d623004900c07072030307120f459000300030200020a01e80d0004002c40595a001554060480c4100600c2d2030081000902c50b5022500301440152442e405c025070ba541040d041d0b0070b40c505041110300003442d40d9900503d00b00e0900c0c5003600a40c1c0100c003281200b2003440c41108080d034090024415030044031046a078440740a10014404c0310307003041035a070954000c20300364899803200d1b080101c8485107440c0c0d0400f800d160040611a0700c40c0c0c11a51001c038009008a540c864440c40b6043f24500290510729030281d001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 599441825 1250 599440575 599440579
    0x307030e0f1b0f0d0803090313120201080a15050303042301090b0f1e0c03120a0513030c0213060e1e011d090c03010c020102130e0411092503020403030806 68
    0x10880006a0320441402550b802400301c1c0c200480004800100e8a20424840d000300428804030500102c1940400030301401512540c8042c035859450060014001c441c0d000030f80402c5914022990484085d0010819070301c001c50700c00b1403e552140424556030080e0300400d03412000c00d031007270483c141440c0c08d401c20550034609000e00c1418405803505031311401c0030012004100086500d40382c0024981e420138180002c2e034254071015483c2d8015100d5200004c50200712151000045513511140702d00c9000d03501e8105001c840400130340d429942110001e1042c0d9101504407440412001075000300c0f0041c03c40a81e400c42c45080c480c0081345003000a0180c030110360803200050040d410041c0b034003541c0021a0366019500d89035440351508000d000805960076500b4850108a0745805400030304101c0b08040c2d9407605541c0e148a298420a420340340140802032202d28101c9625100003119042901c0366080500c000c030655000500786000e21508000c40c1d00490304005158100035603940c08641 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 599443075 1250 599441825 599441833
    0xb04050606030f180a050a0c09050711070909051903020a020a061706041e0c0305100e190203071205010f031a07020607050a0201020d06091d0a050c0918030307030e0f 73
    0x1255015016243d4000e140c0b21800c3c0e206910244900c0301040000034494009040e290744400905004511501e10301494024506090118082c940f11707624841014808401600d01c040c188807a0b0710190800c840165030910601040e8480340c1444800c020400340300750001c2040100e10f10501c1050b5441c0d0b8888020b2061074101c03101c00c07090a40109038001e07401c88001032812007102c8000ca003005c480c0143c400e00b52804044200e44c0d90980d01090290000c00f00d004a032954074031000c1034a00e0110781c0203071003140c1c03140e600001c09500d8000d560042c8840c20504001081c88039507a0440381d00760301c00c480311004a4401c10500915990700c1c61100c1008418030700d40d140c0158080d64a09000d0f0070041045070008a40d500c03d0300c02e505503071000c42c41400902c2125034850b00c0c5005004940703124511181c41c042450b2141600050384003803e1350140c003810384098000104180a0001008026510114604075556200a0004620608442d200011032805151b03625290014580a082003540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 599444325 1250 599443075 599443081
    0xb01140c07050d02120d031401081f0b0109150305071b0f0b09160f09151d090102040e07050310050f0a0e04050c0306070c150606052a0f010b0405060603 67
    0x90201e074000542e038090f111510610b6243c80070415021041035520054050301c8a0901c6156054120450310480c601e5600d80d181d0300c2c3c1900c182c44d017803069986141082d003031050b000c41c00426003100e0202c6c0014100350854640e255911030021400c1025000000d0b5244104100c40e504801010041c20706d034503c10300240c00039650101444081940a00180302c040001850050200800e5480c0101a980ca254140d0b075041c40021800c414003c4100060500d0310102c8441c0d00201d03140704450b91841c07007082c40445483c040104080c058088001e65408000104205480d103e05d0f6026503065942c10f55613140164400841e040b05070086441600180e180000c0340d500c00742a6002e81d0180504502240c0301d511f041031900140c02130083c2c250041804002c0c0b41c54214405183c2680161803d082d0381e2100301c45131040340c010707000b00c0c40401c90071b1140c41d02c0300f9545400c0c4407885241000c98841161036210b070524120070b211400440340c2d154882010141014029540c00200030380355981142 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 599445575 1250 599444325 599444347
    0x10060b1303140a050d110c04020f03010b070c030206070309051e090105130e07080c01080a0b0603130f021305060406060903021e280e0105010e0d030305130b0a0b0114 73
    0x108030303100141921003508001e1455030820300c030340300704035510400b03e070346015884802800800803031050b007113a0b001d1010214001d0503c2d008036001e54040c00095451603007071201c000c603541c00c500400e5404400e844408401610380b02d0080c15481d020b51190300001d49800104024410b200e040300181b196007007004162074507080c603502e064403002ca4201c00306804405150b001000da61400451a200c1e0000008000e003002c40c52214901007a41e41007465075644800b4404c0e1402c4240c202d40000c0100000364080903050504211148207045445918074640c0010320105401c010710341c40d0715501c03424020b042c501445018010080e506001000b14030390b8000500d20481980500e100954200c11850300341d9071240311600c201036080701480480800201e041a84080d0301030010140c40003c00810349600903080ca6440c150000c00110312480c0e170741d90881c0a4140540f240b441d410740c884080703001950708030b4910711401c020080011041c48c040001000c48400008665002d00c080001051132 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 599446825 1250 599445575 599445607
    0x100501090207030e040c03090503040b0a020f1c0e120133060c0b0c1b030304020a050103061413270218070903081c0f24050d17091210060b 61
    0x84c04040740c0024044907a100190050020440000c1950100040115800440310081d02a240e0b450303003103461034180790450755619510f04d840d545014026015561082c3d21440d08801344900c0070301003400b44003550552900751500142c0307080c9100001c0d000c241000450000030350700168000d081030703442442c0040142c0783d0f520b840c4010f0444d4064000142c070b0600c41904a40c00c41a40f42400b00d080710305080c0300ca80740d800c2a60100d00c900c4022400103200e610a00804007a41c414400300340640020b5420080140542003403100d4180d03c3e554003c003000613086040440c40c58104480c1c011202c180304000a46070b41d1044500b045044906100c149170b800141c0c0d40981e580481007d980342d599401401440c04640d640001e09405c203007a0f41d000c05415040421215440d8951011300d4a1044d443e03980000680103254010040d81074440c0402c49842000703c4041c0711461b003c0c50044c41c0e40202e0502801c0810400c440c1d4060541c41c0200a518403502c4002c2003005019814407407910001288 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 599448075 1250 599446825 599446847
    0x9181506031e180f030703170c0a0c060b04230c04080d0c060605090411040c020c0603150103060503101b03020703021209040b040504061b020f060105100c08040810050109020703 78
    0x80c069100d0300042d48800f81c50504079109040008840c110100f500c100c41c0e40c0d03072090300106c000810045c5540020603469910328056150b219200d414004894412600248411000c7c0c5455032a2402200b464903540b02c1e000b0700b01041040c3d020020164400c03101c070040c02800040001004201c01c100c0850003080a1401c000a40f600911280c41c500f42000503007440d0700500c0d03215003040d05110800c5003922044003c1c18050300c061203a41ca5844099841e101e190020300e030007d0042001404145070040350240e48130050400160003622100402e01d40016541b2038081140e403160301c0d0581086495000b200c041031480d065150801c42e503802500c480003000385070703584200840c3e071040d0740e81e81d07411483d00b07103e0241c402c000f0b5261030305019014003140744607903500641c61202c503a0024404214241c85807442c000802943c0d1a007400c0c88001210003058404000e4480c030300d080054101c60080000b404114020410780c50101503800803698182d1000314007610411a6a0000b40c00c0503111074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 599449325 1250 599448075 599448121
    0x301081e0715020f031207031107050c011214010305060601031407020a06020307090909030f090f030b0f04031704030c030e010806091609050a0909060b180c0903030918150603 77
    0xc40c02010b0070041e407501150713404659090001190a182c00724410765028491821907909025004001c030b0004203900c00d014001d07040790401d030989903241d4000c0261903c80c02642d0030016030801d045100060080d030a0300229401d400040c20f2000c00e40c0e141c080c04011440d0045040701d03030b00f800340001e9aa20071905005020940200000300058000c5420400030050080c0500001086240007092036001010003030100725680780c04110550110151000e4a5100c0c032140313425106c0308000610400d000304220200700482c002c014054180d2041640928466150000300c8480c5203070181c502040781c2036650400c030b404d031704000c115074480f0b100ca40c01220080c1c0c51091041d120384201d801090076049641c110142c014001410846a84503107441c5014400030001407000900300300c07203a2411109036440000d9480032824030344885000f0119500020300f00ca01d00014040455041c100003925000c00b40c2c28202007000d1b600700e920034152403100845a00b4614542a41140d81118012000390 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 599450575 1250 599449325 599449349
    0xe01060e0102030d0c0503041b05010e0f030118030810050105030f070807090812070b130203070b0d0605180f09010e030316050c060a02030709060f0e011b060e030301081e07 76
    0x201582d000f401110051032082009100d10114404064044d43c0292000c8503501c1c0d400c2001c0c84014a51500324040e200142c1d626805206010100b01c0317126035502d94140d055583c1c40c00e4100b0150704048502c4814469198800d041c9094511001018400d500060501c4001c00c200410408080507255111f00c80c0c3c100324a81d504c0d144422036802045403c00c1046208801d0012504440e0300082c000c40b174031802c1110296078801110030b40701185600003c0d099070280c9418400304810002030103444401c1d20b00040c0131981c810020f515540c00780b03000d0301c00c29184011b1121840b68900c1c103641c00300300040240a010344111206030340c0c3c4002000504040306607c80001c002c0d1140c0c003100d403220fa110b0119122410189503031802503100381d4515020800448000580502440c40002d84035034544980c01454013120042d11702c03a501c03820074aa01c00740441548002506442400d1404c2c03003590081d0380340c0d03050440d0703d4500340358910302e140f41d240b0140000703182501c0021004103031000303c080c0ea = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 599451825 1250 599450575 599450597
    0x503010b0d0f0906140a0c020c03060a110d091518020f09060109030f0c06021516031d03070317060d0b0109090303020903030d14060a320312040306150e0106 69
    0x400003003c103038034014000360810003010300e4814102040c0e80150160758003009580b08004090365104106400c1f190550004000211010815441604102c0009891914180301d07890b030801101c5809800301d60801c01e41500307400a500031b218120382c00090f41004407840d001034000400c002000d07901544240c5500740090101c4c1d101d04000303001164440c060041d400c1c001d16141d0a102600c2c01010014030604500388144c3c10780031a8103001700c41542c40708079a50400e4a048002e44a1300354502c035090305841250b05c500900304020081030703009581e0394001303600c5140c0100690b400603043c0ba12038a40901c1c1400441c84243d1000d04440c03207c1e5001800322418a0180d0203070240c807483c40d51600011074200c2402640d90800c0d40340c600414402c8509985640c101b00a111441c0103213104070b00c41144c0f840822040e0400925600000c0d000e0a21007042c420003c1d00d071208800600800d014081410801c00845024900e10319551980d2442c070309003852000341e21083c0502ca000200b0180006c0c0f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 599453075 1250 599451825 599451851
    0x91809020604080111030a0b04091703060409080f0c151005012627030a0c11120d02210f16031e0e030f150c09010504092a0503010b0d 59
    0x40701e0083c04140001d00c445109030604601c10f40084800c8010b440c21f14000c91858a014440c0b0080c0a07031110241130800d80c504d03114440c6800c0200882e402035a030700700c80700100da6007a014080c0b000c6102c81c2c071f658940b02542441d04221441074004050040b02d03090103c031114103882c44066032428a08a40105034040c1d8941d0000320310718030103290304080014171104d0b00700344514007280194400e0700a8101945440140d99101c2c4420800c000740b03c1c100c6d00700024003c58585810b41c2c0d001440045032030760045c091810044800031200260784200440b544000e14203c030010b044050070321701070078000c114050320034a204010030209900d030241742100815019056000c0301e40354415520203142946000a400c0e0030055a00310b00c240300b008502e192015002810425000c5400101c12203038960741018916a0044251581401030600010440da1814400c421890842080d80401781031111915400d2b01140d094080802c0800c20041c0007031009503040714500f030440c000006040c1d5101c40b03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 599454325 1250 599453075 599453077
    0x3080a111c03060602060106081e040f0b1f050621220c0905130c030209270a120807020634030603140313181b1e0918090206 55
    0x1904012001c100320006808961650050701550090340803141d071a600d5540c166070f80c034011600b80c810050203000305404001000e410940042c4582e4081003694496072780d80105100480b4505012900c24008001e00a8204900700040c04182c0d0040e14083c40412209812620104c200c03640c4138140000c9207403c005c01614494640c6c0c84540d0070348aa40a00e015a410317502e40c031030745030518240004140c411415012440038281e000c46841d40251440e070034880d4041009000b0640140c0d8102102000c1d43c1c108001070340f241c2010068070102c0c42030300c0c060208000d0310b04c285003000380d19020445c0254000916980015900d9120b900d008001c1d009018800da5994114031a0f4144110308880c0580503008402030781e100b80f0742d00301ca4961202e5003d66a000d6041814584040c0220400401d040b41d201810b0080038841c0106056100c440c1211130382d5501c101c250300080e2205031a000c00c00c0b005c14001074500f49840c1480541e882d0103603002098000c00c050794041542c4004250455075800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 599455575 1250 599454325 599454343
    0x2031b0c030f011410180e011e1401080a080417100f290d03120b0603090307060f051314010e0d02070f12020306010b1b01110a020d0903080a11 63
    0x604482c42c038805416100c0c003808400120390b90f0b6040c604085201d00c8001c41d002000e940156220002c0c04201d14030b00b00252880010044c01550398116a054106c005c8001c04104007503410041071034001c0b0407036098140e00585c03058001d508460190000141e1480840b0100c9002c01c05a2051000190b4050f0600351814104017501e460000b003180f04030300c107400c41014a00700030115407541c154003815001d9142502b940c1940801d106048000288c00f60300514503514604100045116a00c00403504d00d9005403540e40c0b0302d600104294080110700c0c060001e90045080060216040001100c1d000c0c40e02c080e4010884c0541001c6086040400d5110240c80442d00c0229043d09d025000080d440c1d1906020701c050340a51f141002c034801100c80d61075100d060380030f0010a81d903864402c94036040c0d0072022210460a0907021407803912413003401091041003080d80c00310398640c2c82e42c0c0c001e41340402d0420701304244414081d003000403641d000c050301c101103041d0410182d1042c488030400d04080c512 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 599456825 1250 599455575 599455579
    0x609210307093c030b0a020a0c020307060503060a06090e0c07050f06070305071103040b0a0c0201021509010c03141005100c020a030c080f121e040e0f06040f0b0102031b0c 75
    0x2401403400c07188141e114000f81c1080c907140090143c50900c1020390a8855400050800c5078400c001c070320450603a90051010650318600788001d12402c1c0c1c0028200341040d03000c0c3c80024404814032080d4904408804010400303030a00380803c900d80101183c150f000280301000b503000214030841849030900c44035010040c00030a9805501d480e0001038000c02c011303100d9030005801c9494400940b1400001c070340c16540e802d0102400e26915203402c40d41030038080c5080f030460050f6030714200c10840100c0320600405142c1c00100c0c03014075903a0000c085914011240d010f04020800b80400c003201e0007813010595001b95102c141c4100207030820703a54183e01400c001d411412050000040c80400100d080c01d035414501603d05004d10003410a9032442a00501e0451200402242007404401d03601d00d4440c07035803041710b18202036840c0502c40b02a40100d6000030454440360400090345054443c140032014129001c0000c02c1c1c02500003582c90041d4101e80588188280781e501103140200141136001c200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 599458075 1250 599456825 599456849
    0x80702060d0608010506030a2f130605041503110108041704062007210201021c0c02030c0406080c0402160222140402060d0f060e0c0a02060921030709 66
    0x4801d04203000301442d100e0b80c030030f5519050104449140204122080b1900b04030741640303110000303a41143c03000780c00a450100c012064210340c01603c491040c90440901e90b000042c03810b24040600054400c0480050082c000302101880000d07840c402600d001c000131310340141103545a21b004a0f01004001d2804d507036580210b00024910340c40300380500110814510784809918034a2560740d100f100b805590014002000c40c460705021780c4a4001c040707030051044444d1500940612440d00d4140c02a100020344d0803207010096050410007105035620944d41001a40e113410742c0240c444104250b04d81c826600000c41e0303801120540020360217590020b08800e502c2d2046040d400c2640300c1d603001011001d00b01071000c0c42203020344041074400c1d80c010f005e840c5800080e00c07001c40200700200c100155196100001300300031600311000e1344101100481d01f940d0307600b81203020b03160410040c035508183e17002c082001000c2c00e41400c3d5041800722191010b0300c0381c03610764040e200801e0035001510540c0c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 599459325 1250 599458075 599458087
    0x1407030519032901230a080a0207060f06030b090607020c1002030d02030906010315050403120c110f071a0c0a030f050c10020414010f0f0f091205070f0510091208070206 74
    0x3050703c0d01609061091329094001030201206240c002c2070004e1259003401e0621401b6801d038051500181c1c89100c02c80014581354aaa403030340100d800e189404070169981d80310500800c80c0301403000342c204411000900043c41c0c0214020764410041c00d01034081c0001c48106000d5600030402d548100380411300954980c980800d080d80e40d120300f4841910380c4403103103c0d010040a1144036640c0241e416030340e80785080c204401d100000d001d02159040401800082d0107011b80c0c024408004100b8100f409450f51a113040302e04509550048802036500303500b004161240003000608188961b80750400d2070030b40d004d001c2c0c1598580280c4418543c140640e50100c04080c01e03542c000c1c41903030150102c0c01200c01004004498184c14420210081050740400300c160502603888c090302c2c1030080c41d2840f101901ca49001c0c186c3c076400f210486044d400f0100602821021545500242206030b0b40f845242045280c0188180828840e902e50141503000843c1441200300403900aa034019041d00c0d5946 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 599460431 1106 599459325 599459381
    0x302090c25031218052a0f0f0d05030f0406020604051513020409020a080a1a0a050c0f0d181a07020705010905040506040605031903140703051903 64
    0x1000c003004a000090041180c02d0085c0e00f1a0800854641c4003440a60402003101b661441411207070318401080e01c480710050781802c003c8805031009080c0341051415031156003c11044e4103000100400c082d600069010b0081b40701c6d50440b144980100381e2021b0340c00c819144005000440000f01c005480d244c2c00a40706140000c00208000d070307a400d6400e00c4c1540020003110110b83c22072440450000c00e0044c03a034400c404000c14040351811207a070420900c02c0146072079074102d022450364113142c02580020a4100c40c000c941e0b11038020380c1032070410043c595001c1d82d551011040002c610a02c08100c00f002c58006031a200d00ca203041c041000701a08009090720742003aa1000700207000c0c2c1c3c00b00403440a0000500c09203048445504000b888401c4505103030200b00d030300b0000000065030003403c0300c50008000c801d9030f1f800c050a000c200c000c0c0c01c0c0c0504030b0451040110f0561020 = true := by decide +kernel

theorem cover : BRFrame.Cov 599280575 599460431 := by
  have h0 := BRFrame.cov_init 599280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 599280575 ≤ n) (h2 : n < 599460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
