-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0965
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:32:33.211696+00:00
-- url     : https://prove2.me/submissions/4324d1d7-0d85-4c3a-8670-2ec82940137b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 173381294 ≤ n < 173561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 173382544 1250 173381294 173381311
    0x2030702030715141f0e0a02091206040b13080d02070f060c0507020a1509050607030215100302030c0a1404180f03020114090606060a1d040f0501060f0804080409150806 74
    0x1400aa90b01907031425130f0036440100f0002c4040707164400034880c40054028000c414006c040320002030300d0840c031901102c5032910050076000a840703030b00c05407d8071b840c0140c5003244c008104130040780c003844005400c0310b51103400000711490840c91171060002540001d4080310704010015070f0102103507103841003107280c0a498072a0b6603074003218410042c45940355008101091030007071703026103880d600611344000d854040c6d8000b59105180d0500380d107410b03103094610b03040e500c5540030840c480b00b1007003180c03044a00c207070b023180e9981040e2020404545031501a000f50300e0700010304a0cc40b483c280c0c028681a80b04004440ca21009075254403012041c036400c1030340503030744404146401a0034001c0b000d0f07000060300050101d0f42450000a80c46103e4070b00618100076151324030600c00b01c4419015104200000c000b000a00d04115400c00070b8403007489158082440301180d01c001e98020800940f0403607100c80801e260506101c6444000c1c50240c607034000c500030103100403c9940d420071189010355841c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 173383794 1250 173382544 173382551
    0x5010f0203061201020313110604030b01080d030e0c22020915030f100308030406090c09290a06090b0c2d0c010903080a0e04020d0207080403020a0905090a0602030702030715 76
    0x2c0c6060060b88000384070100b00c41c2e841002040b1100c0700c0a500080d4440d032211a800c07417142200c00082d010f004c0e5030006000ca0180300000111124006000c1e030320005517460910400500180e09a16074039003445050300b2008074059158940a80084070381250100354005092402410124207514404414007520356400000d1080c4400303008843e0740e0180d40b00c2122800903045a031a210700e8000500014101c54071440b80c14108112030340b14502030001c0350020010208907460b03c1d40c0c0e01c003100340305c80040700807412202d0490030040005001e54005031100c0c1800c501e05110000c00d50b00002060415003c4c1203881000b0081d1140000305110b182c0044019015008000e203003020100d440c81c50600c11600d1040001a44070410342d1410310b258100444801e91a0002c038019109200b0f00b08549480001c00c0400c04c00b48002138010f4a00a8558074920368461082c60304403031302510742c00107e5002c007100c0000210303036030000d5500c1790301841682e003042029507580c03010130101c80000100720744 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 173385044 1250 173383794 173383801
    0x3050a240905100b04030609020a030f0506040209070503060f0607050106050a03150501050d12201905060105030d02070e130c0b0315090f01050d081603110607020a02010203040b03070c05010f0203 86
    0x4580600c2d500610b1030028504510302d0700215010522580c80014146a01d0703501c0d400656130b13102a1301b001940c1010446010394211714282e6102c02c001c64003207118800310302c0465803840c410303010380303205040107031550f00514001010800705401c224421034a40d901c818002c141501c408010000843c802c0c561205007940304941030040c2c0341c05800040c020403846640e0030100e001051200040e80c2d02e4280300641d04460710164942881d001c602c1101c9204903101c40c4022940384403006a62030082c000e80d207850362501d0416849420075407803c40180e0089000b440344148808420350440d00200c0300c04041d90540d56969184407140c0d0003000101404802c002600385d00c4a4001e450460031502400a803900c196034400403e8180501d50081160800303034420030280d030741100c42440d420000c8241c021204d00d00100940003041003c580d40c013840d0040341520740000343c00301c03640d07030b05030080c5040c10704002e030440040d00000c0c500e2007000240110071001c0b600030b04c9104a0524090000b6035240b5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 173386294 1250 173385044 173385059
    0x303070210050f0420090103120f0305010e0c03180703030e040b010206061806010c05030304060509010c210b01200a0308150f09060d3f0e0103050a24 66
    0x1806200341d07503495420101040381461071000100c1e400380d070001140c41140011402c0c82e1515031200951500600840008001c1c001c0c10541006034555079507c030703140c4040c0d200e400c4007502d0080c0319151420b409440454100b1550101850348110011029111500341c2e48007140b5102c3c103688103030040380031700c0c91405407400c040c020034019070420b00040400b4100400420700712060440a100d14510440c0419016841040511506604030b0112620303070038039081c158018030050310264540d41c41c0000c00384603540281e0700035541c01c0e070f24042c00001e403644000b41006402c1c1041e426040200e01a42c45282e040398151517180350304840700400b0b080c181441c024000c814090415100d401c44200c005109035149040c0d0012400e054489401a850f00ea0108510f48500c1b00001d210107128202580c211181440050741c4100d0b0340c0c001c1a0003220b42c035170020b040c903d20b0a8900004c082c04c800e44580d500981005810041c4044009074070550303103a0000740c90110001500c20b03400303244020003440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 173387544 1250 173386294 173386303
    0x1050a0204060e0d140a0602120105030606011205040204110f0315010201050c09010507061409030c070608040812061206190614010c0213110d0c020d03050103110f03010f020c03030702 81
    0x4084400c501d09818084080c1110020500c9603100c0c0301c01d0002101080108424000e21903011001c645101081d403400300040e4110141c60041c1145100000540f80740001d0228014a010384803040c48000d240c0381c100c040c0c42c4c020403d980141e01d03000904050301c0440d005100a905c441c000a403682818604440d6031061417a0382c81c11a0304102c107000004d20124121002c145007403e000b60740f20402e10f00400604405041818000e091400300140310501200030444101c0d181d082d15089520381c03800340c03001880ac0d940500091014014591000c030702070310958000310000e1510440082e9000d5407884d001d000c40308110014209145240c0380030b40c50240034050314042c0408201c4a10600000701554490400130380700d81c4202d8205100560203901400000741352890141e0345800304142400501004400d0380018401c1500b100c039950b1092103002c4c180c1c2e900c20040102c0f12400400c10103865905040c05526540e100029402602e6500c003c103250040d45001d5a00e9103001032019080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 173388794 1250 173387544 173387551
    0x8010524060405180a150e0402270c0c0c0402070602041706011a0304031707031b050702030a080906040314060103021c0506040303021c09140601080a0c0e0a0e0d090306051b0306090601110a140105 86
    0x81704944c40d8091203000492b08501e5104616809450b01c51039001c0c10549030200049511360014400a4140c0c02c3c444141c00900a840841c0718600c00d6905640301103682d00d00911403460303030300440460355070030b20414002580c105000b441c05910b800880140e1406175001512985c0c08203680e0b264103004240c031440c170305000d030105041c05c81c01c001c0d050f000304e070300c441e07131003c00910001000440c5a065941c210a4074082e60b00002c052402d020003201090b1b88003028082a0300c02c5604103003101c03000805459102c03c0c51340c0400035003401c1d2201d90b4150083d4201c46043c04800c88884542c48500d50140300d18140b03940500d901006046000f15030131300306841a0405840c0c0d800011805c408100d811241404032800d1941d507206a60307500500c50010100000b10000c0b030b0140e103c910003000c0c0c1c040750240a80303014100400c40743e180c2a00c3c2628011080d17015409010050000038220b1600b07403451a481541030612411000a2030390143c141240341c88105c034101140030b040900e80e002441856403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 173390044 1250 173388794 173388829
    0xb0102010c081342020403051506040b121b091006080601020c0a08060f060f0a090f0b0301050708070e01030204050f060a0908010524060405180a150e0402 68
    0x4408960301c0100b01c400c2c0103010007540400c3d403003104100320407075044500414200154000002640911502c0c41300e40304240a1401c140e02e100490002c880d01c00c4804980e408001013101e84190144202410f04c0100104c0c2e1150351140681815242c4a001a00c2890241c0c0a0040105c080904000b2006128080d034040c944500030011089512480c0300c0584101b070602c50040c2c0e40c0c00b00100e14000c0244242d5800070212030001500a0000404030300403070360000d2881042d981e080c184020b01008442c03040e4050183c410030040c0034220303842000d0300a0b4845000c00d00500050219003903840943d02040010b09107803c000805520902c2e494400d8000d28066142c14500307800604000400241c103440785100140c40c1210501401c0c03408010003e0400a024601e40191041202240c0701806054000d0b00001040f50b032034520300b02da00341c07800240f203c0300030748112080c1241400c0040402c48202e50b581204444030082c00b80410080c0501800c100c09840c15105101400c516144003a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 173391294 1250 173390044 173390051
    0xa0203070b04030c032003030a0519020a0308011403010f02040b07150207050606090612010603030207060e0a0b030c07080c120301091107150e01060f0b0301050406080714060f07240b010201 83
    0x40c4c40100e02004990300070307581444640200c1c00b0002c20648039495582d041c400016400500d8ad04200a4040c040d01c1c080301031117403413000c2802d0707848940890707008001a070402c005201110603c000300c41d8080015000080c051050a1000b0490f0300c160040d601d1240b001c01c440d800c000b0014031580792179801c08419802c041e0595181580c0d403070301030405032145014400003100e40d190020f44170f04a5070f0100003070060560742d090186d16050b00b4005c2070b0024002104216042c14038505030320071900002942c1e07203142d958244904030782e0444082200c1c2e103203003001008001e0b40c0400c00c1e5480c45045030032003030344c075450100e400085030201181a4109141030003407102041c40c144d00d0b880800e00994000c00c2070005140c1140c01004103400ca6601305828031408103008941c0743c050360583d50b040e2020013820341c07a046055900d400074401c1d10300040002c0b40031600750401801510900d011141c20a0502481da1f0b02d4048810020800007000041d08204603124600d600900010400c00c3c0000c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 173392544 1250 173391294 173391299
    0x12f0f060f071d0904020d0f0b060a050f0a030b0c0f070308190603030507020f0a090c03020904050601020a0215130902030108010209010201201e07060912230301180b120a0203070b04 80
    0x4120f00784092500500c40c0b40e40e58006415502c652540f464040d07071040243c0700380643c92038400180c140030b0750703498050040800c0100301c50608031120804030200601d0b0003d094036623541c03075070030342001030070343c0e607a0042845020072092400c405000110320a44580c82a40b03042e0012101422004107030380001e50501c00c0c1000400e0f040070403207460f82e0301a20304070f012007950804501044a00d920421195142010614030103615501074204d100d8122814403058550800484e9550b2540301c001e0340c0155440300e0058255501d20040c41d01c4000d001d0999840c40c0e03103449140898000341c1c08070440340d4000480c20b00941e030a1040c16000d40c043c0c1c23400b82524000c405e02c0d260380d002c0d541e40031307040c01118010000002c4440c81a26074141c1e002c0c1040c0640c00e070782e00e1b00300001d015441810001c13501c0c1800c1e49009082d48105c0e840d140f008600f0190541e0320305410070050181d85184003e10f1171f0741e12242e6450303403601804000c8a01d00080106a50602031061510b01005503024000c03009090105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 173393794 1250 173392544 173392577
    0x403172710030c030b030712060b040204080d2003030f04050c091b070305090a1e0801020c150a1b0207080714060d0c12090b01050f040b012f0f060f07 66
    0x1008903007507910b800203c0e0500c504040e00103080010044e54584200600001c007400b0095410103558170500003072115040071000d0000743e004901411005810224400142c00e02c1400803c03000301c40c171200c044010740301030b94040c15507100340d4050300841e80c514100b20911404111a0100540546002030710707140c201408408500e041072420007545002819006042c461010b94100f12001009045540c0d66109000343d2a6150111754040c0c44040c000021440e40610955000c000800003916401008001400054400405a56420746e075101d081c0c4007401076400c800310b500403d400070031520341007010541c50081c95602203d02070700401900c0005840ea90284d49501d00c9074040443d80d4003465409a9503203040e440c40d9050285481502d90a10081100060413520700341c8031640c40d4a911803d10054541805009000c1810312490a4032074504180c0712807141c07050b510100c00c58540742c180300d040c0070540c1c0560645500603c10700040800500c0102d1f006100c82c10705130342d200001d004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 173395044 1250 173393794 173393809
    0x10206060d0308090703060e010212071704020103090f060c02010507030f0209030a08030915070804120c0809190503010e010207060b100221040e04031d01030203130803060604031727 80
    0x1001000c03c041000400c82c0c1180030806540a141d01c420184070b8140e0b896080c600030b401c108444a0100310b104041507629001c0c10b000f0186c403034842000c0340c4681c0c5580040d0058601d4010407181c0d240d4042c01070010801521422460b220f00741e002180d00d0034a000300400b034848040100c600184100301c100388940d80020016901c1d54807203d81901e035950290301a007805e0040745512100040b000c20428602da004021070b114070702c01c090300c0c1d030f042c51941001c83d00b640c10040010300041d0100622141450585004220030034a0007080741100c0c1c5800200c0e09480e00c00e0013558480c3e40208007003040010501030800824401d5400c03052135880c0f200020b541d80c0180781300a400c00301035101d207a001103d150480b0042c044907805280e00d03013030900d030003003295540072000c04064007210055103241d03200c0d001300c1c0e02441c0a090305c103d10415a480301592988007410480c0d02c10420080000050407200a403051685010071540e20360303c40310720084250817041e035600c41c3c3d445084020361181d6034008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 173396294 1250 173395044 173395069
    0x121b030b0906030723120d171605092223070504030201080406020405030a030e03010e06010605031b0903060c0c10140a0221040b071101021c02090a03151a01020606 72
    0x550454101e13041e105d080c10100070310b05c1403500001d5691108040100c0040c41e5294042580c0d81c00b00c2d0491024110a4066010b860600100c03c08401700824076200e0b0020748000360000f025080e0f01100070030550010700c0102c2c0c2046103d601e5020b1007c900b03030750344061044142c0d14440c10b407003490300500c000c21522980c0802030510403031401040500100ea4183d401600c4003900310381c0d00740000e04000d44803140c101c1b0000c0c0300350308100310f900c0980740c049042030407105962170302403d540b070315516945040c003510a50b11881c48140b01502076940c04208031401581e445445d40c0d92007903100c1045003031009c2c81012a04050900541c00d01d90703602081340548c0714012107001a121142c602c0b40d01d4415202001c0071903002c02d1241444103104240c480c00c0c2c010320040c1c85903883c4206551026090740600c0100000c02c04003030501e901c0e502441c1d0014680d58200601c01203c10343c6039520440c250070403d6012114541c1c0720390110300309124024907849180d090004048601c0c1060015440d0120034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 173397544 1250 173396294 173396309
    0x40902090615120406091e02030d0f140d0e010e060906041b081b010206130c0b0a0201060e04050d0207050a2420010506040b090403020a030f121b030b09060307 70
    0x82c07003403031000320081c03003a40d0400c410415145918140b505001000d002101429101020000b800c6001c4184100c0c10081e41a0301502030540031880d982d0a882c001800f50a01040c020503030003614402c18090000c12444071801c10000e42c45d41c1c1e020146086070800d6400c01005e0340101d050141048000480e0f44e4480d5101001554000110040600c90354003580155140c2c450b400c1091000040d40c8001c0c00d20a80a17403c9400c650f44403510280c101408240181114030815028401c4203030703100c02080c014805000110303c00b596114500c02c401c40480e01594141c10640540031707400d40c1400b1007001132034100d918901150030580e5900342d0090480039403a030001e900d09082c0300f050180805821408034540d000741508a01c0c440e00d806000102e540f6131140e803a145821520740b03418000c0c58010780c1c042d4001c014441d4142d03400e0341c82480801c07010050002d10719036a000b404450103840c103001c400f80d6015003520001403014080c2c07a00350000a1003403124404224040d10000351300c10498010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 173398794 1250 173397544 173397559
    0xb010501050a05030a18060509011d0c0a05010507050304120c08120301050913050c0402030a060e1303020604030503090109020904060e0d0327020d020607080306030f0a03020c0103050712060311010e0409020906 92
    0x10071544064106c01d13001700f006080404001d00403506511140030034003a21000c503c1c08203288480c507161140541c56680c0711007014400c0c0302ca5446600038004151051080f40d14003a2520601f562031a02407004a40b002d00b42c20b020301000c202404a0190782c131103486198290f50508001810142000b8404501c988107801e41009201003040f0442c1540000f50085580342410301c0c15001920b040d000303560031650034401040107407501d680c3d40d00b4001e0f0980e020f0003031741d10340343d404485035440a485600650340740c3c00781002503911132030014080c2d48540c00002d01d2903130081006050840c0300c1482020315181c017600008104022052008040c40001410319001e5030f031000a00c05180024041c0d08107101007010010420150021401040c1c110119011511801034584da10300710a40004d005811480030040e541d4001d401c459000481030a15480a0708444c5541c0100c5100e980306603210070612184082d0740d41c201c826803c90203800d079010300c0a013456070046044500007500c400d000380384 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 173400044 1250 173398794 173398811
    0x9020102070308072108060f060906160218010605070b090c010e01080c0c030f0d180809040b0f131b17040803220c0608070503190b03010f0f090b010501050a05030a 72
    0xf003890044d08074070790440e032598100d0a0743c000107106d024100d0b01203000b03605501005450b407a268042d1691100001c01c6586010400c8030031000300145103104903003007512031803d0080d0107c54032a5502803c91a40e8841d203d9400e800c5c811500341c4c0103440b01205401851404181da40d0048051100d080c0a0038141010788030003080414034450007200104500000c5120a241010480200341c081c4101005205004804804001c80c0024000040644404018015080c00c01e5008942680401458114100101d501040d5001c102c3c01c2c814000543d602d41104c5501000c002a80d000d044905c1c110520881400018208200160000e0440c0501000150403000042c0344d44000442d002c0401d62581c950b0302c1c111000c40c1d42c9020300404501900005154075202c1d9040d21f1140c406c02100343c90030345071140650010108102d1054165484030b866443c0c0300583c1c000e60b07590340e00080c00001d6030107882c2030510343d0fa0010703042241003081c01c000309013000b0390000c2681d4206006030000103e20300c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 173401294 1250 173400044 173400053
    0x30103020310090c05030109050709061703030711070b0d05100605030c070201031d0d0c051009030c120c02210606061602090c0403060606110c010e0a0603090309050d0c05130902010207030807 84
    0x1300140d100c46e90540c280345a1400f00701c80482d4010440782481d02c1400b8503615419040501c401c0448000380c0d580c0103000240d106441410b6036004000e03010240e40e010343c0c90700780ea110180c1c044040c4501060300c6006025005244505500080946190003821800d0000908016200c1c1c004081c5c10151100004411050f840d0f00c22401d400c0c0c5002142c884083e1150080c00c1d481d002001500c090141d1800300c0b0301d008090290446040d45a501c2070103c50543c5d580c24040115100910100080c81c0701c02c20068403150308107040495028591008110405052441e18800404240c0100c50038480c858140a00d4450101380f281d045400b041940d4800d840002c0e40c0c06241d0026005500740180000c0b41500241049090080038040d280103544000c01556402d82619a09030442e07500c05040204034401e51051045510900e014114242c0d1800040c0001807040b5040d82c40c0c042c103203010880c4d0b152038641d1030003050a441e803c0c09803211070b400213900e400c540c0c8006001c518000580d40d0401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 173402544 1250 173401294 173401313
    0xc120801050f04141305071503090c060c0c052808030c1908180d060c0903020f0123090409050a0510180f110d15201305040903030902060a020a0c050603010302031009 73
    0x10300081d242410140b01d0b0507230044c0a00190441900d16084003a008500d0f5403280500881c0140c021080da240d151820050103040c8483e04010601714484c8d0500a00b442c1c1c3c4090810b00a040c1e110080da20f4940940d03515041840d0340d0080402c89028048400c000f44400d07058510040d0801c0b012482105ca00c0c0120f541111600c40c01400180341204014515400030103c001740d9000781c1d0f001c0080d03d041c80065404c09502081c07030820301986055049048a010020404000301910115540b1641d5640701e107400b48440c4200d0b02c940000c83c080f504903025200f50215086d1409488040c2d140589035207166640d0380d00082c00c60300300d03460b40503050b80b0313146110001d4075841406410313461066410400100700c400444048050f006901c0d008803928281504d03003081030320404428030f0380360004010051204d034000301d00349922030020f8000350343d0358006404441d189402600320a5002c0c038250000c60696000303944105420300060026803000210500f03030041c201c000158540b914102114031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 173403794 1250 173402544 173402549
    0x130b010c0b010f0e0a0203060d11010207081207051b0105040905060f1c030e030303190b1f0f08010506040b04140a150c031103070515070c120801050f0414130507 71
    0x108402078000103500242001d0802180c490181c502c403644c03a0900e40c2c400ba440283e80d6254450140000c12011542058030258501014011100f68a581c1d1100c241807a459805441d9103003004580350041c80014000c40b5000b0340e4074440d044900c85100006410f80c0140e000e8820256a03410005180d5110a90901c110481c01446100b00d024412a840303200118003504400144155a1022140c100002505d0158842c05030032400d0340181040030000b00a410443caa00216690302240c54140810104a6031101690f80c140c803c00401c0003e0140c036010f80c0140c1c02000e0400040258036850030a40d07007030761540365406101c800e540c000030340c80070002d8000c20720310b2078040038258865812058410100b0300c2500d40a50340000d9011a5850b4004c4d5040642a504002440c5c2c6401200320a52580710050b41801001c0034103a482c1c1041c031242060301d01d40800c40400050040780360000c1840580b40f82180c1c1400f410341007140440010a018104c5008030080990b1074040150070b0090740301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 173405044 1250 173403794 173403803
    0x11060108070e0a0e1b0f0103092114070503030601140306131d0f0303010f05010305010e0705160c060309030806030105090d030c0905060c030406112107020604080d0c030906020c130b010c 82
    0x40170400200410501c0b8003c1859502c1000c0e00000025594028000c078800b550b040365109080c0701129041c900b4061006601c601001030106084115001d40d90142400600540065840b8900100054443d507205103004046960034010000b0542d2048040301c00070030410008200e42c000070b00010a104054810b2424a003d112060f40c19044000042c60403181100030f40510541d0310401981161028003d0180c0c0c5500e4800064449000702e0040c000c0403204c4030341150f22000c030f071138003200301017150005800030341c070f6503032200a141d0b220000a070012001c60003005282002480e480c1e44241c8403940b00107158170b0740b101c4c072552401031840c0c3d001084090201031352242e04015142d220b174440c1c0070b05408034400c0203c04c060b02400040b00d09040188503640c2c0720005140003510503a03048500100d0b0301410030803005c40c401209000540850949031100000803401d0720b00031f03148900302d400540031036000c1e1404074680e54581011007910040344074001000151100100c843c48213560000c0d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 173406294 1250 173405044 173405053
    0x5030604080906130824070903200d14030405010f141209120d021b120a180b0706050603010c11070e10030803010b0d06060c0f02010e040e0118020111060108070e0a0e 73
    0x140c52818211072402c06c15440780c0684603650741d516064400020500004d0141c180d414080056620000400908168000d209440402041d9621041c00f1081580410540c001042c10000c55030040c50f03d1103503020504101c258032a00c103011120313500400c401c40c807580c126100072648000e400c0c4008684521090003603a030b0355141c45c23000c401a510009400c03400c20604280b05030010b80110301043d841070208003c0b460041c80c200121303010b031a00c10500b041e419151100080f0400010000d1002c14400e00000c15140f40880c00c0508488010048505128000c8001e00407240301042d501c09079402d2101843c3d050f10344040410b403561003604000c002420001c004100c14950101900506040060900849403a294115840826628010020008031f442c140040d80141ea80400c0e50304040d100240b003440458140d0300751a089010f01455064038120602507580c81058080d48001c17450041015500d00801991b48100e144103c8003118003140c0400c0e117003885a084801c0b034440b072204a5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 173407544 1250 173406294 173406313
    0x3060f0406170304080708070e010b0d060503100b041a0a15050904020406030b032a0127180b030f060708040201120501080607110d0801060f0201180605010906050306040809061308 79
    0x6583d654005e0259628600c04c003100000c0b92980092020305440861101d070707603c2e0346005030f00b01254010119244038203454071408100782d00c080101c1d200c200c09564001c03440c41648824001214696110310381420b8405051480c079446070189401103d41030451a45100039089044550740288009158001c0c00010001b41d1240d141d00081000c040480584410052040b5100030400010301d041354502c9180100c03004541c041c0c014000c040340c101110201803c40c10301140040d0003941c106660f040750f00101d01d82d08408501c920342041006400400301060028070140c2d542c0c0d0010107240c104a5960005030131a4841c08103a00740f109006000e00055858030390f100d40b15007040b10000c0015042c0143d0b00100340000484400c61b901c10344032001c040e420072404a880c00705102800065640301c2040500e041041c000c6c020959010f1000013030300d541008980740c07d403142035101502c43d0303106405004c007060000013207807808070b0103c8813542c1d5640000b182c0d015400aa5014540900800019 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 173408794 1250 173407544 173407589
    0xa08130e041401060518060405070e030f06090c040608060105040507030e030a0e0f0409030f0c230102091206060102121e0c010f0605120d1808010504030203040f080604020603060f0406 81
    0x306440e1142e0082c040307a51120701340480b080b0f40e030040c40d8411502802141c03031070400e54400e54115107240341c070300d1f100d8840708040784c03605025140d40011540b1a40c20041b40c0320003404550002c3c3e1003140c060040c1481e0020b8680c1d6850180145807080759600b0200b0001400b9903ca2411088004240e030744a64010705e001e40381401e02240076014040071030084a041c6054031821070510390548a00404802d126011600044082c40403140c1d800c41c410351034042010326081c141c0584981001682d10410070b02032060350100d410201002c0e030f00090034401240e030086007840410005003911030304c8030f00e42c0c407038030310b0020001014580103200011081580c0300107412100066241400034031065940d0302c20312640365014007100245810080401c044141304103c180d504d100c00f0a0607602c4540c481c9600341c21980c003a14100e01580c00000c0410207c400402142d00038279440c0701034400c502d00b98000c1a418030005001e64443c1c065000e06182d107564941c00340024000310380b00700c95800d0600c2c11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 173410044 1250 173408794 173408813
    0x1091703010609121220010e010e150c0f0f0405041b0315080709110c060c03010f08060105060703050a05070510020d140c09040c0207080f0102040f060c03020a08130e04 74
    0x16082c00610300900101d24901e44541000602d94880c40b01d1268501400b4112107603a05c80100b4192001440b0801182c0c044c00d006000d80d40f00040c0001540c12105030741c1f5450415882c607244120000309041114849100007030320045007018042e682d60b00611100050f2034811500102d0307019141c041003981030105036048681109003074904010416404510f0700c820b04203032044040603031040e101400102060341190038013641594109080c00f016201c82c81c00c0c118102ca00e0005404044010000049041503072070041c21a00d001d010b003035041c0381c0840c0ca10b200e42080070301881000034017280004d1141080b46c804030b410005a524101d050008a000395000381c817110035080c00c000c820382c004078121520a00656400398030390300c2c01040509000182c6212041c040540c001c8510010302604140003000010204400041e41c2e03506108000c0e84c1450035810503020444104402400a030300002c220720b1680c2c000d2800354850140c2c3d071844c040b00e0982c0c0c01004400914205200c10400d1058 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 173411294 1250 173410044 173410049
    0x4081e030a06290f0f0c0a170a0801140d080a1e110a2303030103080a091a0d09050c15120c07210302090411030901060e010506070605090109170301 65
    0x381d05101455071601d141c80c000d60030722102c0c052007082d41100e02100b10410300801c94080c000c140b035804e0008503400d10025401190040d41d02e07030801d0f1486010410303c01c031440f180c0700291a0960030244601710013400c20405000d00c040c0b02c00491040740465a800d01c000400310f0384030199550f0b800b101880201079202000d040c004c41c00c20207135000a41400b600b00074185001c500020200d500403600c80700c4520408003401200ca44c0c0320840001c0d1404280000c6020b18081d4901558510ba51071380203204640680c411085409141c80b41208230821704200c901c41d03140c0c140080340038805828440c2c1070032010400c040d842103221415014042c050805409036148611244c04d807590b403510212468807808100400c00c1500403510014449a5082c00b40049501c0c640141001860b81c085000c03542c020802200000b000b001f0400c21510074026032014012200003003c503540342c90003140b4280548400203140503111000980007940035480507001c150800307684100c0c01c5943c01170b10010307072003030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 173412544 1250 173411294 173411311
    0xf140109020a0f0c1b03081b0606010c060507110613031103090303270a0e0f15010203090f0f030601030b010e010e010510030218120d111506040504081e03 68
    0x4000050410028070a0ba4040303102d40c0c0f2070392144040d00c402280d090083c0b42c41140c083e0b49980006282c0c0a4849608015602c20740c2c0450384c03040410b030030456014980c0d0f655113265005800300030b02da0742e011f1075030384030194800300c04141782c0c664000544100007a0780381c044070b13840341d6000c114113208600002c10b17002d4044e4031050070300380c40000180d44911400d902d03c0d070181e008104240820404070000d2030f07504220040704030046103403c001481c1d202c069200c858900d4188041c00704c001e0240072507603040214160032003046001c0d50000307503c2c1d0007042002c52064400e80d188181716212600c024a0f0704200034269030ac0d035a103924002400307003003e01400c28841d84020000c11102600001c043c142e83e0020030940c0305201290742103000e076010703122000910003002c1d0440c1d06616010000c1081003251070140c00b0840d541a80140b507082b00382003101507580050741800d60201145074264000300b00340d401243e2a036645c188601c1510030303200c4c00c6420076000c1c1d001010603030f003d130702071802040207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 173413794 1250 173412544 173412581
    0x1b0302030105181302011b0501020a02070302010e030a050a03031e09060f0b090405030405090c04090f060501030b01020312040206130e0403080f0601080903191119060f020705031803010b040f 84
    0x9014507208280f070844e42c0c684181e00741c4044002542c0a074060f040700490084a0130280d11242d65107900b07a808c615190400f684c0820703824021581c0040c04c060115205400400d482c80c3e86485007541c2d4140a4000340c1416614040c0174054540d80185c50383d0034a40c00014030403100180303424401003070302e0468070300307014644090b008084c0f4000c10313050b000b01e4106005608040c00c0100300400074001603c4040c0c0807804001c0020140344d503000d04159a04100c5001071214601400075082d44d096094031411034100b00300304043c0d20607444a0a80043d015984540c80b0120b1454286c50324005400c9254800d0100d000c000030107512454a034401c902407150043c0c16107500d401502da1450650302030005070070500290700e604c0110051040e811800d032034103234080c2c00441015410810766568440c83c01c3c0c0c00d5a0780d1002c1c0001c50107125082c940c192070441c6000501e03140c064882c0a41c018400c0007901160140700030740d50940150642440c0100100100e0000c003d015000740b84950391007140610 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 173415044 1250 173413794 173413819
    0xb100c1407060207091107020409030e0901240c060f15150203040506030705160209010f1a0f0712021515010806030609191704080d0930061b0302030105 67
    0x101007600000c840581d002080071904000105016103035003041c80c03644050611405025a4582c06064aa580683c071082c0808078080e003403020703001c4160006c5190984907001d040f011284000a281c2411841c606610740300914034122014100c500f10103468181800b000c6000180d25244d448111460054a440d409428050680c2c903805684941c6070b01150903c0000c0c9240d009a000744811404010034410080710341e40002c7d080e40007a0401d40911543d4801445004040e50b49003880000d40c40031582001062070205120344610341c8001c3c00499001c3c014580c0c03a00030404040300c0b1007150807407a05407401c00c00e000301c0c0620040c850f42c001410f400124009080c04074206d03014011030000b40403070600c1d10b002e82a00c03103407410302100d21280300d00c402406405e40101410141480001402c60303119001c0c0020187c80d5030f90003441030f400c0700c8840c22444a404200c070005c1258501c805080b2802c85050110040c03840309122030121410100d04413050758141c3c0118141c400803158001d4124 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 173416294 1250 173415044 173415083
    0x509030712031704050a060501080609070f0302030a0f0c170d08070f3002070501050402190b0a03050c0408010212010306050106030911040513211403040818040b100c 73
    0x9104400980483c8000c8018040300070101c8480e0707403041c090f40441d95044000c1c1d441c0011151709901540103070300040300b44409110280401c000a0040c00b04841400e415a0002519080034050044c804000e240542e020000c03c0c064100050641000a4160b00441110181c40d800720303c07480d90020741c0180004507103502a82902410b01e00c10b950324109000d10703601083c008504104801c901c0d00c4040581c6d01009694001044801d100390001300745030074175106015018603407064081040c1000d440c2805140c07001401c0e224100f48501c1c010406031100201c01140c0e10403600708079143e500000382140c0400d011218141268400e510402980e070307803207104500311504c0d1f1400801e041049800d03030407180707410b0b008581c012503508400b081c0c0c00000e5554007600941010400d04c641199505100304a4006400c03140021182c030940e0714515043d81c1d02a0300d4401c4007211070105854003085000740c1c80741d0f88400b28041c03010305103651000403804040d0241404d5041183e80f0003c02070ba9a0014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 173417544 1250 173416294 173416319
    0xa05070302190e06040f020c030703090807080c1c020d0f03030203070210271a090a030806040207030905270702030d061a041511030d0203010806060907080610180605090307 76
    0xa40400c400f1481546840c010800580981d124026040d5000d0041e00c071007103000d0008101082c0f01e40c64a0407000d28000320340d410020b1076032150f9000c1c1c02011208080c0d45810058640d0203402e8030604014110902c00208030030025100940803140742000442056010741c011809480c2c0381d0212001140e1256201c1e090b6101000039042e035600d1183d44259661404242800321840b502e0752540354450071a858810b0202140c1448055001c40ea8400515800119042e0001401d450941c81c0510340c1d02d000c1c0c8450a079210303407400f403600e02e9031002004000c00c01011809580800940c02802e100b03000960340e070000c081180a003440c03c80005050000701d203680d480041c800d01414106440c000d031000280004002140038030144d522030301c0e5240b0381071009000a2019020050701c0b5410301c0b4905143c01300c0140814040c20b050707024000c200390007610b069403000007220781c005d04404d88801203030a141c035924402141000c0d180082001c940007405007150040503021102c416030364448003140e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 173418794 1250 173417544 173417549
    0x409050c040e0c04050a0c12060609210203101a0a03020a030618080c150127050901090f06050117120f07030302040302060a0806120706121d0a0507030219 68
    0x99403114000c40c19a050580240e08504280c03020b07942c50710f81040100303003074038011034038251580c0c0c0c1c8050b10044242c026000c031280a103086020042c5e2410030001821880f40b9001d100741c407010401056100e480c40c0d01040100e0765018058032040e40d6450320840180062054010012046441481141c03d010700300307000306d81d0020b01d07000183e807071a11140001c0100f07885024800300e03907851110104064100038103041100d40d000700140d402400c4c80c90041041a00080c80c09006000d90030803c600002104a101181400c0001c00381c80e030110041c01801c07140d6004000c800d10300071040074400564070007412101e803060200c11500031139034110745420034005003a004c004c1c2840a00c00301d00b40280a0108a407080c10014a03041d2242c0005901c1c1e00a0700c3d810700014a0f01081024505025262200707002071035000b00852410701c10b02400080c50040e800317001d01d036501e0080ca4580f42040c40034400131542415220440b0803820641c2d11940e80b4003003603019090b01000072100601e00c4801004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 173420044 1250 173418794 173418803
    0x60807122109150203180603060d02040f061701020306030708010c02060f1306021803070506090121090b13031b0c0618170304060e03030705030a120f02270409 70
    0x4000995101080c940015010110410428403000f20b084401007110b260903443d5038004640340c070000c1260804c0c0e00030180382039000d5002071007409003e845040140c20715550442e0007240c0d042811400e90014550b960101041e0311400304403c0d40c4620640c000c500443d0305a0507101c541e61600da40a003622a142c20350f000582c00000050600d411480c030840c0c00c003e910840710440c064a407207500a030707000406017611034821000d0b04034180c038040100702d00070041942c040381071140355000a406655441081e1000c800c090000702c144510030347c070a050260380a10940f1700740c28101092403051640300022804101e0400041c15140030754608418043c1e8402c0121581600780403003110704652119401e10060448039000c180411151951000b1a500c0002541c0321031508000911440300b040d10700340683c00820001000ca1008411a0074403140d5040155440c2c00100750304000703159141402ca42544017040ca102c000620100500c25000c0120f000004941e00004110031148850402032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 173421294 1250 173420044 173420063
    0x70f03020604030b1005040c030b030c19060e03011e0203011d04120c020303190f0e040203010e0f0603030c0706030204090f181707170c06070512070e060d0f06080712 73
    0x40002c501140890b40b01c07070b20b401c50300316144c0e41b000481d0a9a0310380403950042600c941462800c0c1c00c2c20403151854290031200100507980d51168200341012a000300700c2008502d9812042d5901e00350002145076000c036120b40024480603807607030000e400a010fa0a00c00002c3e00000000603095000300e8045c641014000c0e0b9100500b04065034940d01710803080b0303018017040c010183d020840740450040d59900d501d0f14490790740319040003400c0400c05070346288520710500c0103010848207a881594001c10540a5030300a4850000091440c094031254184a21583c0004921a42d154002d0070403074040c00c005222000005a8203819035209120f810400241103000270b002c01e4009a50160f2001001515803400301291506500031000324801c0f000340700d0004542c00a407504001140d842026031401c00c0c180f10030740d00d0704100b000000c3e09440400c0b4107100035480a6445800301c450740c15450300300f08040b5508680d000094541441100d1043c01104c20000360036101340c00d10b100301030b030120684 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 173422544 1250 173421294 173421299
    0xb07060b030a1a0a060b03090d03360206090909070f05010c031b032006060f01090e070c02060f1602040608010209060a23031311010e0f01030c030e07120302070f03020604 75
    0x8884844000c010409150705d961300000c0200b03005005500650589014121b2220a1003018040d122015040c2c984186520b4001081031100c548409400c07a85012070500d040321400011490b0060322405588144410144544c041c800580c9030210344007503940b50042c0ea40c503401034401103140d040180101d07041c0111b28040b0b24820b01c0c03603265688281040596520046420203200c0c0f0040302c107480e1644540240495031400540c003100621091924203910780c1803980d9403209182c040d2406c414044c91180d100115502e000070303100340043c03c2004a0311a1540380004001c900030071400d0707005915091000c0b0300242c0600031501001e00180903145004440c030001c4500b9140300d00c01000d1407004941045c0c20312000300042d80501602001c1d20410405418448001106050040e0600982006041e400e407680248601c1103c82400c00191034605c2800c10b40c0a000441024a000d000e480b502103451541c4041d49a0744501940c01c950394151980c2502c605113040b404065400607041c4001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 173423794 1250 173422544 173422583
    0x10f14130213030804080124050303120414150f0a0c020c10090e0703020a140702210a020306180706020304141909090c03021c020120011103010b07060b030a 69
    0x42c0b00788055140d400b20398030354907224243c41d80c01c69041000a65111460780072601002c204c2c41000b13441d4642240039051070200025580e100300f0114000c800c80303100000e024007502594818000b28800240c034040305500700d14142c40001250300070381e001140c00200f0011459441030000d1050680c004140d41c801001c200032011041c401030f18108a0a8400444d041101c03c010034080c100780d80b805601c4a0210101400c0c0e030190f150b008000b00e03400c0c8642c0b0056510a84a50010840010114040d070303443c038140c40c01d050001c1702c040e400d032203440c09000405039041c0140c100d005804054401180e00c1d900100c3e1203100320300c640e9131115070074440b0b0745e41c40c6400c065280140c11000314841186656000d4001a1241103000750750840085c4010015824110344030141c25140d006c0b14207075602158000b030458002880c000000707001c031502c2d20500c10350941c8042040049135440399220360395416440c2c4594090700003103801c04c1c144604208030f41000035174088091307030260000a440040948 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 173425044 1250 173423794 173423797
    0xc0e0621070504020f090f010507120503040303020f03040302060906090a05150601020a15061e0608150a121110140a03051005040e01091704050f15120c03010f141302 73
    0xc00c405501a0381d60000300d40c1d55610040041c00c1c0301c00c181c50f442d00720352420001d2100c1d00c0c0e5003286c14440100020400a200800226a0041b5506116440e82c4407400e0880081c0903210300405429070001c184001d043e000520a40701c0c0b26403104940182d925102069141c1d802108000c004c0d42c05410b45400000d50305a085500c04018812220340c03070140d455240700c1c010805680d480700c507564002882030384420015500310f108105000c00400e403810300010141c0f60018040000c0798103070780c80442140d03114028100140042c4006030220b008601b8510500f500901a880c4204e61021003080000e0107010307550002c0142c054154185460220258040c1c0401852011300c01c41072440480c141c0d070b641c07240d103664a050000010702c506882c0f40c18501100c2d1018030956040d020f10080016a4404040406101c1e040e2411029401a50f89103206d5015048040714410500410802c4841d4064040d504039004800b2054101c0d5072558524000b14120051940048100c0c0654525500580 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 173426294 1250 173425044 173425099
    0xd020d09050d0801030317040b0c0d060b030a0b09010801051612141008151009110904020a080405060c091f020a0b25020c0a0303030c0c0b01030b040c0e06 68
    0x40200c0c0400e810759401d8148410b003402d0101080d000c1c0014018541d10844100f001c500c46640e1340d4880c202600e815803100f1004010596051000640309000c0c0600d0f08044001c102c68041c580c3c885c1040e40d9014041c1182c40f884a000f554031400024414005009044c080c201c0038403d86042c040783c404c112103560f90030141d406899118241c2884141c0341101c124820020f04202050040c2071049250600a00084086a0010304414803415809850f40a02111898480000c801c0d0001c0341c59603050080243c6141d2261010500351240c40d0803007011031040c5d01c1581540c241e039541801000c244e006803551280c010350f1044070101000103400d00d898000303d050040b20159025030381d610380c01e043c0840b01c0d20318689015201c0307141c090200000302060013150001e40b401506400c081140c50504c0d11000e4101903c0d190704500c801d014207240001c0640000803c1d07400d68407410008920007058404552040c40b401c0c00060000020034001d01852000b880d589000c064401c08400455954 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 173427544 1250 173426294 173426317
    0xf1b0302070b04110a031b06030b01020109020108070e031005090d09081501060806040b060d1e0c021906020c070603060608100b090907020f25080312010306021810020a021509060d02 80
    0x182400300c04540d100e05416243c00140710840c00550a2a1001701500c080b62b44444c15607040000030340060380c1000d2000c0c3c0c014002d2030191020207010000920700410740080902a6150500384684140049028011202c142c1c550103a0300e5918a0f0556403065011401d03503080c4038450050010f14400c640e10764005400030004541e110354000002d00c00c4c2c0c00701c007070030980603510703418103c1000040c06903100078000c5000401c690f021740703140a034584094160703654002d440320300c1c000204000e03507041d04c082d0707040241121469911102d02600410301c1e4040c0c040456580400165008019000c1405480300642c0711810b1960361403d115818802030110720030344c09107c040c080d6214041110200040741442292170394280707002135240d07410440d04030100d941c104100140355824440c01c103071304407648681c006075120704c101607100400010030001c645c040e03142044115101d50001d8603900c000d0017101d11003604016a110396126114000c50f07140c100c10103001c2d100b080304840d4054200d01021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 173428794 1250 173427544 173427559
    0x1f090b09031204060f031116060b061e0a020105010f12030e0103060b0f13080a0b13050f06101d01050121180602130801112b0f1b0302070b0411 63
    0x144920462141c01a400c154000f62400030005ca51a515001c1c00e14002c0e00701e1915440d10000141c422024007001d000a46034a86410b0360003283c0d1181c0080310708040011446c036003c100038101c186010f80c03140c511580103608201c0003082410414600d00b00300c4a1410840347ca1260564007a2610b00981403070320305141d9189800114041d00c0c2c1d00070314200c800900c90560701e041554010208000c5c0b83c004840ea039100b14088000241568151504230010300d55551742c0d04101e1400710315008100701c15084500a001c14021800d100705203a0081e00d0540c0d104031000c6151131300e40b52a40340c0900c5944c0c00a080602e40d6403041c9002040900c10400501c40861251011002c07603c01c0e4004a104a40d82580007401004c118080f24042c0e001d0701c1490000d026420748070707921784280d000e881c0d2500786a00c3c84140e03920049214060300d07007891480c01c000380040c0103c0d401c0040103210169080c0c4001c20641300340000d0300d02c00c1c422500070b80d5000f50300c110035840300d0f190440203002c3c40120302d8200d40d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 173430044 1250 173428794 173428813
    0x2190b130b0703020d0c03090c0501180f030813060206042406080703200108151003020912060a0b10020717071a09040c0306080604020d0203010f020a020a021f090b0903 74
    0x21011144030b0740d0b081c0c402503520741c101e0400c2421199042403e0080500e841c602c040024405000ea0f42111004d203440800c01d40c014001041d0342d800d5511010910150304400000c100300e08014100050700e14010361a015610f040030790b180c80c4100d500a2503480d00b807460030350441009001401042400e0781c0051502d45030b90040b81b8050084e0801e81d03003000301c0c1204980b40c1e400d0600101009200703282c44106414181c2c000d24001842404003442141ca5600e64100f082c030030b60688104610040000390340b004104410341d241d500985406103640c0c100306040c0c61600b401101c42d2020280d036401443d13006c0c60405209100d039450180d40b1454028001300180c010320b90444021204402c5d42c00e6079072042c0b110100411140545942000d040c140325080110981c04590540c0c8950107468a000c11100e0b0300c0001d00408007158600221480071507120086035001400070400c2e031081d54005840301788452429035460070340891100040600006204079046071001e40721581025080300c1c1c0c03460 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 173431294 1250 173430044 173430053
    0xe0d0804140d0c02120d0c08090d0c1706060a06020307060225030207060215100e0702160b070209010b03040b2a0406030203160e0306060d020a0e010b0702010f02190b13 74
    0x84a4420074000340c42c107008002580f45c259070410300710702200004c041c249400500601001c5403008041c2c50f0302d101080203825a107425130b1012016600000700e501c40e075100c0c2164a51a070307408007811000d1080301c0c000780c0c00e42070200c040403e96086070000e5040589684d00c0d01c02039031199020f40180088580400903000420b6166003440d40300b0707000741000e5420440d00038074058005510314004101c0030180314400040c1c0d6040b0040c0d41840404003403640e5200c0e016480c1005e800290001403c80d46000a103002059016084052080b50041150390340c450408a0038001a2400f506111424002c00c1050400c0740310030201401c0c05c088580c2105903042c1060709604141c1c040f0b00400e40020030080030f6880b00a542c5002551418030550f0301c1c240070003081d610b6078001e101034041d040c0c40143c64299515142403100030715000c2d41c1030307010b5a1201c502054640048900300d01180408121003038950010034204c2d095044400600180301e01a15507000c40300000d130105a0083c100901c880c04103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 173432544 1250 173431294 173431303
    0x1208060906060c03130303050c0d0206100320031c0905030309061602010c0b07170f070c03030b040e1b01030b09090a11010519020c01020f01060605030105090621010b0a090e0d080414 80
    0x118000d4469984521014944608103135103104604119001001004dc48000d80488102602e0f0010300321001000d000c1030081c180301d00442d0b00d42e41742c4110300f044000d40841e160b25002564890740c81c200140e07603400c149a40c1c3d020756400154443c006202101003040c0005521b00103e0051410030700c00c0c4500c4c0c894903150002541c0c8440013a110b8100d03010003000c1d4071541c2c1d8004042048641c0030b46400b0360000c00d184007980004081503240d0502034220307139480d0003000b031006080099581c070440d980d00c203440c02c540442902e07012a0030200d04001928100c185a0710424080c00540f0008503981d54250040d81c080c0922414808140032442d86045074111038440030f500c40d0000e000051418002900d05055004038400700e0f03040174070074000c6c50341c0030043d2070444000b40c44003140c50300c8100020740c1c101da101c40d480740c80c10fa816010314060307141500140790b01d203400d803400c50b55151038884040c281c07074222030110b0b02030348010380c42019070780700fa00e10380d9000d409107280030b0800f9110b01003903080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 173433794 1250 173432544 173432549
    0x60901030b0d06090b0c04060507060f110c0105150301020c070e1003060905031e0a0c030e1c05100e01060b0a0f030b06030901022104020307050132071208060906060c0313 75
    0x5035a2013486800700301101800a400041c001c10182c109458144001d0143c414032000504041c2c44d07203e9104481e5042e08a03140302404074100603111031524103201c0c02040e0854918400c9014081c1740c0c1c001d0304040c42200d0498143d040901501170405d0301084940708003400c151b20141141c280003010443d184600c000f1a88a45c000e141c1d9581c64200c1e4454070000c40c5840d180c502d008116115900d5000301c002d448042d49800c010404240500014420780c040130f00300f445403001c410b840c80070440e0108243e0304401100c0001c21000117079214140c208c40b001d0060100d074000030010207032003c2c0506015480071b036641ca00070950148003030200343c440e0004c0e140f41c0941da4001c52808100c10743d05401020b18603040100c5010341ca42a000aa03480405101d0035062101086890000c1c080031081440c1c07408403540714010800d04c81c9200041903001034025a03040362a104001d0010348a22035031341c040d00c001000072141d42c4a81d4200b150703581c40804240c00358032003000300881840084981800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 173435044 1250 173433794 173433803
    0xf10030210020f010216150c080105040908040e07020706021902090a0e030d0606030203010603061403060705030705070b070810080f07060e130e0601140a12030f0905041d010e160302060901030b0d 86
    0x1b40307011500c2c1900c1403045004008404038248000d20300540e0f8010001411140d0403030300400d500b1114201180300d446103410000d42c00104804014030503400041e190300b10f410507421503410015480c2189a100c1101e90002d50103280b10b804a01016620380041c0004034490050320b20708072282c003042084070742c2c507405840800d4000c40100110368051080c0380007025009900c4054154200010b511244010003c00038402c0c0403010031042031290007075030442c2d5030040c001807482c24000e80181801e44100c030564000701e190140411041004030f1030210904014004103d000c1c01c00b01c0075038041c00d21021050f041210140354070541c03002802080340e03001c00980541419410b02034004441ca500500c8540501c00440017000407140b40e00f200c52807107815140a440303d0007201d40441d81040b035a44020ba0103814902984828810300ca4420300c0303050382c403008100f240b031112405034403009811041400c4000b980c0c001c20141c04c040b4018403803500705141c0081c181c40d80c0400075111203600d41e0182c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 173436294 1250 173435044 173435077
    0x1080c100e06070f050f0a02060403121701120203060610051603050c0d090f0503030a020607030f02070614070314060a1205030c0102190e06190c050c030d11060f10030210020f0102 79
    0x400d100717040c400306242c040800040d140b007010f01c0c0c000c16018452840000d1508200400b0340380120b2044020707482e03100082c200c008465a48200c0b85218400d5803c060b40300c5e0048401042062804581e003000009480d1035003810001200c0b44409950008038050301071081c200400070b100001484111164861030311450310f142d00f0100140b008502c0c1e9003211303010f03a00070081d60600a40018000ba40a0190b10300030901f0200142c1800290203000b0000b41440c1c10b11000c000c811200c500801e1040400d9902082034142809080c440c1e40c20944001350000500302e418800011103840f844400c40c0a0f504076450700c6445c00f46d842c00c90b41b01c43c10805c000050006501162a8000b014a100450464005045c002d8032010a2034010f0080044414058140305480401009100310030385c900d40181a18010025101c010b81400628000042e5034010040012580340c3c00901c014010202101c0c42a801802c0d40d003445003045402c1e1030038082d03200320300384090320860900007010140002e00e0902d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 173437544 1250 173436294 173436323
    0x3140c190e0c04030506160908010903080f10030809131107060504020a0f0e0601030504030309020904030f09050604030b1b0705060114040f0c08040206090a03082701020601080c100e0607 82
    0x4800101002d0618425248100420404980d00043d500c0d044591062000058008024151080760282e400302d9a103508081503141456040303941184502805402204556208040d402c2002c04900006100e900140705110300c07410103016140384015108400203500250390180b4100d904150310450b0469140c03030800045040ca8006403000340421034210b62014108001c1b081300c0f08008152904044ea80c40c0060245446604602d10198028103040070500346802d005148283d148038007800300c0d0704a500080c040c28071000300c40c12242c0000c0d00e0542921210000d080000030340c0d1409111900601c002008200144501402416002040f04680c0150f00512050b501e0240700708002900d040d01c200c45035904110300315486a4119646541c548075500040d13250202908007070021a800b0038005641d01034019440b0002035800c03800c654102108004a0341e4071000d00445d00507401c8270500d04010308150100c01d41c40350300c40c244548000264408280c0542019006035005460b56850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 173438794 1250 173437544 173437559
    0x3090c040e0d120c1b030801090c020d0905060a050717030106031401051806030102210603010f180605060a03060504030509010e0a0803121e01271503140c19 69
    0x400096403000000b40120240c0042c014100566240755400a55100c3c15a050b80034801e0310703290500d42c4584e01d58030b6001700c0c1d401c005001e81024000e10315400d29000300c00003070340e00000c0e12000344140d640e6803140700d0341003c0c20b1002e95040741840364180141809203d000814403001c51182c040e00445040d2250f141050040c01e503605c04030302e0303900d05c0031450051006440b91030380121014410407580e09562070b04030200c0d0082c480d01c0c0b1003410100456000340f100d1240b495031503000d0380b003c40003444041154a4194220380c211001d0588404084401078000740072900310740c3d44881c00810400c0c99968a031902d07000d6607002c850490000780001a00403c568000412561410003515201a014104601c25959114000703600d2014203078500040e00890701d0310495800381d21140b0b1226403550350b880d03500c120a40591078200200001c4d13a0144c05280051141d40c45107240e803502205801d14580350843c4610280502c40042e0080d800c03590031940720f0000d405a264240604c25041d14a00140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 173440044 1250 173438794 173438801
    0x11d0105011d0103140f010509071a0c07060f0c0501060f06030f060e01060509040b0d050a0308071701090b040b04090b06030705010305150402030601090815041101020a0201020a0b060d0803090c04 86
    0x2000e541180c0c201490b003244402d12018190307a03101c007000d10344000c003401c5186010707011801c41069600b401e040182591011540f9000c8078400d90882d05400f0702c5842c40d196a0080c0000c0003010361060070104465841420f90451041e03450410250302d4135a40c42e00c03400c0d5112500941010080742e40c04205c030540c94400c03000080c0c0310301020048941400c540c10103205041c4506070401c4004610300500b50307078550110500381c0008080c260103040c1440d10986400803501d080d0081004400061549030190600e01808140180039000583c00d04903d1b03402400003d0019809c00c2d681c810010064031944141c5030400e006060719002442c001080520b451116004681090701f04818000310661f81c2980b003040300000c40307000d80c0303d0b5218001240c0c220b21550040c02e01e0f10801d80e828003840c00c0304408034000c0c0e0148500400100c024030059075288007503500240140c0c800850b07100401e028400503600000010184102c0d100140c0741d00b441c41d08255140c1403241c200c0c3d0035a00d03103468a840b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 173441294 1250 173440044 173440049
    0x3050d11041a07020102120306040e070e160809120307120f0e0712030503011404021303030e0102100c080a09031206080f070503150a2d020702011403130303020f0408011d010501 78
    0x141014076020684e0f0000f500d0f07010b290030340d00c881400480400e00550b629005080600760140480d0015035031800e034035181e88002d5a141006019502505503030600c0340510714420383d0084014030702050540300e840d2099000821405c100000f041102884e03d2450240c1200110117001c081480f0328411882c40c18000a80c0c0031120094504442100094200c010340b030464102c400c220260f00c0800c004640684100d8800720031407695504040704141d001080300c9240341081e42100d002044014a040071943c0e41007041c0e010604040018940003002c1d0041d00701c01d4403d01d0003298401d01c0d40040d50980780306400c070980c9600002004018030340104030344402031034220000c28110b03046d004020126000a8140f001858075000d040c002c101d90004d0010024440c9200e9036030030920306070340000a4024440c102c2c005410010b00244404031141624000d031183d1007118031642e55a40c080d0000e5015040119030305409100004040000384602c446607503041d0080980f400100140508540e8141c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 173442544 1250 173441294 173441339
    0x50703051e100612091a1f0b070206030907080d050a08090106060f0c1109070306140a0e07050706060302090709080601060203040312212a030509030304020d03050d1104 74
    0xc600300000395a03411080c500301e03140c500340f8911304031600e000301c0064164454042c0904041032040d0041014039508a44613a2181007003c6443e088083d511840c04810321034124228000d01001000d403400340d00071a0015203250441341c2240d03031011380a060018041607500456004265100403d030808101039105107014000c00900381040c00c041c0c130381c00c2014001c41c100000306004804100c051042280c090100070054201d625215800070041c180c0c9009400b0007451103107030342e0400c1c24402d42c801c06a981458072030050750745000c0c0441d043c2d00041c40a403207070341e2500d4000016031500d0a00c107019035030315a190900141482000c9190000607804003086510030041040403a0440c00d003001e00500902c0c001031001d82c681541c1942140c40316000d0341c403a00c1d141c55100490009840d501c50011040c1400310035070b808400c02d50440d641103440c6100c1e90401c00001e0014600341c1e105000091103410050b003018483d000d0102200d06007406900503802c0020184045103200f58054600b0206 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 173443794 1250 173442544 173442601
    0x909090c15130303140f03100f0e06090105120106031e0203060106020f071a0d05150405010f0b04031203110304060b091305100e0f16031104060308181305070305 71
    0x2c1c0180309202d80c45110103801c210011401710309070b90081003142c51701e07030a0400d401e0b01e81c1480080c1490100701442040e0040031380010025090400c04403d51180b0001400c2d0304d0281c0c40c00d01071010b61044405031009a5503170701303808000100240c0010400d61440e26854250070307001d1040c145807000c1a00000155800340c8032010700690002440e10a4903403100c070135402c50b10000c2c0030700321074080e03c20035507600f9040004000b040c1e5140d0450031081c0b04100c5e028040d999039408a003140389803500500119400400041c4003203400c0800c05484100b0510740099a145645040200c2d600140d07000ca81c143d46a000d50806440c017500c0c807030f0b00035810300e2003911045072aa4030107684504407460900c1e1325031540202003000405000e10b400000d41d0b54151181c030211404d4426a904003800b045404a810f40c10b1401c2c035007001c0c803504bc1600d034003882e441d00c2c0c84400320352411090b203604c0d419070340301c8003101c0021a200a035000c2c080c002c01c000d450200e501e041400c601040c1c204421140720490700b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 173445044 1250 173443794 173443807
    0x120c0c0f04060b04031101021005092104052110050103080c010606050414091b0a050a17101a0708070c050f01020a0c09110c03070302031e0702031b060909090c15 71
    0xf80c0700c210b80440b035104480b00b9005c203241005038148a00e0000c0300c0311035490902000f01c0080041104841007035006c082c0d0010860b5004241c44c207000c0c50081ca42c03c08044240051a400d5922000148095010448039100100580c01040d00c07001d030011207071280c010034200e040440901a14010304902e091060030301742801d0407240303442c15117074886214511000118181020200d14500c003071503000741c600d80d2000304480240c02648500c0300c03000002c581c003003c07040300c0003c03090a60040001d0040208000d20f005220906180120007190150f0380411042002420b100001c02441b4842c204514203140351000304507824410f01e500070305541003000f48500017180e49175460241c42c2002000100010510304071002802110b105c0b0384a8480000c54105241e0004050700c00c03141482e45a803081e01c400c000038070440c014500001d40591010740c9a41005400c103d54541008000c0c215508102c4200001906a803040d02c0344800ca0300481841c200702e0030020f20400040c81e45030b501c0b501c4d004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 173446294 1250 173445044 173445059
    0x112260702090606130e10080703020f0622120308060d0308061e0301020f0d05070c051002091309200d11040f090b04032a050d0e0102120c0c0f0406 65
    0x204000e0024860204200082d050341c1e901070940d10041031098054280d161240281c07400d00c00d0946a50480080042000a03000000503100703007600da01a001803c00c0101005101e413980046c81034031a1154860183e500c2110210102c200a01e031110114200300307070504024101c2030015086a00481c510441807011079000302c0c0305030f0095010340d4104280380c884201034404170002041c8541c9540002030922002c04014081c0a80c4114940100102d072200d4100395083c11002c0c0303004005030804081b43e088021183d02400c0510005800c0310182044c1d15030b0f030421102c1181c81126403090080020843c00001c60580140c4a4140e419031080301d6161291421400c0c0c0c242200e10550b00d070940c1c0950a0b01d103801c1a450160310210024081c209494090139a41200301060f81d80860b00c030b0604a0001c203191000041340d00708010340a005c0107e20700711102088108a81e040d441110100c424100500c4018900002681c029003c140850003c00ca050704040c21054842c2d41030000030311820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 173447544 1250 173446294 173446297
    0x1203190f0203091e0402120a060b2502030c1503040b0a0b010504031e021206040b0c09060403320106050301050912161b0909060b01021c0c050304030506011226 70
    0x51000c841c136281e0b220050b482184100030b902c000c5034106002042e02a00c1080400d1528001d900210741071000300c0d00c2d400c61400728092020501d03280c7c406060919049402400c2c0b21100c6400941030f9454000318030042007000000e101c031800800000804c010a00141349241c40e00500b02400521a064034000024030500483c00041d003040317941c0901d50009004500300d080481d901600305c480601c88104a182c80d0041220300f82c07828007070240080ca070500f00d8070440d2601c190040465060a003152a800e801404da00c1031040420000c0c070f100c20302488001d020125000c080710021454a0070f1909045c04c1d11400340200c68070b40d000c8440720031108081e0055480058010140d50030940302d070305100f21204040c0c10621000c0001c0c04021905011301d810241e1124042d40c805c8c407840320702e500120382c1c0d03015038201005106200c81c1030004143c4108820688c807402442103a003055100c0c4c8a6500300202030f80440d00e80310003034440700c0802031200c4a03400744080c0c209500d19a40f0034046500900d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 173448794 1250 173447544 173447557
    0x105070e03030418140c1215010c06020307050c150615130e0714070303060609061701030b1b160b01080a03050d020702040e030c010504060b0409020315040c03021203190f0203 77
    0x4240108024100c0700807664040c0c480b8411083c40300305c4034141010703c96542c0d0701402041008440010002d1840c244000d030b00301d903000040c0e4410807012010340751748000750400382c40c1000b0004200624014180300304148403082e00c1480c0300701e42d641002030402c80d01c54980034281c201c03940c060045424400c40a82c00c401114000403124a20350744900d0101d40600b0070345005000381c227020500c40189036041d40518107803000c60710740300c14654482c401901c0701c860207410025a0080d02c0c006000086060800c90b8003c3c0c900b03070880c04020020480020250800c108800c1c405d86103142d86000e01c420908100d0040c101e08014000518990710000c0041c170490001000403078000980500311344460b840001840c2c0c1c076109594071400d54a000502800042e102900e090f0300b0070402c031016141503c50000c0d2643c1c02801402104220b40070015080d000520a0b01e54038403008000015840d5041207214140c84e0901a40d560001c0c078542d00c0000341071900800c1000511501c070700c891900081120003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 173450044 1250 173448794 173448809
    0x5040c050d0906060e010f0303020106060503131202011104030f0b060609100f0e040203040308090606041a130b030718110435010c030209040b030d0e12072102030105070e030304 78
    0x1c89980604100015150607400391710002d04070310000481c0383c0c50b122204142e9110703034000e10040755900340442c0c3da03020503103500e040005030043c024001415002c0e100c0d00036581d8000803487c40358a4003007501b150003903171056138180c40340c04246041050485e80b01d43c0c070441c101c0b4094105040580070400c9007001f102d0440900800d4580f98841500908081c120490018003d5580f0b10f014030b0002d120100640380c010040c45200080380f030341d2400340900b0900083d4401c444500945c98002c100c044581070700807590a80e90b0f856500b901e5142401007901811602074510324a007020440c210440d84524540e03003003086e0a200922220b485500c0010801e007088541e039012944460281d0b0440c03080c4a601c145941c0703801240c03d011a0503030050507142104403010440c941240c1c0606807074a9500c404030001401400d038030075080ca84280c0d518645151706048482c0c40341ca6400211841c414009108201000001030400b145024019242c0c000e0052a1a004969801001c69600d02030741c0034825 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 173451294 1250 173450044 173450051
    0x30408010f06030809060a02030405030111070b1006140a0507060e150c04030203030301061d280501020604050c2e080417130b030727080d02060906040f0c180501050a05040c050d 78
    0x1e007da1007001507034003620004000304050400036041801d03581c40b07110304680441c00f980004010243c06200c0004854054841a0500380440d10001c0c7d540c0c0010001c13024043c0520584000c659140b02d10f02c2d40070045001494280004e0441c5030846200070007014004000300802c0c00107840100035681120315600304044480c0080070a6407001000c0b03c202504590a0040c2602c0c032103d549168014071000d603586411142c440004a031110011240a0038585c801c501d400c6d601d044c041c4452107501c42000650718881d0624260890266200001e48006401d40007070006001c403212004842140e140b03403142c68440c0f0203020b44c0d6035600c00e200c2c02c01d45910200001c0d41490150b40040541c8000c0b0802c12480c0841c030402c00f0410304c850042c0d0b0700c02d100d440301d030524050000881c07a006402c0a40280360305d81d10703607440d212403401c6a402203031400c0000c100040c2010094500000107444e042d00400c41e9810903003842080c00c01541301d84d01c0f5508040c0e19506480d00882241e219254464020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 173452544 1250 173451294 173451307
    0x4050316060207020d05070e060d02011709030403080304080418140a05060a0911030f060d0201140706111c0f0213030b060d020306010e0a0c090f090203190e030408010f0603080906 79
    0x70000b4040c0f903001a401100d9141240b040010105030f05040e190004601c480031749811003171044d102c1300100000e01040d42901080b824114500b0b09a82c0102841d044030b15264895507200c403141c0013500c0450307040c0740c081000e200c16810701c084c0d00142c6203045804c00484c4220316803400031590203800c044a065031369006c03031015100c004401000d4011000280a80a00184050043d910888081000000d550045a00c503e040200071b081c06030144e549185101d40450f40050603400a40c0841d50184d0301c9010781c829160b00c03000f4010801c960340000071048613491608080d904140f0540b82c031148108115516075000509510a60380c00c801c0b1044150b0320302000c901c207d105d8400195252090784000601d001a40050034441c2e02102824401c1132403049056450462901500e4019807a0103400c0c410044158061940320b50181c05d8003401c1031005071444e0440d80f280d014140c5540002409002c1c18200340030703000c00d41500f040f04205461441d103c0c401c05008041d801407150301c000903030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 173453794 1250 173452544 173452553
    0x60e16050901021612300f0201090b0411030c0109150c020102070b0c06041a0106020c040b0102100509030d0e1605010513091a0406050907020a02090601021501151704050316 76
    0x1c0b0b2802c070098401444c8a16201c4400340c00d02102207504a60125080070f40b8041e00201506000d21401403c0c002e5a0701804407805441d0a2075035404002190741c0e4204000c0407405402c00b241c0928001c00000c01100f511005060800701c0d180305481c148019202c0c03c0003c4182e0010310030f04031400b440d04810340b4442e40b00407030418607940d010f200201c00105140c03909650114003140654880ca0641c000c86c07080400310f6001304c1d424401d44003da0400e800304c1da240e087c030741c02c140359401051042d1070088894440302800c8510940d46400103600c0070425207222025403150344400b100b454014407100a800741d000000903594005d440c100f11003c54200c9809650b00b0951018000004040c00f01400c030300a40485101c03c60580340c421402c080d0001802c0c200490f00074050399595005e403e80340015000d0001800029002a0440c861500340c04251010280003a010700150450078210000c00480100411010520044000355240501000500010403a100c11000c0f050b862006d404a080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 173455044 1250 173453794 173453803
    0x50403020301110405031e0601180905010e0a05010c0504050d020f0d050601080a060f0501080a140708030d020c07060806030a06050406140a0c080901180b0606040b0c030409060e1605090102 83
    0x4025050740c2410540120f0301031040141003604c0d4180c0482d124209030800701c0088000c040800003198200c10018400110780c0214420800041d8001045021762603403814211184803000d41e00740d8106040040c01c00c80c003030160400d50456440d00d40e00b01030401002031241400d01344024401c16030241d24100740c0c2c07242411440101c0d041015180b0540c1d440b074885403980d20300c0404450a9107810241700003024103204460507214000014240d0040300e42d12910003115071607082c00d1501c41d68200040200081000b0318040451070005030716202000380c001e1804955030050000c3c000c1d034004003d0f95480010b44590b030795410940c08030300350300c40341421001811858000544030b4160750400c01d0b181d14941040d035120f811592690311a50700c1190550813030b009030f801000c0c0a60450345c00750104581c15010383d0031281c01001280703400c0d40d41194608943c01031089090366000030404000c400350310300c246401411590340d015183d14013060030f84500d050806402d801d002010423040f103030b83d10800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 173456294 1250 173455044 173455049
    0x706050315041b0e0307060f1d090106030603030e060405012114070c05060702010506030c0105070809090103060902150403020105030f091501032a0f0e040f0b0c0901090608190c0504 80
    0x41c0108070340740c030f0022105191540e003407200300400d4070000303200700c0d40c200015950200c0d61160784d58005056291011130702d10354100482d450900138000c00007019511900d26a009058a8800055151079440d021700a0b45800140038400c9005100800680c4d0300b01e00b115441d0400c2180d0348242d4070340d00300c400f4014080b104541400c0c0b200c080c10050f400790040e11091244c0e01500456089a40d00c0404900f6140120b50460301170b00f1101e00c074005540240c001d06038107403161036018108400d403000f1403003814090740250b40f003a454141c0070041d07017418003603004558400072240f0301d80b60950300048e00502c000350030102c01d10b800c000000c0c0c0022301030240802140400c04621180d5940e41800c1103c80001c400c00203c0b900c0d205161501d811074101400e0480328a43c55a4540506c1e181e411042c0c498001c4c01a0781d5488a18031440004003241701c22031141c2826005162038036544000148005819040078040c0003111044c04184070005032f0729201c003000b003403011801441e490b070102d4407405180e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 173457544 1250 173456294 173456299
    0xc0c0102030405012c070303081b16060c0c0f02010e06090409030e010315120b18060c0d1505010c0210030e0f060f130201080109020a0e060a0f020105060406080706050315 75
    0x8002e0104101040d0801c600c003614050000b03007502c82410764a0110100d441145140d503000040400000c0d000b52921170344480c1981c04004030010000d810000ca40c0040c484910349890171009000700202031054200846583c80c0060049846a48040c028515064040c1c1804039400045480e43e5541d802c5900203e0b01400600ca0140c0e50310300584103c0a21100c0c60101741800d222080c49925000704c04111a000d4000300f108031200d4440f80150500074092403080310801480c40c200900c200503050140182c02d801c2d0ba540e0071101d41401c200c440d8400f00504010440c041000540e070b104120086454044840c210b052405040c180c00905603020640b02030300695030340d10341014003c60514810200701900c1c40c1c4c00d50f41d8144450039400c0e1007074020b01060201c80144440030580d400b90141424a05140b00c0c090740c10400204540c00c900440e4001070703515010071070103581c207004e52504100e055509200c0b65007040c002d2521075489008070301c01c00c20044001500c07011007000c07032020740602 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 173458794 1250 173457544 173457547
    0xf07050118030c0c0801110403060b04090b01080625080601031a03070b0705060f1312030b06040f031109062b06020409020421080720040f02030a060b090a05090c0c0102 74
    0x51074040e04030030382c03050f099980c9030806070002032052041c0104060000701c9150913103005d0465840c1002840c100c1616074101d9500e1030b4480001d01e0400e8424040d00b815002452549065007408004201d28100942e11790020241321031116004149981c01c54801d0078041114901c410103144056010710f0340307540c1341c410f403c00020300d0300824008004060145003a1001c9a50300b6032810f001c04400d0b242c1000003040c5495a1003c104c445040f070b140090f41d807402040b0700400c1c1e800140b0b0340e04280c01240c1900c00c120410010032803844204108028242d46c403948c6031900000040d94105c0326031a00c220170300388201d52003000004020640030158008805c40d110f40d15504080c00940060140c080c04119241c901c00c8051041c00080d10202e82c06080c043ca4000981d440c40e00e003111400049008440e120129803681d69140140c62074402032000040c0c0341c0c50030030070001c10b59440da4420941c81d20200002c04d065224800f120701550400c1e03404e5001a1904022804a4441ca04030210325510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 173460044 1250 173458794 173458841
    0xc040303172805091603050c01051b010e03030a0b010206190f0605060309030405010201050721110708071101020d17180307020d0510060902042610061e0902030c0f070501 75
    0x16030340014000c000401c2295404000e05148090302052408003070605d234080f41c450520307584103070300400441000b0300c0d85201503054143c4950035a40300e10f0804203244c001004004103103a10b8440c40d400c0d04c1c0244010700c21802c142d29174400200d00c2c0b50030b0a40382c648403101242c004030207401440040c02c019264507500d1400c0b00501c3e84a80045c081c0c18015401c020210b000700d03115404218200030010450080700e000b0703828420040c400401d642c00c04c0d400030700581e030214001401a0612901448400703041684c2c02000a080c16544581c280c01d206040041004400340e10720001d50000c600812a00b4810301352003003a02e10b0040e40002580203c003042480c0801c1008500305040c002c03404010300c0410f80303801d85401a806180a01c51054102030180c040701c041040da840440c1400c0c20036907120405040c00f100646031070b81c1211840442048113181c0b42c2d58000c15603002001484401c5055040411204031075108420b88000e00190220320746003800401c0d88060000901c1d20340404e03030400b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 173461294 1250 173460044 173460121
    0xf0a0e0f0f0111040b041e030b0109021b0613080903011407091a1e070303091e03020c03030a0c020d03020c0301060e090624150f0a090e0c04030317 65
    0xa50750348050103039403c0810030f00003a004081607030107455603a10030b5420301e0305252200c02c0112591844010840040342c0c0000810760b0b09001d40c0c00382402d55005a9902c2d680c076203c1c80303082030600b188070b1254004001c02010400c901a82c40101ea400711202340d036060900006070242503800c2000c0750700d00c44042801102074000e007025045840500320081000c0d10f0080130000ba0207038510981d100780d6265019182c03440030600900c2103d02c40d080009035050141c887c08004645000040d00200d40c252865050640400c0103808800d0300314010b5140041c0702c82e00405404000c540207000d648551624410503009001a110182c0c02800822601e81e98441112035904291840b2110740110f02c0412580308418410821070142443d44442011107101408810700e19680c0790682c142c02409080c14911142000340b5031b91081e60758485007a400d202e1010745003400941810075401c4100030401c00a03070000391845003400b01000b88046580c1d0300c0c0d00310429042e41800b103c0e6a004c0c0341098121031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 173462544 1250 173461294 173461303
    0x50d02150106020106030209010b210a020c0709110904020307170a090c12050618030d110c01050601050c19030309080309210406051903061508040303180b0f0a0e0f 72
    0x49440a840c08016641c44005030300300d44280c08041d403c810b07650018460707510703c1c00003403c448072400c03541c1c0c2001c060320544443e4400e040e1208041c0c56000515050710460402c4044080c00300c9140412016032442e0800d0350b544240006d060041e900400000c1849003d8402a0754032000203030789240615000311042c0050420f4001129440a51036001c10759044401c3d6036443c1c0da40c451700410145e00c0d0210044003030004960324030080d10081140c1c22681015004400d9080c011101c015118090b04600c01d080d00d40003840a81044020f2154110814001521171001e01080034081c180c0c403035a040031000303070800010203440428004180040080001480603141226480c411508000311b40741c0a1541b045d40b007080005181881482800c814641d41070324096072501380003d45540d1420903c10b01e1051001d5100810740840801080c1038160040301034070800c00c10061f6207070b001513803524180d40c000b4041c03041c0030800d4400284285001d038400a99103410701c089071400c2200c0300001c1c4c0d44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 173463794 1250 173462544 173462563
    0x819021f0323060d030e190602010504050f010c02120711041103060f06090102030d1806050405030a020c010306050105031f1a07030e10020a0b130b01061116050a090f09050d02 77
    0x448511899601c0701c2c00d900c58050280030010404001a400d03518101d4034000c1d110030283d40f220498003078601d250fa900105000a110360f40010a807880c150801c1c43c00c0041015104100307074184408401d46135804180c000e5a00c94080b07200d500c5407218103040300c8040d403001c8400c0d00146050344e4009004015400745125913412122094400b00504c1400414021501c0803409640244500461688140c2000b050b2641854201034041059102c02c82501c0d01a00d048d01c860b040000c0542c0300d69418004007130145800e007828400039141ca00002c000d884010580010403403030b1043c4000c0000100d2801004045440c402a80729050500c41038840e84254800c6011490314280c0c03a5003030401c1c58042d0304c0c8483e59009007052041c6c079254550015002003444d05000802c1d15204c0008040c0110180030b8285942c50400074940e003103107a0320f00402403d2203045106240e03820000ea80d1040c041e50181d4842d0b16012810300b2620117602c0c040c003000c81c0001c002c0d0040e60090084640e00007080d42c617 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 173465044 1250 173463794 173463821
    0x306290a110712143c0a030e1005030103150b040f06060f17010f0e0c0c07140a080a051b03010f0212040b0115140a0908010c091703040819021f03 64
    0x501240c924513265030344668012801408008401403002c0c10212400c8070204440140a030003844ca0790f00b0f03450501207103050803000b007601c0ca46801c21394101000d411108150791304210303196506585445a51680c0d44012507504c584480345c0b00910349540d00803070317107541d40c03418140007031600c0b001d0240a982c2c08140c40c030001180910030074500361070040120304a410003510300310b23410305102c5101c1d403500008200102c040400c01c160940d03040300300300c001e005010404590300200811401c20000c0900c584c084411640040c0b0b001001c18008a200c60300c44c8201d01e80252596042004a8094100c180c80b101b889840443c030504903400703100c40c041c070a502c1917001d5003c0fa070b21500980e200c0c41030410300b44001026100010342401c00d072802003218007420705024120320b68030a09682900c00b841036160010b04640000c022080603201c0c440c507080b8841001d9400c050034186c00c95669903525030321500c806c88020045083d9120f0703d800d5105d0384010038105040c03480314203014000d000d00f1490071030b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 173466294 1250 173465044 173465063
    0x2102102708040e0f010605030c1b2a0a03110f1503090c010210050405030a080603070b0c0105060f1206010b0a03090c0b0705010e0616051e030106020d02150402010503040602090a05030106150306290a110712 90
    0x1203585001d400c40010b0702c0d8030002100c40c00c0b0301000fc1c4800320802c0c03041caa802130417859140b1022600c2501861003140280000e001c40342d001d200081c24041c01e1090320305a14140000e1000051001c810f5031003184c4c484c03510311400e940d420006490080f4540c0b00451039900041c21707500824040d04000e00c07805043c2c840640005641c0c092040100d00e01e040340c81250840c900622a451412004114403821440d0218142481c0d481e240790001141c2c2c05090340110000d886401c0103020300410b1005c00c3d646020f01180c0c0791681054030b400c00c503d0008400c201c8000741203442480d00406c3d4401582034900b840d6101c0d0b846440196403220981c010304094400c2c00b21071460180300e40c00c038600c12a4103a4400303056494980da00d5000e9000703c5403003603200480541c04105501c1c24494038004144104d10070042e54001200a012604944c220340c9258085040c0000c2c090640c816808010300c28186007a82c687d44100205c60040d03a0019a48290182c2c000c00680f105904020902440c003502000c0e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 173467544 1250 173466294 173466373
    0x405071205160906050a03021c0501030201020c0d11010c0201110a06050712150b030c070501090c0512010b0303160507212102102708040e0f010605030c1b 68
    0x1502c0140c0d00d4100c01001a90703000341808028030440c0a40106c3c9a5400d001d820941030314040410013000f1070950201e50364400040040d0369040000c01c0c040803040d90701c10091015502d640e41141c03410700700c240c14002c86451210840e40700d500c4007044060074400303032075050304a840e141c2d026100c252031210004010340c01d0010401c41d03610542c000081030000b101ea5181c60064108d0380c64100401c400c3e1210300601004010800a005441865100d24ac02200440c104404c111240000c0300140c05c0e941e240510215850710004200e5205290f2181907203440415450014a0038500c2d410103c001008183c1c442420400070500e104800d00c40c1034041c0b040c2013400303d1840c1c0c174800074030650016804031056000e000501d60040643c0d8252403541c180710000100d606c000d003800108201c83e16200000e0401c00d040d40321880036080200040b0000181d494603100401c2c500010703014103e03a0b1400141003041d2075504102000795074161003a2844d10982400c00038071600d4441d100d81d000b0000b081711 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 173468794 1250 173467544 173467561
    0x301091d030d090206040308120901061406090405060d050a05060114040e0606010c0201050d0c2f06240901090903030f0e0d030908090402070c030312091a04110405071205 75
    0x20319403031585580045041000044400d40038000a02050341c0180c1d0400c4044081101c1800800003a500180c03e4141420140c90f26401c413161a4404658808290380310741c0c20341e54034021035a40c094225400b0400d0348130300300054484508010300401901c40d8000c60720800c040403c03607034100e84000c2006038840c0c00400900090714a0502000641e40001c3c0020b8141d6004030085503099006241160810000c3c3d5850b10445141c404804007048903a480500180598031402c08201425881808407044480b22181e841d500942b000300c0d00c03110320011000c1242081c1201400742c5c00200781c00d04559507036034080c0c014101000b041d80083d003002c501140000c40ea01400c07424502c51001040640700c114801c900400303081a0844a0b00e100304607031041c40d41c40740080e14105e4000c502826002d403540c40c024027040f10210161085500700380816001c900039040121440c441040c0e800503d42d194500079042c0708004008a500600d01002d112000e5404640c80c002100184c108220545071000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 173470044 1250 173468794 173468831
    0x40f030311012c0d0305060f101202040f0812070809010c0f0606031104200a0f02010b0933090610050c060403120612080901030c090e0412090603024803030109 70
    0x24141c0d0025040c100231241400c224036007088080c01807070314806120b0102d5854090303900c56804103504980d800400c0c080340c1800d10609803003040c1020490311b4000b0958800c0e1440c060910042e040c840045c558000344140b0403041c4400ca036100e4001c01001d500d9107407200c4400e0b40c1140ac14011403501c5407941078855042d00400e1114007960b4490b0500105850440d4212400040c8030119502c170525900700e52283c1e8a4580911040303025240155800c10510f80607880581d100c0c2051169400340c190f450301c4107031101e60400e60540c1d5041d11160144d0b82903449100300076101e03c481c85403404000034540c3c05a11201c0209480307605000703150750b460002500e05126203000d020380c0000c001c01c074810341c081c2d8000c91195070141040c414030741d9600d908041101040354180c47c44e2948004a8a03c2640410741c10060840d5007411410720f100030b0528004601c1d441c002c85404584000020049003c0450500d05101c412b00c02540800a034402d6548a0304284242140e142c02c1005080e010f804802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 173471294 1250 173470044 173470051
    0x6080a0201210b03010501030f020102060906043f09050a1a0d0b030c03030a02010c0909050708060904031803051c141c0b0904030c17040f030311012c0d0305 69
    0x252200005a00c10403000412180c1441c541d0b56240d5a403201002e68500380241402540900c00c414541845400060b0400f04020325402c4550001c00801c800207203a6a400b405400c06122080d000580b0980c024030a101c0c000d00c0c061041c014540c4056102ea8018000800d460064580002032941d4104006c4d2017004200404460281071048881d882c110703500c81101580010100c0c0c203441320580101e41903034400c0c0c0f9102e00603510313074000144503904074240740c0c000e00072180c08010603d4984802807075420090800743c0301c4c024640c080f8091500c1800056a070048100d45109501d03924540207035600c607000e0740113880f020084030700140c0d14026030241c0e000305000c526180c0741215290004041e410242071401e00300381d4801820030030382c0720300e0b00749031280f8802c0e01c0343c8680004504000070300704401c12140390040d90400c41406040540b24401044a0781070a00d003401d4140c031040a40075040303880314200da80d40c600a409825114940310180501240d1003a2803200368280b400710281d40045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 173472544 1250 173471294 173471297
    0x6070e030609030d320a062108070606030c1205100501081c020a080d020405040b04051504020c0c0306040615140d120c0f110a0e19180c1806080a0201 66
    0x5002c4641400c049070002160100c58042c20700e170308143e80c000561102c01007861010502001c1c001c00c0303c0c5410920412025104044005c4142c001800140d802e01d0700d0750320020f0a01e6804141081007111580100016683c000001020141c44001c05040188609010344007442114001c0820540c0c52094506903021400600145280081640c1c0280f00c0b030b28128007103104e202d4140000c110814040d1201e240d85041c0503031303624644010001540e0b00415464462490401880715001c9408c00051140c0c0d0b00b55805a141c00c060880c95040880c070f070341015014041c1718100800c004069001a41c2201d0880f1806c001030740f9a50000d44a9003812041900015140f030a4408115a218400c0e0035610610f4692072810722581c6e00c80344c200e1901c6049030111304035095010203143c924048809440d14010310344503803a0146103881410030307501d500001c0541d21f4403071414441031840d107040950f411000440031540e0340c08001070012005800308211501d041404140e80c0000302c0c480a4440c0c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 173473794 1250 173472544 173472547
    0x31e1204020906031e031c0c02070501030e0a0507120b10150302031909030306060906052104031b03020d0f080601120b1212070203160302060f0f0d050906070e03060903 74
    0x3140c0c01e020320040701501103503140c0702d24902641d0308003a8250120710ba240c41e1010703580321031440c031040c4042030504564040f203c0c01c00d4443d070001640083c60004480d0240780108042c00004049400d001406901400501074084003288482601880170349852107100c950b1281d560700c0c0d40c0580c10340220301603c043d54043c45d0b8406070f401c3c426000703140c01c4418200c4c40e00340348060941081c200c0380740030b100310082902c2c2c10041104c1904021000c00030071413420034a20701020101c040c0d00800341c80701c103c0c2c0052941400308043c140308100440651400340c0b03000e0000c24007070402035941c0c0c40181c00c107800510b140121000e6540300d00d0001e8022801070f11040d10101099400d400500014034440f40c122000320358801d00c4240c01c209018140e005d0130f40f029900d800c20f00500d03060404140800c0b07040d821940301040161143d10454840c191404211030f1241c0c6201142e005600c0741000c07500b00f2a04000510808803070200d58180a000140c40b540040001070040c140c403540c0072251450942c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 173475044 1250 173473794 173473801
    0x100b270c070602120f09100204080703140c0607030512090a02010c021e190f05090403090b030c040b1305090f0f061e130204210203030706020f0706060305031e12 71
    0x6444081d20741c552103008007504141d65041041300200c8103c850316040b406820a04c48000e030140900704410410b42c1c415403400342015809580d031100d41c8402081c8101c49044614013400c10701590024510007001c1d144c0d11f0500303080040081d00860110100300e09007402098000c0400100d1810003541a1600050011a6000c00c50300c0303281807004452895410121074030319540c040c001c032070502072031a1603400c40307042c440840582a1b050b0800ba0043c0e020a0501003c02e0300200d0300c4045800c1c1c07144483e03603075880c4010030354180941c2d40f04035210000880c09202911521000a054a6064508030300a95034800c130603c0e940340950310840045c00500c0481c84609200c90503144045442044203d40301c000070128410103240303009120000c1d4041820700210240f02030b8010202000068803003640d90130340010341c503441a240d004012640c0011103d0a2421182c03d8590068004100f0807210356241006030f00e07a80a40b00380203841c0034031411030807072052842c16603020381241d40340f4504564 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 173476294 1250 173475044 173475061
    0x70e070c08130312090509010b07080703021204080109031e080c0a111207060b03120307030f0603060e0a030207060908100e03090904060c020c01030e061306060503100b27 75
    0x580003005960042081102d00c80c540701481030440114481d01114560340540c01d001400d90969411032440f41d0286001040100882c0007034800b1190040031641d541d2009180c140c1c41c0203400d1030801e00443d004034000a02100c19401800e806002c7d456a19050120707074071000702e4280421050000c00c8540010407492886c520282000340042d041c406081024020010328102140d59420036454001815a00f0000c050040d092012402c5d002450b010200ba81d80c02004d020060000040550b254a40e000d400001c2d0401c000840c0c10403400c02440c130303107010758907140c0e1000181600544984400001c1540c4980c0041301255481e401404100d15503072000c9016001c4100009814803080c4440c04607965a2140280190700c079000000f000780955501a06004e8505c003418141407030424280f51840c00414031942c072104001c2c0c61824a206464540005e0440340c0006405100303003106c0781041c203016400340000020440d541e090038171041c84240206800114502e06410000000c00c2e00203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 173477544 1250 173476294 173476307
    0x50720030d1d1816021212091c08090f0f0c0f04061d04060b01030c09050d050a14010c080c09060909040f082109010902010912030306090f021b070e07 66
    0x40c0b1002050b855820514400643c010329403a40100904488806002c1e40e045254041e641d4506280064414440b046102078460f0042d008040c8201c54079000003040103800f40940d40c192124116011001d84080303030020202002120003420341d114040c05c1114485000503001002c000300401000d000d100d101c2406040322207201000c2c1c1050320781c03201080c17a281c61401803024113919480744185240078140241075445c101c07503060515152203402c04a4651049030b03407050359026140c11180c1545498500d1806803c903e0140180801914559008006403c41304e42e029055903401c400d900c60725044003445c424182c0b090384c03242c41000b00032400e05000325426403203405450014000081910380520030b5000c104069a0309a480c2c0030501420409008641c00120354002005070000503030029218000364001c07501544040559002058031940104018240d4124280b204002d1240764034042e4000c845204070680121011b030303001c8400015a4802c5841c0444210400d803901001070f10b06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 173478794 1250 173477544 173477567
    0x60a06050711060304060b0a09111215030d050a03060e130303110f040e1b0c0c090c07050106080105060306090a08090d02042714070f030b0603030415050720030d 71
    0x100d000b05105502070341e0702e41c400b079881540513500100d0348403128001c11494030103603003209101615092512500114400c00d660618001c12034280a80c0c84807402c4206a005100750310350b25104650341c01156a81c400003801071a540c584043c40515203541a000c134504044550a603010794204295020a110340c00004032a83c3c202d00c454a010b16000030740d2100d03806604049440c0c0c2d5542c081c00a5088802009124504031400c55030a000d0b03040c1c50a5151001c5204047c4210f0300c1c01c022480b000d420b18201e41d2000e502100800c007150740ca0711658040c0908079102d511034040c00c000680200d801044032842036502240c15450205050704003c0c410107250000d0f40c004c0e5071140000c01000511401209403120b054143d0f2034501d02d440e0016003003280030401045500508010021340c0040042642904d61001a155644d075912021074510b00a5a00590024000d100484001500b020051680074002c075101a0803015040c4030204550070600929015400a410155000d1044401845 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 173480044 1250 173478794 173478803
    0x30e0312070c0203060103030503070215220314120f070c05030a180b03010305030d0c0207050a0506180301110403030e0105090a0509370e0613150e030406030b18060a060507 76
    0xa06441035004a450711170240c0044000c86d10000501000540420507030280c24243c0c01c020002b45800c0e84215015072050402c8110003402c440403200701801200d04000d0041c15024164661020000036a029241980d02002c2000c42e800494011307840340304c03403142c3d080c2c001005514019001408840004111146424144000d240801d013036104000035402140100e00554a501c0044800e4044441c4985c4d030f2006d65021000400140d101c2005c01800c540c0100c55550302e0300c0d03c008000801c0d080005009605500c7e1245424080440318080e1003034902a0340c030412902c02034001074802c0c0c4190030b5401e81c00b2911010400051502c0d214a0382d101c40780040411001001c1c108460b86d02c040580303000580e0242c0d000070324110b441c43c8101c1c003020120324010401c5007002242c80c00481c00c80240600718900001c5541c0c0b80301c1d1290040034004c1c000008403980c075076607204005d00512001d03018034030544000855407281190b0400d101d0040f0001040030b59007624002e0f041d0b404e070384031050455 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 173481294 1250 173480044 173480057
    0x50408072411030403020f0c01230706020a020304081b030601260105090105062d0405090f060709140409020a051908070315060e0f040f0201030b041a10030e031207 72
    0x41000424003840c2d0080007025001d6499080a140c0641081c0503c1e1500d4220341c403108070402e041e030b032003801d40140300460345105028080006152140c1d104001014050034000500b9000080d40003009108494401d010341d80e0500e04010124220100d0224050707165010320700520000041040044101c401d01d2f07040800003062135042401e540040b1070703921715031350b40e40700b0811141450841c211124042c604207200d04d801580d40803030142804046580525511000121103400130405101c4514884040b142e5a10345407000800400c07042c0510907100500403102907a034140340c0a100200381e4014000c003411130030f0500740f05851306080e0b442c1d20000d07604800080c428900740401c00145026840f155a91441d444e090b00035542540c1c84552038140450030410003244c2c0310b8440b5003081d07100b21480b80080150004a020300a44c94000360b00ca4600105060968988005004804010349030103880c4241c850081e411070b0851445075a2a07001044034051031100704945943c884c0c0a410b203075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 173482544 1250 173481294 173481353
    0x807052b050a030801090e0a1b120b010f050f060a0f1413030203010e0705031b130c1101060f08071404090c0e0906010f050a0312031b0903020405060405040807 70
    0x4540c10a4204162a03a030094440c600505900c00340e45409000c0c0358105124000c200c00c2020340c1c400c09a80b014011440002c100d1000805621181c8000c06090940102c40c007140c1c20082001d110078031410340a50840c0800092034142a80b1141007642c00800c04c500700141c560f019103501103140c1140c800c200301c222921440ca24035801900440e442c07518010426811403040c5401c4807419080e80040d07030f2019004000781d0350000f40d82c14021075802d240c0c85480000d440443c09d03000d602103617940c0e03082c2881c000d195029400300e1090b0118190100a000341c680c0ca080980b01c195117802001069005402c05000c803640b6090f603541c24a002030030014032501c2985500c083c4560541000009441942c10701c0040407007040f40a0160240340e081100003450a40000ca140d641c0d4800104040000c0180c18100c038081da100c2e144544440d01030384054065048014040300c428002244280d141102180c054141031245134803031640035400503c1c00e041c41d15010b410300790038042c0c0c41c04402840c400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 173483794 1250 173482544 173482609
    0xf050d060807120c090b0303070f0f05010609240303020606060c0a0602041203080108031c0504141c030c081005040b0310020f03160503040308061c08131d01080705 72
    0x12000100000c6203910b9000c00d4a00c1e0004d58284940d00013200c482c100102c146441d41c02004417100076501841e510060300c030170303d0890248807403158060100d51074010300140d07054040e0003050b00041800031103c00c10405004c2200c030066140400780059000d48001211402c2c0b000040076030309445003c855000380c650f581c50060303a0246e000303800b80340e07101940c02e010160041804c60242c0717020005542440141000a00c4030b09202e0041c102080c1c071007011a05101d040c08890000c090030f0000d0b29001c803088244060903140b101400000245000e207003a00d540d200d103070350601840340510159044c80c90001008060402e0004c01036041c041e2280c441d240c10703400d00c010040e030000b003208552039252103c0001c90b0344010103031703060501104208110000c0d922040641d4080340440d2025404249005034000e69003a8150003000302d48000b034610680f480740c145d118101d4075001410312441c9410b4089102d208000c0c4103880307065001c04000d00c82450600c03d820550500300844000841a41a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 173485044 1250 173483794 173483803
    0x105010e06130f0911160b06180f060108070c110f03120301060903021302120406110d140f07030608070e040302010f1d0705220207050307080a05040602010e060402010f050d0608 78
    0x4925405141e0318030130404d0690ba4090741c0e83c0389004000d00d90902c610895035048400c240c84000b44149a000002481951046a800601076444948441b145081554110300401c15160305002c02c111a0028181500c10fa05540002da8001600b001050452081c803600c9104840069810300030800303048400400040518001c24913507442100c51303403035801030003120134840142060707541c01001014a07025440350402d4000c0d500c4500012002603106490005014400e00ca001440c01c2c40c2c82d242505a00e100500c0c00307699400c9490754203848000040c0e044480503c26244c15070030491f81001110505001075a105000c2e00010560803500c814003001c4071202110200e813484400a80701e03840030300b04890302c06403505445c4440f001c0e00540340d1490501d042e2003080e58150300010540e0810200b44162001f590340714400075128564450068810b80050281000540c0381488100070080000b410b68065601030b140c088140102900844941d44194001c042040c0c68010010b0100350030003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 173486294 1250 173485044 173485049
    0x90f0b04050915091311031606080405010f020c030405010e03010b032109210f0d0503060f010201060f1706220b09160f1e051f1b0803010306051e0105010e0613 70
    0xc01e0005d1110300c41c640508021141000e0900a602c00c00d8802c00090003403203048190303119403c2001d0665200d2030280e0140008025940c000d500100d0b41c0308103900300002400544100b625480400070b0008149400c0790b01d1524002d5055004070040018880b0324440300c8041d18000c0303212072030601405c010559000c0310080c20f1034013500ca07001303024501c04248815218280c0040c01361a06803914003009286020140055208074000ca00c900d010340e000350701000003010f0411101c40390a523207650307401040b008010328041c02e000310000112110403840da010b5448001d80e03800340700340c601c0f500c41000c1d100d00180003041034030030b01c1012444503000c0e01e200e000500665459100d40790a1026907094440e5528086455501c400030a0110307a80d2490400c0c5e5544007a0650810025841022520000002544519401c12194401c02d1181100096060328001c102c04d00a5450b07002c58082c080e100d14910080d5400c00f8001845190310134194003440d9540101881d0074400b80f40e091514807100c66 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 173487544 1250 173486294 173486311
    0x906120106090501080a09020102060c030601020703240c0224041e050f070f06090b0d1517070b03040206070609020301060504020c030706060501020319030f021315090f0b0405091509 80
    0x10003c020395a400711501394001c00b48101400300c4241580080c0d0f40d2a00589110b10005010001580c2640b08010403070007141c209030008140045c1d56003110300d02d025071220900560418480103100307400014103007400340fa00d0345450042006446150703003111000c0c1007140c20143d480402e0b10310381010302451211a0052025111124503248100c1c0f0344141e551100000c54840c96081001c8c5401c004c0c40000c49081d5480c0360b582d85c40100c07000c801080441c001e1b21400a0311b05000c00e0390122203940080c100401c0049514150700e4052904107800304880080d0301100400c580400540e4603040a50314510150000c6906034a800009060760032804c3c1a080640c40415250f0600c01d507030195a004000a0000c0c40c0b4050014500030798030031443c409035060546a46c00c0101803103c640c1191010f44034000d010040544980c58440000442d182c400001095483c01180441c64441514212a1601482403805281c44144410074030300500380d1459000b0001580c4458640303c03080c41c07190126 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 173488794 1250 173487544 173487557
    0x607080115020a1406190b0a050424030f2a05040b120d030e24070507050c090a0504060506010e10030b01090f0e0405101104050d081c0506031e0303040303020906120106 74
    0x34400c0300751b80386070600303a20200740d003007880c040e059440c0c040080044da84295800700c0c0d8000744204030881d80001c45900307011403070054000014000744c8140004101d02c64003a8600340d00301d14010100d01c2d02d040b0090030588074140020019881e00d64444c5258a0001c2d2800001d280d40060b0b4a0804041000743d0f00420744925500048400600800700c400710400c0130104140041000c651600c40d004040da820700030002026014010104803a541c000e00c0180390700d0541c5000080b03400504802c0d03900720f80c10b80c1801c01280740766000c1c0b0311440341c5220103030141d81c3d04980b41da8120040c005c08040705052120400380403804059402540d03011700181251500c007410315107007841c580000702034010384040c502801c1040440c1e080b4100c904446003140c0d030f103542c0200c500b0401c025100e103200c640b5008400c0d03020f4080700b508a4000910503d02142a40d4200034905c0c2140f840105c03c842086207a001000084d0019001e5400350010740340c041c0c102e0341010703040941c460052900380c1019012400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 173490044 1250 173488794 173488801
    0x31508030406110118030305040510020c0c1c050606090a06050a0b0c0d050301060c060b0103020c060f091207020d120302040302060409050a0b060412030809161707080607080115020a1406 82
    0x100201c80140c40c203c3c0c50b000300310011042e8a4030710038061441e001400c050b00d40340454140f000410641c2d82d22404520215074604412a9160f517039498400703487d010b200c13038001c03992000340b040c00c0801069401c18041d200b95520001000311200c2c0c01080c0071010390f0344d483c0200b659115030345640c000d17240d943d003416510b0140c071028074a810003e2003079100300b1100f000103000311580810f6410500e54020000304900c82c1010068000e4004c240d1100d00500c04d100c1000303d643e40444145d4042c0d0f8030001500c60b1040040c1050000c5d205d00d0f0000781d00441c01c42c9187d000503140710343c403c02c10354842c64014203040c0c80342d001540355130082e4040301d40c035501c51051064010032445140e20134541207802d1850989000711982c1c0e0241d140300c020f0305015140c0c0004008000512110913800148034010000c251152803600d20020003540d00030303541c4116800400c41c0c100010740715000358070580318609140c0c68018814058036405000c1c04c214056041024001030000850103025191f030b001a0040f0714 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 173491294 1250 173490044 173490047
    0x9090c0503013e0d0504060b040509060c09010c020409050703050609060f070e09040c1703040f08010903051608070203060f01050108090c06030c0a090305030f03071209050715031508030406 83
    0x50b403049500d08075031014290101c5800c0303081e02800d0050700756241008001e00c40540150709008104d810710460f41820204010042c4541c4505c81d032000480d810031103034480d810240d85c0c4000413550b405a500080001c408191700480042c21554030080c00400c540c00181d481a0170a070f20b541c41120180c7c400f000707200040100b4025103511216003007581e00c82d850720250050454608820300c42c018202407006c24280300ba2403030024058900c190890b01d00766120044140d0380e80c00341c400c0030400c0c11034503c0401c12840c18002c805020f50160341c1d0604000e102c01421703180c403400100895010808014101c016101032044602c107901b0055002080d6140500241c84001d004120f495260804d0301543d80541e1110103136a0001d003030303130761554681c60019000d4921100c6904040c05c0b0340b0021800d03030f00b074403c02ca00462003043c07150344411101e41d200d03401006564541c00000c0854001100900940c64100c040035150302161501040f420840d9424046990650700700f86542d4000240502103107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 173492544 1250 173491294 173491301
    0xf01061517092e0c02030c010b030304050f060c0f0109060204031208041a09030912010e011113051302160b04020a06050f03010e07090e1501081e04060905010609090c050301 76
    0x8220320720949024580190b00c1030301c8200d1040d0500c1500c0c00103820300440300e00c24084901c0d0201080b400c0210603032442d4040d40d00d400c640344107250741d030a180784407c8604001c4151740072207401520840f54a07840400300001030b008054000d40912512140521000003400362900c494000c0c080180d0f541d0640c14a980c1c9030343e45071400804d000303a600a1100207030303c05083c10b0360510512410029615070000e61800c5101c0c41409541c0000034003c240c40e031000c103522540084000e18020054620703000d50410380f030b000d0342903102c40070508108200180e09103045c54407071360745060b04018507264500050708504d6160343c0045e28401150400c0000b1030500e5007035a0083c0c06c0f20b0804c1400c0507090400e144d0503110500800c0200e640d0040410b4050f801507600c2400b50010910030203c5180401d08040e8060500882e1400100781c0804282e00e50048141c0c039550180c0c061740f1002d0f640d69a150306002d044d55090481e0159655900020200618480c2030000d51083e506400e1003071400c0101400d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 173493794 1250 173492544 173492567
    0x70b0c04051302070807022e18050409050312090102090d0b06130506060a03110c0d0f020106051009030b1008060907140906030d080a090b070801030210080601140c0f010615 76
    0x40b54410030280000c0355807181075600a9604030360452800c0c007400c210044119910000050303600072041414113460300245002003c01c440842940a0740c4d907141000140c550781e8030301411542080000021442e4440200c1783e000090310009840e005106010441c0c803030040c0b20540c0c14020301c070140000d925022005200c643c030510824440d034205100080c81c1841200c11203818550345040b41000d00c045902a01d10142816041d42e4400e00002c1000e040c010310003c0b490019440c1800110f032514007074442c0b03c1710824940d64242414116590649102d901801c81c2c0080c128071400003654600c1042081d108101c550080e1030030340d2501001c01100943d0380714151081c0c1a1004011964400042004c90f0461700d20b001e160030b46651a104004043d132031400b42c83c12040408001c610303500030144074100ca109403101081c2621201c0c04880c41c4105503035023400200c298501d1640c04011101030300e01015408195441c1744130020b522801c41d4180d5019595007401c0311040703090580c202401880 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 173495044 1250 173493794 173493829
    0xc010903020105030610020f030d140c030f010902090f041506140f07020f120d02010b0108130b0a0522050a1a01030507090515180a2706020c03070b0c0405 68
    0x2502400c5600103000382c000201102e000e152000e0701d11102610030070620a2034400b50040e039950705003103051303940505004495800e0120011010070711500d103110440703200c0d8492009254003a402c2c1070140300a940700c5413480e54015541c0d00b90141c1903540e03101da40380341100841604040c900d03120000d0300b0300d1440380400c581d070203052141d020b961103000300b01c2d004580c0c102e0384041e0107580d00000505181c0c03016500380b1148680088501056015403101c61201d0003600c1d0341ca0980d4811020100b2002c1c8814018046020700000c5408403039541c00184e0049020818042c00e10301003611300107000501c60095030a9032040305210188140040c05c5034200f984a0f288055660540e184c2c9540c901003031042c91031055984e00094040c0880c103406400c4c1003001090003640c52400c0c402401058800c1d11503d00d0303d0700e04107d076081c01102c6490070440a8205a2800e013005290301d5070700c002d400a0451000500040014400061903956600d02c01c00001d0940c9403a581001c080c0310502e45084210303a17 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 173496294 1250 173495044 173495057
    0x6150f1003050a2f07020402040f03060501030308060913060911030a03021525050f09060c01020d0b01050a020a1b030c0e040303181a15060d020d0f06032319060209030c01 75
    0x1440d0485204025010307a1310583d0b0541e140e00600c017213130081c4507540c012405903c1d40c490110070050950005412240070380d81d07004c542c0e10703034100300404200182c4152204890a41410000809139082040014040c0396180c000b030300c01c030740400e0810715880c00403001a040b0020070060911403006413508903131000b0101401d0001d1070580b000e21510000310100b03000006c01d080c2c051000c07900844003600006046d150705d621160340024013035046055019000703410b01001c0b00301b5502c210b09170380d404c54082d4010004034001e070f100c00c000e074080b041518484019050003c00440c801c0a4580c00521807a003050800d40b40a0078000c0844480140c5000d216000200b550003141e50329042100740c4e2100e81d00e080540e00c5034128003e541862061154101e04041000195512070368045c044036a0049400e20585401c040030b9001c82e1785902005208030313001c1c2c651030b80311881004042d248032019011181c22402c000714014480010240844900d500014108001d0500b4021030300504421b00b0b000c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 173497544 1250 173496294 173496341
    0x12030c04030b09071a160c38030112020103020c010e060f0c1306080903120c030619050d03110a0f0c030201030f051b0d1103040f021507030206150f1003050a 69
    0x1c120000d140c000c0f01c201c0408503507002c0c911b0300300c22101c00250f40490010700c015540e408003600c456841e0702d40c2c0340c181000380b00d08a096590301e169610681310010858078580c28415860320601c0f02c030000741d040507030030700001c00301d03403005d1203281a19040840240120b00c0c088000340c40440006110b200801c80038459400ea590340102140d0950303046040100c0c9681d641301c003044c50760040f0074a80c10a01c010f0014061410040401140078143c00e4844558410201302c102480340700d28498990081200680c50340400c0c450802d00030307114011400d662210703000e9113900100c48900300e01600c265022060401c119070f0144220701071100900d00a201520b1322800c0702d6038804096100c3c0d0100240082c6a002d4441c5980c04418400c0841c0400358490415040038518540c0004049003d8110520070860f05070014041e1081307113038194020306103a55401d039006581303e4401401c03900300c0c425543e107035225514441140d011005540c1d0020741450101291010f580d5142c4200400c10000420b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 173498794 1250 173497544 173497559
    0x7051c0212040302011416030f0908010603240b1009150305060d0f0501021e090301060e01050607030c0c0504050a0c0206181207081b030c0708010203010b09100212030c04030b0907 79
    0x107550441341c090810308182880e01070711081501c42c034412005030481c103c010104254214016000e0800c3c02c1c0d80b81600d40d6203a101c00c0d801c0b90014000174100c0d41220600400303515400c810102040c401c498081103804902c00440c1003201c030403107458007049138030405100c800c0445a5a00c410101c61400f40804e041030000701f020501c0d80741014001c0c020502162052000940442d1141d00c0d01c004a101d1688509003100c020340c0080704610302c40d5091000c002116000780a125041e0780700145142c1c500501a0340644404050350310403650070410080010700d594542c0305061207010351074400302d0a459140c40007070900300000c02c0340c600307003007008403412206400003540c610740d41040301c42d150750b0041e03070038041114000c02d04c481d160a102c8125aa4036410040041c21920344984125150191591661400d034042401882e150039020f0150114501d01801c0600c00700e06640151003c03102408649281c81c0d00448180b840e10710002030030401c0001c561603865001101c0360151042d43e00b004807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 173500044 1250 173498794 173498797
    0xa020307060918290f03030a1115070516061b03090209180c10110a050a0c080102040b0a050904150b09031e030a03020c070e0f0f06040b010e01050d020f07051c0212 72
    0x1154a980c0131124404015a225000e1807081c3e444024100c07500e030751503942c00500401694078095451b0041018001d50b12075125811800342c041601ca0508255030365492300041c40c0010402e85d015900c80740741c1d602c0300000f183c0071020800702c0d0341c005c03450a10070b00501404801c054440c40b40099003488003010b60002041c681d0002100711031054004100d11021600780710019200780c0140070b002d8521301003000005242802d0392250f2501c8143c0d0790b4803602c2508030700072803243c1d440c5501c00304144449035108400a10324504002e10010306841d5403080354140f19110b821100071514005080c41c80c0749010000c0c100d0360343c03240c40400c480000c000401503d900600c3c46903018144c01081d421070700303181403011002030715810b890001c851506107a030421801c81030740c58299a4070440003081c007906240c00f40105054060312115034003489607004480c5030744221030787c808450b400e12956981800143c01081304600600060000c000e0b110001c0700120345040069003594400e68614086445090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 173501294 1250 173500044 173500091
    0x204030b071413060f0c02041103010e060a2102010908150403110708100b0301140703090b070c0807030f1103160c05090f0121150c030b0306070c0605090a020307060918 74
    0x900403400010a505c00e55006d030395607000039132207420a040c909030703031030240301850403030700900c4080c00c0c076444010904c001000b40d40104403210314000c500b4010200e62241d03c40e2107078410300d000c5481a0f03031100c1107070400c0c200340d6032282a0340464052005050f0b00c803a1004400004c071000d00710f114603000d840750b9922900060099410303180c001a4549590a62044080b0040c9183c100c90b82d00d0074042c02001040c0c0380c002290300b42c60000c0461a210300c240300445034242d009008900d0000746860a4500c655401640010024003078030203140ea1000341b010b0210100c161500300c2c603811403840c0c02524802e0b641c00081c013039007941c000c10240540c0034203800d0449515940c0b04800d0b9a10846182c0410038250002e041c089810f6101c101880642d0302501e4022000e94041088803036400400d5103d4006451031000640158046000308071140d00681e00178409200b00c400c960f4665001c01c3c1410850390004004c81c1b00c16408005030044040406080a220803042124001280b8008044140c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 173502544 1250 173501294 173501297
    0x70b041703070605070503100803090a090e01090c0b0c10050f0106050c0a23010b0103090203100c02070f06050309120403030203040303050a0c061406040608030306240d0204030b07141306 82
    0x10100034155030520445a1282d0030280c144007a01c0c140c1c1000e0300c43e40c01515100c05a0794107540000740c170071000c003e0302c03d0402e000700200c1c0c000d413901982c0b41c094000400c400d146550f03507a251100050ac0c203403500000f441141c00b00740e1203845060f0540c0c1482e500d0120008503505240400940d500048041415900382c0d0909603101c4040907400c40c60000805001050310b1812543c2d0a0f1400e500b6100038444940c900080c00340c01d555400440564240200003505603010711401d02d040c440507040034070282c0c21072040301d11240d03440c0c004d0320255690750720410105400000344540300c013027401507000c882e0280192a1601d4034640e4001c3d524401e82c0300c0502000000f0503061036032403040a4031855030340c0019080c080c900c2d080284104a51050360745510a81c50048000741c1c1133000301c19a440340c00001d01d07035500d582c1c40000e41400e4606640580e920a00c0411013140c0700c1d201e610141c40514051444502d66182041001d03003000e0451944403594441405003030006041440b207042516143e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 173503794 1250 173502544 173502569
    0x3010b0f1c08040f06030f0e010e210c0102030109020a090608070203070206030c0d02030411040e0a110402030403170a0902010305150d30020a0209010b040b0304080903161412070b04 80
    0x14201640380b400340780c208045000d050711000844c240d068001f80c502810301001000805078134030110b07007240d402d001708a8860300000b9058401441a1040b02e402b4010803040d1803801c00500942e5003240c0c026000f03002003990104000c074481c1d60140384280034210740d050201c628203040c0d5019640b8082c05030002c0c031070b6900100086030b1858404c180c41c05010992425512030402d4940600b415110021305406146028030580d4810360025046001503000305c01611135151038814031003c1d620080041c0e060220085c146103c2610345d000003889101c400800052040040c40010107175003020b420481e0110185000b000c4d00d81d0341c000d0b0300303003081d51040354a000078098024503000d807110341040800e03240b40b681d06502005c2d00880c03282c909074421106402c10381c0c4c980c640b0212500032805a1401c420048c0001400526880001c00c801d0000030121403000c504081380d000c1c40142a08140d620300d480542e46145402d001041a151810389006080140d00340b110a4407079014510429503007031003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 173505044 1250 173503794 173503849
    0x30203030c0310030204090f02130203150d060603081219020304080306010e04091b0603200f070302012a020c01030e0d030c0504080102071b0801020c0d05090f0d05070503010b0f 78
    0x100f1101e60042d60302810a00400304030703080502e14104e0a40c82030340506540b03c1030150b070744500e2084034410030403407000e1a0400002070511200c54658441110300030383d00c4001101249001014101c001c15003c964001482c2402101421440d020600202d00b40180107020000f150070301600d90111080c81c05010480b00c43d0002009001e0120028202d04054480c0002c01010b89145106450841d1014003100780360f4903204040718504417240100e0401448a120720b0390b0702100400c420350003071001041c002e001d00300490000d10703d01c90000400302c0d95070140c0d03000c6030103008448024a090030200129031108415945130f8140070a407230205139540c0240c450080c05603040d100030300707811802152614002c0c5802c0c40031544112102050103180c80d000140700c107050080b110042441c0d4090048200482c40a841c142c06c10309409070300ca01189402040358841c0803501c0141070040008040c00740ca0300c070502d82142c3d104a5640d01512080150380c0682e183e03e00d11420b2a0740080541d5020300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 173506294 1250 173505044 173505061
    0x121030804030c05030909090102220b03010506030c12090304061d090408161e030e03061303050d0e0114010306060f080721050a0501060e0c0c1b1c03081005060304030203030c03 78
    0x20a0315481607004003085c0034000308d2001580648484000d02442e0400140e442040d20191b22240c811020b0030501040140f150781000409560455880c8007241d04011030f010344410001412107041781c6035070001c2000c01c1010f80c880c0f4114005001d0050441e5074218110100d1b005a10051010700b001800140460902604041c6283d240d50030000800d100c800c141030542003c01306a100740c0000f014481054143d24010410601540030758001840008c0705560556040c0c21006541e02490398422003d40007440c203000d41c400503182e06008003419819850644e00302d500d540c21038004890101c400f0302050b039000603c107040d80d07004030b0b000341301e00303400d0300c0c250b00c0064442c600400b6406404114010400e054002d0802c1d210044d03010402c554803151034500b14040e00d00300703031003543c00044a013568803810040c2d05000b03070015044094040103400750740501550000124005241c3e0801c100041c03034242c1c5500b02408044502a15600306520300035a02c1c000500210700740c2070300001140008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 173507544 1250 173506294 173506297
    0xc0e090a090309050d060f0507020102040501020d0f090b0403050609060106031109190306110309011a0a03030804050c09090708071d071b060c0306050f0d0b1303020a060e03030121030804030c0503 86
    0x3c0800074030b92003588099180840c00b5007040e0030004402810900412704c0e0138010300944041d500b040e40100b8202d411200210343d0b031a2001842000e01608103004110607000800901c061402800100748504200b0a030350710301801688440200340c0350555800c2c100d8035023000c840c0c0d1710108403842c20501c9400ca100340b0700548a40d200904907464001c0c60181c03551008055441040d035071001b000300b01c00d1081000079880f80f04000c5a8803101e226001d0000a0054440300d8021780130340101c612a100d128003060308980180e406a00a0340300310700030814400100126030190142c0c103011200f0407040b1090081e1014090040307410b1150440c01a402c085020380c0044055800c61014850700c02100300c0038000b4a034034019580206044000740c510ba06140005003140740e44000000c009070b40300c8030108000381020a040302180103035001400070403220702a40b0b581c618031b04080c59586d454022201d00c08106502600060310700c810341e09020030741021103581e0064043c01d10764900f14251a020b42113 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 173508794 1250 173507544 173507549
    0x50307050d05010f181a0103030801090f14150406050d02031c0c080f03070807051c0b010c02030a1b060f080a02090109090c02010f110906030a110405180403030c0e090a090309 77
    0xd62521050303482e0340e041ea040d0301080902401e4441c000c403106502180f01c6e0002400040c000c40c1040004020001ea42c0e4400c0002d01c03000d01d4001800c121040300182a40740a84400301e0041d0307a0050807a262030f16114800c000d080413507440710780000320f03408691140c0390303410300c8400c1a0394088020700d01c0e03008901d10301410342e0000c4115a507018040c10101d00313410954020000032034010000382d020303008078101e580b41c03079141d50305194040400b04440040c103070030000c00f81004030001c0c1010050f201040f14990280c031030403905040112a405440c0c2d54410359220604001c04024161085508000c3c920f4000219100c05a07496040000585201c045a401b5842061400b11001d0704150306600c44010540c02c48420b010804022101642502820040681c032945c1080410560002d07640071072880e03510b2907005070521750f0310300002e425810624100800100c6401c204010980e251144c40038000190070000000b0700e03241d000c204400f20050000c2c000680d1055042c080c1402207c10000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 173510044 1250 173508794 173508821
    0x1c151d0304211110090602060109050405030d0b01021906090204050c1201030f080f210702030c030d0f14040f120c030e0906040603060e0328050306010516050a081909050307050d0501 80
    0x8013004090320040400c040c034407034480180545800030400c4d0805001d210b0140f9089001941411a21746190700204030301d240362815481007825181800d070480b040b191086014020008050f6610700600003030f1400289042c000031420050340c000c158101c4800341c1502d401004070720440f00f05183c894001d208121901c00c2e00940840c552250b201d05061031550246c10445200e00d036242d07440140d0742c9000b03290961169400038030009402009942c420251406801030101d01d02c02400600c018203403041e24269404a40203d0040600548000f19800d0404628101c0c080b0826a01d0017801d000b14400041e22600384a408540955541c4d006039015540040007048030f10b4030380c250141d0342e502c668042002210480e120042c105040900101061180d860f01c51560b590380004480590010000405000c41c10b001070340404c1041101e282c5581c840e400041c1d4078032065603001039481c6003c0014041099500042c40251004940b503002c48000391250700e0b54044a00e000b0b405021503614034003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 173511294 1250 173510044 173510059
    0x40f050f0a06020901020c0a050a0b0a0905040c030b1e090103030c110907020606010f110303010b0c0a0b04063602010807050c0a080304060c05031003021c151d03042111 74
    0x8140803583e4000c009001d03098003119082040c04090240988040c414960300400a40041000e20080001844002803a20b483e945264a03400020210340c10f42030300c200003070796440b003400b080d040c03600401d410000000d40c13020b068442c0b01c000030482c0805010013010801011140030030010f50b02048046032800a1a94216251511000b540c490040b240140003414403802e51006602402d6242c0030344c0500d4001d58556800c041c42410329900c00440c0501c43c0c41102071410105190f400b5907400703075120302c03c0840c1d0528848056070402001c02c2d003e070100781e220604400b9a03c980c41d006c1d10225420f003445600d03a0741c0c0160503a024040c00b9450120780c09540440d608214120300194441c0341314490405c00b8140b000022500f40c00210348031040310848103010f00140c40c001941c1030443d60120051041102c155590040c0c84d000962201c0580d51101170000e00e07100e01120460750000203030f0007141051720304444ca075502105019400c20408031024804140500c0001d082402d0102400c204d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 173512544 1250 173511294 173511313
    0x50d0603060e210a0804020f0d0c060305060a0f12110f030d0c150510170307060e0c0a08010b030c0d061409150106020a08030402040f0b1306031a060603040f050f 71
    0x701d0f250020704101e40c0382c0322200400005820620703c25162008215910410341d0343d00c5909101c90341c280319280300d0780a05129501400a201000450050011a540800ca6080880500400c812039811043da58031178204240f02031484400c130790017a281c004991640e031210501c0414281600007440710303014050803000c0011680c000d03106001c82d0f445051000030b00803641e0f040c0d404603a0280d0b480f1400d14103006c1c040010502020f21206841900410790b0314108183d9030b400112411800c07070801507009100050b106142c01d2040a004000b402e0081c4929100040043e0b143c45903085e180d88204003882550f002c0c419203602000c0c254200618800240c103110844a90b1130a2488044c804c00c0c20040010071a42d10100d10014980d60002980e030541d00d0b03503400c000181440d55540d0480541c0d0b2081200d1035034501c0d1450844842c0501c00152013400c604000008255010405410703109000c2401029102e41003121392158026002450382c1c50303540303041e9040540e0b0715505400d911900038103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 173513794 1250 173512544 173512571
    0x121b08041415180105030910020a03050f0703051611070302030a060b240306040221160306061e180b0304060b0a05030c01120209010201060308070804031a1006050d060306 75
    0xc0c0090081250010300c40d000c070410ba48100e20640310040c00f003e06288803098254003410245800880302415101c0000380021100d003280c00c500300050001b80c58809105e0750b140e510310440e0700b01440d80fa040c009407400c14815040b074003411202c6020001401515041403d09100711400f66034004c050342e0440340d4074140503011701401c0c9030543c03265002000c003102d100603140d81c075100d152003088960f0840d40ca00b000c020080d0449004406d01c490301d0150086550074222400d4403544100581e2615804501d00003411101c003a0400c0007403103d20542000203854480c0c03640403c40300c0c0c0c1b801c4014130300351450009a5160f294417040b04d042012060104022103030b0000313034580170295a140c0d80c25544104241c0c0d00c01d85102402d000c9050082d0101010030207030000c20810b08107000201d40c640d600e85d201c0105a120800036241040e0204e07080c0200031682580c1d1501c1c01512000d217061707090a00402800312014800c160501000040107843c802043d00080003d642281d4104440500303040e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 173515044 1250 173513794 173513819
    0xc090108010c0e010906080105010804020604080316050c011115040206040e090304030203010c030209060315040b030703030201090b060d2102010b0d1203060608011a13052205060d121b0804 83
    0x1000007181c040c404140c0c3c83e52185c40c2d254112480c5948244d001e03441d090041d14124400340c026078000c10304100100c2c4240b0200003c007405d42020540d0300501c5181d00f085820187c0c1f04040034104560140901d03642c43c1c0000e10b0110181d0200031031000342d2124400541c90348510380c45251694048002c212416801002600c21240250024005613040090440880c41100d40d1160701c04010710200d600c2800b0b15100708801c1c00007910009201003540c000a141c841c07240d1044005039161180390040100c11200d1035081790041e50b15484911141e51030b140b500201682c049855849040c8441005100b5042400f0040010307041007031404650800d02c03040380040d550f40740030038200b25001450501c03440e40141203601803c441d0008222210700740304580d00c000080e46481c40da41d0700100e5503540308c00410040c904001c2103600100d000c03c4891040d910010613240c410700c203410350b010102d4070b8196611700343d0344103280c031404440c8500c4400003072519005018042c40000b190200c0c2034118801c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 173516294 1250 173515044 173515061
    0x3060f0e0f0f06010b0418020304020406050a0f0512060103030903080a0c02090f0703290d0204020c01020409020c0f030c030307081e1602150912070327030605180715020c09010801 79
    0x3002d50300725a803110303068003a1b440346104072195901d81d40c1031340303182c41e4459024640140c401071002c2aa60780e503400083c000c032a41d800c8482c0d081048401008207140134038100801345070200c0682029807460300c000c1c1119065200142c00d60300c000a400c40c3c014407826403901c19540c02400d031800c038186150a00300300d1904568403000f09103000c44102403c44c2644901000402190044016041440a01070601c0c490344c800c0340c0194080c8400c03680a8000c4c0003810140140000058807080d1650803103103499000300c00c0c0c0300c81350410041000781210210032694000c0b12410a1156920b800c101c40303031407410b40c802c0c04802e5003005040c042506280c42400f50300c43c0040d422a62044030368811030301a070600340d0b0210313141d60040301004040050480508a0a40241802900951041c2c1c120607103c01034440c10b003503200050401d00401c00d0078400c4e160400c20080c107000e10f03c103041e414a40d035403009000346000f00044103400c0100900c200000c003040e8a000d4142c60581d69518800b83c040c10050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 173517544 1250 173516294 173516323
    0x170a030f0e031303120c0b160e06030712020f19110f0d0203090907110d020c0103230f15060c0c030105060d02180a020d06060806030607140403060f0e0f 67
    0x603408841403079000003580e0601c0868000441c0c0c1a00c1c59484140801c00c1900300340600a4030010803002c60000b0100505ca214400c03100d100408003010010042d1071409a2a4442d85041c014822400d40c41091004da1002182c401a0340f20113911208070a40900020510784004600e0760b030f00d1090380010031041e007580c03243c111050721504107240c41d101d1041c6002c00c00107038028454030466290654210742c001d0010700f0050400c11040d80d5807420003100586100142e4818038201c3c8255905120703290340030310507031550b850a03d141002111114000381402c4405403205006c10550b40a0846c1c804010900078080e0ba91200440b0f002502d90348022840b61180d460000021114102000d4242202e40e004128038615628000c900c0c440c200081e03c0348029a50a115108800d82c0ca4801c66000d0305007500d130200e803403821004040c43c00c3c5005181c401081060150300240085070020784007030b2503004c80c0101c0c104400b207400b84c0003460240c0b9929020b205444003110000c4001c1200e07201181d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 173518794 1250 173517544 173517551
    0x70611071b0b0301050105070213060302030706020a0c06080c03150111010f14010902040803032d070309050d03060b0d0207110915100824030307060504061b09030f080304170a030f 79
    0xb01d107495001400240b04141c0450410071400700180361203802d195241516040c0090407941725004a494600140c100001503400152580c003800904410800181000d18006c0b0316460802c1040744a404050003117a00d107045242004410703809041c0c005c00241284000f00210f0030a980a01d003e0000e8050190001c4400b1002142c121624021501624441e400451840c0c82d05070700520380c1104214540218030f04494a0041c8001e1000c036280034400070303603011801d25194240342c0c0c10004841600320500d46058002c20651243c002554681c200f0941d0040e00d031a404d040c840321814480d034403154007201a800b00448500660b1595414020643d104e0007012000741d4107803174441c4159000086001200b00d1450094000354102091080140a8038100941036441070107075401034404455054031880401c040c81910118151400c07150301d0003050003855511a0301603030044100280500300c00100141c2400016003961642c501c400c280555620401c4c00700030010300107140c018034410304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 173520044 1250 173518794 173518799
    0xd02061b010c05130e06151b0a0f0204230412090803040305010c09150c0f021318021c0807061107050a050601050112060b03341110050f0c070611071b 66
    0x8881c0d00a0320541003e800400c007041f4a0b03400c0c6440e42c0101c144000d941603800e0444465913414070106070028800c0d110714865281c140704110944120303519081c0e840b403400c0020000304d8401e180c110f4109402c8860704006056510007124900381c02e800c001170360700c00003500100300601544032a44041d180e9954125003910795900441180c3c60754000700005201c0743c440d4020520600702031603103603c000c1c2040c509500801811040d10460040d1494400102d0f01c0319040d801c003041c120b082d081c0428000c40c2c2c1c00680740e541541901888030041e00a955440c6005c192203900400c550640c0d400800302c0740fa000c11480d110380d961009020303150004000090b054800c0c03100d0f0051000341c502d4940d415095940c0c0c01100101844a40d1085200100c1003400c44901808a07901d446000312030340d22211000c0e241d0000510b40b0481440c452255450b1804120442c4d240741c0d01180c1040c40d140159658504c1420a00050070b50710404011003140022520108081740c0c291084404012060130089075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 173521294 1250 173520044 173520059
    0x30c04050702430501020706050a02030909010308120106080915040615080d02010e07050a0605090102010b1314010506190f0c1205090f0d020906040906020403061d06150d02061b010c0513 82
    0xc20510420b809031f03200700d40038005a4000d03c003401c070120302c900c1160b00f003045000002c3c0b4082d200303034810341301c1030800104603c420303210b07503c0e043c0075240b503003030003803083c100700b80c1041d0784a00b03c0140394410b10402011800304071407034001c3d1343c415078100c820300041500c80c8412911100e00100f0780015600c0d01303280030001000414400100c590080c9066041450700e10141d42c1a448580c400381103559442c1803240d2030b55940c0c03820340c031002c04200005101d444407821107500041030f04124803501c0240f114112840044c0c0301c01300e0000851a14007000304501034155080340030020000c15003454445402c2c03202c0e41c0b00c0c0117000961021145015035408071014031442104442001c2e42104000000450a0405400a562a41c465a40140f410f42c0d0386c2c0b103100480742c01c000441b1005031701c13400103e40c1040420886800030910303000308005110b03050020341d00b4200300e20000e004a80104070720000814010030090340c042c03e10000e120f014565240203245c5e5001040c5107168411503003000c640b06 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 173522544 1250 173521294 173521423
    0xc1609050c030712021204060b040b0d08071b0b0c01050403030b06070b01060e010507020301020d02210112170f13060809010e19050115030308010e060609030c04050702 74
    0x10820901250320b141c0382d9520440700c181c030910307256048a0f001c004440c400000e4411942c8618080ca000042927005442080251030250700c80078491882d4a400c40082031240382200c0302c0341c2d4400648560010942100b111180047d4440998042c01003503c500c40325041d0010fa10a034400c0d0380400101501408010701400303210809000d082c01240140708450142e4001000140c0c141022400e04002e9400070b801e980c8110010f07001a600416201414911110300108a40c0b241b001810150305140b4070f110546c004150251801c4414007803c40c0c40d0b1f0390b0340201d9510f00c00c0f900c1641d50f0717142600c1c0030400b07416003881414002058000000c200f03600600c0380c281c004680344007401d01c403549600b0008801c400f03480c054980d9580d900749400001d50110400700218441c0e1298000c82d85040704616501c4401402c103070040b6400c00500103070759400f182c0c021070020304840000311031300c508404038503109142c54140c0042030500c8440e02a6080b002103003804510103101803070585c0e0100b0500c0004d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 173523794 1250 173522544 173522551
    0xb0f1006081915060c0b010e0910020310050402071b06110705010804020a08010516030f060614031510120506030a21030207061103090d0201090c05120a05030c160905 73
    0x50000004980d040c2c0110100801c50318000354040b8958800c01c08060b50b810059018901040c00c040c8058100b16010700440e005242940300008a40741107000c0544440c40d026400340025070000c0040ca010840300001c40160801030001c54503002c6c18a044859031043e00c08032010030f01e500340700086591103000b451402d400000003505c05a441c080054550620140049038000e48045005c00e800381c09118040c807a841d203c0d004003003002c0992000d41140c01d0746116080242c02c0100902c98180c001c002c039041380503ea800107540faa00c0380415a90114440e0f4040e42c0191300c004607104007940401c22450070418410100415150706082582d58208598001e000642d00c68107038078019180d0700b9001c005002c030304025140169a55500040741d9481900d0403410201000340302070410108014075242c801400200121001521400000c00322441454410075091040741d19a0760103003c5c41c19050750100c1100d0700d440289045584800c074841b1103000b07448a0110014225140d0b000340ea00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 173525044 1250 173523794 173523797
    0xc020f1614030a08070b01031205031006050a1b030e040606090305070302150705030c0a150203070806061309060b041706190911030a15050c0c070924030b0f1006 71
    0x1120310389450080304407804011190325001d803070003403c007007444040104900780c441e0410009030b604502e000e031380c90304441c0c15080c20440305000b000105106080008265007090070b060b9200d00b44008202c8802c4c0003401110221800710392100101604006031101038807003110306011a5440348012074480b403051001900075400110b04102504184403800c2781443c804200724034009241d00c83c21f00e580e01c851148895a40490062800e11003911140d0701e503042c50300002d624508114000901c10900a09090f04c43c160010340d031031300b0800c80070400e402051841d0051140c01d82d2404151607a800904c00e803e0341c1e86501d612840c03001e5004c60041e200745482003e00007801601340602c80144030400302100c1840d0b05884201159801b000141c030014441d00c00390011110290060382a120040e000c8080b905003403060b000f07016004a4010140d600300b11001520315504000c10400d940354001c00b68001e0070404c404420f02640b42390580c07050600f800c00000c280c442035100700e1004014030a040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 173526294 1250 173525044 173525083
    0x915030b0a05040e030702190306060e0906040b090c19050a150c03050702040b040204090509010c090f052e020f070b13061214090d020609010501061704060615030c020f 74
    0x20070340c0352a611507481c0d13040d80300860b41498400d40c00f04a1071a451a03c4001d4038041c403d040003007040900481005c1c1103549491402c6007800c201c003503175a41c0090700040525a54000261842c0c104010720302551038010310824140340364030100020942980101e9014081d500303404541504802c0348010000450b6403030108400807600c0856035900541000c1380d00503110302e94100d450b6954006040501480c540018517030500541c00ca00316082c0601030004d000908404104903007005c0c10503001c9503415207040d0384415104043c001c2e07800c0e02d20011101001d00c080c00c036407519070000f45403603c400300c001250041629107c00b1000c40c00b0711251461030701c40d5081c090107103074407500000d1040d499401001c0307401400c0740c00300c02009c0401c80301c0458640c0914640440307968100803440d00001900020402c9505000c4020451001c0d03c0d00c500c104241c24000ca0100030071a030000008181c186200c03a003441010710300030301521840700400c0040c4507107512405203c2c000728500129800400101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 173527544 1250 173526294 173526299
    0x6040302150c13030605010806070306050a17010905030301090606180305030d0207060e0106060302090f0409080a0810030b041101110316150f1a0a06020304030b040b0a0e0307030915030b0a 83
    0x38103407580002e2482121101c01d1103020000185800160b002d1403040801140542c101030708540b0704003006022904140c100407007009540c44404100003079a070030640603441014085031803409022220030003007040c44000000a441003103544128195001e03aa140a294484103240040f0a00310380000b9010f40c0080180801d024010b50041405c0c82c07142030082040030800032507908546d9658000d801180d0001810482860320800e155181c29044904218082183d220360099020320300038407090182102c040b40c0d01015403c5020b0045502420341403c6140034640004490a41544603006c20441000710140c01e1011003950440242c5040d4030035103018a40b03c1a209100441c1a00c2c0c4070f9a6403003041c2c1300d03601c05003c3c0794080800c1e0755802c81440603a0051003003145040e80101c0464005110500028484405968010b42c114881d0205070301d4001c00f400041c404004020b81c94440060303658100364020250340c084507405903240700c1c1078402440c180c00340c0c0e003c036541c1903004200f100306 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 173528794 1250 173527544 173527573
    0xc050c0601121103150105031905060c090a03080715110a3002040801020301050f0a0602120f131202040b03010501060909020304140723031f0b030f010c09090b0306040302 75
    0x65880d198041c0c3d10309005010a0340202e4180803400c441002403020020060000b400c0c200040620f001180000c1c030900c08160321210345030100a080d0a0f200d0000003000c1c03609a031036151902c055608070a0050340c42c00c041c900b140301100d0154544104900f000d071500c20020609c400d031340801c04c42c2d032110040f800d91010005d55000091840807c0104d4859103115500098400b40003d4051a400141e8a5041c00c080040c0c0180c2c1c400600d07c01ca80c8820141300d03c660204102c000200000401038031581402d440c1b60190041441303543c0c0ea40d0a4010004041190030100541c1a0090f5010000f0030360820078182030720800d00540707012410510301082006e5142d402158014090700c0d4148122000c0c00704642080590fa0004200c0d0140d94014144003403900002c901804084004100c0030070030b074040241c9103c070700348050541591411440b44948003413100c0106c0c000000001c2007040e0580c000038010040c540295280c10f0f2070a0700130020f5090001c1e8580c01b0300e4054004250381001601d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 173530044 1250 173528794 173528819
    0x30207080414040f06060c03110607020c101b080702010e0d051905010213030c050a080105160509030a050d03051e090307060c020a0b1015020a1205090a0f09090302010c050c0601 78
    0x1a00750056621340900c9401c8409115200103480399030b642480034111810300030703c008020000592913802c42e000340102c00d50001580403007400c003590f07241c03040e803d800303400d448900b5003000003e20090340c0b0170036004009541d0020300005200b600c480c4400f03481003090000350403418000418550100006803000341c200010403e015210744005032421103020345058040803107600442d8211607130b680134482d40c58960301c104050000301c0020000c5103001012107012201c54500001030260000300078005803003c1c418441496005412aa41c401c1e91034001401064100d0b00e2103c40d901200256500d9440c650449005820000c02523080c400c03540c84120086c141500c581c025072003980c2d0002c001598510420b44034541e200c55900300c0700e240c84c00002c0c401604682d0300e030442d000900300e000000c40d824664501c0c07403040c1ca42544c5074041180850300d110361a8014016942046400168200311504080c05080c07003540241300242a012080d505802404126a03039508202c005000901c1c1422 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 173531294 1250 173530044 173530079
    0x30513030c020f130905031e1e28020d0306060323310b1305030d050a02041809020f04020a081501020a0210020c010816020a030503182b0302070804 65
    0x90110000400440558041700e403026406c851030380000c0f400900048800d142c03204482ca0040c2c00038540003034a1828000c03468011007618103103601182240011401c4c0094514444210b520080c1c0d4031004000603580d2034040106000207414800c02269880c80303805080241140c8401c2050444450350400c0307a200e8004000d40769034140368200480000d1401810124400d800341c080000c80c0f0035045c000081c1c800100301400072804250313010001040001107500b0200c0180c00040d86031641c40071070019108683c0000441d0280300d0b01403803004c1c0030f50700820429208890703107419007240030144401c0e80542e42d20000414408070000309041c0c2101580d0003070314030501c143c84d1500500d50015841d20b0210003400c0c0103a114401060140d6000301c51180c0001100d0815546040d1095009564500c145801010442c0c0807000c18403001003c0c1d04121100c2e10038081d9180807414880b20b01c0309aa50100040c03034500c00320701c201202406442102c03003245e00454042e1520303003021500341c4003140d0352 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 173532544 1250 173531294 173531299
    0x906060a091a0f0409052a040c0c0b040609121107092a21020301081006030203030a030b1c0501020c060114030c0d0317040503131d010510050403060906020406030513030c020f 77
    0xc05140c0001b51040c0308a40030148105d00b00e1044035a00410b0340d000800303050640f070081d0703e0407458076401d075001030902c0c2c01164480917405990303a803880d00d28040c0c42c1e116401085042e41c410a1f4240300e40003244031100d428040105d560b826502c0443d031042d00c010001050380c1d86c0307560780020342c400580d03001e044030060380e42000c0e449018990a802091380c0042004400c4a502000502c0600424002200b0341c10844105000c06401c5400103900c0b485151500028141d542c10300c008541c0f5504500c600d10070081c2c214003410720300c81c104107010358000407a94503507000340350001c196a4455040140d003100007500600c0310003894824040800c444a60a5003400201101414103e1518508a00c00c0d0b214002658407a01403030100d682841886e013069140d66034102041c040785603c6c091641c1189c800719160021249a0941900e080c81950805028a41426041c1040c003805400074400c907a030360b0790100481d070b0360138904800030010814020000b88450b0140c0b80580f03010f070100741c40107100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 173533794 1250 173532544 173532551
    0x16151107031707060b010c03090e130f0b0a06050109030c090c03021216120b091f08060a05040b060607120e0303040803040603091a0609070f0210050906060a091a0f04 73
    0x49858124410701c4a5802c50100795000035036a0410229002d10700c0000300c2800c1c40402543c0f55500074181d510a030080340410030902000460182019103c204481c0d0007183c04000e036451803c001d940c00c2c1c0c04441e802c0380f660074160006429441000301d40c04036070300030301504509418400f440014200140f417150030107400f031120046402207180414080c049074102c00380100c0310800b000d031110801c142030003299860047c003c91580c845507110340d0300c150001d50018000c0001f1070003003000412a040104d0a100d040e0401c162100d190740150f0146000c1c1e803030911103a65a0003001614828041c000740541c09145054900501503c00043d41c202c006040c0c03030500380c40e0401207146800591110b070010348c4401c9018180f19658030b0000302c90751028030703100c040d1130808007041c01c910700901400204142482260384151081c8542d81d45084018800d015505001c000b0641c0c40304250b650522464182c000060100c40302c0c070455144000502840510078403100c108181c15442540082d040b90b103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 173535044 1250 173533794 173533799
    0x1a0a03020405040608030a02070608011202060715230a09080a050304021503130c050406060c02091b0f030708070e0a05101e050c0d0c08030c090118080d0216151107 72
    0x2c0f01e0007150b0103451408021922000715540091070048a540304805100c048801031027420a00e0300a01c0c180c42c0c042e42c0c02da940d50a0307440d00c003412000c600078030354079030340f80400c1d0403010703451310544241403985017014128640302c08041f07900300d0b984d000340100383d03203c100010209140141d02469102d400103045604143d070154040b010780d40221000354091922814a100304070311a44014007400040d00c5c1080b8040c20950701800c00c0040d840041d1040c504039002a00d01706420a000343d00f4a100b508541d1a07070f849a10314580c9800c243c4110001c20381540c00035503005e20800002c4080c04004041c000d89500d804c00344203d222041c000c0600700b000280b04484441e10246d00b050300340754140c0c5c40c555140f221200e10f50a1414035117940d0200301002c44c9081c04110b42e4400ea903048003122136520380c0d072b4030310000507070300071070090072000020101e21000160750f031021503288000c02558007a44d01b070704c000080d0304407500005d001d800610040f2415a950251242c0e0726011030082c15411649801d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 173536294 1250 173535044 173535049
    0x302040b07021e1e04180521160c0612050708010b030c04030f120809030703020604060c0e180109050105040207080f09040b030307050d0f0c0b160509040f0f050606041a0a03020405 79
    0x100f111425002c0503001c0c0400002d9041c248a034055445506e2151106511540c0d82c09855020b40c5450011802107424108890139003441225200b0009400a51355110706240681003500e070745c4036020200b0404a41c0710040e040310b005040c0301e000380b5030714a5990781c2404081e98550304050984440c40005100100000324210043c1e04454094401c00300e0700e075030002c03009103003e00c010282e1b9810341040c4079a80000b0b40000e403964102ea8814004202e1910b00b1204642d507030a0b40c20019031205505c100d08040d4119220064107031000504103104680c1c0f03074010300c0140c0c42400001001e0307001c104610628080c200e0060303e15000002c00106d02d400001000074903582240c0300580b01ea801c031101100300f80b60808250314186645080030754080803203440f014840c2c1c000400081c241a00b4a1a4030803e41c8a001280c1464500070402c1240c440c1300036980740240892403c10304500d14140201c2c58600d080000c0d0740c102d81c06043e4402c08004c1d01d000500d25504101009001e06401748408038169 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 173537544 1250 173536294 173536309
    0xf07090612031d03150603060a1b1211040303081603020a050f13050607080a0207050904120c0f02060307180812030424021602040c0903050606010c080c01021909060302040b07021e 79
    0x3455170140030300702418181c04040c20306602400803a5911700d00403005c01441c4040c184440c04054904100c844036000b130304058058281291104204580040c000c801c02d50814251070142aaa010441480c6120030042d0200e01c0b4202c504800b00b0400c0c00002018100d4034000c0c4030383c0d00710800b0148000c4d40c0e0004030b000c0b6005150111741d050004101c0d403103410350410400d40100000c540d075005901309030700c620600380aa085203400708443d440081051101c180c3d10103d410780d0151085650b460100da000700301c0c100f1800441c401580229000900304070001d89035062b400300f007580c2c1c0e2a503100c03a504d82d82003011640f0f40c03142c0b0b180e2420441211102c0b0348050810040110180c61580190b44100802c664403c801001480f040007001d00109400081c82607024000b801c140e130100c0128101802030740140c60340507c3d20340c00042d0301c87c10b170003004000780b002e5411510fa02d80403a07202c2d4000d90590049015040f4400024021f03840585031000002500301c1c0e443e07007580b0718000c034440400e020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 173538794 1250 173537544 173537563
    0x150c0210060f0602060a0507120902120d090f170618100f05041101180303052101090e070f030b06010e04061d040209060a0303210209120f07090612031d03 68
    0x11207001c100c1003151980502817203500201c4108104020f15000001518132405964400d81055407807840c10210b4558892040813503a0503022190b0751840f580c4010f1612805000c0c2205240c866103001801c0c840328800d03100c2c03001e4528042c00c03003a40ca140144d252000c1c0750703d6107001c91180d0002448000c1140c0714200b208001c002c00402e6504c1c1c41c1c18590580400d4001c1c89041016240d808082020301104440c1625411b191080d91005841c0ce42c2c410040320f412014066010b00000007803550566201500c80c07950301d025103014598a0307600121800e000d01c4043d00b00113000000420b258819800c0c003040000040c0001742c040e456103812207000d104150202440c000103024002035107002251141e04c50001c440300c1805a003141c1c2c1c02810a1005070840e095010680b401d402c09040d190161a01901d01a01c03503010084a03403011942d86680007102501401140804200180640503400c25560b01090101c4036001c1e90380c0494480205c0100348111882e004208081c69509001036000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 173540044 1250 173538794 173538809
    0x120602071a0f101a180a09020c01020702040e0105040203070303210e010c020715170402040b03060403020a0605070e010e010503100f0b04031103010b24121312020604150c021006 78
    0x40e9443c020100c0b0008042c07982140d0f10340c900d8503040041221800b000c030340c00402e0319010781070414214004a24910901c0d0001c64a19001045103902041c056000c1c1c443d8074002c85003444040c001401035400c840f026a0080d4041d0170403103060000c28000c0401c044603450122109401001008a0034100c0380724042441c0c0702e0351580d0620545035410408030300940030f44010031801c01440745000d0015042480541380d0f100a0100040039075640d503110105000e00070b015100300707280c903140081d01e542d20100c086485914010129403528402c01c9141c0c410070040e11800c1d1001c0a2400640e01a0801000d04501c445c2d14100810384804403c904002081c110b1083e40e241d504502c2c0202003000c004040a009a04d00b0300060307296501d8a03404c642e004440400400ea40c0003000b83c030055841469200a030510707101c0d040c0800310001c2c4508006503801013400401a01c0e00e22801c036203800f03054801900c00301615043c0e940030360b42d0364040c4040444500440f120410a80204010740346960b200b2175 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 173541294 1250 173540044 173540071
    0x100c02130605030c010e01050414010c0f03020708070e04231905010c09061103181201020a180504020a0206010501050d0f0e0f06011706042d150b010207120602071a 72
    0x2d0b09082203415005882400c02a1041d280000000c2032801644140084c0b0300c1901107080c00c40c2d000e40ca600a031507811000d140d82240450401a54800d014403a1035640d11410f00001500d5481a0700b49000f00e900000c01130341d58019250080100401095030546409445040740c0b4001c40420710a50540c460400401d01d81070013807003d88001184c0e40001d050015102603040000400301c11140410140080c107080000c150010400550210700520720b2580300081c034032105a0024200d401c001001c2021094240d103c0f0140416802921451405603021000511542d80104050030f1040303080030001500c0c548a5140800740e8404124081546d0031011100b2001300050007000d0142c902001c02c203081e2959600c0450b510000204058541caa041b11004000700f51190000ba10141002000044160f5410304da42030001c030022140d00940340850442417540040342020480d04143c01344205800140c403003901a60014000b10391001060402454603041210254010f80d078030058070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 173542544 1250 173541294 173541299
    0x12010902010e010203070201021c0c08040305031c0614040f020c0703060518060405071509030c091d071d0901020403061b1b1218080607030218150405100c021306 71
    0x1400402d06140b0050454104021083c0541d0700011081aa0907401c2c029480309040c1032001ca5032640356600007800048002400002d00c000003002d04201c0b10700070140c60f17204032218840411551a44a02040122804404141450550710003908000051405841c000640584500344205500704682040d55002400010681c01e14200078412040e001071460b81416194650f841b00d41e131055001c0c44501c0d03188046841e10410340c0d0802503500c149007443c0c02c5d03280c0b2803801c058810140b20803c5890003642c182d180d0f1000240d244102c1e03150b143e81c0709141802204050f003082c801400280c0d17642d02001300100052461203031142c0b110840d40c000c64440c021800042860302c002c19200058036403c8c030325002246903010070030700e10f00032810500e80d1040c103042ca80c540e8540ea82e000140314007c44040149268040e00140550f0461954804681c0501b400300495810312000480d4080d00138002403006007084414032600018a040c01044980c1c0f6900140031568140c1c0d51048880c0c940b80c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 173543794 1250 173542544 173542547
    0x1020a0615140d080f1c0203010f080f120306010309060b0d03270e13021207030809122a0109030b010626060108220c030b010e0105010c0c0506181201090201 69
    0x10301060b80c40440300199082920b407503400050040540d9894801e0000036110303420600700d42c038000300541c511015505c80d0313035810741100c0004d410710884002d402024004040c0320804251600d01040c180c00c02c030b04503140c55004600801c41c20100329211590b80641e02c044d55500071000340c030244281e66441e41000c0020b02c41c802031028045ca050440e070140c5c2c0503c11840c036802c419511102d03801d5159504902400020221080200700900500440300c012003403001d1080206600c207421b40e0034014030300305030b0700c6240d950f05540070f030f10794984044c3c2105101707520301b28400054000c145070001c0c4440d01c0b9114525059020381c0a6804180000e102814003003d002007000c5841d110540003100d490300380b0020702102e0340209200049124058006261002c940c0e10002180c2c003c080038203520b0f00d07440d000802040078025481d202c00070400000300d0f9840760907800c03e881d5101800301c0a09240805205030b503007000c2c42030001108001584031890700e0302c03c034000c00c0070400b50001c602d94089000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 173545044 1250 173543794 173543819
    0xc0f0309011a120303010911040b0705010603021f020604020d050106030516080115080c0d0203070b0c0307110301060b22090f020a090609140d110301050403081506030f070e01020a0615 81
    0xa5041c010a1401c0607000f003210b000c02a01d0440d0003c2e040450060b5a190041c007541c440e54201101d66a40440d294007071000550103101941c1c42918007840f88503200c841011104002541400160f000c18001030043c01c1120428010074480c400104520f52660f542c181422800c40c4c00580710b046031071080202880074010ba106450702030248a40d602c0c10880069116201070408a008100401c0e0070001c544003005500000c040e20302580b6110a03403c0e14198880d44008803c0d00c400000800224162906118030000c6030100e1f00c46d00d29080e4400e071140c0041c008070800c01d200d2018140005400350031401491035840c500d080042e42c82e270039900050943e41654208034100841320005025694a03c0c0b501c170b064000881b44080011441d00e00000d6164004440c96055400d120a0200f0150481d0101c0c0c05401241c410b203a120303d102007488102e010440f45039040f4104400428952070050004024401d0180b0640c3c401c440b5548415040c3ca10400310242c100741544000c00180c002400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 173546294 1250 173545044 173545091
    0x708041101032007170d06030201090b0c0604030f0201020702150304021e1e03030d090812090d14071b060504090f0915020306031509010c030e0f070e0c0f030901 71
    0x701046140781e2401d80b1124140003840a0141c5040001c130003040c007041c4c44102c1803060f299600b141d80d41b582e401d4100c029202030300c022804a89403490109040c0100e201b0364a40d01c0086000386559034441d1812116200f414409105555080044101503111440b80341340c070221008140e542ca040510502c0700018068248048001121072545000c0e940d89485d4005180e1203280d4190751090803001a086104402d0b00121440c600b030503030350400c08040068862041a03850700340084e940c0c220560345413290741c0d484000152600b0340c3d0815055506002e080454018026a20f148203004561185500030b6041280440c0e40801c0810140361140a1110641d482000500c21221142d485c1a8080c4180c40b4150b001600400054102d4078104001944404000141c1d203641c01c005030341a000302209000712002904202c200d1410030000184d03007030b40d8402d4000170078140c0d14061040b104071001902c0c0303003803145041002000c1c510740c1e00c1c0514000d07101000001480076501d10a00c01c220140d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 173547544 1250 173546294 173546297
    0x705090f01020606030a1203020408010f0c030e0a030203160602090909060a0b030f07090c03140a021801080c07060903050c010f02120907050a09050a27050601090b0604060309050a0503030708041101 87
    0x143c10440c081d200464200707480745d1b006100965110b80b0750010fa0183c021500402c60b01c0d0b20302059480840001d41068903030b1040c4d80c900b003000b8122281c540b502e40181c0350011f00035034000c100d4118000a9481070036844d81c02401c0c0141881c0d0040d001075520b140640f202e800c1507004400340540b114a0b8800c07291040400c41c02400b018401d10340b51a2261070354070030720002d01c3c2c0d51f885d1303030035094000d030030282a28004030303854845c03441c010300c003c0001d410169541c0303235405080f08070f00300c00d50044414030300400b02c10001e9410841e1640c2ca05001e00000b51046003040f105015480300c0c00b00c04d000d1f030500401302c503d001d038440f07000c44810304100320020031013890340d8080b030800c01c483d4455620140c142c654840300810190340717070042103018050076100c1320b11048040c8482c2c412420310f01b0f40318411f58480c0c0c050b00e05990369603d425064405c02c0212503072001040208202c003a00036805001c03424414010303141d040e11252a03090a581040300c5a0000c0b807261001c100400c6000e9030030038801e00c0d09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 173548794 1250 173547544 173547553
    0x406060b04080a0b0624040e0106080601080a09050a05010510051306030807020607050a020a0608090607020106030210050d090803150102060f310f050102090a090b060a050703170705090f0102 84
    0xb050400c650729401d94001400c0c4160366000b162060b01c0d103080340105c881c10b01100c00c3c1c0540b5102c020010a600511030383c03502c9494000049113151007600007134001e500595071008a52101148440202030100d0110b400d40b207201c46078000280203006075407003200602d50040c00546442c06009108000c0803441e201d00d80383c901c09000142400050716003da070140c80d041d0301c5210602d405844d25030b07081c102039070000c0d4600707001035034a07408100c0b144100128425030b04280c513610410303800c0e02e42d903000c001c7d07029038040d0100f0070b031a204101404914040c2c0002080f000390b203440701d03000765006413480210310f015154001c02658040101903045031503404010f03410300d021421085040041080642038441d0051038094482c2c00c1c1d01180b032166089032800408424528106000b98082081c25026205402000460f12410b00c1031010902c0701629851501d1f101900842d40755104030011400e00956290060f0150340007540e907807040707100d9280d299680002d0001c004850304880c9545045500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 173550044 1250 173548794 173548799
    0x8010b12100b03030403080d02070c09050712051e1906061b02130209220501050a06200f070905190501150309030e0301090c14090903041e05060705060406060b04 71
    0x300081e034049a1121140015041c000320380000d00310700c107541c030142009801045408008046900030041e1500c00c698a17281c0940c3c5885580650714121914000316241951202e40f254003074110981c04555641801ca82c0804040e204001800980c0d07050b00000303082c040c41c0340c441c81500c00c0340050308090600c01114403403844000794000d54150028059011802c060385200800d8050b51240f0800424160310580c4000f80c046070b200f12411880745c25414500005814144490b4010648540f035a442e40802c56050460a03070f034400f2138155a81c3d10034884903508042060000d0b44c050012030802084908108150f4641d196490305494903451a0600400c10700300e0341180c0d161488201d0030f001c10305101906081d5141d1080c0c408031381d05542090740c040e080111905103a015030f948400c600241169070380502051074400c5803c3d1005074030421040c083c0030506144c1d60030040000f84403440b001c0d01c4102040664110100c01c8030154080800d200800c082400759101410811480b1400d0070b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 173551294 1250 173550044 173550079
    0x2030c030a020a0309020402041d0606091c051e0d03060e01140f04060902300f0f090c2101180c0612150602030a0f050412120302120108010608010b 65
    0xc0054503041c061a40010100c94080c00f80d000380c0807103600100210740721544c3d250501078038118403190140802c144000104a0b2030214250384681c00043c0641d20340034000c01d000144080c610205030b500e0300c60440c5001d41d80d402c204640e0000c000c031030081c04014007c0c0034060207407030240c8c01c00c062403003001005000c806011568103482e41d108589403981c41c0d240101007030042c00c840c0c2000704854000500c0c5000d07408003554010450581088010020004c4020009a03010a80d0030021000f21a00030541604000043c0c0390880c00c48800c0d5411601c0c00000500c4400507401c102d56442c030605640c410703904081c425110140d01140d90181e504810340d540210302c84150041d03e0500144100d00d1031b040800350306c4101010503580750007503610b0700c89078081d5903a00404c3c84180061581808000f034184548141c40803601c00104059030b40c80c0c1a0303500c803d120315205044041560a1202c50451014407120034000c04c84038000180d03803406c0000d580e0a45189006032802040031200904040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 173552544 1250 173551294 173551297
    0x150e0604030503041a0c0a0f0203090a0306151212110c030d05032809300c0f02060304030807091d011502010b12060f06040b010e040b0406090603050f0d0302030c 71
    0x281e45442c02503501c1d5100d140103117202d00c3c88401031a01884010412100315075490003000401c2040c0c5031180e046074144012a40d0784610114542c00c06920720081000401d1794000c0b01c2400321440e0000025911480c100c165504c0150041e28030070f2003e02000c022940001401c984d00000070060030072140203078041b03660f400152140030100304000001554458206004002194802005c5042c0070307500580b010240c0040c03002502d1103201d01541e20880410311103041c40d40021074017044032420b9000016568194000c600707940d0b0b075035842800c90060b40d400c00210312442c8203898400c41d40c280410001c080060b41d030040c1e441024404d00940d80c043d052902941194403a21001c0c600300b00c400d008030b025200c404015604002d5000c0e03030300008800401c80c0d902c1a00351649004490340c0d00d2082009036150744170810b0105000420742013a074100794000c0031107001c8c042d02c00f25901e0b55072012003088882caa84103031401d420042111105d2403046c82180c004055918095007181041003511203c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 173553794 1250 173552544 173552551
    0x306080303040b1506070501051012120509010207050d0605090708010b0a0e0903040b03010e010e0601021b062a01020403140c01090b030a060801020f0d1506141b0607020307150e06 79
    0x4400500b4002034218240b5100e9008402c3c0107080e0f1500c425041c54030034089c00381640c51002905e048000070421401d90108404015000a81019140143c0409580c182c0c441d0239028114052260041101c5d00d401c03a0f00c00c03145208010016040c9080ca6103075040201c15000614a0b0b418190003031020703501c0a940030250b814103090902161a11216035107140b266610090a20030040000208820180c508034102c481d011500103842c1d503903200481c2c4400b000c8151001141300058807000b00e00f0014040c3ca85054020403803181142065900c0d101007110845800c0141c0d0000382c240108035800c40200b000903e41c00040141d64507000000c0c0c09001c2a010700300503140048000341c061400c80e000b6000415221000f103585100d000015801540100da5202c0200d05040c00310001e003200c031030058100c40315696100512064103800b805903500284810b128080d154607005440c5106000e000c2c001d01c07003a0011681c0e4526403410302c020300c01c0142034a80541c54140c034041038180214840b0f60 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173555044 1250 173553794 173553803
    0x709140f06070b070305060307060206040803070f0c021509010f0e0d02010804150218090f0f160507021306061b0c05010c080c06040506010806150a0b090f1003020d0c030608030304 79
    0x21108008000c5000782c022040050a071180e031030300748001c282c1c155004901401c825029609999140c800c01e0b650f0b1481a14000d142840400c00a07902d24402d05503d00450000e15004040042d07540018401d445074940142c0d05c85c00c0062418819070b0440c81801c00c600c0b20303081108000f040f080c0000c500b9103e0f80e4010341030100d1140007904000b842c00c070440c1c451402c80c10464451134000300da04051140400c80700e002d650b42d040840c0000322002e502600c91440b1080c00c0703c0079a40c242c0008031a54044600300d050210601c042c00040c1c0c2c8194003100903c0064200041080ca4440000c10540e1240d0a0007280e000212200c00817601900d41081510400c1c28424250301d01d40c500900181324005e900b01d40ea02451003400304200003c54400e0483c0c4084044420640b00c0c601c034807004051050304e03964451000801002403004180141440c0300c80101280081030380381010408a4030502e54005c0001d50001d038070110f02c02c49205105a00c056032504100d83c50811075002c3e0707284070150002e030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 173556294 1250 173555044 173555059
    0x1205100e070314010f0506011e0c110a03210306030f06050c0f07050609100509191b080609190803010605090d06060603020d0f0c051b0f0a1109070914 66
    0x40449800c1040c40000d683c4003164024003540381200e14003d080c000b01700c403085402d19000c6140b5600c20030426081e0550315480204c115200081610700ca058982c048071032003030703101c064a096a03500200e180194041d1801100c500144800301d2b008080d40315100085c0342c58802c090010035410f0107030015440e4081400540c42d1101002d4080c03a00600104c2080b100c0009028000c20001003000c0c1e010702004800c94403030b02454052801921001c40d80c12681d64003003c40c85864210082020440038044c412946600310880880640c0003500d801019165110b0000d010b880c2804002080f0142450842880001700329a0b5408540c40180305460810a0101310b5000075903c803030a038281641c0c00074040000550f07503000900a50000c051420701d482ca4882030311462006c4e40901000a5842e031f40c0c0c0d51511400807440c0709804100080365149200300b640c8608003900402c030295109001c2d0241100411801c0c040040101008000700704000090303130200101c0c1b01c151401400d040e0200c0d2030b007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 173557544 1250 173556294 173556311
    0x9060314010b0f0c0703050a030c05010f0e0d03020a050f07062304080d0905030c07091a060918090f01090813060e0d0210020c0301050a020c121c02130312080a06120510 74
    0x45c0c503148882d0005803840c02802c01010405410000c00311585200d24024032119480526110440c2c04034412a0a56000801c03480907880c4240d000309000c00150400d1410308401c4210a0915003000108580e001e98800810041c0c500c40002e00381a01184098585030b89000d5964106600a03101c00c2d80082b6200e400010070410140261a4080826021602d02690740c2c0c800350060a400c9c0c2c449404241c2680c503190450030040700710b0745900300161150341c080c5954440d04000c0403008017940c0b468015102600402542070040051945c000ca050540703d0f401510b604000c40e02c50790205040c00410404040d054860405100c00540c045544215103403101c24180d09024910f021a54103500e080100042c1c042103a02404070350001c401291000702e504000496503200d003100d11103144540364011056400e40360005c295894503c440d0011a030b50302d507641c00c0600854140c61004c15420f00401080f00b500f0b118490042003010003480e560304068592641f1a000401151061340e2120f401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 173558794 1250 173557544 173557567
    0x102191109060a05090f0f061002280209040c080c01170f040501020d0e1006050108011802130b0409020d0b04110d090512040609030c0905011409090c1009060314010b0f 74
    0x1244000d1601030320b1110380f46440c0411480350354081f204c0315520076401e4003203180340c1000380c5000003013907c0e40c00400c1c041c0c1d44800c030790b84990a8000b0040d0040d010345800340060721a140c1c400d028074416909040500d0030400b1160074040b081c0b140320704201e58541c9201e02c450454290b17507041042c003102c00e0102c0c0c0305c2c0d090150292054105000e20035041142e0f1007146a800a00007034140c02d151010410036442d80011556100207120b84028490229210403030102071740e008150044840c15100f4070350341d840103002c096030800c0d07000203140c40e030110b9000085a114000e202510604032070400c000d02c0c45808402caa4000c8070031103014a6580c28001040103420000780380c0b403a50764400f003a11141c0c0c540e8004c04001c0039000450303164085100015680203a4041d80e81650b40a1344c4620072a1b04600c180541902e00424018070b500c215a5800115211416480015051683c880c0c0c06941442c0c2c000d0107441e440c5141007081403038840100030109003a02a507d0750b410f890701540d61003006495 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 173560044 1250 173558794 173558809
    0xc06030f01120f0c170601080a0503030c0a090509040308011d09032704150f0b0a05040302012106030b16020606060d0203071403130b0a02090114090307170c010219110906 75
    0x10052113144515404190030f4030b8080d0390038074445e200b001c5601903a01c41c00100d44030581014001c043d98070600129052601002c054029000036140510b480c0790707035100080c14008141c41c2174000c40e19542c0148400c1c0c18040c00000050034040705d82e001814031044507580e0344981c1400503580003101881003180c5135651845040494010000d02ca40f4000300549c00d18280644214408001070f00c03400503280414906841c0e4110183d03c446080503d5900192031030600d1a40f0741004203003013105505510400c0c810140034500650b4407030194904805506940040e09441f602503501040410003d07903148012104035030f002c231202584070b803140c1000b034551608500303c40d690400f0110810403609103c9004100b002c1c0900034404c0341e61100f8111600b244103484c05140041c6940b5034010f54042024004d024182c0054102d41c4101e41d954044130b82841407048000703558201d040b44450560f41003001c20303c40807030420b40c0c00c07030000e55a4410a182c0000303c6168010340780e110014200d80d41c0c100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 173561151 1107 173560044 173560073
    0x2071401080a091218050111030f130509011202030c040c17070e131a04020307120c022103040c15021f0e0a080a020c06030f0112 57
    0x80044400e000300808241e07072680c8400d034041c0000c02004080003014280e5441040c0c10b8100c00440c0e00158007640200d040084100c1500300c041404001c661003a000050103030760701d40c3c40c8022000301c40e14540c0017950080e0000000640483c000c1e01c0e00d105541b089065540b0080c4034800c000459013003004003030024042d00400000690b11111540c0c00c500325090165040c01a0000580c5d1a0070403514075032002e46500880c00c50203010640e500c000101100e056045150219005103403810244000d00c175140c84560588000d8000d120500c014800088001048080d03240b030002d240c0d000303030f500b259040b40180300000c00e09400d600c0030302c2290031075002e40310020540900900700c0d642c11004031a0ba50360344699505c91802000031841e40362003019003036280c9002403070283c24140d4a0082c180110010410801d02041e000300003410349400030890214002117040c019411082c12 = true := by decide +kernel

theorem cover : BRFrame.Cov 173381294 173561151 := by
  have h0 := BRFrame.cov_init 173381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 173381294 ≤ n) (h2 : n < 173561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
