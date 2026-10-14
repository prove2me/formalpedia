-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2205
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:59:32.896158+00:00
-- url     : https://prove2.me/submissions/151e5768-4e19-453d-bbbb-814249cc9526

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 396402877 ≤ n < 396582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 396404127 1250 396402877 396402917
    0x8070e1c03030f1d0a020a06020c1e0d020d030c0b09030906340b070305060306010b09040e0106090501170136030c0b0a0b0405100b0301150e0a091b 65
    0x98001400c06842d8007a122101039181c010182101c4829071911080e5102c01e01e01d0b5417140b086108a0040381c00e040c000a1541c00030407240b85a55000c6e1242110404601c04042c482c41e401c0d04c2a84d20103820b036400700160f15041c0020b81c065100742c9820101c10450f0a11b01d01140d001010701516502c100054079603901c03000245c9480f2001d09240300400e11445280c0c010301c90f111101c60820039200c3c980c0b5801c0c410f00c604218050707501c40d1020010b5440c0c031004d150301e03030b10f09001d4403680b002e081001880e1030402c0d900c8500d1302c6031150300001c0c4c0c0540302d140c00c100303548003a0b11071502c151030800751132180d8000b84595051399200041240e4620100303910390820940210a021540309010250000e0500840301c4c202041d5104240744800d1a12000c1d0000030b001101025000308c0c98100001c021054800740ea030199258201c1d01810f60780f030b0681d00d00030303084040d52110400500184609140c0c640400c80340c0502050300380824808003829450b0420110000d0660402244c1002c03440110054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 396405377 1250 396404127 396404179
    0x612060501050f16050114060901090c020303060607030509130c021203040b0109021e0a0f0f0f140c010b0604030605040605061504061d030f1605010914120f0a0308070e 74
    0x4103e503151502c120030600c49414031400d201030303c6075092032400b141c40591003134518466182110b0354505642c07038520700b01c1245c84107420b4001607801000401e1262403c40c000c0c1000912078500545402150004603040f1138042e00b8203810b041e2900a100d000d15014826050301203180c0c00824190b01d810740398009558418854103c90a13400110555500d00702d0405143d54898000e140c1d945078401000103050340102c411900004002e14058903406205200d0707000007210564510301d50700610812888158000c1d20070f6415503580c0c509041890702c0d81c030090310046006100000d018605400c21500b0380324020640e900c20f216880d94850708170400c03001d8505845551924401417002e0b41c0140d9404800030741e625a062088040044884000050765104005c2d112080344145540d00d00564107074400d8040e07426507866025921006080c0b440d002e6006a07016003c490007001d0b010942c9044c80304d0b014080d8001840c000030400c2007a0081d110b1412010160b0741c50b610110347c004080020441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 396406627 1250 396405377 396405397
    0x10209060708070f120c0611040303080609060f030a14151003060f060504050f0907050f03070302090603030f0f0c19020607060f0b2116030203151305070f061206050105 74
    0x201090304001d0040000e90403136131395400308078490500e10501015000d4402040f080b41c070207040a15403201b000c1b844040da0304072981501c400d401174444008018409000916507074201c2c02020a40341e0503501046001d018030700907544074010444030003030303039040444940150001d01c08a01c01c0c0450412204004021660400c00c0041c1500626070800c2c040c0c0a0b5500c0154400d00b00b02c18450396100c100740c2580100f1843d0219511545e5030401d1004c0800b40600407036040c2c000003810009810000720003030384440c00400307403841c0c040103001e4001c03d1f4101c9401e01c100c4c150007040000c1005400c100c1024000c000e4240039402d09020b0380012030038032030703142d0007854251204140c407410501604582100c0c40d0061800c0f4a0280c2101c540b05010002e80e00355440d40700f500355420000031000d00d1330081d41d40141c080c0488070402e41c188900240d010308107501c00c004210b190b40c0442d0050000b0805000300403c6a0512450300364010911619007000080741d510703007070080041e6a0060202c400c0444 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 396407877 1250 396406627 396406643
    0x170a02060105031c0f11030a050901030b0306220302010e0d09051207150e0d200f1c030507031205280218010f020c040e0307061b0e0103270317090102090607 69
    0x2017495822240603501c00da400e05144004181710b02c621360090043c3c84100401c0c0c0c1d0801034021400e08040e81d4010664140114030340d14100c1d4504521201840c203035070b500a000105240c500395a400380350400c94402400003421500b018011451300d0303020000380000820003410000d0900300c64200c8a0f0030501d00c0400d0148842000309991244065046c1c084d410450403e00101c0c4641c154480316101e00c16144110b00001c0042c04070328103414007051040030050741c500c641c4150355064030b041e480000140c00b40100140300c40c00c66040c03402002c3c443d4200600c00e01010185036040d80040c4107606041c44c100c0d0051000c0c053f254148000b501a030242440c3c10038045101c000140d040042461046800504040b404074a2800c000004d010342c0348921010400c0c420342c2c40034148604400e17a0064005040380d82040c14943c40b03034005580c4801c1034401c64490455102d003500402c514220300310046080902084c50648401c0903003540056008000e602e007403400000202544a4048000c0c10701c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 396409127 1250 396407877 396407897
    0x9051915020a0e0d0302010f050108010e0a0209040c0e16030c0e0618220209030c0102030901050a0513090606080411061806030c070b09061006030b01091809170a02060105031c 77
    0x1d11800c84205403400141a03861001c404d4100280644581100000c0540c100400024000c10504c200500d04500e04042c010010442e03082140411000d0421340c1c0044010201080041e05001b079907000b0401c11004040300c00040c84c019050300c1c400d800f07100501882007402c0e04142c0700c08085840908040d8034a4505521500c001850f10b90541c1e104881e11420035184c1d10824511f40c020101c442040f0212060800082c004a03039a100745005980020300900c00b000d0700c180560090035103070f400d001c02d05000684404500c02111000e41c080c90000720458180820300c0380000c81101840000d6603010304d02809c4110908141c640c4c00351582c00b900300000010b900c414013100b95400340d5882a8080c4031820a040d1495903501b050391680032a04a1a000161140c000c1c86100030030380040e140c50000754508070303443c1c54a4811803501c1616079220019080003412200172419621607420651381c45a400345402840c05005070403481c0a580042407007818040d045105503c40b4085140040740c030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 396410377 1250 396409127 396409147
    0xa0e04050a17271f0905040c0807030b09010e010b0708070605010f0302010f05040e06060f190518030312010b091306060e0915010c120e060d0905191502 67
    0x4050200d0010740b2a0714412048460b40e0418001000d001d0704010074016028005064860081d81500d0803903400105584207900c40490503610190b40501030405080c00ea036104041000c1d240b111611400007020801003006150305480750f20007802051f6490700c0740c2c3d07042044000e440c0c3d00c103010310510041c01198400400200308110380354607622240a21103540c1d102086940c005940c00704030701080504070b402011a1060090740d080304c0440d0b420000503118002071105650203091080116002000702841d04940f14045508000c9203070340d01c03595801c01c200e82c1041c0070817426855201e50810840d600900d003014007c2411354004211050744c4088140000e0034880880340315120230b9080c4200090980e4012244030030548066aa540c0b03a40d5807580d210f038501c1c1e03400241601281003144181d0106000c948032081c1c810701c40c209400e200d400d40b40050225006100f10420540c2c85200c2c10f020040103003e150021111302001d10241401d50b07568202015900d920010110341c040740107420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 396411627 1250 396410377 396410383
    0x1a150d02071e060b0d08030103030c02010504031406070206060102010b0603040b0c0403170d0c1e0f030e0304080c03010b040b0a1e030807032039090c0408010e0c0a0e0405 75
    0x180a911482c881d0486480610b25041e0610a1006544032840c00c8404825818003031989142240d1100300c451841c1c2c2941e40c16254042000c400360b0400c20b09100100010356000c2e11420200d80f031000402032031901040003403074104000c040604590400c200f6024035220501a607400c00e171300038036403881951000e050304141d0040b07a1024080d020072212080340c20307001400403c105810b840060001d0500610140c4040b21089031030030600c042c8044d0030303010610901840300010100d18001c10010404030b9030038519081038020f103480e03411142d1140d81601c0c0900c02c40e54406005c4e1401c0c890303c03011f40001068444c481c4100c90708822115a61000c00514948a001031580010b07031580380c1d4100e00b0018050f1140301c62202c009521043c030344404a01c001044045031403980000040000d0240c280f0f50352000d6047c04145858050b100f10f20680c0e10040e107540f0807403040358802c1d03e031031a00000d6802d44a0307035500a01241c202d03820550341900c9a10001050700d44115402808d0703111481c1c003900d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 396412877 1250 396411627 396411637
    0xe060f030304120b0f01050607111908010b0901120305040e150409081209060f150a080d0807021c020601260105010f051008061c020d150606031a150d02 67
    0x94540400540421800180c048000c2158000c4c0e00a2a40780c2c0da818400d421074100703000d09507008034288926000544000304035150315074058007080489000000440411040342c120742440d9440789031a004600f401e00a80340140312106a10b030014141d5100a0328134070860144c010300d9110140007c240c000003508950001d074001c1c200b0403600115003000030313081d00f144810710906481c40b00401c9002400043e068080e81034125112560f4440d00c0c031b01d1108040d00d200f00c613000590b682e000034148209002081c001e8001e0f031103e803000d01d04000c1c000d0030061841030062201004051105040e035000952506690340b4070140103a0801c40241c403c1c5648089a910306198204000491541c5189480c80b04030340e13046c0c40c00e0300d2a10500c4400d480101c400c903042d541010288908507100c80f00032941d0700e642800039000c5c042e100f0b450f403507410044c041a1940c80c400c0340c03102c0341085071070392502c104032100280c0101030f10007941d83d00014005851000b442802c03003801180b26429801c0c10380c1122 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 396414127 1250 396412877 396412879
    0x1218030d0c080606070c050103051803040b07170304200607050d030c0207060201180b15030a0f1a0f04030c05030405040e010603020307090c051903020d0c0507020918070e060f 77
    0x35200d00980c248003014100c1c104041d800107a044000c14060304166041d161102d0b4080540041075051000440080c440107080518546a58070b8803a0184418002040500303100340305255600e00034108880719090152001d0811902042040045030020800002d5110207000c5060110031400c00540300303000324000588503009410801566542650284640f40d400307800f076840407a0307915010b0b03080300d61080b80341d042c0196010704074000940c0e100c019a402400c4110010042c691000440c2c07420130301038421140c40c902c1e103d5000a110000d0007000d484812031414440c02d140031040c84a1003107020b040181403060174602801000402e005440140101400801c10940c90403140c602922079840142d00901600a0100e1720f8406401807603c0003403a501e034a485c04282855030500004800f00c0c0f0700400d41d00b80300a009042603030054502410407039503100c0d00c480507401082640320300506114035428220004094005c1c0c08074a00045a10f140706900150fa42e9401188804d81540002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 396415377 1250 396414127 396414133
    0x112030813021f110601180e030f0408070e06060a05071112011a0a0b033d0303030b03240a020702030f0303131707020a0b0913050c031b0f1218 63
    0x448601401030010300c3e41400b0ba551300ea460306401c1003a5240d8400380540903601d04160300701e400034440d5402c618040c410010403280360103116a020190358008e900013034030603080300c0d0007004641c0d034254141d41c104001f00d0b0400d00e4901010400760441c40b810500a00003070a240000507241d80e204070080c4460001c4000b4803052201680700400b09411240c5103104001d1940302090440041c41aa4481c03405210411030400c2081410301d020f8156150960003101d40310000d8042404400d0814000c5100392004a80303c0c12007000c040c00c0009820001c0602c04416030301550000030000200c0d001030324210016640c91a50001c01c0c100403181d500b0f12103d100000030320094080880034641e07000e014010710011354603e00d102e40040e1150f01006540807120000034081045a0070041c00c080c0801091170419a903401030f041c065074021a80c184000c81c0103c00c106004150303c490805001c46448d071246082d0055032540402d018070040003992a401c0000a4800e1034505101c40d9000186030403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 396416627 1250 396415377 396415399
    0x7030207321605010513031509060c05070209040204180602190f02060403171503011a090109020702060412021507050105040c050907080a200a021c08011203081302 72
    0x26030644401c00c11075100465881106201c0300c03001c086103450309a1026403001c840350b403403c001121242c10405294010031242c060001c00200c042861840c0444407100c041070b4241d00382880000c561070f001140050143c10016400103039200c001441d80306034101d50019030440195244501c14400c1480101490320024680d1182c04020b890340f10682c0c40c55482c00340e00300306030324102d850b24000d0320028041400c081c208180d0b29941250b00d0707402569280810001108000007038207450248500300c4030303024280241030075400c1060b000382c0580342c0c3c40401d42c41c1c41c1c0347c4d50200381c070340c4102c0c42040201e4680411080071560b41c0c1d102d10b20518002c1001648030f4446040c99402020260307400c4411000300035000036182807241505201c0c000d141c031110800ea03680c00c690409003203071240d10388160400114090305075074040e002e840da0300d00c59401050b100d141650b1040c18041c05040b00014072403c00c00422400c50500d00c10412035515107850145604d52152005020f0320405000b50300603d0024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 396417877 1250 396416627 396416663
    0xc09010c080408160f080a2f0406030b0a110a120b031212010e1e070c020f060d02180d050a02190504090b070e0d020307140f0909011e0209030303010303030507030207 73
    0x41080948802d40c40408501b03989403482c542d40c41d0542c0d001849030021a12003402141c407503d107070445808069100c18440301c24130005080f42c2c6c540d0800c8400c020714406010321407a882c861207401618800c9018a0410840806040ba40c09001e080e4100303034841d10700d01100e4405125140c3c0d880e2402c00c0e440e407500c01010303e042c0480d00074020400008046400030304880385000d00300000c468a00007403655a110040c04440d044051a03051340c125440d8141001c82d41c0780c560080048040700b17000161a92604803c005030300d8180b200741c5208024104840d030100340089104001298101c84101071f1410050811050a4043c0d005681c0039181a80441c00d00c0b03403001c0c0321403180640e50303240100030303102108105842011400280d0964081c840503c40c0c1c010300508142d03071600040c04c0c400b0310301000b000108420341c01c07191071400d41d460b0203c45451161801c941136100c1e080300015400c01184e0800300c1d40c1c9000520028042544802c08101042d001c1c1e41160340301034009020300c44600c030000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 396419127 1250 396417877 396417913
    0x14060916022503150603080a080a02072406050a0b09040c1701080d0f0203030f150a03080f18030303010806150103061e06021608120c01181a06090c09010c080408 71
    0x320060b944041d084c01d002000c11000d210300c50903607900030362440c01d0620303c4008891032007004000c100030315820001c01c00419801e044151062694074010b520503d10b10001105407282ca40c0130501030321b0705501c00c2c04810140c505540d0505402d46002910302c0300405c080398001250340c03041442404c0d1400201d41d039640410780c4071180190761600b10b42101e0342134041780c0d01c0c4401ca80010b000d640e02804070fa03c0d150f40040b0359212403402070146284680f0b988500403681d200318080d003070b01000054101451648401243e001c200201c000d03500399854940c2e043c0d21003000170a12180c82160032020740440e8026071282001e0400034040c030940e81131141840754030725241c5c06600058410000e801c44030103070320203024003030707031807aa0291454114200d440030203600500305005265485500086541c49002c1e04140d00c9401042030400c80b102c0106540d01c01c0801400710f5000d60840d00802030340c404154229081902c081ca0090810b240505190042e4019908055041d016010041985601070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 396420377 1250 396419127 396419129
    0xe090a0201020105070f08040201180803040e1f0605071511030403030e1b011b11060309070e01080c0a05010804170a0509030c0613030237060201140609160225 70
    0x2c0c0c0081103551203c00c1e044d0740410204a8150000d4a4140080e0055100381b02d1400190b1241c0c00301c0381d0300c03601e41c2043d0f411508990019501c400c003200410511000c020f001088146803c810921802e0900000404c2807041d01d00140003a0410150b5940702005036000048411084666507101d007460310b0000d0140c0043d00d07a0001e241303c2c5400040e00a40184a840d04101c1c0c141c440d090041000342003030400060340724043ea40c25042146c0403c2648403a40214441c64500003d00045802c10840d407100d5003042e0800c00350f590100a0340600d41d100c00713018109940e000d09000144d6070326458200c000b100000483c0103201c0c0045000500160004007034489100201e0640318003000310000c1c040c540c06401d1003840d030948010010405402c14030303c071090411061601e0300d20168041c0c4098400e01480703081018080c0003c1003042a20390a20075001541d04401505140b401c181000401349030000e010020b40660814105004034000c0101c001200c11408002000c0003a00d04541400852 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 396421627 1250 396420377 396420379
    0x5070f031a091b0409030504050418050f011e050903090d030201050709080a020307032a06020601030b010504020909010510050c16060207060c20120604051b061e0c070e090a02 77
    0x644000c0381440e44080340082d65442d000298201c49440d260030130028009244007901800f40402001c119602d59024401c1120343c092134900c810381039403070181e103444d00702c0d0300164041c1d1600c8585039490180c441c003600d81c19242080410191100032403d420352280c0410254400c072400354100c00c1603010340001e4800c0030a070702c615200540e01c00110751203100b40c660095154200e46004c0c000a10a115640505109a0380e0362611031071620703c8003400109500144050f0740b0401c010030400900f0f480150241c0020340d815400c6c4881d080105035000f906011382ca00c41c1000c03070b0200d40803510035030586401c5111401110f010082003608610856428002c50005001d81d100100d2050f010b042400e003502d0b4440014030514944402030107082785d2441d40d0a034020554828004051020000e10f4000d6000700003522602d00a400708201e10346141c0c0d880e5025100c1804800302c3c0b402030041e4101c018030700344006640c4030140c8080358100103c1e0303045112414030000c14030000110000c4c10360704040c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 396422877 1250 396421627 396421673
    0xb090f04450203030f0d060803032806051e010509040f0f06060203070b0a0e1606020105180d0504230d0c06030f05060f0d020307080d020a0203011506050f0705070f03 73
    0x111000c100e120500841d00060f4040d802007102d40e1461480e14001c0c40c50542032080041e009468050032403c46c2d00c25140c0400d10307089042c1c40d1180c003000e1203500c131640848031010072045290202143c03082018480c220508034030212034241c941d000f24100d4100d214001c0003001340850b10000c0c5001071070f511000313040c1c1e28585080482d20a00000454410a0300140c00350000c0d61103103030100280c00101c80380403443c0a80110f04100001c400801e002410030351b0000300712031426611407250203111081d1300600d40c1c040380c14060a00d400400326410b4480550304540440703403107245890a040160340c102c0d0044080140c003410301280c1802030703065500c6950b0078401c900b00e01810005035a8140c40c150390104151090201d03519180d0100940d5920150540d00e40d65550617107642062a14442c01b80980c02085400085250a12400c1503010710303011120780890910b00010300300d000d07134201d035207441d0000500d4000340441040b00100801c43d240c0c0c0d040d030141d22482d2031600d07110000b8003ea2180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 396424127 1250 396422877 396422981
    0xf07080d140406080f040f12031a0102070f1401031508010204050a120203030a0807020f06010806060a0b040e0f1b0d0f1d0c0139030206070503010b090f04 68
    0x807408021502290610703540d448017070701c0d240c022004103280a007045071284905409403002869070303072200b501510705840014800b49202180741e030441c941e44006045400c4032409001e2100c10341c01c1c2005607950318070007031641400980160000e0143e000b00c15803411034401e00046050301500203006441d01640c617005c1c0303240d60307a80303101038007021002c0254582c0050000210492180740881d5010342648100c443c9000007680072404c1100030f80040303800d500000c042140f94103200c02000001c1ca030b4890b00e42e140900c1c240802800d502c002d4244400c01204001054800c001528413003a0841c4503502c9c4d0b0b075074030b8611800900812420305002c81c1982080c60100c0d00c40c9034120040c6582220001030315005407031030011070320000040b000840d000b241d641d0a0240c10030547c441841c50090105120f052015403c2c003a29140300140345604001d0100f0050080110000903a01d82e540240e4002c03000d800c1c01400034002e0f01e60a80018070f45d6a1001c002c0c83c8610040c5041ca4075600880c4240401ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 396425377 1250 396424127 396424157
    0x2010c020708070306111b010b0102011a01020307060c02070515090f0f0105070b2d011e0f03080c01020714030715020f040515090a08031305010206070c020405090f07080d 75
    0x9500c144500c2c00c0540000a00b000840c0c029004403840b10b504000d1140362210b0883d4100352171245411200e2070380c0d9968558074065809100703503004086040d260342034803010500000e540b840344c48002040c031912800da800106008012010140c2402030a455038801141400c400f550030400cc2c20b0720481441000642a06205c0c0030162011810b07964035241030080d8480d8500e441002d040d81d02e46480b11032140245522842006034a841c0700700202c402c82d4500414108030086210b40f003c0c0c0d00e49000800c00c0710945601c2048121b0394060103881e11520312039111030082c015407030050500c00119407444900f0030080014072009101c0d1021a00c803c0b03c00740c1140c100e020300503905220040401003844186800d170302c4200901c0c21000103d14100310040410060340d000c0c1c1c02300e0f20690020602122045442040b140540305c00c1c03000740362614081d103006080041804000e40a40d0741c03400858081d02050114000c3e060b603130411070b0f41e03175952800d640e0b13616259090581c0004607506040108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 396426627 1250 396425377 396425383
    0xc3f1407020d05030f0c031305010c121d03030f040f020405070c030f020106060e1311070602092103070305070201050705010608030309120f041413091112030324011403010f0602010c02 81
    0x9494900c10000b825a10400842e106e580050211941210311828175400a0824001c5920066103541e52035466064003960005545950304803103085107540030b04070400c1c14004217580d4000071409000d02c20b40ca403414040400051803001179042810b0030300304540300c1e81201c4100c8580b0722950f40d500f2075000c1750300b04900b00c03042800365000052900c0e8804c041840c3c002c203d0f0003e194000700c0010301d40f000b142c0d04401544030b540104e07801600031420340310b50301d411000e6000d5250441c0101919006c80b02e001c03a164800c218005082c0417010600c081564483c90607101020790105c02005111f0305c03030121941c1e0360001c48025030903104441c503034000c0302119001e0381c1080c80d6105c80b00c2d050a0038012121003443e5202c0103e83c000000000d041c081d5035050040545442c014003c200f0510030600078020101c11149400e2100d078070400a00c01d98000c140682404819140703080c4500010f040c00483d80350044215000f043d41020001144040502c00e00718102da040da0000c0040141945069803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 396427877 1250 396426627 396426631
    0x503120a0509071505090409051c30141003060b0f031b0303070b0f060a050901080c010c0c05060f09090106080405060c1c0204090e010c3f1407020d0503 67
    0x1a03030300b01c184108200d4491005113907003104581000c606017400707507000c03070300311000c0b51015a10b03075100810340500110200a02c020701c00d01803410f2580b55250142010440310741034582038428008118400790403250340d100c200e440450003048010350030400c450214550301c13030005480c01460210222580d2405188a980350341c0040c003d00300100d008d51f01407000c555110452505804200080000241a5402c0901c0344400c1d18400c01d00c1c1c14038001307018441c1c85d42c0c2c04c1540905103800040c44201c10016139a0030f000000d103010742d4008010b14040f100c1411503031105403c07000200e030200c4140481000741c00100070548450031943c0e40c0d803908031181c800503540030b0908c1d000307040422441c999a000920180c0c44800b820140701640c05d45c013804903401a800b080075581d42d10085c000310070080c020940c82c25050314000020080200400c0304551030038840c0554600d8100c04280180b2140c007040c0c548009100c410031910701c642100b000c003a0b90484040006003d540d110720005406441a68 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 396429127 1250 396427877 396427891
    0xe030a0f12270b09040b120d020706141903091202070303081302090c0a1803080304120207051c02032d0d170a05041b030303020417120708030c160503120a05 69
    0x2d54036900c1c00e003c0d02500c2d071003800c400750004d4440001d00e102da00d070204100c40c4c0c1c40405008040448902c14000c4c2000c1c541e0b0048000c110124030341c1140101c1070020754401c0350341c40350b050164020703544042c1c001f4141690000c21030b01c03010810b031003141e0f00860f100003100d0207a11368003000c1d40c41c46010a441c50044100960040401002c01c1d144c501031800303000401a41d08021003188280007191034458015442212650800800c001c100041d00e580d44140c4482c0380010720707195050100042d82d6144881c03690a60000740c83d12501075503400c01a403a9043e1100c000f14110b90810811080203140030300008030544501618000103c2c8282c0c001d10701c108408402d0b0845868512204000c1c100142080e0761020021a104095410048015008600c6501d00581d214903011170003510900c0100000307803e8004071105d403200f0b604002151821a070104c0300503601c0d0303242140e9058500541d905407078044002000719042100000003041542411065141b00717980c0c48002c079055920494100c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 396430377 1250 396429127 396429197
    0xc05070e04031704050a1101050c060103020f0103140a090204150b0a0507150e060405061302090f091f061a0418110903100f0b01020303040807030e030a0f12 69
    0xc0110040310301085070001d00c2460300039580641c0160f512440381080d10191465040b492000c010001c0710300c4541c8000400f8240241824590f24a054642d0014400a8002e4009050741600390703121350b08c10401c924100811001a0505003035030303c028030412008900480c581052044051500107400088901d08809207103040d02d03d1500302c495401c0000b080300c2c181e0303050340e800c0c0c0001c5c03090050510400041e4001e1210349003504025240020103804035512244400d507130400343c0c80c1e206180d64015041d91800703c19499880440349040d0300059803904005589140184069054100f003049610700d4008a0300a1040c1900c0081d03071245208032300c4082c683c0100b402d846449030f0444864200011002c0341400140310103c0c0c203080f81801040c20581e07607518244030422061040320310004080c0f000754110315281d038a030603080c401c2400160a020400700031580d0742d03408110000825500081e00d1081070181c0c07500c40116152100d903000440c000e1005042e00c80d0f0300824048944891040c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 396431627 1250 396430377 396430379
    0x40b100b04090e031b0307032a0f0c05090709030303050703140a0902150a120e03070f0201110a121e0e0a051201020403020a030f0203060708070c020f0105090909010c09060c0507 78
    0x200500034040b6410003c2580030901000914098020010050f06940f0002d107646103614a0000d00800d540041070035044004c10310340303403070b92140c84003144103c0d4084c2c15020030309241d0600718044019640b10503406a811001c120b001036020114500300c038460744092007030351581942034054540d00002c210082200100007a8004040d80083c0b4400d40090701e549560912442d42811f258894100c55000c260030004c658054842442a80c1c10113146038099030500d40e06a80700c040d4001e0140000e410002403420800c101c110134000180c0107644414240d10300a864800640110740c202c0111007058113034802460420b00030303000b131100720200802c60b16981d4100800c005a8041e903c00d243c18035075080c40b0201c010380f6003090b804061070003501b0f9829000018810949030920041c0450100458030092203c0d00d5042840f190300300341d0496503d0520708102c80101c4040c010900d01ca40d02840000134440c0c0c0b000706611030016a10a0380c1e414920b0364943c43c068030407051a00e4010302c103604ca020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 396432877 1250 396431627 396431639
    0x3040b16051207021606050301140103020c0304080f101a03060109022101030f120c15110708031003020f0a03080d1a030d03020c0712021e030c0301060e040b100b04 72
    0x21151500c80c0041c00d14504104140c15000040741c021509000540d02c0004140311113841d44409030010102450200c1ca958100011680c180e450003001750305141d00401c0e00005600148195000b80000300102e4010501d82491140e803056402640202c03e131800001020140440381a5240890058000c0150740d10300507100000750701c150400c3c0e5006d0785002c41d240f4441407060000703000314000c44040529100c1c6007440200c071880030030800103003c020250000007603244141840403500d00400041c03698295003903a2218420303200d0082c4500400000c100c1e81e007685c01c0c004402d0b2402a42c1c43c407401000c2030140024032a80d400064010741046c00000e0500620741c000346200103d0700002c000c44000c40001c13030300c5d21b800315402c0408240c021540540f136250800c8904000c02c08000440b40c082c0050300451480318003421407201e04804100c46400980f070030000a800da0402900800101d5500d07104004508000c0d20300b182d0300481d0001090414891a005c0420b6540d4240203e01d000e01e400d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 396434127 1250 396432877 396432901
    0xf040e06040f1509031809020c0a0f0201030f020a120b04020405010203090607110a15032901030e0a170403150c0f0c0f0602040f05010e032a011701081e0303040b 71
    0x100c401c41e203480140481810f402d00700d010300710007184240c88030038010404040040402c03409400000301c1703501c140030054125000050420b50280c1010003a0400029400100e020342040d0301003210f8680001500b20b2007641c001c249500c50300c100442080111044030402040c0e20907445024010317441444056454a8148001c00030300388034150184100412401048141e5030035406031400c0d0b01c603007031580042d03605405280710040a1100c081003541102c2e01c51443d1002807207500b03041640c0e41413441c001c0801044070030000d030742180950342d1078003400e040030740a90302c83c1c00121846107200300c01211148403401342d03441d180e8407034843c090140e40050046440c040c28036001e451000c070004030140450758510040000e09241a01040700c2c0c1d0400c800500308071000e031181c9020f03030b00841c030007400e00c01c01050940070b007400f00c44141c00205183c0c0040f2241c83c1d0405001c900c40c0404000040c4e8000c2c0081c4041c824681180ba55880340304180b040c54a0740000c460150107140c80c0400a140602a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 396435377 1250 396434127 396434153
    0x21011071403010b030106091e0603020d12020c150a020f060c0f03040c15050405040e030a020d120204090f090204050711060c030a020c03071a10061e021903030b0f040e0604 76
    0x2e80006030681c4030304002400d6906aa0000540e42da48102e00d024103080042c020030598038000d010302c0f182d403440c0d000c1101034500600140801d010303903130f070f40c0e2800e84240854000000002e02c01c5041c80c80350203030420326600c100c1600b405803140c020b021128040101d0210f00c15a41070400c01d06003240081000400e40c0020f20494200001000c08a90416840a52036900c0c0b5280d45058645007800c00340300888403641c440740c44d507900a0102c0c80c5800d0b80012030152580044c9442000c082074021074001034092900300001507410040a905003280f55440120600c1c000c840510058807421820b44105019004403d6240c120f42c0020720348007100e400175500401070a40041c9404040b030b26032030658021503030403182d03c0f659000a11803031000d55040e40d002070301400328284480c0f90003409040071400d0445440da4500c20400e102c0080e0081c40300c6880c5000030b18503060711001614005008002c410310703061244640d0003844110f0b0501388543c80c07414a864008040b1521903403198142c1ea40d003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 396436627 1250 396435377 396435379
    0x11090d0203030403150905010605060c100e190303020c01050105040b0a120c030c090c090509070c0f0804080706200c0109230402182e26130210110714 66
    0x4100400000261040d9292a4005c5a80f4000518003614507185080d100e0544c81244554424880d1a140351000310710a8500c01415100061001544600c04d04000e440f00054a01c9014000a44241500740c1c00038000c0300381d41c100130070440c0e07290340401c41110550222543c00c100d90590070300c115000003801c417440d04d0040c0c00000d202581c17580c5008885207981c10242d510340c0c42d02880340c021a0845030543c054601102d48221510f0304031401041128140000390485080c0014dc60621031400112000f07071849905460070035445103000b4044030b50800203c04562110300c1e01c03a1106001040b14a00d00005a40300c1c80464a0650110f0600d10701c20303280403401c80c040440076078980d6148000c18950100740741c003c0612003560100403480d981c44070a5030300c0d0a51528181d0404841d10110840c0c09101c2c1003002481c513071240c400300142180801480740b91422024000741224102406030b10310b2003182d80c01c00000d06444201c0e0b007100c050071200c1082d8041074042c01400d0304010328040801d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 396437877 1250 396436627 396436633
    0x1060504050120030301030f0b0709030201050d0b12330601020d0f020c0a0e0702070501080408070b07050f040f03021c0b0117010e031602041112071808010e060a0501060311090d0203 80
    0x200f2900b03640c00e640c0b080e407044500c0340d50120b0f29800c01c01841030040d8020803a00b00302c1419880d50300081d000388602c000c107401c015540c840108090f0703103c81000d40380610000c11506100450000040c0115104441d819100c001d2038000c200c01100c566079920031035040c0c0c007070b200d42020341d00b055407180310074007180055003c1c6151a08464440d5030f000402403582022843d101d06040a0107801d000c0550409130410802d00304002c00312f400750084642c52544040d031441280e0b20a0000c556500801d825030005103030020780010a01a154100c405507070085030045000403011903e02810703c07241500030485540c80740100036080400165020108600d40041180c80300d44690b0390640e03010001c496510075070000ca035410340c1494070424071903070307030f0f0f040e6040c40c1040000c22501c07154801810754041115500c61072003904405c5182100a2051100a0045a00c400c091903180c1c41d040780c074458658501b1000207800361280c051020128103640ea43e6142007481c030b090202c002c0c104030082c0e82600c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 396439127 1250 396437877 396437927
    0x12a0309170304051c0c030219020d0b15040f1e0b01050415210603031b020607020a120b090c0a06120923010c02030a05030f0612010e0a0b010e010605040501 69
    0x207000c000194410381c4280042c10940114140d119405041d00d1404002c02100c1803403440017940014040070194490100303402d44019078800070b030250340c80040084c5030b07145960038003226800620a03541381030000c803814000000c80c054140200da078609940c10055040009099803000150301803110b0400603d00b0500d001e40703416603030032100f1240c80c06100042d50b0b000340c0c0c0d5882c1441007040246900422003403100500d5500d000382880f00360030b400c0311031140081c803040455884004036a461540076011160482e600d081041c01e002c04240d080c1c8020040c0030025000500c041802544510000c202104680c102a412500183d080651070b440964605164011903954600100b1900f0034106041351000121000360a5400b1b2007030010a40d4801d106582506810006903030740240303c1514640169200000520012040c4075444a00d51038001502c940030300c045100078516011b0280b400c030690341c52014003070b080c1091155800150080c0030a12640d8441e048482d012000e28010b100b0720 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 396440377 1250 396439127 396439163
    0x2010e0418030339020106090c03060824070c05030903190515090c1003090b04080405120f0604080c1e0d1403060907031107060203010b070203012a0309 67
    0x2214005051200c20162100754000c055050041240315210588403031a030412011218810384084418050780b48112264000310610075070002c0001c1c030380d12006005060f50303618098001e00c0c1c0d80c01100a00d0042e100c01c560032201e404202140d00c03150341030507030300d42d903030711b40112900c001200d41103c20703001c1041441d01640d410080140145690f405e0810800c1041c6490351404510b589017280d0f0030040401c01c4103082000c6100c20f10001e007a64070703802407007803d10124001e04400c6070003010800488280700070f0001e00809001034031426a41c01034001b011180f104d40e00c1d001c0003010501e6a0080c00082c0020301c00401800400383e2280c01c640040701c0300044003d00746946018030103640c2c0a41000000903078081544503082003d20380c1c00d455400c00e18003042e5001c4005080f01d09141d1940c0243c0303c034032804411280f07483d40251086407696150024110726a0042c2010b13441796003002a41e000070a2910208400000e41e00c84460f010b014030700040d800f07060002410345000c00604c01d00245 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 396441627 1250 396440377 396440381
    0x5092104140f010903080a052a0d180603050c07050312011a2d09060d0b030127141e010504050c040b0102031e0f03090f07080d09050103150803040305030a0909091e02010e04 76
    0x300d82c101401207209d103001480f2483c40c11400c04600c40c10000940215800c81d03076148120010341c1c403a4a404a41640c89003140c8071b10384103905004204e4400018110b0290014454484c1601c0980182082e40750003010b00c1141e90003449165901c0400119031406546050788040e03a50340d680c0c542042c140030307103a00041d085800480003800c14503140d00050460385002e102d00d078240d442c0b400f55000740351000004a941600c900740010201c22100c010340c0f4080b030b410858810841e12400420a00e1403c01742c005018050503242145d280c4175043ca0100c40c5d01d0f207402414200c0d401a4021070074459109402006c0c00300301491410014820170090303010f10b8901e001107100f01d01400c000d050690501ca40f0503d0091941c1c400358040c0c0041c500c0c0d0340660b034840d0884084072000d190205229040390079800c24442c10764400c0c00d4a106c0014000700f044008809840401c00c6601c1d41203c10703942d82412400d0700c1c10006e009110740c00030910204114a00c2003000300079030040c901032000081032000f01c1c4c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 396442877 1250 396441627 396441667
    0xc0c12030a0b03030f0409060b03100b0a120515010e0909120d0906050408120906010302010e012a140d0206070206070507030c12030e010b040e0a0605092104140f010903080a05 77
    0x2070707900c00141444050301f1802200024510440b07810f00e035290044c43c2c0b107400d00e80790240c0301d1014800241a0300151140c40044950840100208800d0500c4601d4902c07400341c900076207000c03450240c050302c141d1604040452103401454007501342200804044441d0703600031000a8070040d5907566140104140303216081c85103110711040303580c0e0540f0740d036100c200180040281c001648002c0c01480180d0388400c10b002d8283c02801c04052112540d81c00600301550304034901d203102d202c0741c0c80d4400d1100040a103402405070a05641b92a04000c034200e0b1113000494480c0c001d81d00213070220302d14600c26401414140d0027443c20310460103040d5500000c5403140d400e0390700040d4642c1010800c2c080700307115140000d90129020442c4007042d4488a03112000078201504050f940d40005c0c001410500c107100b903000021110316070848840f2910055a0454029580d559071043c500c0744480c00c00c1400b02c80314031816126603507014035503590300c0d49a60000307038418100700051104810514440c61074031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 396444127 1250 396442877 396442897
    0x9062109030c0c42080a09020d0c0510080f0412030e01021201030606080a0f02130608030a0201020a0f08090a02041a041505030d2c01020717010b090c0c12030a0b0303 73
    0x414600d9001908036080240e801d2409054400c8102c101d0340031136402511020b255141406000d0ba41d82014400042c0104880a034214020081c100100b12000090800392a0304868000003440288011586114200d48800e1981d20034804075002c100d180382c0ea66148034907840c1c0820401014562142681c228104041c06812004014410048103000f1407028264190051010f2080e503140e5884070403005501a001d02e048070003000c61080395800c6000945556000ca030781c0e4038560f4400074000e41c050000500003800d0f401e0b80d840d01a2042682d140545110802400c042c2e00d1502003000403d802c242218000c9500507000d0020380b9540980f0741c58107980c00084000a160009040c107001c0c91403c0c1034100559403000708002c903170302c41080300b907810382082c00c1401e0f009040041c1e140a841d5002280e840c01e51030b1034100c000700d0540200400e12819203607401191220b08031034102e402a04401d29058000740c030101d444522040146034000007a02c0301140c145050f001007030455114144003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 396445377 1250 396444127 396444149
    0x40602180a06110f013303080a021e39030d090e15010804030f0c06090c080d0801030b18070f08030a080106050405010210050601030b04051609062109030c0c 69
    0x1503a2400410b01612030074504c414002c1c402000b00c503203a801c07021090b035012140c1c0c1d1500145407640c07200641c0414081c546c000c407401e40d90300078644045e41e91600c4442207502c0b1610205010040b01c8045420348407085201c14800c1080742e80c5403601c000211080610f240b442d450340c44501c00ba5020080310501016980701c4a2103079040c400c01c50340200c00100a525500f0b00c0144900c42039a00402d0240c1c07050305413801d00004c0038108800c40d4540800c940103080182460007103410302c411070140b5011a001d40040b5000e4210604081d201c40000f4840604041a1880000c0c01e110110350401a0090070406440009031260701d240c6e8001d01f2500b21041e10740c400f041045c8401c2c2c115101e580034186904007d41040c0c94800004c3d81c81c506e400040c002c1d01d48070401300b449a40640c21170035098100030410301c400d24100040c2040c1d04803a003440400078254410000e03a00340101e0030000303450b500700148070203424040f00c140042c009040044041003003a200d10000b0603c003a45040160a416400c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 396446627 1250 396445377 396445397
    0xe03100501090e010203100e1305100507090e1302121608030c0d0206160f0e0d030f020c0d0c1401021c02060a0c1704060b0303130603050f070306050306040602180a06 73
    0x80b140031541c0d040c1600b400c607031040040c050441028a100000c58555800501c240e40d22582d4a01d4404152100103105d07220340c40709214601e0041c0c000a05c50740c00d580e03904043d565500d03101c0d4080d10003650484000f1840c41e44803009414000c0740303081e03d06130810807540072100f08032160602545580c07004560350000324000c01c10300400c1c040003032100c0280c8003e1440f82007155a400349a2402e034030401c180142d007a403503032840340121b00d441c90062004080903805d1219081c0500000c14251000d00140074039103400c989450407848011801e50810f10706d500d203500700110b5201e1007403804601415407040a00d506100364a4a91001c8800c6180e4040c1c2443d0802c4504041a5005c101c0020180f0280d0782d40c12040d816056a000e500c0341d00150003250b0600140d021905510400d41d9007098000721400110b482501900014054500e210b9407402a41c0e44c0e0104500311103050103010b6160b0032650110700400c515030068190446662035884200c408140040c0440c0000d902500c0841d0303040c21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 396447877 1250 396446627 396446639
    0x605060408030d140622200304060c0306060f03020f070f2603041e020114040605070c08063907061e05041101180305060915090d1e0e03100501 63
    0x20b01040b2a0070b804160128144000041d9921907a424440440b007006904906c1c4d10b0003e030007100300d0040340c0408084858810002e0703841c03540115010780b0451304001d81e03c00c000b8402c2c41010300300c404640d01c102500c4040c400c100e01950001c50000c5039003405104140100703200542444690717215034a80c0415001a16400028000c154020396460900b4820407000c201090940195400c2074602040702501134401070310405030400041420580201d000b24210350040000c0540c0760280c1c605504080e0b0392461165100000c9411140002007109010010050f952902c201d0104103242201c00222220651205400c1484165050382d160085d00146080050365151914002042032084c0c0c6000d455002006400302d821504100b900c10240c0fa0500d10380c0340880243d540070080c0e03605410148032403a40c80340f003079003c4460380340c403000416562000024440c8801d80380f91164031a031402188100001c112450402c014001d1500c1441c2c8699414800d508403580092400191541084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 396449127 1250 396447877 396447881
    0x127180314030c0301050d0218010806220503040e1819021e090c0d02071e060b01180b030a020408010915060f030807020d02010e0a060e0319240605060408030d 70
    0x70518020780c0400300b0034045000d00c0c190032a410340c0c1040d501c4607454003040c40407401c000c4d103202c10300001c61880f000204803000041091401a44580010f002c51100f15125805550040900901560040008003c0030348103885140c0c0c00102010b6003444074000d6070002c0d003081c26600c10b071025241d01d54540303021442c00407002d01c0131075201d04218032100072480c08504c840c40080e00311004018082040002404e903501200c11065020b9000290320301c508040315280c0c00e181c1000c07210141441408137042d40310300c00210440126400c1c920005103421200e180c0340c0c0c03002d40450300e8290208000328101e08240500b9500030f1044040e0301114006030889803c07100c042e08100803011042c801040030520b0a815a0780880e0115130040312043c040c40181c40e441440c0c0301c0380f900520f10a10000349250410b400d20080402a0700742c0f102d154000b01d5a4810a87c2104000c111100c1241c44c0942212002c000d00d40e82014070300006111038a420019001d90455071101040390300c00204a45030600324 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 396450377 1250 396449127 396449147
    0x907050d050c0a05160606050315010f0506090603071119080c0d081324060e010905161e14180102100207021503070302040b160302010b01080f01271803 67
    0x3003105103003042c1e95a07000030000d10440c17001800c1c0301d0340038080c0c80c1031201c541c0c02400141802021160b642c085030801e00440b0300c003485810700204c5000c4000402d802d08400b200d0000c1d038020001861039440710380a640e200c41c0003402c0f80d00ca00c5902040c4101201403030400516034064003582c4e0301c42c0100860303140340c150401d40c0c810800045106102d85042d00c40b4246011a0b8001c1082d211082c04902c02e07a0000004040b045015044c6031001034140b0351a0030b07170390607030b5010f110902040d5600f400d480c1d031131941514120006650715005408101102d4401c90b0030341500d01d45908602041560f90003503400c0742e0100801d100030001a40c2c2a580c0400101a200e080110154180141900003c0b004003520850080c2044c000000652640c032940c1103c1c050103460341510340302c00b07408400c103640c1e01d20003c0c1203015619090f2030a680390700070b107440341c4110312a04c1020f00344da00304507130514601944e015002c40c10b28030101c90f8141d800c0c2801035409104141041035000348980c14010812585 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 396451627 1250 396450377 396450391
    0x9020d060b040c090f050427080417030708030f0901020712020c0a06140304080906040f03060903120e120a0512180c01050c0709110903100507030510260703020907050d05 75
    0x2901c0400440217803602d01d200f1140b040b2000210080d007050702e00680841d000042d00da120500e4211020414410b0182c0261022005549540e45401103a00c0d03403840351076406170401c1c1050000805d004011f121070340d40304141c1c00026007000f0b0243e0302c05205405c000105009a080ba81ea4140d1905102c64484001c00081c5805442e21a055003410100d05c8007408c0540329810000350404903455103821075006048a060381c01d186544d0341004070081080c1710302240002c0c014013054070700d108103000b0312051001d610040c200381c1082007401903560303210200f40300038072609211a44420740802d201522441d118091160241140500c441c100201c0038100f90601200380050400c003000007840d041503801070300001904114a00804034a4051003041543c944034000254410300711a0b013001e03024011940f001c0c041600d4401c0c091a958041e4010a2000741c48096401050110800240f10200c0303030005031180d55031242c01003121707000c08644580103d2000501c111414050784140b41e0711240b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 396452877 1250 396451627 396451637
    0x50f0705180d0f0c09140a0504120e150706060e0612060f09100c0302130801180201181706160306050109050105070204060e10051215040b090109020d060b040c 70
    0x41081c0c00440c0c60742610501602c800c1c0c800300c003003000e5007001402c41c0707030091040405641d48100307a901504415002c00341c50b00c0c40c10701180c8500da10303004080c041d5521270811026110b80000848210442000e210740c403c075081c101d402d40402440042c9280750152030081462803e00003080d18140000d80007d024001b1070401c0001e5240c007003601a00100d084c032640701180c0310304a44524007914081ca07400200d01e050410541c4d01c7d0103500030000d4030101c134801c040f01c5964448080c200c4852101c00300e50392070140f000394015889a400c9244810041e80f00a85440d1189176100440c4103038820120303158000414024558000028850b0f01410b0745014000305003004002080e0b490345100301c80c144030003c070b0050b007159102c2c0c00090161001e00910001840d01c5451908000140c0c41880c0c01514901c44201352007001003071009541c8124104242f0035145e80d034640894407070040c10340940d956a02c003198016503503030585100c0c0c80c0c0240008110004420100000c40780b6000c000d00030b000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 396454127 1250 396452877 396452887
    0xb0301050616050109020621061230070f05070e0402060f03091c031a010c05070501180b0a0509011b0c0306020a020c18100f120609060b0301090303050f0705 69
    0xd80c1d040126900002c241520714011201c1d858400d001d08400b4500035800007010441c500102c40304074415245001c1c042c01c0222503111042403040344c000d0481300e139407507401080c0d0f007040d07180807820f1041c80071030681c0c2d00c1c0c40f11801d540321001068000c09401c45806146072240010b001003040b200015240105c0d030511107040640c0000c542c1e22401c0200c005503400407000504550050105640c0c0e124030030103403400e00c20b10240003001440b9900c21502e030000e01d81c141065551160100880f41a0302c04002c00d40d00b070a010064501100c00302c20b81007403400f17101c0c0105e800350a000113005032a001382c1b20180ca5008031400504070401c2342c81d200c03e1803115003140401003102c0c0e182c901d044030f80003040107a6503121400304038101206c0a4070107401c08514510741030100c21404030700d44500020f5422414045d01e0f00100e1503a03c28038071441b01c0b812400501030b00030510319407000700c0551190000044180c00310340401e0a40381c0c8100c041e008641d64004011136841070498140d400341d610b01c3c0c614500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 396455377 1250 396454127 396454129
    0x10905091204140d02040f050402040501121109130c06030e100903081303032c0f0304030210050a02100501080c0f0a061d030a0614150901061707140c030a090b030105 73
    0x20b80610b2045007a10a018243c0900a865070442e19a456030050014803d42400c10b040c040501070590b000c0313018034607040002682c50003503644080318580c4094001c100e008031030100082c00740b01030301f00101e01c0799111200c00001c040a4600e0020842c50304c0c04a044079200b4035075420b00108071424240c06041000402c0060741c00310303606078401c50191442c06000000e0504600400103200c0004081d8880ba004210b100002d910f080e4840000200700c801d28480203101c55120b000b0303403200070342051f00070b42041000f07030003580600001c80881c0704840c0300d2440b0220f007405840c0e0a0b4400c0a1750b41080d000b11000f0b086c04104045d8800c007d44c1c160511320f1400d000140000f124039000030320500000c0c0301c941142d80070300c41c03039407056042001808550043d200e0705814000c250b80303101078500142c0407540c6504002800e50704950b4151100c3c60b40b01c88284410300c0d12440106550104000021520604407051002e0b21034481064021601c91060080140030032200750003a4071010420b000402031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 396456627 1250 396455377 396455413
    0x703061b08040803092a210c010818070303030b031c0f140d020f040e0901060303230705010608070f0806010b040302040c050d0c0503061807020d050a0c021801090509 73
    0x15806180c096076940d03091450b1b810f0400c0420400080401c00011024481030110441d2405d00d088a864103400003044d521842021043c4000110f5003244400c840c807036015100c4141d2002c1082c2c00680111301d200001f42c10045c02c0c1c0c1048012a0f60344121200c23504080100419100751b07124501101c00380f4507000b401c1804070078105400c1107a00d01c1d815002c1c100030030542d2207500024000b0b54072030300030380342c080a10340150160180582200380081d1044005001c0c800c02c99070107881c0c0a41304521401c0d043c10301c01d030852050000440c20011040020824890500103141031800741185c1d40c240b502d058422541c0b13070b002d0710040d4800c000500c4000880c4040b038089a0b8100c0300001c0a542d48035066070640541611005024900b04900ca44981c00c81d000714883c13501260860360340000e0f08000045500d066600900582c07101480746000c40c09030005180c0c2184c942016800328105600040d010359400166407a6240120010440c1340c0c1603001d41c0742c20094400203400051a80d4505040d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 396457877 1250 396456627 396456631
    0x50c040c0203160503030105040e0a08071506081c030c03020a090e0403021c0801030201300e210702030105090a0312021312050c010822080304060e0a050703061b08 72
    0x1104995490940c580c0d1030080003200c07548030301d026010756100070b24184941c5a82091240c280502e04141da001c004107804209804800e510108450404e1865100c1520207181c8451640c0030a944841c08201d41c50100000d6240d868010302d400403490000b600202682d85140701d500500d801800f100c030000340c02c150306005555400300b0384d9189642e1401e0403883c5c034a00c1c1d10b80307840010106608220031030b403140c03071a8140c1e0b00030380f01c0a0001f00b0141000100d03221040c06e02001e40402d540c45c4845102da034002106100402c0102c41075000d140000c6480c3e880700c100060055040003600000b181401e005c2c8036445020400031f8102c0c424030340c8001c0c1000c00300c1c1110150b4160300240c1401c0b841101c140000107401c00e20798280c10002c40d441d0140ea034400100045000c00c2c52040010400155031700341e540e80b8045c1d0a01003007900c609035500c08040e000500221380b2180c8031261766640c481c0c2041041840d50081005280b198a075042941c01c4860059005c1c540b190303c91030314200d030345d0000c00150b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 396459127 1250 396457877 396457879
    0x1e12110312040515090d0f0c1205160b07050d1a01300507081e01291909030c0e010617040302190506070314011410020a080d09120c050c 60
    0x1c0042e55441c94690308040720300c00e0003821601c0c0e010501040350b2000510510090b15a00ca03000c6503071035160143c650143e02c540003031800b0200001d2038002881500509034411600d641c0c00304414040e41c5140556404540500c00210040394030040e80b00c1030300505400c1041550002100d0403071f500000c001000c1c00c0048180e01c1043c0341910756428074030090091910030003604000e60f003040e80303000b0801d010603148899040006500d48002c44041c0780b62a04031080b00c06204c1c4103420490724600c0240e10700b804100f9070b1f4024000100040e01c8103810704207000c00b50380c508483e50700b10302e4841c8461003140c102c001040171200051000c103411401091072042400114012541da62908074584500006541024010315a81c00300b00800020340c0b0380503102c6038a003440214000103951110a0b001d1182c9010031783d46005120b51410041c0c070540c1d5034002441074868411058541d10815031007411010701c00d50b86c40820005103d407075002c441140d850b62804400d200010303180c00d951000080c40075 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 396460377 1250 396459127 396459157
    0x2010b1e04050c070b0106021f0b100e0d050f0d14040b040302010e06040503010903020d0e0102010903020613060213080c040506060a051e041e03020306010e01080604030503131e121103 81
    0x451812030f40e00e000d0320401c5501c5070003c50721750b8450030000c1d290f1098201b4286241e01103010b0000109090081c40c4040794041c0103a00c0d00d55841d0811203941d0580c84850b031300b105480c64440c021401c14014030880e502008020684103011000c010541d030320860204081c01c07404d001c140004500e07113044500b120f03024a0411103a590381c100140561045501c0310741d0561070044008205074020a68940041c0f00d40c40d40700200d400e40c00168261054004010016001540055001441c2900030310440e40240c10040c100340c060b06480440c00c1031a0000c502c26071041515268514050003042d03808903047e95041e0800c2e24804019000d0302460300c14240319480d5003107500c45450004180c0d4000c00c008040c41c031840700107a04621040e030345400141c0c06402000f0000c218507140300e02d060304032421a4000e1000e039681d40c0b01241c66400140c030f010742e030046007405480403519160882c0020f040d44000d01c0d0100000c2e160604007181c1a494141c01d101e110740021036945404400e44251044d0b541e03074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 396461627 1250 396460377 396460381
    0xa090b0d020405060a020d120e1f0b1020070b0724020d140f09030f0a0306080601090c1e050d0f090605100303090b0c071406090306040b0702010b1e0405 67
    0x4035402901403900669004503022580c2160075500042c4000c03010b03801d468a4500c0d030030324030710401075410981c034100b540d91001500c0000214034041e00e0180c44036202e000a4520003610004085840244ea600c00085000c0a5194030306203000556410710b10b0380004002552034075001e0305041c011800082c25034030701c03d81040d4000b003441410000080d054081159900c900b01101d2006104500d59150746203001000602d0055198800038040c44c07220005500b08602a01c0c1f54559500040c059410161944800100c80e50308110013406032a16800114920012036001000c41c0c05000611200034400701c00c440c3c20710f810100303c686403442c403180481c2c1c2a40c411542d002500d82c0e900010051446c0c107007041801c80711042008280da00c00d50b030b2011516911140c08280b0702401810154076046803104214110b01000d882c0d41c03031407000d0481d40c240740700f0a00281c1420011141a01c003188200100104941e085c8158205e02c50203d841041c0d00581c5001903600c0c901d01012240541c0d61140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 396462877 1250 396461627 396461647
    0x1060c03021e01020310090b240c010e0c0112050615031512010e01050f0c041202010e0414010602070501021203011e0503190203070b032203050f0c060613020a090b 72
    0x86850040300311481400482c000d0903210600035401155500440e4001392008102c0141900841000312001403180c0650085500039580307025103448034102c031302001c100c4081829028003030704007204440d1001d0041e042c0311000140111400701c5509100d030b885d001c05c100c150f03503400e15545004446007218645035601c0280054041e0b501c2007490b580001001030080c04200150407004e01d20b200740009104507290700800f4030003000255007600392035806001c1030140c0950b40b06c01100e09401490140c80350400703100484d0407612109106111108108010b0000c4c0303404000d1003008100038401091030f400b4409050030540018020329490b0504030300c13542981c07501e0f603541e00d002e000c1c01800d071b9002c580300d102c070803680e2000f00c4002c90003802014000a102e17025070065921403070344070b14070000c0b0030012045040351401d02d01046040c0f00c1e080c00752501d204144409417003c44c851100820341130502c00308100b07554000d4420044502d00412008a1982d0720404007412590701c0f0001c1038070744035524 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 396464127 1250 396462877 396462883
    0x70b04060b03011104051011060118111c060e01120312091e12050310050904030207030c0f051806061e040e0a240303140a05040b130302010f0305070801060c0302 71
    0x1440c1d182d455800c005140800c2c0c482c05009208544046801c690400310505068030384075400c8084044640084004008607010000904c1d681040b0a80c00501c0e465203c12a41c05074000040388441c0f080c0c81c04208012a000d0303c2104064048030300c96149561401c40c0d0b412025270f001c1c60080400108030b1a83d140300203a03420190b0f03071a500a40d03880350980140480c103040380e48910203880d40c210030b2400e1341000c1e00400c2101d00448150f140f842815080106010100c10064021030440c851084000003080103039000340040c0007802c1072081090f25041c10080c0c024090759a41044100d078070244001941d58030b040f42c090003610704045400c894241e40e07031142c6005a81c04240c551007400304001c4450410740c040350004400110f004020540710801c01c08145083c080200490f100f40d8100348904448400f0788030101c2c68cc50401d15058454000b480c66402c04103880340d8034025140300344119a004210540315000d07510f01044540351044004203000070600ca4401404408101c0105040c400c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 396465377 1250 396464127 396464141
    0xf020c0d150f0b1302090910080d05210106180f0b04140a0e040309030668070b0309030d020d240f0503010c09052e03050a050a0b06070b0406 62
    0x1308406012241c0340c50740c8010303501c0100300300c0c421000200001c04441d03050881805442c4d05600400e4041c45207a4141c1b007a60010141600c20242500f010145040924a01e4041c0c00c041c2da521007140703804440807181c0051a0410300d0075012204041c40300d401c480003039400310b46c0240014042d9005081c08984400600d4000d505403203940c030100301c240b40e04502c0240490f0b10460f010040c410350700885068041001d107400780003124005048844050b150781001c1b45022500502052400a1000180b048901d5032024060400744d03100c5000c001040c0705400050517030400b1146141f8020203640c0d100d1088c00314000ba1694013240140c0843c01642c840350440110340301c0c1403201d10450680e40b101c41602c2c419260161000100841c5508043c050250465441d4032103488207800c010400400502d0131000e56010507032900031003003c11100c4e0322090071104a4400007445d0600180b00b1050320001000880807030f042405c454180e48034101103545994009541c6010f644841c0380860290400e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 396466627 1250 396465377 396465379
    0xb04060e01030b010e07090302031b0a0b0c060901110712120b06070602030a0e0f070302010e03120724020a080412200c0423010b0a0c0606060f020c0d150f0b 69
    0x80c0c08004000c0210542d002810381d0404c0c51240280d82c2c41e40c10407503019034507000080d05600500e40403100030f00d41c44480c55408100402d01001d00b0340b6101c60079680e4100154980daa548000244198180280b00750304004103142c111a01e0038a1644809440010410b2010208005250305036450341240e03200406c110002421503654141909220700603410030744240c402c01c2e142c45400001c8480c0000d220714841d4080b40581202c615540040da10aa0001c0d8420741601420441d5004110361f90700030020148560b1801d40d004462a0340e14210050b210103080f489441004101051070300a00c1c030950065001d00e52055951010404440700786401101052610840b19040016a40403540458074501540d08111410011100003243c01d860300b104900f0300c2c5502d00622405180c44004d04840c3c000b4100344c03054040a0b40d441048400e40d42c01100080c0d80e4001e00b8001c6981407045540508080b81c00182c5070842ea110b081d10485402c0c485900583d80744004031402c07800303400484e08031034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 396467877 1250 396466627 396466649
    0xb18011404080c0d03150510020309040c030c0f0207062a050f240115080402010c050304060903022706100903060f0c1e140304080d0515032e0b0406 65
    0x61902e0140700c19009106500030b98000c41c07143c5440944071b41702d6941a000c40d03151002e2020324010130300c88903a420282810450100b000380380030944a034042e4142c44416607900180c00703c0319034801031013184841200c0b0119008014201f00b080da1081012001e028030706843d1600e68401c40c02c840881c000905d0050480c003400303c001c69043d101144142031217401007440d40b41c0c0c817800f1311501030b1804240201301501410100c1c0045051041c520b2036840361040c108641c0f2040c2da80c903000d2441c6c00c17076407180b000030754955003d10450500d104204240003c0a4028220302c00c030040008102c0001001c07140110030700004000068400c0319010b0081d504801d082000d0040c9051800c06000e06110b0b04c00030680b81d20032446401c00088010b0804049030b035902a1050b8020351156440e1303c090001d0703450711020f000040d1006920b2180f5405000015400c10b0300c006404227050620602d0302c0100104c8401c0821020b1a02c41c07000c03100035048484500007080000000042c0040000e6081981080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 396469127 1250 396467877 396467881
    0xc0a09080f0718060501140d14010b13060c11040b0f0a0e1b0703080406050604062408070509180603030c0105180c0609150c010603020306151c0b180114 67
    0x1507011500341c0946544440c03403100c0052040b4070609851281c1318050000302c40e6880c151010b5101e80103011f0f00718402802060341c1a01001d5001130386403c0e000340d201d4060010340d20684196241c03010300204514281030b02184600d4440044100408615501540c0c550540d400e0319070f100441c201c50050010301496540351640f2502e400300400321102182c5001c1507000c80301d1050b0000595214643c187d1b5400000c1c1d485540391005001c000d41550340094480001081d041c400080908110351901061420345100d084010f04480016016805000c400c101c2c02042d074a58500c8001540c0d0304850703202075034645d940480d1861140c0b80c5506070340d510384805e002a10146403285800c0345000412203444e51544800c00c4124800d03484801c0e84076204031400080c0034550030103408a014100000115a640c903000b2a0812134100d50a40409400420750001c80c41d201c288240c02c40c80101ca4115501041c0ea40c00800c00d1000d0444008a000350038903d8080d0025001803d859070344060780b001c18 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 396470377 1250 396469127 396469153
    0x6040302041e021b06060303070f03051608121e01050306010b07030c080c070e0c0309030405092a030604060b040308090d0f0c060f08010e0f041104020708040b22030b0c0a0908 77
    0x102c6503902c200c0d1307950702416011844d20728001003615082a003045e000d00d1555070564041c2d0740e5074491a003142c49038200402203004071b6a004080e008da00c8040c0c40a01180ca01081124000703110b04010300c03045240703c40148440d031800512181514048044199110380c1410261000300304044002c0c801000001c2e1240c155101082c00f0302124141d4110f03608540f54891a4042c902045038540d180d1341c0140b0080042d8501000c4586d0029131981d5495014040340b40c0c0c2c0000d60610302100a1491070000502220f402d061042e20018403480281c0c070b0600c0e003140d581244511804c10000d200d55580f2a40100f41b060030389091506680c0020040e0255a5034103000c0c1c00c03c05a41409004602200000107182e59030042c00307071080e11810140c588030340d995501d1540d11000d0f081c44d990001d60900900340091041d0000384003906200480381d894109558005030000b0151100224502c04200f0403c0040c4820000a81261448031165154010944116030300840c2d0b50140c0814440c1d89200e0b518 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 396471627 1250 396470377 396470407
    0xa09140d080412020f06030903160f080307080601020705151c11030a090b070c111023070501150320030307020a0306050901151202040e1c0207060e040b06040302041e02 74
    0x1400e1003a511800741000100820400d80800c581410b0227800030803d40b2603080640e000100824416502c81c3c012106c2074a5401c40c941040384c6130750109019000b44040f40d87c0401640004000854210300d0302d1801ba03a0f811800e0242d150000010740709500a09492007241d0060f5140c3d5019010140c1c1304d10344005550007500b0204010b07210003001802040c05c0a201c0c00303045881a07049503072034100c40e440405004410384c2444160042114103030540300202d0744072400c0c1300954000c15902d80c640c02d060409a0031580101004641420390344810000250000e07202d9a220900780c0744134440b203061802090440c800e0080003540501d1440d80401080321640c8410f014030b09580081000c4804841031540d41b0941c1e01541c0c600302d9600580304014a1b10b90406410100b1300e43c141c80d20301e41d001c0b082c666848056041140541c0004405201c0715038060840e10f80d14074102d80c1406408036a50100e80c4620880c000a8007a0f503c40315000130003d40b00e02c85a0340001114070455880c0068680000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 396472877 1250 396471627 396471659
    0xa02070609091505130f0e0d08090307240906090c03030e040c02060c09030304030c0b0c10020301150309060912090f17102004060909060602030a09140d0804 69
    0x8501e588502044038101403003546140c00510748410340c00d505190400490340e00300c01c04096015100c3c4880a2041c0b018002d800c1c00800030b00090000e0340011002514240b0020b044610562040c40b00a0108614040500d822403079500d0a010441c070070300c13029014000002010f4103ea040890140c200003c03505588101ca000e5901c814a00140308100400d64100c41d0410340181e126001054000d10440014500d90400408803460241e880d07540328000301481d840700d1801000400d882c015540c050103c1c03c083c000c010310031451036040603554200c4c0030142180e0002c02d030707444501034100a0b40740d1002000030740100440e40d0301495007000408484c00d0340a00d4090040c2c1e07031000120825007185501002880703c0181580c0040e074803201c0000c0c012503103140507100b0001680080400c0000061002c1c182556400144034105801c050603903203c3d50220045620400400c10f40550202c58401544c1800340340e0980008004000781c041d6401c0d88003e0400d0500040001e03810032220405d039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 396474127 1250 396472877 396472889
    0x60108070510020d0c0227240a030b07080604020d0218030c04060b070602090406170f0105010e06011205040302010b04020f040e0f011d06031507050309012d020f0903030a0207 77
    0x10b84031400c24a42261210720b0030030200c000c40d44201a0800601d0580c52144070141c0248400e500303c1c00300d00c89071480100945d6001813038072a4101c42d018040f07800100c40b0300c0342c03001e54034000400e10390f0703544941c0e1440003072400040002d1000828034640c1d0f150100e40344024903440039515141805000d141c2154406d800522a00c107400400b149800c150040c6402c8a590200075401c14204c0c0d12140b01a44c0803008880d84180d4842011801d5900015107086c80546540240000c0140c1902c0c98215181a00004061240202003105581c0c1c0b1413800e80340c00320991404299504c4a14044e8054604013041e25401800403920802d00402180500300711014900315180c241c0751401e4103429400207014024140e5841403001c90312145106c4516008800038003124403204e40034684024545007580c00303c1c0041c80c0001400810030017401415105143d12080a0668840c4000c1c00c140315424444142c845401003080c2d200c40f8242c0741641c00300310014081e2561245132071002074446502e40203034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 396475377 1250 396474127 396474139
    0xc1f0b06220501090f060309050304080303011d0f04110607020a0e010b0a1403070c03050c031c020c010b030c1020060f180105070906110a020409080406020f0a1a10080601080705 78
    0x307010f600c1961150304450402040c1c4a81d2030030110100e02520b04400140d03801e110801001601c1102040214020000c0c0500b8a10500d013503480030340359400141003407180101c898140300c00b045146070a031500000031a107150383c2d603001d88082002500e0a6025040000030100002440d071003060042100c1da501d030313a5055100b10502d01000040c00240e035008005003004800781c0021b805000100f5402041d0001c69040900e001d06014000010350a0416240d4020550280150382409100c98440c01180584203007980100801c00a03828070402c1c40820401c1d82c50480400e0b640c00565400c1100c540650701580f81c80410807681140666000c0b41c0e01c807000c1075200c0c242806100301806000d9a95504c154540b620408484914124894810500420300e0000069442d48100ca421902c21083c6030303122803034008003038104921034145590340c0c0c009502c1800001d1540302803640c4005000745410403500c4070041c100c034500e0582c00140f454403510002048294000a03000d0840d8001c40710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 396476627 1250 396475377 396475379
    0x1e0d0f030f0f0513030206030c070501150501030b030c01121a03060112031b0305070b100b0711130b0f060c0106030b09010e0c0109380706021309020c1f0b0622 70
    0x44801340f05a10742e0340304092140c60240014a011401560070120134803005044c0065601c0b4682142d03142d815070070481098080820003542c250294048204d0300f01c001d004000f40500010744000b08410720f4000e420b87d100d554050151003002210400318001d82110321a41c0c40c0d00e0300706407040088ae01031b004103050644001303410100c4240070080380c1c1c3c141d694508280f81961035607c1c070800604031102080e254140882c00c07040360009054100e002d14480b2201484100520400c05254020852441d0411003440c0c445d481e00f42500c88a001c06503041c503990140600014010005030700001c00303880030142481a0480150400c6d500c840d44c00007907403803040a550054829051920a02280c4201403042e454444150320408041441a65004e060400c0c0311a160982d5806144211520380c1d011514000c00560341c040d0b8800b0b42001842140fa1000324001190303500d80d070700c140701505907241052210010341ca8100f0f0b01d10140203803400340c89500c1d151398074000d5481040405404111000c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 396477877 1250 396476627 396476657
    0x1c0c1802040f0614070605090307060f0e07051210141b0403320d0f09080106030c031b0902070f2109060c05030408070f050307141e0d0f030f 62
    0xc200d40440e80c0b4220424a10340c640041920300c421014810204142c081c48404080790103400342c2c5104600e44030107907036114503500c4e1a10403502140c1c0464030302c52030700e015861401b00024100d02524011150113181d580c160299503e02250003404035886410440411100710031031090500840002010200c0040400d00c40c000358001c40c4006013400040071b94915510704910108009414081c080c01c02c880d0f01405083d1400c0c2800b00c621000810600b80007200c103906c40e035a0b030080c084c818000d200651440c1c480500082045c0006008051244407007c01c03607002c0d142c41c000401c0d9142c0150f44a420a09188901065540c0156186514000b0412052406264407410b00c0c00755169903541e5030512204880c5095020804c4416201c10000440c1e070785800c1040800500e803100300c81560608040500d410105942d120b60040d01151074030b07040f41e98900d5004840f201c4450b108210541c0d03c01d00080800300b8078031010b024680481a01418954043d81c0c5084030b04013500d42c4240a080c9007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 396479127 1250 396477877 396477881
    0x60f13060f260a0b0406080c040f0e15091c0e0f03012f0c0109060903021207050709051005041b08070512010506030a0e030a180b040b0a030b1c0c18 65
    0xa4205862074400014019034518070b00b0807075000030244500040388003c550102c0d04440264101916950112010060604d854090f100145c0072541d41801080440440c450351381d40550018808107914000044a03240208a1040c030b82c240501031098909019a000d4100c4020840050140c201d5200059003030405004481d00b454200058044102c1c15004803a0baa542035031803c4400c0c07c007040001c070420030900800800030301a29000801c8140c0b0329011385854850216010000c2003030001c900414400301b41c480c122203420201044030f80d01c00c07800c0100d0714030039001168071600d48054864050300700520503014680c0368440101d180c9a281c000d80c0d05005da607a82c0019514250018451410440055074007d8118a00490803114105c0c2e590305540043c0c06580000c0c142e40c500921000003206100700070148440c90501d0035041c05c00c51030b01886402c0c040e006064031401030300e06030349408020b0140c1003081690901c1c0300815103809018078103203101308a1981c10000d22a1207012580c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 396480377 1250 396479127 396479147
    0xf0b090c0a0f090501051b0c0d151401050d1b050603090f0f06090c012118032a060e120f040e01140f1005040e0709090e0f06060f060f13060f 62
    0x58407110700f4107d40142c0d58115540d4800044001d01401e800070f0f0035600e960851201180c130940e1a0722a07080503c0310b110842e11b82501031040c982c030020041045d5162284100601030b040b83d801003143c00040419542050f169101d6a0401c8000081002c003a0001c0703440c41c00502c0c02d4058400c1040c0000c0b40c0c0b951f44800782c9950075513030804a03041101e50700400403000104e0a04202803200442e9202d184100e41e12603161103090185503c83c0030825901140502080740c4040c0c2100445c003d40b40041e03288144031100801066031034241d0b90380b0008c09c229203060075860301c0745640da580d044c40115186401a11512800f10940c50012403003070303080cbc07506a0039442e018060b1072150b04c54000b0821702c0c80d00c45460a06000b001c20012550089185441d03110f60000c0c0c990744640d83c0b5100900044880907640640aa0000c001000c640140440c20341d0b00030204942c12001b006a07400003e402d4895410540384101002504402c40710f00c0901900841e4120f4403145040d20b6048030646a01080d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 396481627 1250 396480377 396480379
    0x70f03021504080d0f06050d050309030f210702010e03060c09040b0108061014071208012d090e10090b07170c030a05100503060f010e0a1107060f0b090c0a0f0905 71
    0x14448031318180000ea11844a2104102000c00c81c01c0c2d581000c1415030307503078800035108d40d04006000800c0d82030802c0149040207021005020000440060f00c030b9030100d8400008040ca80004c941303080da80b2070744551408503401000e9501038202991a00714640c0311041c1240514200303160044658000c104151080b4009489089012503a28044400c0c800340a1802d103445020b0218201040310f8070742900254025031502c41180d410b00f00c0d550304101c41042e122400710120110700ca00300880c004000200d52007200c011074a019005c080d1810030350320401311542d55240c0003400d41808011800c107030107914a510760038201c0880090544d803019044801001841c2e040000c83d405100c04c5c4c1c0300035484054119040101c0740c0f1000040d0070602c0035201c8411815040b0018041000794120f00c54105035034030030410110305582c1080e50a0300401030301502d415a25025442c6a54064004014510000380080c100b071400d104120030640000c442d0f078001400180c0040203550148103244280c3d50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 396482877 1250 396481627 396481643
    0x1c030917030f010f0803070803060d141212010902030114040f06051c11013213031202010b011b020d0602120f070e010f092c0c0711180c1608070f03021504 68
    0x38ad44c1c024012403040b03910301211201300302c040e248810507050120141f8420307541c07000e9036a4540c21065120001040c1c111212030307841000104070b8600d504d103154402000070388000c129464012007400090480d94852a04081a02c12903e403510101040004186c0b1450903030680804980044514981088000701d00c0021450220701c06402800c94032400584076a2081c40e064503540301c2c0c0b047c0261648111406a00140f030403039040d0b02230040080d043c40a2a140c0d03541ca008030292044010503501c00303400381c55005110018001c46030111101e038104c0c619025a5410110100c0019500886141001a00018040d5055032003180c0c03021004003555a482005070030603e07800c04071103440c841c0032303160705d0310307111641c000c0c03c04620161042c034403025459183c402508040c8904690024001d100e80c0900442c1900007801c01340b803d8118089120031600c0d2030307000398880b003042c0d04070030701426400c0701007203030402c10002e045500c0b003a41c0b081e425036180481d48030342c405440e40d003900c000309285 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 396484127 1250 396482877 396482881
    0x501050702150904150501080f06010801060e040906020403030c0203060703020c030d1e0906240f1205030708040e0703182307210308091c030917030f010f0803070803 73
    0x440c0201c000407041c004002c0c001d240031001d50000e42200c2128201c1c0e01d901a0240041000b9070b006a20540e210004018a010a242c6140000d007904c0701405a0410320030150103401843e107440d0700c0b8400d25503005400315521900c0c1e007005442c4641c4010128400d106140c009407590340f00b4000c2c0c45021002a006500300f004041d040b1000d440c07a010002907003400c0502503108071402d03004296805014400000d403081003901160308250b220202c03191000c00440c070801206080c00000001c403841c810081e02e0202e02d91415905500c500c0202038500c00011901084500f144d100090160f64035880400464050103080450240c1446020780603850020740c80070703040c2c000c00d21007059401190580b110151100c0c4500900301c44280380d482c544ae401d481c481c0070590002d507400d0b0440c0f070000c000d040c00c1840c680525010000c2142c030904142c0c48800701c0c030800c0380d0000c00c81c02d0382c401154400d03100d01d0720510401e60358400740304200d801c5100c0300d000100700c2c0010040701c19040d0012451440c0d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 396485377 1250 396484127 396484129
    0x60d030c02100302120a0c020c04020f0301091d0a0809032b0e01050405040c020c030f0307020904030c06091e0501060f060f140d050f070e0102070f120c08010507030905070902040501050702 83
    0x8441c040000c64140f58080240c2d642110540000911503140210b00041c0ca02c150403009261101050300103003d40c1c0b04100c90b034401806802643c1c11510708880120740710002146090000040d50300303004083c401e01c1d030407400b00010b00b000b40c40140016000c403540e00d0400d50149003e0b1800e070081c040700e554403c19418a10340315000c0455a040103040031840c1980d5903002c02c08a8001c03014040050300407050b14006031038107022078440c0102c1c0c40d0040d800d090b50b540000e9a11103001d00300a0074090030704401170811000e50030506180d03402c500d002e54104c03004500c40c541141c0d285400ca0700c079485d0190100f0613491200c0320070151949a40d48501c13140500d0810365054595100050107050180702441d0010500d00606200303c070905031290703040c1000800a004103108011442c1990481d01701400880d41e41ca48102c2203520350f0901c40503080030f0703042031403070708489401c21501d950a040402c440c0a4240c2c001e024014800c00440e4230007682c0b85570090483c0514014180040c0c42044a0f0000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 396486627 1250 396485377 396485389
    0x60c03250f0e0d0804090c0e0f0919090204050a270816020310090302070501090b03242e090b1306031e052706090a47060d030c02 57
    0x42c4a0018150b8150100c0c59200d841558002e50300c50007116841b0b102c1d940300329070710801d454003c01007078407107580120030f41001501d065002050225025a51456400e2014103500491942500500701304140e00300802181c0c080c1240d4000c3c0c1100f15802d18400e03006c3c5078403c4681e41c3c41074001005a061800c004114500103480c01000ea905100d402c009070f00b200c400c1e10509021038441c0e002080c095242000261100e00d09034031001c4503d50074020003100000041d00000b080300303281106006600c03030b034000071540bc16021030350383c2c14609030a100786030b07500380f400c050a40c14a81d00c5d07502500303a642496603a20f110703820f800603e01120020403c600e5021790410411424504060b03203024804a100d00100c034011030340c20060b0848600c0342c80d1084981400c10255481003006000c0c03920380b50700c03240d654003405d0200031700703840c0c4a4500841450901e20304400607004000803400113144225005140602d45a110f01080003120204485242000a482070a83e150315407031040750700c940030804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 396487877 1250 396486627 396486647
    0x8090a03200a0b15040623101e08060405100f15140309030a0e090c0711060c010e010f0c0804150c02030d0606020d021018080714060c03250f 62
    0x41c0070721508284000054040c4680c5214441144103e1305030310714a01000b060b280b075584503094200341c4520700a801c41c0b43c00c0b1031240004094038411154212144200d03540307980010040f885806040380914000d600c40c011314002d042c121000e0180f81c49025004203168403500c86c16030f91000346001040582a14030f00d03010300d811503040c10240a40c15a91400d035a501c1220200350507040000c1d00041643c003c0001050200b0949041c115450480711050080c4103403400030300258968003411225558043c1190503052205c802406003202e6440154041c120903000c0e120041c2c24070100f441c0c954425804684070b26041100d100c42c6486c0030b400c010052110b900000118041000a402c009000d40038101c0141007a500400c1c13141c1002000a0910382480805000344d820003c081d110303c4c000d869403407402070b049500b080e680c9800340b40001d0160000004402c06001d61000c100017140000b028610030381841c810440b141866084066000c000382400ca0089102d18082c0381295104640b454 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 396489127 1250 396487877 396487937
    0x60109020301050a090b1c1a100f090222060903060e01270f05070608061918020f04030b0103060518070302090a0b1909050714091509060715090308090a03 68
    0x3c03c00b098a00c01c0c0e490504100506943c6660218007681e044070480703e103990710402701c5030a40c000c0e505180d10101c010245119400c0c903a600410300303503803164805003820800040f981101101580d1610064403880a9110a03200c9515043d00c0144601040c0580b1200d0514600c040e0003201c400051002c10b50354171001a119403206011450006070108030000203030001d91030b40c1660345440402c000d4080c60b17189071a64030702843c0004010341c3e200e101445603030501038140942c803812145e1102310302d07000300d0344080c081116100c0008140220380d40114000d03840f41d2491000305c2c020103100d41c1d940f1010701c0000d411030410301c0040e038200d030380d90b00106560b840200130030318082d907807940320b603940009800c02da0b01180d80d5001c1c080346030740014504864240052010b400c4c0031000000403d0501c2007105c503640440005410070080d0340795070031100e03490752040c06c0551008e0b0040000e4000d010350f010840c003085108001c5482010001504005a80d0542e01d0300d60050500d201d00c0b00540d40d0740181 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 396490377 1250 396489127 396489139
    0x3030412050708030405010227011d030a05010203010f06090509070512040c09091a0105040e060f1b13031209050603041403090303070302010b0f060a020d050310180509060109020301050a090b 84
    0x102c0000d05154000d42c05640100700242e1514151110725a04420b02c11002c108041c219410034640d98100c1d0510400c01c100e420469980840f00012070304082d21603100a0180d403001001041c03044800304000140d0300c40da42e82ca15a29201c0d41400a0504203840150104005001158098410008241d4011b1140d191031400b03955500180382074a1802008079445030526142040f49007407100d0b0640145004c440500009140d80c2c0a0b036164803000e00441252810764001518400c164441d282c29010b403400c10071f41d10b91110146001024007804126503200e03d1404001006108004280035142d004104a1950b155956211014040d2a4108103035010a200d400e40d2960140041c007121130280e0008514041880100710042c23405201e0103208200030312a451410390b0001e1340c0d2050b00d0090400720769a4541c0b000460601c0390035403044450340585056481d2400064111a024008601c100c410603620f600741a0181d020900903141c00207141e0404000040082d04a481241009410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 396491627 1250 396490377 396490387
    0x100b010201020f04060c210909090f02090907030b0a0203061005070f0507060306090501120305030c0307030b1507060e07061d0406030602040816080a1a2d0106030b0409050303041205 80
    0xf241d40c6a400c250300132400301c0d00892000301404024140003006900d101c0c41600743c40b0034580040c0224885025408045940d080c1c00f104100c0910940050a0340041c0382804601d030411a107551200140404c403012075050001c1011103e45000350307406010010000c07010000d008004907100e400041e0700f070700e690320720764008000300c1c2e0b051110b0390182116540208140d4140841c00040d0340701a8000d0701040d16100740c09000c21b40c00740c1981d80008005800c280d07242c6031881c0450140030542e214642c41844490340301c4034200c05030008d001b07141c4180d0301841441034642c00f26884035018841e4101050030005100004260078030a29442c04000b4000200343e922038440008903001038000e9243d40c0d00604200d0400303090410031030001c046280040500d03e1060f40c07010401484100b2445629014401090742c80c8021119090041c54030741283e40301d14888521002d42090a00c00c0c6130109180541000d1103090038000d0b00e070301e04e41000003140b541e08d5664a102c08080d80b400900e04004060007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 396492877 1250 396491627 396491647
    0x30212010f080d0203030606090d02130e060708070c030f030e010e01090501090b090d050f030606160b070e0a0609030b180703050319050403020919110403030207030c051002100b01020102 82
    0x28901825460802086141c10066520f00d891800c0c460b40040d940113000b00262a0340350400c82d006400103842d00c000394078403840030a9680c10801990a8000c0c20003080355842c450002e4910720851080d5a941c00e1900c6801c0155030100e40004050b00054010035407000090190700410401c1012000000d02c071001c8454003402c5032429031080b00c0781c2e51122048400e20094850300394000c2881c3d0003914000902d03031000380440c03041c001d0041d0b01d41c1e00400001c203550303129420380e0003a40c0c400c50035440e80030580c54080e0403c03404550340390109115010070300c4141440307202c40054918a45801082c0384c1181c54102c06110000c06070340710a8507507802801c00810038043c001c01144a1001161200b140501c00f00381304006003110010084107100400140c1d5580c030840390050035400b0300d0a012690403003418003600203101d0894000500003000801c01d03900007a450b04480c0100d5894400b03d89910401c0b5044840c0c200480050f88681c404203260800c0394042c2090083c140001031920143c50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 396494127 1250 396492877 396492907
    0x60f0b0d080a030543030203010602030a0309030c0f08070605010608152116030302010c022404020301111804180b04032001091406060312031b0f04090603171e0a0302 73
    0x5c44e154050021010041540182c241e10303440800030700d81425401e5606200c0c00a41d64001c060402c010152100b104c41d0078940294000c1c50503a0700444101201126407d051620742d00c078030300446500d494500001200da21400380507000300408080c510300030010000304a03000c0c4038401600482c2e607900303059044007030041000b02040f400c40804002c0192a40c18083d0855107542004400d6400450400020f895404840c650951a6002c50b450688640c0086801000c5120a1880e02c00c8001a4507001d200140c03100d0315010b800315810302241b50314054050802030b6140d0010400c02404d400f203400240a054000940c1015020850440700d00540c9c0c9130950b000702505940e00c00070b03da4141c3c01d840c0140481c55000e80164014a100c41103104aa0487d03c0010b003d0060041e4242c0d42003000340042044032401c01204411544803a201c0101d00010505841b044900980c0000c035942400c010000f9214456080c03140c582c11003845407050151548440f400c070301015401c004941c4184024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 396495377 1250 396494127 396494191
    0x2705150417010902030f07050603010603022d1306020a110d0302100c05041409160807090317030a141b0a2c01020f16050415050904060f0b0d080a0305 66
    0x1076000400c07000810b0040c90308040256045e194181c202140500141e03c40100b2a4116540c41c03a0040c1c0d540c848904103c000041015600c501800c1e608100d501504001c014001c65143c04003020900b13640c40d6803c0ea614107000e01c004141c00207094080409103014110100f0150003801a660407550030003089085840503c4031401040d0045014043c031210210000e45085041e1440781507414070754264800301d182009a01d080060b103c0c001a900c0788549440002180e0100e500303420002d00c080034240580044032444d24a038504014065905507004000740030b00c5004101070040100d503092207500d948007442e440140503200f0010031708440941d9074000d4200508403080c00342c0f40001d000909021005102c004076030b101d410380c04600c072006c00748201240d800310740028121b6040e00b003106c8014280d50010368031807072403400c00091000076080004003080c0d50710100302780411802040742602c01c0c03c5e8060031555041c02140c1e0018002e50141d900292007100320110511401c10703000700502d070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 396496627 1250 396495377 396495419
    0x90f0f06050109050c09090a0504023d2f031b010506090f0618040f020406031202060a02130504150305030f04050301050c121b0c1c27051504 62
    0x14800042006580a1003000d4203d07110802c1d0520303090050000a07c040e401600507214180e844010401f15514141d6800000c0121260151510166141040c140701c40e0f2110781c0c1c14503640221f54104611a01da00160104503002002c202ca200002003450621100a40240303480104000351244075640ca88864014105d40089907915249080c0880c81d000034103880412003034a014021280e481c188445040c1c0700340c04441255640b1400d01411141003898080c2d0001d28007807001c8240001030744443c4c50003180707400322640c54981c0e45031001288913180d6052a40050844d09005506e016003001a007100207200b440c2c501922519028190350255580701d40304040081c0821082c00d0a000302c0364001e100091190402030b22441480c04214010306a80d034050304e03500e0120740800c50809845106d90540d04490540e46491034084155540c011a03501240510072000804090b10704c203a24100800390710f103491249403106002009550030046a82200c0030300c00031800d414030355100c140e47d00c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 396497877 1250 396496627 396496631
    0xe0303040b0a060e0a0b100906091a040e0f06030d022b030b041104061d090402101e09170d1205090a0b130303060f08060c1c05040f031d0102060a090f0f06 68
    0x64600100034605000300090828440035223010015207400c02d20000440c0c2204c4000304c440184621200c9451149030041001100d031082482041c42c8109045485220141d003101c9028100035000d903550100c0d640c1d9440f6405840264102690746441541041e100908011038440d01c001d0008003075900b000445915940f01060401c0354a52080c000100c6121172103214140c0007070750f000718050420003003010380a040c0c0c54841e41e207014820100044032542850440d03440008078400103012080300d2061078103002c0c01c400c484400d00030116851070124503580361494110780360364440b0041e0800600c042e42900981e8039500100d1010454941300e0019061400005515841c000c0d00721605034100d1490581040f400740b110020000f6000d0b0040d0b40c0402094940344503001264240c00c88400c034401346402c0000740001c00403440120042c99210740c407043c1c4804d100d844211011840f0500003401a0b119802140000c0740c0c0307900c10445d181c0540f10111824009447d4549258040c0d002103030059 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 396499127 1250 396497877 396497891
    0x30318140d030f1a0d02061c05010e0612150c0d0f1401060c0305121b040801050f0c0a0e010c02030f01020a05040602010c08040206040b090307090c020a0c05040e0303040b0a060e0a 79
    0x254144524510440d88100401540125800344c1c403ca4074200e0440b0b000f00701c103100c0b5009640c3c6000540d9a0380d1400d4412625220003141c1b0030000d00f07800e2182528842c0c1e031401081c07c615180301500c00d0706a60200030700c0b4403404004182070082e070140c603d810f401802c0003003108030249401462010091080003141c40d0300200c4000c3d850590590001d001c000301c1d80c040000081e070020441c1c221540d05044ac04a03900c41030360005031980c00087c850000304001030000740300b40c01034010920810040102c981c9582c1c03500c6110b0980d1082c40701d90340008046265084039580600c105650840c0084e049412006580740e5490881e404800194041400450100f0185034240250501407244e894242c825003020f0703000c80c40500a80c0240d821901300490021680c0d01d04205020003445030310018080280c800c0d0002e5103030b208140056500b19803c81011a0b43d04050080380d881c0e10186005500d1070b0364949622044480180c000f4001540b030f02070000d08807141d503030914080c18010a00190704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 396500377 1250 396499127 396499153
    0xf080f0a110309100539060618010501050d0e0709050121030e0d150507030b0f030c030601030215121006032702060c0102041d0108070b03040f03031814 67
    0x103120700314048080d034010041042242c450110321444010329041c0307143c941003503400c8508000f2246500d0301d0b000701c989401035805000220801d01410000d01500c4031034869100740291107d0000350420040505e800402c210b51003030000703200c41150164001408240c005142d42404015802021020b0315240188115910a041240d44041d400520210300d00c4555000d800b40341034603a16480341c80303602140424000c41d528466500003540100300b04030700d0304c0400a002000304000c032034084c0200401201d042e060001d101007400b4030040041103075030f1a41d82040008440307000000c905e54014008100c0c0a80101c0500f8043d0008501641c296801d0003001800ca40850301144450818020030000640c0e4810355000a02d07010340c0d9007940c819019420354068450360f80280304205840e104c002c8407082456116041e12a0107040c2c801c020313070b158401d42d43c0d4081510041c041c000880300040009005e980140ca040300d036480700c0410440d86464100303030702141c41e015403c1504110201c0d144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 396501627 1250 396500377 396500387
    0x7050f070506070b220f0b0901060f03020310020a1701030305030601020105060609180405030c100f0609140114041116060b030f030403020d1103010e07081b18040f080f0a 75
    0x41c0c80c003a140c65041540c80c2c0c840512200001e4006400503c3d102e8404049244800004059035048828241d00e50034030311b00030074402003c0b201110340d5480c24001090208080141000300e0f60010f004003041034201c217041000f980300b10304e66006d20540750084a581031000104034000d500070386402c0d48a1514200181c29240003d14182c0304600400c102c061a40e2610a6840d821001020000e140d554502d40f02d481c40c861140d45e48114403400258030b001c11801d8000c8101c14034408800d100049e910748038070050358442d4050000e005c0e00040180440c00c0680c1400184460003403003c110320f40d540804c00d0007a48803c0d1884041d0016120b41c806001e80b600554414090640041c000f00921600440c1c4a02403404001d20503502c41b8070300000e001c60014903130302c40307a4003c000b000308101542d20595208501d1184010b180a180490440f107240703a8808042500080c000c003501418003440c012185000800072541d07032004407800004906e000001e000d1644c1c081d00085e60301d096484014103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 396502877 1250 396501627 396501629
    0x206010e01030c0b030403021015240e130212240f0604051012060e01080d11031603020a0c090501091a030d050a020a0f030302031b0703020d08060a0b07050f07 70
    0x400203250004000140c124501101110500b445154070707515039280407400d004210b050742c0280381c2000e001040090030381044104640c3c402032207404513010407400d004000c40c45100d180c08105250700b42c0400341003003100e8071204000c0440c018a00071025100c016062001e4030f400c403600341614016420401c500c00700c1003052a08840404c243c0c091a000180c051085010301c0d40950000401046010300920903108640490b82d000d014682d119036521032090024071402640d446903400b180c08260103103441f4a0203400400281d8036140d40100650000168511700301c00314801d102c400300c0415000522880508000c0700040f91551400c4131344402e03110141300503c1c58100c3d590407140c0316580010000c000c8400c5080a80d140d82c00404143e0802d81c1d18240a07004552003c40c1d4820960b0580c0150311420341490341c201e8182c2c1484000c480c501402c00014090b83c800300324400120300a404060b8044802061001e0315501c904900f0103075003241c2422103007a4403070b401e203c15000044c42010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 396504127 1250 396502877 396502889
    0x12050a140303100503031216030b090103050307030807180317040e091e030f04030618120302030403090e0127020c030d02130806060a14010c0209240f06072406080d020601 75
    0x50700701f0300e02c15030704000180c0241880c2d030607a44200780b4000c9240243c0041081003c018619005582e40342821343e1a82e004180c12000280200001540f603805890b071030030305003404c680c10000d403030541c0d0b038082003901080e0014440031001d0000081924000b20001c0c450f00c0c4610151040ba42c0c1c1001c40c00d4050440409110103800a204250301d00c03c00c034041d5012030760081004900a07041b55000c1040340101d003005003403000803d0a02c0c40854145d001140140d12036590b8054403559400c803410414400c0c01020381c0002042281c6262605030701000d520105000001840c0c4140c6400301441d680c003600861907070903000710354000042030701b1104000401c000c5010788524900000040d401c0f0151b80074460103a61644441c14140e4410b4040c01c0505901078103405141c00c00e100c40b421011400250760041261040c40041c4a0038a4000e9241280c1c01400160810905035501c000e164804020301c0c00c1072500e21508514411035005250060003000c02825011101a01c000d0804605800c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 396505377 1250 396504127 396504133
    0x36010b0307020c06090a08010603030507030e040203040308040807021f020a0302010f05010e0621030f19030b1e0f060403060c080702031602040903020c09160207080c0a12050a140303100503 83
    0x301a680120358020b810f00c084400e1a591140d039000141c404200750010f030159840c11402004041c0c01500402205029446122441c001102007000b6440308540050005000c0320105000032000c0000d44507282c4010031940c0c0c2c100b00405d0881c0080400c90000e4010b074060014241415028400e0f87c961220840f000c1c030040d81041361844201d440581018052203442c980c107003c8038404041d8184403c03425041d04d56a2800b140b041001c0c0d007000c0007540c1d00080004483d81c01500900c04d14420000c003030080015400180c2042c801ca02c040c01c400394010b10310780d0f4030206503910070000b003018510a650005c3c06a00c1d81100425005000700504113641c0100400515010008805010290704941c041040501440c1c1281040180b0282a800c92903520520101c001145090000400680d0843e00141d41e195a840d5640c45600d5819401c00e202c0361090206144008416121170301035011a2040c030a00e40d036503900c5512110840b41076420100900941d00034003124400100400c60007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 396506627 1250 396505377 396505381
    0xd0f05060a1a0f1005040f090b040c0f02101505180708070f0e0607150e010f110f03060f010306031502030105010f0e1305090f12040e0615160236010b03 67
    0x407030540115034030b071240302e403444d000062045403044080382c020344442e0a201c0d855543e038000c450054580c0003030151150b42000401c19505110b801c141c2091440d550043c80714460243c0a5030041035607060000813440e00d51004103158903000a10495203071468144103a0340761010000340307080c002801810400a44003084080030b0740c0012404185030b821a10701d0b50b550143d1034603118004d500d400200303401c0d00317100043c6180e0130103500440400c60081c03000c3c4400c80001c1e554100b107109250742e0044540d0240003140381d81c102580b50b4102444107040c0090b2a90b126140d10300312401c0309102450b03041e000401401035503401009210114680e040080350354a01d0800208100c1c03031440100807450f03440002407408141001150102c80980c82a600c0c4402e14041d0300810b03030b100c0e0081c22180703c4004e010881034240b45240ca07003043c7c2c02c01010303400e016a031904140c0388040c2c4a4140e03804030908560701c100c410480e5003001c46030b102040b500d40e180b00180b004041c440e8145e001303040b69441402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 396507877 1250 396506627 396506629
    0x604060216210b090a06050c0a030c0207081009060f06031b080105072c210c0303030c07120903240b010f0519020304090906021b0325020d0f05060a1a 66
    0xb0444081d940300b055994203542e0308071510315100100d140601924140400e0004e41107240c0002c00c6020119a414490350ba0003d41c01d80c1d582c2d03518444c1e48015401610302d428140d8169000101c001d10480c00401e60441c40380d15a000e03a2141c0c1c0042e036500103a0741c1c0c2401c40f03402a100c2d4800800e01c803c001e0081d440c088201412101111609180c4190310401c0d514524041303070b00402c001c11b00241181032858002101c1400a180c28160b0885031144021340c68032031400000307691240d0403640007180b41c9040fa0307580c03039180c0810040601c10300c10140c1010000070058848080ca40b410b140c001050300c3d070844503000075101d180d0511414040c1122160052035841400c4130b802e2240414074600d02502984104d1851156501c41030303d4500c0c160240c0c04002641d0003d21040e40c11424011559401d0091151a4030801003860361142c0224540048004002c90142da40707400180018440c0d0380035260a00180c0014100b2903c98100c40d0030890981c26920030b19800c0498882600a1804400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 396509127 1250 396507877 396507929
    0x20703030305041407080309030f01050f0c0a110307060c031b0e0f0d0206180406241202091216060302070506060f040207140a0201090e22050c0604060216 68
    0x80405401c0544400001d0240107140703e1000703007a24a44112103003030f656003058a48039085050007601c24011150561801081402214005c0d50011280c0b04c4c182c4840340e50b2a4140c3c00080001d052001a44000c03248034001e0020b40b5110b03000c0da4020444500c0c00c0c00c020100c1d0211861609100d68070020b03aa48141d0042e5a104100c0c802d0704c0081e822004000006c040521464009500c01000946d401040828038110403c4013420740302800410388035140c105540c0d440c554001e080c2000307405501c2c1050b2088110425000044200500d00031007640417412000c140b1202c01000c0d030110345c280510800c1020700300c006000500e4218248150350742c6040d214a0080c01d00d0344121000740710356800740d40c0c95040300d4031560301203500504120101b001e00d484080012060380071079419140010382d40f4182803050f100d4580861003020200c2440c070020280c80f0494000d031040d2043c103d4041e060740351480100042c15440d0020205812071840710000400540c22100190716072208450148130340c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 396510377 1250 396509127 396509129
    0x60b04090203101508011e0e15010203130303110c09010501140d090f0302010c18060207060302090f0d0b0a0c0c0c210b010f1a09030a081c02042309041e0302030c010f1e0c0207 77
    0x8100d0074800c02c06080010cc0c910b0082d620f03503100c6000c090343e0000c1055084045580320055072421341710000e012004010304024244aa81d0205950f0425030307040c40d010400400c1030000c41740000030b07184169264a0507981e0b8080781140036030740d2385500b40e040b56007005901e1080c803916a0380301c0c0e12a040c01e2000307407604004d100e0305c41415004101c190a90303885c00e202840c84003000d0000c0c607201889051950502100352580358602d860001f00300f4503688178070103203100b15410400a00e0440c1c5092040018030b10110550f8200f411840e0400c0000341c03101c40380b00e000300941a403107045281441810f0302c0380d00381c2d500ea180300144204560851b50300d010440700725054000b000f45886030b103100048083c07454030b801480c420910006010601189005425000c103102510740a419004c4c0d20920281e41d40035900506a04030100e21014501c20b03e0010402403403191054070309143e45440d0840c25030344240307405c668482c1c8601c1c007020040d11a0507822148451000240060700781d5250180d150300b0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 396511627 1250 396510377 396510391
    0x332030901030906020910030c120c080610050c0d0302030106021b0306160210020d020a0f170f060118030501050403110607090b0307170f0118060b04090203101508011e0e 75
    0x2602c0f039240510540e0b9050351041c000c050f00303440249108900c000c00401d003006020300400c80d920300c1007200362881d00c00c418410b010b50300c0d0a01140c407460200700c1d202c1c42c9440c0326000c100080000820015041c0100c1a10010f580c4000d42c0781e5041110103070928034840c9114020101002c4110866580000d070541c105500d22480e440000004004a082502901010b80000e00020301c00004001c142d00803c0c10303940960b60030b1000e40c1040c0c1e007100c1000c05100361020440c0c5000c0460305006000000b69040781d0305041490b038050310b24400c1e6180b03040990090720301d0396582d1704010a25411024803550101ca0801a00b42403400c00000345c004034190050b503403d12400300024810a000c0c4100e91541a4401c000c46200d00e4030501240300241c0900411480c06159000e5035648034140c0a06010b548213002c600b0708084c00c0110313a01c029000107000700340c440001e01000900807551944506140415560a40c143d810204405182d0b03000c414400b05a10b83e900c070402415814100300707900001c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 396512877 1250 396511627 396511631
    0x1110d020a090503030f03040507090506010c0b070504050d0b012d170a02060301090b010f020102040506040e101205030711010e0f06280e1206040f1b09020301033203090103 76
    0x40e10301290a00302c60f4120702c1d0035200001d4080c10034101c0300c01a40c4514400c070121040305860b040342200f030750010f440c1e4901003052407910074000340c84035402d1580950b45240c031130b040a5840002604c046042e0600769010040100103100794061907a40316404010901d08824000b0204019040841e003485540c071220480454011189000e10900900540082c1425165611b03003020000524420401c1d502142e01b100201d07407640c0c01030003510211503008104905262500719440c1e1000401048000412032460010401104030798640410500640085807241000c0c64542d00f120801100303281440907441d200d0f4031550703880014090014040c1c0320030382c41e00400d00e6018031021a420000d05040080c00d180300103c0e42c4103041c4418050125044401502402c10013622130300c0c00c2c0d0b03028100903e824200350104500d181e284c3c01000d805040c40780350307513030710780d41c0000726082038204440c4d02d6a03408010011180440807880b0444401c9910710180e07403a140e01581d288248981c4a042c55 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 396514127 1250 396512877 396512887
    0x23011d0403020708060c04050f0307050901061b150c081f0b0705010905010e0c030d0908190f0515071101020307080f10121a0106020d02060103081c02270301110d02 72
    0x5100f4800940141a0482151403904000312045800d0301715014107030150100b5180712915180000744803040342c2c0042c100e100a64200b5000f2603803005400000e410091500080703000148040e2103000b6046046203000442c0082010003c00003071016040081c0ca402d03120030044100c040c044803100319581d4000381c0342d543c1c0b031910b080c0380903200e15207010b01103528020b11101d1003000417070740e0200080c1c01c40c26036248080302c190595400200340070b132106541c440d541080d000c43c800713024100c0b45030050b105041281010381c1c0b0780d440d04250403200d6400139000c0d000d100b10032ba0032000460851901400a6044d4a041c41d0b0080120000900d518540f51b1034102080d88107156844000c0a42100b2145182002c52418611203d440003000d01c400e03010800000580749101241d200210b42d1180d028000e145d1860316000c1c12034011000380460340e49601002d65159150b44002d1005422100c260352440076039100311055251901079484c0280d061440924a584103001142c14118200b00016219 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 396515377 1250 396514127 396514133
    0x5060303030c0d09240609110f07120509060a0f03180201020a0b060609061206031212010e1e09100c0801080d080a06030f03021507140313061e23011d04 67
    0x880828003002e038405c0170017090071942d00c00130717003180041d00c0c0d184900b800109540c1c044109984110f10b8804410701e0305003d8800000c1845e007440c0e5100740e180c506a8100b600f0a00051415400440f440d13003c502c250f0b40541e4140d07054050016620000f001c4c41c441c5d1011900040d4403071700820707002004660254001840c03540d4113025101804005040e05031118419103843c40003d0341901c01d039109100e9040c414014100c900125004010981c1c0741180396480d114002c0350f0104040c200c121040a42809040d0844c081c1d00c4440c8a800e4500080070300035080e4000600301e0f244108120308002490006000c0741400042c076014001c42481c1030318403981c0d02400e00008080b00d800083c80518811100e0040c1a40013400d02c5049000084004a80d141e0101c1070310b1081c80303002c10388021101800091030f81a60752031041280c41c014030703010400107041840f071070443c0814207180c44a80d1707880781090025400c5107000030703080358032131196289035050401c4185c140401000d556407072040c110001d130030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 396516627 1250 396515377 396515393
    0x100e01060c0c092c0d1d030a12030906021809070c0c05100e090f0601090e060a0b03040f022e0206090634030605041b0f03050a0908070c060305060303030c0d09 70
    0x10015031414025800201380c40e041c0e11101804100320000360118032070901300b5494402480002c3d402001040c540040703035101100c007030502038103d040c107035550f03002008a40341e800105043c500c080c2103001c3c0140260304101700700c3e001400c01030070018100040000280c51a65060a443e4101d82c0d180c000040b1401c00c44000010780c50217508003c20300240600c00b402d03849001d000c1c600980b66112030548810b050300d0b40402c1103407400e42c001000380040020006020056030014050041114010071a401048461f1003016581c020010401200340d40301c0d0006d02020254107461000d40058140007007403e50b07a10028262403640c03a0f5880c068102d0f030700e000070320a1011302002c0118461125201015000381298400c1601403410710700702c01042000c2c8501c62440056a403925032420010010440051200a0401c0202507a41c410100420310a9000d4001c4070b04c10003d00104a0600000900341e90010b00847e00070740c0103000340304141d10301c0c5042d42c400c1807402400140012050400e851 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 396517877 1250 396516627 396516671
    0x14120103110d0614090105010b0c0a030c0303060b03090a03020c101d030f1203010f05270c040b1209010608010606050703080403050d0c02030c060906010501050403200603100e01060c0c09 82
    0x1120514040180300b49a4003914130038401e40c4554000c00950381d8811801b141c0d40f044424482c242e401c05048800001d01988440040074004c1c80d00180c842e45032252620160320550f208903a40d4017051906040540c100945421b005082d00c405100c14400358014110ba03600c03a40c0425220382616407200162020010750110800c044121944161088028402c5901c00e01440c440140003a10114030303401c2c5600001034036032030b14150404031410002e25902c02c03000604180d400d240708000004000450001400d11010241d01880c668200744180608503410b9501550b41641040300810240340c0003800d84298a4150500305110742e1945030840706481940c080440e101c0c0381404001890b54008060800c14840000300c07106a11403824440c4d036600c2c24803416000560410007400041d100e5901094049078140403400080011000181590002c41d06001070307039904602084601c2c440c00080340140042e09005046000c1a180d4080b045018082c000707440c1d803a00d417141e000c0800500449 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 396519127 1250 396517877 396517883
    0x150c010209040c0903050c0406060e060a090512010b090610020c10110d091d0903091207030b070e0907030603050606010807181e0608130314040e0f060114120103110d 73
    0x200da12011800340c00110b0500040c0c030f147c4a0080c60703090608041c42801c0070344229440f14070b4017406d940308100c0ca0354047da54000810008010001d81512038201d507208008044e0f0001c00c2080501c0c061001011000780440e00c210001011031442d1500825036410b568425a01c025440119403c00d45110640118410540c03080c11030b0202410b030f00c55804010303110f284c0d143e2065230350740110b0310302400740544502003142c03c01c000c5010300307260109403020061148000d42d903180d95070351507286c0364240031900c1c2c001103280c0101c0c01039140382c13110b6283c1d03200f911420200100d40c00d40d203c05035505001806581800341039004180b0f218001e2403041691020911300c4100b00e03450303000201d0780151180b450040d0304541c0c0d501084d01801656050311400805040d52800c0035580ca086425002108030200003000c1080082800e40030038104c20b11420086500b2081410b22500050120302d28900b82110345034240040d4081d0b030124060141180d400001c0d2443c03940c580c0c4002100e60300758140003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 396520377 1250 396519127 396519131
    0x906130b030a020706050a1515020106030b0a0b01110d0903060f0e060406090b1509041b080303010303030b09010608060906120c04180c080309150a0504170604060f0605150c01020904 80
    0x1200b008260010702d083c81c4220414445a1100c1c0c60140030b49000c10040c011a0014500034804588080200c10000e4518400800e1040c2e6170344540c0d00b0380900390751020507907403140454082560040e111015810605005003501c2c0381c0140c00920b81001d50100800040d1a205448100c0c0065000010345000e92400c2d62900c0c02c0038a000d00c0102a2030320200c0305520800000f400c2840040f030034000b607031030141c68032081e9510780e130b902021600340c828584012092444045001101007024602a5100e524002611080783c406c00107050816804a01088540c1d41004007d40760300e94101e4100b90f0998054044d4070708181e03042c0c101f02c03002e015190040e248c140305007400004203800359003031800f0302c891200440c1c4903607103180c6134840c07020f90541000c900b02c0345600c0e090b40b850041421048503d001d9080ca80c49521612002e140d42c407121b00e0f07030303400a8184424021948921110b01c40101d01c1004610b15081c0800c0c0d190164110251542d00c0c041048030a025083d01110748030300d030007401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 396521627 1250 396520377 396520381
    0x70605070807080301080c041410030605040204020c01090b0708010b040f050607060b060a030209090c12220203060403080a0e1b0607060b0d0f1a0405030306151303050105071805060906130b03 84
    0x650f22987c90314602e100314209112400801c100c00040e03401001d504650554107402c5445481c0544400740080760016070030011240407003000e108138500340d407107202840d440d0f05103070350020040401a081000c50481c00c00c810091039000e5030404044410503102152035141c030f414100c0080400c851071540110000688100803641a4014194450101c841e0801912400490b400500031001c0100c00c1141c0d2202080ca1903121040016401400101e000c1100c2d04e40d0303010a0074150262011800b0600400034400c5042072800b5880040c2041e40007490003019518520340320281e8084090b0013801d00007043c0081c80080d41061311907600c007034800c900d442c60360f10b80100049180c03541030b140600b08100991490b22010100c6001748d13045070040d41561900302c10800f501c0f40342c80a0440d109800c00c20460b260a02c049500002c41c010800060319140844015100b0204641080314260000134103005995941003034542c0000207031600c1c0d880b0740c1e0020034051b00c005190091140d03000b0200c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 396522877 1250 396521627 396521639
    0xf0c0915190b0c0d090305070e0c040801140610020d020a02010305091015150503010b0403060b011e020601030b0606040b0336010510062d03111803120408070605070807080301 77
    0x248003d850351401c44040d00481102101c5034216404001c05a401640c0308001600100850719001400312400314a01907a4010179030860700e02164013030168107041c0400a079071030700030843c00705155180007500380155100d100a4507290a040002d040c90741d2070f0045800c03003004000c1444d034009402e804220b06245100848841c0240b8403034282c40604044a04a81c1803151040c1d03412030f204441c2c0076003800d056649441c05401801c0520781002039540842500040000e40d0741120486a0041c080c15411818200800800102080d01407001000200004610842200e0b03000c0040d0a900c2201a00d507500d18880039488200c0c0e00c3c104c007a40000c82542d541c190300c014020701c4600030403459079507650030a0b2003034041205082400c400d0f0521100300f10f142d0300b0106060009520700000c505100500c44950307600004c0c1e4010810314485415041428100044249d01c100d4403019414280780c14201e5079904c0050080c0f008101c400b10345030701080141000e4410166000f40415225070f1604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 396524127 1250 396522877 396522899
    0x806100e03071214031215060d0903050c060a0204060f0305270f10050411100c022706061204022103040603050604051311011b0c06110f0c091519 64
    0x9502911050542d0445204e0000300004440d581007408030049096030b2100001210b003400c401520350459002c2080e103c14490610030011000c1c07080e1a5107440310b0488005602e010340090010748510710401c421b000503500000300b907120f5240c0d40380101e010341d41e101e51404116541ea080c1e100042c85940c0394007003140089060901c4c1c000d100100c8601c90359411696054a40968020f040c00289000c806c4513410040c55280b00100e041c1803a85507000700d503010807054002103040c04074840d01704403000b00441d102400f40382c00510441d00750f030408080b010354030f80d09440035100074410038030b043c0b54000c80b80c055161304251210040c1903e03202c5556000180240804407540c600c107a1500000507404061068507040190300181121102c2c0323400300040d101d00009149a4a90303011140c2542c0018203d00101405807009035508403090003401401468040040c40742403c0f9007040e0104000d0391a1580c045a000040da903800e42d40c1106540805d801014401044080c105000008214070401c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 396525377 1250 396524127 396524159
    0x4090603030f0f08010f090c1b031e02030306151b011e050105030a030c03051803070b070b0609090c0114070206071a011a0f0306220504021f0806100e0307 68
    0x1948446003000740c03004044a50403400d0040400c2c0d40011b14051184020644c0034070000c1a031418030080d403805601070102c1c200c220b1401280050b00803c56a42d4059a002003440c4030301c0203000550550900c40001941c02032410359814a800c0007107040e5120303181c003249640002030128001c00c44040303211403543c4c44400b20b03003c866880341400d00001e140d00740041e0320b4840d140c040d603900503982c01c260f5003168190300c0b5600061084c0c0c00601103454968003071000c1c400400e0911085c41d541c804901c2c0500b00600018206440350b480e403001c1000c0e0003004204888010800d10340090941d5002d0740645080c041c2280194000d84045000d4042100240049000203861204490035a0743c031803520b030000c80f4030343ca0080d003000f05211604a0581200c041c1d500508018000685400d00364510019421200c44001d000e5403940d003440f055040a01161800c134003000500c402c0b901407402c010703001c0e100203008240503c0b516185d0035043c5202d0030381c42c0a0700d400103042d500025a50840c00c0790075941 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 396526627 1250 396525377 396525407
    0x60e01090e1c051210051908010e062208040e040f11030c06070f0f020315190b15070c03060f060603270f0503071a040302010e0c03100b060409060303 66
    0x141c00c1c80c075021040182d80c29000510b82c0e038520740352900079800e291442d0406415030072556400c1c440800e4580e1a0311881581001114404c07161502d0041144c3c01e648902154202070340000c401d0244619040e00900e842d035030002520101c0c00035526001406105039401568060007003024032003040800c140306071059005208404ca4002c10344105511a00402c800e194010800c000e504000b40311521501e0301d00d4014544040b8001e69034010904000c8d080442c0000c88200e00108540d012041401c1b0200303010002c0200328403940c000101d10051840c50201100313a80120f500010030040100792006554001d809000036008103026030050916800782d40d0100c6e0401d649801c080060054000c400d07803d802c101d0490101c952914030700022000d20a6403107000070026680420520025003a005d400742c0301c00405481c6c20b05009003195001c40c2208110340220b8a60710b85542d0018400140c01302900f03000a140603240700061440c8035650081d212641009000014590008503031041c50030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 396527877 1250 396526627 396526633
    0x30d021b16051c020d230c01080708130c03060203011412030a0f0c0804030b041406040b1b1209060105190e070507061d0f0f030c06010b0c01060e01090e 67
    0x5034000006032109101c00c44411900e045100c2003105150140106000c88031042c8008282d04041e00415010071a40f80c00340c03641d642807524130340034400d11541080710013000b4020707040141c50f13000003e200e12006060401008000f4020851700c80c82c4400c201400c9610041000409580346000c01c00394000348a0400d0700c003412104005182040c021100740c149058002d1803410401c068181d4600b00140e521a04000c071802c141070001e80b00000a0018502811144c8160728041c6042c1c03c40000b130409085550308580140000242c89802d4640c100c83d40301d10726007805800c49035032840d50051082c1884030750074604c00c0c85043d18003c50708074165071096822004600160700c0d00c10050149124111008999400007a81c0b0f604c524003520116101d07a034042003c407a04402c8945e6841c941c4103407040c9410203105011b40080420060036841040c4c0c010754207110a018505480381414414094038480005171420189820751040015001c0210503942c81c1d6112744501000700320070380394003c2901c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 396529127 1250 396527877 396527917
    0x80702010207020a0306020c0a0b1504110c0307061a100905090a0903020601030f080d0204090b0102010e011808220f1401090302130209040b100201140a0903091e0503030d02 76
    0x19106008071000da030740203031440d22160315607030310340c2d00a510010080c4114094401440000b9000b441654010031003c02c201c0761081c0041c04000032070b041d0101c0d05103115020065841000804000d807038100b504000d00041c2140a000511403000700c1c1500558441000341c00145110b8000000b0400c0c4d4400703540e0250349985000041c0100ca840a01c09409607106100410000d90440e903001c2d03507140304203461800e10160540d58010380e0410340121200546800c3c0302a15568244949405c1000070130007880105110b0400404901c0c9406002e451044000351101b14041039010390b10240904000400d5241d40c0c400440c18141d040f800b80481025002071002107035849090361500740c1e0780041c800c13280d02000e640450001d40c850300442da002030301c0c0d444092183d5241012851201c3c0190000300740d150500710400344041008296844282c5001004004a903000003400213503503014001c03900b00543e248407028404090341c0426494480082d40012000c400d80162078034191180c488034900c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 396530377 1250 396529127 396529141
    0x1606030e060f0115090b0406050c0c0906090109020d1410031704150804030e120607030f020c0309010305180109080a0909020c120d020f0f1201060c0b060d0c0b071208 73
    0x110816201484507000120060200d000411442d180c1041c180c14a42c030590340c0d446d01200c407608507500c08008a0400700c3c0d012110700041c080381710440006c45903109a031800000142150034107010f10f5000d0b99000c501c00c040008154044036a1507040210400e05c2e1a201481c00d105024900049500820002114003801d1b0021b0076a0f080d20101c80b032000d11000003000803194102c0042003035081100e041d131091070546030b07840038010381e14041e030161140f03141605000d000d5505030740082d20940e20400a0b0840100c0101c261818480e0074607000c206034407503e203500341d100840c0c203416015520f008a020104100c134001000e591000782c5400c1c1d041c69580042e482240a180f0040700070b07030040341c4140900700c02d80c001445904d810281c014100381300d24841000b01d070400c1003094088000040e0032103000480c54103540c01440350b4500900000484c0c0e0b0f42484000010300030a0040c4400c1410008201007100c0307400241c0003001c002c9440f5601c50070300c2800b400c00f1480c2da0002c5207101d8081908 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 396531627 1250 396530377 396530383
    0x102010e06070c110d08120601030605011b0624090603110105270a0b0a02010509071401050f090d0b04061b030c090302131d030711010c0c0510020109051606030e 71
    0xca02c210340c8401da595002902c0307038009406140c00d00380d40000e404ca80000003912240c05486580d403404503010552a0840026003200d000e6000141400000044051403001c64141070302400e622a401113150014a042242088082e0400e041412070342c03a400303700d010700c40d40b100d0708490080c42c4407048441f010005407010b1040e00660a2048d01392200308410700c0c0b940c00080300580c000340107400210b0356003003a00310541061031a440140d454005029809000b0000480540350122002806000681c0003804500c1202d14103849080e0200d1886600d80c5c40e03200c4001403d8010303c03451410715080c50443c1c001c00c04d0540d0406111900401200107500c640301d17485003002c40d52140100d030b03030951702004403a000c6203070010146a1200d48010a04280501540344150101c0c015a00c0b0701d480e00e8a0460020581c48443c100704914621070007241e0781c00b402c44100c550507076039160001c1c10410100d0240088250107000380c0304004d8114038404081d900001180d1065904000c08641d02c4840d0391 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 396532877 1250 396531627 396531631
    0x3190204031e110310060509091506090406020d090309030218190e192402090a090902010c0605010618050607020607020927071401110d0320030408090102010e06 71
    0x101084184240b41c500c1d8116920aa0340034000d420380c03403485900000e103000d806501c0410307090f4589004120906208440a401c503003003d010f400b02075130652112511600040c5854480d941a00c0460207000d2a50304503045207840d50030a10813121a030034054100e100c00d11040b0701901c0864201e904c2e415032004998040c000256503181c0024040c68040040c0c070f03a4041c1d5109a00aa0150301c9200c900c0d01c885e50f400c2031248034641c1090603071010488441c112070b0880356030180100000442c95842408100540b200303000c000881007000d00048402c40c400c0072000b0615490070700045a0700307030416030318000c0c00380c2c4060024816407520107000c0b00c0c0c000c01034002d403c58420700c028001454804450740d449054280d049950f1400f2510704c9411502001c0d11607400e411a000500c8100c407601200107030000e00382012030041d14007040e150b40d07a1504a050004159803071140d20310819048280d43c560700c1c10f15040c151a4105414400919400f54110794090b40c80c12004160310303540810254 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 396534127 1250 396532877 396532883
    0xf030810060f09050613050402031017211b03032e030201020a06240b03070201060905072304090905030d05090d17070201140c0d0509060613020c120c030319020403 72
    0x3101d40c1340205124140d0401c088240c400001c203000419192150b1010318410b101c0340090800c441d15000d040c60b00d00c0b15041058645802211050022890780f58900240301102403800e0759502030b54002e148401c211841e09031880c0000418070050903100c081080f001c1c1400d0340c080640c0d08545d164070394210400d03c070090160300403400c3d20b00800c889902c054001c0203401007140d000030303143c40403100120090300400d84102d004814850b5082c4d0900c9080050b240c90103041126081422001c1c0840a0412400109d003c002094035040c1480754159402000708080900c8054054641176881360424801001d002d490f00d00000c12481e0b000401d40d03501c0900c0c4d292034014448807c418001c4509c01000b06043d992551803450549080c04221441562005941038440c0441a5804252240a04110f131254400b00a0216a94956583c8060b000f10001d0040c0d845d810b034182c2034241915420784801c102004100c0360110030012000350320036020f40c3c4a200d00a024107481c1703022030086000c06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 396535377 1250 396534127 396534137
    0x51005010203040620010e0d02030307180e0406180c080c031c140a0e09010f2c0712090804060203070b13030c060c031401030c15020a0803040303180f030810060f 71
    0x1407030025105c1d06041c80040c5928004100240d0b400003980c036103c800010076006130300002c104060190b01a504030381c0681c00100003405240fa00945200c0500041c10141c401a5245000c280700014442c040c105c040d4044010098660348000c01034860122403806400b07070007107010700f04403000702609460810f00541c0326144451401c441001031500425480740c203110003401010f4a941d51001c1060080ca8805019400c2c2b40c100880c804c0c1c0718038100d800d1640780d81040d20580198800046090340001d00d407030f10084001c04441210302070042c600c409001ea02c00041d022a20741c0d4080b00604819008000f02842c5840b032100c00d68640408a5015000070801c018050000300d0a80100f00d01a0541c6008074644100c100b40d00c5400ca4203a0046401040380e80003004030f0328903c80807458441060010301900c1e01c180c0c0350160140b10041c4020201940c070905100c0c03250380c4d500030140c2d02d50082900100e406151070040c09c11482920105245a1041d1000500c141702e10342d203120f610b170342ea902e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 396536627 1250 396535377 396535397
    0xf01020f06010b0a0909020c0616020f1e0102160809191d04230a0303051614300f1302011d030102040504021c05010b070807030804080d0203040302010510050102030406 74
    0x820a0f0364000c2e108041c10810700320300015680c1e006001400040c045100034100d030f0300303154132028042c0380f07144a41003d40d00103404110f84000c0104550b00080c0c0381030351040c03004658000090091249002400700d0340c40340f180381010300084001400c05148151644e20400502d400284500d011a1003880318210082e9614404056650001500148100c20442d00c1005500d020203012010030940074840c0d112083c0007050651501985405c01c07100101c245151804c05401015881180d07400c80030a840001c124080c41000c0ca2581100c0f440588a010318038191f40c4002c40042c0150ba0201440d90101c0206075103545050213200c52550507103407030300c292080c0741c010020301c071007404040e5140d5400d0000044c5610741c3c0c0000c224100444505032a911403142c1c11204455068100d40000ca17800d0081038002500c81c41240e814580600b4118a00d581d030f4a810b81e011700c1440300c0e0718066030000c02400f08061301500401c0c010303e00e1071401c000c41c81d101c000490f50f85c0034a1050308009441182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 396537877 1250 396536627 396536639
    0x12010e071202010210050f160801060504030813030605010e0a060902030c0306090603011506032301060207031e08070f02130507270b07030504050909010606020a15150f050f01020f0601 81
    0x4581c14a01e4410300549042084103582803044500450301c032031030500030204106640e0608403070f90443c0c07442410581901c1d414110000c00d0b070b024070b007c0180362481c00205180a01043c04600c0c0065a01400520056860380000c60300aa002d8450788140b509010340401e80d01c1540c003d40303224000b140340c1c0380d0855450808000300c0b480d018003240d8040d540d5112940208286104440c00792210303803000b0940c0300700c0e5240181c16016500490340b14406110051003082e6002ca01c00741101e822281d6281482c1300c00351080002d0800d6800140310540c00038850040085400e850703083c9900807514100c00006c000c20200070340300708968803000103000d095000008801c2818100c2170507906c02d07540040750b031100b0400c08140c0c4540c006034041080410104407030f26040b002180d101018030002d001c40c0341782c240c02956a8604240047ca20560300111441300c00c00e03588681082c8408074111040d0356a240c00d1001c2d03106c524041e0380c0c0180a030114120140d400040c1054001180000400140e8a402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 396539127 1250 396537877 396537899
    0x20606031506060909090f19020d020d051005090706030f050f180c0d110901051504060807050d1a011d090402040203040f020a0306150501110c040e070801020a090512010e07 76
    0x104207540c4850f00340318080c0c0d01e03111046000c6c40340202100074908401c86646841c03030f0070913502c810180070104506500060710380722208500381d6030607100d040c80840c07039181c040c0c00c02000b0611624000c0c504420854123000000d0780038120750a07900d08000b41003915442d501074903021501c218030247c00501280f80e0b0150901c0c0702810151450a03580c0314202c80001608608a880081d01d01560300d090100052410b90000b03801010211941c24844031100802d00d15405940309480a101c059000101d545003c0c00840799107039140340040040d00398020940e00b070a02415203c50001d140c0000120019001029130a00d260000b408003482359281d80c00c00002c0e50004000301c46180705040c000b40140c032030741c0d03854019600c11030001c2070140c3c80b051f09500111090313000504004044d4036032900c200e00419015800641602c0c00305203894820240c0346802000da0102e00035610028080100d1a40309540354117441c000c50303e80c00966581a201c5c0e0a03116111858541038200d96010004901e0340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 396540377 1250 396539127 396539131
    0x702010c02031002070c170d120c0c170c01110a0c0b041a160e0603040b0a05060307050a090608010608160e15030303190b09040b010b1308060c13060206060315 70
    0xc0071038018143d5280c0c99070698009070b90031201115454018094001803100441d64807810f10000c2085101c0d04000401c008441014043c0542e902c14000107114403960b100c654168007d00d00310404051b800b070b00c0e64164041040b00c400755280c04035a00d051065401140d0b41910240d0f241c04010040342c868803800d502c040c10032a034840c01d812030090304195070815248a5518501c2200c036100c2000c074050903a070724019000c0c1c401d0504004000001d40e580e00c1031a00a1201000001c1590b04d0102280ca0544241c1146a02452081002510444940010b010754081400078003400f96112000c903941c0c07051034006200900c1201040c00802c81c2c00e00ca16a10072004882090b0300d000e00c9000c0390456200b038401003040c070b1300048007601c03c0d425400340e010340000031b0780c4528061600d40c4501c034040c04103014020080c140051018002e549140102000c0d11400041c1c4445d42002481101241d00c80c4200314000070340c0400004407140089417040c801c4201802522150b5400b60380b8070036403180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 396541627 1250 396540377 396540379
    0x20105060f13240311090702010b01051207051b0303011d060a1703130902040f060507050a14151302010816080a020d02040b0d0504030e030a020f040c09031406040b15060702010c02 79
    0x20807002d000c0f0300705030079801c0000c1d4010f1440700080d865240522001c80f1009210317005582c141400441c1a0740d101d801c84911240c003400318541512581c00803161446800507030003d14600c008041d40d81400440110b0489500510500d5441e034410620000003c0487c1c0c05d9a1182e00321204101100400400300300c44052101920701d0b06030785142d60722500d00140c0045400583c081414085109000d800c000901002e042490134001503030307102a07440822000050909140205100c000e00301040012140e1007411303003113800d61402c0c01c2d614040b4102d030101a030010b003c5001040000220320824010150703150380d81407441d84e030a84010040e40c4007068043c5050340c00c00c4002a0f0f01090405404140c401460200f41070401c1d06008115156003044a4401d811062880d03006a071144041c0b016240107903400320390070801d802c0c1035075002001c0c4d01c007402c030650388420240414400b04205109500c0b4030480d500980b2244180c07010b5446200c03005400000070056080590b028a0020504603c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 396542877 1250 396541627 396541661
    0x9060a050a0b0319091115091203120606030601020a030e01021606020105062d15040807060f1404140603040507080d030c0e030c2b0204091101020105060f13 69
    0x5652400314400010aa019410b018004400d02000c00528081403801c008034240600803080a034403046e601000c46100b0610a003a820b2030403104030000c00c10b50341528002000c0300a500341500780b02c0d4803a4032a000c3c00a0304148c0100140d154034100095900514042c0d00426143c601e81c1c0c1d0644111505608140c103603c108000e0304c0390b1050595800380505034541c0041414181181408042407a41c07041c80d10041c940144250081805010035525190440d010100341071201c0d42c4445030703c11030f008240540251403001c00c9040d0000d16400d49121541d84900045141d080384031400d0103240204601e8580380c180e458020314100c006507030801c6c0220155107220759542c01d010310b1720006800c1240825211a03c01c50b10582101c000341c46642d042c0d02800c2c82d00d40b0a000114500c8400340e2100764107801903110402d40401048884440307502400400c2a0f15285c03c0074407450000d4400e0500540c02c05000502c035080024110b41d00f08809000440e204a02c4403510000d0602d40704041003182c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 396544127 1250 396542877 396542879
    0x11010923030421021e0603070f050c03040906031704051507080c0f07060f0203030c0a0f12050c0315040b0d0303050a270c06020601080624100e090601020c0f09060a 72
    0x3900c26010f4018180d1001210031407490f03910601034110001c0c101a841010120b05204240d11400700b1a0381c0481145041c07a284555142e003980d0ba4003c0c0f84c45254180302c08140030903560707580e50044050340e0088954590b1a40891003c03100d611036406070036000030104400c0d25914217442c005c0d0407070602c90320200c0d0600d0300302c0401c24035080400c401100303143e00026040100f150420851014055030b840514658580b0310344080d5248280074540042124549840c010544190440c20308144224028802400c02501800864006582801443e03ca605000c85103181c00c1c031803080450009055051121302c2c94400b6001404020500c1144503280c0d00b082c07072010505401146c251700e119880484415050a2202031090140c004a05540c4484014400c41c1c80001d0b080d640f00903d1103101300c1c158085030311141141120130031580c110f851070403900c00c0c40d40c2220800c01c8120b029130301c1903219035840c0012a65140043c051603040036078500c1340755141c1401c9600c603a0040015102103405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 396545377 1250 396544127 396544139
    0x11060405190f0219140316050907091d061306060f1448070b0903070f14241606060308070302150a05040305120a060e011203110109230304 61
    0xe004403090788802506a0342d01400040e415501c8920385e104107a00030107803c11030072512070202c1600d0090b81d00c0340004100007080144111032400c082c041906046540c40100c417401280003030240e501d5807141d03e4088801c2150302c80c62040000701d40c0c0a545088100c10050030a84440d981c5024026141100300442450121f81d81d0741c0403d427290040c42980a10600041c803003803070f00403440a47c802c00340ca2400e002c0000d0006100c02c1034a13641c02a8599030050240024a421559484240c2e0200410000942140318500b400300302041030307445000650240c3d140d00030300c01c600000050003132002d100300c1b40d044040160300c1a1051041c14001502900c07610752100c190800707401100117a00000c44a000c0d400301140c1c0a41007c0d0401c0107103d81e017055507004c1c085000c1d41c4002d89200c9031a6002480031280f90b00118010302c0c4014001c0c1072541c441a041c08038000d03510003500810858a204840750300144522001540c202404080c10000a5100c0c1070401030043e0080862005210104603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 396546627 1250 396545377 396545389
    0xa0f110703050f070906120203070501050307020a0c0303080910052215020c030a090f030b1506090d080408070b13030303020714010f0204180e06040326041211060405190f02 76
    0x4001000f000900c0c5003442c0020103002d03101d554000090004090283c480141c070f0014208060303c3c03007420700c180c40c0d5541a84c224030701101660080c10100140d2400030034941c02c07000241c040e80d16481510f10703a002e45001c902c00e64070250790311801c4103410000400401d010b16295808144034000861001e10030800c01010382c6c001c82c0b4000b0b401d8000061a811141d003084644000b0108140340101c01440c54682c0681c010000740701200d5800503c0d8072282660f0740c802111300b200d900410302e09030511103042c200c105401ca4000e801240c0318881000c141003e805003540c0e034403004480c2c4012940d00b540e40441c081c8d04078010443e40f07410007104c440c50100013800703048461005440c005031294a09458485074801050561ba18980343c4800c400c1050303004a141c650294040c10840e02a607004a000c61511040c06040801e079490501400200b0074100503074070800c002540c0303055604148420341601ca11094800030a1688001e10510003480601d02c404007090040c058019001c0c616004100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 396547877 1250 396546627 396546643
    0x31b08060a0e0c0307030b0c0f090306070905030c060405030604021003090c0e060a05040b0d061a06160c06030b061207030b2101050703180f050727050108030a0f11070305 75
    0x1c01d5036262022040a00701c2000f40076a109801c400515010b883c64a4078605100c4c082c09902c2c080d803000074119000d00000c0226248020b02074221803182c9001040144000940d000d01d501ca40a8046560030701d02e811000d80301921002406004076482e2582000401020807601c902419105d13110b1001180142210900814919005018074904042000007420894002c603100c1c81c903050000400b40c0790045005081a0b11100c001400311003505117a8260707401c24a0b5941c130131000100c407020311a141c00491174281c882c00c0c4103042c4548030603040d0240c40c0001c4545800c40303000e2000010408615101581000322420005000545c40700030401420502841490b003e921802c0911107001c01d102c0c46034400c2e140c1ca802c000c0101102d95036100740b40b1f040750142c811003440403490140041400220000c00042d5a20307041026260000c000007056030100703654403494180005070085002c81250140d4250b0b075500f02a10800310307000d0703500001c00400881984501400032002800c10810f410f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 396549127 1250 396547877 396547891
    0x3090f070e04030f08010b040e060d200103110f031b1215100819020a0908060a1512050a08070f020a0b360105030613050a020a0801140a031b0806 64
    0x81e01c240703864100600411518610402041580b4004004d20b00150080d2425500300420a07072a90702c4400004a003100060320140c03481c00c0c2c090040d100e5000301d9800d801089008c0e203042c0800780055014004c036008008061140c0d00e030810014210308000c1c4914402941c007034400c5030231315420324035816a844c41158071000040c0c08c03807070f084a0303480c0201180e0100500792030000c00300c0c540f010040100c04010545018200d4000c2001e82026008035881c0010700201e00c221852881c040004038007521f04240d103440c0850048601094142003003d00500c0d1540003401006c0c403280a94612104d58040801030b40c400340c903504c6e10700050303a0701d0f9050380c001c041503044d031a1039401801e510388520f11240181c00c0c0c3d101403440c01d9046500c60340040421090242401522980c3d00e001180b11008840161060980360008024000ca01a070240c0700c40505a03403185030503070b00c03400e108840441000c03500740d02c81e0340320f00c081000030285069085404103003006124560358a407500ca24082013074480f5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 396550377 1250 396549127 396549149
    0x308030103030c14010e0a03050c0111300c0901140f1204030e011b060906060b0d060801061d04020d170711030f0705011d01031d030a0923040203090f07 67
    0x2c2000d04c002c050780d100510402c0300c002c0100c40c1d01217030b54540c1c600d0f40003001024404017044200359141d0a500a0703280350380791f800c0d090395401803800300c2d090a03c0901000540051006403020110712040d103144c441c140c0c8080151401c1021030054551145081000c0e100500412081400c0559840602200c0304500c0201d501c60a0520f40030740b0b04217030007404604000c085051031a00403202d01c1c0020045801c00c200041f560554109140505066002800c50001c0005c0002d41880c03290b0080040301c510400810500b40c985160f0281740640d55005088a50030402103405464658000d5040600c121240044400e000c01070300c1c46600180c905886c01d24855440302814201801002c4040000c41d010f0325145003018000382c007954801200c82d204001d0306814001e640d002c1e500c00840e4641070800c0002d41000246035940d00c0c1e10510141e400198102c0d00056a14034504280404000180c81e049406200105000c02500001d001900d030b803043c0c1e800d08404503001e10036900688080200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 396551627 1250 396550377 396550397
    0x2717040801020d05010e0919150c0513060305070e01120b03120d140f041b05220b0a03030f050c01140c0c191101110a02040c0809100603020303040b0310030803010303 73
    0x14180850754141d000700001000d00040203040c00010440b2002070b4400342407030038003006600305128000c40b0007800c0d2101500d2b0000202ea860b4000c03000c3c0600303141c1e1401e850344003a1103190480542d2000e40c1c500d4080b450700ca24250181d80103030980b00380000da01d1b0700007400d460008000781c41c00807800042801c03910300003032104c043e11250152220041450303001c20410b09140c40d0400b01a0001031000d031901e03001188042c2c4904c54810f0311001483e004100102ca0180c88403070300d0f1024045240e0f038080f0340c640244003242d8145075420f0340450744c050b1120184c0c4442c50105a409900502d8403040655070f40e122000c0400032161181d0080081c00c1c98581c9450001ca241e920304030440d04600c4001401d20180790026900948270b403c446820b282209400c98404503451800d482c601000798401d0400f000300b881180d000c85c9861090081070b040362aa44030101c5d0360303c04c0300e82e14000030f03400d038008100510403505510015078001132000e529903550b13a85d039110300165030801c1e08224006260612 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 396552877 1250 396551627 396551647
    0x50a020a2a0b040b0301031b1503051e0702070b0d111303060606050f0403060216050f0a02091006021024030609050d081311011806021609271704080102 67
    0xe2010142c81c040c41d81600e4a0f081c44c19a50081c001480000d000038172004aa046115594001100a11001d482c0180448600c00003501804d4100ca0138040c083c00307441e40c0c80d20022403601e914040c202540190415608000313810f00168001c1f50404500764890000040b94181e10004146411440b029102c81c0d82c1145406002e540c1e01d0ba00c0074040200500c400640719080104650890364072800c0140d590b1107004540003454080341c0098041e01641c4000d040010300441c100040c50310840706e1100b40d6030b6a054031406076140e401060010b80c0455002c002615403a445288018200245070401d20349440c06620640b0720b035042118610703154841102007043c1040841d5007a6050700707100c852840c00001d10303035003281c208001030303e944060209024140d0013424100d503520100c54030840e03c0c03a195280a551840203100c401c80143c0c007a01c0000301c00c00d0306e00c601d100194504110510704405c41c12200007105000c4001d0721003000d03c29458080020000082004029030f8001680b1285109 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 396554127 1250 396552877 396552953
    0x30504060b0333090715210b03010e0712060207050705061b070506090f090703060902030c0c0f060618040c0906030b07021605030709020f0d050109050402030f0a0c06050a020a 77
    0x480c4102e640d0fa600400c0c08083c240100d81c40040e2210340001081030120f0b000c00310b0f04800000340c0611491000800640c504520307070410004414150020b100c45601c000f50580d8130300c440e120300142c603081b4050180c0013400d290014403c190050084404c0580c9840c0050032940c001405540108284600e12001180510107000106000c0394054109001080850842c0c800c2000480c0711740c0340400007035038442c0240d028001510544104544a00e04220240d1081d032001072000598400c0b1050110140800110240b080c58040d00c3c0b458103200300300c184518444060011911284001804104640144510b60003503002d503e60b40c08605150300042e0400b44880d10298800c040c0c0642489a41c07000140601190b401100060790b802c0201c200c500c3c18050109454019800d12000140b14070075a040749014034021810f442c0d844000c5042c240c1e5074820341034003c144070340c036083c204035050142c0c0107440f40310018019148034001a54588154006c00b41c107410203004100d03442103201c0c0c054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 396555377 1250 396554127 396554203
    0xc0603150a0f0308040e04240c1112040b09180702060a06051002120d06090e0604021512070e010c060921030905070b0a02152d0c0901030504060b03 65
    0x10641d00400c181182c881480c51710440c042d000154410001040400c1000d40c0c0c541151881b500002d4880003103910614003500004840300c00141154011044500011075400e160704100140e1501d40f91400c01d000300780e81c1203009129882040ba0341c05900c185103000303c10f0711405c1594050711240c40d0011504c3c0488070036412072406408014544804031781c000030002d08681214070155110740d8442e02040241046401c0b0b03051036401c00d06500701c075800000328240030314130850343c00218080c600c040079024083d01c8010501c0c0741c250f0011405590040c2504541c801040c9000c40701d9070103640300c400075210b280100312000003004441000b611962420801105120310b400d0052001f0b030340342d843d9114018040c540902d200081d08078550b5000304604817a49032010f2a050790351130a440c001404502042d58640449a182e03204070060102c9200d89104040790344049007800d69000044005000003001244d03561341c1c500300d2040d1036030200011032a540000c4000002c030009222889150050703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 396556627 1250 396555377 396555389
    0x10b060304061e0908030a05060a0b0c0303040c17100c05070b0f04050c0618011805040504080a0206060301150918080c0109020111010b030a0201121e240f060e030c0603150a 76
    0xa0240d181000039002c0c01100d1f0010305407900400c00791034050014003504c0341ca50005040e00d60001e4120f916120100203944a54000c0001d134094542e1902d140c140c10724001004401da0300700362034516501e25550300014050599207000c0b400c040441c5d849441040e03090b41d0303031400c6036603003005c00007041402c018044084c1000d0300d040781001480701014040c1e003001c2c0600c9040c8800c8200050703038410700c156a02c00070040200144194241070a10304a01c1d84411075081c01070059500044a9041c14000d030800342500041040e0058030304800880108100b854081c0c2e61b0340e0700d4543c01c01107080304d400307810750740e070060000200c8640310310001d0310325245247e03100140e90504483c0e0496681c0400c68418050302030810744a500d0211007603138010020104840c08400c1240f0a0b990040d00d141c2c003903030b10080b906c00f900ca00c6a84003a0120480c070220710a100881c5082c4d00d0910165100b201c1e01042c0840150032201a11000b400280c2650000c03201c450408001c44001c18132032400036090001045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 396557877 1250 396556627 396556631
    0x90a0b1b0106060504050f0f1302030402090c0310170109050a051b0111060c0703110a0b070e0102010e060a1109030a0605060a0510051204150509060a060803040f120302010b060304061e 81
    0xc43c0c10b4001e0070f030703000d1071055600c59042500340c1e15041c0c5603003112060a000040c400c42c50071180d072404400070742081d5021b90145155000103070115404e6011680204a40120703241503e1410030015082c2c0d0072000c08200954895901500141040100c2542c05201d000901400580b0761600007035a00c1d1050020304000c54180101d040b01004a500d50304000d00303641560350b50b8954141900e40c2e6020b030910345028801c00c0466000d1003102c1340b0041c00381019640340c9036a9011403004a003031b9a0506120100f0303800c03481c04181c1130742d80b5a0200b405d4400d5104c0c8a41000a4840000e041041c035600589089450b2010416645401c441800c00f40908440e0340980703a00c00c10703006055014910910708202d8007400810103000034540c007904100d5a0400901081c1b800f09003544e01e403801920006481d500380940071a81d600d000c800d80701995012924204250315103950f0b04048103403980264155503841c1c0c2240c44544482d00194450390207448007003150301d902500407d104021039060500d1714 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 396559127 1250 396557877 396557879
    0x5070206071202032704060905060906190902041409060102070303210b040c030b12030a0f26240906090601030b0f300f030304080f090a0b1b0106 64
    0x680c9200035603515a410070110b01449811034000d9145100d4181ea001915a50501e03c14200c001d2144400e501e6405072000d012095071014520b05940d800d66400798032060003c0059a40d06200002104050031750b42c4200c1002d50b5070f01c400701240e100e070708110001c100080503449a400c0190b04a50440c800b8802013407004c0c6140c40091103900c40c2c648038603200042110100021256411400307007640020002c1140140d4000c01400410344a80c055004500000700c0008070800401694042001601c80c1c2840d13402850045484d0710341e0016064441003000f0075904030400443c0190300c162141c0e2105001800099140c000d280204900b0702c0c85040c0400030055103496900119170408001e003404503800c00401c001a07a84550b1041064200141c0f030315140061245400d010030035614000c20185020094216a0301c6e41540300c3e20514a62080001c200000c0c9000f0081400d10340411a40e414582200c0010b140c1c5d10456020646400300401e42e02410f0504c1b0f042c0308501c8103110020000c0c0c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 396560377 1250 396559127 396559129
    0x9020c070305070f081507140d0501210209060402090301020712080702060906012303030903060412110c0d0b1e010f030c0602031603030c261006020a0302060c030a0b10091401050702 80
    0x40c0700086d42c3d501140d482c240401c4c511f5028644800100f0003500b182034542118043d4000140000d01c580702d000e401c40c40262201d0781c0b1005003c0d41300c5402a1100f00c040c0d0b506014840030307500044180d0f8056500300080e40c003041079070380305c82016440d503a1800d0340382c180075074000c0c60244060701070070140d000788004000008641030300b03180501030341001a40004c1d0354000203044d07004900f03c954150260000700300400c20b03110301002000300700b0344410500d000410902559170300c200882581060040a242000c80d085202040d806500c4410303030303104002080d6032641c49800070391011000308411942442002541c8411202070802807008500381a240301c200b0280c45030003c0040c0034140d42d5100c6a4103240b18031081c03c030168841c5a19034482c0b0288130100c1440c142152041500c070420080422628030208080ad4684d40590003414030351100c0c10242c440381d20151844017007590b1200f05001648401360203e0680d1000d45601d00078ce46054410790929611481e0503042100c100005001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 396561627 1250 396560377 396560383
    0x6090b01260309101e20010902090a09020a0305030d060501030c030506030a11060408120c0c060901020d14070b150103050108010516110304050904200103020901170403030609020c070305070f08 85
    0x80d0403021240340c1e07260801c914055840c11202441001012442d034140b1545c560070081501c0245146030f0010303101d44c0781c07600243c2201c009500080d8030480f400040b9005034810b1b04945600c1e8001800d00d4261a501ea407014a523501081c0140c0030f050300e841040146681610600c00f040e00385007418401032402e43c00180e1169000500146007442c10f896105040d102c100031384010741035820071660720311440c0040030030540000011910345d21450050400508004083e02c0309042c0c182c00034070907402100c40640355200c40fa00b0050360100140200c80108000c4005540140d02441888800311100d00005056a005030000585681400c01b484070383c684071401801c1c4e0165900d48004025030443d4006e08611075503005540c01340149040c442417100c0050340110600340710880c88014404080154142d0040740345c0f05000c11407004c1184450325031446410350040c424500080d0081c1c9521015049070006075403c0e82503880602c05008009080084202a10441e000302c040b0070300d0840c50541e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 396562877 1250 396561627 396561637
    0x80c0d021507030c0c12051009080a05070807020306040803190b0f0f040b0306090c0306070201060503030706022206050c011404051e070e010b0307031a030c041806090b012603 77
    0x4484500041400034148520f913070292880d80442403a100d1662041c40740c00500806400340c500c1d02400841e0003842c021445610003641e4001d4030f280c00c010341107006a8154000020035a2491000c220002c01650107211680c821480703031100c95140d00b0600758406c0503506480221300f00c203141c40841061503070f4040c9500981c03030080b00c0004521040750041406031005504441d0944180d4040c090000004038a90345c14080c1541212880d40d42c18008a00b03035480c910486416410402100001c43c1003078006054410b0300301d604054951480740f2031140e00585500000c0000c401162841c1444420b02074080e4202040004c8141414030b91140380c0c6031800c4504110a00581140b19019808140864001404a6484030030a5030b55006c41852680c0100e0f94100024075003410060030540840c1d442204000250007041d02c1500c80b004d02000b04240084034004006100d80d03940041c41d140079032200903101e8020746070750b5490002c540c001119030190841c09001001e02c901c65290000040e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 396564127 1250 396562877 396562909
    0x40b18010e0f040f0b040906020304060c08130305030c12070207050a080120030a09050a03052101081c051909050f060301030b0a051e04062c03040317040f060801080c0d02 75
    0x1d2941c0910055070085c04403520454000c0e0610340a04103201465015601c01e03070040304140076088405d02c085031511000c40f19003140003a06408600803901c500701459000348c12041e101e107404100390001c0c0e8081c80c1116180c0047e441020240300170305114500e80c0c001e180c07071030090102d039810002032140301c80440301c0609400c40100000320189402d4000c608115040307016505800b40d9402d004100ba070104000031034010040d961200c41c040070b040341d1812101d6583c090a586048042002955070800d000902000818441c0c1c03c2c3e004929041e814a8541075210350101c00d00d40800d11594800d4600c01f6032241200740010030204040d100c0c5294402c400480000f0695101d04409039026805510b040c401a1410b00708420400301e503100c0b01100b00c1400d120030102c0800040044d00b0b150598180341107401c00e010030000101c2858043c540c004070311300128140382d11030003900d02d5254a84d01000024036034000400003c1c0c4140580346640000b9243d9070012002038003c2045120821400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 396565377 1250 396564127 396564131
    0x30f0503010b1806040b0c10050f100b0a030b031903031b0c031803051902040e0f0c0103020c0708190c091514060702193011030f0102040b18010e0f04 66
    0x43e8103503590412a03001e0710f0080003d40e21044144241541c60444d400c0c0c8007412850304000c01d0a001d4018840ca2007041d49980602c1c2490801e80141070710780000c040130040c5900c1d940610a182e80030f104040410345018040c541110f22800d0041c107803100d1020342910007150034034010602d030f40480d41050340d40c0c0609018030205d102d1201c480100200c0c3c1e001070710a011303050240c4031061141341c2991580780210345c180a1500c04c05502c0da181c0d0a0320076940d010754010442c0c1c645d41e502076000b9082622248082c0c4042e0780d80d48072118144803440000300601b90540062a0801201156050203040100400c219031403002000c0c0103547c000d40180e00703200b41510014400350751010115484154090900d6001d01c00e810701c1b281400c0928003c0603c404010002443c900b100c000254441c0350b20018008404410303601c8a01c9524400c1d018540c041c0a0a01ca0701d0000e40c0034002080200b103d4070240c0e548001c484846451000002c0d45c031410421000031201d11561042d5032a0b240740c000300d0300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 396566627 1250 396565377 396565417
    0x2120f0a0f15060503100e0702070f05010e0a0e0604090218160c0c050103050c091017151e03070b0703050c0c0111100507210218060f030721090f030f0503010b 70
    0x6c0b0709284021544071044c900c10174000c02074566030100e82e8108490b50340e6000c149050311080152050740c40c800607070b0b0700304d030418000f0805c0e80040540c2d02c1d0081406003001489105640115440c0110441c40d680c0d507a01c840240b05088003030181c0c40140c1855031a000d0300300c08256540410003886480781a041503110702c049407600c105003080300c810100042c03900c603040c2c000b008051b00c0b4813040c400210b006050100001d46840b130401d812034400d00c00038003894900c0714500300b02c2e500a016040c86501072084550104584020200a01e242402912003c1d169038207110183c3c0350507034401d005810012455a06d150556000601852100c24088042840d580700340e4100c1e150b008001c0c0304000e20603008000703008c0003042c0d8020540d0021400010720450880d105100403441070f18039421161104000181c1c07413a108040504540c0208080b800b0760b00400c012420982d10807080664000307020305084010107400040c0404010001e0408608561401c41303021218001c0445503030811985041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 396567877 1250 396566627 396566641
    0xa050301090e0705210609031e07060608010213080c1c06051e1003170f0913150e180105090606010c020f03011a031e0303060d0602120f0a0f15060503 66
    0x1e43c0001d410007504220220010000058024080149050ba94081c010100c1c001503008030455001040c040c60300f20168401800c452040c1d03120030815140301b6075440340416003120a00040800c10000da030100305203401c00704641d0a11400000c1d992240c000c4103100c002c0d00c0821011415500d810000000c0e0541d0b80d426401003400d00b8503004000c5802a2080000049800d9041016a802154040101c00f11196084100d103e400c0c0704240e0241e051110400030324092941c160116450f0344c5c0441c80204100482701c0001c080e401110741410718104005020580ca540c202d0680da01a00920a60900341a0641ca03010301400c00e60401c98641c2e800f00075034841d5883c500714401c010300204981100c0c1007682505085e00d4040c04d220703001d0a00c401e4030341101c1c40c2540303100031030600165180d610750404001d1341e8107040360308a070825002d000171500ca01c1005029840741c811042c9c4121207141051600048981c222110b40e5164134200f400c441c4810441301c048240c0c0c0c0c00b0300300706a80e501c81e54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 396569127 1250 396567877 396567883
    0x115020a0b01230a061101060608040b042301020301090903030b030604030e15092d060f12100b160c060c050a1415130b0a02040b0315040e0a050a0c05060a050301090e 73
    0x403d10341007032540400103038540d4485003041c41c1140000003048030760780b640400c0b40c20030000e55014282016a60214010410f03410500856112042010000400740100c8a003680c109038402004190b49010038001e00d0b82600854095800480c081c040c5441d160b5009000f41907035035041400340044000035004030361000d0031124a40d00080c87c5030000002d045405855a1480c400e144000078500541c6800b420408190361900700c0000e0131905000c800d5200f0209880010500351900541500004401204400070240004a030240200900721428002d0045405510260030415a41c0c030302c5021410105907050001d52064104140c40401d1100e98501081036010042c002d00050902c422242c1640c103c2000c83c2c800e0380304102c0307076603400392840c1240942e1241c0c01c001202000050b50108241c003860200c2e1100030070019041020302d6059141c514000300c200c403103600c04003159051095180340100100001c40b0014174054007050000c216000c1031080d121a5512036403400440c0340c0c18 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 396570377 1250 396569127 396569189
    0x7202d04060909020310020406140c01091401090525050108040611040807080c0f0d030315080111040602071202030a08070303060b07120f0906141308150115020a0b01 73
    0xc2041c000d0766203540e9954010481d0080881c0300707200740702044684c44014000d85084540320b840c1ca001526450215506603804030079248259585c134100240040c0e01d07410340318000300c81c01c4000201142d9914215182c01d01c07a2440c041d510350070600346c030180d1405007820000d81d00c3c01e00e480541c94a851038408041e0506104a81c10a2800b00e004a010140011031104440341c0e0400c0b50201c0e8087c0d8240011020403c6489800c0007031001d900380403034040e070003c43c0005013409001001aa070780e1451803c441c2d0312012240260b8001404001d0258101f0001000e8000720485021110055000a0750307045000350042c0300d607401155107024103020b680320741e004004080035165204107030300e0070b50b0b0308540302040d61021940b07005002c0f00301c91080c41c601c0161506c83c2c45011304003042c0c14024610350001008524511203004022902a600303000d8070b5000b20b0758200101a55040240700c3d041c441244d00700c2011544813040050110f045180c6440c11210b10b00c0e01807448600561034003c01c0c41350 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 396571627 1250 396570377 396570379
    0x15150c031228141b1611040e0712061d0a050304030201080c03090601090b0f13141b0904091104020a120b0406080601050f1f0507202d 59
    0x485081040310710b0350002442c07040812001410145403440d10000842d0505203007081c1903400c0c80009403501c030b104807001424000d80320451342840c2070396000003254441c041d4210342c0f44003071030307440002c03030078580210440390900e54040c0503e181132000034406481c0004019100a0f00c4401c451914007810410035061040103040e44c0d860042402d10f00d82c0ca5001d88800c038002458500010400441d40064030f01500c80c50000c1c1c03007a64a072100100250140c01d40091f4010b1828160507a2030fa02c520750038007107106400b0007060020b01d183c4404901038000b002040064524925601c420300c2c4981100e554040131a4009003900c0b203401c048201c0c1e0350981078690032510001d0702040da550802c00d0030141d500c000c001405038505d5002440305a8695100708401d69104000501803840c1c0f00c00c01c50f1000b4806441030010600410031202a02e108588a0003c51800219002402006413242080000b4003409940303114810000c100000004586c0b07422000c1c2100300f10003000f500038404070308400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 396572877 1250 396571627 396571657
    0x5060f15090a030b0a20180d05160e01090c050a020a03080403050904020d02190912171e0a020105151f02010603051b010e0a030803040b09030f1b0615150c03 69
    0x680280544005c01b4004009030280341d150300b102ca440302c4844102d40d85414501d062409042d0b20009102040102807000c9850340100d4504024044600c601c0c8002801d00c01c0d074400d01c551409041c0d00449001c0018441088010003d44820302c0d0002180c0106680c1880c2c0000b1507696405d00300e8240c0605101c00358050b000180b5205d815440e50050020000700d116034950070307049000d00341d0303400e8264440d0091a06241c0942d101198800c8210f07100030394001d840300d01e0000c0842080c040d860322a20440000b000224034002001d909100c0d00ba0b10070100c100b203142c204802800240b4000c409405110301c00c40221f18410080d1003034204d100210b0340a1b08468820702d81076003410300443d1500c0b42d1030000d03243d072138111020b2401800d10001c603500069102d00c1c48e2039070780b1680c404980c01843c44169100c1040b00e5096900030b18000d1190100701001170341c204a4800856040100261101b000c8800d04204d00c40301d5524110140c0d0140528110199100b40c840403050441c090582c2c0a0202c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 396574127 1250 396572877 396572881
    0x60403050a0201050702060610050d0b0a03060501031709031f140406050702151005060901050c070320060a09050402090a09140708100e130f0501020d0f05060f15090a030b 75
    0x10380100140216507141e4000b4000703951000c40072070303445034216000ba500640040d20310b2034080c0600010101c5011201010410140b80300100300c0c00c007e103a004650030350780d4800420034012030440314070a004d580703006c0c0c5250112080c00603540e80003503101007d0088008c0243d0340d001025500140b24800c4000c0c60f460306e843c1c1818080010142118458058041e9a182c0784c16511111030040c07181d440c0c00c41004c0d81d02c2c01c01c02408001d802038442e40d4140304080000a000380350400540000318415018440100c0d0b00c0244125071000c04036085009003410b0020a00c4540c01160500c1941c0c815900142c5841d60708000580c0c80503564004819945402450100c2450900045120300866290804181c513103010b5040c400b0017a10881c03283c0c40d004400f2400140c103400c1d080d45894052080241d9038403171521200c0c01c9a12001d858140140d582c491585441e545004403680680129442c0100c03c2100c008581d1020024460550890700003941052540e1001c00c000061a000702c0b402d090342c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 396575377 1250 396574127 396574133
    0x111306030513021c0303050702010e072c040b06011b0213050a0615080f0f0402031c032a030c0f1b1407170106050307030f02120f01020d09021302070308180f0604 71
    0x19030b204c024160300003420203000480503401401245d4080c1640001086030510380f4040200501c2d0200310300020303d90310041c21081005001e149401a80100c42c0451036082150000d400210014400151b00200d45116009680d4140030520356030b103c1074010403540d0703a0072118001040d0980040700316005d52612400c03042e0384407030a0783c0b00354404500340c42c5d1903d80c0d00c600181c48004450083d4141c0c0300940c6420b000082103490328500600b400e000c2030b844141c07404a00400a1802514118541800307010344c41c0d5454000c0603d40101820209601003514a000b400324034080070042031506100c150b9420454001032000c03214008800303698245841e0340c24103614041848070350b10103600703000010590745000710740351040f039521140d08004846c590742800f6010050300c00c80d1034207000701888082c0408081c00205000c1007809000a1221100d04c10414a02000910b00d180e292043c0001c00000c1e400c003a0b03a030340007800800759105040b0a42a4140380003e0b40d483c4600d1030180342c043c0410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 396576627 1250 396575377 396575419
    0x1031b09022706031003080a14031315050103080a0507110d0807020a0911120a090203010908031e010e0703330e060429040b030307050307030311130603051302 70
    0x30424a1640e40c2449082803040000c1c50209868a520b05502c4d10006c00005d81078034014104d020160410030306144018020780ca00c0d420841c1c0c01558000609003030343c05c11109905414240808103030070030107941183c56075a0a03000d0b800d40001808000140082400225001a841c0d40340080521000808606d01001560021041280100e02e031200204030020b0500900303003406540b0351194100234031081d1941000c0b0000d0010015207540b518800c000d07880a018100003d0f00a0310165074074100b11030a1001050003546211710b42e2204401403040e800000c004940185481c500440c8501c0c0c4104410700010b0864034003448603400002180c140000f0b0741040c0b080380d040d20181d481e140d54070014401603680c04c5a100d00840c504062542c08141891481d42d03408002a100003084002000800d24550101070251640d034408182c1c6800c0540c540641c65500c1c0b41c1061440c2000c1c1000c003404508000341c01040b050540b2000055020501ca50780100c401360000d012070300244401c000007031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 396577877 1250 396576627 396576667
    0x160c020a0f1a0a12050612011a19050904020d0615060905030d0318140f0106032307030507060f120504110f0625080f03040302030c060f0f01031b0902 66
    0x124000b003403a0014103030b000400503650a10202e0715000b106205582030030b00180b10040410354040010004030400000900c00e032141c0d25458521003040d1803220b010404a1f1139805100b02c045004280107005940b90441a07503003159050311101d0b5021101c1c5814000350003180c1c90700d4a2138083c80ca00080040c1c1c040481d004450060382901c40c48001e2074422406c0d83d420850002a60746000b44480004840341d001c0034000034a14159010141c00c003903170f1429180150300940c0d50307511003000c0d0403400700c070110708580d1212840020211589155120764482070117115480c01d004034408034103105c5024001c2480e5525888104000b9845c01c2c5c5000b040cac030303102d0807034450041e01c40b4400d00b04581803000c1100d001442480c0100d012414007100021a8402d1607001c5a0003c0144401a40110300d0b00c00356014a1090700030f1515180b00c2c02e4094035040009203804004842c40c3e042c41661044c48020505480c0c1006000850f9495400b0010388901c60342d101800c0c051000401d26071000c24422610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 396579127 1250 396577877 396577889
    0x1d030a0b0f01050118120f02060a050706050907050d0f08090a150f03050903031603060302061201030b1b070b071b0507140a240c0c1206060b03040308160c020a0f 71
    0x10781c0c0c1d88820045038504040328145941e03201d0b44800b48503100f808103081c039040d481260412003d284503800308640e500030035090808a9808580e900402070680a15030340008031100400d551884c200000c0c81744000d00300040d00030303002010040309004148040314440d00001e020a1792075962100210340344d8603086030720000a1003000106400320322900400303000708054030007503045440300b168242c0d048241e000c44606041e500c1c5400001a120840545403802c510302a1034900d61650614445140000b0321080401c480c40d5941c94103034144109403080c985c2c100d21118800e60350340c103081d201400d4010b007281c80b80c000c0c400c50000300600019844107032207002c4034912400000a080c0154400303240250403401034454454055003040d4151058a0192407510035030085854490080b10781d01f90f0402c2025a62001d0f204045c4005401040000c0011214592440c600f5860080200001a03c000c0c5108903021150390254411404854403c0c0c00820150815994015140034a54688103032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 396580377 1250 396579127 396579151
    0x31704051c050c21070b0702010f050a080a02030c070b0f041209050a05060304030203130f1d061809030c0313090b1203030114060f0406050d14010b04061d030a0b 71
    0x902481c50740281e040d241e512500030103005038040100420005407001e01c403e0b01d0680f40c03101000f03201c1002090010200100029a208141c0c0001010004003e6200c01482010088011094ad00c2030b4450780c006124080103880340c403103030000c5520b88941540600a41d103010706200402001d90040743c0594869440e092202c404820140c0b00002d5500c00c082e4010017481040010b400c0490046d40c0c86842881030343d2505004844040036206c03150444c00d2008100802880455100309003d0b041803400181c1d80e80c1860010b001469585210050b4a4000030040200d100414100107a990961104064030345032682c0d0404074502e1101c0b031244180b01030424840b500e05003000c142d00c21070f513000c40c40a03602d1a030030300399032214070302201201c140c0050040104a030660980c6002d0806046a03036192640c82940f101d41105407020b031360400702c1c0262460010400d01a42004841c00c0b1001410421151860100c035013a5506402d2001074141c007c0740c0740b0008000103015130300c0c818081c030002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 396581627 1250 396580377 396580399
    0x2030405010236090a0204150906021002130510021c0e190302030a02060c070b1b010e010605210a0602071109160f031d0d0206242803170405 62
    0x40b1400c0500c1c0e40c0d003915440003e5004a40c850304041c00810303131144640c880585070584e030b1034414402445205c20b00f800105d4010301804041e0b070500030b1500b44050650158103000c2100c0030b401300c2d52181d100d0188205801050b4102c50360092003091941c0700c0702c202000c0501d000303180103846035a80400300c510400c00300700c00d2200c560080351200240c9401400805e01d485440d0300b0710940d60b0010207000d01a200300c00d8001081d2000d03600409020404104104001c5481d240c041d083d101e83d0104021580d041041c21f01c001d84601c0c100301060060080c2082e802580500c0c410308180050001070511400010f500c1c040c0050080d2404020308165a581001d82e1208085019500300d22140c80004025882248081e4801e030402112603940004544c16091000101d524010740b0710340c504003681141040040f010301d155a00c83c240d01200344001084440c03c40003900e6844210700800440304030748171811810407501c02d10701c00707141d204004d0229140310504a200b103800a1040314883c10724100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 396582733 1106 396581627 396581677
    0xc04150203070b01170c150913060806010510090b0f0408060f0901051602060406050a0603020d0309030c05060903030d09060b040903030b03073015020304050102 71
    0x350b550300780c2480c140704a120141c1c004c0d9030030031440550401c49040030400d04005a41241d010305004919122410316024610303405410404852125000541940c0716906541900c8126003681c0c2c0e031a810010703164402181000010200c040801c0412400000ba0048003d070030350b024201500c4040f45454800c04403496012251120180110384100380306a0ba008580301c0d204041440c05468060f5690348060b02c0100700710b9075440001d2801c1900c3c0c1c0709901951f4003c200030502c00983c140148001060300060b64540ba4981002510f4640141204d64246016015504110f1502000b000030021601d095816644035400ea0070039540354800d05031141c0c42900c00007601c02d0202c092514041305030700828000001c0303509400c400001c0b504419220030005005c030510701f00a2600d80c1e0395a001c00c88038002c3d6400442404104081900640110064680407a4104079840 = true := by decide +kernel

theorem cover : BRFrame.Cov 396402877 396582733 := by
  have h0 := BRFrame.cov_init 396402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 396402877 ≤ n) (h2 : n < 396582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
