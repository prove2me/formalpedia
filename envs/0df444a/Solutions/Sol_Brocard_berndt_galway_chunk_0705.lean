-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0705
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:15:15.786973+00:00
-- url     : https://prove2.me/submissions/9abb3ef7-183a-4390-ae37-0a6648307c15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 126618705 ≤ n < 126798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 126619955 1250 126618705 126618733
    0x260403080105150a0f120603020d0f020a060206010311040b1206090721021806011b0501020403020a090e030714070b13090f0b0a06080714030103140d03150303080603010905 76
    0x140a042c1c0c0c0c0c0503181541202600711003898103010b841d08800105a80781c034000c415601c1a8101214101e503801e0101d03d140d5a50040762013103000f8203094642c0200007c1060540c14550020720080c0844d200520301c541c03541c0c95060300c1c01601004284260707150140810a907444094140014070040c06480300c5040180d170107a40c0d89090306c00d00000074020f09030010b02c42884004e8003610340d00a0b0aa82401c0419a11021962801849103041c801c151481c6003405451003500c0c17456512035400140d0311800c500400500724800e0b40600c2c0b01c0307030504d5a07503045860040180c903007540d0310048042a000c002d019003401c00e840750300420700407000414007040180000202c0030841d0f4102c2c00802800c140490002c044d24204214150041c54940007009191710030310384103034488110326140c0655401c0203d580300b907900c03e9000741c0c0c490313540400c103001a0a09200309090f000041c2010000640c191401400a01c034501c009402d0040000005c0d1240e1020b401102030982d01c042525100f001070f243c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 126621205 1250 126619955 126619967
    0x42414040c0501140a180803030c0c070801050c1c0603021203040f0f0501080f090703020414090d0309110d0201030f0207030c05101103011814010b0901030e06010e0601260403 77
    0x40c05540c400440000040d45501603103901c0340806074400124900085031500340d070310f0130821070080a0001d4000c2c000402031818005140103000d486020741e590040c1d0310b40c5920b400c446030480b1016914060034425070340000c2d01140c6c100c0b5102d4204841e014225800790008000c04e900103500071100d02c000130903140010004100b40c62981c01080b00c0551035000d004100c4d4554080c0e01c5c003207410751003c02d0110204081450b404084d0004561256499a0124003a20042810818488041424803001d20400e000f072111200c0e603032804000c0c22000d40ca0342071001000001075030141c1c40c00716041c030969100350440f101515004c0d400390741d01d10380c0d032900400440310013000359040d010709140300b100c1816038081c042d601598002100d007140d0070429028065005100741c00101a95100c40140c442c2128800c14002c1043d10f1704107403611600c2d00058250382240c14005620340055005001400a101ca4036400540a20305000d554006424140d5a42d00c9c1d0140310f84290320447c100310415034420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 126622455 1250 126621205 126621211
    0xd0506040b091005160c021203070614070c030f05090105040e010e010f06050a0c11120a030e011101060e0c0306010c0203120403032a110a0f08030c0c0d0506042414 72
    0x20b400c640000c0e1401104400320f60060319070442c20b80d03081d0810101948208842e0f00344070700040c401c040010380414a1459684030300c908503000c90702d8a0104458802c1a2084c5602c4541d6003007001c2c20a880e60b40040c0038001607090803083c840c0100b2401910391040007914003500c0c40c07101e11080365844003032229010409201c2c2280c021010b08010404501c1042950000502c90b00c550280182c3c60350f507401d4440b407070140b06410034054030421301640400c02071040a5406615541440d00700c100c0014003140d4114114a51a81466810071136509203128041e4480c80140381143c581d2180c0c0c0048802d05070090021794140704001110030258610b1000b801107901c241c40d080050702d10215000203507405c041c402412507210030213036004102c0003000c2114401d001003240070303210703100e4800351004152500030b4400c9a0010401181d034180030024800105403c0341e0782c41c1101020368649903200002032009081118100b281c0301034004500148450060700c04043c80b104a014003400c0001d5011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 126623705 1250 126622455 126622471
    0x1912080408190206040e070c1e03020d0e030d0516060e100501050d0b011203120c0201090c08070f15020703050604200a05030705040b190b0a0206010b090d0f020d0506040b 75
    0x402c40707a40d448203030b038100b10001c66800340c815400c05142045e20440e10000400c25801e01512990382c000254946016100005460000c3c40303901c034582c103000f450b040307608180d44244030106204402c180c4d00019079800072921868000d603684c000443c822850f904a44005011030300b08001c0624444000c10a00400104160300708842d0380c1e02d1040221401c207104010f003402c0c503204e005101c01d00080200250160107410081422040d01018908852800c0b40100050359202d1225080203501008034004007a07500090904601300120a00c02d03040c50f205183d001c000a6008405d030500a100940081d03070000185c8000d45003c0c20700000551404091a40351a04ac0d1203440962401045101c00d465000c0c00602950741043d091100400e000d025480e4400384160040318803840114854015041140d0040e480354030148020785064010f80011400707400034400917842c0e40f100e80d440107100c0e030010360440036040c103800030a148001a00c3e028085e40500c3c030401c4140010901a94000e40031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 126624955 1250 126623705 126623713
    0x6060111101a27090a0206040608130f05061b07050304150c05010507171312050a090e090f1c020604020105030c070501021305120f07180b0d030806090f0f061912080408 74
    0x140c1d0f1055905e4038440c0d00000d500000510003803090a1090103500c1c4d02981d50f8041c041007407a05d031181203a81c0c0054004880d140e2100e401c11602c611141c8034035500e0303818541c4180c2040642e43e02c10340c990056008100100202c1d281081c8031510914903280c2c1150090000c000c6810410802820b0410310880d07040703101080d0f0085001045118108040250041e050798804c50103607100311010341c0241d840c10108168020302081119051074080d0160001d40b0082c03101c2c0e82100380144c00c04416580c2500c04403a080704581a1039000704507158030070750918219689030b50708861059103024034080a0040d40c400301d91940381d00e2030700c00c003003003078802c00c40d6511400112603610980d5262403449102c80d581204800300a166540703406002000010329001c90710010550215000180f44981070b0001440c4500307012850030300d02c0029822440c2c24165039020710342602c03500c800c482c001d08840d0040003d400004003e00300b10302074030040c000f4801c0a0606c8541814001d035203420074020202e45000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 126626205 1250 126624955 126624961
    0x1103190c090c05040b0a0e01050f040810060608040203100b0607061a090901020301060909051b0307080a1401030c0e1906140316120f0804210506060111101a27 70
    0x101030f000343d40840311002615480c1400101c0220740c0f0042c0c014005040c00001e0041d2a1040382c02d0340508043d051880007055503100c4000880300b500c0e107950201c03090010b07038400e05c40540c81c00b04100c480417249210218441f0f203042e004ca0400d100f2404041c020354609440c0d01058400b0700c4a05c02c43c21421508152162510030305503080b448203215490110325010300412a0740c0301c41c0c0040c2d41c049201c41c074441c40b010605600c4030050380f04681d030302d0005610130204142100d9601c0386034110164000582920b60440da54460030540600446001e20341e150001070151035072206950313005d0f0107020305100c0c02c0c0d0344101ca41c104541c1030087c10722902624003061181c4400f168450103c542041c0550801900c80c1c5070ba51140e42858025901f8007010031000c101c103180c0958868a5101021a10000540c1414501e00705031000c2c01c0c40d4100712a00208149085000455100c025549030b400902c1600f0f103401c92000780c0842c880960030407840300d02a01c10a0501070b41c03a49207409100e4151032a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 126627455 1250 126626205 126626207
    0x18052d090603061315020f0301050109060906020c011b050f06090c010c0f02100507050312061206040b18100e01090506070906050409110409150f0902040e041103190c090c 75
    0x514101d46481c0c040e0b00290006035030798001e0302c800031018000e0b504c95424861240b012810b980c0162106040c1c2000017004101c3d550380401110010545c0d407a08174082801c10100075116a051020103040104640c04151154030b0412174000c8242d02404480602050180054035034100711640342c400e018914080501e54059403003041601d502c402c00c404e4809091f0708002c41605c1e403406010801c0010700a020000b042000100751015001e1000d00c440d2a041c010001440c190725a04211341e000b0009010004801c2c049058112095801460015500d1f00641d880d1150501c071406801d400c0240b0200071b0101940080506406207080d61704650742d2420a45240210f40f284c60700003642000100000c01869002c2424420400c45d61890300f0740ea03400c9542603840801003100d0078900801c0c1040b8401011941c10001c184108056003032a01e00f900248451100400250440c1c0101ca08001d0030f65050240b004204c0005c100e81e10f90382110705080e49002c0950242e100c0c0280360440121b003403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 126628705 1250 126627455 126627469
    0x50702070911030c0a0c0c1409060a03081219060905060906040908030106142701170118091e0308010f05040207020609040c020106050916031116020118052d 69
    0x715441e02e007140b440d140c014801609a1108201a080144144070350b00020800c1d03401c3c000800700c4140806082101d241000b0403400050325152203040002c40401c002000001a1600d4a24681c01c461a96407401003880c40e10402c107101c2c060141c0341c0640418500d030315600640c080d02d400d48500029a03181c04c24481120782010010307003c40010305c0104036991241c408082c148842105090910441ca10b44407030f0380500442180002c040441c00c0c03952541c1c032481850350688041c20a940c25450030841d603240807412507201c5c260984810744402070101c0303243c014051101134001e00c4c500c03501c2420014410f00c002e01400038107001454001079203140034002d031000581c00404a42c94440b150040000405c42010f1450542d525040c00080305c0e5100344c505449210750030150000207504100c002c0440b201e00d242800c28400c05d1202804034480e16140b011317070380d90a0a0140c5407404172011243d2041440d070200742c2c048403056030404510700c07156081c44030000202820380303410030351000c2184d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 126629955 1250 126628705 126628721
    0xf010e0114010b0703140706060915210303090b0a05040507080a030f030506130f020a020c0a08030405040c14031003030305010501020c010824090c04030c1d0114040e01020d0507020709 81
    0x1901100700502851521400516080780f0a00300707541500d03241c00e003403078458001d1f04c825211195151405c10841110740030304071a0f1880b0807600b0461702d05141c0c07022080c2c40303088000d000312100c020700002058040c2d4881d03070007a900120540c2440c0746c40c00d1041701521048804940b9070045030300009070b100700007802440c050350685503042d40c02c03107010341100104001801c0960000e00c8810b507980e800068030640d90f00304035108000d0b030b5441002c035001c1d142c00c511a2070103004030942d02c0100b1000c54040b081d5026207400704c40100e242007070184211000f540b45c40f4841c81e008000000c0c404c0340c0c2001e4502d5800c881c800d8034148003582e61980160f03225222140418040740c1040009020103050004440300981c544a040030440741e1200850302c02d09c02200c1c800102c010024041c028800d500b100301005200340c2445a1901c0b21503002d000d00c1d6130040c400c40545070340c03101004d016590b954008100310b038030b120300842d210700180d94040c000d04030640310b0b48003500030f840000c5035143d068010900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 126631205 1250 126629955 126629981
    0x131401170d09050d03140307031d03070503040e07110f0706021608250f3005101802060705030307090906050105071e0206030f0114060a0e0111070e090f010e01 70
    0x706a0b00d05014004c591064100440410110009031688107115001444c01152075980018504010400c190011240c590164903e5031017444181e000400000c1250213031138040c0102612600c0e412401c0d00d08940300b1000503114020241c0c0c42c2c03c4035500054103412105141c0c2100c007100080c6244041d5512503014440c4a42c1044804802c0c1c0005916041c1242c0601c880024040e603039081c41c59080012070b001902e04000c140c12000f11003541d15070540030108500414100a039039a640c10796121200400c028400340c076a1803450051141c1c000030721400350040c4c0300598468441c0784c2035484c3c1d4011600940461412800032404000500c9038805441c4180c41d06854018240c40d5842407290b0782c160130241c1c20f0303020076a40050704c1d580060344c00391034030f0104a0480e504002075440e0f41117075181883c3c083e403028000003d500d50700a0300e450508400b807c110b901c0c100d41012017410021681c01604003a044002440307131641c0d0002d41980f241c02d014000700401c8004d03044003800e81d0070004440c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 126632455 1250 126631205 126631217
    0x40f02010806010207031e030212160b040c090501121a01030201081306110a0203090108090a02010c060518060f010617040203070311012102040e0f091b131401170d 72
    0x140154060481107800c010140120750801307a8070740e182d107540009440c030ba040d07029074241068205601081000000b019050615040007000c440907402c00a0b5800007505c95021200400c06201d2588106c1020f0840317444140429a114180d405801c2e070036410071a60700c070926070b010b55042e883c2c08003141a65416034440000d52030b500c0019140d0102584107440440d03444180d0107611580d00c1c002c0c00d980c0d0b034030b40180d1f4035101441d002516807900113000300c080d03401006008005070f90002500c1c690540c0700c0d1000642d034503500c02605800e0f041805a00301c41c4103881c240050100d043c1d10290403108261f5600e9820340c200f809194894006850094040d405090140006804050b1511042006142103c001c0186802034110008208029440d20741c0c002014000340400044166005011070164121403c0020255540300384c030300c046c1000c904514800d610255038240300310030120342d500c40500080c95092100740c00020288035071745203401400d240c0906400040f40314008094180c581e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 126633705 1250 126632455 126632483
    0x307090512100c021005040c030b011d0c0f07060203040c0e0117031b010b2e030e0a02090c040506040b0d3806040b03010305060f060105041809060b0a03050a0506060904 74
    0x250300a042d159005030300b940100607041609581d1791003854440d90040c88110810381c030714109080091380c107811058050040001c424401e546140d0515007050b18032890320f0350740300703420916180c0b0302800c00010060382c000010701082c0801191110280c5031814a40800da998494000400080c02804504180c2003482581003500e550580108680004400852202c1410000509100c510402c0c000908c00010340031101c8c410854115030707a040541003c00c84007085400700ca5952032a410028424159100050982444401510000d000251000d81c886031210002e13442c6400440e114400c1038a0a901c410368140c4856040ca8003a503184510388880403d6130b40d8030113001540d8071040e0482020440001c01d20710890085000714000c00c043c051500f4104010303001000003828190401409120512800c1a0213402da851005409000101884145002809006084042030380144144000400e102012852508880c81079080d1201c61380e4101c10411b60711342c1a02c0c090481a9000c880d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 126634955 1250 126633705 126633733
    0x20d020d0b090702210f0403030f0f091d07180b0714070302010c020904030c0b0403090501020c010e061b12070c03020112020f1b0f010504050d09050306010b031506071202030307090512 81
    0x150903400d040d8100d5062030701b60600c1030030031075a20aa10450004000da211607064540c84580701440c1a014a4481c02079403918142c4111040301c031403088403200201e40031480080c01a01c0f1144c0d02c0f00429519840680e503418945490707000722400b50360114042c285488900310128a40041d20b60584030700d051840543c00340204d004005000700c0c140a04040340c10041407281c00464425071190f640d408906081c0b03000241400f000a03140340c180120308072101c080382e85110580701c424441041404685224500c15450f200c84000b600180782000900d580a000f056a003d00a9900030789451008004c46400f072412441600400040c414050015078190080c440001000850b601e045982000700d1912a03802c6400c1030b0b5085500c4d40c8007114050780590010329803001050102c01402e40c540c50628005d2043c40020080c034426003c16561051587d648415209d10a4002040680d9401c0640d80039640b94402e0750004045140000b0000c0c0a03d80411004a04600040a02801c03d01b05c42 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 126636205 1250 126634955 126634993
    0x1704060e030f030112170a080612010b15030f010503030301030c0b03070504031a010302031207020604090b030304030b0f0a0621060b01120903030203062119030c06020d020d0b090702 80
    0x518010980400c1152040d980c42c05000345000c0d080840500c0d416440f01d00e00b844600380034070456210928240b1641e002039800c1908180c0c40a801e551050b000311030782103002e0060906a00369580115103400342400141c041c4040c521909c61186896556603c403410107a481c042407000820301e001d01041800107940d10360107107401c02e04070308115007030941b41d40d940158041c4002008003064000310041040d807404104140da0b1341000340d0101d2a083c00c40d00400c08512890103606044d42d25032a8021141c2c0b41042220001c2d034000c04804180d05224949005802c4280d035807110f031030300380000499644c8440c034883c1854003002890158580940c4c0d1150050162052941e0601c07007003805540401609014203c0d01510035a070050b601e142030b40c04c00c20a6200381d219084050740c803412941c00c04200213100380004100788200443c90501c0e25007103c0c542001078005001c0b600204042403500003076005490320401c0b00300e00f07000c10340101083c450051401c40c1d4000050344860444100b4000804d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 126637455 1250 126636205 126636221
    0x3150417040b0412050106050603011809052107030206071707031a132903150a0207020d14061803030a090c0f0b030609010e07090504110c0d1e170406 66
    0x240066007410341c0d07403a1480305a0051381c000c407030501072000b0000030005c00b8490781014060031100e250555041c0700f010350381a10141c0c4075240e00c40d516074001c020310000b0040040c0008002000314140c0140701070644154102c40c004501503c900f00c085100540155000e0500f13003501d0000e04440d40d140c0300103c01908840d0525540d214410080d00003035101c2012548110714982008920610542081344d0040d800ca51809042c51003160000c45503500030618602c49404514040c8464a421031028000e1141481c020340c000f13038100f005400c100044800100c12141c004c01e07a0a10391f264140d07110400c100e509604010b41040000603001545075109a000c01d00560064503540e48484004800c60065009a00010400701c2004510b280031802c0f10b000d041d04c03601c081c4031410803080140c60003460b4000c007807103a929008840c1c0c0554100060b54901e600030302c102d41c10208140e0015089a40030090385406050141c038128582c0d00034005c030711020700589820046981e0319207903000181840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 126638705 1250 126637455 126637493
    0xa080604090506010303031b090b07030f1407050c04110c070312020c1201050603010b0604030c05040b060f180f03150c0c010603050318041404020121020405130b0a05031504 76
    0x8119201c0420310400881c0c0c0658425100054154040020440c044c410600c5540411040e01c80074010038000d101540c00c0a9894100000e000414032406d49052886610301203901c40c0c04228142032000008031300c242481c00750f0b0100200a40d5036029071551140e41c4211001d6803100c5d0702000014100f1000e81c0d203c2484d803060301c40d03c1e440800040c0045030304504521090791124244412480e0a00c600d00600c038049911926180ca590340d82c25602c401441405d00ca13a568000004040c0c803150104d403130403c012400d0542d520260000c03101e280d017001c5032080c01014407209100c21420700042101041825440044c210703960144406201d50050000d0f4850303540322040000046d001b040038080400d91072011429414028050004035030045a0f01d00c6040e0100003030001503608910040001200e1085815950903002042c101a10943d40500e40200b40c00e2459020160a40e000e000b00800459240316004e5561040550300c04804511024a003d0600498005001c00110030004000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 126639955 1250 126638705 126638711
    0x1e05060912011b020102070c080c01140f091c0501050c04120b06030a0602040e04030210090308060105090d020a0b040e0606070b0c0d14010b040305060a0e0c0609030709051003050f0c060a080604 85
    0x41e04010031001d42503c1c542025079004921001089001d032940c0000e0304481000b05182d8040400080c05200e4010021004000000d40e90340350a2841c000c44012800103092054030045151105a0f80e1304c81b624103540320352901003c00d0980c08200105c5080390310403010f65151090075110300c0780c440005803040303605114802260000400b41d001400080040ca540d06e243c502e4681006400d28118072441000c091915042d000065044000c42e60425000c0ca0700a03100d14285001c07038038681e0036940180d4082207581d400200b0f0340442c401030069072050200d1030340340d80703480c0c0c148a018000d0384002804410b07104005449441c100c8043c04400c840e10b00046012010701c005000030b01000e17045541928000141030040c000108503980d00301d07000c0c02c0100201d803d03661070161030301c11321540180300e048000303240d40071a0350820043c406403a0a2000700694109034620701c2d5494002e1000b22000d01510542183c0320402003032100400d1409083e40d80351000100e02203804110040c407440c2e12581e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 126641205 1250 126639955 126639971
    0x60a030b03101104030b07020114270601090606020d03110a14070602070803150303130501080a0f0509010903030e070e04080304021f020a020f030109020a0b031008060a061e0506091201 81
    0x482c40c003c15001410803041d560391541075042c143c0b01d240c0c000340810256030621005090541540318411b0740040a40341401080441005c801c015000100c41c03c0441d12a4000104141065600540c105c442d150221445402c80313400c03e0b400e035114200c910080c07030310520115038894007900c205280502d112004070715044403561514101c1e049081e0a4030340300c4000c401c00411622005000d00ca0500450066040001300d080000800c8048d006090400c0a0038010941900b0a43c02900e801c0d00052001d0003186009046d9074024002d1302026070019050400105c299080461400c041d00c02c0300b04002c40584c0c5a0b11190030940c4060422604024002440c1010805d03400f4501039011095005d03040d14061b60040180050150848920907458440e8010040c0e43d14031405040300d00c081700c207030f49039500d44658480010307a07580803003aa0700496041015003210355000c60160f038500c405410082c038800141c000c0e0030b0114040c064000f001003052003042d280c091040e01411000c1c030000300e1645 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 126642455 1250 126641205 126641233
    0x1a0a06021b0d0807030201050129091e030109030810150f1404030b0108060f090105060d0f0507090903021c080601080a0b1201021602030106093605070609140a05060a030b03 76
    0x240c010391301500141d40d504010300c030110b258200da4900c0190b00300821886c2940031020035041c4542c403d03440c8140c050f09000381442c0c1c007204e42011007400048c001c00c508809800e0141c03420000301c9520300d2102c075812001c40d55420200780b44138044000e9541e00020041448103951110b5003920341891180c0030f101c00030000e1017282c46607003c0c0c41d012020341041d0903c074000540e0070030090840320b5142d0400080103100c1e25020200030b41d558000c66071404c40300f62800c1c02c50400f01641c20681d01a070034004103601781900025180301c0d240280a4003940142c00c2e1100300c0b00300c4070030f4651b10700042008001c114022000e40040ca44001d005113001a84020220364a00b243e210803c0b018030305071000340a40540c64288500001801c019800388810328280d9408804000c03e40c0b00c19a091075000302103409840e000031040003659011040318143d54031640080c104500c280306076025600d46000c051100e040828401c002c030351021f010345040c001809000d401610760143c810f0f40501c10b03c00f0141c0c280e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 126643705 1250 126642455 126642457
    0x3090b1308060a06080d050f09030601080309030f0a1e1a090120030c0a052209020d064a16030b03030f160c03080d1a0a06021b0d08 58
    0x5050550546281071070018800d061281c0107001800c0b403494000d04000400000c1078001c1403450b145803640c0e480c00c3c2c10071008004d0003000c01a80e00751190b04008208804000300502045104504a80c82000701408842d9100e08103100103012041c5100c0081061606001c01c3c0d2400c0e114407441070390340107440285c16103120115403061180e91204403041c201407905106d011200c0e03040c1c40d01031451400c9101c00146201d94480a03003046000145104103400b840f1058800349048a442540242c0c0c90203504040e401007105c03284803916188002810028050306075044040c4054004110044840d80340f2805420366881c1742080340e004d040d400f00b1700341600380a1180e40382a80902d80301c085507900904440032111114000d41c01000844055039201040da101d84800e02200b0394425607621700513406120b50b510091600d003010904070404038885d005140502110800c07505681004c4040081080743c9100f114003580010070707402000c02a4074444029698054852908501e142c0c2c1e5803241c2d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 126644955 1250 126643705 126643717
    0x9150d020304120809010207030e0d08220e0105040605010f1d031906060f06050304110307090c03051905060d02040e1606051804020f041403160f031106070b0601080403090b 76
    0x34510b000f060340800d600100d14541240c0a035008600340850340d0340c080c013514005100c41c0d22444043c0000f000308035110007201d1070400c403100698101c040c920342408a01c025030041503d92009d8000104035418944554811948140e59074610040d00c450140e40484855844501c200c204255032141c42d00c003080812011403280310400084800c2c0d090800865005420200009440c18420042154800292500540c1080d00b01035003807401030000c1d14103182c035881601c03030f00d060001c01d9004e1a0182c4c0040e2081031000074902c00c0e2040001c4c50001c55a04441c0564080300d0603110344050308141e0311401201c00050300301c4003000c21850300700c00380c00b1903070b8000f00015200280b28000a4403260001d1515041604c013582001d2080d0600c50507070181e401039007580f40b01008503545903a820023040601010410000f2690381d03c0304180c2c06001c6e0302d4001900c400100806658690501104503000c4a40191220310648c494200441e0310403030280003503080050142000c10440c5000005040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 126646205 1250 126644955 126644963
    0x2041103070e03010f06030302060105090a020c1603150c021b03030403050a0615060908070b03090312010f06030c05130e04170f0a0318150b0118032603090309150d020304 75
    0x1a01d40c110b0341c00c240c2552010442c40e468507040c0001080000c2e000a4568151030003210904000d40c2d40c0c0320350b20b00074004d0f010180680c1c494940005542010000d2120960307014211203000d0300c00c640d440d4015600c0c1c180010006a01c110031805030f4a5011459103403540004003541d15040e41d948a039413038074881c0c00040c0c501c1591850340207040d90026900c4c00081c22181488507116107031281c106d031030756907500c41c01e822800004002040004140219003002c0c125000700b030f0095031a00d29445000400d4002c07807021920b40001c3c00c000b107000c5da09587c903840350002e0345061141040101505040b01070400c942c6410201126800c10100301c1c084c007090211254082e40b01c5103428001010741d01442c40040350000c1c81c00090000c1291180e003036003151200c4a000c608403504000480d40520004070070301c04c4903442000481048507032803070b1007040100d14101942d500c1c4c000c00d2184161005961031095030707000b0020311b041d0f414032007061210b0952503040b450406280100300c00980c6c2c0100c40c01c403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 126647455 1250 126646205 126646217
    0x60108010f1808190504051e040e01020f07080a021203010303121109100807020c0a0e04140309010f0c0309090204031203061a091912030801060e060f040e040204110307 74
    0x94109103284961080410610b00c0325050035982d03120300105204031411840600849950159040d0060003100d0080002401c01c0230980c5810380b0400030309241c1038010744214181410b03c1001401402603900380381010b15024a46201e507600d0f0380b6590f000a648100f54015620021505400c0402450080d4020784440c441c00f170712540108200c6090b845158640b813000d00031140745403113030b0280760819a603e00702103080c1d464590b411303847c25021140056015100110200308402c104d44464001c51185210395180d8160240380e46d1a40503c201c8180090340c3e413420086500d10424001c2c002c2ca0181c18047d1503139448a0b42d400c141d074842e4000b41c521200c2d0158401070140e0510500e80145601c1400c0701c01810745070f204d46c58500c41c040e9180e200d01c10040050108408044850008003510401e283d44d000c030ba4a4013800d034080902c0f904000c0f03008118198131504010303040f104e17010004409545000d043c0560801e02d110080d2042c1c5c1c003d40c0d40c189401ca003100080c0203601503656030b240d00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 126648705 1250 126647455 126647471
    0x1412031201062c010503090106030b150f03010c0c1209080601120b0601081005060702031c02010e06010b1603080c07150501091104050612040f0b04060b090612100b0103020c06010801 80
    0xd4240614610391414581030382c000103c00c40b41c3c2c210042601c00c82440c140e9500d44484020501600440c1c002400f1981603805000b29100b00095806000400707071211355080c1100d104240c2291160750004001c1080b8110207000940e43c4c44100410001038109100c1c030b141c031034805070328104090304036175441a43c019a00c82031005640c405540040c00b46000259850034910310000b103c06846070f14041d64000c0740e468115a400d1040d41414944001c02c01c0f80b0001204009000c0e00c03507145170107520b0213040000300d200301c13250084411401010005000c910503543c1c04646c002d4008240d01a01f05040c07201200060b0b02d007a24105120080764003140c254101150b18080340c6d041600759000660802080021381c03569001d80740008031180040444d55a02d0825000354100e03014010701c40d05e0307030700200802c02c503480c3d11482d5103c40a542c10540342c5c0d984400d101d00c1e0160160141c02e5503101c1e20a103c0c0b401e030690810303130100030103140240c10002d0305c4600c9031508034280c2154259035154000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 126649955 1250 126648705 126648707
    0x2030301061d21010204090908030a050c040e0402090721060609050103230702030906030a020c0c12100b0a080708010506040513021503042112050916141203120106 72
    0xb8031041d02e04100036512000810310b002803200490640e031549005900f40c0d1100c4400420360685008280d0040c050140a10601d048007941d4001c807030740d2003a00d1800c00803403843d80c0304009803810b40c0c00b08011090603848903000c004000c68002c0c524000c00c10001307010b08a500304001c2e240e0786044500d1022451034100b00e0040e2800200b0703044070381010325080c1c11140c03c0d10039089175041007000c00e1006409440b150b100b2030451003801030842d0030000010900403030300c0b059030040c3b4150300f100c410740d50b6a21443d401c01070415082d054000c40c9610801c0030314041c80960380114491400101110320561351204094182105a80705683d280d6444041160f141420302071b4950050354920502078241080c0c1c0010b201c25034012110082c01d0700800018100280c2d030550074015909000340d0040b41c3d9041c0e000415880b82c1583d1800070909000100d2016400005d03d2207144032503511050342a070610f14240c102c80d410b07003172007548030784d004c3c2201c004020140014210310300b440401c0e01c40d540c10404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 126651205 1250 126649955 126649967
    0xa03060509070c0b04080c07060c050105010501030213030605060a1806080f0c061b1009060207060c0e15180904050a1a010b0405040b0d02031507031107050709021b0106060203030106 80
    0xc44580600e078203900304108564800a1910380940c803200c0030b88140c4641c01c4c01c07051030042d849082010301c619000858510b40150a001e00b0a01c100000e02c99a80c8030300044040c0d000713034942008440b10080301440000c611f600501d42c0040040d1101c80040e0f42d0310b01d0328a59070002c065074046555540303018802c0510610580842202e10001050b040d856000030848610803441102c05540030340b0382406d4050070501511a903c14410010b1200f001035003480342c029445410201c2c0c82c0e83c640020640001e015034034011000340018601300306800e285400c10f0f02588400505000301482d41c08290841c0d55041a1a0140303004000070054048540340143e29075200c80d40380883d00c00f0700710040003140e10540071141914429600450901681000b2a0030b013600410000d5050042d001d001281c04000c0b00c540e4030802140d501440482c6c68100f10751583d10a05502410390780104d0402e00019016400070103124540002d0b9902c199002c03808613084420075006100117030000401080015131001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 126652455 1250 126651205 126651209
    0xc080123130f11180904140307060204060e0f010e130b0a030c0905010e0c03040609020d02060c0105070f0c0b010902130b030c03010311010504120308040204020c010c02071706010b070b09030706090302030a0306 92
    0x1880151400c00c400284c04181855507181a20802049001808101e051000380b4004084001180d8449003586802c0c000380d0054001c440c0020100c3c6031300d1400b440c2a030300d10700030f2800684a00701d02011780b000380715692243c8100e82d03d0140d01d4110002c0b10351035000c0c403a8000d40c054a0902ca0f00c40c2880c180c0802c2d81c4044e8000c00c000607005042c051203005040032290480e500800c001814810b0b840070904c1d510189002940c07100000c100c02050001c19007245100340551780c0c1b501d00a00e40e80070199524400caa001a00c040f09500040c006000305500601e4410b010300318407001c10341c1e02c50700d01d001c1e50300445031103100e0800400104100115082065000c00090821900f01805c041d4171261040340c2403400f500300f1641d603000c18150748071039040fa4085003440c8024000e82c1e44481d0042e40e6000d0a10a00190f41105000d500104002040c0c0b907058490f07041010745440c4031034484000d8480c000d0440c0500c0d0000b0016030b0001802e500c03032100200d2003038003e10340759140002c0180c200e80c1c0d9030f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 126653705 1250 126652455 126652481
    0xa03140f010c1418090408070b0f010617090307020604030f05070902120402060904270b06040c091206060b130915050604090c020f060c0c0607030c080123130f 70
    0x1154074100c5040d0080303c07510143c1d039480c009607110010203c41c040590500703a1202c0c3c00071180d000784400e1005100090011138019200345019448442420398042024414000011180e0010300d81c546c2e035504405410a0003032040728204441c9800054060f072180c2e1003141d074500c030001c1e9074003000403d2110704003d2954000450408800c00c84a031103540300240b00922034000000c021909960702e030301081c4009881c5045000c2080080582d0380745d11070914059441c841d5580000b8824076160252040040566031000700c0301c0e251150710301d0f0410214508992280c0c0301c1d0b42c08500420b00001a080712641020001d0383c040c90104a02c0c1265800300303c00c2c50040c400c90090100d92510002c950440d6940d050009522415000c00c900f442c51172030090689001e090140010000504084c101030340d44842034600340d440d0f040303065044980500c1490049040d000040101743e18262040b40068000d1020000d50a05400000d41191011608616150342c1e0005902d0702c08152240400440314 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 126654955 1250 126653705 126653711
    0x5010314031c020d1e0c140c0a060509030408100c11030a020a08030601030204030c0306050402100f14071a0901090302071e1a12010e0703151d0a0b0a03140f01 70
    0x50504980c14442c0254002c48145400191141c08220558031900305000b04000320718100c02c0005c1c5100140030451146000628096000d134452800c06013101c0288580100400c0404155960040600310040c1401580d0005000005185400b030003c0784988540c1200022142880300303020b848134003030700304010340d03640144414017515800041d0781c80416003005e03c0d48d859030b0b00c520040f0080e00c200d400081000d252440d000040280c0c81e000341d40194400c8844031f10346024800c044500e0000b50010300001203590380d66003415203450000300706ca035001d40c507150035030304510030b5142800e403003540d200034541c0d540c1aa88043c164140300c844040c11540713809036880aa2040249184e1081d4000d4001d41801b01e03815480191003401210204c2c801400116003d695805401c002c4541c125045000b10b0700b4802058010180e04280e00e0540303060109050440310249001c09101704000e100780d0120341c2d102c940b403c2595640f254080207510034a020b0340c9503143e072100345050200d00c101c1e600b40e60781 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 126656205 1250 126654955 126654967
    0x80c0303091c0c0312061701020d0b2205040f06050405061b0a02102408060103060b030703120f0e0901081f0e06190209180f0603060103030509011808100501031403 72
    0x50f0090040d080ca80e014604102d10207206074800009114550011100c0142018904041d800c103402500c1c0c00b00c9506810440c01d40d00a042c08007070f80d00c45071f0302480e15103203a000d048092403581c0240e0b000790207441c0300b512500303044e42c558044920a030f6042c3c401c3c4e8000b40800c5400d6a60a01d200061059654690b0a0181582000c0d5698048180c0d660140c5d4a130307900000d8081c0c81c88400c0702c550106a4000040c0c2c1e43d02e180c016101c0100f80000c1c0c40075410210784800604000611340100d9600400c001c410300c203004030488045540501d000100041400729520b15500c2d0800030780641044405022000c0d0400340e1503000c4044145031210503030510004112102000c94120342c001d41c0b941b01440161400300e00d08000b40b1840c00f40d00da102200d004860312100003181c18900c502c0080c140d40417944c03102000c050756907030300b484000e00291080000003900c0d4031a01040c40141c610720740f09624181c545c2d8156003007002c0003c210b00090f5032072004000b44007004c02c504081510a6001d903142c48 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 126657455 1250 126656205 126656207
    0x5090a0201050a1d0406030309080708031c09031806020327030a170f031501120b090c0903011503050309190303020304120c0e1f060516140a080c0303091c 68
    0x4050900e0000c14040080124180c800080821006400004201b0040303580c9a15026101410034012030a8074441d01001040c2903400100b10b5041c81040c07940782c4460341d965142d14000d07001c1030038100d0820035101c00002c0b20383c25012880b80034156940103140c41e1070700b80e400810f1544450f441003045203026000d440310380d103011802d92103050704003d109034181e03820451416a445540f4462003031070000030422003505848910061282000d90f110360003205256642400d95854115055022140038042100c0c3c03e0004000c00041a01a00100e03501007422090410800c1941c4162006d40001551500a02d865207081c1d040d06980084000c50f80c0c2591802540c900035801848220401d690100051008a010b80307402000f40ca68003030424a0000c002940341905c45000c2c120346e600003a004107545015400f510761012090b1603108130302c0071503107588030303d0150018404918029181c0c62030100348a44000d0060f00d003a000103542d2401d002c22400e1402c1e40c0d620f1003c0f800d0960076074200d611 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 126658705 1250 126657455 126657457
    0x140709050a030b0612060405160501050309060601110106092d060e0f0a06030f0f05010f02030c0f0904020403050115030b09011a040b15040602070914060f01050a0302070204091505090a020105 84
    0x6250440f500e000c103965000003141d001141801210075a106200400c01088400110304039850000d0114290302580c0c4e00056940d400281c5420300290058000943e40c0e500c41c0300b614070340d0030901c000030504940d00c044107004c90f88103060f00c003111032407005100c10304107006030816240b40c8501403c00005260580c6406447d102500b44000c000044c0f003c1000f02e00c00790000b4002d950041c482041c02e290301d2134101044000620b045a095007080b040130030315003080c82920f2103918005070042c5002410160b03c03a2540c0004d800c2e5500650031300011000c01c00900c248015062203600317100302181541081405840c0041c40301156a042041c503022002c4d6220318035011030410344002c200e00d4800800034801e086040e0700d240009401250009203150300007280c10458041285c01c120404260f41248070703d0304210380c5942c21001884450b1555440350000702540c00d8036207001414014a6070000342510300001302a00d0310040c1803405004505c10344181034122041e1001000c009105500280503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 126659955 1250 126658705 126658709
    0x5060d0305070b040f08030115110d020d0f030603140d120501031115070215180f0f090903280806180c0c030912011b050705120922140709050a 63
    0x3280d0204045130030000807807000d50794540d2100c2000d45968403007005413000d00440601100090540380004d0107404042204483c0422a44c0a0000900828000d403100040791481804260340d80d14008081480112501c3c00c122000010f02061812250001d02250340155101d0702c5610f81001040041d0403e00c200a4100b001d461444441c0640b0301400034034004c034140a90403021528040403e5201c4400402d0895903000c01d01640c2c004c00030502035020f408410039504140d501c00e0b8080945072a60799945d229a4100840740340070b0b05401001c005200650b8402c882140e000c0c20b41c030403980c00c000820b03806581503a40785002401d6011082020340050200740c42c3e08000203d448855000b4021100180c0e0041d04c100101000304610f20f0003420021200060544d070020441c024511490403503800f80c1e04000144800709a8000300384495000505059000d130b2100c10b80803a48280e100d0011504403a0840003d1400b186100ca55095030700400540400c180514140007a50326210300e501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 126661205 1250 126659955 126659963
    0xa0905010e040e030d050403030501091509020d02190503090d0516230a080c0d02150a0203100e0405010507090b0f07031101020d020403080703090501021204120f080f04080105060d030507 82
    0x110740c00003031001c24001c0101032006041030000007400040f002441c0c20040c0202c3c4a80d502b000365030f90b5501c0000498100040400860f1080802004a549560050301c203914071484010b252040b4203a00c07007800c0d29286c110101146000c0100900d0b900e051014262030809030403e00e203000e0b1440c03500c9480d02c0034800c00922010a40482d0741111414001403a031031007011003283c0524409041c040581c0c3c00c90b070780c0c80b42c040c4100070004a2040c404194842c0754070304441c4403151900c442014002a4100801d1004e0602091500080d02454209003a000d1409403000007220300740300710002d011603265004000c0840041001d050019000411590313203503094a040e980f0b0810805c20705019104048040008078000f01e800700070f101d2a40000c1070228440d845010120b07984500582c1c64120741c10350002c0b014003d200401455060201e1920300341d102d80c5904e0b608842c00d949100054002e100044d400384008281800402d00034410703d5040007003201c10036040300b0f00c0d0b03400410074490004010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 126662455 1250 126661205 126661217
    0x70f1409040f1b091107050f03120105011214130b0f010b091504090207050304080706090b0301140103020c16090b01230c1f0c08070c120e030c0a03050607140a090501 73
    0x512240c0f0041000044c044900041c492082c0c0c003888200141c001e84001c3d41c150040d40410041e02200004462040c12210141da245a10304001580e0a4000c0500c140066803210601309a004020860328440c1080784030300d41545a03d0b050107070f00500d00a10110740212403c0041c04840500000e0b43d06c0aa800c5544018101c0b1003400c00720140a02c0d0b110080090000c00c0070010480c0100190051302d580404503042c141d0346040c2120041d02030320485030f504c0c0b41000107001342c00c0c41201440300080181000740c030703051043c10218542501da200f0820740f001e8440b42841007880038000d11360221424030700610010742a9402c00807820407401d0300e8070000400101d409203140184122400d43c1b40381a03099007958540d01401c4042c080d200c614000040755000020035840c00f808010480076000001c03a0020070111005407000041002400d516101700000c1c0340d01d9540358010280910f03c1076000d4000c506090740c0c081c20a207e010056099140c040c41090754003584900c146040b64000d03e021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 126663705 1250 126662455 126662483
    0x90507150504050307030b010e0f011208090a080d08010503010c030c1b020d020a030b040302120a05070f06020d020d150803091f0504030204020403211d0f0a08070f1409040f 76
    0x39181d501c00c6500907901406804000018407080300800c40c12100d03884079000d040c0da20031300f0b000402002401416410084200b04d1008038882d88041c2103403900c003402c001f4030b658440a28500c4c0010400b40503000548460050009007000c1c019009610310509003849a04003403400901208502101c4074900c541d0f403221041595189040c1c9032840303401812702e070700c0c10343c070bc1c2421361034aa8203c0b415005442110140007a0000040c112121003201da07907001c0c1080826941ca00e10100203110070365a16800b0f10529984040a100500c82420101c078001340084052001c1c1030044944d40c4050451317041403202d0b1499803a5051183c40c5080c1c20050901000d418020a0f074840c0203542010703410030b1000c0780110820180b04c0e01c061726605e4000c80341e06d05403502030782194000e4503201c040394a07121300500d80c212420300004080c035820008140981c85d903101c00c40e0314078108559002a1044061070340070480011440001f90420506613480e2034240781c07607240ca540c484a942c070020305190000ba14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 126664955 1250 126663705 126663707
    0x30507020f0a030f0b09190201230c01020403060e0106030b011a070f0807060510060f030c020703060c0203312309010807050a08031201050907120501151209050715 72
    0x40781200600c010161644181c90381003040300454078520131a02c000030000411800040028066042c142e401c0c040a40b0440c142e004440441e070421408680f44081154030003010a60f034090b003c6440701c0400162103074079600301f21040d5000e404040b10079074501a002d0002c206042d100e98151207928005219190041a29110718410418040d1280006d12100c00030010200020b020300c5001e42001c0c01181c48001c400c05030f0424906c9020003061011080c140d225010b40c122810315000c40c0142c8101503a030341c48050a03112445800320068000040b8801084441061082d0ba07203641298800d441c460f001024060b0b03507550141c62003500b102c90700140c480b0360340d45565070000d5014005420550b91100040d9840c00341c0d0060030302c104803108000c60100c8000080d183c088922450200841c0d10b040180008400e0180204042001e10f05d4000c0e610030b01401018020721214017840a95080030000504400544c2c1009060608010344800481c1d0001400e4064a03149010007a200c80f8000f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 126666205 1250 126664955 126664969
    0xe0703050604081201090506010806011211031603150b070209190219021e07140303040e04030e0a0501030b28080d0e090901020306150702032107030e040b010c03050702 74
    0x2000419512681d0304000800100d0f1004e02000c80012072090180e07626442e000096881c2203e90900003102d180008a4030740c411544000d500204003000140c090800606843c03513841154903901a02403040324088a0794940b0840200001150641d400907003841c8520340c181c458004060701c651100000314100e400c042c04510f0300703001045421540d40d401504036842480850852202501801e041103084880d04609000841000c402a0400360b0800c4103801010a08008654251109010100e0801c2e0004030303803402940a034456480000e1038404000f48079030f6541180b410141070000a002c56124642c00c0201c810508000103555101040326580d403801340d601c13001d0b1620580418161a0340c100c080c680810b0700a882c0c05100b130b030380d52030601c0c240d1000340e482c1030300030701407184200a00b42520050920369100a0a5403d49080c0c0c000d14040000390460607000c008002465404140d0455159200480290b5080c0841c016a1300041c000c050214009030510500161030300456580b00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 126667455 1250 126666205 126666209
    0xa0504090e0c030d081e0c0405180103050115060503010303050c0a02030d030e011103150909010f0f05090d020615060d0905060a05040311030f19051b06190605060306040e07 76
    0xc04104034242040c01419500c10314a1030150080c011520036aa213580300e50560b41c45980e84112030b111000d031407484c0894100d0b00508200070b1001c18003020501d035565501140c1004202c81c40d107100703541142043c60864102104008984d0810311081100b180c0100a0320f0442c1c2d014200241c81301205140c0500300b00c0001002507042c002c4201c20348410390036031710902c15a90408000c21944050040310455448142d51901c0304000103200101c040c80c02c41402c03540f000e420000880c03440001442d200a488042c0068001070340c840c0d0402103401c004005601c0e80365003500c010310b143e0510519008080e1340d00c020300c42c05010009500411140e1903085420410390090031540c25241100052005280030341e002c030f00259591443c0c020342d50303001040daa1180303042d401c601c1c60b1002080000c03030300120b250040740074404280407070042407404c40102448100044040d16a510300b501070102c000790840c1c030416049240400078031460f26000240d0327520407415140002d06140700c1101c9843c00e05a5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 126668705 1250 126667455 126667469
    0x150b090d020108060f13020c1b06041203090f09020304030f0203030f0f06120a0615080d0815040b030a0609140703030c0210051201080a030f080105030307020d11120f06060118030303020a0504 84
    0x7841d49141b950300b16900426403100da00c0c00342c2d12070307810010044000d460000740103a4401d409200a011250008030003000c05840b90070642c483d0340c3e90300c0d1050b40d210425406420000c0d4044100303c00d140c2c120b40600b1444450303201442c81d5180c030018203402d088000d801c1c621490041e0002500c1500c81d01c1419078070b003c0c2c45080311110007030b6103090400b400350540c2c5c10094581d80400054011030015114119052940f80c00a00c2e40d220400703400a2401801c03103a9000e51147c00642e01910284411150710380210408510304600d070900d021601005070301d80e401e40d03001c038604002095002e1034240f0308960403035103601880d00d0700c00c0486007405410554a00e0400700800014040000503000c400144603840f500040008a00207844d03c01d001d100b5590103402c20041c2100520f84040b00740740151180058802a0781c1c0600892410085103240403000c0d480b000c44925034102c10000154010300c2440c0c900442d24013100c01d4080450144402000d01d0380202e100f125240c0100140d90140c056 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 126669955 1250 126668705 126668719
    0x715090512160512031e07020c06040e160905030c0f030102070501060e011a030c030708040f06051609050303040302030a0f050304081c2d0507081c150b090d020108060f 74
    0x4902c400400e900703900e10032549440b50b0325440401208038010b0b203101d4401c0711250300600b45600f1031000c00701802402c00c021030241d10a003604030394031074014102501003c0c0a10fa114070702000e0080400b40304584903810b10011402c00c10044e0b5000a0f03c100044042d901c5102c1505660b02081c06400740320b400034529420300402040e42c61554100c80c1c12030b50900700e501c11102c2c07821010940341c40203079141c0c1d0b83d0100070400503c1940c0100c002581052242d628100c090b18291a04406c032041510814040a2101c108213040c40c1d101401c4806403d080780510314203860340d40001c0c0c0d80e10058100802c03041c90f01c5416000c1c82014000c0d80c0040214406403030269003814182c0203580241c2c0340450214070040042d088541d441c0440d2400815040a011491040000195810707001580110f6001c1c0c0204070b107801c035070f0a04622000a20910f400409e401000d002c4e0181d140c2560303004480d116005012001e4540d94084201d0303101502801c0124154503000080761841c5580c0b4515900181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 126671205 1250 126669955 126669967
    0x4090807080c0a02090a181707052a0a0503070303080c040b030907150c030906050d090c09020a020708030a021209041418010f0e12130503060702010204060f050715090512 75
    0x8000c200f03202e480b0320071541412140e0b500c1c4a00011244101c41000d0060701c02d11040e0002061581c2c0007900040c02904c45041101541e00c892402c10b20926550716030360740e05800f80e80c180c004040c150782d0020440e51400410304001c0420340e02c007030a10029080042d1400031030180000001224041c2094007021784e946d10b8070181d07480e920305141c4a50450083c0405601407064480c0308c80000d07145d8165a1411100d05c0c140c030446075900031489c05520140e031207040c03800182502c1003980042c45140000f50f203c8070305000207070070400603600001a54108020700c026440d40401c629410310219080c55440d80e102c074012400500c0122000c8041465101c217024003101ca440c000147d04d41094028015404580401c4007510103031800c0d102a036001040541010040001800f004180e110340010a80d81d120006403800b0002c1d038510300540d40c001020300c65180c1c410344810f955449801d050346018400c1c0d442c0821a581184030001c0b0b90340d140390000c100311081c00f200460000e4142055105c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 126672455 1250 126671205 126671227
    0x21c05060102070504050f07030f0b0d03080f18070603050405100e010b0f06040f031106130e01030b0a060608131b2705040b040b04030903051915050606090409080708 73
    0x401940c1803405442a141c0000325072a160080724481d20030344c202c00c651a103074410300340c01030641d5049440c641d035258014100e258860408000c41e86000e590340315824140384018611111000d03240d1883c50806044e8001d40b1300300082c6180c100d6a103072800007550b50311424401e06000c030b42d280d0074240c1424045420b034021415040450507403421103400c9404002c0000b0480d080c0f20f248140c46a0714030320101000440c080c0e40d0031079408000540124a8520201c0007043c0c0c402c030941103090701c12508030061051184010000343d03c8450356204202c03090400801906400004018502046209140d0700030420201d25080d2001d200754103030700c14075440e06c0a0b0111034a2443d03102018045903444620f0f01c20b214082c0c0350085810080550081e112030311004c880c0e00005004ad01170180c80c800000020b13108210410300504602002001b88007246011180e000e03c280f080c404560602003440816500c2c1d40031100d00390401c0b280010f88207075501d0401c169026901c405001c1c9400401c01d40000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 126673705 1250 126672455 126672461
    0x7030c050f0103090b06060f070507030c061106130803040f17042d0603110c030307031406190603052806380d090221010e030922021c 59
    0x2548003218028007a80098004404130303902c1300005007024a80e00041a0582403040c000c102409035055110b00d44a404e49401d4a0100161b00403903407174501c078004111041d8052000c07080800c400020784001e007801c000091016480340c1002e8280301c0000f02081c2005401d0042070450b9600c030018032405900c2c42d1803401b1503001403289842c0c10750071031040d00805504200101c810342c007002d20201e00604006040f4018144404040741403103003000005c00e403010420246110b080706130ba003c101803500c0318129003007560140456000701c11601c0d4985558451942507026030300300b494002410783c0c0c0c00f208500c2c1d40791888030500c1c282490320b0b031011030401d0303641101003030350081d2480652001941c40c47d0300d10f29150340f8003440a100038000305d190b6494140c1c003c084906415001040d00c0b10581c00184401d0a010701800c2407014145103c0140b40c000e0046070007010000c03000d14213045080e80070840d64910700007204002060304e800c070300c2da082c01d5078162201101d0805121300e804204045240003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 126674955 1250 126673705 126673709
    0x20705090c0a050901170405011410081e0102041806060e0a060c02010305060103020d11030108160602100903020a06290901080d110111030c03010801050c04230109030b19050901020307080402101107030c 89
    0x10600380e00005024007041c000c40004484048004000e10b50340689a123a0b0303048404a0020dc55408000028000c40d072003607441030155981000264891824030040c00700390304586051b0007110440d0040107020303080b80074961041d8083c01c02003907a0740c0303000040b4020311414001c071264500e01070523040f400e09040041c50586440d001160b250032504072008200110074072403000140d0100390380c40e0f8040e0b559080300314054420700445001c40d0a940c0c3c0c00040d40c01521942c0b40002e03411035501d03d444800341e11003050300401d4612002950422540070b8039010030400c400c060201d902c081b403401c2c01003584060b01e0b8424100356a526800c001900c10450340c130030300c2022427641c00d2a000c0b40d45480a2011034084841c14100014518400f408914921804984407810701601100020103c0e2404d07044520859003107600038586004200400c0881e04082c0c40f040c00d0743e105204101d01d59800c011301c941c0042d0120707054404504d035403008a0359408112910701d0342d8018004000b04101000c0303103002c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 126676205 1250 126674955 126674981
    0x51e1905030c0a08120c03040308191709060a1d0304120317060102030702010f0216180e0304030209041e140106050405060d032106050604080d020705090c0a05090117040501 76
    0x40d80000180c10080d8101d072601444440c3d801081d245800c0e8070000b80105052801c6ca4180d074100350342d9840b03000d500e03008a1601c800c9e01e00106801a043c40e405450b80804603000d500d9030354141441601103640d04401003c1118266441e4043c0241a0803610424000034980049030b40d41c0361a08980b030840304c00000200c2c00300d440441804501076180107600c1c82014103034000c6040c09103c0c1c004690510312200c041c0c0550058410766540303940103000050143c1a0f541101410300c800e03407620300407644003202160f8103410a010034001641c607850443d80040d008500c0151510095056602e6000405402422501071140484801c0c074107401c164200e42d804c4800304101d0380c600d4140f1200d02a0040c00070f0001d0403111a21598890b55604448010007940d00060010b03241c0000c290f0365131203600300e801ca59116001810101c3d904102000103060152180c5403075050900c0312980c207002c1e200e82c0070244407001c40c410241d03900c07034102c2d11910050800c5a441600302410568002c104c0304441c03007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 126677455 1250 126676205 126676213
    0x120603080a030e0d1706010c05060f01031b08031603020f0a1104050703140a1a030708011508010608100e010f18060509030a02100e0f0d080906090115051e190503 71
    0x2c0c03c0301012815505800741610303108202801e000010390340d140004e040a040c40315429038000072800c2000024400c2043d4000509a0f5040d41461035078083c800000302c003180d00e85041440780440200603103c01c0c141da081d405a00355000e2034103034149000c5200c5a032440c8106284601804120307030b85110146415581000303c2d440c3c20004509680486004d40c504900d640d002c82c2e40c0c21101e81c0010701c0080485468840b0080707500010f400c04805030b015004581d15520b00f0302d0a8010b185210300201201d80080102c1464030754030700d4454075402445d10030030341d85442d84404010207400481d00310b4000c06041141c0e010303461840b48208045001516000c0c81d000c00500002000021030b0361800c510b4008040356011800950054852442c02004a0040d03914518401c4004c02c41c4490143ca140c075014101d01c0d007891400d2400f00010301e101d407140e0500c500f02c8c08040303140c41d9800540700d00780c1d03204c80dd12191960002042003a841e8940e0013a030414007400c03a500005c000c0c0000d50b90104c060ba = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 126678705 1250 126677455 126677471
    0xf060509121501061215030308100f08010c030506090603060414070506040609081b06180102120d0e0613080d0209041d160501030203090601050d05190605061003050708060907120603080a03 83
    0xb1040b0b0380c603e618000c0342206d541c800e00100b0300541501b0740c031441000011850a0b140c440701c3c120b034482c85e8400050b5a4440c1c000c3c0f05041e4150003000e0f40000140c0e684480c500d0300c8000a41d41d485d0250018100000c20002603158413401c4c011640508000383c030a9550325922071005140c1e003a144105085406441503660000e14856009603441200421403400c143c3c0784141e400903c1000100503056200d404c801907810729802e000b900030f26615010004503050101500da0420b4401464003102102d030b062218000f80d45c1c00d059600c144041400140c681c1102c40c081402003a1750700441400f11070800442d00900380c001385044907803000c03008001c1900e640340019016400300380c580400c4d5400c11780c018070080c1450b4000d604100d0240c011191081d105045681051100381c0003036607541c4e01c03401040903504021110b00c44020b081d01d0204641d00c1c003004010400380010300501d11860b25000443c00032407043d0300034006036031807032001c02c030495072490100c08981c060000780c00444d0030f203900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 126679955 1250 126678705 126678737
    0x20303041502100c0e0d11010507051002190807020a0b04060603020913150b06040b090a0b160309170d0810050402120f0c070302190206070609080304110a0f06050912150106 76
    0x54110040c03000741103d0311b40550b9541c1c1c80000342801c0c3d4154100b20b0240104070104008000c141003019036801c00680c0c815503031890071407146d603040c00c680c14000c1d20b609020721541d00040d6030015641000140269880324500350001c5e082644c0080d5100621409001c0c0464254080782d403074600c44e08501003505a00560b01080d14006950981e121318240401c2028040c080010101c00f01300a140001840d2605001c110540144030a0b040c1d07007030301c40112010076803c041004007628180d80c3c64a01e4a403e084501d540b600201210010000f101e00400d03450523a038034001d005010003d03c255150030741c0880307100e1030080c101d801e200040c819001041000409508482c030281d056409001c0351418043c0805c1c04103108c280481e0040410081100414118803403058100d100b822116036a0400d81000e041011b82078040c81d101e0703a1001800c211104584c815082190a141404d58885070008001808a8043c903a2654140601004001d40650302d40255050740d046803034a0307540000c1210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 126681205 1250 126679955 126679967
    0x3040813080c0a060c061d0f0d0201050402130f0e01020a020124030201050f0f0c0102040b0301090b01090e0a0c11070e0403090b07110f060705010606020102030114040905030d0504020303041502100c 87
    0x903080d80c01c0824030030180f020f940304002c100c5240e0300845010843c0e65001001c01000610f500301c1f241160841d00c211f203240c2c0407d220745003080600303200902450500e60000354800d01c0926040b0100b50b5510305102c40c04001c1d420950b180320b1710074000c54541e40c020f04040c0c0038025003c68003201c0c80a0110040e080750020021100392501a5112403c1500c50410469a80c0c802940c9000002080c05540c01c220ba00740001d10250080866190310380d40740800c1c01050b06c00e9400c94905101003660203200544451f00415840702c44c400d4041152000408103464950518000c00e10502850300045080226101c1c1107001b81d20a9403081c24040d40e6140680480c0140070009100c41c2d0f0f40d00c02034000e460298200075071070b18028285031400660b5134495007103600950010000d80d4000c070042007a50408070380008410002d4030140041441583c0d004e46134440e03080080704083c3c0e6500450150f48041050310060282c0e02d130200b81510359100040d544400c1e10301064031082c1044000b003000d510681c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 126682455 1250 126681205 126681223
    0x110a03031a03060c2d0d09121b0618140c10050307020a0609150c09080705010311040b0a0302041a120601030b030d0c150f020d2304260304081308 64
    0x20181c074100144201400161718284100a14100550110145081c40a001002d451083c800c0000f04000d19150111100c00102080004d01c01d600d461038000218001003240c825903c041c0004039042191a1240301c001211406003028543c0c20581c80d40c28000924600c1081045a050780c0c088401075044a40c0d1008842000c016040104c507200045c074036400c1400d4452040c0040f41a00005200c407100f12110105840d000802210342040089030600c00d000150800380790030300a407000b807a141070341d61041c0d03c690511030000040700100284258107440c00f92070180c2500108100342d006074a0980c215070741690151540c10b0101e055507009101d01d1194640107005482120f45d140010b4400341581c20b81030b904d0031b88600421083c143d6511030603110741040c0a00507102c00c4140744000031110144202060811b0a40c44010120040c000b49540a903111002100c24209040076054031206000c1d081e1a100e80481800f04104020015098041d01000d2200301c5036540c503565540c0c2d900c12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 126683705 1250 126682455 126682471
    0xa08040314011103040602070b0f2e031e0501050708011a180909010606110a03140705070503061302090f01060e0103020f090a0f06020d18050d0201110a03031a0306 72
    0x80104100254070140c0d01d1449a10315000081c8070f00b0281e40080d03042d44200c404554075540002c1e50030400210f0b1400703580104000c0ea10001502e031030044401441610354482115500c030600f0301041a2005071041c019507408040390851180349000000050030b48001203559500707010009140c01d21807654103040700c03062203201203203032850019402c081e130140420003c001441100d6885e43d445041c90705000d4955000000340d081e1410b2001004041207912840c040e0300703d100180003003a840b100700e0a03d801e6411541d9959000f900d0b0152034031f1141e1b44040d130117008090401c24207186400c10036103030178025646403003039507190050450016000d01820011804520404800d54480c1c1c0c06000d04203004114a854045078000040f0010840d52000d4001800d0080504c0074079411700c680d0140340881d0078901a088801254150555010300405001d000c10443d80c100356032051035904000310040c1c06862001c3e0319070034000d0103042c001e11800e104d0006030500301c049090000d5054890050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 126684955 1250 126683705 126683707
    0x50103230d05030a021204120210090203030a4a0103021e0a0c0b09060619030b19020f0307180605090312070206070203061e01060e010c020d05100c090f05030a08 71
    0x80d054090302c031600007400039500203900703200c0c0c00c2d100800206c0d01c2d401140282c1c1503000103e1820f60003071038401018903426000741003020000040c0c40010560714100c006051594031040e0005d026554556200e1102801d200551203000f620249218036607000320344049050282181000190305920803210310702615040714411603d0304900001030984031016117800c14003250f503500d50700c4402c0019900e0f02c141b0b4101c0f2007442607074134004540781c00703401000110000d554a5a109c0304c0c0c0e011001010401462403100280b0074101590341229084010700490546070305080000803d01c11602c403090b10740308204031021952328060802e903519404000c0051070b0b01d0416131003a04140c0c00c1032404076007181c014841c54005a4007400b55038490300320000c180c081100480880c04a040e01a8055030921103200c12204869a1101030400000d405485000b558422442e0452030b140201e201040705610b40340780c07990040d074030401c1d0340111001803107810350980d120000c25450b00c040c1d103001082400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 126686205 1250 126684955 126684973
    0x1c2303070215070e1003020301050a14090406090609080403140606030f10091103010e030a0311040e060d020d060c0504030303110a050417030d0203040b0f10030305030c1b0a050105010323 82
    0x480c1d460060350040f102c1c685031003c080390401168200710b41200c08408680c000c4014070042c20084e030ba2074003c2888200003106a154040800d00139540640054041500c03140c024041c40340039004140c1c4103a00c60343c0c0f2940c0b2a40c4e030402220100c028500c002145c0540404103070140703800a0802d00340d510480141c200d55405802050082600c11001c64401e41c61841d851142c0e0380070700c0b030544c5011000d4051a80c0f83c0f000c000080c125103580b05400300f420b07030500061000d10401d071011a407202c2d055811006072001d50001902d88030300640020100d908002500350300650042c00780c002c8070710036103041c4a0340c615001d8031452405902985000200240001c0194140c2c1c218a1041080d05409903458809400b01d80000ea03402101e0a4898060074014090f540460092042c7e12054001040d01d4039803c1d503900510324400540341d100d00c0c0202048120542c0004d0030ba0941d02c82641301120308402d005c0c50158041d0000b48402d84901404801d41c69500d107401000303034200001b68000c1c002c003107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 126687455 1250 126686205 126686233
    0x30406030b0f030105090609100c0e0d03030914030d1103040b0f19050916090b01142a0604030f020a0b0106030203040606090906091407030f02090601021c23030702 72
    0x310803000380d0302c144019950503032030302c00707115150041e03103200080c1c40c079894150707512841c2060f9114100030a034a400310b2900c2596101e001e54001c1e8000b140d15140040c29828101c000e801c0303c240151500c100307002e50010900d0000003e10440034a5041130001803510711007800d0900084402030f1450a202c40000d1100b170301010600d910056103060303100c900103100b10000449408803100107050b448040c079801100e40e005202402800011818084cd03041032000822031440e0b0206c100202c41c000c54408074403074a030350100303407074660302441042449030581e48255140001c0d80c055000c604d280d0314140501e480403900c032103400e402042c82d8209034a02170f003c800a6100801c1070b130b603c55650b207002c21180035900030710f81c406001d25408148004181020243c0c0b00001504412940c08101c041000403540c01100301015011502940141c0d0760313800603170a0031248510f030400f1005c1001c4498080360004041c80000980c05074070b041002440901009174403080d510a4007684c081c0c00307060205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 126688705 1250 126687455 126687461
    0x1b01091523060d0506090a110d052a0d0317011415030402030a0b150315090709021309090813060801240e031603030809060103120c0c030209100302040e010e03040603 73
    0x14000d009028450f5280e2a00c2e82030403410b582c48003650300306141c24802c1c48411500d52415082c212040340100b1100c0c0c1d52282d940788440980a000c1070800700c0300d80d92aa01004130104802c0261184440100c1880c0040c1200342c1c0d0b210280c041051000003207980c0c81c88441a10f40700c00044d04051a041d14440f44078025040104100d03450303c01c2d8482203000500781d51016000e0100000c100e0320b480001c0e03041500705070342050200000b121131420060b24038000501d14085400e040401a1b803130011543c0202c0003103464105801c0700d410300300700100304280d0000034140d09180d40300144280c5e80b507141c00c9441840078801d42441c04e0180203070030751911f9042c03015000c10405080c042803c01840d03012070704180c806c00c60709640f590706400801c01d00d034120340d81d282d20007100c9018080c250f05659610621410001120040100c2c3c2c001d40d4041085800741361010f50740041c0320074200d103400d00c0261b0381d06c0d5a50200301c5c0a0381c1440a0048103000500600300801030090145041c1401d0070800c40003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 126689955 1250 126688705 126688711
    0x15050a0e0c04080102070f02040e0d0e0d03180b09130209010c060b03010b03101b080115030c211a0f0d110f091e090a0308010315021b01091523 63
    0x80c1c0c1504010015100d0401d200a109240c03044034a204810007900412003219003c0e401131040b40c10401c4500c5001d40c2c080c04511030a070301114883c104002e0342c01c00701c9211545500e0003c080c0380501c008200100c0020152529500868500124003640402d40c000e074000d19811501141c1166071400014083d42c12130214103c0107800019518030400000b403420101d001101a40c66030b542051103e0340700040304000c1e800c20b605000340503500d07190b4074aa000b4a08800381e070415030340b460000030092051481c40d41d420300100261602d0300005051a0040015110204000c000d511172100d00d82040300c103128000000614101d00103040d500c48103180e6100b6804203034088004440007080c0c0d40c40100450181e00c02d01591454414209060500703842d0181c400d148035031044861900099220320310300d0540340c5c041c0e030307000b121030490f48648041e00451141f282c524403110300510700e070303241580034000c8180210010564100794000c160212581d00d0200a803104450f074840c4242c040038103042d03030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 126691205 1250 126689955 126689971
    0xb0901050706111801030b03010908090d030201150e010e010905010522020f0d0e060a0b030613030e060301060f080c0a02070306051506040e0a06080111070b04050f030d0606020115050a0e 82
    0xc50040c0d2943c0205076900802d52104281e2000182c6002541e00d4030032942d601c0b02c143d00800420a8a80b1000b003a030248950071441040350709407010801d4230079046007004003040d29031701342802e4440c2a800c403101d600b4090860030b00380d92030001804894034024141200c502030802040d07404d5070300007420404100400c5081a9808100c4405058040d5008100a02e00a1400924506031b180341d03d06244c805001e551040e13041c8000c03802c803a5004a2a180c10901b10401c84000000310300e800e9071020b4660202e664404000b100000c2d5141d000207550a142046585099482e510503001225900402040e000164070002d410b03c0003404561010b074001c8101800f078400e446480002960540c401d41101c00d5030040901030107207115040c0600000350030144001d01000041d004620442c0c02140c0001c4c000304c109001190130b0100601c40c01e4244003048040d80e5880c4d81d58401c890203407456108003001507192811014070700070802049800e68078000c000b0700c9264906040f400c3c2d0101c1c0508030318 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 126692455 1250 126691205 126691211
    0x90f01180f060507020f0a03080405060309010f0f02030613051005040f0b030a0309050a150503040b070e090c0a09291e1204030e04020c0d110c04050f1503070b0901050706 75
    0x852010100c1c24030000600e00303a07a50f540d5074a480d206020070040c3c520107503402070350b20f058103000143c2d185094a045da1010713100382d601c030307980c898105000d880041000f0032072628008038420a00307116001144910f0302524003400d4007021300d400c042194000c0f40c20348800c2c1c003015005c4c804c1e484c09403c6a410007001c180d02140f001c40500c00079042410b5600201c012480c003900803c0142002d190450080c0110694140c07141150400a40144801003000342544103220005214038003442911704405070145c0042c106260490720036100c1d0340942e114001080c0c0e24200080c80030302c240c4e440c00c1b07441c0c01c1004200004a1031441e45590781c1190f100c029404c0b05102c04081c403c0364000c00352918021007a0070b1160760910341406001c505008581e40d0003a0700400c8102c4c4404400144102a600307280b030059410004600c04a00f031010188005034000c0c245000c4c01011505a20b10034015428840d900b120748418000305139a90300341d4480d04024000038060000e07290300600c00303008a5805401e001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 126693705 1250 126692455 126692459
    0x1c02030603030705010618061e0603090303060b030a0e12040303170714030f040b131101140d0e0307020a090c0f0c0c03020a06030e1e070504050618010314060c090f0118 74
    0x1340d0039034046822140c050700c00380b802c03081181c1e00c0c0e000380b07401041c08031b00d00c0c002c018284030350aa40100c20300810090545580358802014425401200144038080c4040c0c1c4a051244d021f801410717540410500d544140000c01031140c0f0220200d078101c070341c10b480c2d01c015950400b03030310722000d42c0041911080c0003d0648000000c841e00c40110300c0740c3e2010040712200c5c03400b0b1405802c01c0b0000b4207003691414107071400c6400030315000c0c1100031a000074207009041040f41075204105201e10140490303003509024030b00032a078100101510402d48200c444803140742d2219002012924034107000d00005000c0c5d52070520703180c0107414a0281502403a45468035036141e402103501c00c510382e44032100007680e441aa220b001c5c400e0003d000604c10460300d500400000308551a0703200e0b400e0041d148141d036a41c0220384255104442d9445608200150060030740c1d490038010300080c3c0321500c0b84040e0107410001a601a01007044410b201001400718031310324007600044842c0380d240e0441040c804021500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 126694955 1250 126693705 126693713
    0x5130908040305060405060a1b050c010b19140d030509060c0106090c050c0105091501090c02010605030d0c031404050d080a030e01050a0c0f260c160b04020a05061c020306030307 78
    0xc00241d4090802049181442c6c50210724007280102565005031801c070a8042c0049480c04010740018549001521159494402030040003000103c0343e00030355500100704040d210000c28803c4a048003041200786098406006030483d0f0b9072001400280100215401c0d0f00e4420090502e00c00404000122141c1310b030b41031011a1144d07185000855404503a090804409003d4030790702000d00800340120342144141c00300e42003018010800d85603115180e40c1da06034401d5100300003d2000504440c610450480007602c1d003001000107038001541d07040300201a5200303100f12011108c0144c103d000c009583c0d140c0c0c030034607001341100ea800c050b2511038004401c1424002ca41c0034500700c40d0700107041e0039201c401a1284040700401014814484805104041e0b1601c81d211a000801005840350703072680c090403514460050805c0001c03203c452200c0601c440030418502c87c0e07100b541c0d446225601d940411045001c1c0000f075a0032a1007070301180c0b40310440c0703401544d0442d102400b1242450396541da = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 126696205 1250 126694955 126694957
    0xd0e190308010f050402160204050912030103060606080702060106020a0b04170c011b030b0a09090c0f0602010507020d0518010f03060b0d020309010c0903020319081308060402010f020f0705130908 86
    0x10140c00081440740184840840c40280360000c0008960452500c606604003007180c800425005c0c0c4115501c80008444420920100a20f9800854015a81d40e12443d00000811041c003030000001c8010300042d04580c000030b01e007810fa402c42c0d0010f000414440d507940c6210381c0c0c0284212031140c0300503600307140280c0b01800381c074144545400100740c1d11600031078800d010b6045c0740f102c0c1c08c043c00c014415801c1d440309003048007501c440100c049801a26820034410641c141e42c06000217041910001604941c190f000354011b0080d58262140c1c90034036013003141c00d801018070ba41c5001c081500204441c1d03000d00e82c80f0032955402e007000324030710390754451035203041d04410203802e10503400004112848070300307210b004803201d060306011003c142142c02290740c3c1c1c1041030035089841c0b100150700003840b5085043d5203061412001011100c1d8446031040d8844a06503800c902203001ba445c95155940040340341c07800510a04010400c00b440c11041212040294001140040e81c41c404400400c282034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 126697455 1250 126696205 126696253
    0x120a09050907031a01030209180903210a060b04030230030a02161d060d0f020a0f06110703080f16020307030f0b18060a0b060903010507020f010c050f0d0e 68
    0x3440000d4254a25080c0c10007000004d2295810103204101d0000c02da5500c003c030440f021445c400384203556a0f000710705459032040307603079114551030b840f0299540007001281c0d462080118440a0001340c2e43c0740ba40c0c41050080d400005c1d80000c0d55400008011070f0081592040c1c07036802000848624850680c6003107600c50300703070000140c000901e911b807400c1d060040c0200602c07005528a42c4035103c1980507180f0300c8040d09041c03044201b81c80403014004101d4158606030b030002e000e05078255403800305904420300340c4108004626003c03852003a110703000c10000b080b0b0b60400c40307161400038a59000b100300c0e4442803003525030001d0000c604000d40c8040003030348082c5110b441414291840303820f00c1d24004500600b04122455100281d0a500784081401d94010001038004146400c081000030824020311007815059840c05003006002079000076051395401c00080200804030441c9400c4419100d0680c0c2180581c0c030401070000b030741150783c1c0401c80080041090b0781480d1045a00600340744108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 126698705 1250 126697455 126697457
    0x706050a15060201230405070504090f0b100f0501171b0d1a01030b030d02100902040e010c0c060f020909060f0109080d0f030c05030105031b06040906180501090c02120a09050907 78
    0x1404c40014502c0300d000d05c00600040980d01184900e80365490a43d00c501e28003403c1c0c0100d4807910400208040342c00710f0b0400e50b1b03021121962514292010001001c103a109951202135401d0b8006040d5000d0b0440e81d504d0070f10a400c40140d640c2d00c060a00545e65688040c0c2540641042001d051801912030a24400c0c143c000301c07000901003a0005040c0c0340c44800e030500c01d03000055510506600020700c401416281d07140401d005c00340e400064001c0207900e034070000c25400c1501041a16030300001c103c0c0030034800c1c0c100300070510a01c40f811040303004064040f030b0401c01c24008280c5510340200100001c01c01403505143c0651965030590500d4103a80c801c0c2d000c070b00510341c1c165015401d13004584920a240c941a42190f1401c070010f9a02c05124003107406c88801c0040c0000c0039202c910464010b03200c643c02c01e10290f03581d5003c00700ca441004142c541a2403810001040d941c0703140c05011001d191507402420a80d5800300d5045059014208800034000d5103400090170b40c4070f91a8192080d043c2e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 126699955 1250 126698705 126698711
    0x301090609060506090f04240612150605030c24040e01030c05010206150103090201140c03070c0905060d020105130e0126010c050307050a020a060204030b060a06080106050706050a15060201 83
    0x1c140350036415a0b001414440c4910004410040c903504d03003c1105038019008030001800c4049110403054082c007150181e40400d003410000f150702e105100e03882a00307901c00c00440210510062640080340c056008480d410b4102c95602c00023840c0000c1c0c90032a034110708022006804402c0030040e529400756000c0308504025000410034840a0021b14008000070b0020b01054540314080006000001d41c5150500d6640c0b600300c025a40b01d161036101440701030045680d6100d0a01d0f0340c0d9a80d81221108854040030854040707074014050185500a0802030b02600188505500542e031035080840500741c8003140c150300140c000c120300c02480c0202880140012000024000d620028001d071030b11000c107070704140f09541d13940c0c2c0c0101100d900c8041031800585840080104904207110000094071190002c41c010090040c00011325000b450201d500310582d680c0c032181925803800903c240804140305118120200d001c0340c10096010504090004041d06644524540450540c10000041c0c3d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 126701205 1250 126699955 126699971
    0xf0d110309091608150109170c0315010807080a02060306100c06060303051908090a0201140418020c010c0c0b0a0504061d060f060409020a09090501020915071106162003010906 77
    0x81c100c80c8690f0030180441c005c007514110400040e04180c0c66109140131400d01e814805208002800380340303e404401001d440e00f03040045032003c4044028000c02c0840c2c0034000001031405000103403190000d038041d203480d042d40c0c1c07040c08100240e81c140407845d040c04078184220000591501c200c0015605c65101d05858849103403901e03404082c05c003041c40c2405141ca003400080c03c8005010204241d09186c1801511041d2a164117940107075030008d00070341001c2500e180c104001e03402034085e40b21054000c002100e0202c00888464203440030142c001404000400c84d01c01d01c580001c0e42c054010040070a032500c044c20300340c0c042070340640010341c15000390b000d00105030074040e02c141d0448421a014811284031fa000100c54038032500c11020000e5454100a041040030340588082440041072040600e04040c04107007540d04c682c00407070704d12808808032142c2d480c06409a910308008545c025543d01c6142d5148041041040b80c5540b01451410030b900c1701c4d5130240a07540c1058820300001c61000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 126702455 1250 126701205 126701207
    0xc08040e160903080315060d1815020a0503070c0c0320090109110f07050f0609030a03110301061e020f100f0b03030c28080a1706030f0d1103090916 65
    0x80c5840c1d00140070024207030001c101162514051320b401144252030400001e05402c0041c030103124900814843c02c0c00c1c19404507074002e0194510010034058200980500400400c0703400300d1040c94070182c0803513000c1c408503041505c1040e11441d5a03104080702d0300425141c0c0c48511140c0c0003070408100c02c00314206521460b05003100d0003030041001d680184021091a1400401da002c0c2010b140c5d113541021407400c0a0103010000d0040e03e083c103034185c8825051001c4446c0c1c881d4842c03508880881d00b000c1c2e0552803001e02c04102c90484071702d81c3d40c455420200c41d0038a03e00d0301d82021a1021442680d415900ba05421701c030100d21489000303c0082c50051090b46407083d40d00d030004e1315119410a00c4940f440c0000410041e090580014a01d60014402d01144c1801d4100c2d15000d0100440492081007094004900001c10b40260100301d44642d110010103039100c4418005810681100c2410300d0454060341c010940551184c0541e070030010340d240421881d100c210f440e08003803c00d030502c00e9101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 126703705 1250 126702455 126702481
    0x2001020d020d1503080a050703090302090903040501020609070e04030809010207060e06060109050307050d020f030a060203270105090a02100201020405040203130b0708010b0f030a060506310e0c0a0c08040e 90
    0x41208441c00c900f2185142c58000b0740380214135010701880f41c000748103400c162203508640c0c00b45070b00520400c46418041e0599980340c00c00e000e9940544540d0020880c5050002802800c442443c00c0c0414641c1c0c41e6a4100c07035455018000d2a0f156400f485884c00180050050101d4160320030000c14591610b0070004104145070f52083c5d001e5005940240001c1e20798055803849130f80c0540300c040c1100054070110346010006080500154404824804005c1d115101200036020001820300d07980c405a5644c0d0899900382e6406403580d01c042000801820069040850501c0900005041542d00c1000c5800e0fa0302c1100e141384a09110020f600c204054070156541001c10351034810050340c14013a0410a510900713241701082d02c800300004141421302c0e04114040c18025142035241e01c0407820140c29500841011908941c24401c0001c3d00140c20302004201c404a43d65007019886650140e403040e4011001d2008004000b60800c021541c414000e00040462003404941071401144050103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 126704955 1250 126703705 126703721
    0xd180c050105070b060405040c12030c03170705120402030102090d050c04200412060603170c0d03050c0901030b030f0a120206091b041802040f0b030f0604020a03032001020d020d 78
    0x50101c00e21040780424a521030f5998848402d0f100010940c80702c0c10b003051407031101d038400c680ac2d05000940c201007550000c40c4580c8240300783c9a410f0300250403820803180050851b200f0001a005100005018010a180d6a0050300141c001071600b03007030001041034503501440a8515901001101446051600c0340c0c10881b258034246160410601d4080c00a51082d481000c0c41200101c0389441804040c1d8440001107500010000280c0d04019a03c2139540010f14264228000c0d40003134a95940207004240c031030355403500694134146804006400605007094265054031072290a1134003507004120198005000e90440c0300e2140c0c0300740000303180c1000242408102d0b00700c1d0b106080b507100480152030800301c2c111800709003640c09100e8010a84a82c43d4007035031190400d400e0003100000e56103c84450034098043d00d2428010380790441e91540262002500441203d5040003c64401d040b040802064001e0118000c801d665590342682c06c914045080f4540c0000d44404480c614465a42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 126706205 1250 126704955 126704957
    0x907081b010207030201080a110307030504021c02280312020a2001022a040603140f0714090415050f01230d030518120a05010b0a0b030112080d180c0501 67
    0x454416030340e000030f44607030041c80000d050054600200e1030503d01074000407403d20004003115144d00d09060010060542668140d0203001c81019030039200310a242d0143c620f54016003090b500c4070001784241007141c8220004540108070f003001000055040300600000041d40c1d0040204502500300484552400ca05581d104645013010484030f0360042003040408211210b0802d5900002d18440c0d040450000b0280c3c0c4140380c09404420803403031080300c0100c1c03821042190b0040c0354849105580b507189008108c0802c10707100742c1d0143c03031610f00e40d000c3e4054480c8105860720f0000322033540c140e4605913285010070040500500202c0b104218405800c10a0303108000142c4410f400702d203861055210140800400013141841c0c03840c0401460740e40038007d0084020241d10b00c9103592680b1019030102e486500b02000c0503d50310340103007118250f910709544a49141d00c1c09a241058210044046031400301c140005004450781d8400e100842d88034800100011006181c4003003440f60035000300d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 126707455 1250 126706205 126706243
    0x8010504140601030f0209070e18070f020d081b09180115080c1b01060b070b04050105010902131806030804090b030c012f0c0303040803220509040209041406090708 72
    0x4003054024080c0005e0b16019210a4550340f1100022a44d026883d0400364200803902040c0301030483c820310540c0b0604466444805031105864220389900881c0500c2000482d554085002c070000c05a28491401e11980c1003031502d543c0d4004152015130103413030000790101200040262290001242e980e1141c1454034062600e4401180c54440c05440d007410390728491940310ba611828254042000b510b81c02e00340700d86500d82c0c0c1c80c1c50300080c0000c4504561a50804000144929250003034174980c8101c400319110345800c20700c1042d5264000c44001001c592184000008501e2500052018000050003caa081da401007403525003c07041107404c2c10440d07401e004d10f5000e0302c0140d0110301c1c030740302c407680f60008841003409925121601d00c0b8540d040c0400500000d403c1c400200170400d60300c006425516000000164000e07401180c803480e0307000001c030302c0001c00628200c3c900c00d80c01442145c440800301d0980308218a0880103d03503a5045501006c82400b00e44030410903004220002c3c002a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 126708705 1250 126707455 126707459
    0x602030d0e01061d060a05030f0c120f0c0d0602040e010308070b07080f0a020a090b0d0b0102060c09031216120e13060f0303032a08060916090b0c0c0a08010504140601 73
    0x40c010a082400e20f0007051240b42d0080341c002e07a06c0704688002404002e084603a1039120580b02a01c0e00740d80c80c070040c8118180b0002d1002e101d80810070301e8003080703d80042c0264408078410302030381c000c00d81c908445840d8200004640b54804800c0c59001c0e6014018140c2ca400480c07900f0340d18103d01602140520010000300815080c0d842002a400300c2000409a15843c03014002d503034100c02500f040e10502c6010581103030f864456404004404001da0842d00281c551f124501c0d4644520400e42d45c0503044820000300c81c0c0840d20003018140c511704c5900f440701c0090b48a1051050714140d4400c0001c2c4000d603442020b01c4c0802180c082c100441d1010002285007129030b460541071b600c0014241600c40ca00200c40c4450800b64040c0c02149011000144034114401084a001115854400e0042c813021030007200c0300d001c071004000300c80d4442110300c0d420300c001021180c02c8000c0c0301c45180328141d121843c1d601c400b1070b25030046c1100000440c00e81000d04d0011001201c2c1190080d90368000401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 126709955 1250 126708705 126708719
    0x1e031a15070506011716030512090f0d03030c09050a050d0b06010e0618010f1110050411041e050105040e0615060f0403200f030c060f130602030d0e0106 67
    0x9101080082250056003000c40c01148025078058034902030258041e2400008034003c540c0d000803010441003043d2119014500000f507000c141c075000207011940725507106558421a01c00508584100604602d46141c0d03040c0000d150401340e140450010792102e0410505e6030300031019201401c411107010200a0821000c20f5a01c1c0da00d440140200c3c4003540411081d03409080d591214281c0503005c95600e00c1005600b005d14458008201d000450b54000701030700074411100314070408140b50243c12140c0308200c007040a030070082c0003518100d9145400303150b00e640f0780c450000c0c41d000201241c1046100040303c1021140143d120a000e00c7c1010f100c20144000845c0c03083c0d1203c0703000c0c000311101c08402e01281482c021610760000607000001e021003808040d1840800301030910300310580c58401c07001489815100be00ba00340d051381c403848084400f40b4160020300a4a603044510505103907a24208000c0200c1945c00b4101681000031804400719a034002c0500c1420700000a02500c0d2510078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 126711205 1250 126709955 126709991
    0x40f0b120d140d0b0402071b0e07080112020307180f0605060f070305030709081b090714030604020d020d061203080907030b01060f031b09050a09062102010912031e03 73
    0x1150a1070000c001985504810300d44e40a481d8840c8090000c5440354030b280342000c40c0c2050084081d103280c5640d04005000c1240c01420b500c03988055840000c20303440c04030320a00040004004a07414001c070304000c40ca0004500c008003421070040000304852400f1440c1c001112081c2c2c00043c0254001c00900c02000c44080480b03e50503810b00d80b0a0350381e55180e4080312202d026070466445401a005c0110004282c2c03c1456200c03a0115040ba201d80c8404005440100490721402c0001d402440026214035196001c3c005500c80c1e054058038088003040a48211f90158100c81c126609910310b400034194001e2140d94420b0b80f90b0700400000303003103881d4402c85000501c41d030f03020405641640b8552501c20781020000e03a980d6000b950400c11035800141268040b8041c00703000750380101c00005d0b070405c1406260120b41141042c911982c0c2d40c0144d41200c3c68141800ba4140141c0740c0307000510492250754041c41a0080e903821040c601d044250b0058001b007100f00800b0181808402c5a14011000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 126712455 1250 126711205 126711227
    0x61504080c1908060106021c0305060f010e01020a0803180613050309090606040b0309071505130e04030e06040f05010e0105190c1403160606060201180312020405040f0b120d 76
    0x15110072030100d80108902c0d2109050304100350600070103000107000d5400140d402c50084041a42d00000c0c1e01c5524200d08840c2e0441740c00754400703941d100328100765002d803d120115500620540350150880e4882c42c0144d801552080000c14402c0c9800345d84500502c81d09401c01c0748290b22042507001c035120644c2d00d019015540344284001004100540d43d00c0b41150010410400201c1e228613101c0d01c03032a141c41503881400c003904040804040400d00c80c0c1c0c101c6031041d11807418491498108080310540f640c00038012020300806c00d00824180da034560241c0014900c004403400b590f03040000051010001d20001c2c0d040c00700a1180e40b00303008010700001e08100052401081c0e901080c14800b80f21000302c5000d60290000249580002c0d50f21220140d02600400091010660390b010890072513404030320241c40740710712105040000340300390700c41071146d41042009820240c1350000581111147c40030801c4c81c5540e00400e000d1030a08003100c0840d0200d0a01505501d5152078028040784500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 126713705 1250 126712455 126712459
    0x60c0506060121020d0b1005090405150109090f02070f0b070906030213120f0c15020609070e011203120c03050114030a08030c130e0907050910080c010302070602071a061504080c 78
    0x1081c84900d000c4146d001c3c4450351401400a035400c1c002072000781c199405410124012400c1c40e00094001d0010340c45e40d0302c0b1000603941c0101d21441c00c0e02d01e0004213040c56014030b4603078003001030101007607813907030101002401642c9010541c20620070240c0082000d81c084001e05005208a171b1011042c844400100c401c01040107280700060b01e4440582106aa00102a40e85104011aa002030040450440380c1c4a800b203c0f2240c584c055210ba4401203442610808040c9400521002d02c04409000032507100e410700c02003496074582c50000740e40030703186c5450009507210010008001054074801d80704505902504e0601c1081e03e4028003440000e0100703d00010006080c9540e2003040312800052441078400c0c2c1d128140480f070651160368505c1010321949028000c00d030040c030805100400c032020700d401040d8810000e40150003031740041c0000d90303a43e5030074040c0070f010844020617404204510b4070580b05610b843c4080203555003484407100000743d410f1100780100900010b0079130544c881 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 126714955 1250 126713705 126713707
    0xd0903050c121504080408070b030907090b01110f0c010e10171003050a050106080c0a21030c060518010e030f090402030a18060203090c010e03031c06090204060c050606012102 77
    0x8100006403501882c0000d51000400b8541044240090317100a40103450f07812054135242569025a51784502041d0340c484641e400140d0104407100c807a9000d4400300d00181005041c00211310b0700942410500e422040803a00256190342003581d11603403800c401c035004c49200c407c5a4040030300402460212664208400b21600410030000d081800d2000459100742219560140c618041d4080d00062041580602c02c506080d04185400c95a240548040c07406242030568420816076810015074403c0e01406520003105020440c94000c0b18801e090340301040749480c440b400d03a20308407401c1c505690b02e542c106000c5440c8070400042101d0801c40c0840700544c90b915458201e00080082045810b104d416820700082045003c1e000f55118022480076944521182c000644030016909841075140d0410864111903140103118060400c0b40c0c20380000e901c0da1106104000c0781c1c850b4000a01150050a080d81007241c20020b5a038042420720b0801100403060085078068030351790321480c1005070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 126716205 1250 126714955 126714979
    0xb060102010b04060b07021003050f0a0b0409080a030e0f03210901020d05090d030501120b070f0c200406090e0a0311030f0d090209070c0302060606090f10110d0903050c 74
    0x310075040850071030801003003007011030340e50700b58150940d0142a00300d016202005042548a000b8460340d8480d450304c03d101240e82d0759a1054800a00c00d0f04a01e0750b10039514420766000c170f03155201408529a00351000142c2405000d059440d00c14403000c802d0b17181d4000c100c00300c1d851203200e0080300f04c007210341c01d100c080d52201a000781c06400303421050140c2c80c3c5402c0401104a0000455002007100394504104030390300d50005400c0d4800b520342c0503041901304408a800b1340d02c256129242c0c4e04040c40c01814070130203555649000d90000700e10400d44400d4456025803460300340705120003000c1d00b02c0c0420800c412070040944603c07110f6400307420b01c183d980202c40161024802c6034504681030b40c1c280c0d43c0748101900e92000f02050003099024680c50b000003901140504481c01c141901a0010070b91607450008001031507100001c03042e000300d085a14100180c696051408d030000040e203404032000340e4004224500038035250791400b000040801080800e40c0880c0040c4403c0b0140c6042c07440d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 126717455 1250 126716205 126716207
    0xf06090b1c0507150504080d0305010f120f0803130c062102030615070314041e060c05121b030f300f07050903190303150501080a0905010b031e0d050a05070b0601 71
    0x2c082c0f80e02200c0d1074042c80235410b035090b0749584282c0c144c5405901260000b40c8404074071113400d00c80341c13004280c8411442c035800400c0090010355031140c5841d8100c10300d4043c41c1e03149400e00042d6408400410001180308541140d062500361030101810310442c1585440d000180070352403440001051000300182440600d407044540c5494516610542a50740c0c2d40d0782d0b51005102084009010005070300e690104405116044081d40310340c109004100f128900c40044406074403491200070303424200002600044000d20113418101801c89a582d1124000ca00d0408400507045400e001c3c0c2960500c50807040c5c01002c55580c0142d5010031000c1c7e56a40d1501c01d4032103124034083c940e03052203102031310603407440e104c8003201c2c802e8460350b001d2002129000c00256001c845002e194085120b402c009001031104c1e512000c0820300600021a483d280040403a00304400d07004103162645c2901c1000300e0030308007080801c0e0025001c0c0743c0f11b4900541c024008006006203480100790500740004101c184e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 126718705 1250 126717455 126717457
    0x90c0c08040e0603120c100b03010f061e05030601050a030b060414010b0705010e1b04020d0603020d0b0a0c05030408030a15170703030e190302060d0f06090b1c05071505 74
    0xa80c0d0000295984980311481030b640810200c078060f11030f1240c3c1c0303411811062014169890030140d40c000342620078007100414064000360110a40643d44e6482c0e9800400340c07401644020100f02e0030036254092a181c0401c21802c0b20b030440f90096100800421a80c2c8582a21408a980140080d82240c03030f101c0c00030b0050207843d0070900c2174601300c07030020650144440084c20600d1188008215922412004940b940c003080d025042800c02ca80e154001c03810950014060760100d481c00054690301c0780d000030302c180e0a02109a803407040315020011615400d224600c0e082405052160440c900743e551413125100c01000042c045490b00c201440300c00d02124403030b020f030020b80350340946050030103180c5070780b109244010b0700010300e88200403925081c54801c0784080001180c003610118159001d02505c0d41c0500c01410b209070351080c460300608003501c5407001500070b0a0340801c040300d41004100182c402c14031140a1664000302c0c60b030018100180a908448600344002c0c9081c4212809882d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 126719955 1250 126718705 126718727
    0x1409060301030809030d0305091c030e01150303170606030a0e0a0b01060302030a0f0501030804050904051e03070b0a2310050d050d020f060f0403140f0a020705090601030e07090c 78
    0x402008000482082000d40c040c04030490207078100c5062141d585c004805841c0d0544000d99030350080340905041c9000220544000c1c80c240c00d0218580104a664034216990120803010311280c90a09004041d03000420126060340014400228200071000071030600c000740000d0825591000e000460580500440d070700d00b50446200480d82d070b515403001e0080e41c0200d03081d06050345040e009038a0104d061107902d044c8c035000211a030400d404e100a100c14018054415034403803250001c5204515100003c8100902c45000615100c4d441881c7c03840c00c800340a403440103010b08000d03520300344464501e80b1244e1520b00c4d0301c04034900d443c0c803545925030380302a402c00343d0070a050854440600c80005191030032807000f9401c84115140740f0a180c0e4440c034054494240300444a004180420305c40d100b5075652111016499160881f00d862584c7c0980c00605104096000480204182d142503201140d01c40b20030b00302031004401c1d5140030354450000d405541074107a6601c1a0b25090f512940390b00071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 126721205 1250 126719955 126719959
    0x1a060a030f06060905010803040f05060d060e13020108011406090d17040b07020a090b01020d05030601030b06072102010b0f06130f1712071509020d0b011401020f010212071409 77
    0xd601d03406400d18002828403400386000041c1000c00000d08036100204443c100c03000180c0f10441e05092404100b0940d0041480825580c3c40e504081175440ea0401941e0007201554a91202c00c5183d01c009024064140c0c051951440700309040b0324203481e00c80445490603401c40e1080d402d03004901c0c0001c2840c0920389582d01c07000d808140420540d440030000d11026008503281c0c072840340d81c4c5900c40d040d90344203500a40140c0200b1000582c49004002860300300c0700506011440207014800300c1d00e25001080240c5440d10190014803402c450003000d842c0e46400c0388000d000001d0070101080c41701c6101c1105a0180e000010014100005101094085d104252418203115036440c250449002e12008145450207005420302588640900302c481260b48201500c4004140c1410200101419841a80c2003104219042c0008801c41c00242c080c1151005c2c0f23301405400000924000704e01c00400c1c9260b104100050303034000c1040d58607a204c45245000380d00c0070805000ca0320a4015004015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 126722455 1250 126721205 126721223
    0x5060108010603051b0319080409090803161404060c060f02130515030717040201110f060711060408040b0a02030d09050102032e0e09190614131a060a03 67
    0x204003090190000d00407a80988125180c1c40e0901c410b143d500c00900e04883c0d4540c0c42009403044a022070305c807440c903040c005d03010a8105542c52a0510550340714010071620b216001080240b803a103200d00d00c01c181c071310b1440d040c0c1c080030000e00f040c0c0c154840c600640c000d100040449104001e91900f01c8042c4940c011400c0d0f45401209c550090551303e0750286c01c0c4200d250003c48d02d4441c00701020780b44a03001c01d070b59030703d40d036008504c03404901031000e04241e0410104410490303804400b0492100d20402c0040103010b5450b06400c020014580f02d00b202d621303074011a09100109446074180c0f41030303510103030741c0590b11003000390268950701c200e41c1121002c2d800e01c100301080c0001903010310311401d040380c00c04178003a03099006401100194008101c6030381c9105e070305000ba80890940c4941c407401c10400c80c1d2104064005400542c2e05801c812a00d45445100411844003030040268104441b0b05110000e003505c0c0d5a4440820440a41240792445c4540000da2590f0365121036401103402113980 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 126723705 1250 126722455 126722459
    0x1712011a2503030e150a150803070f0204060501020f03030408131805040b0f130303150b0f0309010c051918030803070e0405060114070201080a091b0303020c01051204030e0d050601 79
    0x10640000580c41070707001c04e2803c00981d00b8100d001c00c41d042140c1c080e9401c00c0d0145d0700d100b8400300401e0301c4048000b5074004140c0129811004000030444e03c0d010320030907801c5410074410003083c0c4100b41c00c540c1c1150032501c1c0f0040508400401c0e2900681e01a4030252a1205452284d84503045903204014441222a42029405090344850300581c09000b03a42e4580d1b58081c41c80c0c000d80c4040e2040c42514200c00400c002181c0300782e1104a8032074000d41d40301000c640d910660300041e08001501d2400c4840041448a400d030b01340b10f00324001285e8142242000d11045c003082e00d044081810905108160800420a00c54151048051a400f9203141d03224208960014001d00d45503840306d0145107030102090481d8003c2e0603513a1601c22421160b07151900590045440441c080d201d042c603140c90301d1547c00040c0c0940000c900440300141c000f0096480d5080080c41d140e20342014038180b0404000c5003140301e80f10040940d1160b01400c1059000d005100820b100300c0c0f0165000c1c140c2d014441c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 126724955 1250 126723705 126723757
    0x7090902062a060601020a0c0b070c15020f010f06030b0c0c01020f030a091e0b010b0d15060201090219180504110d0501051603060e01050d050709050109091712011a 72
    0x2d90180d11502c401211120b60741d290059030350342d54100c0003030160134036400100103001030036005101c11445100340d07010302d45c1d83c0c105014820680c4501d00340560401c110340001301e00244940360340700c010140c05005603403854541c0c83d008180074015070200c0c000026000000c42c000d4040f213840528041d40c240c2c0e80c1c5000261040103000b4031008a85590b819460440105080304d101e0115580080c00345001d6464646810403652001190540c01d130740b85e40308202101c804041e40e0008160a40010400750800e10401a85523840b0020850340045882d0034803803c40b2000b6030346412003003500700085540741c9041440080c0b07212080d80e9485101070240904214042d0001801403d150810081842100708154140d410900075421109404d200420042ca400d01003841981d0051060752401c1d40c4425510f01a990260002c0c0c89030382d251140c070420400b002c40d2210b20640fa40100e01d04210800b92041c803009410712400e446000404102d083c172202d06002c850050311300018195a000c00720710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 126726205 1250 126724955 126725017
    0x120904020c0703052b022407030e0a0b0a05220206070309030605040c032003031801091205070f0506040303020a03080402061303030305010306151d07020a060623120709090206 77
    0x100004503a0031050300717a05800d00001d0550000c21003080c444680000300a0043c90070703400141104209038507aa41a80307800b8007800a0b1210030b000d1000c018491030055044801ea440c0070b0030440d038205c44043c00c02524440d584681140c240d0468030266180d0080c101100c14009a030000340410f46000144802c0004c004d1904044034820030082891840d00310b8460b2020014a00d0b4580540040100382d02c1211040c0800909402c14140300320042d8071108ad181c04484184001c58103030780400030500140243da884d24000b032204469031480e142c00c50b83c009440d50054100103060189180101d01103582d00001d072040c0b0090044034505090380c906004028020030311056480f540340403003840520103590810350595070305500d220800c031810b1011034420f41000300804114010502e42e100021030601601e001030040d02201e0801d00b040d03840f9032000c041e800007543d206040701e981d08614024041007940881e049518000382e02e001a00202d085442402c0c280c0031000100014001c4403001c0d44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 126727455 1250 126726205 126726253
    0x30711060a110f21100603062705250903030305060a0b0f03090a0203010203430302090303040302030105010f0315050402030a0b07020321090f120904020c070305 71
    0xc40300c00740c96030201142210554649900140002c102c00c5000c0e4400d00010800c011140a801a240c520340000214501041d50000009a60300404014160b418002c0e074000e041c440201d00fa041a0782020500d02100310428554425110000540d065041d505400b070305c0b044201000302814188070005007540141e00048000c2484c150104401d0b0070908203035420b59400000c114900f8501080080e02600001c09400040c49461156401038901f0b0010358015030442c21614021a25895140e624140081c40d1508590980b101030f0400040d25040c000d0034030241c100142d8942000780482d046110301d82001e5050b60815000280c80c55110b1404405c0703900941113201806008001c81060b28029140030b5819800011803078080354142c40480d4010310140122460f10590001c4524924004400340040780d401c401049010581444008a07040e0044091700d0840200d2500003124092902001c0c002c3d50b000c590741c1b04424080110102a42d000300498039a030b4680044c0222010001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 126728705 1250 126727455 126727487
    0x70609061103040b09060c16080d030506030a020a1e1205030a0305090a030f080705070b0f180c0904080304050102070b0903040503010c0e01020a111c15060806060d0311120307 77
    0x10200740046071404020348041d81d101200b0310786032510030005c201036038101200101c820b004880c114058030001c4d440b000020450701e00642040000b035400070f411984001c03c0a802504038500003001691602d0080d01600c5500540801c40c0d0012014070704080c1d002e070130003010ba05000e08444c9c107210b0001b014040100d001d680c1409136954004400d5202c07070b0000b00040114a141c4002e000c264014030515030321a146181207400d14106440e6500d0160003560754004420801e03051010492110000c203091038440c07801020300d2182c03640414180c0800410107092921f0200c00300341045000c2d0100e8400d540c0000d03d08140342410a4080d8581d8490b01c1030522942c03070030310300b07424482c010441c06980e080160040c20100b0036a44a45014410709805035504c0a05e0010038818601184417a14403540108128911071a14202001c2110307490740104101c0c1d800103040081c2552140c4610322403e6042c606401784074020604d45240942c1d011540c20201c0012081060480e8041c4075690705041c1c13 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 126729955 1250 126728705 126728717
    0x3030c0303220c2d031a0117030d0917120f0105190603050a061a070209090c0d031d0a060503040219150e120a06020405150f070f060e07060906 63
    0x484201040040d2507100810105548404000f1041d0508400c580040c1401c0c0c00e0031390100000c2135205000440d00101c40501d4100d0703c17149610a0360110034050106001213001310684150681d40d280124004030407040e0702c54941c0420009031842d41c00c00803840400c1305031503200e003402c0c212100c00f04992400812001400005136803a001c1e60718120001500c0d1101c40060130400100c000c0d0138005c1186007102c1e200c407070028414004003912034903007420040c01034884034940b04210b01d2030800342550105902c803005c0c5112540d07404618003c4560300d42868401400b00403000b0600140c0c0c080380c02d40c040900c00c400a155501700008511852003162900301701c0c4124004410090010300031180b0300d450751908503082c9401030142d440a24402041901c4440040e09101e1a10302010400c40e9103540206040110307003001a4000540140384142500303110100f29104036900407008058400030041c4100d40c02d0101552001d6284204541980d03500f5490f6100034040340c406104520000340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 126731205 1250 126729955 126729991
    0x3010512010c080403110a0b0901020c10020421020a0b040e010312051806130803040f0618080a0206030c0f0309010c0e1002031903060506040909050111090d02120c03030c0303 77
    0xd040c8648141c1e10a161078800300e80d00c03039842c121654001d58003074031000d12030140747d075000c920072200c002c3c8582c9645c4c0015036034a9072904040e05010941e43c248501c075005010500080072000c1001241400c800d585445038801800000e4009170540d214010f0040c0001d00441c0003c0e00e034005c43c0c141c900840003e04400c0d10000f046801d0321030080c0f10300c11803407004544a1130f45000001081940d01c0000e510407071740e80740d40342c241c1141d00c10391000a104615600810405030002411001d50341c14920500f000c030714000d035068490300f0500b4000e200b2040000041c03042204101500d0100d00e100004645034070304008503038000c2c0440c50742c03800852083d09400c50b03d4036043c01c0d1400c44251583c080c50030440b02040f0320f400022014549400d040d03c812000c550364681a010300010300b18a0b80c00714901429040c060b0031108c00550111342c44104000314101e5807545488080c2701581945e4184200c080d44080c070313080c000c6241149615000010341000ca152001010758020410b00040d0342c40c4c05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 126732455 1250 126731205 126731239
    0x60302041a09060405071206060201050415110f0319050f04020f0307060e09060406170d110d0c03270b21010e0408071703010906140a050312180a0902030105 69
    0xc6000c070860340e0201c0071030001a1542841c3d00139540240a42c18522001001c00d82508252440c0e5001200180e40d14000c200500101d088003040c110600b84007001250701d54000101c85106440c1101100ea0000000c42d4040950041e8656203d6603288200203a04261241540110302620180d108241300b80c403800c8907103800b103207000c101d90242d00da42324025040b400307002400a0007003480307501507950000011015540300d0365a20702a44640a048941c540c0c050241c015070b220020003d040c2e0000b1780610140da0481c003007156858140c02c052412124080c003100c0e40d0319a00c0810403880c003001000085030898140074060300380c03580c440d8180303508403070fa170b8980050024801e001c2e5554680e800305000c2001c0b07100408a40c0e004150804103000b11180e402465442a0b11011803180c0e102c400300308040140915070701c00d038801c51704103026a140c140003e5541403150304d04600e1100005810044064610740810040c80182c81c5128065480c40c2a20081d0002d115450146009c03540541c040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 126733705 1250 126732455 126732491
    0x50a02010c030e0304051e040f0509100b210a0c1403010b0118120812090a0c050306040f0210110601120c060c0c1206020f1209070b0a0206010b090102120d06030204 72
    0x30420040045045c07502e401c2c01c0081c044440c94030800103160601096801d034036540510154485010b40c08903441c10314000c49072030450100f10a042c10361901340055425a904e884011200070300c1d1a08801c80558101c00905012440e01c0040078041c015000141500700000311441c0800308400130055445200015500d41450b0030220380d17001059441400359003030840c004480c1c580900031242c2001804000e03100103080c10784118910340c0c0290988403c0050340350080740a81400c1d006881b440c1041d40d58251141c00c800d800911494920792041c552510aa05298180c08400210740540d40c0d1841d00c080c0c0307414201010780740082840000308219001b8110040c60681c001901041a80f416904041c6064807150884056408000401003c01d0080c0900b40c0c0c05ca01c2403102e18070f07050080e102450301e141d82d8030134844841c043c03000c0310942ea00810054111004420100c0c1d44440000040382007410008041c00951400303c0c1124458105900103401c4d03c2c400d4404011803031108410fa825 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 126734955 1250 126733705 126733721
    0x6090303090b0a050702030304060509091602031803010f09150e01050c032404090615080715080a0905030a050c012d0c230d050a110405011b06020307050a02010c03 72
    0x206804000c100b144800e860003c1040404130301c1c103d42000e00390f500290031588981c5c00400000c1c0c2c04203c0703c4403032500e01c4d51540c01a41c4102064003180d10040081d4590242c2d1041401b913604584090401e40c40a40200304411a90942000003001c6031804185480c0c000c410030f65a289000e03428540090140318032801003101315041411603803001d5203041c0c1501e04c24203214414002c050b026140751618081e00082c24418200881d80a080102c00300002c2c01950100030030f0b0703110300c5d0100f18800f122045000b42100c03a2402802e903540d40d4003580040c1514401c0140345d44400641c0e4078a41e41c2c07140c042e2003083d03081c000038800803020f0f0568601742003000a802c02e45c9070409883d030190100503030011200786a00d00700150031000c0c05003001002440c1505410704103000003448414a03042c0d100e080c0d80410454400c100d54140008040314034026401082e050006040c004021907003210103a4000395449501036541303182100b0001c0803a00f1407440f000240d030a0000000ca1103000e80a0940 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 126736205 1250 126734955 126734957
    0x40e061e0c090108040b19060f1706060907031505030304080a020a1e091d0109122604170f07030306030b07020c090406050703240e010f03110904080f13080706090303 73
    0x181d0301c9545407807400340d001074107d024604210055101903c1d55001d0740004103922030380194001e19200e00c10359012040d020002c4d40d50044070800c801c555401e041d940d00030304280340020b001107014040c005896910f03089079516108c003207400030f86103070300007011026944242c55042d05141d0300e6071441c1b1b030044200c0105100c042d00305414000410705510131001400c24000448104c48440146821600c20020544240c1d003502c141085803900202c10f02c070052404c0351b4640f4084017500300c6100b944800340000745004c26085000c903808045030140c40050100c400e250f0f03522aa42c0c5030180040105220454001c200300001a1001340045a480800f00c0007400c4600c103076940b940d0b100e0003032800900240c02c7c1650740c034540310941c429078a03010b42a00c0a160150486060500700c85808105901411130390601200501c0080c03900c801c94949000b040e01d8415540d1540c7c60442d52900401200059080c8081001082a03d0001107201118646026a012a030b115181141c448420f8003000e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 126737455 1250 126736205 126736217
    0x603020312181e0411040e07170108030c1011040b030a0b040f06080c100320070b010509060a06030902010c020904061b05030705071103070b040e0109060f061b02040e061e0c0901 78
    0x40d03600e00f096040420b04a10101c12149002c1c7c90b4a9100104a0282c0e4941c0c0068180d2503170201e0400080001c502504481005500301025a91107560302c2c8032441c002c1401030b440d01041e00091803901c0980c1c000d08110788000c0d4032480c0400f07404000308410307400944110b05050000f4040800740c031a50f415601c3c0c1401400f000803139281405079405807900b62000701965000b103220703024080c1e21003100030400d500d516a5142043d081c107a03044101a005144150364a01c144643d41d0303100d10004045030384608022800c0107181c00140c6000042490103500b00c0045810441007280b50342c400300815020f921030318a401d42030007044601c1d02044800740c0100b041000b146020982694500f0302d0002c005044428031a211200303170f0401d407c1640207448804411005000050003130003000007a00782c0d8034200c100285400d000511490103040b1040d182e10781c4110b85015521160006e0f803840c81c426040700e445003415021460040580581c80c00c02c0701c83e28021801440030701c0304035002d14005079200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 126738705 1250 126737455 126737509
    0x20f2a0108100e01061d1017090304180e0f061b07060605030a0503030402210703110d0f080c16030b0a230709060f0203120a0f060302031218 62
    0x155040000a0612481c0507050b100c0024202c1d101d1038450301a081c1660f5007269a000000c9a95025041800d45486940c0c031050032404144d126649184181045402e10107585803044d1640c01e600c525000f03080403c160240b03210202c0c40c00d40241c502d80c44940100c5404a50840d04035407268000e5a9214284000384100410011883c0142000034014000001c0d1a41c0c0e600c0028944580740d501210260001300802041d0310382840c800c04c104480003032455480110b1040c40c2d8881440e0b010060007800503050100301e603201c40202186231540030400042104483c1820381003038001070006c03c0c0b50f00c030303013001c02c031000b42240c240c10b0807030382d000340c8084054481502c1840681424403040039000380c514a40c46007120082c1c0617a020300030548941c1c22103400c14030014841e40080440d42c003994001c114524000955182c0e059000920090000b4141d0b101d90002c00030b070880358000b03075152080809a00c0c2c1a407680b40281111850341141000003803540080c0700a400c21102100751100f144001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 126739955 1250 126738705 126738707
    0x90209030d03020904020c01051801060617061003091203091e020a03260d0c09060305040803130507050a0602030405130c020607030b060d0203040f0308060102010218011803060c020f2a01 82
    0xc4c00c8500c00c0244003500b042220b521031403c60360308882c044010700c4504e644060350340d028407882025100902d00040c104500170b00c800c281c0c0e0b1028204134001c074100300c1c2d8400c0b05031007035005e448060b5110604100d202c044a038020040d1a80340c000b5a0944030031901d10503140c01041c003d1450b10380c06440251800d1a540341d00341602982203915503120190b04034040c02904c914000c0c4440e01d640000040c10760244400103060900a8101100341454030080c0400310b640071083e6984074003240c010203a202d60707924000e414200141c1c00540c00c1050100080b40294020026100b900c9054070840480144020008180d4580400820240c1c2083c80410746c080c0c400d40060700101809001c2c46d2400031001004004c0341d0081b5816101083da100040003090740c080340094200300c09100035410305502001e040d8280007040201e60500c109c0d0000612112a00941c200c02541c100c41d04000d0345c501c600e400303074446801010b4a840360158510110b4605001d0384840b1010041c120444512a95200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 126741205 1250 126739955 126739957
    0x90105130207051005090709050105090c03041209080105090a060e0607050301061d031002041d16050a0201140a0e100c08070e04090c083d110403050a0b0709090209030d0302 76
    0x5003e840c0341c003c0d043d82d904021030501510b030003000050010f2007028070f008030400841740180c11035445604d6403030500276120b1010098a4020380c0251100148400c541401c0c0c0c0d60311140c0e804800107500300401c00516000c04140a51a14000c4c3c0050106000341c0060903181d0000704e91542c00714100780300512208d4032030400902000101007000700c6030402e92000034501345140c2484c1c1394541d0005418084081d00c412000025034200c41e00b407001e400d0003801ca0b14140e0745a280c50301000000302c0d50206542c400d422040c2c0740c0310461969001814072155001c0a40860040000584102d0380010040c400c544120300d070042c0150f45055503501c03070160407581d070003c40c036080ea8040c2d110014000440d000c0b11008000300201c0c1c004143c0307050f8400e00c6001d8166141e403010186c8600b21094414180f00c82e010341071050080500145001c60b02c8101065400384d0741000d070440c403640440c402000810040039001d81400d844030010990307036000490a81c85034411458260b04004c0020003554000c0d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 126742455 1250 126741205 126741217
    0x10030b030a0f06020a2a030f020109060e030403020a1a07020910030212150703090206121b030106020a020103050f15131d1f0507140d090602070f05010b0901051302 72
    0x101074034951921a00c404218609100d02980c3c031590020780c0c61405a04401090015100c60722031081d490309420341c6c0d903850248048080e007840048005500c20620039800104525031000702002202c2c03080c00c40a503203070041e0108900682c16020085a14103000014448100c00491580d01c1d1a00030f0f400d00080d1030b00500004905000c0c4c00000c00143d4a4401e81c4a0400c5a980100f0482096004075280b10300c02401000038186001d445401503100c200855448030101102030110752960310042410340c80c043c203034452f0f0744004070020540b80d0707002c101000c9141c000d0348c0034021a00c443c050301d407094000b078482000d0949220075040650505001049056007040c1d03000410000304410001046050044481d4079002040413016032155451000c3d14550024020409407030483d002614025001807120340030400418103101c108515000500b0043d4400c4084d9142c01040c58058210001d00804541075402c042540c1c995082c04401c42d8120760004142100072168204640c000354040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 126743705 1250 126742455 126742459
    0x90e060402032703091005070c0609290c07030305041a090a091e06060207031e0b0c0310030602040b0d0b0904031b0c08070605040312020313030201050d02070b0103030801080c010e10030b 82
    0x502100405686d0700701d9801d40d405640e00c0c0c4c543c2d0b0b200585800b40c000030458000106002110700c0c10301064100c031400b0410b148801c642d502a079020000f81480302d0003403c1c143c208501c22644003008055001020700111043c0c854000c01d942c80c4501214101d000394858035800441000041001502c1a00003440c020440903050301d41c4c402c1072841c07205542158004002581c000c5100b0010040621003000c5141001d03140400c400c00c640d660311084c014040d03d440c01212000c00030413651900c14001c0d40095600420440d0b40720790f9001c440120790082440e050300b4610300b21a1260600748003010b14420f5034981d0340ca5694603805200005100240745058900e0654400003080000302000303580003400c01c07912425296490b40c680700e8402000c0980440442d00140151341c0c00d0f580351050202521b90908005441d0351000141c0350080c060400040c21300b07038038440000141074101051505981e84003085d030b004802884019a03251000300d25054000d6103038980075200c01d10a40c410001c00c480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126744955 1250 126743705 126743707
    0x21030302120103080c120306100305100801140a050114010207030204020a090e0a06080c06040e160c050d08060f0604120807060209030a0809011206120303091110090e060402032703 79
    0x5402030712101940260004c0302c044000050460119008002d0044960303c0c46212514619011003c20740e00b0007002902014141c41e0303404940e0305120544044007510300d1310020080c0302c890b42c02300000c1250540706403003c145040000306120004142d14103e1080c10b800405041c0e140d030f400e0200951114400a007004270444011524180c098600c60180040c94000308a26051840300f609141c8a100380c203210b070004010420803003510b1450140d101d510600302a41811820b142943c80700d550110042c418041d0340d44c540c5050781c00c8107401e402654103403000045c1000e00300c2030000c944642c1c0106980550f07004c0c0442c0010351100000d0143d544600f078007500780300500021a24100c0da00004840500011604222a580c040c030500c106040c0320109101441c034080440400c0e101c282c4001d03003015182c05080082c4801111094a5000c0261002401c41c40b07080e001049094140642820980c020f008102c8525140c02600e002c1c20794503400c0075106400d6510700806000802401000d404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 126746205 1250 126744955 126744967
    0x1008040b060f12010605030c060c060a0e0a0f0b0712060605040b130902030906040b0a060509041b3503040f05010c0314030106050c06060103050103031d1f030c02070f21030302 77
    0xc400d040011150010070000c03868908006c101428581191029030055405000041c010384000424a030010343c45440010021307141ca034020b040203039019000e0111010b0220310302c200484800300d18401e016594030300104010303240901341641d41500c00c50001490074031040c894404600b0042030a4001400c10042080d0b40c4c01c503070b0007682c004449031100380d001217003004203026000743d08a9002032158401c102540c1840b00082c11102e0140000d880410050400c9642c0c1c4480300c00c6030f020f040d0100d0313001c0c582c2ca1101c21000c058000640c0c03002c842200d0400c400448103001003946d040e5450407282c09203840c289030046a40707590750701c000e60402c10102d80d96030410515600840c040d10782550355503641d82050141601d484030140c82c80e81011305d031030010404250302c1082c141c1d84030114100080700d81c01d03003000a00c1c2410300d03003c00c07907407441000c03e104405ca401d5480901c1546058080d034149a540e5480668a41518403601c200400c0840405030b014070351811090441c2d1283c10b00500f400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 126747455 1250 126746205 126746209
    0x161805130507020f0307050304121412030108010b040e1203040203100608060a0e0a0506010b09040f1a0301060f030809130e16380702060909040305030103060b1008040b060f 76
    0x4100c040c0400c0e84165107100303000c165a418050000d0080c0c0202c01503281c00c0250fa81e00d5076a22031031043e00d41420011215104003c100d40340000705250050480d011001603581483c0241c0c03003840f45088039031130000b02546506090240c145403010600207040071b41600302c1e00b58035560008008070f0b41401039040000c1e10100301c0c4a50000b4100300300051030f031072a19400c040112001c001820455500500348000003c00004059043d44c4d0202c2003940c45060700008a000303882421500c0740341a05210305090615a10045c0e50000402100240812641c9540715072a807a01400080c0400700100320b1081141421f000710804602008000a90481c400c00745c14200750b214038a1940c1151110020000c2c0e0b5440b0f441501a4484001240740e003030f20401900030741c8200210404840c01c0040740840a40d510201545d07500500688a50202d141c0391400030700e90750017400100c0e2058500072100301c042c1400000c10032080d5094079440300ea5180c0782c8a40e5403e00c002444580c3c04850f4480d403121a1b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 126748705 1250 126747455 126747469
    0x2090a080a05150108100c0203040f08060a060b0403020102060f0709030f080703080703050601050403060b060903010221070507080d092604090509030309030403170d29010305161805 80
    0x8215600c058106001e262900c141001900c001c0c90700161219001480b54040100304c101c10940024000103148507851411380c01c5001da54400b06007a04031440001d040d001c00b0a845100c3c5400c1031081210b0b42d2280c4a51290340503600000e40181d1000b400a80a807403800200e64008049003444086140d60b41d40305110b010308040c089900050104940c41003640103049650080d05604007405285450400205030380254400a40b486441d8035406c0c5e00345e20340500b22034010201400a40d03542000920070701c4602210b402c900c94500c901301c0010521881601a22516070344100c030b1038a81b8951364101c80c0540000002078a0740e440920307002d08103600300c8103d21200228117411549403490684820304844000300b14000c0758204104004001070040201c800340c035030040c422040140c0c1c0f040800401c2c0582481d5030051454040d41695007604403040b68221232000f000340030380403400340c0110160b41095441c0c00401c0703861101000101d000e07509144000c40d80200c01010580c0d04ca00040803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 126749955 1250 126748705 126748709
    0xb0a0c02150703030b0d02100c0606030b07020a020102070b0a0e0909011803020d09050d1e08040902041e15090306020906070b1e011d070f1b05060702070501030b0a030602090402090a 80
    0x18100c0016032400b0943c04d03008010114400b2500801c0807a410f030082400014400404420041120300074401c00c1030b190305c55000b07507811180918852070403100280d5104102d01042c0d001d403144800004507601103008541c00d100e183da5541c0c9031402c0f00d2040c000400d1001e00088030390354880320031580050181d0b40512025000740d0080140d000e040307901038244442e680019010305030003054480850400f0083c2d003910020315902c00f08603801400c1c1040c81d806240c20460035280006000076944604c0c540690858918025030560b90b542c4104504030301b1003000b110000300c1d140000801c0030805560280ca4040300c05410140350072f015941e59403917900c0485082d6034640c0240c903001c06400940c3c04c110701401802110400006090a2090700c01800405030380030403030303d80194070384a072241074000c40d4882c1c44403009506002c00c1ca440707a201d41c3c040b9140401486200f4001406600c03a000340181000d000d403c40c0304050950f207840000e0b5002c1c41c16160800d070200415070f001d8844141c6000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 126751205 1250 126749955 126749989
    0x30f0702060c0607030c200a0f1b0608010302030601091434080108060601030b010c1101090b12041b0f030209060402090d05030408010506031b010c11150405130c020303010b0a0c02 79
    0x9200004008081c04002080307840604007684070100c0201d24000040122300d26412110400c8644041d2401c400b80150f9941c10900701c0c814288001032541d000300604c2c3c1a01d100300e0984035070380c2c0c9805468085840d01074502c24000c4032040851544003042c402d85075481c510140c450381c2081d10108002c0e90020390303804079000036110801080341d582e050100c0764102c1c0c002d203018018141600002400340c800b020010b028840b000500c040140c0c007400745207004040b07401c80d00340c4a60240d101402000c608580c00c0e94601100d50b09a8440d0004042e50004d0b90b885139840c0b42014115020310845074401000c143d08907600b045060040d60f0b6049501d800340b440398000710796071130403c1055400d44001030111750003a172090101d2031000c0c0d8106101c0ea00c844003860710320610f51050a0150142c84188006034000d6a8880c901a50100c3c040c000c2c000c0d40d00541e031030705420a44000d4981115002062603005803c20310040c4200803501c001001140c940d40f40c1307401d2900558000070074180b61854294 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 126752455 1250 126751205 126751211
    0xc0312020f01050c07020904030e2e11031318020702090c1809040201140703050d020c0d091a09062104060b010306050307030818130c0519080f04020112110c07140a08030f0702060c060703 82
    0x3003200f4ce07000006030400c0c99040007460408191902580440100d400340c25411560200d5490452145078161800355400510ba0707080e9081c43d89009501e90b03c11458540c031190303206880082810320443c01402240d042c0c0d80d03041441c44106c2d08210715080108110b0800004000c4422162000e0015208410885000d1b10254155050240c5590b507070fa80003407460b60910548840707002e0840c01380c5100400940740140c0d00c0398400030001c3d901240400910440490101744010302095a08c401a170340000e0303c040240d42c0c0c4500c2016a00c141d184801003003000104000c02050008107807668541201030403140c4484180f000c80c006841044441070001440072031103101ca6484414542088001c0d42421180b50074040420b04040c02c0091000e030511407081a08402d40c01c480d8058a041001c0b5607520746c6810180b1078403a150402841541c09500d034402460000b850200282011135281070011480c0003540c410f03001454000381c0c002eaa200740d06200d00010921f06000c003500c0351045503000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 126753705 1250 126752455 126752539
    0x302010e0d17030f070809100b0d02031b041104030209060d1e03120b040e0d030b13060e010e090c030303070f020c060703052a03040e040c0312020f01050c07020904030e 74
    0xc100300100045c81c1d141000300440078844030300d9010460104403001500301083d15412100890a20403076220000c0d05481504210440304058280c440c0d9000b004840a11940e001000800924040c2d400041e5001c00c40798045000c42c0340c81c5480324038242c4103c100c442141c0070241081c0e81e00d0000785060f0003195041401da584401b0b0b92240a404850880b402c210080101000360354030301c0c3c0c040c031070010316980b005003c020f5a00c204136084034814142061080940302d05941410280a1080149548a4001081c51124003007010156210064015811a55400c40440f603403800b102c001419401a08810482d68454400a1000d01e000f43c5070145d13a05a000d48150300322042c00c075100c100317851411640014907000320865040740c218000704801504c07503040031a4003030001e6000800004009103070300082900414018402c1e10030308000c10081d910650003000901c01c0c050300a41c4103840034001400207004040c3c80c0c40201e07018106140c0182c01d800e62450b81d01d01054080741c000c526001c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 126754955 1250 126753705 126753721
    0x614091005011a1b01020d061a04290705151e0f010603150803070c0602060c03011409090c030a0b011e080606061b0a0b01030303050a05060a0302010e0d1703 69
    0x145010300034500c03810400c640c50181401d0315490b4408030b030b6a08240000e40075109080240c0e0b40b1040007001c000855541115902c1c2c103000b0803082c4200500040410101c800441c800340540b421a024402d40c107480e41d00c0800340d2010240b003c00c0304078402c0000d001da140864010000909070071800000300c001801d01c40341d41070000060340705d017075030421840d0704000b18117900400d07003070455005050125a011416146115151807608071200d1484041080b0040c40341e0701000c24101c0c1c981e0f40039a0324680752169581040d210034000c800340e0214201c1081c0a5007026054603a0004107142a038803d10400340003c0d007000860301c1d0070386006081d24014002d008800d0381c0040000c3c03040c500c01c4016494940d0b095125240105564422007020451045441100064980160a220070b80384c100000780b800e115901020f0206400107440e0400203590a0010b12a043c000e2000411003143c07146140d00440703042c1d0300300c101540c01c0311000c0f903000c0025241540e110282e0081c81d050903248d1800b050703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 126756205 1250 126754955 126754963
    0x50a0305280c02060a020708030f1201051002030f07020406090f06180b1c1b06051e2d040b12011703091f05070c0e040507090e15090109061409 63
    0x21640d100c000328541ca51096040750611005660541d18141c07101405101607040403501d50054400c3e010000e10030155a07a820000c00004400040005c42e0742d88030414010500d0480b000d440169004111104110103500003412403248002c0c0007296090f240c2d900b413815103200c004a090595194a000d00008418a04e8010303e00507034501045000c10348400036140d0b142a1280b4200d0280b0500c001e024030031072505030100a100d02940b00300c20f50761000b00610f15440300641c070003d01c858075001c0001411a50441d2350040c040d411f80c0c038550312903100c800c0c401c0145aa4001c0b41240c204000510551501c015000c4c0e40740380907001c2003641c0341441e010071030400c0c858007242a80040001410f0396540c080f035440d00e407010180122000620005c19541ca10070030078083e105615007100040d103000c0b00da02682c417603803080041d2115207580d00c0e01c5e0f80c141c07050811241543c1e0406070701c01003e8075503142c0f03040e480382c101c00000c100407101e9101d8a080380c0c07010a00d0b541c516400307005c006522600308 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 126757455 1250 126756205 126756247
    0x1215240a080c0909061009020310050301020a35070f0e03120a02100b03030406050c030d0510050f01022a04090609030503060a140a230301110405040c03151202010c050a0305 76
    0x15000e0700c042d280c51500001c3d41b6184e4040c04003041d13404000700b0800000c031600b40e0094a409002150f403504000002380000c4200e41c40070100124510041c804d00400c2c00d003606500201041070101501d0384401540c02d200d01d0640f0504000b4404010040c6680c01c00001310ba1149000500380d5480c00004006c4c2040c15030100c03815001d05112101c0c0d841e407400003c1b03908480030f40c40c3c0140c440302c117014464218418100c1030501d150400741400b0913828818105022650100c41806140305107030b006a07120828601800c4a00315080720038511604602001c075400c4d60001c0002644034071503983d4904580c0a82001c0e0b0010300f01104000150405c22031030005000e03100e0310800c01d41410300014400c01100d000c1d9a080600d04034510300040d02000020078500d030018000e1121f140320080c03c511070381091080c0b0f88168104109022045d01034031840d808000c400d0803804245d070a0404d400d801e075110000403410480c098440e08003141090284264240c400d560f0b140d41c48002400000305050300d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 126758705 1250 126757455 126757471
    0x10f050109080307170706142e060e06040801020301031203230403030c050903030703020d02010c03020a170601020a0510050403090e1311040f02181215240a080c09 72
    0x1c14001d001e5038800005448038598401855810f006051101144901654500810302400c0c40c140c101c1410780198054416000b07030310a040c10348401d61400e46140c10f000902440c090a11400b40712843c0b1541261409000183c08030b8030303056840d40d40608982c8268401e8400808000485c101c50760300d030242d01889890052503429480000c18020304503030000d0002070900d9640c1c100000c1076401396082d0792004c4002402d40f5160041410042c0d00d0b003c80f00c8282c070041d40f074090720601c12402842580c0d2280312070354501201c1c1c0320a02e06641d4200010300014194403c02070080c001070410444110141950000841c8500740380c50060b0048805400407a1078002d01d80400445184000707844000c00d0f04035001999650382980400c008100d06140c0c200311900006119a10007003581604010f40c8003500c102c0400031f008480c0d2919100d49080c9030000044200100d1940410743d500c0c01c0a50002d00041c5003500782420010304521856030008015411a0304509031514007084042e0740710243d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 126759955 1250 126758705 126758717
    0x506090c191101060302040c11010c050c070e04110405090d0905060301031703070c0813030c0b0f12070203130e060315090309130b06030126031e0a030b100305010f0501 74
    0x20340e10009050348000c0d204007080041003100002d811800750030090080d50042c0c02000452101100100107825003040842150300301300d00c0e1203106204100319282d08032a00040d00384c09051800d17403014400003610940e0030800d03542e841d11179030b40c0c0e5200301802020500c0042ca03800443c1800600300403500c0d40300510510051004001280741e00c2410580b910f09015182ea99a55009080e5000e0020b01800b814070540170070102c203100240c251000540b40220811400c20707907103402a0348240f1800f0712600b40000240b1402030700d0700c1140990303600150103005a90030001c102e42d1314840301503a1743c0104210301d400010310074ac0e4101032014281b5102444010b02c0513290848000d5030340d1041000440c000c038441003600003048080d0f4400944c1180c02400d040d50303540e45000b0040340c00c00e40e542448042034555051039982c10000215020070215214440201c0d00450510b442ba4204c003510b4028543c98102c0d0004940d500729441d10303900301944001625505240c07070000962855000305050100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 126761205 1250 126759955 126759967
    0x10b030103021f0210090317040b0a0e0c0d080a140a021c11060408220e0106170114010c0c03060f051503010b060d020a1b05030909100302010e240703030506090c 71
    0x290111703101394034104040000c03590380080d14080351020541c2003d5440c1d10014001e00007048181031304039001311022002031099600d0b020701c00e07454403170f04a00d240d4000e0400403070782d00058813030f40540310010705400c0070b400d0700ba00a0080103159110720840001a00a08401001e05c00d1515072000564604d15212403203040d5080c9141d513820010744050050074000c101e082002100003e80d42d013444800c502940c20f43c2d501c00c144581c0403c203000b2280440c00c3c03d402c28801d00110b04499040720f004200c50420600440c00650762585285000d584040905401001040303c502415026040700f0000081070b182035401c0c81c0c50400070603103491191341072584a03e516500c140c103595045040c10001640e0f107603070311400c2d1850710115804125008042c0f5825040c85004070143c80e02020603948000560b03035525204e801d0780a9400024081007080d8410403071030070010382001b040220003441180d40c10680c0384900064200c800c0840c000ba840f00c04200460600c0071015400c01243c02c005802c0130 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 126762455 1250 126761205 126761207
    0x3050a06030f02012102040618060f020303071b0f03020a030908160e090c1005121f091808031003060f0905030304080c12070c080105070e0109150207090203010b030103021f 76
    0x720440103810000030b15508082140e01065003817041c0c5010314215a1940d65143c0544804032622000001048500e000a80b150040d0303012003044034568040e41c0395a0b90300405640e0810000f0789000c0c0d43c01038101100000d090040030048460085d0014525100e003071400900b480c000c3c1d04403026640194152061030402c1e699440e0580308050340000c055550001043d00e84000c46001a910103101d441c201c0040740c1050040040c140c0c5095800640d50390400601181c00b000c02c40c07104000342c52003007000340110304e13806590503255544581a11000c0e6440d0005076410698458241414180007001008001d106e10841d12041c0d00e014490045241ca0762912404020000790080f94002410059060240003415190211000f8180c075000d081c10841d048105074055440c0d15882c0001142599000d001d86400002e0140d40340300d52141003180c2c60b100010080501030942c0724291000c0380b00a400d00141d03003e000254060743d180d61550040012240c801050498000d00c2864004045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 126763705 1250 126762455 126762473
    0xc030319030902060a030605100504030c060c03110601180c030603050316020a0b030c0a030606080f0606252006070b010509071202070f060b010f021e070803040306090303050a0603 79
    0x40014912100a1600c0194260301624020100a510800020700c4004054141d400380043d5042651644100307440204140c0c0c0794816808050049021190100302d0316100e07034540696184640307008843c1070b04002040d4580b501c20380202b2001c252508101e0343c0c0d041030303104422900e0500d03e002e00101c1d103180c0b100c907203034070a0907051000d4070100c0321542c040d900d914030114000d00c20300400995a1900c0c0c0c01810b01034100b8600000000d05103400050302a10513510310380100e000d040401d21a481354000c00509034010700c000880300892521500441d4000c11580e640c803030040300c40d0442000787d000001e04e00120441c030b5a00c00c65091100c0c4010034194480c25056920589218486845041083e140c01c41c48021440c0002d000250150403c9040010030900e28031503001400f045d03071094015110441c0300e450203001a84030f1041c10650280079003104610075860301c180c03071035241c5540c86181503900503002500c1c1a510b8400c0d55040560611549a200d24042c404010b8241182e50311580 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 126764955 1250 126763705 126763717
    0x1121505040f021518100e0d060504021f0816110a030e040609020f0a0c03020a0804030602121b0a0302091c081e07030e06030405100e01060302030f0a0f0b22060209030f0c0303 77
    0x100c402c000c84031b44403402807075400610007008014101480c40e514050002c1c0c142101c4c100d01a124071064121040309070b405240014034140c6945041e030f0f980c85900701c41c00c2a200354420411042c2c407040c60f21600c0c107011110005000703130703111010800d2180601064480550002003042c0c4100300140d40100070100b52410749400c0d01d40790b05402200d0408034682800ca4a014005c5400050004108075141c0e0080c05c9a881441c1e081317103160f4900c0b010401640850111104420b8108001e100b2503109900500120320000c0c113003603001009050500c00d0010f00e2500f100e0104000446152003039064004084440500c40f10500c0c03d406560700400b610300045d140790040402101103400c10805010741442c035416400d00b00800100240c480d8003038140ca02c0283e0181c0602901283e0384400843c40a091070341100c0000c1c0494002c1d600c1c0d205010008140825114400d920703040020521004a0390040c0181d41c0036032541c012800701824800d4030480e00350603a2100c0810542914084140c40c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 126766205 1250 126764955 126764959
    0x30b0c0307050f03010f090b0405190f09080a0503091506031507030e0109031805010e0d140708121b03030f040611040b0415020c0d0b01121505040f021518 68
    0x900c0c0d46541c042070b5194025100004003000020001203810040003144108803000003d00380325400003a0184002c0f41c000b6a034001e070801201d01c103041c000c10590401d008800801600194105844e1120000d9820000703e01c000104004140051480100251960001c0310305040e409414900d001a03a281c0d14108a099914001e40004641e640660b1040d06c456550070f0090281c05440e14004001415070020b03001d058501030008641d07544620780308584840b018121004800d69078503015004240c40d82050800e215407800410b18110900000711a0030307500040d5030f180c03840152080e2005118002c900860381c000d0040107071048a01c0d40481e080ba820150002d420410105509510320a54110040e055400240015244006e0400c10031500e0301d9803d4914082900041000c404580140070f00018a02c0b00188400c144445500035014401c013244e0340580e0000c0080230644004903000d580ba40c0740c000083c03040d42010601310300030550720345001c0d207840d00740c40c1794040000d01103007014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 126767455 1250 126766205 126766207
    0x1201061403070810050c1908041b08060c0f0f04060302030a0b09040305030a050907050d0b1006050c0a150617060402040e010e0a0b0c0c07080d1e08010506030a09060509030403030809030301030b0c 86
    0x21401900541201e1007010700941088051f44090340280035084d041e01c003107500e040b0145500d0302c020324441c00001070300c0400700500029140c500c01b0000c29008000b00b40c030700b08410015100d0703009440d40280b0080a854601503280e03d001000c0308111240c180c4941e024000c8031003007000080d4008112507004040020000d403030303103401c1c840b146000b103140c010039013000c0e0b04002c610a000346481038510a508040300f0025850f21044100c40b039009500017000d041d0f009203a0400003035006038404106003410701c0c000851030780e5200a008124555460100035800c244140001c2d410300340111038106050380004d0000c0c0344041d082564950340c141c401707444105284c012039030044003107003252440404181107a0100d61031784805a142c1c0c1c0c28808600c003140800b07848280010155040b120081055140c00805a2a020501407039910042000001c0c90b0b40c1c0c0b207070400140484c8201d0340148200c1000710f8550b400c61034090440103010700110055441480104000341030b491102c1c0d40442038044407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 126768705 1250 126767455 126767461
    0x3060e010c090e10081209130b01050403021011010216020108060a061e1707080f0f01060c030302030c0705010e0303062701051507062306010507110f060702120106140307081005 78
    0x101c0c00b60398083c4c22003003c40c00340b0355140c0c1b10145c03c031003c0c1256980442d42402044064000ca104a034060f0920302c6c00710b54180402c0000d840c14031181e4007031050500b054482244001440d81c02c9074841900d184004614460fa40e0940d680103914540c040c000741d9a032000382d410854060108003038403e1590b81d03c820314046610703c87c4a24158a48100402e00e0b440d0f07a81014203000d4040442150380030f008803a00e0000500c81505646403504a49994a500b40c028030305480407800396000825401d0365520400510000960902c40c0d06c1d01a040c010165031203007400c404020100d40049030807000e03150089559003443c4050740e074050454000b21100005650034000345007840c000c40e0400b50806140141c86404401050b6048040c1007801c55401c00c1030b901c0c80300644440c01030480142000d13440c4015169a03090140364150342082c0104400d040441c1540054a603424070340240403070f0b9440c0e40041012040030080310003211030450141103c5401e01c60300680e80c01089180c10f480310384940c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 126769955 1250 126768705 126768721
    0xd060504050408040305010b09160302031803070c0609050409020307050f030a02150a0306090e0c010305061f03020405030606040b15091305040f1a060a1206141003060e010c090e 78
    0x40100180009442440039160500b00407003140c200d0b10095915500702050318501d840c1c04440e951040c51041c0c5040e4002480a404a0003900700420040302c1250440000c1d01000f02080a489102d1003101041c075000d05012005000c04140e50100b80183d0501d880000140e90108546003920030942e040e25041c0210380c002884d0010720b40000e50085010601117076501404001800d55032007640b420b210940d9201e482030126100100e4200c159049201c120085611036000990801c000a10701c009044403a140e100802418811103000b1950004041015040500c180d552205049038208140180380e800b08100c0d1204118040c402c2d00005142001507481c90800794101c1c6803000f0410513803400b45045016035030520426240e84030840300b041d5403020100e030098403458000c0c02c2950b14620b00111140c0b43c90b0060300c112081601c4080c000c031382040f2107140500c02c14003491500190791a5081c2601110501403201c40b480e4103200444d0811030700166004101c40e1190b082c200c950b510806 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 126771205 1250 126769955 126769961
    0xc0405010507080d02040f0f08070303050904020c1c02010b091602070b0a0c05070b030609060a030203070b0903011107030201050f070f1b03031805030a090503070e01030f02120f060103060e010c0905060d 89
    0x10803044154408034011900e07d00303000d0282c0565614a0100750340b29220b1012642d81c1500c1e2100800041080040da090f508090300a4150030403910304662800700781c0801c4158442044a514005079550440c05041d840e000c440705030800348121840c508095060720003900e88903140030b0701d0030000c0d000448000e00ca106400342e040b03068110080d180701984501c1070303409550090303803128812051003001c9141460904031040c03c8941c000c0040807524644001d92160303820489105a141d541d0398421085000f2240007000524460390001480c1d1508242c00024001701400240400c0260500e09d580e203a0442801e01c2c44004221088404035190310b021006002000080074410404000340d104001000029045400f001c0e2108868591aa818147d031041c5a00c01c02150500d20001000418425841d4a0404e4000b402602500980207401403a01c00501403000c0c1039881391004005200303582c4070743c8910801880c0203104000c4215801802000075000d9a44a1070000810210725000c0d0b038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 126772455 1250 126771205 126771217
    0x161407080a0b01030605010602030c1b01090e0112030201050705032a0c0a060b0906060c0604020d020d02030706090602150112170c1204031509030530090102090f03060c040501050708 80
    0x39045030410285441c0c80003460744203120841d5050304200011848600200a4507550030700c2500501014411104100c40030311454a8a0f040c0a4010408102e01070141283c9020305030b205544031008200e0b1800034211000106079604000091050180c44405140b50f285032090040740c10b21030444401e10140c4512400d40080d01c0c0384035800e6040c040190541003130b0b494440844140f9059500e003000e11040780b040002d5159250032500000d00107290168a0110180c005800c2c05079201d044c0e80480e241500c3e6410120110303d000c0410824240e04001c1200b0f101840c025046840d4074081c40b001c41c1026418004220300c4260b021b12207071400c0350007a1030551001c0001c40d0000340038401400324960142c0001e8410740c141002c4509840b0003406001049541552100d01e840e403484042d01450100b840101c42c41100c030300035032120340b01c031852203070080c07410a0005a41c3d400c08820881e505020031150740c0680c2041c400c01921010000c1036034110f6400f030a1480c0c1d141070a10701911284144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 126773705 1250 126772455 126772469
    0x10180212070e010306050307061202030a060b0c0303010812070f03030506040b281d1f030204060f090506100806010e030c04110301061d030721300302161407 69
    0x1032800c006103141d00c0301c0c00c0c2c440e8060a8808001031a1031301705064403441140941004142c100c4000da4980308594011a0310082c410380004d8440e8540384200300b40d501c41044a2403d500100060182c080b05025050301c2e1011904075901d04680e554818100d0100d8500150500d556800019075648540d00441c110f408001d0500e4005000c641407581544c1c1c0c80c41e0001241050600c01003002e50f1403110f001808c102c0c151407102a42e40300300403001040035121440036444001f000000058550f80142c0001e84488054045c01c03504024480c803c940f401428184641c0b5000c3e00c00c4401604a800785800000a02e00f9000460391500030903d454000e4404a4200e4680201c4010080c11107000e14161b40455440d10100244400c0143c0d48007800055a903045d000413008204d0040f0f070080341c403030041c950081082000b2054455058866400000c003003841e0061200351201c2c141140d21041102d82402d00b14109103038520603202c081d02d0044001d00d0b244071500d15a4422034200305c0741c030040c203003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 126774955 1250 126773705 126773737
    0x20a0510050603100509010203011701182904030818010b0f060f0c060f0105090f071b0f0b0a06031101090308030606090d02030708011506030c050909150d06090218101802 75
    0x106e00c0c001d5000358030900c650200142c10190540308220f040c001c000e03202c0182030151402da04a500d40c552001c440d851409200d00010b1f5040b160460100b1042e071149000342c540760b206140100005180072034036030201189925140d0303070f6502d035510030801148210301a60125200e0f1800c49207040c0500c9990407440c22031056034104103000d1603407011913041e25002d5521700310300d85803a5802611810242d51540118454403d40c00f10b992031429400d1001c1c0c011010b0450308015078880001c24a07041c0d846a4105da254141481480300280b00f800307500c1420f00c0c21140003490b5880c1d02041d400041d1200b403148c83e0018100c01140c5e2032a0f03152040c1c0e6002025a07000726900e40b030103070003070192074501b541c01061164000340d41400307031040035000c0189850307091902c6280010024400070080212100c840b0b003203056401d80d1124110380040340d1046000180d044c00b10300400510030243d2425102030345604040083c1011005060310480d44e00a94141c2405030a80912020b400394001d81545198 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 126776205 1250 126774955 126774961
    0x509101d0d052104030c0804090b09060303030c040902070f0206130e0f0c120a0e07140909071208250b0117070b030c090a0f0b0c0607020a05100506031005 68
    0x200c00a012000040d10040392440d010003102078807140034020100c4500002054483c0301d0303400c40b000c15a4031900c04c0c07030700c3c14800005a40726012600141c20139048190380351400320150a02800d00ca40101c1d04600441c02c601e03202126200a09c01d5004485003550041034035010808141e0b41c010843c4da00909141c0c81e810300c003202034101d8001c1d10510759180c0f4404041004a83c0040d00d0f2805201c90090862070b040d0307074100b030120f080005801ca804403541c0307202d281a0840b042c040d1001400d580701d85103044c021003408102c551000030b081c010340380e085000c0401181c08205002c411250b8400c494989802144468801810311203104c1c3c20381c0b15042c22900d0401c02c2c9032000d00d06840600003d0511004800324443c6c2c1e8100034040e0348250a03041001c240080c81d440007a186846004003489081901c85585070050300260b803140c01803010101d0340003103807002881078075409003080c0300414032000141c8840c1e40d2000d400c1e1050a41da42d0b2540807030a00e490a000c0201450380601e070911940c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 126777455 1250 126776205 126776231
    0x60c010b130b090609060105070c0906051302040503070e0712140415021204060f0e0a11040506090403050d020a030608010c18060c030905090901060e15210d03050910 73
    0x38900640319008444a00c4010394062040000301c41001c0e0400c14030b50b640c0d4060101007040900031505000701031007400001b854103000c500241180aa010480314504418072044400502500303e010b401400180300075200005c410080304c4000e103a0310312039220030205650508000d454000c2e19400d01a018103420350820b000790065108050908070001c00c034051000b03e0003086400300a00303048101040c0030070181d03008500a074040c1031340082d8003274a0707005842ca0000c10020489201107210070028040c6041e01c02c45602040641c0e40005628050794002c2051007182c0041e03555a034081498201544071307a10030780c050b091000c020807250060301c07400341c50020381c6510f121030644410004922903204206454070b040e03044d1203803c0c0c030314146002c02904000c010f0118000390750b100000180e40144050017800751205e01c02c036050840c5131100b40031100160f81111034148400780409455140e0004150034012598600000c0d1600c4030307100307981404c4182e0803035044030f41445202e451034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 126778705 1250 126777455 126777461
    0x120f0206071a16050301060f1d0a08061b03010609170705280605040b040303030b0d050102070b040c0603110f090d0503031f1505160503040b04030b0a2324060c01 71
    0xa810041040c3c0d0b41d14800401150386100034024480000c1c507061106034100c3c01144112007410312004101e855081030360225102c00e1090b480004c85510200c00d1040e600d86062020f8548030b0307a403058511315810a440908407400c140305d0468900c00035500340d6104c0c1c00034000b20740600307402000f20b40d09040841c6412413086103001d1722544201c00f901e001640301d00030701c1100c0c01c590b56114400e0429280d602c05500500c0c0880c01d103600001c0c000007000000c0c00c288002d2200511403020b2100c1030a081c140f01c8114082d582050042c18645421161280000c40a0b546034400f0b208443c1c4c1d44600359004954100881840241303244408420321504105030000301115031815540704906a60761000c013103618a60f0003051000c00d10400c0640d400050007a0f010790480e0044084a161070780c0d032196070186521952041da00460344105000c0ca544050244502e90318140941849045800003001c103408000740c02c60484080040c020464007505210150340810000c0545807a02c00052405000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 126779955 1250 126778705 126778711
    0xf130b04060c0e040e120906070506010b0a020706050c100b0609090106120b0f100311120403200318090702011416030c020f0615010309021f1404120f0206071a 70
    0xc2861004070f141a41080e20642112a000000805c039501884254400c3c981c0420301e450340010040000b040820010060303031f802031080039003243e600c2d0010b4600a041ca906070300800c0070003604001d510011280000d460b02e00c00c61070700c800519480e041c00020f06c140300b100301c542d8002040c28000907107a030300301794a004108603603101804200b4084c0100620076041e507044030340c02900c1115801c807140c443d0f0302860120582660081c0750183c20f4501e000802400c81e0101c2c00190305284000303c1200a070080191683c03000011401d20812101080c0c0d403082c0650400d000300c0c000000a820140300350000c03803000e12103034035055040c00d0089440b05548110701c0b815010906240c02403d40610005524460003404405407180e030700c8485002c071082a1200e005410542c96442c0c627400741e62840c00300c1c00c0f034a07801080382c001050800006003540720109442d181c01c030300a00c0100658540c4890205e034982d07010305c003407043c0040e82c07000400c10b01482901400000d00803028940740742e4201e4190b40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 126781205 1250 126779955 126779957
    0xc0501030506280e0c040f1401020a0c0b03071e0206060d080d060f05041416051e1903050f010501020c01080408070c080d111605011805220b0406030b0f130b04060c 72
    0x2d42d955052910415803180b4844d0b9aa0b10300112000c000b030b01d0744443c0c420308e10742051042d41e41a210540315a58500c8a03a04000c0ca12080001400501c07030f000744c8503640d040c071581c0c005001092080b00c040d495241c000d0a003030140b00c80c01415003c1288660440300d043d0724941c41006020f17100c00040c042ea9103d8010076000f140342080004810700c403506641d02c280081c208a580b41c11070a04100d82ca0342041086d4601c400b004510186204084d001901000e0401812100c0308403941d02c0c018251b403000b42084d038800c09440014405643e010890314910202030134401e1003521a81740c00c042c10710600324050035282a102c00405d00c040b01080e60295084030f6035980400d0f0120a2400303445241ca40040701120464200070825035014110491a42541c55054024190740d04007180720018156440180e0001c99603840350321452500c182060924299020442c3c18196516184801005000010004104000285000c480011446140d54414403450203800d16190020291062040c0c0034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 126782455 1250 126781205 126781229
    0x10606030f0203010b030103021201090203010c1e080408090d080d0c02010b10080c09040525020309030d0c0b0106053004022706041a04020403140c0901030c050103050628 75
    0x140301e240140c000d480c107031010181d45070300d581d00c0d41e400c1042c3c00c041080c07291200d54885002c0c00141c1d070207210702600030455898200543d05120041d82081c00e48800f40d0080c050160113100108070040d041d00c0c00c4032070507540e02c0100d1580b4141000c05000303c0898000140c00c1112680440c0d90640115204050589407661005c0104400703803902c5400301c0d0001c03010301d07040c041401c1c0c1e4505600070640103c1c1d50407075209450034042d00081d1b40c0e01c4c0d0210100140e4400141030b10b45003020810182d00150318038000b9014480c42d6510102d403013061103080100301c0c2c041684100a0301c0070082e0818414151481d1000120b10030350300441d240b0880c0d041c2e21901c1b064180318010000e00c414544200b00e00c0b2a0703040d817036803084200f10081a0310101342841c480701002c03945294841d8801400030314015076a41c0f844210324548a8605501084a1405001402c00400c00141e0041203102901e43c24240422030743e4441c400701c0c07481036a150b0816881d10b51440b24602c19242c003400c1c5401e9550114841c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 126783705 1250 126782455 126782471
    0x50f041707080624011409100806090a0b0303030a0e0c0d030207031101050c0a150209120105010503060106170f041a010303080601030506061e09130204080322030f0b071403070201060603 82
    0x7400d2100c1511688094134081e14041c0186588211b4600000c201200c28840c01d1240440103d181c03070180c070103602c0c0400c3c421420b0007142d10702000b40b00d1303020500c0300b02400140c5004000c680c503400050022680540c40303c41e0030f510100c090000a8201d500a41024080b1a0030300717000350b0304d001e28030090300c03c4040409070000030352003102281c596914540051461039080c0e030320034107441041e01c07035180c801c0e80c00c1c04548029956401600300441c00c1d03000200d8554104020981040c206a000f01c041c8000d800d14140b40c801c2200c41c40f0381c002020b1049240e50750b610b003844500300381c0d103c0700740d11264070001c0040b08041d0021840740c0190000c2c0d070100040e81d200e0040c084103100f034400f0f00c20460710145a401480900000600c3c040a0151042007801c440d04960b80c1070b40c0290300b01e0300c841c2d000404c0203803844010344080d50707041c002001d10840003842c5840d00f5407440500340018005280c0d000002d480d49014030030720404c480c0205003ea40d01e1403d071070000c0c0203000703c0c050070000074101545 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 126784955 1250 126783705 126783721
    0x1005040603080418060905070509030f0a031e03060803070b0708090a080435070816050609011209021e01020c0103020304080f0717121008030307080601050f0417070806 74
    0xd000203581d844600d06241c1804c00e001380112500c049025040241c4694000c5050816402014015031103601e8581e210f510100800d400d16114403070554950340701403600d0300420341c8002c004100080901c4c1c60161074404200850290075142c001c0c21051200103980301c10465400517a80c4a81115640c1c0403554030780d8074146071520000300700607003550010310061190354110300c410484000001c0d18000e80c004803030000c210003200102084006d42094801704214242840050007020303400c9030b4012018181400951a8010b40e1200d904121101441c1401888281c0c00a030136150000d1141c0e50006d090000450203c1050800b6401030040e01c01c0e100c0b495010740280d034052039103c0792050030202400ba501e501900002e1b025286140200b801009085d1520000c5c81114035000d00a40d55140a81d1400c600610380d03070090742941c1c02007040100740c0d513010100c0d80c0c00907400d1915642d9511801118a070600860304034661001d021a14990310000c00640201210180025540c5941ea0024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 126786205 1250 126784955 126784961
    0x250e09030304032015010e0a06051009060c0303240503010c0c0302060109050903160305120c0c03030a24062705010c080a020106092c010c0c082d03100504 68
    0x1001004140d510044c400f03088015010103034802100303000c449030105650389a2000035404e0740440c2189142e082030100d041c0150280310f01410040c0c82003050550301a40040c0044c58520404040000d441e00040800d846a0000c403101c030041c44d03a600c0340c0b100400076800302c860681b0666120f50310f81094061241e000b00070b6041c03d95010f40107000e1580ca01804c15010304402000203065000c10025220307a00105003203c46054001c0d0742e1181c6403101c038182c000000c4000b828140d4000702c05d02c0980b039659000000c0740c0d4042480c43d804100c900728015884c1000101c0c40d00e034a000e80c81401c0211310310340e014070341521030483d1500b4000140c030f02882e070302e400c07034984d02400f0300141030011103001048020300209000d0500c0d200010b2170a030398600d1581200e8840354006528400e00303600b01e0402c0c0e8a40908888541403400802c80d13101c0503070024004072000900200b142c035011030507007004440c03180940003514038420300f400c00c4074042d0102042c0354421501c2c8810009662008607450500b44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 126787455 1250 126786205 126786211
    0xd060816060206060f150708160308060105030c1c060b0a0c0506060f060a0c050c040c0e010e04050c16020d0206030f010f0806040c0b0d09050a0b0a0e06060f04020903250e090303 78
    0x2c5c00c40c1901c45409818018034802d94507003007284d090304000100000f50180011710080360014048624640f00345401003203a4005461241040b0040c400d0040d0020860100c2da070000a0984100c3e50248060780e01001e05031540c440380c0c86200c08175568a4840d04041c00a00003840b44040d40c0d8903950320403c001100b90010709a64101a05220f402091030040c00b0146a55005400b01e42d01c0000c103800107003c0d21042202c00c0006400d600209105580007080342d942140100e40900261800d0900e4400c02c0c020519a001c0500c40300410606644414103502002a00644540c0c0c0d20f281c041c0803a00e10003400e00c18160035040c410400a01340c040400c0b1207000d2a48801c6e5183c0c424038109140c000d503004140e08410390341d52910390030b0003c0c0c820044200003a118201c540007602c0c140030028201c4500301010940d603000882003180d1030f900d541e08020b1f107503402c90303006131a58140300200f454840c100c80140107a50341d404690342c800e000c1e6207000d4200e80d0321065000b0a0b58400c02a1512030000b5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 126788705 1250 126787455 126787459
    0xf060123040509030711131104031707050d030b010504090203011d070903050d080a0f05090a060b01031404020d1b1211010915030e030d0204030f050606040c02030d110d06081606020606 81
    0x207000358000902c004201801802006100c0010b42c082c100c447d5044800c0680c211942c0d00c8001410400c002e0028400701c1c01c1c81c1e118801904094064a40c5611510701359509420581d648500e050300740e0041044d02c0141440750021074aa40e180d00c0c001980140c0e000110701c0c10903c01001881c0c0300d1180040c4010340364410080d00540700360000c15130f0140406070400c0c80983c0c851000d00140c10700c0748142c80c03040010800406c942c860504000089404840c02c042c1054100b03501805006030b02c0c045144c01c036a055624106010640c181002d001d21510003d00544551300300000c2d903a03d496000c4140d2034020440c1038440500f880040da0144007911864060303004039682144001d0099110132814081081900e00d0001d21045940c100ea0080e08111401e030725001c0c3e00401d10004001c9107a10010950b402c229241200802942e240902d0014621454131002910554810081580c030b0624402c1c209000c41502d41040a0703d50104204a040c0548444000580c4910014070b582c003030800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 126789955 1250 126788705 126788707
    0x11706010f0303030e070b1206041d1b0d05150712020301061707120e07091401060804021c0611030603010f0605011b020a0f031a0109021e0901020f06012304050903 72
    0x6141d40c144d001d0110f500113007940b4000c0c1c82c00018010004001407440a10f030800134801d6141c03410404c4200e030313508910510140522450840842800110b44024131418841d00102d801d0510000301e80d00c103a00c40c014020f02900302036100540070003283d68010301d075a892348090000300120000c101d020234443c0500003001500c40110016141440c0e5800901d1403a000281c52500b40044003a2010205078a080c6e81c800d1404015460310340c45401e030600760f0f52400c809507502d0008001c0c810380d0090710103881204140b5800000822440c4020313800d036441070050211441d110b22a910503042200c080c2c0c002e508003502d0f03041e001d49920800007500c105860390040420b030713075000d0301c0e144044050491b042004044041740b084404450383c401140701b011030110406900f10800001403040e0b0004001a0042c04104010210060940300c1c00c1c030200c7d01c40780c541100c080100d150483c40400503055008400000c070381360b4440564110b1080c0c0d08641c0b24400e0b850041444110342086414040a0300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 126791205 1250 126789955 126789959
    0x519050102240a05040f05061006090834030b0106021f0c081803041e03022112090406090504030f0e01020d02030d0903020f0d090305071406031302040609090803011706010f 76
    0x2e256010303d400c640a181081b5043c0310b40e075030311450322200345c0f004c04c40780350001000c02403d1f0b40001c025001e820400b01500c4000303491600c00c840b030890b0b1303809039182401c4081000701102c1d04083e003000550304030020380c240e541d450a01030340318107181c9180442500c41038140305142d00280070b00300c64210720780e0706d0b4040f594643d04901040520103114404902041100040c1140c14446502c540ca55031414100e5071440c41c410440d0070400c506a06410101c013408002d510480819000351f080d1700c6000540e5103441510003c1e009080f540c215202036460607080c0000c1c076a0101c594208880e250304d8400349500798000680e9500b050f4680480160300c00c100804880005030000c100e02c43c0b01340100c4030021941140b05003440020320f03841d030008017554402c0042c800d0030040748005040c444442da1040c003418010070001e1000401d880703882c50f401d0f04844219200d0b6804000107001042007080707101540d14040d0500e074400e2254103584003001d40514a114404030b0224101d803031070b50200c1c01e114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 126792455 1250 126791205 126791221
    0x612020f030604110d09050105060a0501030608030a0c03020309120303100b250c0e041202070e1005010c0f05010c1706040b0303091003090c0e07030f06050a060315051905010224 78
    0x1013100a40070b138040300107202c0c55441d04441d00800d01d20342d02c10400850700f460010284a0103520300c0e8449810542095010054000c01000302c404010303007882d08001c0544541030917450740c41070080864003c8582c2814803c6a0800310156004210100c0c1a24040c1d44c2c40c3d240700803d0040c10300d01c0710b40410a143e040810303001d80c0d10401c0c20602c00c44240c0c0d085a959403050441540441e002d80e00400c0f07041c1c102001c0c036418421840507004201c201c0226003081d041c0810f00050a0040701c0c1800310300445102481050016107061b6944017000340100d510001000382040d107800c414501c2024101c2c04284149041c1c002d03012840805001142450395040030131444071000c41180060540d5400104d01240d01b1030365250107050006204109402e100030000c08171032490044ca06000e00d01102840695a814040d40803a5680d11b008100c07090f102c50741c10120a20f680c09241e202410014030400a614003441c4000c840098098941e40390061104da100541c03180043c840036050080003500322 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 126793705 1250 126792455 126792461
    0xc0e010504060f1710030b090a0c1a2205271b07050a0605071106070906081f08010606031103070e190e07030608010b0d051b24040612020f030604 64
    0x907655244c10f929000154812a4090000f550140d0701441e42e040140240810700c040705030045141c400400d9503941944500310b0f0306007180540c80d806010042045d149209840641d500300d00020f804030012020036406010784102803095a0040100c1c140075030300340099001e1800c070300e0245500304030705580e55101e0340c100b20558555141141d4060018101140c420013144011034420f1000003901d003807070300700030b070202e1101011034400d980a0f00822014070383c0010028200c8001b800c10074a2900c90140c070440000314080303191845040f14a000440e0401504200c00b2101261010400c08048d4042d113042480200d81b82d002162617002d4080d238030700304a445100940950400054415120000c142803000141c650a0002c3d03160031090100007028030131150304590481d8802d203601e00d15070f6029103504001c010205007641103211400315031104440c80080701c80d150609039194002d400880d4584d00240034074800520b6800201c1c1094403140300702d61512000c00c580e2415a5140400c00010f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 126794955 1250 126793705 126793727
    0x92c0408070b0709050f090702030910030605120319140a0f021606080406050a060815040204090f030f090e010b0f0d0902060f071703060d0f0f0819030c0e01050406 72
    0x10a240410a21000c2118140c1d0b6038082c00b015519003400b90b142c03004000030f00c60000919441400c0f00700612460f103800000702c59503020240c8508201ca9100d50096000303101c654441070b0080030540c64010795807000300003051125441c1c030855070900c18407441242c0040c26038241c101d5917030042140804c2e060043d66204c0041101788122030b880300040d0301d00c0030750321010b501c03201c080b41c0654184010080c403401903982c4102107220800c00145001d00c50b5a84242506481000205500106055403901e40050515981169210903046001d14004010b4200060300d50b0000714280c0700810010a2501d01074100c5d5503c90b06641000d00071102c070440c0343c0c40b021030681c0c101d42e10540000145c03a0076000e8251881c10b80c1c903064554045040108505030001001c0035000c0c0c080042040a80c0c4240d4010011030704080310300c100c10140e28105071050310168025000c2d41e0040b0b011210100084080c43c204640d07980c080c4114042d0f0b22083e03072242404e840b20f0340842c0c802d00051282c1e41c8a0404858 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 126796205 1250 126794955 126794963
    0x20f03090f2e0509030c01170105040f020c01020307021507020d08070827010209100e09010e041502070c050406060c020d030f03090f120905011407060b010509040f0507092c04 77
    0x2c0c0c0003408030001e24031000d1020108042640400c40c0d8000f4502441403001c640e100b8200650a410400000c20180c8414010a80304540d54041d01c09184026410742c0d1002d00481300856070380c14607000103513540a441400340803614440d40020115403010a640007040903545030b0301c140b919428419515200001e0010198410302c0c00721405000d0100e00b45039041200600059031a103416007449003954103070803080309000709501071032055100c846070300303044402240781a00582c44518003208002ca4140100308018008100d071400d1080189880c01182c80c129002c0220310307034a40c1d05449090401c007010b94805100b5080da80070a008800f00503848a0350b19001804a50660701c0640c2d11129170030581d0707030741070520a5240b83c45d0003164501c094a02420080381c4000300c030702000c1c4a8843e050004141540700d80707180103075034050f00644800c1b50303008200340800401c2da07124030000c15044a108001502407600002c0c00b5a8442202010501188003503109034464000c5000b1250082c20072a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 126797455 1250 126796205 126796249
    0x3060506010c051e060108010e0a11030304030507030c080c1507060c021905030705060108161401170405030903070e1009110f04030302030c060c040f03060b0a0305160501020f03090f 80
    0x840081c00c1409102805480741035010004d110000466190030016041100c185c5c1c9000140385178403c0000302c82504560109543c1c040b1315540000c82e0940c0101e40c0028101d20821502208002041c204213068615600c1240c011128620070070044420461071081070010030000d540104416401604143d18540100d981003e0b0b044260800c022072440c1c117640035000860700504001c4103001144c010300d980c0300203110f50b0f0202c2d1001d1483c2c881901c5005010f40d00c14a1403c1a81d0091201c2d606401c0c8400202225161a0605584940c84410003070701c00c2c0180034000c02c140403055503080c0905a014003959040381003030304040013006402c400d17240a40e010302440350b082a0000041c0082c40c441d60280d0344900707500036802d107407a801402d901c0c540380c4240814003c135010303805038804a903001040072450941020118603500341eaa04043c105c1e00070030074500e0514a131414100308444d402c1e807c507030000c108411000d859014070b00c000d95200c2114411f000a51130110403200341c1c0701d0a00010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 126798561 1106 126797455 126797477
    0xe07080d050315090103031e080f13081608070c0e0c0a03180203070905070905040b090103020f010212030f04120503090706110f0f07090608160306050601 68
    0x300040020210015200c1d581c0c0c0c1c01104514070002e0710140141d6102d040040600400e105400030b0b075003655180b2400148070b850454840c1100007081d440302d072a40104400c8020003124140c62421003440000f02d2400b1042e290000c0c180304900c80da030703284803a01c0d0542d000c60051740a100c0d608a0101044078034400c15088807211040c515000540ca0880403540c0c41c40b0040040203505445000c00100b00c01c8550b40c400c50040c01542c032185070407903031902003001b40c3d84d003100301c0754210f4060401040141808810354801040c140140e0380000c3e03401c40c81500a80003141c11004007600c40051109002e50fa00803041d8200c02854613a1451525034180c580c2c5111a20a0004200d44074884028428090003580d07940240c100070b8815410801c1042ca96070a071601070001c2c02c5143c4500000d0020000400b26000168080c4030580146035440c3e0b10018640200b46605000e041600 = true := by decide +kernel

theorem cover : BRFrame.Cov 126618705 126798561 := by
  have h0 := BRFrame.cov_init 126618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 126618705 ≤ n) (h2 : n < 126798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
