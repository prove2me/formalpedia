-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:54:28.294695+00:00
-- url     : https://prove2.me/submissions/f4064171-37e4-4142-8f9f-a5ecb9360ad9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 184892086 ≤ n < 185071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 184893336 1250 184892086 184892117
    0xe090f04060207060212150406081504080405120a150902010f08071404080705042316050d020d05040501050603070b0a030e0f01020705030307020706030e06071d120c030c010302031006 81
    0x3800364510103004e0b6880850240070342010442c01d54040c102600042c042e1f01d40040c200b0069a03418002c0b4031554000c54201098080d80c100300321340192050741140e00b403680720341c08102d602828990000450303100240700002e104455160b0038800010301824004039441782c0010b083c00c0d28410780c510420509000182c1d203d4403c40f210030101c0320210072583e4980d40d64900e181d8403910344c0a014440c92801c00c02c1458145919a11000f480c103003809000156a480311180c030080200141c8030034840704011740703d082c0d0800d01c000c2000f14440c020005040c1082d040c128215000101a02d00a13400380e007007446060400410340d07100c06600d140105001c020441c84608080502480000560010446200308600803010f188994020741c200c800f940c0e82c50303204070103a88500c550701441e03400883c0814400341c0b1880003030143c0f0030042508084186244003103071880441100140154010305050a0203150070311940a0b020004d1074190304505000c014031110300c1c3d0611031300050102451022011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 184894586 1250 184893336 184893341
    0x50f070b010308030a0c080f04080c03120109051503011a04050603210a0807021209040506010e1c060b010e03060105040510050d08030106080c0c0303070c0318080c040c0e090f0406 79
    0x21103902580c0341000e07507982c0c600319580d5041655211006800d200c1000031891103039116610903203611090820640f01c6031603001303443e4481080c4d4a8540401c0040141060500c100c80f130082a418000040f6441c0125003109282a51110381d4440c0c1d05226105091011030030b082840d08038126400075250f112000000e01d03020701c1180710b10b07860700c40800c20b005070300d05d540c050a050b135100e4a40c440c0b1981c51038012622581e03480141440020180501d074001c2c00e05500a6a1060040c142960000644400152a424840b02d41c1d00301d6500710f1200820003a80d4090383c120b001c02030074402a00781c00c010010f0744541c17050103010b01941c0d880000603c00c04064a1100c01000c1c0605011113140642c2420a0264400d000319000324107180c010450300801c2e181105da40d1442c1e04003039805d640b101a030890303956110b508241c0402c00c18503040c00b81003441f204514010850700c0700811029003d0824041035a0138800c00205114040500c20003980300d40c5a00d6034000145100c0010595961618100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 184895836 1250 184894586 184894597
    0x19030b0f04151a090a0e100315021c0b010e01020d050f032d0106080f04150209011806030207020f09040203060f071103120108061f1e0803070804030c0f030b0601050f 73
    0x46404845801114203030049008002c0e00c0c82c02e580c4091003d0b02c0d4006c0410003d400e44441007024010382c001c0020580c0d0b082005990000c1c101c0140c41c18049810641c1f011403211442200d02d41d0711006885190f801c00c8455088020a001915000010000191003030080a9035969000000000201c83da244a4058203d100030440301104072030710503141e5040b0349000d005000c00b241110001c03031020101c80c0c1c00d4901c00e035400300b823400c08010b075070002e200179402200f0101e052003880b004068006010310807030009401c4954005032030390b0450040008000782000000d01580000742404003581b0042249644800242c06502c00c1e601e8108003210b042018110012803400042401e218840703050006504075a02102111203c0e01c490101c440c6084c9111202e244403040c12808102d10107200074060a20140c854040861641d18140703141583d00003a02200c9074800041c0c1030040000200b441b41c081c0010309504516142165a030400c0c480340a00002c0c180000440d0803440620b04008548 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 184897086 1250 184895836 184895849
    0x3010b0603010b070b0a1a2107170c04050405121e0c10050708090a020f06040b0708030619300516060305060409020a0e25020319030b0f0415 62
    0x10703600d6956004402d0103030040f240495038241c0407030109481c0c1060340106500701c40c05c0341750400401c42c0fa0040210011002c0386a0345000507080001c404400c0030b2100390300800303480c000425003003030369134041e41025244c0405900c510310308000e0001203000014215602c852002515550f40304404004002001d15180d6406940f000520120801004140e02001009800f4107001c15110460213842c0381c0d008507046040703a440448588007502d400501c09000740000341c03070036152070f8403001c91000a51254400b552465400010b000103401e10101c0c01400f0110b0b000206800f9003404050b2192060b22102080c1140c08138458850b508041e405e05145158050211544600b1030380c50b07045a0000f42c07150001192a21001418504042c000d0b0840d0940c01020121a10b0070240e80c4074440a01804e012503046a660072041c17450750081101040103c1030b0021a01d07007451095a940d10214011140f040505200300d1a20700d0f125a00540b6101c001120041100c40080c403500c00710b25030b90b0380300c2c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 184898336 1250 184897086 184897099
    0x15051207090b040b0403030f0306031109040c05031b09060a080a11040f0207060903080c19030e030f0301061709010614040e0c04020409061410200703021801091b140903010b 76
    0x40c40c0c0c2c0e104c038000c00c00c0728466200c841504000760015411100d0901c4054058406c14903100d42c0e6107441820150700078401c071110001161a10003092034094120902c030251082c143c3c16102c2ca207071009038654041c2c0110b038807140040c24921107503141d5200701e40c010412040302c022001d00f5941d90304074200c040301ca00e004544400c0c6901708503002c0d012168041d40450007d0000c034006410003012070306030307800e100716045000d152450304800800311500342d40319038001406140b05030807440c1d000b54000c0485558030140b4201d45405684001e901502ea203800ba850200100200c5489424041c0e651030116400141d240052240760b040c00d01d00c10242e0383c410303c00034011071700350180d92068090342c0107942c202c12000e403183c042c8103001d1010784002001ca8805003628480704408045070700f098000380140c605142d66503001c10b40360500000245081c6644100511140c4128401c00300700c1c509030180c0190460400c0b8002d4000124076280001d0240300082c01081c41d202500081224a40035110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 184899586 1250 184898336 184898339
    0x8010c0c1203060329060a05060a1107031704080f010b0108151807030c02010b0d08030c090d08070b012112050f1c060303020c06040806060609040e060901050f0115051207090b04 78
    0xc911000b1071100c4407845e803848501180041c00c203001c0c42000da400282402e45401c003900c00076600c0c0d418007003401b02d540c4a140000710002d110740c45555180b407504c180003604c5900f020030701c500300380740d00311580b00980c544401000c550780d005441c1c070f8020701c4e14504600b46250100109480c1035001c4d040c900711707140c0c0005120302140e0590004015009541c02008104022410403040045009010f800b058003070000c508880e440344000e00607400d0041416040c03000c0d13a43c43d240c26812201081d03d8030400c510040081c1800c1041852a02c201c400b06100001c04955800300502d9040029504000c0c0100f000200c14070480201d8140071420b006041030340c04045403010180071a400110018002c407981400b032400c01d80d09403015154900c0c0a00702690302d410900070550021501036900c10b844c0d0039501c0021006000aa0260704068008103103172500070b110306100081a4010f0781031401b00d407400b241480c2e0000503200d030395201188140d0300784c5401108880c1c4d8940c98000c1e620300c0600080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 184900836 1250 184899586 184899623
    0x60904031706041b080a18030203040b0d0e0f0609060606032203031d0106031202070b1b010b06030705070308010b0a020a0312021e190201020406080c070c0801061e08010c0c12030603 80
    0x2038031407040d10382010a02c107001a82c4010381f0440c010800080c0564414003062240c001c515014000c0d10300241c000150188401d10f05c1c924100c42c40c000208035030031100a0024441083c40f001c0d44c440010784000e495400c0c95a09501c94408400c04411030f59105c0b40030604040c4039401200d01400c28140140b41031381800c802074024401071004941d051600c0480c10010741c0003103403a81c101c031604110b203400d1000827942d1036980088481c0d406c000355a10035054080d80d50300d9000c0c6025031a070340e480c5034950410f03140c00f810340310068001c0002010f05000c455140790b40019124003807030380f520f40507500300003450a01c0060b001e80c01d202541c0700410740d80c080600c0300c040040d1181d0000301190600150001e1020390803413103240500c0c0009040c5000003846594604c0090202c2c1d481010210649552a4213090850720345811101281c481c440800800c600941c402d5009054158020043e12132900005042444281001020352002d00340100c0c3c024040d5102d0f100039904602c040299104194 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 184902086 1250 184900836 184900847
    0x50108010218090606070212100603030e01080907080c100509100e090f04020901060e180108160609050306040620070503030601090602010504030f05180a03050a0b060904031706041b 80
    0x4240042140b0032824150b58502200500e0280d400501120b10740312241d000d2001040001407500c680e886404051480d2240a2007094015402643d40320400702c9441c0005021a46c0504010701a0380b00c40d10078803c1c40c10100c0c0d50100d43d2402c45050384004901e44040d519400f586c80886c0c0d000342c09650401000d504280c0b0f0480703560003119440c500fa035580d07002102040f401e58000c0d41040d44040144029406183d0310000004020b00b000d80c1521943c00c042c00c0e142c026007110841d600300c214070045c01d403029010701001c1c0550342041180c290610000c643e80304001040a4012901ca0ba0054044410703034901d00c0c115040c409910341c0d10078140c20310a580754410340c0c1203400110070040014a6910610606014541c141c0c0c40754150359040400b11003030782140d55480c181554900700c1e080341c0e9403100c148200840c4a01d020b0107100b0080c2c108624054002031016000303540328400c110002e6402031164205100720146000c840c3c50b241c0106004010302c01c1c14582c1000c0000303445090a0300301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 184903336 1250 184902086 184902097
    0xc0c140a170102071703130f0204020d0911090a0e060a0504080909130c0b0306061603020102090a08070305071e090e03070c03081206100e060315030601060804030801140f130b040501080102 83
    0x911a500030619180b60b0070441d84021501407403800303400c4052000065005088c00e00c0c00340020b1000d81000250300079a011508951801c5504030209020300003182031610140381e20031136003a42002032003d2046410b4440320300403c1010015540c0740000c0411441d0700980701016005010300f409480c00409440701e041e02c1c0700d01920722101c01c0d0301c005082ca034003004a03403003a40003500c0a800c010f840c0700c4604174180c9145c000c800303554080c85594801c0c0c0ba881500302c01000d0403401000490300e94244142044903503000307680d60041000380d0b020480901c01c03941048400f802000109042d00c001400d04602524400502882005800005100c4040c010f0030050105804c80c20003512590100595042c200c0d0014001c24221141c4200303514160000d5580000c0940d41000080c0107440001d061035801d8004d0008600c4a50500c014554800c2c5e150340075180101c81941000d4203070000506040c4040380451150720108017450454850741c1100710f201c0005002800556100c00c1d0b814081d410a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 184904586 1250 184903336 184903343
    0x20a0209060a0e04050f060105060403020607080d0605030d0f140c0c100921020102100504171c0204150906031515030e0a0c060e04020304150507020f1902010e010c0c140a17010207 79
    0x10f010000c907442c034ac07040440d0100c96000b09841e00c0c0c1260b41d40c4104c200c6d08200d40444410750b0fa42400601c030388051141603129901c99442c0354413607240707140c041c0080080401000c841041442420712804c0e0021f44a00f43c0801200c42d146503050500c002c480280c200e1304148060b041258440103215041084103030b00c14801d1f000d6640c000450030807034040700c0d000c880240c040c860125102640805040050a10900980824103c080070740818003c1c0da0081e4030001c00031080860504200741d2188034040604428a000c4c1700c81d0030400c02c1c11501020900810304007070740002d042c0325518026440fa0981c400d00100352142e25040d070400222400340340c46240080385400b9900d149910709031007140d1103180c0c4000403458890080b04030b00d00504000301010290710031a8030707140341040200a81c648080721900f021912a01c0340c400100403c80c55503155040c04903402208e03000513154079600c025140000003012240288000042c001300765980310029000700001100c502c04010b40051007010702 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 184905836 1250 184904586 184904593
    0x1e0c0306060905090f07080c09150a080f04150513050d0c05010f180f050a0b040b09120f030403110106050d060f18150c12020309010c0e040b01020a0209060a0e04050f 73
    0x43e140103002e074460b4100c40404c41c18548000040d42540140901a00864400c101604007507200d00400c40401c0740400a50307001201241d108480c40d40941499401441d44140501c2070070603645000298100c42c1c400440c00b51200b00203901d191b043e8a11140181c0c1250448800066002020b0100c0304800e07803c0c0c419509007901a100401c01d80202440c01009001a070706009080e107456003e16800d00046410340144024000030840d0001841c2c00341d401104004841c1c00c1901e00f45203008040d4032015883c0b00180308143c0311000400540f507010342c06003410340703603012420071480c018034950304038503071200450b00711030180704c200e6008203d00188810100030100302084030b26500c00000100a0404c0302d05400e00d5407800e0310b80c003c10b008242038140000400c0341c4140d4601aa04210392910080c0c0d074511400340c00551140c181040300e1f5080d0350800140c800d07600002e440e00682000a40142c9091003c11078540f00c12030810020042d4040d030210f01d050038a0a203032903449c0d144800c2d03540d12 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 184907086 1250 184905836 184905839
    0xd0507030b010906050d0f05010605040801060f05130f060b030c0c010b030f0309010c03020c0307090e010b19210510090506010602060601020604150b03010c030b04060e01030203101e0c03060609 85
    0x9000344a40d40c14100141c440d100490304e802011100c60340f000031004030403600c40400780c0c0e445502e03002c1c1a010b40000d49445403640d050140300c41c00c440c030540c01400c1c1514455810011910740d100110f016600690000c518030001039895000341c001507000807141680001006100c1c0c0c40368020f00204d41018009100e4008104109603452154501d2000240c1041004001640c0103409a2107141e02c80d0050720522400e000000e402c0501961003412a15103c1041522000080c4124080e140c6d040ba4192204440041032004140c0700b801150b0038800305600c03224010754640e00b40b120031680a805c4481402d40c0d207020401400094001315654030802002080503070011030b446100d200107074028041c555543e12007219840701020540107140d554408016a51801e0066503080c01c065200451642e010304244801c90f0041d901c0103009002d442c0040c00140d0303000c0350240d4404202030f4045803080000d000c2c40b4131044010b804405075031405260f082010f170103401c0030040f202c45449503860306 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 184908336 1250 184907086 184907101
    0x106090f0b0d0b0109081915051b0a050408070b090a08280c080f0d020c06040303140a0e0d11150c060f0907080102130e0114030303070c02240d05 64
    0x38006030041c080440380030b000e422820000da5100c0e1100200500d08041c400c0d598426540c10710703104034030301c5070407a001e015200700b8810841c001d00036942e09002c040045150600c4a050710310000034031650f507400c00040741e140442c400d200307440180c0f40301c1065444440d0b81c2c03c0c94010320303402880344034081c4040b10800070b801c007004180844000c91849048640880804050412000c200e000311507402e207070540403e00c5081041620b60701080d1000a240f24454018040e00d085c08541d4460f2065100704002e00019511541c2511513032501d095041d294407c0701e00650318501214141c9402c249004002814064100d5506403541c4060b50031b51800000c0f5400c000c0c60744039a01c0540c42c20391256000c5030400c509200c0d101c0d84203080c603080c0c9503119200d1140c00d003640c0c4000002a4801e948020911a034400091080d00412184405a00307070300b0748001003500c80c00700420800500c40610800c60030340d25144d0b00d400e080600c840c1c2009245202c628886002c1c0c1180b4400c0e600c2c04d03d020f0014412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 184909586 1250 184908336 184908359
    0xf0e04140f07030b0408190e0a0e011d190504050304140d030e09280e0f1903050a0216060f0f030b0f060d09020d03020a290106120207050a0308010609 66
    0xc00c0e0001c0502000c50031501c840b010848007074001c8400100400040d03c500500c040000e9440c1c00540e5a0312107054070604101e03c01e200c070340020040c07100007001000050502c4a400c55401e41103010991141c0d54900281c004c00c01602c8800364040c01e117410001005030110082003901c1655540310103e40002040c40244142d021005000c1030000b034030b40c510787c600700d480d003607100c2411541c000d8200b1180c0344a02c0c4412140d00341c20076050722805c0001842c2014004401100001002046802c1043c9106840075000d404080d0600c1400110030703407200c0c400d11149410203240c1c1b2004500701d40d241c90040c903106600c2003400018504441c05a040c0c4e1090092202ea81401020042c0c2d04405408000060348036001101d885544c40c3ca00d000141c50b02c606000e6440d01036000b400750003416060481d02400c080107000101505010b41071809035001000605583c21071400d008061100345070b0100920a040700a0600d103d284107000401d0b81c01002c49041c3d0700e0030341e40e000715180d461700f030310301c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 184910836 1250 184909586 184909603
    0x7050f1e06010510030e19061508011b0c02031507020d140a090302090907030213050f1308070b04140105151f050d1a061216111e01060f0e0414 63
    0x40c066415407000c403119101b500640e86e0004100250341c2e03100c030140100842c05001040031100c407521540340305c0c01164052614030043c41c400000b40b1035020803440b40492100448024402d02407000402425500c0400c1154903641c3d00502620090400b03601c0a075603020500740001c002090305441c0d100329403018081c1c035410801e075190804aa42964204452088010105045881040c1002000d45c2e100c02da402c5103d000d0040008050a100306ea50407003003002440f4166a035071603460080043ca44104499200b40c0080d02200e00b9281ca01d001e907160380021901d03244035820241401400d17034076000704820a01d0202c031100c904080518031200d543d0003031301c00c5801040003844450340140392500483c6d66102d17800306040361400070384001031054100ca000b000d201c8000da4100b00825030860301c070070411041800c12010f01c8070090a91030307031030040f02600ca19110488002140c040000d404c140c000d0120303d16101c0302c00e030722800451800902210f060328160000384a1113000b031070106d4080c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 184912086 1250 184910836 184910839
    0x3010f090b070f030f060308210705071203020706090b09070e010f0e0a09021f021b090403110a02040509011505040606020601120c0504050f0a0b0906091303030207050f1e060105 78
    0x15450361800c00503034000d511580124281926203c5d4001480110711542010b03520a00b41709840300c2d030031041c08100310388540d0500c0c018030000701840806900320741984c9407183d10000000d604034a6140c00c40c00f03070094000040905003011211401c0240c1495a0342c42400600112080d081c2d0f10000d00880304000c4c8282d0480390301150307081c03102101623140c16911603000d500c04540d60311290301045002844404064091076488440101c03180c3c184410000440024080c51604040b0000111080c5001e40001e00303000036060718210000c01030080815403a00100304021916011250300d001e05501c1003440803041981d0750205552030a80f0460f4140c07080380c1c0c01410070342c1c2085001c22510713109800644100c115600005040d41c5c0d1402090f01c101e500c03180444590030400040020340700101d00181c0b10325403003420065a0b885002e03400794000c86600042c00d010396641400d50091181c0040545103001c0c075082c080d00c0100008078a030207030440344207062a50b9840c3d43d0507a2030303000c00e0158a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 184913336 1250 184912086 184912103
    0x19140411090d06091a0103030801081c080a0b0d0b06040605012607050f0a0e040b03010c0e2808030408060f25050c1603020f060a0e06162003010f09 65
    0x140381504280301c01504030b510035500091038200b16168204003030b0403c00d1901c0701e203800030014020158080055401485c00302c0040c0000c480d014020b200110003044160200000d140010703440900c00c4c0c014a2816102500303855100060b410400710010703089034142d0246040c820000b074036501c070342e03036010b00362072410400d16410a4100e40c00c0313000038000d0710000c02c0280500c51840034264140042c103481905845074010700c00d00c4000d01003035071170885800e8406c2e45081c065030300050b000350000300351482c111080704605ca4204243c14101c00307a03242000341041d2240c0b0200c0d81707440002c01001981c40c7c240072075550790345584070141a503104440b40300d10032805101e0004101c000d00702c00c18404034181095400e00701e003128110310341002000094218081e0764403c0055040c82148035420840581d4450300c1c00f2000752014006840c05000c081c001c040002e488020f1491402e80c82031915844a409141c074803640c0071145010111000d83d5119518201e03058101140358131031003400d51307400200d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 184914586 1250 184913336 184913347
    0x1718040b0105250305071a0f15010804060c020f070b210402060d11070b07030c0e03010501061706040e06070203030f0a06030209010603090501060503070803070311010204051c050c19140411 83
    0x2402100d40f00030000320244803043c010386000442d055081e980846c035407003c079100c07031801c606000f841400240c02201c4d081801c04140c0d50b5a40d100c01c034a40c1c07050b045034000c0303013204400104070700e080c5100c034400784030b40188200400c02490b80b070010310281d00c1085c950000c0700441058905207400c1035a0003540b15030200a01c06001e03055030000b202d0004542c48480c10113101782c60344504002c04550050010786d913100980d490342d0f04840d6440070f02505a008211541c140030303001e0070b05090007281001c0c504c4542c0c006400e9945541060400d000d0100c10346519040001001e991707504269860182c08000500003180301030705120351804c42c1d4008004071920b901c0c05ca0180c004050640082d00c281d505d030180400c494804000e840000c0900c84011546c07007045090081c1135480c07000c94107842da40108030410143d13403003400e011034031600544601881c000d00d02e0801d152524010300f81d42c200301c2e145914440780c4925107100c030460f20b100a0310070405150b2030410007141d030a8001ca02c44001c06111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 184915836 1250 184914586 184914637
    0x5060901060e1302071b05030f0a020f01031113031a0702150403030b06070507060206010815040b1503030d0606050a0f080f190605030a060902010906090807030209041718040b0105 79
    0x55102c1c0f60f00500300518156031a00d40c1075683c840a410105c22262411080025050800c0119403c6103c0c3c0301400050442c1da002809200c100301da0700e41055141c11038040104c50343e0301251920f8011180701d10005d962460030800c000084403000c3e40130340040c00010301c072500100d0300c4000f21141407198412659255010740003030203c2d80602d80c01200622040002400c2000350102421040c1c0081295600d410340e09868441501c80c940b8002a4520134080010700f036410041d0440d8440440c010f0300c14100300420f18600502008010481c01e10200041054000000b01343c040c04e41d41c0c8200700402d4200c0c00b175415090036a444041e4078400c1c00058122a5003114850090401002c0850003560300e400203498001c900702c0580340c484d034030300c070980c11903802ca290b1200810140c10006041c0c0c0c82e0455240e00c80c56135102c060300030001c01c000101001007207400341c00c403d4011401540c0360701501c419081e0402d80d00440a020302e00e4801900e10340e6002e9800d072030341401614140c3d0f1802d031081c070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 184917086 1250 184915836 184915849
    0x40203040c05010315080a1b050303120402042403120512011211040207080a0c031e020114090d02190f02040501060804020102070803270a030501020a1101050601051c05041a010b070605060901060e 86
    0x402445001d234005001054a82d400d00c024040c02400b19501c0380582024010001210680411420102c0702200c221036001d000d5403043e0200e03a0402c03401c003132154220401b500d05101d80c440071a400c042c0d04e0000302e14031032040c1c425800f1781c1c094200d6100808002e001e1004a05c1000000f51541c8814000090840c0c40f440044849078482c2c80c250081408004100b050200b80301d01050140c0d4480c07a58010044010480300d920085840c02040c010080c1200a51904541c180e140181d00d00c6c9604035003031003900c80694075000e03400742c8108010741e5280720080c24410295012030060054500c0020700701c07000000d0f10210306440041c40065141400c0d41c8a800d89a0700049030009060b0100102190081c4040c1601031043d84a403844408001c1105085440c02020581444000c1c041405030b07880e49404010b0f800f042c0c40000409443d00d0424114031019003900b0941d0018046c000f14810701070001500b4a07600c180d505100f0f40c0c0703442c0c1c01c2100444c024018003000403043c0000c5801c81c5000b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 184918336 1250 184917086 184917113
    0xc110109030209100614040b0406050304111903060509010603050636030406091a07080d0b13020d0b0409020619050c03181e090c09010e040203040c05010315080a 71
    0x141030038204035a032980481c15600045640d03680402c0090010001680c01c401070344200a42c01c01424036040c10900c84200c540180e000311310400c00d001c0002410400060500340003c41d00405103a0b2610b00301401000c2c0000c80c0c007049640e20b040502003801c0d20b0f0f0501411050300d50090103014070740c0d102c0c0016017107984040c13003200d44587d80d5008064010480a402551000f142c40910760311402e10801600c0400d0f070350702510484440d10b1803550344505980c140d41ca940d45c400c081540d034064800d28172016042c44003d00741c2c0000700800031010030f12994000d00c0c0c998a010010310a10b0001c00401003140e80c9200007941084080115600b0300c400d00804001c0c410682c20300380d0800050002c0d40b40342d600402603800075201180d100540340e1030300742005c039102250811000c0503c0034501c00308103400310203446030302401c001180c1d9203490780c015465070010b04005081152285031034102200407203c540f0030300d80445d1400e1b52001c1101c0402101c3d0069408220050021a04035510003405078106c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 184919586 1250 184918336 184918339
    0x203090c090f0402030f07030305030a0203151002011e0606020a020f011e0206060307170d0309021f0c0204200a0f021e0d02011b021b0d020d2906010c11 67
    0x416a030420690780d080e5849002c1c0c2003640d405101c91a01e481850300d040601003902801b503101e0700c41040026404001c0302d600203e8203c02507200c1e11081c89041200340340e403040540c00b01201c042900d20590540c0020f81d82031074890030351112902866800102c1d6428010035006800c550a05009030424130242520100d0615085401840304120145104400c81711407005070000000c0c40920b2400304030342406062001d08030035241c9004110241d481c400c00200b1028540c48103003500030b659484041003400700e2000500c0b49443e1095070000e1626a006038100d2156182c42680030303000c007844080c0d01c1091142d002c5c480c60a064400180c60104162414108502c00c2419400c1004586d0a21007070910300070008210f10400d41c2006400e58004007410700071501030300d031f99003200742d0b00007604012140c100301c052410b01210400302d070140c41850700280d00700000c0e01c2c8800c20015600c90811451039056a814180d1080354050f925034401a502c0900041b891030000002c90144c2c84c00d8040042c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 184920836 1250 184919586 184919593
    0x327040501140d03140d02070f11040213060c03020a0506010603090309080c01080117100204030605070f020d020c040c0201180c03050d08040b01092309061515040b1b2b08040507030303020309 84
    0x10206c03811001c3c0d17030142c2412280c516603107041078200001e5032004918408220b50660420b100f40784e07610b07040d000310702c44c0100b0001d0401d0b03c402414000d01000c0c010300c2d04441966410360712400701130042d007040b080450014581620000710717420081500245c03010140e48140e05a441c02d03002c034101961400c414500e5009800c0c540001d51200c0c4014001944558000304461034217403c003516011610401c54150341080061a001542c007103070a04010004a800246089284200700c1c01000c02098400c400908240404c3c02d01c0a2503d21408480c070590031559003410000d8111502101070b10001e051000c500018841c07840309800520810b42d00708a0120400c450519145440794141c414800507001070040c8820b840e85d505007556200c4090b10070003240700c060016680c0c075110b940b0030303448022400b150041c125200045006400b80d400700c1100d1011410545120b00703103821130044112401d1a1600b5850107004401031032083d0340000140c0303c0c15145403400c2d0040d50004051029900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 184922086 1250 184920836 184920847
    0x2030f060106021e062505070b01030b0a060812031311031b100309080904050a0b06190e040e0309010c02060d0f0f0b04020c0a03110327040501140d0314 67
    0x11810040c2078024902a0b00501c1089843d90400c03000c0c4540401001c43c90300100100f0660051780c0481084e0740032030b0041104100003201c02140c80b8014200010b054590f803c00003c1444101c58404d801500080020800b8aa403a800160740d01c03009403000300c500380700b400003da203c00c1e4050384640a900410409144070344400000b42001104e8031403401c0103190a4840751a4184201c06000243c0705e81010890301481d600c0d6402640141c100403840b550b242d03400501021550f0f04034940118010300010744034408491000752002080400d100081c00b03080068403a4541070058051100100c0040e40c9072604410046500400c4000c0690308080c00300004405611288100e88940301c542c0000126030900c254002c080d100700c2c440c6684105d00500034034800030130116400c04041c0e814101104480711000c0c6007401d5006060300d00c0910700218180c0e03001108040b10001c88454111020050340ea01c45d0b005d002c2c05400c2120700746c1c02020ac07600200001c0d005d02c0c03030050200f520179051420311 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 184923336 1250 184922086 184922113
    0x22020a03060c020615040216061d011d0d0c020108040602031b030106030902010801091a090910090819020f0d0302090a03050109080c120f071203150e01080d08100509040203 76
    0x3140d00c1a00b14005030300400c104188071240c80d0050152460480301503150481884411984500f0301700082c0015950303800780100c150b181180e2080d2001d1540081c4041d160800e48a40c07603103c840c1203581640100003820851038461504004a42e5058403500016161a21050004d40005116603c00c855084490089800b030310702960080000c0d0740c0204260010340b000402100c01a8824489c01d03060814007000c1d059440000d9003406010b8600700102c0d40c0344114145412142000c10007010301e0480f4000a204440c0001c144105480d40541d007411880c2c0300c126964074001079000580d401031902411024466001070103040002803c00c00501d850780c48407400c40c2e01071407048502d1000082c0b40309481406100f40543c8440c00e079125814070a10380e00084d401c0c800c81000915003d140c8003d580154080c0d0b00c021400281500c0d074560042e200d5804244180080c0640030a0344641c500c0b81081071310441840344a41e1a070b07080e540e01c8524003001e1000308980034000700d03450302a209031845131 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 184924586 1250 184923336 184923341
    0x3110f0111040f0b040e04020d030219080702100206160302090103060512070f0e070507110105071a010e0603010b0a260f0601150512060120150a050c0322020a0306 72
    0x2140d505072031640e55280f6116180e540c91469611801201d2420b11007045180080400c085d070064040d2540300c60b0329500e00c0c0c100d052440c00c007800440c400400a5103000e00c4400b0f80074242c0c0903c00e48140c20030500c5500c0a0b6650700d0203c035894114020522a050790511a4000d49030210301810045100d6840d4000111400c40d81100e1810a5100700c000300311110f4044502c00061035600504e0f10f50381010f80000300a807180c040301808507400d482c4c0c2c2e200c4a0344a00304540b4400c0d040021552070099a030f50840394050300303100d101d4800617560040b899603d0103210341d50105000a00e50000503281646801c03e240088184691192081c2e450b400030b804140b0409001d01c0882000e85015070402040c401d00c10303115a402800c020040c0419400e098400400e00e03080f107403d013084600c5a0401c40585004000800740d4191401502500480cc00c1d41183c40d0f400344c04580028403440c0e44800e40c0701c019000841d5074442c180c50b080c5108031303103941d240c0e80e218140f0b0010300801101901d07922403006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 184925836 1250 184924586 184924601
    0x10110c04020f0d05010e010509010b07030e09130218220602070215040f080705060f18150c011413140f0105151f02120a2105010e0f0609010303110f01 66
    0x10700c005112166162144250380c091b104075452603207203504141c04101420310501036075036030180000340e140605002e280c8078440140d00904100140c6030035420780c40c0040c03100744101e0244028803030303405040d007054102030300c1901c184404040c102e00041d0041c070400045041035418550070405000961500751186031000c81c1000300a13559840c081c02d41204a5280d4405ca2154101c508207000607581c140480e40560150024182c440c880000390903081202412000e9010042e4501c05841500c500d01030840c2031808030082083c0041155141100c4030222002d48001030942d00c5030000076550001502540000c604684000c9412080542150415681c5948084d9144002c68952901c400d00c20009406022045c1c071740010030314042d5a518580d41c034205000000318450b0b11b502d20503c1106500109540555049010b501008008110a000c0c0c030103101c6040300003070003803418011894060440074109140d01d81c40c5480464852840c014109403501030703401c00c3e0303101c00c0c0309000740792 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 184927086 1250 184925836 184925857
    0xd0204180b01170307120309210f021002040b04090509030d05090303010905060415050114070606150e0612040206030a0207050d110c030d080609060a1707031104050610110c0402 78
    0x200c10b5040120603207a50422442d076880303903881046180006a039208191071901d2003404c011803e0301c000d11380a001d104000c20001550b4182210b12349800343c5c032a1400c02808403903001d40d07801e950101030716026845107014251003d2010041003105c0040d50340500c0d84483d009081d242480304400e14135041d658152240d440030b60001c40180032850710342c441c6541101c02141c082000b600344128010b184403013840740034184001110412180d03400070781107504540e4030400c204401074690301034910280301c0e01c41110000e04145000d00300b41c10210120b40c0c0c621040380d0030144035607640d420004154001001c40001d15001d11407080081c00400900e07140000585840c500003900104103460102058200381c82035024068441c42e0540001c0d1090f000001510305801950760f02012a94800c2c0f40d600c0760040d84144850026094130201c0d844060f01d01c1520020040301001c810802501c2d415240342e684081e0507004e01903400c2c0900f1901043e801d000b02a108000c01c4000090200c3c0c100700d1031403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 184928336 1250 184927086 184927103
    0x17010f03050d030501060e0409050f01020703030203150109031502030a110a020a0231090f0f0302071d10060507020a030203010501140108090106060207060c080d050429090c0d020418 80
    0x6100704401401944060b55072072404218a6140c060010700e008042030360180101d56501ca10402d105050110001030030303180c0300070b55990303046c1c0c0b400800a50003140c3c0078601e1451410510106c0d0f10869151b03048940100e480390040c840c105016000350b00140c100d6008079038404103d41e40500e00c0b00580400c0c0c01c01c4e0094140c1881d039006111503034007000340b5440c842e001d00d000165607140b062800494021030300c0e000911a00c0c41e1815180b110310f11f40c1c0191020800c01c081070304050380001c001c001d8a168121241c560244022408110070342a6995030f946407200c2424080903100f00302404180c0c0c00101030b000750983c4c0b03801203801c440c001e0708103043e40d80c00d0051018036941c02842c3d15400c030400304002c014081c43d206000b034413a11540500d0041241c1000402c1c1400b080ba4241d0704a1080d00e282001681842c0c42d0400c0903071101072007000c00e4098407690360041c5075503c07005031241d507140c0040c251030000401042002144900101ea11958800310345001140d0b02489824291096118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 184929586 1250 184928336 184928339
    0xa02010b102a02030d0509010302040b040902030106020d03091a0403021608250305030403020d080409060b03160e030d120e0f0c01031b2a0203010219080709030b010b0a17010f 77
    0x1c820031100340c10b084000248100a005880010356000c400781d0394a02141c48284c0140100c000e07206a50040c00da5140100b0003142600041d03000354102c0e147d98003110040745403488140d056900c00c800146c0065194000f120034101c2c0f407204250b2091084c4140c0340c560400103003807500032003950031007035981d800041e2413a00d9040c1660440303185c0107001030055040345180d881386c0d078a00c10723800004e00500c40d951584040082d464107031409456180418002640c84072483c040f20f40040300c01e044482c100c0307058260210700902880c0e0100a02034003900c0c90b2800c41c501511803400340c6864822a0350340e51800b440c05070b0144640343c0100c3c524409000e00c03094240004041e1000462442c1d070303a2150084030008150000744031341c00a00f800340c0500c030032030784442000d41884d40e0f298040d40550000501000c80803880e20003909087c1d164980c90400c0c0c0750b10900301c030448034900005200080c803000500c1084100d001038000442940b0f8000105803051081c010020820f81c040540c000302c8000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 184930836 1250 184929586 184929617
    0x50105030708191e0c0305010209030705040b0f0d03050c010f090209060303040b0301090b0f041a150406051206060d110d0516080412020f030a0518091b0a02010b10 72
    0x50102c40300810611190b580c001c40c5103000325000401c20b0401445001180038415010b4207642e800110403c810350342ea06005c2d010b50300c8903011034828040d40d030300401e1341d10341880354407604e940151402900003105c0e42406a58050200b0079414040184604400c1d801d003402015100040c4143c0070401c24001d1040c0100b0f20005002c461003500b0a0109219503014402600e0441d034031404003141c4010000040740386402504501508682801c1e00340440e0b21004202410391401a150350202441c0c3d0f42d40080700d8000e40c003c541c00148100020307000c210b07070041c03101d4000380f00074807261500595200d00011104901c80786036014002217543c07400d00e06035100d1a6801440002103912100c64900010402540188000c041d01000304400d00e0180c820000400400c20f490102c03a03071040d4245000e4181e41158100d0b846a5843c0c0036104140d050410011b80240711110005103000d45641048205400402100c4115036907018450a60b5840c0005650f1212981d143c09041808500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 184932086 1250 184930836 184930843
    0x90602031e0f0c071e0b0c0322030504091505030109030305090613020d030c05011b0905030709020903100b030a1a07081501120c050c010603060f0b190504090c05090a05010503 77
    0x60520b03004800100400412650100c201c0d03411540c04090f00b482050070030107091061603590740103808004060204004600f544004500614460540d2081c200e401988010803143c514801030004200380000c00c1a000c4030380008119510748403080100603240c1020a085070a41c19040c1c0c0066150024806140b038103004144e04850f24a000c1c0b24506520f0300841d0005000d128001c1c10841c0441030031051010a5100e101858003224440900d043d00c100020040b001d23902601b40b20303000e204400504d000c0548211404107c0240107800790078254207900004220310100250117015080ea810005201d2040c1103a0f1000c201c00802900d040c4140c000701181e8000b04052074a5900103614101c07680c101c2da00890f2012150000320b101140a2412145409040e401d80c0042d03090000120422003190800d446d085550711041001da0030340002c200c652210340000c0014100c44200510142c00c01390490201c550207918155285d5560700089410070100300c0b81c940049075901c0050040c2d25003031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 184933336 1250 184932086 184932091
    0xc0307020a23010c02040906020a0206010f150905060304020d0203060405100609060b120a32070f050304060b01032d0c08060f01030504051203010605031807060507020d020103090602031e 82
    0xc8a004009003500034400700b0022005000c40c0c1401400c004500440d56541c02025056038001010364403001d20110103503035501c080c055180d018220b007001017400c0c215105104800c6d8910390340d9015852500d07082c440a6480a0001da810401303104000015840c104802c9004ea0b10440c010300094800d0190307141203a2158128130b10890070b201e0100700e12200103094903800e15004643c0403480e152000404000c203034950348460120412030906d0f05c0c403a581c0c0d803c0209034130707002c9010001d69911b44045518032480325082001c12400d00100b000b01c0c4455011304014030040c10001a03d10b500744191030307004500c82060700c00440b5030903c0103d500c85070041d42a150790780d007041c02e854182580026101021028201d040581d50720001c0e09002c4100002982c082c40d4030010366407941c44941c018000e50044079030030135400a08000081051002480000b11042075580314102403003582000001c0011007016810103407528403071008942e162008601500100d176802c00300012000039a000b02100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 184934586 1250 184933336 184933349
    0xf0e010801021c0b220902010e060910050d0207051501060e030703030912060204030602071103060115082d090106170105100302120a08030403080709082a01020709020c0307020a 78
    0x43c050352400d50750004807a64080401400401c850300d002010805120000114400050b60001082500119981b100e09954000e07038072840c0040301e800500a4031300c514040075800c440702840b2003441c0380c425000f40c010564404000342c6000304070f1712810701c2e12350600010710021014000420503550804800d924455040d0003400381a461a10040c14a00c424400c501c80c1884001041c0304000159044030040c560004085445240900781f0b59034030364441c00c02c603000f441040c0c00400c800395410748c103c9441c0516034030603a0b07940d81c01c4a030140740c05050044003000344d500300540042249407045140700b0140000001a01841e1862240c42d6100305155003a07164504801c0c00202c442c01804401600d17019240b003911401d82c07095043c545400642c01034072803080402031004156200b6039242c000e1099641c1d4042c10f64840011b40e84078050713118111100c140d54440507440700d0032240c844900ca03038140151406039503241e410b00260b83c88031440d07568540001070444110b103808904007010b42070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 184935836 1250 184934586 184934591
    0x20f0a23010504111005071a0f01050303070b040305070305070618051002040803071b0506070f020f0f06070f0318060c06060602120703121d0d080c0928030206040f0e010801 76
    0x511362155410b424045041c0c0d40038010140c04800194054811034001344d80c400004a00b41502d0203441c101540c058404044a42407036000199900d00001610101c682114840010b1384581d0350540746580111400c03818440c09000f000c000c00d0346031181c607030035182003149002104080c2c5040780c1444449408420414810300051040100c00000c0d954207542c0502203d03440c481c4030701040700d103440941c44581d0292000174180b04102c80e2181410600b40300f55040d01d9a0b610003003c200001b200d20102035000754040c000c100100350104803880000d8080d042411200c440011701210034246a000500840d83d070000c0d0704200b002921428006080754409452a0800f4135816003140c8501c80c40074040003900300707010381c81c1c2081d640001c0076803d25204e0074126480031140d443d200c500703103c0040082540a00040e0140f4010030480c1c0001c074000304104041a1840046820061203001550350480000c1d004801a02c03a0001070028000404000c00783c1c900d45211107a403508c0507002540940d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 184937086 1250 184935836 184935841
    0x1302190f1d0f090114030d30020409022703010506100e131d210403020d06021207030c021c05041806050402030a0b0a08070602061501030b03100c0f0509090115020f0a230105 76
    0xe058004070802490044407120710743c00c0581d1110041e0095400501032fa81c0300180c401080050b403209400000a29a0270b9403041a00404050803500c0c200c0304160024902d83c02a92084c2c843c0c081c0703140e503c2004044039040310034440d82c1000c648103400600300c141c4483c1b008140142c1d0403c6050a0701d8201c0440c03501c82d14010303081d00d00e40e025506c0020f01500080d56403500300301c1160181c480c040c11030ba4095584e403070492001030142205c2110040075000325074054480c1c5044140d4040c0c90b03c3d01d900c030305281c50301c0e00380601c6402c0d14810781e44411035030301e0901003066030356400111301401150802184040c039400421803074140507808101c42d50f0040808004c92a0007107142d9138000090190030f08040121801a400b40808520040d810f00130504c0d440b4110080e6402411891441d03a034000003012065401d0310350744500b52015505c90008130042082d82c40a980416002007244113035052040001800e500e84802e51000b110502c107001300405c40384601c40f86e9000e41c0e062941c028400c50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 184938336 1250 184937086 184937117
    0x9020906040509040503250218060d0809030309031b03150702060a0902012706080603160b0f090d08090102011404080a0e030c1302190f1d0f090114030d 67
    0x244602d00c62140202c030f00703000050a025060040d1381400c064848081e4420007203c500203e00c490440e0102c0c441c1c000b03413816460844003002840c1c810701d0050043c440804407a1134412182d004a14245c0e894070042000d03044585060251075100c10312800f00660b0340d0310030300405080680307014083c49a00404010003102c2075001540c580c000b4450503001855217101d0004880c410b160660010041c40045000c80704011f920340c48004480b8a0b80c1c07049056110341c0e040540b10070b14003040b0404020761000074070680fa4404010b10480260002d80c619021503000400c1001d1035000d010307a00d13103c0c04540c903a0700396028002c030285407000582d42c601e10700c0c03ea603458445005807a204010820780c3c0c120308499890404c180341241000610341034051540c0c1d501400030794424892030281e02035101c400c080c12800f034000c5034940c1049850790754628210f1800d500803402d0410100e076000d007250700403148039160010103601038081c05d400907840003103803020b16291100400018041000c000440f1006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 184939586 1250 184938336 184938349
    0x60e06010807050d0f24080105092e05012c0106090308130801110403030219030504211e0b0f1504020c01020c030c0a0213060e0c070201051603030506010306090209 72
    0x1000031030402d2030b02c0304d038040200c1d40103000c07410000000c2403418030920112620f039801a64040855420003103060f445860290a8500a0354035800a501080840803c4800e11400f41c0500101e00c3d8841d0210107241e8100c41070307e0702030b0300031902440d100243c44201e8843d40f0b60740206500e500c900403078a5141c158010403400d024800641000c10114040040a41e00e0000e03800030000b110091000c0008851001c1407984148030484c054030455603a28600c218080e408c0c25059010307103c2e5400c051a200c80075401664513611401d10b021501300070700018008040806100071261f0300070720610014a007a1982c64005000c520302c41707441008010302c01e2030300c40340050140b9050f240940c0302ca101d107103524060f025020084549020200e03000203050800500300800c1c9000312a1920542c042e25038040c2143c1c601d00445002c55494800290101c02d24001800c2851061503d1854442c0055118601410b0001c0840010f038617036040c480590386c0350080901410740c0b0381c800c616100340302c00082d1a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 184940836 1250 184939586 184939591
    0xc09180203090c0f130f0b040c030908030a050612030703020105010f06110a0201030e070e0103140c10090302040b0f060a0201060501030c030605090411010c0c03030203071502091818010c0801050301060e060108 92
    0x108540c0e4094001113078a074411128a41e4503005818020210301d4041240a41a0620424048d62030a0b00c07a0701128481d00505094130740040350203180d0b4a401860030041e090080400d03404c0250714510301900d0b4410002001054025400000c02d07504200c0b0000b480401c41d44001c007004500c1c40450344000000c1000c10305280d0902700081c50500640c20a03003001c54a40c03048098001c40703400081032008142d10a8002c568090643d80b004640c1420059003d8044083c240081c8032034900707100604003a4000d1481800c010040c840441c140000150941d1010401d400140d440c0c02c010855542c0502458900030020300f0140080307030a10010602c43c090050000d82264240b200014032640030f80ba8020f01c0325008510181110b440781406580c80d40200b4003100c2400d0503010100240c0680d00c02d54020410003802004000c5004a21200000008d0441244101c84c1c001e0400f449400f41f0540030012620385a00e0f42e150b15040c00c00d42102c070540e001d21103410004080040341c1c0e80c00031703441b903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 184942086 1250 184940836 184940839
    0x3050c09060f220e03070f05010b06120f13060f0921050a1d21060c04120201081b040f0806010e010b19050d0603030302090906100e0f0111010c09180203090c 69
    0x2807040d00f00c0c00343c2c00081c3ca0b440c410429207000c00038489045c440c4040e542800725010324000d020045e0383e8001e00c4520712400d180282c480301440080f41c452040041d04d0b60300702e480e68400501e100b0701522001c0880740d039056407011140e50f800c0004c041099043c0c00402d00031011781292001a0600c0b006080741c421107029104100e038128188142c00d0215060000f03c40c0d02600102d02211a81c0381d41040c040610001110b40c070581d800514148000012a02134032481c0e012840360030110390040d141c0c464044d1650b00c145403484800441140ca03540900018560f0300c0c1280200c83c0740c0041d06040c0304042c0c00c0207201100c014010722210104004540c410180b21020f07000000000c80d00321002d0090a43c154004e0b0706240e400030500d0340c1a000b4203000030f821107040d40076485000c2003000c405141031922000c0341180b07100d0340b00d44c0f500b84034106100806041c10030380c81c840440504d08560381c2c0110600030584000051041c030704580ae0142700041c03e107400b1843c5080c01c90b01595148072810b070300c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 184943336 1250 184942086 184942129
    0xc130b0109080a05030c101b0309050c1f0f030b0d020904030c080c2107050a0204180c090f051303020705090c04090c030506030c2409030106030c03050c09060f 70
    0x180056442200801c1c01044040180c86a2010341d141c0a52240d10010303038801288510303440d0001d10300e20b9103c1c0c0400c400c03012a900075040701820050740030700000b00068504c1e003d0030f045c240c09500c03054509403804404101150b4a5522010080c10001408482c02e0405103050380a031403d4541201e07210b41141c04840b04181a600d0346011514913001c010300424090000c81c0f036000c9a07200145104000803a400c502445011803070070384855015504015180e507024606080242c02d0661001d000d10803121804209203030680c84d01c4802030f129510a80b00c4a50701c80f52174100182c54807500703401c801c41d2403608040d244a51030081d40c0ba281d0740030300342c03082c0000004140300f140200c0072207004010090080c4001c0244500207002840c0440b011402406208503184540c50400075080049000b8001d09416182001d964041781d04075800f007503055075072402e010000c180001c49001c01142714030000d14812005e40305210343c031400585814000c00ea0a021440c03550348044108006215801d583e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 184944586 1250 184943336 184943351
    0x40807050c13020304110d0818060904021803070906050907110a0b090609060f07120e01020f120124080a050406061a0a02120306030d051809130506090c13 68
    0x6504090710a001550701c42031100c11140e0803003058014600c240e001d006000c0f0f1491540040c4040118500001007007020100110740040000c1492418200c00c050411400e080c008808a42240e016200c0021100340504a80945140800c41400a0024071006008140c5001c000c28850040502103005106002c80d4942c1c6030202084520f0025422034840401c0782481c05002d0384550040d1407441d128040d00c0e00240101520010301c6018004555486e4054401150301e800100200118403940755020031402d40b5200b403045c0a0009200d281d100f03101f080d45488052100d602d0000074000211100103000c1c8113050b00070101c598000445800403d85a80328900200200042d4103e524002c89030f582c0e00825201c030030043e08120140c0d40803074584604805481c1581d0008450155265020f45901040e091007240503004488400851179005441c000000305200404c9803201407926001c134081e4103012040100719040b42c03100c0b015143c100c4181b03001c903024074003404010101d151100038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 184945836 1250 184944586 184944593
    0x3020904080d050c0702010305160219050312040303050117010e28060c0e030c0108011505070510020a021b0d03020a080c03070606080a0501240905100b0a02010b0102060915040807 79
    0x40b202c44080c001c50030021450811818a00341d0040c800c142d00007460800010700415919040c21800e8a03542c0040c00e49091036804500c1413026228202c0c1d10780800d0010003804411000c0c000d002d54400e40700480d1540c10541503a070b0380304034135081c07607003980c1400c0c02424140f5021030008846001c181a108840203d60f0f040c1d240000005002010689800c12241d6140e07440015800c14200880c25265512060801101c0111080c0034207070390301040e2010102c6e1203020744d009020b4140f2503001c0d5008400f403c1905030880e003148603da00541c012550392050380503c103416100004044881c81e80e29070903610004d42e9140300e0302008000c0800040c60004021040054031340304c40d07124000b800217503140c1041d151610802c010450315582401c0c0c011400d0390796503000940492996001501d2a03142000c9080030b040b018100f42c4505456403008106c1003c2080240701c112144d40003c184402e080000a2402d003000f802cac9100d5800464118034045c60581c0c4003600720790070280c410b884024605 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 184947086 1250 184945836 184945853
    0x908370c180b180a0f0e0304050913020306040f050709020705030d0507030e03160c0b1926010b070b070306180e010e0303010e150108151e270108030705030403020904 73
    0x5030b5650004403078001c0351080e140300a040340701e0451628148410802c44500c00c06556032400741c1e400d56001884240601d01b020300080e0ba00c03440e0503070301544004242d00030906218056905940b024040d5011405020302081039000a102c041d008500d031001c142c1b1038544038003810344550300c00c64441001c50704892082e044440400410010340c0e6598800e5100d030500004c1070f440495208070011800184d54604105550060390101c07840454103064840881c2d10745070700c44400c0342e141c0c20480b451002411a000701d038081d042c140715140d51184103040001e201d0380018580300406051040038000c00c3d86d58040718215203542075020843c01340b800f070ac860241c0301c007141c114810300c0088000250006a03a40360707030090b110810100e801c4c0810400441e20504111014140c0a43e44c010740d603118106408407001086105018020300d10b41e800000c2d01448407a030500f081000d0480345030009029070705da024014440f0800070342c50b00a580d0394a648070b000310303c0060311075070b014130001e824400c624 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 184948336 1250 184947086 184947101
    0x1020f030a030c0e0406080721060c0503011d060a061103040e07091703040608010e0916030302030310170a0201030c0203042705010509060d0b06010908370c18 70
    0x1581e4aa801040004005051000c003003400a0108007101c00c0713030308007446138100350f80e84400601040b41c101103a21024000d1703c4c01c2e0740c80842c481346220010030b0041c03058505148545d5542e03941c95141205001403d0f072003041c41101002d000c070a1042c81d0351a0b40c1c3c1c2801300d41485c104581c000c0840940d450440c0590350251032100c2d144004c100030554030852000a488a40440c01300e0039080d058050740d01c0c0114010080807030503050060242400c0d54002c9a8008001030464500b000f089142c0d072103000180d80201d02592012042c4001c0da520424808040e080304036584501400415500d41e680030030543c060f0505980c0d1f480103442510a004407030241c10841c040451100c0703c2c0001c9101002e61280c400c00b640d24120000c510f034606184140c2c09020020100080040d035501c2c0e10500741d034040d04940c107200951000003442c04080c0b00703844600303501d03000d4008181420048040b00b11920011121a05072642c18000000c81d48000d55003517480340810481640080c40d418402800719 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 184949586 1250 184948336 184948363
    0x607030e0a140a020114120105010806040f0c031515020604060e031207020c040516020c1005090a0b1804020906120601031409012a1209020d06110c0105010803070c03060504020102 79
    0x42c072a07090054000801c403424502c00c1c2d8440e1002c1e1001354040744603010700c4000da8054075401004024035881000080c0d003280006000191903842e000443c0103c80058458801203a02e8941d003021010f034881d074007002004d004030310b440950301c80c40b03001752034980080000302541e035944079144060f01c08001307803101101c0740758200b0280d050407030001e9540c84200310a14030440c140b50019560581c0c509004c00681c1c2182c000380340d00c0300b141e000c0201e01e0701c030441030004001091100c205035985119200c2c2c000c10034855225501c0d0704d49540290303c55030301a81140034074010040c00c100c98441d641280c0c5909030f59000b401560711101c004801a0000e40d040710000300103002400780e404810751240d09030a01002e18840005010b201103c1200d0b011045407021500503801c0c00384480090300810415031008260640340c1b41940e480604031403214050b8503802e40c01140d13005501800f403103690f001d0107110008504004042d40c9500700b00c45640401083d481d220030104085900070001d0500c3c1c0c180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 184950836 1250 184949586 184949603
    0x7020618030f0f010e0309180912040b0a020106050406030203061914010311100201050610030f0b030f03090a08010203010e0604020702060d0e0318010504030c0303210e010204090f0e0607030e0a 85
    0x156254420f9680d0800c050001580d40307440d01c9190741c070708000f0854250410240c10380003100d0b0b04148405c4c00350001801e051a83c0600c18200d09203420340d01c0280040c14442e0300c0301d41c990030750400003800c64030242c1002e0b00076860840d003800969800108190b01c4201e104c400100c403e408034148010f8230403400914521400b0300000301c10040009000248107906582031800e41c418200700300d0a0312400d541103504088402400210f283c42a040400820101200800c010b44651f01081c07a050000c0711012031901701150242c3d60340390a021110003014000000d500f1941091a8100c40c018007030440d5219685c001351708000c5403501c2c400d41d4680580c6039010000020044050742d260380c0040082c015103281e605a028256004030107079401d4a80001411500324250b5030182c0c0c0c0200d03516141039003120085400203003070000c0e000744400500c8540000da1543e151481c000309507540c49003501c51503400c14a07880e0300c00400007002070384030f03d45181c0400c507800048441c03402c010140b107000c2e10494 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 184952086 1250 184950836 184950853
    0x2030711060705180415030b0a0603290108030307020304051c1209210f060f110403080a09091803142104110f0d0f030e06360102030702061803 63
    0x40d0803c000e048800494650b4006405030b401c10403040741c0c11405c584601c10034602083c00030903000c100a644c070030059400022041d44980307600e0160100e60000903064070700d5481c03a01c8090f60100f901030051540038002c5007541440d08010b034490080c0e000317080c050f80502440e4160ba449147e10702010702c0d00b20310090002004400b00030045090350162400541244000d0300b424011441e07803007000b070b800019000d400320740c51303070f803440584148510b2045d000d071501080e000c9030518000901c0214441c0c0c01e00c50707855507a208060721085460340b045101130303d000c0751501766008001c0894242a814500155140784c0041046041c4c00740c6803080c0c1840d1810076444034850200355080e40aa80036840c90a441503800081041c2002d08990494100542c50181c0c40080d010080d504002031103400e1554401d04118003007146504550084000103040d06170b0b04119544400181c064007044000024100d40c00c000003030b40c0d0b0702c03401c24001d0061100040c000013501d03401840d1405031400400303450050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 184953336 1250 184952086 184952101
    0x15060f09091214070201080405071a0711030721150f090c090209060f031308120402010e100815040207060c0801030308070905150a12060e010609170c040203071106 72
    0x40998541c1114040c000c012030a075210300840d01084814002c00801d40380801c07543c01181c010901034030448062254510101d120002580d44c1072083c3c07103103484a51980c806d801c2c8504418800c40d002030103900007100034041c5002403048901c12003c174108a000b000303010b280242ca81118101524000c0c2d2520504807400102a000119201e0003000322500c01e80d11424135404030311603038082c154000c108005c0161480341c000c004c0c59009154080b41e0100700c9147c2c940030150b610000302031300c0003541c1d002000115a0404208410880d003643c0e004d904841c0a0300240c4415400740001002c0341c04034101c56450b5541d070b01111420356125400380141e40010001070407440080c0000ca0204501d000080c80c418403440702d150032a80010101e2103003e01c071603030058950307001901d04000c0101c1d40354420690341e010b000351802040b001814040b50340c5800780040c031002c5180c024034006e1f00d01d5004e0a080b110001880f0001542c00c440c0141d89855014055455803c04544808940144030030090107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 184954586 1250 184953336 184953341
    0x3040305160b0a4a06070302340206030604060b0f03041a0c04050409021315060f0c0c05281415040506071502040b07081e040503060415060f09 63
    0x62070004001344040680d80300c91151055011218081403926100e0851245180c0032407500604401d0a0301d080c030141002940d030420304112280390220b900011a51080140c601109952100d01e840603481c7d01e025102071340d1359502c2d008010344690004800308a142d92aa0300540c02803041d8003081e5602c0540360f080502c1504100c030305072803601590540b42080008050224400d00f81d4219451405080108210082203110001d0b83c101e01e424042188190b424400c44403000e0034001c1001c60b41c1e150540c020907e80341114138100300007000c0c0042000556103006002034410807540c082082c4000c0c02c1c06031411424035524051005000c0380081c26001200f0711041d500825102e5500c800001c034226074982c030413441002c2d04640708010720004140d83d52400c5410444000d005450a0f58414010a16030001d4000b43e844400000d00800510744200184c509030590030301050a0910f401c1c0020789070280208050700b1240491040320a010103a40407402410348005803004283d100c5520200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 184955836 1250 184954586 184954591
    0x41205060a0e0c010c0b15040207030e0a0b2a0a02030102070803091204060507060b0a0312051210051c06020d060f050f01020109080405040f0e101509050405070b03040305160b 77
    0x9142c1c5031201c0c008100e000032604440da0141a1220f03100c0314102e5681c042200700040c51000c40000e03005043e21140e40714001054880e02a40d03a2400c8029100704000c488041ea920a04603400c042142d081805010002480f00114081c090501c0c030381540c0304242481c2d081c600080d80b552000907010104014403028500032542001203030306100606200340124882d500030344000c54024401c400010380b541c0c1100b044071901502c01031003103035a5a10701182192403e010b0012030b0000c2205010344007c0c04100b13900010229000385100c0c40d210208214a210311758600044c00e92218080c280907454048480003c408113040001c03a03036640940d04688800d0180501c6501e46c07060076569980305020340602c1076001804180b81a181008000003820482030350004185c0b2180c54a072492814801c071003101013042d03c00310b481f603071040c00007807810110340002d030020381f501c002d0001140b400202e210594a40140c1951f6030703200d40c1804c1d2040e000f00d000c1c08003008040d1098070200480098101d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 184957086 1250 184955836 184955851
    0x901020102040306052a0406020a150b0a0e1503012a0c080d050105010f02011b0e010e04020c1608070b12180307060f0c03020c1213080d03020702100806030c09060604120506 76
    0x4414580445141c14074402c234030402c80140d00010182000c20807004403d0201c070b048040020b10100c104001c185011126840300b0907102c0301f5810442006030150203030701c1080c801c07002040350701d4007201c422002d4a000e440c486141d0201402c0e91402a0240c402d080311a608001e00c0c507241d400101c00c4078040e250900980e030000d800131040c5030b8024014081e001514080508144410440c403804840709220701514a0400c0314400000c0c1807a182c62005000152049000d0000003004403680c00040613168011140381d07100070010008180050f0584041200d100c0044a085e00c41c48204d21101d410900010040c1c040054a5010001503a00c03500b02e11080580600c202c18401605030101d020b64100c103d05c640084100c4900110804000c0c032032405102d00c0522200e840c0c40480c0d1901c42c002c101c82010035070000e08001503240c4400401403d514614242c1a1481d00601007a01c9200c140b03080e17405291104081021551000d003550050480112210350114150901c9a80c0341019504074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 184958336 1250 184957086 184957141
    0x90309030d0801030201120911100201060e060109060f03051003060f02130906050a12052415031b0d0309051903060605030a17030a02040e070c020415060f05090102010204030605 78
    0x1500c0079000d0711007581240d405840704009880ba80f280c83c8007030681c41e80d045400a80000c85040940d0700c041c09520503104540c00000c21070b080c070901840b1500c3c084d044a040c0811060200400c4d98840041483d40240d841d0108007520f4903401480300200c80d030001003110b070404078803001050040d40074100010148564400c40d550743c0d401603048450074000d262700281081410711800c032002c6030401c20684164101c5200610720491341803007811018042d0341081028040c4044228805001d580e10b81041340944620201c044c40d1816103541f441400d4040c441850101c01894040c3c0d200100421024007010b04040b64103401c030344818600e010480d0464070b03103040812070b4140014918031060380f2111904503e2002d982c40689030b04000c2043d1045c81d000c11000c541c03a1035001060313001d0140c85d110401d0003406441084107444641c0d405203c0460705c41410040560b00c541a109031040300c1c20312669807142a00100c0c0a80710780c0d00090080343c2402d080c0040d06100328050812580600bc10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 184959586 1250 184958336 184958353
    0x3050c01050a05150f01090b0d050609010b28020f01060303050913060e01060302070206040810051b031311060c1603050d090e0402041a180a1505130c030e0609030903 73
    0x4442201e0f4113840205516039250203004090501c5861072942d400c050500045844c0d07100800e020507404001340000d07068503141800b205040180300d59015200301c2003a2400c180002c4d0101d070280c107030042c20a5440c03542c01003c0791018000d104815003518240c0007409440c1e124200503116a000791281c1c0d01903011101d2007584040070f0321580e400e851041d00c19410592901c00210041d410542050340e01031000c1100146800003004180f4031885810004541881d003118401d05080c0349001406a04004000300060303900c008101007283d80e404420402c111200b400899481d01800f5540009881091190380301c1c40d407a180d0b800202c0f4402c404946268605060841c0d648216101c0c40c40c0000e12540400c005151a8124020080444292114510701e0074002001c403503110400700b00401c2914140710380c01066000c1e5905540c60702955150141c41c1002048621101e1072800d030f5841d64500700ca005251003908801403001c0e07038000301c403580e00f01400d4441c3c03aa84100140c40c8240b02c0c031001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 184960836 1250 184959586 184959601
    0x5180f130b040c081b0607382a030a0e032a06060d0302060a09030201090f030804060e06100506030a1d070608100605030705070f2f04020903060402240703050c0105 72
    0x101d10705c050f08041c261505040c61592500e15511409100c8046024000c2e288618002105240c078207218100c41000950308140c0307041208200545240310125000c10381c2c09001e10300480480380c102610a90004010491080160440c0a21f40e81c0c039a0386012501842c110440004d99200c4c403103003c0040d50040d85411041042c400040d03213000740580c101e00d001941a4000364082248107000307000200706015650780c2d1081506c12110101c002c01e4641090006002080c40381e07c002e90388204c01010345003010121407106600d00e129207440f07980c0000c00104055010703004003001c850340b1510034001040010025840c4c01140c09040002502d400002d507040c450f078800d0100704c403019110303185580c5404c041210680d00141096559520400403a000660800030f10b42450584000640d14007208004100d01c0b880b200c00510b118a005001d0b5500725500030500540103941140d03504226151100e1580044a08901c1040c1182e0b0129184007030640110082841c032008900800c01f5980318007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 184962086 1250 184960836 184960873
    0x11d0406080c010207120c0303180305010204170c010f09050d02130204030b01150804020a0501054009060e06011803050d0302120609090a06110f030c0705010605180f130b040c08 78
    0x11801340c400d100358a02000427074040d18915000c0c18120503000e00803602c0e5211942664070990000d1410b101d04100c00f48001404d0007041c544003c2441c1109003171001c01001401895240105886051883c2da900304546d142c000121461500d0a415034580d0350300e003004c0d40c403078900b4801e40a80700750b000a0400103034413485041c3e02c59680141500703c0503040c8401152280c00003046e500c1f6000465900300401019409a400401202c031481c020640d60426450300d00c110035031000354102d09010090000e103201040c1250311400a182a0fa0840c01c8240120300e040500da0000d0864060750000d0342400703915400401155011204003407054489400b4402c3c5098101c0d100d0300c5540210011100013130341900100b861402c10b9005500b0180c00b0062000554808c1d9028410f00c0000507030740080080a020384402080c049440c0116602103000314450600010203040140c100307440011a2203000104480301c05410400214481c074144c505040144980d0266880ca0701c1240c0c440d4106901c2c0b207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 184963336 1250 184962086 184962119
    0xc0f0e0106080408072402030f01030c08010603080d0c030615050702011e1706060d0608060910020307080417041d040c1a3915160e011d0406080c010207 67
    0x4c2901460b1015030745a4244201001040368201222024030320b54002c42c80c00658001e00086050b40115499031400d00d00392041341d40415641e07410183d04002140551040d00c808508a07180450b140428403030071401407056800030400c00102d88050750500b5846009425424800c1c4c840c548030001c5150403030320303421004c03c403240010004c5000080040341d41d50391b41d400a02c050b24a90428243d601510180c501079040146180e01c02c004200040c0400c2182c5c00302c071038401d60114136600f040c0b40300600c0780c1d90043c005418189a4401c20140541c0b82080790000c215800302c0441e071044d0180000c95050050302c01341c600980d401d02c046404595182510364102000041518251192080070101e511448880035010783c2444940398065a6910403218021480c0c0940703d900d101d00040550440044c0500142801d0810b0004200760450390704401050b003401c103001c0c600c060708001c601070003298486507006402c24600060445000a8180107445c090b001d691184d6240d1802c031000b241403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 184964586 1250 184963336 184963343
    0x1504140a0f091203020a0306080d0c03031404030c08211005010315050303221805041e03050306040e030d0e0f010b01020c1e0604090c020706030e0606030a0b070c0c0f0e01060804 78
    0x503c0383c3c0798489001c0c2c0e0060131150b2140c1804150703581d0700e010041c1400441a41040400c101458040415a1600c6000880c1e10351a1203404641010b8030b0081019011100007802a800002d02c00321100b41865800000324004c0c009e000c2341d1174090319614884145103d50740c0800c2c1803401e5400313021100e039800c1069800c0a40298202403504804454484980c424103140c0341c2250303c041000c0030480d43c035407070030744000401285504051500c03204003030444030709550380e500d88441900001d503c0011260020f02c201e80110b60354103100303801c038254800e1001c1c10310110303e410300d0580840004a55115260f103114001c114000c481001a6110101d110110380d001030300040e100d01d1200002641a18000b02929040c2020784544040080f40c50300202e400c00b580c8004010061641d06000b0400515250741c0a0052810800b012a07561109180014101c1d00e0140c00075000603c40c2c030790204000e40245507500415a0b9100c9152000c10720b004034102000410000300e181400340f04000e001c2d070390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 184965836 1250 184964586 184964603
    0x8130c150e01050c0619020f2101050303070b01090c05040e0f0403180b0d11091e0901120f031d0a030305040e07030c02070b070c0b04090e010c1103070204051504140a0f09 75
    0x407141555807140e006004600d1b446c0e503090021f00750307100f15240a8884288485001c10030f80101460302144004164800c512035032080103120b0004104418041c1154100103012520302c01a030415100da010b2038100c0a5002208010802000c01600b01c860086029807204103405801c08041e80c4d6107045801120719039442084503101c0341d03e07282d009128000c200803245080920003400184130b20400c09a200b107401c0041c542c060240745c40280320f40144020051740396045070035510700f420101d04c44000f0b41801603200c84e02ea181119480010064140100510102e076181e140281c03240e080f5000d41c040b241c400f0030000f00c03000d000c0c1c0304022046510746c00130304030103240c41840840d50b404048200da800e078000800080c4801d4280142010f88030060003c0b5401802c1400d003821600e4401d4028104018031081e04420070300130044a0016405503808112036584003400d4601240d44810180c005181c100c0d001000c40c0c1c2c0354a0745000da82c070502e040c480076400b0f4000109607180800003a22811 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 184967086 1250 184965836 184965841
    0x2091207230414090a12020a030e01030f2a02010e190f0606091506020c0f09060607110d050c01021b0a150c0c0905070212040305060708130c150e01050c06 68
    0x701402144600041c40892090700c43d480102840c04241c070480110b078010070706007082007449014030340d20100b644010600c54031181c600030300030f21000000906141d40c4039014082500c2d0783e0800d4045038500703c0080002600c03440c3c80c0070480340c0141c545005502e0180c44440150300868013145a809180802150143c55140e401c2d100b040c040c42107401a83e41c0380001141070007030150000100c0b60030300c0044950f18013a00641080d00110b0424410840680c89200c0e40d6039000c4003d402503401d40c0d100d41c813015185400c29050311030060169008441c05c140608002c0c00164904808400303a0907a200c1c11140401e1011400b81841082d600600b20242400102c0d8191540c0c00c3c109094641011400d0341d40d11040e52138240c03504038800c019202c20411003003a40400020340d003041010306480c0342c00e1440c1c403116181c001c06848a0100a070600108007060b5044400180f02a00026084a055a1070741d0003522400741001003000f03c1d00d01c0c0501d80c015070140050761a5200300502803d50340c3d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 184968336 1250 184967086 184967129
    0x7032a0503060a0b0a0801050702030910020606011e03090204181101080f0718031407030605010b040605040902070203210c0106051807030b0a080d0806030609120706090314070602091207 82
    0x38844c4620303085d0413441c4000d001900742005d01600780200c545030050765640c0781142c280000b509421030214150b51040b001d000a0366440342c180e150f656454031140414100000c0704602800d144000a940076080407459000c2c1d007804004029a035110b4120602540e100d04019180040700701d984400783ca2269000032211806102c10248904c2d000c89850409922980c502c0c1c9031240300d00840c2c920390700001040c010005984034032805450307041a01030401d071900500410f18802c0c0d0094402c3c2c1030300891581d0441d00d0030040c080801c1c005460407450840004c40c2c0500d503402c00c180c240c05030340c28400c0000b01c90408030340801184129004003003103650355990550251184005050300804001400507107102c040c491900d046440d0703030303904401c0d04000e0b08252801d07101034410310054004814020181e41484112103580e6800030703000c101d11079141029642c0d501d000d0102805c113040003949004000c52507000b403100c00d008545001d6006410070119649000a0140301078119840c407500401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 184969586 1250 184968336 184968341
    0x316111002070c031e110109050f06130e01120c0603060605070602031003120302120f0702031b0309031b091312030e01290909060c120702010e07032a0503060a 70
    0x401d8051a0805483d59880e510b10812003082041c060009107005008010807024204210340f540c0e00b482c140c1c4081d8203140010380314540c0103501c5486150000f40d0450000300201d540001400c000c8200001036a48251048055030040d204581d804841c0b080880c2e0907000e40300d0f203c01e940190b90b5841c00c1590640c0d6200c0258009408483c50301178441c00000000c091000442c00d20285036405a2503440f1780242d69505600501480d13130500c0c0c56030800105590010a039803500308034000d0a5540140030600605610402a005400d801001303600c12440303c402440007401c64040e81e49c010a0b668014442c40502601c80c03008000120b00348075a40c00034820b420644280b80c24a0002a001c00d42d40f0001c0d800c607501c24403d00030102801c0d42c00185191500d05070b40c0c4851188003401c12407070100610310311441115001d0007440100c0003c681042c3c400d40c081010300c0b031342070103c5d880756840f403d28801d600c80d07560078081c000310301410360303140b0320841c2c403110b001c4600240041000b500d903150810302 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 184970836 1250 184969586 184969597
    0x7091107060b0d0209040606092a08130b040b04111e040c03290f06160b1504090506090c0a0509130204090c030807020906040203130f03020f0709020316111002 70
    0xc1c01000d820040d405a5517512415024601ca4940014154030b040801e2090b12000d44490440a82403c81945002c4840501c0c2081c40498a440d01082c2c3d10890080f01c0c0721052580600342e10301d0700040000b00203c800180d4003031400ac1d50b403841c03032a151100300544024070066200c26002840d2400c00c590402d0f0704002d02e20036040c24085aa641020b10600c0c0407030405807080003601603000b100d041d40c10f20501d4521414010b590007443c2011560402d864a840710313400810300203060700056030345502e0102103900000c0050061040b240181451940c0e1501522494118003071010481e07080d16049290748200c40000c0e00b024039542c0c901c01c1e1002d0410302e81c913080c1c0e0010b1710340015100258410341d0301400796101e84030940e1110724034018000c0c0d0410040c4900c3c0a107104100b071203c0228941020640207034000d100c0700450045280c120f0510011010300c04882c40703001d801040c002c18540113144281a0b42c0c03000310f0800d5200b902104d8084010340000c0641d00001d42a080ca003000d0f400920 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 184972086 1250 184970836 184970839
    0x8030a0216090c0e22091b050a03020a030b0a02210403021203060310050a0609060602060f010914040803090c1e0f030a080a0f050405030d030504060b10082716060207091107060b 78
    0x2414007590034942c1701038a030140000c4a00e601c1c5c03c007007654640801000000502400d81d44602111304560209407008468000500f505080c880001c8040c1c01c07a07012118000764105000c11002540c1c41c83e9840c2d03002c2a00e00310090700071186950580383c682c0c001c3d02e1080340020000d1441000b58002040140000792803072208584403600403c0c101100d0245200400741940103045510b02200c10030380d14007040e04607840b031500b40260561035006502100380c01c1a04886c88035a03e483d40309a02d460511025602500842c20706a850016100402d000c00c40402c1600d16800305030711102010b4403003c807802c0007460807005120122106200f14404000c00005050240c0307440e032154002480c00343c4000c8118006500e940030401001464010300641c104240c429221025410340003034410080101217001c1300f01c4070341a6104406940b40d04180522611042c0c961a0414000f410301981090140c0809482078100006100000744155000039030484c43e42c3e800c03c1c400d0b03500c50010300540c00406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 184973336 1250 184972086 184972129
    0xb06090c1b0c0a08031207080c0a0e0f04090602181912080d0e030d06050d050a030f090e090105010806180c0d020a09050a05090d050c03030414010608030a0216090c0e 73
    0x11410b0b07103c0412000103018610019901c44680c28421036000030010405070401c0600d50a110000e030f881c00c03d5800c0c4144504015211030009404905018540f9540c59845401c101144050001710b070300808040e80c5600152006a20380c0d170600120171380005103c3c2c5503541d603907003c0154401501c01d440c18a84102401e610b8103800e842e6290984880c4002a022034100040c0700d00580360522881e0000d000a4034103214261850b2249a140ca05440000d8180b1030313091881031406c0e211752800c1d00078100c070b41001b030b141c1c0c208060818008c1009004800c510b100d16404200585002c469204004041200918001c100390041c0325107407061a80803600450700960101c0e4882c0103000e0300340300f11441c03400000d580c5058000b0740d143c4089844840700380502084490b41c4481d003c000c4940c415000041c8200c20001016a180100b40e0350384046418003002c01ca03111080c0d40818454441405810080040d81c1c981d50f000b01141c003070828540c0070400100e0f5841c41c5007401e0700040c1c031140045c92030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 184974586 1250 184973336 184973353
    0x806040b0a030b09071e0308030708060f040e1c09050d120c0c0905150103050c1b0703050a032003181e09090c1203040f05060d02070c120b06090c1b 65
    0x210003c2143c00d8a10420f5508201000d101e0150b900034410013081d15401101d407010b185407624910303480041e00100c200050407001842070385822a03551907556020700700300a00c00300702140580320f160b481498602c10300e40c0715185650350300c103a41c40e50681d60b008002c900c0313528850ba590700205d203c10f40100240006090000085218a04400000c01c001000820b00703140c502200b0711400c0f039148180c0d040c545844e003031000214003401641d410850f0202c5080e49113250002051074940c80390710003841441084641c20401d81e201c0382102c284100290b6194801d091944015200d018044c0725407000c07030034030104000c0351a0202c441e04000842c0040880d0303150f100c0001c0b40c00141c0848641159034403440302d1150b9030802c00d0000d00d60700b100d000030314240350803e604428841503a00c50a0b1050002103803180d880c01c1254100c3d1074441d403101d03100100d2aa9500e4002010700d0060082e101030301c0702c41c0001e503d410702e42c9200d880760b80c0c8056813518051303c03424040c0080400f08c030803c56922a04c2e41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 184975836 1250 184974586 184974593
    0xc0a21050115030f0c200a0f2a06020c10030207060c03020318031e0c070806070e010e030607120f02120103080304140a050d0c03050c01051f060207060806040b0a03 72
    0x1859001c0c2c1072884410060600c0030070301409840405403001841d0b4500302404003020340c0301510040545070344030304103400400380d81c0c01890600203050103010f20003c8054501001244072603d8444803083d0001e41c24000300c0104884602c030203108040147e0000c3c80756040b03524100d90311648020b06400c0040c00c110894546034210340102c9810f0780440d900005000c42541401c81e1904258802c0004526140182800644034207001c082e10281c6a4086280b8008000622038540945007450031150380d480c01c54030007404484c040d0f2082d40407a480f01c80d40991401c1c0841c2e45886064241c44440000103035420940003042c00b031185021450b400d101240001c0c0185030810b0095010700002912420141070203506d09180301c400c010759510400f2100d0001c6c40204111241d46d600e424151303007040440c00e099800d80310b01c0c0301a0754903504e07040400900462000070582880c1034407140f9044182c44510980e03031031200f4043c800124104200041281c9050340014008200145c03880000940e42da4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 184977086 1250 184975836 184975841
    0xa0b011e0206010f23060c0109080c010515010f051803070504090b010302090619090b0409020a0b1e04180e010e0a0308090d090e0c07061d0703060f02030c0a21 70
    0x92414016000b020040104c0d8462202960240c404a9002d54000055a40702903c08016000c000d0040a0105500150010a40c040c110b91600013181e03654884010078000c0c02800e08980000e168442800780c01c10a5104031002914200e058859500d00a100e084028241c42c01d410300710380c98400e81c030740811651140e0166008080c450302400d102c9506510400101d91030040445001d000c0d15110304400021501c0c0d46c5040724040c1e0000210701d000080464042c1c00680400b80d01b000461a000440078080c5000300301410328807100081c04c110080814103944164800c00d000700701005018080b04402e1f9020540c0754003030030f00000d6000c0e400c00a02d410104d81910035008a03c1500420408410500501d04c95442c21326090a80e1800c0c901c0b80f902c0f955000c1d021200c050b101156807003c008150344001707a1691011803480a0500c5075080584e40c41c00c034082183c440341403c00c0040c003440e460003030ba40103d4407140c440f030405506102c01c8428202e00d032141408070b0174140240c3c62720703a001d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 184978336 1250 184977086 184977137
    0x1e0d050723030d05030f040303020702090c0703020607030603121209050105010b090310020306030d120207050f100c1112130b2a06060a0512030c01020f09030c0a0e0a0b01 75
    0x500c1071030900a2416503200301011100002400780e007080307102000460707004007166070102c0c841300a00002c1c4c407035050442c000c0c0034410f030003500800031105010109040302c004c0c0c16118420703402c03140f0719030f580c90084054680d030780b1000301900170b100c0040880900400801810356201140011803c1050b03c0f0a425180207a11071018000300142640300c170305080c050f09841a807202400d528500b0040c000c20f50318500f10200d0010441030521091501c1c0d4036804455440e41c104089030714050501c04c80c280c40d000700301c06010741241f400607011491409505c2102c8480c00c540f0162400c90f94030149503a069002c03080200d40c2006040340490164210b0f00540070307006804405010300c0c1c1d50240c489a58a8010052007600e0f07201d00200041a83d445c241402503650940302a0b80c5d8072034044640345180500d940e010955400450030700c24003003c86014040c10001103045030f031884280c2c41409034581c940d0044107112a0703600001500042070740c2021800c03040614107109544040c031811151800e25 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 184979586 1250 184978336 184978349
    0x80a08041401230c0c0303040f0518010305061315021804060909030206040b0601020f060118050109060e06040908040807030308101418070e090118150501021005040204021b0304030311010207021e0d0507 89
    0x220302c810300c000d08042581c0d801031420403111840c4cc5d4116116a40ea4240c001c2c4100203000403050100f08000c1030850b444200c040d42c00040d500d8900c4205180c0c003484011071814003c42c90000b0001301e0301114000c80d80c003690960007419003a101c5451304114144004d003010b042d840350b2203141d2072440c000c00020f4001c000b45003030b011100280103201d00c1503502c1a84034110b1141008400d024841c10390402e5a0441e0342110700107017441e81460080d005010320340c0702c48003502030b04600006050300500c3c8103224172940950012000c0d2111148080c2c0c00350f50b0704041e00980820308141e00f0018582d03c40340c0048480c2003403981840040c000a20a0000342c000b4404c00c03031001c0e0b40c03c0c5007a040d401036180c1012640c8a039031130941040f000075500c1c641009000c072140d488001040a54440d0f50448059000780c0344032002c8a080202065501d501c9032008030001441c0040000041c0d00620030b84c0d80c010b034010000142503020300d5445041454030740c1410f51001507291450000b030020400c000041c20f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 184980836 1250 184979586 184979609
    0x60518010b03030a0f08041b03080c0c0a0f06110a0602040f1a03040b0403081503010204090c0f1409060a18150f0906052b1a150403050a03031104080a08041401230c0c030304 76
    0x3000342f09207050070748422003e8001c2807400403c0c0240b6202851800c19944186080038407800081c00c824903080204038040c060380c1c0700040c0402c20286002842080d201d452422020044541d02c07000030921048401403c1201e000c8045800a88a0b6402d250800390795000d500541305030340002400c80c0e000e540300b0782442e0380d42c04421002907003000012908800d40c0c14900074030a60744121410a10800c08494494403000809140c10b03800381c58003605441308424420b420b5502c1d10b130060340d00281d004002c0c01040c595611002c13041d109640351001d803280741d50b89030f05045482e0880007441103000480c1c402500140c04901c1c038000b00f446140c1c080c92a8038500c44519184c001844890245440025100d2000700424008140f000031201055941032400042e1464682011b000502441d0414001401852040006c0c01100400f500c02d4400c014040d1008c0c0440b2001510710904000059200b4459560031031000c0c40b4400242031448000c100b40c60200ca18600020b0075540315400071100c066 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 184982086 1250 184980836 184980847
    0x62106100518100303110304030606150311030709051302070b1e15090c030702010608030409020d1104150f02030f0c01060305210d0902010c060518010b03030a0f08041b0308 76
    0x509145204503203502e02c44216500c0c2005840c0d03500c2d60340d2501001d0140704805100f880c289608004584c001c503040403003080500c3d1910303641c0490404042d010310000703040210600d1810003402c11a40968125101d8a0b040c4d8030388414044c4540312529008203407035084c05600c020585815002d0300ca00c412801001070b1038902191281c60500180c10300e5011f941486035190035488220207650008011407100d0384903943c50301d04a01401641d00840358901012034009415402c5801070704102a10a1044c0070f03a07408408248540d0159100354014020f0344180250501d01503031080c00e0b000703030741e00c1581c0c50807400b02ca012107175078401582188283e54a010410900c2000d115070005855071522440815031b6525240070680100085035900c141d981010004680c002ca0001c100160300c0082400240340804585c0e00f0010300d604610300035400c2c200c3d02645850080101d0308585540d884520303102082000858004000420440b914a02c60320910b80c83c1241c0d440d0314005510640700159520f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 184983336 1250 184982086 184982089
    0x5010e0403020d030c390308090c0f0121060e180616090506030703061d040614091c0e060d06180b0604060302221403070515030621061005 61
    0x31005002c031001c0600c1d000e180c5a805611080c0e2007154400006640006d540d2952001030071745808003000c11061101858504143c0c000300058031900076102680d078406031340400d20203c003204d84c9447e400100006440d00c051a000300c240d0040120f4008006001c944032406489040703825900340c1c200c03440300c540000500c40b0030060f543d40419520400c0302100702102000d058842107018041c415100071000030f141601c00d5024000401000c10312000d41010728030300c0740b6012000d907002e44d101401c040d010b80420300c030608041e0280c5000030080202d4012034500e00844000240c1200802807880d861040641d501405404143d21030800050309078a4501403a00380c03800595203810340e90a06010506907614002a1821124542130150760380503550940c98403d50030460a80c210b003050400454100903503106041c0028051703040b1403c090702c8100b005503000c00c00d20300940825042002503090308140b000140307035605511121908030702d40203c680c1000c1c011a10320300c1d0090001800c1111303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 184984586 1250 184983336 184983343
    0x909040c051518040c020312070314060108070804080309010b301f051306090c06080c120a091a0103030e03060a0b130515130e0d030c170606070605010e040302 70
    0x21921078082040c900440c3c0c0698220b88600c1050709446260b8400d850700034a0300038411034010f8a110a46180b29191241d4054010407080381d40030030084202c0c0000d42c51354024100c05006154940ba000c44c00e554030f980e030b00156400142918950f5403a85001c05540d180d815416490040024141c2504002c45800300c0c1040e130103011494a66110700e544005442e440e4900014030102c009001c240b07591303003851814101290243c020100c525004070081404600302c52001500c2d101d641d540f040c2d0315500c403c90b10500a140c080c5160407a004045100342c00a030303200d114103c1c4205e0b80c64002e40c00d00c0360129443c40090f4800c1d008104114400300403071601f0700c800340d400310303640e00200480003601000c644124001d181a00d102d0750f4a00114144d018041741107060313110700400080c0200890f40c2820b01070403403240c4015251240c002c494041c1c50085c01510132580c9255602605209841c2e803050840c040a03100a42200c03040111801040fa140107240c082c0c4880c0d450b130609400c142c58000c1c035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 184985836 1250 184984586 184984609
    0xd06081e0604030503070f050906030903090f01030606090b07320d1404030308070e12150a0b030d140d0603060e160f06120e0601030b10080309060a05030c0909040c05 73
    0x1503000407042000184c2c2000549812540c58a40440e802d8003100041d5501d103c0e040c08154400004820854841030000062001310020707191926011100c00c0103505891041c010b0b18041203224000f809120074203006015918080c41038001400c2c7c00c1034641418010030b0218441103845ca4a0311040d040f81005060209000f6140611030450209c91604603802030f8000181080846d038003280c00710384070b07404800000301d00425081c944180c1d4540d040e503038400c4502c103042c04001c442c0003514008081c49540d6861901801a000031510703035804075880302e0b041030315086886040c054600009450b224000c0590312403080000c180d03884070071052030003a40d04500500013240c010184040e03580c1c0740080d0121550303420034005c000b880204500192051443c03200092180400001c188000060741c240910000c5602150f840d841d0b4000c1500c91041c00c0886030448010805074551610070303070007103a000850480042c01c1c0803803c40000c00d64002903e00b0b60300d031800800103102c0c6142c00f440747204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 184987086 1250 184985836 184985893
    0x5010608040c21140114010605030702100506060415050714060103060f0b0d030809030c0f010f0507050a0207050910091d0d02010b09130c0b030108031806040506090d06020d0608 78
    0x105243d000d54281000320410f600a14049003580e10901c00b81003500070a80034511500711180660711810010103541084540c1c8006224840002d40300c2003d62080c2806120080c1440345400d0415000445409040d04500c04003e0b04111b00808140120241c586d6002080050001540345042100c1641c3d00c0d00500300c6d440d8503215181c1c55554802d468040704640c1820210096540d917159913086009070000d9a1180c0035044407888111410f501541000c4880c2208000d240c9407c0e5044540e40559410075000d0780c02284144842e217868020741e0340c00250348081c403040c0c6480d00b401d5001c0c1d038100d900c8103881001440d80760388100000d2080095000061000308400d4070280002a0429006040c0c20140f0b504019440c060207440741200000e032090041007982c03560348500c65540c80e401542212418125004d02514501e041402c45040b00d1008201c83c0c113214501b4200403401c10410022101d10b0781c20450781c840083c560103410001c1c28000050106840c0c00702402000903940b100c0c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 184988336 1250 184987086 184987109
    0x1260316031409060d05100519090c0219081305060a110c09060d0f0614040b010e010e040308190605150d0605030303040b041704050301050f06010f0207081002070807020405010608040c 81
    0x40c0094880c002071758149140302070045020b0b02e48018500140455422294020350806a0010404580018a02180e25501c2c00b0002c0c0901c10904a13100c2400d042604660384005e814540807800d078a01800c00e030070305a0005500c070f41d500d00004031140d01c90346100d00843c0c904400c00c2c203000c00911100c400420300351079a660610b84080020180c9012150080901c0130102031801807010035400803d403d4a00517542c102400c3c1428202042d0800348680d8900110f580c1c004103402c3c00710300e1028000e5515444109240e12482440e4680a031804200c0031181d44e250000a1280d50316120080040e02e110300031903450b50540785c1001903c24a410280c0294000c10502c00062543c68032145d105801512661030046c2101a8100c20b114541c0055070640c04c0005100354124031083c2140240d100341c0782d8206402648000303a8903410181b00d20034454101c01034003525803015400a1104c0b42c03144050500e00045540001c2c01c440e1b0030380064001880036000c00c01045520044c10307002d00140b5010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 184989586 1250 184988336 184988347
    0x140601020c040207030221092706040c020f010f02130906080a08070206070803070504060f08070207030b0a021e0d0b0a0b0406030b1f030b2403012603160314 69
    0x81e607201c20381504140150343c002a0041414401e001c111171010301070003030141108900502d00a44e03000003c1282c480c043c903280200040001e100c541c041c00c00380004800d10355940f42c0802008184143c1c503042503002c1e4000d1030312590800e108450b4194070f600c900503150900c03142c11100900c0709070040e00c8541d161100902c152035001504480e001c0c0d020088603505e2210b0b2002c2140341c0503005004000320004400d1001294120000d001a12081c1d03643d00c03408410280200c41c1c004d400e9030940c000d41c01c440c10a00100e0904480540e001101e40409458103407100c0c00c4c1042c000c0841503011001c5804228003001c1d1085014022104c0402c480720581c007810a460300d07415106074412a001d040c0d40c1c0b01c5c1600c1503112445038904103039251482c000b11302003007580a00a0611804414840c07004c0840c444400c4100c82c030b40304003e9845442e07040c2140e080182c1c1c2a864900e10000c4440c8d0420300078500e51301a0100010104030802d0540440d0383c2380e81c0d04d805860322481550080005105121 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 184990836 1250 184989586 184989589
    0x1602030708130312030504031229010212040f140a030308070804050c0904060213291303020307060906140301050d1e020913050c060909040f060b031501091406 70
    0x195004141c200c0545641d81c00c1d10724103200780c0051544020841e081000d510300c901034055000d140325602079201c00c4141c0304100010802c0f200c1501c00c1442011600200d030401449804400300d21703810600488416402c0100c04582c1078016900c141d45100701420140464807102d0300100319450207a80d010041030071590040c10050000300150f040041e09800607091104c00c01060351140006800c000030b40c141070418201950248a81d6600a005481c0000f40070104109a08248082d110101500f000107140700c4074590141c2d4000351a54801c140110150740c083c04848c005055948614080301c1c50404050088060180085c000c42e005000402040d12a50030316180d065200104501c1181c00d070b02c3c90380a101414801075001001401081148030396100241342e0180180d088a064105540c00c0299034800e1a66040e04200000046800100122280117aa51140c0c8010503180b0010010a03c1d1a04292820905c2000d0100403c1040868441c0e0001e200d003020303220109260050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 184992086 1250 184990836 184990843
    0x40b0f0a030f0c0341030409110c0106060504060f11070b030703021306030c030e1b010e1807030b0108090c090103080a1101060f0503010b0d1707020f1807081602 71
    0x1c005031480c00e00030400340c10005100124805164044014010b1510120311002c820b4050298030160000003e854000c0303013480161412000f030300074001d51501e8107003440031005c1d001c0708844086205003440203083c038810170300810300640b500d5650a9140c031b1808200824024040b040042448122280200b110201003000d0080c0c074030f500c81c0c55035a5111154114020b104641c0403d900c41034050022400643c160003642c8031b8151a6024000c9000002d00c01c2c0d201c07690401e16000d011365521010361554000c4805010000c4018004540d594240719600a100000c4031f01c10300096841c80c1d840d40542c0c00454080d001044c0700002d1000c0c00148000c105040410b00001d80701c2800421030002c2070303100d0300c8010140d8040341c000b4420f8580d6128071402400305405114072030b508001e044070b0f990900180304a030a540040b10907103211051540c00c0701650124900b660041c03801c94001030980c84141502002c801401c0034554507162054000740301c646c0240441d80161003e0000007009580017 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 184993336 1250 184992086 184992089
    0xb0712170402041a10020c011e08130f0803070c0b0a0203010308090108061201090b04150e0304170c100809010c080105130527030c010c08060a0b07030c0b15040b0f0a 73
    0x54074005401d58040c920200c4041c070070541c040d4000508101d117001d0f66070219030486454001c0e01d0300082035a07142d098a031480812030341c1d06d00003000c0c000015841300c28440b05215081c09901c42c02c10409840d07c400f9280d9108403040c0000c039524000d158200006038001680c880c840d0501103045505580d280d203010710908070184e04211282012a00560300c03c0c030105d1101200c50000c010000c0c071880c0603c2003540458007500c26548110820034804824010b82100766080e1020f1490301d801c1400a603215407000760059142d03c200741100300c1540b41e45600702d10507803a54940d501ba41ca070000d695070a40f081401740707000308900f50004000c02e80b52a00b007165901002d00011800d50b540e03030060304201d0031006e041c00000341001c110101c0a200403008048a900c980003d00c10802502d00a940b40740e815038800741c0041019004014800607a40a085854424501001340020584803a16010401d41d6a00c40e084641c0c04803803000c1c5042d11480f07650318400e40d100301e032441c1c1400008131000142e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 184994586 1250 184993336 184993339
    0x3120108011404111801150e0307140d051006090f0e010c0509040b04020c03040321020606130504061503210305011d0702030c0312011a03100b0c0a0c0b0712170402 72
    0xc0405480480e680c2905c00d600c900302240d003003031503903a54150020600244407808404166105081401400d0105002e020785003000c042035103040e1507001f84021003484c01c5050b5441d00600f00000c000c5440c60081b8002401e0300c0c80c0c00308480c0701c0d4001210480341118440001c9a16001250248503040402d03951b070004201c0700001c61400c01000b1401901c0303030724030006450100040c01b0041080311036401c1c14408501d080c2c1c02005007204804c0c0e036203000c10fa82c440e81c049605401d1701119940341c6c12041e4410300c00d10000c555001c07885c42203003041c2c8958104030340d04c144100c60800a0a66441c0440c1282d0041c0307010b0216516100f600d04490403c02c3d405500b901080001501080c0201b044030444000041201e82c4e0700040c1d806c111007240e080c0241405007c2c20404015810303010b00607a03006859050601d052240f42c4503550185a20503c001c440b5030040748600c602140031a00184024450050304070342da140546844595078290540340d00510810750240000c0c502c1410312079501035030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 184995836 1250 184994586 184994603
    0x60c07090b010201060801060b040e090706141b1b01140a080c0d02040803030a060f05060c100e072606130302070b1c020c030a020606040c0c03031503020607030203120108011404 78
    0x1d107500101e014280540000010350b080460014006003450020000c440c841051100242c840b04940d60f101e00483c400e00c0c002030703100d4041e020381095900080c401414481c0c50400c2500d8458a52401c00009100180c5c3d49601e0741c513210307200d5030400b0107040144260fa90341484c0c1200c00c4805404820081d101c0c03a2032000100345840b5400060b411940074080f001c046039101d2a1829182e00580605c4c050b625051032038440000e000d041040580c0c0714030700060007404142203001d03904802803811101c40c8031248511703c0300048842442e202240303040b810b07076150a402c0d80c1c5180641d2420f030700680303480712105020010b0004a41c0c042180b405a0703036600c40140c0d4442e400001000c1c41ca81c104050340c2c280e480052100107414000000305503000c2c2c65026140e12750b4a04003000308403a546102040812254030800000901c00e61044805a5201e1601d20740344bd101e40102d00309070081003040700547d200107070408541c241c902d951401400000000e02c1002002c18600b080307142d018000914a04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 184997086 1250 184995836 184995851
    0x9010b01270b19090509070503060603041a090f07080606031507020c06040f05100306030201050306120127030908070513020c030c0d050a03060905061c02011b061a060c0709 76
    0x1005080101d00a1036500d24160703e5603407282694401241459040c4081200c6030350024031400c210480e00e100c0c08140c1c54503815a60b54005200d0681e000800c100c0300b96004004a040710822006028022981d0030010400303425519400d91030b001c41504203042c10b0380030908009aa5a001411260f1514456401c00094442c45c009070703d410310750b0344ca13903a001e80045008908404003c00200403260201c820908421002100ba4100c40340360001034005182000000c0c240c1c00c1003946c0c0c1c0200f08403a000011401c142e016030314807418100380600001c0401081400605511008080c0a804080301503c1c00c1071078900000d075071414402521502c281c0124810a481c1c0040c0243c882010822080c0c03580941942d90040c1070781d00c80f4085101013803900c0f0020854500c0c0d0320600384960405444c00c0511a042c0007440d240d8509014200d04201c0c1c41d4685011490b81401c0b102c0300c2e90320a40000c140e400c3c29804210140340310410f15400b0395403c1c40303910300c440300001d0400c00f01c2d01880000101c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 184998336 1250 184997086 184997147
    0x70e0105040905190302060403080f1614130b03010e0c03010803090118030219030605010b04030503040509131b14040b090703090c0f0e0a0b0a030203030a030c1e0509030609010b01 79
    0x21244c2c0681490212648070000070306801103410343c4114800d07947ca000d103a0394500600e40c4036405942c14a0402c8060700324101c42c0e400307502074030003800c0402007060411201181c41c1d951f01c002508000d02c2c070203010004000d60b1324100800d40e0081a074014443c107541c1042c4003150350f030151004c01c9041001e05506c42002a0503c401c0300091500504900d0030f5142d186010100c42d0700a01c42168102d140c84000680c80e400a030a84054907403040c095803425151404010003103d01602850081182001ea40005107480914012810000300e40481080c03400e14240050140002154065401d0205042c420364076414159401100e0781400170311440d00e410301007900180d5810035a94420501c0d008a43c402004908a02c24100413000340001103600e0140529082c0a11000b5099070042c082c5442c8203020b034109450703008091801c0c10601d0030781100005a4040464040046140014906507600742400680d40c00800a0000d2000ea820322000038040660180e1860000320a005540d640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 184999586 1250 184998336 184998343
    0x60e0105063f0f0129030406020c010903091a0a050316090b2a0c010519120906090302011424060c0307050c010f091503020c0c041b0908070e0105040905 67
    0x54605a0702071948000b0102c2d066440c486050703c0303c4250300d04407400003c803c0341c0070000221481100b41080c116408980400743c00d43c20203401111641d80a011840d03485e40c0034400c90b642036010f55122207407103140c401902c0815090110709040380b40f081044207046600300c4105d80c0c001d02d442400204000c0716010072204e0f02d51903004052194400a072003c40640740d034140e12181010384120380c00c0c840ca415210341e540d0500caa55180464014080c604c00903540f881c1c030342c5d1045814100b1590b00018070700e0a004561980a007100c015589800e800180742e4248070362203048554100c0041c150801014100e60a0752102907101c1c0390b10389407030f40c00c515120740060391a02c40910701169140c65030f51810503150b00c1403021003800226860040a68503128001e0082143c2280694045407484000101c02a40c0008502c81d960721595807468510340341e611640c94254000034612190600e100401440b00e40e041c0d201c1409680562030a105a80e00038048078112201140d00081c165071134900b02c1d0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 185000836 1250 184999586 184999657
    0xf1c0804090c17010f0b040312021606051306030203040f110a030b04031e0c0507090b04150306051b03251704140c030c0f0906010306050d0c0e180a0f0303020f0f0d060e010506 77
    0x1003502c400d2034001601900070004e1b103b03068280c2d01050f9856142c1c0b104501324082283c001d84840d400000340004265500c1c1c03813418504001e04001c800c42e449031507082035680141c400720f001498022821306281620f440d902c5c9101c1c01442c0c410015000340e100c060303481056010710300105545140d041900d40d50b981c0441000d0b60000081c5580954900742640144822a080c40548804003c0c016250401a04903440346050043c185080300d004400c03200c2c402a03000928051000010500d0301100602060512a91103000d81c44070b0192220003007424a0b05140c04c144c020f600c14404540c0351398503a1644c02507144141c80c80c0307040c0d56554004802030216540702a0f00413040181076018000011150400c0d101c28400d1024207489000d068064410800425041d580001d1000c4000441050f400c1e0890340c02880d0250030441e10502100f46548240c0d4030318000d0000041c0c44d0b603030022501403c002031144603407810641d8500303008038a01d44a1440410003800031600c0c444c0010750503070324808 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 185002086 1250 185000836 185000863
    0x9040320031c150b09061e09060d09060c020f15090a06090c140d02062d0310030b1803041703040e10140f1c0804090c17010f0b04031202 60
    0x1048010702d003125401080201c81e03104101d1000500070685280780b408592007a00c01401c2e09190940d590246030072401021843c82c04003200700f01d0762410383d4560b0054680100c03114800903920380141780000c201d640f203200e00019034000f0481504e0300e031004910401ca00301d50340b9101d900c0b956003009190404940380401411075240c4401c0b501448101c00842d4140c40c004000c041c1d801c2c0340031081141307102007201c00940c00f40b070400034608240c140340d0240841207500c030054144404140c500c04030f29001241c0003c280c0b42914020001e10141c0040b4641090300c001172441081f4a4910382a140d1080f80500084030701c030707562002d84200d020000c031402850082c001140c10b06001c50750880078030a51007140750861001d105400349161484203550b0004009101550343c8080f800e641c459081000c20a65990805103c0041d01c0016401404144400b594990f4248082d0381118003c80006812000800e1040c420074403212101030100c0b015a50082c08034800690400002c0780303885082c11060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 185003336 1250 185002086 185002117
    0x105011a16020a0e041a060d060908091f0215040803040f0302150709060f02011404060b190806040b0f0f01050f0a2d050103090c05120708070b0a02010b0904032003 72
    0x22412000034503140546d104d000265401e1040300c10301a507200c001e41d12154041110010b00c2d0000c2c0c0c0c84c0d4071a00c10248580f48041c104070741c039400a16214100840c1c440300d820b251014004081d4140945800845e06280e65407003801e054580000b14000288001d054840440302541814020410914400c00c00c407c036011a240a260040118000b807007081c021403804074600b035232140180600c140742000c4081c944056595a00c88802904050051940000300c3c85009a4050700f5501e000b000b030400c410052a5604103842c03c0103144500034000c0d5010100d140921140c00c40440001d811504119122003d240c0c02c1c800041000615500c04c88420804a07680c0c594012240713007400814154464544c14075944800540640d00c40440090601120a105011b2132500084100c0184440c50482c0c9905845100503032a00025030040e0a880d00041005281c0d01d81c2401240a03030342d400d449a0b0081c0c14540d401030a9038484402500c1241703080d00300240a070108105440c42980c611402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 185004586 1250 185003336 185003339
    0x20d0207151b050c2509110408120301030b150102010b040e0f1006080304050402030a0b0301020a05030a060b0403021003090302010f15030201031506050304081602040f14090105011a16020a 83
    0x301c00040100d0140c0300601d10070700380040e000601400c1514903001c0c60310003030701103c440441c071180303041001034004d004041128008210301130148aa003414400c003152985d130365801d151440340b9025904240c0085084100014000141001403440d04880c000c070190010307204680060b40942000310721907411602c2c0c420310031045c0078001500c8604040300c2c4251911003281d0020032080d1022402500703850392082004020a0805d0f030300075640031070700100000d040f0304100300103801c1ea4020705e0041d000500110034841000c0740c3d0320610000300300c552049427030141703560b001c264001c0c400240b26090644c0c98919105050017034026021544428804200940e481c000000042c001800141d0000e0700e0105d540005010000c030000c2a2581622502e0950742e40b0390b98400f055228400c01c000744140000e840e001a16540038044446c0d605140c041071b404100d0000609e0807074000c0c194003079681000c0c0104026210814003010426410511030b030f8520000c05040c0040008803002508903142c2c400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 185005836 1250 185004586 185004623
    0x23031e01020f1315020a03020705010e060c0304060206061512040201050a05070203150106030b01110a021203040e13031101090308040201110a08030405010506010f0f080f0703060b03041103100915020d0207 90
    0x807007000e40f91341050007000180f01202c1260b071105241c00082c007503031090500788415070040360384481b0f0b0b40c401032480b46005403006809046401a900110241e0300c01d900f072041514000c022000c8c3c2d0400941064104022804000a001d40140000c3d051120003c2c4902a091080703089651054018080303034800d100008084070414800d100b62000240390801416156100e0030075513014504000041480c202c0070340070002d03081c2c200003076194544820440045c068910704250380c411907c8508100340391240e07042c050301003810385140034410392506e10001c00003500f20640c59041502807900b40542106c841d082407400440e032401400e0035002004001c2000300542201d449031030f007a1380302045115885019100b00d4900249100402c8130040019200c0c040e5440c80d652005441c500442d000d80c0c0e88954403104e6106560560344801d0700b02d40c0e40048d0034200f0601214811582003000b0900c079548a41d98180b2014010804080e0002000c002181003601622b26541e00040000a002c81711007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 185007086 1250 185005836 185005867
    0xc071b08010213060e0406030c17011413170a020d0c02042003010323030a0509010203070b1510020f030414040e07120c0501020109030c02060a0201060807060923031e01020f 76
    0x31403440004d0517030b8095a03243c10140078050440c0d6000c20501c0e95542007210350f007070718150406c2500c010f641e5800742c0007400b601c03022214015450941005203c11480c2420348090b0030703015031003480710010042806000d41c0010603513044a01840c0400d0080c00600c00075018048004180e0301200c200c00c04240c0300d80c0d41c0c9c40154120703485181747d02c000d005440315101100740818008441e0750801c1c4002004240110028500071105206407450f181c496942c4040c981400c1ea210301110341c6e07040c10315401e410407101640b0050305500080c06446040402030350342b446a4001e9400444100d9040d08031901c803500403041d0210b8184c240c41c415034888101002a40b2114001d0701c014081c0701001403254010f1207400c13122030300350740d42c2901010940c0920005621070000c007011590307510701c0015420410300400028180c156105c9480500d000102401ca080c0c450b200201d1000c150b004042e1641c00083c0d9850306a002000c2c802446100d028242c024001c8100b6500039150000d00c2c0c000912040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 185008336 1250 185007086 185007089
    0x70201020a02160b04050d06060503150405101401050d020d0b07020c011b0803070503090a06051609050405091c12020a050409060e15040203090a06090c08010c0203030c071b08010213 80
    0x82c0d007140c042c400082d45241c840003c41c440c1e20140b400c01c00091107141000b0410707001d05030003000c001c07070503940d501c2c007003880c0440b425410f01d1104058814001041814050303e03801e2840c4090070f01c50320510741900590500b06114072845242018012011501d48114022010390000e44502e1103141c2131102940f1981c2d81c1c0c103500d0014102085494640001d201c0030402c85030801403890440d40c9005041d5041d60019100d0107092003980e003d000042c04501880b880344409040364030200c0502c5602034654600e41d0030080c415400c110410200e00b9001800c0204c0d4440050640341030400c604066459054040f0817107082800003c1855109401100800c11520042001c01000d039031035401801d4214107540d901401e403101402c000051515401558000c2c3c044802d44003049002c0e41c40d49d01b1901c50320b20848044032080c3d404c110000085c4a0002014202e0003e91324600e09210103000341c0c855190020020700d29071800c09030488018810303e0103030850718000c540d0762501c3c0303a1186044e260f5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 185009586 1250 185008336 185008357
    0x15040501030b01031407060219081605010606080603191707020a0803040f0f0605030a0b01020705210c04050c03040807030c0f05060405010c020106080706050c0111120103050d0216092307020102 85
    0x117144100f0381e25400055003030b0032a0314a502810071074140c3c81c0000300d4001c0940f019240b01ca001d000e116010915415070f907000a10403000042c00c6850035101801c200c000406c1c0c80d100e0307008a01059403048081d00038010150740020940d0850107410344100540c000d00c10f000c0d4015103940000f0900103000401403080e10300c1404c8441441c5d50b40c00100150040034064400000c03c2800410031307850701c541103982e0144050060341c40d51900c500200e101040418007607402c10320518031100c1c00d0041800003840104003070b40c0600c468030f45141e0304016884003810081c0300c003000082480c14103110f041c81490b4143e0001d00201280120300f00141d80f40000c0d01c0544540d4079140303c1c204d0107401403081004076881d41028003621454140709540c0c90300110b8a4114035500d404012000c41c5c000d40040c0b1001c0701e00e192030802541107040081c64001480b034603005662120020817100f4030000698021a0000304c40442c5000300039129046c3c4005050b03000248412003030503c820540c064000d004c90825 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 185010836 1250 185009586 185009603
    0xd0c09090c090b0609180a1d0102090111060106020a02060c01090b0a020a0206180c01030c02010b2707020303100902070503120709051206010b030708091603030905010305010611100515040501030b0103 88
    0x18043c0c10866a4429590620740c03018101c0c1c06051542011002d29600282e207190000e00009050004107121460030314007075440c0d40c0000d0381050f542e08807440c0e40c00412600000c1c0700031740c184407010f50341d058131200291140401151444d03443c8000d4102a5019900144900e01c0e070070f005802e1400380d00402110303c050301511001400843d110b0300009c411030520300040111002100c01900189402d005071030455403190803011280c0c0f201240305526a03044000b61900020708000a10641e401400310000c640041017032144121880b1032500603074041040059039008241fa01c1442c0d4880e500c0084141c20b02401082101031304000008101c81c03055841e825001a41c2100300c2c0c50303540901684404440070700108260a01c2081500d034894051001c0354264440942c6030790781c601043d0705c22000034112200c04c0c000d43d40c3c180260703401040113040c601c0404001c0148181c44502240400301e000e6a200006103100250340c41a009034200a001000356585904104601100c00d000c16550000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 185012086 1250 185010836 185010851
    0x131e0b040b03060103030809071703030708100605030406110c06040c0905010b070308150f031c03112803061a070b1f120309032406230d0c09090c09 65
    0x91038001e00c64412402030142105a0071642c05480141029003581d4161060040104e8050301e4200910140828000196201d00d0300300f200800701200105000302004d13441d0404c02040760000b060300e0b00140e2185010900c0b81e229441d40819000307400000f0810b201700010f00050010f407204140a89100c224280200d031303201e80d40110383d44100d100c014009030b049400100c030800203441104070510300a014800c1d03c100c013000245070180d00300c0d001d64004030000940032010340521035400c02405188980707080a002c40c0720b4020110011b46403d5109d118440038800343ca200c0d42c080c2c0050110342c2406c507848030440c1500300251b0069442269092407580225510742c13104401525403010045561182d0703401d019840341c0c40425018111b0030701241d100040001841404c0500104140c00f0710030464422061480c41a00c185920161410940001c81d1030358490206014500c0344094540710307189034291800410002450348010342e0146800f0b000800c100081c100001212042d103800d20008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 185013336 1250 185012086 185012089
    0x72c010909060b1909090203030c03030c1c111b01140a0204051203040317070f0204090305091903082a0715020618031b0c040615021509060114131e0b 66
    0xc2005402c4c0100718803035010130115038150041e401c802d01c040d007a0790a14000246491441e002980c0700c8007141808a401d001816a00e01210700340b0f0b80c001018800c0308403c42c20445548518550152440030000001002802c2500022002e41810040f0409071070b106801030000e42203070007500d00c54074001100f0302c18050000b0550341503940040091440c0090740d01d800c041070307010140460382150301140c0140540d0f0f0380c3c426881200d001e621a00c0e03603000c0d1002000610203488181c004202d0f94160280082032444080c5d40c140070541085500c00701e114a000341d20341003c00300c449501d206000c404514001780d4645020b4051068085490507280c40100d00300b2880c004803031071a0b644c0207000014103460b15000c1d41d00d4080c0c9241c242c407800041d00005c81e060b988240c00c80d0049056510100301160740c104070b817880c902d1031a01d24a1060800d04d405903216003041c4107000a445003020580f0740e69a07008503d22148001135410042c1d400c5181201c100c0a4903c1d11400d03219181c0103494006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 185014586 1250 185013336 185013349
    0x2104061b0e13060b0a0c030903050102040f030c06171801060e090a0c05030307030c030309060b060c0f0601060203070302061b0f0304150c0c0b0a1e022b020c072c010909060b 76
    0xd0710040d1307500078140282044100e424940005041e410881c0048000012410a1000b00043c00c10b280004840b107003142041c6403100314591141d0108003044000f080008a40d400c0260440e0500184100d04126241d21300c0c013410054101c00e84d035009103024091240400501c2c200068400e02c050b100103a920307000c143d2a4029007078040c1c040b4042080610000f44240c2c00b1150071407003004005000c43e05000803540c5900324138001541ca0380030003009540f02804008160041189200444c603281181c1d43c020340b0b49002601a001001c41450400070141221040c0c40303000b000102c10703070384be407a01c1c0c1030011859450220844201e1300c0e048100d12034030b104460000b00c107a00a240d800d4a40c8401c010746000b0262401009402613004a85415084140c0010700e08011611848901c1801e010010261310342c80501a4442c50b00c100003911000c0004a208000c03141c1e4158100001c40b08418507140c21240691080d0b400c94801d800402c0126850380300440740c1c0e006120402c80c1d1000c2d0f1007400103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 185015836 1250 185014586 185014589
    0xb1834120f050c040314010216030c02010806060915030c070f0803010608130c060f02010608011e060b03040506010b07030e0d121b050618100f202104061b0e1306 71
    0x16004400c11062000c103081b8164103001546400006180507002200c2681c00601400c0c101c1c00100380d480f00da0150b603031002040c1e80140044030014601102c0100140941c0742885078000401c1c0044002810040940152604250015600300304403200e0300e402802c5600034064600815074600111b48403220a0300e0040a55503c0160400c0d89030400e0400d5502130000701c1f901e000c543d242c00000c0342c486c20038040d14840100b698036403100b01200085c0300c1e0542d58030350400c0028170b0003401000080307000051034604441104a04668400031410704498401c4403014281e0844138250004041013108201c10b040440c85071f66540c51110540d10041e4806448031024060790f11500108001c450703280410500c0701110742c03c071140500380da103441054495045d0701807600350340e84185241400e0035082a98030b041010940d40e1511201c0d00b640036204035054801000c000c203003c0006c0030454140c0c803e6503407e180c504100c0586a03a800c00920703400003800c00c41e0042c0040103940301d000c100d5018210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 185017086 1250 185015836 185015851
    0x3010f02130f080d031a1003050709090905120c030d0218040e010207030215062205090d090e0705030c0d0e060103060b030d140304030309080c060603010b1834120f05 73
    0x4002c10f50086000e05510902075002ca2001488142247e5a1a440e00c0e42040c40c1d0310082054a0000b4020700958104d90180892030b0030810300c04000348003c500c550449244e1a03010b034894035045841c61a5001d03100300703000da403440080c811001030780c144446c20b9810002c4a0a02580b001d03880d0300381c282c4c013881170000d0150b403051410001c0820320340c18060340140040e10400c2c0600c014804070909440ca90034080c00240c0e0344d8144240c400b000c1c0300718000411107040504619180c0511000328100c000c3c10039080102c08008520540701240071203006841c1c040c000c0c00b01101600a141c2c4880003031104680c101d203070141000040c140411000160010394030380009001a18060b11181d5000520071000c040d0b640351600c0008034460040d007204560507004105518181d810705085070903440d070180c8a0203401424021031035510764610340c049140311006204620310700340c0c0941da58103116034441e406080b18103001515408080c424280000440c00d1184902c0b07a0440c00c12a0401c3d40c540303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 185018336 1250 185017086 185017093
    0x13110f0d050114130504030e1503061806011202030a0f021207020705150703081306020301120b0a050f060d020d05030d09110a0305030702210d0e10211a03010f02130f08 74
    0x400f1a20314551020361b119000303013400d80c000110700c03001406007524114140b8024001006200b60b0b170071711180e14070104030030000840c0541411030000c0c010440303200d1014111600000001d04445246c2c0011513401c418071806c0d03455100d03929a904601078101c4031200103220303105d400100c1d8500b46010507481d03408004070510f0000c0e0341d1421202450001d100c40c61400b8610541d40c0040d849100850003800e01440c100403003070b81c40c640b0010303002c4090004a1800d0a200500500500c48154160044400c4451109039010f0f440401d0020300852409401400b010450440540050b000003500f2407190450005101c02d55082128540d0b19020280090384240b04031001070402030064500d5080b507401c8140e06522405c0100d25205404264400050040044c280241003c659908203d445810a250381c03408203543c13a610010420204182d260b01c45150151000000200c000e1501d4060300a1000c0c1404451a80103944004041d0402c0307d03c111000445070050342d565025500302c100038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 185019586 1250 185018336 185018359
    0x3008070f08072411191b06051608040c12150c030b040b031615140a0207031a0601020d1808070e0103021c031413090212091b030c13110f0d050114 64
    0x2118a00c1c41009110060048804604000303864401e10300c6c8096100f41c1c0085450300d040b002480d12440f820500409008041d814007000a036102c0e040c2d0213442102e0041301303100e0200d081017007910181400885120b8070740010303800c2d640d070b25402949640b8003d4400f8489109142c062550390303d0300596142e15400c5001d81446599043d4a010550490618041c480d551400c1c0c26441164404580000540d00003001001040b030b14003840203491905031618171039440e0030340010b9140c62150210408021002076146103600551140da0701421005088032009500d55007107020044080c002641b040c4c1440901c400303c5d4404403818080c0950681e1801a515040c4509503130a0b00842d06424101305404408203c0c24410310151455401c040480d451500b040b40240d8101000c02c4a180091070001e00d101e451a1000505001884001c0e560400b0503200394003454004c11884031491131300c0d40c0002d1020903600c0c02501406010b03500702c20070001070343c1c0c0c3c003a8255924001c41080c0d4100324240e14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 185020836 1250 185019586 185019607
    0x8030f04031b030c0f0f06050306061e1b0109050c0d0302030a03051317130803130308071b0f1a0406090504090f080a093008070f08072411 61
    0x8403107240b0b1403041c1d181416644a56824100c1000f9030811007803440c540c0420809180c41e10000401024142051b0b80b450034210302054280c4a82041c820041c16910b00c0ea0500408101c201d440c1188201c0240c203010700d5460001e030280491840c00e07501131080c41c5aa400514180d02e1468849506400840c81d0000022f000d8001d07110061020000072203940c402170200f01d15182010304904101d02d07507603446007040081458540c541d0000001070380240222005451550218800e40c0e8220780126112442441c1642001440701401c074120a10000700040081d001704d841015a910b6080742014482c180e081681140114032512000516141c010013041c20961301c0f084400c0d001d0b0701020000c0300306460b9603441d81d100c20402c0700012400042000f900000c00f50901c0c4080345401000445000ba08001c0186c02200313001901c01000060750808005110100c0441d8a5201140356120030550410401800d2180001880304150521465040f4040c0c854a5840752100503843d003803600103030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 185022086 1250 185020836 185020853
    0x10314120a050901020d0309020a050f0406031403071202030a0e01200111040f0807120b0c040806012418030303020d0605120d020705100503060904020a0e09060a050108030f0403 78
    0x150801a01401280e0129005520000e10141180751280c035600d40d640b02c002850400103030f00b0384040611b025400c43c016502e096134070f011101304440c00d0720a5804c0d940000e0040142e0303030005140c040c20311b400146881000c0003030302d125030103815804580d4070150001da89038401d011080c40022184081440291b004400c1e6a000e400074288114110310350400490845100c1c0742c40c500035801c041000c0102c0410300c0203c2c3c01a00151026100c1c0074070f80391808034448003201340108940e0382540054810400740d8291001000d40208589095a503030303451007410980303040007181c40744c00310303c1c84800203010707540b01c200c02c802c011182c1e0130907407454600f20001d41100c41006040d544410700094140d45100402c500318091401130700e43d51035a0400030349002d04940c40a0700840c2c40d0402100d41c00d41010940c1e034810400d440c000f1481c0c2e681d10018000c840705d6048521150301f40c0d0240100c1d0500016403a1058209020412040e6287d15440e030366401259806480c003502000705100040f000c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 185023336 1250 185022086 185022113
    0x1090509011410030f14090706030920180a0204031509081e04050a060504080d0e0a1503110f0c070e010510050919080a150c090501050304110406150305010e07080103 73
    0x4d1800080460300c080444040d5081240149088550081030005403036060180c00010310160900300100d45656a07030305500340a200010180000b000d9413192140ca500c010b2038410001655003145610304001c00c5d034002e4000740800d4038101200c04070703190414024030410082e90b800005103401d04d0728602281541b00451090f400403000f091100003501d8441c442c81c01d01401140e199152664100003066140034041d200c0f0f00d08010340c0180608951b21001e070f50505890328441d0f0425a4840c0c01c5065025101001d403580c000c42002a00b00511040000074002a5808206462409540e8810310284080c00e00516610a03420300341e1044060150004001d03c0d51301401e07500707000054615031034010380c5583c00045560081445102003000b0850004607065404030108100c0040c0c04000705120514002d49042c05000000704040c00b030840e001e8090303401e00900601015880300d108201c1510f513000b091000c203080c0301c008640f10a0780020644207030b0455a0310341080c1e02e142c480c6c03002000308 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 185024586 1250 185023336 185023369
    0xa031b03020301230a0204140d14191a010501080c13050a03061b2d0314190606050f07020918010c050a0e01050c060f0711010207060b010905090114 65
    0x12400080161001e0184c07142d08803844078050000c13110000e42003000c460050140d80c40c0762040000344002d00310f174612070300f003103034241c400404082e000c0ca4000500c50a0081007040c40c0b003102e005840c01c126088803a0581c5105015407188105011051004448207001e51804201d4000006410800210180000110390080c0e064001d42d10008216140c203160000d8036001c0c5c40c0c0c0300d81d2002090340e2403019180d213075620f003214894864400542403403540000c1c84168409445c01031300c1e424401c0c1c1040011030310174521901e45040c142c1c54403400c101910141e5960701d0400390006141402001075909040000070911710700051507081110350388000b007921030304004e41e80e000684000b0920a017001a54541c41e21030f80c4d00c5d03440c04041d20841800079110304018041044000d15407000c41c409820a201d501d105070513031039140703083d0f4018414400580c42e035840071031480248a00d0b6006001440b41c01e0b200c0c0310042c1c1e00c40c802d1208880302405258001098200f04d030b5414100307401000b082c1001e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 185025836 1250 185024586 185024633
    0x706141023060906071b1d010b09210d020a02010f1b080a0c12050702042012070201060b0a02060a0b090105030a0f05031303060c030b03030c07050f0307051005040807050d020a03 78
    0x860b0b07030746c00300c0079111610581c0b10110070402888009102e41180c2c0c440c08104560030724030b42c0740400c1d00c1c00911682400170702941c1419120712503c516a41042c5540c101401510205000c2da00025951050300400360b0003d61a070014002c0c403409400c9080d00211b0b01c5141340710404d05e5490b1324040754400c52a550400c03040524080125a0131240c0d18080f103d1039450355692100c2e40100030030b407020800d812255901002640000c0d02000e0101e55084001c29040203842c0e031813650503801130543e030f440610100400150418220713404200c00f8800ca120f5141000340c0400034007480703000c0c00240180c03a05580882900d0001c940c1112511000740e100700100c0c2d03e0201048030140340955698000c40d441c644511041c6071203500740c0200085040300b90004c504019081d80225a510010320a25001c2c04803104001015103041c040c040280a000e00070200441c1c14010091090f8070506c680c0384140510700c0c022611f4036200b403000319107a4004051045042c1036440700901d800c0c0c950605a42c045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 185027086 1250 185025836 185025847
    0x1125080c06090a260301050112110d0b03010617150c0d06030c050103230a09230a1202070b0f0903030706060902031e101a0706141023060906 62
    0xa1080101500c5948000c003e00360001c0f8070701d8a800d140d80040c0103c030402c03d60614030000c540045003a241160824030b045501076006691220040c495040011381c50000090800c1c01a200b9801c07140d0b0703001c3c0940080024036915036101c1100c000408031540790340c015001c29100b848440c1c0c03c0c00e411038440310415140514a00b80e4004481050b441215094a6030b5800c100790b6030903104840302d032008218010902ca100e1840c812030140c2c0246a403030400d44d18859038080c070501410007000400c9030030183d112080c0398141c10386c0d60001220b0449548005080300701140f840400c4000c21200c0c1d08171b03490f0524101c040840829003144000c0c0d40c05104c10700c8082d000c41c5e583d006410080400700030050380d90420302c0386840b0203030110205486003c0900240801c14074416122412075400d01070300c200d40742c00d0340004240c0d4800d1002c0541381c0390070013400824019143e04002d014980744100f1040080e07a5104c0550003040c448620040d0540034944490181410340080c094410020300061400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 185028336 1250 185027086 185027107
    0x81603120c0206040605180d0f02010b03010f0b0316120b0612061608010603060609210f14011805031801021c0306090614100f05090402031801112508 66
    0x240c00801d81d480060780721509110601c2040e100380f94210b0440880802152108915150f84413200300d0b00104008a00390700408651003035001c8161010018024482c107110051040050a405200c0911030300450841043c15401c1c3c44801c0c0803201103004c1140b802d00300340c0303540804c518000c1c50b00c0d030041c110325282000035109000701ca1080140030300358949018000001004400140c01c60414140741c1a03084c0f00590300004080e04458503041588010114141c00604516451600a0090700614080302c100f100d80031000282c102900d00800104150000080c00f00600d280d018043c1d401c1000714207541c40044081404404040c01140c101c99489440c880346460300280c0b001c0065552503080c45410503c1c040e43c0020140c0b003d0225404070003000140b600c0c8040320841080c800b09a107502e040380d02810503200030700401001107460740f45c04c1d10440040c10007030801c203185e9407030011b850001c00504425942251414241c00b001090300e01c3c140211081019010390344200180304481c0ca1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 185029586 1250 185028336 185028341
    0x612060e0102090a0303081006090f0b030c09090405030408060f04020d0206090102010b10030213050904030203030c03070e100c02130e0303070f140304110a08070b0a030b01030209120c120a08160312 87
    0x451207595883c3d143e08d010103000c00101034036045401003280c00502040013142da100c582068071140c0c442c0701d95985a61001c04510701c0303100c04851700003507004c0c10002441408800380c41140c2e0003070b0507207440d5507e00780c2c14071500b0b41c00c55009504c1000b800b564000744c2031800207010208018000007810300212400241140c6803c0700c0000026000a030390001e800c1d002c1e205070000d04040c0e0f00d1f2131b161b00341680c0103134403804010300541d89440c006c000145076510030510150704000c050902d006e0041c031244c00a000031010481030303000301800321007030703419501d40c0c4560b007c01418103029505540b51203070304541610700070f450307841004403000000d0425582e400045002c1c0b031003107001804185c1d05509001111031541e002c482c254112050802108201e030003140c1444400d0301e0f0000700510f1102c0141c0090181800e40341d0841c43e04800303200300242c0000c0c1d4030688034080714036032804404079040c2030b03403441000b900070050301e02440035004804003c0d2a62400300d2084c00d00c02c1c86103003814801c004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 185030836 1250 185029586 185029589
    0xe01020c060a0e07050306060310021e070b041a100b090f0a1409060117070315030f030206070e0d0f300509010807030c0f0e0a150201020c07090612060e0102090a 71
    0x3106683c2e501030500380c100070010382005003825000340019180040000c0c0d22005140c2c030003440c0e20b400040c1d0418102207480c820121340e2140f05201c0c0c5500490500c2c140b44d050403a03040322480e50b5001c201a10311030b0560700ca403240041c0c0b02852030440c1003844068094100714041a042001100f0400e079950342c440038103016081c48031140014444c80c0d401c02050010140400b8113002c000c1001d0b59443e01354011240d840401413301141e110b400a600d030f03d6500c0650b001414546201743d803481016404942c10b030284030641d03201d1814a036241c0030000c5041c0e940d48018030071109018568005000d080c803001e40410302e0a9070019038059a0542c1e02040b20101036240007030070024a910f215070304081d4180c0c0101080c60200b01d4116401006800c0c1c480d0601001c09020404c0b41d203100c1907a880e0500800703040401c1903450076030710300800640030350041f40050f1054003038030b000403c1180017807117448100c5100703410a00e41012580c407144010408403801e0a1155000c20441890b5201c4010000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 185032086 1250 185030836 185030851
    0x501061416080f04121110091203021c0c050607110304170715080a0c08010522090c0f0f05090702070605030a060b0301031101030b09040201020d050c0c091006140901050d0e01020c06 80
    0x4170410710b00e251940d0b40e203c0e1301462512488000305031403900380d80400740c0000c6d25100680300c095440c041c1810b03407611501d00780030b10030030301c0d2444610000c5603c0240180c6940c41181151299100c049044c2c818803a000601c542a078818801004421400710501d0346c60200c1b54151045241c40700301d214860300b042c02da00d00200742070406000c052412445001c2c0306020760300d004846541403500080c0490780228403081c040d030403090050303c4420503034040800b281d840404141c4a40e90303032100e000c0325420343c4200d080100708988002401d00b40926424412840c90313001e4846241844802d480a820140c1382c0040340e03a80342c9010070f062000600842c040d40c0940104050030301404001020340d1202030140303000704160f8040c80300507600096007100d450200c1c244180c82d00742c81c3c04403900c0e1041d0700b0103a5078003643c180c00303100c1c031444000c40040072b13140786a032104400c4400307804141091141302c985d140094010000001c0181542e884001503660f004009407030400c02c1c850300c0f072030101c0580380340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 185033336 1250 185032086 185032109
    0x30702031c0603020a03080702040b180105030706030522030c06020301030c2d03031d0d06050f09070303020a0210031b030506120a0203120d0902060304030c060501061416080f04 78
    0xd100030310700090103044000341c0301c8284003081c00d640c04101c41641900c030062107540045a10b10071561075800c4943c1e0300c440074000030070000c1280760705007aa04080c03094501030300030030f500481e07014400e0117500d00c1442e1030003a0101e00d03030f108007074461206600300068040100c1e010f5a400002d043d0b00086000f18050b6118074502414040e032408142c128030281440111503210803101041c444818800302e0390141003c0c80111458000182600d86105000e5031202241050000f0060248d018901442c140c140f160015625884103a50300d0100b408050b02503400384404800510b4056450500314002d403030081002d00740003071504101c0b02944000d03000300381c882e003c1103c0e80c00c00080b603003d149a06402030401e92103540109440b001c105c100d000c98000c0014000e0442c80c0740d50030075607019502030411540ca25040c24020009100c8180c00c0b1007003030600c00000303a290b100d102c4001c60340784140d03545844e0401290b807080a07452203800031a00b0000030b10001528245c1e64028000814031500032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 185034586 1250 185033336 185033347
    0x3030b0306010609081b060c0106081005010b040812090409060f0b0f060f09060c07120305040e10140d0c0305070b07020102010f0e030406110c0402070c1707030206031f0b03070203 79
    0x1014140072050f0084010840d810004121604c000941179040421030303c1142c841002c032002048181c0300f4084076400a42c20460300083c0844001782c40d00985040d62400c00ca20b980700c0342c046505200707602c1410010303402094022034000e8060000d1040705001400012f4001141d1744a2060b500d404294044181e52940b100640d405c04100200c210b080c03c440b110716268034046101200d00640340100c2c010140820640380000d01080084054100071070500800850b61400a105500c03d004103510391100501140f44c41d1910f654000c01c1c0d9548540d6001340e00070b030300c2c00e01511622004042d0b45000d0108000030201d2010b000d07023805440d50103d604e66032810b034000603013035a5800300b00e651414600382e2003d5007000f01005880c19a1010301d4481500003450104a1505010b8042c09903c10710000c0c0e6481000074185200044580c4e540421142405100717905444009912004e50030820400001d0f0b00e2500040410000c41c00e00020b5000481d00c03035590301c00e513410490ba03038009607100140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 185035836 1250 185034586 185034589
    0x8030a1b0503130212010501030804051003020f160201030b12010204080d09140f1f050310090509060f090304030804170601050901080a030507030e0904061406012a080c0a03030b 78
    0x1600c105000400514a00100800801422844001d100c094510442c0401004540c1e803072000c001e120f6454070091200c2d5071241031983d03160380503101e00d5105018003a00011105d000b402a5401c1108c8913001d1401c060507103082080401000034100d0405039586410142543c2c2c409010004a185800041c1c41c1c1c1c4c1001e0420b440e05c40c0001d8081c2c02d0050300f00080191031400c0c96401c0090b041551078034039010101d0041941c1c10702d40f042240301c030340b9a1121918056030181c0a18400c0b0b00403440c0031a100d989241d0342e012984140c5010800f5081680060204801c2c80b400c0c1c1d030040d5014048074a42551382c0c990b00e03140e42180d0041412440c02c0240394001c40c108008071030241c02c08a80302145549016261a603502c40b440000f41403040c085100d10506004501130120203e000d04034400510741840c2800040800c4c60290b0300001c400030104407a544640521440c88041540c0e01800e4840d41600300301c58001114121150402000324002c502024005c4c0c041c12442a200468607049210 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 185037086 1250 185035836 185035841
    0x1d0f01060c0506060f04180b070207060f0518030f0f010203060a24030b031c0e010201050a05090a08131d0414150a05070c050d0504090f0b06270d08030a 67
    0xa01440402080c412924003241001c40c846802003002c588a511319501140440d0151081050b2401d031f800c40121500e043c00b03000c0019910500195080d52240d81e1100320960320864080c0e04000000d4041c4808109203400000d03401e014640141116200700c01c030219546000d850741c800e080241d4010051000e68101000081c025144450841308440e1100d4900307000190220700210030581c660400c1c140545040c0a071200c030b60400c0c2c410a074400e4000c50007402001e403074031040340150b00c3d001c00074044601900c1658021a1040040c10141d1403944400d401900404d811070b140086140d0000340d00119480e0b924040d65040301c0a042614103400c203050040c0400701040c000350040032844140e003c03400046a4080c242810000b015103c81c84119401b0f40f26060060040c42804181317000150080e020b08110340080d10140b02c00c0c49102002415510103036222a00440244002e130b002081e0a804800003890301c5080603001c1a00d50005455400c0c60320040e51481c10010034001c1c20151030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 185038336 1250 185037086 185037089
    0x90614030307030e010c030c0c06030e0c030c150a050c0f010c110c010206190b090106030e0c040b0d030c080d11040306060819080f07020306090105010e07020604080a1202041d0f01 79
    0x45001c1d5080202ca0b440c0540240d000044042c100032466142c00201400b400d40035101d10b0f082100364425503100c4801400400d250409800c4500c202540c8558510f000104164154009004a5464032540c4071000a03900904000c005110040c4281000c0e49020020000301300c0c6040004134030800b244501400801d00c4104030501c5400c075014105031640c00007600c1b904168041c1c0c806c0c01c010503200c955401030078402d170030701d80c00f11003400001011580f60300a00d00700703c011000e640c4c1d0502c042e420442254096213800d0781100300c0f404c1080102c0c0c0a40a4683c80c140100e4a1a29040c180c0c0d9010080b01c101040040580c040450b0031f005000c114804d03240a400c6d508001c100410750311503140d202c940000302c000c001c0c2000254100400c181d010540f552580d000d412180d580c244012114043c01003400f400b882c1c4228400025401480000c0305801941c00010b0f072890003c406504542c440d84000d00d0b51003039502000002451186400412080700101c1d059070315038101001c3c403141900c0107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 185039586 1250 185038336 185038339
    0x14180a080609061f0801020a0f030b030c01020a060203090f070e040309060503070c11031006090204030b091f0c031b0804110609220638130e04020a0f090614 69
    0x1d408120040b0740c0016002d401040300c031081d00101e035080e094041104050b400c2002c055001003030608480750021140190f401007503c0078002c0d807000a05065441c0c2c0200045070043e4011a018004601e05a0003540c1203218441a6051000d002000a1030003840740d0000304101c0340c01c002c200c2030552040d00d01c4094100303440d190f46941050f500050040c02c1d0003c0103040c11106400d43c03006503a040001c601070f0300c4204018000711b90b40f18a0b200c001d400c07600c0700b640d03000c441c070340000d0b022034001c04c0e6010341200b02c600e16001d1090154032140102511a008402d02d95039a03129140c060203150b030000c0c00303c01a40d03000c0383d510701880c14030000c0b071400310701500584060000c0c800b56580c1054202511503080003101490745c0f6040a00054a01540151144001054001303d904a140c018440e4800c04441c0b01100044030302c140b40f040e00c9100d80d0b1010f1180c1421080c8001c00b5412503071500a03000400401400e51680240101e0240a03030002c0115565080e017049011848030041d01003510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 185040836 1250 185039586 185039593
    0x506060108070903030e030a1e020a09090302030a05030c04091a1201060e0622050c070b0c0304030507020f030307050607050306010f050301080a1e06020a05030402041d10020a14180a08 81
    0x102050040c00354030240c00002e06100b1100d412001b151070422001e0310564004100c001c50f10040c2d456400d4114040340240e00846915130041040003950040e020144ea040d4021860110f5045040340d85ea0005003055400e10b004120000b00e4805500038813612000e00c2e01024040844d0204002903d01c8107000070007545d040002c104201100c4010082e802a020745010040710b1403441c0105000c0340d22107001000900d07040034401e000d11004003500e07055101d440700c08084c0c1c0b501d00700100d05020071600180003c0c8108012001418001e28107540e24202034100c03401e04010f80d03a150b040c4034046039500d0008d080441080402c2d82c3c84030b07580c00d0701146400c01d80d155505040b075842c0c580c410035070054049401d03058000c2003a110700d10a422007030f40054045440380361110380109990b00944040e0710450400320011003101030042c001021140e03150081a90700c4840c080e01020390000d44400c0d0911032071340003a120b213200c1c880003840c1c2e103100d01d26080c031391a014008000314150107401003403140c1c0c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 185042086 1250 185040836 185040841
    0x13030305180f090a020d06080a0c05180f01050f040209100e1e06070204240308040618082a060c010207020405090105060904030309210509101d0f0f040c0801030506060108 75
    0x116503161903030300303c0f40c0300b0781c056a10342da035031b07120f80141c5402d5201d65641d200e1094904244100c0b403080c9401d403001207034a241450305811072130307401d07101c2503603012619200040104494a42a95400050640540301600340060440041d1048001d0000d200201c0d40b84240920149003004500c0d40e200034004120302945450300c00302d0180d010341c0c0802801590b0703685540c40c1c2410000030000c1c06451100603140001d07281c0c034101039143c02a2085101140088448242d0340ba00c0710703940b00980c3c41003002086442c0001c1c80e21501950000180000505101e854842c151a401c004158080d1040000350f40d4541500c103010454500500030850380c0d00d0101807240c555138118103160444d40601d00420383c1d1a01e400c0030075098a40c0c3e80554514102d20600c024a40d4105e40079060b000c0c011152203103c2880d40c142501c2218100031038000b121044403000b08a40b40401008000350340203000c00b42d8131100303c0080340444003050380d200c01050014004204000342003100c9980301e902840c21200c1070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 185043336 1250 185042086 185042089
    0x2030a17031b1e0306040605041b0e010201050402100807180602030a1d01050f070302030c100506100206040209070318021c0c0605130509040f050a14100e070e090313030305180f 78
    0x260003403803403030103140f000808129580e0300e50300b0070b40180000810803c002c07282d903003004403000f070b04490360004540c0c4240ca221581d070045c8246842031b600500f01c04414507056200b10752419006004205001001511070568500c408148c0050003554008687d0754840910150208140c1048a00009030780d134140101640c0c00b405030341c0d00d050380d8080e0b0354845a041ca0305034118001c4a45420084c8102e128003101011641c1009000700c906907001003100113445000c98072404101c0e8040d402100800100300441d1180c1d00c440d00140c18092140b50408d940da0000d4140e0f684680500c00120030380990806001c6d2140c921801001c40f030802d18a041c9c005601480284114030600d0302c41c90440c0300040030f00040c142400c0700f0a52140c192150881c8500c0e202080700038074054241356101e045460364842540344a1440f0101c0110000c11043e8644003849000c100010a07542141c0802c0c0580302d550098604030030051803190300e0f00303522034070f01014071140040448529882409410b6008006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 185044586 1250 185043336 185043367
    0x90f01110f0c07080604060902041103040308041b0323010506030d09051c0f050105180c1c031b140d03020414012f031207020a0b1302030a17031b 64
    0x249680566003a4442202d07501c02030900702c555000c2c1c8880d0107800300304410003c0390783c411102a07101726000c001000f41d0126440c5540000c60b0010701003480740000c940460400701340c03090028800b4120001c00341d10b0340d40d80800b03621310301035208100c00d22508a0440e0802809003d9014100b900100030318521440020800140c601c00d0b240140b2900989800b40200e81492545458000d007624540c1480d80c90701034024402118521200c81240350300d183e842d080481c0c1007107403a80007440110b03050526210390481c0c0c00180300c11018030510820b1124410046d903c7c001c68580507040c00010b00500e422003d04298071f9410003810548100414054440d41000380106144c0c04c3c40d00ea00045000300c0014060042144214580b0605a0350030005e00000001032154000c006548499034076640c0c0160fa40e0b82010000800300c03100c450000d503003c640c61854069980c0000c0c00c5491200b05522071700200f211110880078405000410001c080302410043c0007540d002c00380d01c3e440c204520648000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 185045836 1250 185044586 185044597
    0x10090e030c1b060d0f02091002160603020901051206030f060403230a1e0c0203030409061e0308120405120301090905302206030203061306030c03020d02041b0206090f0111 75
    0x100d03075551002c282c1c0e503145c183d058801050015100c00d40f0a03250010181d034401d1b41603400e00e5400700400c008549280319000351084440306031101400c14080e0646010305620007030416070588a1001c2114150b1010420319004a0183e1070b100701d5220090600c2241c0d1182c00d50900c4007a07810888624040d610001007441d28240c16060381032074111480840b103e0006500103541840003240100d45003440307038400070480f80c200c0c521415028656000d01c144400905c005082c20300c0c00d000d200d40703800c6080111a4803510500640b50042c5c03070340a400000b60400e070412107441e50b640346070300d040000821550300040c4140307180ca0742c1d01d880c540c0c07924a52128103d40219a01020940f80058031139880c5d04864003113800c40e02d0541c00e0711200010300039001128810b00c00c5100c00c80d0030800898902ca88029a41c109014005050440c0c090149808072000c00301d07040782d13450300790f1116020352810326401480f2944c050900e6082500145146c9804030300c10300800d900d080500343c03c08480204490 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 185047086 1250 185045836 185045857
    0xc08070b03010b0316110d02060a0b1203160c090f150b07050c040c170114010212180405060d1b0e071812030504080601120309060f0c02010810090e030c1b06 69
    0x41054081724080315030311003111a02c2d0240c4201216181310b45e4021841c94800c3d00d600400b0002e0b441c3d04400c0000d42c0003906250020750300200501e900002a001219000070300840d00300c50b40702d80d15000e6400321603050180e648250303510001d2088030500d00300c00000410702e05625600740103a035103685071503c80d4144441e10440c1e4590800004900450501155488414201c400c071360b1741c0c0c0155068000180310302030050107600e001310700000350481910501ca149805180a0750714013014400101409400c0a51091115182c0c200040b0003581c6e80041120181d002420607190120725415000d0140140050250707401c001c8030005034864640e81200d800200740d0b1140445410f058801d44107540100e0001c0c0205400030864003451034409408034803a0f610360f0287d59079550100e0701c03001085215000201c403c00b01d640558429106a0380101d82c9115001c10709540c3c000e0103045810010400c8402d400101d0f24050b0502e0a02c0b21025400b10603c1507103250020714000340c00d82c4140c0c034501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 185048336 1250 185047086 185047111
    0xc09090a050a110c0a110a03050a03030b0609120109120503130b04020f040c092c0105192301080a05010b0301050d05030409060e01050918060a09020d0503070c08070b03010b03 77
    0x1e034484295070031400d0149110ba105542e20202c2410030394844140700b0b030941d11b42d214018121194142401c410048a80000140000d42400e0350114040e101c00c562861b403002051003403032142c1e52003c007000d054040c85000061589042d14280c0d1b08001e0600032041409014000c00c01c2c00d48410b0721908030300c0d5121150072100e54561001902e03807450300c004160400d1810780303060607a80e00042400d05480c80c01015004c4c540c11b14003201c0d25821629440e0000c081040010026400d1070121140c4000902c60800a455201e5101442e4800101070301d1440c07a03002e4100140550708510308542103546040148002d604045200241d0700c0103200355030043c0d209c2420042400070a20549015094610040c006555107d00300761039103000380181072080481001080340c5104400e00c4215204079078026000784d42da0156000014450900c0990f0000c024024400010768103100421900740302e082c01003034030fa0802c0c003028036100440d04900386004081005100524502041d00d61200313007400e49 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 185049586 1250 185048336 185048341
    0x21030c27050d02010201090f1209090203091005090c030d021606030b24070503030a0609050a1802010e22051f03240b09090a111e042301031a0c09090a05 67
    0x101d0042004120103001503544903100b1007003003040c0c3c00f271440d03081c103036079510180c03503140e010b02012403006551404041d030140048040742d18154009940c002e40c0d01007612940208240400d0030840620802401070f00003c80c0204006240c4041401814442c5000c2040031100e40c00f0a00c03000c1203151514510010241d032101440001c0304503480a544131080d2600c90500000d400c0240207e4040d011b015400d2200169280c1103074402c207404852180080b0440304c201c1d40040d80d024600c0d16040b90050903803011000c14840c001d81d000e400d229080b100050900e08040d46030304040e03524140c160b415070f044404101113a81c2012901c00510340014035210410756401d981d004164030340ba0039800c07001900410651190229201c2001030040a411074500808001c0100c41c44d061030041210441c060880c05640c00c00d80d1107803440f40c6032001c88e0009500e844524052009099008031000c2d0074591000100000100045400181c0e29400d0307828aa103000000c3c080c910000c1100300d130142d45800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 185050836 1250 185049586 185049589
    0x30714010b030a03021036060e03280309260d050a05060a050a0609090e160e2a0d0c1413050f0307030807030c21030c27050d02 56
    0x3200007420401011510640d007545006515a603c030154200303030354502100000d000c2c50700c40c5401030f00107440d224054504120040315500102d1610160f9100b035861601041640d0208001d00d24400104900507140407036900b51804a46108000c404042c1411100d000040495082a490151121002514000e01504204280250300b0070603102420041070041304280c5500031405008242c416080c110380b40d000b48296520540314080010352000340402c8280b005900210000d06600180c940313500365103480107003141da10382003940401840014881124846004007640c1c1030400504104620070f910041d125000d5849103800d5151506001415188161100304442c040400e110b5120315600b080304603040c2c0c050140c107010301e003608a0100c1519000a20008603036000308524641041d42c0c2c1c0454484803d580300320b82e4500410350144c41940800e05c091817150740c0703550007d07140301c13003074001010664402c40a080c00d1a5600407500500e02800990090700c60550385850300c00c444e1f10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 185052086 1250 185050836 185050841
    0x4030b1602060f18120d0f06061202180d0b061003051003030804051c081909020303040306020913020d0b100c020d02122a0a050114040312090504050a140c070503071401 74
    0x109007407200e0040c00005d0420340d40d160054010002c80c880100aa160703000300a9040780c509000d2080131031401004d4035955101a0028a14800d0300e10340b503c00740207010081440d4000c56031048403044003400410200e401d2100205400c01420f1400748460308003070340308246e0f0103214000078003044080c00c005400d020041004035503503404141c82c2c40a55800740b02c02003d06000384e031a030086810b121460720190748030340a12003501d600107010b5031410b4a16502c40e0025405191342a82060342481e007955030b4807ea101030502c1c1a00245d020500d03002c10700030040503a1603051444284050815424090388070b241c50080000c1c1e054504046400041d0802d03403400e1065580c03501443c00011003421440b0301c042592040002c160b50500c440d90329240191480400203c1160b900b12081c0010004100d5551481c0089030040c02e0210009882d0004038003a200b048582c2480d9039196000e0301710003011119034a07481000040f810b8100352603030356215160300c80c0060150024a08a00041c0310300740a6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 185053336 1250 185052086 185052121
    0x1a2803020712020714010c15230906040219080d030b040f090c0302090a05070212070c0e0f0603070608130221060103120f05040303050403032f0304030b1602060f 71
    0x800810169081410013580da83e064040d18107048109809000194090640200c6803680010b4184280020124560081030400544030315400340022140b081542c0d8003070705004403101c0000c0c080303030b14160041c40980380c49501040c04d200300c441d4041020391408560101c0710f094902c0c1c0440c41d4004080082d010700000c40c403940e1034502d4100f9900420100862810861784240c8948442d130ba80e041d803a80c01c40d50708031076040c00342e00180c20750202e26100c0b00003814100e120310031140409403501c40045150004540c48603001d84c10006101f11031504100290080c0170070310b030a00703480c9044a0498034031607170740400900950700d66400c0000a4080408001340003903120440325650707500d04108001501e0b001c0d0769800b0820b540407405120707202e0001c480c140c03501525480e1519245680031601074074040d0000c40d414540826200e85000e18540c90301d24242d5810055441b01d0441c24046543c0001400c0d40321040a103000885001d9000700e0ba0981c0503407108849110365450541613011041e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 185054586 1250 185053336 185053343
    0xc060509010905060a170c070302150a11030a054c0909030c0b09011109130b0d1b06030203040b010b03090a050109080706181a070e191a28030207 64
    0x3007130281e00ca551000c6c8981e04442000c2d191411511424130b155114401c6003800303401038110986110b6182411484203410402240c03000400403418500c1003140d810607a0600b54207a1160240a81d034601c80f2940241400a40c540078111351401125010407017599802408031030b00015100351070b402e052415401031050b0740060190341d400f450000d0030302c008204c0c101c0c0c52600c0140800c41c409414840d110001c444240b0041c501201c0b4800c20610004142c258030182d516255000f6442d10340b07000d8215114807c4070254031003d010b200c0d035100c03204660007440815205000708404a048040c1c11411180d0900341d490342c94942013022030070100d150002400541c280502d0504000000d0b000300f503c58003c00b001c102c0e41d03242005119480d90600e80c0038000038880c2500d034404500340343c2200d810510b00e0505102100055000c2100f40003000c00218100c80980010099a500101405001c000071800c0a240c1807506141810340c90794404001524902c0f000300c0c22400e0b00030340c101c4200580 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 185055836 1250 185054586 185054599
    0x160318090504331518022a0d082205070315021c11040305070314060a0c020c100207120303061502010e030708090310110304031202090d020114160b01210c060509010905 74
    0x345440b85d10f01079880b44100101c0e028206060340d842005080702e1000c4c004000c409015803600c200c1003255140c81c054408520701c0410021818016241c00100d682c86200c0c60281900700d03e1070501d242007984982d280c8036214010022003070108a070781a10b80c5c0c452143d40300064403036240800320405000320340000f080f40c8140400801400301d01d80811149614030402c5030051303610180c0f074a05440c91303c40e8082c05640111062821468900d4400d09681d00520440d00465600c1d2481c4a081424070421340100390780c2c690038044041ea1203c9a00806030a0009124101c01c1d114069980d00c24010040c01c0700d9804150043c00381d03018400c01c40c603100100401e10400b03040d4059111149e005440c01c070300dc00c10010f13410300115440e0090b1420706000070003188603400140c0042d20301e0f04409107019800702003003000d126064012800854010f02a0306c1041196040403003c041c3c000b440511140c41488080403103000904a2070020241c51071454080d0711240c060f40183c070040d90541000d5880382 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 185057086 1250 185055836 185055869
    0x7060f0203091e010603081c0902060a0309030206130503030115090e0a1a0a0506041401020c0d03030e16050307090e01021303120905060306061603180905043315 71
    0x8000a401980d01611a0310040d05003543c40c0164202c41880c0b100600c4a4000d00c034100030f202e000c03811340c01c00c022070b00c1021459000b01d42c0021410391001c02c00f800843d90b1a9584018107904000d050392090610134020501041512225501e010503c070303142448103801410302910703102d020048003c0c50b158a03481c1c2030b4180f220504019142c0840d101d1034880403290b012400e8030f440d903002000c444000d410545050304280c004620034881c3c40900341136108902210200c2c1e220603080c450303994042c1c1d40c00601e2054010300c8a003445842081d110080307680c41c0080c4000c0d075020400c0f2080720400350000880d548060320282c0a07018011200300458100d000000911000d00c4280d0074142c03141d9500d038140354550040001d540005d6030140e8101e64207101404001c0b060780141c80c88103000703041030483c01d201190186c113051500d8203c40e03007140d10741c8188020000080000440c80000104030000fa600075182418884e083d40f4a200c07525132581140b4140c0c40d00020a07101426016800c3d05186 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 185058336 1250 185057086 185057101
    0x60608030316180513090213090b010e16030c0e0d0c080d0c05030714010605131b05070206072604030c050a0602070803041203140703020d03110c1207060f0203 70
    0x81d0412164503588220310510807200074824100c0c610f4025000880c1c0708810308041c1802440410030750100320083d550256080035a80f20465140c01ca14102c10104090740d0314501039040aa06901a00075070603604244001c81d40361103424681140140360010341c0d422460412203158203081102c982101d6803030311042c24401c00351306400a8684160498010b055040800c5a45840c071701000341c0190018804040000c003a0290b142542100d6800829010346030400601d0580c400803030181c8495560310740c08940101071840c0c0d2a00368130360038242c0c02e211854010520710f101b003407001800003ca4511000540d5004a18048a104c404248903103480d202d10707102020a0003801020710520608800084044c0300103200d0341554003d20203175003400c0c946110b0440f4110010f2044040c00b086440c0c1c078400400d00009058114040d034010001041ca4120240444600b101480011032081001c41450f0000080707920841801d602c035907985055038104000200070400216650038000030511444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 185059586 1250 185058336 185058343
    0xf060308090f0906060706021e0a02100605010215040803060117071107121a09190c052d0607030216060c14010203090706140715020d061e0b03070c060608 68
    0x41d0744150b5422403015051410031100580840320b42d40d12800401c840360004441d03030003515020302c441d04a42038081035103c80c064190000441600180d11802060149070018001c14005090030b00103800a604c80d24010003400c40300403c05410380c0c03030000200703050fa4440c150309c003001c60001440c602141400e01c0001d0560010032445000c0d4896040c003ca40310884001c154650303584284122080a01140d40e0080010002d00b00c0100303000c0c20240782001c460b081500c4816602c184400000c0e1401e140c200035404102c42180600303501c0c101e81c400c2c010b40c041c1418880710042110074588400051070300320b2818052811000d0214401c040000e4013a403c104a408168480c02d902e0f01e040da11581d0080c200c0c0001ca9410032294050001048124060241c0d070103805050404a4a0101765445000300c5083d034100302011940d00051400b24024540b00c1c6501405400807038907460007609122144142441c041c0100c00351001000c114000d018440f03480a040e48090300348581d640e0340520586 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 185060836 1250 185059586 185059597
    0xb01030c140402180d05120d1407050a0e01030b0303041d0702060c0703020a0303110c06040b01060305100e010510050403050a111008240127030606060813030c060f060308 75
    0x40c4155011890240c90207000761100070a101c4e96130300704040001d0800200c980e0380c4000f0365050140f2000c055481c500f0138000e10241919143c00305084104800401c06418014811806c0000038010729a45139400403142c0120311003441c02180c201c1c203400c0000d003184520fa0241421805c84c2401030707880c00030380803058444c00c2140c00347d1b100b51307990300f023220000c5c130500030001e00607040140e030540024080c0e4070288100f1800c00c00c0b5824a0b440507000c9151a405580c00d96181001e28010881e04d507140c010342d85e00c0b40061421142052502c0080105005e043c001c85128201001014007054402c1e02580d0003140c105003191220700a03800d0844c900c4554520036805098090142241c59000f450f1460144074020500140c4820600e00c58285500c2208020304009840d030313814100c001442c01c1b040800390711102414801d40755180980881d04035920400a100e14001000b40c64085814400d4a864041c24100d607041c2481c50514002c8c80204c1d40e2182d11484c1160102c14006030501400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 185062086 1250 185060836 185060849
    0x3050a18060b041a01050403170d0905010912140703080c130f0312030501030b06041806051501090905100b13030503030a02030711160b07020f0907050306010906110c01030c020a0b01030c 82
    0x84415440000e040300d910b0071350f034a80d0204904000400c0061101c40c0c1c24030b0111300c03a484840c20071181c10008000d80344614015205691500145400c4c04007954480900d5090b0b41010803401c1c0794402046060b026001d07002c0c09100b020030004620510503030480f5a4001c0845010740c2c0543c0b50010b4458030a900d000580f0032801001d0310309030b441e00030301c02c440c16281c1041e0340200d41e47c0d550b030405c8090441204d1007501801100c411400041050003118003404504c0c00d070000b40c0305c0c004001030200e800d0b0741c801c83e04903040c4818400600301118401040e20708040c2c000e551420300c00110802d400142c0c0c0002c1c21407000108111900300c25a02450044501c0d0740c401c40d512003107e02071130352101e8420411848070102d010812240c82540c006002a61001e0000941403000c01c00058020008640100100b00000200045503a0180c1e841000d004c56040c03414a651349800081d40d20300c45c0b40031275811715a0351001180d40d18000c10800c0b65039030340189002d443d0340e180c0c5040708415540c0d11518 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 185063336 1250 185062086 185062091
    0x6040806160201230403180905150303090a030b060a0f03032307031d01180807031e0c050603040c180e010c140337020a020c0111060703050a18060b04 66
    0x3081d12030b01c180a40b4015040c1100100b5014400b000d54146400c0e024004405020700f01c0c0380c4280c00c4002d0100d0400a00a406000556180070182445d012042100c201d00c29001080318a00031350b05c8100c40425a50031400000c0795659041c04502855115000346810204000d0000100740d4060846e540240241504140005c1c090315410180e0090300002404100000703200740e81c103031102d0700b001607956051404604511213040e10380c0290340345030450a095000208140140000c1302d4061035440100d0300181c0040100341c41e9203012187c64010340d8803480000020600b44200e100148000c0d00d00b404240340502032450f205c00c010516264032103069428032755404c83c1a030191600c0c0b10081403902d400c62850f5152000080708400d8180d51401201203402d030700030003c0080f0344030b0110100700309006a48080d400000317468105040300c49410099640d1481c0c18000d800308070301d42c0181003803c02207401d40703c10301d007480540000189002c0500c1d003403c4c100248981c903046910181004d9808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 185064586 1250 185063336 185063371
    0x90c030d05210702070f06020c030c0114031b093601210f0b010b0418020a0f0e010e0909070302011403010503071e030501020301180b030708060c071106040806 70
    0x240c4241c010720003400600b0401941e51480c100a0b5903040d80e014425105403280d00713480350002e201c00401604054010707444510011814141041070005805090030178540c0b00c802d0054120301d41c030005000540e220860180c1d05a003580100a44851000003008402c000749030003104510840c0032b2681180340c000f809840a5410840a000c80c1039400440c04903c41002c074010790752061070b55040442d9214041c00d0180042425000703002c6c0a00003a91400b0f5845c2d02e400141c500c1c1c170483c4032880303080c01e2040211000058105002910205840c05d1002900c003c2200507074000e00002a2140c1101040e01003082040c808142042507a03c01d88840302498517609504440340402d0060b0381e0164450b00c8280078051403070304d03940b44803c0b440d0036241c0c10079141e03540c00c5d09a0b0420780c05201300395103800030112131b50b42502030001104829401410301e07500d4a81c41c5950b074500904080d01111000490000f4440b054004440c0210050501942c4a80d00c45007180d4807039086541003451001002e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 185065836 1250 185064586 185064613
    0xc0b130b160509010c0c0509010b12100602070e060d0f06050619080a020d24061a0310050f0609040e060a060f03050309061305040e0c090105030d050301030803130506090c03 76
    0x20340016500740d58406062040e0340c0010745400c1030413041540d46283c00da01c000359950390804124042c002d00c40d40e05494052209843ca084100600140c060010201c028060b00354009040403c49120007404030302a101c0c02d010809403885100003038650003803181400b0a100320354200da03000c1c0d00195542031081c400404600328082c0c01d03004e648856081200389001510b40076405134103050080424403c80c550030640d00410aa4a414000c00300c3c0d140c0600300540121a5208040340e07510103495032851400c40011080c021a0b0b024040c8241c0282070a00c2c240d0300da4009640c07500740d002d03108020a40712240681d50710481100c1c80f040481c02c0140210301c03c0c0d10b43c221881220791100c001c5040039060f10401140d908900c141d04000741800e580058180c0d15801030000c500c2401c00a010340125410030711a031042c050b00068081d50006150711140395000049a0440c3c0d0010356442c4c0305c3e150b240c0c18000c2c0c2d07803c0c0507002d4810b11900c020300040c640049591500c91034110121002c404a031103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 185067086 1250 185065836 185065861
    0x210020903100914031801080a110306120f070b040f1a07030807180e060907020309030d1202090303041701061d060108090703050d02030705060f040f080a0c0b130b 72
    0x980d15034041e048526030880629050304001e0905200d015402d0620700e181000e00d01c4d5401c03a900310440884220a0b01e00c2d5540c00a01d2650080840300060005007031003075140300c00340310180050340544840112402070120522090000031480003e0307441482d80c550700c8003000d400501030059103000d040b00000303000d071290800007040c0b80070103801814000c080e01d007074a142d0401001e0000b0701001203198a9080450744041010b4220b2400f0944107007000c0040c0158040024081400e56004100e0680641e90004121f2580f002e039140c205010800505450081d0060b440503581504c030100d0085902c1c86a440ea01400140d505c000b0007050355034420014403240200145003981c8840404110380e5489a00040d074081c1012045072807856481d43c9207440d01309c540a0420041c0c0021800b0b4040000034002c841d00203a96441342812810181c6900401220101008003e12800590b40d0b44440c0031b000100c1041c1c1c0c00854001c4c0754507200c8250740743ea107101c032011217144010b0000a100544243d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 185068336 1250 185067086 185067097
    0x102010509160b07030507020406030803010305010b0306070e1201060803280207051305040204090f05010203060a050d0206040b28090e010e070e040b03010e0f07060207051206041e150903021002 85
    0x10b140241e010b1901e0840b80d000ea01031102902080410400000541c969018080c01144980887e03903403585542405801c5a5a9203036a602c01d410400078014520752010286d0608101220003c640c0f201e980840c0c5d004042c1680b0109050002068641109407051340100360252402c0c5440c2411195042c02c0340c880704d8600a103640000160b014080c180904d5000030350162020f000040c3d140c415440e00c09c00491140012110350b90008100803440c11319840030b10081c10b003500e07a0307001c003003680d80000d51030301440c020303034244080101d111641507155458072000c243c41c901c030b0b044c03041560351402000c1d0413460091200c60315501c4000685103298010981c424210b079503404028544035010800074050f00f030190f550642d02d80c140d494240c0740500015141b90800001400003618150000c0d0500b24a90300c114490b60040390800e1484901003803032644503070b002c003651503a03810780c00000b42002d5103800c01404050941c108615600e102d5844a011b03180250221140b007004c0210460680c8601c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 185069586 1250 185068336 185068363
    0x6050408060f1e0f1807030510020c01060e04050d03110903060703110c01061d2a03040c03080a02250602030f1309091506060e060909090a050105090c0102010509 71
    0x14000098800c220300301101e0300124104500d454601c0c032582c000a2100055803881c02030520b1005000055100075800c00c44900c0030400b40c45000d01c2c7d40c9500f61110b003040c0701c016806800154050030140c00f0f50003003000d42100148100d107400c150030100e070f8400200410201092030701e055803403480e8684041d16107941005009080030303920400101c0203040c800c1c5604154180c24802c103661041c082c0100310141021207200503100c80a40a04895820041c1c0042c12141080308441070f5032441118054503503040c200ba2a0356034407180b6000a0554069001030409a0003040030b24425502191104420b0825030544201c84d852040100c0c090402c0d21544c805a0f000300190100c0b081c40d84040c08802e030b100210200d05c2ca5403481d00d14113072042400c0450300d004002007641101005441290040c020a20b40004c2d00c0c144507003c00d04a2284200e401e120b00b40c10750020300320300010130a2407407490b80302000740414100308015694541c042000d0030301550a01c00001c0301c0c2d900005078481d01118 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 185070836 1250 185069586 185069593
    0x3051c030f06140d06150b1c0b06160f0507090b030f060601270e0a020a14091c150e01020c0705010e090408091522140a050f0607020a15020706050408 66
    0x851501300003084089420840d449a112000741103840143d608620041c501e06010355a2607a408103903216100351440700205080c5400c2c8405d513103854103415260300041e0107451f01545002402c0c903920055984000406501c1214804910101075412261803840103804580000c081804455210402143d24600180d50104a4200d440c54482c025400c1d800c549403c090041d1a2101140000d030211918208960001008000c0f6175110380c0204041c0224400a401d01c5804070025000c1a50303404171b61001c030052258242840340d40030754482c0000326001d040043d03207041d14801d4083d400413010329119000b0ba040c00a007650181803807410500f00103052188130755499480c00d40d103400075038620b80c0114044040d00b06c511010780c001c00001d6204c04143c0b090501002c001c60790483c0c281c01500d0b0904d0814102c07685174032800400c1041c0d60088600403003051401000c94894003610102a600c024070440003d100c20114840d20b0141c0c4581c6d09440500b5243d0000381c0d100c1c4100e110304011a031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 185071942 1106 185070836 185070869
    0xe04090b151807020309061c0c03050a0b010c0b0a0c030e0d0507050607050711240f03011502030a12090305042d08010e1005040c03051c030f06 63
    0xb900c105240040c2d1420400007901c9004a68166005150218140013000300400302004860b58944003080404071442005020704001d03221080154900006480a54400c0b180140e140e0f82101c40c0d1002500e4018506004001c2c22086004140e83c800184906002c140014000e08409070790b425256801d0b030810505061000c3d21810511204018000000300142d40d204650784c0201c40144e400c4120480d042c1c10405400c0c1000380400700021910740c189c803550b000d58140d50045101000b400c44244c02640d492080d03294803404558044400001587c0c5600205030b214800e00d021800c1903541c02141080060030ba900044401744c5800c050424103072404502d00800c41c80c8000e0280700401d81002d03440380140c0c40d40801403a26140014280503000d809072000350b50041c100c841d1301c4604006840c00e124091a4800003d040602034000410140900350649821114407046803 = true := by decide +kernel

theorem cover : BRFrame.Cov 184892086 185071942 := by
  have h0 := BRFrame.cov_init 184892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 184892086 ≤ n) (h2 : n < 185071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
