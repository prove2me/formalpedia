-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4875
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:25.288968+00:00
-- url     : https://prove2.me/submissions/ba633463-3e99-4d36-9272-7aa27d484264

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 876618705 ≤ n < 876798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 876619955 1250 876618705 876618791
    0x80c060406050f0904021204050c04140711010207080c0705190b0a0e010314091e060c0a140d1802040e19080a030642080406050a09020310 61
    0x100c030308503101480c0c120b0303d03221090300e0240a803282454896110b4070000f10403020b9844052420302c100e025100780c8110007100c00a1006482000b102c19051034650f40014280c2d40c0903800c6100c085420030001030504a80d9662082680d21000c00701c9565805807000304018508001a1a52034441d00c03c01c03166a46050a101c06602641c0d03404401c5c40012049111164800d0740400100d007500c003100c0c1d005041c0100e0484c2c540d2203011103845d010b1007002d03107034142e058000754050190300728030712280c9407000d101d0341205c002e42d980031311013685002003201070101040c6003c1c144004c0862005140588800d00c108022600000d42c2210150460542e4a4030180090414042d440d044100302e692851594400c40052140340c105041d244449508648101c4100c3c1d124009568441c805c03052401d024441000c2c81c003c011030741000071304000001000114183c101a411030340d10000420680d907641e00081c284071105808200d06503590007802d180d07503601070703880034140030150420f5109454082 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 876621205 1250 876619955 876619957
    0x6020c01051b070308040f0b1806010b04183801180e04030c02060f04091505010503010810110d0f1e060f0e180d18141305040606081002090307080c06 66
    0x150150505c000032000606029504649074074403644903180c0340c55887c02034440c50b48034040c3e403415038091081c4400801d81c0815a41264250740b044544500d101d401403e502010744556003000207140082c010019000c48c865040300c0e0b861a05000d1201821070710300005000c041c0d4884004240101954108204008801c110703400c21340619080a50403402d0010880c64443c010078a030f50b407000010002400c0c18568070414081341e28010082d03200e80d86500440d440e0200b8001d544844e003286a180c4022400c40d485110707150b1195503d40c0c1000c1c0030300c504000721800070703001042854a4a4805004060b8042c2d00a400300c100c40302004460308023140c85100350310500a8030409000315010428000d1040d400102400b12041107414081c90120010441100e601848404540030070000c2801482001082d07a0b6850140003d003c900c4084c0c004005071101403c107986041ea6458042100207080c00200c809220400016955004401c245460f105c45540010500d0308203180150080d076800e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 876622455 1250 876621205 876621217
    0xe090c0a0318050d0c0213020f04170a05070902030114091b1c0911030601170d050702130c05031801060e060111120a20030c0703020103020a090e010306020c01051b 72
    0x21400142220303040010b90258002c80c1030282907486506a0308012a61102030035580610035103070240c0c10703486030401c4c400703a0003203803801c0c52842010704c41070002040312800710f10710350549001c940c00c008858441c58109282c4d5080948200d0300007005001d403010901800b1000b00003903900c04502d261080b22640890001d02c40c82054500c001041041c000b84c600e14000030304000c03102000340c45614549800307500109600140a03000302c500006001c041c0b0780c1074224140189000e4071038000444000c83e80e560041000301d91002155155071542261841070048640302c644071700c0e03940d0920007540341201c52585507650907a0304080342440303105607004002d40c000c80282041c1c3d840e0f40400783d4090814844488000a000d8045154811554051411243c510201c0324048402c040402d81a40f45d01c01c04655901607805202c0400c0103500c40e500800b44050f0b0f03490551444ca0319400c404940f94000e07801628010380206401554400c00c2c412540c0100e40e03506000500003040aa44426018034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 876623705 1250 876622455 876622457
    0x110c090606030c0d050a0c14070302060f1008060f04050106080a0206180402040b16061b0c0f03030b100c0507061b0b0705070212030d06060809070e090a020d120e090c0a 74
    0x300100b19100742403c00d031000c1d030300721200134480703841d0030030200b00200b04010004000441c01c40a10881d900810100c9040c2605903010300503666864403001d107403420181c50041c0301c0c410403000107824402440003034013400212900c610702d410103003041030941300380c0d80141c01683c01a03e4003074016070303404085070851109108042200d451030300004000b030055501100c9136041c000741d4401d03513080e0360035a031078040e10030a420032102520090160084e944140c0c00c0000c503004800400125401114200e11244a454089025000640130944c01090030500d100415003e43d0050104036050000e0005444c261030048080300300c3d02040c07840340ca2803160141c2450540000704044500c554103c98409401510070700e90400305580540e03990340511034074070702c00e40740c1500459020320642519000c1e4003075100070a106030034000021ba401401a0180c0b8040c420083e108006848540348000014024480c4c40348801c00f00c1c03000f0340304c84181c42d05c551180f21102d04000c81c461000c000d6031181065 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 876624955 1250 876623705 876623707
    0xf070f090b03030702090403050a1202070305090d0f0c0b040e010b0f040302120f0105072606060315010314040f120f17041109010e01050307060e03060115180b0901110c090606 77
    0x1072000030a08602c00c00718065040941182000b06240e0040c0040540a1701a55400305194020f08800c0890052604c000e00103003080080c00500d140000304184214000c101801402003036030749003040c10500d64000e9000c1040850100f00e1102e4000d00b0301d0050507006541482c120f14002004840d1041c0d000080c0701c2c40c0002c208048001e0104510038131724070404002c01c03c0b810070b04c030301800079580c18020100c04bd03100d2801c100210b000f01001e41c06030001800541c11516204030030072030304059091540c10150f40b440c20314a80114000041e000354081c8010311034000c0d4608044009040c84c034180c1d000d20a10b0b01041c8030890340325805a6400e45141b001baa02d58030303145030599a464040840e10f5010350501c1c00030900c0340010b01018101c0d6011000c070740403142d590300c0c2600c504051805056054108100410034000c044800803801c44c9145002c0391020109420b03102e03c030314142c011441c00c0c000480c640c401540c021050000c0400a40000c14404039460b0009401c854000d04250003244 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 876626205 1250 876624955 876624971
    0x90311191e05100f06090c1106040839010606140f031902070c060801080a020a030f030912080c0d0c21030b0a03030e090a060b070b150619020f070f09 66
    0x12042c00450003002041c0e00c1070201c05001c0340c008000d0310171030040c682c51526003c00040e00c14010300f0081a0020360308054075960366291260006030300520110324000b03100142c2c01d80340b000d003500c1c0508020f00c03c0d489891440001c042a030b003154115001602400000400a8840352019007521003d0021175982c40e83d0380d9800e10b5401c12402c00c08003110185002207084e104104200c0c8002d020394481e5030380c210a42c0c0e070300d0500607070f0b40400407006504018502000d10205038003a00c40c05032320f40079080c0400c24554501c1e80200560070f17000191201e0001088007105582c0c14005142c8600d142c1c030300488842c000741c0700d0303e40280b06044030709908031129200110407800317034000e1600620f006084019503684c0c1e040c0079000010b04030509200c3c01c11030300010700219042c4a0708050319110204141041015030700c1c015821000760103621403160789a040c00aa544800003041101c1242004080902e0300c1f0078040c1c138103076450f8440303c2150400072060104540720203007081101c05407000801c48031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 876627455 1250 876626205 876626213
    0x11416081503010b0a0303020f06150d061508031621080a0f090c230604080d050c010b0604030f030314090309100e130606080709060509101101090311191e 68
    0x4802c1d413900fa42c0103161a0000400e05401003483ca81d03001000003581c2e0f565440d0780c80108070440241881d41e20045c1c035084140132032002d03440140300e420034103101c4407010b0321078414901d10703004034003030380411140049401d040018a540080300a000409242502d40a988002d409072400800308145907642d2034030301d0302e540b0300394000a00840c0c1004000d107580b52a08001c01c46450a948420204401d42a09100e036042000440341100c940c0e00140c41d0345081ea0204803010f5210a6600920b50340b240702e005800d40c0c40a008000851141014020441c006e141c0642920307000e00c09086000117103410881040800300854412140c112459801a1a110b5080d0350420100c8652504490342c03060211285942d98407a005840e0f107601c91900690707032808100c3e43d016150050100050050050007290b00300051a1640c0081c5c5040c401a07001c02c09481c5402c44100c0b603001c1d000a0b4014001e40107174402072146030320958041c0421030014125440b07142d6030000034600d0168a005c1064168280 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 876628705 1250 876627455 876627461
    0x120402060327010218011403072115030b07030c080417070f060203060f0a0315021b0a0b0609150303030c0304030e03100905070509040302060a150b0a0201141608150301 74
    0x40d440c1004030030510001602c60003500081c141ca075007554220204811036020b051004580d030f40c2c00002c1c9180d0f544181045444188100c00281011030a10074140c1c1000c0c1c60168510078a1031070702c102c140d02e00d1800c0015200d400640541e041c9071030000314618142c1c1c0108100e0740950841d0301c10204081d28400300c900c030301c181d4001810060341d056040041000e02c0d0025400303040d0440b0400e00012440301001091519444000c084100140d4400c00000580d00600300040d50b201c20a108450b111108604080b02a03104803614a010341c10010359113050180241c0051130f2019074a8a81c80e00808242d503031101134900300350280c000c0000f40415205200407850a240541516441109100d1003005800c424000721110b010325080890a03041244803e40701f150164024009a210380000400401c070800a82c0d0b46040c0d070f001c0102c0c1c5040100c2c02040410400d5000082144501c0c8191001110141002010640d595800401c50394060400c03900030800f802c98001001c2150300007801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 876629955 1250 876628705 876628741
    0x172104050319110a05030a260309010905071a04090f111209011b0e0d030e0411131202010c030f121a0316271d061b1204020603 56
    0x71500c07840c4001140b00ca07201c0c0c86204030350b1003254040300c1014650100a441201402010341640c003034160030003c1240d0781e10090700184403482d850b841850701d41d034180d02036008503440880c0f40e4407010340c0c108005042281070300400000d48441c0407401c07240f40741078161203130388075004400340c503442c221895071801c2d4440c506843e503240c10940e03038940d26100c1c03402d02001200c2511155103003444060900d182c440444103003401d150359500c0510381850400a4003c0c152500703904001c2c103420300a9564503070b8071442030000c940440181e101c18000c4044441d00b0790075044184000f03610700310800140d8001200821850341420440810b0717441d05c00407980c4084002c080002d1905000740c03000d03007400d2241c0589040c08254141c80b45003400c05059403441c81c0305d11401110502d0703130041500c521200b503003e4010054040001c0b40d018614400c880c031a030203455540446410060501c1304006400300903000c4454039100e900c1c20710708030b058100401e10b0020006801440b0000000e04115410450100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 876631205 1250 876629955 876629959
    0x513080105070e0909030906030402060c010e0a0803090f0a020a03060b01140a0504050406051e04180b0f090c0915090703110705100b040902060409090203010204030212100617210405 80
    0x21981c903080342c0c001c00c1034114406941c040c0b500c240224001242c040201c844401c030281069255442ea5800e001c1140d00101140000355a902d1a000d412075041c0104412a402080c0c1c00352a41495403440342071132003055407445c055118603910300058440c105202c1c110380e000700000070301000300b00060f103040300380001030400c44000180049025400c20058000c1d030300c0569041000a48a200340f10322190403030201d41c01c0d4440c0f0a282c03000c9113000c2d048925141d00304840607240240e075075a14500c0034000d60351540c43c5c5820204119070f070441003114101140003141d41c0500c50804000750441040a10078030380c080c2d035620f07000a42c0e4a000703400500d100e411002d09142d482560382801a1501c6040c540c03d081c0c3c038207020500e0800d1610f8010b05c0e26144d001020186014a0002010010b05540380101d805540074440000035036140c0e010030b0582c2e0304010280400203980c0000100b101c0700c1f90444104006649420092400009912843c0412081007550b03400158401c001843c01564030141d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 876632455 1250 876631205 876631211
    0x4053103120921051e04031505061306140f01030c090317040509070201020309010b01021c1d09010e011401030c081f09240906120201140d1112180c0105130801 70
    0x12003480c0e01c080204000110600c401e00e107110170f002c5114982c840d6100180c440b0b102c0a109001a15050303000e10380010004080640342c10701a0804000c1d258164000707880c0a452314030452090900000001d0381d8402480e0030003003107200c000e0151110700349000c0a0f0008501c4496480c09209410407600a0f21005010806914101500030702039807003207442c04455420040f180c0c0c90b80d40000785c1c1c81002c14541e049907503e01c1b1102c200b16016074092890f06c3c042c0c801003c0300f64003511049801303070180034007024203500c1e5810310000a107800315580b50181014504005c0c00640d60f80f00c0041d80d0031040c091220156400031010030090451aa00102145854500c5d03010390300e60210701807034a90448104211303690755104240c07002c0b2a0a4481c00250345a5035006000542c403640c540d071007089a0b0402142040185c40c40c0c03d04517440c1064003c545040000d606500324030380002180c0c03081403c90003400c2c08002d000ea007511007620b02003060602c800450b5032501d0380c004503d40c07405042c44000070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 876633705 1250 876632455 876632513
    0x70b04090509070f360623060d0c02120a050408190b070c020609040c1e0819020c03210a0b040903120b030a170d05010608100312030209040531031209 66
    0x2010041620f40308159150100411019016042c7d2001d000040c0c0000c01e0541040c441c20780074405812034841c0e110442c00750384440d00544141d00c024041100641c2e5500e6180d6050280e0503280c00768500c1d40b440c03001d5669031108000f500407c100c03039100710709203031080c0450781d284041500e5004450b101644541841c280085c840d901110461041c004465500d50038800350401303403070102c81501c0f01d588900000c17a55010701c0440e81c00904d008541081141e141400d044400d50342010490201900009107000380980c034040b0b4040c0d00140036080750700b003150300e036150b502401c800c10900c400b034005074036020404250390301800000061750f003000c40c100c0d03c480781340907080e9182d0108000c110b145180c500041040f80c807454086102e50b8880707a544a4490464480c0e0040120184095003090340822407090651514001c0a0043c07200700060b840705542c13041041c02e4406140d840e49a5184907002c0340700800d500803a0400012440740700081c030621242005086185c0403000401150240341d11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 876634955 1250 876633705 876633809
    0x20708040b070b150607030206010918050a0c150e100815030f01052508011e0902040803070c0602030319021305030f031903050f04061a03070b04090509070f 69
    0x43d92003540314982090f002c008200411170030b8000d001c2c0160069200f60b005008074400c80d84810f485840c0b00000d02010a071980d2101d103480e00868003181c100d0384030b100400c40f0a444451100302014142014000401c4500c04520400160740103041080f00400200b112641205201009a00c000c0c05480c50840c51040c528040c000544440701b80b18000547c03c1441d00390007054002c062a50b50350b55106900c0c20581420b000004480d01904041440c1d000031180340c6031004000500e0304001454039030030541491205186981d22820030740d00b0400400041e1008114030021072001d00c14016101c626071000e1011048482d007140e5007512410569002415000004c1c0c1403442965040b21600c80c9000e00407400d0303400c10748800f10032030307000000f2400090a0742c112510154500149078405400c05001a1400e41c03154019501c0340b4000505002003000e81c05401d40c0680c19500403d00c1514160900240c0c2c219840742d814010000b00c123003148110b08054000c411420080111468100c07203a0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 876636205 1250 876634955 876634973
    0x24111006030b15030a0f1406040308040b0a090b06012001020c1e070b0a050903030d09110112140114130c030f1a01120f091a07080622020708040b07 65
    0x80d6000d009181c00511004094003c03070700c5945000c0c014001d541415540c1e0b86408004c50341c04c0b6000510034851444011041110f0b0780700d43e000baa111b5100f82014180310602c8480a80248030b12030401c030142c00804c0d145141681c1010080c41c00130340360003a9250514402c1c00c0181e40020039400000d044010302000268130085003ca5800d601441d0103425606607a54480d21840e4907a1105001d86000e0368001d20181c01032041c05419a4a0001864a01350813208044000c95903402940c206201559004d40c0e1425000100c141c1044404400144050414414894000c040900650703003c0f00e034540c862000c072004504d100500181103010000742c013410b039242c8040b207064a801c0d01e03204640f00010f80242c041d28103868042a8074070a1040202510078001c14141e40c94562030250006070309080c2c500001030fa9020044118280044024075490026210317074814094403602000c3e280c0301c9841d0010900b4601801a43d446951401101d54062a03000003400d54000c616001440b170048 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 876637455 1250 876636205 876636209
    0x3180509101502030a140702060408031204060f02070b0112020402041a190e100c020319140d02011509150f120b16050d0203090703170c0105060a24111006 68
    0x820b01511002402c10490fa03c5c05030100c1640010071a00d0340020904540340184165800940403d280640783c04185155604c0000c640300c3d44001c13481000240a42442040d0f0300050285065141c051031f5103948980315018041c00d40c1c58566022103000b150703140d034105c82c02440702180001d240d0031a91240c62280c0c1118040a000d604101c900c0d032030041c400c0c0885003070024020034140c000203002d134084401011821080360540b15030b400b88070303918007480b10641c4079500ca000700035000c2c44818011401c00e82c081814034256810300e00381a0a802070740b2028401c0e14450392000445d0b90081c400d07203030308440c00d5201440d00309022801280da00c8804c15481340142c054a5889916101c2c10052402ca440312254200022814403800309000095001190050f0300f420469404039281c1d11070003020f20001e200312202000000300500500d00038004c65034401e100711140c035582d610300b90130f800c240c24a1000b02c400001e0700d043d0034225a4003c1407115908004101281c40140d00040800018182d134 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 876638705 1250 876637455 876637469
    0x2401030c060f05030115030906020c210705190c0306060b220e0c0a090503011409070e07142b0e1b1f09120c0306050a050f040318050910 60
    0x8100085078450007040401154400359865a00d075a00e401c0110843c190f190076a603003019258039404001c41d00600150044428040c081c1c0302180000b01c21200320320b070680300200100801c2c0140c40124a010446104111308404e40350b074000740b185071007044d000d040e4000070f0410b49400b00100304c1d401a40050801c500300c04041e006000d0807001c2001d001c4046226140840000a00040d180c1600101402d4004428140504400d890300002425214144003251444480904210681004205400060603103000641d0541804640104083c05c40c440d40000c00070005000c0002c900c00d0610140306030080088090b01101ca0030809016002c40040401c088c4504001b0890328146100f50310303510000200310030742c00106540007900380a5241c0d80103040c41a00c0b080007455400c8610b41c43d40c0c003480740c0846c411844c15850007904aa00c0506003001c81c9250000b001840c007011900241c11903054104100c40703513440c418190000c0034503044135400160042c1402500018000302c03906032488 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 876639955 1250 876638705 876638723
    0x5150403180b180607020f01120e01060b03040c0509090a03081306140f1608040210030e0a150c0516230d1205090a0506070302090301020d110a08060118030204020309240103 76
    0x10700f50810032075000b15030700a54407000b00346400780198024480c20400c004c0c1c2d1000440c10034411102c42d07003100c1080d03000c0005240300008020400207540958005460102c400d1003040c2041d01c1450b95404201034010103119181c004141c55012202003110380561000d801c3c848a0301303c505862500206803501c4030140c5480f004120401001c5407101d41d500e4240d500e9030b1b1150b0fa01d03020040d00504404000d01819691280211306c21800d20550000c5801610243e01c680e111960020481d1094040d2204014060029034001906038000d00304a64008080040074000c1ca10800303031b081c0c807071001ea1209104281d0b09104072074001007003e588002c0301d07100b08859520302c04079944800f00008020720303980050b0f00251040d4043d5000c1c050203103015000504005050300b051084402074940d03010141404034011054551200401e50b2203403080c81d08100780014001115042e686a0200a1149402200050008c881040395059005505909441074800b412010700803040070300003643c01c986 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 876641205 1250 876639955 876639997
    0x606050702130203060f190e1f09021216020f060a0e010e030405060715060317180a051e0301091b03020109080c0a150e1801170a05150403180b 63
    0x440d00c2520301c02c10303020b07080d141c07134115030820003540c7c405010300c1841700d49101502103803010724000828800c1503117618900c6101c0c0e058443e000002c01a40c0f12001a90040014002c510802500e403900b1041e2882d841c1441d00405000340d041000d038400c8a25548646800c100440703040e60030880109030810020010010b4400119071240309900030350380c00050030019000026403001d801c0e641c0107801c000000d2025102d980795007074408444201011904040f40c019101c07059022000c00708902210061300c1d40c0c1c60305001c903468810207540800410b82d05804d90090303480070b402c40582c080e4890090302688544607105002d5440c0ba01041e80011829400422250800584020030b55002814400590700c0c10380d00b25015012140d52201704a111654040280c4408a11110250044421003165030414082c0c2206d03109070b2850071102d03030004000700c002c5100402c0e990000107a681421000d595603040a560007042c1c0c4078030f20380c282403400b8002b94081c484005000100c0d08460704d003191403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 876642455 1250 876641205 876641239
    0x207050f0411070b060a030503070807020109050907091a09030a0c09051006140315061201080d0203130e0709050303041e0e0606191407140705010c330606050702 71
    0x900c0300e00c00c1441c1020304001031008100c045130020750203c00200603a40d40c40d01d903a9800d0960300062011941c121001c1138202c11580c0218040000e40800d0303540345030914101c0401810411a8490190400e0122420319076414400045856a07100039040b104542460302d0300740e281d0344940c85010aa18545008a9207514202180c18100c1e41280d0b1000740c0000c8009040e0708540c030141c0700c10b0307800741d40c902d09031410303200c142c003030050a0b515116480380c0b50300d0702a0340d030f0400b444960f0b504c003103400400030501e21042003107907103051760100d2143e441250f440c0b000945043c046500704542c10b1001050010300007020040525107140410071441002c0d071f80d1003040030390380e4082e51101e50010083c03080894481c49070500350100050703854481043c9641c0d14440e0319036405490b040d070324105031140c02c00c1051020001c4a00800003880c0c403908102464440c0401c030510b41780641040d000c10880340d860100d900b00200c0700075218940400000c1d41d204000f900a0303000e010124000c00c91207c03182261 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 876643705 1250 876642455 876642461
    0x501060e0c0a03020c07030c030b0603060703020313140114091c090609140316080a02010201050c1911070306020a08090c03070b0409020f210103051506010903031b060c0207050f04 79
    0x1d031000894941c148010510141c0180d00144100229403040120000c04954a400c804004601030381c1c1107225410030301c0c140360800c44001c091405050041081c0420804070341a56400d41c0c0c0c0060302c0c000d003461a10300c40ca015002224030402c04850a205003e0710080109882e00c000004a0000c9201010749009681c29403003480340238003082506108100c01d044114110a1510004040d600306608844c01442500f0043d0002c45a5078403102300c14045580904c6000c0e0410000c1003c58107106400c040102300300725000302d901c10010181d00d000e070213110400c620b201840c0d02290654aa01c58100c000344068012164801d1350305c10b6040901c07160402040b42c07029902000750070ba01c1c050030801481c0180d44000d60b820130b06107080203d100041c48802d05085041c1444031151025451410039a2a000c05108000b1840c03040c08140312440e0b07004808003080341c1e454181354007000740441803562400c4c0e038424007510003030801100601c0e0560205004041c0e5100b204c00140f054801c905102c21 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 876644955 1250 876643705 876643711
    0x29060d0e013827012705130f020a080102030c280f05182115090a0204090201031b02010501030201090f030b0c0706060803070f15020909070c0303150f030501060e 71
    0x4a86403640702c020309003009000008000a40c0d80b024501110401c8007803d4440264030070484a5040322a40c0c0ca00c0d13003402604151400c42c03541c244120309260000400242c01c0141c0140640f0562040f0411500c54a4860001307103100c4c4001c42d185e00e0301c0d18500c1010382c805450118000005640107040030848908208240415900c20203048002c040c1661941d1200d036014070784600b03130b50750103605698a10100480031944107079002c2c40248096994070b01041c01c1c4e01401440b9202c0d0030003402e01400607030480269012280072800c881c0e98001a0000c00d5444411225402c40e4030b185443c443e0150080c0741200c0c400e03a034040c0c5003540e41d400011192060700000300500c64010200f000c01d00d541c005007028034083c0000160f521350f1002ea051075a40070300c40c11500b10040440e12014030070349045040403a413020005514010b08040094440a002856002480004044841410701c2035000854011001d15100c0a5503103406a00000e5602c510040f034166080540c0800c000307a02604480c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 876646205 1250 876644955 876645041
    0x30f0203011104030503070609061508011b052106010302070f06050907050f01050426030c060f010506070f030f03060e150325211a0402031029060d0e01 67
    0xf08121552380e60b00007400024105850f06515443d48035907048006296000030f1080c0000098591801580d600c500004c4951480902c0000e21900c3c030303110000d03004900780b95504030322102e21b039403260010b800901407094098109840d0781d15113002c00c42c2c13a500c924052242c0c20111071a00e507444007000401c050f1040010f0005801b484100718141c40c020441e00110001103d9083c3c4a40c46c00c00c20b4910740100e030305a04035500000030300003d0750150758613601503c0d050329020715240542d103d01c500032140c248024100b000c162503180d01903100340d2104000c0c040c01d412a9441c2c0c108000c0004464062450182c401c5c082c070340620080914485c80e6001140314003c000b581c945c901a4200d1503804161561300a0042d5080c11200280c2c60300403010300400d0114410060b42418010b040c42c000165004102035490720203c81a802c0501d02880b21451001c600c1030014187c20000c64998040d1100c014059030802c209185856019040b2000541240c2d10000b01660f00c0c1f80c040c49180d000b429191 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 876647455 1250 876646205 876646207
    0x4060e0c040c1b11031501230a060509030a05070603060812030108070302010528021c020f060c0309010e01110304060e071413180b010602061e0109090507080601030f0203011104030503 81
    0x1a642070710741c0240c07403001d801007444c1181451010046030034844074400300b03c125044180107004001c903481024150122485100c5a80402d0001140c1440610b0142d1424001d022410880c155000c0044a503c26444026610700301e071703a040b000d00074007840d0103425158099048a070036401005004d9034120b0303010500501c001440e580056940b9804a19a0036a41007501e40c0e0000c10814140e400000e00c40c00e9000385400d005264040c0f10704082c441e0f80d98115080a1100c140a507000220a50460f400c01085a0b990700c4501903140189010595443d071542008800d00c604500040650700c04c60003200300740100304200008a84814850103000b200303580d02140c0d450203040c6801d000c0c6160b00070040001e80c41850041100d42d07404c1c00310040750805544030051101e1581031240c243c1040415440041c43d03a02d02184034a00141401105901941d407020301050000070810707400140442e800350345055841c1c2c18511100c0c45042c000340e00a40c00c19000400f010b000382c3c101c40449070010055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 876648705 1250 876647455 876647477
    0xf010c020f01290103110f0a020d0c0201050a180f0305070f270506010e090a0906110c0a020d06060308030f01090c1e120902040c050901081509060105070303110304060e0c040c 77
    0x201c0f8007081c000301d0241c101503484100980f00041b6100400440030720a00d8151188030004000340783c88440403c00003000b07c0c400d0740800603600b110a8921040c01801d1400d00c1d480300711048544100380342e00084101844000010500034041216816150b14528800c0c501d5180c14640101c2079007914a0300d0a407884181340c029040301c550026801090500d090780e10032050a0019003100c80583c2d180b442e45958107444401c200d402d200b1000c15a410200060600300031400e4540c66044988020340942d000c8005102008020b0340181c01031a0f100410303948078140112004424542400b40c0e0590324075201c40300195900841c4030502c1c0101181a583c5080e9440c40203d6135058205141da0b03005844200c00c43c016170780c0d409810401100da580d9035464442041c001410814040e021004460103082500c00369283e01c8101d90b4010750a00788290b4031030441c1303002c60080c0604c0c400130128100201c1403104108070303900141c0c82464030004440c0f04803c0c6404110032580c04c05c4291020070007203006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 876649955 1250 876648705 876648761
    0x21902070b040e040b0903070c03422309010c111501050609010219050606131802010c140d0c20030c150c01020433020309210f010c020f01 61
    0x109035004006a007501e06040613513840c3c0d0101c2ea80345e0021100890350071840d6a000c0c00d04200844403a800452100444007400c40c0001e03e042245e95694010fa21240550fa80070303940320301da030b6330700d907407503400e81440d03d01407500500034211b441000f000208902d0ba4502d140c00c001600d042c0c0c00c61181410351a1342d280804000c010b034440c208003410760040d0045800304d03002d44159458401e0082d0007400c2c15181c150100443c1c0e1007107201071015640b4080b0200c40d00d59004440400581c1d0a0806640d01c1c038450502c0280031620000041c910300c51403980a01b100c1d4424900008540300b80a031036801700d0340000180f00c2280c00c1500603010ba119464140052400c10100c0ca01c010300b45160a2616003031500ca5400d9a226810100f6554a44113202050714400e10300b0f035a0001c081c0000382032101c06030b14002c2d200d01c82e0025a501c203410210301c0000700001d0f600f100030200c05020440e201c0d54841c1c4e0695010381002048000503014598a1059103207040c0283d26032040042c410540690a00c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 876651205 1250 876649955 876649973
    0x5101107090507112406100203040306110702121c050a020c0f010306080106090204030203070503010621171c05060109140918010207051609021e09040f021902070b040e04 75
    0x40f4100c208190360760307041454801801910f240c840c000c822040741c1c180200c00300280407405400b1701e0090711003183e402980e590100c00e6806407030303000c900412810140c040c000014084c586000e036201000c0c0710b4100300040d0028201c00031603400c030054142c00d11403100680346805140308000150304620405025403030141080c007100c4205060016402d46c03121019401c454485d0000c0d00c0ba03950001c1c0c140f05502d420401d0360f0007044110028001c1905020712550803c54240d0419070391032a062030721007040620382030400c40010081c0507984881c00707080c0b01000d800c074007142c0c80c001c10700e048080303501c55101e26042000d0754859000ea019541801044c000098030041111038405510340d20342e04070900078001851a01c0c0a90010810804020032044090660768000d002440c810440402d0081050015070002401c2003030141d10385982c90040340181130b400c0e05020109200240c200c5543e041c05e86080e0030140d480e400c07159401c5d26196805003611803400b401080301d1043c0002000a50924 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 876652455 1250 876651205 876651211
    0x209070c02030f031b0708030a051c0b06160201031416050c0a0f030e01080c040e040f4814120a0b0901020d0b06031302092a04051011070905 62
    0x340c03c50300740c0c4510300b22207410354000d104080000705240d002a00c0b004402c0125401030031340c4901940c601041403002401a22942000c5104501c030800c50f8040809243e004904400000e880e40d0f9170340442424400880c1014081240405c1c5484540480c1c2c0d900e28480601c00c1103c0016107010700a8100244c030540c0021341d0140242c4181010762001900c0d82a82c0c484052107902d03043d801e14044800541074600051103000740b044144010003451514990f81500a900a84030514411250400c3c03c144c054a20b0285803600c0001081401014540103403c00c0f1030401706031010b01d00d000d001d10482500544101800c7c0c0c10300f16403030789051402440003030b003c3c41584221074092543e9a200c840104040320002003a95012a0380360844175940201c0e203900c0021034200345103207084a00481800c01110003e030140944c0000a408804100e11501400051242d4401c09110300c028280b802d03401801050301600346104041240c6004594080f03000c0510006040b80300c2c20b204225000342401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 876653705 1250 876652455 876652459
    0x80a0210031113080a0506090a03020c1009081b041b0903080906040e010312090609050121020c011104030c0503010603080d0e0109020d060504050601211704030c08030a14070209070c02 81
    0xc202a46200f41940a500000d0800b10050700c1c60f0412418002d043c90340084c1040b82d10340143c2c014000007640440d6001042c4411180007a40c224506011105001d186c1c002c92a02d2043c1400b0b0f002c1c1940c0d241004822110850701440010032140b000803107801e0354045440800c40003075050000903040c2019000245001e0151030401d030b03a900c0100c40190080e8000d60740148100c01986020394414400305c00703400756003840d410350f610300400280303402d009403c3c0e0030b03503c4481c8428003512820b0350111410001640024003000a8601510b0700a51143c40300703c1d1403048911000a413401c040c0141400c032a00030f8890750a00c0ca1980d06a005007981c411290195507840322100c0c01a0707150702084e44000c0c01420005100c1c41d2502e80b8615103407042c0c00c03088100c1912076001c83c0281955a001c5550350f4004c0300b0090250ba0070034464018000c640000b491050f1001e40441e10020000142002c0403455441806861014480c0b001c0c92044980103501308070078000040c2c075140201003401c0c2480c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 876654955 1250 876653705 876653707
    0x90606070503070f030908030f0405060310050405010807090f200a02010902190e060904150e0703170307200318060d0f0b01030b010e0f091306050f010f080a02100311 73
    0x80da907a42402c56010460481c0e500700642041801e0550000c000e4018010f880300035460800e828182078481e00461082e94860f940000010302c1002e4110f01c40402804082e20900040d610780c005640c03145554010301039024504045071424507114010014861320080b86201070b4081580d0313480159010004c11801d44d9201d54005005807580700c5d411415201c48900880c006051450b403110786140904024424102c03a401d2102003001c4ca0507090050001450002d0141486500e0505200c2980d101910540e14100c1c0721810140400c02148699650b60720302d08020000d940c006444242042d00b404194014005030b11025070307440d0400f802200c02085242403c00e03080712141a241c0c62140007069a40701c00d180032403540c060040001c00700b024205001c48a01e1040406c2d00030b41e241c0c215522654a0a01107441da48031401750400d219085081171026261840d000140f0103402e20501c5065102c4800c00a105600480c100027071690003002500003d03400c000803005800820240c21502d50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 876656205 1250 876654955 876654967
    0x1030f1101021507090510020c0102071701061d09070f03080409050414010c02010e0c04061d10150c02010e010c0f030807030e07120209060402070c03080f0d231014090606 75
    0x70300300500d50304c9220b15555140107181080c0a2060059600c4071203015036201803521140d41c1e80203c4c103402500e104200f000e610320006c605030781c007400c000d521010f90400d00c0901919581c021344103540c80780b14a40121604a5500d1703000001421581c440508180001c0c071040c0920061600299045801640c9502c4601a1080480c1c219000314010a002d42e65805541045490501030f0524889003180e0400459140800803000a40301d100f218840c07030b00b40d1001408418820003d00c0207080c0060001d04c0e0500c0c00326000d082181e4441c070a9011a0804413010320547c400c403a540c2c450341c0c3c40180c441096010f550f040d141e080303018200c0000d2648070b80d03031011400010011203000300f00c030f011415070104007801406000c9078007500c16402540100315590218265602c20700881360700c814010b03600d8500444500003405100c41050001c3c0c1012001e07800d24414801a000080209082c0d00d4261103103245030070320840500c1010741013403000361050224a081c0340d180343d010303201500c1030745002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 876657455 1250 876656205 876656233
    0x10060c080d14070206100806060109050418050304171504080a031505031212060d11060d06050904060207051c1d1f080115030605011704020d0203061005100801030f110102 75
    0x4030b0300f19031075001640700d8020021003090340070020380200324170b070050b2660303041c003000091000915001d414000c2d511101c8030300c0f010048181c00c0035041c0c1c0207016207488540780e418001d41d03405424101c02d001d10502c4441c03484031460109590085074020013151812031525030a030050020707001c0081011b0307002e41d400242518107000d150065500403c54a5442c0399050340c0d90503980000c0c1406000b040c1c400700100001d10720510340500080c007200c0c00c80d1110840c0c104000603199581101350800c0042c3c041c8810025250054104148202d040d9048450042c03000e90a1a82c02c481301000114401600d04c1c030709600349001070304a0b0700909401041844035128850205074140e5400c00102c501d401007005110700d4943ca00711b003103e0f15051002c1031611000801190b20300048a440714152000b0030215541d85a101e451107602034103961061400011074031080c001c03445164054441100d04104152040e0500c50680b40e1156070290004440d1f1540408c100701c0807059815071003032005c1c0100113 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 876658705 1250 876657455 876657491
    0x20904060801020a170609010e1b0c1f053715030209100810050c04270c11062406070c05011e050a141303050a02040510060c080d 57
    0x103005101c0000d41da440381c060703000305130311000c4100c0381840303050380c041c009599150280c840c110340c0e01164421042d10b0712070801d1110b000c441c0e00300d140e1f180d002400300e540c0100401c20180700e155a00102d0f00b0310000c11216020394000311047d420383c0590324155103110790301c1200f000a0b240101310003025000c131900d901c1c0c1242c09400c21210008021301c03007001103141c50452075a004c040341d0007030900607151184c1159601f0510100c0340b8099102d50019828a10483c10f48000f444030680c0305d44003145030b84015681100880804200c942080034512056015a0b1144252443c0c070000700119920300c9401c050b031000c051640c140d00390308004000304a0f80c451020701a00ca0251000c04090f519120015040c8552901034510100b420050020480c1d040790540e1050350041c00c0520608400c105035640e180315a44586c0c041001441010080c001b000410a071850310031f480c200811740711502c924624002c0d62040c50300007499003000c1c40010701c0c1c100161410190280c030120304a00405075015032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 876659955 1250 876658705 876658709
    0xb0a030203060306061503070c0620210105010e0111070906030b0901200405090411040617011d03251a0f07032a02031308010917030105010509010c0602090406 70
    0x280e004024020b9910b0140803091704030340201c03442d944001a90140c009540002800b401c2480407030404c0d5014030001da0060202802110f009080e0245030307201029183c6c000d0034804421081c8420044401c07501c0310305e194140d4405858080d140050000111f40d0400780d41e5543c1c44038010074100013901540c40c041e24026501c102c01d805050318048801e44e0840350204440c504101411b8154421030140320125401e449007659041407996650800201103001d48490795001440d2500015a0341014512030070025500c4e0000e00506036450b220980847d40c1c41d40f03440d519007040100750640110180084464940c042c00d82003108100d4032070002c4081050100200c0c12000e400300035010b01149446944044182010001c80e01a0488025841c2400c001281d00c100007d031740c400b495000b0000d8031410111500140b0780f00d40ca40d0304050107000d040204031629502c51030304118155130007050b00d040e58810f0390781c1030400724518011603a81082290503229160f00f004189050f49550041c800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 876661205 1250 876659955 876659957
    0x901200a11120403030f08060a0b0a02150406150b0921160306020a0311131a0705100b010e090408090103090c0e130201090801090b010311190e040c06170a0903090b0a 73
    0x140f914610f04001e40b400d10046108000c120704402040404d40d10b9010300c509950024121688800a520f0160301d40322840800f0406030b1001d03400c000030403a4a400000201c07055484c21505141e0f1b5240301d00c2179015000c041c40c0e00013000b2003d49001c0014035100d0b003070030b2100c0c0125002d0f070304814038000780b00d642608266016500080c64800040d094000c030f441418000b103c4924280c01500c010151401d90b0180c0713403881e948000a191411102020359610310f4001d01034800908084e43c00b01e00601140d000140817030503860100c100c5182c105181841541c0000180b8030b80001c000044006096911049480c01d242107000700310400b0b002d54441c46100940c0703c15514021030b00024003180f40d5584544505d078100011400029104500181100ea2044400e0103500300300c0001810303001c14100114481c2600103000411505081c41c1038082c44c02141600d001c0c03511013408807118141e000c550301406040e05d0128445041c03d90165030366500070701d0080342940d100e00508006506c031108a80c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 876662455 1250 876661205 876661207
    0xc0f04060e040818011d0112151206050108161e03120518120705131103101d100b071a01080a2109030215040902030a140901200a1112 59
    0x200b02d0f201004a82c44401500f424146c41c16003045082502030040c0c404418100403200c140228401005c4e00f100e0340025000612803940f5849683c400c0804108100517600581002c00000f4036910200300f5030b4030f05031003a405500903030408030402d5621000750a84ec0d01080c4c503841c000040388e900090404081560350360540c0c0c070038400c000500c590740341d4070095111350402141030322802c40024004e01203400030303141e55114500c10449440180509a03c0b0340002e58000204840c03000b00011007001e4400300428480e20304a00004111500001c9400c00318107081058107106080050300070f0006584201d2031110162062040409040b00c01e92203004542c0c060b01d14035080144e062000084004654002c46060010880080a980303491002034018103400010380105160001240d0151160b82e00c199035900302031215500800d040301410b0540030b030010101d441d04506000b0060840c1880e5000c2c03040708070301c083c1c01410391701514040341072180f41d2803100035802051200f10f40032844543d1035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 876663705 1250 876662455 876662467
    0xd080417071e084606020a0306150311070f11030a050c151e090d0c0329070206060f040603051518030c1c030f02131a0a020c0f04060e0408 61
    0xd190480d00150083e50110703d9818104101d405100c01d02c3c5078071019590901c4140200c1000c4c1141ca2070080038140c3d50000a42c5000b458243e00300100701c4004820000e0044141c0e00c0403800c0b81e2a15140f0023404404004000c0400c552415001e10107000b54084103070060300100280c5020707940281210160040c1088036107925010351245001080945c403c0c0c90310f02844003101020310380c401c848040c002c000ca80d40304943c81c0c4403148000940d205a101d407501d074482c208640b854280c200050707951400c01c0b000080148103110b43c2800b603a01d5070000d11981d04c1e07442c02c000981441c0000a50801e9403242c0010104038100003a10308020600301c4008a414210040c0c03800790111202c0b9042d503803007040841800c8400040311800044400103d955002000038118090440541c85112003400811040407159000c00c023541100c0f044a050005001c0c40d800814150127000d8900025802000c1c8400250034807141c601c00341ca20091000409540380d5044200740c4406590640c1c3c4c48001181c1c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 876664955 1250 876663705 876663719
    0x120f05070801020f09090403020c09071d0a060e0f06090418020316060c030c02060d0218030c0114070204052508070813110103090c0e1608060d080417071e 68
    0xc02000d400910000e5182c258601403c003e544242c1c11001d010322400c0e000070381031610a220103d00d10310300921080003810711050060144034a0141ca4007400f0118824090038070b07007010010220355054946900c03440743d40c0108041c21883c0884c4a401010820801080c0d54640c4507500c01c0c00110191881001d0b914010301d0700e0840d1400c0c1c550402c0c44d868000f4803905d50895080c2100a41c14a420321058041d0710108043e4094035070071420150010810103a404d050f1400003022400580440c2d8621402800454241801c1c0700e4200080200300400000341c24250000b0380d020742038068031801c840e800058000002144a0920000b030b02440c10f000e8040d900102064100a447d0741c3c98ac80c3d000c403511488100020045407a050540d00c030070344020170800d150103500811384001500c02c40c0c5880c201c2e810b80311881ea00103000244821000860ac1d140099000f200680c201100341c0c1082d0805031800c080003815015003041c0d205800c00010f0301d91542c2ca0799081c01c425905440c50312880d00782 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 876666205 1250 876664955 876664963
    0x203131403070303180809060703020a0812010e070315050d0203010b0a0e241e0d0b16020123010603020a020f0303010306090b060603070c080313140a03090803160605060604120f05 79
    0x20030b41c07030b182d41c43c820340e800458010011f84490220849003aa612413aa00d820ba02d0403005060060100c0030106002c3d1040304a140464122098022641055901c50314110b040b24038111b500903c900e0345c10300c28021400c2c51340c14070b140503101500014000e00600c002600361900365100101c000100d40c1007041c0c41c42e03075100000491400034941c1955503480ba000504064103100c080c1b140780305003032514245503190904040240e030007144640403410641030008071010040500ba000d582410782d40c1e40301c17006600d85040401207821310340401da42000c5089000e03620001402e400c51081140c4040d00d504240003c60085100d00000541c90500d40380c24924608000c18061040205204110740360b50025004454590300c0700c01c150b5607079203541c401020302e60a0b131000b4000303003117031074110030441c60004c0c1111605000b5129441003d0b40c4c1c500c51070360b9214003800001d0b45044c440c000e5001800c42e0b00f0594100b60000d01090415803100460105559000001da40400d0314203e81000e000c4188 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 876667455 1250 876666205 876666221
    0xc0d05070f2306161e110a050120010e0601060801080c01080108030313060f020c010f0e12040312021504030f090503011a06070204110705060109150609090203131403070303 76
    0x4030003080d640c010610020082c0e91040700c06800350100066298000700141007110740c1a03400000b0242501034099807906400048600712007900d40021880654608041200211003059441e0310298404c107900160751280303482c42d080f4542d200d40302c4800d00c074801e12015001e00025540e484c240d62500146d14500306294501605002258005100128010084a40c072025a0802442c0d009151501c0c200070600c82d440481a203101244d520304880c0c041d0000343d802440305105028528052103881d807944031008003007007590400c0200f000052400502d0082c040418016558131000300500301681d08001c82d02240080d900e221907256280d0800f44a0000c1c21080d4002c01030740c24020100e01c1000243c2031114803841d004110b190031541c90360048a0942d006a0481d9110b2406240140d0342e2403080c0205400b0300e00380000a0452841501d6507006c49859541d40c4c01c05c03e280090f0714000f580050500c1003d0400d004920001c10121b8001c000c280c9082e000440c0e40d11a103041c000d044419407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 876668705 1250 876667455 876667469
    0x17010501030504120c0212010c0905010e0f031f06080106060c050d08091b0312210903180909010e0a031101110f0f030c04180212130515090c0d05070f 66
    0x7042c240004684a440020408503050800184101c12070000035034240661079101c1c065801d2480c0d1010f0140c6c0601200102ca60a88507599810f0456041022000410039000d8150780041000000c170200d00c0140c02d004104c8000c001011515450030300d080d0341e00ea4009201180c0c4401d101c41c00c0100c10000c0c4102442c492030929401d083c00300803552a413900d40480b003d803c02244c06e80300282d60500012b1202c4001d008216910883c08007603005181e52041049200f5500400144000001000300c440c0c1d80c483c041d100402600e010200321040380007070318454043d96a640320070361071002049000d00b201e010352600340407000492006825030307802078850103075618148102d50074407003070b041919801824160115241e40e0790525604181c06968845004408518142c100c1560142c1c010000d0f1270030702107103200c607686180804000030760000b8000d2a0ba80000c48203007803074641a020307a41051a44066912890a010014803141a829019101c0340c0002108100409044106000074040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 876669955 1250 876668705 876668711
    0x2031b0604050607050f0409061701060e0717040f0227010f1a0a1e0c051506090604050414010c050912061015200102090301050a20071e031701050103 66
    0x841da0b1041d440d590041d08007801e02c0000b143e070f000c0112450050b24050100200308104180d65482005000180c220300e44006510700300703000c0740010960282c58401d40840e118150a0090103403020200300780204181c562189a203180c85c010303602c0d052040302144005401d1891601c0f030405070840c07950182d100310380303100d100e00d000c00034401c50840369510b00040710005038a600b0b0b1b1910658062015000e022400c00440f5111600a50044800115603010790b0441c3d455034071040c90340d44004820b460581e03104d0704072400220035242c242c1181c2d5010344a1046011912000c004030740c20b45030340c041c0c0040811808241c4a88906115403515640705a103c000d040e241040050100e0103140c90184101104141018202450294803000c8038100d009102585620354045003034000d400a16015200354201000300c1c1d41140c407030107540c04900e0310f0300507001c2c016000d06451641d0b602c030358070407074101215030600c080203548103002d00030346030003900d07144106100016901e029020580005040c545 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 876671205 1250 876669955 876669961
    0x5180705010c03180e0708160201110304060b0a03050d030e062d15030a152a0e03070b0c010b011209050703030e011e0509040f02070f11010903080a02031b06 69
    0x781c800c9060001d030b601424240c00101203400000300e0301c26160400b0320710203040d03024040d009a020400f58454550944541101e0101c990106d007270b02d03cbc0003014030700f9040a01c0810007081e03495200ca068200000d10200849603680d81d05420010800468070100f40d407220034040c414000d01089512035901c482c00412840540c40180c0700e160b440041040d240820b10001d51a100c02c0c00710341e807170700c040282110300c1201103103001c2003845688003036179204906144d9200034004510300c10741841040200342c12040840c600084070342c016080880d0354184600c0310001030241105000f06040d83c00c600010402d4500000090280100c1c0c60742c42c02e00c41c0c908622400412400b0480314213613035040c078005441d8100304004a80c0d0b130060780c1c503100c005104940d558542c1a04800108150310b02994244500820042074408034042c114002d4105112900e03c0b1001826002015071031b4030b414100302d500b030303520707504d5149640d00612000000369100149485402080c00c038032150070381c1142c000f0300d480c0c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 876672455 1250 876671205 876671207
    0x4060e0307180213030b01150e031b0907051324020607210e03030901090203010b03030705100e0307050f0303060a0f0302180a180308011805010605041a070c090518070501 75
    0x4103040100044582e40420011300c0078040300084070065400851450031b0356151540d410240741d168040d1008194107030000c5400e42400305640329000c4401c00380c02c1d0300e140d0810500c400c90400078480403c20808110440e07100390a00c1c00303040a0f0084400752000c3c41242500d070502e030710800d500c140130340d4003610400840982c0130403000503035a40c9030300c075a030814080c1902c140a0071403124054258040441040f246050560002103034a0084009014455101c020305469218031040074005800005a004240c05288c011000c1203100030200da1601e009602e0389030801010429070042d40e003001050240300e280984068015007019021801140d155500140c41141081820b101540700000003444c240322680c400d050315074a507440e16800d08554a0010100030007409000c6051010306203c2503445410310601d8180d65840c0c603001d2405081507407850034207080c000451003550b01002a04006032042d52188014000d44101080c00e0a2402a03800802c511092600e03d070741c400c00d010410342e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 876673705 1250 876672455 876672479
    0x702120313140109030f1b090b0f040e0c0d080307030b090c250b09212508040f0b0408010e1216060f09030206061c0b0615070c06020304060e0307 64
    0xc1d03142c052011905015000142c0d11600d20758000b070020600061200c0500c40405c1d1080c88640a108015102d15111828841103c0c8900c03407460b0840b00c224a1a400b50030702e0340c0403602c2400c0000072101c0c030f00c030038100182c400600c4071012912440c001c000c0c00401078050281070b4101e4400c0b11100400e191408402e034090050048002e41d01c41c1207201461807130748600744140c4182d0454000b00e1a8680200401d658a08910341c1c000300c10400e05589089074541d00c142c0b03139409541b800104119500c2c0c0001d65660001c4001501c10040400000031020901000c0000403c011707410580c0361884c0101050031036441d0240785604c0c0d08942c1c0d40c000c200411004481516103181d4021a41c0e505a003080b6005003c9071440d8550240b402d01a08185500007640501c07480c81150f41d0300700c00140d51105150304414100041040104d140414036a251038141241400c00740c0e0143c500304052926a00c2410005a1000000d80c000080130321180b03602010703105500c00d0540040000e00d14200c020441 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 876674955 1250 876673705 876673709
    0x60203031308090904030221091309021810050109170709150306022206091d0a0906231810020a03020c030409051e01060806130615050702120313 64
    0xa8002048001c0070060494180c031007228000e882d6801c1880e15280c007a42d41d4a46071481e05500b42440c82000d00d01c103036541140c05410303002c0c0051642c15a406e901e540506a6540f04070b9104035141c2e07540d0a03246601c80050301c1804191110610301e49000005440d1440c00e80181c141c01583c2c0c09840504580003421004680101000144490005500211140b62600010051030001550210b03100040007110f1900c034106044d0407252b81da031354090310b088002e442100440907454040190091002e0111a4492025900450003421a5a8020440e2001c8684902d4103015544581c0070500c43c10040380c1c04420b24002d1460603c500c000d181e40c42a01030003d4451640015011840c0d61190701910417103240350040fa81c48075103492030800034000441356100c001c1070b404003001400c01e40103a114120703010303902c51081c0c0740c4401050102d42c2c01901c04001d09e02e5181c81c0700044c0c60540c1d81041050303c4669a6142d1540481d104026034803510040640c410b0307006120241119410510b0042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 876676205 1250 876674955 876674971
    0x60e07090803090f0319051c09061e03111c1409100e030903030f2701050d0b0114030910140f010501051c0f1d0604110105090d020607050a02180106020303 68
    0x1340441146001074502011000e040c1e2070b50125075840c0301007040005451105544020043c076107410241011200340d5031034401c3d600021852030100035010210b40305030098140740c0c507000c58080e42c41081c08619901201030742100c404851460150306c07800344207550250303c07400d10450701c0d41042e4409035a6075103a5409505103c0d528054000030000401c00c81d0280140581680d8903010081590503c603000800d040c210b49114076078150f200c54422201343d200040585030301d410640c02220401c0209140340105043c0403600a00031030311203103a80903510440c0d4135070081c5500815145100d0644004120f8503241c49010018000800841d01c203440c1900d1007868001d0320340745542c03001c1600b058005001e1012514000801e010020990000f030b60100d030540e686110f00308040150f036500c0c0c0c802c4070042c241174000c0a030302902e90312420050400680c010207401105560381c002400710380c050b001c22034840d1301c541f05690840c240408071110003c0005080d000035854040b0103034032840001c01c00a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 876677455 1250 876676205 876676219
    0x101e080f011a0f041b052d030a0f020d0609051b0705070504111b07151d19090501090203220b04020d02061b060103050601171b030c0d06060e0709080309 67
    0x2003610346a00441c0c40030b03d081e454001c409400000078106a100110b901f85441c4210f11180710f141c03620003080c8964511040c201c1c83e55594103c3d5000500c140b52107101159020002340e60f45c80b81c0380c0134030805445c0c01c103400503003800e2040c44c00d214100413021241d00c202050100501142c804140c040c1214400da80106201c4c42d40e410b00c5001d403050700100d007201030300d07c050260107600014000d016a07110644080140c0640041a14455118941c12a611442410001090900c003604890344803100003111080354076900c8560654000343c000464459010040003106407204003101c148440318004054005401d480c0c50b0480c1400510117809040001d030b1141c110b440340004c50300c51502c402c102000001e44c07111080d498200038031080c0c80038440c010003c1515144410302c641c5140021000700b1900c081fa20a4441c0c43c010380b03650300d6042c001d075081d81c2015121009039001041c4600700c0010640d007000e240e140e500901409400c03c02a4080040c407503064000111051820100d41074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 876678705 1250 876677455 876677479
    0x80f0a03060314030a03060509090a030c0c050d0311010c0f0212090a260d03020c07170307060c0203031015080601030b0a0503070b07061a03060f101e080f011a 70
    0x54000d0581c69000800d69095050346074400e84010002d00040101039509000650340c0b1002c06c5038070f010a407400091900048403100020f8044d50026038210702c241d1401144950390f0b80050354a141d01481075001c030f000003012088503c003e103d41d11104106091280740da030180d0303e00030340d210b980e41005000700000150030300e01a81d84c00c40c0c400c010000a00d860010b46002603890000b1001500b03407201500c0b4a03407010398005c0c064002e0350620300840e802401140d242680b086048501d074512003000c0e010400c141d4000c18501e000e0815143c80c990025683c6e410140000e890855190b4000e40c2000f00c0a86146d00301e1b5408240725821150910b0f001c1080c1e600c070300000d10180d140f079012560501c43e140000904041c000d01070138101d400b41c0710070481c0c01040034000001c950810708169054008000048101da41d01c000207030000d0040071044505516840f5820a14510010161400500444c100004e0100300700c1c40d0f40c2645550b00038002100d04203d01d80620200c07a001c40c1c0308002050031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 876679955 1250 876678705 876678707
    0x917030304050a1b05131e0b09060607020103111b0f0d1b0318090c030e210309071a070606170c040c0212030a0f0b030303130b0a091b140d080f0a 64
    0x4c50029010080403082d00e51005456140246245076020707840c0c10403513541e041403002906c1009140360000d08940220b55410080200507403150004030705041c3d4904e0115500b000030001b0f03100c0080302081c80b02011030021100792900b040300030f041c150750f40b00f10010208150701c03244004c40b90405603180c00400302c1d80d2800f40c44010380b0b01100310046e10b445c400002d1075201038104825117010341c0c404124519040321016241c1e0701d01613103c0e104030144072411032155000001103510020103800d581403152070f04043d03448004c415510b500034090104011b82403100038441e013801400c4510842510080c94001c19840d107100104c40c0e8415903413899101d01c440c2c000d01440d000e8208540f4031079502e2900150034001040c100702411940362805942c0040c500300001100d000e4400c45d05100c4601c817155440340c0180d28010030302400d2a40701c44468000038582e00c03045507650302441c0616905030615003000100d41e18184103e100d07001e08000c8038080380f100340c21505039242c8003004954641020070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 876681205 1250 876679955 876680003
    0x10305150301050a06061103040830210a060530010c0c0611040501052b020a020d1d06071716081207020601030c0918080a0917030304050a 61
    0x14058041d400c007001c201104c10103504c071606a450301d450b03400211600031502903890081c0c0c0500d408960000c07003c07210b400222101c1000180c134180c403030002200c645a009120360450f50340580044440002c00800807000046d42e81d1100035450100035541c54a00002c94101c2810418015000007241410603220714021540c401d01101000707101130008403000520010f075000095501a140100c03101950710708408886c100d0310165101c0d0700b00080413010510620303a010f800c1a010031000c00550b0a804180080e058108098000c0d00c60402e203604080c20040311904ca00415914280c02c441c0396a4401040c1d503040d03a08800d070320000480920340f5152074880d00440416041320940007004100c003c1009181064910001000544901348142d03901d0320300703000c002c004900440c03050294101d5644604614940b160f0001010281c2d9201c14240d980001070400c0010002003040c0308071450010b034811400d9032038005500d1881c7c20780301c86454481c0d07503a0050040d51070380c11005c640200c140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 876682455 1250 876681205 876681241
    0x170109050102221a031f03050115060e100207090207260415030203070801060e06130e0108011107151d0f150901051302010e0102070e040b0108150c040302010305 71
    0x300c002c654641d40340c0c0183d600c80c1544035041c01030804850001c10005030800c5202141c03102c50a00d142191034680d14001801c2070309170380c40b44808000d10700002003a001d0045c401c0307503454100720140355401e003c8000c1c0106003102200c3c1c042d083cbe0f20310318041d490b4000303190700440311141c0c030042c0c03659481e282c44410840c13040c0d8004280e01c00550081d0042c0d000000070f10071070303101c481c1c500e030300c903055250590603804110340010100c1c04210040201300e0080600e02c1034910300402d528505905922750f03030780e0320705540c00190858040d000113100c4603a0901c5048a052942c400351030400321b190b0354052850044040e41005192545c80010070340d5203419046828008070010b54001502c64014607944a0020002a1880404070042402d480040c49000c0c00b4a80a00008103001210780041d0349212032a01c0d0f580c1107100d100f2000401039070710f40c1070070300483c410b4201041c9545810061407403d001c914070365551014600030701a04015000480302201d80c2800c02107601d0755242588503d1120b40c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 876683705 1250 876682455 876682463
    0x6010f0318080a0c050f010c0305090a050c0f0a0b0a0207030210050f0315030c090406020c010f0e0a140705060d060513050621070504020313030305091906020c07050a030302070303030c0e0a170109 86
    0x100ca0003106003031b0190010110001940e80400482e5280c4204941d07903c45900c02030b1058008400c907040904040100034400b150140c00c2605040e0f440c0d807011b10f194000c146032030040e00007a070b0038000c618224840c400101110f01e4400d0030724000c82e004240500c005001562003603c9641c900c4080c1d1028001c2416082008140e8000381c501418045c001c3c1d41b008100d003003c2d5107080d42220128900388030300c1004503881707402000b00c586140e0382c1002c0206400f41d80d1500384616000051556564401020034950480000c0350503481c00f001e02c1110f00060080f880c42500f45410805070b0f407611814950040300c09210450300700504240542480c81030341020f900580008100480c10b110100c4006030076109550070403851f0344041d042c540782c1382d04c041500400300801c40e181c00400e0054020b0b01c41d454070390058415144d510030019000000640c01240942c0188108000f450b41611416403010070318100700e048a001c080000381800c81d54014000b84031548550b01c00d0700c507c01d41c4030007101940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 876684955 1250 876683705 876683713
    0x80714120312040b0619060f03090209071205010905010621060807230f1c020f0603040c06170709060c030c0209040c0f0603020910140705060f06010f0318080a0c05 72
    0x10380e000450b551042190141c03028a5400042501414810085a280500c4c000c180b2141070a0542c203c50384808a03080808151301c0310b12560140ea80e4403070160280000c1c0e00c8420b241c0d114440150140c840c140e00c11481c0304d10702401000b140b5001801300b0048101c049180501202e0407000e0401041c03550003010991141d088007107181c640d014034088061601d51f8204d510351a1f80c404010300c0c40f4400390060780041008607442200e208641a40c00388034801042403103e07209a401065081d00121019514204055810030090350410300000803041d880c10f092038146400040601210034920405041040e40740c1740109043c0311303034080c4038042d03801081d18a0310f0030142800700007030015006407140c85803d0744000491600900c01c0314038005001d40508800d40e5214000d44000c0e0395200c80000004040110f035001903401d003d6648107050103200e407040c42c20002c0005149054074241802818980b4002200c0b043c4009e450035081c0e0f50080300303940c1e41c14504400310b13241c0d946910000c01d1449 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 876686205 1250 876684955 876684967
    0x1e0b0f0f0a1e08031c0e0307050703060209150d021305030a031707050405040c030b0405090109030813030905220506060405031b060d021611060f07080f1201081c0305010807141203 79
    0x1418110040c0d40d07203142c5e01400f00503075001050741c99200b80003004045600c1903004000247c2c990300902080310f0f0042400d100e0303a4102d003103202d00394400302180b0619940005d4210390581d40c0499070000c1c000543c0100300b100305550f00508811446908241c0b1040300c00d000a003658400c0c41250058a0080c00c18888161400b10180150902040300ca101e07a00380400030385000ba0510503405c5968265585980e80d0b11003408440ca0705801c09401c0d400c0104070035000c0380d540c58161000302c6011034220306a0a00d03035100108000c40f035001c2c0000d44101000c020800c4256000942c1500d20102c2060b20012100320100040d46032140c8000341010300d00121301095071205001502140b0390244909211402d03010b420070a042c0318203131118603000c1040c04443d000c50007a4015115200d000003126140860900800d400381500344d00c1001c2651003031426950040300002d2003000502a801c0a0085505105034203860703051034020304400c0030481c00d507c181e030740c1e4116a030100069020141c90b6102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 876687455 1250 876686205 876686227
    0x30c080705061c1d031b0105070e060711030303011d010504060b0706050a060302030f070810050408071b1a0a030c0f020304060f0203090d030e010212090a0501050d1e0b0f0f0a1e0803 80
    0xa0407486240c0d261030301d0010606074014040c010244146980e641e460ac43d0741e091010800d49810908003a02c0494001c4000d075015101040250302800500c8004410580c00d174283d5841b01505800c03a030300807811301104015100c5064291041642d1000d00441c1315a244012503000b0500c0780c0c0b000e03516110b5100c90380103140000c9209001d80d5801c105a07104140d0300303507030389003610029600104462070400ca14004219501e00c000e00504800f00b0b005003d95450b410105240e40c203490f00c01a01800181050210790184518848640b644c203103001400201c0d24043e46074099031040c00140308480c10111040c1d8400d000301c848152005000241084081c20001e040c1b8106070b18490240c4210100800244400002c1e94010317000144000c44260401004451640202004c80e00b007685412026040c1c0c80b0300c1e0340303981300040310078000154100300c14200081c0944c04000c060044d99003c2146e140303a1181d681d038005842420a240c1c031120500d4440500009080d0b010005500022035160b0700d40b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 876688705 1250 876687455 876687457
    0x30606060c100c1d040b1807210b0a150909050a1d070e010b0403080711120f0c27010e1510031e0203011401030504031e09030c080705061c1d03 63
    0x1d2142c1d1148134180c282c01d0b030500c0110346080c80c0d1107a0003004651741220001030b00101692004843c605910010907031400c140040c3c24040703885642c1a2076045401c01030406c6500c0d03800130408450300b4800d1032001c80c0b000d000d0403030300d0040005954450001510b035548503001a400c8010400540003020b03000c01105480303501e03500039a03840d401d42100001d520300d2800c066400303503a00041d0721403601c265542c645004609800c00d4a420034015401307d0550700c414000084440440400b604400c0010006c010607402d05640c0204180d9460213106200b05118100c6415a224040e07000c05944405412030b007441e03107c803071007a40455003544110100e03a0680040305008061032030020440800c603039640036070000340501c07800c0311018400300345558420340107140c00c1343c001c2c01c0510641c02080f4502c1104c05c0d4101011000c218414401c0007000542540c580040c08203402400c400f505040024202e449506403220540707240303c040e01d2507800140e202d51881900c0d02013603984070550f820313107a8503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 876689955 1250 876688705 876688727
    0x3191406131203020a02011e0222061202160204022b11180f1002010e370c0e010303080402190f05060c0a06020301080618010b030606060c100c 63
    0x2050040c080810301e400c081500346000264808806024082c44001c02c5009410826100045640b204560f070000c1091801c00e0341c0781101c420f005a81d8015010240b00d072180c5c003030030065141c80041410419203a100015803410840408056270380c01026103030702c081f0b444a00d0043d601920010300206010088003000c511b84010ba41d650701c09901d003900036021604200808903000b54100500d00741c0314001d2950004112004112501a103000030105103c100d0420703040c1e025039901d820500646408106100d41464458440c0b144060f0a104101079060309900c0142101c0b00c0322005010003079603400c0d100180684280440b03071580d4900303000b0306412094805030f004800908260001803001420305054030340d40c500a91610f0b142400307000340c0d6440f00c0c0350301d509402a800b880d400100c039030000394020302d801001000c281c100700254034440780321040c0b010382da40c1c9403049035251520041107140e0302110840d1402c0d00c9004036401135040403654561306070514a000a230700c01540e00500b00e284 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 876691205 1250 876689955 876689993
    0x1e100606090e0f0712052e0611060105060a230f07060b010c020d022205040b090d09180906141f1706011716030308060310021213020319 60
    0x140c0b525400102e42e00b03044103031161300014042d86040c1d1903041098000b50340051004d4603460072501c054101800f0342580100b0b0f9840140c00b0300c420443c46030b105000f41c5503d800720000d480d041d49844000307001403080c035851030144089030802015030700031540c181c0044884820760716503072081d07060b080d05240d200810032120f5601c2d01d000004554440d040340221076502420b29900482e0507003c02c103040c07141c00c0e01d4441c4041105120f0341040001c0c05402e004910400440080b410f0400d607a170300345036440c0c443c0c004000084c5400c00c01484403080f0707241200d07012040025504000c0c104040640000e000c032000c1d0818a0091007c02480440190a4040340c5da10031050346032600e4501691070620026000541d01c040014499a01000e0500010f00c1c1140c040340c08403040021018486011782d4415404181e040080000c80c1c2024403030f035850504840003c5103040400b0702c60300c515a0b005890300300822002e00d03110b811502c081050310b03d0003a029040d466081c41a00d0200a18090304528034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 876692455 1250 876691205 876691229
    0x4060203030106080703020405030c3001060f06110316212304050f090c0c0d1106150915220f0b0901060e0904170f0304060e0f1e10060609 61
    0xc2c485c0703440b907c203075015a0001009840074000b500100311401025092040c40c41021000c44403014010180114111003000000315a583c5000030318501c0b80390300d504c04414410340d5070a50000440c04001c81e000703007224580b20304900f6100d0400d055040c0810f1800e4101c00c0c003403411780060f1508007031401c0085031070b0300824509003500c818845c9540a588a4980c00003101146040149044258540d10030710003440c0c0ca0a09001140441c40c1c524841c07030480c0800c1003404020710350141400031030360000131000380f102a1040c0f1404201083e4000384403561120741040c51b001c031551254645040c1030600b0803e062030204c203031401002800085485200c0f40c0c42c1c04544480b03800e000d0301181c100c610039141c002034603e07904d00703001c01c0c8440108215401658046102422902c45000c1c084002c000078180d0f440c3e15081c68180d040320106001440300354852011700b1803030350f03001440300c550803202e00600c4c1202486c1f20322a89000c0e00c05455590542c100000440d1140d4468048000c5034000041302c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 876693705 1250 876692455 876692461
    0xa0e0f030a030801090b060c07060809070b03090a0f0212010603060c020c0d0b0c0a05070507060314280e0703050a080904150e070e0619110115230d080406020303010608 74
    0x95500c0c0050034004003c50715560040040388199800000700340409001540751880e861103042c01c01c12142c200f600070856280a02a54003401c0204802400c00140940d166041c60308015a580388041c03c01400308000c5440d500864032186003801900c40100028800952240340000103400120641c0c4014840e65602021615025840c0e2803031982015a24203191074516902e02e0951110502c0b900f480070402003000041c42c04c010000c008c4c0042d80c0d00041401c0c400300c040001c10f4024192505503104904c0d0100e550030a011036160300107400301d001512000080c00e9a0070b00304554405081030045402d00e4090100341c030018840c40008903020045400f500400341501d05039400342c9020503915900007000d02d03000c0d0300041c1c940103008040a00f03207100c0688000c91030b050458041c00240349260290751101c0c0034041d5140d121400c003100c103141030802e128013102501e034008c4490205210400d810b4261114910b0700d15550704011607545d134a80f04d41c0043e540350710070300c25200011891400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 876694955 1250 876693705 876693709
    0x30f030902010915090f060206101203080a15051e190f120609081c0b0901050d0b0c160b0906010608013501020c011d06130b04060e030a0e0f 62
    0x150031846505071034002c901d03801c090203400400d01e402c05400034481603001c040340b0380d2051199880100a04c2e80203102600d81100588020304d2958001040420340c5440180000e4219144035808617030408001000c4131200c0c00700c0d289680b1580450341101e111514100c000d5803402e0040603a40301030350072100140c11164150700c030f070119218400c5402c4964805020100a072900845418007500c80480d03a050b194130341c5421640125a204c035200d000040c400b2060f8070501420104400844e9290440d40c502408180b48143d000c1c402090a0b82c0c0c1c8001483c0c0003540b07003d8500e0000c8594064458010700e251005041c81d0568105103280300e440000244140305510130b5050302d141b60711032518240b1416607100042c2d446250b8101c5000c14000403d5080740c244080e03e506001c100001c00d0840384800409220503920300310300e0312078020008104a01c1540001c2203155503000c010392600360307a203007040d40081000910746855030100041c80114240d0060500c1030306842103984800038071651742 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 876696205 1250 876694955 876694961
    0x120d0e0904050a2018040b13050601060521070201060e100b0403060e030928062f0a08040b04150302070b240a090e1203100b0d09080c0703030f03 64
    0x70014203940c0030041e50300004034042904249180310440200921240e07000007441c0c4c84070300355400c4000101d2001c000c01e2061050200d9008209100742c0017012206485e02501c0309014000c250901c040006c2160b40500f0030241e6100c0c0070700b03198041040d401c0485c0700038040c00c1c10f48500350350040400d02107280031422160000484485500c0a491f003895666000050920350b258150700b408140065001c81c2c50f090402c0f4511845031009403690ba070114481d50b03443e02213400603801c0042219400d440052454461001144600304022212040305482840c288400400400c421004240000c034005900003510650310b88503d5004050f072a9181101240152403014001d5419140480c00c048101d002807501543d11a0554000c40403d6001c11181c00701a80100041d55035412038840000e0140030718100d92021043d0180346051010b030440b0300700e5150181c1034520340000344103189100640d01c984c9940f64040c8849890348600b05000c0d032034115500c8150040b5121140d00b40d0401d1080c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 876697455 1250 876696205 876696211
    0x405030c1813170a02060105031902011d040e0d0e1c020d0303051b04030b06041a090c0c010b0a120c05030c01140306030a02280614030403110a02120d0e09 68
    0x2080802107540c1c0c0c2c0c020984101080081603ca070b561104041c1c0070080e8400c002c1455541d150010000e6500d1b09080c146020a07a4034800ea444441540020045c1c1e407241002000801d00d40340c12030b203140d24000003001060f504034a88020701c118030b804400c03030341c214000c42e00c010380403500d103114004501d8080b501c10495200080d403002c2111050000240664441c030782010700100707600d8041e81d003548000c081c0e03801a00240d9035165694200507241c5024045c445980481c52502c059515000c8041500c0690251020104500c08101c2400e000710941c0712010382c40707000b40403900c07082c1d545910006880c4545d86c1620803a00a15000c02d150400003115036400c0c1040c0d40f62645480120040c0000382c00250000d45d25000c1c8000901c007582e43d50340e001d00c2260742448041c3d40c01024480401d603082c0558030003420301050740450040c44400d07405a81c3d10036003606021902044500009041680904000307502038148040313900d8134840015602041c0e00140c8801c900602590100700c2150070031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 876698705 1250 876697455 876697489
    0x4150e0f10020f0d17060919020d0f1a10110f120409050f010810020a360801200705160e070f02031303020409020310022b022107090f0306020405030c 66
    0x1a1020604038104204e13003548c000007103804148081c00c61040c50040c0e80c802c240f44070b065038403400310b44540c29040c4207403081b00f00b1000c0d00320540e030b262402081d201c654034603544003840034010903004614030a00220a901582400780d40c00c070595524181a960040e00590080c1850540001e080c1d04100080906076030300000280344081c02c40710610003035445a1004010080c16101c400503988021540c0d1700126099141c2e03020214aa414640008510fa44211043d07070424004403004860000340c0702d0744004e02e0b0500390755810ba03030401c20300d44407031842008401690100c1c0019540303165800107000718150b0380d0301f88a20400070001c907500c2c0500003000c02c030501c20060410051602d644150000d520160950700d03070070780988070507080760000d40406a00c136641000c1811001c00810308260800301e500821400c00c07141c983c4000e806440c50f6000c1c44410052000318440074040e0010030001c1a200c0885000142c481c07408101942040c031429004e441807007901e0b1030918000749540446200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 876699955 1250 876698705 876698747
    0x806030f070b0307022a030c0613050904020a150206090106050409110405100b030103080a02060a1103130311030703020705030c0a080d031e0c030c0f030204150e0f10020f0d 76
    0x1030242c109015840540114254803600390401c0c1840d0300b907000e0040003c04030942c8588183c1503002e141c1014400d4485c41c1c420750003008504084402d005041c8141c40d025200300c540343d81e542c0701140144803d44c20240312030812108000045030300007402c6204034030314030090203d6540c0380d00340310603038003900c0d03000f02042d80034240c8291505080c0c2c040340c1cdc003c00c0c882d110351106030f071a50321081690003a00180e031481300004456410359010020140c10000307001040050f65a50305000340c1600002d8060080444040060340034907100e5141e0115940b101000d03a5074801540c038002c1d60b075103100d20481e40280603070a5051294984ad440e10f0341107402c07042c090244035000d0441207000b8540c6100039014072107200300c0006043e01c24481c0c241c8862040c1c03000038241c100910007410202d11356283e28200b5004001c00d01c00000142d41d910003201050400350810a012400118000d40758140241c118621034902c40b01d10740e0000302c00c02c00188410565900724100702c03081300d1b10b1841c003d4445814007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 876701205 1250 876699955 876699959
    0x30c040501081306050c041502030a2f0601090f051605122212110c060f090f0d050102030f1806180f0a03020c040608280f05010e0a030806030f07 64
    0x400b5804507076000c2c1e0395559020356100d0583d1840f0407100c0c1990141c2e04c03050007080038050964000104078404001780025410301510250080c5600c00001d6114946280144201034103841d405c0c000014464060030341b029582c40d1003002c0020900e090399803020a040501144024041900104007030b030141d51500d14041c00e0900c080420b2002038610b00b900300b150458100c00780c048c0c804d507110991003040700300300d10072044100074070340720b502c074524001d0b038010341075144260399440c2c110b0721800003002d00607441d6410300c00056903041d80b0f07544003030704507040030201000c10a040d80118840d0103016088903036a15141600b252229025801c08074550094001c650070707958211281d401e006003042200c1070b00c0c82c407020329400c001c1e10a42c11005a8004181a011451700d07000b11006400140d005050409004240b2003002000e01031107002c00c040c0c074034000144041d070481000c0281e0088000c2c801907002401c660b80d103030150f100a400103a40b06010038600d28001c5046460b982001d402409458 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 876702455 1250 876701205 876701207
    0x90a0e06031b030f011a21060f180f0709150b0f030a020405030a030f09050f1f02010216110f092401020f0f0601140a0323010204090e0c1302030c040501 67
    0x140c0b2009956a16114aa801d581840b80034010740c103507035510400004c9180344903010722080c0d8544401d5201c800e0b440400d400260b4100181041d80407850041124081d1205551412443d010148081090142003c0083d02d64400541003044a80710303103041010603d40030344071126101501030048071700010050203212010410266400000a0000603c0c255a600c0041c0c40c0c0102c02d501140807500d1107440d008080d403ca200a002003405541410384202d14a0000d0403942d840720351000300d070549444a546591003541078030b00946030740d18072910103881410b14081082003146110310030b010060b0f24190b5403d1a10b40140240020003c0080c000c1070b142d0540c2e20309400c0c4000d50b045105081503048060810000340c040d01c011107003c0d250b00d504210b00c10f101101d200c981580107000011007080043d00061016061118614412903000f01c0141ea803806480ba81d40100d0140341451941151000086000c800900085840b44c00c0d0110800004c070603400212109060000144000c12081d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 876703705 1250 876702455 876702493
    0x62c07183c09020d110a030504050708010615030228050316051303020906032a040524091f0e061c0c26010e0a170910050a050c12090a0e0603 62
    0x1040d000113011800503852201c191098020756107130070000382c03580c0c1800240082441528080c00401307000f44a41070800d034440346030b17601c40c401200070141d00040c0079480c11070042d040104c1e0380d801ea03400f0034a070307d01520040c0140c105452401580d40d070680c14134601400b8008441009144115a440e0303503145400300300040c0002800c0c01d0b098080c500040e231403c4281e00130020608416030101c95010020001e100407110000c209210900c0018640c0302c10703800705c0b1152400160200c5041c0c440e41d0300c41030500f070f081946045480040c22154000304060394894413281c4030b40029601d800f48050703080d004629502d610391000d408905482814042c201040e0303907034040fa0712500001d40500710703a0300c502070071110407203450040c41d0091090b54080200c0b500d03400400310b5100601508207041c150014054007841d01380e042c14007200140303803000c040c06071084c0d8500211780015200b02d40205a0000c2c510303031001058501c5130400440101d08152441c0400d4000c20024000b80a03c1c01c081c0200c4500e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 876704955 1250 876703705 876703717
    0xa05040e0f100c030c0203091804150912030b060310030605070207030807051507051c020904090605070e0909031c050402011b03030c03062c07183c0902 67
    0x540c0c0580e90301900144020403942c91810040c0d01c000030003120801000781161040503410045410400140d8503075628904440c0e02580340070003142c19034659141201d82e03500129055074119052890340414441052084440b42c013103a14284101141c4108004640c8811038a012444141c05810310100c2c140ea07000a03400700550040b50902e03a2070b03445120031508105021038550340071078150615a14a00d2490390800500c1c00d04a041448010440b030030000d1180d5042c0e0a29404507403800640c2d04e580003480103e070130110810150500032401030036451281f500a0040c0d01c284e001c1120031100208441d0500d000c84400303180c15610141100280102500c16410800c01c8c040d201c8400b402c207445840043d1003a200000d01640707044000c2c2c103494199010f28120000541006402e512400301d144001c0c040911a0220355907a94043c0d0741944001a5500d40584440300413801c005060742940c2d20f1146c906126401503c020b15000c018003518001900070b0003498001c10190500d5005801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 876706205 1250 876704955 876704981
    0xc050304032f150108010c0c020307030f051009110906030c0d0b13050d050a090803091c03090915080c040b100f170a020301060e10050a0e04021b1e060103020a0504 72
    0x900d14502e4000e8a4907021410301111000d001004110028091090001c1c4104508020514002ea0780001e6200c0caa5880080d119800850482d01040814442e00101082d601c00c104002d40440c241005000070340c01f1300c2405099100c011078030031b28000403000810b0308000d01d0341441180540c0c807810f039550f02406101400310250002c40003c0c00c1400020b46800e07144da02c03030b6210218030400170400c2034140e0110710150420041030b4043e844d09845030800720840745860701011030302c0c5421202d101381c0d80d005444c01c91400f4640340741001003030484401c5a18070021030704104d40100410080341c178852080c90b0321401c1c083c01300003410302401c9400d001e00380074107209034a021260342c00d842c076100c201c40d582c070740c1a400401802080d810070140301034208281c641c5040d06074800005031080c45034180c03d00502c81042080d51869507a43c040300c1c03000c980042500c0d0001c5d41100710950340c969000002c800034246103d202106c41e000079500381242c1c0c00500002e141450708007448000c1c984482c1882e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 876707455 1250 876706205 876706277
    0x160206150f040b06120a051f0b12151503060a060801080705150d050a0516030c2003040b040f06030509030a090510091d0115020d020606060c0c030a08040302040c05030403 75
    0x143e80c030100e034040e214422050340850b252800c07800c4486211181c0007947c1a4560300231060000318485400c0d66031142152004080c15100c2c480c03000f09010841c50703074982c841c000640318609800000095801211700742c03461608640c45800550321040309001b84e001591055000304054948a001917a41440c00c4081e00c1c039200004942c401920780840310200ca00703444200344545190303d2148003a1140f50b41c9000c10140f4000f00f0000d00c0d161142010049006100007803940200c001d00c100e80060000504059480781c1c0c462401a94010701e00c58100803e03d400c2c00070707004003404000c036113a8040c5a619520380d50708007402c02c42881c17042c0300410104000c0410110b1440640007a150b0070801c40e01112035a91f02d030100e10390120700d01da201d1004540000c500d012001d1740008041d0b42289040300e44a44461000040d58580301d000342c09258544240e5401d00d051282c0c8030024000e0b01c0c000e45051108000542c01580c10384010703100240020724600c03080c0b10340340200c0b500402e0790f1b000c1e10b004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 876708705 1250 876707455 876707467
    0x30904320708060d021e060d0e0705091315020d02040905040f050625122406030c02010c05120a110406030f050901110a05180306160206150f040b06 65
    0x8005580320245002011514440c148140e06030400519a4040d0080302d41240031441c640c00316140303410852418031315036000b1400b02802c1d41c1305001d8407070702d05400390200500c01d03080e6a0543d40320780c83d216071030040130402e0204540840001410418540011303051085030030a882c560000e40c054040010880c2d800d0102240000480c080c240c0501d0181d0000720046c0c009050841c1015005440e01003401ca6031280704c00300300c4d541074541c0558030380c6042030751000314818a00c00c054021708040c40da4216850014850468410900764140d80656404101c0c60002d070100383e080303818801030070011500c1401000d502e14044620f0690200084c44041070b10210714100643e945c0040d04680007190311840075990880740c41c03080a41c0810070400910801007080d150301001d04c22034080d0410004000ba040403104464001c0d090043c4001d000c84400340f0380668001c0503080c0c01c142500040c085c841c007040c250070072810341034440e910003883e403c0c00500c60b1040100405220300042e030000c10038005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 876709955 1250 876708705 876708761
    0x15110339250909030908010c030b090a0c050708220803041d090a14011e05040c050609011b051614030d03180203060f01090c08040b070507141c030c050408030904 71
    0x34804040b0b104c0d48a00328828109100031782500c1944002908052a00c1060b0050340c0e5114003040d0420741a070340004049c50700001c21501f920940d407025004200c002000a00407000440182c107100a0740c01d01e0711156116030340701d0740f203128501c24030300c0c90140d0344031041d014681c0c3c044064100f50100c04803182505541c0d15140c604034000c1c200301d03103650351700d060300e011103030410510702809080c201c2040703245040c2c0d81310601c41c4400e0181d64003580c4045010703107c40e4003640040042e40010340d841d04042001e85400380d5511000500c50611506180b0005030702a1285006c121620006020382824404540110020704c884c0c8181080d484d0840700d0707800561400d0040354002c64101e101c03c0750a43c10000c20300240c2e511056040b007003000d09802c10022603200041c20390800d00030f06d0322540d5803006080003c0c108010b0900300301140104a52100390510380b00030301d19801069202401501c88080007980c003401140b20300100c9800411007030200d45400e50000e00d81203400041c4103000303258050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 876711205 1250 876709955 876709961
    0x18032405090601090b0621061903060b01030f0912230a0c0501060608221a010e070f0306120f0c0e070f0e0a0f151103392509 55
    0x41c41c0545500450014008903849014040b50004140c4401d49403510408002074215074200e8110310440191010844583c1c0700700c0403000d180341e0644010111600c904003c4001d200c205c0307105000c2403900c5800f0720304081c140640b03940c46070001d8049480c104100c20995100048014410005c0004000914446c003d0006440600220366625182645524001c1d0031520141c01c200305000001341080542205d40c1c1050407020032030b0800c0031038407409142900500030b191500e0072200c0c000c10b001141e00c1e001010014070840b041d0f1303544141c0602c0c881c4107a08960850040340126602d08a45001150394903910b6039072284202c80c10803103650340709001804094166028000103104034100000c01d40d0004e642d00f01d1007802c442c040c0030746d0316003100082c8029091050507100803806108001150180368000c10f23203005481583e41d10100581d158a001400d91a10705c1358440400c6480421341031401c040c0c502c0000c3d00c0040403140a489c0183c1090f00e540040303101c440c10410300102d050b0304680 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 876712455 1250 876711205 876711211
    0x160317070528020a0503030f0306060c030708040b07150603050615180c0406080a0b030309010c0305070b01030311101e02130f0909150902130b03030d05040c050a050118032405 77
    0x89400b42c5030801034810420900007a60016100783d00c203006c0c001d4402246000c90760007a800303e071016600c00345c1e494543c3c19030040c4980609405000301c0c0c00a01883c00e8030081c1070061003020944401c5070702c0010701049a919000290007503014800141d00c99064410360f03040c1840003044103070454001d0501000200302210201682d40001ca0304114554015042d00d4000807460402e009039109003021079940e0003001c980d2810800007000034010305000c0d104030740c03e240e00f04181e40540e60b100d0502810140c0300c4005800e883c800c4880b4110950309922400345000c0280c00c155400c2880d401050300a074200000341c91480d01c403900e0000790418960303901001000344003408600b20200d07090051151090980060a03075007010641c00051365880b116403007505900000054080807200880c1c614000c104801e01003c1c030b85802e04c0248240302d183d10049481c11128000c2e0a5101c2c0c0045980001020711410600041b08090000403846000303c1a03080301080303440c0980240c008a001076600c1030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 876713705 1250 876712455 876712513
    0x10207060209010822030e0d060c0206090709021e070501020906040e10150215040c0510030b031002040f0306050403050d1415030c0102070905270303091603170705 72
    0x140d442c216507004890700d81e0209201c1c84048622080b92014070446561950050030864100a0040503569030030031001055040300d410052820f101d00040d544005c2518007580920424900081c00c1c2210300841d036601c080c00c011a0104400d080900d90207030002c41301200ca954080c4440005071311004e0250004000e401e05000c250b041c60351410099116a4004240c049240480c1c4c1c4c0d04250001150054021034442d40200c0c0d503224140912282c0d950740100382e00c0b803503040030450b403644e01d50019110fa0a0850984249041d865254030491045205a40b4042100d04081001c1002d691182d43c1c828007038103000d403134081810b0b080d40031201c90005032024000d1490520456428401006000110907002000c0c1030429400107982c8400d1403041403a4692a0400903004000100460381d50a00001e84604c00050340039100e0380ba07800444640d1201e2040c50109441192912028821243c106085070b000c8508106c140c112644040320640c0c02e40300d1340340c09401503409084141003205503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 876714955 1250 876713705 876713707
    0x50405040f2604050904030e030601180615021903261e0106120b01090305030708120a060b1204030507140303010602100b090a0b130f020310050d0302101107050102070602 75
    0x74640803000316590415100382580d904003850294480b0b00c112429640101c44a144598403442c04a0308204a500c1540e0907021f02e100020f01d07107401c40002404071054103130501106840300c00403400034a44030010070040c0d000d01071418070110030350611407003140641b400940b24000000ea00100001c0e078115802c455203903804118020b42c43d000d008103500c00c1d90640d20700d654500300c002031909a5291130420220f5071441d56216503801001c0380002190301c1030136680c036000d0506020310380f500218580041b4540540c00140d4190f02d910a41090750281d540e09410403015502070011484010b00480a10004005503400302e41c40c2c0703888016804810000f15075035810200000d06203481e00c240c10700c11608003400350544d0b903250031070310341d0002d411500025403016210000c0c4548941806c02542e10740740c501480d00011443e0011031140c0c005051105c1d089640c1c90520400000388900900141c02410030800342c03026a410401c0d160062202e01030800109884550032a40f00c40c80895016034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 876716205 1250 876714955 876714983
    0x100306050907050a081506090916090225030206010902130e10080c01050f1b1e0604020102060714180a05190509010905090703080705150103050c13200d020405040504 73
    0x140005200c0041c0102c0c00150021005000c01c0c81004c0c800a080c42340310349408000165245001c004001125942594100b038907656034050340000d40c002148110404881942c2c47c589140754440d009000d0f81c142d0060a1a0f86411580d03002908040008205002d10700b000087d2481c84041c020300500e50300100603240d610700710340c00e03182c52078545489040c8201406a52140e801e220180c030303030b4192048131584280c09555002e6080c01194448940a04207501410b107100100091085c41a03100307070210741c0c1350340f500001580c4e00310328071407121280c40381048800040610401c0540740a2005008071800d03d0310350001501009010f004020708000c2d840d0304105030b140c03001140c1c1c01040741c000104030078103142161300d440d0070705800301820001d40010350108204080010f03050040420020000070750f100d10748561150032801c100c502c0f481c1e4683e002a500313015481102d1004410001350016052a8221018503800619070801402e50a000010302030701c990007490700c075502c1950800040c01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 876717455 1250 876716205 876716209
    0x80606090907150e031c050705100504020d0807021503071206090513080a0512010e0106020646060b09010906020a0f110609040f021b010e1510030605090705 69
    0x1000520344190342d807050804000c906039060721107421900928064103818101c1d40402d1612103980c02030072101d00014802d080841c0c0c888050301c0390350310500c151004580f0a0103000d09550040d90082d500c640c0d8000c581d00002e0300b82c001880c40c1c2d40701070181c2005001c3c96000861981041b078404010030034204020040b43e4092040d4000b60010000800c0781b42405501241c1130345ca81c0a004000c0c0c0000a860f0a05034000c10548542c1401280c03600141e60712041490700702d400c28891345c8003501c01d03000498442150f0744003003d9264050301c009411a048041e0808c0c44c54400c0c0505403401c4444038000c000600140111000b40069a08c1c03113a48110f400e00040c00c2100c19031090781190098044000080d07100d00108400d03035042a40c0d41030041c2030400040561040c072840950203450181a48a00b50554011b080801069075214200e03d10101c001802d0716010180007000b90018229001071800d12507229030030508210484034030319141c0e038030a01194000d03158141d05034840340e0200b10134 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 876718705 1250 876717455 876717469
    0x2b05090c01020a0c0512030d0c1e05160b06040b09250801150e060f1306091211040f09051b100903030e010f0e03011401170a0305040308180901080606 66
    0x103040a00c0240314501194944242c0440301d8000c461207003041ca101d0340c026400800585201080c00e450030003102030030450141c24075000c50803d03000040b41c4050707d41d6150045042d00d40e00c0302044208000f180c504d03901c030744084d0300003007800d50711550f00c8400310b0903900c0e40d00942d441800285e4100b50800103880d000c43e11501400d40100800c08044010f01400a048000c40510822800e100c94120305100015426016030311807040d001101150012054160f42410402c8404c181c45d5003a10039290341c0d0900e840c220044006c1c1c000c410882c444c201c5400c8c10f600405015402207000103c0c2d181580e107045c2840760b0140d8008081c02f0019009403079181c00b0b00040c04d40c089504005100701c0c40c50380c001c5d12500310044164148030705014442c2d543c0307001d00012042c00c04010002c010201820500c40305101e002e0190146200806034062a0f0310000110f2183c5076405407122824940356550707800c61385d804400d040d203c80c110a6030500c80c035158505036501810582d0045c010300e1a0040c1030202c030f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 876719955 1250 876718705 876718723
    0x1302040b130b030603030d020a0e060a02030304060c05042106063b04030e100903080c01020a02010e190b0a06180b03011a0a150507051b030d0801050108010b2b0509 72
    0x2c004410070500019a4002040392401490329102603100c5000180030b586126120807800c0c0c11060000305002e0003136000c0011403182d0b12445003005850b041203001c4900740078a0003009403c502885900510040545181040c28400c0f9804504540c0300c401c9081e01700d000c00b1410080e04010030f030b045c1184212512000b02000c070412603a400b80b50584000704024009159140038240100060100b2440750b400900a10342251200e0360b119400c41701c0318000c0d4003109101e40154645407518032003003000300314000c07121140300000708480130a803a01100050041c000c05e15240c0d568400003001d181c401e4038806111905000020300120031418942546c07419a0f036640110080803185186036160950003007620f46c031200e040300d0240c80c1002503a5a210750741020301144648e40c010000c95130001502030344c0e00005e0741614001100c1c000c050f141d00300203004150221f8191401408400c4000001d00210002a4041064419600b81c01036019011240c400401500c0d001086a1160108541d0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 876721205 1250 876719955 876719969
    0x30f121e2f09100e01090509150d0308060a1403100509190b0105100c05120d02130806040c0e19050406240609140d0b1f1502060c0315040b1302040b13 66
    0x24007855403000800e25102d5024141c8280d5401c4003040540d074419202c0c00302824080c0800038070507420304010708800c0007113555920400040101190341e03280d005004001001c060014100016030310300c841e01500008051190702d14c1035121401d07401c0b90050703034501d116000f0720004c4203550400040c4040c10204560302428840c030301e040034000540c0010303541c44c00440c0e0315005894114851b400000f911484174280116503040030003050540d000300d8150f0049100e102d0503040b007551054030809140048402106031151001082da4075546900300c16031040c4101c2c40028001d444003010100911460044120300c81c94000c18400240c1046510b0086d080d83c003125104c3c01050030008011071a4080300426541d013400c04585902941004451040700240070110b060b5103400c0d02216100400c4001c01c018413400010a24400100040700c2c010302010628203c90880f80041c0006486080c0340550802a07143c181020903850f44003034006412060703001580d4580a0350411100034140d00144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 876722455 1250 876721205 876721217
    0x603192004021903050621070e070314043e031612021908030a0807020105061807110f070f03060b0402160314070f030f121e2f0910 58
    0x145160042404110f03608614001c1748a0361540d02140d50000520003592010031424600340c0c0440700803604c0c1050352a5030280e254107a071248002c505031110f0f100d403065150150000718001c101c180f100701840580c2400d24000ca28034441102a14414043c0790034400300314099110b006240034013502a1144208240da80d0b480e04006038184041c110f110020310540d4141a905002081e2417820802050103200b81c4e5110303007401002400c502d1040700e400d0019407070310b400900580b0b0030b00d47c20701503c1c01001e1810b400740e07120401500c0c040032204090300306201d554240500e00754100034040c090401811000729040c41c61501328107480404090510590050080d03480002e16001502011905443d00030184100c80f110a0310f54800c0100241c000b030341407050a800e250b04103040c0b0a005409544e210118480078204004840b051905042c10200c808501c0c2071408564100450340035a0721070944410340d0801015a0705074122400d030400150120358250a450915070089000310203043c50303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 876723705 1250 876722455 876722467
    0x403210e0c0a05031f0605030d03020406020d03230403270501201504020a080303241c1218080a05012003010618091e051e0a0203060319200402 63
    0x139444102129124401800210b041448075407580c2103213008010150580e035150345514030003006503110f4001d80c005442403485e06d40a141c030901c11850717000258502c104100c06030f01c403040c812440c0500140d040040414032601e154001007003d10f08400c50064001800d443c000000d42003c0031120200702480b80009103150b1000c0110392500585c41050000c1100c1d135861000482800701038005031040d12002c0204640b4032a0030b250082001220030139461804100000c000d650b505010703040c0c0d06940312150130400a841d801e00140001d08a050030521500800354102030750350658481038050384007440010a0000c01e10a510301d40e1014000c0c0c01c000c0ea0040c100000e248410710410b81000880782c82d20080d0003000310000e000d00006081403003501600b0101e00984c02c1c01d0a030015045207840701041c226400e0b004c01801d600202d0322003c0750366480402d00c02c0290001441075400d401100c3c100307140d000401e455466001e11640c0d9800d5240f144015450010f43c0709012540254810014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 876724955 1250 876723705 876723709
    0x1b070806071407060e07030c090501050f0d02030d120204050d0501090b06190315020d020d05090c1207030807140a08120f10050d05150a020901080906010b03010e0403210e0c0a05 78
    0x1101c5050f500b04c00c004c10481c020110701c03450728249074070160903584140b0011038911940e800003412aa011038480c00240941020010070a4040c0c4000307505501c00e00d1050306c590b02607445654204a020001030400740d840c2d011070204205400d0454850350764400700c0707007080311080cac1d000e801200c140c0d1001c01600316018409001055804041c00c441c164406890511145404403a1200740e08041507458910402d0300c400500825101016140a18010343e1000d080103000042111600c00086c5450703841d546030780d01c06e54425081900d0601444211f01d10120040003440c510310303c10b000359641ca400036004940103440181c81c1e1000103100c20140103549040301070703810984608889000b90521a4a030041c908048018040d21366044035013080b1405506501400c2000c0d4203880d2002250769050f00306880b483d00b402001c404110a00c01400600100c001c0540d1142c1305cbd04101b55031800341007400034240c00590130501c0c1ea0780c640c500241e60150034014504072150681c0c01e03481391814440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 876726205 1250 876724955 876724957
    0x3120b03070501080a1b110d020f250f030308061f08040201030b04090506010e060312090d030c080408010212010f0b0702090402130b090109020c010608030711060306061b0708060714 80
    0x8030326810040700c40302007410b514150b404031002c402e001b07101455400c0c0d136820252074011807a5601103980100301c20301c1031260000c6040320b1154801005484002e00782908503a0342c84045108401d02c10f280c200100d407800344680b11030060b60182e02c031980c00e85428401c109265414440c50241c20021508850310590004503017504203a0900b00440e03c603120602040041c20b5400c8081c03c03a100b0360000041403d0b00341c0341e01d805020103a0540b45401e0314400480c00754801c0c0c14041d0703004604000d108000c24410904030310080c3c401d1040da81340580d1550b07120300f07980001210440c5c00d00c11400400a000020002e5402044000440d03420540707241c000030a50351300104003078000c41c070b100054454014645e00c03811002e00e0041c0f19846558403841960000d400001060701c5561034950040740c001000003e8070807041d0320045c21102c44542100b070294a4101621580d040382c1c0520034102003110140101c41190740d1000100909403402100c0b0340380c0b42d406880d0205000350000000040b0348200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 876727455 1250 876726205 876726209
    0x6040e0a0b04080a0c120c120203120105150708040608160804080a080a1d1b121c030b0402070f0303141911070203030f030703060605091e030a08130303120b0307 71
    0xa52602c540c10300409551780101080000e1050381400740c0c01c050140c004000b2500a4015902d0700008080c0c2042aa03507445000c05682c0e0300040c0400421051400c0490001c4240c8000011414809295121019600035402070001325082a041080004d0b052007015118100c4d0316080c055070805458080080c4180e034021802c000480c1c000501b445620b40040323002e004ea40c0904180e5140c600c8810ba1246e9814080c40c5401d00003c00c000202c0c5410311840e090800c003000541059111494540c20040010f5800d609054444170641e94039034407031000c2d0003080e0140041202071102854000c045900c10003011841c9403001040c40348a40c10a01050182005844001503c17190b001d050b001038056440000e60602c00050200002c02d51003002d1070003854103803010301080c0c0d11180140c4d201d01940400d5600130f0a14159804280c4100a00061500016058440c81401d82d00c512001f0750000540391010408031604100300343e8015005042c000300d060007048500c1c3d8840010307460310558 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 876728705 1250 876727455 876727463
    0x150213060e1f05090f100509010c110a030b01061107060203181503070e0a0b04050306151f02070612060f0905071b0606140607020a0e1801021206040e0a0b04 69
    0x9416010744503102c82a040000202800e0301071404440818020040c0d401803800d18082d041021440d0905e0801e40202e81c1107034000c1c0c90749802c1c403100e8001180c5181c01d0850954210600c4c102d40344075603c5d00c1980901860040c0341d08001c940c1003c401070481c40d4a4500b80368141d000010400140f580070080e6082034112110b04600a403900e0000350364500d00900c8032030841d2000003407206560700070703410702481002560002120317a03035044001c4650242d40308860301900220001020301d98680c0e5001c0d4241c00c020080303034015214080c8204405801041e040250b400603105100c615000031407d80d10007a000ca09002090a00e150250420207a2107256105500c4002155059001d4040a41e40303000760407240c0ea17400700b2070601c0d00c0586454071400005800b00c20592000c2c0c00c104086454094002d49100f01062a019a100800c13800504203800783c070302d006a80f880c801007800201500b681403031415242d81800c00c100000c44550131004901079200c0c07007905002800007002d1681c000d401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 876729955 1250 876728705 876728717
    0x51206010503040c0312200321010f0605030402040f0f1d01060b2d0d0c1d011b05010b03030703030e0106150c03210608030c0601140a12150212010315021306 69
    0x6c41c2c5c0e01a243d03079201c00b82c2c8504590124403502a0242e0000c080e110409262003030300d110343d460020354a500c070028080e481c04084111402c0c003c10f0f020358000d6810601c09480041c2442580d0015401c5a007082d9165541903100d140b40442c454180302180c0c0d099a20000800c619440c08807441414414089070012840103a01d0045050040701d00310a00740e43e451603c0c541d6401d034a61450020b0020f1000e00303010071420255184c500f880211042c2c10040d048c0c640014030369807000b00007a5802e0a40b000c407071a6480f113840400c191014400780050354401d48000c199511141145070a4032184c0c0c0003140302e02420078070280320550180a2103142c41e007505103c1d02c401e00b00d05c0d84180600c100460020a82d0030f010380081c80080c000000c1c6100c01508040d507140341d0700c030443c0318099200c0740495507025009113818403c2c200f4031203801101c01e11a03c003036042c14000329400e00a980051105000100c2c415004000348101100c18141240e0b03200700442ca00f15255404070301c040c010380552410010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 876731205 1250 876729955 876729983
    0x40f050915220305031605040506070201053f06060a05030f04140a300203090118050a080c011e02030d0905101113091404060207031e051206010503040c03 68
    0x34142804030200701a55030541c079440003410f000e40664000d880c03035110821980c007a040d031a841130050304c2c29500020407680c5820140e80044416400050307522101c11002060141141c0241504485405179400c42920341ca1101c05040100b1500038440340c041c0c0c074200b0506200302c0d032007012644d001c83d80240ba89100d1700c0b181080109503980d0480410540b054924000a00000d0043c110350300b0801584d1140551204090a400700c1c1c449064101580c002e11101120758019620600c10040b0600d136486440d5132040040c0c032108030b540c01f131140742c0c2000d200140d4a5a204824020400c5c9481d00b420b5007400c00d001c001e659203c2c04114548542c0e130f9030b02c10030030488180700b0036180c400710030030500c07004804a5030b14a10b580003010320a6203a0302004005841c00460054405808220340c0c8a07419654689500300a54445a8100d08108501c1401220750814185510081c44680d45058039041070007650030760464050969418400280304000006424111883c00c1e640d012229441490b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 876732455 1250 876731205 876731221
    0x40b0703020328052512020f0d110408010b0102150f040812160e030a24150f0618150e040e01060e1611060a020a140315040f050915 58
    0xa00b040025000c100364015059408a2190426406041026912005021081c0d040f0170f281401052000126807528103100c55004070b540078000e08245401800e02c0c1a01d000e00200407203000009041c820700012409000b500f2003485801c503003070707000e000800b07181c0d07510f82682d4100c01000302014015901d00d03000400f00304080c0103a0318603a18030107090026080400007420382107040409100015221064012036190004078907085540101c0100005071000428040a41c1d1b1510244191500d91140315400d80450880c0002080c440380c0d10014181080070043c11f400c1c1ca4901c20540561243d800d00c0090300790800110701c101d80303007821400d8100c1030300400c0180c424401828240d5103801c0001072500004408030b84a02f02a000007880328400102c1541c05158840714200158440c83c000b0301603841a90081034441e45505112a10114200c2040610351003120311040c0d0300c07803070f2500480904050103500d100300c846200a000310301d002d000741562400302c000b8034002c0254810200c1c481c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 876733705 1250 876732455 876732481
    0x61b02011205010b0319180f170c0d1409100e04110c0a0b0a0c0f0810180b030f1f0f090b0408030412020c010f050306061b0c040b09040b07030203 64
    0x1c1654410912466a6816030078030701d80c0040722400025100310030705151040c024403501344402030811809901c00815100c0c62107640407448121000c900340110241c070404c0c4100031342040d0040ca8000d1891002e0404000c00018a890341503241c5481441200625581c052007201c81c90070304e141012100c1314031000140500748005110405003000201c04907250780118466442c1d40c0540e10a81c903944903094081c04032510710b180140014039001b041d1185510075032286800c04440511603843c0d6840d040d9554444010300c9200e49400d130744164400a9060501040305000112805000c500c20003030f04d00b496015850b00aa141c2a075500c8031070000b844c1c3c5034000c0302415080000030380360b4a403a1900001d203500540301541c1c7c0c00c01405502c1001d51001940710710741c043c180d5480d12002040d540075200e80d0006408207910072401e20440c9001c10f103600c1d2505491040c10024081c2249c10b10074401107600c0b0044480c02840003108010200d4098030103150012100d00d00140e4a40c1d130141c0403c21 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 876734955 1250 876733705 876733727
    0x50a1b030509120a120539090f2106070801062336010306050603090a020f010c05062410090b1605030703020723030a0f020112090804090e010204061b0201 68
    0xd2406042c1f14440c940c0405200501c0021490501005040f05846d954000320909010b2012010000008281010b0035644c0458401524682407810080308070310b00d0103100c0c200502c60358480010400050f5000307100a00400d086d0030801000706032403c0a0080451450008858420020744002000d10041c1c0fa071484041c520070030380b01448501200784000c483c0e0440a40000e0612001140c0e624140084074000c2039440001d00015065070300b071010149a80321818117001040c0c51030703000b0a27011321081e84107549000903c02041c0103602001080103411202c24052100340304501034441e0040100d409803200907030400c4d190481090441c0290002010007482030201090b842d08040e000151a01621080b2072224050041241d5103e402040c84e070b9095410351043d1002c0c0081191404005075050040c903001c40d448100e032100304180c0d01d64034002c59003054005400c104070b00c29441090f01c041c2c402c41c02540b03018074140f0009c00c00750312000010030030100b801004085a018110f8681 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 876736205 1250 876734955 876734987
    0x60c1e122a05030733090201051b060403140f2d1201092004030b1005040e030c0c04060501020c01081f090903030b030f120d0f050a1b030509120a 64
    0x1c688918000752650850b8004480f10303010881142c40c514007001014144055646100340b414842110b141c02501d4111000d0341809001c001c0110641400a800d00801c14010b00401441c00c042c80c00070301070506240f18800c4544140b1207040380700d141000316811079822603144201d400b07040048041442d031110503000180c40c00181c42c81c2e0721202c500c40714100e4000c1a020806c09415001d20b490340d05036298161013240007007100b80000782040342410381044980007203c40303180d1030302c01240403940740116000a5a1001c1049940c40134200030007241010f06440512405180000103540c070000d070100302d41401400000600b001544804009800c10601c201d5001c56949051401c0100404c00c030560009040040342001800e0008a040c1c4415041005025000d614824041d48e500721220028180380c444002810b09545030150728054001d10b640020b400c01042c13080010500340010f041d0525051a00708419007001203018483d10104901481d51201080c0085a40307008000d07101c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 876737455 1250 876736205 876736277
    0x21070c080105040605011a19030c0e120106080c15070f1a07030504140615090a0603022701170d030914061303080130030203090a060c1e12 61
    0x3040c400d030744c2c0105d4100d4510003441510414880d1486c0b03554819008940d4500015525004240b482540b08110300c0b151454500e60112941000a41c001d84016918131640c4d110503041c806441c092243da19008811111b45022044000503041c00707026801002c6e14102016420070309222914095025842c8422402c5d05140303410b0b030015000300402d03181925500c2e10315020010327100c800502103004d0100692510900f244503810000c117902c00401c54804103440d19000001a181e03503540c100d1f07114005090043d80c00d840885c5132500d9005030311409a4580500c41d41c945083c0108400140c4a254500843d0345c40403820155600c0441c18180c0c211842408100f192030018804140c1c4403911030303603c0e21000e03662460f810100840724800e84c0c0e20345c4001c8408407051102c0342444c039241842030050341e091181860002d40b800f50254440000300381e418483c1810402c100011480240c2da84083c198404550340368680d40041194132502440a0010440070114401e4070500c3c0c080d640160039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 876738705 1250 876737455 876737461
    0xf1403070e0c2104020303070b040c090e010e010b010314010902030a11070b0603010c03021905090409060e060a06090239030c030901020f0a0b0c0d180804030308070221070c080105 79
    0xc501d02d0390010b10301c542010300c1d40d003d0400c0040110802c601840c0c0040c01541020081e4483d083c441ba40070f00101c0d14482c00420009441107540104041d404c00d01000080884150b54a40d080d03131454000a0704051030b01c002900c07854861039802c2d05413020081c0040c0c032030b40da51500c000181316000e031a502d076240c00b080840420038480505845000190000c3c0303e440c148a50503401d81c060107036440740514011200d070603428801c5020b4540d0b801c00400c049902c0701c254071071004440b902c0c0850810b0381c2182040003c0001140620310052100b41401c51038030801000c562065102041e0114800801541c80800180c0e440c001500510120058959646140f4241070741e80c0e0000356164058000e002c000000040d010a1394003600d500401c0d48400f43d03403441d00d284c00340c0d44041048008ac940d940300e0350160f5020802e030103002138440c40f0b10741e64a43c1181030203070070a14010209421503102036209283c40d036004028441e03c440496155449213110b1038142c1084c0100d0f006000250718000070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 876739955 1250 876738705 876738721
    0x31e0f0c06030b010c1104020f250b0711071a0c07080d0306141c080403060908040e01171b0102030904051003140607020c1c02060a0807030f060f1403070e 68
    0x18101140c1c500d4074200030014580300151064403001102520884102d01418080c0c00e05400501e0310401d40000107150809081d220180f44815010140211005121a0707040001c081441e40e0410503d040120025001c0040c10342d44040318000e42c02e141c4000311500071021904010b0f9501c0f5845001900d40e0f0755281c00d600f990740c40b900102c82c2c00280c01e0400010f8407404a13503c0980c1c110b008bc0650450640452526211018040303040395824010003000002c2856849042038031071144420303542d030750701d8890700443c0c081040c0c1045c0080d141001c0d02036488800002c2c84d4075012107102c0549070904a00005038118000c0755003103034004d4200020001c0003a004000f040c1902c0c418000b041c00149450713062983c0c0c4000b01c501c0005a801011006a5444c0000810354501c04804c0301070b102034800d90201d541ca8015550310004036080c0811f100b0820b4050049840701d80c041101004000e1804950104416480c4100115071441900303d00d529101400600013030104508440303010705000d50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 876741205 1250 876739955 876739973
    0xb1b040e150406140315040f05060f0a110309062710020706061202030325060f020d05010503120702120312100f0602030313320705030c090709031e0f 66
    0x800e80c0c031440c034110000c21081c2c1c2100b80c85440c0c40b0017800a00c012220100f03c46040c010142066510410315841640010400c00070315219844484034142c00c2c1c00c0c030040f000290340d0a20107a00c0080300501c108440c6907030000d0055441000003a2640000c1d080b42d10b603021400522848607824040e80203181015412034000380702003481040100000c0d60b03650702c07001500d100203000070350541041003001e0740d07642c01d09000310b0001e10f02015000324003080d9560000300c82c2c84540142c00190041003c181c03041c140c1c400c081c010312040d006052210009031062881344201c51009200300c501550780c405000040040d201d04000554821806003000d00c80f15540261a110b41c1d400900b8510700400c001e44084280c3e4000d1500010754104020581d580d810a5181d1107800d00d8400022106010b21010b080e924103011140403000d81207450070070081c5410000c2c0080d00354020501074045c0441158065a08822260440c0c070704503400c1c1d401c60201150072407000b00540700161f0b0518030424040403003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 876742455 1250 876741205 876741241
    0x506040f18050c04112a06150f0d0201050a0507150c080402090114130f0e070303090807090501140f150316031409070b0a0e0603040506180a0b1b040e 66
    0x200c80440c00c3d00e200b0070098817901851980310341014008010140d852007549060314003d680c6510701d03100002c02152500100b110a02d00200140714110030074180b04000c1c42c204601178a50210f80c0c3e06640000c0e0580c401c03c800303102000400074010040c003540c4148004104201c000030b005e08150200700414580055805a125554040000400c80445031104c0144c601c0507154080240f0344010404c014280800c034402c0160f1202c032001c1d1800030510240000e1403180e01c58242050034402d5403494a100d540026054900d070100502c90340300c40104100500070215000400c401e5894003044030142d661525400381d040200c00d01040c5407030103c3c0303d0401d00c40d550381088560480154a010080d0513039480360f4941214005110102c40540100410021030420815598103a004592140d204541c00e4456811000c28004401511303510101000b800c4030040c40341281039102c0c19500000070b003000b0750251002c3d1040300d03143c00c688180c030001c1c03d409448070001e103040724041d90110841 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 876743705 1250 876742455 876742463
    0x60a0605040e03130303050703030e060a091101030b01120209060418020c0c0a061e21060509010b0723120c0a02241b070312050705160e06040506040f18 67
    0x42c4000210200001c240d4480c2d5007105650300b055491030714150340350350085605a0405172114284601d804080125078041d80c1c41c0b180001e10f640c440d042c402000b0b04c4bc1d0002e641050f041c0b043c1010542c0c0d021010304102c1e04c3c603260042c2d441040e0f0001912910499120080c4100e108503543c48d00d24060340903104804200060b640d8000030a0b08001c0300740c000c1c1c05410082051124841c14910b00706a5901d409002420710803a001b8900194402d2514508058100e058441c402407065040c0700e02524010000148854201007840d41c0310040390102d141800c44040030300d003100b01100c108005444c01c2848062304665229541000242c45129040781680107c840b42c28815051b02d0140304c814a80314800351180c141a101e060030003c5040002c0030410920643c20007001003003a54503583c8101720a034541e5980d54280385802800c10021005401d80300d11100d8003000104500784101e6407046080300d001410342d075541c00140060201041850000389000c8068000c16950ae03104000a07000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 876744955 1250 876743705 876743711
    0x510030c0b0a080f070e090c0702040f020c060c3a0506031b040e01060305030d020301030b070206060f0d052e0b06190807020a0f0305040512150c1803060a060504 71
    0x71200444014030602ea4840300080d01d10b03000416500d050060350b03070000300c1458076440e2441c030f0500240c0c900d4010749046158150002c5e1000842c40c00b1300c180101400c20300001d41c14801240b240c81e84076940200025404600000c4035020002c981d42049120f003456130343d04090f0a4680070707401e2400d004546001e01c0b0b0b4603260104a1510740001d490070340a0782c010140303070200c00e040c0503c00070f822400c2d41540d083d901c03080044005071013840906142c9854440041e16503265040c66000c15202801c00300554020800380700b00d41e2039901d942200010103940c00800e4181c54038003030345000b000382c6241c19a19800c1d003030300c1543d015008281303044000145051040c9061801000014403540391045900303004940080c0c0100c0c0580f00043c0d0144042c01aa80b0b40300460725050002e8000400440008000090900030744c948040c0b0b85000184110040107ca4241c1c094401c40c03100207421500309090215100518517070f211100c2e40503510290030340b9510f003040380b00d90021340082d001c2c091160342 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 876746205 1250 876744955 876744959
    0x302040c03140402040f090c03150c26180d0e090106030c0905040b030c13050a050708040b04062a020c0418081605120304030216050618130b03010510030c 68
    0x120030b0007581c215000720360050b001620740d83e00f004000c01c2103400c40010f03652035144010216035000461402103005d01000c8281c100c000f2100b904444c0d5004011050100101d04001c120320080b1600801070b6010442200b20307124881e545105c5192900f0741480f41c412168007c0c1d0040c0d001c02c0b0201090820380e030205031030362150816403e0302ca100f416100060000c02d402c0160740b0303003a0012140240080e0940c7e00e00152030000c0703805c0e0201d502c1d6041c0025280c42c14007819600f04c2c440d0b10381c0a14a40390001c480d04195032405114100500007030706540d1111000d44443e1a010045c8100d03800e004035000c01c02589450282d00d40d15400b060511035854110f41850010031310400307800c2c2c00d0780320614518000c0d0555410035003845055043e02c5d0f074480e85211302c2c01c41104000440c0201e0003034004009840c0081c290100c0c0306c0d00740d0052400740e0014003405607500f070b04298008583d5001c540e6550341501501044d801400c00002c0076501d50f08002c280324079440704181c0340080e24060b2000000e400c3d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 876747455 1250 876746205 876746207
    0xc06061d071418040b0901030c0806010e04080901050310081e060603070605120702070b1c0516020c01260103080c060112031b02190605040618080a12021005100302040c 74
    0x1842e540710781ea0328040700700814544500c16140340502e0030002000010a50844000f10b07058000036042105c481041c03c07030601101b10108440390060080300384000c50391030142c1da64001c034060145200c0c1406000702c0410300c9480003d440c0c8000d04450001c555017407203807003550005010010315038500ba00481012801500f000b00c3c000c01942c44940750949054907410900c44400401400302c821405445000f0805110003002031080754101e40f64200d49034485100403045400c05840310400078980018102031a4000ca05610103060900302200c08028103403140013a000c0c600e100c034030318510341d400100401125201411640c1010300c121112aa02c64100b4040007070700365009808500e98284018a88890344082d1451502c0a0a4000102480b5500191050481e0000d10100c1c80200c0d00340072141c2d02c09400418400051582441c061824506a885045158004d081c01507051f1010103505d0013000540502c41d1b405104010a00e045401e1914000d00f5010491045080681890800d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 876748705 1250 876747455 876747467
    0xe1015030b010e041b1e05010302031504050702103204030206150d1e030810051c0203011b180b0307021f1d03040915030c060f0c06061d07 61
    0xe25444a1684416400c2c1020700500c404024011240c00076007014800c25004500f1100c03005140c0085000081190a40a02c05400994201c241058410b0041201d040c9456816103410a0261000603c076181c12900700e08001118400c401c107603045c000c2c0140001030304a018035400411804180d5059011019102440700c01c1d60081c00690049000c2841c1002401481c80c0d0f0380001080c50585805039074034a0751500140c030515243c840030b01018414160003481540e40300c0441d00c40402c415042c04c00040e040d220615258645a900b10015811900e09605c04034a2400190030f00485080303501000f00419824419445c140b28507000004090300448143e0780a1021900a48415a002c002d840000f071040450b45030010707180c083d002c110001c202e0100000305440c1c070140d507640341440e01c200103441095481100c40840083c0c100301081c107100404082d1121031808101c0d07418801d90485000004c01e5029001500d003240002310b004100d9102c14101100d49446155552080000da80d9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 876749955 1250 876748705 876748709
    0x306060a180209010e150a02010f063f140706020118032322050f030a29010b03041109040308060112060e09030c0f0118080912010e1015 60
    0x9107080003498994049440d4000c0d140070328040c500003d01d108680001a64140030510280002c00c0005110749455828003518855481d102024040390307140c01341c4040c4510540741c0c00c022182d08030803480a1148424810a02001c5a0164991124141c1845400c8001507543e02c40786100300a0001141030043c0940c0151000000c0096101603075900d0588001146000d929407036841c0d81005910710301c01c072010f0944595144045003610b0066881c404550b44650801c0348240402030039040d05a0380040c0820044da03010038902250312108070100c00c03407d01c82d0030040320503180000101d00c1c03200d000050b41c4584d0240320b160f00c07045102030901c1700b80d001c15103014000556410003c0d407694022258280740f500c92800c00142c05654184000304044162031085094100068444408601700701c100e070003d01d0a4001c00103039070703a1303034000c0030b02060300c03100500700c040105807071005540d0000c000d408006064028000e4003110641991501c1942c00502049840c00d440c8036441a814903070134003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 876751205 1250 876749955 876749969
    0x8070315050d02061218070b1e1e040602100f1b031a0306160e1e19120303052415090324010305150c0913020c0712020306060a 56
    0x9801d120a11041862410302aa044407003044129148424454064400c06e034424101c00304041a22080b410244c060340407445c030410600c030001c055100c6990065080200403d540e80d81c40701c02071035145c02c15070703065195001c0c00c0c04600042e501d50045081030481002260810610a502d0600740803031380c0b80b51002c45a210b00e000d0740141035000e43e00c60740303220034050003420700100a200000c0c038110040700d0180c400c0580400808015070480d040d03151080f001c8454103562418042c5440c1c010a1201e00340d4403c5d0305a070f424084000140500801400b6001e9241410301402d04024010b05010384280103002070b105204a030011983c084511101d000a064201030500c10031002c085421180f209641400f4a10360900451074504421440030400034102c0b035103604d5030800d503007401d6500d0f100e40d101d1004042006424050f401c12509078550441c0c801100c002e1a4070044000e0040e5507803214544264000403c0c142d82d0840201000c2e44200c040303600d00e075101024000302ca5540e110f501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 876752455 1250 876751205 876751241
    0x201051b072d0602120702060601021005060a0b03180c010315060c081b06070e0d1a0a060b0c0115092c0f060c1b0601030305090112060e090706080703 66
    0x10000d090820300c9803000b80d4800e240c01d41c19211480b40014034440302e9049545a5000442c42440c210390344950768050802e0000d08407500e04580081e4460075040b5031000065a00c400103240342d541c0142c2280030f050a1509603849140c8500b01e80400446a032294042d807084c007000a18030362080c0074400940000c2000080e40a20b840c2c4152008094a4801c4a04680030701410a40c0100900d00030012a201c0c401007146080040340034168036085056a40242c20752072408010402d83c02141c0e80c40c45428070341040f5903680c401110018121a04a442c40e2180000c1072060000e054203c01d461441c000c0b0042600c0b0754410905049900b40300306940b290142009501d08a185000d40d4100810180141e54161446c802d000341000c0c0c04640c0d600d002c10700413558640301c01401211031000441c070001000b0f135505588020301940500034404e4100151300414076500303013442d04518024182d0104002283c104403103020380340c4a0500410380000d00000c00030717940c24803070701420b03941c404c0c0154a8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 876753705 1250 876752455 876752467
    0x7150e3c01090605040312090c15180311030c04020c06011a13060f0306080307020102101d1912021f0c0311070609060c2d090305070e070201051b 64
    0x10340000091148598115008a1611a800002806801d030040c3c410140010b403460249409800b40701a0036034a05003030314024048001480c00c10280c803d84039071903a94104540000b004407140d0180e00d00281c03441008010020030000075100a13089610110241e44500c070300503091000b00e000e0484601855440000104440c5656906032101506203080191602d107688038075901040c1c080e448030000801c050150f0b8440e43c0d242c4100400303044007201540c81c00e000b50300004d6641003038514a4100c555039050362404ac0b40315620003220440c000e4241d03100749443c1c004041c81c0030300380d24013903801e600d5203003103000310610124039012590712040000c0c0f80b200e560f00030f00c2d006240c210f40a1040c1542d8940c207241e64641170000c4d00c240d07440380b032000c10044014a0810150744440c20f6030b07001d00002c100540c102030b60310b400d0448400c418402ca034041c0180c03203000716007203840c550001e004c03801b8004001c1441400c005111b44903810a800134000fa8550000c4a81c1c002d0030600c0070000080309001c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 876754955 1250 876753705 876753763
    0x3070809100207030515160306120201030c030e121b07062001061809032304050603040609080f07060b091e04060e0102220b07030e06030c0c0307150e 66
    0x4807044405140b0403100b8054072a51001d1410101084038002e0010a2040101d244249140740b800e180141c80c06220907881c20102e00c11216649500a0605032549010f00e0103030301c039900005180d1024021541e440c41102d0045c1807941c0403d00c005011001000c445000744c0000076840212a615600ca6191042e0400f8082c040280280058400e54955000054881820f09110b0301c607000603200190810107460068280c00c03215401d40d03020350040200c482011541401e803000c40394243e903034598907600d501d4418001e003181e0000501c1c1007400b186082d012010000508035051258204000b00900c05c410060880401c0b501030800030f00c035035004ca070400c0c00260700d80e8212b40306400c080794402b544108a826a00f1282c4803158600003180c2d1014170658031032a43c0000c010342a01640341c901c1701e4070000c01420346640802d01451001001c1440011700c10b00705c941013020741d8103980e1a031216281031034000041800c2d061000c1d06050744880d400342e0100c0c0f0700600c4036034144900c000c0705400c21 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 876756205 1250 876754955 876754969
    0x91914090a0e150c07050601060e120706080105010f0c060509010b120109241503110a060e060a0c03020f071206060e070c0b220609210e06070f1e050f03070809 70
    0xc0042c4d01d20b1018481000050010070020340600348940746d10030701034514018004000d031801007403030300ca6002c0e410801c6041e07040302507581510000c0c0b03008000c16001d0032003a26003941108008211382c0c6403078104036038500194085184030908581504010484200d0385003602d480d0b03000130f00b1002d10b0344850411270280b141c0e030450500600f2008120310001c564140860b000c01c1d07009a5002040d000b6808461605800380d4002e0002410816980e1041c200072550f54010006120180020300c00c3c1441803500801081306503030345003011070b0380c40390311958100c900c940343c07030000c541c0e16041580100d2445030010b8018812a000e0782c1d450504c04440d2504072040c100a005144d0070180350001c1180050000958030140d805010041b50301c04c290b192a41000e002c00c0f40391010360000540110030994003240d000d207012021203d054598440c0d0501403660940a20010b114110441100c544000404000103456000b00e00795030501001203140c039200d100e10700006080c0d13801001082414a0f0040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 876757455 1250 876756205 876756211
    0xa081501091e0c030605120a110609040e030a0c0302010c111b12011103040210141c060f12060614060904050a022a06100608070302091914090a0e15 65
    0x510b4070070259120a105401c482058512070300080c2c489a080c04181003490300308036064520401040c400095880e01c850020802500b14403801d0f0000c0c2c1d90b50a50f64503040003101d0f41240c000c5ea91b4400d401c000c0a0310007609001e044000d5400c045101a4281c0034610074510310b00124050302a90541000798800310110645056102901c1c00600d18090320910420f0445100d5100300c2da40c0381824010004c00803100611903041140c207030180f001c220340400c16921a10745070603c50040503410304a000103828540c200322080b50000c000020000c201490f040c040310301a49040000c651101403d030a8518a200340c240c121000300040d8115040c2940042d50041040c100103080c808000c10380e06080486034240842052a040b0020444005100e0740303030002107112031300f44100e160030700c050048000180050107144d400300e90510303941c4030b1218401808218810103000540c6a56540c0c0600c0c01c00104240100b10210000301911420311541c01940112002868800014100511030343d10003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 876758705 1250 876757455 876757481
    0x6040b07050c0a05010f060614041d130f0f030f03051b07030207030221150702190303140412031404050309060f040b04030804090f15030b0c091801050a08150109 71
    0x409444004c10b50038440e090344803006181c080b4115240c640000c0506e000305500c4008100304120070404d0351042d04080ca0032031901c180980c090390b102d1184400c00018840302408452618203035404000c0d000503500300d0b4620a46a420300505840f0b4220100c0e441281c8003201c04885910061001c40c0c02c401070400948284110f460644c0c07240d020a88841078060841c25543c076618141410440500c5120045005500600c07040d16140200039a40c0c0c0e0445010500440400c0d80704080c9440b039001800d01d0369841c4800090b03803c06180c8240b040c08081246000207240c149994001281c01d1200f60040c2d400200940c10440b40500300712440c0e1002894490711041000001884e81c8a079010300021801049100c0d101e40c54000b430101030716680e120030700c1010315204a50f00d59000340442d076419a42c02812207801c2d40d6030031171014a14490b42d0207642e80050051301210318007030700300c2c02c46050740c0017519050005075450b9040ca5a5811810b4018283c505000041c0300003011648400222103103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 876759955 1250 876758705 876758713
    0x20108060607060e07051503070e0405131a1801060506030f091f09020a05040b061603032004030212070e070f0210020a1106010b042303010b0303040f061106040b07050c 74
    0x1050369401c0c221140240e03ea40185c2111204000b2440d048854010305102c81491074a10728107140700401440025140503c41e564400104008800c041c02e01c001da2075008117200700d40e0034a03514086c10142c0c100e401008103e03d00415628840060107001d0840d4000f400650540d1992002003088450041500d0000d01c20751101c1b40801e1003010b026051544140e40014400d08030b40140309404030702c2c0d00721f10300480c00c0c0115021340340c60321001c4401c030100c124003c003031600c2d00340703800c03800741c40070b4107480100301100c0d24003e100088000c02070044910842d40d07800c243d4070b0410b030300c1d4848119200e8400002d240c140040d908602070410780c1e20002c400c3c4141d030042c04640c09007200300c2e0800a44c480008241d00c980201200c0100304040c09405209545070400d803170102c200c060360152940b00502d100d5807040700c0c060303500d003500402400540141920744503615000320303102c0b0f50b50b188074920016601c4281080401408030b411030059400ca00ca50545980700d05c2c007590303603612030883c9510344e201d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 876761205 1250 876759955 876759967
    0x303090405041401050705030708010603021810050405040e060705070b0a0e0a06141305030a140d09060506090a0203100515070b16020f1606081b1818130201080606 72
    0x349a1180380c1c440c5202c0c82140120059805107507013110002400e141c01e00500b00140054560000c092504440c050b18001d83e030707000c4180c1480d030203602c5e200c1c402da082180e0081b62103074950440302900c280d54094074200201400e510641c1d40d6020290b4510b0701080c0704010400100340e0b01c0050a9012820007000b10350700107450b80452404a01210a490b407556411000707558003a5010502c2c0c10400c04110003403442995242c060300c0348038940b0898140b108072209840d00ca51248280da0500001d084104005441814140301910080f11024416040d10001425905c40d5109890040c2c0f9a400081e2146040c01d080c4200001c0b000c0714800341081c14408400087e00d0180c5040c0318222101c0640c42040e07240b003000e0b1410114800082c401d07001242e0040c410400440400219503480c0b400f1802c80c1c4840080c1001000008120480c0050008141650542030840020090000d5070400291290341032308282120b010348448140401070400381f40990302c641034064102c00000c0c96545022 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 876762455 1250 876761205 876761209
    0x601030b0d240b030d020601060f030f051003030e0901031a07032909010f12120e030304060201023a0f0b0d0303060302240a0305130f0303090b24010509030309 70
    0x381c41107107040d80ca407a85074400110304640d0f000c3c3e2405150241c004150765081ca0902940f144414012032040018542c4500d80ca18441d412800401e1240308003003000d8109000d604005044a00003a00880d90000c4809014107120400d2412250018038000c40448104c2c03075402c255102419640030184c49040c044400900414a04031031840b00610080c0405900244110604160700c07407240700d02c0f50f4000f00000740311414004e4000785d12000044040c58178140030f584c0c02d904a0180341c0c02d4407000c1000b0030101e03015802403204400440400400c5030301441080400520740c1e09000b00e91100b05806444442c0540006219a400150110304a1032060220380034220b4600c2c182d001030b0300c42c0c3c42001035090142510148090b0f40b00c05908200b45002d01c80398602c5401d503258200355031030700003c01103103140282030b007825888000c0800c070122038140200a406100350982d5081c82c2c0d44089525074510a4140c150180c185402c03540e00d42c408801590740380c00810802d40c06020802984101d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 876763705 1250 876762455 876762473
    0x31b01060b030c0c0714060909060d05120414090c16021816080903340204020f0d05330105040b0c1e012a05070501061502010b0109030b0601030b0d 65
    0x140e034075001140e104c096000803186080496400000a100da41e94a081142c0324101201c1905005544d0303044d058541c00c0c08103a440709030310809800c6014028040301da8800d03940c000e000300c1c4c7d100100409006000c800b0002c0415056402840320101000751035144000c4003140d600380da00040c8209000001c031b01030076000707280131200c80400c40b90040b500400c403038001c8200350300301c4602c000950a0003004c4801e11903501d40012159080045100b008003a2a0111419009203078040e1055443c0d4070040d40d000308c0d81c0c116161801340785040c03000003054a00340c00c8a2a07a0300811052031455500c515141e00782401c4030360007450420504200c08641c1806650052120418502c02000d4600131102d11380080c070b9020031000041d0741407103030170000120500d400c48601c0c0d03c0d44044402d400c0c3d2002c0700391400d04c600c00000381994242040040c1d2685004000c2940815940084c083c0c1600d1030011900c100307041c00000d0095107508041349041d4400e9100242e0802d01600c0061882a151556400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 876764955 1250 876763705 876763711
    0x20f0304050d0816150e030f0f251109010501020a020108011511010608060604060b1303020f040b030d0906020c040e150c0702120109020f0f0d0f060209100e040e0d02031b01060b03 79
    0x100c41207502c6400401c40780c5104038800c45a1b40d0019600f007000c208943d030110701c5020351001d00d4000c04103091103440d80c0c6d00580c00c152000050b1114150f00c00d850b2402d40e4868071181d1512811003d40001100d5001091502d8041e0341656030900682c00d1041004481c412045010b082040c4038610a0105100f40304800180075094000d040700d150080810095400070380003040c0c81c0320f05200340120038180c040420140c0354101c0b8140c01900c580d90104004080b25040c4070780c540b2410b6004411035402081840941d6515401c0c2d032640d0391040180010f039895890a012140c0c445041c4d41d1851020307040c000d400c00c0d41c4440783e500e4011240c0018480c2014145010900d0b59202c810380d0440c94820a0003544020035100361404410040005105081d64280506180d00e00c10030305040121a504986000c0d000400302d20464003d850004e10b01081e6200c1580250310f4620886096580060350a0f00c07a031aa9000703603e40004002801550f0242c18407006941d92154004100c014441028500c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 876766205 1250 876764955 876764963
    0x50a0309032f07060509030a0b0903070602071b080d0c1e0606080f0609011b0e0414070e03100603020a0323030307050901170c040909050c0603040506090d020f0304050d0816 76
    0x140980560b401142022415400542884030400580c205502c0c0400d400000c036400400e01ea085664014819007103114081c00148810702c002001c43c00c200400c098a6140050030a04600258032890a0f030b82da204e180c042080400c020240b00c80005880140d03c49041d00b001c0c804a00c503001907078410040c0c0701c0541000055810581001111a0007001300941c030020b03520003440858040ba85140b40c402e0401c0380390080000580da860700945a9410120319819400c0107000300746840c140041c043c01251140600c01d00482e80000300b0b403c042c3c0501826640c00804030303d0000e10307668400580305d15a0a4a101c902d207505100c0007070301c1050010f184652a40e4444541e00c6100500040c89029280700d58000d907a0400d007400004c00ca40c200781c4007514800703040041c040b0040e00304a460a04016165036001000108005c00c007c00840c1081c010400700046499041030b121083e40c50f8420424800c0c02d1354410f010401c080c0c50304540c888060f90140c5629483c21509a0307a50b2007900175448162 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 876767455 1250 876766205 876766277
    0x220b0c0303160f0f080a152c0408030708041b08070f090510060807030902031b01110312040f02040e0a050a0c06050c03031303050f030a09060b10050a030903 69
    0x110b41d03196000502111400d080c544100d07084206503010b8041360184910308200201c0760002103401c4c4050344110081f130b4800c1203280320503aa504484001e40500c071018000c0c108502e00d060b0f03401303940d0f0042c1d40c0a00e90000314507042da90b0700001110340341c10060055030006040c50b420780840c03010301a54009000a02c000e400f0050400d80546844580ca1307110840703551070a42003009483d003c8207080c040e6040e51828480c0c0d030b110030500710f0141c0b0b503100c4040d40c03600680282554403850b03003450381c01da000300b0780301e099107081550b585a45038080c682d072440c0500b20603c006030010340000a40c00f0700d24401000000e01c5113981e40716920300481e184007210240d02100b50002403003018061100148040d01e0034514040000690907228000500781d180e201038200d40c020101805803042c0d401000f10a1007064807031500e840b02c84049e201400040d64420701c0c0001c0554182040c0012003d880b80365101c0518004a40604500400f860310040e82040503001103840410300c40c552000c035041c0c0c42d034045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 876768705 1250 876767455 876767461
    0x350a0b010f1422050721020d0c0e0d12030f02030f06030615150d1413030908060c0403020f0f060406030c08180d050c072c0601020a08220b0c0303 64
    0x629003824092490344190403841c084400c0d512260300d5259014030403c80440c1581341c0000c20f4800c5080d21351181125245254040c0445000b58043c01d0052041d8406100300d22020b00156080700d0f00e00c18440d0404820254030000c02c40c03480b041f16180070381e40340018510141e5840542240c0096400390700c95071444003845614030b0204034094200c001009401900300841c8000399450094030044080f000d0040380504400401ba03124820861700d0210302681480d00800741d10040180c500128003041802ca03012995000000e881d5106440d5034140358606410741d000c008403560140c134140c0d031080514a0072449500c0706c40141c002005181c40c045806e0040400c082e00b174080060001c41d580c4030072000110101000104c20781014240c1c1806580e960000f451241007074201c0d0480f007040e2100781800c546203205924298804014151000040d84861004a844914454001d400c802044c42000315280d01e42d6440303030003203900c4011190300c541c0c0c40c20307000f005030010029811103803c04010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 876769955 1250 876768705 876768719
    0x21f0c080f27030606120f070305150a020c100207151a01120b0a12080705060c030708010e0f01031203060504090b010f05090412031a09040c060306350a0b010f 70
    0xc0d2901480c8042c030424801d4400c0020a95510000741000d1044009045030b040112051050b85e01001100c01070b14500742c0c0303c0c1400c9035a14214914030b800b220843c00050300b1038a07140f003990031124900b00500f101c680900c0344d8001a40088409a81d020071410250582c80140e224410100d150300404007001d81d00c030800036152040e1000b444005c2410503c5400a83d91004109002c1d9045d02c92104150125400c4c00d0029006041c0020032034883c180501070034401d00000346200e131000d07580f100d105030380310200c80310010030903601004c0f5107600c03600610006131a50514004c13140380d40f0f400a4400d40d03230030000e0300b1f44189030b1090f2808603840c0e005200300704042d4400740192006880000ca00d041944d5040c40d01c0c940c100d48241010743d91704200c00c41c2852f0340142500510001d0141c203550400e0700340f582c010355461064a0100303251800008451641e55900520080700c0c002420050800450314850401c019122603101d00070100c40300006646181e219000c1c025408520801c0e0b03082c084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 876771205 1250 876769955 876769987
    0x507020d020a08090d0c0b031003051b011d01110d0e031009050a110a09020705030c01060f08100510050a03080d14100b130e130302070e04021f0c080f 66
    0x61100110b411101001000c64070700401c95000320360540700590402d003075003020a9524090b812001200c0800000c1c001c4280350a500c00b403c0d40e00410984501c41004143d0019080c02e507108280481d1401e00c0c0c080c030f2050008809014260107042a40c030700ca0aa508a60408041607410000b14452001018070380c10204116810710903104010420f0030096120745582c3c0765218401000c06414410801103134031007080420040c80442400d5440f0407090c98403039243e80115649444640c03a1180028144002d94001c90803a8580c602030032070514034920700009450010107080c81d9a1906a0005141d140c0509100c0154040c00203d9203d4010140300400d0350760200c84000a6401c0b503090205030001460070307408848070000195035520b06000008100c00131b940c0044800440700d01000b40244400b1a00400544658245c5030303159115103040440d5503007940c001e9004890700c21400c40c00d286c0c00c1c2d02e10000d14003500348038a25070803d594038115a8051a01e0740391600020450341e520b00c60b402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 876772455 1250 876771205 876771223
    0x140702010c090b041d0405010902030d03140a20090402040e0403050405010207090c0926060f18032505120d140105040513080d0204030c080d021e1c0918050702 70
    0x71040344d1030b251410800704404800040c0d100e100d14048004a010864250b0108581c0c55001d000e03294401c0c1ca41c040500105070b18031540b0003911054001800b1141c113440740c151450002c080b000c541500807040110145c20402240d60407a03420000402d0389804001c506200c0c92090b910036a4507414031000905050f6241e1000a001e0b0034200b0780c0228640120260707058812041da201440b082200c495070181780110084242d500455040c460b0265030500410703c1a8031210b00c4203864441e003030580703989100b43c0240c0340c1240360502e58850300b0f0300d060182601e51400b9074101c800d007061000d100c4038150310021441d41155510307102c1d60540d40303500c3d00d41801440200d43c10005443c00002c480300094000d24000c00c902c00000701e001c0d070030203c1e505a502543d000b01c01c482405403140c100990703d545c0c1c07040c8000540325a807c0009403904004c40681c600c1d0301903001e000c250f82808a4400040d540b540064280a0450408034002000300c41c1c803501c14104010105103810005070282c1401052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 876773705 1250 876772455 876772469
    0x5030d0b0315040c12020a031e03030c170f0c040819150e030712050d060f050405090105131e080c030d0c05030108070e0c09040e0610062a0204140702010c09 69
    0x8801000046068100f07548122121710041c4080c500c01480003440568258000030080911a00310b000f110f0003090b2003808180c420b403001c204011071a0001d42d00c094030403140f40c046001e510005501402c142e031a10340c100c503d08a105081c1a00c2d40340007400c10302c0203006c0e01040c03e200e071118018811007004840c010101c0030020001080d20448240d240d1042d41c0028080e000c1d450f00f400c104500c00d404490300b051082004018403903c40301c0c14400152a4451705116034102400300702604410300c60340b4011207524028401845190380d9040c0240101c903100300c860549480d01102041c90b113402001d44480b41c0c0080d60ba5150700c402580101c440c628085403c1100034401480b0611000074100c040d100d00b0441441d241e40c4404007440144214250903800909101d0005052640010014010752207640891441a02e0b80d508403030b03811404070801140000720032207008240407030340d01081e07003800600b02051080040c0d0b0f0107000c0c1981075403c48010b0313540e03801c1501502d40c07045041d4050020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 876774955 1250 876773705 876773743
    0x207080d0b04060b0a0302090d060c0903052103130503070b070c230c1c0503120405100b0d150f050c1306140703080c0408160603110a170604060305030d0b03 69
    0x28003180403031170f00802040c2001d069000850145c0c1d5030781c0c1c108804c2c1315503208034140110035822500600310351080c44100c4251050307640070303602e98aa07440d9000450740e10001403030560384c8006041c0c90f0343c5020034058400340000c00c011808100861807240c0300f0074a9454078051010130b4540804603030545400340008080b660071400416001143e400d10658013120314241c620b400d03040c1101c08804010009025100020b100e81c50742d0003101c0220322a501a5007581c3c0d942040700b400109642e20a0100c4c3e9010360140e100360000b50800159054100c190803000421526400d05c1e0001c0310802d903a000114035000c074a00215080c8244041c0c043e008614017803c2e84840c00b0000804c900547e240201801a481b0000ea4031280e0101503030020029a021240c0d000b1100107845290082c0340101c0c00000d0803d40403400d044906012a4003004050740d0380000021401302810340400c3c060b080540c016161840000410402c0000d00754907201c081c00000c42c001608101468451005141300e01c01e11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876776205 1250 876774955 876774959
    0x602060910271118090d030515030d030f060501140415020a0b070f0f0c150b060c010c020f070e04021507030201020f0a0e18010b1803010603060207080d0b0406 70
    0x40841c40e2100307035108800209045184038441c0000054100c50000918404114a001d103c1c80b00c1a03202c036807806458408201c8580b43c10f620100c40b0460342e01040c1d40c0b0082c41402c481c4e1183d031113558010300c50f102d001c0c40b00800750002803c5c84400d00e0b010b40040e480340c0030722550190070310401c0000c0400342800d5614215412440100e4040d51203040340003001018850103640c000c3c4152000c603980b10b054520b80d8901000c0c040d2078200d08191a80004800b1541d281d04240211204c7c00c2c00c85c3c00039912042000013950000142c01140c900941084050002d06a401da0074001d101307081c00c05401404a040d4145070b00e03442c01d01c6070751145401ca80d00300c00703020268070b5411328101c4481c0d442d00b00070340e92205810705a0282c49845006800400009210904994050414410410100c95010120341100a06819504207014009008008002c0300081d04902c0c006180740380301c094004a541d0b660fa03244c80c4101c0c2c000c1c0e075094840480c000b8501400107000d2241da00042d4089a041003a03034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 876777455 1250 876776205 876776221
    0x11130506011407020f1c060510050904110a0f0609080c060a050406050f040b13050907031406040903120905010501170f030306040b0d170a02010c09140906010c050f06060a060206 78
    0x100a009012014400003c202e82507450341ca120185d0340c00041d0100c41c0d4000d20402c007003912080300314103846071441c0c03101042c140c2d02a1a40c0100f1150b004142e821251076984075210301c102207101090b4084514480095202c00b14003015004124070b4440154462171710b440f29003040031f01c1040500c030300020040c1c540705c00d403c41c00b9a0285c9026150081d154030400d0265506881035401008144601080640780903071401880815218280d03001e41d0a81c981d03810030750036243c00d5049100e4003130f10800040c01c5818180d01c0360035200d000345800586000020346942c1261098042911103035110300c010300458103024440082c9400090081500c64986200e642c0c4901003d0300d00c61290342c650302d1285450b41c8400b07056815540204013214500600045140150700c0454000095401c110450f501c042c060300c0014100c1d06a46082040045400c04016131000b000344542e05000c1c1c581c0d11800402d00030800005010800340040c029401c0443c10024044001d0b13010200315030254040080071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 876778705 1250 876777455 876777467
    0x2131a09100b0f0c0307061d0607140a02070e040507050f090108030d020d060b16060b04020c030f09010219030207180608031c0221010f050a032105090d1113050601 72
    0xb607a0240d401c50321144180450916441450b80c280f440d4070001c43c030b04e4140329085e807007192008440803c100c044066a800340340c5801013101d2160102e10b01002e01c1014884450050400a0031441514030480e2101039035920f0180549041e40d1b61352104034180081d0622701e000c240c6c402400c8444500130341c90100000c1d541d11a440001c4845030700400c14120104003070300300001502c2200b0303100f46c07580101c041f0b82402c2010580300340e5009041083c0d12280f03080c03074400c079039942c89140051403500b0404041c050b441d82c00400690b0442c400c000d0100c3c0c40502c85020002118402d6002c0c200ca1490300246050b0180180c5030415903030b207414420400d65100000700c8a002201c1e0100c0c0c01074803101c001c0c5000a000b902c5110f481361400d820403070180b0140008180c1664160b5251034040d54503402800741c0c00b0300034000244142c0000c850004061400c40da04034510819142040c0781503210070104002d0044079000b194199095040001286170480314143d001d40d01a4041109140c024002841c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 876779955 1250 876778705 876778709
    0x50d0806030a1121100609021602040513080708180316140a0f080c240304031803210f0c031b0305220825061b02131a0910 54
    0x1281045148201060302c3c0c581d080c0d9aa074403408504c002d0040030b4008991140e01d22010780001c86d2516101046c040098401d884200c0c688003000a03c034802a42488001c0c18040c04111100c090003c0400019280710000c120309d03841261450346900802507468040110900410302c0794108221030030700800d134246214126903110019221000805020400030b04180e008403000564115011030380c0d010000390200c0070003080c2d44010640c8070194403603c00c4500221900c800f018100b0114001c02d21030b0b8082c441d4141002844810155265a1120268841041141141a60a440100c1ca5000505109900c0c6541001016541903990003090300300c0c04502146240040305070b400030b06114000b620002504805404603040704c40c2d800c100c03056028440c50040c0d1080b0849040d80c0343d041000031840d03041d1a210081102d04205003500c14030542c00308284980030130400040980e40b410f08a03581007005003030000b40f1545070405a0005241c241c0214050301c030081c1480745a6500e4015501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 876781205 1250 876779955 876779963
    0xa0b100b0d1a040908041a07020a030305031f080a020907030b0d12030216050105060a15050a080c09030a0b07140f030406090c05091e010f06020d0c060608010f09050d0806030a 77
    0x2e40048007045031402c510781c1042240c1003450051800c00708107920008000352130140c1100301030007480c03400703c50251240e91002500010340c10350800000740a400616006400582e45d148001066228140507911030750003490590b202c06c83c0d030070a43c1814105240c100d80d2619081c8502040440420010948060300a01c400c2c051000202180d22035415148028000490345900303180071f0514134041c1c1005e484217442207904a00c0051903800d9844962514072654036030b542048540b020179580100e000707004121144041101d540182e81c00d00043c82c006100302c0d031000090500ea400200851020141e11096280410061000c10340000c182d0b076000b40c6c48580404e0039a451310701100c0500065202540061000c001d00c1003c4103985c1c924075031a154520b01d080360781c1ea21015020f00448a1050001680081c00a0300f0400d1241840c50103c030b00030f650100d25540d80d41007076421200022080005603544191120821809100132076074101d05d4074240049003812400030740c44943c8040010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 876782455 1250 876781205 876781211
    0x30c090617060f04060e060f030613030305070c12120606050a050403080f0403060501030302030a080703050402012007260c0303092b0501110a11161502030405060c0a0b100b0d 77
    0xb00381e950b03031000300c0000c4403024006012140d80c60301031031101d05e41a01d4041c800e1050514064981c200000c01d60b20a040c0d041312440d6041a5032800d400500e8041c103e2010800321104c08800701c2d0320740003844461900380e59400303078510024041d00104c482c5070f0803500400404203d40c10000c2e52040584051b2504001c0c00c076036515042605040520a96000030503071400c03d00000113241d00440904401c41140d12000b216988901c022011503a04131802800306115a0f90300a4555000310300194480c0341e001150901501c0300207034484c444c031a809812200041307038016102e180c0c05206291044200750000d5050514907000100c0300c40e10703032000113404400b211101c22121900194421304680080081011455500820607144e20980036000030807c6004031355203000d400100800c040e10346111402a15003000d10400c0f4411030540c641d4210b100c1444080303020b5841c6001803088810300b000415610070b807454980045e4900810a001844101c1c60811142c20b84100301e07011190f001c0000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 876783705 1250 876782455 876782461
    0x4090b0307050a182403030f030204050303040e040501140906061c1505060d14010606090b0313030806010525021002030309030f0d06080a060e0606041a04020d060506030a020703030c090617 83
    0x8020410170303140c41060020840d1052001c2c0d4100c80220990307000b5039031005001105c3c0030640a034800c81c40307810b4040e40104010007014500d503501e507400c2031140c4000300b100c503030124200d008001c064542d9403240e0040e00c14410f00c0d140201d001403500b46802c40781c442c10003040d200c3c0410220042842800152034000181c0c4035903600c0c051802c096844201c11000f00702d91002c0600030030140c0184000303c1c2c007400d800b2801980311000d0f03d108007528103d5890100a50390105c44c40403000e401c0a051210a00000c408003900d02086040c50035100300c45d03003076140c05004201034641c000b88004150740041041c0b282001000c0100d4211103248103040341c4d2000b81c4800c28000b403807030790300440700e80c091088480c003000320940010394a07980c03810490b03489031201d9040004945a5026102005017108189021030030310360087d10000e0419000050482c6c2d54001160b01c55008589640302c5ca5030004024040641500c0f880300c4644d0280b03003858015003000e0018010384612074400c483c40c1551000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 876784955 1250 876783705 876783749
    0x109060f0206011a220e100e062202040e0609181905100f020d1a06040e0a09230f0109020a050409111e01031b0c0f06021e04090b0307050a 61
    0x1c954034810341d030249540000914078960780101702d502900c450510000301258a080302c1d401c6210079642c0c004030140c2140c44403804c0101410080e021100300c4c2e1900038400b146082c0600c007420007040081341c03205461801500300080d03130a00501641148048150358104c2d100001410000c00e141d203000c2c8a103002c0c8604101d4500700c0e49c101c00320091814000c803a102c0d8003e40d0090004115888003d00001940c0542c0c4a580341c11402e0240d04001c060200300091240d40c10180d8000e44102d800042001c400d4031034040c542481405983d0810051144c40300920042008282d0103545800807c0349040c1c1d54001680800e00e0322490348516110b90142c014098144000e11008100074801000302011144071003284401c009804c1c0400d141009084268040f2108801d00300300b0740ea41c0552054040d03441004440e0742c00026205941d00f800048a1382651300340f181d60003000a05d40c0342d25280b1300a034240503150b0b10700000b4043e4000c50020400740d12003036800320996100661050408040f002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 876786205 1250 876784955 876784957
    0x31b030a27020315012106090f0803040c090b060301151107080d0311030f0711030409050106030209090a232802122512021c06050109060f0206011a 65
    0xc0d2008820103402250214401601c2440c040540300f074060b21003c110040000148410034401e1300121000b406040349401640800581d0f032502c9480c0c0060034000540303c0380d50b01d4601c00070403183c00c10700101748001c0c0044a080f00340288031950040c0000301a2101152240c001885505210300c442d003807450700c460044040710008803100044880041c0e840345c0569407011103c1012000c24580b203400000102d03120110b0313100e00d041c2c03003049045458102c1e003114440362a80c03c14060380000d000c041100a91801024000e1000382d0307026846903000800c2160b07a044c05000009002d00d4440c1c00e00d40d80c100039290420140c120750b0011125901d0b065108040c1000114203c46a44003603c2000e0000080d40074012003d07510041802d195900c500016032000c416898900c0342d9400a0030705081841205420040aa80e0307101605158102e4100903284802042ca008841d886090901143d40d020b160980200520b1400401e041d00c20301d8043d49600040c001c2000790700c0c40c090700c02c00f01c488800c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 876787455 1250 876786205 876786221
    0x141e06090a0509090c0f121207020103140f01030c090c170903040902160b0612150907050405041110030b0d0b0402030a0206030403110601050f0112050a0b03030409060614031b030a 79
    0xf6110100e14580802c0c0d0a480321046604144540784903502e840181c1844c0250b50700c14007500300141313500c0e0032039002e00100f50003600d03080381095159803105811103c8510103901600c46a03501090341d505520300300140b02e0f110740020302c00902d0902066005944503004062101d1020308c44012600e03280041030440c03045400035042c56000107456a210b8080103440c00d03e540c014000c0c8002921500b0410107040d4865080f0503840c2d0000031807101030f4074210001c2e9085507940e030490310304955503c045029100211000c0e034002100714400b800c60709002d03444089524a0303140800010900c140042c007441002880074200003450306c0080c0464408010031850260000c02d0b0030b480785824a00100f5100641005c100a8014074000280506101045141c0000140c6071039194608403115400103001c0245080409511001040f5050303c0a20041c00075000c01e003000b245140c00d101d000f8001122602d00d14541010400400900281e840114040811014000799603a00d41e600740c0806004c181c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 876788705 1250 876787455 876787459
    0x4120302130e06280303080a090c0e0c13060c021305060a120206040302190f06080403020a0807050a020a090c020d08010807270e01021305060703200313080304141e06090a05 76
    0x100c500521340000800504044030b110750303101c4545540d00c02030791003500d15401c40104007a900407030501540c10f03c14038155000701000b26180c14042107005038403090b201680208003044981411100390304160703d1501e98842010f4041c4450b040ca480450750340212446212408042d0211035821941c84400b280c001710f400518581740f0307441d01c00340d056480c1041d22440d542166640c0c80004c11030b002d2088148580d4058010b0401134032141c4600140758070a40f000c50b0203000da10074007401030f80c0342c41c00c0b94040e00c0045c43c0002c143c842e0384030203403400f5038440c0d4a44c14401448010468004002100c406840b001c240d1101c140860701c021100da00900d11404503c80d0a0a00c11254a84154042c05607104035501104030300e642c0b0403d209061041070000b8000415000e0480c2ca40250502590300c00c00f01d120440e86842d2142c1c1081d080f13400680c002c0310003900b00080400c03c18907100d800032544c05080307070b40141510030f100125060100302d030f010318001d00000c42c3c15011583d03a0071b613131301c010800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 876789955 1250 876788705 876788749
    0x120801060e1215062706040b15161112461e082205061b03160506010503010e0d0801090b0a050d0809042004050906130c020604120302130e06 62
    0x20140c80d10005d0003100c10600452034615080045d14045260740084040311001c80c1c03414039081844201302034003034416101d6045041c11040a9165440391041c20b10005000e0080b06100312080c507800c0800c4a0054155058505900100b16041001c11800d1256505404900c0120300c1c210165901174011031120f121540d450700f05101c141c400030980a0001084e5601c100e407111140c000350310817405402c2d04840305000d980b0544030110348402031500304500b00e90400030129280c0028280340304088941c0d4110b02e0040240b07037002d0090f0f40c0003268490180803210782da03d0707005114920520030543c40c192070300040411a00d0f21008072024100c05861031440400c43d013006d0900b0f622100c00203010b54580150141c20865034951444001a42ea00c00d43c0307001c0ca00003c06c03044a0001d00381c540d02c241c60351900a81c031012841004070000090300a00190314007405c1070181c249103003081e642490b00400a4090341780180c0e607079105403064000d0144107a201c207030224400920030403a038280400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 876791205 1250 876789955 876790009
    0xc09040302160e2502160b04030b06060301030201020c100309120f110a0c090f061806080f030c0307020d110d06020c0705040b090121120801060e121506 67
    0x341c049900e000c2d540c8481900c071101a40ea2019506031082261403464030000c52502d0481005205540420012540304417035060b01310f56400720500d1200d0f4054038904130005401c20030400d50f115807640c8480300300c0301d41d42550f1442e00040e4840520080c0b0a1094024584e910603260003030380141400c54208601c080590010031000d02494511289100800e000407421015508001480070985610911030a1040c0c5000112006002200302c0019200e45610b4003044506043c003400c0400480304202107251847c011926085c94801c0240341101e80080003002c02d0907030000704440c0c2e0380d80d0694035680000818281505030124025000d5840f104a04003a41448015000b40c841400c1d00b000b5188501e95030340401c000c4900300070303406800855990040103004185c2c0e201c90b036101500c0601c0c1035442c4550352903800341031040c494000840c800f1401803000a40c01040030000310700590b030007890f840c04003114036580c1d00c45113403400740c03002400700081e459100c2400c0721004441049082c14048 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 876792455 1250 876791205 876791207
    0x506060421210c02060322050703140a0812040c080307030903020a050d020a14040b030d081f030b06241b1204300b010b0d140702030a030203090c090403 67
    0x10001c640a84010500149034050341151840d008411a040c1e11a4450b40c815035007444115003000381248003104001000c01403070110703e06110082072054002d420614210300e442000401e04001015159002c2c2482e00e000039803c0b003c94a11501e400281e102640e283e01c1c1a00455180760003950842c0004202c480c20983c010714088260f900c21103021110030384403000e00c5441c0c60101e00196110380302c2c0078108001809030030980454180944081820311080010a107008480b80191300003030b030454104441000e203412202900f1142d03411a142407441c0d91164102060003a044500c40d400d0030a030042c0740180354060588428000c1c0400d52120700500c4582d958000400c040f20403170246040e000c50000301d00d4216000c0d2040d4909144c0c0c0800e11011b0030000304040365845212040014400d800b0502c6008124002c00020045580d10f0700102081000c7d55160303900e2a07100712500c001d102d040e58011007620b802801d01c0c5801622a030392a045546810b0411190075088640d000922040c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 876793705 1250 876792455 876792509
    0x4090213051329011d0a05030304030308010801050c041a0921030c070e04031e170114010201200a0c060204090207050a020913050607110a0c080d021006030b0a05060604 74
    0x40404003d0340414011001600718400021450b4500140c0e604002800f91012010a00d0f00e000010b0007aa54640d103400100f45180e119400c00d402040c1201c00401048900340119540000c40c404c03c14101450441000e1070040d49402d41d00a540d804034072002103843e203031030b600a80d1954906034508055854001910703544103107142c840501429001040410302502c01501403070340742d0f8910720508038040e512903c100c485c11441c170070032414086500d8945e00c9000c1950103484140e004440b10344c1c040c000a400c480c00711000b440d000b8602c8613075801003450fa90503a6510340e107034104410420060700d45400280b2898000c01c1d40035202140d404140074000958201f118400d48201e12503441e43c4030025621040c448008015a01402c0010b000a2095014040021004080f20001c04007a60303200002d00c00c40e000704107194050b180f03600d01a60304002560f840c1e50b141c0300402c0304600319281c031426080c008107001c00140e19000819082d031680c1044600500003400c14602000c85000701c0400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 876794955 1250 876793705 876793721
    0x1030c0519050a09200c07051e150307050405040603051006170a02100c0b0a0c140c071707030b0a020a08011a030711011506170708060303040902130513 67
    0x8000c030201507240009800100350541c0e10040186003610b1800c2281c0026007164846840010030000360a0440f11840c4d01410524074560050b140039401d000038050b50703070748810b4140d650706504510041c0b03580720010340d004c2c4042c5801510340d50795a440c03000d407070700c0c421030740982c4d0050310f40031b00041802404680c05503200b001d0788090040315908c0480c001000212104c03560f0320b070020b852000041c90841c1c0010ed81d1402410000015000c6440b14440a401242c02c0100760f41c48100c04d40d46564094203203000000303004012811b0603034078440548d07641940e00452044a02380500280302c400c040086d403004550041300020070703141441030440a90000c071a490301250b0000004910300c140d00d030403101340e01e07102650703603095a40c0c1d282c003203414049026406c02d0039542e509190b0103020345040700c41d01500d0941c44401404614481018010500500d10001c00c08000305004455402008650442d40c0c0448056100d1201c0403090001011943c0080c1e0b000b120305451404900c41c40e041640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 876796205 1250 876794955 876794959
    0x22031d030c1c05100207021e03011e0f0b03030c03070303110c01090c0e010f050603060904031e030207110f090103080705011b120f061a160807032a0b0c0f0c0601030c05 74
    0x4d07180820000c0e00059019100c4003d40c056034504c690329a15840c2d203d841c20800008001003820403060007800e102e0040f00c00328078005912920b0407600602c01d409071816034001980250320300030665001b02d80300d01038000c0003410581c0711081a2a040b0090080d5240e80701551f00820010500d8500304000f502d5900c00d514100d460030000080b03610080c40c1f108201c8a0151940340b55580300406c120052200500c11420b00c150019201c42d04010781c554480c0e42d100d1500d0040c2d481c009400d0902103031710400c0c940c9105411040c0200a40e8445071400e904583d84402d40c5134451025181c49409851250814190f1182c064419030b03030030354404541481840809420007038581c81070306401c2650720034018035926500340b002c103410300503a000007400c403000c40c00340c514161820b9948042aa610034403040d800200d0f04000038052808541f203902c610520707075800c103100780c0d95030b80e58001095005024031401500442c002c1500c1d80410215480382180b00207448041d82c40e850094045481c4e401428 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 876797455 1250 876796205 876796213
    0x50d021f0915051207050307021903180909051c050c10061805071e090506041203081312080703020d050405060906010915050d050c10050322031d030c1c05 68
    0xb101c1d58010400c8401d106000034032080165110703182920746a0015107068118410b04000894113142103100d50780f031510944d5040120985914481c50800650300030480c4145400300100002d903000860300c401c00e100c40090303007001002010691f0f8600a0200b0f1400c240505071350040384500307035400b0070107952180130b5283c609448a00d896085a004903122000300f04c20103a07030341500307040395070071410012240382c006596a103520200301c040e0000e500c120384203220103a07003004050300314001c2c2d54000c054603118614440385071208680398030000341d00801e20254401095015100e6011501004141c24007400a42464503001e90740d840100c0c0c16051741d01400d400811001410301491510010951690705030301d0500b07080281104840030122074900c603903881400f03640c6401c05a042c480d0496201d641d100d103003200b11032030095002e0254041401228030b548001a400201e81210a0340c0342c0f031810312421600c00801d01d030020f480070095000c1000022110300c48003214401c2e2403d84554159 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 876798561 1106 876797455 876797489
    0x90b0a05061306091b1110091b0608060103110415050912151006050304030507110301140118140c07020d030504050d030e0f0a0e01050d021f09 63
    0x40c1202039182c030400b071640c0c0c154122005e1004818140001041c0d410308201d5107800a01c03900301d680e190341d044464140b260030710700380340705010030000e8001c000d84580b0b020304048d200700c0b601e41c00641007840c0c207004034084109940803641380108450204042c4502654160014144990859443c6649000c00c0c80100148003000362002480103113410118452586081c40760060303401d00000f0024000025845004c6406d200d410518000036400c3e17601c0001c4c00751090b2030140c0c540030304001c0042650348445194111440040c4001c1003170481d001c0185c107c03610100d500e0348440d5000d010840250604480d540c5000c5e109142c0a840c143e25440050581c4030502c9003030300000c1500c03c0120580c00c201c2032401c2c2c0c5820072120761882c00d14120003d0352a0105000c1c2d0360003404495803400c00c5403200013110182e54824035003410806c1042800600c1e0592910601400719211902 = true := by decide +kernel

theorem cover : BRFrame.Cov 876618705 876798561 := by
  have h0 := BRFrame.cov_init 876618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 876618705 ≤ n) (h2 : n < 876798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
