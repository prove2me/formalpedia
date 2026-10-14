-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:11.512289+00:00
-- url     : https://prove2.me/submissions/c73df45a-fcae-467b-bca8-be1f04b6d2a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 381474820 ≤ n < 381654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 381476070 1250 381474820 381474839
    0x1090902210c060309070305070603090506151311090603040615090c021c0e092e0509040b130507030305030a18030e091003170406031503030f0302030a0603020d1b0609 74
    0xb0980c40041d03c2c0142d9030389a070240649442d603181c1c000b400c54003414002180c41d66141c0c020400450141c1d049030707501d8584000d480120321141c2055903004a01c16000c2c0d600c0b20603500710000126140d540ea604015040011525940c01181c0c200c8619565213940d07080f0b030f018840c003075000c0c00280500300845000b418001c0c1d03651000842c5c0c6034125131000c4428503401c0c450f105008508801400b0228581400c1c1d215030507031000c047c640341c44403448040b1601401c142804040440e08010103182d09030b05c50751600600a0400b0b07080007056903905103188041001084404003c40c46a602c0c160b1300c1c90980014000c0f940c818541e01000e44241c0803c00120f0b902c1064030340705da4001c403403a200380d44505850a800d2010b580c4002d122040c690b00004072029404003410464101751024010207060007201d689140403404010082440c10001a410074441d40c09181c1c07202d000700b40010038036100d4000500003c0e0a9400701e0342428914400400c248081e40994002c2c030b92410003180700307420104c43c05d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 381477320 1250 381476070 381476083
    0x703150c0c08040504112107030516080103080309010e0f0304080601050609130b06090a090501080c012a0305040302041802190b090d0204020405192909010e03070305060109090221 79
    0x851141ea180c6d0031100548120f80c1c00c4410015000c0b201414905140c01c2208410404844a0b4082031501c000605008004422030300891403a03501c0c1000c2d40e0075665401c07130941001c0c0505147d9036840b80f11045e4107104004a446205108000b1512949003610f124030b480c00c140c00c081d00484060202502ca5212040181c9402c03035030100c007182c400c80d0300000c600d450040781302d026400b0900d85800a60381d40240d00c0f181c186c4c0c00c2c50041c1e800b5101c00b50f0046d035401c403a250010a00c0d607110168140d4000700b601000b141d0503c0303032070020b19141d80c0c0d80004068070307a014850106000102842d50451031301c44a076074219400c00b01a20a0075280c00039120503405503400c2d041c01581003203014811950369a0458000c0c280051140100384a000b03203111845080d401035444c1d0351804c0d101c260103807401c08481d14050644880b0240750911080c011a54599000c8540d501840750301000b100003041400903901915070742c0c200103079a242a00412a004810314019444050701120300c50b003036180484d94 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 381478570 1250 381477320 381477329
    0xb040207150e0c04050a0603110607080304301713020916090506070606060809010b0f060d14070e15031b0c0a15050708070e0906210703150c0c0804 65
    0x240c0106800b50726030070300c5000040d01d9803151600f41004844070a43d8010000d480c001d103030044910000c2020711605104461018040389030a00001e400181000c20980098142d0b00304400a880403a100c004469404c04c0312201058034161a80345010756110301590120a205692081d4485600800c0800c0b8008d004000551081400184078501480c0d03904020000603152070b0b5155070600b042c00c0100042c2c010280002e00e20341c08503841c107030140110010303214014a000c240c4501c001c200516584000101c2400750f441d84a150a951070302425180b1896554070303044001903903075042192030741c40044000d0b801c03e001c4c02841260307103903003e80708013040500b002e0b10f9a400120840a291100d14078009044503500408650480190780000d8050302568a07982003540704c215041c0d17226181400c06d41d0b00140c05000140b11440c0107000034020041460810501040c0c2115144c100503250b0003d80d41510070351400c0f071b0f906903903129030100c82e400c0e454a9680b04000d42c0c2d401e07042d80300c0c9201d07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 381479820 1250 381478570 381478613
    0x306050709150512070509030f120711150301140103090209091506040903080a18050307080a0305100308090d020a12050c0a08010c271d060a150203160c050a180b040207 74
    0x447c6006500c040124111050940040701d8440120900001c0c0c294418402214120918034800e1164244950034420310b01105030f0182c00c6a081c0f26201d0541c0555a1b021410181c483c5c02c503501688904009071302668400001d0014207007000340400510101038552806585004c91000220f6480074000750054003221001c210707941607414800121180c01000b9261340000034039038040222401c0101032003065501c09000035130301c035140b01c0307118021480041c10303010042025030001d00e4220280c0800c1d40c4028917492075580c4032841c41701c4114040108598590010104140c0362032700350440c2cbc0082200c480203109031100c590000b083c4074100000519107070b400c40c2c2c82ea00420b20040100f8090a03c14151280d601c00c400f5441041000a8404d41d0150181c840e0124408030a620030344404803554009610346000203180c100400d0301c518050b1078070900600040307042d0f03442c450142c0041c0601c014405084250404140480b4400d13620780740324034410065003001814a076940340b1808040700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 381481070 1250 381479820 381479827
    0x50a1209080f2a0a0c030b04031e09030b0f060f091e0a02030106031b08131103010c180e0106020705010f12290102120d090c03060507091505120705 65
    0x41e10815038052600361502c0c20801041a4400d02801002c465240030020ba204014609050b045500c84081e0311001e41085070840c01400455106001d95170442c0c424070b03109110109414042c12481036211071303e400103014020410902003407150080d084902000e40e40040d007001000549010354644040e402412a80300103042c400101402c4000c5040200540d200c51614441200082d8001d000c1c4038082840c00300014029a140d082c84050b400c05602e8104a40d103036106006080383e45a8001c658104814a0010342c6440038018800c04107100e40710011b007180c420411404040d0107030400000340010200412036140c3c00517603030301201e90a007003003050351210050881c4c2d00d240f0182481d2095082910254860090701c00700c205001001403681c0701c41c15807000482c0c036003a903100c42884119040c06009642d80b81544001c0c4460b100382c640c5841c0c40c2e1f40b603032888240c1e0030459409001c5107440000704804221554094190110707840e109103051000d0000143c00403018000000700070010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 381482320 1250 381481070 381481073
    0x6030f141b0c010903021c02010911010e030c0310020421050d0507020a08011e05100e1803071205070203150609070c170d0e070506030105061e120906040c06050a1209 73
    0x34119000c0204490013840030194506000e90744010022000d1000140701114050f1681306210302507038558401d10504e000702d00c1c0350045510a080030241a807500451445091a940810000394844c840a10158031340d45080000159841381e00e0442e1601ca001141085c0040ca010844a4100301c060078216100c949600209003882d007140c001c502e080d841e01c203400003089488007410340400b01c0600b0234000c0d940c80c48a903d41c191081d01ca4030414038143d101259008050101100c00002140308581c2020016118000c400020330401408a40c000a80030b0641c03c0a0100c6c844942005a41c40610f0500c140440c0007490010038001c10040340001c03290800030510031000600000030031140d1141c0340088600001c046901c000311280c420400c000610b410040d003030fa4100d0f180203083da41455444004107400e1804081c0886101e9000c001c01078000300e06104a501410310080100414545441e101c2900d040381e0704040c0c2880b105011030170381a40d100c000042c030342c26051404940740c06903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 381483570 1250 381482320 381482371
    0x90a0e0a0912170c04080a0209061206010b0310050103090312020913060b180909060c2203030f170408040b070c0e040b040506130206180118030c06030f14 68
    0x74a14001c2620b02038a41c401041c0394001d0280c000c1034201000501d1a455400382041c09209601c90402950001d00c007403000f42c90001c4943d54054806001c0c0900c001c5912095810702d80260010f0720300710000b005001c81c161414141c04040c000a081c108008401d83d24041d10050881c0e000049558001820702102d884421200400a20a105c1480b525444440e22401c2c1d40090080e1062a01d030909000101c0c9881c902141c0284a0200035000c241c0380c0305505c00c203907441517041d881d442020f00c0720b44c0c0201000045210040d802aa04e103c0c4260b1140001000b044800c110400b042a51005002c04111100101c404a6810501055540603285846140101c0360342c084008150340c1e804010034070242040244c851031244050701c20954810000c60701c01d070890003004c1d41081c005d20881600300d08040325802e01200506002c0050105c1c01e84010b41420641c004035449040c141003005125014040c0001d85601e4103410701c40600b00c8a100e000100300100680c110b20f0720111400c651044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 381484820 1250 381483570 381483581
    0x3031909050709062306030604050705120c030712020a021209010311031504050702030307020d050315060705010906050a0603020d200d05010212010e1501030c0905032a030102090a0e0a 81
    0x90000039507444655030700c043c10041c070185c071078061051081034141c54014202d803002c507540d5800404076420740e1102c00910009140c01001941032042c2000210075612060340e00d42e06c1a08183c100d02d80e24905044000d10000d00401c440b45003c1c014407011086a0300441d50315204826000707240d444180200049000d030200c00118809000008240260110f07018207101d49090142c40c240400d03161001c080b0394902c421111100107030840c55184120134450740085400100e5041403c0b40070706820006506a840b990040310a6952081e102040208a014040d0300cc0c051b4901000881d141d50041020954041d6005001649000d00c1e4014410317905080d248a1078007400402030142c0c146451381c000d5000c2d00f5503401c03d4000e03000004e848003442a54511445003441041d1840c4600e100540203000c24004d490300307021115a020410340c404204c0384030b1918510409001d003030100401050001e0b00d080c50350303010303034010449400703987c5a40712420301b00ca1150708610119a00c40d12280000d14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 381486070 1250 381484820 381484823
    0x6040b10091119020c10031a090c030901060f0b0901030905150c070b011e09090f02040e0a030905150304140a0f0b0402131505010c060e0307060c120e03031909 70
    0x514021028140d18840380203004000b0004010030034030f50070444142c0e640e2034044801a401005050840701003072007500300d44000d00c0700107901e02e80d000d43c0c440000d14541c0102d60076002c41002200f0000002c0c0e0074002e1100801503d010004000c0c10130008441ca8400d00102505060300d4140e5542004000c001a17114208010407843c040d05007140031030081d50100c1c1c03040d506145203500111b94440c0943c50a034143c5a101c8c2005000d9290150280c0508103001301036408060154030200942c6550146103040002d0314054800e04203203150103040903e45410040c01a80810141032200a80c07400f105d80042d0010b880341200c6181404407440c0c81c1d80d11000401d44113414510b1410005034000c41809244221b507070f20818070003024804111400c90076992040c0504141c00c000b6940503010441e401c42c0034a10119400105006641c6035902c0350b407040307500503500c050032000103621070a020744d249804007083c4104040384035900e503640806003006000c540391040e03203100400c7e607500c44108070303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 381487320 1250 381486070 381486089
    0x406051614060403080c03060d11030a2003010c0302271f0815040b0d1205040504060e01030b160507030e060d05070320090303030f060411040e09120a0206040b10 71
    0x1c0051039600c5460307910940d41203020864150102c0d6040304501d01341c82c810368002d42900c0460070941c0b5149039275040407000c2500f41c0690903807100410031400450301e08141e0411000403c15401c018542100d0708403100b14200351061240900d00e00e0705621988036101356007400440c5030707a50720003d0b05c82c00c070203000704e06c008402e0005c0d0351403140c02c0f0303000b035201d01e0481d0b12104050860310280000d80c1d0040b0701c5250302076150100c03100001c0580490a910725150302e4038508051321100414225981c50300580d071a1103d1f41c0c010030810030a400702a910035612102c0002d1812481c0018100d03015182c8010107003c04501441c5141d00c4413800e480078070646403014402820310440103401407100e27510000030040544808403040442008460241001400852860b44d4248550342000b02c00303010a980a0b0300c1301000481442d0f6000a480906981038040f107203030404044441c904000004101e0920034107104100109401152865210b40c125500f801551b4400301074031102c600703981003070404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 381488570 1250 381487320 381487343
    0x204110906040815060109120314040807090f1b05040b030603030d09032609030403150b03031210060912060e010e010218012d0c0c090908210c04060516 67
    0x404001426451401360300c80c244413952918001180c0154032809000049940d104c14100080d12038ac0c1d0f01226030010704402400d15803500b07081070400d02903520245e80551a100c41101f140b1452080b8405a140c03440010018400042c01411500aa206541e85503034084001346541d1014070855501101050080040604502d4013814010814401c0c80b4200030018507442c41c1070382005900d0003030392954002c0d0304003451551141c1d0340020180c1398000e1961142c0e1751481c9610200301901d446802c43d413004509141c011501c1582d08019407242d010408010010080c00764142d4800b000e00381c01c02c001092854a441040e4054200442c000740c6541c4009060700b22500000110122940309a070381e80c40600c11904040c590200548c404a950041019030300d0701c0c1400340c054648501e1080e000424155554a084000c942c441981921160000101019560000d14095219514003c2600381c0f5080070707800c5900c540118055103007070100024840603c003200103882c941c3c0a51000040e4036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 381489820 1250 381488570 381488579
    0xc0d06021206010309080f0d0608030d06080d0804080f07050c0a03140708030f030a0b010c15021201061706060d0207050f0a0501050601020601140906041b08070e01020705030a020411090604 83
    0x2580240701d0481000720322000701c0c0079503200c0d0088615040d0880d0849080075030210420b0b07800c3d400300250844031681d9032800245c9540c24005401c21982120000031410314116501d824030916010020801c4414020032002810708e02c1030f60301042c81c0c0244151905402e00d059881c19501828031507102c1000c4000008000007110501441c0360510280c840740d40e41c03054141e6a82c01500021080c40200b440080e170b0300300b000c2d444054450014074080000e01c01c03544428407071003a12060740030301c1a000550682029503060202c5d0040110b4a030182c983d00d40034052500c2240c014106500c540b000140c80410080d258040d035140a81200c1500d403c11a0440290ba607081442d1080f2815420704000076520b41c00850000d04139904080001c0c100960603081001c0d00700c00902c0c10350b200780e40701000c00504002c800409020299601d900b919420030003c060701c1071040b05a080d045620079002070000780c0700480c004e4540c07035050340c0101d0f1590810301e840506001e00d21515802c00d201040008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 381491070 1250 381489820 381489833
    0x40e0709092d0c1b29010602010b01050301181a1801052103070611130303030e0609121c020d0e1f1401030f030c0b10060201110405150c0c0d 62
    0xc1000c01e0400b4074001040b2507840d036206a4651070f00140108000440c495820080c608609800d50f10510940a05003072070216030412009081505101c604c134a401401150340912900142e12824240642075603d441042004032100b050341219031503da030f610b40d000140703045146440c040001c10304c140c0e84600d04003c2981c001d0034411284100081d01d2000308010540d5040080414190301640c5048200e803900005084200e401c641c1803e410000d44900c050316200c48005517100e940c01003149103803000601c2c5002809000f098030ba403c412001079004031100e048500e40401c0c01d00038801d000300011040000c1c000c0810419a1504005400c007880401042040c0d0002807200321001d15140f0040300d50840380a48a80e0400b0700c240750060011030107440080030746078400d20b481204460256100281c654013078802c0041c0766001481445141d40a000c0c0907900614100036600700707460140020351410700c0745608441c1c0fa0700015400300310070050010f405900b40241c410341c02c00700c0610b8100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 381492320 1250 381491070 381491111
    0xf05150a110715050c120705030f0307090b0301030c03050c01080f1f08030a091703070309030f06020d1b030b030c100e0315070c020406060509010c030806031005040b070206010f030305040e070909 86
    0x8400c5d078000c5013101c00100442c103040e104500c0d040380003141024207210001070540e201500f40810b0240b40760000900c4040d840046019621503800003240b2490742c900305103404008403903a8140200201080725810412610302c5d03000e5030040c2d0391020010038200f542d400700d1058000c00e400d03000c0080c0b05d4503466000b00c885011100782c568072085030350210500342e4030390248003801000920211810808500c040110700703000d90091400501d40300a10000000312242c000c440c440c00380c0c1074258141002d4061003003250010041d0098a4180003480000c0e80a08a03021079209008020040140540301009188441c640340c840000c2d2500340b90001030106081440f040388103600300780c000304000744607005031614030f40306071180c440700c0d021540c082d210000001c01d403036018490030342042000403090086600880c018803040c05c2138107010390020f0601307405030440c908a4030341400400020391320030300701d40480325103500445403030b1071b07030242210007002c10f42c80000024101800104925542101c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 381493570 1250 381492320 381492337
    0x40503031807151d0d0f020a0b04050d060903030222030c050103090b1311031204030b010f05060f0703030b0a0b120a0b010c030c0501240f05150a11071505 68
    0x900d668200018a0140e80c0c54440c011207000121001280c407825000b4a08030031003c0c8605840c2c03400c1c44101010503920954107100b5039421b00c011400310705604003960004094681880d4035403500b4100f10204900c00860040204070550b25410002814820740c10b4400c03282c2c00c020100035542000c540070a244143c1d000c19540d180c00703041b000a0319030003482001c4d080303944003000381e00e503aa80e1003401c0e070740103007404054a0180403e0801d40785590180400c41c0094420380ca415144c1c0d00714100070707600d2007058014410502c0e00c004248469503642c0241c5000769a03044400e640d03200345107001c401503d22070001a40154032040301084010681c80a0f111086188101c10745559174003c81506988035065018003041c805c00c01400820b200300e01002183e402407001003007500d0000b103424401900304a01e804544002d00090185002c40d1704410700400c400c03a903000c10002c180032002240d01c50503400905001709101100d01c4803c007845090005e100d9607034100c03003900103600b001e170003640b00c546d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 381494820 1250 381493570 381493591
    0xa0f030308011203090e060a0b04080102041e0e06061809010b0a1d010f0c061508010603020310290d060608010c11071503020705070e2a070b060906011704050303 71
    0x4141c00d00b91912020b0551381580c1c41c0748090b441c03d04000d4015070050401a08141542c1c00400d6078407070040148010800d030000140e9491900c1141c9441c2085005451084511040c013080014100080547c102004030f46081e42e0300351010a0300c92002041c614160883d0641c1e00008002c0703444009044080441d403038041c082001c60394110f000001101040f40424204140c50064a120714014500c040c440c400009041000000c2203440368000e0b480358400da034454806000b141000d008910704215106010b121013090300c0d03e40c10a5400380e600d50176000ca0450303151009581ca00220030403007074004000700155a1205038030750181a000da000c6020401000009120060008d4081c0c02c4480b0703410260801e0344600c00450103540404026a40c82c8100c60000c94000b04581410340034021151040f049103040d009a030848034003c0c031804048550500c05840800e02460342c1641c8003c040b01c643c6080d07520003005803071040240da484442000c01700104003c000d4008010b600841d81d021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 381496070 1250 381494820 381494837
    0x12080703030216050706210509072105010f050417180607170d0b040b0f0a090b0a08060f0702010c0807050d090602161109060402091f030b1002030315090603190609020a0f0303 77
    0x214001c288c2d00181c500c80712580c8442d1081103401a500d94403405000e856120800044c040d4485a00307507002841406c4a40340d07120b042c4410004201a02d0100824051009003007103145455a0505da440c40c185900917400000c0001c01c0020310303094001c0a000040109484445100d0040020501004201c0c022494250900340b00d141c00c40c514085158007d0003800d4580c00e201c8032201500c900000c3c40d4002d8500307100801c0311601070103014860080c0200301c100c40d14241200900f524009810301d4280301c41e038410300904c66405801c862183c42c41010126415009140c600020b1150b00300752410ba080c058541401c010748254441800032007150410f105032900c104100491080c811165030100080c0416a00100c0d403104030360180b03c0a00b000a0080c0003203003c82c43e40c0218542e00c9005800000070000401c0b64001980340c000c40548812045240c6500840d47c3d5a40441075001c1c080300255290080003050340003003031010b07030207446d441d0883d540e140144081e0109000450100b181030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 381497320 1250 381496070 381496127
    0xa0f290405011406040608071a07050109030f080f040c03330b010e04061409040c05090f0415060501390f0c0602030717030901090215040f12080703030216050706 71
    0x60003a50243c861050123440514070b40040c2c4c004d1074264015500304030300c1c00c3c041c0c0004614280304034040d0340e0082d1100d20480c040088000d100c52801003644081c82900424480410b0716031031001c0c2030341c0c0c0c40007002100c80110411840c1003490000e080369180aa020780828002c01030f00805c9051a0030f0300c0d116040c4081c1000c02007519602c0c00b03610000400e0f48050606494440d4400303070014010a02e541c040d50b1100701186c0481000c5515a065100100500c0200004826881c42c0707105a8001000310a007007000090050544145030741c000303086203010318440c40c43e065072040050309440f144a050751300752030840840c10b10464242d81c0d005080000280c11800807003158070241c0d00c10258042c03009613448d2961f083d00091f105040b190350310004040162601c1c01c1c911000c0e01203040894850b40750640a000d40301880d00400d00e03041d0038450b440c0000324907400740e0700030b01e0b8181800362303c41c8540314020071000400d82000c1c3c440c1c0301c4c44100040f0143c0114a80e014610034030080d89410046 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 381498570 1250 381497320 381497329
    0x260108060a020703050f04031a150f1003061d04031707050f1606140f06010518091e01120302070b04030206091212040b130501020a0f290405011406 65
    0x9224510580d00100c00081e108001e69005003152032007424903904000d030b064903031241c0341c0040d00111200040e818041c555002c0c030440c103030f6002400c900c3c0d44084038880400b041c54103002c80c1900b4001c290003403200d50268081d40240c1c5c00784c07060b0300c0300342c5035240c3d03034114242c14440c142c80c00c0c0c010a00c40c42c41c2c2116114030039135280c490b01c09038071050300c7c0210b004a0b0170081e51154503020201282c1c01074075030004915003d2030174071000d03861a461081c241031540380c101e280050106810f00c00100207507003088000d10744000e401002203490442e50340c0c46298560603010103d068015442d402d0b400030130340e250130901c2184128080d60855080390b0b118020100c003407040340406035000f0020f020007103040ca0800d010102c500705e07180503141071801c5121a0191500180c000000b0b0705004506034003101d0f480100b21004107000d1008011000b034540b124440d501c1000006880c8141d60301d00e8100501d1134298011301034510031880c10151500c3c0c00e00600900c201c040759034501600c503010502c1c6250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 381499820 1250 381498570 381498647
    0x60901030b1602030f0c06070207080610050405100503010203040b1009050103020d08070507210b0901020405060304120e030a030306080c240d060b04030819050304081b1606 76
    0x1448071451a203900c1c0d500114031064880d840300e1045102c20810202c15035581e20203840ea01498200070030301c5041622001e42443c2082d007210f1100e500001c10401e042145c65041400c03100b0030b450014154480d110030034801b4119400180d00b540c00002070008004996800921a200c0601a480100d032112400005c5d140e0a100c00703075015020f2444400800da8850003810401c2c1320700304882c0303d555030b203c02545200f440c0070050310700d81290f50148280031082c09003952200c144802180b0301410080001e000c4c0c0005070000e001c06001040340d510780340c010300c0700c5000e05c04c0080c12609041394924005004e01114080e42103e40526811a441c508100c0d00c00404036083c4039030031190203500041d003102900515440882183c960400007941000b0400078805180a2030403a03658100840041182c105204010000c0220810812010030142001e68545051a010b42d43c0c0501c00880c03c80d1030151460000c0a00e40104100000d0150700007054101d200c0c00340804400507011010032103030100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 381501070 1250 381499820 381499823
    0xc1406040203030f0a050c1e070603060506071103030403150b120606010e120705210114010605090f0112020315210c100908160602100e0a0f0303240e06090103 70
    0x140107000210300c00c01c510015100b111410711b09182418078040303c507454402c0d000c8a000e1400c544170038080d2a16001d01c070020207000e107070806020152a00001c02d055221343e600244c844689090404215903040c81214029a000000440440c1c40144141c0040c88180310140c0328003400725092041010100d496840783c0016141c50000c0d01c07112060011600d64000124260b00034491f010402c3d585403030748444901c219082d000c50008010f480300d801c4a0300110101110741412004110307055022045031030410041d1010440d0720008001a01e0402e94002e8184100380040204071301d1742800404141070440131a00d00302a9220400142465410328604900e150498000c01d8110300300051001d110300e0580c81d015280580e6001c101c1d05080c0346c050001001e04602408002c07859041000b418140400c02d0f0420000c50020000ca83d5141d82c188010880e60042400d441854083d500901d0401d01301e0f0307480340402550287d550700034003083c043e0f440c1c6a09410049040703030030400398a6050743e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 381502320 1250 381501070 381501073
    0xe010c02030c0d0c120f0203070608060d030311090a0b0702130209060d18060c050a0e0306070c060b0307031203090302060a150b03040816060c020c040c050d0b01020f07060c1406040203 81
    0x4001402400075085200c3e1042c0c49450b2200c0c0b00040d05030b201144107141c070b400b0303580740c500c80e996510425007424070691000c030410407a4001e00007181e940181014000d941410005941601081003882074050411402d80c8461060800030303491140380000d0016600c00ca441c0c804464440f0b4400040f0302071000708941020092040b0071403842c496103c4062200c0c10028002420304030b0b511042074901c40e00071200010b001090104115820488400500c3c10440241109207440324000300405a01d600142c036a03500d400010a11342c0741442880040c54025101d52214190800080d0240c407100108500621401c400149500340034460924204101c06244401615104c05180716420290040c0c500705030400c000310380c0014124413481c05a02c5104003151481280c100070381428641e07984135001d80e00300f0103030341c4000344d00204440070058000000a10400032900403031400c003555034003128600c03c541d80421036a4101c1884540240304007010f100c00300404400c00e842c1d14080d13a009416 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 381503570 1250 381502320 381502333
    0x90302190b09101101150f0f080c01050a181e090506061207021f0f0506030a0203071a04090f0e010b01090b0a030504030516030e031002090108160203040b03010e070e010c0203 77
    0x180780c140c180d4a00c400b03051500c0d81d05001c14444c004d08480c48000051501d55100700e04109081445e211400201f00307040002e4140703450500000d03101c1066000c42c50420100040320600c1c41d0180541c1d00d03889181d5000007090503100c947e400e141445242220404c0f02c0f00c81d00001c0ca141443c044e40d840b509001d402c59041505c10007622040744c80140862055000c0d0842004840c88200488006030740182804504000c40312490f82c01c5400150a480c0aa0045d240b1840941c400281400490b000c4128078402c01e50403000484081c004c540000c0011400d0080326073306203e49400c0400d50b107120000800c40015220300561352034020703100d20400c026080c080301d00c1c8680281c1c00158098000d0822034904080b520a818400309090382c02c03004141c640954091a081c108014426020401c9045141c0686400064400300004003200410150603445042491003441650020b013a1141c00980301e58441105144444045803d01d00143d11011512980e40c0310707002c121291034001d40604107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 381504820 1250 381503570 381503587
    0x304030212071806061d0607120509040c02060406060b0c0703120e060705030316090807030213090501050906040b280b04110a09060905060a0801050904150903090302190b 75
    0x1500481c8040d03150715004225001510428100d10851254400381c40024400c0c1042405060100b100c2d9982000340c60f09103080000e03072568022242c1d1143c0101000c40c00341400d49003250144511603a554000b420f225003080b1032a0001640350140303210f203105218058440c0e00300b50f40740c028085135001541c8001000c02c0800d00c2c140d115400c07504546845810b1014500100324940d0100c1402c482c5030340008104580345803070382e100e11100c0c0005c1c40c100303200c07515011120340d990f1810f0102038030681400c10091004409030740704207803003036220000744860710b00840115141c0b10219000d5440030082800a01d03010146002c0e002040f03d50342d41142d620303802d21007400007040010a4680c1055036101c50000d103000c110301801109013659034489511341840d800610a40701c60740440d02541086c404032100d9a040019141543c4058421859a40e21420190b16040104104000300c074036209007070301072561080090042e41d0081d900078521a000f01d400308030103003440c858180401e03000d114100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 381506070 1250 381504820 381504829
    0x50108061308030a0902190e060a291c050412020604150e0a05011109031b0904020f1f020304061b030207060f0c060e0c1005120103030320070b1f030503040302 70
    0x180c200d180c2504c000f8096074240d0103c3d1802030390100113034060a20182c00c10200500c1181389512901c1910001034052a01207880c42d0709507000010500c202c0300c0c009c80c10f44152114282d5840c000340c0315005842d013212640c901e0081100343e9080c1e41c201c4040002040041c00003420601541d0b100c95800000410034912034002d10308a1090b0046004e04120a400b0580900903032001e01d0f80622030759a240041d204140c540710f50380b007801300085030742801d0140d155140010307141e1107601914581010030200c00042d450704180c0c00c080200501c0c0000e200c00a40e07000010300142d81564130f9218a480c450000c0c044400b076132031402801079202c09000c1c80701511448259028038820300f020100d4400716a5400280e400c840c141d0240d03907200c025010303240c0c42c0411502103908041d041c40c510b040090100e034425054140800782c00e054031021090720302010f81e004460010552a01146c8a4409103404012100d05130781004041030200d08001c81c500c80494410122544840210301d0107184d5400d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 381507320 1250 381506070 381506077
    0xa0e040c090b0a0824150a030603080408011410120f030201021c150909080a03051302090415050c0423130908042309010b090f0a090b0301050108061308 67
    0xc02003044074100015004600c03400381825403402d885564031071800032040140c3c0307504042c1c203191044003051880720391744540c600a65403541d403030302550f51003810a00603000f40c1055400240520000070740060300c00c1e4190b001d85109000360001704000c0d00c0f01c1407101130541d0f09000745080c00a00c8625500001e90f805540350b000b074403d00026080c10308000400c1d030918401c005800f4070030b071070341e02e41d59001564500302c034050100820100000e04454491141c14041c0e0201d010500d0341c1c5d88081203e0392000441c1442c40c6da401000c0003100d02c0c1c80e02d001c01101c002e81d840620043c0c00d040c003140742c1c0c42034503040c0c400355003162044400c00c140701b02d42a84104002d55226030400817983c003403000101c00380501003099009600c0241e0304e614101d054110b402801d10998400c0004007148501c03a510070a0303041c111214000e483c0d881d40540b8001900d03804890120034ac2c0040d0b071312400640304000d6000380701c440c4002c4000b004641c1eaa841416211034046400000c040c440c4101400000c070810041c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 381508570 1250 381507320 381507341
    0x50c010c110d06060e0c070302060a15150504030c06051216050d0b0a0302030615100c0209010b030601030e06012606010b030711070b0403060f0f0c0905040507111209010201110a0e04 80
    0x208045a40c1c071014015175030306a500c030000f000001280c20506404009070368001107240000c0100c002442100c48080d803050098a1a030031044800c03020307840c441d8054601450304a80388400c440d40d28000604075030300c000340020b20254440000303085020f041e4208548111991a6103250034890400c20009003c003284039030f03000929150220241c3c404114603441001103030010000308103010304000d00380c10f4100141c410001208200030060300c540041a045070f94103500305407684c41d90401038015061500583d0803501c240d0700001649010060480c03000ea40c40711302050b00c040715161040e100c00c002d00884075884401c001081c3d0b002e02c2209901500360882041d249600d88810321090f0952042d402070790400e4541080c1e0800d1500ca12400c0e4054202e20f03001c1000020040c4090b107058080c5c81014031a41d923520014002c940502c0450550103522029030b003e010120446407425000410101c0c019071030240640a1015000111481c1a00a44841c40400e007003604000c0544120300340c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 381509820 1250 381508570 381508583
    0xc070501080105060c1f3201050d12050d3206040c020c06030604110705010207030e0d030f080402030c04090c09050c12010918081b0f0105010b09010804021f0804050c010c110d 77
    0x290000c0b0102080c11800c4000b03620700082c0d80324074212140e5407240d20107070030544c0b24405101c0a000016528400040052f045042403925007458071100001809070103054000800d5284e00300041d2020400004c4c030340766980c50f082c0b081d03884220030702c4100e40840e00c3c988096807059500c010b0380c0c0742c10f01c05154002401407000c6107403d00007803c8143c5403c0b0880c220f0700e40e034000c1010001c0681154404010350010340c2c40c0400001c01e80c034010015885000c0c038100788004080030cd001d40d1001c0c8090b5007607a802600500982600d807038030b011048418415021100d1409000c1240c102085003251380d1480d0402c103200190b420b000d83c001c020030808425003c111101d440510000d040e100240502c2544050b0455209581d0b130010b500300b00092020050b80d9140400500c034009482d0203a4080303032420301c1c0005071a030341c501c00300303041c4103080f0b01c1080109a14444411266480450f03903204070b22520a031003504002500544450145000040181d9520341000405007000340607d500ca80c000e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 381511070 1250 381509820 381509831
    0x3060306180b0903210c0904021b011b090e151504170a02090f0702210301090b120601120203120408010510060c0302073809190308040b07080c030c070501080105060c1f 74
    0x40008c089a000340740420844181c104014108030080c03041540304000c55600d0f000c000c0004078001d11a0b04c45010f4041804912070108011003c440f1503903c00d4000509802c071003c8001c114840301c1e80051160b82864909440c9200c0e000e03002180311080c642d405810405245c0b1200c00d480c841040c010301c1c103001c600c84d11152041c0f890b80403800300c0442d1b210031b0b4003036030700c0d41841d148070b003521410b450040c000c484000c07008445800008042d030459544402c01a096031117480040e051400c101f41e0183c0700700e004180403d103008198408c42c0200001400c01691030b544200039200c0303503007115015000d40c2007843c0410140864044482d041020f1404060a90f800d8142070840000d01e50003460900001064a07803050401002c0c4500c4005691003c0f9512461940d80d81c2c13051203140075103003e41d500865060b007001a0241a143c8c42c3d0f1110741560384038511883c80035929029841403500080d425030000900d8103000085881c5e6030709000191140140d1700780a9082c802a42000c0d510041e6200f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 381512320 1250 381511070 381511087
    0x307030c02010c2010050712051602040203090c01032009130f181b051e03011103040809180f0406051008160e07050307020304030308060103060306180b0903210c 71
    0x14078001d07030b24a4045240821028130611000440e03403964001400005c00c50503010941d600c1c0c00b01c010568078644640e480d9595410700c2003800d0205c4000350043e001006000b2241e80c04524040c0141003a0303810000c06801e285903091410143c1940302c002403082240607d141003d0680b407251015060001c00ca000c29804085c0441c1c1000d44008114032002600d001007040c0e43c1c01c0d41601d010a600c00250f031904001c00940d80c00002d580725002110000f5210220361420b401030b07030a440030b05019580301e14182c14050541da000e4004144a410a58110b200c1c62001c0d003500360080185038a040c59907519542c40c0c100510000d00b01d540300e05119680040c541c48100819045541c980002888a900d0301003000110300b00a010300003030220520803c425150f00009071000c0326003500c0c0094868440ca80103034000d24254001400345403d00f040554140c00b0303950102d12440c8201607400e030f40d50791045065224091000e00f03c1c0014469645440003821003600c1a4014440840451420050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 381513570 1250 381512320 381512333
    0x4060b040b030c120c1c0506010f23270402180405090a020306070f090e0106051606060b13060f020c1c0203031902061f0b31230607050307030c02010c 66
    0x4a5170b2014003040041d001245d101d400b8080c1d61140b19030b86e41801581810b00001e04264902d027119410821210301c900381c1c40c2d841d61004100301c02031494503035807400c0560701d209440e10800388041010502d000c3c9000503080a1084480f613078410a10301d00d00c1c0c0c0e400410440988000341c200a024418101c9010240e40c00b440510301801c941d89072010186210720700680311002c580d00c1084840c840e640100541900070040b61288042090070206400480ca810781c0200056040f164032000c02080e00c2d1800103800c01c07414150b40140d103800c03a1341315002c0c904990350000041c42c42d4100c3d06182030103201c040b08040c80f003c1c5901c001d0070780341080242c01c01e007111040c84c07a0341e070001070b84540b040c021201552160408480c10000304038400c24102800c0c94003074800c0d00001c4c0c03840c000340418407035000400e40c0c07862800704503070400c0c0031029512a182c0c2d0700c40514064130700481c0000c1110300811f140120440320255400301c080e50a01ca0107071019101c0c00300c1801c05034142308205030300c0070004a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 381514820 1250 381513570 381513607
    0x914010804110310241d0c0d180c090506031f0605030303041b0e0c03040b070e09090d030c0f0c08070606180f0f1e0b0609030a0305120604060b040b030c 67
    0x1d40130400500d003544d0145091800b00041440f14240303d07002014018103e1070492044089402111100d07191545e5080300402e00c200f124a810107460504085840c0b039214004002c0180506640710841c0e07200c011480c101c910580b01603906a10010000c000307001051001600c0044031540080d540d030765903021078150307070046608a941c1503445c0400c201100020305c64a0150041100b102c59624001000c101d140c88090030140101c5042e60000f00098407440d002d0650304009007010740d084c01e010b112035a5513040080000f0219051607442030341329214003003910854046682e01000060580c8545a40360700079401a0341682c0c86e518045690f6000305001c4c11402440c01f000140c90707202031816003c851851046401c042c0c20034009480c0c03207041d00d06038040824049000522800808005441440313940c0f03a50f03800d07016619491080c19003040260a4032408500b52000e503039662401c000454416008036000420240400c0c0039240c0ca4078003850340040e05065552429061100a042c500c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 381516070 1250 381514820 381514843
    0xc19030603150903020601060c0219090c0809190609050102040e0709031b0b03010506030709321c030f050705030417011503081801021914070609140108041103 70
    0x340c903800c0c01c004016000001c000c5059080348204840801994025250740044c4522403c00130740002c0c200c259a070701045031000f00501100c0b4a4099941e200302809444458802400302d22104001000071901040340c4103408500303500b120114119070750b040000c1004e0402980d0030f650074400071030f9000d8010407541c0100100e40302c944d200c03031440c03030311900340454141d0869083c0f00310a0f00f00008603001c020f0301d0542d2421542a5200d540319a401c44a800d119403042c2c01c03009076075851030418000031209071980180c02455000d40b071000801c3c000c0c0799607020884000100031402d120080ba20031045c1c0c2802c8007d61800074a40000f58651914640103600510701c04140240305048044007440790b406024040d44101c0c00d55031442c1c40c0d800c228050021141e540d0f048180d19203c035a03200340508904e00c07144001c1003030420800e01f410204880d2000109201c2d00c10107102098031805813454004031140020000060b4007000011906e8210180049450300c0030f540b2000e5065609201180c10003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 381517320 1250 381516070 381516077
    0x91e0c02070302030601211509020306040602040906060302090913051c02070f05040b030c010516170c0c03120a0c0c171036081204050102030105040f06120b0c19 71
    0x403402c0d070041608051040c4c0c0080018072028070a4203190032a0503d903404a6088100341503000780707500390400601540c080c000e42c5401354100b04810000141e01030000d40c1c2c184e820800a131501c940044c3c00300c0c0304111a031035000483e040058802c00c032116040d81c8580c0700d00269001c006944800201c0c400c1c105900f01e0158101c00410301081c0000b0031100001c0c10201c90a102c0c0245c10b40100b525040f40d044503904000300051056414000d0701424204582c2c41034040c2c148440554081200c1e405c0031061104038024140c541c041481c1c00611100f031820507507030a902d0f00501620075103030b40c00404030860300d2010f00500000c600890f40e8030145025500703400f80c100c0c0b10710b4602e000200d40d5010655220402d414692111102080c1c0740500910000700007121006000c0c2000e4a5501940701801040508081040204003064010354100ea000b55810301c4a8810314000d40260355030750080e41210810104401c01242d0500d50036030f003000703820209a14121100b00d0350501c02d800c41540a003c0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 381518570 1250 381517320 381517333
    0x70807021f0305240d03030b0a0303050c06090d090b031b0a1e08070212030c09060f040305060703060b090f0d0b01120b01050904030e130209030105010f170f030301091e0c02 76
    0x2031607094042e80740d1207400c1c1c0c00c00c03420102084c810301d09142e81e80d4181c503018510030540c603c1094000c3c0d12456620800404e03090019079031f031500074802d80c810341c10600390b07000b007502080b408840002c89103e0404640c403603c144605100039000d403900000c1c00329a510035000c8625400d41500d00c0101206545a502d102e01d0b840390f0341d8080f8946034006103000400226100300003589a0100b21010300c04c440781c1e00071384c0c0c94a41c500364130316034014410300b05e40c056800a0411600345112000b0000c9038440c0c0281d40d16a42c81c080d054003100c88a1003142d22103002000007040310719010b90807200449000348101b200c6005078690b0003400600340c002504041010b50502c00380911144814010705088030702e0003a070314255400403c0d03000d404001034080e0522070f8920820035060b030103440c641040500204040d680d40d85444c1e6102d000341c40342030407058828075000c0c02001c010a2010115145c1d60040d4510303443e1200550051151262000e41103115400075001030680340103440081170a40d000340b11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 381519820 1250 381518570 381518629
    0x40603020c0c0907080a0906060f06020604050d08011202061c0e06010504110705031b070e04120801090c08220f0b1510090303121e0504060b0f01080c07080702 70
    0x1d4000c04440b410711440b403020801c028035500c885544c0e4400000c12001c81e440200b882c181000e810070f03030000094031547c00d80110f0410350004005200320b001e00704941041500c054192901c0c2003e000b680307000700c2481c80715805810030b540103203d140c0148c0c1d00c412050224000d0038040b10740b80c3c081e00111703402100c01007055107064050a180b100440400c140f801c0c12030383c1c801e270f030b00d00c00c1800c08015454110400c0545600900c2181d006240704e0010b034180e071509140000611000358122804100c0300000852000618801d40980da50a602c070300403e81c036400fa4620f90f20b5800c0d40021903c411054407103000500d40d10f11910820312415000e02d541c100340040607062080c940c0740c42e001d0441c1d8000713524650390012440c001c40e5014200510142070741d00042c1c01030500480c50bc0d050380e0300c83d0034800340035180754802d40c401c6000f1001040b041e841c08041110910010f50402d000620b000c01240c030141c2040001c00381584500146071810480307501080c003003101490038402ca110249030316030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 381521070 1250 381519820 381519823
    0x110613030f0504060c20030303100614030103081210090204080a0b011a0f0307020109230d0f0e0111010f14040c24120f060f1e0f2702040603020c 64
    0x840200c003504109051900700b13900149514154100034090000100d2204805d4103a0400c10b111440040c098968038640042c05400210702482820002204d55281443c00c40340001924144d0354882d01d00361800160900e90144d010015264801031a103d60300060009100c1c030051004106a10140c68040d019042c546c0d01c06005a01c4410320440c0304080751180c400e1601280e0750000400c100390349030344425000b01c2c01441ca090f402003031021100d08003510015440300c0495001102c6c000c41d5910211100c04641640e085031403500480c4042811101c81c0d03000e2103444c0c0d13082c1c2001d40000b07080d0f4001a54a4240c905100c044010380486138103202c248070885401e080a4480c8a12040704100982d114030001c6014420402c01c001c9000010801e2180c0c9400c8031243c00416070302440301070740b9040d0500c02d401403442004555801c58501003020072a0340260740441304048405504a0b1a280b1654a010308034840c1005000162840000c0e90300248068001340030b19540040c0c54124021456 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 381522320 1250 381521070 381521087
    0x150201090c0b0c030f071a0f06120a02030303150d06020f2230050105010303050c012307050a110d08010f050f1012020d020c01270b0601030c11061303 66
    0x702c00e85010448020024000800c40f1050041c44494558503412420300d06810b0381c0c00d0150741e00c880c4100c800c0c01030800d8804a103902694045605000543c84159000d9072400c01c040001d40540041c0300107084080704520070302d8001009171030010b000000c1c0c4d44000c100d900c0340150403410b003804a00c8560880d41c4800302b100b4603400b0140301d120f441c1030176008440f41410780454035101c2271442030740c0b10000e21805080c8401c1c0e8084024485540c4070320340a08240c105100c0300c1419840e0010700761200148500880c21140b009401d0401c80c1c0f00e441084406a10003c96001400b42082910300451400c204803040b587e00e03581c414450354141b0f00c000b01c403003449500c4140f00b5071610400342040e64034001188820b00440c20807085c00e00c0c030f042040000c2d01408070b03981521071002c140801d5207401074010008103440ea8043c103d40b0b829641c40d444c20150072b44000740a01002d4130004100394000e501218a01c00075081141c41a6081115580303050f00440d601c10f0900781304800c50702010381003182c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 381523570 1250 381522320 381522329
    0xf010615050a02060103060b130c03141003020a0b090402070c030c0302150a020c040b120a030306140604080d05130f1203080106050a141e210105030601050906010c020a150201090c 79
    0x4289050100c050080d03030303284103000142070223684510f05500c1d5901c68000e54211120714074203003d0801180c8019001340303200403401129190721000030f0800aa80f0280500b687e500130b2052a85a041c0031002c0496040403a0080d0002d6080154101041c0f01c403031000010b51103036001150140c1948103019000c48803040c0b00000c04d1003442650101398010070301411548050780c00044081121000440c07404410010035034900900d11940d0501d41d150304240d05441c007506095030314100b12401d0025074810b03403148028507001410340e5540f06101b80300508403400758044c14040c1c0d903112844000b0f4035049a1050030380a240b810420201600841c82a0040c007450030080c2c2008400311000c0c0142001d0303401316401c081d0001e00c074000c02ca41c0381e61400b0515140700c034041e00c88000c82d01029142e18124031004640410000000380c070302d00002c145050b00c9000d0000e00164031080015515249221802c0307902c401c0c13400010030100c0345d190b201c4030240d4007603001060045884c00d102b2450155a040b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 381524820 1250 381523570 381523577
    0x4080f0708030415020304110409020112050133020c01230a091d0f150103060305011821120e010e0f2a030706080c040e0412031a011403180f010615 65
    0x204004100361203075108c9282010380c0c000c14110302520040760381992012690034150304e41000890044808989540c0c60030354500e034800d60080142c1c2c4906400d01441503540168080740c1130001c654400e41c0c6504200701103034401c54000c00186100c0e030064114603000c1c00055070300c400030072014610000d01c05800800800c1a01242051504500741c102c00515006c1b0411079048001c40692007980542c00554019008100c0d200359020b0001a0b0b508a0005603031407082143d20303c40c61a10130311103559441050300c459904200d58081d203400380c0a00440d40d070a0303540c0c484c40c01890103001d02420710400d003440c3c0600203544a070505400e8032040c030b948900800d4416400d01c03140391400a00a000d90b909810405081c0d540d11059407007900c1141c102101403600001070104210180d0902518202c45407018008484024000d8a1141b851003007140003030814103d8601400d02c100046420443d5080e001864055500c8201d1405002c980d140486070340d61001042580310080074400d0f160620700c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 381526070 1250 381524820 381524827
    0xd0c09090e070302040c0c08070f050607050f09040c170901050a1b05180a030c0e040308151c060b032b0201060602100e0118081c020f070b04080f070803041502 70
    0xe42d6640701c141c04000d001d241d03249280110340e401546041e0b1081e038400c0400350b98048034a0151503064a105003100c00e0322a2401003068140103c043c0ca020182810080381401003c10070480a0004030780a03d041c801c003884c134200074080645485100b003910038001b05260400346a5102119140e0046002040e4030428480460740d1000c01c40e4280c68210242c21041200b0000065140c1101d9000410b46418140001038990b4035400f103174403e41c0203880340ca085956860744800300200340c40c25160300442810b88405a1000309607a0b4030260b0268000003035082c61480460319110000054504a620001d4910940000104262074042c1d07a44004d0006a14108010303558000b120755a02c05151100b802c4070580000358080040b40008215902110741c82d41840700c80c80d417003180d021000c0340509030a0003001029008944204a10b00700280c5010415200ca501403a40940300310740e500f02c1000200b150898001c05401154000c140c0c4d56034909062400c82d81c0d102c00301410001160050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 381527320 1250 381526070 381526091
    0x3060a0b0604060e0a0b030403080108010c02070501080f07210b030c06041d0901020d1805011508030409020c0f0d030221040c050607020402161101090503150412090b0d0c0909 77
    0xd030a42d803ca0700c0c141000800c0f5451600020301c072055a800030b80000b8404810001810b61001016040750815070007081842507400003243c40e4905030080300d01250600e4003050381c55000180496002c8401c2c03505c0c818440e812501136007594114803076120030b6510b0b2042c4110380e140502003d4407a0b00101c0b03030246400e1400b0030131000400182217050110040b00c001075110142901181c43c1e0040c6908104030100020840a2800440c1882500c06600c4c2051f102d0044800a0303185080c1da41c01001141400c0c6071110f00700c041e502c0340c41c404859026082800341c4c001c004010341c9000099a48015031a89201344504980d50100c2c00e44400c1540d0708024000481d8107220100c0c00d440c0141c45455860743c0724000b01d400703440b510001d404d00518001c0304105125281000034900e180c00da8030780802c20354504c01c050b0394841d0041844a02c44000c0c021030000780c40008004408c3c5810f0a0080c000e69649004207029000365003001d02c1c1c16122101e03220301c84e40c8054414054510031f10708000d1000c40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 381528570 1250 381527320 381527329
    0x908061501050309030f0408160806090a080901020c270708150f01031415040b0102011a060304030c0b0903070b0c0f12100f1e0803090102031204020112140603060a0b 73
    0x4803518107001000010420001061044486031003a400c107035581d41c0c0d66920803981c0c0700f0701c0c0c50400a842242403004100c14802140d100d0181c142c05004000c0c800480e11918003582c0503d03030190640c410084561030548988580f508030a0104221039969100f030b010403804074000804090800c100d0008002c00d032010809200d4880d0740c01c0d07650b0540e514029005a00a143c000c005001562840042082d4080c900407502803003801a00e007408200110741c016401d075004403a0007810384641d03079464021030070000c1c082c40c3e00a00031302e08104003c2290b01e0b034880f03980068440c180181c0001074035100380460b0b8201c054001e0303400030002c1c0c6003850aa103002e140d0b0041c0c000e041000404400030620202030b03484294050054003a000303440c40d41d60030500340c0c3c020000b8103100144005200004071050b012081d01c0800c0030603000345150003448002d04529640051080f41441000e010300c1340380381458401c0074000c3e4001410303c105410b08000305860520300800500301507040c2030500f8501d864 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 381529820 1250 381528570 381528601
    0x3021009290418230c1b0109122703080a050310050301020d0209010801091a2403070302030402040b0f03070b16021c12170118090b01060906090806 65
    0x611007015a110100e803980c1a0688140d9000703560000040d41c400c4610a070700c0c0d1221090002c800c000b03080740440c0800803c0040c1e070880702e1000310fa10038401c0080e800c1505042c1045a6452000000c41001581e240c004000c0b00740c000d04000f41580440c0d8a900c00014941e101c6808045401c86070180355aa88451500c03894901c2c000300900400030a45c0c0e440502c88503000b0340700040003035450700c0030a01468025086042c0c0d081c00180e283c07000203400c03481032041c45642d40d00f00c2c0c40a110403a0080a001c5000c4100c03119482455100001c01c103104091006540100541d0340c0142c0c2d2820980100410368103a030350107910495031682d4484440d5000588003080300c80700350103070391a0208562101102040c140300650401c01c0320306941c07000300101036640a45481404a24042e01c0d100400b00d4918442c241d6001e19904071f0001807048448505034a09059150040811808115541d04298807800c0c1c0c400c0c400301c0c25601c000e111068005210402424815004101324500004c000c500400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 381531070 1250 381529820 381529859
    0x2701051c020a0e0a0c030506030c040b130f02030103110f031c0e03060415150f0303030b0604050409050c03010501150912030903020a0303082403060619120b0103021009 74
    0xd2110840421040000350100c01098008250016280e034030040c2c0d15000c1c3c03080f91071085080c90808150403841c0603214880c0201005002083c1040c5010705000080100002040d40f1100c0504014050501d900410641c840741d054003680300c0d4554076040b060545250b150501c501c088004610050318002258032210362132500b449502818041c00380c40c2401d21602c602d426008031004c00040c0001c42c0c102c40801d00043c0410442d03407422720300301d141151041c000e0f6030040b10415001c1010a100360840c02181d50002c00352460035680c1d40000301202c12000c0c0c1203031582c1080c3c804d084185401e01c1440d005181030840fa00420031030440003881c510450040c00212500c2141e1841854401d0942e01d0182d07a000d41842442a280c0c14083c000c40c100320b550206200040c00b031405441881210340c1541007024009100585404041007003195074155180d8501c2c240020000d000722114400c031071914003c072511071040d419401480320b00410700d112a1f0500c24540b074200500c44103421030140c401d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 381532320 1250 381531070 381531079
    0x2120f0901120b030318090106030501120605090705090a09020f0103061214070b030c030108010605060a050324100302040614031303080901090609060c0e090705030705070c03050a05060105270105 86
    0x10b46081180010514002c02c01d805200106900200b2401114186803154003250089503d82e41d5160480aa039402d00944900b44282da00c07a5000880076001990401d07000310595800355110b10109600101c2100c3e1060050344070070b0708005500303140481c482c5e442e0081c070301800320a08202103040c6081d6402001400c8250560f1a000c607030a05010f0700014040714811140c0da403e0015980d070043d08203000c0c00d1007030351900340001210724113401150500d00c52901c1e01400c40c0d456500114001d203602c101c40101d0860141a010b840d80c60056001080515840c016181c9040110051924000c24800c12060100304180300818000c124504103082c1c0c540f410310300f280d80f03014295014007590700380209042d0a005440c4100305a5801c080d142120316038a2004c0aa1f4000400000c00c105450790800325a0400c0490341e068030a0005221540c0038020792000d090b0b0f241c0e14603180880f58442a501608440018003031450f20400308040f1024044040c0302d101014260250105030601c03409108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 381533570 1250 381532320 381532337
    0x70c0b13030816090605070501090b040308010503120901210e120a0e01030605030a020405090a061503060b042c030f040803040e07021605130e0303190e0d0c2603070c0302120f0901 79
    0x8c11a023508004469a0304c103141c40710a0030649400b82018800f8040e452090007240d08007040304d10300006850901005070750350008681000303042c03104400300e48505140c05803102c00300014107004008000e415541080c0079951500c2c030203402040c40d145044060f04143c2000810080707075400144652150340c0407540018640c5442e8140c61515001c03820040c03115082449004511140e009120100c038040d5006020700c000c12008c0004840001c0c41c01880043c0c1d102140305405401d030318419040030080c6c2186c3c6400c501c0c1c4895922900075601064180d403000400344040070244003120f8004403640020518203803030380d21542c50700312140501c50107400300e18407142a60340141c000b00400643d20055990760305182010490360390079034001b0504e0390305001c07020504900c00251048500c40c00d645070021007070320b0b07511010f00c03240d20954000d00d200104c2c080720048299000840c0500442e44507a100c03581c080c034019040100c40400c10503480c03400e10003400403401c1181110b035401000d01c0c04005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 381534820 1250 381533570 381533573
    0x50d2007090f0b0a03060c030b0105070201121d10021305030d02030414010315060c02042405091503030a02070614130605032a0d0605061908070c0b1303081609060507 73
    0x10042d40400c683c0c08813040c0c00000a101c001e901040d85500f10765000c1c0001d91009005480c0e500c92002d00a00081c0c001c0d910b5040c6940d00e07403104651603840b49400118941c8010302628140b014481d5400765640016104090121100390800903c0150080d2100000d4020065141e00652080e04035210083c1810072040c0e1103903118000441c1e080100130300f82c03501c40c1c1e0300914034111030208034080e51500c0403492441c280c200440c1c402c0c1e51002c4254070040c0c2000b05004107070102074040c890302c240803880881e842d5001e0001e800d001d15950300824095181000003001803841c0d0801c000b4482e02088001428509102c0c1001030b41d0440c14110b550fa1120910150311042c40d106240c4840030400507a04091a100f0040502c10035030141807102a03102c808001c01d500ca1012440061340a18a5400b03c00740030328007060f4010410706110003401e44c681c030750a04a0100701c0e00042c103450884404801c168114100e6504652549a0001003011401e0050030041050241d6401d02801040110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 381536070 1250 381534820 381534851
    0x1c060515030a1401090516020a02060d0c03020f1b1209030c040b0105090312090f180601032d02121e01050f03071d01080c060705060a0f020f07050d200709 68
    0x241c2421802c542e1004a60756078080800403c1d007503921842080040705a0021288001941603840745c00800bc20b20741105150301c00000d1585800b80011325800780803070a03200360030601a0035141c90b012544103806402d0034619041c0304401c1c00c2c0a036041014404070b501d6440000310390405113803c1d10f000034000400c81c01600c460041c48032195251180318820700308066001c000e44200c00059581090840c4e221040100d44d030304145240070881c2c00d290004401d13600c42d4224180701c490384c00030030a000c2e0304900b6800c20203001c0c6030b00c8201c07a034000500098199a4408141d4030004055520f5240900200c16590040041c4038a511444808194030515541407044000034000c03502110300800c090105800c4002d003d10481c00c042c0521904602d00f030800500b116406076000300a40030b180c1c1c807a04410010300541c20700340213070f550901104804150300310050083e94000d07001040301d03003000031005150221124003501b04801d8224210012078000032140103072240b11401080b03c2d41544800b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 381537320 1250 381536070 381536081
    0xf021204050d24090b0c0702330c0102040311010e18091204060903020a17071703040b04080a020a0906151b021f09060f090308090a0801060603021c060515030a 70
    0xc82101d101c1900711842107511340e104211562040c2e00660b17165592102481150017281d10203508030071a04081038203da240d924030000d140c50402d8110101c41c50800440403a00b10201000c01c80e90300060034000d01960460300c0400c0403092a11042025101d000704105081d01001c000c8240104004a8910030041c010071011b06000b030407035520303a581c5080060035078643e440140d00a004500f800704d010000c2100d00c1107070101901c003d100140c501800d088080c0440031402541c0d004c140004601e44001300014002008541c0060107a031089004000c512103007580f240580c107152040404c044801946820a030074000d00700f003070810034030240e032203581c10350403800035800f6070040014a0a00c00011001d00703940c40507654411401d8a43c2c00c1920b08000403084000490001c200030000600402c0c02044004405881c50480305d17510ba80050a4030700da90010008290040380f541403203180c0701202c1040c0031140c4014040c4615060100700f00400d16440d200c881c0c48004005a1040c040d500701 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 381538570 1250 381537320 381537353
    0xf062707170109020a150912050f030307090e0603010c02060601030c0e090a140a05071407150f020306040c1809020906070b07020c040b0d031e09050406030c05010f021204050d 77
    0xc08502105003110300910f4100d40480c426840d01c44045412016800800d83c40d20142d1600d4125908000c0c08040420902c1004c54040c0f00340e420704141034800703102460152405850304035149040016804c1c2190004142500030b82c075044034002550b5001401c190040000e007000500f0308085d0000f182d02c9401c3c0b150b0b46802010b0603092181e5003189612081e0241ca103010000091b0b01d51024020a0301c90942c0c24800181142c1142c842e500c616500500301c1c1c501c80c004600b107004070700307092900303462429200e1100103601004000d9a420680569404000d01d480c10183e002010f40c00d0b200e84034035030700800c14442c2e0301103403041c15604c800046954035600410502c4640c03801003402551904c040000300e001d18104111860582005082014410f0b4551900304000381080e058400c0c20103122092010403580340c1d00010107448a200301d4014600032101100d0b414280000503200c1c4020380042011540400c050070001c100ba0402d81d02903807401c440206180340c16042128482205800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 381539820 1250 381538570 381538589
    0x8250815040f0207080a080c1201031518050105100801140f09070b072004050105060307030b01020106122603090a080a02070b2d04050d0204050406180308090f062707 73
    0x40d20400d204100006c1c060320362107591031140654410b44115114062043e4008498480c3c200500005108860341d400c1c0031400d20700000c018024a00c02d0010480c002e0080c0d03100e940d18000e00c8849080134100f01c1c06403905000901920303000008040000c80010711f000c1030700705040c021681c84107050100d6002000100c40d05d68881080d0b0400502da00303c000492801d03e4941c4d1030401050909000310b5040303960040c2414107582c0c81c45400d8010b40300c0071040380e0465603101030101d405c051102994900034020003c0b046207012101c41644030160440e15142150400c2c01000742803000090b840611315400005c141e150071086e101a45011f6403900a5002428081401d1026003280c0c603200c400c410b118000341c84407120000c06149640300e0b0740141a00005003001d404c0c094207244d000542c100c0d22800c40051078840502005440710b042507411000a011001481040402000f800c034840c1d0748072014004904100c410303a94081d0510b0744138030301000c50f191020010352060182d580141904a07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 381541070 1250 381539820 381539827
    0xf0a1b0f050303010f05040606090b030403170702030c0105100f031401020f0a03090519031d13050a1b0315032003070602070503010c21020c0a050d08250815040f02 72
    0x60482d4590b0024007034040c03a0403520500081d60300d818054401115007984807040d03840d04082c01030115510041c000d80c244034850f0480000e00039145081445a003d0b68091502c8034420440f9500752138014207500344042c0408000d12998106a00c1c5800712984038060403c07540c141c101c02c074064040c0c0011040110008916550000c1d0160818106c841c131903008d03914590496800c0c1c07154101c1c1b109001d0001410407502c601500c18008034540c0b03070800101a8803201074042c8688050301c00840380c020341a929010086000c040104110340105c4d101c1c10240520300d40c0802c400c0e00247e032403101810300c00c080070000349820300389240300f140c0c10700160070340300740540710403010390340f0314240c482e10b030103507184c19604048244110785040d0a21160315103403404140c0803c10070081d40048101202e5801801c9411000410030003030b402c41d945881e00e4490703161820703140000c036024410800c1000c50f071411004402190384801040e034440c1c4001e6040080800842c00300e001845441086240c551001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 381542320 1250 381541070 381541073
    0x30405030d2c07150203070507050405100b03151519120e2e1e0c0e090703091b05010f0c1407030803090d02030702130203041707080d110f0a1b0f 64
    0x309106040c1c40103030200458451541c40100d1b501e216004c40905503810121060000c0d10301a000150030040c2824040d090325142c14901c0529802940c5000b01028100c69030210f504140d4100c2000d00500ea81c40c0d810603008011109048a550b045007040001c52184150002e8180d40400325102d00c081c00c607590034013001c035000d030300e8200c0a05000c1090a00c041454402c1c40038040c052611660381102032400701c11000100c0a44200c41c9150280151489070410a8907480e0721036110b00802d90b13010034441618100381407800740c01021044c040414020510003a43c12800c2e07030a0920062504000c50444c605100907044010a504208c40c0074104000090082c0319002d5402441c2e00310540c0c0014240d160b05070703524030440c2002500804103c480700c0c2c0010396540615070141c011001100c0e0040030090f1940c140d44440c03000c946602020075824280c562500c500c0f801c03100062407440c80c103101103022160380c4c000c0101c060100710350b9510124110400340d00c0150065400030842e16090040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 381543570 1250 381542320 381542323
    0x31e11030a0e06070c030e120f100f050103080414210a0c08010c02120c010b0d14100506010e120708030f09011d09072d050a021002030405030d2c 64
    0x981e2505100e50a000b40210402d601051031409900f82d500c0e03124080d011650b05071000716094040961200c07491851260449007408252903411440000c2d01800c5c07510052a812109002000700c0403524003070052000410402c101c405035881c00b940d44650702e40d900002001e48000f07030041903502000604000080c140087c800180c24403c59141403815240c2c1c03800e900700c481088200c00181d211201c1c01d850b2001020050811200e500004590700f9100c00c0411840720348075400315803640014100e00c040d500c0034802d1107c034143c101700030311180c00e080000030301c017044c1c018041e889281d0744c15807400300b09070820010f801484072405032502d5035140c00000c01c03035800050890b40400c08040100c01621103107400311240301c00090851141d5111100100d405000c100800802c22070440b00790203076200c0d24010140d41c4d03000c550340d059a8040b0503100a00b80414080c503000b070301e4014410b12000460100c00d840144a01c07800c00250000c000790400381c002460325844000d00c880c009680b101850 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 381544820 1250 381543570 381543577
    0x706021308071403011506081305011e0e0114040303020a091a030109050f010e0f040f0b0f10080a11061e0c0d081b161b08060f060a1203031e11 63
    0x100d00f40100e444204010a00d42a901c1303031880385800c007840c140103101050141188941001080f4049402c420b003c0c0d503007508542040e56181280320114614080d1a1100e0103825014604e80740280540949821051323a80800540018181070700441c08103403891203107044100a08041070003582014510181c641158020702440040505040020302d58281d06074006040f00c280c2c0035245d0240c0c2ea003007000c50a01c503001e84111160440318020350042040d401d0950f010303071500d100e00c5440781000d50540c4000c0c02c40e94480002d603002900442c01003600d50850600a02d000c0d0781e4990b0310b159020340300c2c6418119224045c441c0402284901541500282c0d440c052001511000c00c161070362a030050074071000c0c100140ea103060400444e22036010104064011903c900c051300d0903010408000ca86c400d4403a000489190b201ca004c00001410340c48602d600b00c074064411028090170203a925140b200c1d003400150925440d40c10312114440b58555101040d584481c0030482c0701c1c0c1e40641d5030b59592 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 381546070 1250 381544820 381544829
    0x51b06124501060803030402061204060b040207050606010207081212100e09100c030b0d060b01090302060d0b0109120f0b0c041806060e0108090717010b060c0105060a0f0806010b070602130807 84
    0x10303e00789020414550020880340507540050409090070002c0080254003040244100c603415140c950550701d940329030020745000c0b0310440141990380343c40350009181c004554071118455101c0034110002102081c215040c00501e00110b081d150f4429000341c9240c0002d90040c0f06e900e91217000c011800601044c00401c81c900e410080c002600220340440a6031059012140e02c000c07200451400981c1d19803000070381203010305180d401a0398940014011ba0841e406485525071664035031000e03076901205882c090940032041ca81c0740e03010350b190140740c483d9408000786107030f000d600801c9541ca4101d080d00d006028180c0491003032850000c074500a4003061040601050030150500780395030040d010740e482001102c0040014038035080c504040711040c1000708206d956541284151501c2d007400500300100c05c90300200c0c9505082c3d0921503940c0d00c0d503000800c0b128509406100ca10f07004214a41111114043c10b07440b02180d0404030002e101d102c222401a441c4190006124400414020101e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 381547320 1250 381546070 381546073
    0x8060408030f0106170a0f0f0c05030a0e030717030702120409021803060618070507020a09050108070815070c1a0f07030b030d0c02040207030e030307051b061245 71
    0x741d81c0c030035007943e00c1600f00d12100b44864462000611b8980164002c0e8940407101c000410007504001586040360100c041d9040040c00010802c03241103098001c0a0201d40e40e00d00962074150140c80d2080c0e4030f5081d0740c080781d50070300c00004984964801c0003108610075551204665035a66405564029804111690f2170400e1300342031800c040c0350121700c0603c00c0d003010300112180d404002003002c4070180181040c0078050144440b501607143d600c044070281c5401c01c4000703469414080c1c00c500d07040681d1300120b0303658440e9480c1020042090440d94000813542031218417140390303140c0041c0388007080d05030160155404080000c000c0342a1482800307400c1e1920b041003c03402007800e1607201c8824080b6000840c00a2031464014202940240030302e50181c5805140200a0f0000a04540c4404001c2e01c140d4888030a00c2c100c3c40c41c0083c594580380007110b02074501428400c524083e04401480100030300c640090a8a06082c0c0b20046180d040307a00740c0e4024a031112212a00c680b400c48003965440c0e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 381548570 1250 381547320 381547351
    0x603010b070209071e0c150207140118200607080c060609070239030f07030b0a050103110d1b062703030519050d050a0504031710050402130806040803 66
    0x1e0380900c49008400d100700d120041d915017209010343c2c585849078003c64100303090725001243d510700b80c80900798952140d051402011680b00506080d103100744c10040c54014040c59100c0041c1c0c00780d100c03078069009807541007002001180000c0c501d0041c0207000d03082050000b060000c444010910f14822403003251b243c10f00d03441d9a0402c80e954020101404849d4000301c0090b403403000d40810042a5980040769440d000414602103400c009aa080c1140705074040001403081117081407400b03a00014402080280d503155884c2c0c404002c2074810703000e028500890044045c005500c01c40700761345951007100c02c03549503900401000032620461064181040410303243d801607082c807012007142d40594505003000024031650904410005a64003131003020840c40601c0642800380520555141c080002c2038641070070040c10304082d0440015191402008005410034000098006c1d02d0b000c1c0c0c2c005840c2c60b0080c06490218186800480b064400c4008020802080c80c00a41c4644801040d1500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 381549820 1250 381548570 381548581
    0x1c0605070c020f0f030717240408040303080c090d052a0f12070909051c02030a020d1409030f07060314090d122405040c0c0c09050606090603010b070209 67
    0x446119100700250301801040340007040b4982074021511902c07000b000e45103401d66801032000c060100c549202035640007881c034142d10507080300d03002c12400100a0550600d1030f0030ba480c400d0a2085000080511008a010071809040b010030f5481d04403000c1e100da00c81301541d0601c0c1d036650600c0c0c510b03c1140e07082c0c01d1000741c0326501c84030b04102c0b10340090515201c84100d54100052285102888400e07403140c03076000580428140541d650103401103002c6e002001081d1141c40c040c0b02c4064101007550b008120034400e481d4009041030380c240083c90000810003009003000b09130b10414600035811300c58101045a00140440d0103030442d0004c0d01c08103c11307030444200c030f0015142102c0c00d05440d00b000d107688450303500845018a038010a410002100700c2440074403446070040400800b45c40e030401b007040c420341c1000c1c0300c0d564840715031f810207081d00511940c81c3c0c4c48005e101d00541c000380d5120740110b5042e840d400b00303036254414001e25098582d038413085501844d0300441400d80c801e4152001061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 381551070 1250 381549820 381549827
    0x611150c040e0711061b030c070807080726070f2d06020309070f05060301030803040213020307020f060c030c0d0b060d050403121a01141c0c090303110705030a021e1c060507 76
    0x1404603181b18002c9003903a41ea10900403040e000300c4000c0e244918100005030008843d0303401071108511940700c0c030b60b8040b04290504468102c1c8254007000400c01c00000002c2040828034a2000b0f921506107003500304402c10031a010b500020143c99014902540c1000300030b00e680240d0f01c90030f104e1040310401980d546582c40e0360902c81c402c0b00d41188003000144003080c401c500450b44180040d0186403070400c3d040f41d1030101e9000304d407130f400140c10400021710171700e1040c40340342d03044001911000e066041c003494212080c800e03c910081c90350707503a00380601151100000d4400c01940c081c0100110f02d41420040e0503401603079a42e5071403e140c1000f068400b2a031490364054440180d561038000c1c400000c8000d00755001840200d032504070004030903a40342d002c2c040c071110900280c1c0c1e02c5503014614900a000501100d4900009800c00c03001440381c2d8400040240450350102c9090704c140c0c071440300340050415103c0207243c20242a401e0148251460040c402c1d10754440d9030304110b41e98400100b00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 381552320 1250 381551070 381551101
    0x302042405040e1f120b0609070929030f06011b030c0f2102100b09040b0c03190e06011d090706081504020c0f01060611150c040e071106 60
    0x501080092000348081031003a90341ca035001c0811904203800c2000f10131080c507032030800e5010b003950404101c1c80e1410000c4611115412807419945540356040c8104003a11283c0030f4010031000b00202c10020140c04070751000f2003001003071540c0c050f9030f0382000191007045982c00c4401e1030200f1804038095405218076484007460a80541e214590301c501a80d4000702070003000e030144d5907200180600c1c680410200c061a078000301c00c1e0000e0812a00d07040201c0c00340c0358000d0b0203900c14000d1104000100d12078a89c01a442848420040c0ea245e5481c2c06441d070200140c40d4428031189004041c008012000038410f05841c1c02074000342c600c0d140580e0365030b256001200c92131500e41041004000c1103006000c4a42c000048106080d140025500450202e070002504140c8a51040d6800c2d0810103081c86480d019003030030701e8049800f14551550b280d036020b1601005100f02804800a4407405195058070040c0111002040a0b070520070303801080c1260000289485016800c085100210b11448a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 381553570 1250 381552320 381552389
    0x70203040e0f10380d0f0605090c131a0c030c0d1b03020c040b1f0503010911030906040b040f020a180606031b11070f061107140d06051b0307030204 65
    0xe881180c480500400081c4440101c00d020a14083c410303050580024000c100451200e0840025498603010420249e40c0020709800c1300404100481c1030081d050051042c00d40d07102107181017000040c002250650300c540c8840c0b084500010821380301a40b408078100c1d0300c0581d076545202c1e4400b2200e0741c8030f410307082590300100542d101030209201410a80c1082c46422001069820303180e03001c10030585041181003000000031030000c0140300014161042107424103180c00490b05500d88049040c0c3d455034040c201800404251001608014000c0b04030449194040e000b040440d41c2c401081d1840400b0759034105050f810300d0390120b4414401d200c3d003a1010140b0341202c0c804040d2001c05c0c0c81070805015107102e00d00412101003000c0040201c206c2c01861541d4900001581c10051141040103a4200105017908580004c6d011b541e0342107040807044e044040000c2980394810741c03002441804007a012000c1002c410050380e90340583c0540101c90040c078584520341c08801d42e01e07190000802c403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 381554820 1250 381553570 381553619
    0x10e030a1b051530040212070f060905011b0b071803060204030b01030b130b0c0c1002030c03071103090d08030a09050f0d1706030303012606010b071403070218070203040e0f10 77
    0x17400740c03900080c0345100e03801c414143c622260b190390845921011540146010846804040103c1e507803007402c24110f102d2101c00640844410751300c81001e101c0c00307080b074810070007aa00c240742d51a003d000c0e650000c0d46d01200c00c40d0798550345d141c10000b0100910040d0f0f400c0c0c50000000745c0000e4528004041180d000b0300e005803641ea80700810400750003e400c128200c0c841d20440220802c1c981c8003d5011700d00b20107103e03440e03180040004003091141140ca0690350814000c1507042e48078003041078030f11544038a03070a03281d0340c1d188180801090403000252141c0b00380100a00c0242012071b034215480710b9603543c8141c238508103412074400d203011748005805078401c2004100204114160600c010003081c03100b4034010100c401542790160a8104007401c03500001e24908000d443c84040e02c103a0003410255041100e1a00000c0c050b0300d064059031860018600040e0f00c1c035100380700301c070050b044000400342d6034200465100b0b02214125134a50304403070b003260041103824102540c401a110a03a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 381556070 1250 381554820 381554917
    0x2130302010305130c0e0402031c0207060503060622061e0806090402010512040c050103270201230d020409060501030e10020702012f010506010e030a1b0515 69
    0x60044004000013002c6002e81c03c1074880c0e000000d13814017007010044c410050340030f030705040134010541400d0200d09091610b008100403420050f4012034000122070603801c0c1592640e0301d020119160b480b40f400d03001e04a51440c0c800b983c3c4840f40066180a131100342d0780398040718030040d03000744901d60550104008074500744000741c1c280c90b0028040390305c07605c1858104e04028001403443c42c0700c0416601212000c0710440c3c14080c0c0e503410300c95460410074003080d001c40c0210401032041c0f250f01682010f810000d0001c4400c601c2420105007a94100c0750540f810b9640100d5a43c00c002900580602c41041d41810400034066119020f0150074141c800c002e0b04903108072601c070b54000d511184089061008140c00407000da440280b10101c641d0840f040f2403d03030804402001d0131190001d04190501c04991020722040e02d0000d203a905081e80000015070080c0304004071084251180d02c00c41d4460103403850507250f1804480900140100c15003041e4421141c150403000b80440141060904103c0c0d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 381557320 1250 381556070 381556073
    0x1170c040b0325121a060109030b1603090c0f090608070803030601181805070305090106080717010b100306030c060305060d0803060d02040c030606091a040b0f0c031606050604021303 80
    0x140f021040401c0b5096040841d541c070b036aa801404003a00541d00713803540b01040c0d40841554140e460740200d0910748004080e040d42c4e101489040d01900520070f55410303407011401316010740c0c00001c2e441e82221003007603246d5076000c428127010303680c0c001c221031103040c41c10008002e10000b4042c010340d080c020256046a4480c0011a030341c00c0d41040c10504121a14000207500410448000300350300150b40c042401d1421000290079914007030980701c170030782c0740c403038104841d0342c0c041824002c1d1a0414002c9511004189103240517103010010141c5c4403d205a5000440b42c055000d401102d1003051407800259031a40309404845045541c0c5400c0052100490000b402e880011540400010014104440550003003400c03a10402c0000001c40c1d0b580c0c1040c400b6981103981040107000120000030380780800192401103004611030340b90410b00105010368851014415074542d490302ca0212915012040000c040e00c41680c002a10f01074a0140421030302e0825000300e030700b0390a10103100010a49103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 381558570 1250 381557320 381557353
    0x503040b0c0f1603021006052e02031308060108060108150a090204020d091a010b0403030512060102010b06070b0f01060c030e09150d08071106032e030b01170c040b03 73
    0x2106019400d4404020403c0200001c8803c1d24145000e0b50051050000a0380d5283c1160b6003a00700b240700e0503075010f080700b07100e6201d03c408200c408101403100c0d140d02802400c1e46180594042c40707120a00f807400100b40c4000005000f412250b08000b106c042c2d90381d5140c450307100c3c0a6069540a01e0840100056290391281c01080402d07201520041c0741609105d500e008417590000f041f101261483c183c8203550b01550200c81c054492060b215240c5807450340c0c0905103100c1d248410307040d500d0030310005038142e0003907004002c64200030b4801580e6140901d0a0b5103c10011074540c991084a0000899118803523071520400c1d56060300c807001c0d031030088001c0015850b00200483d00c0780640042d0100c042d12401225900ca40c0315500b41030f101c031340500d010135003920f01503c9240100000d00c10002c1e865080b80c0500c18601034400044844e2122201d0f880001c2d1042c0c201915008502c800014420b940d0a10100c49510003003e80f0201c1e0810170400045d90043d80480f58154002a42c41802031032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 381559820 1250 381558570 381558577
    0x1060c03050c0a081b0f0606030316050705060a08041208010506070b0a06090c09060e09060a03021c080f09040b0a0320010507021e030601060504150305070c0203100c0f0503040b0c 79
    0x10203c03820600b43d543e0380c2c0b41aa00c00200226941d010031410420f6400411017070203400141d034003421040c80d184000c41c1e40e90003080444d20300d510305001540244001400b52901810700940140d41d01c903900800039212080c155001c44206001c1c044c05015907100d51003041c1a600010700441c50198507480c1c1c43d40c095006040d82c45469075070b500000e6810905d02c03070b07051150b0040e00da07040040c1c0352074000740500c405440298082c880710b0040002c00d0761410341810507a941155400001416010444555070041e88001d000040000d0241030000010001e0b1820540c116414418440804184000743d802840010410030509031189510380012060811390749041c5406030800c0120740001d20401c400700e000708102480100d1040c4542014080c01e0302610160034040d207482d25000c0690302c280105d59516040650b00c5001c40c1040e4896115036002540050807a50040c1901c040b48000b442c80c4000d103030114030541c0604400038011b43c10b681c4500d801c0301c3c100000b070781d0f2181502c00962 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 381561070 1250 381559820 381559837
    0x7080306040b0f04050f0a0e0c09070f140f040f06210231260a02010e0f060d0e0706030e03030f070e03060906060913080d15180b10050301060c0305 65
    0x1580c030f030200b2045885902c111842402c00780c045507520309240043c481220803402481903240c1000c0418169600c03003c000c140c21014600c0d01480c0e10a034107004490503c4401108103081c0c800088014800700c50401610a448000788411101a40c581096a0500a03012034000051b4007981c0c419402200383d01501c8040c2c0b8181e20804d82c0c02ca6a03002e500b10280311807001075010340e510010302c05540000701d0401e030028800000d0324800da0014941e90758640c090341c002e0412030918499599529012003d10070407901400040d01d40340030031803c40c09084260a400342d0352283d0030740000c40c68800c1c01901c03801c1c00003d0145d441d40e190001c10090242c0000e002030140309885003010440e840070003107140315007180d80c040d10700c03424850100002c00001902e40c100d400f03078450340c0002060160040b99440803901a00007040500754061340340d4100e4a620200030403510224200c2d0541c01da07000034205072801c880e1415462103850044d10302d404280070310740c00684820a1a000240610002e09444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 381562320 1250 381561070 381561079
    0x30e0c0913020f031905060f07080601020604060213050907110d0e01090314030f0c16050f10030b2409191406070812040c0501110114190615030b01110307080306040b 73
    0x41d02821944905c4818a010403100d96200000b0400b82e00d404034506078014071b840c5030988140c11300c840000c1d52181c01400291030a5800654500800c041001c0302d002000081c2c0403d00c03518000070b0142018280804954080c003506052000c5a0303c44c48500c00c107081c058460054050031526a002c44004904290240780300400c034882070800440301400c0164040d1005015442d2154646404003107241d211500455078551981c4c856900c07642c421001a40910740040d015214200050f1802c15007404130b280c440301c0885e50780110121388001c00b8220410f95100040c040a402410911405031040ba90704112407220b5518616140005040042c0110401030400309004224010a04152011a4042e0410304104000d580002c03090042398040300003004405203030040700d000e40600900b9a5070344c2a0743c03400d48200841d950300403000340c0300c1da01003c1010105514061700a1006ca0f0781180401c0f86041b8030b0548041c00001c460403103a01030b4426043d612a1010700c809441c0c48101c40703900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 381563570 1250 381562320 381562333
    0xe18010c020c150d0e0601170f0105070f0f17040605010603060e040503040314030d0203100906090506010c0219090905010506010305010b04080a0f11030312010608060a030218180d030e0c0913020f03 87
    0x6800e080016501919140046c50341940317121008d21318100b0845011307112641403008201950b9000071044102c1201810444034401145a044900b103280d410280541d00e0000b017880148400c0d5849581030740c101d520108205138840c00501d02180c0216030041c031035441000284000f4412241d50340389441c820702164241030100301d96100744d0300119402c0200b0160190104494a11405150001c1c803254008200c1800d216000a141380c1c1c00000280c0201c0d07038044008196102c1d1a6a04001c0c400324504005407442c51a04030f010709016605140000d0034080045003041a003000c0f60300312000311004204940d0260355208107070252020075500443c81060422603514144000c0c4004040805840072541c18071001800d010f10192a01e4010301c0b4150043c001601c8904000c20311110650f241041c994814803507000c41901c448140c40b8501404142c8166a5010703086aa04080b40300255140500c440003484140c480c210741740c00c0b1201000d50070001500f40625a512422030140a9401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 381564820 1250 381563570 381563591
    0x21080a02010e070b0a0206011a1204110301020c07091b0203030f09010f09080304020112020414011d030a0c180c05040b1806030106090e0c031501180e18010c020c150d 73
    0x1c1c2000e9500c402c41c400c1300004c0182e40c040c0e05106030380c09094400c2d440004080810090a80c030300441c1000418907002001107014000a20082c06051100070020b40d03403260084260703500c2d2000d51081500041c00d1007249a01156244045aa00d0074964001c600f10f80e1003501601c0c0840b0007030036010141d5651b018070321121703513503010300443c190080c1503ca5490070075200042407890b40400c0c2c01e50061040c8014444901038070040b4800500074030b400d00256030803c402004200c44e2841460b8548148001b900810982ca03140004076010b03107804a6100e000e4804900c20368a0100c821000218200400e1103210074040141880f800d031082800090240580461030a90082c1c1100001c1051080204200309907100c55580c400b40001825065042484011001440350840c0505100c00d031a100240e05060702c2d1160000c0c018202980030310304140c002a5000802620070503a41c0d400c1c02039840c0c03c00c1c000100442800700240c42914443c0920702c4600303c5405c0021000c0e0115250240c4030b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 381566070 1250 381564820 381564823
    0x7020d032a1202012a0215041a0903090901051e0406060503240607060507140f04050f0d050a03050904090501050a0b0307050d1101031a0d0501050f0121080a02010e 72
    0x100301c820040030001900ea2508108010006840c80326086a040150345103202c1c1500c0ca11600140c403486200011180c3d03410140d0529600100c06240c860f810700c100001d105a21032821910704400405a105485800c802c5031070713115000840703420001c03400040203141030040c00b603c3c4000001000b18141c03070a850005050755025805000040c4d004414081450324850025451480c1c804409004490102c041585405035110181803180d450000074a0b45025102c0b842040402140641d9541040c00010880d074015024140c001c200d88015115541030a0340d4242d645a0001c2c01420101e40c0c0340d41c100c4140e03000c0d00070207801c40d803941540c4000900134000e2074040c3c4c00c400801329449405205141c9041c1c501c0c0d00040c40707401101c2081000c01c144e50081e1140c0002840d01250b0601580d000e481c1081508803165000a642e002040c140300042d0301207406403980f81007005841e6a9403030340ea051800340d039400300840e1401c00c211400151a07280145000300441c0004548402c0e09021789 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 381567320 1250 381566070 381566117
    0xd05010912020c010e0a03060c02030412030c0b0a020c150417040806220308150a0b030f07080c0c2d0601030f0c1d070509010e100908010f05070507020d03 68
    0x48407420300503040d500c542501480110400c010a2070500302e203845610000e0040c1e0901e00c005031099079108104803056100b881107801601d8440480c22460810346401000000703510415241c8100f0200480c4044105008880f40a0b20301e10041c050545503508410b4000d001900440f20341a1034503490b050448204054801415802c018243d50700c1d007202c1001c5c03900568104007903031403110411100040e4200305000c1c0c001c2980680c8004014456020510401464005089548010040107800410401e8591007980a0384d01c484043e141d4455010341c0303000301401d0701d0841e08440034034840f215052640e0410030000b07141c04803807000041c8102d81000020f820994100c1242c2d0300c0d140a02840c1541800108002c03816a90008031416100e80c02c060b01801c030204202c0d00095600c5141e11609001440d6103004200d038525440d404c0780a01540d41500c01d4540381e50030408081074041c200d224a40c82050181c07135180c43c10003690708100c81c080304040e045082c016103160b00e182c500f40e008100c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 381568570 1250 381567320 381567323
    0x108060112060b040f1d040b040f0b01030605060111011401120f020603010f03121d120313060e010f0207051305130503030405010207030e0907120f021c0c030b0102061e060d050109 79
    0x90b0b43d0b0350b030b0601c40c01405d03204881c1c01a8858100007003020714903d2201400c65032107900311004100580f620b1030801c60003e58010090402480030001005106442c1e018038014a8240c80785107044081c0003410b800e807403202d0754040d00004800010885419440c440858240c85804c1e20300340d42c0083d60001b03d0581003138000d004108460101442008450210000d1072016400c0281c0b0864690300400741c0e000b00500c11034000d07904c10445024900c0c00704141c1d100700240c030680031284c80c1c0301c00c0c00400e03426030a103100340051103610641101d54000309408044d56805094102d10786407140445000c0c2c100030301904042d1141d4401c0c0070100b00d00f400518004c0d8440d0001581e06c5126003402090300c0d00b6010303400e01c52410710043c0720799250040d9206541ca001e007480800c42102c9082c4240090041c106202510300e800d0000315118007083d40155035032202a2010007842814500490740c2c1c030011110400f19100f84130ba41111100d0380b1a51a0703000c0401420481360b801142d07501c900b0354491500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 381569820 1250 381568570 381568589
    0x603101802031213060509010c051e25140117010311011202041809051006081c0504060c1104020f040320040b030c0603040501110f0712050f09010806011206 69
    0x4403030031441d0610500003c03c01c081c0202d82414203048180b600111144900018001e002904403903590013044500070854000c0c040da4510014855440711103d0304480056143c0580c0003075036081c25160480d0782c00d00c052882d042c0412070900d0804c4e009104601c40c49818010020031784500d514281000701e002e984a09589841903a41c00c0c00940105a8903045116440c0188000c0c8242c8100c6034511280b0007034041d000c201c040040c144541442c0b0303006400d0244a080840200c1c80c0300300091900e06044901c00049990702004004480c0342c0100c0c0152800a003d40070351502088410524040101c00140014607200e20300b40e4a0300c041c1d00540c01100d0382c040d440c100d40e040404502007400036003030588082c04820b10080010b41c0301c59081220720304c0303501c6c00305c04141800400d6001603008401030300c20720351342c00001e600c4400740d8101500840d07902c2d8400c0740c200c1c4e01da03100b0415152490085280c480c184445980159900c2100070012410080340d409223926200d00c034090302000701421f00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 381571070 1250 381569820 381569861
    0x40b040807090c0c030e090a111b060a1803211503021807050324090a15140a0504021b071412280201110f030301051f090e060310 57
    0x1140c2d0801d541e800f58264043c00800070040011a400c1480520303455002c0700e007801d969842a040d000113043c0b03d40d0504410002041001112301064169070a0003409000c84c0c08a9031a40c904a066a040c241250035103c00c100781100040c0c0554000060309149100c0180c0b450070804101040341d084149000b0000506031041066040c451000c050290001c00200700501e031803240544540b02c050100310511060390009072462500029071268144020402c50361810502c080002034a03402175400851882144006032110000114103c11b030070141c40164a01c0c030b410b04000c004d400c20000c0501c032114401c000080341900740302c2c00c0060800d03408642480360640e400d004000c507540c10205426030064441c0109220f14017019245d440c00c0000c00030401d001c0b4801203c04801810740c175140ca1149051685901e580417021f14160742c015626040380001c00c50300360301e02046020180b000f0840803a0180421107021806660044025003203490f60301d601402d034400c650507000b403a4030300380044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 381572320 1250 381571070 381571079
    0x3071208010e010501170f07032009181302100909091a070212040b0d150923040b07030903020106170a06060512150702010b0409060b010305010501050a0903020409020303040b040807 80
    0xb0b00205000d0300081c60244e20741c0c415902181007520024040b0081c0203007020004000070310981161018981c102600d1507031042520101d45582c2080008620402801083d40c0101c2c1d4500711b094400e803104088481800e0046d020310075044a510468400c010301c1020200340d03007002c1d00881d540c0d00d2113440748600b2805101005244184007401301c0f421500300105030140d415083d000e540aa5078007031040d595500e00000c2d100010541d01da6400401c2141d100002079200a42d03106213401455010444401e1580442d000c003801e004540041c540c413089000f04a90030f12036030100504501c24000000c1c6d090f101c40402020f00e5070403841c400c1c2d55000400d00710801030107001c0c0000920303059074044800308004c03204036180c0560340c41c0610500158000210624400d4004498066020b00304200310303074a506101e070140103010401c0d400b00c0d0400000041e02e5100d44110b030611020356071110052421542004050602950142c0e814802480086104841e180c001d000a10b8002c005000c107600c0c0c0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 381573570 1250 381572320 381572339
    0x9030f03050c0414090a0f05090f15040209370b01020f0a050a0b1906120209100308030c0f04030b070513060215070f0c060c0801050f0916030902030307120801 70
    0x52900c042000d080c08104640400010441c218038012500002a56900d1045a00810311001c2405291f401d000921250032030220f59044ad0323410350b40c02c1c1e42e6020414132038130604241c140c40013504140300100140b54000e0620b4101072003103125036044c8000030341020340fa290384400701d070802440f5601c611156041d80c0400100e010340c1c41c064042c0c5034180342600d52580396003031620090821469100003410003ca44280341c4081a116141040701310b4869800054500000d0012802240c0840216590030403600c6268112a8082d909c00d145556a01c800e94264204d005030003d80d0f03170b0a01000c80001c000211043c400c0070150349070707615180390881c45800c080c501d40c440c80564100c1040c40c105a225403881079401526814201010004003c2c1211895403150014007614502100c00e00602d500140c0e40d03040311400c5407030742c00c000401c0701000424401940c84000800c011081c0700340450203500641c4038540010b05503420040651210141d2000503403400c00081c401c40c0051062030300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 381574820 1250 381573570 381573581
    0xd0f02270307030201031508060c040e09010203190e0a1a0f0105060c060412090819060e2802060906030a090c0e060d0209040c080a1109130302072709030f03 69
    0x1541100c844000e5080082625455140400b030704160b102e03a03e4184500070a045200104004400c40e0b5442c1b82c83c1050392040e82290140f168540c20b0400801d0440805000380c03806042c1030322201584400107990440181509062a4454040e101c1c0d0500443e078048102010a20b000f0400800382c540007404085501058118070300c030318405e022022070800d000599580c040d9214402e07882d0b8103221042543e15280d5588100c10310b203d000a000b010304025006080b00d10301c10101400f90000c0940120340300da0065004000e01c100440d0708052842d41d515a525009001401e1030b49001c00c0400441c03050703442110300007050341d211803d442c00c10a0342070507000101840344450f41c00e8204000011000806d410020344502d03c0113000c03d0601c07404a444d44010480c02e021078031004d410303142c030500724420070043d1841034010200286440291880e41e80c03000d6890346c0034090040c2840024200900c100074260000e51600300500d40c0e040161080f2510079000e034843c28403400e60401c00809030740 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 381576070 1250 381574820 381574867
    0x17192408010c12021e03070c021e0f09150303030106230403030c08090f0622050f0d080a030915020408010c0309020303040603020d0e030417060702150a0903050d0f02 73
    0xa02d4100ca0701c01003688140e124501c2c1c1100e83c1d0250b61600e29200d005020902c00d0126071402d0030010903c1115030b00107804110141c400da0f454220f10140407801e03075034005c0d1400c1050300811003101c80b070801d01d01565800c0d40001c20401001990132a500420b1071500241c005001059140380c00c032800d0a5941c44041c04c10039031b414014a080e0850b81e004021900b90b1f0320040100c0004030b404080e80e5600700c400401c0c81000b600e000e880d8514500340c00c071401c1680f000c600340000c0c0024041032a0801c1c810f00c2e000010050403040c2003c04555a00c0c00315484207003134004256441c83e04034005016140301c1c42d40000500c2d40903880c0c41c00c000981d8211030700c00001354281850b19a09100684022055400319440343c140140c484200b180d521020f1f00c19400c660b24180000140030544d0380c002e4094442447c00c3c907044812640c0c51040c140c1c1c3e105040c1c2410200030610b00e0024042280daa000288400d100f490b115041c145005030b4442540e003070ba02c100301e42a8010401d001301004200000e040d05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 381577320 1250 381576070 381576073
    0x41403040b040b0c01020d0c030b1c0b0402120f1f060b0307090902031315090c0b070503070b06010908061501080901090308130807020a0303051e0a17192408 69
    0x41d10785014030307045120342d00c180070281c507000c515a031802c0300a6041c4d403d0500702c0c1000344134010302070200800405900022034481c0c00d642140f04030b0546c1c0000421202c540c8407480b031a403500d490b0200300901d055054030300018444d0051010350400c092100e0b00e1140d1400840350a80d201c4d0a00c00402d032041c503004908801e00c240b0410202c0d0f64000f031440221000e040005035280c48800e40a80c3c05031810350080c2c00642061314940300015941d204551050149919101307554488006010910400c1070291807a803003484040c02180c482e041c402d4020788141026034015982d80000c0d420614110340c135000040d4031984101c00c80d60409041070b444807a0100070040480f00381e0307001d00903100180c0207078005a003907415003041000c5c140031640900e170001c01c4030341d00d140d4134500200590310201c41c40c0164140780004144415825003580d1070000d080d00c65031801c01d650b03071525087c081d00401c0400004040c6500c121428814800c07070074151400c4040f988580b6101004503002c602d07070b50208146 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 381578570 1250 381577320 381577327
    0x8180715050d1404210905040e0a21091e0e070206070e06031014120a0b01330c020102010b06030901150f1d150a0e0708060405070509100306080a0b041403 68
    0xd001a840c5c1180e45440c250522184846520484e038038641303074200c2030b003080ca071661146e006070000628605151189181038088450316030070b41522103880d0b5440005c00c4c1485410b0141040d42d8554100e82407881c1c656598140d40c0c0c40500b00490b0303040c2c03964805a00b00e102408a100e50104500845810a45855185050040c10504420400d100e03a01052240d0281d15003a6a161008109800d111104641145a860909448070135007031007100740341c1189642c0700d20741510501d502e40300d04d02d1030102c01004100042040c0d83c65851003004134115540c52506030724a41c0c40602540c010f03440500009000c84815030b51240042507508400d44804800e00100000c000d080c20121950009000414098031100f880507600c410702c042ca95409011000081100800306000f87e10481465540d1300072170303c1d00c80501040382c1b4142d683d03000084080040e0341040c100000c0c0b241e014031031443c0014055555814032030800d40194002c03202d41600800744400d208440c03e035240c03e000e103017010354503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 381579820 1250 381578570 381578573
    0x80f0a06050f0103020d06080d0203030709060e01050a080405030706090506010f05010305101403120703020d080a0b0108010b0306150708030619061b020607080c0f01150608180715050d1404 83
    0x100010700710b441410150009a040007801c0b07130781c020500510707440c821100c020f052010082d49981007113503008002541c1c088000f0310070f031040c0c904119a440603100d880c83e00300784d20412542400c0041c01512544010040000010700500c244000746014402805503541055000e6064400d503510180c1050304042c18040040740200041c8100c520315180840102030f01c80200342000541628605030000200780310081c1a00418072a0414000340d0390b036800c40d658174201070125202e25188a0004030010014032101d02107400464110000405000c405054054400059801002d080f40c2c01c00021040c4030b07150418450301e03003166030410b114031611410a1401040741000310075510100d096030f600c40007552620011601e90a400400040e5a50000c0d60156910082184101025842c012900114000b8480200243c5001c2c1c0c6c0c4030a6a62680884e29070465108401e046942c0a05140000c006000c80803583c07250f1215102d468860880304552000c1340c0c40400303005a0300700746008100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 381581070 1250 381579820 381579829
    0x30a1d01380d020102011b090f0b070302101d030711040b06040503190305120f09210a030504080405190303030e030301031208070c0b070c0203210a1115010303080f0a0605 75
    0x1d0310301410390350003050026900040740541988078208040041d942031711441144e0024286045e02e640701d00030200c0030740d5902e061941d44994280600180c1019130107004001e02c54108902c000c212400440500d40304403503880c15a03101100482e2603840038005810070f0300b01030090621022044a0b040d003000e01e06400b0a845030008000c61403601100d007043e404142c01b0b1816100380b0410b0f040c5c440d05c549050b0481004001b41647d10203c039201d84182c02d80c4501c03854a60000700c09900401d9030078203450328001c1d0040d11001c0c10031114480c00340400700ea15100c000e402490201c2d20400445c9442c514107000d000c48039440c18098440d08204010b00205090007610f4001c1d480c1440d0103103c07a62500d03c03caa045840c080010300c0481110700f44403110f9400003484407514001ca00340c0d902ea0001200d80100002d814a4400c0d01c02410b03c002061940039820b403000320180780080d5420407031240081501400260002c4000c505c1e14024400342903503070440940c2c01112282e08010389810310707002a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 381582320 1250 381581070 381581171
    0x11061003140607050f0a1815110607020d0c0c030b1501110a110f06071406011e03110904050a122a0213020c10110c0607140f030a1d01 59
    0x20509038000180e111b0301d41c1c1c070866401c107900e075410f81c1103060075480b072000068a02e8141d060f900060094011111f00c0318000c10a01c2c09001a500241495003a003e07003900c4507a003100c420742d581607240e500013006c12407407000d481c410035000c64802081c0c00000009480c1100c4010100e13a258041c80c2d840000450480419002c40d01c21a4040000703005040003c00034814007400500c41d4281c840324030811080000d80c1810b0758820000c1401070701c1c22001040c1c02c6445d9110160075820710b0a03080c019424481e6110b9081400784040c2c80015525484da10b6070802e90134042000520b900c1e07018046060114079a134128110b0b001100c15800c403031380018404c080c00c415108502c50780010412103000e800c200c0030007000102d410074070071710b4440c009507403860b00400284400350003028001071a0500ca05500c52803803503410b0340c45040c0401c0880120141e00010030b41c91071170b43d6444810300384030000c030720304240c2c040342c4030000c04c003000c0b2035604600102d00603103600349034a030820b0f10001e624185640b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 381583570 1250 381582320 381582337
    0xf050721020310052806110c0616051b0a09050f1b190801030b010e0709030b06011b110111010501050a14030109020d0813050307060507121106100314060705 69
    0x140e1241c982c0c03428548640c50700e511203548195041141e64920b1503002c03c00024003413148844007400c1c6c1c1d50300c0959a860103490031500079004042051424030f46031300541500449840081e41d44981c66484900d00b2500507100310f0990f01520762540b2a00e001c07103100028040c0ea01d0144641c0c24401b4045601c098041d042c4a4110850305148078010340290681d903201c9180d40b5081a99070190401914040c401e00081d10507031004000070844069202919010b9201a90754a0728145182c55406498902600721410011803c2e05a102d6000010403a4174407400b81c0c103242d194000e0880003524810240104442c2c0741d04000042100303594007190001212103011040d403d06ea51400082d006010003103000f036000000c402108203000000b400381c204515500d18000d1101d4a80c0c0c1015922507244c8100f90000c1e808000f580002504909404100255030906148907121072010500b4071804039440704000100706010020721003090390a030034061188002d42150300746281d00405522a0303025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 381584820 1250 381583570 381583637
    0x90e0c12070312210c18060e031e060712060302150301090507020a110d0503040f0e1806041e0503160506101a07080f0f040602010b04050705030709090e0f100f0507 72
    0x1040d881c418051b004030900c2c1814003215071030300c0b41c640f00013521842107964454024403031f50810205201c43c41c41c000a000000100500007a92559400c4402000c00d404210340c4640301d0300c0c000300580b07420000040d0f40700d401c82225204d60400d080702080303442c001c042504551054581c03074085950752000811140c07041e201e041e400907031800e15a00e07600ca95030100c0c88034814080009216245a0400c0e0300510490202d000c02d9500214001e54801054402801080e00225040081d02440350314a900e18032803030a90703003008811202c0320b418061041042e00d49401200c02c202c00d0740c82012074040509000038244075038440a000303420883c0182c5000614038030780000d440c0401420b0200340c0d41c0e80103c02001da0303a07881d1940780c028041d25181c8a81405a42460082203109024500b942e20504084d91a52059031420200b10054014049000c0a83c06104400d162820040c0050741142d010325402060304050301d1f9810f0200d0320010b01c2c240800c120f0386401050a030b011365004480050120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 381586070 1250 381584820 381584831
    0xa1211070b0304150506181803040e01030c0e01030804061b0503070c05040e0a0b1302030109020901151e0c061a0a090204171f050a06050607141005060a090e0c1207031221 75
    0x240300f9006812340580204900c408a000100c601440e0300c0385050700e20824142400301d80d41c04a256180c4003e000c014440e5601303101c10300c0b5070340c895001102050118000402014540c1e102e1905660007014250741c8415a8403041c0040d081500805241c0140000105102c04403610380c4030140340040c000c0310011041c2003145042d540d09412120203150001c01d00e41207960358440801503a5000000800440d030140400c001414000034100034680b0b042e01d400180509940e9000000c14240240040c041d0b080a0301040c99268500b8040243c80882e4005075224100004880c1300c91016180b00c000c1c1d0303c1900c0c500e01518581004201c1005c2d01d4501050316190010648080c0003142c02c229003100c0081040c105100441c00c4200001c1088000d039120b022049a1082c19100c04907a21070b048800c100e0208130042c5d15038012925908407100762803034644001d00150704c500907444040d2466022040600038030820300903038101d02d0a541054030510001001e40303140003560311108104aa07480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 381587320 1250 381586070 381586081
    0x712060203060d060c02030307080a0207171303140d020f07030c0b1309110909090601050a121e1103330c0706140703140105030a1211070b030415050618 67
    0x3c42d030201001c0da00020a11140c804000f00075a80d400888208001a5140700403918044e5244200c4040710b8211712000340000e90310f03110740881c1d0300c11111103040301300c031001c0040854203079600c0403c89044c1102500200b2880700000345809a480b45d0800d03150000b03c0100002a4100c091100f02c0b0031076040140c984100c4e500d251040b180d29401203043c241405242004a82c848001b41003251088500003400d440b441810b130396814003401084e8002c25000000d2119080c20844109441c0c850b44103030840000003c131198044a88207800c50390141d81481d41e039200d15052054110400500c80002050640e02c1095a18a004681060910300d941c0012485203007a0101f15070340c194000741c0c10700400c07000341c1d01c0304410700040b104100001c0c500060007060100c0b0720501e5040707500c003e00800608800e03458800300782c1c1c16008420309024954804603940c4a0074880800100ba0381c1d84001e80300e25003401d10002a040031104001103901d401d0401c0465510340c02c1d161901c44138480d003502c0c2d50381e50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 381588570 1250 381587320 381587329
    0x3061009030804090606030e010b130e070f290a05090d0201050d091104060503030a0e120106050d0515060f011b0602130305030403290a0504170a02030903070602071206020306 77
    0x1075000a00314550000e00802c810140c0c0e0401400c464440da010400001079170015800c0352442c5400d9070f4000250032000051002a400c016000c0c01c045050f0303042c50f6030303500703048002c45945c0e8040e0f00e1400b4644804c6400203180403006034070250a00d46240750901501d0300a01034803a25007550b02c0385298440070b0341036900c10b006507a0780d06076918040019000a0400224083c2074034090303846141000808215404c0202c00e50350701c000b0a45828500c01c01c44400c01c004401d400f08040c99a65035100d000500e0f65400c0c00d409000d030300850140c501a440000038658000000342864069850f044081241da6400300584218800904540200703403464580000a07100e811a015440024600044240a0301100600482c1d200d000142b51040601d00010050b01c0d03030070040500000140f00184145185170441c81e8098820008984035901c1d40c0e061442e1604805d0394800103078004540c0c0305403070901f00b00380c1016109070b000401099103402c5180203440000440108081c2d004008100c06889 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 381589820 1250 381588570 381588587
    0x90c0328090606060509030304050d111507120c0308070f02010f06081608060403140c030913061d250315060203120c030903070b22200301050c030610 66
    0x503180d40304060060315a6010050180d00000b91080e40c40c0400000d6024080c40460b00070440180155040a1070601001803807030000105030756150a045410b805640e5640580e0000c7c134514880603214140c030704040300144c140c4416002440b60046141000c03d03006180035510004038134000d0304c00ba508190481c09000c0603000507030401d0030001c020503100c1002c501c508021031b00c03901d548a03082c2d5640900f030380d42e00207a0f0003070085109000c030700d40e1803800c3d0320091032000650b0085074a0642e07200081038410300c000d4a04100190354460900180d80c20506101c00840c400b0034501c41c5040550001031850b4503000750002180c007180d2807030441402074001c203280e929000c1c1ca040c1c1c9142d4841c8042e4407644107031311003101d4120101c00211016140d0084d40c0c02103c080c8000c5040c0704440c0e860550560010f000b040d5841a0780e250200c616003c1c3e00c07007081007841600c201c140c1c2c04031805003989140009100604c00e905186c10002c035034441c041542e0b8040030454251080c43c0e0340341016103590a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 381591070 1250 381589820 381589861
    0x4050303073c050706090803070201230103060e240a18030e040b0406030f0c1e06021b06041806050f04091509020a1701151205030a08071b14010f0b090c03 68
    0x6081080782001d00c0207d002440c4a00d805400074040c09050075580c500d03402c1064100308001c0041001407001c03d41550207401d0b007480030001c50390008403207004000048586a09800075440c84003c000402c562f03070103415200c0810541104102003160b5000d4981c1d955015210b0091769241d008007000d40d10307504200025500b0126480b948402400d04400e00c052034001c011601c042a9402602501c9940b141c008403032056000c7c00c01c041d6580c5085044606804c0000d90200b0305200108650f038000700442d00340f1050103000501180342030b043c04040d030300c9194072070b01c11484c01e038030322000c22101461240701046480c00020031111074400a4000b001a400c14004407405508401483e0b0b0150f1060780320300041d2442015690f5a410403a480c1c1e500740d0802022030300f051140e450298083c41c1d1054000b451800d141c0010082d841000100c18005c94040d903240d14150740340c03d10002c0a00c41da1800c1c2060750b406100c04501000840c0303000d10050049084030714008006005410400141c2e018031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 381592320 1250 381591070 381591083
    0xf04020c010209090726040602041802091e01140f070b040b010617100b03181906060b072301020d0603060c1e020706051605010504050303073c0507 65
    0x40c046919018002d400c122426406040800c2c081402d2902918051550701c03555203001605160f00c9a00700e12140d0013030005c5170059002d02000c19010a4010000c9507501000001038030b541002c0e0402c016070301e03034443c0020311202038031008400c0d0342c0c40309404040b50201c0140d942e032403100360b405c440c0382d208054029040400d45414041000651050141200c440d6940d54000d06082244128801c80aaa070307140800d01c2d400c002c01001d1a13030800b443d48070302d803000761b5401400c007441100e09140e0400c400228a0488119503000c0000310311075070b0068507803038003020b0034a02195915101d10300706590000d07189c0d07450303042da402d200c43c00d40403100f51101c1130005002440ea68942807000e40b445200f810042040050103a04a0380151342000103000660700400f2030303d00d0050107a0f155800820009100880190a040411003d010f454042c0e84203000031039480c40c2c03460b001004240d4036080d80c0440c2c6505107064186000c50750001d04d1554955019042d070041504044c0c42500c00c040c4010481c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 381593570 1250 381592320 381592327
    0x50a0e031005160311190c020306070f020f070b0f03040807060603050a03030b0603060a051203130b0307200a080a09030506090d030c020313031106041e0303030f0501230f0402 77
    0x7207030040d81c040c0300036403041280b400c42e1002c20390903202001d40c46084544140f040780070741495070040542d050842d0620241e1203086401103402c00c0b800319021000b2030106104010843d03410450603650090b0400030704802400c1203043c16262164101c000400040480400c09016643c0c044542c0307903602040070400c2c50303a640b60560300c5200e00e900030b0700403a00e8010f0020250820004403845514001d040c0e60b941400c00c400c01006400710b03000d0f0b1000384024407200182c0c180180000000d031000b8003005480e403514540040840f00181007011601d0301e0900040107030203002401e444a281d00100598440290400841c0d01800c83d6102074081e208031828030411103c080744000ca0340a643d54107011449204100faaa00e00c40c0b00c4a00503203208aa404001280c034144074032580c0080201890b29099407600d81d0f1407041d00c0c000701c7c1d0184410100d41041010340620030469030004050013800b45600d4000e1012201a100490700c0e0704a481d406d650040381d0380d12002145540c0000e104649 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 381594820 1250 381593570 381593593
    0x512011515030f0903171008010c110105100e01060813020a0e0f18100b041407090810090c0915081605090916030210020312010b0702040c14030106050a0e03 69
    0x2903100740d40c24480402d103008140089820580645842c0d01d800d134882804000090040a8040c540102030381da0100c103820303002c44c01d08801c5c0960010028144d0350058001d104080082c2102d01c040c0440342c0c0c0450841042080048012010341101d04030b04ac0303200255111488034540c21000ca02c001d50000394201e012a01242c1c0c102003a00842c0c070340071008000e0399840502c000142c0310211883c081c0e0f0110040c403130760620310341002004150140000c1100c41c500050030486d0b07171090f281800460a010414007403010204040949901c0340b49080c403440341d036521040252105401079820581d29002c1840d11395541410010080242c079088030001002c00601c503103202c07180c0c01030307a110f0b144000106041030400905a00455801021800c0b940c4c51607081006509604000009500060200042410032401c20038002c12184045980e2000103204101c11900142c03e94001c1c4020754070f000d00d2482c10756043c0c906454150408079500c89054000b0342d5a4810105403980c10b00c0780d42200308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 381596070 1250 381594820 381594839
    0x20d171c0c09050303090f010e0d0b0609070503190e0a020904060c0f0512010b03130507080601051f0c150e16090b0a12030509150c0d080105030d0905120115 69
    0x48800c440c042040107150031084031058158450075130701d60f10a0120210b00d240500320002100b60504142d0307011110b65000c0381039200112400d40d200070310441000490305182d400582d000c0c0481c039260b0300c0c41c40c1003105140b003601508444c5006a9440b00c00e144081c01c00c000101808c1e40051410a0320728107440c00314090703c1c102100d903000544e03001038500428064010740319101d01c040e00d049200d82c2802014982034200a05840c80010300c200c4400c00300e5014407481e07010700f2407100034110543c148070500016400805401c14802e00a58070210300550160f9003515041e4400184406610000ba07400c0c050029400181d600307005a0303d40001c1800c00001050440b8003442c024404548080c00700820994644204910315042560741300000340320700c005101c01c8000a00040141064080d0083d850b00885000f8081350f01400450b101550841c0310305004000490080074542901440202001024403400e0b0040b42080c52400c8515829000000c40e5200480c2208419540d01170342d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 381597320 1250 381596070 381596107
    0x1e0f27060108190302060c0c030714010c031503020303090909010e011404110102030309031c06030b04080703170c0a1803052d1207080705100f060504111204020d17 72
    0x1082c0b00c0c45070040390b1014080903402d4054854240c0c014120035507901000341d01c04d61010b25241c0c500e000400c81400084e00b0004c80703516084990000046064003c2e20141c110b80c107072090686202c80310902000142e4001003100c41d10042940d144509803142c160303aa000d4242041c030642030b54200096a258030001c0100356200d6801070040550340344c5401c0041e6140c0c402a240c2280580080260000c101071391030441c07911035010340c000a0100e503207032620040940c0540e003c66007020300090302c405142c5d102441c1d000345a2000315101060900080781200c502c28071404000380a034500c4e070300204080100842000b940c01100341c400b04151800240840e5821601d502c5032426800320015500390000354a171204501004024502580c5460b801d0058206c0760040300c00740f068404400070015103010740400481c0300c0c40041215401d0000700410b40c0d00e0380300c85000800003408004903a0b5200c480240c0c2294041d20310044903000c605102046104d003d039180100b440000d40c0d00101803000020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 381598570 1250 381597320 381597329
    0xb090c0702030c0d051e0c09010e010602100c210e0f0627070302011b060c0503011802090906040b0d1e0201030c021609110417010b01081e0f270601 65
    0x545500111900c1080035070f00204102510b03a40c0100c2078a00440241780e03202c5004c2c1c050b2803c0b54201035000300012034008e001d801002c001c0f07604400400015404200314000c0007002002030048080c0a9030043c6070340fa030f482000a5040002c9680c004c0d580c025804500000c2c203140c240d070501003451424581d5100b06a80141003443c508140f151a0800300390202e4501c41c072080580556403440c1c00468110031000304849244002990b1400060641c0c42140c00c014066141d0a44170361510307001100810b04100358501e440c3c010001455256120007240340c0c0454111000241120441c0c049201e80d4004000100010552425218407840250503940e413141b00b680e041c804c600d1090320403600d644c00b0082c00c007918040c0d404144440d0140d9004040410700940c2107500b8250307070702040201103883c042e0420701e59541d454044c1e115640b000725194001c44101109040c0030348444881d50500005048076903501c82400416991011700044c2510400400320701a02001c54100c040c0d110300080c840c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 381599820 1250 381598570 381598573
    0x20d15150f1505032214011805071e0e090a0f0809040f0209030d030903030b21060a0b01140c070f14040606020d05070809150f0a020f071401120b090c070203 69
    0xb100c0c0c000740d2003181100c1c8078104950b0804600c0b140310307203010003440521004481c900d802090000da402e0003403090303060320b042c00f01c008000c082280c240781341003011a030001e2141ca02071035100b45804070584042001c40b800300d0a206d200e5a02c0083c3d050070180340840c0102440e120140d528107212004010b09494001150b0800220841c070741104224843e0340c0d0004d030190000b5010101c0e042c002d602c0103038401e0081c00c010482648813000201c075995596103c21101501299180305068100a4141e00a41c40c1c042040301443c80b000107011b04036180140264030400241c071105828003032112200034089074111038049501e810549040008c400e18081c0a14138044000545510016801d5110140d91b120355240418503221502d03207030700203e03d880d013111102500800565007000100944241007190b10780300c028402d002403c080300f401c22800a035010070350901503001c00201881d0140307000d013006407101382e1280716100035084141410342c0c020722440400c4000000c070401440c13000d200300d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 381601070 1250 381599820 381599849
    0x80d0801092304030c020a08010f0f0614061318020309160e0114031204080105070906030b060f07061b0306090608120f0a02150403091a07020d15150f 66
    0x5003400c0032101000094100d04403800541180d076282c1c04900c81d049806450f00740b41003c4079402007416220254040c1210341e41d00d4110951505281c455041d5031a40c1d294180b040038900588802c401240d991140d1084400003150844007201030710103c020041c2011030083c0c1681d40442c20001d40041f507000b900e0b80560043e5610401042d5500015034142480d02c0301c10789d0800900e540c40a002d440b22503054401c8100c0400c500400d1005400100401000410f0f50705c0c1c030060040040b11645c0c030100600d810300403808142d41d600c07400d5030304044501c3e01d040d459240c02e00701500a0908003945003254460704003104206c944c590480c40c255101c04c1024000281e4915180b0ba50b14440340f5200c885003014000845100c1d444401841922841d2046803c44a02d8124007425840243c1d41240810a40d640800200400000e43c4030b00c024100e00c03080c1445295004220380000c9110000c0c03c0107203c4c6100c4080c9160380e407002209003001c10540701c03051b40751403030f01c004d150503030044950004901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 381602320 1250 381601070 381601079
    0x6060d09440901020111030f061206040c05011b06140603010e030a080105040c14120a05060d05030d0e1f1a06030103120c020a05042307020111042c01080d0801 70
    0x40d42503507840d01e0454088200940440009002904092003803030455494612104160302100041c50282c88004041002c40c1004000c0004482c1440d109100300d400c01400c000214141e107010700200d6a0078203181ca018a0385c24100b03808140c9801005240504d0590485910840300c0708546c4120303c2035008004003e00c03100300d030781c2d030b40a03000d0900000f43c00c010043c0114200764204480c80d030080d080c00c3c545006144005022500308004450014542c1e07010031080140c0c6004042d00041d0035070f00e8900203c074940f240741d100e2148440865030b4035100c6004008045080041c403401d004042211a031020814007990040d2441d00c904c102e01c006000d07080200b81c54400c0860b41240d44c03014624150f01a030140980704c5a101d401d082c0c0e400080c004d0006015103890148100c217044a0b414a5031540d206080b4031182c50780030b4908070843e850b111000360101c070700c441241c00707441112030310b04c0302c14001c007942035400c03170300c1d40314030880c3d0000d03c400024001400a02c07084c1c0b290725510344003600e82c0c1303c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 381603570 1250 381602320 381602393
    0x2030c0c010504210c0305060108030307031a0a050111120d020a030605041b0f050408031b0609070315021b01020a0302130e0702060a050703020702280b03040f03030506060d09 77
    0x21030041c04c4090540c207000301039944001188850844c452a80030505503900d0329114100344099000d00c000350800410450215810702c9500c4010701e42d6400641080380144c04150910004d004150500c203100710024159041042030030a05909080c0e1166507103a5810440046d42020031340d980424100100810030707281c5070141707910714001116aa501d0200c240d4040b102c42080700e00d04400e02504100106a0400a00060070668041c040c43c1c41c2c1c51520b800358928044004003040001e800400c42030002070721400c01595081103105c3c01585902a0010500c000b036214007102025610018418080c01d425401810901d20040c89100400d80d5a580940180c0021a481030040e00180c00095038601c40b503000e540c00c40c1451500606221199001c184ea0304211108062158039900030360081c400b002e08040b000c1d04000380d4a13400c5051580d10304c00340400d9100000c01303151b110302c00a012030b1900380c03d440891914000c00d0008503d80e0030040a85081c5107a20340c3c00d0b0206055501c1c41003076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 381604820 1250 381603570 381603577
    0x40f050a08060406020a09150f1716030c05040e1005030d08010e04030f1422081207200621010501140d050c04050d05060a0c03270c0902030702030c0c0105 68
    0x315003001d00580c0e502c84e52020000d41c04520700741c00b030140c80d440200326500030b541000c2e407000c07164880341e10045c0c189070060708401803286040000c0d4461410044035401c0c540b8580d001409904002c24400e000300c10545181c000e6070440071003a4002c2080001c0307510b0641c1d4413000c580301902620178620172440101c1d0320f034209002c0d02685621400100340028844c0b010441900c0c081c3c03401d01c46d400300d044600800d60340060341040044060444003000c480480007440024100c40c00249440040d03484084205e010748030000c1c10080410000301e07030411345042c40700400080103041a50310081e030030003000600545038541c090042624004155075005003102c6144d031002c04446408c15944005050140c040202481b061907414000001d0035294184003100c0c0c2031086025041c985072046a4408a0b110181148205400c0412070801c410141d14681040a0300700075140e084220303424010858081d0760300c14420300b48000b0421040e03550210151495003c0a420303606000c1d00311004403103030301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 381606070 1250 381604820 381604829
    0x302030703141e03040605010806010522060e130309080c09011202030f010e0a02040b063402060409020c100608060604091a0709030515010605030f060420040f050a 72
    0xa0042103903101107030103420500d0b000c4180005040c505803080448040420040800003420b0780c010050004128280c0205405040d80c00002d008030340c901000940d4000c00d01a0804004d82015004140041d254011300043c00c0b00c085544868100b102c03070912079aa1020041d000109161808a014400882d104040d0f5034010101ca000ba428540100c113022181c02d0103d9240c0310740211003c0c0c0d06002c3c05200e0300d02e6078903001380ca0742003003a00510041c0c0d80d820510501c01c2d101045407000d00a0300d900079001009444c0c5524501c011010680c1420088003030010f9171100c0049000194614203800a01c1060700c0203050380e440c502d05121220581c0c80500802c041d517081040020314600745540104256401002030001d031041004441002c06000d403525000124512014010b103c402c1052607600030b8103a554070103941c9001002885800041c01d0310901000700b10102d010341d5255045014446800000710004600440c20110603500c81d01c03400207800c000110000f0b2a00d00350048100b01c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 381607320 1250 381606070 381606073
    0x17030a1107060e130902030a2109031a04030219052a010e040f0b04020d06090506030a0510050402010507050607030519060302092719030e0f031f1b02280302 69
    0x1821500c04200240b2408009000d00603035170201407000d698200f0a061000c2d01889200c11950007c005009092296040c3c000a00500c0442007000420f040000079640e0400c003407103001a200c07803600b2410220100100d011409180c800c1000303206c00410103841600c2000b044c009084804c0c1d01807002d0805610001d8003048000d035160060742403d405c107095441d0b07040c00c0003400900d040b002034207c0c2c0010440340d112640c5da4070300f8089600f85100302c2da0081001ca0050041c540c0554503240c0c0c44401c12440c1c58004d03180d101050459001e80140c8030700c00d5104003550707114a8105070040040000300d54800c1c40c0203001079403148110300c80c0300d401d0035070b40c000d0130080c1d07030b9541d504c0c59104600d0614000e5141550321161070031032603801e04c800c403c2c200c15104c1035a038980403030500410580001c05218414100202d44c0240c5517800241d103d0010304514005031440301c07a008000043c410703905c00e403111850b0410030032122a07010401d1110499a13514141c0c0140e001d102c0310012050406005015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 381608570 1250 381607320 381607337
    0x10b030d0306360f270807060b01090b030a0b180c0f0f07021002250b070303050601030f151a03010e0118090213051e090c0d030917030a110706 63
    0x103c1c0b4a140d18050201140121900d44896001000d01211001c0c4041c1c074080d944c1e9808a100130490441004c4100c240001382400030349140c40b40581441000340c0100000d96401c10000503034059a1000001c2060840080d00c0f403415503406c0002e02900c5005170310030280e40c4002600c0d20321145005008211070602941045040d488141043d0b02040c2032a07c250000d1001c8401669401c00b00c2c90580c8036903000d000400c6890462600a41140f14a14849070385504240500341840d42900c2da140d80502d0003140d11348900005800404c03c0003d001d9525003010f10380814040c1040a403411200c0d43d603c08603411210500800d500d003c00c0c0030311741400c02c0c1c600040240e54000e00440054854511001401c110154000380c110405525915401a10364003005410b03500c440d103060f071140f0701000d03424071860b100704455113071580500103901c039041c01811a03060500c240c000c44080c00100d59079204400c0c162110039502d8004021000c009019aa101071190b08081340060031600162160b00c032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 381609820 1250 381608570 381608609
    0x110c030f1602030d171e1317070501060303020607051c0b060d06030b10060518121002070506010e060105120403031806060f080f03040e06010c062301050a080a0f0b0c070c08010b030d0306 82
    0x441c950347c4d09090315030000407001e8081514814004004192081c800010507030701e94940270b030501038010441c00034042c060142001e00e907503480305c0860343c503221b400c0000d212100f41b0000c5c0090184c0c03214810404d261100c080100080104001c1c02180008800d80300c055503010105c2e513078450500000c2d207140700c0c0700c80285181000080b410149041d81c05030f0f04407450303110140c0220307005801e051311154090001000240a41040c980d000f45082c6015450038181208281c0c000360058001400c040c0e80d40d0611b0315013141242c0c410703e00c5034003600038080242d44040e5002117400034054044640600e0703040070310141001044a08a9a0b5048401000e42e1200c1c01510401004c000956074142c484c5250074410707042c04161880c1d075007601074028003035040905218181238543c0069100e0340c0040b40d000c2c0841c80c2c10f01c0408a2031792041fa12503080c1e44031220030140d801401c00061410101d00307004206580c2c19080441d4104003034044446c80c540260b0114199005886903202028400f241e040d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 381611070 1250 381609820 381609841
    0x9010c1502070b0f07090e0f0f0a060906030b010e10031212090218040c0512030412140d02060a0f090c12210c06110c030f1602030d171e 60
    0x30812840e401420002240c0354211240d008031522950340560b5020072200720342009401d005400100c0a0070924a08602e042a5013580904995181500e480c0000da0000440e00581301070a44071034240700d41507892400300310305d180078080e100003107102c50f000811843c44045400c00300c1c2d820a007043c940c2c20501750207403183d820684400c0754043d1100c04200241c0c0340d02d2243c4400002d041030410440c41e081c1030200244443e030f0810740c850001e142030241c580d03100105680035070304640c0d6034071a582280d2402d021042c003180740040060103400181d82c1d07a01e0b0041403044c0300b01d00d18001030054003d01005081141c011000040241800384000d000c460748005450905900c00c44001804402c1941c03104000f62942d49000005a80c008407034041228a00420041c0c1510340c4003e41404050001b080c1c481c0504002c1c0c500412000c69240f50111148180b0f26a940c0c001d01030300c0d240b9511010061130829030301c5400e4210310400012440a0840031017400758201000c40200741c0b5101c601490 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 381612320 1250 381611070 381611093
    0x30a03230d06260d022812031401060302070210030203070c060f1a030c090723040801050406110a080c0310030c09050901150e060603040314030414060c09010c 70
    0x1440d0390034003445464803000903485440c0c09045640d000a110a45003118661076050040141a50383c1150300c180d120540c0001d10b03140c1c45240e17032200e0b160b542c01c40c007609074000c03001c5080607108410031900324145a41507031209442d0f85a0446c1d40201780e803105000d50503445600f0300250806004040b4814852280d40550740004081c41c1051607044035460340c002b030b55280c480a14440c1d0740d9070050002c0c50542c20004200c54001d030043c0185c104d144000038200a001003406050188100d864483d81204a80c00d08048443c102c40c0ca4aa0740c80b048e81c580203101c220f4081390b0b454540901c0341c4c0c10045940680f0118002c55403818829071714003452280980000d00010074082071200b01000240a04186c000a003022950008191030041c0c400d500b52442e40c203800901458025050000c140c0300c0d101107074800702c2580c070681e07240c1702e41c60121002041555000c2c01c40402006000800440340e5040f00b05030000e00031913603107859801340f407225441b4514045022030300c034403ca03100003200204030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 381613570 1250 381612320 381612377
    0x60203071511070210020c010e010e060304080702190321140a18050a06210204030f03030519050705070614060310090633080c060a030911031218030a03 67
    0x196040c0f4120350302080504064011040c00758012100801042d40d200d0300d80040340c0b100b4a07010704220461000b055451201400c00f52204078002040001e64496010340a4400c3c8001c0e60180d480307580c0e04115010701c4c45088101c0d1000c3c211180f007081039108000007a0f2041e131281800c0d16012000506450742500001e4412481c0b8800500045598a0004407401003400b0703122503507000b002c0c0e44440800c1c64202c1104c0040d41c03043c442030020415400d1165000c6031b060a00041a840c5c00550200d2002c5004d0381c05038407420b1900b0803001c1da520801400340c00d84924810300000c40c80303140e640840d4000712440c64065214440342ca8098a0030b07000841d00a0103100b000445003078955402200d012501c00344c07040d100891410740a45405c9091000040010201a00d030340c0d480c240c0010b00034404c002c10300c41051b0725101110b0501c404086001016240201110700849201d8030781d48072500214581213480c0c0b1140e01d44821401e011507100082540340d03640521820400044000070041c4402c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 381614820 1250 381613570 381613601
    0x50904051218190303081b04031b031202010608121e0a0c031b020108240406030b10080604050705240d0204150e0d0b0703110d02090a0602030715 64
    0x103081084030068008000862869106440c14166107041c0a5a03ca41c10032440540040110030004a6804842d440d04001c41811500d10700307071024070040650040340c201038a801c61590f0350820036040103044000b100d200d0329408a101c0e80b04501a8200c80c0f15101d01075442e0820902480001004002071003410b13110710b1203ca40359002031003061290482819613001c1a040510b2005040c4c008101d180d040d823401c6661280044103500081042034054084c5119080004174a040020a40700c17001a00c40003a00c204000d607075078113106150341d0007a240740341c52340354101e00801c803006c1c003042c0c0038400d40e00300004040300751504c414130010040c5015801ea1410103400c00c0701a0003080310090400d507650040258a95003800c241686420b49007680c8414842c42c100154502d480703010390380c00451b802c0508908555140b030701c19009441c0401350080710392000a0805d41100d9a41e01900002d102620b031f00d5078884d04d030300d0b040c2c2e501d208506018154000314689040543c038903806c0644420f80204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 381616070 1250 381614820 381614833
    0x702010207050f010b0918070501030c05041203080f0a021815070c0608070327020f03010e0d030501030c090b030a080c010b10110115060c0204111e030f01060203030c0405090405 78
    0x1140c2e1410520307040003800d0300365100c20081009103403207061141c00901c01000c840140461200c101e5581741c039440389078181a20b800c800c0340d2041c06002514021b120742034119456036100c1c40c00401c0042d00704c61540c3c1c184981e0011a1300e80300305109440e4650358010041d410004101c1c100200412000c00c28000082c0030000030000070704451070000103080300e46610b02c05081150700075060b1a071505110344504944840890f8111108460382e001c00e40559928040c000ca16000c00d000d0003001d042210b541c03103900800e00703915034941c1c040307030480740148a10003d5546900c809000e07030306070422503039050380a4a00c501c04640c00400508004003144000111101d000b0049502ea0402c92a010003060541d02c40e054905001e008000010210901031030000c0e0405601500030416641c02a024030750741c00c0e201009040c000212181855980042003242007103814011140d8400c03a00d43c11002d01d403200014690340000300303403070181d007856003903d05150401c8144441050024411356545c850300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 381617320 1250 381616070 381616073
    0x50c092e062705150c0d0203031506070c0b0f040f05030601060801180b130b10020f070b070804050a15091202060f0a0e100e040e0601120305092d09010b18090702010207 74
    0x1c0201c8113214801d00700f015160359505a2460a05401c14150010354004004100c0c0c4000c103581d1080b070380c80c000c8501c2d0782c98001070300b80b07070340c0d4007080340c005d400b00303580005060480c1d1003400050402c8a0294000207403071030b241d000f41515400203204510100e00b103040180721f0704150b17410f01801e0340945031000456111010005410105c42980960141d56840d480481e600701003110003010540c0380020801c080580702c4617681c0c2c401c5882464a04500803c6200030040d0900846000b05001040251511385408a41c8442105030704039101284004000140f00c0710354100c2c0c1810103070024807503810041c21040d03d0085502c865a00400c1142106031820320380c0d6100c02c1604080280e9680d41c010b000510300380f00460300b421002030b40d958000c0c401040f0102106a00000301c03a131510b4150748034200c11012070034940301045500141103441000072030396014601f02d003813040d030101c5288400d41d170380d0384030b02400d4407504544a2540c40d0140d1224068104a11017036001030f80b40c07000502d421b07401d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 381618570 1250 381617320 381617329
    0x20f0c010207060c110109020a03380601080f0903030c09011205071101060902071502071a0c0307080f060d0609020105091503150f031009050c092e062705 68
    0x6080b04540f9241d40758601c070324403980240c100c56800320110080102c141d281d000244004400c0c40000c0c004000d0800c880354818490140049101502c0c80049101d841c114480990000488000780060210b0f00011094840004064080c81221011f140386032980b0808188550000c005a8144103c4000c0700d04c00020900c030304c42c0309501541d00c155203c401201140d0a4800e07503884070000c2401407207288003040c40c402074400c100324120b4006a880302d0ba454401d0000d40c043c0221000347c420351003040b002d003480000440c40f42d4515580c8079946d580d03440b0051030f41c003c15980325030421480807100700040c000d54440d040103401410140d040208000000d42940c0e0800e0307504540410120034080c4229140c920b00490001c112000d040c10020400030a50b5050902c41d84420f05484160500c01d00c617040c041040d500401038140d030100e10340180c00e00078440395241031002811110500c003950481c0481c40f04159151035540d0705a0f0480301408528520001011044c0f03034480c1840010941d44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 381619820 1250 381618570 381618577
    0xb030c12011205120f04060503060409020a06021606021507030c1707050d110301060509131e050601020d140f0913020c0d020610030807080304110a0602061f031203020f0c0102 77
    0x940d001c140d02d00710140b904600304603a030364400c4841e003000c2c041c5400030700c0840c0c1a00e00352141c5207401a01ca07914000014090200c400003c2d40000700064003258007503010a020103081b160464142c0a560b442400f01d1b560707050885e0b04040500c035000891701c04c0d84290015003054666107413000d404080c03582102900c0009503040401b055000820101c0c42005024102c0300d40c04800c00725085600d002005045882661292885820701c154810036a20072035019140350001d0321310f09610942d000140c500208030554446015200c2e117296044294811200701108030340001e611414030344686c104d50b9240c3c2010f040558804000407519200e4120751000c1c007801b1031b0540c014180410362220280c200000904802021080814280042030104084038180391b405480f05a0341d41c1c2e24106005400525a40f180c0e100a0f000700005506030300184050280c091101d40e010040c1030502c1c010490700851000400107151b0700980c8802601031382c050401c0a404c491028603250708150900e007241d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 381621070 1250 381619820 381619829
    0xe0310050124020f03030604090305210f060f0f1320120c0c190303060e090106080c0d02030c04050c090a06110d030207031b0219030602030402030d020a03090b030c1201 74
    0x460040001804000c0c25140d18030600340050004131001048141d100c1c03100400c0140a2525004004205441502201c410a07105000c0981c04002c07140c0b2661401415660740803002e2240010405901d0919000e40410700b0003000f038050300c038000301170195801200b11150f1a082e0748900781c01c4554555142088040301d02f10506648280c0e0f101f001d81c1310f61020704982883c61041c00440f900181c0000c030308042040004c100d1002c0e1401d0319007203024100e50b410404444110809000302c01d041500301105480d03464050f00d9200c081d0000303128000390503003030203541a07110040c0ca9140c3c2c103081d40815080415088041d01d40400000031582c025034039489207002680c1001f0389a5070003010b01c403006041c8600d25056180101c19100203059082d411008641c0c1040307940d01e41c0c115a07402c0340780240440c0340201c0e103441075600c2c144140250811030f800c0c0d01a001c0e181c84400f420f8070109100d00303690b40c0f585500807082e081c808244101d80006198250000040101819000007840001d0081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 381622320 1250 381621070 381621089
    0x6130e010209031006050a061404050a030510050906070e0d0f08070f0c0e1902090409021c1502090603220c1715010303080a0b030c0a0927020f010e03100501 69
    0x420052062620b801007401c94100d003186850300034490303607481f52240801c91740e40b8500419902004158015a8031036507100640c000c50702c020000411070045069001100b01a50800050307444040694a40b1b104860b10000620b101c3c0d00c0340c4943c5041001c0d41c0015009400040c1c05a05031394030364240c0c0d80800c80c260341d000500001402004200100032014201142e102c000d00c1c1009041c0744181840062000c24850700030510a03a01d440d6a4800d40c0460340041c0040c0b01543ca8004605221222460a582d00030360140046420300440c02180c00b0700d04003070304183ca11342d03070384c0543c8028030f10081650f000100c1c041014004101c0c81c000c0d40c8060b05448819640401541440c145020100142d03005500d543c080104007103a0480d5926030701943e555001304039022941c000034105240c3d0014958000040200456024420b501a82c07041c90000900e42504980c0b0407040e403841c410f204001d40c0309501251205180d40f240711a440b517208058101c41d520f22612860601342ca4007600214542e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 381623570 1250 381622320 381622327
    0x50a02070504090609351b061008010f11070f020a030609110405010603050f041101050c01090506070e1507020609040b0d11130e0604080f0c16060e01030b090a0506130e0102 76
    0x140415106d1484202c4112410003042070b81203e040c20a08030850164900c102c00400e14813100c0c009115108400442c1009a84281c03170304154040780c3d1496801468819880e1002c030f030f401018584150308214454154250824020790344464030070a041004a070405100000040022900d01444c2c040c80e10a4021490810b0403030180400c4070740c141e02070b01c101070400060041003c245400203030010780000041c64200450001a0740390311500c0d40207000c56203012002e5041c04804070701c01c3d00800490b512000c0c100c8129080242c81c1a094400b920662030812080d0018a02003009220b0800082c2002c500c800085000034a5090540350980320900d083d50141e03010314110b0310f44c4001c80d209071010003014400c5603080d580c5580043c4000c2c40e9000001e0351a40d0312a110050700e0103940c104040ba540b542012a101c0c0c000c80040c42440042000364101305481d40c06800b4801d0080c03c0544a0030580e0313682d03041c0074003410380644400d41100980d4044812141e41c1d018031700403015042d0000d80d9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 381624820 1250 381623570 381623573
    0x11090d05030d15050d06331a0c1005060d12080412030e030f07060f02070f03081b03072f0a0c1401020304060f030e010603151505060901050a02070504090609 69
    0x155030f80795203030440a1031081e20034405541d491100710720351500520002191003401499800f46d64185140341d01c1c1d851030a5004003520310300f2011005985410141d108115045404c08013207014000100300d15821182000c80006643c0e0b002c25030241c0c00800e9401034220741e485841e80340ca00d4901290018501c40104428000f001c80c1e440c244080b240b07000c2040f92440c82029440340074581500882e010001040d4061102c0d54112030000000d2000865aa00c5c451174402034102c4159401c6010a144000040080c04040d20080c2c8070030040c2200c80c51940d864a044410401009402e0044ca00c1425a4a016a050010980c1880030240103000440130303800c001c41c20001070751184c0c803003141071a04113490f030340d0220513902241c045080c00c40c2e1000f24140c00342c000e0103041c14410200d610b450f100005001c14500650750082d038064082110724004005004c40b0031441c01240d820910401a12031113502c244000c0c0b140c1c0740c1034810364a0094468000900f612401d10b0146c44054590380d9110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 381626070 1250 381624820 381624847
    0xf0311190e0406020a0f140a120209060f03010312050c0604020d0321020406031d07050d02120f1b030d17060109030b0a02040501020705090103051f0207060219020705030d080a11090d0503 82
    0x4100f51b02402c02c25100c90455a648085101d055074010801108180c42c0306401c2464059540480c4001e019035240d03071341d003528001c0d141c02c01d10090707079800b29600360159150701600031140035003404005098280d9664080c4500940020011001c1040c0f050102644c08159841488022036000c0050381d250b01e46031004058030b200c0b8191501c1c58505424180e6020b400141100c1103440135600514507240f039000152601690403040107880c0691408041000780120301c4001d405e6000740711704440655582855a151030a405c440046101e0604038540b0701c1c0d624040643c055014036080c08455165500c0b032240c00020364800d04e900340c002c00d0a0056680620056000d0403007501c001e8460740c55034440c50f80e2503500360244410b4003540740001c3c041c1016501124030441c0c10000c299070320a41d102c00a140800707000815401030189590202d407518010645c8400e03403000795940b44d62034840d0b001c03403030040c03404607103d80307a6010800c0710cc403090710b4690a60700941e0181c8044c54a8035600358144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 381627320 1250 381626070 381626087
    0x120c05030d09120504232403010f0f080a03080a0e0f060f060d0312240b0318010507020c060319150303140f0409150906090905070f0311190e0406020a 66
    0x382c082c89400e00044c0070032000400010b030440c0c5241a46d5850410035004a60501001e4081d00d406244007018010903401e010021412644000403a0031a1540c80d9007902110209014102c0d01c0c0c1c0100d84c0e0200400c3c407400f1829000020b03140000f41040d07148134500c2c50805401c1440040b42c0184042280810084489503408202960b94030b101120647d00103210058030704003402c00c1c1d40d843c83c610640b044e6101420301101440c0070084401b03a11060241c40c82e810446181101c801c120b0f0389007601d4107041c0900c0707016200c2500209110000e0720100078050300000c0526a0b12000703225000780c0356400d8000c0c0c01d540080b40840000c0507003141001402c0c04600801508d40c40d40c1009030700032030f500758011142295020340c000105519501c04082555200e030313010f507860505120000c5a0305c0c6680d800000014070640484413101d540e0b2000c0003900c28148000342843c1c100e0007690040d0700b81461a41a110350244007011200d803114802d42d84100e040e81c003641c4003607012074006685608902d42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 381628570 1250 381627320 381627353
    0xe34080a090203281b15020c0303090f06120109021b030a0c030e030f0f0102091c20030712031d120d050a0201020421030305130807120c05030d09 64
    0x18044078107540c0110b40d0300c00800d14500e21407900381840e0f68001e030816140100c0c0710703030010050f582001259211990041280585c114140002c0040e01c006400011400b16091f4054080c41c1040e070034104010141100380d40c810f810840401c5008000f0341078050a602070001100d0042c0c035640c4140c00c003482d12540109040340c0e640100b040d400c440d900711a0001e0841e40c14580313030003007075190000710741040003da8a4600600c501c4455010b0006d040d0060308080c3d0050b1088042d6400420008000346071812000c4c22113004401c084144c9050601e495241e5017000d0100c1d440d031079541c0706001194400713160a030700148d103843d140c0402e11480c100345110030404403403a81c01a100b03100b01d00d0306c4906104034902400b60000300c03216138600030b40549000300361036207120441e500c1505542411f02c805581c2140001d103000001001c6078002c003100c40800750040c0000b41041d80d556102c00c0c0130318a4403948014800250381020018000300000c0c01c11100890002c036241e8818604650348480003401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 381629820 1250 381628570 381628591
    0xa0b0d110f07061805061005010e0a0f1203020a02030a06020d0f020301050616140106060e030601090e030304031b0b15031606020309040b0d050f03070c090b01090e3408 74
    0x452404074403580c00740c410080c1c12410008016100c00000400700040c41c000030880d0045070200840c800403441000203c030000e0300c0d9a200d4140b40c0040080c03144641c0503514030992009000d02c21441c0004940300524420300407164006800e4000a190800461007212060b8000030384011007485400ba08503113010030801541036505010000e01d0034058041401d14011030102d00c003041c44001500350010440b0140208112529440000e010300151803131700d8024440e030400043c20100510910761800018409503042da15165003c555a1030050003814000044642000c0403501c0b1000c3c0502070088089090f01000040c82454184230303010fa003128600b118003801304080c50b0003200f1145410003c07540051807100000006499141542e409010703841042c0404e1803400c40040201249070190311060300050b60703003e420069139000b00000313002503c20391042107095091000ca9401840032103244061015410481d40c2108100000c1e50400c0c581180c1024402e401481d0700d504000e2080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 381631070 1250 381629820 381629827
    0x8270f010b04020909071b0c140f091b07060f020a030527060105040b0d06050103031701080d050a08071209080d060504060e0c0a170c09120c030706030203060604050a0b0d11 76
    0x7000500f550744001c0c0010300380125002c40008405007035800204080e23104007207000141d1622240311404c280040e050b800340131040703018000c034501418840d210b40402c21304810100365144484809410480707007151601c2e1a0120030b10540100d001901c0d0100746580e0004407071601035454400d1012403150007480b4141c520304d00820050108126041d1075083d2404500030460102180340c220752031501421039450400040304060740503820086628842c2c9039200309980f10303000d05440d10344456030480030410801c5414980c500440742070f07034000a0703400c0c840c280c0e40040055505985900804907944240041c480406c0b0340140324040160900346e60402a890626520824100000d44a10230005000c01ea00cbc1d06141b0800700c021041c21440105142400c0c01c2041a00317903046841e04c02d10a1301d4000d8280900540020504985403004004082c0e461800505900035403000e414550010742c100300214041c0c1352402c01c03800030940c005030641d84512480c442c40845151038417580c2c1402080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 381632320 1250 381631070 381631087
    0x150e070807110a060e0d0e0a1508190504150c050f0405130b060a0801080c090702030d0903140a0903050c0a050d031103040909050a0302010b090601050a08270f010b0402 74
    0x411120751064150411501400c1c0e900380302803034555082002010a818a02c9610100c0004500d003040032045454030405a2480004c1003840032603400703029050800c507424010002d01c60341340c0a808c091140380103085841d202100f58140c0d80211000d9030491b00c0c6c4403080214812a00c076042d00f08002d40380c113904000080290283d80d11851203681d11031511000c0e405c0359200b16910100c60789100800180d40c40d00c01b10000307850b0400074410b008050046042ca12500d04181500500c5041c0950182d444e200500d18040c005180d00c2d5001c2c0d04000c0005032085024207250300801c031203903558a81c82d010300c0ca1403424515040d405034140e4090b2401010411043d101da4030705820240e450b080008050030510900c0345180541d50001c03403c40d051003411814402c000c034907101100d00a030700a2010324540400d00c0104401039408a000407020490250241d11a0065035000b40b000da0b00040d0710300d0107200c202540a21900301e8a0960002c0c0010440c62000f44100d59880c082030b01c0540c10000e04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 381633570 1250 381632320 381632327
    0x120a020901090b130f0e090f031204030318051902120705100c080d0c051903060f0512030c01140f0115021c0e2107090608060c1c0609150e07 62
    0x441c440c81c183c880000c1090350b05aa43d4862440142a40740c0d01641c1c4103550b1503103c49003207401d5130300d101d880c00f038001e0740c4101e07041c0030048070019202c003840900c098030386550490050603120502602100904050781c00660309001c103041518010030f82800c0f0750070500422000e803444030807007202c03540000740401c21904e5120841e1a10041800c143c01d458815080c01d501501c1004268800703949400c05030540345410101030050313082c40500640c008075560350150f08541450064176030307000c52940100031a240440510450501120903079007003505000391702d800e4408c142d41030300d1008046004c00038101c00f28280e150061000740c20000f41a54000e03000b80d11010407400088040c084650404191030040e500c45110400c003400b16840c50b490052601c12158003002c04582c1400f9201d00022244032034003c4505441c0140054180c0e920b038112050300d1984280307074890754031043c1e81e03170341c40c018a6511405c0d000f0240c840d03000c034006408519480100ca5590031620340032030090f0030301c07094990 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 381634820 1250 381633570 381633587
    0x90e0a0b04080c0a0b070801080d021e0c04020409060509090a1703040c05030d0906090b0a020705060703032a03180b060409110a030305091302070807110607020d0503120a020901 78
    0xc02604030561600c80c0d040001c41c41c4140d051214240c4181c6190303804220810340401e108005940c0d551780b5507625441402e0b103841031214400d005038490000715443c2c01122018500c041641c00c100e40303031420410003060607a0020790140d0106a6180020000350034494402540040381c0c002600d0a0400c580d00c01000705041c424032401214003000203410401506441000340c01e0007001c440440c0c0360313110010100d8019006400005480050001e0030418160549210b00c40b01d4014228242c1484103000d141c0e0011138003a010181c80300151500083c0c0c06404003400c00e800107589141842080000d0152550015044400c00c101d50860f40410203c0c01d503183c010900f104c2c04a500c1c1c40a00702100341303409030318945600c0b4058803800010076800c43c000b00f10030081a00c1c0c8032118812082914120700038110301a2408004205030310024242c009045c2c40840001c1c0b03401c1c140312441c0c0100d01c2c441a410700c00c807059800021415050303080040700c50707440714000c0419480d0001c55800280b48a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 381636070 1250 381634820 381634823
    0xf0b09190614071b030807020a05040b0f040218041b080f0403050706020a0909020d06091805061b040b040e40060b091608180304060c050102070507031b090e0a 70
    0x5001103400700c100400d8100c000c0e52480c4e11a00900216141e040401096014a0b4101d100c1c1e221094000b81300d0405004139445070380c2c010f00708588441518240f00103035001c4815481c00509445102c51281c0e50380c0b0038030320107400f420400d202c001100740c009819444d010f8059140826110204000660301008071104658030480c056200c01201c41d054482000c642c01110a1600110300e10200300303400c3c1e2010089803c0c4070024041181d00100840400742001806080ea8000d80002a03072076200603c0500c0380a040180c05140c645d503013800e40542e4009400850102101c1c4040c00320900b80714040c81000d007214a02034010050b072001d640c00001c150441d00c1259412098804244803541d80220b001042c0a00401e4a034a1f015840b102c1c108217000403500414044e1000c0350340d2090900048078a250500002d518260400c0000c2c0c4180c40c2c600b00484d00c2e90f4080101034002107041c407042004602c240b03451000011b0800da05040c3d041150058408140340c6800c0c00210f440003d0a900c269 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 381637320 1250 381636070 381636107
    0x151005010c021807030b03190812060a0e040c1a0918060d0b0f01050109060206070504050103320105090a0905060412030204260d0801120b100f0b091906 67
    0x80700c00303201240343c0360506030250a081084008014000e070300b40e00040c41e007203801c070309542d2000d2039450200d01402d0035203406000210140940303240908005807071741d0030401c0140307412400c1d9a19010310784014811602101d41008040080003500d40c6400d01082c0003007400390941c1004800c0307011801d00520344140700003080404d0003068a58039202080ca005940105c0c201140d8902508900300f00f40081c801d1038001904214000307400742c03002c0341090244c400c50707640b40e1905280a004501401c01c200e1a4003140111b03901740b000e1480d25896284001c140c44190b04c0703a641c9050f040011038200240070001c2c150030700101038009400410a140e200380d120b04200130b03524034013100b20024000c54110200d41352194420074010041c030382806440c01180402c40300280307070b80320044800003028030a14071312540541e000800504400b243c00da010089014200c0344603540c142140c1280c0f615809a01010030000d050502420481e00c00342c0c4038807038941303c8000e09160910003002c8058094541114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 381638570 1250 381637320 381637337
    0x6010c0311030a0e03100507080c0309150f040302070b0f220504090f06050106210c110313061704030905010c0314041401030f0603021311070c0b030915100501 70
    0x4140c000c00c040003484882804030383c3c5034031503c2e40c00382680100b00401c511a00c40c040107152204042d00410f48600c0c1c480c6d0f40d1090079203402020180d16000500841140d00941c0d045111800c1c201c00c866101e40c60040c0b00c00b0aa0405080181c113203981c80e0000d54044c1020480711b41e690241100301c55031416030b200c1e00d800b0b014824008005c048410f8010642c440e0038400c9080c2402a003002d8191882d004040030409640c1c0c0344400e03121804c032981d1406883c0a5074140b130a5100281e030205618810f141040318100c4580440d040c00c5030706c40f4800f00841408100103201e803990010022401001c0031115241a0805407400360103100c0f180b05080c1040b91440700482054400d01c020319044aa21240b140c45649038004002500206010980040e251281041d0700d40d140c0d0244000300c0c2d402400f210807541c00924200003034032002550201d07080041002034009140e1440c1a001007400d007406031b480c0d0521203942400c1561030550b41e001084000248800d14142080c64012942c003400d140d0300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 381639820 1250 381638570 381638573
    0x50d240e1b0117010806070f0f0c020405060d230c06070203030d0c020307120203183a0b0426041401050904141812070503070b1512010c170f06010c 65
    0x3c4055005240c020101c0800d0000180450000b86c010f0242c0b580341c86a46840703000c0f1300c0072620706401c2c099400024202d03103500405800c2950050f82c000502520155424085488100c1c2c260351704c504001f02281c1c0081c0c0849551010b1202240300841160f640d8035003401600066070f60b0040403502240244d44003800081c02d402001100c40d416408102c5810145503004060b4480e0131041c4000c5009684415403000782c03604001900c10003030182440e018a0064081c01d00c0918100406007180c02504c55400c80130032890351409206520885204151030180c114450414071484020036000b030041c4020b100b0b4410440501b00c2000c428602140c0b03c080d0400003501a01c0c201100340154040b401c1400111524140a011a01c5007202190400018007510196900c142000a0015001444400002400d0f88852500041c012542407200402100096500d40801d58019a5030390341e02c40b60450550003c041480c400403003262003c40385807994510070201c500510742410080c1e828030000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 381641070 1250 381639820 381639827
    0x304030f0305130e04051506211b060f031306020f0403060b01020609030415030f1d06041a06010503062707020709060e011a070507050d240e1b01 64
    0x10019034114444010540a504014080e0781c400c07040c8001512051030041441295600d42038000c981c0032000341030111540f851802100006003000d9440507041e0144920604450800f1021041ea032018180708040f1344800000031070b002983c81d00070001440786006204848080c2c0c1e0f48000110115048030b0001e02d0100001d01c1041c819007500c07880805c0100034803105034803100311b2400a0702212507030344030301c078840d0f81d28012449444407148422440491007403282c0c01030b4140d013800510118442a4001030650304410038650109242e0086081006010140a01e44d06412036060303117050504241c07000910354070000309a10b004a84406510142c0f070815815281e03c5044210b40031301c40d0400b003138000e440c2e000714861402a181425004980500400007071412214007401c0b83c80c5002c540e202444098004980c02d4070710f80212440003800c1e4175842e030f288602d03521461560b144410009004420b900f198481000200d1a040302100132000001c0c0d2030703940c8182c04000c0c0041c0790170701004a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 381642320 1250 381641070 381641077
    0x7060c0521071109040803070e01090504020304050c1f0c0303180f05010516050c0601032312250c0509061c0f05010b091003080714030a110f010605010504050603060303 74
    0x84044a01c4401240484400c0c80103001c0540c4118102c0381e103101c1c19010840c956034142e030090610207040011564a40c00b82c2c2c0c442003245410f0500c1d0050a5031000058200e803c1114207841e1600400c2c1107000c00c2c5421905c026118103414108810703100c882a00611714082600002c00b403565078201e401e00030b40542500d00c20194499202c6045a1170351906501a09065405001d14a0841c1c4030212850044003915500c41046004010716803170340c5c840303410301c0210603200744c000f120000c0c032102508008c1c4500848040121040c07035980410400403c1305028801e484001d591000341550000703440d0f0102c031801c48008440e507140607100d00000a0031440c0e030340d54006043c04500340800400038483c200400751401403008010040b5107009003c0c80c84800c035242c22420034002824000181c0d00030192a4881c01500d40d02440c0c3d81010429103950310460391540420b0038500451740d1200b04110154000d0305038002071044030700c0c02c000a4481d026034050640b1845000c000140170352401c0064 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 381643570 1250 381642320 381642343
    0x10603180623070e030a110f06121509010e13030e1008061302091503070203040918150204080c0411070515010e010e0105010e060703020c150409060e060307060c05 72
    0x8100c1c440482d000c510b00101070340c4045036a0044a400102c4440c007403a42e800c00c83c034000d000b81c101c00c22155143d05c001c84407030148552100c0e21500e13004054903400060305030f00f240405111441e080070196080c017030048007016072044905000500a5040c940c100e1a003010400d0b400c0d460724542403406581c10b60444103916000460702241701f405036031102505000e1681070703e00c2519050f01020079020f07031040006481e0490b909076454140ca030209401140e00c80f2043c4103a07410b1071b881d15085015960780e1814041c02c445004042c2061106a0540ca903003402d82250440c030301850250101e071500d010007402849140c1d600c000075207801010044415555021040c7e0700303078800110940440000070300500110f400c0c0300d800441c9800905048506a42c4147c482c5028800e0a00030050181d0250700c0031000c40c00b0341000c0d00c01c503440f034002ea9842810f110010300e481c0d50800400c041143c038258818a5214411818008580c4000c251041a1385c0a0b2901441c0840c89042945c41c00e0910b100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 381644820 1250 381643570 381643583
    0x1412091e12062809032703021003020301140118060c020307091812090302030619020d06090509010b010c0b0408030718060e0f0f1e01020109140a1109010e01060318 72
    0x700007500140c0f4180140307055a00c1c00c3e6054941504481d401241e8400f90001c1c04101e10340fa03040d03030300c1600f03004600426140c8290b05110725142c2e800b141d00e05103a0304044020a40200040c092202c0b804203100b1990001c0c40c0100304841107920014080d00c0714451001445003544c0702a0541d1010301c250b40c05010040000d110000300710354030801d50740f00e0000a0305e40d451407200c590100c0e40310307806510860784c006004040c10b0700c40721388500c2e4000290070481803065003007282c1020142d83d80140300003440c07201400901450003e040b03500350745041100030b041208407a03c100c0002c2c02150001d0300035400024464490b44d03a00400e440d114103001c2404403042030030000003040c5601094007030000500b0703103180720008085800d10005491265a2690201900f480e45a405003030f620300c0390540c10141300205950005448011110300b0703c60710421190030410000e01407202c035050300120550207903606000f540c54000d00010644040c015401050b80f1211102c144010b007140300e00e4400d41100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 381646070 1250 381644820 381644833
    0x50f0d02220f1b0206010b1801080a020d050403020a15060305031e13080a050717031608090a030312050115080411030a1203140901020307090303121103041412091e12 73
    0x31010f200d030342e0055104200511a040010030801d1760b10040e00ca030078040c61041c0031421506001076039034010003020181440d500340a09a03000c4180d018203030285000390043c21b20059582007218140303614540c0504072509218081000441c00003c07a481c02e000e4440d940c15103144900d201d041440341043d03460340044070a04c049642c06001c85e420880901c10030488408560303480e0f03a80e82c001031011140000ea08240460f0700011101001c0c1e401441c8104113052401a8440c0020110710480c1c01c26800642c6504010180303880c107100f903034054040c02c89445500f10990302c0c014111a00240005c003444d146c0410071803103440811803403030320540c80f40d480c0328164924400203005180035020880c07804c4254002c90983c0d4018400c80b80915225603030106403d05503203058810100c0d0481d60341c8031594500c4880b841d04401c101035030140c0c0c0b09500310b12445200c0182c0614140c0d01d14000741c010303d010061102c6c5a507440d03000748004040312069403058054100000d0001203455000c10141c09100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 381647320 1250 381646070 381646091
    0xc010c0207140a060c0311070803030a1e06081e0f0706082502190c050d060c30180605040b0a11032415040807050f0d02220f 55
    0x1194500c00c2c0c034480a01e03014181604010881c00c06828801d80c0302244060101074040387c410300d0f9035220281003000312062550744903200c0c0d14580c001c81d04013450950310703094075001c2d032104510180110b4001009000180c05c0101c000d4480312940380401c00c1034a000c1110170707115824444141045030000540380740d40d030f4603c4040c107405800c4036445200c01741c62032040c8041c1b80320031254800c0d0309240e004000900b1054680015078440c1035007543d604010100c0061256070345107035210014461040881d00e20442c15010f41542d04001c103e0704070301c03010700300c00ea95001142d0b6034508400c0c1d0054042100f425401c5001e044d14010340029041c1400c2204000c10321440c1e825450241c000c6600030400c445c3d0109600c035450000b5030311b40c3d5084880e031030300040d50708500d01603420f03501d0010024108420103c0c00c0c2406a4080e501c01c68054015510030405860580c0c414000410144c94140043c08168005201d500c9066800c0302600005030300d8100c501010f80c06100d03500c4c0c0c030160411030103204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 381648570 1250 381647320 381647323
    0xd2a0602040501030e0f0601030311030d180b0f0f0703150302041404020312040608040b04020a05030f01051905090a02010819020d0b13090b18031606020325051c020c010c02 76
    0x2c1c0102d50209041c490084101100040c0010400e18800c019090990843c0d030100e41da01c00c810044106840f0038440c0703114901141c443c1d074008200480110340c040c603592422000e6408021b100b126038002160812198003c3c0c0584a80d005010307140008203040140c892f0300100310b003500042d4106280c14101c26103032410014050040d4001c404541c0002a21035028800740300300d01414000400745008100000e404c80041500b061004000d80c41243e1250302081c41c10030074442c007001d21ba440e00d050141e21718150302c07064403061074140103224030724000400c143da40c0381e036003030080c1004000343c0040c40328012490b219014000410080d0340c1c84081008000c05840341030581481411260780b040341c100d460f445000080c1d40e005051031015504c40d1b1401140407526028001180001c004611202110340c00240c0c0d4180301e202c0050b102e0801035540c0c5908908210404200c6c2c050400704080c02e90441e054500c8000e8020203450117509909612001e0700030030100d81425030034404007400c610740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 381649820 1250 381648570 381648577
    0x103110c0115140102070902090409051207060c0f0504050108040606050405070c030212040e010e04050a02040912080f100b0c0106150e1008040803180109020a03030e0f060304050d2a0602 82
    0x24086010440300f0345600350054244440310503540540c0c4013800800800489401415140d400100002001c040a03241d50342032502002c2520b050400c0040d03070000f0800c003440384000400c070a01d0801804c140450014005202d640074440c140246200003d00704440c5070404805000060400d01c160b0600b4100a0942801e904040300980501f080d6640092106410b880807641000700d41300c80d5905e4000903102d00e074000b0304160f55502030002450050780b0b590050700c401c0f0303200ea030065003159417440000303108810252104e01e60030b0015050190f220032180d811070607200710385000c0d9a110031408000380100041e1780a803001d228942c5442031060780003403004417850400d0b0759000c40e4030f081000846201034125001464100c092020845152078800c00750b40e0090180000282c3d20130703680000b4010040c0d81d1003103000031407410341c110042c201034203070b00e052810980c0d1003415070400356101a1038103001703050201041214031540c04901c0c5400c2c004025501403100b94102154182041c0c00650f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 381651070 1250 381649820 381649841
    0x3020301050a270e01241d130602220b04030204180209040803060d02150a0201060b0c0a0308040f0f12030614030601030b100506030a0f1503120f051b03030411040203060312090103110c01 82
    0x940010b87c0036101018190001c0c450140030b000c0c0d001e294810313540c1c44001e4010002c003c601103001c0d41b80501c401d09000314030020b0302409640544a6107184100001d0b1030000340402c00200b000c40c030034801620780c0040107030002e9000320925120b50320300b004140601c1c030683c0041e500104529407100c0103010400206035401840d8000d0144c43c1d1103040d02c040c0d51040d40307400800c0b40d01400303031031000c0303846551490307042440b030741344050340c02d449440303081c000130171103000790740300004101da0024854151280c940140422000710000101540010303460b214148005486641844c0010704548014120540074000050080303407a0b00340780c20090014800c2e120410400c62600e060305910341c3c500c200c40000c0742d6010307100d42c14680070280c0440d4072105181140c0f0a00c40d0500803030100e001c0d4800700f0702da00d00084005603201d18080c04c0c03c0a160580080c620b000d5441041404001d8501048405c0004580e001c4150b540000600403002044141e0440e5401d030b00200780840d1446041d00030107503c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 381652320 1250 381651070 381651089
    0x51606051801020a02130e0724020601061b020f1201090b0a050606190e040b040e010f15030534060c0b060909070501121b03020301050a270e0124 64
    0x650728035005980c0ca0940030700195100c08100c0590180483c1500021441010320096440c81035a908040c5040500c5403440924400c0813040d4540d465130410400e0300402c6140360280e180c181d40042044030303055a55001c1c0c041c140588081c2c010352a2090f82c610070b8425840200800340c4182450300c0071140545031105224200000300704949056010303100e0408a995000490303000e1854255a400410298650043d07101c04030510542c0e43c0340302c1c04140750a41000401c07900c50501c00c1c0c10803a1443c2c444407102020902062001c500c00081000030700301c2100800340404840e265501b9034000780098091a4904040041189a0300403041524640304028002060720b03031800308281c108044403000c619500065003040550b211f0fa01051036030f5000c80b40003078840f41190641c0202e42c1e80440f6800483d070000010401400c20006640092000b0925080103010400b44006a05201900c494040e510f500c030100d00480290321401040c0022004e072640d80e0141034003440070f03544921841c01103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 381653570 1250 381652320 381652357
    0x31b0c05030d0e0102100e0f0f01021b010207080f09010203070b0a0204060f0806010e041d033c04050904140d0c060506040c021c0c0b1305120702030d0c05160605 71
    0x5090060b443d075500390303005030054001d001c80000c020005040c140105178092050001010b60580706209200d83c400c003020002d40e5900102c07200645554541400551a81c410058400810700141c242c0b400441b60303181d00346e600c440000040f461401528005000d00041c01d052080c2c0c881d559000388125101510b440031300b1a0318142c10b4490700401c503015030100700344100701c02840c030b000d902201d0320391101c100c40000190540700740792070b540009042200360086181c3c490f01c0c040528256461281d42d4890070352100070f10703140003c078030b00035403264600401031240400d041014110380784c003100000104a07186030741e5030140140588c064001c280e40c0c140c81c00001c50f005003885e02480300103107520703001490760050544051030114200000c2104122400e11540300141c1000021400703900040c3c1144d80005190400c0e60402005040803020030317804200d90307001603c0210301c8880c4800242405201d403441410b001d402c002148680448007001490041103658200d03000d003980703ea0480c0c0381041e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 381654676 1106 381653570 381653593
    0x603031d060d022101170721080d0912050408030703050306060f0301030317010b04030b060f030c0901062109030c0221120307110c010801050409031b0c0503 69
    0x2450010440884c00024100ba042c07030140a014404c0d051101c522801107541c4c001c0c520403088168080403900e001c000780c3c0d0090511081e00303c00b034141e461030070307055140040c007645504489081050000c000350301c1c41401580d0503500712900561400480d1784054540d504000d002c10307808201001192000c810190107036000350f11a80f5000ea48003100c0c60b0f10000018160052048410240000c001268074a60042e8002005031084030440c4003080c08039080145000034180c110a03031400000d038443c3e00055044001c4402045001c207042855a03520545128400c00b074000364280020300c1c003500d04079201422031040c581c46100140c070018042402c0c4403042724011b407641404010008580d8010600d00840d001e82c0d005040015400310000c1c0100006001e040d0040d56560124010903026044104901d02217203d2180b0241c50303454080800e0313400c0e01032240280118a51041c = true := by decide +kernel

theorem cover : BRFrame.Cov 381474820 381654676 := by
  have h0 := BRFrame.cov_init 381474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 381474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 381474820 ≤ n) (h2 : n < 381654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
