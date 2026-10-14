-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3233
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:03:15.606233+00:00
-- url     : https://prove2.me/submissions/a58c37a6-3bed-4f6e-8ecb-793434b8e0e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 581294964 ≤ n < 581474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 581296214 1250 581294964 581294969
    0x1203030c0a18060503060a090b03071a0c06091015050d02120703020a1403010e030f1b1207031706010f09050f040b120d1e0906030504150e30030c090d0804 68
    0x1100c0956904200342040309201c0b55a001c0c41e8040e09000b581c0707d10350ac1c08506070381141c20003001942c441c099000300c00c01d02d0091144a8940e403042d101040035a01001500c84000a6005010001c0362405407964124140d0f500800b5003080c0c7c290401001420407d007480c9201c0a05405e9401d070b0b64583e8005801c0215690009400b40c804d5004880c80746420b208400e600004040154945040c0101e421010700401d00f24101107100603c002c04a40000d004440d00e0105c040040ea07070300e080030320b000340c000c50564400c1d81800043d88000f5800d5401100b034040a1031003510b941101616041c1013084c0c40380700c2c5402a4105448040700314550f01c505410702100d907100000b034040c05110396402070040c81d07030070290f8410b58812060081c01030b81140c441c1e402c0e10524600030a090380c990402c4902c400314171000508075468404201203807680403804e03903e11841d0505084005480100c10441c14403060400c034290342c0300f04040342c00148410020010180041c200900b5040c983c1c407890f08940056 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 581297464 1250 581296214 581296217
    0x1140705010c0905120102070c06050708160b070e1e06030a1e0e0609061005060304111806010e0102030403052505030a030507061d03121902271203030c0a1806 70
    0x20309011130703c3c2003903e04104241c064002c48c2055500e4880d050002c80c103114120601c0000608007003803180c041c0458440b6070488100407070b07120045c0b0381001380300401c0f030712400002e400c08010100c0d80340984003801c40b4001c00c001680c2540f48a01003100e5a440a8848c1051540d60002030088001403414907901d40d62102000400040480d0f60b5801e01c1001065a81c00e03400000401c42d8480f010714a6000f5520284d800c5a241c0d580c500e0002d2441d246c42d4404d0380d2080c00411943c20070702003d04a10711911080c3d84582d2440d444000590b5a40036600009101d50803480490003580394081d000c180c04c80b05161041d28a903562804281050300c450401d81c0000c80c006103039002d10009002d80a2603241604581161200240100d900c074007442e07224140d041400b4011070040c071360200800010b0907841008540c0c41008c0c41005070088440b03188081c401c1c0c2555401643c07490414006c3c1081f5100802440c40c580e01c0e00034034185548124442c00038410502c80c28600b00c09031a03002d0000d80303420f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 581298714 1250 581297464 581297477
    0x30905063a09030503010315060e0c090301330918061a100203120606030403120504051f060509090f0601031e06021b2b0509150a0f08070302090a0501140705010c 71
    0x560800d10109008241c0748c03a9802d040030001c1064031413000809500c00c034101074250f01e5112440020780904003c2d035111148001d0b681d8070b09101000300b62541201d54414107080c040594034805d65050f42c1321030810070003020803c06100c000c40c40c1504405019400f03000b00e42442441c1400003450080c401001c24010ba2000c908020108008403255800000803180d1034218034042e5030040546101404444280361505c0200f010048208540d43e040700c03851101042c00e40034000705400400da54482c031403017420200045010590041a0007442c050394001401c0c0301e0f07085427a00074070307840c4007007404105440c0900c600c4040740b22440505420f49260010308542071a07241200d291424402d035024034a001c01608428001c1c041c0054041c02c0080c2c142580c807070240c0c4000403500030144900c40e405800025044003419403113204503110364000d4540b401140c42e01c100407812800754040294111112080a100b10b6000d201050240d5070000300452800c1156641d035425180541140d1012500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 581299964 1250 581298714 581298719
    0x11120a0e030d0c1203420f030818030f03070807210c110301020d0e100c05120403052a01150611102004030b0103030905063a0903050301 60
    0x1014403044480292a1501c0b42e4240f000741c5540401c600c0b805401c07014180d60340fa02c1040d0444503c90018011801054000d44103000c10900038500c50b192080c42404900c03030f0012803440b0f102200d00c0c0650f9000845141054030b01c10044242d58865898130340c0c11b2140c0003402070002c10410080400602c10402e00351039245516010000c070040e504456400511600c0d945101750344442900c54294200c0c620f0090f4010a80c0400e00a101b801209400942800c40d4030031010300005982c1006240d05c1800c0264000024080b51180140b5210740546243c0d20081000701e4800c0015040303907110b201c180d520040d5000e0700c1e5000c140c00469020290b945034031a43e807807840345036112801001ca070700b8241c0340112458042c07a21500c480c28044010b50340c03410241405501680801c044000a0035402e0f52141c403420300358400341d424401100040ca1180c004a198244682903880928a0362106c1c01c0062511707100740d104d140d05180c02100d03e10a021f4611140209000d003410b0f17640131b0b40b40d1a55a50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 581301214 1250 581299964 581299969
    0x2060f031911070210030f15240507020604140102010204090203010909050c032404050307060204030c09051b03150103150603091401020a0915020a05070905071206051011120a0e 78
    0x1480c2d19542c0ca1212030521605004da10389100040f580c203001d140000346099100c19900042403c030208010290020202103089020804c00045070018080500d20707403000c80e001200ca0b0f1251b0440290001c100f80700030000d40c500c1039040000b41c28140009820507440d50b2036101260404d80c090140c0300d40301c00a07001402424004800302020030b070060855600303c50380c514058420007044844004075800000c09010042c0292549194081800d660f03481e07890400e00500d0029000c0d9004140c40d1801103a050411300b40d00100c0030007684c80c01d90a42d40c0d003044401901d4103090545042c1903e0b01c000103140b1241d0300c0d140020b071481d6140010103908908228a060054031500c0185a01c104182000160800c0202048481c80c0f010442d5102411808904040005a00401303d210343d49001c5098603003900024410244c90707441c1d040503d009480d48003035401302c0c42015048001c1208503005c09120300242070040703059000b00c0d01d1500700003d42c407400381d01419011000481c00710f003084062 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 581302464 1250 581301214 581301221
    0x11718030f210609240d0b07021b1e19181a1e060c0609150c0304121416051006080610090203041e0f0201030606032702060f0319 57
    0x2003544070780040ba25203040420b14014002d48601c0d840300c03031740207010040d01018082001d6180080c08443c40f148443c600440c00c042c00350f81d8072000d40105c403e6400c2d04040c0da1070510140c00010302e0903080c0d500724418840c3e2680860b08160b009080007405010b02c404846065000780404a05070582c50444140c40c81140c0e40340034030814030022201d00c14000d07030312501e500b80b51f20200300d2038094484107200090450321481608220b64040c030410000320000c04100c88108400f10303c42a001991408a40000c0b4482100e00420501d4400d280c1d04c034103445085050ba0300c003903c2c259140742c003049180c10075030303000b110708120f0342a844510a01512103031402560b005007020801446941445015029500b4441c081d9074000365001c800a42032002860010031555041406254000050300f0840c04e071440140060b0301083c240540042d0480c4240300e1020712502d150401d154105c20b5403441b03015210808016640801c05108114413003440700011409a0907141c003025540101c480e500d82079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 581303714 1250 581302464 581302507
    0x7091d01060e011d13091502030615270a122001090302010f1209020a03060504050c12151e0c280903030503100305120c011a011718030f 60
    0x10000b0301804c04205001c2a81d22800c0c612086940c540030018030301c0b00400610b40c001c009809860b04034410003400f121940110302170101541e1181b01a0246030782c3c601e0034030507510201001403030034101c80141901030107103150a01c40200031102c91640ea40116800c2c0407020b07400d5615985e03900c0d460b01d55034841c08005a07042800e00b8481283d41c070359000a011480d81d07440090a00c80f00311400d41c40303880d260740421000e907401410442016140c0c20040f0040000721400c803610701c20412590450320344948420132500080004120200300140e4080040380082c1c4440f0f2540c1c0d0300c1403000d515101488890707100d88240002d4648614020340c1e5040a01d4a9141080a60800c0f20b0b08917005d90340110a01d00380d80d0141005a600c1d15100d428011014a5030f0010782a4014101d41042e4000452300925482203000c0c0244420360011100c001040c110041480c041151485c9149a484c501c0300c01c03071b45c89409020a500c00d0984100000e06603401031040e801c01007000999002901c0003404070610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 581304964 1250 581303714 581303717
    0xb040506090c0f0a030204030f0c0302180c0901031a0402030a0c090b1c051503060705090109050603090d0804030c05061003020406081504081b03040f091407020a060507091d01060e01 80
    0x1e15060036155081940b04194040700342401c00203a040c90349000e501201c00841d8064030003d0b140c081424124901000c90100b00d20801c1d021801440f00410884014002c00100c1445440c02010000550050100103141c464580382208000041d96451000c0c0d031054242d4074000c505c0d0780068000a052044581191056035414060360a400d24414169407200004000008a030b44520809514024000c0d042c2d5525110f03000411040541c0640604611902a00e4456031030742c8900411602d80000c48000c46035030b00951301c100702d82d0312589429402c6030107070030013001100c6951201d40c01c14904460891501d20b81480400440c00d081c82110300074141c0740058011903178000e00441c0442c0340034001400f0080c010940c84086c45000c01d12114846030801103c1d543c0d48da03400d402200b41c880e8440c208070189004107090002018846a42c812403482e405006c880c500f65560780003c1c0703000780403c01041001134000c610000c580c5d101d03200d0011507100c11902585054001886200c0740400c8a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 581306214 1250 581304964 581304979
    0x90a0f0204051803030412020f07050108131a0408030108120403210311040816060203030c07151104080f06100807030b0901320c0403020a050d0204060305010c030b040506 75
    0x824844814000565030440c1c01295940741e407484451108a030188401050100000380001c101c0320f00b001207590000342e020748400c0045502e055403212018031902c0e001c1000840000c0e030319120300c0815120113120f8101f0a805a0002003490100c0c04101e5081391003000000040c00110301c1000707050858280558034600e4141995104001d40d03091410349464210082e24011040d4000e0700240c3e010796030102200c2c0c0f00c7c0d5841d00070956410300c40040c441c02c600900302c042541440801181c0c802c460703103100c0c1846c101050359892514941c1221540e080d40ea2840c240018a20f032a0041000b081c0400c01401c46449800d492803c0a2001e002c004070a40080320070080d5001c003180c1d4204903500400c1020b5035a89100c4180c2c003400c2d00c4854211820423030082d80814890300500c414900c4c19224019140e941c880980089620a5000c080d50203000038604100d0391621442e101030152001d003020030030a40c0c070f6507a1800d58051700e441001007a22480401c0450801e8800c8941c095011034000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 581307464 1250 581306214 581306233
    0x6060b04030c050f180a060e060402040e071101060e0a0606110a03081602030c0703031808010608120a030905060c0c0d05031504051015090e07020a05120a09031709010809 75
    0x120a1140c2c280300ea140104852004441c1d6542c41e80300c100c0741e441c95918211158a0b103441120010325103801250204460040070589a042c9842500c0c151f8000403070158994891100580704000380c0d848014088d0f403240008552114860000c9014050580010403903604101010340103a08000b40640705900c114044004250301c080c503241c00c8101c100001e01c6007034200c0305c100c0c214464003100000030300c2151000000c2650013806a480e00d010700a00049054489007030900741c40546c45a0b9295601119414404880c400300600d04601141000501540d6940d6094100031003140c00000c0ea100214640c15040c00520010950300c0141c40d000380381d8036080300c0310740103ca0324000003030140703a0700c10006402c25220203908003d0a140c1410020401c034055005258071080d0082000010b440800b0031a0340340001100513a4036441005885c0400308a8107aa0381c80c3c1000d2098400c010326a80008003040f0410701c08200c0000a8010903038842840c00090807400019007581056484031941 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 581308714 1250 581307464 581307473
    0x20a02030c010e040605030a050a020909060f160c2a0803070c26060f04150e0c010809120a02010906050601020601030240050a05100b181c0c0306060b0403 68
    0x50045200f401d18140c2041840c0115000f480d4641150b6014800d00084406010000030001c034581c1c421611200140d480560307a0343c44039825586400c0a6002c403003c5034007d00c0c101c4c1c02d2456021107150500b4055001d03150030303106141484d4400041100c0700a0100c50340721400040000e44045401180b6000b250341c4e0350b40c2104c0203031203403441600c1c21030824014019030000d05010203049070200d520605248440060b2014250f03001c4448118004820107110b02d54007440d503540d02448080c0c0340da901e01b28015564034100900d0600a0700464070700c0c0a2210103480503048890503540009080380c02c82c81c2590031501c024240d181550702802c010401a030320003840022800740d1050900c0781028000c00c3d078240304c81c1d000e481d03a030b206c03105080103400b030400c1c1d80036074428507003c0310a01c81910381da0854108005540242d01021500304103200a8110707544d4404002c4001414803403c00788089030600d04642501000c58604012540410920000b8003d2201510503400320b80c2c43c040c5156035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 581309964 1250 581308714 581308723
    0x50411090c0f0f130306060b031f050a090903031b0903050709020309070506070602070602032d151c0b0406090b0901020c07050d03031508030a2d0c080d1a0f01020a0203 74
    0x150000c641000540c03130800e00d001ca20f90000665102c5000d010464560303030030b140c00b90002c40e4038100c1c038150074a91400700b17017040302c250041701c401a007149003c0d4100901903001e04081d8030b05400341925903040c034800042c3c0e10560110000360340d43d1544204e0440c82c0203802d0004550240482314010305c207006001e8004111001103038800c031915591a449494005c1c064064514040d02c124030110410288960030005250340d99461110b0705400c0110039081c0c0703040d5109480c07110200c0300040700c295803805c048100c503000c006c4420302006040c071140d56100f203070042210200c0343c03981c07a501d103402040300c02c4000c543c003c0c0508009500789100c4401c0295100345c2d52050503ca004114081c0b8189402a446a01d10804541c0038100680d12015041d50700d500c04d841c010001400d0207030700b003503c0408a0b6006295141c9402c016801030000c0411500034103403100954050108101d882c100081e40d00c40c0841481840d90170101010300b440801400300c1900130400d0541d00303c01040300060f0f50208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 581311214 1250 581309964 581309977
    0x2160510050307140c1c05070b01060e030a0c0306230c0f07060605101e0504050a092307020f2814100e060a0f020909070c020103020706050411090c0f 66
    0x180c102d84070f950b1034004035070075a900303070241c4210500003410300a081d00c0412410b41c90044402c148510215a000440740c41c40344070070142460f2032100061102a00c6403642d20b41c8101c0c000d00722003617100c0c2500d5854070101141c1c811111030382c3d205092016a51402c0340e400d07091604100104207464001c41d980c603503204810844100c080c0020341d400c00c00c0003a90080d0080c0002a1000301140b1154030041c00644441e000c0302d84102074022080b2405203d882241d00b5035002501628507135180c01509005085180d9040e00d1001c0340344d64400c0382001d01c2052074440c01140d070042c00c0c0310b40d10700992402e010781180c1084051025044191401050382d14440082d81c1c8075000d6041c948031616061705200d1280c0c89400c03032a040400514010000050b20741c02922021420000c5504440400e405c910422a00780e8024125000088170103001c0d8084c4030405006040240c5440c1f5140e0b5090202d40044508130358010ba81100e007a01e41c00c2030003080742c1c49407151108500e420491120084980200d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 581312464 1250 581311214 581311217
    0xb06091017010f2303031b0d09140d0f0611070309140301050c031503072114010b0f1509090a0516021612030207080a051c0f090303052b0c02160510 65
    0xc03150070384c040d2010400c5805008000c0c05c05101803100c12003039501c0340b04140741880058080b2102003441040c0d01221f000316040200303520750700003569440000340d200c031690580d41d5903620701041964540003401000224401c0e5a007552590078621950100b10306054030707502a0b854042000843c02080003200c0d0404e00240a15150407100e100113440c0940341e40060400d295042400174031646400c9844800c0c42c4510903d943c84406600d4903806c039012034034400d0b408411a490301d0280d04105140b4140c01842d00c0d50b00389000c500c071022907003c00c810364400c0b102c0d41c2d507034081040071920789400d01d4103110310740b02920210004d400d0381102081103014282c01c4d000c00c80d03040b004050081080e0001042c9280c213552030304170b02e03050068803400e1b0440700784d03071a040d200054203216108802002c010001600c81403074203410340e1001c135280d030882901c00c010f080b13031552600f1100741d0491050140b448080008500c19038001b000031306003409019481815034004005218aa94820041345194081e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 581313714 1250 581312464 581312519
    0x90303040809191401090e1e180105041101080f04020a0e070909090501020901031b0504150905040e16050402070f0b07020102070209011d0601091401030b06091017010f 74
    0x2d94005026140300c1e803201c010643d000c403000110714000081c8103a62940c01d8030b4071084c59170380c1c0c3c44904c01c802d000c0b2031503102e13400a0110812601c040f0006a500840001184210f2800c505821030031118107036829119241003081e01c000c41c2d82d00405c101d80c003200c035201407100d42c10541e001c030f06140d0590203282c641e80d0400d00003a40152041d408100149480b440501c41180e050030090300070b5018800840c0021f04050114280b6420010200f0b01c200b940d60350355241c54606800e0220800140400d4810428512000101a6942c1c060068101903240181030b000398180c6a601c481c0b481136203d240120b005100d85404a50010400c0d0202c1e03030040140c3d2403036680d03140304031b0080c0b01e11380340298010484000410542da142d1000300c0715405800d0781001c2511107074015101c02c0070314428601c21002c0802c8100255100c2d802107031001c50058051814000c0c25030004016102640d140c80004403451644103030303040c1080c01c07580102104070000007610704004404401c81040e80f90300031120f94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 581314964 1250 581313714 581313727
    0x6010c02040209040207030305100506040e0a020a03320612030406181a0a0336170c0c010e060406020604080a050424112b17010902040315050903030408 67
    0x100c0780c048543c0c041c0c0050007150f031000c00d0700d400340c0145029110305c990042e890078040b40303500703003101102d041e60401442141d4545c1c5a841c004042c1d4040c5514900709900c031310075440e540d00320110702000c207580c502042c3d2145518541010b50035038002d01540c4240440b80500c1400613022080b44c0030740348280703810079020424030a0f90441400550000f440c041c051418000c4203010080a44000d800c1607400f40460341c2481c00012a524060840b120040140d80d00d07061507021a0162070040340c442e83c5000b00c3c3c05644035030394000b0303004512a40510f810150300c0c0c42e002e603841040c40001c00703402c032a21410035082c41c03802560b4120040000382034034400544105418000c03c10360f4018440d40d01c18000500803135407038080700c041700e900c0a4003203a41606d04240070600401d030424100a00c00003021443c01c4000c40c070010310030400501007406801002d041d0030441500340c0720301810700031001623901d030324515091400c12a0b818049000c84e150105112250501000f00c0ba003054004080c60745445 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 581316214 1250 581314964 581314969
    0xf0618031d061624090507120c090b0d020306090607030c21020c120d0b10031404080a0c020604080c0901050603040503090603071b030305040b090f07090e03090d0503040e0c1206010c02 81
    0x40c1c00104412803190642503c0b110505d4022194140c4104140c0d418255204901c01d024840c0f400010003040a2110038092030300b441c0c1c405054848014091840e00102d40c0101e8203001080e5416402c2e41c00c0002004403003a0913003d104d00da20140d10306156a210302003a541c68005041e404c8141141d000640801c844504205081141c02240703465995910304900c148005d2011035035190040212820000c010b6001e440b81665410080030203101d56659075542c948250f0008254100344403154910102603101d110251010380003980040c03401000c05002c012007020140c3c00240309460401c10400041c80110a0f07404148041c3c07405078603606c0b6070300140c8440f403c103480e000460a00c0002c1400345913240d040300380218040d401010150f00c1d100d44251301d40c41d400702c10507a1544424010040d20724564007150403480d415043c1c03401c1c507800000182c02040d1070320f0700750392541c00803409000e04000c0c82c44182e08980f036245590700d0144585408020180014003040c103220600d4aa2025034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 581317464 1250 581316214 581316233
    0x70f020307061a10020102070c0f03051b010210020c010501050405180706080403090e040510112d07080a200c0f24040b0c010b0f03060f040f0618031d0616 68
    0x3d40c0060090500030162803000303000790420501035440c0d003124a03001440e96007161a40c8181c0f83c00c82c0180050000d9422103001ea085900e51944c11481003070118a21100584060300b8080300080001c1040e5240104010550f01c0242c40d0101014500c158001000400074002c82160000d00b03003101c3c03d594a04050f190401c090b80101c5591b408401040300300100030a802100c0e1a40000411201ca86205189000e019041002250b02e00704448a030125946a5408010030b9030850300c0c5180004d19920703070905800c03030b607505800301d044d2104555806130002040c07810006204010819200c00e40001450988000400ea0141880e813581041404a0541068211028524641e0713619650040f01503681c0c031200c0c0742455946004800384c40c510305030008000c054801001451542c8460519184100020300100c030010f01020220001940d0740c00380c0014994003020800d940842804d000c4c10003d5800351081040c01070b001020102c0c2c0e10103041d680300d100081070b480440c64a900d0b050544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 581318714 1250 581317464 581317511
    0x8010b090606090d1e0b041a2404020c0706050306011d090a02180415050a0f0305100e0f070605040302090f0f040305090f18040501150b180a0b070614070f02030706 72
    0x1003085c0d000003050002c03074603005009074401e00c1100c40b0300040541c02c03040d80c0c005403811081c02520f2405140d000008120941203054018001480c15154582191828200c0e5120601058011007085015078001141500651643c2c08000700001900006220340b50000c00c07031115280d010a6410008042d840c0c04c000301c05000d4001c0007071300101c06001842e50300398820b01e07100d60f00c050350109114243ca4514800c407a0700200034030000703d000017558041c022044800b136061144002d0000345440804c0310b94011300c0c644c1c903150790302d5088d0700602ca03002100402a0710400703c0901032084400848248a901c00e405181054913990b52000003500300326001440c0d5801101c01c03042000c5099059101740c0035600c204000c204106041d00c00c2a1215054494441040d100703001002200310110301a10442c40020440ca90041e12a01c80340410b80107400d095580d260707101042d01d485000440040d4000002d400c00850714050801b0003940c1784910f13030004210039118443c6140700d0068042c00d604 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 581319964 1250 581318714 581318753
    0x703030207061401050a05011b0f0f080301060503070f0c0308060f040e0d020601330e01020a1509020102211b0703050a0b04060b100f030c12050c0408010b090606090d 73
    0xf1a0000d8005451002000c0c094503124426001000809600520790002c48110100b4181408031158075444089020448240c0f82800b0b81c440c8480018416001140a00410b49996031282401072000f030a2000303900241c02444114900304c80420340000c907980c2e000c10708490681d614000c0310003240181142003410600b82c0306101c0140160350b000700b89181a640c071906900c500740001d052907003490403030303040c0c0903030760014070b603143c181e50b03100382c50300c81340b000c03041c0100c0e4a12500390383e40520020713240140c1401c903030380d801e00f420444da410f000581300c00c003110041104c0e171041c00252004600c610504844030f081a0700415817240300a200c5c0d40d0085030440107407848403015013131241488108072001c481085c98074144429603c8c1150b4100e200c1b0b0115a56407000d40c0301c2d50410b80040100c10b844005202c40001030004410342401018450200c091035145c4441c50246001e00b500c0499031740c144100707468804c004880d00c5a0042c0c800303801045501012400701402c141c3d1906001480150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 581321214 1250 581319964 581319971
    0x903080c0106061206150807020c100809060a14060d11030a060b0135090a120f030f05060906240a090312020c030c040203180303010e040615120305070303020706 71
    0xc800305042d44890201c40c41d82d140ea085900c000007071001151050300030707642c00703901801e0500316452203801c0c4c00c1d5000c2c605004403900700c000704001418484102c10b1510009180108020720080244641c98000b00504014010040384100b88000020010300842c010f010100840702409014841c49018040c05416141a034009042c0b0401070300b5103180882c04501d100504900c4000354010030713441e5400c40c0070001c3c4c0b854a01c4507c10b404c04006401040b4500c070310341508011600a580120751003a2945510072000000c0401800b940c00d2102c1d0346a025150401b0460a911f4450202e640080200c0755003040100014081c04000c8003030b00c8080a00501140c07502c480c82d00030090b84240c0340225081308000310b181c0c07001c0b60340d003001001d425015001f880d0b100246081c503030080e68000100034814038485200d01e44141c0346030002d0b80680180f200010030b20050204a1044407860598491280f66281c141001408030380080800103003040000a01c000c14103200ba41600c0c0183d03400310f02030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 581322464 1250 581321214 581321227
    0x303120f060109050a060e060a03060b13080f03090306040f03051c0b1504051e032a0f040912052a0a0b060415120f02100809060108070e16090308 64
    0xd000c0c1040444485000c505215404034141c5800140c0c41c007103505955690110405600c103101180d00090f603078106054440002052600030707070011b864110707220441e00b440140782096241c90803441c26601c040940007000410301c1c540f004149282c1c00741d003020810320442c20924085520384203c01c044410100400c01c5106203903110b402403d20300360211001c0300c3c050042e80b201c0b1064800d03031140d15807214400541240f05000a031300c2c84e0802d41c00130190303100b40a01206040080f44d1422103540d41070707101501c00209141c98030030310903848016502044a1505903840c5409c610003a5191401d0000104101c014020030048484202100005858805201d42c5140c1d5480041401c2150380e01610800a103890070b0500c1403c8011f4156800360100900d00108894a070341081c0e8207440125414032000090384a07004a4240941c49035501203551234040c0c0000d04010041e040000c070354000308010071001481c40e2a0640002020315034011440f00302c01d041e51a03029950004003001e8001c01c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 581323714 1250 581322464 581322481
    0x621010617011a0a1b02060408010605090903030c0901051303020301140708070f0f030c030204120308040c21080d090b010b0406020d020102041d1314011b0804051b030312 75
    0x41d1405078006080c50140d880f01c5011201c82041c0000c0e001c03082c802c4c00b5400009104112410b2000c902c8094900b40c00d980381c0108034140c1c40303904541240c0e91140300806c410300b00030b520180c1c8901a100a58254240260600c0e0381c1e01c00c02d02e0881c1041804100b5100644400417402c00465009008100c500c08481d1241c1c0001c0b42281e18001090111001442044c0660b1903d0702c1035034161303901480b074103035000e00f50b006158403154081003513400e0101040310640030b03100d5140f0320300030b480f030860b1031400e494407246031001504450f404061106940110407001c801001c0d83d40d902070396a6441f0100c4450f510000c103030180e00a01001c4191000184200c12071300208140c43c0103a0941c0c02450003024180d01342d11031803040d44a0360341c451400b92405285070182030341199401008800101c080d0311281c0f060b031001d08001006942d501034505400c4103600170303000a1013160810601501c0c1545845490701809903480b520f068180d1107182c00c9560a000702c603402080650200c80c6030900220 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 581324964 1250 581323714 581323727
    0x90c020a02040b0d02090403050a02071a13081606051c091b0f03150f1e1512020d0b0426070209010e0426041a0307020115080c06210106 60
    0x10703030007030346494500c074124200f03e8481c206840d0050404030141c0c44681d400c4501d540207005180c110b00807140301003956140307480c4425041704030b0a0303c10b4540d9000d402030088240e03294041c1109130311164900c400300d0502c00d68032003166000e05100d51201c1d62241050380382058514074425031490440d000b03081107401d44075100d0349407400c090045016203401c030400e1002d070a4000071b00b54400d03120060803405015004a8070103003100713070701140750034141d10408002c2c20610600030313405403503500d000c003045e0208994100070300031900308801e0b10107a42c000c42c0d403510030240064051400000041e0030300050b0b0ba00503407015410b03494256403246040ba00c090b0f03500f12040c100e100e42904400040c0ca4804070060a0007150000c0c880c5400385c0c61401521400354108641d0074a280003030000059100314040340041020100604603034a00e00741c44000d0840321a10b80200301101c3c882c0c2c09100c001c2c000501125103010030346000d5568141313201080b249580c2e010100c0241c489800020642c80d40c4402e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 581326214 1250 581324964 581324983
    0x3010603081c0e010203130b060a0f0605042d09090507050306070306170a030e06180a1502010e0105040804092705010c0219030815010509040e07051003060806060f0a090c02 76
    0x707410003c2c00800c0003650b09034407040c0e445078108050302156002082e0711007107080d04104c000785041f4281d541c0d5207640c00c100b0718a0f84000c01241011800304800c901440b120f1030301000c1d080500c144d10040c518004c80d82c1406015516400e503452031960200042046400040e00c0b0040c200c0e4080e00e003c60300180900518040c52041a22710004a401b541d00010000311080e81a00c524071100094028410300d5044200b00d15a410f40d81450079041d5203900d55010081d01d240044940c104100c000040d0a698080b40241c807a83c0c501010000803d00c05800c0d5016640c103d4800701d40321071842c04040342d0b80700c040309241d4905d66401b00c1344100401503211800c5403d484c0c0076a070300f50814050000310040402406070100f080000041e1440c465050000310104050404070b080010420104046600c426041382240d4040141802035103810714249050761101e260622149003442ca4041d111880580800c1c018500c910309040c0640e201d490000140c4015070b0104010242640f00035035848114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 581327464 1250 581326214 581326267
    0x1701060b0327030f0a0804060c1d040c110f01091122020918070305100f0503030403060c2601060801060c08090906041b020a02130213140301060308 65
    0x164009141815102941e208600941c0610340410300c600354403075040c07500841c80010780010441403525040090141c00d242e46540c2d6840c4042c0380501d821021640488e0040081c030661280350210200e03810f142d80001141038801180007105200d00340c0c2c40e00c0105d282101c240c0203004400340200415803100c1c3c020760140080843d01d0318a00240000840c06400400003c09140d14045590410f90011300743c0c3c0802078a10004c9615410b108040c444040da02040080d850700240008404039800c1da0740a041700003c000d116a2806000079501e200e9440010240382d154803000700d040d070140395404019412500c0002101100d13a40200208009000d84000720341c0c500004100030780714014500c00b1035408171a00349082544410041c07400d40c008c01e02541305485401c03c0711801c28900b032145100c4d038690001c141c900c1080c41080b000906000031a0b9040d48103211501958002d60105001c03100c0002002601c80b284030042405041e03542c00150101900090520790403101c40c05460f01d10402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 581328714 1250 581327464 581327471
    0xe0d0807051c0203160804050a03030c020405060a060c020f180106020a031706010c0b0423150a02120f0408040302181603060501020c1c020a082104060c0b0601181701 73
    0x200c102d41a24051007031400c0016441488000c00801d4030300c4a542c02c5c540580c5045003080c1e5207100007803c01202d60011400103034007406210850401e40509508280210340d400c036500c0c180034004041a10f40100a0721030422081c010b40c0c02e880e80c0020341541d0140503510180c1d907071039a8001c0c0d0317240c00c0c000d400c4000036809503c060346907400303103002401800165511800205d10f9110100d05410107001aa80e034059400b511450207444c20406014540c0742c4003416086419044c14400483c0c0101100c040c64010441014005a030202442d44920704640221803038440742000490340c080ca41000350440380e4800c81c0a010b009090f00380c1c0c46268450010b54029103600e034201d040c0c2e2241e00c541c60140e8002c0582d50380307500e0300756046510014a51141600f20881d6000128420780c031303910107811a0428103404140c4600c120f1085102c204407803010345003500d0900b0007400c5250000c40a040006080040380841c0c2c460800740b2007c07001d0381508200141c640450b40c010264246009402d50f1a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 581329964 1250 581328714 581328733
    0xd0809030d0219080f091e1302030c1b1207150501060c1a1503011e0501061d010c03030e011d0601050301110f0d021306021b1503160e0d080705 63
    0x4009403d01c1c890845004844100f001c07aa90401a50000c50340200a81c2062001c4d84072030b140c4000b048900030305211140003100d000c0b81401160003036104031408607030040040002111007042226043d660100d0800706054040d610142003040d800b0100070100400105a8244052120070603019424590100496643c81d8400e6409030070b03c0714018004042004c0901c0c4024044080b5588003105060204a01081400107400c40b80c170411030744080030080440300315030b0300b0714440c05002d000f0508198017611191003c40c0340e0140c01d1003015040019401b000381c00c1511940260b17800110f01c000902080b00c8044403049080c0039004020554411a00005030502d414000d85c0117807080380da55240340c140314844014042e440111024a4681c0030001140e038142284013039401002c20307502805c180000c040d40c00c0012452034285510946480542584030b40b90f0b44103c0340c2010b00285682c515200c24403098440060404209a22480d90748580303046c4050300008000c05071040c01038450150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 581331214 1250 581329964 581329967
    0xb090118030308160806180402011404180605010903020310150b030903270d020906120a0b0a0507030204060e01051c05090f1204120f0507090f0219090e06010c0807020d0809030d 78
    0x180b040302c1495100041f1a6010300808024465541140c010714011200ca00c100c981342440c0d5101e64000301d80c210301e01c02000d10242aa1241c600507100c24030b0070501091075900000e90b5028034a0814419650307484008078108248000314004000c00c0a10f2612850041a01622504001c40300c1103480d030103c034810040c88901d0800000c0d0b0300c004162441d0144560207100281c1f1000380059001040c803960340041c090b00308000b054417481403203403201c545400c2c01c5034400daa602900307a13028140140824408181c00c000e041616080030b20f01191500e801d990803030302c18060103c0c03495042d4604014010101408610082c02d80c941234100e0b04d030b12400d840814050f10a034482d90382d40002c01d5034284000703150002481d50ac94000c074110398410392a071844d1422140c01014000f1120750004500c4803403003c1064600c140703006030030221720b1146400355208800d1001440c0074100103011001004000c40103055603041c940140c510a040c0d846031401c03d00741d511540a0b02d00ca88102034004424a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 581332464 1250 581331214 581331227
    0x10c050a1107060504151112071e15240e010f060c02030303060405070203070516030309050904241d01020706150b180111011406040e0c0a0b09011803030816 69
    0x2640c2a40d90985030a1500104d040c840c0d0001b0f0303400081085800342d490341c2140411070180c0110030f01401d640c0e00d202e60318012201c802c0800015612440c2c100030760011910a9450f2131055076100004a601306000803005c8000c0d42d180c00d4400709200b81c600c00b040500100140a040c1c13030580140b00d00c02a1164030079520101c000b04001e41c5a401000003840a05268000c1074200c4940d00442e8108051070b0340b6603081c84000445940000f061043c00c01c10b0603030000d00c1000400054030402210b05198a443c541030707d10720301c6051032403180d254480c90f581160780224503041403105414412002d01222074040d6001c80c9080d282e003410030240007400d0326004420b000b11407813200307c50f1802c01c041034542142c03d1144003060520640e2481c5403643c440c280200400281446135003174940c5011410081203030300141005041768080440080541c42d00014003064130304500d100364a1782142001241c0e410340c1e504645480712400c1c1400820983c00c0155640a40700c0c40c2c280d805143d0100b28112003d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 581333714 1250 581332464 581332469
    0x11190302070512190501151401030c030209090a0908090307030b0a050c09060301030308190f0b011404051005090303040f060503040512091008040f05030412290c030a0e010c050a1107 80
    0x190004188841809030303061480084e00d2060001044080c0300c20300b550729103951680600c004940601040b81c0560b03061241224600a600341141400c0704e81c0041005c40300010300c192540ca82c0c0f64604e100f4440c5e03444c181c55600f80c0081c00c4030007a81e181d1420303182016060b9403044c411401c00010580f84042c240559114000190404c1d0540c0c3c0f854400311060b10b0b002e041c0620b0742a107420f09007130315400c3d0700461529608184022500c40280307800100750b0852115104090f510512080c045591801c00060001c9020726100c0c2d15030800a0000e030540c0b04942c0112000c0200580001e9005e400101a600c140d01030415521200410660442c0314400e4040b1540c0c48075501850054050240803840c4d0054041e0100141c0d025060b03039041d01c0e40e0b225070400240c208075a181d21007001860b0944841601110042404181481201400110740030705000c1100e500400094140d0400d076100016511515000348610301c01a2005410f40d40507428160008240d80c0000d841d220b00000c202c001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 581334964 1250 581333714 581333749
    0x1110a03150e060924030d0e010e01030605031002090103180b01030318030507060f1205150406050d02060d09051911011205100603020c070302031609060f061e111903020705 76
    0x15a030300807841d8a0305030268441c1d00041c0000c480d01c20186c0b010450b88400040c0d94581800b00008480090205202901003a0405042030401d01c41501d02052a80703900c1c0c0400405030321a401c18005802800c00f0481001c5c6001a0601030020f0042291840b41207034002c2d10b410f28a450181084045443d60b800301801c15808100100015442203c1102003d09146000160340340031401e100306640c019141c5045860094016003c585494801c0780001d140880340d03510fa025080c1d000c541e81e8029486092050f0741c0d243c14900501006021000180c50800b0f5403403480d01031890038080a40d03000c04142d00281c00c0c9500e912544445115050007030710070090900c500b41c903121084000e07511001900b14203016000c4000010303281004842c5c5050311301003d83c0c207a242060756003001c5842c2c5520050f640c2241101c20041c20741c0110928076055415000464540800341c02035403080510980c1f1038603071103801d0342408012841403820204600c02d500350f0301d40030b558008002111074007491902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 581336214 1250 581334964 581334979
    0xb061c061d15010c170706150b1602040209010e220b0f0f190906091a0102030a1403090a0b150a0e01060e01120e0a0f05010f02040b0306100201110a03150e06 69
    0x4558007492890f40300030b10803503480b141182c0344005c030b807610b4000301d800300c2d0301c162680d0700184201014404030024100d1118800c1c03c000b442e583c600c40d030781003000020340520340c001810a040d91154088558824000d0301100540100c0c07030350408000c10f01e4030009000c900d400031003007681c9484085410700742c1c4020030542c0d490014404103c11086200743c1c1c804880260440010105024002c0c40d000f801646000150303c9208803041c180065035842060464008100d000405900400b0401c0901509d0500580303da944103401803400e02c099401500225451003080b81d2481c01188030a80c50300240c0b402072902c0e0ba42c0205001c66042805042c1c0841e04544035400594451132040083c01c00a4002040d00c900704240c0c6410070f2104282070ba0780d90390684c0441c040c002c0c00d001c0d07581c0c43c1044000440c5060b19201940515003c05030a25100368404011031068500c01d4100f0741c04514041e805903078408440101400030107400001034402c441c4000c0018065030440300180c440c90005d071211 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 581337464 1250 581336214 581336251
    0xe07060e15030a0f0e061810140c0304050304090504080403060f27050a0f12021c08060111010209031b03100b030a0308100b030106020a330b061c061d 66
    0xd02c050100e88640e840030665910005284c4d05c0c0802255006000d034501c00c14070803050358013860510f08410811303156181044007140080d2440b0410319440050841010f80b01d0320385280c03407810740c4075a0340002c04c018104800d000511000e00014000ca80c411a001c12189400080703103016140a520703903000707210250061055a035205910000044d10440c00e0324812182c0da642c45020500d100010355401d0f800d02c2c1c0c81c20760503404009014002a010740c00401c98034442000070100e02d070082119042010303902c607242c4220025015503010f89002400e0302c0d030098ac204582b0010720f40b248191403092090000f030085540e003500c0740004200005c2e0150401d6986034906903000c40740640785d11940019003900043d141c00c04009940600354590141200b80784604050400c505442c402c2400311400d20303e09016404040c480a15281402002062402c04500040c0700c90240d14088007a020740c0b86a90781045141754031120541d148504041c0010303015a400700005030007204c0102c8800441c0421 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 581338714 1250 581337464 581337481
    0x411100e01090312090902030c03070216380a021c0306080a17090d050102190806090601030509070f1202180106050d0b0a03020d08070309080609120d06090e07060e1503 74
    0xb040f05074016411708000103541c5107007000482e8001c031000b618424010081c400e0140e41440f0001c02c240d40c6084041202d400d140c1303001400c21203a411403240806d000e1246283c4030300348000c42d11020402d00c04d59221248048080c1d15504210071642d2280034803e10038901c24001c1c4100c0068542260061141c0d1001e0340e241070a4404251700301c0182442808903100795038504078418803582c407480025031507610140940350b14118000a203010300401408001d030310723250319200c5035010b40700340703408600e83c0ca40180d130701c0c00c20302c258000050080b20b820000c41d6810f612580c10b2020744c0b00b9900001c1180721001c888032510420300921001400c10025000020f4968010450001c8028500c0144a6407580000c00710501c4000c21100b601012500f40281a0010108001021074801900c0300b483c00e241c045845016410031001c5490340440d00c0d082140340c9500c4007000d8403000c2010085da11904030302039910b016134850507001422014900c6d01505191071042032080c8280c10490564031561003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 581339964 1250 581338714 581338733
    0xb1c050c0702060a0c0c090b1c260903060130150f0f05090106050f01050c01060e0a09050d03020901090e2a0a0e01080906070809030c03030411100e010903 68
    0x24128582440741c036015984060051243d070601d503d40e40c2e09000d0384d24044107890701ca039000d000c07100e141080045c000d44a540c6d0301000452068a10ba6010400d031a1404408041c5400e014080180525440c10702014600a0581c540700f20100c07101d9a80e241808118410000144070160500c503074089146651506d5070087c1030300c40e0380c148904403001030300d00c0c048515160000d24496180c80e130a444e405050700c00c140e00004c06000a00c46642000301140e01c0340d0000b440c1904001001600503004a030a6101c0c0b80030304105113140a02d030400c8a907610103048116806e132694010120815000c600a100300c80c1e2128043e107841ca410341c03500c00030f4141d24100401c00c40141e0055aa50301804c004900d005121050001d08140c40d45254030700101903a40239207d060500002d001070294450000680341d9100300d0a103412030641c1d80f00c0e0322480c01e40c0204031405025100c0071042c841000080385950360009816a8805115801e1440c1110442c081d40b00c190f02203001c484052000c100a00d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 581341214 1250 581339964 581339971
    0x17010612030c0c0b12041101050c21160515070207030b0a051504051305120f030a0504022b0b130f03030b06130306050121381303090b1c05 61
    0x552000c4a9a0352403008915170320024000004481050410081003110a0100d6034800286040741c14100c04034907291b541d20010f04181001842000260100c02c03990003101d44a2020180c284102e010310f1a04990322001c0400104908203c00d000600c0300348001115000c0382c0d004004070020b81c9407001282d0081c0000f50016064a66102c40311140392141c0c05114010305822014043d40d00450400304e0a101c8485591801c1000800400c807a42c00c214041d00e411440124000541d40c80350300c0012903190413803039813103004082008000c3c203484007801d108900394013544c40d1000e07581e18800f02071f401d0141984010712241d91a8104d5021921039800140449800f918881c546101d0b24500b12592069500480d0300b00e4a5000501108103003207070390103100001c50745007200f14605683d40540b181c10b465000b401424544610150851030091800c42007460300c084642c9400d15070040b1540881804c425000314aa030080000c044d00c1180407160506440303904500e00024102c8050040c0034042e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 581342464 1250 581341214 581341223
    0x40c0903060f14010b03190612172101090f0603030c0b0a0b03060c0c15040c0e07230403060e0d020712050c0306251103120402060d0f0617010612030c 66
    0x409003c0400c43e619a2030f0340c040c1c400400d6a0340c49203080040c070700c407040c560b101443c001c0c0e0801384104005526404140c0e10280e04c40303c280340f0080001c00816990281e00019503400003481c4148428406481405041c2d403c10a028041da061441120b0260b1b44103100040014540961084c0880c100b01541a000300ca069404504440c1c0c0ea400079191000c290354583c1c03000e41c000f034002d8101c80d04021010000c180c602c0011414034068541e0001d030249803240100c21007021001a0403c0e115040d05c3c02d814020b016021548250012041c0741d6410074001141e9041c585004882000e6001540c4001800640c1c0107145a900700451f00782d80c1125403000315001d12a00da42c09806a03410312840f84590009190407004001d0301055002c04e040031402c40c010310880217200394041030084200c490818452411444076221440441c00500c91a02c00e0603030980740019482240d031240e04048102e4902d08042c14040c442502c0150884400c2e11941480c0c28507046410700003030090090350b51b900e010703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 581343714 1250 581342464 581342471
    0x309060708090901090b04230126030a020c040b04020315060906040518041a010b030406020f0c0a050106080124090e01020912011506050a051c0608010f02090f040c0903060f 76
    0x1640c01103281640b017a002001e02c00c0d101c540300c64a07800c052003100b90060103148440002d000d40010607c0c141811301920f560803860810034004038042c0d601c0800e44801080c2103a075568010b030402900c440a06c0c0300c030380c0700c0c81c100080c160a0346801e0082c8c03030164551361141c41140700d0300010000e0540c450890642c0005080c0070008180c0e461100c0b81d100d07241c00c070004030315515041c6807444d00e1380401103504410084040043c0f1404c1c4880090320380c015444080183c1c1c80f10810240701440c040c03a035001d0114485c0510f07510030408190454421100c0180003440305c0b594855803151080f034110713040c00e180c2900c40020017600714903030400390b40d42c246031000602e00546180803515402c1d1201101416a46500001c002000070850010052400c1e02c1c2650501078080c500400350301c2492403e00c040050241c140b1491304c00d40d80803500600c01000200440e01440d1121000303500070003150f92059218a1b1003e135070b410540540519580241c4e1540c14180c203543c1c8480c014058900c148854554 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 581344964 1250 581343714 581343727
    0x6030628030b19050408030a090302070e070f080a0c0507030804110405091b0603060607110f0a140f030127030908070f14040905060c0c0a060218031e0309060708 71
    0x40080640041c0d4002d00808005140840c04480d0045084100f99059072911040001040180080d290012150040440e0440543c03c0c200d140c01266003080c5c0c0c461401000f48034090360001c07122000360720350382c0750000725540e9250141c046603900070302000414020007072400000c1c0f00701d0080b40c1c070038852801c14000d034541502041c00c036801100c0c403400b158841124421203d614201c1c00030301707500448410b0b00c2d40c0f40c100702040560060200c02403038a810804e0800c039555540141002c0c081d03018001c507800598403603010001d5007242941501075048448a003609040600802d188000034010480c07114803d1551540c40d401b03444003d404000f959203001c500104c050200700c008050640e0f111403a04e04242d5036621410451564078440c0b450f0070701900000c4c2001c58420307031160030030a03502d4590b03012090403401c05e0002e41c0c5c010001413002802e148009800b000c1c44c806c00405408540d103c0c04d005818072109040130075440b644d90320601c000f0350103250a6005010b858400d6a68504203103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 581346214 1250 581344964 581345029
    0x30a23010609020d020c15040c0b070326010519030b0114010504150f0305011223280b07020a0309091d0303091f0b0616110306010b07030914060306 65
    0x8100480c13103403000c1d80001c0d240400f2542089007000b111301c1001e42d1100e604141d5580e1407200c2c0b05100b410404240400c0040a15000d5011030760341c0c8030640403501c0d640043d82200480e200c4240540c501c00c840003443c0c001940411541401602d5110b0f1180302e41da400c101c0080d6413030401504441c1081001c001c00309100000e82c00403002b400d0070f6103c0d0300c801ca016080190595005801101e644006000000042458001c243e00900039406840207907040c0f400d041070414040d21541ca00c401c410030050b52600350846c5840f0b1006000c0c00351003243d51203e040032070303e442c15600c0107000608846c9050102c0012030380300d889007411a607000c4010178602e480c0a425900201c4118100d42c000e003e50f6046c0041d0070b405a014003044400402c03521510f21b00041c4180681c807d0310000c103800031540e10403c21003032245001c0c0880101180c0301ca683d207042001e420391150398200d000560200c00014640911201c4008580c03000707008909503519501031020303440204c1d29002c00c1340284c990a0f044031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 581347464 1250 581346214 581346217
    0x80906090a030f0c0810020c0c0108100b161208040f031d0a170609071503020927180d08060d0c24031107120c1b0b0c0c030a2301060902 60
    0x1501c40c4c840034203250701c1c0465250030011801c419880290040014007000000400c00345110482400c0c000819241d100316100c025000d6041012016800160540710200d12050860824800c07061101000c1c0000c1301215070120a81d0001e0440e040c241c403840c0068024284c12841082c0f040840907030043c00703000500e442d0f02640c010300718113040c4944000103400600110303500a001c8002004070519010090403466845c00c1013808066010825000c199100c0b4401e0b1940300c0164000c4600b45200c21038003912800584103100c00d03003240b99548541d9200803840741d0400781291107510700760351000d00348950f0360400b00c400c4528080c07070400803400b0864441800c4081c000000c00440390460444041c084802c41c41f90050011800e10031240000c03031620201c3e03080c2e6240c0c544004222090724207455008003064400c00074203051000446c4001041d00a840307192001d6044900f0f6000c12000d048e190040c2c41005445100c4400d880542d070540c00c007aa002c1e820400d0300000c0c2e0f659881c00030404a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 581348714 1250 581347464 581347493
    0x5160f050102270d02130b040e0102070c1e0b072a080123090319051605010c080c120408130519050117162d030b030f0a080906090a03 59
    0x2400060201030b02e103c0a066615001900c06445041103220640c000401e0140d96101c034584880d120f8060500541350380d044402d10b4442c04009544403440d03403903e45841051405405034581604d0006002d0304510010314045804801c0c01518080d4641c80300c3d4200e1110b84202c41e00e00c1d105c2c840d22004402201017610040c51160000100402e40c0d61140c40c0310b1400006c80d484e0340303c00c0010300c04880c00100445130f010540e0b42d90b14078000038102b41583e00d03014900310803041140740003228090082c1900f00c80c05c20a01542d51000a645000e070788101401120b030045410524500058000356030710008044020f65900c054411580c3ea60000b00d90004540c26450489440302e003c21407541c211120000a03c1c1d0300d0341c80c8865243c0011091040c00030f440507201048100c45c0d803441b10001c0c641c1507200c1b003207403009500014a540b1101a01038099522060f0080c400d01401000840005c20003038910303640140070354036000740102000700c96004a05250341c0700409240000000d450100035111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 581349964 1250 581348714 581348737
    0xa030c090506180a0504020a0b0702010815031c0801082119110a0c0812030f0c070206130e0610080105031b041d0a060b01020706050d0c030b090c07051c05160f050102 73
    0x84074031b03281c4140004640954000d11018606212010040c1e804c2018198880804407080300c8030b000c00c800280c5402d201c02c00c0c0c082101803690303081d4812039111170054140c0300c0d08000c0711484109076140c5072040c0b0b44c42c50000c1e00c0480c28819400500380684980103c0449460022800c04e502c2d40c0c130900b00b68a103803040741c84d55607511040114103424011802058120b801c11800c62030001094030034014000d101f00d10200340014035130304541e508800e40d00d1100301c521512042c4c0c4d0300d170940380902c000280c40092145410410b02032469100344042c6068901c040e0151541843c000032260038200c1d981e103600d6000f915285003000d0102424100d16030341c0780031130080405103154100301d01105c0303040c40d00504540102d1001d200e8507401400b1100c440c9850980041c400c0c1003003c00310024082450f6403079200440005004002e2140800741070030321b02600c16106205500d0f0002540f0194807020b6802003201400548220004070b14941a258018000039084281c41c0da5103c1c226480700741a0032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 581351214 1250 581349964 581349971
    0x703060302130c020127080c1501030f0b09062401050f030c27030c0607031e080a1515051e12041101030e060a0b0f27060a030c090506180a 61
    0x91040b542400740f03105000081050255450407240f00620030400c0c01406480010000703a0f15202300400c0010544282c108440300c004c0c1e585a152510a40704103050a8038000e80801c0400c10001d0b0202d80716004502ca40312404110b400001c598205180c242060b034188a4180700e4001c400100d90015480f840b000d0407129554005100c00b034031040804400c1c02c4c074058018a00044c0c135240003580c130300c62110840700140c0360701280c507048a203086d514411810546500b80301691947e080b040080c00f4000c81d00342804600f800401c159070903661840b6040d41400340c3c811070031080f07005400801303e110100495104403c10b032059014150302101120702e81d03036211000c000a10a100003d4002c651003440c5c180242501076413429991f42002c0e0408108030b689080446880e550300d0f058100c0c824025001746d400d1458200b4079980c8c1e80801c15010a03030003141000844c945401100a02500d502c03610007102c6600f00400c030002404010881c81d006084918803080e45100d01840754410401c0c2600070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 581352464 1250 581351214 581351231
    0x23040e0c040e030408030306040f11270d030c0b0903071b051009030b150301230f01120b0a0504083906150d051c1d010203041d070306030213 62
    0x200b02d038404580b00225410500040c40110300200840703401540482d00072401c02c41d074001d240000d154031108a1207a400c0050b2403120381c014411150580d24642100414101c1003100f880010644040c0c0100002c400400000000e001c0e0740341550030551a00403681030045030303655074a00c0304100740e0b08955580300007002c018a00d0006800080142ca606c0c01b60302907899035036007007100c08016001401200d000b05148505c0e840075401340d80807003005107018100000d10801000034003416241c00d64070b821108004a10031000c01246421305030b002d0071448075691003002c0b003001840c003e0422512031804101d680e100350800c0418820710844540d075030421a22260405011800a489180e86500580e04008204070003040006401800f6070b2464580d544601d040c900b02503601d0380d840d0705245070300d6501212503402280440790182c101c03055200040158016680c2c1d00481c4603034200342d064511201a45007546854941180329810049480d9840f0350010302904155601039080e43da442c45c41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 581353714 1250 581352464 581352469
    0x1080f0f0a030e060d0b13020d0e030a02120307090e010b1911060a0b01030209030307081909181a09190c09120321110318031323040e0c 60
    0x190903960140104038002955a000e480484040d1001e44158800b003640700620820ba000f101e20120b000300024114440004880000c1d042800342800107450280440703420040003046582901164000341001551440c1c0d25a8a91000709031000300001c2c1000024001040c054003406404a102503580b82c001d07803007031004c003088491b80c21020042c003020f6207010108041101a00807528903008101c910104005030064459019010f070103101c00a03100c028003800d00701070907551101034542891048070340e0003122406400e0256158500c414200341070a02510b0384540c001c0e1200b00c220b1a01400120300003002c0c2c0030111500a607000c40c00600c544c00070301c58420085419541d0030440c88081c24050100118600040001c0c01d1003410407000131010311400ca00111810200c03000d0007a012a44e2261050b40c0082d26014040d80d020030b2461880302c404815507000d00031550b4070810f0359140400000c12040300360130210010203800c03802e8880c1e40f01c0c1d00a008600181c0030003010f400ca4812705 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 581354964 1250 581353714 581353723
    0x2106090302011407020606101107170109120f0203090d06060302060307030b0a060c030c02100306080604050c03062d060105090607050f0606030304030b010905060a05040c030e0d05040b0a05031305010501080f 91
    0xc2c550854102e40c6c200915595008622003200c0103524001c13426800c540112171401e0400d8102212045c40e040c0903445104054002e403100501c10400c01d01c284030039000c00d41d039038480c2da015031016802c1401a00c0f8541404110440d6807070088002180c0aa584d40100d00940d00941d120300000780c03550704420140c242080f0660040401d403504202403080d9840091103014220302c001c0c8182c040c2c3c400507039903c0c03190b04030602410110f01640d400b402d00d443c10968030202030710581d01134020000041c640400c0c8045440c201024103030510b0414000101c0c400d40c00000074a01418400140051102c2c1d80b9100003a190f220720a800401303403550318406544c5849001080c5a1182d0300801c02440007034540f1003100e0442e0410714000c1095103070907002070902440c0c5d401150300181f8007038000138800e0781904103507003440d40071043d10320740c41565404490700e00c42c0b4015480d94520402041e001e082c8280010342d0b10045010b107441d80c21a16607035a81c00c0d15001c0e845200b40c0d51280842ca12915401d11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 581356214 1250 581354964 581354971
    0x2130b09010806010b0d09060e0706090303030c050f0906070303091b0f05240706091e06180c14060405041409070b0c0c3d031a060421060903020114 65
    0x403c001d40c5000c05000e1148517416840c10072540340c9500604201640e00184081d65044003522101034803008000e1200340c1a10050700000d04028031040c0850160303080340e295814a11000b0b14281d811024030a0560040344101c04040da80d040c407801141c000029031104003005c43d16198000d1403c00301b1903240d41150402c5220b0340000e0080d801c02d0205001b125202030540310802c1c0c40f41001d081681c000c2002d400094904500e180c0c0c0c00704c2d200f0300c00c19000751a9104030b9003008080310002d04814803c0034070800400181180d40103001c8400910700000c0385800007004039203030a07210000308064503404a28884210014000d2103405442805114050b0602200b40ca05108191030455030326003050300c6450264410076450204404024001d43d494000c80c1c901014005211800551018064210706c00191034030140304000c0e02c0f5620071440d03500c002080c03141000c0c2481218144803040580380400300310320b1601000000d146026843d1080d0007a0000036332007000b800c0a66503101c004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 581357464 1250 581356214 581356229
    0x51020030d200a08041e1208130201020703060e101d25140111011404020109080c09010b0a1b0302070810020316030504150608010e07060306060818010902130b0901 72
    0x11450400200c000b1040c0c400c0030f0164a08940c064a80b0b081550200344d10078032040b41c00305510708180502c1003180320f66071f0801725035440d4401d69542c034aa640b006840c4000090068120040400108003150050b407000512001540c07a441c0417107004e00100c030f140054500514841860000040200307010302c5005100d00400782954402d80300d001c442a6807180101a182c3c481d030803401e00c5d240d10401c01c070310140740d80341d00805c09035140c00c1c008401a882290124001455803c010030301c02008140904010400351040100d039081044901d45904061502c204205020020304146000400c103401c038140a40c01603d0405c1c10300840c50f0510211303000081065004200703220902c104010b07034091481951070000f60544980c40d02c41c01c209503c20091003440d00b02580442c5000c810342c400300803008200105c0321002d50700d4805405a94107881303034401144008000600703189034038140c0031840e01c1c003100004030b40c0b0060b40015a0240002c440c3c54045640e0302c060030260420038591030250544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 581358714 1250 581357464 581357501
    0x1030b1201140426032d15030c0402041a070212150103030f0503040206090603090c040f0f0612050d0f14030a020306031905060703110714060415050709051020030d 72
    0x601d0904140c84040d141e0406d6040c00b09084209a80c0c1003d21301161550b48050226824040003c1603e8800100300500c24080c8106e40162481d26200b198101e038070341e60400707100130903187c84080d807030300071141c26a0803028548085000781c200b0b20110814440324a200d0186504600700185407101c0282c2c05014400208103000c05640c2d10001c0d1070007070004032111980c0c0e560710f00d0047c1c00c01b41c07903208060b00319040030f44010241c800f54010304140b0000b000c0810655640d0340259403100010740c0d01503e06c1e0418110018858407411816203805903908083d00c01440315031040c0c8542e402200c005110036404014008246814000d40c008918a402140d080c8803507602c2e6141c8440026100506042d40c81004142e21000e080940310032940002c5000d00032816280ca1645412045800711120b10448a00002d5804244107490040301c4c1503941c0c4245500341024441f1550440d02108180203820000d40111601c081c0a000300404040140d074031210304410f0901610301c6da1985030b01d25075a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 581359964 1250 581358714 581358773
    0xb030f010f1a0a021606020d0e0d0f02060a0917071d1b0a140f0c0606090c120a111303030807090b1806070c0b0414100503040201030b12011404 63
    0x241c0300e81495980b002120015070b150341402c0168908011030240d055000300b40a8002200ca07004103e0078040700c955100c544080c117004c4108842c0c1598410010b00d1300d0740001e4488094144a4054882070201d401c010718015100c803000c10144408503580304265200d00401e200c0d09030300356000e08510f042685e000c035080c20800001451140b08141198101d5004180c2000701403050450390391051050a60f150b44246014410520b6407088000300e00c1c038841c200101c1d000e030501d10200752040b003d180d002424800281d0030701c90003250240c0752403400c0c0c3e200c0340c0c46075403008120020030341315907040844106280f031031901400d400ca00420341c81c10b001522004000c1d00703214004880424081140c40c4d0811114030000a02e00e005419014003041001c0002041d10000940140f051303600108a003221a0300e45020011120081c44d8664005242440460010750280c0c00c00c4810000040040c00a036554a80b15400c554450408a0f00c003e2690144424070041030341d5034810b18454030041c880541d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 581361214 1250 581359964 581359979
    0x604081c05010b0d2708031f081e071706160203030c07020d020307030c0e090606040207020a03081b061e0906090a030c031103030c03150a0303200f03040b030f010f 72
    0xf521101e07904650302c076030401500316201361904c14000d041c21417000504080e41004801d0703801c00c6904e400d41d00c1044009412822900080178103da60100003891101040211700d115804440d07c085407610a042c0007060b0865102ca9080f4020340d014002c068607d45401c85001040500d2190300a40d0000c10074054607501030300844007207030b4065030201984421803001c00c1c60703c013659001a00c00000002c011071300407014000c450040200b0030446645450384001c020403441401d100039440310070300070100002502d88029103004081d041c1200c07201e55405a80c1030520004a80aa5408041424540040c17000b6142a81c0003202640204414640040c407103a40f10b13102c86001c0c00b03200c1c0d900c2e41c8408141c4101c01c0d0b2008a0700100a4075100d003052070003840503801c20348502c41b42070680390410800341013005840003101e0301030751079039409076509240d808003002c560155019030103a0340000140840400090008018064120399130340341004840e00d04e10b106030400c403507800009101700f1412 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 581362464 1250 581361214 581361217
    0x20f0d1a06030114010c050a030e090106020f0714031905070f060e030714060f0a2003070308070e0a05180f010e070c11040209040504030c0501050705120a1d0604081c05010b 76
    0x118841103c13800095041001600d00030140030000f0700d184910350780c070400c040d0300041c0d605424105961003051a601c400d42030341c940ca40201c3c65a8541d00151017080008585403440714550000340596a014101501c2c4031a103112074442661150300405c000c005c001281e0074003c0040c006882d04514010a00e80002d8840b00d00e031007005501741343d4000c8189240c1d20304080f05c10442d580441107507521144200907184424400075402c0704082c0590388540c01002000310b400941e419600c42c0320540e125641516044804412140c2004200e140420075440384104080c40400391201020545481d004c05012000140c10203143c00f10f01c8000d01500f0b64000094003100381d44241c00b140f0003c107000c00304009011f07031a207065009062809010605410040c0302200d107010f40c1c000d1260340d03030b00300d03060b20b00d40724501c60860103502c0c10002584c00130190340b044c200700711007160050030f10f101c0485161528005503000d0310701031400075443c00140c0c40046808442510310301c040c0a00d624100028505 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 581363714 1250 581362464 581362469
    0x51b0d09111e040b0103062607150c03301b0504030201020703122a12031a0603040602070803071101061a0a0809010f05191406220609020f0d1a060301 66
    0x12a200c04008074280c0c007d070030040143c20110102e040c00c00c00306050160800d4110000e1740347d40101400403c5c621a0301100350504e44240d2a488004107099404440c81c102403007101030054411080500108000360443c0c4022040306000310b881c800144c0a034010780a0700024800b440402c02013003005036004184a01102c2d00b1076008550016a048181c5020340d21087d8134070a407000442c201d0b50b195600e44100030b1580078060f1f11403d1214070f4001e404a460002500c034000c00da18940501d2864844003d50340644901c50240c140750711962855000d030000d0f1792540105948100302c1d0240f260911450000f416040c241c590300d07455141c40f410280c411210f140041140c41c0d800600e8034882500801c5038139617000000c2000d854080c0c003c50484945444120029060a81d01200d944622014074000d130002040c4840403000307680c003810380c140210b09056916440c1c0d04001107183c00c030b1000e090880381c5151003541d07443c002c0140d10112100307540d601c400c10b1201c02c030070005034880d002640c0c107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 581364964 1250 581363714 581363719
    0x30201080c03070c0606090905150103021c0302030f0a0206010e13080307140903160603141e04021915080108010212010303050a030603080706020405030c120d03051b0d09111e 77
    0xba0394031001021520303004140700160040b030a01c0c50000d8100915440a03000034010404e407080868a548012403a4038284408ad6001d10010950008041c50000380a83c0328440d0040701d16101d030418000764190418580c03030001d070f00118010081200c400c80c1c02580314101120200c00d4104d1a5034080f180c0c00054140c6081010702d03240d1504051001c8202d4120803401000c03141c85414500e08401c0c800d030140104400203040000003014200d8001d51540640706420884d100751460b44614201c4a030000d10503030303001d0b500c01500c503c1c1c00710310541e0710003424406a0f61304a90151400140c41c601040e482521039a104111458440c6d45112a06c1d0650340d1510301b0750355035090300108030301422003900085d02c10200064000100301899008004581c0107800fa140103003040400c111050580c08014522500080504651280700364800f40e0300211406402d5560014890a0001c6412025540350344580e5401e0000c148400c0e10b062015002e42203903c0c0380207a000e40110031154a003181981e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 581366214 1250 581364964 581364967
    0x13170a080417040512161710180b040804060e010c02031b01090902040609031415130503190809010b030c0d0b04060b03030a05131406070b0405010e010e0703061104030201080c 77
    0x20800e01e42140c1c02820020841720380407915486a17500c403419071104160320410803030005035514840803403a0a214480000c2d0800c82c3c0301c00f0300d1002a040300000107010b24080c0c3d500e00001100807907928001d40c064000e80d034465040c01c2c000f82c409403841446078140803a1220b0540144d4002403842070003148500048541c030800700c01a59580c21540142d800c490000c10003155841e4880038000c1124000c0300005e1503c190501159211030f0100c04101c2d0418074100043d03240b0100301c03815050940b040080702d1801c42250070381c4d03c60f040200c0407140060b4100c0705001c2009024040e1303e400d007800300d02401c001641e900020354030804180b0000d00c4000c0030302c0080c007480890341c003800b210305014050300e40c4c03036580010080040c1d02ca620b030072060301c0300d4805c007103254202c0300c0a42d030003400d016290501d0705160792913480209200820031910b642d2592400381d1040ca00b17014409201146400602c101c60440c9041401c0e110f078200b416040f980107203c1040503030303400031115030070039400c00c580c1b07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 581367464 1250 581366214 581366243
    0x81b07020d0f0c08160b0a050a050a020a05011e051b03151906021606090b07061a03100e0705010806062d0c030403030909050402031f1413170a0804 65
    0xb80d4200011000381c1002c0501c0400a00c102000ca0322401c0311000400122415072240031b80a602d001c0c802c00d5000041c030511003401220300035030041c01410020b004490800d02159105404c1d20008201c02c004180540480c191407200c0f80940c1c3c1d000070100202469005c109541030000740001406c40030b00070031680074103140d41c907284a6528218503460009840940343d80010b0360307800f642040320340c8140c12500000b03500c40c031400d07180060300c0c2505001d40c9844450744660010b05410740410410b0412122107001d5507030100010110100b902c0340206454038088902410003840c1e51000f41808891800c002159842e0b104640001802c10303031030508500b031000c2041c940a502400351807403450000d04103d0304180000038004a901c03c1d07a80f050400e445200760b00a0316005e9800a426074070280c00010082403140502c0070000703075000c00181c2d00c54030707a4507407a440c6c1c019188203030454000c014490a000b03a0221100c00158414050751410040c58001000c4600c010000380045e1100d9060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 581368714 1250 581367464 581367473
    0x10807030e030304080405030c092a1b070906050307030305121506040e04021f0516031b030e040b0616082b0510080d0c0b190603050706081b07020d 65
    0x4915202000801c0701e480707241030700c5c0065290707220340901442441210340e82c1d610707450181d400903c1035a2140c60b8104030703082845860060106800050b101507c140700c0160003250640e540303504106960000c9c400d162600c1001021030700c07a0303081a4001e4100c00424004240c00400711a003020f94030850f48025941c0d40c0e00310392030480c03090206074040c0c0009800540e40c0e010141040c00760307000b22040c21404030780400c3d0300d810085080401c40440d105204403541140c488684240e080e019007080c00100305003250111424800d00401c901069103482900c80b41e00742881015510f21094461a01e04141c02d0f0b124030014540300e10041601e1800644070031054011804c0861000d0007e01001da00b90216107040040c00040f600101e1040c442140042c076080005081d40340d242c5144c0f10075107038502e991a40804020300078031002609400c500003038007a00c034a12443c4011401140904066404c3c0340f001445034402806030010704404d003c03a00d8080c0200011621061781c1103a80c0c0c006240300707282 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 581369964 1250 581368714 581368721
    0xd1404030203031303030806040510060c020a0504050108030c01051b04030f050304090c09032603070e0a0b0301090204080708060108100509160906051002010e06060d02060403050a03031b020109030e01080703 91
    0xb90503000100e100c004804400511009882c8251a40a41643ca42c1c0602c000c60390212400042001042020000d540c0103890700c1891900141105085070344071000b283c2991801e80c0600c4056200040103028808207100310794011120b0400e0403075540a8401c07441050256000183c009079881ea480e0007040005c10840e40182901d270002d200b4444076130009044555544001c0c0c40c541da1040c0f04801285240c00b0f0100100b505d100d4850854468010803503d4000200130380740c0190751a40701290031844074000c2d50091001c682d0160340c507030800d149113081c4580d65001c01101e41c0320702c005214226000c038500d0601960080c0000703403580c80003034062070a5070f20300b420403690882820224102d0300541003001a504240c41101001c65545c1e13040303080b681c0d4a164540c49410100c0825000e1602c000b90b000345a000034240c1d0308145c2c89842c0e403030400122810440100755030f481c0d00060503400346862107000045000821a001d000d85019003142c1108400e01d0400c502d41c400114854025403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 581371214 1250 581369964 581369969
    0x507020f150d0e1b210d021b030606090106031e090602030a06170a0b2509061d0a030b04030908030a03050a060b07051c050f07031d27041118070905120d1404 69
    0xb110500d0844800182d141c540302da500b030304413138444081e2310040d04000441500481000e0311040e110307868154101c2c01001c1c008100c02010120707001012440c0300a000c0d0320030082c0540c3d00180d4030704003206503404445040e40104100e42c6010100310328244081008681d10360850281440d56803040005212044100f1001078251858020760003101d40c03005180003518015200c240b00151070007017002d0b1070520104000c5d403041ea218070520008507121002500700c0c0c4242400212140c54900060554200c005480c0000e543c440400c0840b0b490b50281c140100384109d400703484d049494442e6921740c29070740f4081c0d001800d0300420040d0780380f141d030498645401c072400307003a11400d561a000301807010a02080c017080301c98180400c15860030b1243c06811820300e804030495200e080070840d461a200400681d610581a140090a9101c1c00302808200c1d00c1d10300c20a107a0b10b4141005010140c03180c1100780a8408070b064200d07054000182c07400410440e0900b412500501c5100d02024032958 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 581372464 1250 581371214 581371279
    0x2a0604031d04320702070f050d110a06080f0f04020d030318051e070f050a05090703021e03091005070e011419050901020d020a120507020f150d0e1b 65
    0x1c1040e80202480c42d0070380c1d60311620100381140358407119412a904c1046002c0c04d6002d4100850400a5103494402008502c3c4102d06a14004000f00c0007c3e100be070856020300007180d00041044090403505071400c0d8080c0820000025508051300459882804020020705240d554850081025601a070030b005955120040307440c0e907038594602d903013503d24200070100584941c00f4041070004c604503400c819220302034280380798940342c4800c01c2100c0901511410505070708002001c014407284a003a9104210300c00e00d07a943c0c0c20f04159283c90408481c00a07040c030b9162400b0300040c1c1d030f40501e4000313071a6000d1030004400c01054180e40c11078428050b20f540c01000421640700c070b45400001030000c0400903000d0b40e4480303010030390a0b030315206240c0004004c0d03940d500b51051200e02440182040c50300150820200701c08403808942d0380c1560740c040704008030003c0b42e0403841c24040d00410551209e04806000460340d00c41d180000c0c040f0140b0102c1c8900c121000102c10202054450150001d01e0f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 581373714 1250 581372464 581372501
    0x70e16030c08071409151c0e060c1b061e0604090b0423010513050f070e0a0f091a090c010306031a070c050601090b0931020102010605062a0604031d04 66
    0x300d03406d42e06258001c071030603030902c1c510708010000c2e24010710030107448003c628050081a510072400306295400010070340340701c3c000040c10500170882040458420071070140c0005010540307070351400304007500400c000d02c1182400c01010015031030448260700f05503c07070408a50542055940134007020180c840c11070f15807809081107078060740c410b44807007011b0184041d0b909801000382d4982c0c0301c0305e00340100c004560310500403824111840d8404005130001010024107401c1c560b4621350140551344c10201005c007204240402c4880622000f00400404d0904100507407842c0d8404c04045c02c1030760008140842500098a0031b8090362400e1803459118041e5550b42d07840e29200c40080064220071030090407680005100001c442004410141070302d00802c0c1200c0f44c041c0d180800c42c032000070481c1195211640000c240c1c9070180506070800340590b824401603c580f045c1486c041e000b08900d0941da000400348070210f038001c1034a4555281204034110000e01c000302103805801c840c0310b183c0c3c2440c0c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 581374964 1250 581373714 581373739
    0x1120b0415090c020a21090f090504120201061202060d091a010306050601030506010801140d06020a050a1103091513080723090708011511070e16030c08071409 70
    0x880e01a2005640d030b8000c04200d4603101c4041203a40b8070003503c00605c0700c0d4020b88500300d502d95849100001404518092491944403a4800d00c159015800000c40d942c698007070008207c440107010b03d103e10350348020480e041c9440020f100d00210307440c0c082e005410004007a00c16801076044036402a400109440901c40d84080c490030b005024801910a989030801252466102c0c0c0035840c0100e030140d40c0c0300103a0742800700b8601c2c440ea0354402da561081090550400003003032030000e0300c505885c0c1e49802c2e8960301d880c040a003a00b01e035013907444400c0c1c10400c60100caa580d0721400604180f26503000a885002c82c0107440980c01507074201250300d1040550003d901d14001034403401c0081d40e6483c066403102c01c2401d01c04840e07000e584bc400031030202d00c014040420000000b040340e050514242d03081d10342e2070b0100f50030f10940d0b4009140c030080340303010448051110042d0103880c9240745410040484500801085180094100420031200c1c191403d000f40780882555281840100419480301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 581376214 1250 581374964 581374991
    0x209190302180c03040b0a0902100807090f050a0e19020f0d1a1e010201110c0714031b060304030918060e06100c12180303021f0606020c01120b04 64
    0x10451004901c02d50b0b60142c6000d07255404031581c0d0150324410302d80381c2181c95542c0c4007014050300800004a5544d01d48110015030b640301240c14400c021a114120700b1b0400c440014596500f940110103006c06140307003001140c0302c0f000502c0c11514107605c2d03501d05854412014144103403000c10503200fa400464042030306040c01005203458922007004004401138550020b00390a0444843c6520810481540c03110b1171000d005441ca4540510000400c119249010100368000d408100c86503031046000b0b100f20785c030701407060000701e80840040030010031f020201c1da08400a045124080d09010010404040c0070325052409061600d00e140c0b100b511003000c0400600441c070078981d9450f000408200305c0c1c2040e2921407a49242e81c0d84400c4a441d1315107ca91388003003025007882c1008818019155007138841d810b902e0186119501401c1520248003111042d0b01c480014541420318041041051980028504240040c2800e106040b001160043c0d0700a1829401c6907400505107a0010840c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 581377464 1250 581376214 581376259
    0x61107030201020415140a0305040c090e100f02030c0d0b180906100f0f06030207150c02031c1a0d0501110a02031e0f0304080c0708030703030903020c0102011116060209 74
    0x16916603014410740c582a03001243e4400006440c61b101d0881002041103c41c42a0441d650050048440403502c0356182c61590031505081c503039010340c1d089520000350009090282e044280c0c003a4605608500700121260720711b20450100540f02940c402d001c0401e619440016008000801ea86005914100d032115845080449543c60150017001c400b00321356004110640594140c00700003aa41420440706a0080d03010b404141c4414040302c07413041d00c041c11401880d07004541c03a4091520381813803014004030300c01c0e6112100d4545042841c0841010707000c00099071306000848040c1011a410300f821401440c020010356100c2030000344500200b50008001c01d8810448107080403c04a81c0b00103c017640103003000e50700104000c00114001c181c85034082c2c5203541c0310a094490503556001514a91303444100202c010a8613490314906050301030001d04900b001c03c0c0000d221080803000002d190344600c025502804500d2b007105010b00040e0340c16548494005001c2c0c2d130100c40c80b921000b040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 581378714 1250 581377464 581377469
    0x7031704140f0d0f030b03010b10210209030607030c03020c1516020a0812060a0b0d0f1a03150705041a0409050702030a082410030f0501090902060706090611070302010204 75
    0x5101d011146580d00c440000d2490f0b003818281d403035240110890a04a0182580c80d140d21350644d210f008207d050398841c0640c07000c0300f20036107480c0400383c001c9611b10550490200c0ca020590f10611020505407004285594040814500003600c03c2c0d1500c0700380e000b801420142c1e225446040d010305001820b0141c1e03d40035a00c2c1c0fa0000e4004042d85804903038071300440e14010203e803014058040700804200071150007a01c02081d1039111a00d4540c4101182c0040c0010340c5a42d8030b401d4025266021403180748c055800308642c02002c49516000309a941d005060b02c01141494003001403015441103054401400303002100b820403403420785600711139400501030000114075110100b80c3c030f81d0002007201c4a441c0c0700e03101c00300c0980d00c0004040389040381c2c000030010640c10080c3d0310405c0d5500c85000000f000191000990088444240c508640058101caa012850543c0f2040982d4038141520192580141c02003002c000c1c034500030010f0069400706601440000ca0381400f0507406402400c207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 581379964 1250 581378714 581378753
    0x60e0a12030c14071a090c1c03050f12060108060f0603070c06060b040b030406050901020c1b010201020d05011205010614010c020f030c03010905060a15031a1b0f0c190b010b07031704 80
    0x50b51540035002e82c448184082c16640b01307148e52110820f8440844000c04054068101181810403611150649d94098501c0000c6090440100015036812407501a040340040d1401095580b0720b1020030014413014200c101403000d501c04120400540350801800340c02000191030300d880c0d9035000301075103030015501110b00504180c00030b004513505200f42d03803040c540d9100515070910101e402107000200d10f841c40e81155000c0080302c0c2104444d001c0d15008002c94481f0b0741c00d40045080c55030844240c0d410050151000e9808200c0982c2c0c00b034040101c01c2d030100d03503604402c05030b100000e00d805001d10b03505806500f01558402801004100385105860407503007402515002003903008110100e0200070100c850003840d8801d000725505d0165800f400134020a0040b0300c2c51080c81403590003141d0442c04031b10740055055070264003402400c808000340251522003000315a104400c00605002e01003400b8008180d50003454400e03605196040a055400c200b1403c02d410b001134400c10700507000c013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 581381214 1250 581379964 581380013
    0x71113020c30040b160203061302120a030509011d120d1106070c0b041e050c12010501050a032a09090c080307051b12030c030403060e0a12030c1407 65
    0x40c5540c10403194005520303400800c1c80c64141400085902c1d60014140c501484084801d000011f072405c0001c00d005845040356620400e850341704010444002e0400f03040b075500b0400486c1c0001c2d401c10280c640400d0f00f420400842d10b1003801a5562211001610390b12070820054640c0130b45010404910400f001d075140e000c24050303140011b644d50026995140003442070003c0e10701081000b194180c01902c103400b24040303002c0810303140072807098025003524503401c48460102070f8038042c0c60b0034502c0c3c507200000742b1042d81742100264146507503110140044584800c030004916038100258000e400c176540e80303200191140041d00c010483d100c000c48052403e584c0c00301d070308400081075071220340e0f000d001450701c0e891941c0349482d6041e1f0081d0440d04002c8a1101000010003800500280c9080704015174446140d41032a07001c2e143c1840300c09a0b240c01500600000c500c43d0717040c00c507400c0a541030220b030305680183c088440d40ca04a80754640583c2c00324560703080088031111492111191035206 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 581382464 1250 581381214 581381263
    0x815180f1b0307050310030b0f070806010e0a030b1003120f031a0d020f04020c01090b1005010e090a0207080409020f07020411460504061d06071113020c 67
    0x92000340010500728404080501c001280d9070710880c0210b5100301840103000c5001d580303030785900c7c00e02025035503030010080440c10464a04c0d844210507601080920b04001e0041200001c1003d0010500000d4600010900001d0341c08070903128080040d640b101c0e00340d14060380c420b801400c820304000100d002a041c24448900000c3c0e4151801040c040103009031f0351a4045c2c0d00704606002c40320009500306400f4003041d15011b01c04e114100d50140148088000c52400c04c203030703100051560300114140300900b03c48500c2d54a40d4980d296008a03110720041e5246c0281c2800c5905002e2507200040281c00081c000e040d15034400050602e80d440cc0d102440480701100c00a412401007010500c6545080d5104c1141064041c1442e00303907004000c0315000010000803d060300c20711040c10240030820001d07080040a83c00b21b4460190805521004543c0701c2040000b11544034155001d4030340c00c22040245900e6440400070820134130400340456440204409807500c0c1c13042003428030105004030004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 581383714 1250 581382464 581382481
    0x603070914010314060607033011040b0a080403020106330807020d03022b0e0613030c080a1b0302010509070f0312050a1b050c04110a0905010815180f 66
    0x101c43c0d4000d01655613145036942c1c0f4090108a801241c002c3e410481041400c507221284c6050107290061220400030601d02d07041c07461002c1d00d40c2200700f80700080d0104000c22940354031200703580c920819458946616215418100e0144c02d81e030b0448c039142d0202503140303052100075000020400d444082c0548901805160a482042084604401507000324120030030140c4a0390040c80b040720320200f1440c01001700c001c54030031002d800f00f04002159030303112488030b041c108010003130f0701c03602031540001806a26071300104914410b98000b400c02d00041200f4401d20f0207245508840c2a20608054942080f410b000b40648801e40b0030200134000c0b944045040e181140800068a0308940300030410803d49808456642c484220700c420007814615004581142d42044e0619a01034001010302e503120300104400c0f60481881c0700a03588040081404058100350040c1c01c40382c0c02d0038235a842e55202c003400b80f14101c012000750780c41301c5050b441030344e4280c13840040d40c02a620b80c001c4000c1c641c1c84040c13 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 581384964 1250 581383714 581383721
    0x8060109141e070e0409140c010207080304060c061d031204020f010201061d0a0b030304060908070506040509180c040f090b061002120a0c17031504020412031d06030709140103 77
    0x19404440040000030f1150390040c03d45500e04032014100154980180c2c8500e201e00b041030b0410382d506d41114005083d15031b4100022005000352001075031903e031400e00041c01090b540c1034000d20b0251203241851964035404034410202c80301c5000c2d0380e503e952548511007038003022981284201512104005d0b2548148205029100c04d030300000b0240e420b040034034000d5240100003809003a103921030441e1648041c8080d2000784001d07101d011405081414040c10400940c00c2a8010103081c042045160350320426190005a080301251960480e900e810342032040d5601305a0300107080032526500d1660340c0d80608800ba015020650142e1555000c02c500b03904c803150200700603440f1002541c1d078009490024200302ea0340b8240070200140941e241c8002004000c3c00c60044000807082001000030f004808500c0301c001c5500314038007070a129000707607528040c0320007404104c0001c1201100903a1511815507000b4018041d64882c58070303a070010040700c12801500d0503106404800c207520b50003800b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 581386214 1250 581384964 581385001
    0x50706090f0c1a090d140a0b0106120513060902010c050618100b030d18030c0f08011a031b03010204090501270902030a121b03050409060b040312180806010914 70
    0x3c81c0e407440d0180e42820001c0c400040803041d100b540c2904d2881e03180c0d000811803c0320180c80b0740420b40347e541c50040301030507032030030300d450b80080d1070601c0104544080350405914256170300440c00580d041260004035241c417601c400040c03081c0f24110501401e4441103082d402c2510072002221a07052f40007104506481c80112003a4044e404500580c0900740582c0d084009144404003100343c1603526200c3c0590007425500110780121711a60910a02c1e5083c040c0c00503183c440e07401d585181642c200071075070b60061200d014540f25030300700003004140d030290116002020084018001541c40e00304e0341e00300709d41d1014075503000c04c00014246801100c50050324a01d68008000c0c000c204016111030042038034505640d4200300010f40d1030001c020301d4600e010302c018020b41d95141c4a500300381c1c0c00c4048072040c1e00000d55000e0180410400680b40fa40360921404032440d00c00c103800c0154a84541c1c903007241e00000c016000c0d1000110b0340c1d046a07803003c01524100350034260640c640d203641140011255 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 581387464 1250 581386214 581386259
    0x50c06010314030d050406020714011806240f0509280b0d0f030906030501050d0c0b0a030605030d0806100e030c090402130f05090c2b03050706090f0c 66
    0x204010004a052000c201505501102c19249821548821034080301c0c030031642201c0582d8081401424003080100003040407020300020045070352651a06445000c3d2500c000740825210545890f0801c0783ca1000d8480da01d45003000314201e030f160039a1525280081c0110740c016010303103000407600d002c0e224040b41e540b26100099100c540a01e0f000304090b000000c1c0c030030340203076a420446000490321000c403040c05000ba551a001c4c0c5042560050541e00d060784040c1c855444c91101c1d1000c1101d036600d0408489010040702d0395140e031900160050030440e0300295240c003444440c450003581140c0c101e8422601103818044604445c00c0c1592910280b80c042ca0b01944648130100260030710240c5580c00500043c003010704c41020082120075210400e26501c03440384c6800034403410f50401c010702c7c40c1400d4100c80c10910500b94000320305144884e001543c0614907411603030024540034808803004150001c00a00c60324006041440000079100d00840d2102c01d044030004060b05030140703405034401003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 581388714 1250 581387464 581387473
    0x10501050a050901170106110f010c17270f0f060c040e270304050411030f0f07090b030c0306010f0c0506061905120a0b07110a030f050d0f020d0606050c 67
    0x10080407505500301070380c1541804505d240e0003020000401500b070003402e940c0c0e64800b01c2000c898841d4107101ca4090724229607030409904019980e00120070001c035926200544149959031000800103032070707068a0500704041201a600c1075640402e08022103200202152080d83d8140b0300a80d4810044030000f40c1c1c9081804140120303600808203941208005a0691264109030360003034080200c12010803503644009810019414a07005e00e03c041520320546505518001c0f110340c3d1020030080003100e12030407240000700f9203805090a03030b0180c01c112114035240e2400001c5e410003a4025140c640c0400c0d15a41641203013481403540c060703582e9118020784481d880d0300051101c4100a06c107440e00f081601a0003040a441300301c1020131403610300004204103580307810240000e08015140f807080050ba104020f00119000842c080410f6241c40c0003100c90525442c101c845006032688081c000b0f00301480341015607800d402800942188078000c100044d5a1081a55144507402101d070480c1c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 581389964 1250 581388714 581388727
    0x3190c030b0c09040501060e011101050f040609050a0516031a09120a091206051e040804051509060d150f181104030f060606080a0c020312090c18061801050105 70
    0xa01d540e035802411101c011418164608002000d40c0c1098120388002010407800800740e41e80103025162800e0180700030070007410090b400352050000140050000394903148840c007004420000c50490f82d030000241c404d4440180c0d02d625100707a452000355040d03d079a0605c3c01e035059000001c64040c09000c8000e0690144006010030150450140b82c41442030b442d000181c5424044a91400644a403070000340f1b9191a032040c2204a02c0004091014840380f400c02001030400d1781240c041c1c41c01119820501940040c05002d5031080038000303508000041101d02e03c4040c241c011010b440a60580d107a056919810b0380342c330300100d238030a84584096441c0c8070007030032000350300440c1c0c410703146005546015102e0711009140c1c0b90040341250700990340c0c00200400c95011103010b4000e01d00f04014800280c1c0300a00a54034002d8500e444410444130000c80d80c10402080809145400030341641110880f0052800c01540d0845200303004050751820102c01036011900303a410380714141c40d86402c0c4070303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 581391214 1250 581389964 581389973
    0x9060609041a06040f0e0a18060504050102160b0406050906100905100506071b08010b0604030803280b0103142701090618060c090825050402071103190c03 68
    0x14a105200c81803841a42e524011a21810010409007101058500b1150302c1c020541448500007040041030318601a181a084040061002c14044d040765000c0b80c0c64a441c106a40281f00e00500e4880c0d90b02800e031700604005103040101e01c100c0c002e5000300311039a10105038640340d100803140e038078043e0120601440003500c50f610480d0130030741e009132070040030361104003080715a800942c0546080740d140d841e44080504900d038031b60181134404002d0043c000c02c000403070034034011400010300c0454040002026a07002c6108282c1402e0911041c3c01c5000030100e0710030082c80c1032404507001038201904810001940450340340103070f0410141c09152000240c14212407811440c55010654880040300c01142483c007516a0045100d80388066561061600074120341d142d007070b894180143e00c1c1080101c114045034480540f40e00c0460b0300d40c6212420501703811040300d600420b901070700c080b41050030302030714101a40800ba0194101c40c0e001c4d640d2442503040114008004122000b914070038000034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 581392464 1250 581391214 581391221
    0x17010e01090906110d02190e010804120e030703031e0801050306060108041a040302061501031505041503080301090204170a05060a0c050909040b1f061d270f060906060904 75
    0x4902901c000130f140c41c0704503001c0b1410350011075039440e07240d004280ca400501000c0c450413030b14030032030400080c1e00034003c00290403c200204003400c0081102101e81506000707501d0b603c00044001c05403454187c9034035014009004000101001492006c400500c250007049200c1c16600300034001c12041d0348071401143c408034024002ca03941072104540d00518000c007101507001d00d20a4010308100d25082d811004200404482681058184000340c600440140e00040039504103a030040b92080542401c20a200304d9a84010030980c0c000000103000712039070303002c0c00c140c510b905002c1104003440d51706c40d0360301c91b80807030060b00d9034000801040801c8a2036110350709980b002c1c24410305044d9894005107174076800f10340503199000c0b04820030030038405c800700c0e662101000c0c85180b200e107800d104004005503503d10300740f80191300c4440805c0c29980d460b11311010300060011507030011034154401d50f00450099442c60a1040c410020808a03d0502002403081d04042d10260400800400b000060b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 581393714 1250 581392464 581392481
    0x715020307090b0d0203060f090601120b150a02010605030615010519121a0102061602070e10030c17010c090e060105070606050a140f100509060d060f12020117010e0109 74
    0x920002d00d01c00030358104001d02808404116580c0140c0340c0ca481014800610030100d000c40c4500c021a040098680c5c019122036810320402034002100a40140410740c0192102d9400d14501030101e10b0940d075a60540203401901c90580903151962148032400b0000c000072060180030510600c1403403d001001a50071810702203904e41407810140518510003151078094507850750a50621001006580401260b0380211200c04160780845950038020f48814440c050707022310b244c0c0c000100e00740340c0e070140d002405103070020341590042d640da0749000780c520302045140c034140d4200102000e100e80105640b0003101e290b45034a070415903a85004507019030000004842c015600c800c041460b48516030b1010140201480302c1c000c0c2c8000400b04605031241d020b1051040752803205503451150b021050751400710080c0c0d40261204450b0100c980641420f400031909080e070b591001a03141d210340c098400c441d0003a00c41210361213004803412001c9400f40583e00035040c1e103000400c035803406648030242 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 581394964 1250 581393714 581393717
    0x414061f0302280e0109050a1401030f2408370b0403050a030b0901050a061b050a03170108030310031103030c032701170a020904180614010b0715020307 67
    0x79100d10300070840c0303c0240c10008030094800c401200c40040e41c21409144030203109080001d500340c03519000442e684682e010b69600404600390003c91a40203800c520310030214518240903d2038801104423142402001806203004501313030000e80254007080c00000c0e280c501030003c41c02086115107100c0c105aa001b54a07101c0c800074942d4002c21031071099980160310030740c0c5056a42c04408001010348012000581c071441d04072004000300c0e0b580b0f4490004403038590410811402c10400000210100c44074090124001c00c00400d007015801100d058150601e070900c5003050340c07141000c3d036490000311108401d902c0704240910111b21441c0280c507180e00010200e920b0601c1c030b01c3c4500d040d60000307440b210841c1101400704a00d540d4100a000c0ba0798000c0c80e103640b1806c040c2900480000f40580058144d903400621000c0e0b540300c0340c100640b1180c011b40c0136482d14600780340c800d008010b180c031240100e01c0c54100120740ca1404c40e081719030154210f01601800160903600300002d43c4081d01080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 581396214 1250 581394964 581394967
    0x50a030b0d050d031a101e0c1e02090a0501050907080c0f04090b03010f09050604110310090302030a020c01080c09090c090d0f060b0303091809010f02180414061f0302 73
    0x20342c1080758002e02c41d0141d8010a20074840031400103540c3c800c040142c030951b03021080c2c400e41035100d01701c0b03189000100f880c0f820681c10142c098034405101680034101004160010701e0b9000d069006071040b43c030980c0e482c002c0ba907a000c00c5030200c540038000c1c070b5404035034200402c8400d8443d038013298000480400c0700340b4005046003650307080d03032003a80059819600c900014901d40340a00c586461090100001e10a480321584ca490326100700400051101d43d9080005890b41c0301001146c0c4120949841045203500300d05000c4c0d600d401610070340c401407040c1401108503501c034010540c0101d050040c440d041c1a804400c00c00200d0008051032007222041c014141283d65503003101d0402030040e403441c03503034032110b0610105070b503c15403003180254401c1003165001d031221811200d101801075840030468451038000c03030241c4118000d041c01140086007401c82079680c0320402c0d14408007201c0030003140102c0001207070036007030444105901190246950030724000c54410095548400d00d40107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 581397464 1250 581396214 581396239
    0x901020f010c0e0111010515090403170a06170c0109090f09020301051f0f050112020c0c040c030b131103060d0f0516060e040203060a06051608030915060d03050a030b 73
    0x50841c2c580c201c55030005445200c046000b0f50b001501c51142c6000c00c5c00900043c039103d8407a0000003080c80100380500d14020001e01418850401542100504000d200c00c505146070404041c2c072503409041084000d10b40f84038000d450004801c0d2080e901a10307015102407030102d0020050050703960503042d064407000346070010f07902841464841c280c4194a200850b008524079480d04807aa044110b0005680b202441207a8100a10307911840101e8400350761083c0a519a506111058100c0c40c4c00c84d0070150b0b0400425003540000d44501000d0300d48400d00e07040911810181c03a01035410503003030001000800c086003060801000d800e8066000d040801d2907542d52140f5100300e40f4000500c1c503404c2c103828800a6848203c204446038210390550950829000280546e802c504c64082804030028421803508043e2584101180d0480001c5443e482d01005107a11035a89170b1680d40040440c2000070300390300e080d4284440071501a99440d0038240d0842e0140c0080100307507001ca83c070801101c00c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 581398714 1250 581397464 581397493
    0x5180c031b040f06030c11190f05011e0b22021e030c0a080711061303020106090c02070e010504061a13050603070f020115080d1b0203031210090908030c090102 70
    0x500051043c151407806251401c0401801c541c1c041c0d60700380400c41c280022520900c4000360407400301c2d8200c2c4c0444d055410305c0c60050143c54170058010b00550030a01c01d00840801200c00c5a8004180034041c484140e0b0f007010040c11040038402c80e11168901c3c0b0941090511560140211072000c441441401c0c003403d0600e186d6800440d400a42c600000400344e00d043d0740030f81c0c196000941410460803d406601466490741d900401d00302c0c130001c1124482d000d1600c00d400a000824412404012403801814000d4650b1150b000b1240c1542045000217407174100744c401c1c1c00131502059241c14000040324845005541b202b0001400c0c4030840301e0201e4a5510b11006500031109a20742c0c846240344980042d0035103202c0703544401030a0001404101281022800c09142d0f40e091400707480418080344603450b10001c140002e901440b01080401d03540082d907000601901c1c8281800c810190382c3c000b8902607811741500208207074000e20101d10b00d62000e0002d45038880050042d1211034145006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 581399964 1250 581398714 581398717
    0x9022101031218050607020f0135090c010c1203090605010b04080115080c100201061715090604080702100c0209040605160309050a0f0c0305070305031305180c031b 72
    0x4240d42c1d900046000640303541c0c02007036004070310041c010542803480c6030500290480c062503102038007583c1c005040e030310982c0c401d030340003a421035207002c0b40c00394843d0240a85600210840b40f21040101c1c42000c01c01040c4009075003001c01c6c0050355041403641310f650b2483c0b09918070103541c8048c140c46408010010f00c2d80e000e150f0181c44a170386106c1d1034919050a003400d40e840d200e003180312500c0c2d0392b9041c04a00340100d2a1600755405641554526888040481c01030440e584000c0c5903600e034000e40414400045114a17038001d640b9488005030329441611a29640c056130000c0c0100c008104c80da00604140004a0041420b42011910f550f915000300c0d00804049408076500350f990010020001021401120345d4035003490100b107008202d40c2c1c0c1640d115405440a4a040c018a14290410030421a550040c1da0300c0015110003076030301c0c9400e9580750803001190445400c0c2c9400400c0905094680c1d002c400e050714070000782619070300c001144a61025100b415900e074008010000c2404040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 581401214 1250 581399964 581399969
    0x3050d021219180f0e2e0605030c0405090c13230d0804050d030f0305010f03110904022806140f12090f0703390e071803031e050a020709022101 63
    0x8a0300d0014600f4400710101d4003181d81004950156561b200c81e08140c4012000b816a541f604080d95241c480d4818031003140101e80c00300d07074824810b60400404034074a80103840032003050350080e40301646508108000403091803048190001c2400c0c40101841c044e03c3c002141802071020300e00c2e01c2d07100c030082141003070b1b1680c00f6408542d004102ea80029454883c20740181204c96440b4015802c681d035a40c014220030000511520ba886d0114003036507206158502801301d201d03003c0c0042068411081805410b81c0305074800300301d0700c400c01c044894488044410710f2010303150880c030308409220301001868018080c46d4203441011508002500c040086602650003003494801c2004115045441103a16000310f00035054001446003c040748002c084050b50a0310541e5a110b40d2031160480e8024081125180031001200300002410740100a00302022002c0d4588105c20b00c007000d040c0c44910441d495400140d1110030100140205940034088210031219510029070148128403800c4000381c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 581402464 1250 581401214 581401229
    0x721020d12020d1806050d0207050f01090c0f0b0f0706200409020d061e05060705030702061c1820030c03010f02130918020d06020c0703050d021219180f 67
    0x1c0403140c142c4c2c1c0081c0d503101202c8503201d4032031210342010700c014818000c40c51340001e0f40343c0100d9030b442013003400e018856405440380c00810162100f400e25114104491240c001d2040c410742c1c0109070a15204102c815504400381031901d083e40d0380d5206401000e10b55200d40e03002e001e6550f02c6010200100040008254412000d40c81e00d50004040b401c5550035841540e1040d101c12151420007160114181102d01c2265020f0300c071007441c02e20508600c10303040025800305e00010241048200507060b0307100300e0000030041040e0720444900c0503000344041e1001c6c18540603240301b901c40240000946004801c003806030b0301c0207843c07140840c1c20348040e850b21096894012403502c149003c01003c050043c00c02c080d040c002c9a070315190401003103000b043c1c0a03000b800d01450756018020250102c1e16803070186402c0310002c4d0754a040240d1944d5a00c401d44006005490301e840d0b20050f15403e56166482c6500b0301c2040d01000c00c420759112104003000003d043c4885400680c80180405034001403208 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 581403714 1250 581402464 581402473
    0x30d0e0f010e07080a02042a0f0311070f12030204080102070c030b07020d050a0302030a02040b210c130905041a01080f1606200708010c0203090a080721020d1202 71
    0xc61040300d0035511042c0704600d00d5403003a8010455418009241c0d00b0107501a180040d41988070306034100f28050381e0324542d003000c14071020381c0011a40080003580c48001ca0380d04005030b0400c000074152600c0750060191008501030080d4010030240f0b64010400152400e0051034140e031100101c0c2640c120320404d4440040550040003030200e1083c038035a201c00e591015250840703501c480074015010f40c0301a4410141e02100064082c05035038101d60290802485050f01c519403c0a00c514070828183c0445c259480d003000f01d81c000350900b054840901c8ca1178083c2e040c407420464010b000b85002403096800c81c0c42c0c5c2065a039400e0400043d10701911082024200040001304501c0c40c0c0b03a5081d8400100d001c14040030000386034002d5486140c4000c48110b0031190107040c4925203000b007684c0008841d5407820001c0810f654000000f0007940c2400d0700c5480c001a40d400302c850701e98040b403240035004100b4050000814030381d650048034040c0f0050400d41d0483c059194051b81502d80514140903a00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 581404964 1250 581403714 581403733
    0x11041814010b0405060f070606030c03062a1d03070504060b030417030601121e0c05130b04030201080610120606120b1912030201110d05100801060f0314030d0e 70
    0x10200c6418050004034400a1505182802088480c0b007a1812102d83c1140428400200b080b01d403c244020342d00001001c82d0f450301c03814130f040204804c8041100d101039200d2604408080005204040902c0f0303160109640703030400f8500807042ca0250419850b0042000110b403070303600e0b07101c4c04025081c060845900c03490b01d460140300c9007102e40c445136013100c010701c2080324070ba91081a020144594500c0420040400c0240c0301c0d42007080ba41071081070b41080d13001d0000a602c240981104070749265145640e0ba40d550106402d403146000280c0020380303060020350306040003001c1403c080000d01d00400001c030f458422404072407903a003190000a5019544900408a90050600d52403040301c545c515000050204052240c643c441c041d46600801e00709000e05000b0350040c02e064005003045035646110155030b000800c012a503000142200010209820005200300003c0d26144c281506010341940c6840c40c0c600008000c2d0022480100003003050b080d86030083d40c0540400d0801401070a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 581406214 1250 581404964 581404991
    0x5130b1b06090312040f03050702030f01020a1403010510180b18090601050c100c02190b041a0f010b0702120118060e030f0909040305070b0705070203070e010810110418 74
    0x107805042c4070321950051014010000b1100c102c607402c182d00c0384140c0e83d80c03010303440c0c182e50501a0400195042c010341003900315410046d002000d142845035582911070b01900d8001d030b0341d0f00003070181079004402d50b8015024203005899200d10850b040c02106149540c2e007165000903400074115100070844541182240e06005107403541120090910318240100700e4420380d5070350a1542c000040e2500e64028241090007030001c5101c19412814502e010784690501d03c40041e0290b50454002c01c1d41007210050425801d406030088041c08032010031a4600002000341e90400c0c0b00c01d9a20202440780c0700c64141c000d00c102130036822031a03610442c20882d401d01e4411990b40240c1a034071604108007145200c506041141e80d500803c5460305a180c0740c0e400d00b114280900c0710020b00c41008070090042094000c40070300360080c422000c07100c005803180340943d9900400c3c81842801d6115038022020400550840d51000c00f080310200e0806641d48030780303100b00c2c100c0218a214a43d48a94090042 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 581407464 1250 581406214 581406223
    0x507090921090906080c030f01020702012003090603040303050711010b030a0b0a060e040302072c06060304050a1502070c050a050d14070b0a0e04050a050601020601050105130b1b 78
    0x1009600410003501506495a211401c11500008480401124103114441c040d611042c06400000410814140c4840301e61b40c5e2a172a981c41d85210b0312405440110260050086654541d4107070344001404040050358049299840083c40040c001840300c4143c90300d80744040d606c5a4020390303012945041c0410003030101e003010b44100c17046034180444801030b41c400050a0141c5580029446400d50b2003c03002c42c020006031704420401c5016030180001e140e80000d0701b00603510340c0c5030079618510350082c0d00c42c024161080d10401c4a01c882c400034035141381c03000180d0307801401007042d00d03100032050b904d200200c000103080b25180c603400300c1d400d03060042d02d4514078040c1100791025002141000d0002c2c281214000c0014101100101402c00c041000e004c020000c0654180068444403d0000503200c561051040760059180c2000540450b140d401000c0c000c3d4010b8015141c1c5034249401120036a0000c003c518802c0381c44a030005580f82514000c00c10340300104c042d0f00d0320f0b140c82c508d01801c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 581408714 1250 581407464 581407469
    0x8011103070813080301061b02060f07030206010b0408210c06390d0504030512150906040b0d02060a020102120414010c051e0d090b0711060912160c03020d030c0507 72
    0x710001c003c00000481c10000c032411760304203050050f0280c03003a080e0304905464090b8001d42003980400e031803417561501009030403864441e0302569850303a22a580300d0154019846121469400841003100c070b01d21141a40070b050500540c064a0b2441000405140020503106070b01150200101100d890030345407080410080c6a00310400000000c09114101d401152481c00300207541c0d00100d010180540c0488820001004042c04285400e40c0c1d2a983c5a941030210390080060318001086031034107104545104100521560031821a0307001d1000382e404c4070450310b05544d405c0100c12101e0210645031403040c0d1060b00c2c00307103850309040c500c40d007503c4050900b0801e02900348882102c0701c220707030b0364030030440030072403000d603c81d2460301130000901141c9001800b03030383c020703010302455a5201c1c078400403042c11b903003c842e40e5803642d0000d996100c032102626248401c1c2440305803041919035299240150051101652490b100c5d0006000c400402604801042c1900001010040d05000d040700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 581409964 1250 581408714 581408731
    0x2130f0b0723070f090b0112020901020a0605060f120f010e01021207110313080d020705010e0d0303050a14010e1602120d090c1e0f0807060e090c04080111030708 71
    0x2007030910741e0390007600214500806156010341038800c505080c100403501c000e103255096990728650b1000706400401c0b141501500103100c2e02c1d100d01c642000340c0211a03440c80180d0080c0040300041e240e8000801010742800d52202041c401d0f0b90b815074800a041d8031310300740b400c00341c002081c07801a401e0031240300d16031425069006100e444c2800141620090340207196050010b8111420503a42d41148a2038680c42031411001c00e000c100300381c000841402001c09902158005611480103541c032621804a01d0703800000000040002817294000c035030407080d03008000c1100740e0080904a1040e40036001126040381d4181008040040000c010340d0300c1c00036001034426805e821004042030311175440500074403911403101a04010655048034000d000d118801d030103854008014000e80085d030720030309485000314074010420780c0c00814440c044529988901c01c10042240502845240017070400880b18070034040003950a9080c0a04074031001020000d40e52403501103130241c0078136405000381c2c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 581411214 1250 581409964 581409967
    0x60809010f110909060f0a05060a05160b04120201050c04050d02180103060c080c07020a0b07052a1005090306070e01020a1e020907030b0d020927070e0f09070308090103020d02130f0b 80
    0x10380382e11807109030300640b2300940740145d4a1034a20800c2d201441a00c0e00403d1800c00f00f0500b4051241c0303201c085006d40d10628a030f03030011360017031000c81c01d0715070a4407909004a0100402c01162422010b450a41c601c00b0300f0030440d41c400e842d110302c601318090f442928201c1d01c4142c41503549900c03460140d0310a1000c146541000c1e000c0d000708070106424010000401800668801481000c10460108843d6042c540034108584010003290110510701d0300e0241d481d00e460009032a0103203040c2c0e600480050000d1659a907110411102c840040c1d031b110303042d4085e10a03011301046d030702958400e0300e6040260505c03048a031441806100c010090076074007054a0301a180900d0307581c510200d09403a4044070301d160319489504800d0340000c0c651a03000b100b942c0448034144500400716002040b601541001800d96032608070102c1000422144030a440e00910030610004041e40050319641d24103150043c00d085002084404070390028801c0d00b150440c2c030340c2c1001100461042040a020480d5055 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 581412464 1250 581411214 581411239
    0x1110a08010602120909130f060e10060806130212030f0a0905040612030320070f0203010609090203070e09120d0e060622020306040b060a080403020f0313060809010f11090906 77
    0x3000f16005d10840b0b140f048507080049100100e00c900d02c0c80a0a4015540254444591501e64000c2c400601210103038058115060603400c0e8600c954002c032580034022700800d81c3c0d245034900e6040102d1000300d0340080000f5a80c1d007200020405404d1202c50b0000c890f980c3d125804007e0b01616450f44941c4c40342d0b08000c010b00002c00c03004c0650310035660504000c40c580a15800e08a04c03420041e041559011303000c0b8180c01071160000102104500950007000081d45580e062401c3c0e030500040a50541d0001808000c24501800ba455000c40c82c0010f441c03802c9048142d00300158004d50000c1d003040d4490300030003080e20040c4561900700da0100c0d201400004813110180608901010480c0c40c2640400003480c5600c0e6078100710541000109666901c0e4003100c005040340c4002c5e1810740c01441055001c4541e018008201d51045e21590400d4994902d8140222003c0800522400d1603540380c11034608918028001e10780c41c5104014901c0d01c1d00340c140b042c0b00200c0c41c000c228600c190100d0721103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 581413714 1250 581412464 581412493
    0x40b010f09090804060302090d050d02010c08010e010501020706050a09120b0604050f15041e0207230303010620011d100e030f18010c0f08070b130c15020f01110a08010602 75
    0x1c580c105d039020b06025803241046d90000300c02d944400c1c805425402070780ca070300080ea903042d07111030748401c825150417460366260407080039801424060f0350f0169000040034080d0398000c80181c500e210359442c0055595844a0400003003658414048400c10648404d0020a15040c0642980451190000c3d803031480c2440c2e8040541050b485094000e82c0e84a1440e40e003a840240b40310b0002c5514070080d580c4600d035150440e001c04123035626142040f0b03103c032030242e0007002100f24ac0c103c403400d0f5034201601c2c00c103503540030b8000068510800590740e6901444042103002486035900e41d03900c000b6003502621004400300390b885101301d00215030401c10007001c1031081c060603900d2482c04480c059804600c4a40140c40c54060658058a060401410081000141401030806500c40d2246481c9038a40e81e000c591180f80b04800104000c0444009001140e600c0d4001c00d141402071048507521000130074410708441041610101011000803100d14003500b0440c160300401c42803004250b5841034605 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 581414964 1250 581413714 581413717
    0x50c0a02060408031f0b0409060e0403080f18251a030a050403111912051635040e16081b1317060a0506030a0618050105040b010f090908 60
    0x1000303005100c04408a601190720388170581e1a0b18040040901d501d8840011070107a80291094040660402d1030103d421000c540a00340aa98151910201a1a0a82e100011a400038007510080b40385000c0410001d500700b080c8849000c0341003c802c070750780d44810011005030f5035402013000400e2211000c054007582a040b258004003041000615484624048442c91004054071125205804040f0f0b02c0d90070722111166180c0c400c01601e0580c003605501503406004103a803460f50340c0918401321020500140c18061013110306e603940038940ca04140c1281d0b4030406c83c10304504000010034148103490800c60a075030810704081e00c4007000010788500604070f0743c0c028030b5162030000038001490811900c005035403101e150750b40b40b014181c0e110400d25650001030b0111302c186115580c04108074040b18031605000c1c3c80041d015081410b0140c0310311000e05030402540389100742203801c0602188d400c1c807605003d640314102d89101c41d403522440120340030450f00a0803005d40b44c0f25071000011001c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 581416214 1250 581414964 581414971
    0x403020103180c080709150e0402130603120917060402030c010c0317130506060f030d0c050c1215070f08240301110c010f1503061104081f050c0a0206 66
    0x6404034450320b48105030440620300d1032000b02041403601e00400e00d1100400c400d000e03a0001c050070000620112000d40510602d8031803940c044c080e840109026040868100c24250070b9100082030f0a0395039943c6507940050384c12001d0008500b081c0900080c005c01620340000078800300104918101900040d840740466030005040c01144c1c1c040c1c074201400b40d522101c10b2500455100c40341e1a000904c2650b0720004081100e06d4000d40002814520707003000403000348200900100358401003500141c80480340410203480714414214400c20301d81d150101802451854800f0b028841c2015083e034100100c09090740040c01980a2644051a400381d40d450384400b00d00c840c00d4003180380340102c0350354900c40b14481e6015401e00962030302c0c2803529002004555100e030004c00c1580400490101250a003c40d040d4040c0c140c0c050800c0803c11076041040d070007000306001c2d440d06d50345001c03151402c2510f0f2280311341c6410944000f40294090b220b01c131340c84420040c0d000c2c500803904200075250000103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 581417464 1250 581416214 581416217
    0xb010b0a0e0306190b03072321120a11060a1401060207060503040f060902060c010510120803160e1e040623010f0e040c020f100905100b030c0a031a10080304030201 72
    0x71084407119546c2045040d009080d4003403a5110f01d050006042881c400d90075825004182da14994140002005030040000c0d42c9170001d008041d031800b103180c40c1540804d121710104224645844504c00302440a580980451000001c1d266680500e4258400f0140c1c000815504200e600300541500311089a6120798001040080080140b03458401440c4196000c0c0d000b000200303501242e90030540c0510b000e6640032402c00007040d50340100c4c103040030103d9402080b000040c0082100007003009044500040075042500100704440c0c045091889178251710072901c05c0c54a404029030801c0c0c42650050000e903518414511a11091003a1030f030791030400e890402565800d06080c0078410b40c108a59148003c005100c41c03811703204025a181c1180c1c80052890081c0d45580b603160015100d0300c24010b03440b4002d401c95a0355002c080c401401803001c100c5c4c25001d0030b130500b6825034680040c00003851142902e90300000ba5026001840c0741c00901c0c200d450080000240401c450010a80f000c89909 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 581418714 1250 581417464 581417471
    0x519080d110d03021e030c0903010b0f01210b0303070b0a0b04091a06030109060e101409060112050307020a0905070201050a060305060105040906060b040303091e0608010b03060303070b010b0a0e030619 88
    0x3d00c2540c80c004001280040c4103500081b0610658918450040050b00d508900030300c6460025002c0016200703045100c035001ca481c41e07a1406010460b9210301c000710010344000a000c3c0d414201003401c552011204591b11010032080000203d02c501c074019009206070b5041011148a0b500c0c101240810310b18082d007011048000f4880759070035000a2400c83c0c0c891010b02400c02840450f13542e4008d5958641030450404180759500d0b1400500d00e8850711801c1d00074400e592a1928122402c6100c840c1074589000c00c00c120340142c1c030b403801100000c0c010904005580c0c600040020308449002d041044210b007003500c2000810400246241074500440c0c0000d908805442d01c60000e2140d9400161541e0001c5000401d060300030300320100301c0e00000c0707080701006c506a03d4280c62031014000c0d14080b40d02c01d0700502012200d8405190700c81409801c076845c0c51119158501d900c0c000740d00c0303032030030703000004000780b2480c4e1055078400248400e078014091800c01c11010340e049000100e205a0315642d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 581419964 1250 581418714 581418727
    0x8211b0c1908102414010f080f01121703130b160f080601121b03050106090f140d0f0606050f12031905131820030f100519080d110d0302 60
    0x103070510f071040030100c2c4a03013403441c1c2507995003015014845440442c3c040b94444a510340c103d40104d041034802c03500922603044a2f802d090201600030410a029a08181500da8415a04a028004500030418120041f00381c14080c9000c405e139010007883c0f502d007030740030b601c6425074a83c1003501102c0f07508860425030259a80e40e0012100703070001c441007220300e0381408004020070262408400300d204042c2c1d028421a82c9031a4240c554035040e110b0800c011001078420003041390716a0f80d0403e01c000003004191076501036143e5200414103054159082552800f08102c81c0c40d140001902e02c042c141c811504104d44a10800c0d1240240c20064190300078000d501c0b090a8803600480b00980380c01c40749400b0042c0c031421220154911903010480c6685010901099100d20b00360341d5560b40c00c91000c8500d556114002c2540300ea901412049600110380c00103d41c030740d01c0c0342d030b00211111900d50010388285002100b138940040741508200380124440500500c0031301060070f40e450205070a0250f503941 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 581421214 1250 581419964 581419991
    0xf0906030c2102010f1806050403050d0e1c060b15030a05011502100b0a03060c0210110909130c05030d05072102070e040807081306030b04050108211b0c190810 70
    0x41c850551203004961b508408203c1035040000b0b40141ea0040d01107681207103078594291072242c0c6c10540c090784004040703084001d0041451003082c0c1c481c810031022411206c108c01003406501e140460705251240801004080e070158815031340180a0303444120120500483c4c00307516400e6140d8000f039102d480c2c080080c2c0c6134640d40d515000660b0302250400061288000080d200c0c03414100000c01e090401603038098040703240d016030b041c0400c0108465915111f5513a07041c61405400b4044801450301c1c2c000261565050011501800240c3c4840c0da840c102860904101c41210b0201021841d0904581035001c0c0e0000e0317001d0594a02e070000c5c1d50b541d203650801407034602410400520400d0001022070740c4950f03c100210850710b032518180000c811f00820072050390024060340c0400d0780b0980300c14040103481001403480e030581410080c40e000060304400001c0b144100002c41d6a880220501c44a092035180c1d420400c0c0303084030f0b520425050800c6181c581065030924001d554030f0700034215054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 581422464 1250 581421214 581421227
    0x30d0e040b011b03080720030d24060206091e06040602160f060b0f04020a170a0b030703080703111c0e1219021306060c1502040f0906030c2102010f 65
    0x401645641c07940a02e003515008100c0c4004441c508005140d824142c0b0050014030f00701f0424040345001f8504100b41c40c2180c1e40185005495002d101380482d18840780c80c02080f1820000d0300325a030207442640b800b1540a8907000b0305110300c0741c910509042843e107400c07001c11600d03000b90b0311840141c0d42d60708000e4000c42030981542c014000b80d440d08040010003429038051140703c2c40c141c0b0a0300ca03a100810130002280603101c000000301e00460034110b5000b240c00115580140c0d440000074200540c00082490241681c00c201e80882002500c0024036400c02410355194010200420700e08440c440c580181001101806c014841c0003a010360250740c9400c1c61a1307080508004030b4003240000032410300d074684000e8050b8000c2801201300c401c103000501804080e6096600e92078610203107640c801074849050000301103003940c02d01020601000d02a282c0d002022003107808120b6600354204000d0074140d82d4420401c0c40d070b0500444041c241c00c040b03003902c4183c090030301c140c1010494000341c031b64 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 581423714 1250 581422464 581422487
    0xd09120f030c260925211a06061c020d061e12032006040b0702011505090c0408030a090305120304241104080f0601081204120c0f030f050c030d0e040b01 67
    0x10100c0d070f1003074912040046a00c250486d46005220350500554820442c00d003c0700103000341101c4d41c0c48107010b4911400c001c050342c12050140c4114070700216902c2d0003021942d45910521065000500940800c240f800f40102500340840900748002040c03418007184811841003110020b0003400c0380742858042d005556640007409000c10803545600ea5880c0c40f1502190100d0340c40c1c07030f00c5000c00c2006105124490344c01c0c0c01030180c8440c45c0d041034100051072200404c0310f12884d02c1040080f400900038000381c03403080955100d2003400c50951a10900340f5480000700301c51002c0034030801c40411413140b1010f54042d24003140084107000d8400322000707481d0180750241141000140010b0510f40007800303003a01d000340307010f45000c0e0340c80758002922002d1404040160344d0080c48207110416060641c0c2821903c01c1c40207501c129612500400c001515030b000751061000c0d244002c0c1403000074440710a203060300314040d020302a4001c0c0040d201c44041c454090040b03a6480d0300480a901883d00f0440303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 581424964 1250 581423714 581423743
    0x40e0f1005060409020c0615060d360201020607081e070c0b040b1009060506072d03050406140306011e020f010f0b150c0309060d09120f030c2609 64
    0x152107440390100c04c080c0d4040350000c10688030300000548140c1200e05000a0001c005145e2880e0410b54411003010301300030802210b4501249804040d60284a042003035402000218030079182240c4c000a070034a40024102024044800f00b002848150011105406140015514050b031203000040b00ca040780d030240185040018814001030180941c1030343c1c030403074000c82c3e4802d85a485800c0c60701503898510419400000500001c0c000238501c104c603281188540294070203006590b034614281c2982c584094002c141c0015007032126541c04503402e004031410303404044c55814101c0000704039500f500c1481c041060145014000d43e4424807290035041c40c580e000703200d0008001c1d00c44009100122486100711000c3c44a040b011302210180c0740c40686040103581468400703028850540e215989052013141e94420100001d04151010b07103507102c1a070ba0f104030420000328090308407401d1042d81e40a1001c000302112110051099094800d04206525101512072030050307840c140007001e0440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 581426214 1250 581424964 581424967
    0x909030512041b050103020c070509041407030606051516030c0804081002030a0e06040203060112020d0206030901050601110601150c080c0a12020d0c0314130816031403040e0f100506 80
    0x40c0000c03482451101c0502840c030381c18a5986034015400c80c4921008c440c10798110170400c12403481c2000c07000da4054040c041500c03034080c101845500b0580e90750002c9031020f903503400612083c02d141910ba80f5044610b42402e14181c5039401401c90703d50f2160005007001003090788201001002003e0300e006102c00401c035505600c12404a402940046868010540c03503c00107100549000400b00d0007550060b0151440c2c0c1d00305600e012102d11500416078101544007100801a107030701c00107510032800e210002806040150004103940e903403035001d0360180d0226005001c69440682d02c20516640c0f400c0c0f910343d010325483c001d0054001da889079030f00b40c0a100302c11424854103070065110564a84c1c00d985241414400685201c0c529607000b0f8002508450103540c0340c0c240000812100083d450744800d0039a64209040c40c0c40c900e43c0d03103050700041a4004004011346048281c008502440156007024205080b0030700844004001d140f400102401040d45404009a5030b00504406060075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 581427464 1250 581426214 581426221
    0x60618060d0915020301060e010c0314040b090906090c1c06050307080706080f07020303070309020102010f0501092304050d030c0c0b09160918031d1201092306010909030512 76
    0x4600810120758142c501c1c016030ba507510f42841e46072003284d041c0e44440d12070f101c25107481001102d001403c81c00860500040d500d900398159502e2004e08001d103134241c107044d501c86182c0203000521501508150107048100c041c00301d01611101a151403119581010300d1001110340040c01501e0554425034141c050b00101150070f05c0041140e40070b5a140313894101d910345841c100c00c000c0301e8045541c83c0041e001800840c6196200750000440303a0700501c008111001c07507503111402c6840a91040c4152a03949003d1a107803164441d4024034001c1806080e11285003d4507a251a000c800c403541c800c040d540d1040701181809000e07125080764000140185130b14081603034540e504003482d455070034038a0007000010140c21a02406084041480011044840c01d650903542c01c603c1c0002e2040c211942d16400c8525100c44d0440c05d1221108000400d16030790724144070341200c40440c0020070380b0440080b4440f40000009040d0304503400004005010207050404440301c0c003403008062401007004013071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 581428714 1250 581427464 581427487
    0xb010909050f1806220807060203090c030706050c150c0c1c02070e040503070b0c160c1d0705270909010b010206090c030a0b10080f030c0606010c0b06061806 69
    0x1030740300f0303040042c207400034038080c0800310780c1d8030b07403c45100c0e01c496140e01106050341000c004060301c05125909241c1000125036031780303003640c00c02c80e41c25203294001d81020b60a440c040100400508407400e2043c82c00144040b41d5840b6240c01d80060400890b880104d00d81c031040c1001c45544c1424142030382c0030036035040040d401c500040c207071200040c810204042001c6d8814a207082c01242d104009628107000307035642e0500039034018841c8499840500c1042a005480b00134418030500c6400c01c20005030502c004200b2600000600111500085040040310354200040b9403111183c42c0c2e614259040c4028008034201440b4142a04006c4010911503034007415040118610000d0b02a07480326908e9403030140d91401103e42c03d84e03055101e00e40c2c4502050f14840100d030410340d01071403144ea8070b480d00070841c503001141c101402d0300da200080c0d82045140511003550003603802d10346030808440580700c0b40780e0004050034503882042c0010344c1c40c00c05c00503455410703c425000b0304003584a0058204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 581429964 1250 581428714 581428741
    0x304090903021605040b100c051c09090f0b030d11100207030e130b060a0c05071212140a0f0e06090405190614090117070f1e05031f0b01090905 63
    0xf031110b9007414a641c045000d241134000e9603020040940a0b40c68818181d008682c841100c01c000d64040c0030707416100e0b000046020001c54003a80c90388a01c0c01d824901100071040352540c1100305200303840c004180f0145ea901081a450303503a240d10b00001c1070114854043d003007902c001307922582e071031000880004240d00300c0320040c41e17a00e0456400d02750102ca21140303419100d41562a41d802081000351708201c5003e90803030088140503d0884d82c895840b1015020303246032a250560786840c4107900d03003940d2680700c4e900400d01c0d448005801c0c144221031001030140c00d240d102400602400c080d0319902a150300c000c0c7c9942913070040041c4414280700352400301c0725880d1103c9400e038070300380b100c0071400c0382d0842c015404a0001400d0ba4400d6844e258400d05100d0f03001d20040c60a0052600020700c070003d5060940c054003409400c0ca0b040711124410103443c04031944200c0c0280c20040d0803030804651412501c0300e21340c014030f0104d841051103004070b03032410258100c000318174609014010200301c0d00303d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 581431214 1250 581429964 581429983
    0x130c032003071403150913060b01021b01210c09090605010e010e060c0106081002131401050a030f1b03020d06060c0f03030b0333010501090b0d020705030409090302 72
    0x20312100100c1000d640d00450301c000c450060103e5481c09000004402c42c10085034007907100760055501e400d1a40004904044c02d40d0420b030351101001c410818030036144a8241401e409000628655101c074000d403111101e400c5400c6c0c140032442a40700310203140c1110709401100100010401e6480c2140702400c019414028200c22134603100021695500403614501d050070140c694504101c03803182004240c1c5d000d00008071803035481d050000b0708040c00b002083c00d00c2851001c05038aa4010703601c40000810a40d1001c081c2401001c2203640c5a604981118000c0806240110700c00d54001501d0380541106004141c46412404200d0750165040d03025141440c100c44050000e1917880d801115421050789000d090051103060f00d90010f070080e40000450600034007501c906214610803042d801c004c0e04081021025041141c0d070b4003c80e40909580503010074204400451f040c80c542007210b0017491200d1107010750003d000c2c000d0142c03c1040d03900038584500144180030407071800075259241c15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 581432464 1250 581431214 581431241
    0x203060303040504182a050d0f060603140105060f091305160602160b07020105040b03100308030c0a0e0d080d0b0d05070803091903030c060908070b040605010513020c0a0809130c03 79
    0x9401619141140c00e01c260b000c846c1600d0180f5964100010000076142246c011103909607917902c4140094054096040218000c04001030304048405c0342509444004001500c15050b55a00032075541d180400e4980080795018160428003003031800031300c0c000200790a00d403441122003000410aa00013800d6040b03d40701400e4005495680b140040309001b0030100902282080c0018019200802d001c2c5030300104c6d045145203103075a6a25100d400e90700540d0b4051040c0d10000e01001e0f13040d00f044840000840940da2605a0000c940359070180d809140e04560310701e52a200c04140d80d40e80d1100d10a14035800c80103031490150340c1c80406584ea800002414080d4004483e603411054000d02184201e0350036444018095600b07540d2000104008041100c0001003403290b038005c512083d0302248140d2282d280040c44d0b5040004001c0f103100350280041c8802c0c0100040c0c40108004200304070b4141c0c4c0300b03a003991606404130010b002c0500d2120f9100c401840c1c031041003e402d5068001c1035000495 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 581433714 1250 581432464 581432483
    0x5010f4103100615180909050d031a130b03070b031501080c0c0d080703020c0d0305190902180603010b09100e310204150b070b1e0109020306030304050418 68
    0x190b014181c5036944070341d141300d6031500411480705000f4008a040c035401c0f10303070b1080096214102401114000341c0144c8060344410341c3c0785036640d014818524840707081c40580d03191084680c0010212420410404449503c17221032801c0c584041001202a1411b02440c40d00c900c2d240c42030248102c100940f180c00521550045250001410220380d0510480750140414001c94101540c84140c00303043d1804041d4200140c100d018000c0c001d02400424945e00030400e8104044404006680c40c0e542c80c0a45140a1008005940301054044a41c0c189103c80b4241e07a200c4001900406440b5010750f00300200c1d42c10040c900c510680e0681c156802c074a50380705a80c40b424040003c3c0612003c4c8040e610708988401c5110b580b03003030350f01314141c0e10040c0302140b80081e2280c01500542c1c154400d420815002c03602c00c0400680303940c074943c021440701c44500c0400300716080c0390b072341c020602c035840141c1d5001000c9001604d0174000c07a4042d2030003a2052211021141c4a0a0140608142170f80c05c4030a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 581434964 1250 581433714 581433733
    0x1050c1e0d0804050303070c021c0b070206060108130b0402040f02040e0103030909050f010e04050c060f04081009030503071808061905060f010e12010204091401081005010f4103 78
    0x18070b0000303010b19000402182107503a001c1c003d484002c441407040c2c1c0d11001204954001d2620b0159a5203070078440c1c6810102810506c0010f8039140c0301908a41c1481100b00c1000341e11005d030420680d00b2500008404095141c50020400410040619940c002d000090214807030f0049000181240e10039900ca00031140e41e0b070503440031150709030b130301001e00002e2100401116050164454200d4080c406071600103418500003819648001d030141140e2001040421152070148141d0321000c010078014400034095640050551000070440c3c002c0c0014100443c814610303038044c120240c03e000c400c0b80c0481c10802584840540080e5801403010706210002c0d00a040080b142d20030900183c41301890341c511503003003095941640b1500704041d9824007000800719464001c00e6001c0001d01d2100420f5414011418202940c1d07040e60700280c0c4c1000010040c681d0800360100444150342c4803240810078500406c800081011610410401007070100150404408045961000210201c40c85d481 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 581436214 1250 581434964 581434967
    0x6030a0b01110d050d0906020d0c0305010515030c0d020c0a0c06030b1e0307180f050a0504050610060f0810030b0901060612060e0402060313020a060206010807140f0f01050c1e0d 78
    0xc0e444210f940014002d01c86a207402115030854120548a001d01505100c4800082c1d805c682d044000d034800607403504010405814007420843c0200701c01f294041c99450040da41e15a41c2c1300340345000d0001e0342e0001c1e80407006d150510142040340da204403146801940ea00e8010041c010000d00075100c0c010f40304c034440240c1e10035900a4074841d400b0740600310380351074150700184204401c50a019150380301c10003102082d4551080c107214514900c070000d502e0a00d410910310f4076200130500c0d0348181640005008458000440250706641c502d4041310035078a0ba406141242c03141c1e84010325412401c8288422400190400b100359403071980c981504203400c205070800d4925038800c1d82075404892010502600b081c10086038804e8500c14110401202640030413240740b09a0f00c410010380282c2c00501c2102c20030710540000f402407003404e076004441c03200050149102c018001c1c1c8640f032a0000441203034000c0040e0f070900c03603580c801d40f00900002c442ca0415200a44a131010324040c030740c00e260245 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 581437464 1250 581436214 581436223
    0x1140112030e040609140f010815010e040c0513020d0c02010b0a0b07060e0307050f010e01150e04050a150903020c03391507030806010207141e06030a0b0111 69
    0x29924641100c100284540702915040c0040310610340003900e4100104513a1214050f054161114883d01d10b0203140440340c0408006d41a0040c107943d41080c050510390112045405054800110b10104541c0b101d28209490120650110360410408184a03000c800303aa40036028070060f9500a10102c061654120300300d842400c041d80d0302404041080c08501c00030303405009000d12851001600480c4112a603107103402504040b5141c0d884020010840a001e000364109031101074001e000b8035400d0451116890b40501a06180903c264000703000e00100f0040c29a046821920b44001c881012031b00c500a005140002d4001d8450501d0030040c500300054000305690b021038080c1003000c80345811803108503205540000c0c2c5441c1182e622425551300101000302d1080744074542d40c1d1074840c80c0141c0302c904018007540c10740d0020344041104405003c5c1302c41081d6012030b0004601000c078409105062a191030068025201104000e44070400ba4048085914241c8031034103100b0400d01150350703a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 581438714 1250 581437464 581437469
    0x504051c1a09031c09062f030c09120a0b042901300b070801050f090708010b030a1d06060909031903021e0d0501050f0f0102030315010c15020c011401 66
    0x50b40f0400500380019014030a00c0b60740c104002d80413602800c59280c0d070301a61004243d109504071038882d0213500305040840c500c170555040079040e04504d018055606580210140b60b40101034a449224112906001e001c80e155840403a500307160405050480c80c50a0381c0c40f001d903d01d15080d008010b4051300784003440c121181031540c002031450641c001400300715441101c02400c00d10b840e103640000c21054901c0d205824a6681007071540c9441c04101010380c41c0301d2040c0c0120014804c1c0000700e030f400013440e41503822804050303540e42c880e00100e00003440800510400c000c1c585006055114001c22124080d900c210341c0e21205881d01041c09441e8480c440f8600d40c00190b414588070100e0181d0007804046003042c180d0400c0c0112040f0f182031560001820301c86040e5900010b12031442c1800001c0d8a450040d10700e210043ca00200103581d80c0b0006c0c0686000b00b140401c100100d0384102c500400c400d5004084801c4004e00212540107904180c004c00e4181d42003110744031810304003400301c504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 581439964 1250 581438714 581438731
    0x5090c13170a0209040302030a0e0411120601050c120403050d111b03162d06050f07050a02060a050d0b010c030e01030e0106080714030c180c03070504051c1a 69
    0x103661600c41d041590300103100ea0301019000e000c0c555005607441303610081c41240250040d650715000990010080c10700450b4140c8142e24184409594a9420707040c0e0701110380c440c2989000e07444500041c1d07083d010301e800c591000d00c102e055103a50441504040c2040307138400e100b01c0da00d0340035007041651000c00f80844c1c405947d01c20a081500d429200c01c207511100000380c16541c0d410072026010003140500c2c1c1001c080c507010070720982d00d10307085110442d5149141c1a08040988d0408200802501c9900b0340c0c1d21003c0004145081845002e1018610244c0d008025666900c16804064a6074000d6100c5206040c90250315400e154015162805500c3e070581e06d03118450115030054005060b2403440c003400d99640c5102080c1405c0811800707001e00729902113030b80d0b0012103108140c40c0a0444481c2401440e1541c0030203000f0481044c103e402013065464075450b5503500301d08503020b01540e40901c0d84015800c40c400306141601200c0b84c100350242e1000c0384a40e4039110082060310090307402d200c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 581441214 1250 581439964 581439997
    0x20103050105180c0d020721170c09010c05030d090b0601110a0c05100c020d2114040303051e160b070c0f0602030a06080a0c0905100605090f01030f0504050705090c 72
    0x400c049213520040603c100745080041c10000c15032500d56141c0005d85084800e05180102d1540d4290800c054501c3c6c0701c070300303a9542c800740ba140d80380d14a28041c4012880c103104072010791504200c0d00b4001d4401a8050120402c0070300c00707905220010141c00c0d82e0950104904d0b61290f16020000701d100038500303410031100307803129203032100341b241d050514a045020460300004034401a0b4a0000500b000c078020652400019000d080000202c500030006005202e00e504094030441056400d80d4112605800d1a54070340702d100301c180d480ca04900a4502f0f1520340002c000d151400111550b4141c10f000b10540001c81d90b900c0426941c821440070b02424442d2980051000515a07400071075000544c1080070580b240d48038911490620001c1c1e048451004211045c00f03056480d118403603000e4a401207141000740b0307004001e0070300d220740902070b400380d8107000032050b0690080e004080b6260f0910400c000624040c02e140b925107083c2c0c0515840f0708041004110b841c101c24060710607000c82d854000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 581442464 1250 581441214 581441221
    0x61418070b090918011a040506010e01020601030f02030a14030409060e010605030609040204060f06020c0f03241005060403060b0406050919090f0f03081e04080a030e070f1202010305010518 83
    0xc081108001c18400700a9501302c06040c40c04400e00032000a0700a001030348041d03012080401043e508000e100354100030044540013080d0781e00084240c116a084000c03000b08042e030340086410241200d40103080351444100e50448008000020400c84040b03440070428984c0325070101d90440c100303100d0b1600150051021604c42e24002c2c840d5500540300a000040032681c58001004c0c0700d1041d801b820141c1c101c03e56204a03070a1000101c400e9100072000350800320400e0345000820000080c0c08000310050034005500402429041c00140c10000c044a0f03e840d81c9162210180030003245c210b00841c01c001d800141402e02c903607014010000441d282c0b1f5031201c0c414898008003031010044d105d80c007100b00410042039804610b0b5003554000c0d91492060318103202c0c000809445005101c00d010f100c0c90810000c40c01410030b0700c080100610b40411092002410b1518044058001c071a240b14a294000385400342c1001c28031209200f80c030144400da0307a48040210792018510001d20841014000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 581443714 1250 581442464 581442469
    0x61b17030601020f06090c180702060c1c140405010e0105010b0a05161b030224070303020a0c1202060928030309080706060b121302010f080601050403061418070b09 72
    0x145a0210043c4100d58610052850441c54808195400c260a41040f201f182c61801c146c451000c0410094030407680e00c1c14030140003540c0745001003d4140001003c11011a172042510740000e80340101c880501400c0392401da140c02c0c0d80800c0e18226803562030312640c044401b0041c001c65040300d04843d00a4103020a41d00300307071569031249104454000403c1c100c2000074220480000c610703405000016402401c61040c40f41c03060007c5100c0c03d07995040e440c90190101c5500445a0040e450710700541c80d81802c0c442902d00181c083c1c801800202c044401c0745115600042c80788c03082d4020001c607131502d506103030340481014080c001c08840300e000100c4027003c24041d801026101d0303c1281c44526004981d207038941224074541002c800707480b0008002076104004543d07075400c400802c801d8124000b140c0c1c0080c00401041d0100420301c50740800064040c0c1c00f420070340b070003150000c109000807000340f10940341e5600201e6002441c080b085002d10800c441c00100c1000ba41c502c84c4ca56490018151304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 581444964 1250 581443714 581443717
    0x5011d01080708090a1a180a0b0a0b0d0203060a0e070918020409030e090420152a0a0f060e071514251109100902070f0b010609061b17 59
    0x21184503c038400500000903811141420740c03404805040e10141403c501d4001f02c10952a00e4500c03d82c401710200300400c0d1240304161f0030520601c8002043e40420f070210314000d130355000113940340c0035820030030400f04101e4104a070604070080c00e075605030785c880e1103204c1220b0710b2918052008503950720000050a241d0b000319001d40c06410b044560f080315400040103003104a40485411031000342549054000121500c0d4040c0200d4a406084942c000340440c10b0050a140071740001d68a01080f1008900c510750300101c005a0050f60784044850070301c07450b40c8040117400c07905103240a4640b09401c2d804102801600c02008180c094070003120011500e01d003003158080c0180b90108841d640d481049001c1c0c021300e94100ca0031000280c3c0c1818001024661702c0c4040b0300418110041202e8000ca41c1a5517098820240c4016125046c604060410078a02079000b40851903a0300003054042d00001401c007114a169200d01300020a0000e0f8840c45049600040c00504281181c001d03a0b0880c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 581446214 1250 581444964 581444971
    0xd0b040303050601082401110f01060308040e010608010501050d1e0f061e03170a0306050a091e05010f1215020301171b0a090b010513060306080c040e060a020304140a0b0105011d01080708 82
    0x230211020f01e84089a450b00712a4107520490f6001000101000001010754245006001604004025624200028102c1d03c03e07008000b01840d42c41085c104074861880a0208604400300d003000700c020403001800041041e0700801e0b91901d0302300ca00c4a61280d8000c80181500c5d400b00304280a4420700c00f0325291038000c80c620605241d103921000c9256151940b0307040081c0000180495914000015009100380e640303a04207400c0d04060040c80194070141c0103404440e020104488841032505007035111384403034414800e015000000004801040e090074000c0c009128060305e401c0b4601c2061402d44c0b40f09a020a84c125040782c2003000039030303401d41c4010440c41c01818498508400d001154181e20f40540102c2c0100399604400c0c00002410405034181200c240c40410142c921083c00a0755104010410104282c00200282c10401c6d0303800b1414400e481c51080320240d80443c83d00d181115000d000345400288201c22400c0102203603102c1e424007003410f0b1076007010350f1601101207640d031200a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 581447464 1250 581446214 581446247
    0xa210b060310021602040e010c020d20100b030c0d11041d030d06030308090c09040b0a0e190b07090e040209040318061d040608100b0d0b040303050601082401 69
    0x811a102c5180810b0000303044001c0341481402110903544100000c86080c01d614442c2c0d030b850300c1d9080c40310381c1d00080d010384986001d0412200e503466500300b00e04080005d0307840c48000e00034140a00c007004c21070f0f00700e02d6146d43c04406440381c50202c00c081c0100382c0c2c0f95000c003074128040707004d07001124102a0301510840303907001f11002600050740d40891540c2e202a50540304150f03034007000c105141d40710304030a402010900242226031001d100068100c0700c040e10241c06a0601c4000c035042d00c00581c410b82100f010ba4095a001030464145802503040c03e100c107035038450380707200010b801c0345c41070b841c0809684030b20348514101c3d140c60702800482c800c0148100c0134070040704002003820440711030050040586d0b580b480320703c1d00c080d80d511701c4c6d00d4034041d510fa00607810464107001e07405001c2402c54004800700d4000404003100f000040010340368a034007501c0a54081e080c03006041c4d0640000784507417001c0c1c8603a81e903030f1144100c0d451040700505002118100074400f168182d880707200700b01c1c86044d86 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 581448714 1250 581447464 581447473
    0x1b01060f03080309070806070e010810050d08071202060c071b0e0a060f0504020c2a040207121b020307050409080c101e0e0a080d1506020c0a210b0603 66
    0x12008896010301858009546041c404002c010341c0940802850000e0003460340a80001e091510000c4c002143d00035140707040c081d01344002540782d00d0400c520303001004002c00713450040600f0300700f0030a182c2c4200c80580d001c0a107455030000d032a00000d40c8074001c09a0416052034403142d41c40315224500c2041c92001c4154595800003a07250010005601030103450038000341c0c9900e8000c01e0100030b103c5070300980c0610f005000d0800703498030208141c0300c1c001c07541c0f000b8000c0c1c6100a51005818801c2c6040581c8507102166503418002e12036a44440d148031a1603c049a40c2d20590045660f003880c1d60003545a8000d910502240c00c242c1c015540341440b4402050502005c86055420720109421443c101503656003800d003444000345400e50a108100380801c032107000920487d44903044d02002900741c2600041c0c0b180c40e40d040e584901d108200b102034450b44151201d50003900d800700020080c0c8129042c42c000314800b107035401d03128503585948021506000742691003042c3c0d1480104801d40c9400f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 581449964 1250 581448714 581448719
    0xa091718040617010b032103060a09020d0b210d110a08040e040209010b1305061e070501060612140f1503070b030709090209060d0b0a080a0f02040e030c031b0106 71
    0x880340a490058450710b0099100f07608a03984050844200340c035024401da0200b201e1045000c2e41080c5013411050300040c0310382d41e590b11800f1902c10250b40d070041410ba4400200e18480000542c04602c500000311030444c2c240c0042500700b0386000c40c9140b090599040280461151800741e80344050103141c8005440044510340c031106502e4000380c1c032421850380380c1d034104004c500c4c000c0b44140c0540100c0c2d2546041c07050507686130406401c2405070070f001d400e0002c0e010300a0702c078000a03c00c2243c4c1036198a40d03942c545142080c040c1c101481100c0c082200c4080c1c1074560440390140f001e080f402d480e160000c0344e6550300309039910b203000751100210000348001c900d40c5403811320a0a0140c1100c1798401e80e01e05144034010036060156004212151050051080650350582114078180000c41c012405101510010722030742440d9101890720301c100c1020b501002050410111500e000321001c1215030ba0004449071244a240c0060702c590f08200001c288480c010a5002c0c001034501700000360854 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 581451214 1250 581449964 581449969
    0xc05042c070f0603060f0e042102070b0304140d05160b041b06110f0304031a0712021303060b060316050a0306080d081f0f05010c0212060115080a091718 67
    0x20341c183c00580009460703c83c180b1624000c5940da1005062490a1004500d8141c94421410700c0001845040f00150600c00d144140300b00480c0004c5c18860300300555a003030601e09444002c3c60400424010b008100502044074010350030703180600b83d0f402410021a81556520b01100c00090089520405070380c031844000702d01c10705c2c40007e4001c0307407600c800d00f80103540d1350b5103020b2a00d080e952055100300800e000240900700070000c0c2078400c07814166252900d01007070303400892204040d0016480840c4900c0c0c80e0390344480c1d08e000c8134001c010400c01d821060040c40b03600d00c411105007070760290bda4461041c3c4e42c031960060149240320310700015619191203034913090043d900b90580c001860b500a100e00c078284a801c100d807840c04611003229043c07801d00e5444054140d8400c042c18401c2d00240407080d91220201c0344200543c40c801c0d1515980c5a58000b074080854514107400901040001168403a05200f40d09005400c01c940d040d011024a91300c1e03142d5407040f04241a00c4045182209058 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 581452464 1250 581451214 581451239
    0x105010b0f0f041e080f060c0f0d0b04110a1403040209060d02030a0f06090c05030303070e060a0201060512061b12040b0712050f07080a20070318030f0c05042c07 71
    0x2401401e1400134183d2801c845c0030320b080d13482c814481d09504000c040c440f100038210212102e802c04c12994940359a00e49158400918400003c190445d0030400300105004500c8028007088000b51100010380300e5400d89846940000c43c3c0094001040001042161408501054240c1d10050440d1859070140d542d484a1215607001207030310710b44800c1484104007540e40d07164060103054000f9811844e10340d4005100d007608219080c0217003000211050164802e4001c1c0c8060100030340000f000382d0001c0750031a40d4510803a01c07005503403100c152504902c070180d400c8509000204008058a4130f9a0712240195007020740084103125001c3c9003c41000308038001c3c68031645921030f4100403481c00b0328024000c4600200f080c1c0017545041300b060901c00e13411103c828501041c140030317900d1303101600c0c1c10b686024482d080c0d1201c99400c0710000040040001a803102c542c80303100007002c52581c400c00d22040d20700220020a8880c5614044400b40840d0140c0988007a03000c000c07502181d03614290511b04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 581453714 1250 581452464 581452499
    0x40e0316080405040c030506011704020a05041406030f010c0906030b0a12061a0108071d04090803180118020d020d2f03010623090a0b0a060c03020105090105010b0f0f04 74
    0x41c035501003401c1015250910070070f04840f08a0405100c2e91521100082c0303c4800365046040381d40585c0082015902c031700d07902101034100548108803041c0e1402d4000341e20071003100c905200340f2540a24101801d81800759001c54100754889110003800c085066010b0029903c4094000c000302e580020000300722004554510701900d00015080202e148035241980c1c0c3c5000d860510002070144291154813030794000000201c0344070346450720003980001c2c02400003804050007003840401404800fa1101e540701d080d40702c81c100200505039081c089a070f10301031232640196201603032211400250030240540808203200742301c500540202e08900c43d810601c01c0a400300b208440c00041c40c100d080910aa03006481c2502064158601d0361104401c00c100a0054030b01410000340482d445608580203241c0c041c50040c41100c9240c4c50300001410104000e5007a0010f60901c0c01055001c50184592070584024a41d02c40c0303003010341128446558000000c1e01241c2004110000302100d40401781c1c0172 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 581454964 1250 581453714 581453723
    0x30f0c0c1c02030c0103060e0703090501111306020d0c0c0b0f0903120307030f0b030a14071a030a110c0607051b060f060306060a060c110d023a030e040e0316 69
    0x1d454086005042c945149000d81d1814180381c00b41c20300c01407950f01e1038140c0c056810702e03000c2551112850000c2c098034911080c0314140d0b41c0480c8003406012107041c0c01044e81c481d1343c200d0f5004c42d19004c040341c2500402341f001e0441320341c492050118808000c0100040480741240381c2c980321000004c640761594a83c540f1200300004414018a5a414024600c91804640b003c0c440c40b003003040025114900800000d0010201c0d00400f007102900348240801000e80000d014242c11040091110941c03007160703030031081d81c1781c08566070028040c0c00940324900d01042c02060940d42d900001d03203041d441030444180da60300c1c400c4c034401c0c1003008000c0580f043c803a02c00c48100c24140301d0241460b020700544418030800c0960030910850f64403416400d581ca8001c1d0111100c08d80d004003041290311210703000b03504001402e00505544040003113085062214083c1d101052505444184002075290b10050025100010016581c0f5058000403e6051514282ca15020244d0022040484000000c68 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 581456214 1250 581454964 581455009
    0x3050d120605030309090a051503030301090225120c0503041509050a050405090619060306020309060403090806060105090d060b0916080708010b1b0705090a0204030b06030708030f0c0c 81
    0x1a46103aa60148000425040c0c005505000100780082c040c40001040c100c2800d5507400001c5503800c0034411701002d041c000d016a6981d58443c1c0c1c0707940181d440346150020948090248040315039254400c00700c01c6810020300e000d401015982103c415045000560b944d10040c840031900d1032100050071a006415100c0d6841c1c64601400d00c580c00c8581d900580c40b403490402045000705010582c0c650010100702440d004c002a0400c07540203105a400240c4258070100800c1800a40012614007a60190302c03508140c0d9604d01c0c446650ba04120380003400281d05000241040c00c0c4030791140c180070701c902004207600d41118042450400202c070300004c96441e00b258007104a0700a402107130070116601c0c2401c1d41d50305100742c840d503502c41d0181d000c5112640080442d200c0b28148038400103424018903a03100703404e00c50301e0403020b90000c5c0130945040780f9104c040303000343c07030300060b410112048500034505001702451031115a4201004c400918015400402016592100050007107440b400068 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 581457464 1250 581456214 581456237
    0x130203010e010c23041502100603030c0209060f01050406181703031602031218030c1005150f090c0c15091c080402010c0210090306061d16090302011803050d 69
    0x2400130710408000e060100c0155400c42c0c508014104a03002e96048228411003000c03880c4e0220300d45a101040059900c1c90180302008040c5d12007000da8195000b1200e00510740c0b200d40c10882e00c865404011404944100006c002550040c00414003207800401c052421560747c240d14545c4c140518144981c035003000041111410740c81c03102c5503036070718540300640c10100d0b01d43d4510b04120007e815a40700040c05c26540e00f2020082080b81c02c00030f429070079104100c0700c20200c0d1000e0030058941000b0300c0c582254807101410054550340c20507900510b28035050300c03844201e42e1035a1040252003817901a000c2c140701a82008a451402070101b2001040143e110407104001180a011601c0802000d03405220150b030f40b04800d401d0044c2c044074040e80503440c94009aa071143c051380001d0015041000025115040658803e8644542a0410300d203594042600c0000320606023424041404a401400517503c1206c00729850310412801d18400b903107e1715018941b4884070b80c2000080c0c101100b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 581458714 1250 581457464 581457467
    0x10911040b0c100e1c081b0d0b01090503031e09040902060705100b090708180f0d20030a051603030209060c0d09060809070b031f1d0c070b0708130203010e010c 70
    0x601d0b95006101c005002e8a80d620584145001000082482000008000705245000741c606181801c0b0000700352039540c0a23480c5c441009014042c25041c04540c04000c00200e84c00c01008a460340f041c0500484a0014001d040300456005290440d8220f6a0b44000388010b0722038100800c0c100380603c1c020305007240324100c40e078190b81c88a806503009803016010300110940155120381c203c1000140794495544040205203800a955070400301031081c408000410340d00175002002c1009804503101000d03d40621807540c070305c14100c1c82c00000b0001c000b048486400d03007151507070b4bd911134070b009407400003102c000036042d4000c25045500360300b0412082da001900840c42800620f51810541a5803038083e10b450385958507442a00c103049000000038607441d00c4890800c1e0f80e040301918000219882d6001e40f19220311041c0c4072781c0361018160108500c003044206803820759520408011456580c0e410860314564086e020348114a0b22310f00c3d210069030b081c00b40504010f6100c00010302d001c50000c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 581459964 1250 581458714 581458721
    0x2070e0912031801140c070c0e062815050903010b090613090302120a020706020d05070f020114090d150c180302040e0a08030f1914010911040b0c10 65
    0x1a44410340c06039001c003030141080380c19a0b902c10500d000c1d120240e11048640e50240060b80c01100b13a13040c0e0708003006101c900e900060084107001d502c00100190b110b426246210741c06072080c607400fa200100300c40f21200a000441c003d40305400000d0042035481da003941c441d1154010082c007007400401c0c41c0c441410240310b44400040100d40744452410848007094541c0041d0703841d0345055032241c12074000d05000300324134012150360244580d654614540025207500031801424010b015260b6070b1903000d403141054840e99078001a02248000c0144d0040d6545c2540724804c1010131400c0c03000c3c8500c1d176142e00c40b491402c0e0141c0141d901c400001c0c800b0310112a02d03024072405004d03000f00d04c0c41140d40380441010699034140d900091042848202c0c92910219080091012000000300548400c0b1303502018000d045100c02c000800740f8040000066a00308036840309040c840c100108180c00441c1c002c1d104002202c48024542500d03140d24411503840700c0d46c4444071341c3c080650552100010310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 581461214 1250 581459964 581459971
    0x3020405120a0c030602091c060504030801150207060503071b0609110a0b160804050d1209210b07140403030518012102030c1306020a1104020310180e06040302070e 72
    0xd010b4211520b02e65902034803149507020140ca00d0354041000e40850f00c822855550300784c00400315490481d5130745001005403404a60480010780302c01d000098001031600c0d60006103519070003428040d4140b1004803a00c0e0001400082003023002d40c0482003081c0740c0c03042141d9032402500003050a810604110305c41c0c02c42d076100306002d001c01c01401c20400c800101503540c0b000000e100c41000a00b18103200919000315000190300c07440820024080140d40c84c6042c4e0b442c1003c0c3c507412030440d40d8001e0813000115400d034001c0d04401d01c030045000261a40002a0300c8180b80c14410600f00350049620802e40154100700c010900000314002c800c000054002001002480e0140503801d00220300c607600480c49415a01407a0040041072500c000001560340415841c112556110360b10b084c001c1d940c0c00d4200c4181c484200800381c0072183d040c6030080328450340303000c83c021740303054540007032034201150801f42c814a02c1d07a20400d110100d5000d018440c0500d000b54001d203182401d091880401c02c5015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 581462464 1250 581461214 581461249
    0x609060c180e06310c050705150f0a090611030106050a090503030a0c080703023a02010b010801140109180c0801080a03170c162d1110180603020405 65
    0x5104011450340d942c0d1030000d6150110136828445030030700743c1101d010300c0c528440e011528100621100031135404000f40200f0350088084500e03025001407920100d00d401d8a0014083c50302200240358160503401803400d680c89a1800109844140d0b03000605070001e0b00854006040042c1c11869140c0c011061805804d04401a5107000f950440281c102110700400905082021580e6410700d0f000b031002c00c00d255000d8480c062084469041030b000383d06a00300c000400c0c0c0311000b00c103103020310500c5581a48074042e1070b0190542d0800d8103810385003080340802030420280410100c0c3c6141150780d64910081ca8180114070407250000c0a02240c130160007440440c0c1c0010403c502003030b48100c80002203035a80d03c9276011611a400080041e11a044890160082e840313040310401181020b616007020410101009201c424841075400d800103042c00b49c0000da02c0d52400103e49400b1210200140311403d010000ba010005043e040c44081c0d0b00440c0400da0204042181e403c00350032210404005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 581463714 1250 581462464 581462489
    0x11030609061005041109040c0918060603050106030506220605220c0513030b060f040903080108011d03310608040201021c080f062b140601030302190609060c18 70
    0x34141c51401360084c4840d451265440d007491611140c01108807001030325450012102d000c154ac0348280192041748508800203150900000e0002d02c20f2203550700a40c2c0c010007070245034050080388410b108445018a0a40383c0e00c2000058642c4c1daa201481503610300500300b000ca440c103d03904400c88400203202e9040c00400c100680426045109120030350394403a03841d040340d840e0140480e90703845501d10156045894060000c0902d5000503415040b140050004d203c036042d110180b10740002010815285a80144000e069083c0c0c1307903030703022450a2051110a2455205501c010840c4050b0b0b0001c030101e619802440107559052000b00c429413919039410744c4551050320000e0002c00020030810a8101d0340300452401c0d902c50100b1880d400d420b03001c0c1c209407403c03505040383d08100206c0803160f00c031440003842c020620100741d440c100c94068028152041c2c540b09004820501500100c0d0a9982d8424038000200d240c801d06003004031569403424459884a034403070003140d1a4000341c025895 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 581464964 1250 581463714 581463731
    0x30601060f080a090528110f2103132907120f091707050102160509010302090408040b0301030609110d11121513020a0906080a020d1103060906100504 66
    0xc2001400f600300c6001c040000d44003159003805806e03e07403125000c03480740c1c0a42a050900c42d400201d100c110500416200020b0000300080044981d42e00d8425a000440c02c8900044254049024501402e807502a40d150407803040608070742c03080780d410000a40e015805040303401880340c1103001c0303d8000c42c1002c5103003040301d4071800411803414440508109905d0302450826100b008070b00c0040c441492030048285001c914940c8940075400340c18018420100c482a85a1040100342e0803203002400501c920f13400c6400303020340320500030029122100704210009407210340500450085010300800200c1402910f4440840d044110000c2d11620042d100c04021540b0810704910710b0404540b803003200c088001c00d66052402c00c014a40c00c024000c001c100021001c40c2e243c00e40d05100300d60300a02103480704004000c9610300d010340c07020350380f005043d40c0040c10201c500341d06040c001c0c4801c0e10050440c40001e80b800070101d4055800350404014044c090341000c0302e00004d848110780c240210384 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 581466214 1250 581464964 581464967
    0x140703050c16020607060507091403060402060d0b150a08070905041a0418020402131d09060f060604050319020108010b0a14070809090c070c0605032a040504020403030806030601060f 80
    0x1d480b48079a0321400460b845011981e40c0c2044078841548110244040e140c488070240204800784582141c0d0320026018a00624010414503c40c80c0d000704064200894065010700400ca04412183c2051000441c0320010b040500680314109103542c4990a6107801000207200d4407659000900a504021a60302007402c1c1c60400c5090003400d44000402c030a20f100000c1000500d144040d41091000400181c0c04011080f400300361407100840d40d10b11003000070941c1082c04100c139410215008200819081f460107080660040320040c889410070352550002801e03c81c00b44480507035403288040520031540c210a00074010300a07450003504159484001908441c031207804006a20000921142000907003004c2d5094110041c008810500c1d103080501c1190b405640107a402160040700040d507203110b0740c216849400310365096140d1100310548081e01004004024519039400d0002082644a038400b07440194007170f50380c070540c41c10070703100749410100180c12071000c001c0d18140606006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 581467464 1250 581466214 581466217
    0x9010b0d0e01020d0608030705011803020303040f051c08190e0706081306021902011404032a060c03063f05030c0303010303051902010501050f0105070512030a140703050c 75
    0x400c60100003246a2604034119030080c41070916080c01c1c10b103012030100d80c4031800006844464400c07402040250145038403d0000744072040e004005910400001e400a0452076600d4a110301c20001c1360750112507980c0444403035021506070000596000c080081c45020040b840129080a000401c024a04440702c1900ea001c140a00c0c424031070444007145180ba0108a40c080301a00158215107a0030844034440b504207504008000540c00c208041030b040354100c2156020356450f4644081050801054a1402c900c1c010350100504142a50402141440c041c00c0c1c551003050b60001189800c0824a150000088188080c01210030301307082019010030104000d0059108a001e40d07001003868a58036600c0b92174003000d454000400000201500100500381d4400b10200d1400300000030070040b070888000f4440d01d60301450f83d0010f290703154001c600030080305002c1ca05484642c98000e003552141d9000340c0da07074106a6a102c0d0100d03102180c120388950020002e280c103004c075080c01551030145 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 581468714 1250 581467464 581467477
    0x2030c090319080406210c02010e1b18040204024e012904030602040614070302070e0c07020915150a09061218030c060c03060b07080d06170601060e09010b 68
    0xd00c81019940320103000d0346a92080071ba400002d052013100c60040c4000d0113441800b42e200440c1c030910404160104c04010942401c0502628241c0082c4030340c01b441036400005041030707030415800c00c4504800e40030050641c3c00c03071050f0070301203000c4e41400c00010300d40d100b9002e03200302001c104d554495480420048141c1129a41440890f0900e61441c5210615001d17101c8481040c00000b000000c12138660054011a10b03281c9400f820100042864480352269a01c024010303000035005021420260001030340140c4568000c608000140c0d000c68910041a19040382c0301403078019031119850549288400c21104c80b0031203080803000200a840c80800d03000d040140003801c00140003d0b4101d13400829052030083c600c0564443d039080103010043e00f8a4186e9141d41071003202c8001d2402402200225642901001c1c07801303210ba103c244480c2c08c50200c6181407601c440000070042c0007107071840c0c04402c400c406044654500b0802508110548001c6400b0720f00e4100100314461103081910034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 581469964 1250 581468714 581468717
    0x120f0f0c090f090606040518010501030b100c0201031a100801081006081c0210110a03060e22060f0203010b12010801050705161110090f0e100308160602030c090319080406 75
    0x83c01e480d408001840c40c010350304100e4224481021010141d4420f10405040760000e8800308542c08094040c4481005d01d04145404200c001c0341400055119034828140005881d4500110b03418900029541c0070030480d031840058100030045c4200041400751490030108414100003552920403c0382c5c60303031242c110070100c05a0528240a00d54000d1140b0040003100d414204100307221b01e81821b4554000c10030718400079203448004901043c0902c14107000e60030118000b2240034142103641030103000c80c08101c0c1c0b620307214001c0640c80c420900265018201c3c88442c0d580301d1003840d016030041c404c140d1114030568144414040d4440c2c1000c22280b490001500030802a002c03414515401031103107110302c2d0011210b1101d40415503010581900b0707103015003511400c00780d42d02100030343c00b101500e007441001020b403010000038036064020100d08516000c01c203501c0c04141c07208012604212142580d40a0018404030350b0300c1d00703200c0114002001c103101c03c4000c444e526100d00a02441c006d910 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 581471214 1250 581469964 581469979
    0x1c1211030f0a09080c0405151c02040603060621120e040e0f07090c02030c250b070b10170a060b0f09041b05220908120f0f0c090f 57
    0x14140442401240c504180300c0082959900071184000c1c140308162051501c503000d0942840c45c0c52130103006081c02007911280f8000340320030200412110000c1c503a09910072811605007000180c4503400307000c0007180142000500e031403400b1100c2d4140070050718100035150800c04403200080701c04500d2403101d8010f2810a02ca031110700045002840d82c8141c841b558030030b10905090320b0303000240c0d1030166540d5003c02d11040d4603820302640d8901442ca0b0700416034000308010424030019801a89d890130300d00380e000446c4c3d0340d189400c800079484200d05941c158110010050b1040c0705009042c0142600551202d12030454030160361907a0020b4002071106459002c10f101a0b6210505405058801420160b4a0805141103044e0661681d505090748044400024052800150480103c0000b4244401e810349444210009001c5450121407144060100d203c00c40050203045114103560103130072029041c607801d03001081c90020305000f6070302410002c03410941c807003150603855800300b640c60a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 581472464 1250 581471214 581471237
    0x50c0f190c02030a060903110c0a1406120702101401060e091b04060315270e1923070b0d09020607021c140a031d04061a04051c12 57
    0x1c070368001640c01e01035454400c0801800074054242c1c0072800f8680300e40c0711021314803c11403039944c03908002082c540e40100c842c0700c204160310700070020300d50000c0010443c0780f4003400d40300c0240207800709446450050340324429800041d5803900c03074060101103540c1d60032015850301c240241405070f4080c1c800d0084200d00040349444035a9031842c403504580c0010b50351200d40310032006009005400c0200108074500c007001515000c1107100c00381070a105181c1003100c0c40c070080e41c036002d4541c018020b1958451001058081d100d1400d202480328410b800b101e400d04544881c8801c060240701310381c1a540c1100c54100040b045204c00c075041c1850912000c580000e050000604a0040ca00065000b10008c41c4208a443c000300c90306244520901c0b01c210600303515020156203030b080290040200c1c40070000c12842c03000442c1602d614850041c000b049039502c9010540c2d9405030400040d1020b00c010506200301c0c0752040d05042504103031403079001e240c4041d0712001c02400c0c00d000703076009200104501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 581473714 1250 581472464 581472467
    0x303131809120e0a05120a0b0403020a0203071202011106160e0402191707030b01050307030902040b030f1c020a08090108130813030b0a020a09210b010315050c0f19 72
    0x816010307800c01e00079101c02d20681000b070b055000c28080700c0d00c20800140085218503001b10010403104070000100b42040042d80c0d062003440c0003030403e50651144088520069904200a001070600d05c6002c48001e038852001406051443c43c0d42070441d0044010041b0104490007006c0b420301d0b152070001c03014200e01010600a200d0b41c028607482c2e00006050881d80c80d004000700c1c0091011403a4518a0303920034200300e049134079510400f40083c0f010004035280314800d42050b070740b060004000080c07400c00c0c60002442c1c001f084a007102d25400c0701480b948800140b002081207441c2d94000350900307000301c1e5102c07800c91145a4030a414010240702080007060001507454040d5800f078251a9249901d510f078420045103440700b2101d095004002070a80c102d01d00954104040d40d8807000121410203506204012004010260404c004c800140101e01c60040c164000c40c010180c41c00d491030460714034802d076040102602c0c0802c00130084501644c880f1000c80d01210b00611048030465080c1d0030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 581474820 1106 581473714 581473721
    0x101712030705030a1416110703020d171e280507110f21070b0906031603090819021b06070b0606090a06081503031318 52
    0x22031240c0307000380c02071a0000c008131300c00700f4031080071085004c2c12442120004d80d401280081c615200c1d4002012a2125280c80040d11406044d43c02003124480009402800b580c00144111554800c00c1d040e503265091000750030340341a0650005102d1500324131045002800c05807131041e0001c10241d80380184c518251503e1b070902c221500d40c1034100315070750300507900b101485084840aa8030581100c0d2000c9400b00401c501d40600392000d1710700320031038000821881c81008606602c0c0d0300c07181600d500c0345605641c1c1c2c60003240c404040b0054004050b0041a42d030001c580800d0320502d507070b400c00030100e0517800c03100d0320844006903503500500040c00c01c3d00400700700540000326500080c10755000c000a0010352524031250040354001f1000d5000308006141322007407214040f000280358142c02411801035042218400401200ca0303100c1c400e41c42d00d00310303640f4100300c0483c140c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 581294964 581474820 := by
  have h0 := BRFrame.cov_init 581294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 581294964 ≤ n) (h2 : n < 581474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
