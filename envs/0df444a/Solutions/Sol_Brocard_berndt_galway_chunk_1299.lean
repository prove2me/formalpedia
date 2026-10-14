-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1299
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:15:01.668465+00:00
-- url     : https://prove2.me/submissions/5a88fa7a-9d49-43c3-9605-44994b22ef3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 233453237 ≤ n < 233633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 233454487 1250 233453237 233453261
    0x409060b04030503070f05280203010c09030201021009080904060b0a080c18060c012304050f03310510030603150b090c07062c06071809021c06060201 66
    0x100400380e50345103003905403140b80320141603500280702940005d02e520214111103409041195029003503811019070b031409000e0b9402c001d00440c5070307000c21400c00703000c0d01100f40d00c1424415883c0b8a55000030351901659041482c049a0b2601003070700f0042840c0503101080f0020740100a00c50300da8400880c0ca50040c0c0346240401c5c02640010705414107242118440001c9900d00c01c1c81c03e81103c01c0c0300007078100740704502865403101d05d031000b0460a03107071042b0a015842d48840490510b420100e041c000d20311910310342c0f9003041012007203200d02005e81540c04082010003180030000010905001d0f911508419840300401c024082c1866054000c94240e80c020550140111512581801214031130204c940d003004071013000841c3c90b40200041c0840500501d000706000b05030f0b07030401c0c854001400c02c000b036a00030b0300000001d0040070018680d03c203455041031480b02c0b0500000305502981d9110b2079042d9a0005030041d205802000c04139000310504100b4486640c40341e0000c2d0290040075a60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 233455737 1250 233454487 233454491
    0x12041802130b04081501060203090f0418080909010e090a080703030b210106080328050d15150c0b04020906030f1204090b030d0807050a1103030f15040c02070510091a0409 75
    0x3079070204441681c17850481c0c0d1103030000d41c600324843c014024015401400168055581d003507000141001800021b0018815003402e5070b039035611010000c2e1142c06801c080060200c0d407041110001c00001e013000000e40080440c0c0d141d00c0c0c0d61800324080d0200380300450f0000c3c41c2241410400c42e1464801400010350300081c4900b944491609a685c010004000c88212012a0b00e44400f080000103410b40c03109803070b000c1c0ca0400712060030410b9485528800d900b00406403020895003444c0d00031000c50f064180340040840d00a40c4411030140320140020b4490301803013021850703603a020001010341c9000303074059540b02c0c0d81500c140c64403031b04144500d5440c0703410716603590700502c0e010a242c4007040641d00c90391416100c43e4401ca500c0d4108010719010703c000b034842e10b072207003c0c204043c40c030405030000400c8440c54442441310054044006c01401a410b00981011840d000b081c80d13070a0790001d40d205068190030709821131318004998801e403401c0e640d00f4485031904408500400a40d240d007101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 233456987 1250 233455737 233455753
    0xb0f060d0f0506101512020a110a03181a0702040b03030933040503060c0306040f0204090b03071703070b0613090f0b090304032d02100201150812041802130b0408 71
    0x3645d4124401d403001c3c8070011310b81c55800c0c0c0c85003805a02600c44181d0a00d00f00c41c44104d110700051401c20a440b01b03801003940024107010101d0401d00f00d5014102201c209074682810300040c004a0140800c0244140e8903414004c5981d01c00b00b064951802d401894603101640b1030543d03c05400c1030450645081c115621181c1107403040c001103074119240030b801410782e0380e1070042944058102a181640c840d460b1802c0704000d2110380060405407074a464005044803410040501c0d00c0c0141d0701c40400250380c0071070404280b0b0701105a80341290042c04515a903690040001c0c0984007141c1840350091400515806224000c078500600a105500c0703070140d80c0300c0100c659528001e92000910304800a440c4040410703068640b1015060444168000c030142c55001500790b04940d083e110044c3e550742d540400d050000c0800b8030041c09103a010f1710950945440e1385040384140d000f500160444201140440385440e4101c1e4034160361040f41e8a20141c41e0001901154000d01c900030f5184142c400d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 233458237 1250 233456987 233456999
    0xf03051b03060619050a0f060201150503070909080d0212040302070e040209012102030706051c0204030b1506040801020c010515010807080f0c0705070e041e0b0f060d0f050610 77
    0x365515060801401006265510820084e40070880c208121a94600c00000261a02c0700c05c039140140002802da003412030b042040c000d0841f0500c4148154000c0c81e880c0c01c02c459140800c41b0020303109202408a070707007412030800303d00902c201240382d40b4052001400c0001050420811801284a9400ea03000036944090b0500545000d49002e540700810100410a0004074a951503402c0c882c004c0340d030361500c065000a03091802179444070380842c40000308a5000380ca2080207041c8803072910411424075017592241102d224000704207001d6648503048500c1c9940d02d0034140c81c01812018002d540d00c031140700210307000c1c0505540c403046100c60420050380c40c0d070081120910409503076480e140c50b9620a0740d41c610665001d422001ca00341c040144101090040c4240000313490000800211428286040c00703191002c50502c8003a04180000b07200000c141c540783c43d8000d040e03030346208907985940c00040d407000d42004000f0820300e03840e03401c43d04100b804100f81c0d100c3e48071080c441d010540d13550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 233459487 1250 233458237 233458273
    0x10e010f08010510141c0c0f120203090304050613030204050601030603020f010c020f0a0801060f0b07032c04020309160801020415050c07030b0405031215060301090c03090c0f0305 79
    0x8000440801c2000c401407219040c081c012207841100c80c50070741041a003410401c1025072050f0541c115413058110000a100c4490140b038140c0744480c81e2484489140c0400180440b000704140c0100c00e0700080883c1542004205039005000024065555004114440003040f40b0921049000e94282030026171300d917010b8407400045a402902a410444000c40111071580490400300c0e8080c61041d030f0a031113030f1103404100d00600f2881e07000041d0107040021048a05171300d50301040c21030008014041c0003a50000601e072094440d2100f65003c54240602191204420145690030070310204c20070002ca08001028500c0f00c0e0007109a0381e46a0300c8100c01d42c240c1c4624001c145451001007000300341c20344920001c140c80b4640c82c0a5401e600d07226503030400d24143c10381c0c1c261140c2d40041450044044c84c46040c03a004810a20040f100c03041c0000440d055000512401080c140d840c105e10010750700941021803241d40c420303010342109844020042c3e144c1c106010070381351071003110b46815180c0002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 233460737 1250 233459487 233459507
    0x71d0604030c21140d020f0f0304271a19030506190f140f10060e0d060207050d08070908030309060f060a080706170601020c010c0b1017010b010e01 65
    0x2014212007000e00300740c400607003120801100c040900403022040f01098050710441071480c500d0380644165401000b000349040c0d00e20400004c550480140341110840010031102150651441c010007085012000c074185038680a141900c0b5013011086400e0044403c0c0c02540c0709000c4a10100b4000d0002a2944d844450f010040256000c1070204000c034070900040d00386108203110100f913240c1669407200545010542c0380071880040002c0c030038a90008800c0c5a4401d11059043d01100e00d0400020136000314889850b0041000114110a11507640c04850702d0030b4108003103801d4500c403818001c0240f5400c83c0c0e41070000e03005000102d0040c8010003101d002d0f10300c4400a2216841c0c48803900014280680034942c406001d0f440084e42030380c01e0144000031f105585448a02129480070040e102d4401415035046401003040341340140e1700001001502030308a4104401343c1c0d2104030700c0510241c103405c2245020000749590f10404c01c1508043c03a80c40007a030391680d84554500064400d0040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 233461987 1250 233460737 233460743
    0x30b010f0503090a03110102130f05010f050708070602070827030601053705030604060501050a0b0a300e0c0a090219032f030421020d0809070806071d060403 69
    0xc00b920f40c44c08a8810140c0600a0315018001843c20341c00c0c4501c4407600e915544000e01c1090401d00812107507070410f5103000d0260302d070b0400504e030102c160380307165376441141c1d001040541e0224a40040c4104201034403070000c583c3c911046603d41548121540c500c025080d20f100307219940010603141000e18000c9401a4650302032414030140c602c02c0c2001c0000590364204514039003c000071281d504120346401240948000a031355414101801400c0c201c40e0041101400b040103003003207241d40642d00d021603440d2000031741c898200b00c194050078620643d00380c041440c1404240d03d5000d101044028600100312500e10400e561191408141e0207134084140002d00c2480383c1c0d03040c6c4c0c2d0180e00184514010043d01040040724020160850041c8070320603000344001200708005c03c401540040c00e210b0411852403803a020101001b0342e21100f1880c160304200d405004074204c10b20401ca03c0028003c804141d406929001d0001000028100c90355045079814505008241c2420f504a40030f880d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 233463237 1250 233461987 233461993
    0x30901020310050303161e08120108010e0d050d0507090b040f080c09071403040c0803120a0e1c0c0606030204020d0c020d081003020409051908090f0411120c19030b010f050309 77
    0x1980c480045d070b00d401f042c071150401c07095002540082d402c3d20003850644c200c91801c081030f50402c507086003140c221140000555200c000e10201c9a0340103c19034420071001000811079540b654002c4030100310a03031100b0b0741d1100101e0f02107680c0003840409400d0340c640c10202e4911420002c100400c558013501c20300f0101e1180072800208008010083d540b00d0b000f0081302e200180c0d00c1300c040c2d256500000d0b802074012034203014032101c0b01440c010f00840401d0140140107001c2074254424012912824440603c050803407107000b00000c0703401000003503800820840d00c1c3c0c107080c01c0082c01360a10fa134102006020b8005111203580c014155503010b15540103101486605507030a00008102e403801c2035038580b09014860b48009048a00e44a40314401d518103501d031800401403040342c0a15074041c5204070300740040030340b01e001300c0da082e10782070101c180d86002192241070b001c1c0070311711880c4a9100315004901d408002c26800d50803607088202d00b070703031a4621310494000c111414001501e888940390 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 233464487 1250 233463237 233463277
    0x15040513020f03030c0703050d080a0c2a0206030907210506010e0a02070b10030302060702010b330f0301180c201c031b0201020f121506030901020310050303 69
    0x410700c4442c2681052014040301d00d000e507881c40700f901d80a0300307a00803500303a40000384101040c1d6008104540100b0720f103000340f003040170442c4003404c003480c0004000040c90b98540c0d01c40d5071041340c01001e0801070f00906480d03a00e080c00034400351101d41501031903001480e0429801c000c0c50115421a000527040409420164208091500b1000001c1c09071902e5540a04c605004681e2150102c0e005200030344400103d60310b0b40c9000380c00c000e0300401d01010369243c80151105621000b401003480114080c202c140c58640014000b032a080c005d44844041c0e03008140940e00b6030850340150f059172043d50144807180b031054070b400f080c1e0b000d440c1c48400060301181500d20a030403101c1101400e01161080d58000c142441d0f0030002c1034030030100c43c1d000030745071403202c42c07005a880503001211112348029440c0c140803416851a038402d01d00c41d4418090b4540000e19000340e0620130140040000f042140c4d40c0c2000540b46021350410345c0c800c0c10403d806c8a0001e020710f00001101c3d0b070f440310031500366400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 233465737 1250 233464487 233464489
    0x905030f18330703050f0a02030d050906010503190203011d0708010e03090a0501081305011b08090105061f02010204050901180c0903020913060905190308010b09220902030a0303051504051302 84
    0x150f00040c10071003e1143c20b0028059071071414018180019060303001303503120303265411041c0540380064120346240e00042c0040c8680c0c1c50100b4000c00c0d0141500700290590424800300c0c9c0100001c02190190001c00080003a41c420045200030841e03545030000d01c00f17030500c421070503164410145015480311100004200c45d5008800791680522051030300074882d60240c54050a6541c2142100800083c00104c170490340e802c00c8400e81c2000c0d41600030803081c600f000104503501072000d41900c88076203000341d03400340707900c02d4044030050480504041240d5a56400b42885040111860b032286814501711482d45031280090200702c907002491800325840e40314481d84044502d050648045480e840314001091003000145210048401110300124203814028000d52068000c108c00b55410044ae07001030f51122103c4000440844003440e9412140004000406140800a41500910280d80281909507014034480c10402c0c8151244a610704100b1040340e000719414400e8078103450140d009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 233466987 1250 233465737 233465839
    0x10815011410021c0206070323011a16080405040f0209030c060a020a20090f0103030f0e010c140618030a0207030f05011d01020c070501030e0c040905030f18 69
    0xc04100d0f401641c0046503c2040d451610080f100060056880007051041040c0c0c944510b036021400c141c0507106403003501070b26800405061040c412000f003814004030140580e041151083c055101051451464a2514280c80e801c03134811244100d203040f210340c039034206500889419510007070291504440720030400541ea0003220202d4110b1055842940020b1904c5203008030b00390300da45846483c02070203410080c075800700915954843c5031080040000035005071001410303030400e09101c0800d11035180100d03182805407074090803119450484e50200c101c0864054018000c19902c21441c507618003c40e550b9100e40c1c0500700c0180e001140400c04980015000d50fa409d103d5030010134030980010840c8880c00410b000401603950028800c4050700007000303400e0007000700382414002c0f114011101600c07820501032040c01f46444803000d2007000710a00890f1801c40c003105486842d007500a00c0e17550803904015000e0702407a0640c0248603680c0310843e002030840018140701101034010805089 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 233468237 1250 233466987 233467009
    0xc090a0513150e010e07141203030a05090a0c0311040c0216030f0507090c090e0106140f090a0308162307031709040903050910030b0a06030c14120108150114 69
    0x2c15560780e9902101c81000c01c1c0607545520a54400800005060980d42014051402d100610400a031010000d1900d8040300b42c036440b481c640d0300080c4c1541d84510240c100740c0810310044c15806024030201c01c0050032103c1c0704a4203801d9401300500c028000090b6526908403200480c00782c0070350020000507030000c010044491003081034071089551081c0c80826140e03034281d881c0c0810031070300e400d2110fa030740100c2490061909280450200341084516a140e10071503503a00c024060020300303580d0719203a07000c105000715842000c01e541c80c403c00412a0a1104004040b02d080e40b0250740642c841d0311041d40c106802d02914040c20035607280d41e841d00000304140d503204524003420300000340155030324400e104d145da0080e01c41c5565090a00c0801c120500003c0c1944145841c00c0016041c54a466480c0340c1903940701d04000404035180d0000340d5150480a051903844080001c00d80801c1e11080401ca040701d00301000c81d103100c0906030207003c000c1c03070074000c0381c443c003034007123050b82c202c0ca0000c804103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 233469487 1250 233468237 233468273
    0xe0d0303020904050903030f0903090a0302041a0a03060b04110f0a0309050f0604050709110c0715050d1d0106050102120904150e041b061107050607060b0d050c090a0513 74
    0x140b901001d0400f20301034401c22a0f10415a420100c00c00045134000c078801036020740070502851a100c108000a082c1c0081400042e004540d2821041e0b1021550f440004180c90300518482d4029a00e1030280040c2210382c08941c003950a2040f040c0368400c3c2142940e11030000801c0d110b0a211885c1c80440051490103410f868038417510380c08100580c010b00420780103a00580181102d50309101074001903135240200c541c1100020070602d0158031020400205403240e00310050300c180100881210f0742e000b03500000403260f1030300080a4903060004405e4814030706c0000240100c90362070f4016a03d649a0704034025a858041006180c90325050340424020b03504000303141c0010391036418000c880e207002c43d803c58940c81c4800b00301da140200c07500d41100400061400c1000540300120050b100c0c8110301c0f480340510700c0401d80c042000b031542c0002014220203040301261140c1410503541d0b0b48050440c041c05200940040b9011a0441c01441d116108560200340081c006699820384003036828616 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 233470737 1250 233469487 233469491
    0x40302091902040e180d0e1c061d0307050705060a090909030504030609050c310f020415021f1b11010f150509010828081e0a0e030a02010e0d0303 64
    0x2203042c048140c0440c1c0968405c030b1070781c088030544203081e500e403580c051006c07001d1044003044613119035204540f0810035120204000c64442840c41c050018012408000740451507000d2008000c03680000500360360f5000d00d0031030301215911002c0c001c4501c00d0803640c5000510485040c003040c0e00940221000920030310300031f46441d0303407a103500c0c040b605580c60444103500b0803100400b45103010246510207504e010303c2c9510450348024410a40c50f40801d031013909603281c140d0164a600e095041d10700a003901d59201c011341c0300c1c0120094950010112105010040c01c2c0300444c10740e1a4400c2407002c0c0300d2003640b040104a5100190385480b00314031044690740d2a440301c607022421602504c4207041d54000c0b403d807501d040404008803103005811552044d40164039201021103016920300c1c00221104a80c0010805804e10158501c25807001c2000843c80728100c510703a03400140180307442010f90340d0301450650180201034981c091000c1c0a40000c0e04142c040400d454a25007a01d000e034403900340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 233471987 1250 233470737 233470739
    0x7030203070b01060309201f020106030c0909050706030c0e0904080d06080f0d020a231c0e0a05030a12080a15080601031101090e0403051e030901050907050604030209190204 76
    0x240142c4060244c01070000251240449400c12001c0e000d007180d084103400b10324081d6010700b000705000541c8500e02003040b004100303203214414002c1d0b0107a07000e141c00c0843c0b000c19541725080007014040c01d036421909880703507071030001d00103201348250820610300c0e41d80c182c00f030f1914600b002032401010b40249d07800a41040003154030b03502072003290001c3c0004406000007240e440300143c100118694428107541080400c0400a13503000b80c030b10240ea22034960600210300b01c2c07a055103090b10b0301c2e105088108603400d14100040e0044804482d00c5012a100c4001640362002d03d9100d02c8007e4000309410540048180c491b4043c00c022070303100e150181d00054194a1511188031801958031100c806e401071001402400314444016102c0701080c200701e144640341c05040c0c0e981440060001e01003003008508644402c14075584941c000098200380754480c185165407031700804041d1248070b224490300000103528142041580d04030f0b50000c20800042d52190303849840c4070f0385250048010b543c2044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 233473237 1250 233471987 233471993
    0x6020f0307031d0c010c02090406060e04060b0a05012606240702030606041808030405121908060909030a050d020c01050115030605030106050f130b1c0308010e06030607050703020307 80
    0x1a501c00d4049a80106030042044407070042c400c80c03540c418103240c0201494100c2c40e6040051044003503415501d0005035a45c07403c0100060583c2e400014603862004144020301a580c1c10070881c5031000c8440b4000d540d035a5005451040051040380114134803030144a001c2503c4110003903101d03502030011500102c0d071041080b524950000c19515603200802c0110030350404100d16540b1507800e0382c0c10000001404600504d02042c100c006041c44000000102000f44c28402c45d0317181c122601403135403100c20804c17104c1554182000c00800052407900000c0240c6007480c0c1d81b9028844c00c1015621741102c03503108075506e62020207880d844035000c20072406000d20034410b140c002d214440008c03001d81540c51009058981c207511882c4668180a028030030307540c403082c0c120822138085800c2403c0143c0010541d005d00144810698054070a258042010114161080d8514840d65416066030788036403050050000c02e40d01c0c26099480309000615150080e0020a00d09010b801224180304481d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 233474487 1250 233473237 233473267
    0xf0f050a090b0c1b0d170f07080f0415020c0108061c0203032206090f050904031101090605062107060f05070b160e0303070f06321e0405030d02070602 66
    0x20b0f454050b030754000c008513002c074400688503400800040301d40034141505034503070441007100c010401243c0380000400c9140005400122601198000d03d07050700c42c081000b6a0350303d0380092041c4140103000d401200301040c40815200d04200c0161a8840f160b15002c0500440451101c900202c01144004180150707400300b000e001c1c010800340e6803803401c002e0b41005021280710790703014409010b8076440c20b102e0545603140c0c070015200251007070103259a441c241203443c404030000c1100c00794a05030141c81417180c542c001d244281001c1e034540f00f1246400d041d1020b002260901103030700c2d030070900703042c000c1c0380c800c4c80c06060714400c13454600d0901009440d1409441d0007039408130310752744a040c2040006c2d9040003420444e0b02d011009076081108a440314815801d01d100000e15040e42e61280038007641c4140b1003101203a1280c000f034000e0b0b240b0322180e1514000d060300c980880c1142e03030344103030992445c0c030840c07a1040e03a01c080a1030500018082c1d00d406500034070f0044842640901a00d89504441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 233475737 1250 233474487 233474497
    0x605060c03030105011e08150402070f060b010905060f030103080703030e07090501030b010f14040e1009030c060b040501290412080703090b040605041715040f050705010f0f050a090b 80
    0x180141d65a0751501001411242e08003600250003c2048410b405250f08003040d20ba22040120040b28080582e0300014000d02c5902e8004040c8842030100c01d0a02035142d102d94003106080c0c0310700040d01c2c1c45a082107242e00a007000b0b03000c0a01c0810051000480c00701c041c1201c0380c0709040100724901040c40c0d0346e05240700707500b200c0c558560b0782004000380007071a0070050050440c8005410034a00300074000b0464a0010342150040d510798841c0200000101304010004100d65010007103612540340c010300d00402090140c61050402940704628035013445168101e613001004244440a41e8601d03c81060603120070584c0c0440610000512a1500e01c44000c100e03c9079901c2a0354080900e0b0180c04070455400c01026400184020300130980c005081750180e5088108041400224480030340c90a500d405a1003649503500040c4410080b44161031001ea91092040d600980d4071500111285400750b040c0300009444da012131110b143c003403002401001003030f16002c0d200903212507401d2607a9000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 233476987 1250 233475737 233475757
    0x90b07080d0f020301030807030318021f110f010e0c030c06090d0c08030a0504080d091a0d2702150310090908090a030b10080a0b0c031e04030c021309022101060506 72
    0x40c680e003055450f128028413400c04404410bc62915600819010b10045c64030b04070508d40c04080c1c048003070040391140c0180c4250342c111210b60744070300d4031705001c0d010720206410300c1e100d442c4280c04c1d05d240100c2c0f011403c01000e4040c3d41040e004504112a514140a00341e03003610f508140030a20800500051810825a44031a640c403480c25000904c0c00201d070119008204805805004c0528255541c40816018204582d1079180c80c2d0408801012410945542440642d09556001d0510003050100e907000b1510000150b100302621101444111400b07070b1503548504003406010650390060b022203008001203424074260300c003c11450b1169410a035494000502006411105c09403580041c0076980050044042551f0300c00400482c09014008000d001000089184410b050300400e50314100b402d8191a00380380c100a0203464110754140d018000006000e02e05051900940ca0441e6000d401445035900e0029401004081c0307050443d495502c66100140c02d0b42d0f040013614040300c1d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 233478237 1250 233476987 233477003
    0x20f190804290a0c11012f0309070e07050c0a03091a0f07120c050a080705060c03061e0103020405150903010e0a120305070311121006090b07080d0f02030103 69
    0x1c01d400d103601242c2d2607800045440e450890345020000024105a41007140e034680030445050040c400c0c0e41c5600d00d01e190100a6281c01000401d8401c4860410600c0c1c0e10001540001d84211462040324401120003100715404014100640458a03200d140d00c4941c0e441c0081c100754a44c0a11400d1150203042900024003010003071165013040b001844298079811119880c1400b0034402c060075014900c805401d1078041203800801601403204200d003035500a041d204d0b40c0c072162910081eaa049104151400d114400004003414103c0d000c40c2d015580041c00024400d4031f00c0f04a0080d2001140381c0d07810903400b03110000e0039840e00d00720450400700c0c8501068131820114241421200300340078000055000d100e120001c2080282000c2c0c40214625020800c2c0c1c2d80c500041e009062200b41c0310011101c00100e10b2190345049402501803580f5042951400396035031000c8600c00000e015400390403030b08001c0b804c000303a039007001000059401ea6000c5010300240c0e100c0d03000c82c1c0090b403056545031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 233479487 1250 233478237 233478241
    0x405070305060906100c020105090a0b070c3b060114040807081903050909040602131d13050304260a0303020a020d02151302030c100f0315050310020f1908 68
    0xf20700b080c0642c0d80030304142c65440300644100300003045c2c4031107180d003c2d0502c072000a50010790f4482c0b082c0400070705005400665240840d180010414049214455050102c1d140001a000f4540890380c2e41103200c4282d08030742c0112508080396440c01a140c1410700143d640c50788030740420540a8001040c4140241c04400d10f043c20725818201d5240342465822075400740d12000035040702c00e64180407000d56001c1c3d0195a00d18040c2e00920548802150038600c1d081c0000300f0a0048038942c006441004680f2215103404038005052030110703500506d5500144002d01c221024002c40441030b601000002e2402d40220b0361250414155000503000660006070ba003c1b0142c04016a038100940d44c40148134410000b01d40080508001c0c000d00d519450640c11013056540c20402003c0b021002070600c0780c50f41e00100041c0c4402108481c0781e010030b08001012070114a0318288504846015021b0200e03801010583c000960162860078642d1405003c01841e24021200744040240305da00c40242034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 233480737 1250 233479487 233479489
    0x50d090c032006040e0c071a09030304020a0e131e1704030b0115050703031a03030d0615020a08070209090f060a0f050c09030a0f11180114040504020904031805040507030506 76
    0x5020034044980503da040004015014640007016070000801194a031038003c145000010480c0303640310303500d41c0441001401000b05012000314000c510882c0c03401b48503a07a91690090180c411076030083d641c80e41d100c0360008100605c084041c1141c0038425100c894850799205800503040e071028903403c1a0125081c405c0015244607180500325021032282d06441054000340f5502c81c05100400305901c5050030052141c0c40d12008035610f074001c0541c0c2c0c0ba402804903120017004d86101c0c0820f581030003454440c045001240c071540032034201404914001c016020300040a0019128201c503100780d03980c04418900500c0000e01640e0f0b0703421b01050845010913914180c580c044e1401d5499101003054561a6400141260f025503220440c0201d420244c01c25030001940c0c246420f8110b8040c000100b54560010103080c140d420b40d4401f19801030001084c002214001c5400070741240180f404580424003901d00042d04201800495001a4990011a09480c01941d1000103e52a10280021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 233481987 1250 233480737 233480783
    0x2040f180b0f06040b09070f0210050c0a0f030606090e04020d06061e05090c07140705060309010e10020a05070813120602121501090902090a030c0807050112020702030c01050d090c03 80
    0x80f41044a080c0008042d100c00070700c00440250558041c03240300a0001a030364024031240071003180b010010803082c40d00c2140c0500703aa2240b60f030300c000103284002d2410514001d00c110015500345640355a41c40342010800741651034042d00990b40184040300810004031a406100058540d03411898902240341c00100311240e2181c000c00d1240c229902000742c54100b4074280d0396075941000c160808a200003c04d10700b0009181c002d150400800010014501030541281c207a0781e86d1101181c0903840c0d07905c0c2c0d81d01240030380707914500011401c114000124143c02e001d41340c101441040b0b40012542d50a000c010100c002c4001c684082e000710f075000e946504000c807aa0b001107500b11541c506d100d0480006c01c80303040380c010b0300b01043e4041564525030302c81a02c150051503001c98038100071070325030610b1a95880d0340d1041c54002040c40d0078a00303040c1036500076a6002e5502800528040e402140151965003040901c40040d070b641c0d0348010041070900c800340d8000c40c01407524141c0b04460b0409890 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 233483237 1250 233481987 233481991
    0x1303140106051804080703080c0c01060303080601023a050c07060306030c061b060c0219080c0f16060503040312020711030c1206060d020d0507030b0a180203030702040f180b0f 77
    0x10003e2040010040410b892a01320740c10300c2e9140ca0408105c2c0d07104610b500480c00744d180100813640ca0844003000709a040566207010790700c26009c4803080f000e480c454803400041507a0000400100581c41c00400410341100c454021050500508210725030404a02c1c15555a210b1000651594000c10074407042d00f0a040190400e03141c40203450b5000318141c8104145400001e04840c0c0e00c0303107800d842610a21075805510700880240040300c2c4c850622001a822507030301041180100010320f500c0f05800900103001403040c02078078001a00d450415182508001d006070240400103455074104840c910040041030f124012071b411f5118008185407070080304c111001c0c003c0700c0613542d24503120b8000800c141e10200440b040d9141c0c24880c8003203038900c145410000c140d80b00c0c800d000b1003000031a0349401d2081001071010003040c070702000e001581090518019400d90401c00c0f04401605042e0026541d416003840d0128007200c040001e0a080e01c4040c0c029552440c0000c144100b03801d803003400715 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 233484487 1250 233483237 233483269
    0x170a0608100c1209081b01020c1f050702070e07031109041b0306090203150402070507080d0203030a15120b060f10050403020102010b0f060f030717010f060e150f130314010605 77
    0x20346244d07a4039102d951159440c200404d00441840201c5520250121540402460103450240d8008051313407100d03c8100d00c0c261003072420800040c10a6100051800844001c225050712903102c44c0d5040d40201800d083c2c95500301c00410070b040b003680300c9001d880d03002040c0c1d09111001003d001c4000307040b2021034220546850041040c44043c081400c0c5900000004850042c1d40c0e414500e8046d180a0303c6074048503403400342120080720740e0740101c00f0394840c5640c00414004401c02003001d5143d100c0303034080ca030001030b094014040840d50f40700403507501140192420100310111000580c800e000c14031b4000000d540001d080c01156828000c0d0040d1050030380e00c1152400e1110002612402240d40d0141844004800034a580c1e100d800da5501c82d5400c5c6644c600c1c5961500c4141c2903490080c001c0201040f2811844a02410310044c00400144d0f018611410030301c0790041c0c100030340d021903980d2051040e0280301001150916002c006c2c100104000040d60528080920210340680d43c0c0c66 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 233485737 1250 233484487 233484491
    0x20030615010801141807080129070303020a0323070908120901080402212d0604110607020604080d090803040b040b0a0327060f020901170a0608100c12 66
    0x200003990304010030702e06641c69000c20042c806030f080042000f0344111402103034600900f070248940150001071144c1030b64190f040e101144800150700c0c0720840300d00b0500c0d40036190208030b0800400d20035405002c2d403040764a00031800f2464031200a180114100880d00c02400b40c200f401511600320003100300070814640a00642e444000f9002c44500603400034906000e072100c001021035944c506002038003a00607121180701e0011031340107681c6819001c42e01d4042011400064036008288001d0001c0018810003413030180c2d1103594200111200342c0303100b80c20410511100005a40b00e5020b40081c1000c2802400905081d40d0000d0a1100030b41c0728482c50780080105000c540d03140402c8909898200d050265900302c806001c600800003d00c1045d00791002600381030801c05440100e08401c0d0082206126010500f80c0300c000b0ae00c11401c00034040740c0305d1410010301003403a01200342d010b080100e00160055a07140094148808079132040c001e6507a0740444000c035078111814800c4210b0300107007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 233486987 1250 233485737 233485771
    0xf010306050d060507180f0905071d0d03050d1a04060b030903040e07020705040e0f070e011202040e01020c01020c1f021c090f050f07050909010c0801060c0f200306 72
    0x724000428442d0060046a10f541c00203a015026155400340d24003004107040c116070382c80c01e00040e001918082c96900504103004100040c3c481d40d0702c0514100e070015924017580104080000540c02c11600b02c00303210060040300d070f00852a01c5042e0704244010b1110201c51240810402101c00e40c2d00a1514607201f030061010414000050341d082e074902c00d03034460341ca8680840c03d0703240c560142d00c41c0d0780c0035090075a01080c455009c500c0d091300c150084120351240c1d8440300c1c44400c9203004d000306100c0d8400c0e0300c010000340c41c00d5080b08080d51f5401d0700041c40c4c01c40071050345003a42e000c0b0707102049607031005c03001c10600c40c441410f029116084940440c104030b140e04080c01452000b6804020054852410300d06120040c240344003c254404c080f2140a0441d000301529884948181c901c01c1001c1c1001500c81d1506025480c00c0501c10799409009a0170124196000440041e068450006002c08500054040540f02100c3d0b002c030007550079610001010980f030000d008010349444504a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 233488237 1250 233486987 233486989
    0x1050a030f1e020a030303020a0e09010302011e090332030702060315032a1309080f130306020301090516032f0d140114150403080315120c0f01030605 66
    0xc564400d69440080a02d00141042c52444400b03820304000c0e6202003080b400204143c2c055000341943c180f507032103500846910071308115400700c0c24880607020039101000509850103065184542d204542816039070144c817515000c000cad06101400700c442800c01c00e9587c401c103010140328100c2d40c040b48021454426a6808900f441c04058115104100030340c0700300e070144c1e0741417102d03111104551503140c000100d101d0340b202c2c1e49120320038114012403407000d102e42d4140043c060010000e401041c281c0c5011640100042941d0104405a4600e0100343f0044001811400190300030725070302a020500d41864110b1140701d40c1c445000d03d00307040c600423241c1801945030041100c0f14100000c43c18285040340440003551140c00c0070b031600c2c00d103424441c800e203107010420141a02c0c00801c0d501c1040c0011024003c0e020038480c804c07400c80b039040c0310410018064070000c5600110103071505d18280c80000c00b08689154810740c501682d00801484c6a00c0c0c1841045100e0010091a0034000b60b4900301c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 233489487 1250 233488237 233488253
    0x1905030c16060c120e03060a06050f060901021209041d03070201030f0603050c01030e01021c091e150209010207050409030e18100605090d0b250807090b0d0e010501061701050a03 78
    0x420000c03c40a10360b504c20b210140a850040145032001e010f131045841d00300c4402008008a010b0503208114455000c0c11608015050762024603040e0010404180c140c0d201c0401508001492940b05480300b072483c200e1054200b152200000860056440300454030001d01650b0702c8006100740c1c61714024040021410006024140c2d080070300703001036844070300f04610740a0f00c9440400c03504a403040250f0018894039511080d480381c0142042200c1183d4049a10714000c00000040e015600381200204042c06580c008c014417001401159812a601c8012409907081041c0680100348442038002c8141001d003213142c0c0c43d451900d025110ba140030504000c09001ca07008000400a0115041c000740d10b90038408600250003041112041c546125250184030281d0311311481001403000c200e120a000c0c8040c64010038a0340c07181c040c91800c00c0010a0245c01c0780c001c01001c151144800740402c0028400c1c2c6020f40415a10f5a60203100d0298503034003d20183c0c00180543c41d2400108040780d40c1e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 233490737 1250 233489487 233489507
    0x20a020d0b070e0a12170f030103030f11063103080a020a0504030501020310061206050102070b0903160905150316030204021b060a09031205040f03030e1905030c1606 73
    0x1c502010040c0e2610401280c007206000d00403a089850600c3c040398549110211800c0305101e1700701d0094031241d1404550103801800b41480d511441800188000390240c0741c00100700c4014500f13040e020300c0040900f4600181a21440c4000d902c03840c0c481d03604a0301314510400d83d0061003d034a071a8610b43d50092000c24010310a02d6460b60100d0040304041c8548111030080d90010002d40d10ba09108804d969004194424a0b021402c051500d0b90b100300310f07008410031a00143c01500d00c45150000004060780304205041e0f05001d88a202c0c0c1c49480c10b09020409403511400018080c5044140200b40140c1000c0440c0b0980c02072100045041240107540b023941d5040c0ca0160b00d030282c61103104012920481030505c00c1c0658820031564903000c2e070156510078020794403001e0051440d2112412508190342c060324250303aa02e81d4601081c082e401c02d0380c40142503021190f003101000e41286200c480040215900d41000454000e020410400702520311800141500803521f0484058150050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 233491987 1250 233490737 233490743
    0x10b03060108240a1409010e01030b0c090103021b010b100207240201060b03070503071b051908160c0f08070f1a0909010909050f060c070f0f021804030906020a020d 72
    0x10360306103401e20f039524032490103518601030b0414841c56294000c0140114440c02100c0c020707041d12000181008161905504030390300f0087c411081e03111442c1c0c1003031a0f404aa44d030350500d038080000300c62080e600c400074001116501d00004203d03541604106070600b610340e07114119400b103070091000c411090306100000c2c0140300c070710101d81860782c41640503090607030000c540da80010042020450b0004011032080400c0d607294004141207041c5041d4000c40d10b0f102400704c2d4044900c19450850001c00c0c401224014168541404100d050111a400c01080e04451a0b00e00e60810080102020480801b5004c1c403400341507207908146c001c1250803000d02c103490300780c3e500140c0540108401c00844000c01809084000550707150a0ba00300907080e001c00481c1d40d4440c1c030103100c8128401003901c0e8003400a2000d12031500c4210380341c124081491b4001524103d0f40000401c0c0140e90b80d542c0814203021850b00c50281c3d1600307060150000d105540b0000c01e54000003138010040c0d840c1080703995141d0b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 233493237 1250 233491987 233492011
    0x6110f0a030b0d08040602150a020f04060e0a0f15031803170c1225021209010e03030c060112020a0806060306040204090503190504051504030f020904030c06050f0a05010b03060108 79
    0x900c100000383d481d038101c2405092035600003408034040c0da01207900d0800040200088050303032541044102203204840c00513010b24410300003808031364844e11365900c440030000d05400d400c03511254004840380c0c143d030040c1048900140305d080680d0301405100c900000c5082240d82d6145551000b81130302c0c0114080c1031a600c281b030009408889228166800c011a0a64602d01c606d01164902c00541c4d0409500e8002c01303001c0d100b4100c0510001e14080d90394001072820b424942d6a00c0155091700b03003006802d5040c0420b000d2078020360030800c0014000e2002e20032600c4040141d00502c40194076680001005070440e0081000c02d40b400118103402c989d064400080c07080150134241c0c107600400e42000701002c40d6400000380d003644200504152902165160042e1002900c03100c040d11483c03000902d40d095041c8d400c009407034944403103a4424000c0c101030020bc003641e40c602c021513604aa0300c1911414000500a01905503c101405044904081459810001d0000e4110480180140e140300c13 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 233494487 1250 233493237 233493251
    0x2130e04020102100903080f0a0e07060302030601140309100b06280c0516080f0d09090e03070507030b0415051e060a05030304120605150a0303111501080a06110f0a03 73
    0x64420011307401c038001404070802c1910280d15000301240000d64000b20040a040c1c0410002a040d21903440002203c200810502e85000380070f402a410003800c0c90706001c0001b9164103000c51450003944650844405012442200001c600444800d624442d002e0b000c1801041d80c40765031070075844050003200203240044015044121241c800d00400200f1030701074a4034000c540511088000280c0d0000340c2980c803040311204446588045000d0074600041c1981c40400100f1000d0780070009000d0702c0d009582c0b9058564840b545040425401107d4148206c0704000c02d21840c07200f20811203240034014459420421403102d0504005202901d040c00c0790f0000c10030640d01d103204440201f501401b901c1d03c0c0c603910000ca02d40b909421105444403821b10300062446594135a0001c2502c40081070f001500381592811541d800c1103024450b0b03a8450092041079020001d119140248003400003045030a0480c5000380650344840c1800c00d90000c140311044200a80f1030543d01c81001754640080e940c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 233495737 1250 233494487 233494489
    0x8150402041e0c110d02120d090b01080d0908010203070c0b061801140a0e011a1b0102031005040b0102060403140a05040b0c0703141507110a020a080601140402130e0402 74
    0x20300c86519041040e56820280d00e40904242e0011510103503540c035203046494107844c0c00d90b10340030680400c10040e000820300080b8540d8010143c041c160086030f00040941982d52a80c550380030a030041b1000e988500d449000c810350080d408400b410f00c0710000d43c212309010002034071400c02400e00508900f42d03c40058140d48909030841c81e59501d000701d040055a498650341100e500c0070403000d0003003101040100c0c1c03409040d42c0b000e0485503010480d078012400708103000e03e00e800c0302c2c1c02203017000001c01c10b013108680d0900203103000301c1000c0310b1000402d150ac020401207071a00000a41590804410800840e4000114102c210fa0000b50b41d561030800308000c45251045400034203c00700c1c0880d182d4200000003892109030f902c01c1102c00d0301107680f0f81d4420b0703503a96040344076403108403024000f4800c107100c0c0c90380301603035035070300342110058880e95000402004c031a0308840c80c2c982c80540100b000003008100030687d4401614214030f4101d0315000030303032007103050300545540070380e40c801040071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 233496987 1250 233495737 233495741
    0x509040302010b040908270604050103020a02071703030a0f14010b0903070801060909110a030809042a1805010306080c040c140409020306011706012c060a0503011503060815040204 79
    0x21643c3c01402005188103070311380700032190000c01500840300d0408000c039000715032070914038402090061580e0b041600e00700044000e503100c1c81c40541180192140000e10328405110310030f40c90b00c1b1b0701c09141c0760b140402c520070407980007500340200c9604242ca04a004850303100e201d41500da840155036a20010200480d02e01501c0b540311710001d6281c00f00001e0400703e240c4c000c25105108054402031441034004200340183e41d0f001c06007943c8010041c2c08501d1401358406000300c0949100800740c105400c1c40141e05a4104548101040c0440300440918085015402c0940000d08003040601d01702566a1780d1490209000750203642e4450340034494034011068041e000344000801551241c03203c0c18103010350010b1711110b000c00c560403840070760100505040b52080e02d0603500d4600d21440000200b43c01c4807814100445526060f55012454031650028110164507881d040d030b5a513d0702810041107100d88055a0070145017220503c000000415420840d403c40d05410700603840764000030300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 233498237 1250 233496987 233497001
    0xc1d0604080f0601030c09020319090f020607060b030601080106080d11030d05010b0a08090312160905030d09031e050303180c030a030e090708040c0b25030e0a0f0e01050904030201 79
    0x4070501c1079512500c0324a200088490503a442250145181079070b8001920684c00305880444c9500e00040d0100541060780d40281c0e100c5001310041d00024020381c01290040d03025481c04d0b07441c6e81d25180e0030a45030504008641c01001c0300f800810066140604030b0b61911100a070304001c1241c45009400b8005040082ea2880c0c08140801c1129594911504000f032b80041c4200010a02c1e030000508089008010b03156840302240101d90700b9a0b515200c8800101c80b05602402c0c8130824002103034039202041402d41000550b240c40b8555800e41c10305600404000004100580078810103400282010080d2a00000c980907040c0c40d0796080a01681820045031344141c00d071288142041c02d0541c0800c01e01c01c0280241c50812040d19403140c100c0f0321400850f0090091101b40008101d065510402004031015040144100c1059501c01c40d64004803100309400158803141031200e2882d0042100b0002c003031861280c400540380164030320301280705110340341c0b04000880010701414006e400280b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 233499487 1250 233498237 233498249
    0x6060c030d1103040c06030c0206040f031809060f0e010b070b06011403070804030e0f0d1506030c03050105090d0f021507090302180703060510020a2009090106090506040c1d0604 78
    0x7008a600c005096800d9030404c079415101c5040f0070354000f41c02c40c080d00c11904003000e2540030b407809503260b4a840c00c00c21954401101005160707074148001602c54955000500440c40020880a16050030704d41c18101c1904421080b80002d00100042440c0804032101280d1052001104c0d17620140141c915400d80081d010780c504002041107000390340048518400d070b20a45569040304102000d21040a10304101d441d0446096140c041c0131900142000c80114140e94021a4694680d5102d00c040765090348200c07040da45400a000390120305021064501105d45041441d00840000096555615560fa06100010180400c40141c0b164580f0b1000e581c003d4003c140b050400040c83c1010340c1d0443d4442c00191415502050384d26000c4081d00104542d076000b070609a14035250002d81012402550034030101040041800341c41c2c42d0311540c801c9102000000d00245041d00241c1520300041480d48500d00c0c100c0700d420442c0c1c000f004ca004620081b0500c8440c00d0040002c142e13103124580100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 233500737 1250 233499487 233499491
    0x2042d05120a030215070c03080c0c011104080c1507080904090f03170105270c0d06030302030a0311030c04090e01150807061107150f03240e1e06060c030d 68
    0x51032900304002070102c0558865422551104034540000840c40019035070280001c1c14001a40b01207446603030026040365110760103501e0100086021421110030034070f2801c40ca003002c6010010342c0c40510a03402048000c0c1e403072035a000d8000001480c9485040001407423808049143da034680c03201d900c10700c011075100e4199450b151440c00c02614101d86800107030f54858044002107040d040c00f10040f9400700c42050b07030190302c4d2504010030b00c80c140c001b40b516010305000e100030620300c600f40c0108002113009801850351100401c000405403003060049404c0140c00b0020b1210100140f01114207c4006900000c0e012040700680703400b47c0241004c408c00e0460380300d008607054002040d81412a103072511130140074800f40c1c100e59260000e82c4603e64a400086076110301607070140c090360010341c406123400141d408181925810707954407440c850040044000e410301c91018510305940e08503a0004502089070310f0001200f10709080201040c3c090b50003c51000801c210802c2030300d04551410100b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 233501987 1250 233500737 233500759
    0x1606180602031f140d0302010b0303040609031a060607060c200d120b0906010309020a1a090f121b06040f031109072a0c090f050a0f02042d05 62
    0x21240182d00152110802c103c04500701243c031030740000002080300c80d2184a2803a040400c41080824030201c10f040e4155502c0d02d00c0241c039540c0500060000d040f072511500701d59801e5040000d617800881c1c0040e22401c03800418001503944020a46141c1c3e0350015001c03500c40300504046442c500b28000c0004c00c0c0c0d41010403001c01580c040f881c0002c002203541c03031500c441d0001d050042540c3c4002c2c06260464480d401090055200780c000080300c5001a199025503591000b001210302c488100d8850318407404200a4030501d0040c19031042001e0072550038541e401d80c00c803115240c565281360000781d403100d0a1690001d88030141038070003d050300c640c0c40300f81507543d040503c01c0000d0781c04018401c0d80c040c0700007600c032401400e04005041801400290485001010300c06a100c0300f4401d6030020b03445a00020a00ca490207400c4000d040d0682c08259410441155404c2e41d84d654043d1311841c0c0140414007445000364034000000556450302c00905002d084060400c60303071a040142c20540840c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 233503237 1250 233501987 233501993
    0x70b1c0c1e021609050a0e030d09020906011707030b0f030f10051803071212020406020d1202180603061f180506030105013507020d0221160618 63
    0x7000c412905555520244600c0381c841d0300300e071601c0118010324200038036804144000003e941c412070b0301c00310072400001e950201002d054515000b500340302007181d46070a04001141028a01e02d9007059081c01c3c07400320306846640b20704404034001c2540d4105a07580c82e241c4403035038035131002170b142c100c01500f0384800740300512006071100d81d04400b06564a08160200b088021200d00c0d00d4400c641d068040c50810b2030f00c0c1d86071100515503081200411a07c102c0f40d0349603100d81d1000384000c3c2519001072031460352078403010740420480340c01d01904600c14071007002e1200e000319404a00311800c461a650320398034500081e08000040401c1060071100f00c003d03c14281c1c104100190040200d50b03040e014075035079810040144801d0095a00003000403c0c0e80045150458024036601040b10030310000702250888840090300484000300180c5c0000340443d5920b0301400401d4143d19082945580030300340307800a541c58031400b003003d50700e00907404041041c0151544040303921940c20f010844200c050381 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 233504487 1250 233503237 233503247
    0xf0321070507050d030c0305030a020d06180b010e010813080c01020c0105010609080c10031128030e0304030b040308060307030b0705041401020d08060609060904050f07091502070b1c0c 81
    0xc00840d040c0c46a00c20100385071402e1641d921103154150750b0322800b0281d6030b40445070340d00050301c0b43c00e07074a800380a00342a00599024100c0a0604503111010784031b5041c1c40f84007a01c0141300742e41d0503c11a02c1d00f250b103070b0341c7c0580c100b64410340c4c401e0313a00e00705546494009002d01c00d1012941c682e52010400030a244010b401c0781d41260302980e5051903150f2550035540c2c56440605200d50701400000401c0c180f40c2c02a00b02c4102010004002828a880c2d0200050695005108282c401c6c2d0b01c00c41c3c52089540502c28420368030f60000c02541484e045035281d0b100c05c1c0e4094406402c1c0324840b0b00089181c0d804000000185900410100d01e5050680000d009034000d40034003190b080d00c00d101c030006540300240102905007181e803444603d840f69801c0c80850b500069507030340c00103020400c0c80702a0312a401007500444414180d0101c5207000b20008140c00b1594101888901ca1840c0b6400c1d06940001c0c2c0c4d60613100d0315000742d40d0340e440d20b02d0601c50003210780c0346c0f040c001c41c10004070444042d004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 233505737 1250 233504487 233504497
    0x50705010911090c0408031e0c0a1a011406030103060f110d06080613030509040f0b060715060e091f0f09080c07080f07090e15180f01090b04020f0321 66
    0xf030340d50745100c0c2c5801035044040d0240c0e028210103588188418003010456000ba000101c166014013031401d00b05543c0b050800e1200d02c41601e02204a40d600001200c60b9590240108100c4000c40903045554000621503c0b042c40042c0030a504e03401042103034402ca0780000340a50540c51850350710b10391900c0c88000380c0143d121b842d109015046c001a04520140444608240c2c556034840c60304420b101004000c0c88c02150f120041641e6182710003441e00c402008101c071a0103001c40449110b054550320301a900142c0091100d0b0a03100705206001030001121703074445c0c60b6400b400d407902d8000084000142118a2040a0b15040030055000d000040008226070000101502c0c00d0715154483c05540300c0305c1c1c46a2a000d030340030b00010000e5a60682c007030700c00c0451880907505801d43c9501480c058401c02e50300042120700d100704516080310100141a030000b903800c0240805440c0713403200690f0510042000e030062040900c4c0403a00e5030103100041030300a10303662418803c01c4040c0e074400c40d5040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 233506987 1250 233505737 233505739
    0x4140f0703050601050702090402040e210c06010f0305070608041a0106110c09013503030f0601200a03120e06070807030c0201090834061e020325050705010911 70
    0x79100120f907280d4412421115140c0d0050543e0304207032030300e600344001400d034060b000380140505d47d250161005041c5401c003c5804021782c0f6030f1196400602c0c1414208103038030405620312400320410000d400414400d044403100e0070500e0051380d0700c0c14102042c2c0450f8035600000007a460000c900c1540065072103100c1c040716003ca071b0004440e0301c20301c50001c00c20700918259001a5144480c94000781e800f480c0200c18030082c8011480031000c5640c42c540080d81d5445051085004004403940e01c0301d83e8a80325900c503200c00d140d6501d9001019119042d000000e420000c0c03107480b94608002d01d0b0885a800c030500411582d080c81e003400d00070601340040d600749000904108070407103242d10500580c25950340005c0320515002c5110318107214246000d20080c210140410140340c405c1d40c00074121030759801030101186405007400f09601442c06041c14030405071041c01803203401900c42c200c41182d0702c06103191164400089905031440e0050f40c00003000356080c0400001000030418200a41c0c0308 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 233508237 1250 233506987 233506991
    0xf490c06080f10140d0b1302011e0e010c21090501110a050c0d1a0f010303031b0c140309060406030f05070503071d010c0b07110c04020306010903020f04140f0703 71
    0x40d0b080040490080c2a03a0b181403c4082e200103112030b01ca0b10403140381e003070001050060440d03219031701e01d05039071001c4603084000c800c1602c1071020b55802038142001000582d81c0d41d1000c3c012182e01500d072420058040f810003c2e8080c03110204159003040151003101140c40050a803100000205501d2050040a00041c40c1c0d0000400d00b0b170700001c1584507154480d001e04030741e201007024080c40c80c10390003040d650744514004400300148420390b00c1d4090070000c00e008825604608014065642c5030302d00c0f80c10800540c907940710309540611042d01c6a544022111105000b03100154651300800c1182640030500040015105030198000200b041d4000414400d03130352000001d07502c0340400c840b418007140c424020480c0d01040c140c00604584414100340a6007003180c3c980c0d0143c0300049a034000403860040680b00364201c1006690755070340d000c940541c550b2800200080201f4010712009025001c00501c03040710341e40b640c00841d44988854180402e51800c50007840c60480c003602c0d0740c03002c24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 233509487 1250 233508237 233508241
    0x18090518010b010f180b03090703111c020108040c0e090a0611090607030c0f051905060603010c2001020c06040305070b0a150311011b08090f490c0608 66
    0x1006000310540c402c4140c441c500d14511540c0c060f1010030500b0503002504500200106008030f0b214050741c0580c12040c001c21f8040e056190004507110b810405621800800d408907100b9480308402c0e044250303083c80e00d011179450f10300d40030443c191a5004a03000c02408810000c20110000b10b4618240c0034520900504141191510f01840303135000c2e094026208110080110740030722510300381d66110b410316002c444a00c0e201e140c14001420740140c10070303401420103014483d08005007604628118000c111007a400171001d080b48004214030740c4480c110103032254011100b035043c2c5a940b10300b01c0644a062034a03180080c40c40d481440100c0e1402ca0743e102080010700a48103040c60490058803000310682552243c04101400094190410120f0383c403405a202034003025000c503501c0740b445943ca0307014100030420703500519640309010301c414640340c40401804403050f070000203090300d000240156214025240c00089562004014850006102040000c44040307044901d02c4c5c0e2106859 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 233510737 1250 233509487 233509531
    0x10c020c19050405220f2d0b06011b0b0105010206070815040f02160b042006070b07030e031b100606170601030b13050406060b0307020304031101180905 67
    0x7014012418850081c0e507807010b0200c1e0405074072868109104a121040301507030f1907050220080402c40c12103d00c801801c48074100800440e1121404412000c0e900ca4040c081211601c10f9415482c05003100459501184559000e03484151400d0b483e440c518903070344035a0a0400c0100320a00c98280140b04480009488500c0f600a450040d00f030030200c1f240c240c12200c02c00020740840492840800c0d03080040c40034440d545042144490b1043d0001d43e40da2516081c05904145090b10b03000080320298100c150700d82d294400c80300c0c02075101c4c03010300d21919a65002c034014070344c55452050b180300008041d001420700c4050855018460381c1103400c1041079039040c0e01078070814455107000c5802c04220078242c0c0400007800f548202d042c500021b600c148a00015031000d040b000051645540310144400d001c0d0901440b80038000341c116091442c01c060000a6403031041d0300c000b0b408202010700300744003a03114060b42d000907400380240001031034441305010000c0c001502c0f140c040b40c074038680c40c810f0703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 233511987 1250 233510737 233510749
    0x207050f0a06080403050304080f0c0a060c080907050103230117060603010b060a0c030e1c0204181716020603070908150105130216050a030305012108030109091104050108010c020c 79
    0x107890081d5900020341d140e40e45c0959540c0c001030002c0324403000901c4104414a0050081c0550315034010061140341c6071414004200c504205c84e91080142c4c0e01c080007107032070000a03004202d52084c0390010703c0484582c21074041c80c0804030070a030903003040340001481000009144d4039030b03444e140c15074450b5110300041608880603022a160094402c0c09481c4840d17009a03c0743d10500c3c080e081c1501c0c0740c13140030700151030013400c10070300328040424801d40c3d019801c081c894415407035030095072115208001d803a41c8400388d6100c40d0026071408001032011820201110805016501400d1641c8904245801401130002c038002c50005108840541d4505611484103504036a03004d441e1160403005d003005c5c00003941c041000140017150148480c400901700300403524401d4000da4000030103504181041c034503d0900d0041300c480084003103030355000c038890408903411a802c0e81000075a49034a4589401c040e0514180d06900034030b000b000107803030801900300c55034031040c0d6401c1d503440c030b62881c1c10454 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 233513237 1250 233511987 233511989
    0x305151303080a090f0203151008060f01170f01050408191e120b1302070c1a0a050921070314030c0606040b0a03080c0c0112090203060708060f03010c0207050f0a 71
    0x20000b1440340c0410b030a442c0b240c0c08a00c202d401201002103007036480d004a80391140e0201100c402400d00700030000140c4000d1000000741482030090451403c0c90340c2d001a2844044c000c4006150b82c481080d00d8030ba10810203014008000300003440390746880d00b07140105070003650b055007004040003031600410f80300703100c035450068070b516162103160501281280c0d50340c204504c03460040d64031a2028a07075503c2040b0741401214904015035034540924180c000282940d0010701050080c1e520014040c42420a80b407030380c0f1452a00701d4503030191400042d0800f02002100f1001000c5010306409110049007034000d490183c150301e0702202603075070100c1d500e105143c0c2003080c82c0c12040104110b8134064000c11410900180381203035140d20b030307210882650f00c0100180156804034100800c10758021868040d00060101c00300709180858020a444900040801080100d4000040e0085d030b02c1420305150703210003400800c204070324288069600c0b0707918000c1501c14241614400514075280c100780e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 233514487 1250 233513237 233513243
    0x17090f04140a051009090f060c1806030e030d0603050a030212130302091015020304060207080a0b011502010e030409090c0506030907031425051207060813031202030103051513 77
    0x10701259100c1400707100500d80a003403500426141c5400141d002c0c00d601540b1503007030040e144000441c0c01481c0c0f40c81203502154142042c00042e0441ca0030000d84001070f00704640c03050038049400d00140d141281941704030215030650a00d480404410701c4400184458498820707021140b90640c500741c0a06035010b46060b501130062521400d10040c245140026008103500f02d0300745000e03071544054051080d11181c017000590011808210040d0f0400810004180036000742064200076214070108a005004c1c2c407031034011130480841540c1c408d61000103500c09400070381703440b2a1a41000c20240a252209580d5400c0e030100203d46440e000007202d010b0300220008150741803540d41e13009000036104101181b903000e821480d4400c0320400b068401d01d400b00d002841c542c103082004010f80c0c0c1400b01c810100310380c08403a080c0400ca410041c1e49130005110030140c2444421890110f035803016801004105074008800013040200004e035407080c0d600080d090a1081d035800070403241e115402000a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 233515737 1250 233514487 233514521
    0x1020f011407050901090306181203050615070f12120c0302031006111f060e0a05090709050910060306050708090a03020c010507060f0213090515010e060c030717090f04 74
    0x1069002c0e0003840281200f03d010304140c030300c4503581d46440e022944901009850310000d541d0400c200b108100d80100b940d502070408000604010011400303800182d59050b5890740000b507690180aa40440904056445100440f0040010000620103540300700f82000990401100b01c042c14004c2c020340e44503003111100345000c2860f019044031554050f50000f16070740168208001024000c0c070010414100800020a0381484d1210051100c000140110101490542400f50070311020600300100c85481401081940b0350841c0315003444250380c0042e86541c6804070010400401703030409845009180c03903806031540d030209095140d4041c004000d0041e0040a51440340350301074006003043e20702800001511041201c0b15104992000c5203148504410050402042c01203014940d440500c943c400840c5800b04d0001808600b200d4030154030916000c554101d00350800c0003581d0f00316400494105001880b207001102507401242d140b03014101003100c2d4800c6041c94040e15414125030011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 233516987 1250 233515737 233515741
    0x712270806060603041103032101050f0f0d060b0319020a0f06050f0a09090e06040b0c0906160807020319030909050106050a20010c1805030d0c0b090c190501020f0114 73
    0x803c4020391008008450b908542e038000d1403940c8041020303010401c0d1403403290052500740c0c000c0030300046050f48114846c0d118804110300c540c5403405824616882a02d8a6040c3c540624060010b800042c40f240d0701403145102c0c006040040324025880913000741c0340700c000c82c0c2d1a0001100c1840e006e0040388081503082149403440d2000c08010710718490b0341c4c40d04440741c684644451003a54044840b07500c4550080b01403100344203c40d00b880b50480c1244200b00d103008240320202e140c41c0030340c041d480c003c51310b44010a42405031008c12103036000e60081c2500c1880000b45400c0500d841c0c9902c06800180e00da41000c100d40c010f9118044c144c0703481c1e0b00d919003001c26000044405401c910102810200c108059000b0300307409000791b0042c103509444004021001403a4000701101d103600c0244280e120040b0140e00c0c41d0031502e5450b926420608041c140e586000b2983e181c22206220f007034220b001c00401180ca81742458040003a80c0c030903420390388040c03141101c26003a1009a01d20440740401480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 233518237 1250 233516987 233516989
    0x1c0c03050a27051e01390309080c010804030e0d0f020d1a090a030c17120106030507030f060e04110a1d0f1e060f030f01021803010c0f090b0906071227080606 69
    0x2190b403d00c00400b4000418150601d0411a280300e81003031b04034041000d803a414051a002401010300c10341003031030180860310b000e450041500f4140a4498010f030342c240a01801d108809903048540c94001d40012a0898245817411100690301314030321904a000011603049500401d507040c1d00364155544070301c01d1210361219190107800b41140103e030402003010805510039481a03900a00c5640c0f80000c1a152540e005800d13594402d161030852454000240221035800000ba90442d070484c0c08082c4c044582c40119a200c80d0b240c00c065841150150040084011005c0603880342e220540c403040180c0702e0320707180e400f49101903c81c1c1c0c0c03403041501d0005550b400c0400c0010399100b8014210341001c60000c602030708a0b80800c2c0c11145804070b40041d9811030030240504541c006407032070080841c4020500040240c10300d4042c00c4104400007a555510760380302d1041ea40b24903041500303010030b1142180c004c1c1024a0032404260f11505110050102c00115101401150b03a000f000d0310aa984e184 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 233519487 1250 233518237 233518277
    0x10b0117060f060d0c02070302030111070503040b0a020f191b150e04180507080d05031e0703110301091d0606010e01210c0207081c0c03050a27051e01 66
    0x14050742007a0700744138400e0b0f5032480340904018484103030040d201c02c80c2140103141c2074810080d40042c10748020400030001510000458045500b10700d6011340387c0c009410201c0c104100c03002040c2c024401c20105003d035100c5040441c42c014440d05045024113105a030383d0946150340d02c1001c418250030000c0590319401002e03c1540b045006000041e00c07510b110890060501e490b0050342c06034040740c030900860000300842c075400b81407401e00504500d0029141400c0c0c1000801c0c84088000345404140c11900941140c0300f031000002c2c0c2c1c45e40740e40c0c49810020040903001680e100041842c5900b5030000c20115000c0d00070034040c1d540c2c20701481c0075170040d01d001c0c50700040303603121005002c100e042030f100500c6001404502a80500410f925001d00240b40100d07000e2490f002140320400a402d09402115001000c1d90505016803581113407038041d648009083c02c0403841489884000f0f400301e40c180d04c51015680103c604c0000003100e1220036102c8031700c4091032070102d080e10703840e0a000040c013 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 233520737 1250 233519487 233519509
    0x90c060804020a05130c080f150d14060c090306160504090207020607060c020a1202010c093507051309110103020c0717030904051e061509061b010b011706 68
    0x50840040c41e03070b1350b00100d4000c818a8804807546503854404415413a44121103d401002d42ea4207400c543c20310401010b00c040c26648150300c241c04001c000c204006100740310b0384800000106403005450121050100c0380d000125440c07007801030700000380002800f00c0710040c2c90703407855440604150a1a00c1031000354400c2c1c0b01a03034807400600450380050128003800e103e400c0154098400e445151031f21402150b490940d00c829641072407130344c0242da6400800b60045034000c0d100141902008010140c00d42d564140b403a1120a8100d1a1410101e000420204642c0d00b601c007905000d603980540400c4920a200003004d59503012203428a5610a0f00580030204220b030594903095514802095403406220b03000c002500007092342c46541c40d0500c034150f480200a403203182c442440543d4080d10003802001c0ca48520070400411500076401002e41b00f10060103402240e448150740840d6000300d01c8499084255805d06a01c40c459521038905800c6429402529018540702c41080010007010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 233521987 1250 233520737 233520739
    0xb1012020c190c060201140f060d060e030d050709090624090509040605060f0402030105132a020a020a090b01050712360801060501171b040314060a090c06080402 71
    0x140d191200716080041026925988521040c10825244c5407010b820350f04181100ca1940f0f028808120300c02041001a950003142200c900f0251a80c0d443c1c40c4008042c0d218007006a0300c40880c03811404856544101c3c02003a458951000d0380e5542c804410a81300d03c1d0241c5040c0074649005400034a0306080050061401c904103100b9517910341c40460308a0408071004e035019600c0308140b20b02c0b400c121783e0300c82001d003007a01c095107150304100201e003040c0301a0518005a40d03450a40c1d01c1218050400e0042c051500402c8540207501400c00075a80d40d02c1c01010307803007090350403c0010100d907540b19150704840180c4406041541316206d0107010b01d42c0224031024800e001d45100c00304070022100481c402e4243c8440d0081102c3d20444003c409200d07042440281e16000c0d0502040c0e0f0070000d045130490208003078400e03070390b078131032040f0074442244808040780d14020501001708144006c02c640301044610442c1c5048e42c4042d804029900038180141008408220502459100310061980580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 233523237 1250 233521987 233521993
    0x80606160f050a140601151e08130b090f2505010804050a050102030109092001020316020619020a02100305070e010503041a100501020709230907080f030306040b1012020c 75
    0x2884e01c3c0c0d24445600050a030069801c04001881009800c6000e5800c6004c1c514180c8030110036090004001c0d220724040c4004d2003031120001c0d108440daa003545001aa1003a841035282c1003022490741d80e294000440c42441c0074441e8000d100125141241c0c01000c41c0442c99102c03549407000565200d00c014009449600900c452071010031024002107009002aa03400600e0001ca41010800e00300c4405450904c101100900340740f03a030f800800c0c0c03179003004d150014801107a40e92000030380303500c00c3c403001222070b602c62201000c80d1030b00400c0703186140e8002e03228039641144261048040392411541b40300403c028000441c860f500c2480555802481410041c1c2c01c9010180507000b4800d00311912126018103040030300203564103000c4000200301344541032000d1052072111000b00445810b0242041c0d00400c0026400313002007120a000b41158400e4650390b00c186030003036450781c0c41142c0050245060100541c6103007841c0100c000203e000d0303607410900c8031084a4030000b17944071401d8501c0e07500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 233524487 1250 233523237 233523253
    0xf0e1309081b0724021509031605010605011421041401050906061003020c060103080703031b08010306060509090c01030e0c15180d02130506010c0c1203080606160f05 73
    0x244005001902128402c0c001c000d020315000300c940c00860202c800c0070074115004800c05145400007040b0b401c182404200c2c2d43d45660b500c04862542c050103ca001a80020f6944501400010b501040a0300c60a980d00c1149080203500e604481c4181d50b0805074141080d585100f07a0f42c190100250490302c506141c82c8100d00c004516400d4440a68012415411200030b00005182040c00f40b200c070f0712117007015814031084001154940c0c0301440050140140000c0003000c2503c80d0744469080c005803008003240002e6004010803c2000340421070340c2d640341900205035460000341d0b5912039402c15006003018a0003d00440c043c20a600744100b051094044a4007269223000c41c900e04140b030036980503210100e400b00708078022929210a405512812501c802581f28520300c41c0c4180001d85003c103a540312580100c800c00d60b4090302402e4205068008200e241804070055001c60003a5076101c2c2131f860309020030109200d044143c8554141e00c0c03410302c0004103000c0300650500d0062094503a02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 233525737 1250 233524487 233524507
    0x12030f020904050a020306030609071d0c0c010203010b030103031403040b01140a05060d090b180601031709030106180f1406150702041119090b030705031306090302030306010f0e130908 81
    0x36602c16105025019008807c20159084c20001158400c01090040c40700505d0111090f111448151101048030203070000240f02c40c20240464100410504c02150f4a40e540e985e42c0080f1b40081c0011070000341075150040ea40c640c0780090301d0041da00040c0d035900d640d00c0e11000100e061000e4081e680c01504100000545070380c1c0b000a00035041181402088511251a0440700307041700800106d20081185c1c007000802c8030009449041d00c0d031180c07080c0203484000d20415854060710b07090b50340c150b0810130b0209000003401310310889010fa06078280f010f0070f01030395039405441c0081d141010700c050300c0c0c00241040c640805140b562412441c40c0502e0580190085800c0d1940440c58050340c44000a20401d070074071a42542003440351702d04d0314101c820b0030600c0d200b4091002801101c02c010011001c540084001508035034055802001004209030f40c0c82e002c5d450742c20454881d4081072042001c050f00701d001b120b800e051060000c0c414090110801c2e001e00007880f01500c2a2000c10080c0100d50303003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 233526987 1250 233525737 233525741
    0x1a0f0102010f1415060705031902070305010c2019022103070804080d02030309060604090303060816091a180a02121305010b0d03080a2a03020301180912030f020904 72
    0x141c0d02d207040205069143c07071400c00302030500c00d130901400b44c0e13010455100800c0010040e45d4180ca0480c2090700d1030f001105040f490a04550400f800c5540713080c1104c908075412030006148a000491194000914011516210304904114103244603410144000515240c00601c40605c645600801311602841c006031950300302440849032010f00007024000d0000030040f5060507882840218554908000c440d40c590501905040c090f945a485000425000c2d0f041b29020b41556000c807003c00c84d94018103100049107100d00340c03a072031420703621500603100606841c0c41d4400192071a07c0043e410384003100b41c035200038400b0703103c0d6a092105c01025642d40c1011401366103000d0b42081d0348030003424040d0841d0303840c140c054401d401103051900026005032000e81d0125a000002420710302400300700726006690740c440b03600031409645070b44041d5010307030195040c2e07072000a08503441408081c1d0ba0080340c0c00c1c2d1001401e60350500644400c0140f083c0c000011440c1c42c0c00d03015040800c008003042c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 233528237 1250 233526987 233527001
    0x806040b18280e0709050405030406030e01090b040f12030506060405090907080a03090602010501090203060a1404060b030a0c08060a030803041704050a090603050c09010e1b0f03010e0412031a0f0102010f 89
    0x301d42c9030220f0b0700102c0010002e0714050940448200243e00b05a507d0075600c0c4910b10820342810b8403020406440002940004049600100d8500d190304d007a00e00350000c107007440d40445a101a030552869030300e22138030625220311006010146018280000c001e000000241284c10714031070f070720740456500f00074080c2c01d10480c804d46900701e400307007401c80282c00d49005800410900e841401000010350768102424200d43c00f0851000044131071001140103409140c00480801c2000020b05c02e41c0451035000c03030051040c0c1e60782c54085468050401205510b184405032010400340042400300d102d07510031014a4400e107100925003665035000c903505030095400395035800c1c0da900c002c1003885418000d1450060040b148241c8540c10107900c00310f50f141c041c012010700c0e80480302800d1124000c5084032003203600d6000036a1a0340c2e5450050107210030440e404c44d00b042d008a400c0c0d2400c2c0c003a0080258070070031307165920580c0200006201450002c0f80230f2904541d00c4904801c4001c1f628400c0700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 233529487 1250 233528237 233528311
    0xc0603020c0f011a010207170a0f02040212011e0b030f0c0a0c0b0f0f0108030712030c180305030703020f0a030e0d0c1d0702010e03090d020d1a10060806040b18 70
    0x540d890004c400190511209030700c94210100d6001c5a0103051a01144284008e03030700502c4400e801e601070010800a00840081307050280060001050f03484c0e801c500340c1d00c030f100e1a84540f81803035112204804540001c3c0c54184402c0d40b00c40104614100e840003034040c100e001d1502c03800c600166201e50407804401d807007420f12484461b00744580c02001281c4180900242c3c001545000c69a658201c0705260804041003010f603241030f151402c62040f0407214105952401068009807241009612548141c40480140c4540b98480c2c41c5a1004108000403e0301030702c410102d0130101c0140803814032071100489507441040d10204810399154002213203180b01000c220410702c0d114002908452031a0840d5226510620080d18140d83c0c40f004c000070641d0603038440541100b50706d00070000d00b00256a02c80000d1030b140410460744c001c1c04a110455005944004158803882c007444111143e110a05401014052002591040b0807003a15089090514100003030342d0712010b101c00c028019a030074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 233530737 1250 233529487 233529521
    0x40203090f070605180108090d08040303020f040b0d0c1713060603060f05150a050a060e060d14040303051003020f06030411040c0e09090609060708090703020a0608060103050f040c0603020c0f01 85
    0x1c05902c07517212500408203400307003002905801d0014445982d040c00100c0c00080022810000e410548a40c05468001029110303054841d511103081110903005008100c04691408141c650460b01ca0012200c0b0150500940340280d03c80100c10b0b402c0e291240c0d4140c400035103682000002904510580e80c1c211100440051282007082607035008010118a9600c1025401c5061225545600d0301300112103850401148202e0307003034086101401400172801f0b44070300d01301d0103900c01100035040074072551096a04214a58403594a030a0780c036031900001c0e4000340003026401007410034500030340c0c20a00520071025520070800028081d160080c14240004408118506d80c60424550450b00b02c0035a4000d040c842c1b411380b40c055580c4000810560800035410041142081c080c41050003441e00a050500d086807120b0000d4240340c01034908600017460300d4000b0301510002c445460080e0f9101c40d40101140c0307422000c40107504810150742150149645101c0104400d20034041050410070039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 233531987 1250 233530737 233530747
    0x31415070503010510020c01081f030c091e0e07060e030a020a18060e060609100909020a080f07110601060e040b0405041a0705040f05130f0f0f1104060509040203090f070605 76
    0x184042c175200c1d8003002003590710603140d0b0f0b5007607a04000d51700e61104101390a0301c00804046c01e0302c94400c0040e03001601c0610424808903000855400010f408a6110fa003a031b00082c00002c45804c039a41c0003642d1015070407525040c05903e200b08201460003070001c1c111010160f10350001040d8015540c01a10b001e04d4018031884014200d02030940101038005400c0424a84500442c41911844442d5441035400d400340c61032203802504101d01030455400c0454449800c3d03000540b0501043da007003c0440e0010000401e4140300f800101403240001d005003071103034a8070a09072010800808143c0e4002d407140110a0981c55500c0386901ca58040c40b850758000500704126840b10a0180800c0100310040005021450038424000210b45003a180011a081c0300e10510b0001d115421300c41125a0a002d2600c2c95a40310f900f04202d90301d8131001c10010445401011820782c4190700c107843c0445c0042c0114425032415601a550154010003501c08400c07003a6582410715051f90030000100e0307001f040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 233533237 1250 233531987 233531989
    0x1b05030607020d1409010c08160503030f060103050c030402030a1212110904052a070f0f050a110a06090e0c0705030a080403140307120b0d0c14031011040314150705030105 75
    0x8282c40403001900c1303014505000e14000070701d020300304400039041140004505904484818804600c00e400c6000d032500c900b4a82c03100002240c1c140c072502d00180c00c2c08041800744020000302da010301c3e402401840d40007d1982c9940340c41e81c0c00914902030040340c1e0074086808607030307001d040d0500103d44080c9581e40d0040c0104001c541001c2d104040d440745c40501d50442c000c1080b0f040d0060004091940e0311102c1618000d180001000f070014003010f54034201c1d408010001600340b40403403003518540c6880411a09001aa0031644908030010320062002c000340100e00c0c081c5500207110b82c000c03502d00b4110b0b4898518551010320032800003040c0c40100402d15501c81c80e501d09441d00560b02c18036508217040000c0c48503803603412102d1001d90b2908080d025036035298a40d00a80d60003208512101c2e91148403080d2030316000b1050b4004d00a00c61300b01d24100180c450000c041c204e0214490505085482c0c01b1801e40c8100c281d80c03018882c444502e0381070034072904081e1044010f03684043d500d60400b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 233534487 1250 233533237 233533247
    0x1509130b180f0105010b1605010b1e03060f042111010213060906140f0f0d0c030507020f03040e1302180a020405040605010302070209011a0f03040f0303050f090a1b05030607020d 78
    0x24121144d16220051122010a404032030340c8040107840340d9112250760400d903005184a6401507406043c17660307407000d80481d00c000808482d008509031009552220746c60071030b0711801c84000b81514900d035601044502c0c029052003103000c061910440f0840f200d4001c4e4220781c00f904400c4000b10314681704114442c2c1c010a6400601904d24003110b03402020120140c281c0034a0001003e004c0c008a801e1003807031500340c00e80700349140c03914045c07000905030303803002c0c000b040140c0d01070005002d1580240b4007a20001f04440466a452003482c11655a10203107a40141d4007180480e4440c0b082d0320610040c018166206000702c906000c0140d8851a0034108021114158003c03418140140b09401c007581d90001868119268200c02d80d69600051758003a04505c00d0600202103668003100348014400e00030050803080d0701c26102040741c0e40364513424014907103044490380d084e540082c0f05800001c00e080c4680c03501c07005401c00c80c510f031074072000000e040480071290417006a106104039180c842e885 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 233535737 1250 233534487 233534503
    0x1e1a09030d05040b032404020a030504020a050d02060702150f03090f07060c030203160206041806031104050105030a112d03100c02190f0506010308070b0603061509130b18 75
    0x20306010746002d192403944d10300340c0002011600d400748980c05001d00044480035200c003800004108641d5280c02c0240900208002c0c2e41c1070780200581c0401044a0504401d030b0b5501c0ba400500f081c4c200072540d401c0040e81e00c2070f50000e64001406002c503403510694200070b58000c8070008080c00128030410215031030f064081d4004010001036001d190042600881122400444800e40680c40c001c80c2c00440c07071610a0398040306a400c4188a1030b0900d1095610910661b07200d0300c8034444200910040000780c400c00c0c0500e80c1d258211028400028910803100b80000201416120707115064440010700244403100342900361a9444552205103000c5c40820414210048100242515804001e5071909002603000030070322a20000b005001c00c4551480d800d80e4004201c41c80356859183c280e9540d0070105088640c80c02441c045825440d01054a501c500486807015603400c85440400610780f0014150032201018030030582c012482910190344908021010440c0c00030880100714641040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 233536987 1250 233535737 233535763
    0xa0b03060a0b0715050702010c1e090b1902010f0c0e0616020301090602030a0c2a06020c0d09050a061b0605190501080f07090b062b0204090c081e011e1a0903 69
    0x7400000202146d040304c4920f1244e2140c2c4a4418ac0c084e80141c00e40710311840d5005034911170300100e41c004201852140c2000041e655900900040144c00001829075003002190000300c0d0307071001c6082e000d0a004014040d041c80f0301104080c19081600800e00b1038240043c182c50300c94000040000b01c0c0c00e9802641100b040700e19100310344900c5052100f07058100042941029445000030740e05001660b0162840c940c809816a1983c1e4502c2d41c001d00b140c002d41c400c070f0380201100440041c520f0300950004044c490311548031140c0c0a059030310800105030003020b00c80c4058001032980e100644c54456280a01680c04c001e2840c008801c649a00c1c00c0f189a000c16882030804006d04400e4484030300355001031140001180b840f0524000751080144c602c40c0ea500070b90310104001075210355030303000042c0941c41358580c0302c13081d00d41c0d00d003c0c50b10a4170104c4203202241ca0400402c8803c443c03145030759004c42c215002010841d115000c4c3c5c17043c242e403082c0301d01ca00030707022600a035240313020f200304003030410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 233538237 1250 233536987 233536991
    0x50a0b06120606060d020f0315011e081f03050f0d0e03010b010e0f030a050a11040c03020a080412020f0313170f19020102011803020f060a0203060a0b03060a0b071505070201 76
    0x445407956214001050180a81c50205155040405c50f4040e240000041a050303512481c0c440b140725003140c450782034207000403840e503020b1617103012040035511750004a6942086990301c041901c07801d0418111400c074280f14050340007002c0b910501c034628085841e80c0c007808a916204200622400300702100906c00d91402000b03190503a005007013264206803c4c0c96209440900000203820f004004001601750b00516160380100302c80301d07031140d102003011a400c00c1080ba50060441c124080c0702441c10102e07448901040c003180c94a032801119000348d2040300c00140c401d4074010b046401c044002c440c09520f80f0014055000c0b19034248180d11581401000c10020010083d9510801d50003a4048070825007401d138250392037074021145502c0d4100032605041d1161800a50b60180d4015804450041d080410301c402a14001c4901819008142100707460904c0200c240d2503001500d46580111041d200055280d20440500110380c080d044e0800760313100e80c01589094400c01001c02c01164 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 233539487 1250 233538237 233538259
    0x80601020f0d120b3d020d0905130609021602041109010e1909090f1101020a02030319050c0a05010e1501060c0b150d0c06021e280609050a0b06 63
    0x3d502c0101c2c0a08480303a21400b140301440000850500b0100142c039460b4241c000740924214241c05403000c0410350303400419000034040c51002c90f1100307950400c500c00141c40007410000c5180c100b845c200ea070030090700009441c95403000c1c908200e0780301d2040642200c1e06200f8080551a00b4441c0c1356103a40d020030498540035880000030441001c1c000d42900c41c0c4902c040c15103021180302010009091210401c000300310840c14241c40d0b40c050120200c800210488590050303500c0410a1104194041d0041d402d100805401c0081c80c200d041c2454200b0505204030310362018100704840744140102c2c0009011420301c1c0303480707003010001c0c032000a00428020042158513417080c10039210302d8000c3c0815140c0e4641d184009e01280e059130006500941050709241172018603c00d60003110959000c44000700c50403c04030280e040010302e0b03901c21740c00c20404450700040810000c0e80b01100425000441a2907070b0f034030300031101c105c40f00355000e03030040300b505040180c011032145e00001c01b01c030529a49 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 233540737 1250 233539487 233539513
    0x20102040e01120320010f06091401060806040e06040c15050c030d02070602042d0f060e0d1a040c03060605010e0d1223070507051801061805040606080601020f 70
    0x1628041c0b1919052a00841562043c944983d807505d20b03030b107081000c5041c3c610102417014064101c000e03502609629102000030350403d54460001c2c4401d900d20780540e180c3c41c3c0141034034102401850141c005803213204240e03900c0402e0040611451040b03510401282c140110764501c07540101c0d0b1101405020000000190b10000603280354280000026075155400d250240180c09281d000300e42d100854504034800226080c18041c5440e0401d1810480f0780c0e803000c00110244252080201044089049032180c1c24110180c803000d0f8022440f101d46146400f51520007404204c8040c0d45158003160140100011070040300000d00d000d1034802c110711410070010b1703240c0c0712454000b0800048021200301581c000c401c83c5010708a260036480071105c40100748100ca83c0080802c8030749014007400806c8a142c5060f261323120000e00e08207031800b40e0034000140e0b2400501c54402d0381000c0382e02ca0000d001d565a00900015028941c0c4010310303401c0ca240064a440035020030094241c104204401071703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 233541987 1250 233540737 233540759
    0x31107050f010f06260a06020d0203060102010b010315051c020307030807110a05010512040c08030a05130503011406150c030f0d051302060d0f020d060611070902030105060307030b011710080c0102010204 89
    0x510018510141c017401400511540340656107000200410b0020903c51400c400b40e41c00b640c802c903c00c1e0003d0001da010701004508941d10500c400c4021404504140300a080140c010300385910702d18151250300940d50000fa16000452740200c0b1035140c009000c000300b00303c0b4500d01029480940e201c0e04028104000a486401503007903a0740d03d00710ba80002802d00c1010140c03140280303034007401d8030340e10011715000401640c000e5484021081c444200040d01d410140310ba0a92540219040c40c0b00e0307102d030010403005041c50710110f080c0c410140100c401075a0b05000030320700f1100300340322503541d2800320702d48c2d1003174444c020202600740302c280d032201340580c542600f12485880400c800280000064000c1c03002030154000158040e40b50200c081061030308451240d08c440e0b114400c90303054994070040b0905130f00c424050942c00510500c04211007900030341106265240c14109040101c00c2c1c48402102c182c2c3c1190051040c440c485002c200d0121b080c80081d604002c00e100951070607092a02c3c1c1c2d90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 233543237 1250 233541987 233542019
    0x20f0a141201052b05030d0e030c0d030b0d0605010612050606031501030f061a07060b0307120213020409053420070e0c090a0603060305100507031107050f010f06 71
    0x10003003000d5080711080c80e142441404c0d003c04003075104100082d080c14201d9032500810078000c007003407500c08803082129001043e140c00c1481c0b28002d0a12202030401103000d03243c0c1071045038001038642140320018810b4040e40b07000e8012a640c0a0001004282003000c1d1480500000e00a001c01c100340044010001c0703140c1108602070170042102c2146d00e62440003015554452588e140d282c02808000721078020040407018021070041c883c961941040507282c59680c444d00210325440d856034001030078030100607050303002600001420a0781e602a0389082d10310031182c811403c1c110174112002c08115441001202c000d1a2401400c00050100034000e50980c00b000d072403080081000d00391281c4d04111546c050304920325904100d041c103850301551034005c801124810812030502082e214401d2150303c04982e00900184542c0300c1424000300103200c041c00c45010540c45003084034001145200a01c0c1c2207101c0e1004041c0707004162401421200010075400880f41860f404101640c03000c8041c1c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 233544487 1250 233543237 233543239
    0x8070c02010e03070801090501050411090108030a1d06040801020a030509010c12090623070f020a0206030a0c09050604061d04092612010609030b070c0506150f04020f0a14120105 78
    0xb884104415000900d8a103141c0d01141d020b41c00c10001200b0840d0642009009500c80c1310451280000002000007100090140390032584c42406203507940ea21039015100301703892400380c11310805030b90008911103074000e40022009030740018854803500d40c50f01c181980960740100800007409c07903020007014030302095029100261110400301c1400656480801c5d203000b406400102d0300000905008501c4040b141c0ca000319659529400f451400803071102c048540c000d245d40e181d40c0c0c038900264000c065400002041003441540450240c0b00c400040003c5c1c80369880b46901c40012010b9500c410400d209058000c1d030400b118a000100c14074810078a03400c501c0030807054100e00289504050140300c041d0b04079018008000149582c228002e5400c0d80e0280c001240d6642d0361060507648401400b100030700c2c80d800040000c1038a00303400303c220400c0c0f000074141e054514403a40080c090740c0101044001101002459132803850b00403e56001403800e0503101801d241031300702e00790074090051040f9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 233545737 1250 233544487 233544497
    0x9020703090b220801020405010f1b020d031d0604080a02040207080f0d020306011e0e0910081605030f0703030804020d0206040b030a0603060b010201150b09060c0d02060702010b0108070c0201 84
    0x1101094003070054035000d00524001c00d915120080d4107a40111032010003103040e0060143c003c241c1c00018000c95081c3c0d001a10340398048425007004582041f44801c104c2400c1403216030480c0180c1d108540e54060368000c1c1e0b1a115820302e40c1074058121040c0284091269004100030001d4980100706529200c3c0c040f50f0068890f002c90404c2541c41c4522044002c4180c2e002804000d500d0300d030750142d0f000341000e80c2d0f84a1504200244d10480c021030060210105002c420b02246601d00055650f600800700141204140da6641d10b0618254850b03220100208020805102a050030099460003a030083c000f00081031031520702410200c0042c0000e8018400042c4610554a0301f1088400134002c1d000c0c0750340d40703241103010319008220500044540605050540540d90300c14001c0310344508160b0b505410081c40c04481000720f500544004da0805030500c2005140f00061040030655807041e0080e0002e850140700017421250350310b03c1c3d10306001001e8140030142e68000d14412031941c0c28244 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 233546987 1250 233545737 233545747
    0x31902030a06020c0c220f1a041104080109080d05060603040803070813020a171b0a0605031302040203040309030326010603050a1407020a021219121e11061f0902 71
    0x403582091803400805d6084a110b0b40e442d03490b10403102c0441e4075454124010000340010310b4001c41503880d222039003000c03050030b100d03030800a14041d8040c0000c0001120001e191555450106003904c0e2407840a4480f81c0020030300ca2800c40c2c460186035405041119002d22790714107903840300d4807400b018000304200a04080000c1c1504041100301021a80080081d001e050307666011401c605147c0030010524020b02c440809081d420401c02074001d04003c00381401ca604065084802c2d400040101161003030280c0d2100143c1c9452008500a40c042c1d9a0041c000382035060103000d12690096aa12010440b02c078244280103094003117065034118035001c500b5450300580030740070b4601481124000011001032101d4907400060300b90300b252080c1d8410300080c904030300d41e54a0b20762481103042c2c14458000103500180014103503880301a014145005980400c103078800240c0112074400717000c90b085c14405401c18504100f40340c2e02c03442c68011080c0310b415142c2c100340b00c4c014922910314082c4e00458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 233548237 1250 233546987 233547007
    0x3160f0f0f03020108040813080303180c0409120f050d0f1b050f0a0f020a0b0a1d030408150601180815090a0f1506180203040c0f0f050f12010e0a02031902030a0602 72
    0x201c40d08c000c1141c6400c9a031203003485045828014140c0c3c03010980c502c100520a170003420300c0d0180c001001d801c1a100140e0b11020701c01038902003010703060a805c00108100042c4504001d10a0440713400da42d80000484292600135200c40300c901c3c0740510180941408117055040b280380846403051250301e041054148122002d81c50100140c00041040000c0403c014011491740d2051000b00d0710b11420409680b81950480e40340e220318010043e8642015605c4403a0b12601c650440d008401803501895050401a000c00c0314292500107942c0d1342c000540910082071496201134100c41607801034800500d9994500b54103818081008140392003040500601803595800030f0002c14080c2d84040c2d1130004400f80c02d00039031040b0707805c030b80050040340003081121046000200351120b0040d15406e82c1e05050405c59002d20340071b569680010049004400d10201703006441c1c8582c107140051070705549520425007003003c0e10f84084003002880e255036003d43da00249427418240c106500680d0744800340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 233549487 1250 233548237 233548267
    0x50102061b09011115100f0303080a0b060c0708010c09140d030e150c060912030405030f180a08030a0914220905070803030702060108030f0306040b03160f0f0f030201080408 76
    0x3501404c060050f980340203220640003152070301c200711100400c401240c44200c440c142c240e05000240000301500f0018102c0b00c1c1c2070b030042e400700100810f0a800d280c0b95054080c80c15070031703820004050351140c0f403103061036401c003950001500307807030180c1c81c2e00c201041c020601e0200c0002e0050200b20f1960440b50b040d440d0702100f01107203180d4000407641c400b420340301700c0d6a1b03000c01e031102c1805210740c18401d52419444404d481c042c5900070081d510b040180302d41010070f900488410f06242c52000100304080c2e8880c4050801172090b18040e6490b41001c081c0682030380100d0f402201401a4403107407160a41d03400c12240b0941c1c1c0444424818841c4031181d030001050400802880b501c01d11101080e01080080554401c2c081a400c45146a8803401400e440e8000c40c0d0f5000b01521040c0085440d500d02038112401740d0700c010301107a40414410310300852146a59220312910310700a20213010262580440c41c018203541046201001e01c0c0d130b0300003002880300400c05400140702050f200c00c450018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 233550737 1250 233549487 233549507
    0x1109010f0e010e092410170411040501090606030f061503020a0e12010603150c0221120115030c0212030a0203040510020a0302090a080d020705040f0e010f0e0601050102061b0901 78
    0x3400060f410b00d421782e5450b1a000b01c81079825032161300c5602e070b03009511340400300440e100e940740d46410310381c1c0e40428110032110f0040c0c0100c03071b440028200500c03152240d11941e0700800013443c002c503400780b41100c09803c6038040a0000852400c0c58020f00200d82c1483d9041c84110aa245c01071355020b00240c120390102203128607035031000380c5401b542d41540e015000b40040e40e00821000801c4002c2c2203820701100d070001c02d03c0c0c026801c5101c01c40c08002c4200828100410501d4126203090b0108035043c2a0507003d070070440c884080480728102c1d0702d6051240031615030990005250224083d04114898000180318010070f40e00000008d08014003844603940e41d04c1c41c0b500541d100d424410020f000380d080941c0040c000e10b09103000103258000000d8030302c00400340c1c0d006401d581e030030709003800b001d032010800241003076450300c132302c4028840c1c2449908111480224005920700d110340324241448810b07881907045500040c14800c80107583c03501126013235410b40343c3c1c540e16200b4030300681e0381c2012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 233551987 1250 233550737 233550739
    0xf020c040614010801060912020d03030e03130602060c070b0114010c08030a02030f2805090c1c060507020303010f06181206050a050a1109040e01180c091109010f0e010e 74
    0xd28800148009002d4268180c038002621045001c0ea203ea0044500599a1045003d80d000c00d849001c00b5090594009194601a15001c0703003031200e100542d4030f07540c400d808910110700300000400c841c50341413150315000b00713000383c005103094543d40703900d005000103003c0e104403074040d2111010703140e00801040c801c282d40003c18684a00d04020000c0083d00304035001010000401d001038284008164034203002014020b50600207402115828020003009050030307241e10038a640040e059648615850319a05002c410786622589407405c1400e442014011030300b558420300040c000142c69007803400c240c42981c41c2042100d01b040200c1c0718007102c81da0160703041c2001040303841c09001c40c60300114819501c5503402d204a450f00300c080412a10f5692200c1440003003408413022514164000380003c070b00f00c200102c0c020008840031000b0761121107003107424402d8140208007500c030600810120020358100d00307041c07841030310000c1e0040c81d8211617141044171541c2a42c2590380185401d050a1030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 233553237 1250 233551987 233551991
    0x50d0b03030d061502060a140f070314150301110909041b0f09020901110a020105180a2619020901030605041a0907173016050d1407120f020c04 63
    0x965a044c00003c2c06840003c0801409680d0000ea10001680a16017644c0c2c4078241c1365000da59605121105c5c0c3e070001c1c200382d08142d2601c00700c92070124403440380d82c014256031903001c1c024141001011308540c0000e08000203a0000c1c84508907550b00d20440c1036200740c01030b8422041494002d152070480c00d5603000351000e01071403200030030002c4640e8050005101c0c2030b01c45c020140e0403184429038800030540300a0004204009662203510020041407140c103002c0d100404003600c5141e018079854150b6910b00c003040425440d820b038030004100b91445200301200254001c900c42d00801e406100500000c0d10a076200d50100301044012403945c2081c00e800500b9040d42d09207502d8094696010348100104000d401150030221000070a50846050501c80c030200320b0b22000c1003281009464442c00410b1340c00034020a800600c0001c8104151841240a02521000e00c5000352640f2440c00d40400ca802e000d110350b45c0000c84031100108000401c0c20410000743c180d000492408041c240c1e8950414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 233554487 1250 233553237 233553239
    0xc030301030f02211c0e0301090b1b0703020d0e011218170a08270a060b040c09030b180f0a080d0f05070f03020705160e0907090c050d0b03030d06 64
    0x441c500341d400c141c5510132512102c1c0c0705140481e081c005200070040d030345140c01003070030f11214003500715100e44040460300703102442c91070790000242103a65106c402d680520b0100d040143c22072182107090300e12200300007075a040403480c1d00d0096451541001800901202c00c100800c103a00a641051038501941020b101d411001041e09882d114059012500028492540d086508101d810755181000d1b0742e4070003201c5c2e035603200c104a95401d860b0031403140301c0c21101d280466130340a0045603d400e01508001c00c5020f0350750140011580c10369200010030910900500004d0001007199400c100d0904100c40c818145015560a2550105001080b44600101c1c00204031401004d0010480b0340e400070060707450340c90609801e440c0c0803910640099544107030b61140e68002e902400909010380203c800c019400c01410f0032542158020100c1855860204500708008100e444050400404140310200c501d50b400342c103c0c002c0480219403541c4034200841c441d10100152086001418030078000d003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 233555737 1250 233554487 233554493
    0x60c0706142a190806040f11180916030b03010609020a020a060e0a030504060807030b031207061a1509030f0109030e030f120403110d0c09060f06080c07020105030c0c03030103 77
    0x2e10320364000c4020455005403210001d4400c8415281400c1041c1c02c00c040032801e006013260b002c8001840182e006580b0b1810369004e401500c6031132038480403e403205076501c1029010008241c00c0e5104075201d1130014003000841c000018110010850303508000c00c03402c43c0f500c0020301615198000341d100510101d550b0101982c002904000c0c035005520800038800c1e6602c100d91600e40c0c07104090041107041008111062180300c000d40d1084441c03800041e40ca40c00d400281c04c0c00103480d00448510004903000c01400043d20a004602120200464030300045401040030381600340d084601448011810342c2250310305201090198050400800582d0030034a806003041c1c000d4000303140a4840c1c09001c1c2c00c03c1e000010311543c80c50703060f0702143c101851b50780c40354441c980d08a50150070804040d680c1000a041a00340703000fa0151f0640850b5840c18010181050301d02ea501c00c0341049091424495000303c9071040312505502807034a69501c0d40c642c0303060040d5129041990342d00d440000000414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 233556987 1250 233555737 233555761
    0xd090602030703240b1605071202131a060a0207080106090207111507060903030b0306040c150e010905190e01080a0b011a030a091e1b06020f060c070614 67
    0x1c0b81c40030752810881103c070b4800c501341c003034460702c81c080d0690802d6600b40f010750510805094070204200f01840d03000c41300d030b4a181c10583c4a0b8400d01180080070390800441c505050312813800207201c1020083c1045c1245e0301a07070707001407034821405810700103040720b01a4828013912002e005100002d1204998510715480203500c011001c0d14180344400c0c00c11031a00e004090030b943c2403071074613606c0d05001d40d50311610018408003030101e083c1543e80007841d00644040c008144114095000780320000d141c90701c400f421010041c0850200320409a010140d40c0e0014100e000340c070003d444160042e14100001c254007240c42d000ae401d0b807100980001b420350740c005461039031a44180c1704060076136620381d20703488011440740300d42078607a8041c00060709180301c1c0d9001e0070405020301c9404101c205480c084400d81d84003040700365082184444400034030075400c041500107000b81d00c028042020594605619100d0140c0b12406008002410700c050003a11b8102984030b40e00c01843c05154100b50888903a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 233558237 1250 233556987 233556991
    0x80a110a08060a12050703030e0402070f030c020109090e150a0e0102041518030308010506070510020a030b030f07050a0605031008010c03060501020c0d05070b0a1e09060206090a08090402030c0d09060203 89
    0x3114121021020138150a01000100b40b698044002c0030401e05542c1c080d10a0040c1c10002038100742d0900000340410507036002d0a418a0280d20703414000c0482e40001892030034250800301145050070a01140183e002540904030701000c0c5540348c698541c0d04254000d400301c80c460000d250300202d0042000c40b100b140d0760f220b0720001c0c0c4401c50340110a0180035200c90795440f01401061502c00104081c1c200b0b5401000c0f41da100704152804420700444240c102e0f00200441c0300080c1c0e0700d05034050903007400c0140c40742000c4080000c0200a15100002c0c402804e58000c100c1000004000b04440300d0b4141102000380050704000e000400c60b190000740209024440e0300d00610440c1e00307a00b8507003000b441000310303a0b4101d4050101207007461221340d0142c2c0f04820480421211940114000b128071380312000d2440140ea40076140c0e454400000c0c5006405001c40d101c982001d01c2130800101040119080c1d85c81c16180941c60756124102c05460f406050b054407081810a1f003803200b0020a58002c2d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 233559487 1250 233558237 233558239
    0x2030706180f0e06060a020309041d0c0d0809010c0c17030d140702120a051c051e09060112020604030506041202060702030f071506030f060912030e0a03080a110a0806 73
    0x1601d590356a0a41d03210390403a00c5a682e42d200000040380d01d0341802c10041030700760118012031349400e4a4101150031604054846030300481ca40d0702542880805200d80500a00100c80c40d0402103400e490b100c0c01c0d8440c943d60681030001c370a10341402c0000655a420050000d40304581c85188c00704205926a4404003565549510b080740305820107560b5000740340941000c0d4010220081c050f040e1203055030084c64050140202400840440a5208150b603040c0d000ca40700807480303081400c0e00a009041202001003545201d0040000303182c000070b1954111940c1d8407014901f2540c50000c62901d116540002d04580190010001403007540080855814030079421600c141da10390400301c1e02c80c080c01d080c03640f002038108a21070219051780d01607003540100d0b8400003080740d42e0341e80d42e4018014079407080711810380300d003130701d0060050b880e418211824082c01c0c00c0c81802001c41c032140d29403e05400003810f0000e0b007808100a854141d11820840d01654803480d075607100c21202602d000c400712542 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 233560737 1250 233559487 233559527
    0x601090b1816180311090a021b0c130b0904080a03110a020d020606030c030d210905070806060603010e01060c03030f06080c1507080301050108091204140906310902030706 75
    0x30881d6908850003500f10f0780c100040241105c0554100000706401500d02844240c003409900c0c1e0b18150403258000003106003008280510144041c017904046003901074149034a450880d640f41e07181d04141c5980302d540100066074a00044805070000d02c00540c01c900d500e94045004000c594002401c51307041244e0342c080b1941c1c0e07550300302019540d030054130885030943c00c0aa8216609401130120030602c11851643c00904616058501c084130180f5038282d034a98800b020402c4003807010300c00303140c00590550701c407840c641c1855052041e1001c103105100402c2047c0d10b2004c01e1510907404400406202c0c1b07000d00c00199a8559250b40d40c0c904d200c000d00c10900560600c0300500c0b0282107030007940c1d1051465045030b01c0e1000642c1e4410000344806641c1c040c0c0d450070145e107107420340280f01808118030054031178140c840c02c0c409544001045d0070702910009501ca20003019900f03041030000260f9040e1041000b5200c4420090041000025003602c100d41d4041200f980018860000e803100d0085 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 233561987 1250 233560737 233560757
    0x80c010e010507051603020c1207060f030c021507170c030610081e040302120301060306140f01090306020d0b040608060402040b0d1a0408040b0a110f0106080601090b1816 75
    0x40c9080703079020b807554000b144d802c1150b600d04000312044490342e0b9000380103641c1030a00000100350401c002c0e09040e041600036410910030241c001c2070a041521240ca000c004ca44c001010203543c80c94940880000749903690f000880d100c4c45138520910320242400c089095041c006002015504181d82041c40742991a40e030020641c40350107110b11401c20f0131410b00f0686000c01108110000180050f000c6004644034038403081144401140244003940d40008c1181c6042d65442e040c0c5240e000043c482c00500c14803e40b26070303215100100b07681d0441d03030042ea1003115581c15401000e103100841c0e0001d09003400010001030200340907200354001d460038030045079043d08000102000d0b4130001e08155000303401c00381d014140f8948641c0544580d061a1405445410703520103a00150044000234205401e251910700081c044d1184100d40c0200038000709041420064a415050143c0180c4540e01c020362401580c9003c2c3c411003520303458960594906040600302c2c3c0440c070152010002c200040c0d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 233563237 1250 233561987 233562011
    0xb0901080a0f0b060105070b180106060e012106120507080c040203190b03010b0409060504030e030f07051c1a01030c0509070c020103051302150a030f02030f0601180f03080c01 77
    0xe5585600303a0141d01c1c80c2c030030005540d4400c04203102511035810040706121040000d58a4038540c0d0243c038880010550040104000c1c6080d40d000350060820441c0d98503420345682d80126024074a0004402d0703a030500c955000c0c4490061409901c003211603900d0310b00400c1032100100b03041050302c0052080c0d40b075030b940f00014001648025514040301034085c502070704c01c0b4601c40d80400c0c081c81c002000803480b40d2a050018098a0803950141d80c0d60759200c090008168001e01010300340d10b000d601826502600c1d540082d1200708070f01c07034103000d41c8c08200000500d12000420b010043d90180742c400004580940d204100c2d00c0c240800c542c1e103034003d00d010656240204000340308014aa03241345241e10694011005800050129602d001182c004400107035110059800c5d0082d0340000305440d90310480c002010380e000740c000005d00c68810400d00c9914511140f1031903110b44282041e844050031604100c0301c07001d003a40040c0b00484000000700c10800d0080080c9006e10f1900020f0002c407440390 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 233564487 1250 233563237 233563243
    0x30f02070c03120e040f0606080601020a12110703150b131103070f030917180406080c0105070f080c060a0b06120103061d030301081005012108070c15030b090108 71
    0x50406400c01181c0d420400000d031981c04100980700c030340d01d031011111022001003030640ea001c601005556403a92800e001541e0b01090003030f03000c8002d10040c007504826480e23174000b40e00e6201000c410480050303d138411003981003100a000f550701101c911a90030420900200134030b2354035403451103205140d134600d20b00c1d29280a01003590804150f16451620707284000e03980042071006480c180742c1ca9824810104820055034640400c1c0b4103650355554490400c0301c030b114050440d89900c140c1c40e00200b031010715030001d9a884110801e090041c3c4d074110074149a42140150140107000450020f10071051800208e01e140c000c43e1800301c01d20000018008021690251001071411180540010000b0400c643c00000300d505000700c4040d1144668180141160b1098010050592244d00701240307440f0741b0702c240c40c014801540c81c1030724104103491200486120716400703800d030b10000c00c851007803119850720300c0c00800e0380c080680445201c114002d00079000c030052080c420740c0c9030000040c41b40c0c404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 233565737 1250 233564487 233564497
    0x2040810140f0f070503060406090f06030201020c01180b030408121305100509031c0b0a030803180a08070308060109050a080606010314100b0c0a020d0c080601050a06171510030c030f02 81
    0x4952030030b61540c0c1d98130003200c0b80c0c1c1000f0b100907402502c511000840c00c80340d100d04801c400c1400400708000b03065000291030314052645050420225071590000d02d12031030b80500c00c3e01e0810503115034986650400c10006e004410003412405022000d2182001030082000003080c49601940d0005189280400850b1001c44a000e82900100040300c5282060b0f000344842440c801c60000d026210000881d810200342c0c0c104039a185030000901080240700715298000444000080490000964648410b8001c00b2802400d000256001c1580c1b030303001d416940c02078500a018404001d5449229560310081238502501207840d00c40b1601541c103103403024138800c21004800041440c0380524a640d640d000100d080b90078007030b00c40c140f8010782c1c3e030080d03100080f8021600c0d2036181e4188005541000c01c1a44064860b0304800020825560414800304810000301c1040101d6079420f940ea00301740303a981c1441c3d41d005009110046510b609a404001d07069020364040140c00d030300026407800c81c455 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 233566987 1250 233565737 233565751
    0x22101150c0f030f0c2001120204060507120c06090f03030e0f060c070318060c1704080d0302030423011b0e0609060a02100c0c03030c08070e040c020102040810140f 72
    0xd04200305000ca80140400c20304c844907440c000495010030348480c20b8080050703100c0d20003080740e81510040c0d90703031081615584000300d6204603e01482d0101c007030040d21608400501c611001c00308181541d01802c101c10070190010400d0055994514100b2400340010700b084010914140400228202c0004c4810039000c1d508010700d5540c940d0701c00084550440c200803002c1042c0120039030100003000b0034020041255440f402c1407203105282618194190407044203282000b403104108400c00080d206460700f986007001a81c82e01d40f414140790b100c40007050136a4043c2a81c0c100780b21460150322020302001108500c15141b48184021202409205107060f80001c0a06c0410b89500c0c1000040a80c0529030040f0307041c0000394606c440548281c030f07014401090701c80641e0003d2541501500c2c904410500d41860103183c8600702403c2150302d000114048e0380c5da41c0c074414a15000754101e50141180c94100d8103801d0102c5182e40c0600511092404409988000b04007204040d80344503000f405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 233568237 1250 233566987 233567003
    0x111f020115092315030f07051203120105010e0612090a0201080a06060c02060d150f0f06090b07060c02070803040e1009140703021303020901030b0a15060c02090a022101150c 76
    0xf10720081429000c2010f0300c00c40760811003002c85401540d0810248442007106000f03401000c0c502030030442007400b040020b0010760810011800030301d018015403070542e942420044400310181001c0303039244c014844002c020810b1041480301f900f800240c10105035100340d8070418695600514130064405070700c1032202181007204107000618100001d0b225241700f00c000062010348005241c50302d60510360000d0180d0318000000d000d20740c904054440030304010b04001d43e24500c1c02440031040d03c51900d0107400c45549841100c075061081c03206c0402000c2c0e0b1300031a5103403a1035000428490506561104c1003c404050009010845004800d40302c003000b4400d045030350710900c003500a5401003111102550000c980400142e4950000320302031401092211205e2030441100b004585005401002d40035550108116a680c04040001519070540303840318903032100d9003100040d000e40c0b003100c1c0f00c000314450f01c1048595403903a0103048410700c20550100c000e28000c00c0c2e8260303c0b4240c014100340d0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 233569487 1250 233568237 233568281
    0xc060901061d13051e1006051c1401020406030f14060306040f060905031602010206241905040504080910031e0207020303090306040809121603111f02011509 69
    0x394075107580d449240400016404200703540c03a0b60034010800030f2580640f440c495481085102084486c801d101c9511b0200061030800c40092103e813803640e4106400009409884100b0901016111615445100964840d0f40364030028004d088811110101a40381c845007000d494034650312140515009030250a01d6111525600e8000204204c2580c074191240662000038400308003c2c05051a214100d90009607144002410040701406a0a8694900940c01c0e1000608004070111003000c030b07003000044444810400d0b6694070795001541c000c0c600001c0006002c17020300106040001115450003169601d40d0070340494801031155494440046100303030f0240d07503541c010a44c15000400702c9082042550010b80380510444040301c038202c0216520100341014841c0e0a021003081c1c000e05004402c0d0610b0f03814080582c8400382088040407410302d0561641001905030100c40c03508480035000022000e4064400780e004e41d0050500c0602c0081c01410700e03c913440b84080baa4001e50325035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 233570737 1250 233569487 233569529
    0x501030809040b0102070e0406060f1203080c0c0a20040c050a0207150e040504030923060d0504170708040e060409020616020103061206140105030f0604030f020307060203010b0c06090106 82
    0x2010054a40c0e13040d07114405010801040480040d8451131103144041401410181400d00120722a4846030519007140204000290802d400303680c0940000d0b002c1c0d442d00c4101e00c046213040d0711303901c0c041c1c81c0040c2d2032041c917844426031341c0d0752860300810303a803e01c44a20040c108690790b10a202014005811445041c448c0d491450010f1241c0d800381d00e0f03c2d50400f4154800901100e0f01618103d01041600b00104401d0307008280c006107030708001d11081c1c0761010754004200540304890f4a1401c0360360350000542080054010a4200c00100c110142c41c0e06480c50084004c0d442405030000103051000001c5007450709004552807240d001d842c59080c034904044d0111032545103c02203062585502d800303d180d2846404000880d4010180824018041d0855001c1034006070000b42c001d8210140764915030000140e5507410550500d010b074540c0585c040201c1c114004d04100a05a500010000030202040b40140000e816008240d42e480d07100c205069080380c0c800d11800740004031021002202c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 233571987 1250 233570737 233570741
    0x32601080604111302030106020102090a08010501060507030804080c070602030703080105150910020f120a030b040606050f03220b0a05090d0f051c0c03140a0e0a060e0f070602010501051003050103080904 89
    0x350090140920f40011342490010b0141d8000f41c10050050398003180520031441c1078500700303005040d101c0007003006504150009003288a1944068280403001000c50200240001120050354807001503980b00380c0c5402c002900c80e40310013000d130006400940041103e00c9c0c01c2e00e01d40d100620340a0360314500107462f03080c800d15030705015405003540a0728950039820401444403130440b10b020300d5002d64a40860030007504882d070044040d8061782c074201c030a20140340c1240c2111030500360039a41c1c5841c2c0d074803100c00d0854401c0c20202e140d9403a103025121010040780b41340841c005d2000c40f9050105560340c1a40c0d82e914014002c4000000f2041480000d6860180004007402800e485042c00303540e0346010004181c544203803c6000003a41c40f1740d00042405007500464112a0600702480308080c2090b203144c2e1070b1848200038150580d25500c07450031080070000d802d814413801c000e44200380c1c0d990070080e009000921503d80a4445581d82c040e441c0c0c80b0b40300d8141078075401040142042c01940500c80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 233573237 1250 233571987 233572013
    0x10501050d09060219050408010c030b03030301060e061905040f121703090c19030308071e0e18090a050606031f0c110304031101090501030903050d0b0a050d032601080604 75
    0x10b8007582040068117074081c054100c1e690f4401794641c1642c0364a082c8080f401c44511524038803c00d45001c21038140b0f903a002c4212411501e0601d0916610b1a201c400280944555908225192400c1048008098111015104440d0b00e011060001541e45854411041e0300c1000140429600040182c195100c80080d41d0011458022220b405d84107a020411202802e40400003101c11044104200350780203109503807044072490484a04a000782074003519000420356002401101d00d8201c649403202500800901038002705200e040c20721060741c9494804103003080d102c0d8061480011050308001404240c000c042074075900f0054068203039000204000d14000080203818450450f00360310401c050400b96001e5120402d500c6003c10000d88404000e501030350525003420f1400000c240c02c02d090718034401c5c03c0340b801700f840d210031000a000e4100e03940010b540f06a6009010080c5603000304a040000c0c03075815992280c08961103820350b004400d101d250304a5100400003000201d000c40d00403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 233574487 1250 233573237 233573243
    0x109030f0c0305031f0506040b0c010f0c0207090903031b03020d1a010c140f03030906070305070e090c03070e0303130503011104031212183f030b0a09021917010501050d09 75
    0xa85103491b400018140c1d070040c0d0008107801c40101d81403400d110280701e1070f001082441000c0180c1d00040402a4940d5900e00c50b900846170790b2415401814040d0f00604002c5149000d810303044103000340003400a40001c501b0b0740c0d40314030f4070380110090300310119420348400c0141c580f080140903955980c050109040c0d582e1a403401405181c00d0320b104104091805201e81c03c0103001585041c01c1d000382199401042c0008000d9404481c0d10740b0707114200f845402513212400140d495555040548a525007584616058440083e11400a0440501700030541d0030450007030150301c1540b514410940180e0202412404811030300300c6680b070003140342c00240c3c00c2c03200e0082911800c02d0002200c00d6004a0f054031001807d4003466044080d101681600060f990b500760540c401410803803100d28100c5020005250ba50030011a01d5552070208000400d04a0340c259510f001c0c0742c00c001008005034510201094201054860800201e10b006040c0c03001a5a0507013008030040d801d00103042d0001c429 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 233575737 1250 233574487 233574541
    0xa18080709110c0d230306090408071a012d0311040203040f1703070e030610030b1003020a170f030406050901050f2104020f040c080c0f0415020109030f0c030503 71
    0x102150f82c00d2081140c0e81180780c0f40d5505240004840c1445000413402ca1000d0007000c00411031a0340c0c5042065800c1600101480c1d1184010319004000c02e070582c40071241d10488500000d281c102010001600140c0c0160200300341c1d05000000910700440d001c000c141c2ca156409a4500d4203203940030b19441030040400c410040e000351030b00e00084011450700002c0020010030041e04540002c2c042c1140c1c4001e4006004c1d51414150840c440c5c02c050000500303c40704600400d0b50240c840c0c10410241d03800422061030b050362400740c00c1c002c180e1410525018003400705050a95403001c0241e0382102c015440740c0c0c0c03500c11907100440b01a8444140303081001410b22280c44100100701d08042c400c041d09181e50024103060041202100c01c480344140310380d04141d075a62545602c0010184c00281d0400c0482d02c845407600108031074040c54003ca0620380848601030101ea0b030540045101d60f011f91201c4039a000c07030403001c0300c8640007040d018020843c1000810380911080c00c08905452400c0c0e41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 233576987 1250 233575737 233575747
    0x50f180714040807060f09060c02040b03010e030c07090c0207030206030a0f0204090905060f011e0b07021503101401020102031e0a1b0207030b010b07050712110a0b0a1808070911 78
    0x381c1001900241c00c82c44050b4480e01e8288803042d00808601c08860040c1041d00200c0e2800000601112807928000d000d9138442001161035142500030b5001400000d0540c0e480d0f030300c0b044005075224a036118815000c1e04000c08080050700201e080d80a40380c01401c1d19141d695501c100102a0185039071103402c02c0d41c03c110001d1041f00300e100e10050f2a00c101d018088500307202400882813001a0000c1c81d1144002400305003032190000b000d412982e501c64030a4803000701c0d0000988a0251501081140d10000200162500501c040c1d800303640010080204910744200128201d0100322456203200c81c648a130b5510075020306180e594050003468000c50b14420103402d80750420600720750403001d60311070801401000490714026014040c05041c81c0e0800c4016103400d0382c0d406152068403920b02c5441040301c2400114040801108400390000c0220351b540c1407101e84a510004804001400d100b41710003280c0881240d0070100c0364510010040c984c102040e43c0004c3c00f044a65100076602000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 233578237 1250 233576987 233577017
    0x61009080d05031f0501050d0c020a0611070c0e0c091c02150901030c0c0b010509071107260c031b060c060903030402120604151109090412020106050f1807 68
    0x9200c042040d0b55503150b01c90070500b41c40c2e9000450814908407461030140700340f040d640d2000603201c00c03842d02a4041190118150164240040003030301a200381e0401148124450481000b0842c42c0c1c490030200c0300c65580c030492020807400035500410550781c02c00444e003c0d45400d403233103100c1a40c5040103200c4400d43d80d002440c07121b4a5a10008500d030082800c01181d81c040c0b00b5020300030603608000300d50a0061382d8808006005000d4644030700c0340d0b0804282c5451048104201031900542222007803929108110070204992102248411100c10995000303080811107080016000d001000d40352902c1d0062240c1301d0300042c1c1c00c0d811407401d22500150304000c1005900803083c08001c0d603646d05050040c010210002119802d03941c0c03242e0240800030b610302807a2640880040000100c00c03020314441e04940c415070041a601040100501090110024142c0c41c2000d8a0b0000c0000642d08c10901040401e044940c40d80f051080007080060780d09100b0381a440300280c0340002010060740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 233579487 1250 233578237 233578243
    0x408030a0b04230103021219200d08071101090e04030c03030e0316021201091203050a0603080d0f24030f15090305030901050c13140a210507090b060306100908 70
    0x148848000760440f10041055003000d00c40d00e00e02103070100240a502c81480c1e50000740d81c0c0301c058010503100140c80d80080c1e040561007198000c00c8014a03a6000d0000d60a10106035080b20700180c071564070b90400da0046600409881d01180d0b900e45042066660365102601c009003003c00940030302d501c600125142000500081c00d8503218400210742c0710301540144103280300d0b9180d00e442580c1c513107401302021402c10b0819841e40042c61170041016600e039005000a01100e07070000b0460880030854100d195400e412200210b0001001007003141e1903410b842d00c0101103001c00d42e0200d0705012082c804035140580c244585409040320040781210a81007404a5000c208141d000500100070301c00b0601080c054150404420304480b03040180c400604007107154140704601c40e03100074071040070854030780081420003020744544042c14860300d5035070880d010350701d24412501800b90040c003003501c400610580b0100d1202502c4c550560752490148080e450045121400b0310040c0640020760300020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 233580737 1250 233579487 233579531
    0x10090c0905060f0403060608010923031303060c030e0106050105030a020f190201020307020f0607090513140a0204171f0e1207030c06060501030b03063607031106030408030a0b04 78
    0x81900e45946511714240a000c981c07498009080340d0341401c5040f0041895a071003080d003071448104082c0b18070101000c040c6588038140700c10b441c5081110000083c0503055000406180d410b03101403100d002c0462005088030101d0081c075000c52028004103150b0b9015601400000000c0c1e02c15524045140c202607000710110480300e00142e400004105032568148010014007070080d000b810781c0c1c00d184101a004815030302030309000704030604021241b11891f4020151001c0406c0001070503090202000b0042c0d0b0090050303c1d21009e54007110036402e600000e00b688454041010a41966000600180506001b000c1c0000610411300d40408403101c150003031840d24400e450306003480c166031409000356400c0d58020b506040c079200505601e51004141d8517808001c0300103e019075004200c0000489415416142e860780840c0344070600c1c201c001a80750300703a070301500240600702800c02c00c20070b403880104e40c010403409061021034403050040e0041502442c00800c08601d00c2400240f0300310903414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 233581987 1250 233580737 233580757
    0xe031e03100605070f080d180507060801050a0f05040902010c170702040b040606020604060b03160605031e06030d180509070e040f0b1c1e05030304120810090c090506 73
    0x40003040c8490140122040401044242800c2d03041c04110b464040170501610307030180480400003000420005d042d48900290000700d503034007580282c0d070f04002e980d900c4580100008192024000304a5103080b030f030b9203800c480c05400b006480c0d81c101420700018003001c40040b810300180c460000c000401d070032182031440300359032210360b20798041c0c0c0100020380b20002d40b039070300480c6003220500c00664007180e85a031103504035001040341e0851402103403030030280c02c50000d043d12140a01261301b540c040000c6000b0075441c81d0a40b8113041809280ca06207a0945185905510039000b00c2040b134000d2036500240140c04403208101965480071aa45100031100b020000d1015961100c50703203018440c4c2d401d02c4010a00c00c01000320414041411041c03000c50350600540540000c01c01c1181c2c0070b10341c00340c0a00c01c0c0541c40784600e2903d8425905c1d00152411075400343c1c281c2220003803920801c129071081000348850300040b8a00500800107090700c081c180d041044c5c2c40030200c3d094450304000c1c951801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 233583237 1250 233581987 233582047
    0x9110901031401180803040b070903020301050a0f0b0f030a02010f02070e0a0c020d0c121407060207050d0813030c02060f090a29030c030c1b010e010f050f190e03 71
    0x9400c0300c0b8a400c648640c44510848560700c010240403554900a80f030740240e02c0603400865403100c0d401a2003081d030b6540300943c11340c01c004c1040403000c1160003a5400c010a25014888501702c2400c210900300100300e0290035610418003200990b110714020103100c00c0301d00650352802d4440c0800d6480d03001c2144d0481c1140d031134107022100316a041224a440006510b0305030a030500c3d80d510348000e0583c0301c04510070000d100700640460484801111300090380810119521942d520f0400c2d1030b000096a5171020403a141c002071000c685503440d000d13003683e2640c4c070103050b03e072164204072054000f41000c030207820341400150340a880d81c0b01081c000e0300c02403981c0c0b80901050401006000c41080710304920540500c1404207460341842583d401040444590361100040b1101020440380580144004c1d800c1c182d00c0d0010800c10742c0841106183c0400a210560b5040178050a100b0140e8152503c0400c10925400c402c10550000005400030011f0b07919050024150107204407500c2d145c201506 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 233584487 1250 233583237 233583263
    0x10608010b010e01260a0e012f03010303050319090b1f1508130203010e03040902120c040605030a050403031d0114060a05030703060207030509120a0b1b0a030911090103 74
    0x2da0030240003488090240383c44040700f09a041e4503411140b15202c0303c0402d035a8280401c48481c282d070002c0690800200c0208610500c0700c0b6141d08094a02462008051031141d41250080400080741d0689405464051030340d02d402558202100c3c0c1030701078085d00b90b51003c02c0b0b40040c504111140c081c100840100f15241c021419013081049160b00c10b0800151020381841d8850f040003a05e0362003e400810010941b14600109001d01080d10390a829400001000701e910701441d4007501d01c00c00340b840e0042d4640d0720140320100920540c05810013284003031000074072031242500f00650003840783c5000f149040c00c01d184240b410603032065400b05651034403440e00c120044015103503031014084419907061843c20020a4403401340e8000074100fa500004c06405040c010012144485070140032540045a0704130415211180e130041200c41c0c03402140440d440e031f442d01e42d044810b89030150300700d0700e004010a000d038000c0c11030000c201c590380b18440a000c0140e94400e4210300850185903501044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 233585737 1250 233584487 233584489
    0xa03170d0506010e010c03050309070e10080705011b080306210a110d020f010f020102220810110f090a0801090501061e030807111c050c0a05060906160311010608010b 73
    0x81c880c01841141000724410089a6503a488640251242c0d0181481540d984442d00040d040c9070f203903007151016003e01001d014806498400314800c440007001555615a161001184c1d03000b00c0c841c103504060b0710034800e40049000000216080100204003c112690541c0d200c1e000b40001219070301c064200d0a0703e8418003185141100c0d141c001214124100b88040e40081c0b01c07440f03040d6802d4100240c51159282d0305001358106c0700540c170b03109501020890403250094800c079a42c0903c907214040c000c19513001c2e0f922805002c1c19482ca0081c228100000750b002c914003504007911895110384d40000000b01c0000030711130704142c1c500400002c1141814a012484810030411208061b17910000c01000401c1480065810700c03a40614078848e2001c56000050080d00140508103031301c529051584108000050081188082514596400351340c44041080074060035400b15040b503c20041040500408050b4142d018444e040c000510319924210320b0031070b0316940002116a54611190200d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 233586987 1250 233585737 233585741
    0xc10120623030f030f0a0507140604060f0b0109090b0a0506030406020c0d090311010e0111030c0a0c17070512250905010b070f02040e031b15010605070c0e060a03170d 73
    0x8401900248a8580b2000b8503940e01c1c810017102d80ba80c130401044d41c001aa102c1d60031916030303079003001580c0020942900d10980307030901510200e071070501c0c0c01c18660040c4000d00032088002016100e00208924200c2e95601820300b2081c050750080c114031000c00c840d078076040910701440c080c0340300503100d0202443c0304d031902440038900710510845a204100103910300380c290120003020300c0c0210894180a006850040d40e0f13244600d01c0c0e001c046141362004100007002c0910380c0c01081100802c80d501d410702c04005907940c01544041d04641c1c8180214108417129039141400030080b039103030ba0180400208144494070003000030281e04c980402c0030380524041d2038013509105244034a407410595900360080b0300c42800034041c60702c81e5040062500c5c107005a41b80ea4901480c0c0e1a0f003050010b04081d101d5104109005015480340d00114a440c8640c00f03550203182d111000d00030544c01c20710b91264911b03008120030313803244d081c81d408400504081404000c03807110190040d00e455440d554081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 233588237 1250 233586987 233587049
    0xb1807091406272e06030b190b120408130b07060b220905120319110306330a08040605060405090d0311070b07020706020f030c0c101206 60
    0x35950465004591210030031091075811911070094240b1410515410404d80c100340a0440c0781442900070000b4001d80541042040b000c0444040050f05607103425000e020b0300750301896030b07001c0c01802144e844100322000d0039040350040c85504c2c2042289a461041a0000d80003041407100201c0c40c50200b03c11030048502d060300442e100c00c1c1c1e892806191207005401c0341c929207102c1d5180d840381c1081c0032042c410020b8403010351418941c0d81c502030004850034004583c0348038520b45807044002c0c1060400080d24010180103104042c101984116424080c1d4001c0d0340b1058006805c0c80d400500091074010042c003001503c851440d440c082c00c083d02118030040c285030050741480d040042e110000319542d20308511902740002c1113400d003a0429400d000328840207107240c0030581400241038000070a80300f203482c150300701c42c0c0042e0a03500d42510f9001d198990a0b059025072070340c48071490b080d0302803c4415544e162000482c4d06103181d40095640350b40c81403405a050b1580d0409150380c1c44032084d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 233589487 1250 233588237 233588269
    0x801080708030d020a05070c030320010212070c0215030106030f050c070f060f06090e010203060307080a0c23030a15050106050702150a03021309050a050f01030b1807091406 76
    0xc0024030305441c1c15103a00c100f400b06030b0340b20b03400140d840c0124011030070b50305030540042c3d03248041501ea18010746400102e000b91000c1140e41400d0100b4030005008913201d032050344810240c5c51f160b0361000e0350038915203842241d21000145102d01c140100390041c60080425aa01050020303c1405040480354003610400c5134030800c00200c0003080600500c051095030207000007841451a510140c01402c9030b410100303000d41414843e90011078150041c1d80202d00c204d059400050340e4460032030340c0301d0300440001c062070740e40a810400540c0c180705500000100b00a90040c4504080c00a82010a46e8804035054070b62142000b40900780781c81118007600107400d00328940140754000405191030390860590403040041c21b80d41482c4a03406035045004600c100030b80e40c9031100e284c0741c00b07030a0440b44811080e2a1400003030700c0c101303501400350490760401000c42454a03042422070001c074540404a03901d118500d00003c8540251181d00074a0940c8405840d1238189001000a9440d21006030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 233590737 1250 233589487 233589493
    0x1090b0601090b0307080703060803040303020114010e0105130c14071b0b030c0f03060a03021011150103080a0804050f0d0905011403040515220c0e0a060f1802070204180201080108 79
    0x500140fa401ca0460780c103c080f500349400305940382c0750100c000c0c0125420001c0c440c080820700008060301508210b00786d085007008031a0340c0e82c860365840300c4200244181344d03008652940806a0948030707480b1040c1d80006162011b0081505101d07006540d0103400300301d0b41c0c000500e2341c01d00b1071001084540003600151075868503500341885c2c02c00c40c40c0a00312003c1030702d10000021450f65aa483c16040c021039000d040c184036401400d10203031101d540306003107020602595070003200c1c600403011001d0503240e00c00309160601c40f101a00301c0780d543c2d0040c41261140314110303c2282c0340e01c08011420008500b5580c48010310300304000101030018080304003040e2641881800b00058011503500e991906801c3d0013041680c894112880344424101e8031a95502c44200000901601c4105441a40c04083e0444000e48815480e03008403040703446802c1e943d0001003170920407410b8011110320001240600581403022175000a811103418003140303205a1000b00c052011942c00071080c1d0300502c516400303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 233591987 1250 233590737 233590739
    0x90a0908090f1c080703080117120307170901050106120e030909070203040308211503101122170604111909020309070801110c100e0c0306040501090b060109 69
    0x55140c58003a001989104105040c00103000f074503410714018105109180f0740740f04038075a04000c030032540600415000102e0041c008981d14001480f0504220341181c0102000890a541070030140c00c040c007001d01700200644ca9100c1d0b240c84007801c0d070040950900010313031540340c401c1c094202c0100c0000301041a0521100503e1101c02106582131024140c0700c075400d907a1180703030480c1140b0031900000c120800120790f00200043d110340c84824030042010019181c4c8481d004040d5140a40081d550705034400c0415000c50031182d04121038000f24a1446810a683d07880103080501c40c14004a03010710030302504114421014402d140c802d035890018101504081d19180d024551031440280182400c1ea41c41090001c0884050018a0130080454490030112604c607202c0105205401d41503090100410194410508403030800e0b0200004050138000072a0b020094141e00007507801d240a1b0113a40c0d001500c0600c4451320443c410400010f82c031030f051600460600018000d1030400c011804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 233593237 1250 233591987 233591993
    0x11041a0420090d020303090613080601051c030324061e080405030a03020c0c090a050f010602030a090515120c0a08130308010902070f050106060c020a090e060103030507050a020a060e090a09 83
    0x104403103501c042070f2403248900b8000d00102c0d140d48500307002140c02840010340c00995050002c10902070307850f0003094078a5039907104204031126149203034a02200c107030719090f1400039000341d100c071103840e14812189603a4540c0165012000109a000c0c10210300c4003400f10701c2901003481d010304002c0c1e5509010750a814907440703969132805444485402e040c0e0024401032078807010807151040c000000c0c240400d9107400135216010b082c0654061010541440c00481d1581c0003000303903079040038140d807054281c61514007040441e482c204bc05468218041003090072503034a0071803103481001c10804490740c42481010040401d8001030400004a65411010000a900110356411034070f02500c056240d00721400c1c4000c1d00103602e90300509035807031300700000f4440c0c0d00224910b100a00841c1c0384d42e00c181ea00c00101066418407c085480d81c3c100900600001340201c0c05020300794041c60841c0c0305e41c40b095010980103103054000102081003100e82c04200d2901040d80e55003e6200c000c107000540c02a5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 233594487 1250 233593237 233593301
    0xa031d0307031d1903060b030114130311010e01020a230a0309020117012408060a030206030709030503131401020f0c061c061e170a08030411041a04 65
    0xa00c0040070000c20000d8020198040c3c62180044400209200907603140c3c0a82000c03810101d01c0200d072024141140c1240da4507061017400c0c034169007003048203455030702e0848103a00c41440000450501480505007266450240f00d11a240c1c0410800140d0300c0d0b00c2c0c014090001d51071540b50390080307103a00584d01c68051200d401d883c1e80980c41d050205450516200580c1c100030005a5540c043d000400002800400300c0b0811410803400c0c41181d90401d01d0303040c11255400110340305c9801200c0304208100500b48a8011940840c4d60f00d040303910192a40c0e00c8500b9940090a14403090704491420f01c03180101100c1d441108400f4001401c5211000741c0e45a215075001403075a03c202d602045101e4880c00030310511310500c010403020414a501c5041c251180d09060540021501d403611300402c2900f0340c0088404101c8242000b03020303402c1e003a9680c00099100400844408401c2c11200302d0700d03112401865400141a0b05a0713000d640d000341400201c610007005007800c1d0009800744102c0401103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 233595737 1250 233594487 233594497
    0x9030717071703070e030d02160605090d0803040f15050702060a050708130804050406030b013f082506110a14091903150b03030414010c030c170a031d03 67
    0x410030b98803903490840a480180079468030a0b010f004400202c031070283c0c01325104581c0881050741407041c545900048880c0c1c0504d110190300f0011010001000c50f0781d5030081c55000303110f400840501c2d00c065954926039071041d04c10301032580e102c905004155406028040d4000a84d0008002d6850294001418100701816040c0c1a00e0283c03616410b1100304030460300070307220140c01800250358034070300110a081d0034461107540b481c20702640001d21924040b03443c1062040790400030114111503001d202c00001c0103084070f500070100171750304940817002009400550118622041607015017041c40a4440c000b1103400015000c0103060901908a152145070140c0c1e03d0340941c1b40c1c02d148000c0b40d4007200d020042c0700b0100344c4a00c008104003054001d50940c43c4103500a201d880d82c504140b55490145000d90601d5074805000102d29500c02e0680c01d044a001c1d1428081c140740945445030600c1e107288039420080700c00204844100d03014026600181c01c0c00900c10030600d1400c0c0c0081e264001c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 233596987 1250 233595737 233595773
    0x20105072105180f071a040b03040213090c0e1603060317092403060102120301030c030201080c2106120a05070504050903041a07140c0904020f01050f030903071707 72
    0x2880c0041034030009036402c148401403880e0101c0c4c01d90602e508410340d6610584c441d00003482902c8132418030301d1a40c001918100d4000f403a0f41c1c0d00315100e0b5802c100800c00d038009a00c924580d00c222013408102c40030f0140006120700c201c2707004070f41030907100a0401000c100c070503001d0500b000e0781080056800d070400c0300800340000000c1c0d110050a00010b03003005042c1c14420180b000360001c00c09404e200c03030007140141026006c840000d00410007a40160000b448050400b1020941c104090350141441c0c0da802500074107081d10b02440036a55147c184043d00c1003029501a041c10440d1030306000c00e03005055035648000b880e0f40f036103076600d06a03a0310b480e024141c000e94481020401588080003a50301070502c072940c0201c40039000561001c9a000020240c45a41c0030b800c2c800d010820101d1070707051080c800f600c9042035680356001d00c1039030700800300d8070b43c10010704008000e40289a20051070180c00c050024581d29921820000c00311540e19140b0100110200b000f1800550b051046141a5031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 233598237 1250 233596987 233596991
    0x9130e19110a320301090203030c060702070510020c01030c0306122003010e031905070f1103070e071d0303091801030203010606031e05090c061204051002040506040614041d070201050721 82
    0x61540468090003420000035023510011664462404c00442c0262090301180d0860741840d40d2203042000c50381c007000d41c19002d6001400c0b2012254400d1b00140440380300746c00c0c0071614994442c031040c002e190301d9509483c0f4048160003a80c04604551100c0c141c0d9404900a0000940070a800b03902c2c0d11484002c0425210900a81030b503450040c011342d856540c100415200d501e503181080d001c22407211290301d119006e904004102d02c14203042c4607000b046103546680c181c6191814480d100d601e014141c0b80c1c90f200500036052243d480e8404408809404520513096515510505080d2503a9801000074942072a5a10412042091903403e0744200c00801040a480b8800307010300b80000320051076007195000070000051340c65042d089000c0c6e031050b4202c808001e03090507510100d000c0d0707001c0d255024100300003c0110501c135212441500c05e40e003040c3c5181940c1d130201003044082710301194001a10980410542e00d80a00c680c603072190705410503000c10081440c02d521520707031100e0341050b419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 233599487 1250 233598237 233598329
    0x70605030a060e09030309010c0305070c030c05011e0b0109080105010312050315030604081b122a010219021002030402060306060703020a060c020601090b010509130e19110a 76
    0x4240e0b90041c400810002400e80300904044884a881e9801200c80c902a5820410f403003402d41e2191094610030301c80b41e0b9030710480c61540e543c00c0340c017000c14000a4071103649035440001443c84013066000900441000061038405100025121114650104819174540401040483d0300f4090340000c1505a14190b0358036a0f4004422600503004925141c041c4940c804000401002e00c0040203410007a0710008107101c4502800d5584180c00c818001608200348024560211481c100d1000040300e0424813003000c0d40308a0590072a0044c0c103000461002d1300101c003002d02e4051006071800300040c3c90551452400380c021807882e10010702814040c400024558045c11700c24481d021485a001c10700340b20040728202c0c02980c8580078010070003058030f00020106298020740071198825405010450075403100c01c0c041c4001c02c074820000910740114000039003d52010955501000c0c8201d00d50228600b400080c0031058240d600040d60b0543c1d003410740700d40940c650b2001d41340130700c406154070a60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 233600737 1250 233599487 233599501
    0x1506021204140a090603050a11030a1101050c030706090f0317010b19030207081b120a080f09070f0b071704061d0f0409060506041b0503040b07050f0703031d0c0307060503 75
    0x40c0c0310354004640b140c64005d0202c01c120010130f44c400c2442c002c0c0c600fa10742248607002c145d1158400301e0b00030f00d92400c0c0440606c4c13a5019101130082210120152410048982c440205540c0d01c0201141c000104001041c1007603000f40000c111b804222000070780a40c100310282107503115503107081c44440f140307440e42079586103e82c040b01c03611603001c41d64546841540d003042228191000c40441d542c01940c050740380038400d4800740c1e400c1c4c4180ea5229989a22600318041011601a0480e2442c0c0a0307000d012602d95012008407000b0040004100c1d52885c107401d08001001681c00e40031408502044104012940400201d1a110001c000b1400c44c2c0300410005811041c0d1004203600241025022018003805610482c801c0f801a034080c84004032407400100510b071080300c0740700425003e20210300892403044a8030b5000380c0604040340b1303142d40b809940105800c07071882200041c2d224240015400802c00e00e11240b03070085000ac2c2807842c91080006e40b02d0603e80581001c0040201c0002c1c04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 233601987 1250 233600737 233600749
    0x11190c05120408030d0b030c03030f0702040209041e180c062d05040e0105060403020a120309180e010e1501090c031e0b030d08060a030308040206120109150602120414 73
    0x555180300e181e582d50340d0b9484100392030350410302070805640d2400c82e0184581c05d020601c0340364060018041c5241c4485d900d8101e00390340090030140d801640c21700c482d0201e6140e0b88111242030300c0d48840c0c0e0f101d03004040e10000a07a4488039104004806103072280002402605110003543d040d410f00e481034032001d14000c2500c40b004188038010041c0c444106c141590000f006200382d61440d9086034140e0f89030b10510102d441580720080d004240d03c0d100f0814019031440c84412213200f071400c0700f8020764481e5015400c0000d041c4403030342241e40d0600700d40301b0102446401c1c1403a00b48400f4202c0d80b40a8120300c1120003052041540361600c0f218500403d601c030707a00003500a002e20202210070140121040c008007004501640030f0f20407010800b000358044e10201d03114200c01403a90100c1d40c119901115600e0000c1c204a070000010311183c4000040c200c543da002e41055040007611010790740030b000c514020b540c4580c042d5005440c0d1070f0000104038040710199050005040032466400c400704e15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 233603237 1250 233601987 233602003
    0xc02010e0310150f0e0f0c090102070906270902030c01080a0902120106090c0810060f09050405040b071b08030105040522080d1b0f0309060605030f03040911190c05 72
    0x101c05140c10b1940003540f14021414050b12845646800030b01e48829801d058098103441c00c0c12034500e00c00010f48000414801060070305410f1054450319aa542e0003141581c045030000e840101030028820303402c0d00c001c2c0160402129042c0d081c070020030b03643c000c242c50300311a0380303018100001781c40081c001020301e030050203e15034043c0c0480e0043c0303007000e0716600a01710390081100c1e483c00c0910403806075105115850203014000e032540c45c8030307180035825102c00452540b21801c0c01b036420070028480c1d07254410680708500034a4041d80c0b501d80713a58000c0c18000c00d800070b03810314982d10b51910081074840c0d05886c15141c0948000410751551100c0414000030030100c20900c801181d100c4003041031003805403e60b04000d032410320010204261035111400d00568020024080c0090440000c0c8680c014070303d01c0b8060304d0001102c94a500c0424141408100e5094044d030000804201b0181d46105000700b54488804050401c400f00416514000c2d40324412020054901c400c401408014049030b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 233604487 1250 233603237 233603263
    0x130c05090f04150603050a06050901030c1206060510020f16060e040513050102030c0c060108060103150b12030a05130b040e06010f0215010303270e0a09060207170405090108010b010c02010e03 84
    0x204290b660350070001d02910b807c5850003074803401e01000040301d090012101d41a2a03018200700803140c1000440401d10100c2d52050b5545610340000080a44030030541d8118541c0d03541c080c01d040503495882901e00b0301110200024002c100004001c43e0b40e2142e10030103140c0044801007155207a03580304d80341c01500703a44050240e500c00800d1000d0034100c1d000608800400d00195486e903a070701d0880d42c1e2144002d00c40948601080042601a4401903000d001e16010080442051701c0311844643d146030405280c01d00030610000d400764400c50010342d1100106404081d040c50542840c80300781203180c2c0508514107010f0450000d4010354000e2104e8000e0b0070b203500c008000742d80e6a00340108440d4000805108038603503e5482031ba0300d0b82554922060b100c40b0101d00e0300a40310300002800910000ca4181c561643c00d1000500113a9208141401e40382a420502e44880c142401c1001d81c00c3e06a000e82203ea160890581c02d990f08840e65801d03154090170302d02101c0030040086824418984040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 233605737 1250 233604487 233604521
    0x506030903040b072108180d0e1915080105091602100902190e0106110307171e031609090c02060103021014071101030605180105010302070204020c030a0201060312030e0601150507140a02130c05090f04 88
    0x52f501c0c2d03500884060490380211b403d40b070152115010320f0320034041300e10080010b07049805040c01d10140358000d00784051000c0c1c034110170700c124100322411582150b000f8a44a80c1440010007409501040b219400001070010710318000e100d035500b0400ce00c4a4140300344006011894001c5007140c1100008892040b00349141d5a140c0000701d44003502071070b690718010590703c04010481515910419000a409400408259080d40c08102a0144042c51202084202860358100c0029400a441000c0c441d0507a90070b50000c200c0090b058038071603004103006080d000410410100040386480c1169400e09005903224114004940a803103064a440c402d84000100104011f605500c42400c60b400703090841c1108846250850582d019400b05e00c290ba40b200d030040c0101c0c8142d041310460311156061040c0781c500c0640e2400083c41440006409640100e60764000358180061a0141030340e101d001040f914a91541c042d016000340b10714507004003041c855100c3d140d110781e0b100da0000c071044607030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 233606987 1250 233605737 233605769
    0x601020c1c171b010e01060906050f121c020615090405030a0f0221031f0f0504020c15040b2a0301061809050c090a0506030903040b072108180d0e19 65
    0x8640c0c0a010141c6220041b5882c0400005040c80140f244d00c050340c04c014000d50300c225810381040104a250400b42c0ca440c00748046000e0602e419403501802d201490b0090917691030000032551603d1540c4030042d0003046c01e40b08100020310040202c0e01010070b142064201200301c003c04031318025540c5807403000e192038400e40c80500c21070100074511404e20400d21164141c071945808101d10b6541c03042491041d440c9400744900c0c0b901c0d4000c2c040e402800811242c00c1001042c01840003081035806403015a1034030207000080804203841c083d49c2c031090000d1800c0d07112801c44c4aa0900c01403103010100991180e0641c019000707040140c00420b021036003070126080c09184070540740e10040e101480b50001d00000134407801e007903066030b11030f09a0101540c00c091030071018140c03e9124410440d81600303451703604040e60340003802c0141c00b10004d50b0b8012013840d0014003480c41c440c1001000c0e0140e8403018540702501e03844540002c280c40252810302010f00820503001d8509850b41002444003d402d070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 233608237 1250 233606987 233607037
    0x236131d011505011103070602040308040303090b07120c050c0a1410230708070c0b07060b040203040b0712230a150e040305090a09050f0601020c1c17 66
    0x22000340365680302100580242124036103402c980c0b905400c80c1c914015500308014941c002c042c003000501d2041e080e030313141c62a0369980804980c080d40080310070705000720701401491750200c021406081c540c245076182002d107442d01c100c03d400002c0c4100410400718681804c11005002d14600c414003d4169062141c5801b48904403d8603040400e0250801004001c619882540c0d030003040780d405405015400240c1812165030f0b404000181c030003620400ca038200140c044842640200041920640c40341e420740381c083c040d9034440001034070440c0140103020115128045503078111a10b0304108464001040c4610040c201c2841d9180d016524150030b45144980d00f40403910a48401c1001c000340840610300008080060191011040710640002c0001c0d01039001401000700c0241050081540d40400c0010380c2d078100e07000b080313000ba4141807090b10350b010030075464680021103280d040c2ea80c4e180300b05100341d8108903002e0054005242102d895240b00340460340000c100681c59072502403928 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 233609487 1250 233608237 233608241
    0xc1203031b0e030c0105070218090307020a030b0f0f010b03162a020a06080403052203080c011d0714010305040f0b09070f0b0f0301051002010f1d0f01023613 69
    0x2851003402800341c04940b4900791b10800840b0091540100140d959600d52000143c082d0f00003803101034030f44010000100943c4e1013a254500540c45107080c1d16140c40c02c2e008403039014202904400080d4118001409909610300c1940d50182c141840308221020100d0220356a020405104041c00700a0340d45054554410361100741641c000d030b602440b42e6503200000c595104007240e0290000300c0038800f440610f507000b02480003140b031042c2c6800703806032030351158002e07540888800c0c0711710b03075564111206080c4111001d003240a01c0001030f2500301d00d00840500c01405801d522410107076150001801c0042c69443c6640c1ca40c0c000440d803159250415206030b85000f039005100c1500d40000700000c2c2c00000d00211981d90035406002c40c250f9213400140b140281031204498155501c48084641c1b036485071140926000b1900310500c85c010490445a050202d21a000e0009900400a9002290002c428a031003d8a0f40c0802d0602c2d4415007a54991190340ca10010352040301104043c4030450270b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 233610737 1250 233609487 233609507
    0x109050a0f050117040816050a02040204090e06060d26070501050c0301050102100e0703020f01121e060f0b090609030a08030c03100602010b18070216090e0f03070c1203031b 76
    0x782c03103c4c2030002611600d2021450111001081c24904110300da004a070356000f10440d007845501120f154070103c1e070008050b60401c2c1c2204200c01d0f034a01041583d003c0030021941c1203030003521601607004054480c41c2d0100351940300d13010401c078091200d503140d4103a030301101c0005400c00020003580c00c100c4a488243c0e40700380319860051142d015200d129800301d200714501901048014802d00b8071716420302214291401341c45061000503000c00700118818044c1e019420302c1c5103080707807181441b02c000d01c0844506410103640c40c10002414040420214103d0300e92000444030561207a100400292900b0200100244404404028400500c2d03924002d5400361541d2200101300c0364a66600b2800c035004000040e6100c0603598584105100071402030360864058070541e10710540c10131040d140b07041640d000d00c5002c0c1c2c0d244004401481c0a10048403102441c002039440c10440d074403100b1900d040c40c014580d108801c52040c0e02010700a502801d40d800b4100c400700e4a115055070050614110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 233611987 1250 233610737 233610739
    0x403030207060809061b07050a0c05090a0e0c090a020408031303060f05040809011d030706050903010501060e100f0302070f030c0b0105100c140f0f0a060c1e05090109050a0f05 77
    0x1c0c00c0700225100b07006016a92244504d200180320302e5481903c554404408009400c0c2c4500040000c107000c02c006000c0c2c24045030003a000d4201c502d00d4601403001220006141107825480e0440e14580301ea00400c2c081d010308822600d4030b0f001c1d113a600c000d0000381300315031000403248000174803001035078021101c150860b40110020002711405080d404142c55003200e006081d1a0204604403080d03005002d411403243c00000300704100c0903030001180c5042c2003030b04600b011440115603040301c0e103801d006007800f400c21881d050700c04aea49640407900500001d5114800d10104402800e01940300f54180d609160304046001200200c505020304400341d0b0480503104803140c00c00100796401e080040c01e52003503203643c1c2c4555048507622500b80c10504e11019080038000d0030742c0303000e030fa070410040310002c2160300025041d40a03551611404076801e001c05c510030b01880c07820848500d403584072208081800381c20801e94461340c010048a00c1c0700d054000b6544107101442c0414081041008601601c1d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 233613237 1250 233611987 233611993
    0x90f010c110c030c010816140c0a02030c03010b09010509130602031501110f031e0d02030916060306060e04020d0e0f0d0f09051e010909020c030a0f110601091505030703060204030302 80
    0xa1910b0a03d0b03118002e2403180740c0030440b55008540d5150108034048a1030506145c0b403580110301c1c003d0400c00c0d034080001459158865000c0d50107602d001c2c401e0b20035001003280204009240c0c4800f0450071030052240a1065142d040000e04000d02d5500e04201300382c1c0280115034a00c0d040818020081108030403600084000c20026085540020840c42e10b240800046040c4051035940c84040001c0d4503165828400c18403c2550241150001e54001c01c03540000d081c0c43c0360440c0300c1020394129030b1310500c00c06082006c20840c45d034102a07051800d213011351300940c6e80e4100000400162810402c03680e821b108200c82120300b160b0108a1040002070795a80350940c04140c0c0301200c0410050040c2ca50000c0751411031a00d0260304400c1100964044c10b03c40750050b55589003104903004950203030301d640c100140521442c1e50142c05091600b055060036141f140328000595075503041409081f491503958000d0060b450505d09000f801000c2c000c00b101c02198482c40c04001079006407108401602c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 233614487 1250 233613237 233613253
    0xd08040b0606030f01051009090e012003072c0d150c050a08010b0903150106080f0a050c070b04020f060d1401050906010c030305130204022109010c020312090f010c11 73
    0x40b624808481c0260000703040c1180c240d082a08004450031308008103030030b0140030b5000103031162160060001080c8210000980ca11038191440c0b00d0019024014040d010300308100030f0501e400c290a1101c1140c170f41100304500960001034509801040031469000f4241c0c43c82004008200101d02490668a1f03020f00450381030303070030681e41f03400b8050402c400328000100502c849031048000d0450040300508640080c00c5043d403483d038880302038000000041101042040c003c01c072610603074121100780c81c200860305e8515104941c1c0c1c020004024208111900410199a10400a15101000100310341d55807161402c42600030711b80c8400f03080401c071034900005004d14105050a20500060311901145886039804400a0400030030a000d4620061211405600c0e2032010304821225508040c54078400c0d14003106040c04001d002245507818802044e04159000c001d0f601c0c0d1006240d551001070700d80c00440c505010440b101c11421390b10306002515003944c440c0340e20043c0701309a02614200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 233615737 1250 233614487 233614489
    0x9041a13020c0a03110313080304080c18180a02060c010902040501120308070f090b1306020c0a03200a120303060518010302011e1e022406090105040507020f0d08040b06 74
    0xc2c0c05045116800c640004080c600401d0140c01c200892485003c1543d03d809a00c4a4424a0b61202c0c0c000c0703e06603001040a002d0030208103c004044102120125600e84d041d051004c031031b180080003200d801c050382c812a0345108082281600c540c1e402000e0b241c552a018248a00070300b2500d2080c0c0c811400c141c000100c00e422151040d00c0071360141d58040080c6e403454800d480351801125413800300201c0b00d900240c0000d07420050b05840d0711100c13042d44424900360000f07141032910400940b003185005820800214056040f9047c0e14074a4501480c00d10504001032401041d1303446440d02041d82e202c0502050f0340740c1d00643c1604c1c4110f990300000441c003001c1a900d000240002800f0034624100f4080c1c2d01c49440e0040c40182642c6846810f488034805458589240f100781c1c45d0160b4040b00110280e8048035408200c480c0c5d41c0102e0303140c2c518040001a11225040c0720341801240e0311008128494802d01144001003950401c68114268a44d00140900d1040301c0c19205041500c0c0030a4103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 233616987 1250 233615737 233615741
    0xa03020c012c010e01170705090a08031c0f0920030106080f060606031302120a030813020d0602070602041d070806010c080307031e0608031206040606020303130809041a13 75
    0x2c51004a001000030940d45001542c0b00d40c1c1d00684e86040c00540c0c11070190b00d000098000b84540d50307590715a034860301c901e410f01110344081d4100340400d80043c032240d400d549480749007070003001400d0030100e260300c00e01601200420710060040c10f400307184503010840c1d220003005c03025211070a800030406075540c1c410454540515610085554202e9000724505d4a000d0001d580c00c5190035012079920109580041e611000e20400e0030f0b0103801615520080c5a0044075140d03200110b14401c1a290075160300081d01400e144000515042d400f0601d803091003403e5069802508200030411441340c0d4414400c984044111800c100044000c1c000503015440740005d81038159000e03071110b0464440110980c080c2c401d02c44890110f1800c1c0e410308250413030f1401001c00070a00300c00513540e00c800490000002050007050300b8095410b00c030081000c95070002c00c03a903001060302c00e140c21800751460700010500c030340d1a0280d446403e08440308120009584965060901181d07601c00e9100500000c40c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 233618237 1250 233616987 233617037
    0x40602150408130e01050a0902030f0c1c1803030c030c02070b071b170c06090d0b040230010e0d17130501021b0607030b030d0e010c0f0b010e010e0c04061101020c0a03020c01 76
    0x2c1710004bd1004149000001382c0a411410f13180b801d268490340d8407419090844440b40038203407804804000351000d0503018815034007143d03418038092210784000d480103955080d051103600d0300010005104410f12640140d031541d4412007000d41d1038042ea580e1900840c0f007222403942d10160241005104480c03820750101c0d94500760182140c4100300280d15145000d01d0020300c1030387c01025048900f20358010141c40710004003c0c0780300300005420400c0c001821910180070719200c1e94032001c00d06901a0300010901586d04030a85034030781c1c0e603640b60300c680d88580030800000c08660000c5100c543c081c03c0c90340c030700d01c407150740004550156803070f07460071800c1d2115021181d815412540d002880340b4401c443d542550b03401810074081c01601c40e07540d800410040d060a40c1c0e0054200e0041c0a1100720b151501d0041c403540c81380385280e00b044000c4041718421403090100b8880c1440b50500c000c2000e40542d582090884207440543c0d00d40c0c00c01075203a28103c01954005050504501000d075041002130b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 233619487 1250 233618237 233618251
    0x14160f0f090c03020c01050703050a0b03010b0f090603070f0f140603071d030a0c0305070801110c250b0a111207051209010912030f080705040602150408130e01050a090203 75
    0x512003614000000005040020707424081540030005503002640900943e40240c801703580c001607030729081c058002214240703201a482a4140300060456a40f42d0301040341e0280201d420807900c0d103a0030300191a06030140d0018100d641c0e4844c2c00183c464020040804460702604458281200c01d42007043d64842161190041307146010b0040f8816451f02c000404c211016049850030b4000d500c0300c2e401103185c0e0b40100c0d11640020010702001c0d60a0103000c0c104030642c45082d040a0000c0e51030b50725082401c012100f0200300300401201c0070204041c540040c0300c0c42c03400720764515405800500c2034100c0980c1259901c1032000216003060441d0465903c103070441c020f08040f0305c02c0c2414400585c0018543c5041100b003000102c1ea01032404c00f43c005076842a102c60204117070381603006d00000c000900e00e6080c860140000c003d010340110701c039019461402420340c0541e4940ca48050305001e5074800d041140e5844601064580d200c000756816103038121008040e05644018190aa02c0202c03441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 233620737 1250 233619487 233619509
    0x290910080a030809030f070521041a090103061503020702010207050306100b09040207060e16051e010507050a0b130201020705030d0e0d11030a060203041e02061c060314160f 76
    0xe40803d00c1002c540340c12110b03003826685441c43c1d200366140f2a400c8004140c45079000340700412713022000c403000030180c200d40003441401e191070000310006066505c614180c90302c00001c0d1010b490383c402e6200e60080d181d000247c024488204400400a40110900700d000d8802e2810118042c42d00280003445100800700c50102c1505005003000d59400c88200300350055000c3c40480d00150305400b07042c00c1d000c040f01c000c00216811080c42160b46440f0390050380282546039044500740046039900380852001e01303005580c1d61842c5032440c80c00118a0303000d0300400c0b5050600c80320104d40740c20800b0f618001d80c00c0701c0119454034205030301c480500600c000828400b001046250a054000d01c059a0103400e11b00070f8042d24002107801d102000c031085605035400401c1001b08141f4080e001e83c1d0b205c0004240380c52034500d44c046401e40c400d103200032401e0203002c14501c0508105411042c040c650040603e403490102044240c1e441000103858103040c80410008600d400740c03c88500102c403851800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 233621987 1250 233620737 233620753
    0x30203150610121803020a21090e04021903050d0906260c040909081b0a030906050f0d020c0102030a0e0313030809042301050f1e04020d29091008 64
    0x1900e40a40070400c1001071603c2d000f074a440d0044d2203290010b03860007900a8a9800510319042d4400c141c280c2100d01484050850b00d03810a9100344a841600d02c000c03408040d035291400010030b981c0c030440c4440100e02c0c0755503000c0200080812108440301141e1035401300320751030f000c06171001500190650540c40b0030011404551041c2c11030117811000250030a840d15884009400613140c0005094904400c00038003a46030469480e12400604840005000340c1600c44c2e600a0040280f4840e0100304200412650080300c03000c4211130070404d2410045546034114294903010f90000c0303440181903450842458003180c40403084520b8004525407102e541407c644d10504260001303810701d60461b07610b44180140010500c0703d034800c41078000754002d156251a0070401c8c0e01e0b40325008640100c642e07042d415104400884008040c400c112405a02c0354160242140100f0215244115803040030f604a0b1107211020000900036901340da40341102d0780ca9460382d9000fa5094890400380b9800070740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 233623237 1250 233621987 233622019
    0x2060702040f0902060d06030c06080903120c040503030c0114010905062101110703020c0f0105040f0b0304060207020303040303260c03070e03011b050408011a0d080a170c03010302031506 82
    0x484094094100c00b40060410700035004514142c010900380250660b9a000610a02501c20700c2d5038014051131900c95170514001c10b040e40c40340a040462811120050003044a000e680c1042e10082c04c00507045070380355032010403a940640300c42844810590310120011030044924000c451240742c0141c4440d4802c4900d0020241c00c03412034131190300d15540d0340d503000800781c41c1d40020440640281e0080c0741c0106038030700b0401c03103c1c0c01a12060510008020820001c0e09071649502160302207240180c803035889042040191041800007945030000040100030183c110580307090036041655404040c4942d908000000c04040c1d4040108507014800a8034130351246403100104180a00082070142906020361210030b5060003100216801040030310100b0070920401084a4443d002a244001d03280041740c0e80407042c66018082c542d00080c403021040c042d400010305205120340f80c0c0018034105a00190a03042030104a01ca80207800c044c83d0450749130718815018120041600071181c11002d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 233624487 1250 233623237 233623241
    0x1211060a1e090203030909190504081c141b040902070c0e070c020906060313170c0f151302010513081b03060412081305030f0304030207060804080706021803030c01060905130206070204 81
    0x200404c03040072a81032061700345161802784600071403103100140e840301c1d84103481e1b034130030a0b0700f40101804528092100d07031940703907031403d5039004148015441ea81a40404c40c0660303600ca160480d10b60940001035076401c2040d131003040422104400c891841d2910340007811940d408915001941c00002c40d800320380540b410800031600201d407888a050085110742d5516034803184402592482d200201d002d0041c2d8200380301c4000300f991420b0207810360307240801490000240203410a52031000042a8208690007181110380c80300025400c040003d986000481d9100301c22020340058040c41c0c1c03491036030740c100081c10502a5a001e98105482402008110340f901001800305003c030001200b00004604140000c0c240804e01c441d01a03520324160030060300c1d140301580010100304400741000081030012050310107540e0700007000340c0e4902915491010b0310000303800481c0c0c10302002030b01420514055000b0422504334403024401c90340c40400106842e02003100203508041e0810420005141903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 233625737 1250 233624487 233624491
    0x4060c080a09050d03031b09120b09011103040f050c06071e0327030c0b07030507170d050906070807021603080f070813031704121211060a1e090203030909 68
    0x262408481e03240d0b0f5000003800c42e0f010303000c080c1d010070b950310741810180c40080a51012009141402d051840c5000c2182c1035080e85400301500e0403d55402041c0700010030b40044c40e922210315511600d904160070410640d1510300003ca4a921400c5081d602905081044e1140c8503002803c04500f98109580440d00301e01020b400c40c10801960841507100350120f011034048480c000140f50748034150f15103203202d0b401c5034000707202050080c400c68001a0f4040e089981e03c65110314154101e410360410384519000724091119030750704090030441602000510184101d003607680d1090242c41d101c0b800e0307072250004403607032030701e880880380c1840815031030343c0103044028000720070615220170b40c0c40b0a202a001412200346648001c1d03001c005201300301c14546000d807200c10f000d42ca09454221a5800c9449020004000314020440c1d4181c4c20300640845003d150600281c6105240030b4414100414008101240e4801c0c014883c0310031540030f200c1c072040b03a60f000e0002d5140c41e2001c3c041084040300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 233626987 1250 233625737 233625757
    0x905150f0d0b0108011d07030c06140c061e0709060e0d03020f010c05070c0806060904060504060b030609010c03060602070815270a0209060117041511030f01051504060c08 75
    0x101004240080d81c014881c42c0241036400000400406d60025004100c1d50310380d8001a81d403047c4818000300310b802458100300d40c594180252801c103e201148460f0141801c42c0034240502402c10540e1920010341154604000320340302c5042d591200b0a4516421901503a000200707101e5065045090104580001038001d00440b01d4682011380000c0c20340d00f10000240014001041d0481049954100c0b84054071a02d0094440d40c5410400310315003040084c000b84c0120b4440e00894280300ca258402d05000c40e0103405d0700d070645003084c00140078124884140d40000c4c03426400003102c2e4808984081541c07003003000f0b04000051209030401042024000030b50321800304101410300d0030000340f400c3e0103c60000140c0036100850040000e2076030010882070500101502c04c942c00d101c01b10315168402c1e03002c40310000580c0701c3c100490041001c88900c4070101c00002c28840003c9403608058120f5404a0701b5010f058500d104c4050300c1c2c0214841e05000c40c00c0c118507034000410201c0030348400c1c55 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 233628237 1250 233626987 233626999
    0x314010b03090f0109110a0602070e0c07060204050909070e100305031e1303030f1d09061e0a03060902040e03070f2a0b0a020d0201050108030a050d090206040314070905150f 76
    0x3000f4840542140c80114080710100407181800d4802d04111120000424150011b014211300e00046108044e030014020f0002c4080007950b5000c00001e541510060130303014111085a00d400c02030181d5a518900030364614991550009407070481803132428044ea135003e0059420086201414015007542640c0c0b41c0c1011401c1c4000c1c1035a000280385c4500940c02607995441d04000c0309030141503d0b04c0059228002c00711400500456110b08070380e2a00000161550400d03a88403c00c9540c0c410041603c45034402e104a00000c03c0c0a50b942004102600890702086000420075001d0351b80d04c0390348401004642041c0c29407012410b40303000d489068410300c14400481c419a0b94030395058016400503541c916021901080d219810428200d02030010b0000300225410103202640e01d0150103010010800005a08294243c2581102140c0d0740d01500d11500c440e228501010000c41c000910100ca11552400194201890080c580264504080b4040d9995800180130070f009014000c682c202d0307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 233629487 1250 233628237 233628253
    0x10c060902040605060a0f1202030103020a171002040807050114030709050d06021e030403030e0622031809020406080903041202090c07170309010c050c071403070f0e0a0b010314010b0309 82
    0x45c462900601c8000383c3d42d6180e040016102d500039000c4a0a000c40842c503520610040c401622120720712002d44048070300d5080e007001c42e61403561400c4001c0001101d194008540003640c1100050500142c1c0e0303098a501c20f100e03901d0f84c101d940300c0c0030403102440060607040c02000307141480d04103000c2c280d0040a000d45400c00c00d20071509965030801079003031440000000c00c402e040d0b0510404400e600d50701c01814a5051403455000303450341501d0b039142c010b0681a440400c16000d03072524020304850720b0304141000e5030382e035074134000b500300b482100080f504000004040a00c040300300d400b5031302d10b020b81158403285a024403018400c000d0954075200700800a090215001c20ba20f451101c0d25140301c9552464940c002c01c2c03d40790030708174280c244003003400489602007010800ca41954000300090070751510b0000000d1418110341e0042c5031002e2145008940000e81080f628810800c002040c400d03580a07000440446403010707420380720030711100010b203e8504100001c58000c2101811a0011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 233630737 1250 233629487 233629489
    0x403050d020a020103110c100506060d0e0703291302010903020303030f0a0b01020c0303031906170102030702060c0405060a0f120213090b03161e150e130b010c060902040605 76
    0x100c415034010002503440b0310005001c669060141aa0140002c03018500f4001c0400f80a82e403a03180fa0102d0155a803110001582501d5940a803032011014013014400c150050343c1c2c4e0b503191501c1740000d0f038036620540102c101320701014940310f080102081040c10150384028200701d003a4426042241003001c0341c03c0020250b1b40800c065800703411100030b03d01090500341488400c50710595000c038190f400c080c0f9800340c560740c040305903070780102d4540d000d105010304040c070360000300241d80100d514078082c884620b00850055014512035070701d6408443c019141c0380f002c450140924402c3ca61300513000c000802003544140304401000d41f40d810480f00001c0448a080c082c4d803c1002c61072030496901034100441e218a00a8880c01c4500342c01900a40e0210560700a008440f801880c0926980d8003107500c01c80a0304071800c0003444075448501c41082d407500000c207140030044400d44900d034085042c0c8103070603040c03140c1000424140c54048601d4215581d2502070813485800717990082c1d0390400000d407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 233631987 1250 233630737 233630743
    0x31213090204081006090b030703290f070e0405040803010909140316060f02030c03060910150801090c08060102061504060b07050a03120608150c09130e0d03110409020f040305 77
    0xd0a2504060400601e1380f60141d82142c1080d40142249414441040515240030440800b41ea820252035419994002e82c03c07414000c20304e40722a4988012030820402030106031040c0d00503012542c42c3c4855a90207400c01081d55400ea17800b4020f401d0800c0100441c4150b5480035190303a02c40c0e0101d80da4888411031940c11904020b880310101504480c416003008403d2040c11054414a03000f1400c50400f1000b00714240401010580203400c1c0202103a03114040310400401840311030754081c0da52011800c000e110302070070300c141d0400303900b40115200e40c1d50041000c03030700c1100181d00800071540d40c980403141d6440241121a005543c03494045001c0f034094004108190107200186424001e62074002d100c2400500400d000515092041c02015000704a2180e0001550401e880031340f00c0c0c0c0c02c031001c141b0503041d611b81d11005400c0c0a491000040e08404034a4507458295450482026000d0702500c030f420f24002400e90b001c1200340110b2034180c3c00303041c00c0c218440d0300c58200f54903992128a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 233633093 1106 233631987 233631989
    0x20a060e0301060806152101290102190204050601090812071e11040b180f01030b090c0f0409110d030e03010501121a060105130902190e031213090204 66
    0x1fa4292119101b40c200310300ea00d000f00003852000d880c114540440d0500c18030040c0704001000c50a40c00881d0603c0030b0405e441260082440302d508010080000416003814041c1d0004007040f022400c01805991000382d03221665181d0302c504080c504040207011030b1800c14124142035001031902084814600b0b01518041641d4640e031002030492580c95120301d0301d00010380d0810030070440c1d01c011581244c3c00394000d09803a0700ca864400391114003c07001d00f0342010819000c0880d0b42020f90001841030300604890900c20072010000303000560034030007907002030354074440f07003550340740078403071a401449001c0201900204654646d821800317500b0102da0352a908100141c8280d005108132580250326480d43c1c27440340c1c0c842e040d2400070740285012500c000b080d0340b0404c4800d07000f914050000007006005040da002c4042109069a20150899561401a0f000080d42c8141400900 = true := by decide +kernel

theorem cover : BRFrame.Cov 233453237 233633093 := by
  have h0 := BRFrame.cov_init 233453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 233453237 ≤ n) (h2 : n < 233633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
