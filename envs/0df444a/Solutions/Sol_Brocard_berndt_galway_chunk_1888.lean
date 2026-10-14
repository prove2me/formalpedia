-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1888
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:02:37.592251+00:00
-- url     : https://prove2.me/submissions/8fa0e752-a8d2-4cd3-98e4-f69c77cb19ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 339388489 ≤ n < 339568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 339389739 1250 339388489 339388519
    0x10c0201030b131b030b1807050c10020406030225111e090c07061d0303060607170703120606090e0112030903140a03030c0f12150807140a05040b 64
    0x5044560700e03480e00403c100000b42002d400c3d5019204060800d03202c800d00421822600404441880c6801442004c62503604502da50902e020142c0113202460140d0780c0d066081308081c40d040100d0360340110b940c800140040c11070703851350140801820703219542c02e0014040c481d4070480c00c90b00101a010010044580b1000d00c1c203003800083c2c0102c0750701c85814044891001a91208044400c0070641d000003e028040050034860000d26a4042c4d880302078044103880f455649000c0102001d0280300c0001c0c54000340041b45214050811140c85a9a84c0c2c406620b001020f038082004450001c608000d404100740740070b001c560b0190350b101420540560b00e8299820320000c5a40c03015401c0c02043e043c0400030a460f0110740110a072104020031075000e81c1d182c01000c80f695200c5110030000101c6041643d2503002c03031004842042190301140b41d080e041c0003201519101c0d4408a01b920030003000198141e0081a02c0941107401c85444400c41d1791030b420701080d10607081000750310042200e21111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 339390989 1250 339389739 339389741
    0x3070203030f0a1b0e130203070504033e040606021c030f060815150618010302070218010f1409041703092404120c081e0c0703060b1003020702010c020103 68
    0x30380403001d801c0c04a208041d001d40803c414072070785460b02c005812408001c1706810308810424131403c0500c0308529501d01102e00130030501541c00700034020060300c1442d0904211501ca00004061618028201d02407180710520070940f40040e00b40c0150b00b042d1000134010700100d00010801034280802c201c0001e1f003202103008206003400c4038a1180e91f9400400c4c0940108442406603544403400340039402d01921f8040b550082811083c0f0a0a04001908081e040d1102511b11083e0a082c091380340d034164800a202c210350a04600c8092a102000054081011421108484d1008888100d00441c2400e004510344100c2c1e000d410445c4030f030065125281524000c50f03005060600380d9400c0725000c00c00c9a4003160051000c00d0060320081480b00f40f01c0020304004208e949820850301050f00341c0d981800d0b6010304580440885465200030207a002c01038100c1c2c18080900003038551264480c0340c00360041100103411f50140ca114003500603070500900c02c0702c00181d0140c580c0c6001410581c0114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 339392239 1250 339390989 339390991
    0x10809010c09140d06020d060302030f0d0e0120060702030d0c11030702090403120911040608030a0c170403140303070207060203070c090c0302190c02010e040605090a02030c090d030c1703070203030f 87
    0x6030048001c0c401032010501707520207840d400d180480c0c01f0035850300e14010985071500411307140c11036400c013a00c0380ba2040d4215101c2c0403016000e003800d2242c1d41c0c0d0500018101e040d1100441c4c4140a04410002440d80c080f00601d01d000da010b0013003084041c5400704a9400c0c14032643c4020745c0e8402c1080801526101c505a0341c0640320340381445184c09011580320540d00901d1040392075031181031214503286828018040501000d034021401c0112603080100480c50005003e0508044140301e80300440740c1404070ba0240d60015420030300180d1040c91250350358011540d000041c040c00c5401b00f1018808000c9401d840d810000100609052020010007810342c00c1c03421080c140d00b04501034010203c102405214415034a501d00050100c0c0005001a001841c120748954074000003886156504402d40f81c10441c40c40005032241c2c0c4410085040340b090402c5a50b000c4e40000d013860405a0040f0b00240713035031040d6081402d54845444a6805000569580b80560018000170b011109020081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 339393489 1250 339392239 339392279
    0x5092d06030f0a0302033004020111071a0306120c181e0703020319050c0d0506060409090804030c0614031305070b040f17190210180b09010809010c09 66
    0x140e91484618250940707440043d400031005a080420b004036030f550b000300d517404c8614404601c003001d41d021140e01c1c880d00324000c0009040c80711030403105110500c104000b00c068039150710032110f0350400810038a4103400403941644a0580340000d6072481c10701050104110750040d2140c4158400c1e0300b000010880c0c001c6c0f00c1c031603c0e0513051901c0a01c1d44145285401120b1031345005a0740d040ca41c20311848680305096022282d4140800c0c000c424003000c2c11581902498240043d4640390ba00004002c1d1043e030307108109541c140420031050000c51002081180e02c107840d9801002d65880090306e51100301011a11440c030184001180c0c8188140c4641c22580f1a000b96a550b507150840c80034070b40c100390858041403a101e41c061040c01101000043c0482d00c40c001004a10800d4400400010600320002e020b202d05007110400640981850b08101d00010043c0745610340b18403140c0c59a8000814190004056002003240a031040c03003034419001e2107640d900300c1142807030341600000141d4504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 339394739 1250 339393489 339393493
    0x10f18030c05150420010306150f0905030d18060c150b0609100f02010c02120a030e0313060c0b0c162603010e040b1f0510030609020a080105092d0603 66
    0x7014900100f80000d28810b42c072501c0e002d010340c029034400c140c0340c0200d1450350f4140341c13030042e06000c044803081d000701605110b407600040000712242c00b110500c41719400340d80c00d88074006003610b2181e00018107648907580e00456401c0d05580b0785046901e0001c489000d0403a442148040c8840007140c1c0040980380c401420052604440c080411102c00c0300950302c3e00003481000c0c0c0c5200d00f40d4280140d0100c2819840281021040d502d85900c0d40d10134880641c050507690140641004000d0040d6100141c0f114400410141d480f070b00030f800b6015a02007100c01c040708070300240342c0444400c1524110034541014154280c520380c1e800f12113101716a110070701100081400d18007061284c0c000d41c0a010142d00c400303068185403070103480c90040078266008540c4e02d41e4542c0c400c00c50071000d0104803101240c1210312514503227015002000c07290000030b2031900001b47c070941c150704454103504a030801e032251030060351020b00c0158401c0c4a442400d860803030380b01030038201c0c50380310180035049100102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 339395989 1250 339394739 339394753
    0xb04050d03030e100929240604030f12140d050702010b0d080702040b010203250f061a0909030a05040302040b0a09020c060f0907050a12060e120408010f18030c05 71
    0x482c4c078203684541141c241546035101a010400041c41414010040d00c0c03500e00305412400044401d094000c0441030b641545d00403c03e0809030380301c07000140c0c07100502910794075901c070705017031102c00b40e00b200035a15a12800006000113205000744466a417805a4075414004405040c6014103c09041c4004641d00c0e05d0080c0b490342d4420002990031842407025545c0c80c030a610500c400c1c0c074200c40c10903040d50010311081c1040202d08505001090035241c41c51000c100c5450309054200c2441c1c40902105d01e084081c07444899862034031001c05504442e1a082c60741d0b44446a07589110320038612b8001403040c44104014200f0f0b0300900e01c544002044140100c0e10381400034204d0304007042045203640f041e01407084141e290700c80c1300d40103440100030306161410b100c00308014a41074403880091449107010182400340303079400f86030455000001d039640740b10312030320703803c050740290080c5482c3c1e519025004c007110b0388610454071400c0d581e580c1703c0126907403900d060f11020034045040c0d5241c000c0784 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 339397239 1250 339395989 339396011
    0x1030911030d12060506161b080a08040602010b220b0a09110301050913081b010e0f010501050f01081005010c0f0b0f01180902030a08130e010e01080f070b04050d0303 73
    0x1009003090340e82c16a842c4880c52080c0307440c0a080e285680d000501401c82005842082d4810540d000b500c9601306104500320340d40e0004240d0456850f44c07082d1890300841c0d0300807040000e03c0700180704072801170f0300a001c0b4941000030420302d0810fa102003004030145283c5440c5084a40d00f0030003600030008d00301c0c880c6d0b0f56514400426034001e20b81101c0300e000000b0042c0704500e4041c012981082244444009808241d520900c0c984134500440b0b0350316a80300280c01c100c0e5425041180c100090070280d6050f5610690714030b010345001c1c010b443c070824501200501e60b501c235500d0f01c0d11840211030700f8007401c1d01d4180103444018002800782c440c00e01a12641c004115400c0e05240201020310751f101c411740c942009101c0f0300180d56021036072581000b6a071405640e0001c3d4003a18190800d00d965964440701030720040340f1a56038800480341e12004000a0031100c03501c00346040355110030a0f510280d0b010040c040e290002c40c054407a0000d07044c0300038000c60600c0446112080e10a00380060340c80000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 339398489 1250 339397239 339397243
    0x1502062d0901050906070c0503090904080d150501030608010b030615030c090106120605010f0c0b071b03080a0b061306080a14130218070e040207150606050a090503070506090103091103 81
    0x403150001c440c0e44400911003070b400300b084100d602c501d071403519205015142c0e0b103042d207a202d032582892107003903064042400d0110320010cd6004035114481000250b0b11250510301c240e15500c00c15000c01c0c607091000600c60302c180900b816485004016242c0b586d00d0f08080603414041703810b040d07014400d030039514078541c5540503024040c1c0710588a08035000e08551b00072058400c039400507410007800038000381c40d07160490158021282d101c84020202c3d910a0030803508182441076100c540c0ca107032019030042c190050301e4240503070600ca1040c0010350a07072007031060500c1a04500c2e52070445036001002480e110f000760540103041107202245e41c0b28852030035049018141c1d14080801a032a91070400c40c40e00c1c0d040ea08241c40322a0a051080c0b40090014013002480140741740101e40000e410800c01482e0000c4d0440c146842c001081542d1729004010915044036180b0b4010615203e00031605140c0001c9540445000a01c950320341080540114098204214101c94000c5846404051541e003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 339399739 1250 339398489 339398491
    0x61a0904080d05150a0308030619090e060109061a03281b0903111002030409141b04120303090501090203060903130918060b0d0503221502062d 63
    0x141c030001d91608a002c6801c0210f80c0041d1003242c008541c0031078000140c035008008421240c01550882d100d80d22100861101021524600d500421451002c280b201d440d901c224601c0c200c840844840707a80f18480c03082110214002c0c3c00090302045031210740f221030700c4001c503444041204004040031020b6204a03040010703011901c00c0a8a41808884200001c0d241609850481c64800015071650b10b078107070220f04140309103014001803100102018020001c8070001e0202000400000c10242d02000c1d40305003e40307400d00b00700c55075415007558841c52015201030796403600c940d14601025640c254014150301c40100c40654954101038056a800c1c418240319000c0100075503920480c80b40d0780303418550325070814800d41d450960b501001207200306c140800203134441c400081090701c1400080d600c108861009001e40300000f200c0c41a446007a08120610124041900585803100c040c0c0c03003c6c1026400c00801071344174100041c03040d40d050313a440300c201c3c0f40150100e01e10f0340c1940308508503041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 339400989 1250 339399739 339399743
    0xf09060d1b030201030506040902240705030c030a0201060602150c07031e0201200c0c09090304030c061812030512100f0801020c070509060d0f0512040303021005060108070903061a0904 81
    0x950702001c0081d543c05005580d400f813012a03040101c40c0c0ca80d030000c0c84800301280308800002111300b00041100205084540445e0850110b80c0c54001d0355038143d980c0c4c0d014041007401942400000100140002245421a0b0b021920002c0039903640b2200300a0703800200c010760400c010a00003008100d110300340e08070050f41076400800d04030b008024510f10b802840e00a03106180c800c000440c03050b0000300c0c4219500d4403c032031180343c640b01c104d0500c0c03450003550406403485510045c001032841d0803001000b800d038501340e110340780d450340c1e00466104003461240c040c000c07901c201301d13031003690982808030341c2e1010119940301445a103441403070582a085401042c41c5030750005006810f000c040107002d00912080347d1010b0b03185020804a011004800801002c401004610300e04000091000d82c21300038030031004545641e92410000e40c2c8190102c0303c2e010302494900410300315482a03840c1440f840407920744949503031850740c0c1d13100140707490700104902208981c0c1c1d007051592000703001c3c0e001c0c1e4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 339402239 1250 339400989 339401033
    0x1902030d0606020a0b150607030c0f06052d0408090d0309090606050d05100b0a1209021c060509060903031605310f060210020a17070807090b03060f09060d 68
    0x3104e80c9400030611501030111b1014050005190070290344800448065030391600d46000d11804a00e04000989440c5030000c0c00d0f02e0a0008020017400b009115026501a007004642c0044003541903110915055a0181260104010030501403c0100c0c00c801c01d980700345042c55465a60b00d10103411140d06030440c80010780002642c44c800f4006015864101c0c400014403c14549041075003105840f070b003078091007402054800c07162481c3d066804140c085070003408101d52804104070b205906500c80800300e50080c81c10001c074000d210000f58440c031501e47d0900540c90364545144482c010241d0010b04820000c040007001c6c42e600205c5155030300e0202001c1001e4280c202207800e00311080c00c9420000180030800340420140c1c0c3d0025075a0044000010016a1146110b1048036000703c8090002d0249604106100c00e2903804604c41d4810500c907600d10400d1a107035148100a03100a41d030255014000f44c042e9103443c035006190641245005003130144030f400c19500c5134420004030700950082c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 339403489 1250 339402239 339402253
    0x2150921010c0908071a04180b090a02120103081303080d0e1e0a080d09021e1e091815040302030703031503020d1b0503030d1a030a02061902030d060602 67
    0x41509016410b680402c9080280381c803801c01c1c1840340d548030310b4401c0e03520110302480f84004110000d4200c40250811082a04038481c6001c00c070000345c458420303114014110040060408000c910036140c07210305452035184941d10707544a41200d90842450351081c54814000000003514020040004d1f031606040884e00d445c4104059042940c0c02c41544000103030200004c0c02e000001c0750141c0c0d1036600261040d1920410b8204600070241c0f010000e4109006081c4400241681c80320750640f58002c981055440c1c51001802c841040c2c080445030b0030080400c04107285800c400c003031658840403403085030410210400c07080e480c0001590f0a4026810015005041c564580215078815800342174590b1058910350100305c0b9401d08407805020320441d102c4240700320b011004000020030340141125114991065400010708219400381180c04620400c00c10b40d040200c0c0d040381468000304880e04200c0c0d940750100e03140410811450440c0020880c07075000c1c81481c46103001401040e130080c058 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 339404739 1250 339403489 339403549
    0x60d06080a1208190c020c06070809150405010c14010b1011100507050703031505041a1c03020604080d1401030b01090b15090f01090902040801050702060f06030604021509 75
    0x4246802d0b082000000400c01c21140d41a0b50b076038200d51040750002550100e107a0301241800d4603a0650742c2e201000180e00802d115604c0040d041c00232049034034907600c8c80c4014003020745104a2041601140e15100c00c0340100c0c88040c2c3c8070400588500c000b0034120440000101c8400d840488000441c80390000b20100103000c120a540302851300f0700420990520300c0f4040d03d1400b644070001e0815407101070511420301c01e420308030001c09010384203121000f82030700c41a201200700c0e042d1034000c4000559103204080320703031000d40d950750305500501202d85580e12040204c0d0300c2482c0c03540c0800e0300c0e804100080c6003486001402180107400240d03403541030a0540c4192601c1400451043d80f11700c13054540700101300101c0d940e44808031880000a14401c006882c1c503180c9074010442140701041c0081c00400c190801c0c0c0c810101d903802d42e142c2d543c2d10a0200c1007076005450054156209100103001400d007003480b1500007041c080a541400416400295a00c3c203083d05071411107401400030781 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 339405989 1250 339404739 339404753
    0x2a09060306021207020706080118150b031603110a0e22050f24060a090b04090e01060b1608030402063903090303220323060106050412030e060d06080a 66
    0x341196207817001d014428640540200545418069060000824203081450301c0f0154080303440503803240d0b5600c01840e41c85258040541040f682d100001100c07d0b0007925842c4a0721a2800013041901c0c410300341500c2040c122030310039810b0442508420122401d952116200c0c60300720313010080f21004601840c01091807030f04080085c0025000881116800300fa44003a500280615203050f10783c51f4407100c0c02c0324101ca905106c3d5100c681207600c00a008220f001c000d4211546000b8a00020b000740b07a070b40e01d020101c610801903140300300e0078080d140000003401e680040d0741090004081505208203d03103408100508010314a800c0105244c108050904641201102d152180c001d141001801008242c42e8802c0b4004030f0382d00c01c017501040c0001302d10062038401554200d1050308c1c030700c01c0d024191901c20b1410300240c2d100340700d203170000100d41d0320402c204c030260360007602e050a18512642e810f403807031400c15020f968071990600203485403016500c01c0340c0050000703000030040c26000b0f04201d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 339407239 1250 339405989 339405991
    0x10c0b040f03120b010c0b1f03030507050d0809030a0c060204090515130b100e0d0c060c0308011203090b48010203100618031704080d020a2a090603060212 68
    0x700c0ba402c14001d007400383e1b00050761840c1d040e00410300d01860790300c1d032202c0c0d001041c08040c0f242c41c0c0041c11a020092691010160181c54414411144001c01c0140c0645081b0011104005598010000140380910a041010071a4494040541090f8849040505950f42119506c010300010b280c648414034001403400d00b1841c0c4030404101c24125600801d1a01d0300c16408001408100088038011b5142c20540401d01c541148109520310f40303620b0000e01c006d411030300c01e030009080c89002044a1045c001074044c030b0341d4142c030380c46503c07440c208010845400c0105140c241c0d10801d40051042e1b4284085031620010381944102d603200701c2d00f0f50300031200d030803483c04c1c1d9103030304c148204003003000503500200594040d0306241c1000002c0500c01c0d00e00c012030b034200404141820551103015200704010b013059580000a43d5589101490201c0c3e0710401d4000103480800003001d0243c40ca108207a40d000c3d9440c508640c6098961941d83c400706a0314039070700446040d54001060401c000d034002d086 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 339408489 1250 339407239 339407267
    0x3050d08150f150c030d0501066201060e010318020609040b030f0d05192d05090301150303030507050f040e0618040b06030d020f120306010c0b040f03 66
    0x40440c07221024042103081429078003143c411040060180e492040030000c0e1313803030941c0e5004e0a009039078558400038003160041140c00b070000141c0303803c2003034904144030705d041d4041410b100552885600d1400c2c40401e1404c80d07610b10400d04c42e486854a81d45c48080c09001e421240c440181450b451400141200d890b1481244081c0c8103e81d54070040c0d69010072079a22000072600444c0380360341c150029081030030180301a00144a00364007414001c0d00f06001c0c010900c10f820b501e001c00548540c040e00e404600c2038081e103076150003481c01c01503a510f40c800b54600d0111071801501b403804040200b800c44c1e05007040d80406a120040410405a041c010503a0101440c03030100d08187e801190850075000310b000d8510300c00364820014140b502c0c0d20034850118070b9240c101c628a41003606000002c2441552503034000c4c0545000580024000641d04110000b000020580b180702281c0f140a640c20150a0504000c0840b4423213010940007400c1c00d015078010f40d900d800b0030340d061030003a140b070f01d0317048038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 339409739 1250 339408489 339408499
    0x150801050909210f090613030b06060304080306010309060e070902030a0e0a020a0e04020d1e02031b03100e120309030408070911030718030803090d031a030a080703030603050d0815 79
    0x108071042d00c490001c80450210400d9240c4c0318225000721a255010b5a03102a0300f05602040001c20350280300030726000c0324050707811a6019142c540611083c1c5c8011100640070000030000300c0c0d0b02e548683e00c40d021450142d00300040d00010100040e0810300140d0181500c07070b4020040c08503a100511483c1c0100307000200800d40d058032350b4040f6144040d184100c140c501240800201552200044680340301e900ca0318243d50b035804940c042c1030b40541500142e01034440c610b911b2b0810703140e0024900c13020300000c009003802c80d44140030201922141d04107000c02d000b00f0414800317082c0502e0145004107a8440a5a00c45040c08a8145000070a0740460031680c1820303044a46101c20500703c0740c2296080c0b0b031143e1000c0c107401c2d0b0011401540d60004050f9540001003040e50072022501c210107442c2690144a10118080403480100d0b05040055041d0414a8040001407081c0020801d00d8420f0a022408542c0d03a161603081513140700d010000f082c417090400c21001d980381c2c0e21104601d130840d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 339410989 1250 339409739 339409753
    0xc0602010902031b0d170d0f09150b0609130b04230708010f0e0a020c2e0501031101271d160210052a071103030a0509010c0606150801050909 62
    0x2000030791680c00d4035809041b02400d001102c2030008403104480e0b0320490300509124040340e0380d08882c001c00950340c05503401d003240815044c0f0b001240c02a440c01c01001031015003012841d1007000448401e0b203400407080303540c0b0581002180c0b11409000500d00e080314952841040c0c2c010160f00d4844001d01c07a80801c08024010710134000100410401d65004100f154055950624000000e1140f1001d040381841030041d8140d020705100300d2812107140c54445509da04c0043c2914005480c400c1c00020000f12910003084840d522a100580741d403400080030840080a440c40d000b400c0040d41c100580d111002e9060036191031410354400d402000440410f09103100c04100251905001c2c450b000c201a01c0c0c2e4082207a100784a4251804815550040c40c0e4900b01c010801d119540215001c44042d4903144c080542490040f040e03603c05030b48d6440e07061500690000445203e410402c0442d091551024003240198402d201c0791108401500e90400750350601e41040480300006180c614294800360b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 339412239 1250 339410989 339411043
    0x50307030c0f060c030516020a0b0304260406020a020402090102150c071709030d031e020a05040806090a030507030e150d0902040f0e12030402060415050304060b010306030201050a0e0406030c060201090203 90
    0x41c1201d034087d00d102c03041501141c8510000b0343c1d460150307128200740380d00442400280001c4042102c520103080c0203181c0707003840941d0400860b014038410b523000740e004107007841c016003480c0c0c00900780048144156090072011441328982c3d40e60544451020f8100862134a04100140068080400c1d10005284c100001e820000790f848e1003501d803070000c1503110114015100d91007030212001c5016000c0a41d05d95034810740003445504a4881c20300140314036008500ca035000428180185601581d84c1c40c508007417030b10190741c5411841c804a4111000144558031031448101820520380b904002040e03420040c0100410b030b807510340c1c0083c415450302e1031141d2600e03400598200d07501c141c490029241d9840780000f41680c040d5605c40c40041c58800807c08040c0d0b8880000c61145100301c40400001450200441c02c60b035060000a01140040190f45642c0c4c0c040c0d803800f01107034402031005c034031191a603030341349040c80241d03200c180581c2d11400301e072046207010710290100c90b00e40080143c3e0b080b021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 339413489 1250 339412239 339412247
    0x1f030309082a0409030c050303071106010b190f0c0f0b16140405010309060b0613031a0f011a07050a0309170109020607080f0d0606021014070801170304050307030c0f060c03 76
    0xb480a45105540d180141e200b01409074404c03030075041d08402070b2612483d2003c40544082501d50300ca03c11402480d00100344240c00d40141c501801188c40c00c04507200d5244802d4a01c4a09010720409208607505000b00280ca54041029010303c034150444203800d04111002c00d202c05090080c0034804042140d1500d203800a09403000c991091901080d45001e03400c01400902c2d1004207035801c100f0001746010001c0804041e44100c0b8800c4010508142c801010b131310744d40c0801d0b070705040042400300040000c60280400c013900820201461850004c85540d25450081c104d01c003240440c08441c0c0421246c0e18121102c84420341d0b1130002c0c0404c0042d0342c00038505110b40744005100c800c0100d0401d1038007001c18181e03450600107003820460030f80c4030350010b55186008981c00104a040a07601055600c0506049003c0c10503500d504829074200400400d203d0380c009803100f080c3c44180030008056800704204801507024107a540300b11414501e2260380d120058008000740150b80610701e0000c1e45c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 339414739 1250 339413489 339413563
    0x403030e0418150b182508010302090705120f07020d021915140f090105060d02010e090415060e0907060c0302060f040203070b0a11010f050108030d02031f03030908 72
    0x4030800e4071560000c6071103c50001c4c188140401d4100c0ba02c0d05031002200c2a0101e907078042c280122011800407500001c40e06032280b4540c204000035010b800404c01410070b0490103420901a04000d800c206226659a042400884210449016810504c4600e540600280b16103107410710140c521614540e407a00a02d02c0c072544010a0302c1c01b0115141840308182d8040030a608460b08035900c0c0d82812090000416001e4500590070751070540810994605100840d900c0c03030b41a122110b062224004100d41c0c0d080080090f107508050b400059144107282c40b4101c040c1c201217103c400719041025040385030182982108092250200d000c402217600001c219074881ca05011058041c2e48520100341030151130381c010946800041041420075030084420300a09484000070801c0c00704010004044e90002c0c4650b40036034004004500350102c485e00159404a42030350380c440b1244903200310440192241e071041d0001205240b081c803d559060200380150072441c1c031303181074400500c6800303904000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 339415989 1250 339414739 339414743
    0x1b070812090a05060a0c0507090b100302031e070f0908030406050f0c031e07020111070e0a18170c071a0a050d09121e1e0c140d050403030e0418 63
    0xe03020a4158165540c0300d0060050107000d400d040d140c2041050290001600f410122801e01074070402054801252081050102000741a94583c082c41003055000b5070000e0140520702c1e940c40091841c10350070940d514015001a5240341d4241c8414200412140d241d400c011295041008204102603000d000da4200d10710721000d80e9580e0840011040c518818208940004001d034000003aa002403d4041c0c60790600070380b01d150f0700110017100300b0384850090090784070800846011419481d426400300c2a0920b82c0c90382c1c8640154941c4484401d10400d034180901810001060400303e9024086003000300030300d0f20b441406c00c0f0818412101030103030780c081030304011001c0386056404a103a00000c9240b1740258504d004191000d01c001d0508103408c05d00c00501c041200b8001c1e0342d074828047e211260001c41c00041c44100039550807225195494020740f90402c0c01402289100341c18825a40c00f07100548403a55a24514500030700f0020a440f0142d10452400040310f07064010b40340201301d11a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 339417239 1250 339415989 339416023
    0x6360507091806060b0301050109140a0905190230070c02090726040c080703021c0507050a06021b04050906070c03090911040914010b040308071104111b0708 69
    0x102c4400103168512000e0001d0f1919041c40710024100000d030300258140d030800c1c1e8905c0c1b01943c469544404402c1c01c000c985402201900003004003a040d0b600c0030381c00c601e0f4144820076030036011a502e02030740c01c42004502c461f003201c403001c40c44000b080f00c0c810030109103442d0381e0502d01e07000d0806000115120b5000c3d00800c04400003480da180325102c40e044e00001d208165035103044200b074400c00e5003800c490444101800c00d00c003003507030131000541d8412643d00408120301102404403e1a542200c000121994030451501090301e035117042002010b00a654000c0415080c7c400300140242120285a4091880c11040c400c11003030124003140c1c0b014103800c080121250a1504950881a591010381244d15001220081c6010400108222007030501d081c0004d0211840960b40c3c00380071310030303021640c104210402c00120f00c031000e051901e0141f40440c08968426020600fa01c3d01000203c0b400000007811032103820501010310790000c002d20051007031078100301c80966282e6002609400382 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 339418489 1250 339417239 339417251
    0x203190908120c0a0b040614090303090705040905030d18150b090705031f14090f0705030105220501060809100c050a1b150608060a020c0d08060d0636050709 69
    0x142404001d103000b050f9005002031046d03d481e0414100038161501441d1251000101080e9000c5000007524010301d01040034102c0c26282104010003082c8170401183c140c0018007400c000e8154922615810346074090b10b02c1c4602e8000d29001c0c20b8400c040c204020036518100420f50301e43c9605240a41c040e100f0300b0141d40d01c2e00c95603020050b104012031104094000b070040491507840030705084054420994103d002501d410020020301042201e40c2c20001e802031004000520305500074070a070504058466030400000283c090540c1e400760000700c0420709079411b0101001c0100005030070761419a0080000d49008400245244500710004082020042c82901b5002032040f01409a43d03102d2680c0450700d50510107038000d055684200b6459016440004207600140e00884a110318036101034804d00002d55015148e080020344031540014800034580b0000781c89200b0403100120700c2004a2044421401200003200c1444103519503c0030604047d0000700300140840030b542d50305ea404511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 339419739 1250 339418489 339418507
    0x20108040317010603060501020f0304080604080304141606090504021305010e04180f060506010f0e060f0c0609010b0307080a0c091a0d030f14091e0f0301020703020319090812 77
    0x8142d010440030072044002e4000028542e4040d4042001c6680c00e0b02500c00c00761244010035107e019074441c148258102600080001d11000300030b691207442096001000b1901d201d01d98541b414010701d007080c0c00325410051101e0b03900401e001d0000c100485040d403421003210142c11070b112040c89003505114000c1e41411036540e403500a2410b09062040401082c3c0c541d041840d605200382009441c140d1414010401c154800c1c0200500204c03661120071143c501c1c503040c4007250744031100368054858184a150f0910f50140081030140c66004004180022450101405c210060340044040c2d4404210a40004c2001101c081102c02202d00058800800000c5e0008641084011a8013440c00c0a03200c0030560071560340c607804c034500da9450020b046500300c00c3c00c851048002007a0b21199481e0618502d00307400e8070040d450740000e42114000e40741c1c0008682a83c01c441c500310050381000c02c0340301f03405108840c01c1d01c5000c4c4510b80004038a2034420003d88698a080248151010015603008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 339420989 1250 339419739 339419747
    0x1080702070515180904020105040e0705040f080a02010f05090f120a06110c0c04140a090c080613060b040504080a0f0e060415030515030601050f1c080306010207120f0201080403 78
    0x801028090f20400500110074440b0f41258000102400000320010900d000c50410743c14003841641c0c1a11000e240c503043c03041c064280c0d90010032503401c00000b00700214140107154800801009940000d01c200300c000d100240058103104000340406c403051090001c01d13550121010f105030010f51341480c281c4459001241071445101c40504424205400b99800d4140071004103c00c43c011415100091451000c00003900e5a0304130b205a04940c0714049080014154072110b14144103c1c20240c0803680e8020032401c154003107032240505102519240213014813401021700c05001128108070510381540c8145c458040c4840001c05c1017410100109001d000360400c901c01103005214036103c99480b000d034007001c0700d880f041c040005d003801c0115480c002c03240100f42d464240280501260303030078a02400061948116810b80c01894450031100e080003542d505000180505c1c00b4550704c0c40c0c984006480c007045540b11045541c980c80441d00070464094054404960902e0070284e662105d0500321 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 339422239 1250 339420989 339421003
    0xb0901050c15090708071208030c070c090209100311041a0d02030a1a2707051c0b01021e0303010b09060912060a06050a0e011202030a0807030f170106050901080702 72
    0x340300ca11928070b1481644038454055480341c03075250101c03074505840701140d9403140807520134800c54290f044415000207003000050f40d031001320718250500703024003521070b82da014a0ba580300da0701c00f0340d0016201086003041c001c074030170b555124201401b484051028441c0b181c45148100100780500c00441501001d929044400d81c0e80c0e000b82c10b54032400c000306181d000700b4202d08040081c5170058140785460808250f510905040521504d0b040e075003030001030314000c6c4018617000410034100983d120700c401d8240340b85045110380b000041e00918060004e45007000daa55480390a03a9042004054242e00100b05d07410740e4682d18845450f81c5000300804d5560041160b8a90300c030440f043c1003030340c140340000d00781d00c12142900103000081d80c41c1d043c465202c5190282214564006005104034042c0b8040700e00c80c1ca00c05011104030440c582ca407040d8981151508900203034425010f4820981d2082c0900d41103840005482c049514101000d851403180b4003000e4184500f100008041900a000c14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 339423489 1250 339422239 339422257
    0x30715021b03030a150e0612030d06060c020906010206010b0d0b0121050405060a180605100b030c120f0709060f0e06180103050c0403050a02091503030a080915100b090105 75
    0x7120030125048000340c690308115070541900c0d1074150519541001c0703d4110b4119420300b000340505845080034000e110718091581d115500c402c000d860502d1341144a510020702c215601c04600070703980d10401c080810060022811903000304014003011758090b00300e90903c04140b50018100303110800603101d0313001450700800454112041c0c204818416041588600d220300150307842d541d22400240c00b1282400058918000d000b444180014115407205412a8820081500c050342c0d4102c80105a441260014151030021a20007031502500c0354141e002242c400e00c03146245441c180081c00c40101344103040c2041074042c2c80071401350081741007140005028201665800c2047c06601c523190401441600080c90680001c3d040c03220b000540d810359911502500d1100c0c0300d9020060030500c041c0010511108d14000205c02e0740c0c041008000c0200c1079140c20059181030103a1034100308071250411050b00c56841040100359112807032106540710241c810740c40d0300302c0000407180341c014001c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 339424739 1250 339423489 339423517
    0x1309240e01060e070809070605220f0b09030607020309011e0509030d05090a050f090a150816060e06031902180a0f0e0c0a050a0302090f130906050a0902010203071502 73
    0x202181c0d90303c16a002c03d2154406403507112541d00c6108106c1d640e00c030148a084c00064050140302920300140c000c0100c160342254041040c2901d84407410504422507220348641000020201210308080c444c8550055440c0003a43c1003980d03640018002614100184075890b002d82000d40c24030340280d050340c0284401400b00c0e010f0310007c00010f4040d0380304805c142d118400441c0c00080780d241c1100b2003144585c0140041d041070712102d09a1000d0004c21603001d0b6030401c03603130011611002c200038040d5540d021021031f00382985411809080400406c140600880b030030410000c0050500c0445000c2496014006995405803484599402d20f0244c46580c410340203c000030f10b030b146006031403003503524040200700951105542c8661500c00e4034800c201090041c00214484e80c000c0c0d000d81203002c0041d100342410302c04440014485280c1d41d80310103400c1c2c0e50b407501405000d21482282d41c40a0068000c022407146900081e5481c0250304d401411980300d0540180e220301580c0640e5058850754407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 339425989 1250 339424739 339424751
    0x20d0f020a08010e09030f072013140708271f0b0906060a020604031112030915100b071506081518010501150810031707021309240e01 59
    0x16000b0040c140a10a480d043c000042c041050b01001200300c4201d1024154401c0c03030b03d00c0c1685d504c642e1448492072056100c100d620322082649910250b42116559a2400038901c150708101d00c84000018106a0804c00141d08202041290305200101000480300f0484407551000c43c145c51300d000c00b440030a019a61600d480b209841c2d540100f005542c0440d44c202c0c099a41506120240c000c2058040050b03000401060100707007c0c805080c0c041c910309080d610300d083c030f0040006c4e031a80182d8920310b0641c0f0104204c000b02c280a140540c01c41203c50b0642415480c2c007400010a0261070801740105100b0700340b0a402c15440c0c0d2213400201011000c4e01d002010148a2000100c811601402e410385802c8000d4070601c018403400b070585aa80d1903103018089850400c55145100400110303810400719400320220701002d601100031200407125a82d0341c0818030610201841100c01c1209103801c00e81c01c40d0006000408800e400610705c10440c01600510091401800300280c140003070354079140b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 339427239 1250 339425989 339426007
    0x10608070621090803040b04030210020a0804020f0f031f0e0a0f1a01080d0c08070c09050115020114060103020f07080d0204030b011e051302130e091e0d03020d0f02 72
    0x540414105010504401c071400710024600a88a400800400c13120041001600051030040301941140c0640704441421003284d22405c200e91081c002c1001103400e030307410071007185000400c0d40b240c02029204405101d4050300801d0341c400120002d0384005a0000050341c07001c00c40c0e440b0080900d1060102d816642450602c1031840c01030352004e440c1c180803030034004510044100c1c0e40341200c42c2c0c075000303002030340d1001d000300e510741928103007180d00e03103000c104000100c0c0844046e034015000b03d20307000900e0f52411040f816414101c0404005690401e240c0510303038804460314661003031003800d0250f50303042003060314202d0f80700c1c158004154007404108840c42000960103401035234860111029240d0301c40300d429031440403000c000d00e1704043da50000e02082c1800c02c083c1c0450a070340c600150510f800100c09481e10501900201d10b170076141030800424110410040078a02c0da0414050540310350030740750701d13168101c180741e2205240d000a00e02101104a6100604104400900b151202212 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 339428489 1250 339427239 339427247
    0x50703090219080705090411091519090e161203020c060307031406060c03091e2e0e0a06051303062d0b0607020f04020d111309140109020c0106080706 66
    0x26000c0d40303c0603c9505408103580c204811407500030794106c50f10584545402e010010004c1000b888010840040c1641c00c60907150150444000020703a2480c640450608400408440c82440100090740c810707805907850340486828401903450b01b628114200b0325505040e403800d1100710340207410110000030004d065505a01a404601d40241c1254050305d95808000c05400b400421244a810410110078146020302845140b0039590340e101100e0110000098400c0c03040245810103072016000c0c0c070009a450b0b80c1d0103140c0d00c1d030901708a008a00c0c114003150100c04140110f81c1030250000e800b4109908001e5080015644000c1c2400361850000f61258400c0381c2f41180d06610760408603c41007252076014205040502500042c01c4c1540354080060b00060707504e0f142e4000354200300c00410b844d564010116014840c14038140e6416600c1e010152107885e030352105403400c1c030700000358111030101c8115904584003600c0c0540c4804841e507045006106c0d03544009140d2040400000d02e090304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 339429739 1250 339428489 339428539
    0xd06080d0206040b06010504034b15060b0909090a0f140c0d151d0709091b0806040303020729070201060605090d08161704030b060102010e100507030902 67
    0x82411300c2c50050b224400150713014051800000c000c01002c007007040d4503244841c0c051460658614115100d440c0314200700e000d0b00541040c0001851481c55500140016900724548400d0008000c204441c038103903171940107000c0c1d034100700c3c806c0703049501095000c5402c2004026158000310000d46444403032501201d1000400c60b152447d0281c0b603500d2501d0725000d40044245a0403c2d03400d0b440c3d01060314031070003c20503035510402440c4c030710341c1200b2121420452100901100b50740000c0c081c0182c20300310401300203124030214120b4010018030402c140801c07a103070030a500d030a016880341c02900e4804540456240201040640c100000483c00704220072140260f01d590002c100b9640c071f440742100d80c0d00c1440040b61300402088841e80028411400402800c00402200f000d03a0300503a50381305401e50041c288801400001c80c092051050004c1401d4116030240002c00c80124143d41c066254040c071148406c101d0741e18030000c1c44181c026000181400d5005000700f140006400010300304041c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 339430989 1250 339429739 339429743
    0x120d0b0f04090c03020f0d050f030c120703020c09060f04050403030606030506191703280f030501122a060c051e1507090b03070f081b07080d06080d020604 68
    0x206000d034100e06003030034030804055a82040c10411078504640900101500000510390045211502d03c004101d051044840401110001c6c5907103250446032a843c000217000d5400d0501c1080001d100000d030002841e1905801c29522010b1903540d000018415000944209802c241040100000c0582c5035210000b640c5c5985c401b000a61545820700100e0301c4041c1400b5003002c112070080c40742d0136140d40f0f10700c02e6000b0841168686000341d0049a0540d9420b400134030419040c0041d0542c580c0c01080131f04083c82503250422166162504032280c0c0040100b000d0a500070210b590500709002c2500f100d082c0c1542080c0e0010340381c1d0f46d100100f0a251201084e1208e002d460900d4802a20500c0c0c1500c1d0a94001e008201c16507444512030f501d1440030b020380d410301558035000180e114503100918450040d94030346131290b41d0118009440d0b000000d02002d1283c40c1c43d88028440003513101a071f01001d81012505898031100800e5000415050f0000400c0d40b041e0310b015280990f00250183c03180d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 339432239 1250 339430989 339430999
    0x30e0108100b0d020f090301090309030b0105060f0d0902030c03010203070513120b041203090501060605091002160b070606030b010902041712090907200f1501030213020c120d0b 78
    0xe5900300d24020451294002c02c030325900c0402c1920210701454003d0010b080208010314600205007002071708441e02d00c501100440d907814020402d0081611207540102400d032281b91501c1c0b89514210464880c03849041030048c2c0d40c0b01e00f00199102044410b40c4164083c000319600e040ca540081c040e07400008031601c1220a0000109000030b500c4220383c0c3c00d50b4020b4401c0ca0b903403540e81e129099000150300c50010590b0b0380000c0c0001c68000d00075640113000903142c0660741e40e0342e034046c020604640340c60365055500803403001b40c0000680e0138000407a80e0078000f81e91100072900c1c09101412080d80302074a44101d1400200309004194010300c200c424038075a9120700300031849116240c183c00d020051008a09202110380c2c0e08080c540c45034000003601c0c005802c07ea402040d00480c1c6840d6103560b40c2544103a601e81d9550000b0070000c45021602c2aa46482d07616544c0090540800c4000301200b07a034002c55580101801001030301d41c44405910b0300d0348c4516141c00081c005185294a00780b1030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 339433489 1250 339432239 339432241
    0x515130506210312040206130306230702120a03021c020409150e01051c050109050c030c0a0b340809030d030603151a061c0b0f0a14010c0f030e0108 65
    0x8100d400d0400201d1400b5480518107000c1c0324590480580d00051090b60800420014114050a100d081c40d018600c54440068a1207440b18001c0341c03800000c41259584940c0001e0140c104c0d00010344070007854400701c41030790710405002e0840190281080f1902c1c42c40d40610350550740c4102d03802600035203418520811240380540e8001c809041039210b45076900940c039006014034101140892440003074081080204001c41c0e881c00d003110006401628a80c000d180500e503c1d01d000c0c0984240381c0c108031112003c250501e14040418800d042c2c84c0600040c882c1c0032000441c01c080c85542800545c25000310403515581060a51a03102c0203c0c0340c4030f8050031700320280440c028841c0c982a2030300486e0b0079502e940c440c51a9001031115069010980c03162040da00340a81d00c0394002c0040c1d00e1030010921602032401110341c00c3c0c1710004041e500c20925644034014680b03412428100f201e411441c40c07903110680d4801600c41802e5408050714102d83d40c1150f405040d0070203200e0402560030782e030300801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 339434739 1250 339433489 339433519
    0xb2704090309031e0b15030c13020702010e03030306010509061b06010b0c0706140403030e01020c040507030b1306050306071b02090a060608070816050a03180605160203030c0a030515130506 83
    0x1310490220010031400704100800c010556400e01c2052034080641181e984190100000e084042524100c00e41e094000030510b0865900008420107814150004c0d42982429000030b0010301860600c18000d040208808802d0302200302c1c3c60414540c031005075151561580507020382544a20110042849508400242c0d1441441090003042422520600302800d40c0d804484040b11942154118850800d00d038105655910606001d0449030f01c001400e1406c20f014840a8003e840c1030101e4103291800400c481d88001c14413550015032132a041da0007040150302c8036140146e040019400c5400e110400200150701d500590940d100342e00e4450304c030780e100d9400f12080c0500316000701c8807000340d034804200b603030140300a80076145060601085200641d21800715404000806075070854545003803288a81101440000c030402c6840694a1850320191400440c40f4540306401019541c60016620300440c0212410111000b068090044002005500035040a07900a07106081440400741 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 339435989 1250 339434739 339434783
    0x60408070320090106111509030414030a0b07141606090606090c020a030f020f10060e070c03090b0a030b03060a0504030311040509010b030604110c0601030510060b270409030903 78
    0x214010b00181100303c560300700b01d02290348410f200f244800d14494200c0c1c101c0b07515240c00442e44600c21000040d607e41d0300d01016030540490700c400d541d001c0c0d04001d103c1004210950b1180b507220310141011700c1b1000100c02e55851610580b5004c0010494800707107241084841d8008803146801303400c09001c1d80d9101c4401c0c0c82124103254100c00913038044100d1000082c000c80400071001d0290040d0b400f5903041c512154280b90245910384d803200e03544c1e0740912020341e004442c103400c070104c0d1a003070b02040c0c4240d0300a0706030421402140861480401c04c0c3c00c10307a110f03401a040005001c0c00350b415070306106024078080d0605503000c030b021034208084141c070508408141c8084540007404020035918002250300315a10103011541c100b9260294480c1d407104c540c006156212071200240303072561550404a0500e4040409d414401d8200b00040154410b000162000000d146030391010304042c1281c5204242d040400b4280c01c203080c000ca40307062580024124044900901070741c0003101540c58010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 339437239 1250 339435989 339436043
    0x30614090a0b0414150a1a030a2d0605091b03120306032b0305010e04020105180103092004060e250c0606030c060f1e0309110604080703 60
    0x180e299000c042103501045032500c01030303001402603145281041600d031040342040c2c2051340c0900c1e031201490901002880d28420462030351219a001a2402d21490001c0e4881328110800780064003d141007003d80b42c1d050a0000300752080b155905c0540509103442405810111002c09250140d505906c000f89069400401600c2c03004010b410b50000030f4200c12a650005400c03d501441013a5400041d80d0000c4440298100303614191801018031010050503241c05030040c0c0c1c49050440c0130f000040c2d82182c00ea921401815441105994031807004900500d010036028003154070781c000b00980c501034a240340d01c030020107a40c144011f9441d0100051040d0041d0f841300307200c100c030000b400c0b02e0790841c88800040004500d00703c501e5641c40e4481d40244c4696070010b6441c03981144080000a400424982c11101d8a08022290f2114420f110070b00081e010300e00401d141d00c40c00e806080200c02e1501e108200700080c0041c1c0c60f16198080c00e40d0300c106500003243c8903e07140d02040003100e1091410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 339438489 1250 339437239 339437251
    0x30504050c1504030206030103080702091021080903120d0b03060c03061918060e010618030b130f11090c0c10020a050c0d0c02030c0a061202070206070f0507030614 72
    0x101154411001448242e44031200002c144031010300001c00180d6404000754002d502694113070382c40d881c0b6401008550f410142940d0314440300140308104011404142112410550281020b10405030030400c61318481d5405141d490300414440595000c42d52020741410692070b0030030480d40300301c00107169070307040241c17800000b0003c2880012481e140104698684180c000b0741e080c003507651019086804032100d0088a195901c0303000a001c12011242b0450040c0020302c0c2c61a180381e0302d140c485c080f5800c1c0d4000a410008910009034007444015240310400c0c0d84400284075080850410501064900811a2140000b4004211180026004d880d100c090407000360a1080b010b0400b0b50095101c80d0004041c0041030003050182407080c004001410100d40f61000340b040b042c810142000004a901c6200708103041040c00200d0b070046c804418008483d10040e924100c60000469070b0241020041c81c00301c03600605010040c1c041607400480380300d18020310507d00cc46a81c1c50040208440b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 339439739 1250 339438489 339438493
    0x70606150e060f0910090314030a020c062101030c180606170603070f1d0a06030302030d020a02071805100905070e0f0a0308070302150c04030201080622050c0a020f07290f030a0501090c03050405 85
    0x38101103032901c3780090200308010144024006000c410f1603d800009a1054441140e100810440c09030713900751010181107109001c0190a00701080607146003840d401c918840d8070540700107196034804201c0380c400b50100c0c9050398041607613600b0707818410400364201281c40301c042002c40e181040034040c110a60703926401650802d04001a0140290044446001140714201c00025900200c2c86290500f5402c090003003050301d84034503110b0a103c002c2d2f001e20401031600c0c040100065000260701c1d0203500c01c40746458000350f03500004039100020f401c0548607102c009114020950005060f10f95145034020000c01c99940a00214040c05148006804240c18600085c001e10380b140d139020070071145900c5078000f004842580381c11102c3c115880701d401034001440700b403115010000615003440d40d0009001c43c1c0d00b08038a800c035400c0c0080c1071500d441c01c40003141c3c1035682120143c60810581c5443d550300d03440c0100d01900504030031301c80d86604605e804a92905a40710707003c1d0034416500800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 339440989 1250 339439739 339439753
    0x6010206040b0a0615090e0f0606040b1e2a03031902030a0e0d03060504060b0423060f0a0e090a0510061d0301060803070606150e060f0910090314030a02 67
    0x702c100c0300140c018808920141c0c0c616020a03211680008a0008101540d40c41e164504240f44d540c0103900c00b07015880704029640c1001100d548180445e0107446c6142403554542038840c80300703990008a40982d084121004c00e42e190545081d02c0060781041400428042824400c0c0000762030740f1003a03440c01c9402c1400c1c4440e05600c96150000d43d0001100f901c00240b050390084030f181000c04c0340b282040020345500c0f00704990300d400c0c05080c01a11120b0b03541c038503041c600403074215808000050129602c041c200b40c003a4540e207a005a800480c0ca503100d00e5901c80515a00a00140060423440d100f45001c030302103015507200f032041c0e600c42c034509140401d0f0103007062002d480f100300000c0f60090944400d50b5002064600307000d51401855890f0003940c1ba220a89442130942c0d105802010a401c0d5001d01c400c0c003d540031070a4151508161001e07039980750703001c200d101c80780324200300d041d04541026203400c1e00e20740c070111100490303014045051545684080340c0ba224130980c646040142e02c410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 339442239 1250 339440989 339440993
    0x80d0c0c05060402090720060103030f0e03150c12100312050a020a031409031002040f06020a0302210405040501081c0806010f08100e191404081c0b03071205070e0601020604 76
    0xd8280b900040941081c00045203007c40c114010301404444640c90b0f009080100300700b5030818080e1f121341c2c205080980c1456485000b1035650b03270861140b03460f00808500402c0340c441c2c40d1421039a10300c2d841c010189091810301d25070028203015200031500102c2e4107000c4401ea41c4030701706540105182ea030181402d1542900d0850f09241e40c0e400d442c4802c1003c000d84022940c04002040050091010160300e503464190f00301c0d02c2400951090702075410503440a400250b02240020820100081d440d105407204e040044160149401190304146480e0022481000c00a00c0c851500c01030103001c142e80c0320b200740c21150090191000ca004c5050070030300c0c0f0341c070700d0013042c0c000e03071203103040042c0c000483d624008c40c21400c0040d07031080600c50508404c06102141c80c0600700d0318804181c0c3d00c443d0750500d940d8071030041c85541903c84c858508003440d0302c18826284c01142d00c14200400f200d50003500c4604c20503a01c980e003441107038a841070410001d000e00000e81e00c40d2061505030058440d9030750b03507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 339443489 1250 339442239 339442249
    0x309050603071709070509061801062d050712091a0d0e0a0f0209070f05090d020d0c06090906092702190810050f0f01031419080d0c0c05060402 63
    0xd07042d4410f22480405914201d8052160b4522401c0f64000405a55140c901032082d010030240c540c0d401550003000780c401001100800904442c2c00d4900034003c4900c1c00552001001c120503100031030010760820000b8183c4c040302500c0080d004500c43c60b01c0d14580001600c1030034141c404c42565882a10a5025050030500a4040400e502d04040b0b120b0082d5002541008132240003140c0250300101614258200120715660111031828070a44a0072000c0014080e0300a4502040c070a48004442d0005c40d21409003c02900358046400c40700c082d250900a0500c1e04a07004204e1054036001d030021b007001c254061190110b08101400102100b8128a100c1098903035800ba82c20026031510b50001101619510307004004080141c09400c4240074050165200a80390344001400c1d1028420780e075242301c1c086030460341e1120602205d41c2c10500e40358245604000030303440a40d0714154140c1880302d648010402c4400850080110082206040e0343c40b41c01c03c031025000784c4c00709000400500f89 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 339444739 1250 339443489 339443491
    0x5070e0117070b0a1b05030406090b0a0203070b0c04080a050c010e010f0801050402130f0e010501030c030903020d08060307090f06030c050a0f14060d02030c12010503120a080a060f0b0403050f03070309050603 91
    0x8501c5c2c1282601450308a080d11400d000204403070643c40003400f04055580b001c0c0340340160511f42105842c0080d4084029a24015240041c04904210010580602c001d03411035005051890507240e42c0d42c29420207030303190307240d401d6120f01181781800c600c040e46d88140c0400c1141b03107094450580b07036402c207801c1c40000d42010307d0181c81d810083d4800b14420703911030300c00303002000d10f00201c001c1c5604090005050b80d2113a80581c00381800c08800c0e41c0001d8000c035001480307800c9031404900d59910b12000070314160165000110152805c404c6041082c1030b9003140060300d0048130407541a0340c0d10b0041c001040c0c207074821281e10070080d06040c081d113a09214000344a03a4002d00060900c001c2e50303188022030f070040e40c420395580030000d4181c612500d841e265500505c0d045002e445400c42030f00c0074401034400d580b90a410004501c001030b21391101544010042d2511040002d000e54883c00359a03982d03406800181d8091042d41c5001c1d1603100b0000803145206c1e490354603041003600d080309124050300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 339445989 1250 339444739 339444757
    0xf020705150c01061a030a06050405040b01030b040201180f141002030f03070201090803101403061b0d021b060709080304080c010302070212100501170111070b04020a1205070e0117070b 81
    0x14841c14009143c400e4000703031101d619a141401781c1d8a0401d0000303002191965800b640c0140e082c40e04110128290780c00d454116500600d061103155030303610040b40e05030034040d10305c041002c140d00e0104559840183e1201601c001c1018241403550100c100520100c0d10711407000103a000300008000e611040d0080c50308000e480c000444c00b207060303603103c04554000701c0d50500c1102140d04100405600c50704100041e45060f0040c205031b08002c1700040c3c2010740d044800042c9000040e18108950242e1304580184040c13400d1429031036800e00c03500361503450968426001612030040410103202c04811a0119035480d0300802040d001c010041d000782d0080710059a000000061101c1d007004240141010101495800503486d810300900300b4a2000243e069861a03140080019102c40082f080704c50940d08120300d002c56035901d10003d0b00700451078008401507054410b6a90402c1000203e6105880520141c0240c0b03a8803040014142c44040d02000710642c40200c0c100a000240002010031507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 339447239 1250 339445989 339445991
    0xe070908281407080d081f03020415030515180f060103260a0c0c08070e0a1113030605060901051e010305091204080c030c010819050705070b0a020a0f020705150c01 72
    0x142c0846035035820203000b0743c0000310a4000800021006502408441d802000401e51501a88481901c18104441800000d0003a552000000301e0f00c01040c0d10328000b154882c04440210313941e021030341c5401d039064482c43c1c3c0344240300404120709040400c00521050003240101466071940d1650060455803100a03c0c004400440300d0904040b031a0092403512802d03120400900e101b4170b091000408668000901c90b080420103200210160811a4004c000c0560100b050021305014407082d00c5942000c24080c0444500001080260740040d0320400301100d6080841ea81c45003030000d10302060301301d0808040814036180d01c2e9802907115540002c3c0000448440c142000031070b0031035034010f4000c100360341c0c418440e2001c00d14080103c2d200c3d404080c0703407450207810a12004052800c1c4189814160750700d0f480001c081030b110344107a40030a038104c10a20101e04050040c40000e6101c0d0b111400014540301e01030303005a00000780b240489070003500d40c1c43d09221884281c01150400c4490103c19 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 339448489 1250 339447239 339447263
    0x60403150515101112130506070809100903060e0304061205071e0905090c090609010f170408030a0c300b0a030303050f07020703020f0f010c06060e07090828 69
    0x1a03c61440142008031680c44009851440c0c00196140203401e000441c00c0c3e0004100001410300a0182c120842c4c500759a52130315a0304502d00030540e80150141180c210040074104d4420607801540301d0101c0e0b006040821003180319810203034982c46280a9400070a9103008061141c031104c1d4030181e03010303007181380041d27440c140441d000001e030691800d0580060b004c00014003081c6820046d40741c0002e0700c1c501d44d80c40c01d602d034002303e007403401800e429a060101d2650550361050240e181c840c6e4090350041c900659243ca0b1804010b1900140c920300341042c42d22a00c481124001d66001c2c1c421040180c0c9400340c8428204030301802c03079840c1d001c540c01c0c503101c06d60001552183c50b1501d02840c400c3d180410145002c64544000b9800105a80110740c4456801c00c0562118000c80a9422050b69041c1a0b00388200040c0d9001082c094010440392506500103409140d104850b80504996550340001c030790307a04080b40c1d58400c0c440c1420342c404140c02d01c2240018200b4400280c15108050141d06 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 339449739 1250 339448489 339448531
    0x16030b0409030203040914132901080a030e0409020117150904230610060315120c050310110d150b0706050708070c03021f2403060b0604031505 63
    0x141c50540100701c001da48042070901002010b07019812600000d1481c882c1c480c078200d1104c150301107542d40c024000700348104505060403c4806d8035240820741c0b044218072541e582d01c09a0b03641d08402d1059002a00e612060100c501d024001c1d0000560140c1d903446411808a1485005100c007800e00110045a191000c0407034441401d140c0c03007103024003001000300c21401c04107140f031f8000700c40380e032080d8225808012140640d803200a007a200d4a10340010242c1170380c6e1741c0c0c0700b00c4c151075001410010b0141100d2410050110701042c10b03500103400703440c04040720440765001d407180740c204001e0005003400030381011011603110b8044038400d03414245c1415074416041419901c94002510300544500030860010b0300021050382280d0546006008000141c078000e4490003103010312001010258075010b290801500800b80640b00c0e0803010800402c440f21010410a55110403140340303040140c44100380ca442e806030b40850381c014071803c114070b04058100b00180f800030006415103107a840c400321 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 339450989 1250 339449739 339449741
    0x30f060f06090a0f031e0209070503041e051c0906020a030c0206160807110312030c0d09080c0307061104080c09100b0d140a1a0f061b01050609010603060e16030b04 72
    0x3c0106003a1081c001d035582141030100e50703120034a01002400101c0c8950b5001622814401903002c002031078000d46a032941c1c40c02c8800b00c52034001101c0c00134011a0032405111000c48c4d03000384081c541030a5003003848004010380b03440c2000e100d58805a04004450408603028468600707070140300030103079440c0100d00003007011403421812054850368400b11b000420094503c80650041208070f00071701040e8071980d10707240700e480000d000c4024584040748a0805690b41c1e003003074a00903070080d681900d940ad04546c156036500305e1001a2501d609020040c81c5031700d4207004440039101d006000d4480c020200e001d112810a0103041c0003448078004200191410040014108890b140320000c51800103001d41c05072404009005850b036680341800300244210091020105044256200001008480d00040f02c5003e491510381d0203d40003134444000820660000e4414001114041400e90300e59504038202c40f030a00800a00380c0400d004142d2060001c138407800c80744800e25021072040800800700f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 339452239 1250 339450989 339451009
    0xa06060603061715150d02130b030c1903080f0408030a0c0b0903122a0d0f0e0f070b0d06090f0f2f071b0305160506030f060f0609 57
    0x20001e0742e110003d0248100c0f000d248400816418001c011801c81100c84450301d04020b002e0b200510810b4800002d50740790084460303402a00144405400309400c2c002030043d015021000d4072a0150320b40010700b0380303401100554240c2d8086443c0030070504540c0d907801d4542c4076000410140406002c001824403040000300340b54003c5170b80b02c0c07400d000b80740b8040320b0070680505030300200d401c217100e1002c05903454840f0b943d110300c04200c94041c40110054141d40500303000000c0d840c4040004241c00c4258a035000f10f07080560b20300f0200800c0726600d028035118a0380c008a4405a0030864041100200b814050704500302104000030340d881d624400300c01100c9003102c01ca07441d41d031541c03118001041d4030301ca213200c0325090380d4440d151020b00c0d54090180a60f14507019441c8000130500c0014801d02d5240e2411040310000103000e101c0d100c0c00e04650b6804500c0f000c82c48074a400c00c0105071800c3c030784182c9029186d8214401074a84800e4101b11016400584079600030005012045082e950010343da = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 339453489 1250 339452239 339452249
    0x20705060907080d140d090804080321010e06010c200a06021608060606070f0c0e0c0d200d0504050a0c060504080606060c0a08030a150b091f020c01110a0606 69
    0x4002540c83c0122050070101e009541e14140300c850022401c0d144090001c8a90f003504155000075402850f02e8010101c1c061a00003449500c404030701a407031252150500c1402c07581e0303421000c000c0d0b0703600c1610460740175085400e1400a020300100c1800100007440d400f40b1414210601096a20780c2e801054070a2581c4d8011801a03200400c0c0d4030f09085565510f0740641044005492149002ca01248142c8148180203044000c000000d005002c42024000090240c1010300e081605090000d064580c0080d00d10425091420340d4244441c45c1242042048010404210f4100a00302d54000001e0400078010f560340d000350b424640024020055410282c80642c030f0f40c42e102c0342031540719440d142e0010900b5024840802c840003c044000815040d829840120150b4958a561103000a80242442111954980700740400e46400120180c88510401d441d400500880c010201c60010034802c031010250b08081000742d83c9520600585012408110840c0d909102d07943d21001125031503445 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 339454739 1250 339453489 339453493
    0x1180801020d1d070302090115020c040e030702011205150d050c220605091311011101060603020d0c1d010e0402070b01080d081602070e0709120f02130c120506040207050609 76
    0x207843c0040e8640c00b020206a04400000c00f01c0d0303410756021588500060084a01e0342891450b403070586c1e4820803864010550180c405c0c841c4102e640e4003a40d40e0b0300145800c0b8080380440312001c13000c90b4140706240c400d03098881c1c80f03c5542c5440040c800c00020001058400d802265146001a201c00c0c2034202d404203210180112980500101e030200d406075080144518651741c01d2155100c00c400d011150310343c200480d00c410302200001600d06408c2c8500390200d550810354002400794140d4040d005001c402801403056001c806400c07900d500d8050184040c280ca8140c45481d80c2d4804c0f841c907001d185010300300600c0c0c56580e44810155180990080c592030344044c01e54449903504c02c02c015001620568401020034042c480a501c443d4240179030344104a901000030501e9214540e98002040c40c1c942a0b80180c1042c1030a200420690000368014059a155040708040d10b00c81c40320100e8042e0745118400d420210884003a05014003566480b9800b4000034011810911180d070144042c180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 339455989 1250 339454739 339454751
    0x70f0c05040b040612110f0307090507020c01080903180f06131701050f040605100e040503280212031003210f030c0e0d0f050607030b1c02030a0201180801020d 70
    0x400080e0b4201c072070b840d4012402d100041001d80800079040411a500c8548020028850b002158170f0344d20b810b0034a40d05115015002680062a920032030140283d542a5003034551014010350b944901515141400c0d44100b104a004010041045411a400500420b04400c5c9400085c01d0398000f40034060549070700070010080400000e2060414882c503000030310076031038800703100303d04403500a01c00341c00c040e210760000320518078040b20100a020340c101c50500e141001e040c5180e036600484101b441c00e0342d4176a0101c90b01d0001c41000401075605600400d202c04024845140d2904040c2418100b0001040007100060641c0502d650b200c40d003102002e00a11041b00060114000e42c29240a052420021114059000340102d12411042c2c0f08543c00f40c005162980d0f80003040503000d81103020b42010300200f658150403181441d2011030b0700085040350742c01c248201d0291b00704000d625520031007801005502640d21000e18000b10750060400691703a070516800d80c1c2c0320300901c20419603910 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 339457239 1250 339455989 339455999
    0x1150906170a030e090703060b0f0c15010503071e090207030e03070e010b0a080601020f070312020706020106080721080d02031b09090c031302041109040e0303130f0206070f0c 77
    0x407052400490303000000c0c80c2009140d10041d02c52409400b60500803043d010004200500a0300480000c2c11603944850750ba610044000203583c01008003000c1a0081c0b00a89040c0307032440380058142c0340c005002d4650b5a280456007508070410401031646401468800988003030980302500c9101d0094440705403650420081504041d016081650702440020051004412103002c0c3c40c500f10b0b2070b0800e0080741d03c99000507032800690607003003040303842180404010050111007a056405e100d40807078032002d8484100343e0981d501401420742650010000300308904003c2d0040c82d9654240070481c44581c520388544415038007580b455550282c000040c0100610700d4441c481c04a0741044ea20b81c01c000c480000981c0b08040504900c0c1e0304031020000c0740c0c1116001d80b29248056008204219002c0d283e84504400d80101c12054800e92400400c80e0440001004503441945c01e041d44045000c1e984c0d640480015008205903000542401001700146a48030041011030181c0a040e4040d4608 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 339458489 1250 339457239 339457259
    0x100204060e010507050d031a0d05010f050106021b090402062205010207050d1e0c090e0601080c090702060c030705070c06020c030d03020f04090e12190e010c030504150201150906 78
    0x80d10442c10440108944404103002003036031807801c5480e00c0e0102d001c0008501401032940d48024240d400800c51030b0705010400c0560000e03050341c4800e02d05001a03030f81d071003041ea12001c2c4078003101ca500c0c00b200612000d03454141e00c000c0d44035100514841c00c1514045080c00040c0090b0441841842103aa06020b10760701080341c20003c0104a40811800c506555100d00d03012540210102d40d204866190f810000400720400161614980402801c0c09810340c49030b0386c140070311a21009001d0320101e007040c0c0c10035285d1140f003040c541d0018050341c1c4a10f00c106a6036840140900c0800c0b80a000d10000161804110802041d5a40c02440007800000405080c0302858400f0001d0610401107004084004000d03181152504000003c4180d002c0e050541094426002d55441791800640c0c1940d00d1325280c00051500c500b0b42d030310000c0c200b41400644900c1a1444d014010030b5060004114003112030281c000d036034030103100109065413118031031003855210f500110b01803a282c503007c1c0485254 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 339459739 1250 339458489 339458507
    0x409050f0411060a0f030515060d02040f0e04020303031602010e100507121b030b010e030a0308180c09181e030a021b0a0317040b0d090218040302100506030c0310020406 74
    0x3c41d51107180541d4040301805204142c2856401c2c107882c0ea0010f0454103e505404c40300110252483e96035071900840070000350b109010b0707880685071940700402e81c5842040b12611032503011b001180743d0340350144500071251403291180308540d00c03076001c85c01402c0180314214100100810104103400e1941014001d03054242100c80c4091901516020004085404401003881424005040c05032140100e0303141600151103501446865106e800305544011038901c0713906e841007100943d1140440755a100c407942c0050b01d511140c00c1300400c541c0398040c0c01c601420320031a000c65119514480048d4094156240315071565003000c03c00c0818103405000070040101d40d103030112000c03503030040020100c03041800064442c110554034040010b00200446025010300c42690740c86403d00d100110207421080c108034001d2210320072885032240c0b2090801d002c0d540c186c02410400c420144508010b140c02410b0b40d60511900c035007138580e9101400741c8820402001c0300980c3c0e4900707256002c4c12080b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 339460989 1250 339459739 339459773
    0x1020102090a060f0c0501140f01050a0e0a150e150f0f0a030f03020304170102041d0702061f0906030803040b090c0127051002031b2e020409050f04 65
    0x100400c1050100e07920b00e111071090300d0039810950850480441d04542c680305555008216618241d01c248600442d030680303500c1201d194014135413603070300c81090201c0c0d11400c1c46078269501000340420300e007034100d40040108006c00340c160700c0a01c1d641c5440d58546c40b001d588021800c030310168000b80c203040c02c10040b840f600041c1c8034071a048003082d0201d03001d14200c1c80054421500405d8030420140300b8030442e0000d084040401a0b200807015405000b0340c41440340ca402e040454400c1c81c0c20311001c603a05031223540c2d55006810303555a0382c030301942c007942070303101002000c440c079000070031800fa031840344c05c014601a00c0c00c0794a03032919150005074210007601c0d8074003550142420f8000c984c0d010320307880608401c040394002c14050018048001d0310039034005070381c01100b11200e00101580000a842d0304003a02040150f52050030700042e841e20101d4862103004034084071488001c410a00070009020319080700103142541c0c401a034000c441c02510755054038100c00341480140700d1003020001e4544 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 339462239 1250 339460989 339460991
    0x305040b0f0c040b0304020324072c090703140703140c04080c120a02030a0f0213051b0a0207080709090b10080a022110020408160503031608070c030c030c05010201 72
    0x100b0b1501c03841c0d15500403031140200d40b6000000050440d2014003244c14048020300b8580981c2c440e01d4049078510004a5014001941c0c0e40c09807880d41c06682203100742c014004900917003040080090040d40c1b4030041a48040c5038848610528420f54003a2261098155517000948101c00d018841c0b0310743c10262112020340021b0005200c1483c1c00720349040b510398100c032540c06803140e2400890a1000901000c1e44c14004c006101040c400101381d407401d842d1080710241b10854070050140c04590081c1d4080001441405510316040c680800400010410340121458603945010b100e1801c0f50940061040d00e0b01c07048007104000d8040c480a801c600c401c500350705031504040b50140d45241d0728402912503146a003c04140d03e545c14801c880d009100810780e0284050400705002950141c894041140304001d604c0080e10200744100b01a100000c01462074007822005404407010844002d5607802c201300603003070019043d800c1c6800114890003400d0100d51460920210b01e500c994000d50540e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 339463489 1250 339462239 339462241
    0x506041b08011a09040c0806010305070603050603011a10050d1a1804120c080903030c0a05160509011802121302010909110306090711010f021305030f0a08030903190305040b0f 77
    0x70f00042c4403032041680130381d4400f126a8450400002810066106d555540074240001c8180030012a044045d580d842d142071016844d00014903080305c82103aa14500002e42c4c031070200342440c0600e0342d40144d04240c600142000008600201141c002c01e00e4001c151010380100c6010b0308000084401c51200c59518603210318181c2c03034900044010280c4c0d501040b406166007000c000e001c07401e0f40c00138103000d070440b5241c056200e0350b140e0b80c1c0e00c00c0800b41d4051048609100b8450030380d100010a44802601c140d0180c0d203012003c0d074580741aa0342202c0c0d401d409001d92103540c1c100d411000c0c400e603812408807400304001e00000d0b0511361140c110310032070340c10030003d0707000304070601d04494200105035a103203040c2d40c0d83d4000321811000c200000c0055420100341c042c1503100c54010b40707411321a4409150096035200c04145c0d50f001200120754440d0000c102038400305907000051075128400c1d00c1564074100c02c422034013468604041241c00420740d12000d1006008070382440301d9110301c11608506103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 339464739 1250 339463489 339463511
    0x30d0827060703091a0f0612030a02070b0d240617070905100201060f0f0509060d050604031d030a150f0504020102030f0705070906080c03100915090f0506041b0801 72
    0x5880e0010300290074561075407164020072440d03601c0011790414800070070380396042c944001488568150761041c404c4140b0060350903011303404402c441d03c50b82c1c141c0041081c149408440d031000d4000d07120070700d0295070306c4640345c2c40d410070400104103c1c2e540c26079281e650b03030074210041c01a80c00c80703102c04420131902040001241d00700c00d07546d083d100c007124141d96284c003940d8200e015000c03a410020b5210b404103000103d8000c00900e2800b40c0d0421a1110142d40d150400e01c130030702d842a80d001c1c0c8035500800c08200441d005607100c2105840d001c00c12400390503e01c02003450100e0f44c8500301c502d01c02d086451300811a507489000c07040c5621a100784014182900000e60b2170080c80400c5803074400010396482004000c11211000300030300e4800f0b200b010350350711701c50340c5806492100d107002c0c1c01030b601c91840c0b8012602c282c2c00159070080d21840d0081404080000400c0d451200b1507460318002c1500e400301d2010006c552185100d80601e050034120840ca080e40122940d01200081e0b0500000d026 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 339465989 1250 339464739 339464743
    0x30c17130308091c0e0102121e0f0d090f141906020c03040e01090c02060c03070804060c05070212010507110d05040b1812030703020724110c030d0827 66
    0x61803540500d800310080d01d6801c42241046442e030010040c110000c500400030b503810105c0003e03010026000c1e86c3c00c1131a04860103056100d044a00c5c040054601d0310f8404400c0090301605c0540f480800090601b41c8010b90541104e0b038240c0c05640c4070310400782107820000101305104c001c1c400740018180c903190802c0d201080544010000340019004a440203c5000400685000b40801c0c1c010000650790740030388000401000035800014040d403000210606400d0003101c4c010303d0180c2d2076400310303641c64403144010418490b110040010410803c3c01680ea5504446003004005000007501d0800e41400780c0304030090f6020341c801d81c0140c7d039100450ba40003025070b8129105031034a01d0341c1d0000c40942d01c03410004501da4a50000710507910f00c1142c580040a807410610035000c41d0f445a4403609524102e08000c1d0350142550040a203001310280302d4400c19411942e80401c80b200c000c074860009042c00e2620300702600003492201008503540e800202400c3d410458035141c3e0081c464040d04039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 339467239 1250 339465989 339466021
    0xa0606090b030c0d0303022a1b060a03020a030b0a06110f07080d050706110c0a1a0c0405010e1813030e0907022107120f020606010306140d150507030c17 67
    0x14850b80801e0304d2201454000e0301260f00c60260240c03810041880600b1a042814542c041e002103031048449007107805030b80c840141d0303032000003c1c90a410400040d4044006c6c0d03014107649020540c44018038101511240c943d40003808551311050701280b840d441c1ca526290f103603014903580d91300002082102c5240400c01c119141b40383e02d811541c42c0e0540c20000003800110081c4c50702508005030ba403224200c081a0081c2d420703c0350340c044003020880c039503044802c1000e494480c0b402000b08010009503019645480400300d001d030122041c0316203080306991075581100d803040d0344200110740b0002c00d41e00103951b5082d91401c44030799040341040e4800030f584107840e4107804071107400ca0311140003c84e510341c26101640d40c0078410300d0031007015a000416004800c184d41c3c0244c42175101040d010740c002d010b43d01c181ca1210740c40c41e10710401c0c0700401c204041d041c1c1c2e081d600c600c024100ca6031442c2c0140260791190341035803404540ca0350281c0e0001c0c030400340b42043d2820300d03007e4418001100142440d038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 339468489 1250 339467239 339467263
    0x1150e06060c0304050d030806130e0c06031915060f0201150e130f0f031704020d2307030516061407030c06020f03070f080c0703020304121a090a0606090b03 69
    0x1182d152a07030b045a03103140d4813483e0009603020760a00d8030b4204041e40a5142e61040c00c09640b500c0c0105e8803030810500b650030100002c42141c001d00b424107401c9c1441c00c081c5038171400401079018681c016050020487d016000560401d005a00b4144511504001010a440014802013120503152086e200150000c0d000d610350741d104810118561039501540403c0d03c6800080c1203e001880e0300d007054506800310700c110041009011040c811001c1c007000607220700e070043e2004640185c0c42e61090251040100710326108603004500e050903c1042004002641c46040140402d12085607a900b4079440c0713500c10820880482c820500074150300741910039043d45420581c0c2c0041e400c0ca0048044d0145514003640440007004005a803a4041b0301002c2c0d0710b2103a100e45001e61118142c0e0700891185c005d0207409a4800c2004100030ba0010102c0c8e03d54038000c60015200e001c4400344070302542001e46114030154070a82004050101074400d5400500906404110405020740400d844130080505 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 339469739 1250 339468489 339468499
    0x30d0504140f040b063108030d0b01020f1006030b091c0e0d020402030c0d0e0f070519090606050a030c020d0801050904170c0a0302010506062506062601150e06 70
    0x118400e00c1e166600808920b001c01040103488041d203075114002500c0181021100303400f403103c58840c0c6c82020002100340c0d914413010b5480c2807250180d0b4400f60048880880c1188039140030705c03032011030900c10400d20709000c1002003800751450030201e81520f4050490800e070780086901054204402034901019021424400102d40b03101000484040398044041d401c50300000070008809042c400420000c2801d40c0e0800c1403031402582c2c143c2d14070000300380d00c41540c07260340144590b18000000c44800b51941120042580d180c2c0102d03001d40d41d450b03100c0c001082003c42c25441c180d406005400c0b80c84010b10042c240c0d0009001d00405030304062090764001d03605c440100d8144841c4100042e020700310310001581e5030010000031076907214090019001540780c4800314107285001e000710381c211400b08003400354031003810828a0355445900d00885105a40d000300107102098020120160400b40c0c0203201141d415070101400c1d82d0290304c1000044002c10014440b01800106003070b04054140c031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 339470989 1250 339469739 339469759
    0x160507020904050c030d03140a05010b1614010e01060602120307021c02011b0203090103110c030306090711060103050601360209060f0d060915030308150a031b05030d050414 76
    0x20f040d400d014400312955003601580a0303114405405070401140c000e0206804803142d5a01e2801604444080c05a400200d500304a01d0300d00030400c140303541d5607602500080031801640004513085407650100c2200594444c4000c1050b1038062040420203c09240d0451a500d40824029103922014807402c942d0104255200d003805e2007513001d021044014080d18026401268020355a50452480580001c1c1000949a902c80c1d580040e200900100d100843c20350b1110750070000e07844801042c01080101c0d1142030301034600c0800c4180e0007075004030090401541043c0c0200c81e41c4d418001c0c221781d4600c0e55602c5c0034910441e20065000841101c50041e102d03880f81e400104284250040c0c0d09943c603001c902c000e00e441d60b59104d402100c44000d010043c03801e1238030040c111589603110180c00704a0030000140ea5200000e101818503100070010500a9225545e4040344c05482c2c402c0000c040c10780b4000c1c00b003400c042114109042d807c0c1400d500f400e10300951110f40b4054090100d020310701c0e002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 339472239 1250 339470989 339470993
    0x161202040216020d03031b090612050402030a0b010e0403080c0a0e011818020310080a020d0803100e01030614101202130207061d0106090209010801050609120601140405160507020904 80
    0x1000b180c00385540245504a165240c1c14014060440c84103e0400642441c992007041c9000300c011354204d58041c1c0320700c00e00541e06100035006060041040c2e800d40a9408580e0020f409001c0d028044d185001850a0038201400d00a22888006001c0b0500e8203040080400c000c0e0820044600c1c1c407400d181201c10700c0d48010781c01d0310105551344400740b440c0801d004503440c042141c0103540b158185030010151a507480414507070380d01c1ca51501a410170403c001c5a0b01007150500190342c809415403a5044240d0348865007808a1000d074002da400d1aa119540c502c041e04140c0c8007134104160500b4030131150300b040364022111046030300007403040121856a0b00880b0700343d01514000c80e003150007008003607805c22058410a412171640c3c4201d519040000c185071229109079030920030180e40e030344026820030092000b240d0000324240c0d070101903900880e50540c020040c2c2c034041c1c001041c1c3c202a01440030103010607241c02400400516241010360007040e640002950101e07501140c0c003003260f807198 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 339473489 1250 339472239 339472267
    0x60304030926060703060914040209071209050304090903030c080606040918050d0807140310142404090624032f03010e070807090902090f040207141612020402 70
    0x2c5101c0105006007010021015095030001c000c55860030014000d01d660a15543c0d01803004840c002c1d840a80d100200e11503510500300a010740c1e1600c0790008a0700215155580343d500154054207003d03444000720010076506000d241e4081d80030333041858242c249000041c07500e00541c0500c032556952035031060702c3c15801081103040c40b5004416541ca10520344402010010101c4402011a525900c0d407500ca10924084034410310385884c500070403d0800c07003440c1d48010010002da5004048009074141012180d040b016240f074444211507803140791246100941d0860303031001a03008440a6080f140c907a4420310302440c00d51a240c000340c035a907800c0c03c00d491070346201541150860032240c0407100a68043c0254140c2e2444580d0680e65034405c1c81c00c841c00b00d011600728001508880040001c2507003600a0494107500600521418101d0300c00318040381c01540303042e5817044079400c040403119020710901310150880341c2c0402d1002c0c20400c546024a4241200038005e560018131450340c1028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 339474739 1250 339473489 339473549
    0x20103020c1608010b0306160504050904020d0203240703060317030403030207080c0703030e0406051020030c060612010605061b15011214010e0a080f040506030c12060603040309 78
    0x20510101602d515580d1981c000c1c40d2800e1840c0c080c0c403c890110f042c50741e0703542c8428088103141e6940c515050401d820301c4044600079100b281c0021415480074016a400e00c180c12010f100a8607802940718802e0b100f101001014018209040c40d098040c004100c02d810443c10301000500c90399a2034a40d45406c40082c0318031354025245000200718044c40d5440458000216030003650f411101101d500100811140948281c9600070020000514079600541080701903a40740261480c5820342c03110800d04680c0300e004890540c1e04480100507a80c40c200340e04002c07640035072000308210342c241000300d52644a01040040c0c0c04e10901d6903d103e4142c03c0003010700418103500b214540d540d448038401d282031a50b01c0200d0b07040140c4c4000101c0d80c2070512034108814030382130003003010100540300c1d0040c1c4d502c40a88910740120420010400d070f100d00d4020344c01460b4050400e80d50b4190075140720a05d0001411940c402d840420500002ca41c0c01880c20b401e8a01c1d056810150050810011140501d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 339475989 1250 339474739 339474763
    0x6060f03121c060312033c0f0c030b03070803070503041a0408010f2a02030a050f040e040c150509150d090c060509130501030b15030a0f0516090b010c020103020c 71
    0x420301c10003208111500b0244812050140c13024001102d143d00840448880c044120b11f1070600304a48204c6200783c00c60414180301890070010b90303030080443c02000d64280e8040c51011035210020450a8201003007210000e2224002460801a590341e441d5124416440340400d001e20409812040f40b00c000e003154020516000208030410040c5040800740481403030703001d10403501c02c90080303403610001c8004064800980c0030b03514084103000150755a820400b800380b403004080c84041469500e0200b0903000d02c0c02500108503461030f210131104ca40b42c0c5da03003590041080034045441c1b6520784451402d000c803100107030f583e2111104184400144144800030b400d04101030300c001081074010000349207852040d50220000c0b0301e03040240e030580710288401410b02245100188201c1322600402c102d400e4020242c81215126884003001c0803000c400c00d8a40ea00070581030814607614140e1840107109401c400c1c8542460b00c1d00107420040403030000380c18583c0010342c01007104014801944150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 339477239 1250 339475989 339475991
    0xe0310020a0f0305060111070303030c0e0607050a021518010818010c0905130c12090f0f05100612081e1303080909070206010f090b040f02030c030906060f03121c 71
    0x41800400108600c5410000b5004645000041481940b05464428540203000c1c018030320347d440d5030381c110001c001e00d04690302080710001101c002c541c0c0d9003000701901e502400041844090a00402c0010051150044040b0f081040700307940380d000f403070384a20b2103141c06d090030703820360783c0c2c4412040b4030207510b000c0303105554030341401e10044540142c0e10744240c400c20b88401d1801801012148112050724083e60701040341d64003100003900d1141c11025640b4811a00c8141f8828948e4501d002c421071084200c0721500001281d040c2580740748104d2008245440d11082076940b640c6403503007284907200c0859180003490b07080b10340708003200d411144080203000440d1100703503407800c01202a42040010521882c08980031442184c4005040c038141c90b418000c0a0025103403550300c00c01801d03007890702c540041c0c42c1c4008003a400000e00c05980b01e224000841640c0c0e1a210390030a051000081503070b8841c26800c449070070180c4000400b1242d4448903900981e4418004036070109118420030f18600d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 339478489 1250 339477239 339477247
    0x1061b060f0f181a1b0f13030327050a060f030605120312090d27120803010503010c030501080d0c030e030a0f050d1b02090a1509051b03040f02010e031002 68
    0x48000401c810b081180291306a03980202c6078094a1001d203415520204071030414203010400d000a80d00400405801c0501d01e8a4100440e00402c44508583e00507004280c0c00d0080c0391a501d28095802d92948045158254403070070680003400181d0344d070181c9001c0100020564007802d003c0d900282c050400145500d07040c14000c9099540d9502803207002a03c0f51103903012913901a80010050785900054640710518840403520200d642c440103848a0404142200050610040b214220345d80d80201d58083d03481d81030000345800c0d00c2443c03000004140c540001000780b031101040f90f1308017002600c1c0c030b00452009030504032052591440c5007035042c041c7c9000740c030403c091107a1414070148240c0603107281c0019640252005004d01d040f24841410bc4280741c001417034034041d10faa1014910f440004c1e00b0301d001c003001c10a0740180c1c0146c1e0400790f9030720034000000d0340c04c680d0281c0d1040c4010040d14601c0c040e500e41c0000321540c04021305000c0c1c4090949156503050100c10000c0c075100b2421901c3e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 339479739 1250 339478489 339478511
    0x60f030b090a0b0111060f07050f071208041a190509010b130506030106120c06210e0c120d0e060c122214031b04180503070b01061b060f0f 61
    0x140300f44442e40d80481d081c0c402d045d04000f0081100c81c400c0c145c0034034611441d0340d02101035400d540f00d00e40040c00c00380d0402801000030100002c0c00426020b0365541e000034a010301c3e003509021000544820f035052000100304d00000ca84039404102403458402040c5901c0e650f200501410491483d242e00402d840310f0807504940c2680002d01c01e0348100c000340206940d03041d08100c091212100a41080b44580341840b9150241083c8840303014641055441e83e410907507550116400560130b02e805801c0401c2d015a286401d191608001d804900907207104e00d0136000182010040f00d600c64001c490102d043c9032104821f0006400c2028207218084d500c11b81c19100804001115807068130f82c1030300c0c1300040780c02d0540713120a1707440c1a80600100361801901944d02000d041c0f000303001c1e501c40d488400107850031a8460f80b00640c14032800c011a00c4103030324074241c0743d000e0050304105d080100300e00c00d01648040070f0300c050803156046280080e190031980f0080e40502007103103404072600c2c1003105a4503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 339480989 1250 339479739 339479741
    0x1803041d06040b040608060a0e1c0203120705090d0f020612130c0e1504020d060312030c030501050f030d0518180a0e0a0203210d0507031e06030309060f030b090a 71
    0x441404102c80800c10000e21004001c12a0168021108681d001030000303032400c04503500106405c2c105000b26041c48031031080c03145130341580c8441403005810108206080b150061500354000d000d9040075420105101d000c02e411000004028024001e02c04928082d501c40a08403510312910b080d42030120303e403400071804a001c54075002c480c000f1187c0f00004546011100d914040d4003881d5407151401e00400810000e500510000041c050b0754850000c002003112101c0c400590b003d4a0110f000c00007000701900300e030016400b80b40101c0c5041c1e414071407581d000c1141901e0320000c0c10190303140c10b000e84000040004108141e038000410301016441000180c2c04103215048022050000003110304046e5216607030031000940543c401d185200904c01521f03006402c8075000912503040c0751020745a801a101e007030b26440c01095840c045002050a1004000c0b01540c0580c0705201c031b1891a03030000d007041c00c1807040404000c2c1841021030702c544681c0080e841c9a00017040d404950030243d030303404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 339482239 1250 339480989 339480991
    0x8070513180b01110a02090103080c0102090307090506100801080c0405100909061b030c0804022202070609140601080a0b1015110d0c0c05061b0312010305070614031803041d 76
    0x183c04903103d807020031803140380005c01803c03c40d8081c108483c03503441c0d503a803450f80b5000100d40c9021303550240040f60301610100300d008010030400c00040f925003020380500c1848003203141800c081062400c01808281d50000d2522803040040e036001616a0700e54046da40852226002802104d0500464800780f080980043c860385000b04940c160341690700700254212010851901c0c0400c650a00007805880c06d50400051422000c03442c580c02c0c0340c41c1020031b0807a40714107000c44019030f80b0400c44007840a8a414522151382c203000600c505d5040006d1984c0d100201c2000038400003070180050034036985210541c0c001d00304040525001c01a440000e090362118152014841c8074070617184611502c9801010805500065058605411314060010907441007480421030541400c1e03941a0800400c010204614507040042c8654150300d0200c0c00d1801c558001c0c42001510f1110000c81c505041c01c4941051241e440c01048608c1882c1150550003990b120501c900000c100d04440c120600100d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 339483489 1250 339482239 339482261
    0x809030712020a0b0c0d1805040609020408010605010c0203060f2d0f0610090504020306040b1f0806090c091c02040e030418060303050a1d090406020901030e010c0807051318 76
    0x21107803901d4081d050110f002d06112485c4541c46500c3e070344d00c920701500c03594004448203150800c0d456251404070781a114254800c0518990009003008010400c0c1f1a44002c0c080901c5c10a42a101c80e8001982d5803201030302401038410640d001c104a06d8404644201603601e00000d4580190fa41403003540042045038401005200b14001800c1843e180380000d080915580300c4414190808042c4802508010413154200f907403502e0a01890307031102e0300e14940403ca06001803030310404590050180c1d4010782002e008a60780c20602c89203140380c80607079946c0c5609595128185183c5040c10b91a0103085001035040f83c0b4150008030549008401801503402c050049403c5201200e500c008940c05d511000d0000b650034000003240500c2085a2924861b5685100091203d045c00040701d2540c03e5804903000d95000030840031702d58240c05a88042101704008000050342d01c0405000440c1c02014441008800500d20fa149182c0b40c5025024041090101d020f10307103030350901001000d6010391 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 339484739 1250 339483489 339483499
    0x9120c05060a0606120c030e030c07030311030405010c0f020102010207021207080c010c020916051c02120618010306051b0c010b031203071b060e0a0516080f1504080903071202 77
    0x40c4440c80302c0d02030142203c810340d07a580030004196400b100141641c0700f114041649031103a0307009115081000d4221400240c0c0a428164514074020300f0009511200c0341c9560024031003006641c0e044909481241e400000d4601340c2748003407004078028843c8210003503005800449803803100368005890001e684205003240c0031102c007140159101125910002d50002810000864400c81d2000c01185040c0c1d03400d00c1800d01c00c041c501544064408081071035415408244c03000d0607241741100c1a04010300f644c98081c1200c8208080c1d4101d101404050400d503290404207286191015014100400480c1111b46600c81100c03d00c0c041e01112800074800c0c4602e03c498014200c903001120b00441183c1c459191841a01203480e04d00c900c0c102082e1487c40e4ac03031203480e102100612143c03400c81d1064015241ca111982000c001c07896450300507000582c0042809120908001642801460700105030b403c180e03038a161070001449010003d035058050341400040e407801c0303c2d800030a042c1c8210382d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 339485989 1250 339484739 339484741
    0x319050919080a03090812041203060b1209070504020403060603050717210f1804110f070807020d0204020c100b010206100308070303060b1b0709020a05120a09120c0506 74
    0x1669594420034141c0501101c04101c42a00026001c40002c0803050514200440c4800030783c0c807a80c0d9907411007000400760310080000c00c030030071451072150900503250703040411030b0700c0c1000352900c1b59000722001109241c1d4844013144200c003042040100500c4000e00a5607543d807a0310340075010b0803c40c4401c0382d292203001700205056a43d1007a4040016420f8002c00c04149007031a0110061309404403180351300c078204040f00b1581c0040004010b994840306030708d00341109003400e110849100c4904580d868105120b2801041d40c1c10007110311f01074000141d01c1d1038030100e00019108440700300e8000d50040c80052025034080001c17070007541c0041c5180b02042001c260400598444604440000c550200d000381480091026070107402401d0103480c0c0003c4154403070007201c40030751004548217440903d41152001111080203040040c208004082d4205005e00a024219002d080b01c1c0540031140e03c000100c2050b590303442040c4042d00500310b46d582f1100500b0148c050b440c400c0e001d0b1114051f0300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 339487239 1250 339485989 339486001
    0xd2618071d0c120c0f07050d032403020a09020d0b04020a0c030906090513020705032a0708070b04050f01020f0a060902040e03030f06010305092416092904030602031905 74
    0x80e003075441c0010490f100181d982e545071201c900c00c0d0311095200c21800c10510a00c0d0104804200c00000010140c0780084c00d01600c01c042d0070794401c000b03044080310202c04410b00051700d9203191101260098031002d6203800c074150701040034224041c4410b800c6440401c1410b00140e100b02062160360081d00c1ba038001c5910b4240c11a400d500a02899400c0214940c091900341c1070b41e4000c102d40c50151040c0c03410100421306030408540145541060b030f1142d0742c0c085404020900c0900d0007082c1035030007040072a2610001400501843c45810700c2200b0481c489000760b4000c2c0020010703641d94200b515003880013468038000070051144d0603405a071800140c055060000000c880c00354180030003402d0320303a0b2010011006003400411440702c0d4018030340301030501d1107030729400341c1c2000020800c3d1480e80b03401c10030030422030540d03450802000074014040110b40000540490a1f407481102e071280d054010811003170034402c030f90000b071030944004100712103ca85d20204910300b5105001c148030b640c03158 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 339488489 1250 339487239 339487261
    0x4120203040605091302070204020c0601090b040b0d06050403050c10050a050604090201270503010c030203090f0a0f17040b270f03070b070c050904140d2618071d 71
    0x180a0840071030b20402030703050304c1c0c600280c441c200304001d844c02516081d00f650200381643c102c2402422103500560051007403540c14003034501040c0307080c0c50820841e0803043c0081d14103200320303602400c03140c0c0c2c4d400031909051042044070a0510b048084901d00f0360b41c00b13610401001d084034150701c40d0345031501207021440c2c60b01030351180540581da1080700d0480c00080da661141807884290050b080c40350001002e440038000e00c0c1d148076140c0c40050b16442c5c100c040a0900d0442c00c9003100981140d600c60000403810002e4490050b00020740b80908040c004c980d4055100d44d400c000380340b180c04103103081601c5103c088180c505401c0401d0b060781151035070030b10682201c4201401d0f403640210605100080240c40a014214000c070031908055581c0d20114801e51400d4409039a200d2421002c440750003410040161445068038010078250305081e0a2004da01845d900c1011044a6038007103401e0040301488139401d16124002e580c41595504400400d0f03100700140250342d04c51100c00280e4043e01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 339489739 1250 339488489 339488497
    0x3020d05120414100c03020d051b0f161e03022e2406081f0807090e150f18030310050609010c050a060209210c06130e090604120203 58
    0x90200391003640c0755a80d54403906200d0b40510000c038401e5800c4d43c000a040d40c00f50780358142c429140141c0d6000840202c4003940c3c0000c204950314021900341e81c041562440449101d440307a10001a1281001240c440706803032101e40292070149a00000341f84190403421000c04944207400311505141c42401e601d0f4040050349001e40890740307885000c449031140c1e811820b408094000c2d0708044080c1550b40c00d000c480c0c0d0303400000c0014604010400406400c08074191035140074001c6001c1c840c03a20080310f030f940c0010b004000c002030312400c41d9081e001080003180910314141800070780a282c04010f12003070900494000c1c04141401260300050007000c0200c0307010300c40c0180c40b580918106030030300030558050004d00781000316642213840415800c1c0246c19410b48211000b41e0384900e000204103a0800740c0b0402c4014401501c0c04800082d07001641001c01d110a0310420340310f000441641c0340582c41903024148071090102009501400494198807680c401c000b160442680b000c0103e03a240a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 339490989 1250 339489739 339489757
    0x120415260405161d1609050d060507020c03160303200a11040f2705030c030406020a1a150d050c0d0501231e0a06210b0a0c050f070213050405060403020d05 68
    0x520401144000d90f025405c1010b00806080c620411aa03800100300391034406803065801c2c0e07940d1414407030041c3c0d0511030700403485400ca00425021a480840b000701c10304ca07100040a2090b00c91042c60040407080d0140000d10080c402ea40e94017280d82080004900e119219622440c90284152804601881000b140d40d410041200340320b211442651109440050243d58a00c000e114a6404c0d020810060005c0c1546a001d40b40940da503141a144030400d1802901c0000d94103c108080500d640c030300700000c1c20080340d841c8041da4060400500b0030000118564000c00d480c1d841030180710054004090300c0703031021580d88003a0000d03961001c01c5d00040c1c2d030345030300024002803081e20500d10205064004000c0d01c40000e200d95504180c0414607000001c0100000304481c0600c18400c00307220581c0c0c0282101c105204403c1500d000400c1840b0360142c1451122000c1030160075506e805800034040081c0880403c243d04044c2446c5550740000c0b10110010711403000018030551140083d130304800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 339492239 1250 339490989 339491039
    0xc061504150902070206070822050307031a07110d0f090504050405030f0c0f06130605090606010e0103020708040305030a03050103050f0a0f020f04140408030912041526040516 77
    0x1070502005001940c00300c101a0f90016080c00030030049103214000f0600382d03906450300c0040703c080f074410711541140340c4cac040c43c802d40000c0010004654001d08001c0211521180810303650383d0035000f0345100c81104514103451189044d210581504040034500340c1c449a26000c50030340c2d80f2410081625012240142140c01c240801004040140c0107854140240010307106200c0e10100e8051a000080725030345000d1000c100c00070180084c3d032140c180c00600050191903e032030503400181c5488004407000c1c0c101540000c0c42c4c002d004840065501669004081ea80d03030f14166400107002d004c01b80030035255400380c1c1d400821590350005815444036030200c0f03448068000c94003008101d41075080716175045929481d41c1d54032581d01007582c43c422803198014a441c0e003400d1564510f0a240009002071850040000380850716400c3c00c11041403116103804143c0d110041030700c0351902000c51542d030703014000340c09001c100000403c1c0d15003d20240d913a11840180e850f4a03644e0740902002c0c0d010282 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 339493489 1250 339492239 339492281
    0x30506120f120a090806070306030308060103050f04170403080f1b0319080a020705010e1608012c0c0d030e03060a050118090212030c0601050301150e150d0204020c061504 75
    0x30b8210b005400203410504040042964038802e041c05d042d01102c1120001c0d03503450082c000c140d0404100390700100c082c0780c20001031800c80d00c2005011406013000d80f5940c0c8002c0d420b807d40c4110000c80d070103158032588094841d02a0320ba000003581121407211060000794a80d42340300c0b400001550600100341c84152070302d00180000f0385038440e0180a403407146408101040101d0343c24001d41c0b5080e0a204020800114080007542c0d40f0b02d155004110283d05282400c185c0d003e11207950201d148a13070090200249095298074900b17040a102b107900240803522a0041c5030b006280195100020390035a5515a90009114101c84003409400c0050610342c017071804c04031080d80007180032440030b088441411142058945940c1051003120f101c1e43c00940140700e64202070041007190100ba10a05150605100c083d41c01c00c0d40040407044481c098615400c041d945000d84842e210350050b00840d40c0308510000240c5841c4c00310b0340805001001c402407006400c083c858403100c0101c47c00a1611 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 339494739 1250 339493489 339493513
    0x705030d0e01061205100b0415060e0402070b010f090501270c0c02030304140a050621040c05130c0e0904020102120702010e0604090c080c16120519030506120f 70
    0x80003091600001ca65880c10b020494010314500c0c10502c0d03000300014202e1030030b040100b03400d07142d0090825000d5818120748010b049450b40b02001651490b05199030701e1146440820000c0c0203400002d04109805400015000c005032040300603541400000c2c0031503030325004035040100e0300361009081c00310581408811100103a201c0e0780a200c1601d02000358030460b400280c91500a50007410f01c2188900c00110507292166003140140700a0b240e150030004038040b20315400900b5005d001c900020740300010108601c40c0c010b40098800100b1007165500004081b200900c0031080783d401203000e8080d80f4010b0b191a0b807642d8400da60580c0200040d5450480a07802e0350040f9004038140840045100041c2c0d6030100600b000c0d0100b00390000e00115001c40003421036030080d180380c004950400400c0e42e180e59058900c4401c0350000560141721050072011900b0744580c01080ca103007411031481c8406990702d0f0300414040d440c07c850314410a440e22020986540035641e6a00c9664440421010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 339495989 1250 339494739 339494741
    0x6070507031b15110c0c04060e01050f0a080a0b07030b0904021005180d080c1203130204020306060405060309011b0f080a0b04060503070b031f0e0f09030903030705071403030705030d 80
    0x903100b8491021144098501d600e11030507900c20b540600d4a104c03010580c209040e42c1085807041c50041100c0c10300002c4e2815146090000044c06120301403107069640411980380c904a8800501e04002140d103541a00d040075000b01509841e540000390a00d1145092490a11100e2340640d80040c0b440b05100b103419000e98a036071104c8004c18401c560140c000415a40f0326040d094807a01503c0320716543d04d030348200c03a0b042c00003052810394501000c0c014004151024101e0210083d8140c0300141e9030b40307601d00020715038000c0c2e034040c9600a82c00001c0001c50b1906421461400c030810f0035003804a01c4400c0c0035100c5c03246172850358000412980018020b51426040313480b84d0540680001090385d10b407030110303040170300c2da07006040b41c4800001071200d1900c080d1282d115a86d010b0b0450384c2c4140c01c02000d40c0c038000c405000940480d10b0705003c94980c003810302c01c45000075002405c80e91f58400f03516210341c40311410f11504000b110481000304a174200441100e0701c569000300550314110840c0342d214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 339497239 1250 339495989 339496037
    0xc2408070c05070f030c03050706181403070f060c060b01050c12030a0b09041a01060c0201050a030209210714120319090306020a03020319090b1308121005030607050703 74
    0xb4401d0b00ca2101d00042c0003540200a00281d40507644e100e5541d8198100a031402e6010b0b031140080101185003400140901c0790904140c81c43c4820030b5840e198514002803400f5200c0e0040400f9000002002440d69000f195001110348a95400d1224030700c850019a0540143c80a1901c540c104100300000028a0b00c015680040d0303000001503401e610201088083c0c10449007213514501075a01b0312201c0000c00b4003540103001d1031626403c610400e82c0020310030b0003015410410300d42c000c244c0c0890750340c3e00060740642001090500100c0b141c64203040d0b9541d0507600c0ba015000c81b94201041c05410b240d190101c0010301c5600551903c14045c001ca416403a0150f00700c3c080061110000c00012498001003100443c169405a01c80c03d094034004c4910300b0340951204c3c03580ca0030150328006084c8902c1d0350742c0200a8110001c800c001410a44024070500700900d140c040504100225182003422134419280c040c1c088a84c0c41c1d4031003005466034414828081d0218891020200c21010025004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 339498489 1250 339497239 339497243
    0xf0225050d0f170a1206050d020108040602160302071503050112080a14030a090201090509061e0a030c0905090610030503040b0d1103040302060402032e020a030209030a0c2408070c 79
    0x403000180710f0f00c80308114000c0d210000100480050b00740d02c825070101c607540c20103510340c0040001038503020000d24282c88580c0024140700c10300c00050144040c50341540c0076108040000f17402c0031040d1138002d4640b03c49000c0c944803800e22080003043e041c807910a1605907024a004580241d42c9030700c2d00a403d400c018021410406442c55aa55950801c1c000c1c5004d000002c502140a0000344005400d01003a0b41020713000c0d420301d400b086000d98504426082684102c0d20b04c8200000780c102040c5011001e030009000e00942d80700010b0804810340c041449000504160f80d816200d02c1a105008819444050003542c000d001c1400380400e03110003021441418000092075405544550015400c101c4040d809600305a00300030660505008030b141080c1307041040040480c5104c0c1078545640b4941d41a440140d020130800b6441d8060f070704a80c21908001d040342e1400c00306180c0231064403031901503400d410b074104144a280d401c4c4140014035060140d11944031565130320308100c1e0401703039203082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 339499739 1250 339498489 339498503
    0xe151e15071a010b0f032719050601060e061821030d0b0111030409150801110a0e030c15030426040e09060615130b0301060f0225050d 59
    0x4250540030030401000418407030300c4114030340359000340d06415020381640300812001003040f200040c0020745084a601040c0a07055030280040402c1b080c8440990400515061250f951281e0075113100d40c0720800f226200ea0708075107040c0c0c0c8440f0704881041030703c0e2600f074020b10144410800341c24260542c6000103406050b83d4102c900b808450084c1119943c10000c040d00001000b0072210350500031405800e00a0074000b01d21100c0074101c9070f0381c0c450740c0318554420341c5d01c0c241040001410059003004107100c81c020702c080001408081655441582e041c0045030702c140c4040d0310340c00d002c5258070b51500010001544140d50b002c0c42c00490b4402803080303a040c68028031060601d1820329005404c01609100d140e1690b04101c0c0240e61408050a80c103901e178807502c20822a59982d0226841c600c070070054003900e0701c00d00e1342890f000c422a50000706030100d0200000c00d0240d400501e42040c0c1045600710790888880c40c101e8a26271040e181100c803604034081e400d00540c1800f60a00e10311603c6014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 339500989 1250 339499739 339499759
    0xf050307020c04050c0408010e011e18050a0804050102150c040b03070516030203030601030f02090901030f050a1505060a05010c030f08070207031704140307061205060d050a03090e151e 81
    0x20210384081710001d01885001c642405443d4092240080d90501305000708110000d054104605601d12180c000071940c44013207021012402e00b403e032581603801012a20502042d1400303002540003400307454010b21900d40c6259001c1004100307940124280359000740340c6400c20307000359800d5000400b40401d00c0070400095500e4030440540f80c42c6036000f6409951241841000141900d503001d60103015980103010032400b41e40c038401618112a80564208140030b0145404c1e0f00b484086039024000014003000f4500264043e0030082c401d140c2203d000015035221001510101c00406004e80003860500303500c2e199034007604502d41c1001c05401120a00c0e940e81c6d031045070f008020b03900090f8100e4041001c00440b6102000801046003c40150012a0030710100030b0100142d00b41d84030300c030368907540410501e49803c100e2291440d04402070381d1007500d0504001c0c14810652180a06451881000075900c41b0200e0340005c0201d0020250451500525008804032181c031440e10f500901c201 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 339502239 1250 339500989 339501013
    0x19120e130504030206010b070c140f1302070201031d0604030e01090512030903070801060b07120e0d050a021008060a0e0907090501240206190e1006060c0b090c010f05030702 76
    0x2001400c00200400d0214503850507190003801c0490691100c0000c0c042444100001380c4401d0910044d03884400e004803810443c01c000030302d01c4029410303203500000e00c003400203261441c0b074004018050003030302c0074802200b4014801300d8030103d1590b6580c0d2608004080390001e84103010703055000c0d0051510039807898071080021007039040c1140300400b5600004115207981030070311a110013030100c10000c100305454181000460711440900030b01040e00030b10341141f518000d0000d051510800f0300211b100450a01c0c10715071320080e4100682c45005481e90303080880b40720b81501c2d0300c20038000c1c0140740c2d102c1c5041001c004950b0080d00c010480e00410700b0110340d0900b01c0c41854001d110101c440254240e2002490503c10415001031085400020402022030280c1445008507090004001801c41e59070240c0e03400e2080c140006200181800070010b001940002445642409809048441e403200300c40d142d80c0321818596540418031030a60003104a02541c080c1d0303400f0301c6500507600450002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 339503489 1250 339502239 339502249
    0xa0b060d0c090c02070812031e090102070501061706130507050d020d02040c0c03111209090c0c0f01061701090506070302070812041b090e0c0f0402090402040e041419120e 75
    0x8200840c0142c0c440d0204100d40a400c0100f401e8147ca110001c030700c1c600f0030010118005011078001c10701c0b4902c00340855603500003507044882d0560000002c01c84151180b491100c001d00c00210740d06c184c800c0e00d000c540340d0340c00e811844030410303070003802003c41d2844c1c4000d10022202802d0f040c2d034000c180000303040c05600c030760080b880d01c002030369148503114059240180581218090070100760b8011403201400300b10160484451410840b1801265540c0101c04085803084403101070303060050b2082d4196684054003da815140301640403404480d0008480342200d40c1c001d0301074080d50008000c54207060107540103000031400381d00e0a45c41d10f0140e10100520500561302100c169000465002d40f050741c045044001c1c0190110601a81d461048c2841c0da0f400c103a0012413144c5140182400f80e40d540c3d50446110a10240082d0b4840d65030f0007003840608021581a250510050303100c0001c0c180201300219210014004c0c1e104001d11030300c1e110008898030520702c0c280550489030b60081c0e603070303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 339504739 1250 339503489 339503501
    0x61305040b0109052202010c151a0418020d0b13081209060f040b0403200d090504200a030b03101a1e0307180204090204081b030a0b060d0c09 62
    0x700000302040d40750080403030440d0801060310300010150b40034400640032420181076081c0d02441c10203607981e16404c0041201600360401c44019181c954488001d9440c20042c001c02e200440d0300700858030b180801144403001c0214000d502031401050322000030340387c44c000794008031110040c4215560715968564560310110243c00003114200c20041c50390002c00c1300781c0d480002440d401a160900341d50f403080030310300900002d06104005000d01d403110701d03405030300289071440c904031100031016400c0036000b90f2050043c01e018a0410800c5111158800c2c101300904a00545035032030b0880041086009200c2441c5280d8540104d00c1030309010449800381d50725210030f00c200107094507803803000c100c00c5c504548041c001d1204a41980c0e6100d66021034a00120f0301c10200030100d441e61500003a009204a4000445a91000c58040780082000580000c03640c420030840c03032004075120400d55542c0303009000401a1609800040b4a07050100d50100264419210408080e458131740388025200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 339505989 1250 339504739 339504743
    0x3020a0e0109180b060105280c11092206060503010c03240b1801030603060504030f0f09050604060518101e1e050309160905010603060801020a1706130504 68
    0x368038001801190500d209240785a074800e085003250080e241e60f448412140100b07582c0c103000000c2840800c01129207030080c14160212802c20301c20104105c05013468405a406907185500c00303048140a0501507a200e00031080c00c2d40b12000440803040304004007020920880b91151142e40c001440e4609009001500485440108080c2039855a12410b003010443d44405501d044000f0400807540c0310880720801d09500f00400001d02e03403801a80501101d51000380700d1440c003401c10052590141c0d940c4107a5007503989104010b000701e076040743c4070100f40c010141d120408000411255024800400300710100042c201c2402c510440000e400da0380d200e0320140401c024011182000e400c103d0300c3d820f803e14a00b4044590084840300e55072160070b400c240d505009000000c9604c82404000f913003c94006410364010032038a84000d10081d05d02841442c0100c3d0501c60702052100040c029641002a290350fa0840c50400c0c40f4800c42142001d0b042907001102c00381d8030000c41c41503000c1c242c4918 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 339507239 1250 339505989 339506009
    0xc03030c1c0b0f04050c1209150f010f1809061a13060803030402090a11030108030901300f020c010c051c050606160303270606050319081303020a 64
    0x10206044581600128a200040c1403510845244658540c8a41c42103503c050b1000100e0f550b81d00c070a0010b038407a003803080e1090600b84003081007920f030005420903640511711801b5441d0320340e0118145000400e00584600c9403082005101cad08156070900d0074115004840404c030203d032515000c04480c07000c802e594500039811058041418021100110302891000170000e546c035081625480303010182c00284500c06140102c0e1203949203030400d20310b8810b00e569003940c95035500002c0382c0d2030f40b100381090f02041d8810045088031385031013482c40c10410041501355040628800c41e400a140444c02d00741c116500b40400400c0b940d091041c03101c009016150309036240345500304156244410014812098144020807155403a444e05541a100b0800c208486041040c901a006084a181707040c4040f03842113440780741c10058118070504903000d1582040010f8890f014140c4880d080408001c0c801c1d007079070420b80020020002010052500e1550308152526a400070307244a0f296804090070b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 339508489 1250 339507239 339507247
    0x1b0a0f11010f02030a0e28080d09120f0b07270f0e010506040611030c030a0903060e15070f02072606090303090709020904090c03080d0f02070f0204110c03030c 70
    0x203542c01014140e048000750004505018801e94000e10184c64110a43e0152540007100c45180319048445c4009003070303d0510881142e00d41000b555075149c89080680001e02c0c00030700080c2004d0845109100b183c2201c1d078142150708a0320307500c50044014101c0000c00c00721001404030b03002052408840041c82c04400c0c2c0c13030035160494100c030900080e000707482e01c080d2910041007036503101400c40d02101d5841c20284015213800b00aa410350050f800c2e021003600000135080340c3c50b584001920181c900c5008200701e0280c01c40d84155403500f6001802542a90813400f14808902680c4003003028081c2e8812a0078158541da025202201c400c50301803031030204038100364407901c41408425800002c142c000e40c00d618002c080580e0728000c503c51030070030641c00130720380341c0076211508551107241d00600c0c0e280c5031560383c0c81e02d490684d00c18050961050324100955002d40818000c8601e4660011444140c11255408000042014581c81e24400c1c00800c44804400c0c81800a0f510a01e802414640c607 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 339509739 1250 339508489 339508523
    0x5120304110909030913020c0d0e0114040807151803150b0307080d0f1103030708070504080f0f0c0102160e060109080f0a0515060102030a03050727050a0501030207081b0a0f 76
    0x40e4154880c01012007e005201c14000450000351502e07000c142071400488040b034010050300c09990301521390120600008000c0703100340f030000702401103500c041e1603904c600d18180d07021600c850000c0c4074900b8005c5030031009c0000c2003d8000000012000303490014284e505540042d10f005202e034023601e0b164124042c1d81441d02e0f08060500b40c6001c0904000700071001c90f000f00758603480000e03d59001e1041c8000421035440c0303da03080d14007428003001121000c841c0144403541d20542f03404038031040e1081020310802944082a243d600820b440d901d250380a00b4040c620301d5400e4010040307030410100794000038500d2020032540c40401c1043c00501180c1e40e480c20018208104600b180c45007200c014240402d030b990000450700501c0c60f500d0b0000c1d030390b2900d4000303c4502641520391021015892500e524034592000f5240454904a9180c03002c0b5950714010340503401842000341034804c0038480104a4401c24110700342c2101a20150750b000c41065072060b550840d4001d00f900d1141604a2a100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 339510989 1250 339509739 339509749
    0x7230901050a05011e05070b0903220b0a0c0f0203070303050c0606040902220902030d02031216050703052b09030806090c0d0b0d08280309051203041109090309 70
    0x40944030a8402a0800f8180000a400c601d203500316228818a20341112045900c83c03810384003050380c89000c0812508109801c2c5940e60056103c02c4100801c04551810425a505056044030862640c0314108414200192844409848107903a6003008906600042c1d8061105002840c4603840d050f8581701e45c1071069242600003010503001c0c510300048000580d41e00b60045100150443c6004400041070b03241c0e002400c0040402909407203183e0101d9601074020001e0803900820b02805040c1e039480d1003034001400003880d1140e011038010801036002c00c1c420801000350703080c0442a1007403032082c540100221246003c0c08409140d4801c4944200b65005c1000340d080780c01221003110f1130411183c030030a0342c401d0128100700d056852440e43c0c2030761903000250003100c3e00458102d8940800e00942c40503106082c4c5440b400c102c038080b084062034024070071804559040401000c10012084d11101d43d940090426690f940240020f1079607a0b83d0710020601c20358444014640f60700104040c05 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 339512239 1250 339510989 339510991
    0x5011b08090d020102070506010302040b03010e060f090d02160b07210c020414100b0c15090303070e0312070602160f0302010e0d0504030b0402040c200d0e0a06020618072309 76
    0x100316401082046c002c1800082c1c3c0c6815a80c0486001601c5072580b0b000030b00410012021100c54052842000f58050490300c0e01c3e48601007034800e032000810005412030312188191640d00418118035014442042c3c0030025065640c800e1110000000941414031f1180c81d885d19000005800c510031001182460300504043d00d0072254000e031035090403d0300e03461116040c011210a200045000209181c00b044002084072010000d0b0b0700d141480c1c1511603c07a401150000c001c03421050001001d8100080c1100005a4454071300b828031a49a071050040d520498422800c00c08640300e540106200e00d15060100f8440d23000000c045101114960030011850341020030306c0302c1800100049180c0707400e0940e0060703045800080c00c0f00950015a801807e0f0002d601c484400c6c00540691240e00244810f20121a61559031082c119141003000d2007203a8000e10006801160100d1540d0420f507580501407620102910185074603003038101c40d82100c880d08202d1010100110b240c450801d000c0076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 339513489 1250 339512239 339512263
    0x90c030b01090f0e0c12030f1803010c050c060f070212031f14010221040e0c070507091a210d0e010e0a1508070c06051008010510050a1205011b0809 65
    0x7400010550551151030f0721740c2181e9035000d01041d030320301c02032040240105c1e18003034071101207503031244802c0d080c2c081b840d0002840380f4000c0d86030410080946010b403054400400001c5c0c020204ca599840001e194000040d000c2015403107807904d294080801072000e5440340f030203000710303048a015900a44070500f101d07a00051801c41c43d200080566640400c0320380d11050340c840e0b0500b6180c90101c1040091280b80d20403001c220038038061150603401c4000070300e4618050b0f400c88502030b4403032070000111010462014502d0360484200300c040e060186106a000e004a00400303500143c085a00c0d0515014000400c009000f000c2c06000540e003110801d00c240c401510042085400c143c0918200e42991404806020a660024010074480d05002c01c0e90707913104d81c080c016824504141242c904c01d500991000d5401d10740004d200038103000286048410050080320400d1519844415440d280c0c102a00e040d520b03110b01c0a00d100c80000100360403052642d03001045c0c94191105400c0903400d1b00c1c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 339514739 1250 339513489 339513491
    0x10206150603011707050d12140a0816050705060a052403120c1603080304020f01110606040506040207080c070e0f010305280b040b0a06080f150406090c030b01090f 72
    0x161861a80300d40782980d054641c141030454100780c02e40c00892400c045580120381c0b005401542c0713030410103030f4491001180d07445d4440c4040701900c000000d51900a45000500048808000a581c0d0000103405044c101450415078503082c0c45454207810014204c8826090588490a01003482c006010384003062407016200f00300095040002038841e400d11030102540807000c40c01d080806c20030302108106042403514607040950b00e11b01012545c204840507031203803048aa140403294011466003091003200310142c01182d41d071070204070080c0005810180c20a80c203112420000f100d01004001c030021000080001034908403d601c0c0c0301d0b100a207400b4900703001400420000d2800102003c1090f044144902c142c01d6417440082c0e014401080035020200080038403080c0003401940034003540b1881014402c0988480d041942d500301c90085181c107074042c01a030100c501c400c120003504130b48210004200c17004180c645044800c408e070419030381004c4a0004101052a5118136840d0b0b140f40c83c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 339515989 1250 339514739 339514771
    0x91502030901080a1d06090106060207050907050901030933050711070608072f01150807030303111b060a0b0f01090e09100e030d1118190e0a0b010206 66
    0x911201c000b408030001d031520383c68a441c44140741140700402050f03445c106c600d03034a8100d078800c2c080c0005228000140c007645c0c1e400301d036500301800000d119400680718285403e00940044004204289068512440303100f2a12407000300454400e9000205451b040040d00b0f084542c48116080900910188192445554407500e004030f21201100e00a040c00d0585170b561981c1984d14110382c5402c03030600c500c030580045500d005000101074101018008002d22159840e101a003c21340d40254040b0364400c28081002911940011580c80e807484202401c00c84012082141c221105042c031002e90484410040b4445d030328840c6d04a004402ca904001242601e0000f8000d140340b03001e012000c07940c8000060f0440d00402580341704200c00355003000800710464181c2c0c0c8913003101e8440c511a40c100b04021260411010a0301c2e850441d54420b06220b1002c03000300070942c4011400700c03404901242000882c0703859a180144100c0d60a500030500c0310118000a003801c2d07000b0316851001c001c0d20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 339517239 1250 339515989 339516007
    0xe1b04060302010e1c060c09031208040206031603090f0b011e0e040809031510150918200406020604060b0d0c170307051b091012060b04020f070309150203 68
    0x4050113102a005540b56080c1c40344501c0c40c020200300380780d8041c140320306010403043e40d2a44841c0d03882c00c480c040c18028403880c024000440d00340b08240d070069400501400802c0d82810980f51607055803405040000d01402c2e50754030710703801050700d1700300b40e4600303a00d440100300d03c9000384811850031403010010310320303a400c150380e03480e400002070005049480c0201d24188030361010018820014640f03e00c400d040e00e05440407513407954450040b003621941c140c08403a000360003601202c0030303910042c03d1580d0037880003d920004088035224002407240c0101c00319411035035817000300080c02c1107601401c01ca203490300341034003514010b03100b0700d00401300c40d0f6004000c47d401985207019202421164040380d50f4000c0d00074514080c3d450040e115001c0d001c080d00101d602046200c400843c2a11600740c0d170f076180700039500110a18401c82c0c1c0f0800420b80544002549540204000034008000605080c0810b40b07403610303600025001c4001ca9201c01003070242d0001c034040c02d181d94005200440c41c0060b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 339518489 1250 339517239 339517247
    0x406020124090b01050919090b040903050904090c0b0403050609010b0a0b0910030f020d09050c04200c07090216020406050411040e090109051f060909031e120e1b0406030201 76
    0x141c070508820700d80d280043d40c03541e84150f044440c0320714000c001d0000320320b028a4900c807030380403489240001032821103800d019050601542c407105416031219400c0c46180014040504040c107011102e150300c1c020049041081c00c400740c406980a81c006150520b42101c480d4212404900918810080540300b0040e840e4403500311641080c003070300d42d0038403000390346d40c2500504000080c00841a002142c0d50b007074203072240e002505241c0540e01b103a031002c00001c240030844000f0048011800303070444045600380c104070021322411100300c1c03c0310301d10307540e401088013244c003c600940f50b1004094000340652074140a80400f070001110200b04101030090741e02c007a80b0507403003002001100c031400219505030a5104408035600310082e00c1500c60100c24045503282901c1c00410300c0c910700f91020620960501c9000c403910751540700c10071103a2006140760f0065103400c41c89010400c01a05141c407544036802079441480300c0390010005440c5980038076000c0002c0500e1b141c0500c5c50f20004201503030380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 339519739 1250 339518489 339518561
    0x708070312050a111207050111121b2a060a0e0601091802030a06090209090d2f070e07170f150112050f0f060f100e0f0a080304060201 59
    0x10740c10100d95075410030300700f902e40201d8001d01203628050142c400613803c2440d00240a00d80c49000204600d81042d100307104c8a00581d80788600d182c5c09280014260802ea824005000b200300800c20308007a60a0b00f04041180018000c4118105010241d02c3c02c0c03108200b121b07004202203d080c0722208548420b40da861030b052165400440c0c4800d0b01c00d80c40d2101e900366040d0340741c001e4140c6451101a080840141172503442c03c9005103211750010710301305804240c135245007aa907900c84080805040420990030002d503060341c40382c40d45404030324594404001040083c540340060224500d0809005010401c180c0104c40020400c5c404000c1e8001030b0411090340a64050070406c444804940101c0d03c10340304410307480c01e081c80c01007401b01c103050650300c0500c1500035014042c00c1c3c1d5502c1040c0031001c84400c01075500101102402d01d00329002c0c0203100710040015000c0d45400c030518000910303480340d59101682c190400201884040c3d821301500444c40c01001d544d844480301040040e0000394 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 339520989 1250 339519739 339519773
    0xa020906010c060501030b1b0c060105040902010905031621030912050106230a0f1d0a3309060f120303062d09050618041e031107080703 60
    0x612000000d005a004480544019401c080200310070b603101d144c29030303e862007950055020011010080d5492104a045078003126640002c1d105503480d11040c88080c11850b0412414400d94070004180303900c003042408044d50298007001c1e136403403502105401e400208100e2100c2030503403025460200303030004d40100c121074030901e2104242c402400c0141c010308003034010031101e041104440e40c10707041d400c09100d041e100403210720103841c2e5a42c40c19240b10449110305070745694101c2c11175145174100d8001ca40d002004c403202040d001201c0c0394071803100c010501c003c244c154035404440400b09415241001a00900c1010070802d0f042130400d50000606108a4036034042c1180418105446a040352005000c3c01e1810402c82210488203509a914203040d6030f0001c0e40340400040129581c010076015110141140c4413581c2045064080c800d0010020740d0b0210004080d114019904610142642d0003541c6481e1000d419000d01820504640c0c48240e255020f25418000304074014100c0850030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 339522239 1250 339520989 339520999
    0xc020d060c39060e07081e060115050a0c060507200a051f0216030c0302010c02210a03020c070b070b01090504050d031d0d261b09190801020a0801080307050a02 70
    0x300d02d850400060203000c0f0392550103000d0000000703501c04000a00b809845104041410400f641c240110b9444000344206d43c644070800e40c10818640c040c100a081c6c9130300a140948502d03d5645a102c2520f406448040c00240c03040b4460706900000000c0802c0e07440b13004060101840d89031203080c0c1e101440100c0704246400c40c1a49001c4030f4403581111135003030401c02c85001d100d00a06001d403030792138240c2c82540503500b845406044144082090092084e2003503a40190401e010803080c2c0b1034121000041c141907003004480e1007250104035102c0200fa800c96071f540c4d00c03025403802481203041a0700166455003090b040c08000f074000701e141c0f050101c0074600007600c1800c0a0072400e540c448010314124034014040c50705811030344814007445210a0803c0c5d440d80325100600c500000408480e0507444d01e0400c5c416000c202c48a00c000c04114200403c070600c40700d132a83c40510301d05103981c0040e074269400220038907015000f101031401004460b0246042800b1512040d4031810742201c000d103d2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 339523489 1250 339522239 339522347
    0x507050a11010c1502030103060c08061503060a230103150b1c090b04050604020325030f080405060d0b15030411040906020c0a0302070305010506091006030b010c020d060c 75
    0x1070b40f180300c0c501c20107600401c100c185002241d000354000e40c0280415101c0c01d041048911b03580b030282c03900038040c003006048405481c0c0a46c103441800c0d04054445a4440300c802000699070b142401c090b203174500c03841c1600c54007202200000d021074800291450741804544004c000e0b15a940d0160340c0d0454445c003010710a90b24040c0300c3d500030600000d008090702000b20500060000015805200f180b0076822946000c040d0a810000c0080c0114003140340b1540c04010b10015003c0240c44215500c280c004904081d00e41c40080c0302074002c814103680e483d6491801480c02d140111550040000780c00285146003065100c0401d114040d545160103541c94004000030400940d040302d2041c0704800540b041003141c0d14000b0b40310f403c6d51006035450340c2040c0110701c4c40c1c40c05402690141c07142580c4407240c60301d050010b402800d0201c60039814400d521034031078013585403004202c0381c481c450074001420701419100648001440310710301000300484c0d40007008540207418005500580c002050900c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 339524739 1250 339523489 339523523
    0x50702010207030b0c030f180a110d0b0405160b040506161103070915080309010f080405010b060307050a1b0213020c030d09080318010b030d0c020f030d0f0f0507050a 73
    0x150901543c0028041c4071800104805030407080055030041000c55080c6000791a825800d82c0300351580200040640c2141280c900040e42544031900b5525001d03002099198581d00c034056039039000c880644090b0084600013144180f03204585016090084c2030605150901c3e0114000e1b0003220032180d0161924415502809140070010100886c02421148001e0301c90041c00041c06050007086444145100c001c141c3c6070011040e20084038040c0d540041a00b0100b40441d4507000c041c00a03940365580c1c03a2542070580b2064002c40c821030710b50300c0c0c01c2d60780c2070201001403208012000c02c0d0f4106004600440060303071131541c026002130450501584800000c40f40791b04500c6045003c20f031461400049000300507000015500c610060341c46900a824504122802d86a00c03044e8075906810000c03082c4075013802102d8900305580003900b9406e00511100c042850024040001008210700441d501c0c0425030100703010000b18107628100b81407008541d01c2e242e80307041075000100025081d20003c0c1c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 339525989 1250 339524739 339524743
    0x6080a0906060b04090b030601360f140f0f040201050a020c0306091005070903080403240905010b041512060506010507120503071704020603040620130513050106050a0507020102 78
    0x40e001d810100c10882c190f620241085294440c0c4904103000e81000b040c070350149804036101d4103c5854400e03200e240c450440f80506030b040b8018500c01c3c1d00a218000e40c10711600c62150002e0700e1501c403400111980d580c0f01c217144202005010707995401c1c00304200714503003d00c4455941c00c88e60a081941d00c6041200f0180e050248403094039030148640d13801c01c1094034001400705645c500c000f0080180e501c7d0350004640d2001180009011014101300810002e03030b08868100900c0440020300c0f81145944081e0410b8500e104006d0707074169150321142080746464070550a0501d4085014081140346c03201c40c05026540260190900faa03a0300021460790082c0211a9080d84c0b040c90824001c0d030038030f009001034100b41c1e500700020320404140e01c3e62f00000c01c42c4900690300200782908590391a5a03d10140460110700c5004c14207c4c080e4421581003d8050881d0040402c00c41d03240324201020b0040107540045c40800e43d506020041207482c1d003180850b40043c20910b00036036a0b98090006078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 339527239 1250 339525989 339526001
    0x1050102030703030e07170304182a020109020d030503060a0902160201080406060b041d01061404031e02061303150504030801060c080f03040605251b060615020307030206100f06080a 80
    0x3c2c1f41542c082c1d40010b0405020008000780e03014181d00b40301170340800e04800304541800780c0c0c0f20b0031085a490140c00220386480d40d6000c85240d8400880d910449502180741c039025408201c0c007052010007409024607060100348098000c012045051005048840c407003100b080c440039060200000220301400366503000319024080c100740c100e0b643d507079810503041180748640d9030f40d109245c2d034400860070710f22035129410a10a0801038905150450303d40d0300741a15446040d109032400111a030005132101d0010f4003c03c1200c2580c0c0c030350189141003011141044507200c1e04600d01e000c0411001907004803000b03040d03915614010741100003030300d0106114403440d036108101e41c1001c0100420490650841d5115403400c01100042c00040c00042c1c0381c0b090101c00001c0840c42071900d40384098402001a00c402c1c2c0200d1010030b1059030394810403041e003400c41e04240140c2001900000303064041041c5900280c010341c008c00440d01e08035010b81070180602030072040100c21030210301d800034035800c20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 339528489 1250 339527239 339527249
    0x30503270d050712090305060118180501020d06080109171b0a0b060a060503061311090d0b010602120724020c150f06011d1306080604050105040312020301050102030703030e07 77
    0xc85a039020710301e0103455a000804100c0740441008040703402203101c0c000c20b10403030358080300818403642400c00089d12440c05e606800052a0307548071aa01000783e603d05c5440d00b43c0200001661290350200c1c1d08103071000794012040ca40c1c1000e60000c0010300001040191030211030006480340c141c00c036140c10fa2082000d51642034404c100c0311009025003021051b0089000700c030b0b900b0889980d414103460328042207901c1c4d44d100900010540c695801600850f442040c0740520500d000d06400c0020420212201e0642d0785200080040c48669010804007002e161921105414070300181c0c1c440710050084061803400c242c1c00002c9419240e280d4060300c52540031b8006403084174402d120702c82003000c3c040303034030700303617034200f200c00304110754083c864490701502a030004a00107034124040c8401c01d00ca0766010a400d0b40d40d2100015201c400b03000340d9020703c1c400c400108150410303003402880c3c071f4241d5507604045841007004201c00da03000012145d00c0c650609010071070030340003180a4240b9000350b01c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 339529739 1250 339528489 339528493
    0x80616120207030203120f090601170c0d050f07080a0c050409080703050f0d021209060610020a02151308070603110a05030f1005090112050f0115170a0615081903050327 74
    0x2071041f20380050028522407035003d000c440c45a030381d0f0034400012100741c0c40c0900c1a85c00010b86109603082040c603030020a40144c0484400c00b00907070b0424074010240e40301444030380149140404000c0180348400040c5001c0724103100c02c5549441700034180c400c01400800b031203070000e402e247c00703c2d00c0026174810345141c880840d200e010041d0003a20100c0102c2c1c3c058024002d000008649213082620020250442c4d07005005418980e4240074142d1030306608403810800500c00d000400314890902c0b80a003010000bd084210b01e07010700902a680042e4581e00c03188010700182581d40d5025080d41c0d442200011020240c3d10748002d00d540200701a0416a00b0400100010412501e000010040c0303e00c600201d91036800040c11003400ca980c0e40c0e84504603444a040704201c0c440c44181c0040c201a200d00c10b503041101560347d240115061307462209048280315108110307041042c000241c2c0001c00100110640030142d4009000c4e00c00201000801250342e00401c1010304802141e24a284038002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 339530989 1250 339529739 339529741
    0x15030a0608070b5a0a03150e010503060a1109030a0804140402040f09050603030f03070e090901020307020d1803020901140906120303040f03050c011508061612020703020312 76
    0x2141d540c0b03035884140303215100c9a2480319000c001c83d44c0703442d40103109000c90040da04800d014040b50010060100251a40900701c02911000940c020050000b0b40e865200000c010070141005a141c15035907008044c1802e4420041202d80c602182040e40000d00080c00600300001a4204500f40580c01c04250103114458082c410400c1503c0104203417a140b80d05d13241d600c002d2030104400c1c0e1060380107000104022000070442a82c6035042140c02c0309000741039a04025050314414002c1d01708444010014159600c9020241414103506030072152200003585940340c40346001c2d6582c808030010b541081106110030292818100c00c0001031a80140030a005503500c03080301d60381c400f90310692485a10b81c840403801d1450090446847d4855842c0a581160b07200c1d00e640b1161481243c064082c080c0c2000a4074207401c2c2031103818040c186915110703986604212400e4a03180f0020455049103e00b81c02048215410848420b01c0c4030420402581c0e0300c4c010300c0c0480c10350040c65900114810248 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 339532239 1250 339530989 339530999
    0x180203060111030a092d0314150a0510210f020f04110d0f0204030512070318080a030e01180e041a01120318031e0c050909100e01090215030a060807 65
    0x8042841120395500c032506c140358040c40c3c90074110704c40491500c0c01060b0311000b0400610611103014400c241003040da007400c6040348986500746011a802e4001e15a82c904000c00d1100c040f0504020b04950780384040500c104881058590981550241140d020b28036418119541c10901c008402c01c041c1051290803801c00c0e1480d115000300990281e40f60402028a00311025842035a0440313802070020201c001d0660718801c0300d607020350741c01d804000c0c000100c2d441c040701540544005004800003020341507201e050041c1f0844400c0d000030f041041d8100d2907004042948540420783d1042c02c101380ca652240d00d0116170b01c24014004500507400c0e00000262550b55007110030741c1c02e000ba1a202800741105182420340c02690100030180d10004e03e41004480048014541c5141b2501e200306040d512203001aa0080003190103800136807240d88031000080c51030046010104600000303010018690340010301221091001d582c4014011001600401c81608010028040d160940d141c4503150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 339533489 1250 339532239 339532247
    0xc030203070c150615030f0e030f0406080c041d0103020f0a05090a1a03070801060333050402030a05010608030307090503120403020d030c0f050a032d0302090301140c0d05060a180203060111030a 85
    0x28111f82c002c80f8a8901c00340c0030340c0004000c540c407040c800342400b4039150800c001a192080c028068a001d00010b100c08a0116400a100c0701c051035001071802e92580b44d4810801d880880221480c0155081c250800c00ca45030902115005084000c001c155400000c0c0041c080400c0a0320341c940c18450300e41c00040300c04043d030203201581d003c1d109120304070040d55903003a560344d56030322a02038a020b0700301210501000e66109680240c802000d035244541a070310740c0c41c01c0d0f43d80c46d00110156000041841005130308840e40702c000305800d03009000d01d0600c00c0d13040036450007a84070103801101c5036502a41094410300e960b4900a6106494000b100c5140c180070769914040c20007100456240c52940302a00320401048004580311150380c0318842d0074a134100c010307400034842c180d01507403500307040031550031090a428032401c490800b90b03803690110f000355401d6440184c07640780a4840b20105010400c07051400c01054140000050703500d0f2076100040f644041e000c000c61120340800b0444902c840e500c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 339534739 1250 339533489 339533501
    0x40203040f02010906020a0305090922060f0501060f092112020718020405030c1201021b030316110304090b031c022406011b0c270c030203070c15061503 67
    0x1381d0701c4054080d1201826a5110210791024001c20303000d1004219a1a1131901c1c240d100445c04e040c110120b0403c0003001c8070881495044030301c02d032603d003a0311989000d4842e460040c1114540500c540903e0a4082c0c02d50105000d022800d44040c40340e40c0031420450444a0002c0d803110034a4a80282a040251101418007451071014440040904d1100c01402a03605990005015160482e9164104900e101d54807090b1004d03550207101c180200b08811000071407031149080655900d00d0b26a001c1090390f40000303440340910200e526110041c1c04000301f5039040e2124644c0c0080c5c144040c0000030f10342200701110150140c9001003c100c05035020400c610540c4803010000744220401c000391180c440102c85450014200c04c03529520000c051000282d4140541c082500c202d48507111800240b109403031000c04035001b600130882640785440380b0714032501d031860b0450642c00c0450001b410b80c0d40640028000b4404a40f1a1100d140d50368400c200400c10082140842800c1e01c2020380070300a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 339535989 1250 339534739 339534743
    0x3120c03030b04061d07020a08030702010c08090d02061810020f071a060319080705060103110a0f12020d03032306040e0c031c1704050604060b01021605011b02040203040f 75
    0x41050688540da0800c0c0c042d01085da1502c10a40122611001662007001c0c401001007045210720500500800c0e018002140683c8a079800072520f240624806480e10401404019003079002c0031810440d0b07507000c640e540c1c10034142000d6480d02010708400503c1c00e0300e01841f458809200180c5941a40001c100400110713100e078945201010340d80c0c41c0c04c20400030440b503468243d00700441c01080300c11105183c0003580e10440c9001d041149644613289080e900740c000b2184450302004081c0300b403906c880310400a2018030715aa000e035040c2019150360385856074009001d4200784136007404160003504900e00d0822442010381d502488244242e5821005444143c021890000130700070300c20b8080b07509104030001a005280d506408881500b60456502202c402c106114242121f0b0007c02000c2d5130081e40504014600c40c100b5042860449100760309144c150340c00741e0100804ca0301154459030032590b007400c00c01d06d1000b02000107201e0b03105a03000250f2080c800000c0004100e0111b4140084034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 339537239 1250 339535989 339535991
    0x2010606030c0e03100209011407081b03160b0601090e1f05012a1a0403080601020709061203120608030c07030c0509040b240d03110f19080d0603120c0303 68
    0x44058009480f6460b0f10098541c058101d83c1400c080301e8465002020442010316001020f981c8110700f4410503044020220786c0544001015046088042103140001c0c50203400385250010b00c0d14041712200001d80010441e050a000040d181da010703200d6a00204049000e040c0d20340380210740304298a182441c0c0d01c060420480c17000c00e4070351240703039003c11000c1c2c55120807080e12040141c180030700141d43c0048454087c904003012090190003102c0303000d42e1094849001c0c0c0d0825a001900384611030704031703448403480e1260400088803c0300950346207603018241414040c0070207100c04090007240e04016150b200004031041d1501d8002a980f0031640a441c640b04c0058035107003000b01102058034060700c1c6d030703a18070003044210112003403d281ea1204281c8141820883c000030642599402ca01600803504c0000030382542c60341403003041018407030a0017404924040d860901d449400e0a04003501c1c3d400c001c507014464488a500c1000510740052011641d0301c11454003d1000410681c110006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 339538489 1250 339537239 339537251
    0x110303240a03060b01180b040501080a110a12060503030708030a0c0306080f0a021503010803030718030218040b06150d2f0403030f090b0a14120114040c02120d150e070201060603 78
    0x3101b84884004140c40110700d0841c5060300d0030004681e1700c040900340d1400755a0741d0845910040c1f0390401040090401d07111034054406610200c01141c905a00c1079002c3d4101304040400941024103c3c2e5000500020024082c1080e52080300104000c0d0004480c9218010481070320480005800040350702c21200700c440381c11800044c0c0c416000a10a040c40c0d40e2040c4041400c85014190b200c81c04002403086a14640c0d698000030301c01c070011000545049624030600c81401202200e860707001b40103454015024200a101c2c0500303204c0c13164490117069840d40129000e00002a0441c000c000e51207894100ca00000c0c041d05003640a80701c110086010301f0501c42c80035006000e00303070494070b60f44c80d0142401c0c2c1c10001554801d030b0240c4d1480415004024452800205002d018040c288203d55103040c501e840081c803089030304491110b003d540c0621a54491110050300312030311070b202c542c00804d10350841040e000c0307440030030342080c080094aa81040340c600c0d0305502031000c13100203907414420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 339539739 1250 339538489 339538517
    0xc0f06090c050423040f02150a030617010b150f0f04081501080d0c03030906020d020d0b0a05010903020a14010c1211060714070b100515030402090106110303240a03060b01 75
    0x5804403041c4c0c110342071401d000000380841c0009146840007400944050248025a2484031030ba5110705c8200000c81d039a034105002c202c41c2c0545a4034840c0031580200b180c89c61010005204807606502c8000d002c80c00140c0c40004942d802c00e850007031002c01501504c490f101d00c40315072a0000707400231074105041c9000004001800041080f120301841e100d400da0100c0c5a101240902641c140550712980c0030400300518150074070081010440820b000105940000f00704500042c903580310904114442c10140050380ea030201c5042240d0100d05003441ea054a400169680700403c000646904c0356151200381036600004040104c408038001d65405540d04ca2003690502d00c0f034500703290441c4045c4840c400044440356100e80007441c0000b0a075100f0382d50400216223000440a5102025000c000d2008605104d06102d001d004079003080c142030b94a040c4216960701004047d01e00750b80d43d0070ba8500407280c0c07041ca01c42c80040301900c2038151640300d08008024240602090f400940c4a0500c206 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 339540989 1250 339539739 339539771
    0xf0d1406061303061a0901030f0636050a02060307050414040501140603091c0f031d12070602090a1403060f040309050121020427020a020d0c0f06090c0504 68
    0x50103045a0807811101410344c0c41d5000200840301c1107044111114800320125500c100c04c5c03074025481102183c4912a40c0c0c07030000140e0710400c00061000d010f403041904440f00c41c030044a181d0306c1050008009800c0c03401d0003840c041c003450b40650450000828021b403164800024019100007078614501107100c03c041c03104a810900c6007001c91050041d103034803540380040085030401d5450084902d0f9403171840025503055882000c2001045005200360302c4079400d409100070b00440c4a0b901e100c042c0300ca0345404c0e103c40d005442c120700785100040d0300302005181c0d0305641001e94040c02c45418951940050344070300e0310400807203101c1e100d0b0100040782d5048099400e441a07516546990b00345107800c0054038180c80b40762140c02c07101d00c660200003560010344060802000c00603004c15070b00200c20049001003941841c540340301c90040000d90200e94000942c140f0101613440c07d4100111281014070400c140c5000c01800c460602ca1050700b4400002e9490007a290300b2a401c00c001900544220 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 339542239 1250 339540989 339540997
    0x6100203090d0b040f020a08031305040506030309100203130b07060506030a030e06160f080d0b03060702030f091f080901060b04270e060a1a01092304020f0d140606 72
    0x2c0d8000c41108805001961010300303070780c200784079150020f5002415400500383d06a50740040e801c039440030511742c042c0c0f045000010020841501c04210500b081b2022170703168440c10a0f518001c20702581c0460f0b2042c0b08008031480644060111101140c0303c0c0740e038140340c0e0300101007542c1c03040c00c02001c1850340c5004146140442d40c1a02d60804c0680c20a081c040030350050041c6941e0788120910800109116904034100e0510550345107585065910500e0100c5e010070052500950010040003041d940001c11561020000180551034004080000d4224245182c5644603034a000604d0f40c1e102da0030100b8180210b55120003480942e44502040d142030195200e5003c1900524002e02c802c2140000801c90755182c41d04081116204007400ca481e015058403a448500c0d544c4280b10540011505807030070480d401d203440501c60340307030480b80603404c280d05000c1c0283d040c181c0c014003560340e00d0f641181c1c51800b1101100744c49000028610b0002e00728004007024002c01d10002503078910b0607000722 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 339543489 1250 339542239 339542257
    0x7081e042408040f11040903081b04030b0c03150607060e0f010b01020d032f0309070e04030801090b180c04180c0f0c06110430030807110109080d0506100203 69
    0x116107540c1d0759110004c08410107032042e80e018145413103021054840340150114540a070b03e42101600302046544848081840e00c0c8101040600c4244002044000e0940d0059a0101d8403900c9840314002d0384010f07800000410350140c0001481001c1011542102ca05585004180ca240001c11000c4500b40e4680041da94016007020b201c204419000fa48010b1050080b134a0384807801038072100da60130041c00c2d108002646927001c020400701d950308200d000d0240c90304143d04805410141e8015050000c107004281e01ca50b00d881c49564582c032800c2e828a012a00403103102080e080164a1b50b000354014003541084595806243e140c8803200d0081100e503841c9581da8004007003105604441540035034a08035621501da81d02c4481000d050409400078003070580807044c216240201d1124a180c040305401380710a070f4a0044004290001c6005500130803a041c074685010700706014500410b81d003c8020181c5002040c0c004401156620107845443c003030b07554004004074044c059030b8074000c1d2981 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 339544739 1250 339543489 339543497
    0x51e010506030a090302010e0609010e07060e0a0e0a0e1e010605010c020a21061401050901230f040e0613051905060c07140f010b011202180607081e0424 67
    0x120b41041c00310391091320f07494040e00c0009101082550103a081101c03d0301c0f04240b46e0346408a10308500024400540203240c5801c000401d8100d50020440e950700328464840111080d0340025005001508030300c131074660707d0701612804030030b011300e01115012620034501e01c1e600c4c11034007003810350081c0d90941c6500e800502e801d0095143c4000140c2d24980d40140940500740c244d400d000040d2a4024032900c00c99454003280f0960600d000d001d800481644022000c0030300f10600c0c1100d0110094130610300e40280e9038540800c0541c40490098945c851502d20588580c0c41088240d269042100b8400d84c40f4609669000180d110310f60707542d0030307454030103000b5800c260301281c2036500a00c0208040c0b8840e0580d4070800b145440e405003011800501070502d0f94607184982103e6a200d14081aa900c81d00400c50030102d15049001c03100c02a10001c50040c1000207540c005d028540059070b28034020040c80340980f6900341704010041d08244101c10f428000150000c2c080d6010801051035041650b403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 339545989 1250 339544739 339544741
    0x14030a08070201031104060c11010e01050d050705040f03060f060b0a171506030408030907051c06110408010219080f040209040f0615080f07080318010c081c051e01050603 75
    0x12546820790000c10200e050507a55025040040c0d48030002c2c0004020342c2e01c2e400c001c8102801c00c0c1500100640043e810050101407410483e0381107802c0d039441c0c140040c0006541e66501c07800307481a2055030020724800004050001c01c018498009804c20800310509000d4150340c0d0b800d002c081d00450300514007050200524465898078206660b034801c0882c0035980200c03d1030b030041a0164800d8405565200c4000108591301c081008180c000342400d0f0b0341c0b910580168a0300314034050300702e10024400e80c2c5602180003940821001e44001e884048001c40d5500030710505c040101c002c03111180d01085030700c1c000400c140200d141403032007039401030a00d03140c0c0c2d51140e4a55480b042c04680440d01c069030f40241740a0300080c100000b01610070b510040c429664802c0c45039151100941c84410107510402c00b4140d1908440c98985c1c8880e002c1c01c048840280358030700030405001d4a8001c1d07170140303d1444402003884458100c240214061841d661200c00c0d801400083c03400c0334000c803900000104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 339547239 1250 339545989 339545993
    0x2011103060d120e0402130603200a0f050706060e070206101d0402031e06011a190318060e0705011706010e09180712020907110718020910030509060114030a 69
    0x241c4082c140083c0c500d010000071481d0000201203820080c111071115085810600030603815110300c51480001d20828440000c68298607056071003040c0b8482e0030004140541110070b4000c106850009600030010300c0000c2e10b4203400d00c550001103540b000148a46e5020a14400b10000302d0b20680340046a4143c104495880f811401480070b0000c07038140c0300301e400d0000790800300500c80780225030610160050f545403401c117403120f080710003102d040000200800810041c580107042043e4650b0b04011030200f00f4080c84c0481c82d60030380d5000d00003e05104814403401c1011139050141c4000741c8400a10204200c1030403806070040742c206000c00e801070810382d00d078034042a2031a4810003500144c00e50580a1280606103465a80902c040403d508201d40852514050f816400a036528250710754600513117040781d03a9001c503c220241900d0414039228000c0654046503100b03000504002800ca0744820024010003048440303c00600415002180c650b51151201c00c3d0b26000078000c1000081316 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339548489 1250 339547239 339547253
    0x4030f08060604090203090a05010e0c0f04090c030c060e0301270f02060c150402130e07031106040b04180b060405010504030303020c0f0706050c240c030a1e060602011103060d 77
    0x191920350b000350140000a80c1003400c0c002984102c1c0c619000e40041042c52811a0a5942102040d042a0800c4440c2c50342a202d500003a5001e420481300419044501e09044030009101c2d04050038903401503001284464224054000c810416802007140543c440d143c200307202c000c411110804042e503002e9901040c0e80702c0003040c1e20f60000f0a40361400507a10a03907850b0440000c114050944a43e0801042d0700e0000c0e10540701000290040c004040c4001d805a1148214000208060700c3c81040703020b5a1100c4080e00c02408641030b80f95503d41d11020401100003c4d4882c0220441c100041d2075821b04055094501b16903040e110203080030704507074040e006034100d0803100702c0034450b2702d420142280c4100070040c010314450301c615a84840c5807104030300f45401004821100384000068041e04411840000c4d4803410b02042103450342c4810309643c0c091b00000c0000d6040c21842c3c2500c80380c20500f940050100c4400380c008020210107100e00113000d010403107400b54000304011001c4042000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 339549739 1250 339548489 339548491
    0x31306081b0a2001140a0504050606060703110d0309020f040903121a030303040303060501120510061209050a0c06180b090105070302030d020f0403021815040f09150f1404030f08 78
    0x1141090450210340500f141100b0403c060281450f80d1600851506015122401500541045030921075464180c0b10981e4078600545501c1c0910341c002903900c140740c40341d14200040d0a0300380903221b914040250042c042c1c440d00b50203911a40d907007140d003000c0b4601031040c04100f03649511800055810b083e403406c01084002070f03440c0d11740c02c0141900c802d07a409000a51045100c4d03180010302c0f606020005080001e0700201c1c0300c94500e000b00f404200d03171a048421048501c94900b181b004404050000050005020020100e104003070628042000c0010b8650541ea0380b50303120750f45004000b120040746800ca00c560070052004000440d055441400104005400b90040f80d1506a000d6440c000720707407240290a0382d4207400708050007186040040f415040006601501160402c542d49004202140b040e007403080b1360b100071004045046801a50540c0d402020608104403041e04540c05085005d10544142d8074240a00c404a8800d068076800340d50542c5c2d40300d814072040d2a0030b4403000740c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 339550989 1250 339549739 339549757
    0x1120509030c0a0b18030403030509102a0209091b060f071502070618080904200703020c040605030f0a0813120303020c070819081614031306081b 64
    0x1040100b04549003000140b031928440d0481e0078052910003000400c2d00302c1c2c440d2200403500b04110802c00f0942c0141914406403085680200000d800d80068503181e00d02800000205004c8841074032401c04e4042c0c8001c424000c0d23816500d1551002c1035a526100d07210788111005140550761001820701c0000390483c500c1d000e401078038241c484d8031490441000d110344a00384940002d00c82c0e00b001401c1c01000d1025079100c4012240c4c04c0d5954421a0034042c104509028a42e2420940c814280680351507032001d1f5000001541d03000181002911203a01c0102c03203004a003000720000d6075040002e0304220785010704001c1d10015020750307138860301640120404100c4a03c20303280400c152003060102450148680ca00680d079007480c003090784c1440302a50200016401204100f11f05c161411120070100340c2c0800f90a0b540c3d414000c54040d01c0d03080c6c2c0320140c2004a003901c0b06401480000003401030442c030101400c3c4042d501c6008403000d0b24203d40208100550007410361100401001070302c02c1070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 339552239 1250 339550989 339550993
    0xb0d0203030c07060f0f0813050a06020a181d0112050a0204180b18060109020d1b031d010504050c040b01030b032d0109120e0303040b040e010311010e01120509 70
    0x110164000038516040041c5610080d08411410421283c104901c0b81207035025090906080f01112000f800344031004054150740765840c0c407010200003081c082d0740005035218104549500200f0700c010301c004030f10b00503041c0040000380d0203d51500f915009482004030301103100d101d40e00784024040700401040046036035200b1141c00800503aaa401003450312450304801128030103803410300064481c005890041907100782c010b684d44c19032001c0350045c15659031080144c2d603005a409107200400106403100064003250115807405585604444e41b40d221b5000c44415004170003244500700d403070903a801061a07024100034805403c2c583c100341303100a414100040d00e034503c41c020a0824001400d210a80842c800801110203810f846552480d502c206c020440e01410790343e221200003d85140d0002e102c2201b111190a030f504104950141403802d00564903260343d23244041c3c58003020f000448040040c555400e4265110f175002d2200350105035501005d201c82111010010503019000781014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 339553489 1250 339552239 339552259
    0xd0b1501050705060a140601080601020a020906011206080c01032009090a09050d0f0f14030109020d0b1e042d05100b220501050a170a1d0610270b 64
    0x442c0c03084c803500c1c1c032403180144007085041c00340c00c02c0024000014500717418841c000040c0059641e0001e8242060342d41982c1c08940da48420700180c52962a40c030000e121542000b40110b81c03078601003a81d82984000b0b80b0140040145038088d104403000b12181030f00c54110903c80c041140c50610001c1c1e410003880c03080080e1700c82c17070358032280e0a09501b42c00c9400450110aa40604d45502c20b003004c0c1070715228a400040341001d6110442c0611041c410480031640116200001d034106510410103520000d02d01c10911400541e608122101c80c401c05105503c0c107840c801600014005079400c50801d48846801049600f00f404020300014000c1c0c0344801424001181e42d07072903d002012000100708180d502c0303034488400d83d060070390035400a50402c03030180070703500c2c0c9140c0001902000b040300100f00503895884100326402440001001d965010380183c0c0321103041d40124103030707000e003003600c110114054866004c2ca007240100e9041645074605807400078400e244540c4000c0c1c04410080040a003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 339554739 1250 339553489 339553493
    0xb0a08061c050105241825021e06010e01030311160b090a0f08030703051b190501051305100e2103010e13050a060e10060902180d0b15010507 62
    0x404500c9107401c031141d81d9240d052108401040e0461155002c940c0c510542d01c062000200386040c0d00d00c246500010b4007103021402c2d9038401a080814542245840c40d074001500100035502d010090004268031030010891048090118404c0d050381c680026140d0940d296a81c225032468071380780c6843c1a0f014165041e10a040c2214080004011181d2601d0302c80326454100301022460340d01c030310076551100f03404108d1020301000790780c031180d058108991218020013114003050090249800c060140e640c4003e044010b2141c4980c0b030f14080c00080000341c5e140303001c1d003040040b020b1001d885c0354040b000d5500c0d01c05c0c03e5000000902c1d00c0030217a815080c0c1c0b40f989903054030f45d4101c4441803c80e01000501c1038008010b00c030b81c0e20041007006d0035805005900c1e41925030500d400054002d5448480c1a00100410080721005d0500084c040201c66900c945502c025006481c0c4216080c0c104144010b191a003544102d03070960b00b00c0d181c021203880d492408070714010003101541c18020180300c0040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 339555989 1250 339554739 339554779
    0x31b0204090b100501030f09050a14030d05010602010f06080609100f060e090a0201020105070c0b0609060a1e030203010e1f0507110a12020607050c100903020c030a1b0509010b0a0806 80
    0x4010b14031185101c3c1d250342098009420784815044800000f441c102a8001040c0005801104aa0002145901d40e8800e42c00c0e24114442c05084802e028103140000031416815800026131601e1090704001c16a00c5148041c2c8414080d1031403c101d80c080c100c020b5194400e540940c0f12500c0c41d0b040040d805554519444007010103c540d40d0300c9030000d403107500a40d6020302507158414050b01d070244030104141d5400c601000d01034011401a5020000609152141e0540001402402c65016451415400302c0a154611804100d00a50034000c10181340340e000038150303a03000300d0141000d00c1e83c28290903c0c0300030306d0001c0c00442000407100e80c40290071802e02006492502400504d140100d40170400380c81d060014001500300401000b107201c400101280103e8000d0030300d02c01180c84051401c0c124a050341d800c0b040c6a140c020120910104030303241c00d40c2c070ba034144a100c4030012aa6034008200c84640b0910640307841c0782e000c02480807168403034400160720610040851010300910740c036400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 339557239 1250 339555989 339555991
    0x1509031706014505011e03020403080d020309010c0f0c082104050d18060f0f0201060302040f151203090324020310051e01051c0603060c09051201020304031b0204090b 73
    0x1100141e0300401c10369441400e00e03600c5200c0d0062180c031080610f0440001e0002c61001c02040c03046d80151098031031389209030120750045401c410080d03120b01040c0c1019000b9882524901f020390328024522881030b004007503660003c040b54035015442009500c80107855403054203485201c1003900718540042d80000803090040740203800400c141d000e002302c00b4100a500401c50b040000d4689400c0152a03800800401c1201140c60316241c2107680340d00603805803403a60002540035040103149404d02c001907000030b04e411110480c0c48203640d07403440c4480304401c01078030150002d22000000e002207400d04000089091030100d050710040c0000c206036013241c00955098039038038034056040041d032402c1d41c52240c1981e5400a16421900c1070300000e460303840740400c1075400c10050301c0000c4250026a0144000310303000354040c841c5801c010310003040d942c07203402054070500601c00300704070000b014803c9d68800c81c1c2c942c40d0784414155040742d05101d003541c11800c03039200c0e480f861250001409a484e80d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 339558489 1250 339557239 339557297
    0xc03080106030914032101060809030a030c0302090901031203060f1202042708040302011d0d26190906080112020f131401080606060f0f09030703020603040807150903170601 76
    0x7500f151b1403400c1100603112060b0300c40740801c01c1403014420a40c3e00441100c1102446040000b00d841d4100b200350b010f80100b0800301d034420121030001046c80401d0348482c104c1c181c0c96800300407041e01d8011160652189004616115407107640840041c1025400560101c4500c0100c04800254100341c1000c0740e1100d0048404c5140403c0400031941c000314400b0b05042075441c86083c0307001c1400403d10044161401a05c5114007162045400450800701d80c0c810802c400031550320005c840464540389151940440010b0012500085281c82050f406068465506400c450b60050703400300b0440003109440c8a500411000c258082007506200740380f1418550b440a040d40d40c54126101c0c18100c00400baa80a02010072218603040a10800c48c0e00612442c3d444c1d81c0c4401e641ca002c40d250a51030b810094000700008144018441444003600c413880c85074041c0140c40342640b180e041510380d460b5008001c1400d2112040d009814400603d03402281072400300c0211201c0503078403543c180101d0907 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 339559739 1250 339558489 339558517
    0x3040b1303020a1811040302060313031b05010615142709091c031803030e030903060c040801050108070f05060901030b130209011404150503040f1b14010c0308010603091403 76
    0x44140d80d40034000e9096100d007007405c50342410302d5500452403070710000308a203c204800340c0240d0704142c01212441d095281c00038411440c02c006140c40e6000f02101e0042105880740301000250861040311841600040400a07a0801303039030720741072039a945c2c09110000307880410391000b0390701d038842e561160b21980e02c550040c480e400e10008400c1c407040d120f84d030050802d070500c4030110341000c95100580349203606150008403103800c03903603190550095583e003a44c10700501c402c0c00842c0c400303240684191403a0070002c01c103d0341c0c2c1d1516180e498000340700e202e0f01480300100c200698a0020098501c039074042c107011560000c0d0701d00086a88250801880403c3c1d4085540c08465a0040006403000c0400001d1450b0505208240c4a0403100c0341c80c08081120020000302080220303810031440350b41c410309240390024400128103170807150340181c0c044480303404034203001c0e9846280c072000e48c82d806807030345a2940d082082c210701401e240442580c00b9584001c6103104054100028901080c504103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 339560989 1250 339559739 339559769
    0x10b15040506180d0c15181a0f0d0b030f06070c120e0409060e0d0302040810020c030c15010608090303071d0a05060706052e05060d0933020a0203040b1303020a 70
    0x203860301200c6c0c4071040e100412030003003640702c0780d242d19840325003c0d6203d60542140c0d0040e810000e401a118440c9202030b60400884e030030000006540118007484000c40540300b90003452025155184000c4441800080e000032400000c10b0300c0c2031140b224500c01d882e0890107900c07244003040503038002d180105c3d070365a62030a940b0201c06043c17103141c070301208916055290900c0c003e0740c0c5984450340e5201c0500c090380000c91080d00b040400488840010f5041036444613104d0031000940031790b00b4829400424041800259101404403c60b031054523261100c170615801c1a0060307440a55080e01a17402c02e01c8680b0118003681c0d140050492207201c1d001c040340c9440c050000d00d262002c0050480170160308485003820b80f000304081001a41c07000c1c3d61454a40c0a0a2118005410480d401603c6d84940034420030803040c00c00180754840d081c180c02041061004100e84040340b04200c030076001070300305101c14040e0484070001001210341c5a440964015180d03000034412002c554402ca18410001c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 339562239 1250 339560989 339560999
    0x190b0a1410260c060f04030b16020106050103051e0601051308030c010b0a030213020307031b0c111009030f0c0308040e090f0307031223090c03010b15040506180d0c 72
    0x5a01e51040610b41e41418440d890381a941c140d031080084482c61042a005c01d141010844140c165001190011201c0c0d14a0401d95410b0b103501e180700d262038006500300000890254041d01529008501295207080c455102844803894010060050b030304000d020400c030528008907058182c01740103280090b40c1c4c1c401a0f41003c03400c4842e81140c1902400b041c040400c0940c0d1000030440d0740c21703c8910056504e554003101280207001c007102200003601100b0b0301c0c840359035200210807002c9200342c00001c9100950f90030007140c0d100e460385e1000040d508038014000140e072010450b2201d44180700468001d5140c2d80c0719441604075401001c030a101100820030202c0c4100202e440d9040d2942c003440c580749141d207008121000b0510704014403070701c0d000d1400d10554403070703241401c100518034004c5d0541804603649465900414000c3d04c00e608000e603400c000d1414501120aa007a10205140352514100c140902500002c035100581d1041c280300e04043c0e110118900240c9200d010f02c3c0103c14140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 339563489 1250 339562239 339562259
    0x3090c0f090f070f0e060703090e1b03070311070507030b06090a06030b0109020c033a020f04050415080a110901091e0e0c1e030609190b0a1410 63
    0x101111481403800c607042c0540d203106441c9507504040c0b145402c19020400400640b402d2280b401460707080708001801105050b8005142c0090300d902920700000c64a440356a0b5210310270309118501400ea042001c507030325034006e40c010300140c00620582801c1000f5a281d20382880815031003566400040801c02c0381600c1d1900c4102da010392030714000c01c0b4090643e04c0d1442d40780014054120716550008166280300b0040060310742d40c0c51015009031000c0007031540040c2c416861044000d512420798220380c0310101e41e0003540c0d59203842c030581d82d00300ba03c2d11007008094013102044062008406c040400d100780f042c001042c0b80c40c09072000c0214007210350103001510344164040d941035850040844602c60051030000890f451000000c242141c2401503141403201d95641503a0084900c0d01c686040014003070034243c43c400c110b0940302a95079481c80c5030b03146c0310444428004040c000d40c04900080c00d2211842d04403484850010300311042d203c60500301c00c4150780d40c00441150300c07810450301c811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 339564739 1250 339563489 339563509
    0xb01030b031623190501030c0f0507080d0e15090c010801050904021201020f13050f0406030b0705070507050603010e16030b01050f180d0f1b0e060607061103090c 71
    0xc20703001481041c8801042561009182c0107a8000c40c01d240300070101c4120b05480d10380a40030040070ba2168001c041e0000e44804194810715001c28141444290424080c44044003000500d40b22a072a0889030740c0c80660301e500c2038206a07401a174620509074101d40c10448000602c001c1e008600d89402e0a0804a1074500e04584183c100100340c40180483c0e15001030080c0c10680c140c0c0c49200408402100601a002e0a10124150355010908020000c0d00800a0b8200e070b2099402c18140b5184a0030b22064404501001e460007603000041010a88210018010302f809a010f0354010341d154000200703640c1c82070344211040100e8405116101d18081c1400740c007030b83e80d418100800721360b01001800f42e0003911030120b080c10000ca011081501807a182254100d002060003030f4080051401450b1084041402c0e43c00030b80d8000480c48000d83c1d8040c0400b5114000100d1f00b8642d01c0c00d082144a601207a01140c480340c0359503800030210fa0400245000740d14142c0548600c442800c240074400d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 339565989 1250 339564739 339564761
    0x3170406030f02041d07111006030c05090411060d090f03031d0f0d12020d0c020f120a0e040b0d120306090f0506090f090f03070f03030605090405070b0310030c03060b0103 75
    0x88100020440000b80d4006a41800d4603801402003546c1d0384034055820342c0c80c43c1284001402500003026612545611010650380714035031032040030392107c0503c410410b0454004000004e400700b03801280c54100040d00165562001c0818074408036076400100c8019017504a0100b6103d2110f1311804002450104400c0000401000d400300d12000140d500e2240b06e400209200809a8104151600d0780483d08582e894020621442a041d44025602d801d0b007450702ca00742c003440c030f1181c2744a001c0004440441c1030a68074039000b20325400c100001400404111580000040002ea0024004401501e17803c00302d03480001e0034a1616101e5025030f0b102101c684400c520f080304102880d07480c0900143c0000384402031112956980e01c40321b1402d844070540d080940700114148080100300b40d070a2070568131940c0d00388107955882d001d110f034180c3c0541c0c0042080d04441fa05104203815400916031100801020341d45199036512503a1040380079800c01d071051384c1c80f482c00199650300b6000700703d1400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 339567239 1250 339565989 339565991
    0x40e0a05011707030803130b040506010302010e060403030e010f050c0607180f06080c210108030304110406080a0f060209060d060f08160e0613020c01021902070503030703120603170406030f 83
    0x1070681da41a20f40109000041c0310001c080f01240c8030f9549a100101c05640c007a40b142c0f01d07420036040c8690f48040902c01240018006c81000500d42440d01c169011a80d06444240b003005001005542c0a200500440100321042c02052845031040188078050101d50b01c4103602c040049071061032001040d085a1103111142c80b0800900350302c4000e8a500c42d500480c8d154940d0390710583c03414200e07051501144411000300002c540500040011350050744200d60310803c400d1900c003440150f400510070446c041e000b4000140216003411010141d81e841900b005140c074940b0b20024580c0d800c640300305000c0954030710b018012502003a2031480030700945e40050203120221007010100085d00c0c0103014000200002040c0261610700d031819001d940319001b5515295104000341c002d411200d02c070014100e00640520b0218004254202541d6014000d14900398a0b80c400f9608600f0f400b506642242e036958000006c03038613800c007490303024000c00b000aa45030f142c000000d0131b81d0094811b1703565403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 339568345 1106 339567239 339567269
    0x6060c011e0e070b090909070312051e130302100c050102030a091506081b012001050103150204050d0f03030f06030c0603140c0307080615040e0a0501 66
    0x1e511004820414120042c07401940c803640382c4100c00c06010100809600741c1882c2035115407120500e4100c03480c0075a2681c504078400407003908a0b00140c4042900d00f4100a2500c070640c070990b1403090030741020554582201c40c14184d1100921803119110304840043c00b0711550400641c00500840d12841c240500c5000b13032040c14401c0314041c1640110006514492050b1400d4554040007071040c49104864800010203c1d00c40074107000381c00d44041108820150300c005003640ba600003107119495031030f000c1c454014070320034400082d00521060226481d040301004459802403140200c5401d030b814240c00500b0030440100099003410b2000c8140101006032004860701950104101c80c0e942c4003200d48004152081203078450100042070b00103114144458110b540100b0a00d400c2240540408299000f588001030703189217001000007513042403142e5030040000308400c3c100 = true := by decide +kernel

theorem cover : BRFrame.Cov 339388489 339568345 := by
  have h0 := BRFrame.cov_init 339388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 339388489 ≤ n) (h2 : n < 339568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
