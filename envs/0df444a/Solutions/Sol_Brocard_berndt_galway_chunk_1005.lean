-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:47:20.285984+00:00
-- url     : https://prove2.me/submissions/f097bef1-cefb-42ea-928a-2ace69ecb349

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 180575539 ≤ n < 180755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 180576789 1250 180575539 180575543
    0x11b080609190f0209030a08070b0f010b09190308120103050c010c050601092c010f06090e0c0d2103090209070302040605040b0a170403030b091501020312090703020415060f1803030507 81
    0x9405c0c050498039407001e00a0070300701d034030076010b541d40d0345050f140c95034844401800c00c0a22440d900014481c0c07000403004c031184c03130008407082c221010401c40482c604902c10780006101c0b400214601d900314140b1944581a07a11910a480032a51000c00455101450707403c05030035a40031000400031480113501c2001c8010036020215045500484489014150445102a0350703549825551001e0694403804000e05204001409a1180e2018142d5140b441c0b80700c241c454201440c90300308011802c0003d80c1e05000b0b09000c0320b0900c115800c00f07001060f1984c4107034040e85001e40002c05640c0300780b00322001d5904540b282d078100f500f005801403041c0c011000c9002884145e0b410315011100310391302d1070700c01e80c840c0c0e0b4046880800c440130b20070421800f0349914413101c6954140041d40e0b03004800e948605100900403506aa15001d1823403500d40c541e88080e4200c1d00e41001848040140c51849007542e2003611205440006010112080324000c0c4818001c0c05481d00140006840350004150180c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 180578039 1250 180576789 180576791
    0x10030b0406080a03020304061e09060810090f02070506010e0f010620060c0a020d020a050304050105090a090606110f030301140f011e020102090f041a041d011b080609190f 75
    0x2500c0c0c201403071903c004074006a002d41e00c04a400c02c5525804041000700c030482186004c0c161200300d10146c04403825024007002e20070034100040102c44c0380c240100040c400e0041c140603907440075040c8802507003c1d08054509020b038000129100401808036400703080101c10b40e08090f072a183e821a60740d18612102001c8410f105c1c0d0750b240700c5004010781405801d010455039910261168040e07e0484051040019034102c140040c020032008420b49040720000c2c00d0032a92000038000061001c45946c000c0e0007540d14123800822429889515443c2c0e01c2c88810894000200c4103294940e42c0c00244141d00d21100c40c440f1034582800c18044004c00000113041111880000240d0745480d088680201d40060307601040240041c68220f6044403005070585080245003030340c28109814904800840380110b880340b44d60306628010b20201a086090900200400d04020040e14a00c2212000035400529882c0c0410610302d40111001d008014080c50104420100036070040902020380702d10b050a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 180579289 1250 180578039 180578051
    0x1611070306061401171305030c1f0e0c032d010e06060f0105120105060d14070815220e030702060408030405040f06120605060109120c080d020105060904080f0418020d0509010b10030b04 81
    0x461404c000d494030003132149030740b98000ad00b44114841195104030706160b942d8082124044940c501241d1207102e0b10000c0b40c4594281d1440f80c0388540140da107200a4510342c81c140d001c451103900895428010b240031112100031740083c81c0112102d01035061449035040007140100640c1c40c0090080c4820800c0c480c02255418a14409480502c400c687ca1030204107000200041d41c0f56030700c1c081c1e007444c60484480340001c841261183c8031358024101d010b45a9a40e00b40d581411108000340c403045070f0f00502440d5100e84600348c8070748941042c881d01c0c0c022030078000e140041c6007050184100b90703411841d01145403510b948502c409041c0107001541401019000031a941c0b5000d0800c9811a02441048151500d0109040e01c1c100c0030690010440e4501005d00129a48502243c0c1c4c1168202200701c0d102d80f145003c8180c14841c43e8042007003208d06149222000c0201d4019108070316410340d0410042c0c2e40c0c1c1d8803217426101030300505079202d0010001310400c00c2c081d03845590310300781c043c0000480c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 180580539 1250 180579289 180579307
    0x21005130b130203100e0c0d080904150f050a062109060606020a031806020a0308180102270a03080405040e01061206091506060206161107030606140117130503 70
    0xc041000c0e58000d000c00382c1034803a0000d50030200000c0f140042d01ca441001440040ca10a9442c0c401c2c2400382c03882104a80e5070082442141b009856074010b004000f005020703440240381c500c480984c820300308408400d84001034545004000e9004031032003034403040804840051840c0d41d1003c0007441e06440f035a607480e2040494164418900904030350340041101c4040e13410301420820300c0d4044903450b070704042014005079601203000b41d01590325092200664848003112803010329040034411081d840131034a200d06002c0b03030990349400400882004401d0402100344407002c4220301020f040003504100070440c5003000d5211005048084c400000d0031615058151141c4461600c15a2040e4450b0795560a00200521070401a01c6968040241528204002e0f458681c0280481c04103c954240203c6941c0507a43e103550000070441901c20a0340c032413611b1001403155000b541104010001d2050003540a490340c0e010000c207030160400e4580c0c1d5102d180d50f0000c0e98160440706800700307101c2808 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 180581789 1250 180580539 180580553
    0x1911070f0506060103061a090402090114030f060f03160506130302030601031b050a0e070516060e060f070203040b27030a15140402010507020f0411040e041103010b0102100513 77
    0x10314410340c050102401c0403400141941c0158101c401400451143d4a4403646403a01b1603020350000c1d5005a11408001e0060300c2c507101e000030203002c8071400010002000e00c030600700f074450b500c111064400b001ca42e10905070b9134038000203081d244480c065000e01540c504400a003c2e103a11114080580344d45950120f81040d42c05c2c0e0040300c64001a00f0032030304103800c062040300503003000e0314503028151034030160310101c0001400010510400184100c00720342c207900041841500820140116507080011a5446800b21244041054000082103019201000b242d0498560016560812060300041c3c1c40159402566418144d070f6041036484580701488640100d5000d15030100700c9001c1455442d094138001d19014000404002c10840183e0b00001620607071501030312551203030356201c00820014401041c150a042a0200c3e000035100308890782148a00c0c421004400c15015443c1072500340d450f2403007400c0c096007241c14030f01c0101c01640e1103554031503001040780303150743c00ca61180c0e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 180583039 1250 180581789 180581813
    0x4060b0a080a0b0906060d0b04030f051201030305030402040b1e0f0303130f1401050a0c0b06030c04020d020703020c0301060b070b0405100606030902121506100e0907030221191107 79
    0x54900c400c3c02c0400541420603c50b481e030100d01600c400c000000180e459030b50500c2c00620060030b01113220f119101d868420b10942e0f0b5510b11b240c0592640d940c50303003806400d036007080310202d100e03504040d40c614a500741000403003403a007403d0100c18070401081c0308120000908000d5a505444140710062160b0420391500f4024000044119601410300082610b05400d140841e4140b00c000c01c901200540d00540c52a002c3d41c01c03d082c4000d5880f01c2c80040c0c20b11400c80742035030781305002040700803002c0082d40c003c154540c40b03a001c482140c00c0c1d10b82414262609442030801d05001800700303401180c4d000300041e510520031000c0e1850130110007005022503407030f40c01c1000081c0d692840541141003d40d8001b124100c008005c0012403000340e190429148020420b6000b1403d1240c800d9415000340003074090640018043c0400d441d003040010b0080d08442c0c010300100102c2c8a680f031010140e0700140d401842c1411004c00300c83d0507005010081e10000c00c40059165003000a440440c080e02094 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 180584289 1250 180583039 180583043
    0xb0103020f0a031541040519060f0305031e070501090506040c06210c020c042f03040302030a0f0e1002070f0b0f0706090501091709040f1404060b0a080a 67
    0x75166820003c90100f01c009070701720300140100074440c0000403071800c41c4100000c0340c21040108912244201c8485924490350b211b0b0400e00b400140f040361851500c52248140141c90300308080760340e40340d14100f14504d920014005400820650000c0d040885400c1d00c940307000d040445c500b1900740d07255801c65020071419a1290428011b1008105c80c203a0401c004101a10308a98218058010450103144240003100c0e429694015400814024011281c881000810802240c081c20040b0114842420780d444a06143e4600702c0076070303001d81c20980e4010380d010b41c01141003c00d0030f1000d6840c410920f603441e00b80881c02640d2807650f5941414814400e034684d000d4483d851400f8801c040740c903400d80110500800c240600651a09400305803507959401000200b44610142407007401044c0600d0064081f800d8048413a0701125058014200f0b21001d07202000900d810780d081070102c90708060403902c030304002e0001c280402d1b001d0b005104020f0000380480501603507030041d0b0345808001c0c242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 180585539 1250 180584289 180584291
    0x1b08040b090a080a1a06010504080c0f0415060e03070504020f040e1009060801020702030601210813050303070804080607080709030b060102010b03010c0215100303051911030406110d0c150b0103020f0a03 89
    0x41c45c124280540b0400340c01c00d0003800d01500b070508003a1040e40302c000d80300c022400b0744540e45c05000244e542c0d13041401003003c4951010300c101e0300c800f8010700001410058034002c6c800d00800048900305442200c03403501b8802c1100d42400d08096440d1608040500010780c00c0307511100c041940e082030310035400141150800141d0320b045a10601d030130040142d0107a013044140130940754400320f10403085a036141c3d00052403559283c2c3d0b40030680f2010844d41248e5011312000c110300c0200035941e0024020782d2400030032584681e80c0c142c0b00b145c00354000ca44100004184801c00c000084a43e45400d40207034050001007180032035940421700311030071030418400681c080500101700d41010300c1159009504003418001250a646000e8400c3c0308151603c542c4200c0da241045071248181c5c4101300a43e2084142e903601c80c1e94040c020107514100000c0e81c0766000319090400f800740110904503003294021403030410030a03540c0f0004010090003070b80b40c1c113040d02004035200114880004001c407031404e4030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 180586789 1250 180585539 180585563
    0x3060c0512060307080718180c0503060f070c060b0117040303060f08030304081902070f060c0605181b060904022a160905040804091406011b08040b090a080a 69
    0x7040303403844007025188600a4100c1e00e424070101030045880020795076004040c1a0781041000000002d00c40785030400820500c14002c1d00802400b032a940c001c41d413048045440b29241c8241c1800060002d480b070310041545111648001070036600904c00307406050400c1c0405640174514650501000c88085000070b0781c2d40300c240031508040000b0805010410f0083d82076140c19500c5c04003c1c4100707880340710901011080022030502c01c020000107481d00345d00e0099240e5880b5806060083d1840c0100c0d00d140c2007030001110300ca11300808182c146603017001418401e00c01c42c0001030b010101c80842e500840d0420401d0510380341d500046c00b008048486a290f038400b50804030100c020055105051a0044042800c02c001200c950209550748840001807039161480e0042c0c0700c0c030640d0701c07401080c7d0a0185c0010841001c01c10180b045400b070f2121620750300580500b244104182100404555091000707002445015003e030200c3c603005490703005100d448150252520085070b17021103003045010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 180588039 1250 180586789 180586807
    0xe03010609020a02070e0402040e03070809030705090c1c0605041a100203090105120717042907051c0603080c030c010f05010b04030b1e151804050d0503070903060c05 73
    0x1100e60300040141035002c60a20614450003515140c09116090324228124081801e5640e44d86c0280c81c07a10044003269a920a40c0c42e100510703800403042039210740511340300040c2506010f40214400e51040d01c00c6460500700c05111041c0d0038500c800d086055954070001b0075581c517544200c0c6100180e07508280190b1914004000b201043c003024541150824003045004e40d800c0b0080c1d4a0f030803552440a41a43e9440744100c8554141003a0001d92007150000d0005106006a2407103040c00310107040c0480800c801c0c45001c1940054404000065080040b8007901751740107010040f941c010320002c24029500d482d80030464114581d00c80d034a400025180034040000d10440380043c1c05400c09101962403c1403500d020f01984c80060245820380001807040000d071114a48400c01c1441c0d0701c0c1141c141919050b1480766001d10756801825402806281c08481d8403020388265403050052441007400003044400c1e800141c050401d1109248010001645900418004100030303625113490300010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 180589289 1250 180588039 180588041
    0x71101060b1308070608181005070c140705010806040b0a0b0708220308180301021209010b0a0602060c070f0f0c090b040609021306140d050f090d0f08040f0303110a0e0301 75
    0x943c8840d07501d9002c21800c0048542050705a5448103c003802c0015019035109060304000704640603000310380c9050200100b0642002e5401c00040c041d043c940080c4d01141c6506030b4a600d640215404503441c0c00c00142c5918145e0010b0440900180a1032750044d9121110b94080e000324500b2200d80d400401c42940c0c4224803601811010b006210410300f01d40f5507154403642d48503800400c201c0742c088001e00e5155445c00d4044401d03a030100b04088446c0d00d450510b4074020101460306910400c016000002c00510024803540200303e200d45591904909a5580d45003040c078950442c4c0e0329001001c10804581840546c80050000c40c8003c152155241c0c2004200d890b036400807054680705011032000508070560300d41c1551070360309000341a84075491311601c3c00e004001954006a04000800c0035030b1403407503542d40c05010208100c804459299505580030300f01c0501e62000220040f0000d000720303500e00c01c1c05080758000c1c14001060102031000380390540c80480382e00c01213900d4180c0c00c640350400b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 180590539 1250 180589289 180589327
    0x7020f130207170a0f0801030f0803070e090a06050301050114011b23010506030105060612190213060e13021608030c0d020301080109030f080712051806012d06050301050405071101060b 81
    0x86c40c2200d0a9030441c0e44074040d0404000d4082c0203100c0201c0014070040c0220b10901c0e14510013041d0a81c0d51904101d003c02030480f601135180294207080000441c0a2021146451202d0586681081400b0b0b0318005603000d0050400ba0f80070030f4804031803000c0c00c0b04c500803800504080300002c2040d1400d2000c0c103003901c4018121078052401042610031040140c0c04064000445104800c401d403111184c032030290003060055100d80500b01400140f950700b202d030301c1c5545074054034180b41d000c03448440b40080740100118030590515007141d800c0020145401107030b000301120b94060905040c0341241d012070b0401d0b081025136139900d000090500d40c019940c007076091440e2030188c810789003070f41c00100810081c0101c3c0b25041e4032030021400d90480140808203840fa640d080720819a0b440090384618045401c03100880c45101d0a180229105400405c081e20310a0307c41c07a1940e4600418080140002050308080005420180e1440882030140d0001014100409921102003290303061744460 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 180591789 1250 180590539 180590567
    0x1b270b031806070207062a080d140603030702010504031b0b1902010e0604020a1a07020405040305031603020931050c0415030203010806010b0c0304080f07091107020f130207170a 78
    0x44155010003640790b003c825059810500703040c0761f8003950503900d5103ca081500c840140000008603080741051342c0c3d81e10800002c140120000c0c01c1e070b1246014161248900c010180c00510204824008942c100140d800b14a650401e460500b039921146e81d800364021108900c5001d1003a031300643d02c203609008980e50040c000c0b02a000e00c0c20141c0c0000d40f962035920a0007c2d503440001e041101e2040e503000d640300d040d0082c00034002c920705460001c042e5403007210740c16094070100c0301e4020628401d1094400105025241318020750401000101c0c3c40c201c408440111116038060b1009500140150f600504c00322a083e92a10f08120500d60300098082c00c0604151040c001004125030016041c0e0444003010001c1d50f46120416072503085210350382041070684608081010740d003030001960011101400003c0200c11200c031801c000501c09d540c0003950001031031840d4149850905820408640c220000502d0082c241c1d4038050341d15074000c1040b20700800410440d0885400c0000311444036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 180593039 1250 180591789 180591793
    0x12021c02031e091e030f030f07050f192d0309030605070c2f0603070e01090504020408060a050606041815080607050d0902060405150903011b270b0318060702 69
    0x440000310b40c0d207400200c00902c01044c84810342e9880d0f01c0512020175441c0d40744059981d90260320745800d1140d072084104403061321441c04064625140403030701000507250b503041580c031020341c1e40315110341c45041740e0441038012501c412045007403e25035903203400d42e12a44640c6001490f608004048030002054441440524000f1100055030001144071030540c15401140f0b03640741004034661598802c140e81d4100350008140844240c0000d094a20032000342e03a001c0000e5110400d10007680151b10800c80541e02400120700015815040545d00c4240500310700d09156440c0400036140740300645158030580e80e448061007040c03202030f4110107801c80d03000a00d1213040c540341c010054407940e116440c03ca5590101c403000c40d40d0310800c4038002c1c20001c1440030598990340004030254003a0700345a100398603108202c0a860341d09603180038415410b888248000306440030f0011710181c0c0f40419049075220150110b03914500b50065405400600c3d41900c02c9602c0d880450714120024002e9400c0d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 180594289 1250 180593039 180593047
    0x1030b010203040e040f020402070c360e1f1517030a08041109040c0501020d0309021005070c0305030d0e0d0201020903033f1608040b0412021c02031e 66
    0x140c0d0300041150110340d01501d0510b401d0703a032410b042114602007038000354002c4c0000723000c1061044801480050b16404581d4420074040c004070303c8561750888000c00522248a00d0422036503072158003403051100f035041075a0300881b28104442a0251520010300b0043da03541c2d9528082c00000d580301c01608003001c03078050550290128590302e0143d404010308000c0036000107010407504040022000c10050114801c906152408100170341590085900610449000c1030b840e601c603014481038150054880751203840455022680c80d03108103030540d80300990020000000f44100014540b035120b030f020000321007100c0515282030656076940c003411680148100c001b181e501208032043c1504800c080352002c08800c0341c103100510341240f6003848042d0b661881c00703c1000c20300c52a1056105a10254454042c680146c4450900f610701070420000140000c0020302950403420b0203028038011548041355003080404901c200180703120060b040411400c2082038200740b03d07014451451922814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 180595539 1250 180594289 180594311
    0x1801090b091b06180a0305122709160e06181f0509100306030605040303050402150a12020703051b03041e1211010e03010204090218060415182c060103 66
    0x3400307511540f02c113035071040520008136994042a00300441d800340c143c0e00e102150101040c1c5540250007481c000b17840303105030791004400c40010000030b082c004201c04d941c0d4a80441a4140c0070300c829040c1d060040c150000820381d61032802800069002e244829440c02c100800d218020440f0340204051400d144000d503400c07a08002a684030000c19142c8541c400c14946003140988141d6101404030b6207050300b44010b241e403540159208038029580f52a0341030400c0c4640305c2501c00c0d01500000038008000c0d45585104076001021014000d1400c141003d107a5910784612284031b002d0402d442c3d100103401c024110303500c04000a51803040b44e000340224030706030311350f00f040f25810030051848011960068140e80510a0307031f501200003a00071900e4540303800585001b58810f90340800700407181d84511701289010b20031102565034414101441e03629403042980c12101000001100034030100000c0303030b00c801000741031031100d043d00e40002502034443c07400144100043c00050405040c0070038000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 180596789 1250 180595539 180595549
    0xd05070f060e130506030c0d03200706050702041a100207180204031205070f0c12030e040b010f1404030206030705070b1e070f02010f0f02190e1302031801090b091b 72
    0xc0f4a041e9031004a05541e440002a00b8000d004003840d600c01d02c10f6140d801455409015001c454480121f00c0c01c803005015845a0340d84123620070007000680421440005040036003000c50782c0380d6908642d541403866400012903419200d81d807000140e018080c100a1840d01d111303004020381480d00d045251506588819171707040c00c6452124144907001840308200182d100000d040d2541061103248403e031160316104174503103407140540020341c80581440c0c3c18032b010300c1441550541611a034982c10707004001501c10a01c00388040459480034080000561184402507201d81c115541c0c807542c41d03040785000100c0b40c0740945a4140519280c0380d61502c00c142c1d1108641100c22400c3c40d000c1306c031140800720301400e030039044040c50600386021595420b4054002c1c00062411200d0b000d24040c080000326075000d01c801b41e550b80b00c8600c15648542d800c03590b000750740002e05540907540c8030800c0300900307007580c4010780e0445400b4810030402142083c280300d1089a001030100315040c0f0318655001071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 180598039 1250 180596789 180596809
    0x1314130e07030206090117010608090705120d0c230106050901080102091315030c0807080706050a02031606090b0f09070819080c0a0b0403050c07060908100509010b0d05070f060e 78
    0x240200030015004500c0e030b00030414044200341c3e4003607c120540c3c50b900010040c41007035540381c3c0580300c0c241e000301d0246029048000d02200e024001e0264054014045841440d0110285c465a02c158000d407042050582481c1911010200104200d40f80406200d805030050f0b002e40c8050348144070f900440e9403400040d9420381072500e4040745400440d0803160401c269a4401440c0700b452210010b110400481c3c1f1108496a403401d030f921f4150759003010389443c40303079601c801c0058004000c41c01d103103030312040082c02443c0a1240012a105c0d1503603081e003034100a9a005942040090400008103410041d8001070070074040640700c004400003000075580714074107000704108008142001000b5007040081c0d825500034241d00c4980c04c10b400d02608980c410440000c0d640102100466414060500e400c1228080c0e4000c00c08002c60040c190010100038255002c65520b5a1915035641e0b40c070f01d45101c2c413a02a001400c1390500d4070002e50880c0364240e112f542484403e4a1901c207960764241c0203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 180599289 1250 180598039 180598043
    0x3060609050f300a0c051807140304050a15150b0a0203090d051005040f030806241305040204090b0102010b09010311060d1b0905011d03030d0e031314130e0703 70
    0x70a00c0e007189022000c1d48407602480c0d4643c0d8440c500c010000d022900e90040c04580d8203441080e41140310290340d00b608030341299800702080303c8841c00801555108001c0d980140900291145400641c0e1886c1c4c21401440492003041e45400000b1800182155000000d0900c405014030785006c0c0c80010751240170b0040c0c000c0c459041251007000b40003040c014810380081d141010005841c0038500403118400c00c420960010b205500040c800d4188945480704883c100e40d0b0308150906070390049003456121a15600d000d070031003440050319883d9400a0000b0782514034003c15810f0602c4002401c54224141880c89180100010800714500515048440d08140c88080d5030b002000913200160409080c0170a4066441c864040c0403030f1701c0311402c4182e4100b6070350640840240e04a07107400340000c454941d0306400c1044010682a8203074490901410301c5016281840210b4014030302c1c00c003d540c030114103400f8056284841c3e26050054242285011204000a45003016002d5591030035000c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 180600539 1250 180599289 180599329
    0x603090b06090709170f060108030a1704050601030b0604020c07060e1206060603040602090109151805030604120513030b1003060c0f1d0607021309031d030c1c0c0603060609050f 78
    0x48100d0010090103000280c0c10060115045035275500085960b80d8480346403039001036a84418404403022504500380030315081401012640d00710740750700051201c0500513550099003000b600031414001d0042d80014201a15402400d0000c130040c00703402c1e05d1202c08150340f604000100320146d0350f64419650041c0d00810016100d0810800503038043d01c203078000140d0108580d0480300d060740c2c4208031b00c1041d205081c8100c15556074200341559101c064500910150780c19202020342c62050024045500250300c2e0901086d94170348540a00b1042a0b540d018840b030105400d205104140c080c0307079002c8200340b034103004c11116480020801c65054440401e144860354038090f5540d207040640c1e080300e80007050096000b0b043d1001000038800c00004501260110301c1e00418400054102d402245004d005400748411400405c103074100c04a8400030202900e604a00100d90704010749000342c200385e10700140c000c2c10101c006d8011030385076000ca84603050b8400001c0341c0b521400d021503a01014040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 180601789 1250 180600539 180600569
    0xc0a0f05240429010e1902030403080403120b0a0e0f0709050901060f020114180c0303090d0f050316030c05072403021305060a02010c031d0c090c07020603010603090b06090709 77
    0x51520800045100c81ca642c1070450010441d985010080c9009840c0c01d20144094084c519031b11080c2d000841c0c0c0134011404520003e0042405882d80c03083c034481000c0e0000c3c002888200103240741146400150158420400b0005c46040d4482070b15000f13403031828010311316458400000c1c246030f01409200108544000340741c1d01c047c000d401c0110400c0c1245080403541c0340c200c19200161406040c144810320400c841c0d032220341404822513180701c030301800d040c0809810b46c65080c10903c00910407038107480200000c0601e4040710524003295440790b46c40400200d41410001c0c586401500710000c103480100780740900440f6292000807903286410050780303030b000d80d0015454000603540119017003040003c82e0219260306502481105089480400031504000302035403c40304404120b6138660302800407003150b443c2c00c100c5664040c1461800354030f840c20355804180705400a078800001b00340c9071a1141c0821500d101c0389a40510191800c0c1d08610780b02c440145200400e204000c1b603211449 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 180603039 1250 180601789 180601823
    0x18050907110f15190b01020d050a0221070c0e010b03061c050a0b10060c050d05030603070b040902070303270605130206130602071a031b0c0a0f052404 66
    0x2114411049065074107840c0481c0f1124403150716118201e51144070820807078814076540d21684518040204182e006114102011000b5111544141e14003800d500c42e01c45158484200ca0f000c0e6007000b40701003c00d88e1103803020f151501d440717a4141c00600c0301445407001840b80002c0b50b41501d07441a01154528a03041012034014640300300300070080d20500810451170140090310b45c1c250301a07d01881803403407940d51a002111510303041c3e1030051a9030031219641031400c0c45200510b402290060556148580e01c0c007c001042d8007691101c12400e0b0080380b400b051607098814050b804102900c6081c0480402900130500030701100c00404186c0c4d2480852a050318684400e564140c0c0544290750700d65042d88451600040742c0704940061080f20400309003515030002c0d02c490882e141c3c1c0c0688c05d42d29011070040c500344a94002008249080c006804640d0302000420405401012505031039650790801a003002048000030100102d045c040f400c0c0041c0d0194141c2c0c2c001d400040c20981c0e640701c0d07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 180604289 1250 180603039 180603043
    0x31213020d05030a170703060605120c090d0303090605100e0f0901020c0307050106140303040b0a081f0603090204050705040f050103090f0606030302072c060d021302191805090711 79
    0x38400180c00c43c440814a02d001035081031001402ca40c90b12020760303c0d60b030707001c2d404c500b564524000c020000e0003d015070411106400e036429081165101c4482c2070081c0c03403001c01c0b0f6210748107800344d001a4071801c0700c0b42800301b10300c0703015081110140001c40680c20000e0000d5a03040161442100350b05540015030307590360a5041d0f42007001208281c0b0364911450508c50702070401802489105c1502510010303003450008110360850700800c40c214180140c228040c1c82d4840d0051212061f00e246810904203042080c050001400380c43d1400542d07801280140011500000c0180b000c0c06001c00040c85050316054829049520074079011804030850314240404026100000b054541081e0000c000c15401003141d030140c401980b80000200c040041c5d141610080d0b0814011001c0302c000403030102c0c1880b22000c6082400604400c2100c03c0400316035007260b01c10311003c0d4580d80ad80e0110906280c0c410101c0c9030304600085050b982c913041c4000a01c490070090f02180500042041e0f03182d1070801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 180605539 1250 180604289 180604309
    0x901052502041104030c05040204080d0807020106051c1a010302150703091805090d020a0305160503070f060e0c0301110406030518070f0e061009031202120309010603060b0303121302 80
    0x1c003030800e000f412104400001e15801c18001160446a004404a41c500b07180c4262806c4906003c004c20005440001c1641c0103100501020119500c1e4040070803103071260041c5180c50349200c850030403000120b040450004180903041807810814000410140c1d0714603070012140c0c54034549070340d03881c1503074070b41550060131960285200c01e2a42821949490895000d18403c9400030245c50348401e070349408984a5100c504014040390b001e00c0202c0707101040c02d0540b0700440c0301c0c0048a160154a49611b501c0500000d8111803480e00d69401c0800b1683c207000000403008142d0007840b54444401401c011802180240001c0556600c0014030754500d00110030290803405003602c0d0810f40300c414205d0040000e006081d61407280c2c0b00402c00074241008007000300f840e40d07a118801d890640c0da031001621f04241e4200300310b11500c2c54003010000280c00441c054400c2e04000180c20785585015029075118802c01031007600305001e07101c0700486000245500c2600000c03082c0b2051035520009c0c2d18211 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 180606789 1250 180605539 180605543
    0x7030519051f030f050c0114070605190e25060c110f06041706150603040f030e061b070f060f0f0201110309010510080607050d050c0d0c020607031109010525 69
    0x102c102c100006004100820400180c002c01c140e03191a44085d00540c1c0e0213019411425404030100b1100c804200254407a0341c0050115500e00c1382c64504642d01c106a58010160700c1e01c41d000290203190310368250b070318180388400364201e140c405490508041c001c2d002103803010f06445d48400c054142030785e030014105c045690080006445503101d0030501444031141c1d13040091480340c400401c000f03805402e100b42011000138009840c0d50b40d1503542829854100c9c0c011010b0020041c410600c9985680140086107540008451000c0c14000c078545050b5180d400b80340c54181c019421b10506a20202903000309190741442e0b000c007185208e04a004200d0341012010b501d0700401840102e043c190440e078050b42100c40340343c010680b42d45a507915180c09403952404207030200326410700d401c1d440c4c00c075030b40c001070400301d15040904140c080d50a03102c0d10b81184005070081c00030481c0e503e030184144600c20715001c01660a00340d9440010302988201031414849074044400c80f40303c000300d202c038030304201d07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 180608039 1250 180606789 180606841
    0x20304020a0f03051014040804060e0a0e0a270503040e100503011406040b031f090227070219020a05211204050a05041a0402030414010c050d050703051905 68
    0x2c0c0e076034140103860356004d002590034a0308026541c03d207030072030884171805241c0107007480d8070b814548001580c00c0b080710808290080c01400c0c0c005108003000c4209842440210004a8514010341e180d650528190b030002c1440c01407140c0c10030105100106a400380c40c4901800b40301a10f0302d99107460007a009078001a49136003000e407141214040c04400c207006080980b81440802d0303441d8105501c0b880e41c1181c110060500c0bc2c05401199181d41140d44d1190001d00b01940e100d00000341e110240c1d42c5811300a88224921051100d4140d042200744040402c1d059800c1103d501d40e1f00190036903215120341849681c4881c032000c8030640b0320ba80f10120841c1482140c24400c1128a0314029812a1260b0b500c241449000001c20741414010340c4900780100a101c5841400d090800c0b0080d0000340003500c8902d105140d1240301a030034480c29041450b41c1d12a29225200d0a188405850005007003c003010309000901041001d54280380d1050720b40321030081030319941c0f2040d84040451060f00b500c864 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 180609289 1250 180608039 180608069
    0xd15080a0602131d07080c0408011103070207120f0b041103030c0706230316051902010f05010506190c110d0305030a0e030309030301060c05010209041a030c0405070c0303020304020a 80
    0x400c80b94001c11000340201c0c0000c4030309035650250021440fa18400300c0020080b032000440041c440e40c4699481900110341c10b0826480702c02050844082c51628a002140042030240e40707501005071070028010b00d076210700d901c0d20958070a1025040400001c058240c181c01280070054180b440710308241000c1c04a0f0381358081d00320003540d030b184944581e801060006070740320610500c64001403040c03020010f10b50302d56101d12200440c44c0d1030211000c01080410b01100880c003089441860150440e5400442c50a011007041003c03960103900003441680c0c2000040d11188010240340c0719040b070b9003448000664541061010f9900703599200d648444100410400c0503000b001660040034482400c2107210307200c20481c0d035244002c0d00d5004a5600a20041041d0b07880703556481c407054401e0740050b007444107000209081e00d0401441625545140007400780d00d0400300902000007004807020b200300c0c20001d4000e007a0868044000e000c054000002409548544401000174541c0003805100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 180610539 1250 180609289 180609293
    0x1c0504030f0803070f020d0e0d020d0605070504090506060412110a0b030106091409151201021c020414010c0c120206040503070308120901050621160b0a09080a080d15080a 75
    0x650049071001c011601d0f400c00d01d1700c45480015010010b09454960341d5980404104008000200500490b0b2020020345c40c2c40024116018950060316a6101c240d192030a05003070105940000300b05a014034014481088030480b40488596a02d80246000700080b00c02800b045c0400000d03007003c0007040000000181d595445404c01e0125502c821000300c004c4a65000c1100c0004156000c0a03584500e40c0700704014038150480c1c44621032400700062812080d020000f03400c2000609071311140c0c0c0d01180401c08030700603400c00c0c0c005444c01d203002141150039a903110072005441c0500c10070031061070030110464840004550141800904642c01039507240390403206644060304030b40076440d4450105150f1101401882d01640009003014003010009614070348807884da6401c24024070500d011031003501107100d2420007400d03000f4404c035038590125002030110100703544104040d80c0701500c9070010070000e10a4807000701c00340f00c001c11401009800c0c003100001076086008240103803890601 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 180611789 1250 180610539 180610553
    0x50a052703010b0105030105100e2107030b0f0405150a0b06030c030a1805030405010c06180b1f12020d0f02060f0909010f06170402150f070c0807081c0504030f 70
    0xa06180d089009110f0481c030040111660700080c03181c540c102c900e030224100c2050151160021044002e400c40040b01580301441200c03210034502154140c120030024018080307440d00301a4010080e015038030b258101035855a036201407480001d0350303003110040800c001e1401030b00006280e0500034002602da0500f130001c940f65034000c5d1000d10415140030310f812004c9000300100c254240e00103001d142018945001560f07503030849201150394a03510726060324111320440107854454054103491005140c59241103425020501e410400900301807404c101d640300310b4203282c000c0703541130718170f4003030781d4024130f0408034a056541c0029840030000c245c5104040200b80580400041129070404c20390341e6203c1c2c0c50564869000700310006043c1c1260f00c2c1880480955241c1262002d403000c071950000300e022003034907003019503101d2842000141200c140040340c0c1c1401d000d098050050201e051401c103206070341e03e08000001642000c1036a11425160080050f20005c54010700b0800c1c020241e450b281d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 180613039 1250 180611789 180611857
    0x30804141f0e07060f0503010308030604021612031406031e0102211e31050f0c0405060a0503063403020406020d02070e3409031202060c0703050a05 65
    0x402c403845400800500148106070042020031284c440c2d03480d44c1d0940c0c559079515130009041c607070400e4003041013085059040d41ea0014a40c080e4018044400d454030000303040d609500d24541200341c0c00d6003444220703500801e441040e2440b40201c1d950883c0c61002090282c040c6030503015075404403220f59030b01c10b461810014441c1c0f80507481300c50003200400c4054071104040d2108038004400c2080034400d0000c100a0101030380111503491000078071541c80d6851308682041d42e54103034100024842140c1050301490740c0150084880c00c080a0503c40030982d19a0001c2010345081a0524240703602204441e000507210100700e0320707a200000d4110060069031040c854a40140300700d0030a001150f1000c101d020507101408406002c036265075181c181d801703254041b0081c00c4260113545130414050303604100080700340c83d260516441d01d1030030211aa0b046108040d802d40d0407000400121345006800c44a0040e4581052915600d00326400c84181c040d614620011714504214001e101a0041d030348 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 180614289 1250 180613039 180613061
    0x1e060d060510020303040b071d04060f090e01060b03042406060c1712011401030e0a110a06021209010f031404050703060b06130504020c0a0c030b06100c030804141f 72
    0xb00340c0308803200400301e030b69210880f000780c040d0f2817100221341c1e464428003034010345d240040d44000c441e9401d1400501207413442ea10071403414000307403c00c00603007400d80944144c10242500802c02c541c90080085083e200040c8000e00078004840d8901c0c10441c4a0040c149888101c0c0c810044d460711010040c00001c202c0906682a400a0152904403072680040b80d4030101c0034902c0c881d0303036441c004c15144001c03803801c10b00c3d0515848848010310324038200a19001540194428810351810b4801e2207071120f5140c2040045402c18080d403042107101804840c4c00800a180403920340d0210101280101000d00010b0352180c0c0e0407090105102c0b0006900c01503c3c01617504022500e5402c080085e64400c000c0d0300707a140c0340152070812807403801e680039200d42c079542c00954902e42d696555800c848852a041125040d00302400d100f840e003003114190114a10500388400820003d850141400740300174402404240d20044c040301c03064040c41060708000203540c0001c601060089a00040c0c4144040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 180615539 1250 180614289 180614299
    0xe0a0903080f131103010e190c050603010e070c05030702060c0a03020c040b130906061a0a020c040606051c060902030c18030c090412031803080726061e060d0605 71
    0xc1070030312900d8600b19004809600f80440000040c3d0f59020031405030102c903903415503a613030120740f5040c41401088080c0810147da81170300380441c0340c03850400c201c0e40c11260003081c080c801440704c50000036840790413641c0c1e4100171100594900d8480d20b1482842c100940040b400b00310f00c03841100024201c181184690203580000e4511350501085403000c404160f400724200d03400300900e400e00e40c80400c1c80740c000c4201040198440c0b1580c40507003101c4145906c03205000900c045e00590512000ea441c400c210380078003103245400c1c4000c000d030103141c0401b461900f403540e481000026940c04030004209900096440e45009501c2c252103401030b2418040602007407440842500e4041015120410000c2c586602d41e140d60702d5078600c40c540c900006d014590b40e114140400580700c80c0b5a29220f22a903070302032051902c001c0040100d40400740d518105040c03200b505049003155299141d11400507150303500e00d62804203010000c00c59109145401490008100c000710320300d81c11007401d803081912 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 180616789 1250 180615539 180615541
    0x90d152003060f010201151409010b03010b0f0a0516030509030c0f10030e0f030408031c0915050702010908030a06030b0609090d0e0609040203091006050303091305100e0a090308 78
    0xa41040403003004001044240040000804620744001824038511041c13000040e0b411502411900c0e2000d160004940c2840103c3c0c1070085280c0b00c02c0d050b014112203101ca60855241c8403049103a406906206a11040040340380c4c1c550620030010745c0c07101c0c128011100c0742c8807030b24107000d4059803080c44510b0083c040c18880c1000d074200520036290805020307091100024544404034010304844607120124040c000031210728040c104081c00203082100003550745e0f003050030403005a240c2c1410080c489103090088080200300c02c0c201c00f070f4000d00703140d4001c00c0f0759a1b40d0a0880c01080e6a290051005102105000c000b10441d40301c101601d10801516070700341c4905041242c3c109045a0341c802c140d00c5200f0040c0d00781c0c031a410076144146d01170003150802e440c2500003401da130407c442d9008254000b001413002e1074140e000703080003028290041d600d0403032120003046408003001c9002e00c0a42d103550109503090910100da00052440ba01c801d50035040038201880507102181e0107800080c0c0c1c0310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 180618039 1250 180616789 180616811
    0x809061c09032601031106190807030605010f0f080c2703061e130501090803090c01021e07060318120f0206070e09040b0612100e060a09081b03090d15 66
    0x403c0c0c0081501a018010185e01c0c40d0f807401500100810140c1c1c00030428042c40941103241181d00c0c2c6541e401d51204016880c2ca9140201243c099901c15810007070640d81d41c8468540000503e10078900c540b5140d0002c0c0c0c0c84d660103055a1242612107904518802c02804801100a194407160901281030303418070348401d0a20000c2031403950702d010145001c000418406e1603080d40604207148204000301d015400c07519855010307042100e04201e2a0401b5010011642e414040d40303c2e44038030122040741310040d00440300d60315034107401030b0414156520841c03901454600030031002a544032180b040040341d59a0010841d4072540300c0c1d0700142c846d20022400c014040c240c10890710501409020150340c490703c9103003000401603d641e4001c0f84808445101580500403580100c0f040803012640103c01c05a041c0781a600034140301c2c2c0c50345001c01050000301000200c4084541c0c040d8006405210b0b01c07149807c5126071440385500038410b40300079081081801e8840007808545900300a41d0341d2030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 180619289 1250 180618039 180618077
    0x1517010f060e0112060302130b0f010306350a05030a1716080705070b090f0706030e1504150f0f05010b07050a080d02040803031503010b0d0f0809061c0903 68
    0x15001c1c40c1d01003046640203280301d520600c0300e41d45250f00f44001140041d03a03900417074040140c01c0c141c80c641c2c41d107815400e81d0f1418200c0340305410107030a183c100300700fa1a0002c94884044004030550180101016542405020692014602010f64255000703481545000fa6070381d40301000769004510203040b41881001c1c1040310a115900c41c40041200d44800c640440b141035004040505000c41400701c00701103241540300500c81c104c81d100030215088078003199894501244d100c101014241429030580c0000442c0b0b451a401d8601c9210703080741c40d1484e215011165070803102c02c50a1606044076503030b10194008054810110300d0410680e600c88103030910300c3c8101080075003154000b918050004807014000e0880f003011110040c205074407000124116402a184001043c500005103181d03441c080c8900a81d440007180c4200d801002c40d500c5034078018060201a24041022600081d40e49902048401c4924405900d41d030156440d48600c00410001009500041810300d000e8101042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 180620539 1250 180619289 180619319
    0x5010e01060504050112060b1b07091104140f1c06061203021c09050d08040914040b0f0403021207051c0f050d02090319051e0304060903060902010306151701 69
    0x2a588841c83c080c209801598410701c100d034030001d07003942c074000054a5464040500100c1031841f080b1300c802801c032180341e460200160071003003690f840c0074041d03403085460004070b8040711078110001c06400b80500007d801100ca40100c40d400080403426039110114400114036840d200300c80400000344c4841d1042c07201420502d004000da1310044803240100444401d07100451981e140c90303c0d00503119408a0213107465810119200003001c00d05001401c01c038010490b0540345038119403650300c0d0036212001d1a16014101900310b01d40d0f0000b240515209000c65882c0e251815826941c03002103103009a80e505100414409441c02c01511342061441000c0c480444019944e81c01e05140046520340029032181ca541075242c414980c4400c1c6581e0794201c0d599140b4052006088a0703091981030541103451801540842e400070801440480e0b0840b910800345c0b60408000107480d0900c4c401680140400e4001d84e403110384080e20b4681541d80b10a102000c48001d40800c4c516036030f16160940481c1d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 180621789 1250 180620539 180620549
    0x31002120405121224030d050c0f0c010f1b08130303020c04290d0605010602062d010b0d150803180301090f2907020a020f0f03060a051506040b0304020405010e01 71
    0x9902404280b042554401030300c80304512465017400781403035400181c40c08004005000100f000030401c5601e00030b040c00365151804004c3d02805c0340380169030000700021038440800061200c5020310b040550100040403c0d91584030044955a4034018400f401029281c40300b180140b080d08100405801d0038002c03010b000403001c1450740218455a0641e0b01468031501094020280310000f030701203001e42c01032500904140e000303490743d810074009591b112001d1007019001c1c0c0d60904040b00d158090354001c0750440301a204a00e481d4006171490354040d21032040c2041d00032640d00400305043c1008401030403000c0341d00261100c0030280ca010715007a182d000c2000340211001110b014081100420314500948000d10025115400503a000003081010781d0303a500141d0005400303804509040d205200243ca00b1240c40c2c55003206400081e03030b00d1500500181c0c0c3c568861010610b044403426903a42c030b40c00c0c020300703c0780c807079460721400c22207500229800e82c4114180400040d0900c1d4056a281c140c42d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 180623039 1250 180621789 180621817
    0xf09061b08160c061407090509040503121909110907090e0604050603010e031318021c1d030d09020f040b01120c020a0c03240606020307030c0203100212040512 70
    0x740e80c03056071000b41204070a6010911002d4401240001c00c03e10806070b903404248605905400c003d81c008155040680001d4020302c40c5400340070204d84004250392100a40c00000b1384590744580840c0700d4203d0100a00c4800380c10498410300700081918030788050031041e5400c074029a10b21800302d4404100e0320845c144201c940000c1400340c2000c0c0c02c110350129000d0000710f8400c10300c0710346628590203010301c22541c2c4c66403d4184a11003d400314580c1042e8207030410760a100f00340e031070480b80c0c80044c14054907103a0303108032032004c2c540d0b031050303100781221001e094a407940107045140c400b820743c5c100c0c100d2185000002a2802e03140a100f40c00b4062810f03500c840501c41c2001406004040c00d00142c82548200d200410001d982041c0d000050340c461a01c000c107100c000440001d000943c1c140f4445490f050017401d102e0701d5800000d54070030982518000344807292500101c0e05251407008000320f12070000400403030800c00404068001c80c85142103500c1a402c01c4498406401035081c10344101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 180624289 1250 180623039 180623041
    0x3020307020c190611032511010f0509091e01171015030803041506090207020405060406081c110d030507140705060106080903120103050f0d020a020906060703050c010f09061b08 78
    0x917846030440401d40089101200d00e44044407101c0000c40e50954000580320300c90303402c02010080b5150b242c8040d98000c2c284801013200c0381c000a42603005002d413481c06030360503000003001d8010703a09044a081c4002c0c05440019610b42d28038902d00000312652051a114241c11904060414031540c140c030949442000380140c110fa44045c2141e10250007030703d001d9440015101190104d04c9a18010059036034016070303401e4584103010582e0b00007810a03114518000007045140c00101d5100c411344016103c0c0040014610004c0d0b130070602d089103034030041c801c1600e0f103242c168043e804203005114549610f60010300c019a0843d081c41503c00090542d040280108050b40c00341e1041a0000310f180141c9082c90b0903961104486c3e60240c2c01600d040c1d00c860900016920f05100b03104452040d031004d002e5004560f000300d00b01d000054015802010000f03600c2062600c240c094600c040720b20802800004030b02c881d180b002d0104418282d985500e007a1041c00c80c51070074090028070000315100c00b0f443d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 180625539 1250 180624289 180624299
    0x6080c030a0b04140a0b010912053d05010906060518010f02010207050601080a0308010e010f05040504060e0a06090c09060f050d140708070501031505030d0e040f020a0c0b0604090221120301030303020307020c19 92
    0x241200f80281100595080c00b0301302d1282408805006c4901c94450000038158034110ec40344c240c480c50b5001909022042103114030004002114150110003803d024207100c1148008900901c180c410191140c0190b400104200c0c8010520100040c00f03955641c8090b43c9690071000f48880a100300d044020380034400300402c2c00c15802c09035105e07026400010f4400c80141416046c001d180c0c1040703510310f54a181c00340800c020080050060710003000e08122070340c04d10f00201c800364101c1c0a02ca210700700041c030345010444040786005a10301032a013030302c130040c0e51114070316074800944c012180840e0070704c19884a015107940700b1100300c03003000f0010f00d1342d5204d0342c20a0307a00e038080c601210340254840d640c120102040d40010029605250b5600f403030b90486040518501c440075040c6485a410714201c278000d0380c2d4480403092034055210310b0031404d00e200701005181091254a10f4503245004c0000814550998051072040e5020f4003640d2800c54200b0411030610100000081914030641c4c080c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 180626789 1250 180625539 180625573
    0x50a02060f0705040902040e0a06091514060705030a1d01030504020d0201081306110c07080102040812031807061715060415270f06080c030a0b04140a0b01091205 71
    0x10b041006401e0481c82c10b0b07100c400110a87e03101307030002c11500e55480203110032741c0254030540c0002d02c850001084461040013402c449081c40384a81d2510000102d1246066039420080300c1c1100d9000701100e50301c21034948043c020000c0381030000301405102c80140c0155000b401480e220341c3e0300a1103010700c6a00b9600544144d00040e01c10315401c0101c4424100251403032007514900380c0305040c0e05407110b0580606502d410a241c01c0810a80d0040c0002c1081650018000c1380103469000b100d0748a075201e40c485954400724001400b1103126030400051a01d400206c40074850708502451811540c1710906800d007059803070401600100704200070400762000022626466817145059256500c05010b111001e400001c203298250000c40c0c0200000c02e60300212000a0103d07042124162900350244180e50000800c400540e0351100000003150ba160350100b004d0354030031302600802d810001c1d0300000800b200781c052400300d400104082103168035151044d2344035a11074001e240010710725403002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 180628039 1250 180626789 180626791
    0x10801170d050c150901060f09200304021807050310050603060a03140a0c0e0105120624010c120c06050c040803030a0209010905030601120312020c030d051b13030204050601050a02060f 81
    0x80307026075113401030307a100c00842c2d03c2e01401c4408004100c0504020341c420350608294800c515003442c00070000c028000c10404c074140b201020305002e44903622030020030502d108415401030079080003004c000b090b80d088400345001d90200a400035074181c50f002442041c0c802960940c3c1d00400700d210810008a031a0015044141c480c070075140300304000d0307882c9207103041c00d60401c8001084c4640103201c2da007003000e401c0000054200080c195810032001c0030030485040c407030116001a0100740502140d000d400c00600f815442070491001e02c0315094014100c4e0400744084460074107040100d803004142c5401d5070103442958003c0d501e141ca83d501c6041c0254000041c01d418804114000a100c2d075040c03165600030203081c03940c40c0c0744414a14005105c24602a08000c4151042c060003015030000026121009824500082c6c80e89480c03101c07030b0340041030b1311201e031200400140e08620725440795807000c1203910a581c2840f2b1a00c0d0900150f40034081e0095841c01a409a800a100700720300140030303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 180629289 1250 180628039 180628057
    0x21c09030516030c0204050703020a0c030c02060f0406030504050c0924030f03040b1206040507080a0911040608100b040c140307051606020703230a0e0301021314010801170d05 77
    0x418034010405552030380080c101e0b401036000ca40c81c00c0c5140190708090140da030b4041d526140c21894851481c1c0c000c1e01083c00c0b9000034080018285c0e81d03000310b44983c401c40d0760307210f90308040c981c0329035981c10010060300e802c030750841f5540180c004010060038050304d45070043c184604610440006e610480c5070703214052000c01d605124003032959200b000d01b0f10003800a8054068000d40c2c0d60242010b031200c00102900507405a468202001040707603010b142180c010032003980224480e40e1600b8200303084511581c00c1503010b840c00d54001420000020785440b00c000c40f003c00d00540d4620b404200466454404005c08207280001c1103d004160500071030b0b1007805400c100b07062101a00c01e10052144481d02290015070000d041c1d8180364101651980440180d0003e40c1244610180f03a0b01d140500c038080d4050004040c4200c41950307007074040d200f440d58010002810a9521a9495600c070100541d560100e05000f002080d2040b156182c103501001c440c00600c4000301412049038290320442c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 180630539 1250 180629289 180629297
    0x308130602040b0a090501110c130209030a0b161808121c0212010314010207051b0a0e0405060103030f05070804030206030703061e031403160609020a0e09150109021c0903 75
    0x2c0807406000900181121031881d68481c1417050900002516160340747c0743d841c100c0d90103800341ca20995242c42d5044c0811101c00c80250f151070110021900d00011000020811070000e400c1010403100d41c0395216401026590b90300d60340d03c81d1404040088414019007549400001c00481d2244400c2c000384400c2c07504170803050719802c54a1805080781c2010381b81403c140d00460040080c40610400e603035002082d070b8002c6240041982eaa02e9070744840c00402c420100c0001c1c40746045917600340904000308030901c8411079030b10305407070700310b494403400d01045001c128034072000515144101c040e525640d034040c40c0c507844c107400c40e020411590002848001055114500400e80c502410740b50f180074004024840310b1a800c624115008003040c9d00c00c000039038001e2200c8a181c40d50000072115064122100144004141c0081180100240c004a801c10f20180a00c90240030005510303d254040409090040c0d880350725040030b1744140c00d40701c80b0304141c28400004003484d030b42c01058540d100e800c3c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 180631789 1250 180630539 180630547
    0x90a0c060206160516060e100f1b080f0f090c1003150b0a050403080708070f0507060f0203130311040605122808030408160c150e0301090308130602 65
    0x16460000185a40200005030000c500380107503002c104040c03055560440c20201d003040b41510400320007500480c0042d040603210703440b80a103a0428000ca0211030400071051248504d912813a1000c0c000741714902081c124082e90b480340d06481002054001d81c0c80310f111805549400b950150b800401502072190703401018a44242c50343c8801a1440d40f0034292004078100b02d4805406100c182c45d50b1040395840400c0100340d203400d601c0000c80d010307a81d11562a98944005082041081c0034001000300510202e014140600c5400030301c0d4402c076021076569114500411324101d899002e800100308a80d100c1e03d1080c000503004c20011298107101a20000b0420780e03880000e0059001190245c165030401005000c001054032100d0740c01d1001e00305840c8004134036a40391000f40c80000c00c05030100c000032502c40b0244039001e018080c0560094400c40030349440d0380d024065021850300362400300d2000301c0a05403904060140c3c0e000e49402d40c884c0e14044d900d1100216002107101001c6480a070300308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 180633039 1250 180631789 180631793
    0x108060f0106110c0a030c061101050603030319020d06120b07031b0f021c091d01050a06030c181d1e0402010e150c030406020c010c050a020607080d0c02010b040b0406030c050603090a 80
    0xb001c10002140582c43c0e42c0b401500e23001c0f0140210320000030600030769060904100c059200001143c1d04410010240d8045103c0d00001000078054050b002c8480c1d403c051001030195030310388072149d08034000d10f0806140d0310790a0058044580000d40c043c0e03500c0040721040c048900800140d80020501c0c01943c0d40303c1c401444c940c40704045491882d0108410100c1801021450f000d0168030b20300240c01b038007455040c42c0001e41480840d00c00c0804154540301007c958030300c40d2000b4003002441d2000700380c4450702c5000480108487d40c1c4451100c118020002d424204030407200400f03a1880f04400500351115001103480c1030680d0480ea1b000740d11b10303a941c0540d0400d807000b42005e82d1800069920399091180003030406007412f2459041240700303406100459004140744410303540c102c410503510802c0e8640907109002d44454004164036003a00309605a4064005980d003241c1103404001c14010381c8100310031203091f800044c1c85012150001d10540c01c1120085422500c500b049a500011607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 180634289 1250 180633039 180633049
    0x1106040510050c120f070e0321031015020f0c1005031501020712060f0506010203030403020318040b13050a15080a0201030509010906020c150106090b16020a0509130b0108060f0106110c 81
    0x5d4070402581004d100405c0074081d4402c0040e10162021405000392403407d6007045074281c012600c0d141c40200001c00b2442c8007030900705403030003003208409a1590f1400120040c0d161400001b100400d0300404281d140d03540707018000320288618a44815045851710080c9041c0d032103190071690f040d846022804101c0c820700c03500b03214202c0e10421001c1500300f600c000010585802410407415940b040c000d10000a4021083ea05c2500427060721550300c4031840c2c00034000d0f0100344405d03a00920b8000d2092056445a00124460101d0440600c0016409603105016000c3e034464511503821104060b4010341c400c1d000b02e07410400841c00450034a4064840a0803030b801004100c006038040313800c4000751000880c80900501c0d243c10300d159900e10705042c049043c421400c50b00120074030320000070215a10107902d075001e007038003a242c200c0c1c80c0392601e06005408095441510340740145000042c90500c0015800c0c85502440041c90b0507034a0010103075131499080101d04454040c62103d0f000369161 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 180635539 1250 180634289 180634291
    0x1a22090318060801242f0c0402092b0b04030f0305070f050a050a02120d0501081507050d050403020a14010b04060b1c20030705090916090b16140d1106040510050c12 72
    0x241d001b250f0b07001d5039482c12140c9002e191361901c50099006110350400c40c0c0d51005540074050a020800d4050401100b10001058003204020302c1c41d2030501c14801810350200d181034140d101c6840400c0340b80c98a40b801e8466039550901c0b42c0008000300015001a440b40018107500544c1c0d004032810310341240c1c0f074460150008c1010b0900140d030b1b440100200c180030004101c1403003e40e40000403030b0030141c000414a00c0b0341080c140216454802007800c151080054421154221b0107580b0541840c1c10054064544107a07441d115074100385e004102c03c512501158114220307141902100314010500230040e000311001d40c1c4146078000040d050030074800000f5071203101140d40e01540c0c0c5d44100100291101c000d0400d9914001c00725400400d1500403078044141c481131014551140044031154021a484540042000c0c922007100d00808100140309240303003000e9102c1000050342135005c29510441180c1c0034040307601c981c480305425042603021640111140040d1440d01801d44802180050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 180636789 1250 180635539 180635597
    0x10801020901140a05030103060506150a08010e011403060a051008030a0503010812030606090d170a0309020306131e051603030c030809011a2209031806080124 70
    0x50000350031107056078800c5082000d00e1403010140d0a040d40050018140c0c081404001d03e11592400810b1040d60b602c60500861007200f04151381c2d0301c20504000342461400c3c85880101d03d5800c0002c208240c00c03255400b1140c034081d008201507a40c80d07910f94050b0802811140d80d2300d403890740c04602d410342400140240c1e00d094035003035501c6d4545030710240340c4982032070703414ac0700f00d0144240242503581030110380d0045000c4480401c01c912509018100480c0010300200300d007400600c6541954040d0004c41c0700758000c4090716216510740181c090300800c2400000c02d03040c050003009400c0e03181c0e080c40c0c0b15010b001b20226540e004001d9410500c040760340d001a8003042e1001030a0080542c050744031a802038501000b80544c58200703503043c48105070303119068070500280d4814601c070034110141950301007001c4024030203401b1600b00900410ba810150356588200b4510104540b80200e030034a0407036426844200054090300844182052901c0c41c140411201a2101891002c07081c0039142c0381e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 180638039 1250 180636789 180636791
    0x180a050312031008010603080403062301120c05030d2709020703050910021b041107020612060112090b0c07050109050601180c0206010524160506070e09100603110c06010801 76
    0x1040505840e058583ca55002000e10b030704101d014000254010140d5048a52020b40070440d0380c2030500604148002c2e200068482183c0c000000381b1301840c20700241c0c028054041000d8240c1c581e4189501c50203c501c441021424070543d80c00c40328400b01c041c0c0200d18581004510300380d03c80070b080d810b0f0703800040c0540c001200824050114541b8101c02c0c69525050b000038094100702c20410098000c81c0301d0024030883d80d0380e292618000c1420125122030f940141195500c90081905070361001003560741d240020b92041200402c0400ba00c14100859000484003034540d42e039845404d03031544080b80440d0503540301e600100c00110304001311400703032050040c640901038010042c7c00489002d02680d200315403041c001013141e070312a42c0600244d20300804001000c40c07100420003006210b2285441c10218071000c0e04020301070b0100302c09005001540c0c601002d85a40740c20401a00c2e17096800440d00d0001e11400c0204502952040c0e078007000d41201c03282400e12a02590f03003458000d0b80000b440f0307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 180639289 1250 180638039 180638041
    0x105010303170702070603021b0106090204031101050c0a08031308030f090d05040b041e080d0203030f0114010e120c0d0c05030709050f070f05090a0311030f06010803180a05031203 79
    0x1500107000b42100300c05007202501d946060341c0c2c001e6890f41d6038443c0d0001d140c1c1c00140d403040d42c4c2c4401c528604501d0705400038000d055441c04a40700950061105803400144400b800c0840d6120705d0464405220b01002850030751100d40310381d040c80d40033a05042403038003180c90b81c3c0002109080a0346c800c90791204200c0e00c42c90040c541d581003460403074a110070403000700070500114420320b0545081e60b644900c1440710800813030a280394582a60400d103d54402c441001c1c803610b50000081d0711501181c1502091640c1ea0084020015582d40ea0300c0d011030b604c500b0344038050501c0d00d5154181e121a80846d060002e160010803c60000702005030782c11450403109120900303040200d0700090241d104104001e1820000f64440d40c440505a00200038801b08403142003880349040e0341d0001d40c02042014030303da50b490300001c0f80a04405c218024007810038040b80518001c1217042c125032446001d145040000205011082040c0035a5948100c0c80f800c085843d803410410b40d494a81080c2c041552 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 180640539 1250 180639289 180639293
    0x190303050a090605040803150301050610030e070302151b031e2101080d08060d12050c12040b0a031b140c0106080d0309231203180d09090b190b07150e01050103 70
    0x319040144049c1c000e0303040005101741919207000e4604003003c41c1ca4000344e404480b0403120b0405a00d80d001a600602c00340881d80c41c450010024440078a031680200340514030354184685a00a11140c40500030b490762020580507140e00062010080e441103051001800030241d0390f03511000e802684542d4003410a581c445904000802e4001c0400c482c540b00c600e40e5550f6545001052040ca00304011000c94803450380c1d5410441182c500d1200d220540e01c490310340394506400d81140c80044002400e1000c81014a0540a2a11a80b03031490780c4400b0502804980d081d17040e88220b1109400d5960f50b0303c0003412210602c01ca9021080c50ba801182889190800144118007004201d100d07204ea1210420011030014100884849600c0c00c00c4c0c1301d5480118200e21403010b100071002c0f60040c041c811400d15484008403098a14401c010480ca4001006000207005038100c90705516016440500503240c00700081d1031910703c01c0500d0f5a8031880407486006031013001030f42c228603030b444000609c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 180641789 1250 180640539 180640561
    0x270f0e0a03030b13020f070201050913020a082d0105040c0c05010e06060103060f0e0604090309080d0c0b0c0f09040e01020f070803042d060b0307050a2303190303050a090605040803 79
    0x403c184031900217504040520300e48030501c0c414003400a040c4200050640c801c0e480311280390085d400c04c1d080c11500d034000d07600f02816426045415035140000810b20213a503205244a1b042e1030440e45600c820260308140601c4010401d8010200034400c400c805103001802c24082c0d40150b41aa002600325070500b00000750660741c05800440384c10341190300601403110f41c20a0554170013000c03a000300750140c13581015100206103400000050013902c0d1448600d07904044000100742c07041002c0110f6550f03a402ca50114002c1c400120801d84c0c080006036500c3c6840d070800e4800b0f6000310001481e0030340020303000001e5880280100d1707003a6004010401031246800c0c0072042120881c90700c200c520742251452001030b440350360081c0020391f15100d01c8015281040000c001d001c0140406d4421034640d82d0303109401d1400841e0a080c4401514401c901d400c01040d02d0752480d102c2503603417110340304a0303900b034000e002d0040400380620380c0c1c0c140c0388020a055006040c00395018149040e924202600004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 180643039 1250 180641789 180641809
    0x50405030106050a150f0309080f070515130b090f010629090105030415061802180d02030a0b09010e010207110f04050c0f1303060203070e0a270f0e0a03030b 69
    0x944034a0003500100204d60b107030765481c108007900d0320703080c0c6400c000306e182a0b0040c82e49480181154101058507850f0030301070001801400e005004540c0050108018074103003000841d024100d5060b035102d0600050070304035042e500035503410103480c4928000d680190841e900c50f0f0080c10b082e2030100b070141d0b413195440b00f0554501009a2264508080000003800310720001c1d01c0100860b860100e00c2406800a6110a01401c0402842110309680384030040c0a904003d0040f80c8080c00314413844101e2030f20b440404155540a0058003400c0c2403a11801c01200004120309500d540b05ca020740c10100e404c1c8010310f4110302c01c0c0c00312000040800140500d0107031840c0b856001d940340109009501140710250b40417504900ae00c0c540d580e500c5102017607000b016a02c02084e0a001100307109055070013014149550038180d500807a11036543d4121040741900b02260303201a1580000298807540c01e03080700024003548480401c14443c0d48603900e2030100710840541c00259914444080c2d45404442c030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 180644289 1250 180643039 180643049
    0x108010203090c1002030910050a11010501050319021908071508091e0a0b01140f10050708160203060a14060d0519050c060c07090501120b07110319050405030106 71
    0x21800c610308882c0841d42e401c02100182c0c810705289200441e111310030800c8600324500a4600c81c41c3d031b41e06880141998008a0200700412030258001030000014840c5a0484138000c1c01094140c2d0b800c2d600101030300074041c080c0d800c0b03004040500b442d00a0011807400618001e4010150b2070319140d000111000c92441a004001c0c030396041c40040c02d00090144c080d54584804042c00e16520743c106850039003241070080038248035030000034a0510480c1c69a200c2d48083e074a8401181c2d00e14100005840c3e1541c00c000490001c0c003412011400d00030207440141890002031550b9802c91700000c0c5001d0046400740d10250310f40d800c13007a840b1070240c9699001030054812008203512543c4040c0c0301c40c40200f410002034001c404070801d0003010000751403030287c054500c0340c0d10542c0203c19610350010340104481d441c01c020000030500c1400b030024114035040520124162925882169a010034072240f0b10a8801031160701424086190716042e010041c0d10b0795940c440c5010107050a5440c07c0d400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 180645539 1250 180644289 180644291
    0x507021906080402011809142703250c03060f0f0501120605041707050d020c060405060d1505040c0c030809030301064e0515130903051b15010801 64
    0x4100074440c1c21900e010b42150742420308840c00d0340c0d81100860090700c20303440105500c2c01d080c40e43c150a41014503250041101d007000103002d07010000c081d102148240d01c00300e07595108020043c0784140c07100720001400190180c101d030130140e80d00c844601c08200e070070036940341d9a14502e00c1c40030604d80c8134000c0803d20301c0000344460740c07620440a1103148120780241130540c6410014040140905c48483e1030044100b400b40c4800c10782c28195664602c9480c10005482250006200c030f18080c1e0a8070101d640081c002c61900072041c5074040604511000303c0c0d1291041c580200c0c16030340e0350091620314041959907407070074005420018a03040014103508915001000140045603000b04400e85800c500c6c1c904204010f40c5a00c4105401c04030403000d062641c1d038010002641c20000c0c08070741034014219041c400340d11014081d0700320094507030059501c03a007889081226409141c10140450340207081076800c107440100401c180300f07141ca0314000030313821040b0003040c1d21034044420390243c070314200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 180646789 1250 180645539 180645589
    0xf0403020c010c020102010213080a020315010b070206090f18100504060e0402010e0a080619050f070f0809070302120c040e0a030c3e030706020a052107050d050702 72
    0x8019440300304020800d41080140d00c04a07003964000d40446191400800e00c0d94641540d039091180ca4040f0784108a2103402008140121203034072482140c1a00c42440001d07107041e0300c913401c122a40c0e1110036900e42204060447c00c5035a510702620450000080f008c40003640383c0050341d0440c0e001d07030b07411451080d882c0184c01c0c41308540828070250302c80da081c21310031014aa4400098400b407803079485020309201d054100084200501e1940081c0c09043c03106104503100c2c0940c0d0701ca80d440841d11000018036000f185403501f07114211480e04203082606940c0000c0e180c1d00880c0001c0c03014400078000d42d1090100b403040d030a0034800e0003002c0405801a24150020b6540200991009030000c0d040382c01c08800d5848818441c844110b0141191a540202901c00c6800c102c500703050075281c506c64064042d0004000b0b0002c01c0c02c4c40c11a80c80400f0700900301c006403207032260280d10380280720b501c0824444180000c908104403040240d05032a116160101d610400c41c9002c02500c0d03441d85081044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 180648039 1250 180646789 180646793
    0x91202120d020c03281709150403050415020114010902090d11010306090c020f011a010c030302031506070c0806071419020f060703060f1725051003020a080f04 70
    0x64a140018054000d07a403040c40302215031842c0a1010345e00c044003090007110503024102c1c031040c400c0640580b12404046905460103807a19000c81d10003400703800040800c910305442e8100b940d0311510a0400c54181034888a81800b800702d50b200700c0c00540c1d56501030390020b15243d51010300410b1954015441c050f03150000c5003040f100c518000700b181d4000358400381c5c546e000760841400740181c2e4004100c441500c00c80203507034004074032440105501e456014010452081d0101c07000740d8040e116101c52600c42e0f501107000358001081c6190403c00c07080c0c1140d555461a0007020100c0c020580d51524600b003c84650800ca000b42c030303520611041e45038200034050901c0a0b108000d00740c031010031018030000000e83c00c001c6410b041c150940100e00401403d01d405612034426142c0900c54a0f14007a15840c840302009900711060b00b240d40894044c0c29a0317a000c030203400b035a1070000c150030342c01561000400c0d0420350f03000c6010041f80d008902c4041082d40400c0c542e600c1040200101500d060503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 180649289 1250 180648039 180648073
    0x10e250807050f06070c2c0f010506180118090606110d0215190518010c080f010e07140a020d0f0203090a150e06030f04060c09230112050901091202 65
    0x74100314001d00b0301140700821700c0701e0420118001c000d41c0983d00f52102284107c0107181c0d038800210f080103120030011950342031125410354161400584003514101c55040700d01403120403600b501741081241006040c1150002008030001c20079018045815420100050222881d54400d000658080318103507081d60303400100c10110b10399103030106035130b03450b0440c41c04034500b500c0d14186e5401c2d081c0814440c10f0101d0004200ca0002040003c0210400d0b081045800c4171055408414242507400184060300d82501025000012400c0103903030a401c205500c40c11381c020f00050005600400c40b40e1420356080607202cac05a615510281d0314051007003000400d000c40a000c3c040c14a21107174034070280c95004040110310003000070103058076850424120301440b401120f00f01c521a0801503001034850203044400300b0349050305075140840720f0345180080901c50901406040006100700701a0240044c0318003801261014000b06514030103052205490600c18056001c640c00700342e44110401c03074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 180650539 1250 180649289 180649309
    0x801020f0c1908040e0411271003020a030b070c021c0b011401050a030506030708030403081317120702060904050114030c01051c0f021902070f1a030f060102010e25080705 75
    0x403005c1c00c43c503900c0d40e0420300306a409000ea002d81045034030454888402500010b0503d490203101030500075602c10382043d01000a030b1100a4122208100c00c0c00003c003441d030200d9100c152840e2017022001c6940001d0b020a10120000144a404a604d00140802d0300201405031501c00d0301e0700c288910301c4000034480d02c144404101010307503c13008200300703aa041c003082d4018000102103945554507030074061100c0e80074100e012114408044009900404001e1500001d4600c90141400b2001c0290340803255002038070490f449041000003a07440d41d00ca11440d8044d181a0501c00c11401840061618201d42c13a008130f0b0500900380110640b204010000790040b099062000c24407000e00c0c50039201070b0141040d9104005440749240c418641d000030701404503110301d80014006030b0781369003030401c00350031000603814940200005203164516205054002d03606200002e0381510030300302503051150140c03038202c444c100900e5038903064420710082d2020700121005000550f07c1e1000060318410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 180651789 1250 180650539 180650549
    0x304030e0d020312030c0409051b040302011101020f040e0108011d031803030904020a02160b0f031302010c0501060902091017150d050d09050a21110a0801020f0c190804 74
    0x10708900354008544081c4540003820005202554480c10402071071201d5412502499104030f14120020703003600c40190060a000e10405000c0345424199001111851000c001e8500159001c1264840c01040e0700000c10040100c0f00340c002155040c880300038250741c90074965486924800c46101402e080220072118518510f114940c00551100e01081c11809039140b2150302510101e10045030507004180c86008120b07040c0b80e80c5000e80c40301250081401001141810000b0070320001c3c68100a50b44030404c090b00505000c0c8810440b0703903c075030a440040e040741031180c0d0003103600040e900b0414181408901c00341468410750780303190080c010b05100200007244041c124a095070b895101e00036600030994001c81581c0001c1012038014140b0b0110f813060303034010032860388002a03c7d10301d40400300002c007241d008405240e110f92107940404c03032482030141c0c0c0802003660020b8000c0d006d1000301140d00d8040c0080c0c3e00c40c05039521843c2800085480100c003030018441d0040040c0020085800390f40d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 180653039 1250 180651789 180651799
    0x32b0516080f180a0605070e09091f0902030313030c050a05241308150115020c0112271505040803011e0e011202042f07060209040618060801020304030e 67
    0x40e6419000c116010545044068035000b84c00140c01841074503004a4481e11403500c9044032242294140074500130304894500300b0340c1000300300004800112141810001035403c0c049403140c4141c0001c1e0841d40003400b15208250b00c00020801c01c0400075011005000885903a4969440c004c04601c1082c1001403403120034006005042d003003090001905c031209140080e0456190b100d103141980c480645404401545403c8000038402d82b44841803202104250701800300b0130000001034a0482c0d13200e0305020302907143d02d80b005500410407084005084c2c00c921481d0041c046040c01a0910701101800307407aa810f01040101080c43c481c11641110a00c803248240c45150b00c8074216480803070742004000c0d0070400000510b0f42c943c141030008050080300c0030050210030301d4003401e040d0794000580d00c6000341d04903844001502d440180c000a8000d08000d8506000d02002900700c0e4195004148144034007030307480c51b2903621441450003a080303400c000c500c0c508290310b0140411815298981c071607 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 180654289 1250 180653039 180653041
    0x211e170402040f1104030506060405130609170309070915030302120708190509120d08010b0706060305100219021203041403160602031915090509032b0516080f 70
    0x40d26142e20161500c3c0d481e040400031a050744410f6080b5a0052006a540e4440c03e17020038421724040c403406005d00300000a0b6001e4511941c0d489003e0036049209941a0b9510f458026200e14440d0003548100460405840160b040002c1c0e0310480746007004200f6100b0310359109000094001910040340c128038264252585070740d1030402524428a60844600752401c00b0003264950800080c101310802150030142d410f49010030300c2d688158240a040004003020010428045450020100c02e17004080c04250507032a0f0326810324003001c001e40c0c44002039000036964403419080341148004501440589406049008225821300001c1c00c003400200c40384425a820304402c20488000e18244070100c1001111420714000a400c01c41d01801000906200b10341c0c14602407261000c81094180c02244603800c0c0690700b0003c0000030200820b074401040b52101030b1342d1518104450785041c03102c014810391500c11140c141c6a01908002c13040031811b940b44c0c2019001a80680e00080c107058062007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 180655539 1250 180654289 180654293
    0x61e05030c2205090a0b0d0210030b04050405150105060f09060d020c150103031101060b0d0504031b050c031b100e01020304150c0c0602060712020702040603211e1704 73
    0x403522654554100c0c0c50792012208807008040e10994003198001c961054040d41c840c200304090b5000b0210850340f00c4894121400107140c842027158a03031001e131800195031001800814102c0d5400d49066980d580111b1010382491940c20b01a80541000e5880701c2c10420380f2220712016005001d18607204d1a4003003500f042c4243c0d01e42c1035074640c11840c0120f03080300c400070b039440d40f120401b80400d5000881c01200303c2e0b03c294050240310100c0b4280c000041c540000080e41c08002c242c00b62081b01000913601117600220fa007000c18038625400b50f03000e044400801e0080500d0300380308042020b200c4c003100b9100c52042c0e861807120340c0400c8050074511510181400100d00318819908080750900080e50208c0700c4941c4003a01e2045503110f6171102e40d43c9a16145c040c2d0740c0c3d0900721f9070040042c81601c04102440102e401800c84a1300c00f80c00411841e4482d41d58504443c00390307417440e0b0300d440ba50b88000350859111140b03c240382081501c450001c034901100400340d4082402172443c000089001ca41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 180656789 1250 180655539 180655561
    0x102011503330e07170a0201030b0402130f150e0a0302010f030908130f05040207050613110301050c0a020618251802070507091a0d060e01050c040807061e0503 70
    0x403207000c604000b0020071414490100c010642c4030000303155841080008250100d0030030074920740280308002405041025030044010b0300704880e01d00c0c2c100e5001d00a0b1242c203521681020003501910704042049070074001e9652451030545403101c10807420341c1310143c55444002c6907034103a0b50280f82c100001c050b2200150f001e4035045030001c044240008603003510010780c80680085c0c031283e0456044065440c401c0000340e001380d5502410540080300455015041c0314100044a40303c0c2c94a1110180c1010020b821240d048a660032560000607540303420075818008180d02c03001c030b13008502008a40b8990307a9960540c09001043c4607400d84543c600c020194524a00145030604c19120302910100e0048040d400818003141e03c1c0c400c0300004610755449019401380d903160303006480c501511140030003928003166035098555541d900f08103225000c0030b0194500c1450304a044941d01c91900580354a000362070fa10070b04c200035503e00380020764900015010340702c500b42e1621035120340300c9513503c40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 180658039 1250 180656789 180656843
    0x406022515051201090c1115010501050a1403010605030402090c0304050705040b040209041b18080a230a06090c080c01170601020115080d02010c0801031a0403021f0501140102011503 80
    0x80d40c0c100183c40009042c90320b540020400000c10b0703907036030005243c0c10700d182e69620040e0080500c1c0050b6500502555100780c1c0034000d515400d103400f49103068140c10480030342e4401e80202001031400010401507043ca8000705800000d0008007524603e070640b0713010340b0348015014503407183d1b03221810301c0201c1d510360b01a00d8540400400402c1b28100012060b4141160115080b022039034482c0d0f0812038622541160044442c100040d01c3c01517a2642da0001c2003007130710f1074414140c1c3c2007a01c03c80402030030842402980d225040000e500009424081240905603010b003e041c3d101d0004015166070141e2051004029001805260380f01c96005134050f200000140014040d60a4001020100043c0700c01656000d40c00030001d03034010703031350840e0026800d00000d089c5002100641e1100d00d1035a040d26400340c080c0c030585010040e491294035026055800400ca0141c6031401406504145c0001140f6020240003c000c1c40c100705010040703a800d10310000d0039007100e040101c06003018000e18a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 180659289 1250 180658039 180658057
    0x18060109080f0708160510050d0906021c1109030a02121905030703030b0a0b0405010c1425050307050a18090611220302032109040908040602251505 65
    0x951010319041d42a0ba41e9000700f8403410055220b00301c41014001410b50080c000c0e94000780031340c076003802c5000003907803a980107000030030240e60303112403007408180b003403024128400e001600f4030701011b201c080d80070a0311a194400c00e01a001000000c025907000501e0060a0754140e40108420b810340054505060024194900105090100c001001000f03c01000080e100c0c0e1002c1004444040c1402a0300110340640745d03031801c04100600066019142d054100ca10078141100440b5010042d03c0c240b06c0e00d08481e162114481c2d220040c000c40b00100c54000d0a02500203192803481d01c800540b1f4003509202e05112604d079550b0100b44241144c02c030240c07498101405011a000d5271942d071540b90b0103c5500f14107021480990740014084041e92011039170000c00411000340120858610184070b04c1130810403100c200000c80c1151107a001e01032090f80903102c21601c403481d006010381000d680016003892413102d1144000300c115000b0f40d1005071760020501c4400003941203015202c500ca4400d00d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 180660539 1250 180659289 180659293
    0x30e0c120712110904050705190311011409210d03021303080c0a050316020901060804030e0f01020a150212010b040b1603030605121609181407031a06031b1806010908 73
    0x80006002c6d000481c00c00300c803010b0324544140c1241c109040c1c016031940c0070041c2250908607644281c0d600c1100b0f1501c2d07000c4442402c600e4203c08500040c40c4404c40a032400c50b04040080d00040d001040c8002c074018841820250314052040003801c2840303074503000060804502281101d4a191304000d02403119a010f0300f00d035584c0d18100c0300c0c4d10240c43c90100c03c81c860000f000002c900c0521520310311340240e0389501c540f24142410300c10800140a80c40e195811441000030344804aa040c0150000a011540b40182d03102150b500301071600710140c0001f079241c44100410421042a07000701d4030140210b584802141c0342900e821000307030a1a43c066584008070200207408454045030500e0580b40c000c0400d1122580c54441805403895003000c0c0410515a030740d49400300e0b1088001e00d47c0b0400103001d540c0807135166603e07003000c1c1502110f035038445c03140c4a04009540c01c0c1003045181042c201e0a2402e800134080001541054001d0305225141320031a0110741c8590003030ba68a0f000c0c00130801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 180661789 1250 180660539 180660541
    0x40f03030e0f160501031803120b0a091d0111070b090c04050c0d0b0103060b0d022107170108070e04140a06020a05090f0d080a1409040c030e0c1207121109 68
    0xc0c0242d69004840d0b500d443c40c0c03c3d0303440000761540c00307032150044180142d00720940f40e0b601910207444550302e000740003603d1910340076110219520139030404041c040461001401d800f1015000b61041c045801e62269685444811200c803200c4505403030320944e01c56411130465a42c02107407800d10f04e5800000740c10a081600340072020801b10090402c5003943e203030421004140e1001107050702c500c1d01c19191449010803000205408580051a083c11040d45169000d5084a07e18003048801c90703d0000161008a10300402001078040c14010828040101a0103050220300c030483c14024000030718a2104495807280d1007001d01c00c4480f8903070848411912050888000b0f02250f00c5161018443d20f16015044080e1401074030f03047c50b482c5c200080030304049240005a0b0354640c4412090480c003018010309095039924042e100c212040c0342d0b8040364074418880d03e03a28181041070014850383c01d110701c5000b0160700140900c00c07a0025207044904000b5820004c1c0d1807a040c429480d00044a20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 180663039 1250 180661789 180661813
    0x10050d050a05070b0912010c08130204060513060f06051804091e0302031308010218060703200d030608030304020f1c0203100e0d020a0b04030c0201050903060a060306180b040f03030e 80
    0x4c070180c603403880150350050346001e0440e0301038200c520440440c1e01007507444001c00c0d0b01c13081060f0000b0a1910180000404603210b000050f40644079a1414030640e880700d9007840100280341389040185064109141090715580602e8008040d40084d140036943c2c64a0000a2010614a07190030320110301c0c03204c58005460400039100c0d030180c50745d6000d2071355405000172598014400c07500e020340c852030104030441d400e004201c4240c0c8028026410801062140881c00030101d907603012080e07912008002d00510900060140c520544c00706646401c00d004000140c0c9032a0500e41c4128400c51f0b081981403c1185810140300d074104e0040d405100320188201241c1785070340207000700700f0094101c98000d1005502280d640411080041002c0c0f440380104000900520380360403000e105060190400d03000c000420b1910380c04907005001c46444d00c40800c24002184140760040c19400000c44010340716031581541c1c5c101c0540003c0c44030252406140c01c0c94440d510000d5140502c03815105010050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 180664289 1250 180663039 180663059
    0xa15180b03010501060c0510020a020c09070f08060d02091308190908071502030414010306090c080f06010809030426070314060606031b070c0308131d10050d050a0507 73
    0x1028003406980780400228141e8010300c07000c0d06c025480300c02040700500c5031b041700c806908641b1800d801c0d1f116042e040c422566a003901d071840307952180d40704a0800000d04004080d03541c058081806604090115009a01e0b00301c00d690b4030265010501d51401d800b80b03002240c5110342c14a0700300030000b4503100000d055014840d00210b4096a040f01c07126516404100c66901e200d801500160b88200820403004480001858042c0d0050500191981d96507100c8401c0c2c030700d040328041c0025031640412441ca49000311141c0c00031400e113403001c010b00d000c003240c581c0d0748200e000300c100d102d1070540900f08104c100340b00e0810141c490701c1603c062669924000c0640c2c80914607603000c0e806008002951811b01da810390f072084e045c100c180e045012056031100f0407544896420780701c0700b0400e4404004140100010491000031010003012a46807201780900200041520300b1002c0d5144140030941d039402c17070414140c45048400c812503240c540740440c605400c440000f031860007080000182c0b2018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 180665539 1250 180664289 180664301
    0x90108041214160204050f060d02090a0e060112050f070501021f02070f05011d03180d140a030816020c030a03200a03030b0906060702010207210b0a05061c03080a1518 73
    0x401c3e00c0c18051907c0d2942004401c0e01d046404c66000300b2240c0d48100949800e626080c1c0110b00b1010008000740701580c0d060501009800105030840d6680f849410400b042141c0080d02d01d101e40034144d00350500d40000d4032a44c15600f1405c0445d191800940386021507070456034001d90107040441c81c4419031810740c1c040c0c946134a84080c3c0391903107450b8000d054004401c42d0010b4a03040e01211800342858204280c41105440076580304000e0024281402010001e8000c2d0038060b440e400c0451070480301c800151034004400804540058035010b034291800108104803607414108525894014510340c4241c1143c02180e04003481843c1c2f01e101031680580c040a81c00c9000d541500c0c280d65110b0a0203814842c0c80c00080c01a804181d041102110840b20400c0080403070300510b50810481d264406200b40c02c1e544102c045039102c0034410146800300114818400e80c0c41c411482c072603192806803030312200425401c40d49842d00e84e0030810001003031010001e4400c80c03c2d0390b0040624005a4401409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 180666789 1250 180665539 180665543
    0x32030a2d050c03191a0414010c020f0d0906090b09010e060d0b0a09051501080c0d060303080105090906010b0a03021c0608010203040c05040e07180f11030a0c0509010804121416 77
    0x34488003051203c1c2110080c01ca645e030070000c0b0b021060341e031070200f0001400c0104143c8131000c11600700000d02d402801001244400e40e401800005500d040f00c41c2842c15040c0a40c040c0f061500e0104841c6421011000445101808c156284d038022001651003500059405038000300000b1402080e24803940202c034848400e490000300c041d103400c0c803003044a6043d1000c2184110114980109622400c442644400409001e80c14501d440c0200002e480301030b04102c002c00c40703900041c4002d0034010700035139001c2454001841c5a514142d44815203205202a0500305500007401c0c494200b06081e4450011746600800c00001d0360b903401560003508190b804507542091882c0008141c50705026103100e80390841c020340318940c0380040e444001c07840d03118034000e00d589800c031568a24039035108c2c0140d080c02c0001450b50340d1811120941c1190381d0b42003124107124091002010690344040740c250b0003a8080c110b4498440005420b403801500c14507048480c25001a48810403080d402c0803100c454 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 180668039 1250 180666789 180666793
    0x3090a0218040c0905070c060209030a06110a11060c0a0f05090d2a030203030a2a0c170703050a02060a180f06020f07050303070f08070c32030a2d050c03 67
    0x6403039454030800d0340c101b600c0c2000080c030903403184000700f81c0c161300a04821030300508882d01c41003e030b540e000a9404070700002c0242140415828007030794202d01290382e400c40d100c000e07240754a00000d40f074590780102c1810000b00308090740400911800b031411243d003c40018070070001c0028a00e410070019401c1c8202064810810b84c04400a140c80c041110607031794000c01560814895050890340c10050039851201207100d69000610052000f040703843c014001d0340001141c82c2400100d404000c0180f02c045002d038081c10041010900108142ca842541103800c142d44030309e10502100d1040100342100709070000c2d500000f500c0159a19440210746d4980c081e2007081c2d0b0302056403612401c4078441c894068000f04040d10016424160442d05c0c148582034050a0071290348402100300190b821208a41e00f03d40b8401002604042c42075503400c0c10000c0d070708410311622002c03944410103440300405081840c4003414043e0032507501400346070010540400f141c038150400316a41c40602940034024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 180669289 1250 180668039 180668063
    0xd0f0c090f05071e02100c0e1e09060a0311041107080c15010603020f040e06030102120103110418030507021002030c1b04050a02030105060703110123040b06120a020603090a021804 79
    0x5542e0600c0346503511115000b0b1b220485448120030b02a103e00f050800c10000d00116000b420398800e06a183d1044010075680d0506003e40e042c407002c408085c142d00e100e0741c02600c04000241c4220401d03c1d01520984003c0b034892823091040c1c900c1e0290040042c091900032445016000000407030718800c001c44080c41900f641d80c0d031030a800b24860010800c8111100b0801407007270910b0301d1500340e003004000d80010b00c0e040c004040f2042d821400c1c0c01c10ac0d00c80000100280103440c3c0303406216280c503050040040041016a4064032510034000003d010344206070504001f140240700350f5402500541c20b031019038101c0b5040302425000d110f01700b440b5515000c08500004298400d890603194040c00321850700080341ca003640c8400203404811055034035000590000030340b0041b10b0001e941050760306503a506246c50b182c12011340050005001d440044101d0005130b000240e83d070311080d016110690b42c1d031100c03012107003000b24049011350040f0300d0b14400c07224800e107280c1040c0304034001e107454090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 180670539 1250 180669289 180669317
    0xf1c0204030803331504080703122604020d061506030c03110309191403130602011a0105030106030e120c0303070f0f0807030f0b1210060906050d0f0c090f0507 70
    0x4a034100c03a242c11301c1051007610502e403428040502e00d82081114075890415654040662501d5840e8000303d0b61007600c540410b01d80b9070013901c0d602201416480c013240980883c1c038a45510784005001910810000210205000243d131180490440c1114048402516520090f0150006030303201000607192103042c0391f00c2500e02c1d0a50b4040c1154001501400304c5082e081003401e079071054243c4180d00200c0044131540d40400040c00e4800806250f814140c1c941203002e42102c1640e401100000700c0720b1f034140d220faa805421641510260300f0001000164a44402d00c0d11604087c44401c000c0700140e05409105c002014502c00d0b02141e03512a403982d40303201d044600c400102c0c003250201d411980462203040c0203420060603010703c078000052814520000428900c3c80c100c0c40aa9504888110b82e6000032600621000d40b914030b400340841464031011814145009001504855410f00b1041c2008003910f07082009020120003400200440b5420000400041d44c003100820514001004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 180671789 1250 180670539 180670591
    0x80a02240105061e032404020304030915050c01020c0c040e0721022b0b07020f030f0c0a0b04030302091f0c02040f06080a05011401090605060f1c0204030803 69
    0x4600c08a120405000703034070708814000160409060780c40300151800c000b9000c00d20340000380d44680110341801103a54030302e00032950600c442104081c02140100b0800000c40c0c1c00034068811100f200d20f0411000d00800811603d50140c21900d80321540005036600c00b0b8240000c0110040c4411a02009070b0105494a15a02c0a5603c19000440314400c610801ca00c00300d02080345140c00070304044450360120080f014070312101400408150b0000444005000146180580c4440302d8001440038800601c00503550740240c071080081e41c034000400c9a4002c5003401300704081c540c4940511401d0906207030180103500003004250213070064005004208142c001c2180c004084d5844669241c042034007404040d006850556180c02d8a800700003600c2c4604000ea86c12944c0200000150814084c0c2c28096155069002c07890b0b141c1480401c0c44559207000444941403020000036030b0360b00c0459a142414480c481c840120b00e03201080000c1408409001180301d01a0007103101044070410311201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 180673039 1250 180671789 180671833
    0x308030a0c0f0c0f030903300306360509070305010c05040b09010c0501091205070201170f0f0a060803070c050108060102060f1501050403080313050d14070303020901050d0603080a02 80
    0x14000440f0a802080881c1811214001ca00d02134504040041d40301e455221001003074040b00a118001e01c402d031907942038aa550901d040301d6070715050080038034000201103000008488090304113070740020b0700185401096100c400c1896503006100615110390440d4036884248010340d115424a0040e0702e516100313100300c505441d101078200e07049c00ca80c18011111070072091400c444941d030f22448071000c03c14241e11403404181e540d4595582e0382e950700c001041d10035420348118a04078107001340681012140f103029805000030100c0c05150b40c6003010700020b802540d00440481c00000b0b448014000403540a40a4400a88404540380c0302c0307000490b55014100c80b00781c100211400401d84401003100103440540c01403420b1410a0340700d440d10071441c0d0060f24500c042e8064002c0c0881009000d003d005407506040c01c0400000c1042c200307222582c4603141000701059400551070a643e806a0141e070700e8151120010805036031203103400030381a840012107130050f10400c4000000710501143d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 180674289 1250 180673039 180673067
    0x5102403030206070f02060f070e0316090f060f080318060d110405010914010807050a020c03120d0b0306071d0d0b09010e0f01020a02070e0c04050909070e01120302190201090801060308030a0c 84
    0x49181c0c0d0f641c081082b01c2125050850075418052010740c080b480c09080400e5001d0301842000040c010b0700b03034450000316034196100020031480c0316420450380301c004c400e0312541c2800040c820b5810001100082c01840303040d954000c81842d20304850b151258103000b81007914406c1c0ca48200c426212175500c8603900f0030041c101e000450314000245614468000fa221180030f50044842d058403101c0000d082c415480d000c414034400200f101c120b00d1005006e00d0008150507405070809040061004104050545458070740580c00b00326148191610101080440d030040001c400070f003011401030b030103040c4c17228035001030f40705880c445c4840c200706100b120304e0051150020103065282881038001140300920041c40242c040c8000211612011403081c070682c2c00314050a0103906250f481000031030180c01c84079585582201010002e41c000035021312841014042001a44030b500c0100c07046501c40c1c0140742c0c59400c0c07400000810120a02840c002c0c1c408440c02c0c801511500300c2151406200124 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 180675539 1250 180674289 180674311
    0x50f04020f010e1f03051b04120314120a020703022a1909180c0f0b030a051513020c011805060103080c0109080406050d0c0c05102403030206070f0206 66
    0xc808003980543c1ca05207150b44040d00f503001200210364a2030f44110b100362080d010984a000f0014140c0b1103031010f04410280c001352906103810418410120808a4401010b200b50b0070041c45251840c0c07004c1e02d00804904107001602c0c0b42400c0a0f0010390040c5070120050711440001c840c586c04110190454103402c0c1c010030003400d0116013004448480c425010030510030220011903184a64011a143d04810505604a0311000d1924280c2940660300800295030448424042c410800c001c80342c00505a45000c00d40f5111403000b8414080e40c0c04905521006000b01d411401189401401001030310400030049401e00c0b4400051244204800800c81d0300709800500004613488045d100c1100b64100001d020141e95030345070305030750060f00441c003c40c0b4040ba1400b03140e0a2400707031444446003442c01c016083d4041c0e9441c1e031f0f40c1036100800b100203916400c0401c07411602d220070300c2035000c0da0300c0e9a412266403070501a40358079007690020000b0b0802c0411540c09400012024041c00500c92 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 180676789 1250 180675539 180675559
    0x118050306220611070b0901060f1403010f06090515011e1b0f0506180102090d060c23040905060121050709120302010c02010b030d09050603060a0305030a12050f0402 73
    0x1410680d58403082d409038400000c000490100d121032040c454601035040c0c4071641c07494035052540001c0070050601002e41c0c1403c5050200e17032070140380c00d0100d803070001c1119054600c00b00000d01402181000102c2c4074948000001c540a680d0066805240005402e6001246400044401c1112001c4100400b100c4d1071031480f08621451269030003000f40359400c0e80300c000d161381740c01e00b20501c2813059071981e220340b0912007a9400046005440c1ca081c000861903c0c841c20040340441900315400390465955000074010300307004005c0383d00d05000102645c1404240c50340e86201d81d400c1805003c0c0910320b005e002490a5005400e902803400501d08980c080340341c0d03d0a03140190800806070800c00c0f81c024400103640f4030300b0f0348503465a8804e40010950b040c94680003400c503691102803500c45e911003003d80b41d17095000325448003514010ba503e11350340e0340c88a005c00c940001980c0300400d41c0c800000d40844140d440343c00601080ca480790244020703103808000302070180041c0d501a40c000e4070f050b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 180678039 1250 180676789 180676801
    0x51f0509270604030c0309090506012f120705010c0509150702130906050703050f06060406050c070f080d08100308040b0a0c0b01080a02180103030806060a0201060807030309050118050306 82
    0xc60081ca4445010081215508000c041d800c0c60001c0e02d00300d010648502c090020582c001d48a02c0c09007101c40f008201a01d0007900080a500c540764403810507803180b0842850000f54090600c3c03038010501e0031200b403045038100e4148254000d00d41600d0035464040210680c912078811160070f80001040c82c22081c07441492201d0070f6000081c1203920184d607900381e80f04502180194060740340203c5000030b86d803402c3e040c080c0a0f00d400030241e045410340310040040558513001900d00745c076050b00c4d1503a100d00b41d241075545404160381040482000c07150000903e080c00081d401c1801409923200089910340c000c200d010407081e400028030042c01800203001005101c0042c000308089172605c81c03104190390711040003110080e00b00d44c04070f800c00180d02040d418918418195a541c0c0c288014240d072458030010700c001c0c405407445204030000520134241c035200350080f102800d46001542c910301d64918000d400488140320320f0380072812028080032080444400f10040b1100030f0045e1001c0e075600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 180679289 1250 180678039 180678061
    0x140105060d12020708070b12160203181203030c0c070f0501020d0507060b040e0c18040803040b0606040306150609090e21070f0803010e06060a020a03080415050a051f0509 75
    0x90420300b007180f09843c40020b4600c02080f80a00a0070510000d940d54520f90040301c1c00e5001c0244294802c80c021182c00c0c692541c0003044401107000030b001c1203441500b400010703950700c003102c1100181d80301c040140400305416500404040201c402110081950350041c02512200340c4512030241e04500d611100d0307240190020014648900d0f0001092100417001030100c1c0c0c140008101c90342d11428107a800303400d2161040c0414840d401c4104040e01e01992816007610009000600100c000800b00d40603482e104103540181d030340035805000d50010100d0a2718001240c0c4240c0001800042c80000c85810074820202a032140d01d01500b18a80501d0309800800e5042d6082035550b14100420b00c080703094030303000c110b0052007a54101da481d450140c420035440e8000e41450b204000820070f201110360009088a00c8a5040c200882c0c19592030804090030351240c4100009141000200100c400580e8805449040d00480e2038001400381c0000456100503070080c5901310300e50f10042220b00100b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 180680539 1250 180679289 180679313
    0x1c0206041101030c030e0a111509060702131e1401050105190e03070b040e271504050a060f09050709110f031305120d1a0a1517070c140105060d 63
    0x4d801c010488800c41c4203240e10740700c0c410a043d102c02c0c1d00280012568a400281a205508a101d015003810100303070001c0c00301c0c855484028450303c03440b03a10b040d54840320b400507042c003585a80803a5000c0704024030303440a0400c1c841441511010b41c0008606036000c0c1c4155281c6001412203040907405a21043d9090102084e085030b040c440c141000815420400c002e001030040200d03510403e0604940c080400c08800d1905800f24605603e1141039410025010200d030f460000c00e90101d4445050042c2406040326005d888203007811348001c1c920641d43c2080d0300c00d505c80c000301d8541c0395607150035400321413010743c8906d1b80401c108203c030101b00110f4040c43e04290181660b8101071100d40c0c4003403400c00800c4d507034102c0100102744200c0c0c00f49607107e540050200c04c0f6040b50088413040004211131241d002d0700108000c02c8000340700d454407c48024100e0800016900c00a0400340702c050400d07031a0031002ca0301e8940c20202100d580c1018040d050040e04d000e08680d650a006a80c0c8100d1165 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 180681789 1250 180680539 180680561
    0xb030304030818190b07030201110702060717040306090b0105031c050406031e022d041d040602070c08061605040e010324020f03070e0d0c051c050307051c020604110103 74
    0xc400c0c41c854006003004c0c0565004101c100362455613003c45103406405d45e103482c50a100182018400207015031100e00c02c5881056108000700000e0101109101d000c0c02543c10140009190803042002c0200a55915050b1070045040741c6070f83c0d860b107068881c21141000c5010005a0500003040468040d81088021140c150364440c54604800b82c0603040f0b8020110401c0c0c0036120003d160000e0003d08900d003581c16050008501e09810306030302420310600c5002e1780741209100c0c4001014454294103491806a001d240700d01e00c06c3e500c040315030b82c40f0001d0b940d60a500960b1130004034128000d5044504540100050301c03543d0f031840c0c80c2e80b402161031280e115a940303050b440c1016031603080e10080a5400710701141d2034507820000801800404825000c0b4002d24aa02070600420075400120003107400031035800c0c0d822580c0c83c03090300041c5042e00c03004099202c0459804200f103000b08140c51890310024000119842c0b0030f200720390f14602a20068222540d0b0b000c5130046500ca5003102078000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 180683039 1250 180681789 180681799
    0x1020304050904060b040b0105030f012105030d05010e150a05061e0403030224040506240303130e0c070b0c030718031a07090b0f090f0301050c0304060b030304030818 73
    0x41c0c0d85001190b2960021201200c059a40b100d614400b440c1070b2140c0301c403000081c80c1c0039066280c641400c01075002c060007108041415412005040030810109407221907101d800e40352181b8031482c3c4000602000e01810098034008000220a82c203564442a00c1e0f0b03200400507103809290a0500c61294402000410140080760505440140000c02000211700c82d6000306040f500605021000000001c001010003c4000074000440c50008040b5046403000c03000c81e144102c0144040b4040c01400c0c4c042d50580808213a07402c100c180050000101c2e9030303501c1e14007450b40c1c41039207442640c401e00c0740c020034000060b004960034800f884d001c3c40d03104030641030000d0a000804c9241140c9108e980c0119a559034048102c90745400c0210459080500c41c200f00c1201ea0070320075042c889019400444071014000f144501240d5a80360310184a01c83c05002000b55082c0001d0203203140d0300444007510380504040c218200c6017800401c82d81160b411011480c10111459403003103a118220a00c10f600c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 180684289 1250 180683039 180683047
    0x315090c040f0e090c010c020a210203010c0504090506031c05031306020f030105100903110d060204030b01090603120206072003190815010206040206091002030f04030302030403210c080306010203 86
    0x103654000702c00780140c624600c406540c0c0c0707440da9040303140c10740300d0b000c0504001d144410b1100580300d0020b14400d9903035180d20f802092044400f0002200c0e00101e010b5415800c00c2d240040980d0003000400aa0380b4038035060020795a01814503582c0c081180484130500c000a8840f09028030520243d90441581c43c200074041d43d43d0f49820082e60400e41035001300010000c0104000d190410300c109840c040d070304101913640d1030340c2c4450031495100502d0034005d0a2500104041007400d504031005181c0c03000281c165541c40306503140c001c1050380000c40f042209401303642c6045000050481c412070803035580d0030140c503441c001148540360070200c4d1500c51005001c45803203801e50309908447c008066850b43c07c245040d28050a00c14011000b543c1990011414000503031203042c2150450304050700c070480c03101800b400880c40d6216460200100c12008240070041607404001801203030301030240c5c01d00e005002c003102181e90ba100a089008503c101114a001036074141c040d542c4400140107903414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 180685539 1250 180684289 180684299
    0x230301060806210102032e1403010f15060f020a050d030b0a0909120e041802040507020f06010608011a040803030402190b130905070903020612040f12050307140315090c04 75
    0x1c1082111030301c2165004001c00071074a9442e8099482050201f50780c8a4582d50000204000001c03030054180f103540c1401007101a80b025006060720300281d0304100407818810007128401382e114010f010009201c82c980482c540d10000c0e031940c000c0c3d000805400581b82d400000d40060041d20341d400e42040010000165051440c4281d010684c056107150442c65100e200080c0310315114500c0510544c501690251005280c900c42c070851235060300d00140e0303601e5940c001d07460b02c154940d185406100d072100120348030ba4480c85103030480d20a0340f8110305003015990030090b2070042d801210714a500a00c00540507140042e5000d20034040c2100780180e076629074009070a280c3c0300743c040840310782481008015200c1d003441070541c0481e40d881e11116a90441c0e00084403442a100c41c00844010540440e003441140068190055031050300d01c00c159a241001601c0ea07003007150004d0100e04175080383c41d8a01302c0013044911428068002458403ca05801c0144100003d0881001801e040c4400f180c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 180686789 1250 180685539 180685579
    0x1802040c030b03010609020c0a031b0b01060f02011802011e181e0801060f06271205010b030f070b0705030903060c070203060c0405010917010b04090c06230301060806 73
    0xc9419030315640400e80912007002d043c00c1d01c00039401002124410082c00008103400700303040100540c0b5150600c20441c04941204810401d4030f805070a54410300c000044880d002a03240034043c040350028800d030b40340961800012040b02d08080d0204800d02e410118100d942035909004001908110584020104000400314069000a01402100c00d13031100c01c481102d118200400c0750340e001b48450340c18504280c2030041540703d4a81485070039a00030319642071a50a80c01c0c88028052031021090362000e0000e1030000c000b44c203403038039482d1800d1004941004a24600300d00030110080409618010701c0e800a6481341b50b040d2804e020502450181c0d0f034007404120301414000300c401e611200c86004150929001411010100500b040108901c4c1d030442403910407200c000f01070803800c17480341001c240076100b400c100962003403401e9410740410801400b080240c1c0c416954030f15244c0045040e015007138a822070300380c03c80c000c1071004014041c42040201c0d842070014188252880030940031003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 180688039 1250 180686789 180686801
    0xa0e0702150916120809040c050d18021c030e090a0608061312020f0d030b01030b06130e0604140a0903021e0d02062202012a0f050706050c10180204 65
    0x204580004254002c2c520b20048443c0260001c1620140c0c00d040e0707640c400600c0d209240300c560007070f9154100ba0f00d107140600142d84822a141e40c0034400010780d10544075010400303500881c80380c0b6020401a000c46184101201100e0749034030703414200307056202004403140700180181d00b21074a620340414440824022140074441701c1010004503034240c40e0284010050b403076131004550000d41c5820300008000b0b4120340c1100103080008000d0785000040b40544440032500790407800000304a5541030340e0200d03039000c8034050003507000745407a00f4080005a620380c144d54030b00b5041c000b000c0381d81920320303030300924440384680110f4000304044030f0446626254119054080d4000303040d1007241d82d030180011540801d0362461040401c00d5440101d518280c0040043e041080f01ea40ca1011191072280043c10380100d041250f400503024640741101d004690800c840030300850f0ba0015900340954140c8440340c5509014080140305050b00c60000d068240950600a01c0441d201025031142e10503a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 180689289 1250 180688039 180688051
    0xf0c0801020c070e0a090c1403210a17061e0d0209070c050613080a2106081b030a0309050d170a05030a050f01080709110c070f0f060503060a0e070215 66
    0x904040d6240c040c3c0310084c003200a00110005007001d00038800542d1048004051b914003800300340e41411800c0120b40780620385c960340c0c004440401050700080c940d400c090442c449041d84d0700030020000e0301040009082c1a82c00305d07007018100f4110018034140a0400b0600340b0058403440d040c901c0c40d00010000501030f1004c1011400006002060000a1181e10384c031981440c20fa480a140b95510001c152007244900020800141c0100403c242c1039503218403104603030700b42489095110301140b501c400200c81d01000b241d2244090501d1402c010640c9100c8a401d5140c0307109031440c0c4000c0c00940c03201403001311000c0062440451f010801080904460405540ca040d128074108614104640c005001d031900c1b00d44210040001c2100000d2500c25074900c0c16010442d0380080000c2c00450007058059007090060580201d82255800c410804a900008900c0c0c050b0766514400e4070507210a60f02d43d41c0029080c903051064502624180390090402d03c1114442c060003803400c10948015600c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 180690539 1250 180689289 180689293
    0x4080301051e090604020d09120509040c020712080c071d060f01030912050c2805120304030c02241c0e031303062403030906030f060605070f0c0801020c 67
    0x14010340c00c02c498014142e0039400b00c50320910440d00001203401900a0003103110f1500014034a004075803542189501e0317a0700c41c3c00c0701000316842c04003405940000940c54012450104200602d901c002400070840782c06110300301c04000389071141d0080c0c3c3d0108487d04198442d50000241c01030120998000c01c29010a910b981400c01104020002c00c812166074105400c2040000108807414022008100701e4140b075943d6280760302c901803d0050a8101d055460304820010700c017416075200c82e0744400c1c4100d064030180015404503204500080c1c0340900006d00c11480580141010742d521483c803900c0340032004100301204103030942940000c1d490039490890810100617030080e4020410803103001400b03541480060303810300f0155401840041c00307241d1280030182d0f6040d806007040f1641c040144d19a01e2640e140d04010701818544d00c02c080003e0310300711000301c0a8515110302d0341955000d58446140921940b00d00c2510007004000342c420503040580000c8104003403000349840705400740 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 180691789 1250 180690539 180690541
    0x91406070303021b1015211b030302011505030109030504030b0c040e07030b040b0108220606080303070203070c06080103080a0f09050604080c0a0b040b0318010f1503052104090e010f0203040803 85
    0xf8a2400f943c141c070507800d21919141d403003486000d03280a00000c0388182001f0b4a120b5410505058580c01c03585007400d411035180860200901d5410340081c10401c054400c115100c1e5951004e00d405c82d010700b0b80140010b1814401440045c82c590007064002801030009405c0a481c0c1d201132801807001e46420000c240d0f611040b4a990410340203200090100f400c04444134680001205c0b82890320000c09100100707129810010481d41c0d600c2240a030100c0c100b22501d80c50f002401030b42d80c3d07014010a0301c0344c0c0a089000030300360b445101440d0680341d02c0320100b801c003003145405889001c3d044070b8030403e00036101e1010a26449510180c0000c0000307800414400e000c80c0140595a50030307401081d0345043c10401801150f44003000c90b07420800e5800346000510b4170f070749198010100a4103070b685007030400621030141001c407032035001524014001d0303c1124158ae6140f6524170701000e210071600505000c10401d41049602c4242c800084100219070a02c015142c2801c9a0040354102d4060030040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 180693039 1250 180691789 180691813
    0x31a1809030d050f0402010210110306040b01030f060e0108060a060308070b1315020406030b06070804290c0717010e0c10050f03011706010807030c12110402030702011a01091406070303021b 83
    0x8051278145c0403159041101103815001040c0500c80100314900880e01d50502c1500f0340d00c01d5100f01010800407000301f05103a01c424103981d49071000e1150598030310030003000c2015803817a032140030304681c0e100710460f2803c80e03160b850303040c2c40c84003c0000b55200c0f511072218000c02c0ba21a0b44903440001c0c0040140d80ba81081d00141c1103885900107140900c034148444000640188100d80c01e44020411000800b40382c001109808814402580c00c050004600c148100f0780005102094070711403883c0f1116074a010030281e00b00d902c171060710902c0ba4031841d4500300b24105680c044004040620740503180c00b44001540700700b40d0082c0d00440340c507802d00390150701c811002d0211a003d005c0103409007a086140d80c45525400b03069005405603c64007103000c404002c04100000c1c0000c0001d0420343d100d140c2410068001c240701d86003480d00e1460743c12614503c2d84160610800d6940800c26903070100c2004003400501d400440341102495401c00c049e208002e078030070300044000d00d00340c002c0460038082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 180694289 1250 180693039 180693043
    0x3120910060302091b091c03080a0b21030c0d020705040e070b030c0f160605070206010e1003030804021206040c080f0601180b0a05090109020406031a1809030d050f04020102 76
    0x400c0d1940c006850801c0c1480140c2c0c8001c03c680c0c00c809280c41d0410f801392081654025031095482c2c0a07800070212031800101c46040c110110024081d07129031a00c0d503140300714a000ea60114403890303889120b0880c081d141038112501c4d1001180f010080340d081a00b41120310b4504000c0d82811000742e4000b800811140c580f80c0241948c44080001401410f4513004401410380005810101c812402042c007042d19044801980c211079041c151060890240d801d2040c000e0109487c00001030154200206004001c0303031255000d20740030f00010281d9465518101e505282c042c0040764861800c4d11545c0ca49081089002c0c02140905016082d284c0b03080c00103458402c81c5101d8111035008013004001075880701008600c500d03030300c075808a002004c4000268042420b1741220741d00c00c840b00004a203012880d030180042d258141c40070004421186c41c901070b4408440d0000f680141c101e00b8040c006242c2c0200c050b003168030141140d003882098441c8000303803841115180001e8280008110a541e41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 180695539 1250 180694289 180694303
    0xa0603060330050a030908071a1302011d040b060d020a09080a020f0d020607021306080708030c100c09030602070b04061103061e0d0506010b1306050c060105190305031209 75
    0x80c00b02c0012182d076148801e05058000c201840a00c0340106250301c040b070180d08039440701d40d40491315a03a200400c1c5000001d0b9400120b104e1003690303c0400083c0b101106c1d05000c072500341c05031124240300b0255484007007a880550030540c2c02503110030304220b950b15401c0203405c11240c1c00c0700250320342240d8400104100025803018040e07511a0645602686409114003031030310054130664210701c424000310b000d0340700e8601c000350071404452903020042d086610000640c2c01c018140c412140c0c0d6820360f241e90b4003a8982c01241900000c404e41c054000a6214013002e04050a0050000da5651200000c03038100c440251202115442000200140343c42014222110003004a042d13050000c0403802c4420300100c00d4103900c04182e04905140d03034440030380024503800004c0301d440d90303102c0360b50959680007a5404150154480d40c0424220b000380242d400c138103072000080590b41c1c60a02040080c00c503903041d00710002508500030003c110b040c0001c01d52151080312078406400e061850a15182c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 180696789 1250 180695539 180695573
    0xa06050604080102071a040b010e04080c06090c010e2706010e130c03230a1a12010b030f010203010e1b070b07031406150d05092d2521020a06030603 65
    0x4813410410002031041c8440c23505403012100342591581d506c4c42e040c0c4007480390800003034132840342000f00710428a0006020303a0b0030000ba40c603450130f08802c0c410302100c00305c0b918101142a02c907000224032010745803440d0354840c405140510110300c4100c04100003200044a83c80341c26200c400600100c0c0d00b5000b0082c564a0100c442e90305450200d000c00000726000e0b00c1400d04a4441428a240c0101905c0141d640e200042c4006003414401319001d00170210540014082c0c010a109620f41541c1882a28120b0310112040140c91392114080c10071900d81c00006203240c40c0a000000110b06071448140c4200d00c240c83c001121013103094a00710030003004100902c07402d2405030119a40720404191404064088408201603c0300c0c010b00c0e007071a80f030341c0c1040100314031000412543d034654444d0108103040d00c010f481000b180c1560f01e0942c2c8014011200d42107a100504001d0f13007900c240031224088040c2e00c00541d481d0907070300140401016078410b400080e140e9000707105100d41744be05290152 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 180698039 1250 180696789 180696833
    0x806010f1d01021f0207050708030901051603050d0f0506130b060d0903030b030f0312101d09031c0e01110c0d0302160c15030506090403090302090a0605060408010207 73
    0xc52008010081e111480c0360103641280c00c1800d1200364000c2145420050f10b510300064408100d0010100039080818150b51511660b000003d040d4000f000f11480711006940340d5140044000100100c0200048110b041200420066100350074034414480c3c84400c40c5004295070504070100720648500640d050301d000e24008481200365548003c950804581040208000010782000e0b402819845092901402030701c500c6103441002200404110b4400e544040d42a143d1044540c4020070602800b140007050120b68042c403d52000351a6020f069401107030318040403101c080c500c0c0008559402e00ca0b61b102c1030074144280013802519005c0c0642d10b05941010b110408483c0d9400641450100f0305500140b800e0300d030001c1181031061a171300700e2000034003503586001c1c040003101040d040e01c00283ca0080840c02c549000d0101e6070189415540b4085024111b8082051045018041400c002d6a0755070001d01c81d00c0d020050401001c0d85400180c41c0c1242d4107003000740c020442011a004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 180699289 1250 180698039 180698057
    0x3121627090c030b270705040806040609080903010c08060a090e12030702010b09090d1b11090a02130f0f060512010b0c07030611090a0f05031917031303080601 70
    0xc00c1020320304116405035034040390707011091800394010042c006031160800035001d10819520030b000003d0780c41100010164525035204002140d0343d0141e80a0100e0b160803d40110b4081b031101e4000008060140b40400e1900290301c00003803c6a00e9840030401040d8004200f100354906004004024454078034184401d49207040c0c4c494444030307c100202181070010001c00c075528800d50200c0b20420010b082040c260074160b41c65640c0d80105a40740e0b0010301d207058889a05c0b801305080742c046070340c800216020704151b50100199010700800c040c038400c2d4240b2041032070361060900d101c001c2583c3c100c0704e8413160900464003600f102541205040c02000c0140203620102c400700541100c010614080d00c60600454090030075002c1d610260030f244c18a09550035094914008002000b0100d80501c1e0299462100c902101410302c1401d40c1340c0c01c81104448040070008a10245901c45c1c000307045402d01101a0000c0e5070419100d99010040d0000c0900030140c000d0030264109400f42007034009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 180700539 1250 180699289 180699347
    0x606030709061d0301060f090506011b03030203041a010b0d0e0a0209010e09070305030d0501080d0306030b072105070507230703020121060b130b0403020a090509031216 74
    0x2081c800351041108100c626141ca07070b110301d24060251810b0034000d0003804203503500e40c000403041c003650107a81c6e403161802000c03c1c5d00b5802030035415030350200c1e00800401c12045071010340007500010b02c25a200101003245541c800d03040d182c40c0c2d0181a903910410b80b120348175a4000c0072900f01d13007444101503000880141c056601e11480604680380d40465002d240d40b628421401c000e4650710003031a5100108071000100d8031078001e541624000f44c121490401c403264100e0a407829484058079044081010900a520505441844c281c0c542c89580012420b04101000c032142200c1710f0001600c007007030040811801c51100e420080f02030402807213141414007916214545448000d040c4160350599078800c0d04540c85407881050007880400423141c0d035501e45803090f0701c50041499442c2c1c00c010080752511803981a141600c1c3c0147c42103603010300340344481e1300829000d80b80501a02c401e019196405c0004501c040c07041e82a11a40d0000c0a0035030000740144079500e501b4109020707400b0742400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 180701789 1250 180700539 180700547
    0x908100b060711060c0f070e060103051006030c0e03070b070b090a0b01060c1406040c0920030a0902120607051c0204060807030b01030605120a05070503010207080706020c030904050109090302010506060307 90
    0xc0c42c2e4101d0200201510410000b981c68421056026018003640d40b90072440302c40810090100d13542800640002d60f14040118210b40301203c0e02c0f4407280045205110051096110240b401810300700543d51010075400203140211551047c1142a00006c10004001498072040e8100407034030000d259800e0749903205175050105001f5030003001807a0420109000400b1040c00e80c003003125050318020304107030804084040c840d01601560505080404441d8003d448010204800f010b078082e045440d80d082d03040107002d0710f04050303030f1048013182c019404400034800d06028042e503403036641e41c0c2c40d2550711016010b030800c103600d0086031050104002540d00002050381c024a42e10b400180d1011020040e801040a034028a400a10410b084000410000352011482e406801126200ca5032141018240e1040c0c24000b4170f000d5050200d1400a07105401600c20840c4480c2900e06000155021600300c0b0b000343c0c01592400e032107460300418550217120319038218009865940c03544c60180300186c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 180703039 1250 180701789 180701797
    0x18020303040e0a09060c020f15061516050d120c03060302010503010e0421200a020a050603180102190f080709050616020d06060f0b03040201021203070c0507060908100b06 75
    0x4461070440c2c0004580a00e15440904c01550245040261106031b1a00958500c1004130b040c03541c3c450200d0404401c20911a80c034803d00c002440302c02e00b03011629081d410303600310444007007212200b0f268900c0024001e000c0d040c06403410341c1d1151080e12481224030180e80c45158070000f4140ba0040c1480540d9000782200d0540c1d6150302100c84607201c0d4a090002e4091241002083d800146c0000d0340240c2d00070f00d0780607100c0001302c1a042640c0c410200c2030310b401500c00d00940c420f04d5081c04100d0750500f03002443c1e0041200c0104a407000f520075000c0c0c04d9070703c50340d8201d40e14580041007100c10358211808062121040c076005480b450817000140011149001d07080c0305980104a241805501030a425882540074200b42e4042e41d0324a464009444c01d8015400c896150308404201c9144a0060b01c1c8200c0d0140d005003500030402c0c204149a0703002400340000c012240c0740203804280104040c4c00144120b607a0760008524080d082420a01001c186800c000d060031405c500075a260300c213072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 180704289 1250 180703039 180703049
    0xc021302030f0f1e04031d04020f040302040b01090e010807030b222d1b0b0a0f0507031b0c090f06030507031101050405120705031509190c0909151802030304 69
    0x1d032604c2c102295851410000b240a004c0c450041008040e400500381c980a91484d83c031000c1c3c8101c050810003680241700d00d180002c0c030140400c00c090300c0c15400940801c041030502c80c0741c0503203401c5180d131281c03402d801010465201c81000c000b0845406807075540f203904006201c500c1d0002d020511135030700080801902d903e4417001c40d0041070040e400b402d50910301590244100d5a02c501c0d0031070302d060500303a141d0110f101500700040d482041104454200c101c6a40e01d01c0c0050044406684580000790154200020700c4c1c80c007168540d40d91404e020032409070020085375072610104406550703c2d0b1310400b01031800c0400400010b8000206081544c0c0e0081c0f04088440070b07540104c41c1ca0289601c12540030b4190040d0410120700800c081007a18001d40a0307652200c80c070004814103030300c1a036110309681e105d03050b000000e4881000541781c2511610030702c00055a900b15100943d400b4000c140c0c1c03220100d9000d444a45258814080038541401620000c80844d40009403203000780d204d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 180705539 1250 180704289 180704311
    0x2030c1f1808190210020102041a03093406091401110c03011d0d080c1c0e0609030405030c030f030304140109050706090503370201031104060c021302030f 68
    0x514080d04106201e600301800107207040750b244074030800364111603041ea100140d014100702816410410702c18001c450944008042c0e180d00c94280c41408022644000c00c01c00075170080c1d001e080011182e164510003000788044100116440301c1443c4007840f196648040b0910001c054104082c40c40c0020b4000c071000242010074110b0381c203500b100e00309241d181803141d1551a107200c8002040c2d2658040307600e1400d44084803440c89000000366462501940c2d44403c503001400040105100c0d10040c00c49079601c2e0704003081d030541a02c07109161407805c0d5003062007078001080a01c80d505040084200c0c400c41200144028244d0a52041d180e2002801c050304c6401102c50511800740e00f500003003101ca070300404481c00780e0782d2400010b18601480c040c89209001f025456545900100300600780c100426046032032045291200024002c4003d500301e05042d2030340c0300040040800742c0608000c0000da00d034040c983e030852040004c0704504a02081c4454818030034003030240011010f459210110b41c031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 180706789 1250 180705539 180705557
    0x120d080c090f041104080706030c020703060c050c060c0315010c02150919030308190b1315030605011503050c280c020d1a06040b01021b0a05060703050702030c1f 71
    0xc10b46000b40260750580050030452404c1600410400810440f45000140c1d8501610b5140403800d03030303103041c3c203200050780030a80901c04202180e1011950302d1036801d145282941c0c46201c0b50501c002200c03a20007107440030040207260102c24040c10094502440c00405501981d40000c1c038560041070456030540c0046502c911580b2403000310f14504580d41807442600f65245402800c0100844181c1c1107881c200050145d02076050080c0b0b20340c1a4010041e0b070010040d001c0310001400e050b1004441c00c00200c0d8000046801441610b010b800380018010380d80900e580c000d0107032013003e01801a400740400605e1040242194025407218518110389a00a85284211070141030fa24002e90310900c0b0480080800c080c0075031100018a054104c01e070940d551000300400c543c0f80001190140e00581000c0f40c4c0c00c601c0079449925244001d025080543d21031000c102580c1100d034040f004240005030840541c07904001c3ca00004400300d95807540d002c16076213801c81281c01c1090b160140a1845 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 180708039 1250 180706789 180706807
    0xc02120d0902210f100e06070f02160306020408060726040804090f0e010c08010501201c0206040308060d020604050918011506080903070c0b0a092102120d080c 70
    0x64410030380c1e1404580700e1844003840310040382c4500c04c008800300310b131044021010142c1d1885c02058160701018001d0542542c882c1415201d0210700350301201180180350741c0c14060007900ca80b180142d805034030016151418030542c185803d03070242c40041808075019650118101c2207032039040c0c146484c000301099454900d4086c9150141c0d030820b000140c141480c2c200004420780c00200d1000d0304100030701c58100c0504055a4892081c0601c070300092409030115820140940001901c00803036045946400440070742403c1c001e01b504043d030068002030240018540d210940e01d4120004407048000b00300d203a0f0016406129900c0f0740e500414000002803070f0000744200c001d0382083c0c1c000c000e028007801c070701c1d03c1c107080c06c000d02901d00401e0311800440c594000000982d614180d2220088187d94204044183c3e150001c0c1400820055a00004591880c642070402004408504011580305092040105181901000100303e901c86018050742c1d680c07044a4940042c01c62081542e116001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 180709289 1250 180708039 180708049
    0x714060a050705070e04050d0903021f020c0a0b1b01020313060c030b090a0219030e060a0e030f0c010c0905010c0b070e1201050f07030b18040201080709030b0a0c02010c02120d0902 79
    0x400c070190040c050500c0004245d003000301200c3c80b41e81b04005641604504540584070403030305d8000030f500080951804900381c540758032400d200d1a1140101c0300c07a42c07402c00001e810550540c01c0070010b2035011907011020010140b901301100c8803034009606501c2c0001c010a00f4404990025042c00d403241d441c3d00b0128004d5110300c0c1c1c0c2c1400902141c42c9841c0140450001c1d6000c3c00c002030083c4d040301c040041d094400d1143d404110440800b6010b00d4a03129001c01c094441491041c0304c9010400c0b514503110ba061004021142c02e03400046030450034410701038840b6043d076018a040c020030882140000d40703c0320005500014508000c1c1c1854003e60126400d5400d80103100480c1d8600401d0159001005c0b003614031403540c41c3d42c14400512440c09011a5141a0002080724038141e40410015070084880755480a56032804001040d070704d07220b004040d8000c0e0b071004da450344c0e0b8000d10360080d0713428042c00e55034441d40c0c00244100e200302d07102e00c0e19030710415000d0100d459032070f09140210758035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 180710539 1250 180709289 180709297
    0x60612050c010c3e010c0b040f05190c05030c0d031205090316080301030b060103200a05090d1103060109060b0d020d0f05010b0307030e0115050d0c09180606080714060a05 75
    0x1000000344040b61080b5100e40003880064280034207504c810101e40d00640c410201129025840122a00f003502c441c0d54071029072800e80300c00c540c030380100090740c0b0701c600e024410344a0031070041c0c0041c0c002c285407005041c204026548000c0c000e100600348240030030b8004240303561543c200300700040c580c0e50740f440039421400b0399200d0803488941c1410341000d11001401a505072030091200c10050b4071510015400c64070b00c0100e4009403150703031040f9200541c2e900060b025080003410081d2600e4000000141c4010007414110342d49040e030155030201d03040030480d01c1d01402d0265001c2103207a04260216509008502101d0215a000107055141c1042a000300314209842e50040c4450f5850743d0012050717070800c66004000a241c40400881c50780140a003400500d0030301d4212200c03501304401d100020910742c40654650070581c400148030300c0300784101c44014440141008814031149805002c0e01d1203a840443d030b5031b100c3c04003840b0a0b40611950307006040c0468116070340c1c41c0101425151402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 180711789 1250 180710539 180710573
    0xf01180512010e151003080f071a0420010e1e0a060905120703030507020d060e0a050d020f0f0606010818030406030b2b0303051003060f09060612050c010c 68
    0x2018a000d1129581c054015940103401c40341603031a02000728965480c10341085400c4400021080300410104094400070141102c415400c240b800c89192142140440c500001c00c8139119024100000d110920f610f8541d00d40800a40c11009210500001c2000031070800c298071801c0100f040c1511041c1c95031061031f81e010050300e420b4066a441c00c000e00034000a01c5201d00a82c030400300d50710038500204207081980d5040d1103e074101125a000d00680c202d02150071190603644d0208100400e00c200000550700d0310410080040aa5482000342029110301e01004658000400c458104002041e025400002840c01035aa0381c1c8820034582009104081c0309464040041d0124140ea071540011035607400640304910000f040351a0540034118242101c07421856038204100003905c2a0850740d0490400815542d0132622500c0710000c480d024000c80504681c1d606042c0c041152a00451000300380420002002c40e05584690740c54107178a0750241c0c10004518506801c00560440c420203840b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 180713039 1250 180711789 180711799
    0x12030c0c11062a0d0201140415110d020c060103050d05091302030a0b060a0c1b0e06040f020f042d05090403030f090b0903031801111608040302030303070804140106050f011805 77
    0xb400d40403540300c0319583c3c2c604d0015400c203008482c54030944c43c45d10340100e41c010343d4402410103a0120800500800c01d49400c05941003106102e1565a4009003819060520140007654914a021803511741c9130004c4005002c418442e03021035548a940101080c40c141c0f10160b0b40350745a03480140104032484c1c0b044d5002c40c2c040741c400e0365113a1091043d04500c1c80703103107a0000d10803442000b06d40b11859115402514003500b000600d2420140c0000c0440c121000d030242c2040d03224081340c4403d81003a00480f4040c000b00700901e60440001c401440680f80340c02c4100300c102c0c1441c003c01c4002d14003e0001c1e040c95219006a9034640a81d0700190007150010751142c6c05041501c240e0781c499006031640d0004211400105803940f0040c426131005079903201c4a10319100c40d141042e407805460300e906680701d81d000d200010141e1010310041d807103507400c0e46e5a0031013841c00f4501049106590360858480c1d81c5030080038041c685581400511301082402c0050507445034111140c00402c45401c225000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 180714289 1250 180713039 180713107
    0x504061a090a09063b040204090201022109041505010503041709060a0305180d0e12100203010b0403030f02010b061804020c0709051006080c04031b0b040312030c0c1106 74
    0x1c02801600311040d22564518000940e114040020421501d11a1460514401740803a00601c0c0580c00f443d1401e1060060301c2105c502c41c0440c2450280000e201c00051000040c070140c03610b011300ca14002e01204031a80701e1950305040c0000c044d400014802000546d455900050101c031940c00d4034031041000703042e20b40e51003081d040200075110031348046503040160098050075160201d2148280b055030391701ca55103404080308100c01d8403500714840041c2e00940c03e0022019200d80011030103800655021075aa41c13070b6150081c5003000304d60001c0704592501450800f01c2d5200d8080365000c8103000c1c11407842e07000c0040094000d2003202e0b0400c800d4030640c240042c114030f280e0450380c494403201a54a0741140d40d0403050790303401000c45181c3c03400b80c0c1c100000d20000710341d9030105240e1080300c070325501000d07203902d03c0043c2130b031254000f40c071038002a030340c10031070b10354140110026080540791000c0e0710a9160740340144556081c090341e205170004607014444104080000f0008000c0480c07140304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 180715539 1250 180714289 180714299
    0x20f03070309150302091305070c0c080a03020c09010b0a08070302042706050f0901050603040503130b0405040c050c0a0f11040c030506030601170d0e0103090f0b100504061a090a0906 80
    0x54861907100d043c18445020100b40600c038001c5c0300360b5580302005008202c1c0380c1000c81d43c4c0001000014444801c1c0040d01a041000c40c0c2544c6801d00030703200c8034000301030004440c00c019203810044184035216619500060040300f0000c002c1d21406001801e00014580300c0c41020740c0a80140d0700000c054110f107588029541c4084043d8600000c4445001c1000ca503c950030301503035801c500d00b01c5400c0015440100405d05281000303560060003102502c1c10114122072002841209500c408001d0101150a020600d02446001101c0d080d80c100b051030b010030b402131542c485260150103400c040e56002010306103d0800444007400304010403c100f40104c0301c8014000348000c0d16a02d0080c8610300020030b840c54100d0060782c0c0107292100400d000f18101e00308403120219000114101501c50004100007420700702c0f40e0b24050f200e440300700c4032860300d0400e4a0b95021643d11051045003001782c100866000301d107114001031808414242e0b00d8800c4008224001c1007944003d070a24640f80000170 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 180716789 1250 180715539 180715547
    0x4020a0506030a050609010f060e0603150603161101020405090f13060e0d1101060302030316110a030f0308090105040b06100504080f010c09090504080d0b040b10030f0b06071a0601020f030703 84
    0xc170504007100e44da840399072601440c01d07400c04240162030128016919810040c5000e0b40699484088914102c0e4210080000f2a08503002561121504d801820340c2809080d00008a090704c8411540214142490440010543d20014000000390407220011900070425a40900c20841d003045060000c02d41c0e11034095610b001c11401400014240c80e844403c42e94180204d0b812203030010300460401383c200043c0c902d280d4892004031400100548000b06d5601e8519840c4000c6014031400c60080400c0e003405002803500030140940c50f4586420400040c61007002c3d19005402039650a01e45100d0b0001600c842c4100c0d046030880307105d440c0703000004180c15005078881c02803075605c1901090703403425000141c034000d850040001c94103121407100050540d00c940400103005002144241028010908024040c07440783c00080c0c07607000400354201580544466100107540c42c901c0d1201940324115400c10181c202c0040480140210b000d5038401c01418203504090f40580b580c861040c94090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 180718039 1250 180716789 180716791
    0x237061e0c1d04090c1406040815010e0606030f073b010f0518010311040504020d0e07060c0b04110301060b120f06010c031205072a061a1804020a0506030a05 69
    0x4220402e940b058400c0350f0810740580445590711200509116013003882980301a1411170202d0380269081c000014420340402085070980c0c21620301480650403c04921941c800042a442c000c540820034031444080215001f40d02403001e10340046900340040c84aa200c0c0000900648031140051150802d9000195040620f1900f41c03100c40303020303ca0f28000d407094001d40d0089124040e0040d4002d11030f5019401488003a41e01c41a00d51a181e00d8400090072030708182034130b411180e07980c5800a8081010800d07100507092606020449180645d00c14000880045c0010560071200f44030f4105034900750440d00141c51045403103910760117030b003820200880781103c0c034956905820011613040c0d406803401002081e01a566250300f0406040c0c1e0801808018104004111000100141208411080309078003e0085103401170207905017454419200865840e03032015045070620200d076078680c2002080e4003540700d4018010740d01c03800021211100c42c0d0005401c030b2000410081c400c0c032168401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 180719289 1250 180718039 180718067
    0x21030b22020d0c170f09060f0901060e090102030405011d0703020402090409060501080d09140a030303051005061801081620030c120a0f080127060503030a0237061e0c 73
    0x3058541e445244506aaa0742078400585940041c7c012030a44a00e503034000d544184090008140300f9500e0000880c80c6000701c0d580c0c40b00d65408024001000350a000e0501c041c03184002003101ea070103031408581c84542901c0024420b9500080d80c60b4241c4076600304102d503036044032082103150f82d580d8142d078444005580034400200948070204400c004c40300754941400000d0004130071542540e806a0084c40040e00070404810402800a00703580d40e0f078010010101c0000c0200300446604001508446025141000102407209a903015a50201a2a068400048140e4518907001c41c03918190311441522480500510040004518540e0024080b401c10f907560000c015030040c004a031110b6080c024146003410700c038025100904290312900710b50410401c0041c4050381c2c0d100191955201c000a400980c0080401000780c0c19101c0d85003040004402684855050b0a80c010641c0c130f44d1580003d041e44d903100180b03000c08201130181010603600270300c100526070035070001606003d103d10741 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 180720539 1250 180719289 180719327
    0x3060302090c0f0a0f0c050601060513060203161e0b010603090c0806060d080915040f031b06170408040b0c0609101406150f0721030b22020d0c 63
    0x128082c1c0d000c0004450701400109203680c201401c030182211400d901d002c0c82800c0085880390840800c60a2050a00800c00ca03191369a03120a5510b0300340768516168041c0096400500402e403451945402c00c0c2c0d80c241c0e02c8180040d902006a4040c41e690f00b09800c00f802030b070820400820200e8165010f1014180190241d00010f42d981242658402007204c0d040d401060314021a00000c2111025080c9604024059056110000c142e107249412940c002861581c4461040090004d15040c010040202120341440f1a0038080c0181004602143c0d080c103507564000040d0901c0b955100303440151095003001682c0d1b24244015550b90705081c0d5180115004032065521a5030301c03442084100d102d4203120009581d10b902c2005000030155141c108001c2c4100b207841d084649135002450124440c9400800141d64a451403420301c1d55100340405240c0341489003802580c50407044403091010604401e0051090041c1b41d000e8054105201c1c2400c0c24251442085500100d000c0210310391852 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 180721789 1250 180720539 180720541
    0x21050703060b090f0f060f0d051909030f0c0c050d0f030f0f09030209090705040e0a0318030c0b1305040c020d0e0d0c030213020c0703060c08060a0b0405010e0a150306030209 76
    0x15000c60396114907203030f550f030081e5a41001d55103428a440c1003050500000d20507820024544840d010682c084154595103543d80e80822030000356880402100b60000041040142c0300741e54041c02e0080109064414083c1850502080110030000000035140180a001c2e244056142a581e00c114036802100800d51030b07481e6440d00c920401a9052071216980d411212070f2544d02030115002c405803120500c0e0142c198007040c19221030003004a00300c3c42200520008429040040010402281c0d414500d2401d00040002c90706880c42c2500ba2003554441c80e039681c0c6010300c06a0300102541c01903401a0925071000030303031500401c240791421195190116172070048001c0004901151000600c0c440a98006001504003091071100d002503a100041ca02442503070034a00c0c003119640100c5901d0345038190803983c2a84011400d410590554882c16900e0914107030701518066805460f0400003c00b110b2469692078550110042030108010b1650f48412341004000e4040350000340d01406d0440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 180723039 1250 180721789 180721799
    0x150a241d07020d14070c06050319110306040e010b092505040b0403261303060b030303190b030703020d05010c0807020312061c0203010c1d032107032105070306 70
    0x1001040c41407659034081c0400d9075425005645a030710005825144120a02c41c4500081040c0340c00000b8010315100d440d141d19001d54002c100d4400144c0748a2290f041044a10169942c0c00541e83c215408a0700403803595140c40701175005129541402d5808140b00b4284407014198041124102c852011071001d00b00b1100f0003a103551059125011150408120800110b00720005a4070081c440d200b5030191111002441d140a81082d44000c0030190540c03401c00c1041090310821507800009d4018504624180e041420118202c081610416880301021151668107000c401d01443d8001c12012018090b030404500800340413000c84081030b044008150901d000005913040c03603480700c20151040e510f000501c03851503ca00c10700300940110f0600b01e00169420700413a03200c403902d6669102060b4840300201c440102d80003281d8000d801082038000000c003580014030340200b440322031300e82d034100e14581101c10900d00244d50803250040c810b010665070b42604100d0142c0c0981c2d8061020039150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 180724289 1250 180723039 180723089
    0x304060b120c090c030a020903060711010c030b2404080102221d0705130902070f02030114010b07081e0a08090c0402030c0a030f0603060c09230102150a24 68
    0x440c03240d520a0001c40041d40c001c030138100030b51b071050783c10354094141030100c00401d241500555101000c103010400c5800d8010f02442030729003600d1b0138541400010031080103e29020940742c40c400100540c50f5200c00c1c520101c1c0308540041004e40001c655420541007580107400354440210a43d10040c20001800904540082d1140d40450000141c90b180c1c10010b4400c3d600c140b62040e40e040241d280000c10724282d2002d03004040c00350401580c0c104081c8109802c42c1e884140103000b00040e000184100d21600c1c0580b16131a0340020040e540e40004003102c008800700512002900c0d40010300341a9555103c0440b90145080d50121110000200b00704000e9000458441c0500c640074415074030700321312940141c4400b80c100c407400034580c0d0b16500c0729015100c460000501107100f106041200300078100503581403498070075031034400e0920700e00003e45070328080e2000b0ba41c402034000850302c0e5281301e0f440010000c4a01c0c0000c4d505440c010105100c51802d0310034900003802c2020801d443c4002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 180725539 1250 180724289 180724303
    0x1d060a06090f02070210080a150f080d0903030207050402161b0512010c081b16080307020c060414010819050403080712020304030c02090c120108070807050a0b041a0f0304060b12 78
    0x10040c2100586d01d00480b0450b40c9050081c02d00c00ca40b0348808900100c0c03000314034001c01911030306120551250400c107840b450a10528900010445880310030004a5800f00b012401d480d022a009a079074028803c45407502c403c40e1034050b002c8060030104540c0043d04140c034030215030040d9810445040140d0200307080303420920b640740120f0003800018448074a211079504440f414000c40ba814101816501c5035590903410049030380100c00014004015010007940d01c080c070040380e0030340c40c00c2d080c01c2e1500079910b20b486400341407040e1600070800014821141c45464294800100114500785c00c004155a500351141c1e008141001c000ca01951000d0007102e2103141c05840700000407215a0074041030010042001d1204501403083c0807070011819050341c0206005d000910865040c807034a103040c40d4007039005d2441840e6641082200c084007100f40c9045840400c03c0c400110003042100d8218840e0b90103410f0680c10000130041000300d150301c03000480d0016500c1c0f0300210110352007255940c071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 180726789 1250 180725539 180725543
    0x170309010e0a18091a10030c050a0501020a080c030c1504060612081e0c0d110c01080108060c03070e0409031d030303130602071e05102d1d060a06090f0207 68
    0x402e0b8911440314000c0c503000704c40030f1441107801c04181c1c0154410200401c1c1d0503102d41c500f08400701405c0007884041041030f409400b007210000c54103072500c40082c1d07a41d03483c81d5004200800101e50400c4880f010300c1941c0d00e44401000b500c4420001c116500460340084404468551410b1800304c1c02004205144e1041b951000c0014501a8001c10728029410307500c14075502210704108100d403011080c480c0b0000f9403200d443c0e40c230b2141003801c09181890070b40025213040100ea10010007009070f0001c6c4850700449559034403031796030311803040840381e03600c001c1703035183d082030a0190032810158030040804450b0041035a0f42e525070041c004050700d134401500c19502c1100241c81d40404205a6401003412610170540040c8500c1d5890a043c14003d100b2803c0c0e8594015030303c08440c2c06010301482c41c03141102c036049a1a561008032002c08244080c03855004245e440d95407218111880d000c44c0702d4038200504039801445c0040d0f8a00140820303000700d0075001d0400300f43e01450003c030b00075076004035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 180728039 1250 180726789 180726809
    0x3090f14130f090606090b01020c0d02010512070c06140a1b050f090103090b07110607020a021e0d1a181b060f1306021b01020a020907050c07170309010e0a 68
    0x1441c010301500300068100e0019075100b003003d001810a215110007018007003130209494010320006410700c6408000140103c44200c03240d00140c1c2e200080303842c0c822070b0000c0d00da07142c3c032111021610350480c204c00620710703441c04042090260340c16510b01d2003120070000c07e00c120203c040f0349000c071580c40384808022074006c1c0b0605004001c0400640007039201803500050221564441440c03e10b41603440c40d0200d078500a803146104c40a00c035050340030940b030004000d03640059000c00e40000ba8010192aa680720743c1d03c0184d10b542d6140d60494681d0030071845200134049880140c1312030f01c181d800702c5225003c01c01c6c4040d41c0502247d402c40048003204501554140001401000d5010402100b2600800c20281c8040090040f0700b0001c1c1000b07500500c0714000307135102c2c9848030b80d429403c0d5056501074001c40006030784200d000c5d544a461403030300649031b00003034600903d80f080035000201c580c5440115091103000002c054065082e01341d84a50b03003403401c503091000909140c000c0300107107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 180729289 1250 180728039 180728059
    0x9030715020a0e0a1206150311060306010e1305090601051801140607080f09090a0203060d02010c0602130303020c090109020a0c1e02090f0402120609030a12060509010303090f14 78
    0x204600d54068401c42010b0300741150741c12562000218950341c50b401c0740003402c0d0001071620521129100380007002e80e004030401c4500c1e04540702c0c500342030600001d1314821a00000000c0d4280d21a115003000b10307201600c000c4031043e10a21120141c00708440c8203074a44a6000006101d143c602480c20b4218010086c0c41d010ba420900289803c41402650540000e401c0005038005445d4100500e00300e201c01d500503071a40a07160802045802c0a40788641990051080c04070651303620095100460b42420180b10340d445510f044000b84c012a00030791684492000000141500403071100d28800d4215240034036a81c07906088422400f4000f0350600055021000340c00081c01522034103e900703220b56200e207441116900141d0800c0d0122070100c800c0140d02c0611046041c28460105142d81d60320140429142c030500a80e40c0303028800d0781204003d9880382e21054a100d542c072481c05040082c107082c0d4550386074103014007880d066210f10021241c03107800000b0b071824081e24516007040000d0008490b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 180730539 1250 180729289 180729323
    0x11b0905010809070305060106020d0905041a0402070f14010b09061801151202030c071a0f0a090c0b12060108180a030507081b0c0102010c02010212040602250308010509090307 77
    0x81e0070b10091114416124080d808404210200b220030300901d450790050030100314051004051400d5a840b0300d01a0741480c440e00b40c0050020050048044155801611656a801d09045242500e0005081d0541c08070752002c0c11074040d0401c2620880640360341c07038191150b40500c40b0030303480a00018481a502c2c070040c0301b6074581d1900c03040003034100e14108800c903044403a00e0341282d0040c2c5484108003000a541020006174a14034050039007044034100d9036140a55800c0d00101004004d510080c1da2000e20b441042a51103c100103011441090342d129144c0c04c5519400e000166103190129401000040050051780e20510341802c04001406221200da602510940c110040440e12400c00340706007020001c01d07144841010401400038100a0745100000e82121800024042164010007494002e00f0140d5036003074226078440401a566140c4107414103024010000421961240c03808440a050b070010380103059840447d440003080e107a403030b56103550380b04010703006103602001194070300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 180731789 1250 180730539 180730547
    0x29090412111e010902010806011d21010905010527030f0a03060806070215071d060d0912091e050d0308040204060f03080d0b060903071202040908160302011b090501 72
    0x7095500c00003100e00d04008031100520340b40c0d03250510200c0341c1d1340d82021000c1d0f6900c040e00c0d80d0002e10a00300001e207024400007858105440d0a2040d024102941510b072502d00c1c0030817042c0001a805000300140d001c4c618110380601010f886040403031000300c241c03410003012110703414407800c81400114078091100e480d000e1190846070400d4145070b90b0b40b000107031100042c0801d901c6221213501400000d11000d20910204402070450390400007544c00000c070a1091345400244840204d59850710360701d003100c0420240031040e40040151103001d804404494008801e84280c8030b51003140710740070022103038074034100d0390301e1140385e43c0055480b40400200b4001c800c1c0da900301d0300150000c50704a44524600008600d6076000f191700c424000380c0651805075900c60910030310000c40b81300c2e185c02c01c0400000e03030301c400c2c80c01408031080070401070790119503035640f01e1402e059000140030f0300c80c071407111915541641124154055400c0642c00441c55041c40c201c284a01403588640d0031050400380112 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 180733039 1250 180731789 180731807
    0x406020d030b04091e0201030c180302010503040813060503160f05040302040b0a051e0a050306010303020a150e01060605090111060606040b0c0309210f160e06011229090412 76
    0x30f81c00603940d0b9078020109000802d0f000480e43c802c41d00c050010818400103080f101900100c10800c10000e0010b04800e51312803141044a4092034815220384807418407841078031070800b2040500701070301000203c2c80e400c11b0181d4460034403003043cac0c00b00a9500d1400c2d115148620f05040015200b00400c0c0700524040d03014a140c07080207044020440e4540c0040b4560088072503141551034481030240c00e141c0360400c44a8060078095020301035130b5145650296503541c45450003404800060b03031310f050b05000c5501a10041c0c100400078000c065035903001030181c0c0e00002c402c1d400184248020900000001882401004041c2a103880d180c0307480101102c603000410381034406d0004015861490b85d400c4000c2e01d4050400345010038854400c0e802c00c1c94010305030300b079541a801c11181a0080e0801c00d2100c2c048a44101c0c00f0141a80e1ba000100c82400710350492070000c80c42d00f60312000b804001c0210701c000320b408c6041c0b40c403580764200820030100b0044500810710311104442230012841b605400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 180734289 1250 180733039 180733061
    0x108100807050409060f06090204050f03030702090f0414070b0415020c130b01020c030a0b010f12030c06150e09070303030b0102030702240f0c010504020102071d1305070906080c0301050604020406020d03 89
    0x50400c51b012404025142c05a011407299600820280050b01d030040020b01d580900310021450182d05074041002c80030000d01242c9162014000201400000868040000210f00a403000301d6205c4052680c250820f000f18102280c502945220090000440e440704550080c00d1002c616400040e4102078107400300313418110f00914880e207099450400121b0320080c41640721201542c1400c60600703030600143d100002c1204c1962089002c41c0d0403240954440d41c200c68045126101408140c0e020100eaa020811201100e01040329007040400c942040d20301c20f543c1880007449080049030740f4000e09002a50104a00b0910112504d51108061150300c0c0b0190690805441c0c0c41c0c281c2180d04221002c4e10142d4448003000115a03040c0f1107800605444417101080e210b0120300d40e1503031500105a0030784521800918800d2040030401440108002e000900405403140003240d20b900f13003401c05034040c0d0300b800c010900500d468002d44043d90f80eaa801032103645020740003100038121030004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 180735539 1250 180734289 180734291
    0x303081303022409010f020702060715110a020105040209060102070503030409051923160903080c3414103b010f030b0a060509131406010810080705040906 68
    0x4081014081c2c411000f0143e03c0c150f4100c80c035282c8802c4841c29160400b4644514510411201006950362000c0e242d040740c000c019010380d51f0208010800900c1c8ac0d00c0075142d019800f00c0c2181c5a90307415000240709034800e80c0e400d2030a032541001640e850005000b4140c1c1500240018003003801103600460b409803850484502a0564a40344400c480720030011041140240c2076010005901c0310031180c0100186030100504540c03180c000b03011908900000707085840006628440c40c1003001081d40c0380c005000030082d8440000414044412062444202200e000d200041c0601c020000851501805010070500300100b107411203d040c51364034100c04c84140c803400400c082c644188200701c40e00c501d07621000031040e803d00140031120f482c88840d0401d410145460301035200d0a0741c0c00300312411410880d4a483c3c44100040109044002e004c0c8031074501216070340f40e2413511100500404003038030384444c651070b2401c0c1c40c18203062502403c0b84a034001c2c001000242403a9108000480c0100c2e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 180736789 1250 180735539 180735553
    0x11107030609080c070f0503070306020f07020a06180509060603160c080a03020304060e0a02030a12022b0906020a0c210602030f010509010f0302010c060b010e1003020301180501030308130302 84
    0xc0c494003110381c0e18200f96144075012940030340d44041001240007529084d0951103042c0e18284c0001c0e9075155034080184441d801094003000c030519030f410380e0340c03003036000306000c90711038440c50010100d44119104441c264812100002d2134140344621340d00520b405410186155102070030828508541e4000d031040245440102010074220405070100c2c840c1550050307540d00b000d003400004d451a14031115996041443c407040169800101000c0450b4040518024a81d400c03400740d06000311248000f004c42d01c0b2083c1c880d00a0010240710761501c4aa44038082110345643c022603490a008400a00342e43d4010018000120764282d80328100c00920900e00041460341d41c0c50050780c1040e1040c090b03284540e001400303203290080c5ca490142c10041421569a49140c000a080c1e01802c04007070310303013603880240c000340fa4841c5140040307080010341075050000b51080000c00952092045201c0000007135100180380e40d10b402403e040f2a01a43c407070f0074540306d42607400e5465032007943c02c4042d84a281 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 180738039 1250 180736789 180736793
    0x30a110f061206040b09010b07170405030708010209120a2303040510020a03090605030912030a060306060b0304062403110f04050115080c1213050106030204050c03071701050603010501110703 84
    0x2401402c12200490b180c0000c1d08101052005507801103280e039100d007040b03800611079824542c05540000340c00a06680c000121840083d11501c80d681200d50140220800032848800540041040c000c0544410300b010551007060740e1201c80002004103160140741c02000c21101450388040b5206907038083da89055070300c0000606022010450a0268018030420828550040e00410080c1441e042461452a10354a0182c4518442080c1d40b14054044085a040211a4014005540d2160040112a07207078851610700341c10494044817801c5c1414030180d0b802451440c3c1650790400752050a0fa04c0b0706590358190711000c020701254000c03c0100c00102d107551a8081c0b10b00908442d1042992560410401008024014019102d01e0b03010080203600100580080e9403011041003c840c1007a01441c01074007401c01a84060f5000382483d05002004407644021400307001c50b91030b1040745425000824400407800d2040982c06030082c001000300794007a408034080740340e0300300030342e00a540c4035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 180739289 1250 180738039 180738049
    0x30518040e150c18120f1009020906040c080619050907082502281a07200c1012020307050418090b011a0d090f020f09091b01030f1a01021209030a110f 66
    0x140032030316059111440230080d03013407036500d254100000790381c2401060700c000c8001d4800d90024003040d02a20b42c5940060f0038208807800b10003d4a80180008000c0c10607200081082c02c3c2076a0007102d40b201c013121540d804000c68079044144207141c01401c4001b8203d0107040198014041010104944582c48170002d091810f404001003806181e01540e401e1041b40209000760290315035820740300c0088944581c01000500c2040030308102d0300d10310602004201102c44100480b041c2c41d455001105100c08590084050010740d2980b000604035400d0b540030030b60540da061600030b0205a481801405105401d03c081011480c007103040b28135081e040340c500c00841e070905005844581e040410001145091580110080c008131861845804d2850400b625481c1c0b07044000d40381030044101803416402600309605203090402c0070440c03581c03a107110781107501a4420090040c00703900c000c1c00c103010903282907412056000e401045110550360780c0c402c0701101c40443d10703480380c259840540d940d0340b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 180740539 1250 180739289 180739303
    0xd08060d1e0606030501050106050f0d090f02030d050a032706050c09030d03050901141b09270907270207050c06030709030b06100c030518040e150c18120f 68
    0xb2940300010804d00e50300700203084401c1a00014204141000790b1203082c1d003000d00f03465684003800d10004640500e45402001c2100c42c0b9002034050061021004005070090302514001965840500c00800080308208005c00e40c84540c0c10202c0c0900030480204406034040c03239004010841c01c0d031030b285071240001d1500c5c0880152703400098482d0100045c5000030b0140c4041001d09900c122030a0501000403400700f80c41d082c070f05804070404510402103035a03c295100500c014282400707000e44600014000c240021248141c03544102d40300020444500a801c05020003081c84284000e00745140c81e4000e9400001d003500c1e241301c1c5501c0d2507010303038807000114014071941e183c14544a10390301d4461000b910003484c240c4241c4d8600b002890140d044091480e2241d0b0518ac40c0d81c0e10049103965064000d50140305540181c86c0801004655000054400260000700040c84c2d41d41c4e200c1880203000c1c403544080c1040c604c2c100280031620700b41290088a4407503800e0640300c2c99926040c50a184c805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 180741789 1250 180740539 180740543
    0x703020306030c13060602011d0a1401380316050d140f070812120705070f0b0c030117010e0d200f01020d0f0207030e13090602030c07050705030d08060d1e 68
    0x9505c000401c50543c0911a00002020650214110803a40c01105484104013540a84032041c3d41081640030341013944102c01241720b03440490005160038002d160795602c2586407540a0b504c1c07a95142642c5400145d048464a40303030403041500c1c2c2004180400b00d102c1d00d40486000d03486898000809005012500308000071700000c3c80c034a49000e0401d8075000c1d885600c0c410740c4008103c1d0b400311030a4803009590243c2c25040c46655180549008491501d4001c8050086003914090240c215240e42c0118120b4030000403000e8001c0c0d40744401800c80784548084411588045428000c05d0300a510519a081d044175080d0300300c0e002e10f0001c50403e000c2202e220b906940c00101071550f0200c0c1d1050703d0042d0860042181800c08664018007101d242c0a001352250040710041da00d024040e4010b20072155100700b003075440f42081e5000c04600d0300302a40449a42c01000800314080c1000900c220030b501503a5070314020350300e03000184907102e81700540c1590b400154103001d40c1c0c4140c0c8031100464480c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 180743039 1250 180741789 180741791
    0xb030109050d030b09010f030b06061902060108100e03070b090f06040c0303020d03060e06010e06040f080c120109050319020102070c0617100609050103110403050601030c03060614090703020306030c13 88
    0xd0301d41800101101e0043c04c245104144400c0103002d4808180344202c00d590b44110301e020310392104000240c070360152441c003042c10070410b0300345c10303072658041034070303412600d14208a80c0c5080c1440a004d0507905031118004140c1e1042c00b200c8045100721108a030003148030800e44440400c4070240718244102250152800f8060800c10403c240e410040d50703a80d40c00500d8100142402c0807040440d40300f014040604100507805a0005541c903c0d04480060a1140c0701c2d020941c0c2c0d403050a0340340d01c4102c171820b00c541d6506100303003101c07a07040c01980c525650040c06140351581240c20f000310303007590302e01c014119076007401020000317004031031307044050b00c51500d0307800050206d01017001708404028181d40d9280d00d420010803465402035080302c04c1d100242004142885400c09000c0b59019580c40909207110b0080000103001903c8800002ea130f0280509110b00c0d901e45420103620301d030a11125400140e6035001a010fa84241d01554008000038140c5d50501c0010000802400c003a900404520f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 180744289 1250 180743039 180743053
    0x11b0311130f210312091a0702101a031f020903060c0d0507091a0706110406030b01140a02030a08090a020a090509010c140901051c1a090f24040b03010905 68
    0x2072501c4007200800c0c16002d45841c209441c80713a074010041010220351058080d190000c0d0010014802d41c3c50361020180c5441d0203c034038020134025512001100c1d48006640740420303440895900b0600049a010040c0003808829580c1000c100c08000c58010842500d40c28898100e040e0303014020320380183c1c0e60400c02c5407183d5110240104603074005e8182c1040c403010303200410580001c1501441284820304d100b41e00c801060505c03138058426820301035069040080d001c541d040d095800224441401e9907414051601010392104510072100b5040140e881444007095051003020340a600c03013140d1040e6080880284c0c00700b102c41c10550001400380da03c0e1720030845010000d20030480c5044d0310340ba103480310503070031441e9a8440c0305d00022581001000203401c004584400891140c0028441e4108010b0070804c0c031300d9a41070300840c0c4040c8121100c0d004100322801e040031982c0102c8401044260007200070030f98110307614550240e03d40054940d90101c61695081c0308210351140614054104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 180745539 1250 180744289 180744299
    0x9010516060204030623040308180a1218060e090414060f060f0303070201080a0b0a0f06020c0109060e1003152d050111060a021e031e09011b0311130f 66
    0xa855001d103540500e040e680440e06c4901c0b090030300f02600143c16040001d260341300c80251603455140444510f000b0302c5045240c40400582501c3c0404c2d0652641d00c03d2054203400700304401c0485540300b40c0c40001e1580203110303003524000e404143c00034802c0b0110410141c801e20f0320b5040c904112105081315038680b0403c40780e8101501001343e86a021005940f80401a900180010001a040c0c0c0012507540d462032030b19448070b081201c040c117120914081414be0750f25000b540c1e500b074460046e000a12810000030810b00504003480c5040d001002c4291544660004900a003102200714140403102c0000203a581040320500c6811004251945a45d50445401100844240c0d1000b8100050012016903403000401d519400c00700f040701c09640c4025003039016001c0d0185504207e8540c1c0000280151040c051450801c0e851410b04481141d80d6020049801c90b0007485080744034400c0c00700e82150a034807a91080f14002c8664010360b040801c1c140300302145120079004a404002d480c3d0003880 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 180746789 1250 180745539 180745541
    0x8060f130b0307080d120f09050a0b07020c040b0a140406210203010b03060c0417030405040c030c02010b040c1407150507051308030702061209030d050406061d0c03010b090105160602040306 83
    0x1410000c0c001744010344014a004200d58002400210403da803591129a072181503046961013030307000402c039204040b02d410311a030004819a4001c001d41700342d10010b2003600b07284c0600c2c28103010040400840b00d01c0d280003194114101040190300651f6600007107009083c06081d071240405421a2074400c4150f403050501b10303258441c600340301c4d41c41501048500c515160495043d2a40001d03118404100c004d515440e5002d1398100540c0302d800c08a280481c140c0c5540461280e60f469802031081c0d00801c414401240d20200c00c4d4400100d21402a842c5062110001e0054a2240340300c81c2da0307000b500d00030300100c0d403041d201d80000801c00103483e1034030172290303c50308090010034002d1440d08c1403c1e0b000036107611407004001e038104c000c00001401200144295103154242c14030511035403400f440c0610041c05580568505088025012552031010320081449103a0707130f586080c038590030100a0030b00c94001c1c1c0d0f5031a0400008100d201040d004003400c40501710b204010168445043d490020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 180748039 1250 180746789 180746803
    0xb0117010204030506061512130b010905090a03030507091703030106030510121101110303040609060501060207080a080c0a0507030b01030506160509040c05040506131d06030d08060f130b03 83
    0x24889a005000c24800b1135004601030380c01c41e204441c5040c0116038000c584140340a56001c2640c0788800c0c1c1c00708910182c011244001061103940c3d0032510741c0e21045540704464003500c8546440d0b0210307002ca000280a5800301d6001080da0405500c8240e5414911800441c0b1a44402d015000800100400c58050040703c0c3c002e0071101d04c843d000c5041c410b00d10b90040c0300031000f03407100d400210810402d902440b9155a011410740640f956883c103818210050318941c4800c1721400d19003c00000c0032031022607500c00fa00d01e40000303000890481d84404810360008114202c035401800340d000d00054013085040c00562143c040e040d80d80d8550b091043c100b0b1401488100081711108049019603440811a0348901007228009000c3c01d072403c08a0759400f554208a421510000310300c05030f0303101a5100c10031101c00c601600b44401c90340e03841083e0b200c01902c516400d85d00c020369401c121130060914590059010f07285a0880a00000081440c0300b480040c2603080e540d5001ca01090405001d48 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 180749289 1250 180748039 180748079
    0x3050307150516051c0608030304020a05010e010509040b0307051215070807050306120c040e1501050a03031407060b10090915030b19090501020c07210809040c1b0b01 73
    0xb00003526062184036800008901600100040010700344003c00400c059200750a00e4064100040e640300c0030f856682e544155402e0b0700c10717010080d00160961080b140002c00c0341040c1c1d20f032410400124148400703040281529545030090050100b0707240c44506540c0c2070154004000c010804020321014240c00f0b02400344400c00844408002e034143e04041242d030021000c1c1c60404150154000f020704000402d01e405910508007401c5000c0c0c2c000000e16800c034400030140c444005d036607072020442e043c082880010003180e0840c8001115001c40c0024003440d9004a10110300e6403483d100107028443d0900980b80031408007042885a81d0107803050071000c0094203d07014000d425a101d0301a00b03400240440601c0c205580400c5110007582c200c5000346034004002d64407a10507070b04a86e1501d115011781d80d01c8004402c410f00308003040700010600903401254181c6000e070740801340f1010740070805c658000c1c0000c01070780f4400584640c600c0341a040c024440303400d107941010070112980f00c040d822 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 180750539 1250 180749289 180749291
    0x1309060203040602091816050c010e010501080c030d0806030a06020a181d06041a06090a050604030c06031113030b040c1d04020306130308010504090c0e010f050108070507050307020f120102040305030715 89
    0x3c02c40034804192020107090500d02340207840718025124903026110445410210394201400000c100e4800610345980000480235101c0c2d06062034000c441c003d5046805c035130726038481080309002c61101d900400d50751585240540220307040540d8070b00071034030540c4600a008008205003685007103111242d500302c07004403001d0040460060043d080c00251000313151140a0000320f003130703c55031000f040100400000d060b0b02e84560745e0341085008039900d4410000420300f0042680c0c40d109021044940f0600c0070209080042e041d80c40e40e070409100100f049551401421000c81c0065014a140850703807070048005459140c03510625062803c0900362210240742a00080d000a8210a4560554205480004082245040c456907160459001583c2c80c3c01e4071b0004161021200180402c0d103d0a8070346000b6500e5400f0704403450300c00c02c58041c01f03a40081c0000401858480c5c1032110010b0010482c0c3c11380c1002140060072680507a100725619400001c0302e1b0100582c00010803075041600318 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 180751789 1250 180750539 180750541
    0x81314040605010509150405040618050603070e01060f1202030a0914030a09291605010e1c0f0c02060a0f02070b04080303010308071a24040c02070513090602030406020918 75
    0xe00704c2d0080380e1005200304103410440200640e45001e84004000082c811301045917210100400014011452110f90742040e00240f058140040c4a404403005a0752040445e0310748042225401d02c1510003000301319a03822181c0303650100b800550302504840788006510040303407070040c07452003860301ca10205410030302000410980100620007141d1401c0160090002a014810700c421030300c0d000521880340c0030484e45442d070511004c91080c28440d0000700180d1401a40e0b807075403011160303103550022b04400c800d07040c800d1181100c91210042400c00c8000d000480d40000c0e0990014642c2000040400e0049201d036541080801c000b010603180c294078150402c0f42c804d880f44414003010b0f09030b000010706181000543c0c00328820f80026090f00e40c0e0715041080b0703000c041034450110192250b151518054091905100300c03511481c41d5001080740607c0c0009100c40d698000002101d07655950700c6640100c2c100380010741c840c900c2520700507914035407c0e0070050700c516040840e0361804c4c1000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 180753039 1250 180751789 180751799
    0x807020d020c010e0103020705060a020903150c0f0a0309140303090d0c120e060f040311180f070807020c03030c0102030f01120503250213060303020c04022104030302070813140406 79
    0x1041d445800b01082c601038003102004001600640b142c0500208184950000c001c004100c5501030441101c0807020ba030300d00d003654a0030040384441610140740100082102d00b0410308020000e040c4a5001d040100c1c0003c2c168540b00950032000105202e2600000104503075030f20144640742c00c42c0341794180030b0151540ba803a070240004045446809010305800c400605540d81020303540b00407e08a04c86590325103a140504401044541e00360184681c48602c2001c06107840d0000e02c21403103c0070014403607132110400c0700c030008040c2c51082507002d503c8a00c00651018402003844844480015a590401c460040d0290b10305a00400b194100c03d220400000c102000312680110b001a6180780041441d146078120f05080c04000d5125603000030000104005402c80c0c002c880c060303006d4404170800c10083c00107038401c0c604154280201c1e41190b40105804000b00d5400a00138900141403170015990000d196101c011b16610420011034204a440700b180000c50481a00f603c003400607030701d06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 180754289 1250 180753039 180753043
    0x70b180d0e0d03050f0d0b01020d2c011e08010f170a08090f0a090c0210060510050705010f0204030b09070b0f0405010507022b0b16020a02060c0a0b0c04060807020d02 73
    0x541d140c42044110051014188254260307500d040c0c81002096440c03403181d001c000140039005445015015180300000d2540c09280a03c6411140003a00e50842d0100380c1010140d440d80c41c2c0072414804c039074441800351040b011045080306142d480f252800c0d4148403030412403104650180c5440804c20541c03512a943c042114144c19174000401905c55154100140f000380a280c2d182d50021000f0000180000c0c0070342111800c081c180c3c09868600700d03800000340136690940151608020007681c9100c80310b120740c1c024601c07075019a0001170312403a0741c0791000681c1d20940c000d0341c000003802c042c05121901071007a84000c0c801e0780c8140e464502031070303410449030040d03119181c1408008562602503407100a040d090458014590345045c0d1000d40c03410165000c940400c9e02d82c45117680010710005000c42403420100c40940003005070701500d50810900d64409514a410b9000d01918080000c0b00380c0a001d000c0d281030106a601d43c3d00b0320070008c08869000f0b0404003150b03ca00c50149920b600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 180755395 1106 180754289 180754307
    0x203150a050a0501031709030c0603040b06130209010801140d05060a050a0b0f0303030109050c0417030703030b031b0f120f070602120307020312100803070b180d 71
    0x700d038018800c8070002d0000402e103220031901c5046c00345d005c07006022800001011941c00703100c010085060f0b504150341c03c83d452004102442080c2c49c1000380e601c00c11088003001c509000c440302c00201881d00600c64550a01d05030141c00b1f500d0f403640d800c20020550403a003100d0746820681c03c518020f05045810246080c50140807041c54940303000c4400d02d200004000318290f03428022440b00410000c0c10018100700c00b000001098a0107002003618000f4002c007440d25802d003410040c0642c1c00204006110350040c128441c0104c683d840c11001c010400e49403113101018003004914040603c1400300c0301445104544105503d0024054094030040d81c282c4082007101c0080310114007090341c0c14009600244010701c0c240c1906407200f035008562028441142c0d50707552007142154031445050300c41e446c0b00300800640c40440c1048420181c44000100800c80310705c00c0040c01d16003 = true := by decide +kernel

theorem cover : BRFrame.Cov 180575539 180755395 := by
  have h0 := BRFrame.cov_init 180575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 180575539 ≤ n) (h2 : n < 180755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
