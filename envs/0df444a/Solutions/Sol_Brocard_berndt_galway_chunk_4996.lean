-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4996
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:24:25.564704+00:00
-- url     : https://prove2.me/submissions/76f05415-e381-4c60-94a5-47c4006f4291

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 898381294 ≤ n < 898561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 898382544 1250 898381294 898381331
    0x307060c022d1204120c090b0105160507120f031d151e0c010e0f010b0306070e2103040f050a0b0909190e0d0e09060109060f210509070e0c040506090f04 67
    0x41c015046c4110060301d5001241c1220342d4001c20f103020540400420022802c0381841c09880d5006009440800d507580c0e0090b0700c05d0710741000c1181d00c11421400d050405409c161007032035007202e54031141d00201c10031022a000c2e141d040d0285940d0361010510405070b01e0120044e070303d00340034004015207442743c42183c14060012070503030754000d0091203d060b0200205214020400b8002001040e180c0c81d401405e5407030503003504140e078111404400142d8101c4003ea110031540f11214001c5a8482c0b90052118080c031a94010301c2c400e5070300242c10440c2403544001c1d5800410708032008011520b606120305481d24a510740c003021a400d00b0227000c035959020444030140f21071600d40759001e00c0707031f0002c0065100080301c030b0034041550b846003484082d11034481d42e000703050f41e810b00386c49883d1030865030201a0f1a249000241940383c0041108001050100074010400c01142900714180074400040350301a07070140d2400f411003c6144d80e40703583e62407001001684003800822174250354541c010390300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 898383794 1250 898382544 898382579
    0x61703040608070203070c0902090a121406161202090402160602120f0c0307030e030c01091103070b0f03010b07051507020a02120c0d060b0a080d020307060c022d1204 73
    0x45140d40340010441d6002100712000303c1d41c0300241982007418148e00400030b41200c0d040f5504405107110102d21650b0f4030031182103031170007505030211000008254500d8008010104100c603045112022456908055403a040c02054640540c503290345102090003030080c84d8032501c41d980e48403603a0040c004076600402003480a0950b4401d540d4810210007010728003074a29102103482000000c244c1840781c0d0044120702030304400d81385040350000d030f800e00b542c0034240240c400c80300c15030490220386800c0020100a000408501c5d08089920041003111b00051140111f80c00c00000c0060030880b0510010703030702c0c9400202c050380714200070000943d0740070298800c81c065203005210313a14103500041c401003075a0300240900c00100f9940d42d00c5000c2d21a076a42c854000f2043c240120310150305000740c54a020320796004544074491400c0441c16a94031040d10400e5400000221394512040d00840c0c00d1524000d00d001c84001001d158140391103a00701e60310038582c10205011807003584010340000d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 898385044 1250 898383794 898383797
    0xc0d081e16060b011d0d030c0c18051b0703230a0e090717060103020a0e030f2103010e0f09160b0d060503030c06130519050c10080906010e0a0617030406 67
    0xc5410000010350b11140583d18810050106100c5e200403032404000c0741c0f00091181c90074044e410515944c80d1030510f10750700440b0900410042d52098039a0130721038030754000300c0305840d42000402241001035510030a040a4100600001400c003030340041d41400e55650364402d0600e41d2820b2404008208504180e0100d20402d41c1d2800325000a103d03264005400415030500c8159448100043d402076114030f20440602400f9480c59556035000d03c20750200b002060003900702c0c08902d5804100c0940143d42950348448180014004007c0b0140c5003940701c010000c0914168454031202813610b0000e95865069203050000480c0c20072810004d0007046403020000d0100585a0041544900450904032030f40d0740107500203840c8110060705c1c01c00590152003074601101031112242216a2280020754690307024050011040c20031402d074000c480281d10b440c0e112170510305d40e4540c580b5010720550f5030921408000c140c03090800e034000d00003000c800c0004a5481459240103440b40c025214a50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 898386294 1250 898385044 898385051
    0x509040b01020c0901180905070e01080601120b0f04060b04020c07030320030d09060908030109050f060a030503390a050d030e1c09030209070c05060106020c0d081e1606 74
    0x4865000048083c0329480050607144180c0c00c0c503030079020b40140740519a4655840345031072008501d051000c83c000d02164007518006604051000c1d00c0c00c003040e4840e00080700300c2c240708008112200e8403180c1000244810f4441c51300c4a017016001b0780030481d47d035a0700c584000f40b00d03400c5000c0025000112407090301d444c80502c0d082c255090501b00c6a46c0c00750700503001040f0108070000c0c0d6034071182c1860b02c04d40002480f616240c9414041e500240c001ca410650344100f48034850280050f0680c8c8041c044035440165030556807600e450b4010040d405910503806182c010740c206600290012030481c00f02081542c4001e050107580e55018110241c0d07807401040e843e0281e10784240180100410500d00178682c01c40c2035080c58220082d0a01500100180b10318080700507a550034206010b6030b480d82d1410050702031410514207104042e072140b015503205000000c02c603187c41404c1d100107038100704415200c0d5203580b280e4000c02021005101d90400009508080f01c13115142018411f020b5981003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 898387544 1250 898386294 898386311
    0xc0b09030d1d040905250905010b0f0711150c010c080906010e010b0d060b0a0503061e01020d120b040204030501020c1006030809061c0f0e01180804090228050904 71
    0x566003a400c0c80c202454542600d920a000d60820b84c2000c11001c1c86202114402c075840c220118008110526440305550401c1081210070024025603025042030307090a458070710110b404003103e20078010300506d800000c95090701a9a145030492401101d421442c942d40e4510840d1103000300040462078010a8641d0040740400d100014554141c60310031a400717a15034202114402c5a41244070341d50402c81e1101d074080381003016007010780204e40540e210307251642401410015440d0700e4030381e03542000c992088034003104c0e030b400620202d03140d81d031742490b512410b031005084014061110030b054009000040010400805600a08409413039100743c52000440083d1501035500d03510010b0010380007842091075a18203140106000c0000b410440080c0c200355000d0b1090301c41c1d440b1605d0155555a0800c1da0071607003802180d507074445650841c0113460352940d500c8034901580c05816407203540441c0c034084110001e9520280c0d180c450748501304503154dd0b14020036540c0281d40042c055410855072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 898388794 1250 898387544 898387547
    0x80c19050d0f022710030509120c06010302010e0415050f0d020613091104140402131e050a0f06120902220203040c0e0c09090402030118051605032a030a0c0b09030d 72
    0x74076a0710714010711840a08a0905d81100a084098040c0040d0b0040b0101c2d48234084010004210000501c40074005941c1346000142041c5580c039900c9008034204950f040071318030300c8442017041ea40121003075000310341201c012510811000340001e4101d5000070f10080302d641041c2d038050444074800f600703122041e0f1000fa024103601503071148070882c000441c5601101c0c90a600540600d006d941e400c0742c0c42907581e0303902c28654244a518460389003c40070051003241400b41d803c5e405070840206031310703080d0310700344004081c11002900200d046a0b03920720142103607900848900e00060070000a9122184c100d0311100170740c030030794080782d41d102d840000241c4d03c1c2c031840100d0300c55032042865030704205048040c000d100354010310481e455542e035140c02d0005041c0c0c0d04100c0d2081d005100400034600842d2201c0e40207080d40e049a4400d500c03040801c624600c04411140340c124440d080d6070008440000440e141c60b100300744c01081415070380008a220584c01015000c4050300b182100c4031018480070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 898390044 1250 898388794 898388857
    0x70906080609120c0601090b040b090703021c0608191403190e0a062015090d030b030109020303040308071407121e0305031b07060218030607080c19050d0f02 69
    0x80c08807117401410041000c00f1041d40010125000a400458042a1036002501d10380302200c10030046540031411070104030740d02d200c450f404007030804200900c0c2d0421480701d555981d81c480f4400962244a484001c120100010034510300c958411a621401281caaa010340c100c041e40000016000c2d11030b082c01840d1a4100c00225810fa4480c0c5150713055210b20280c00902d4480204a184100000c1d42c1e100c0d011582d03007034840c04040001e81017000d94460700900303450100400d01d109078180750201003d660040100c4c0d048131f41c41000d0300d42d50381a92906d602c1070410b11f10000c0d21405025000a1000000320a889041d0310444140c00001c82e245030200f042a15110702400003801440001c0c1c0409001c0e01d9803402a103142807090070300341c25903900030680e07000c1214600c080f0740102800c00181010440540c2109680c14801918500702c21400070600a6680c10b85805a08441660700c280c020811a400c031608444103010910ba000c00400c040e60203110b0420010120111a0b0549001d415 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 898391294 1250 898390044 898390057
    0x12080601080a0507080106080403230306150301050307051210060303080703110a080a021309090f0b01081f0506120f01141008100207021801031101031b0c0209070207090608060912 79
    0x1c17100c2280340d003080740459100f903004000701e00b400040b00d1040c50022110071801600140c440d011030392450000240102c5104510044180314010f00051113980e40215241c415100309a46d001c0f241044861494500742c4000790385800c041c504540441030640c081d00c0b071352088a10340c40030b01c400c0e0680345130480d9030310031082d03810001601d05000c170300d440c0200c2d0020300e103085605ca014068030342c5400a400803501c3c6040102d0b51074585040207401c1103000302c0b48a005045010190170101142e01e01079800e42c02c05980b84010560307a070009801a078030018407034908207800b8116081404001c941900820100d044190403089680c000741400d01c000c040d01094600c1c10014140ca1144035102c000690410302c0f00f2a4005807513002500c0d41125064080c3c001c50290361202480c0c0f450100150490303610742c80d154201c2810985c811180c40c2c0099644940070b505660b07a00c895951440c00720b0030400c0c1d80c1c002c1c00300c3e0350400000142058000504a01940c504070076241d205c4402d0540c20290b11030722 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 898392544 1250 898391294 898391297
    0x110c010902030c0a081506240c010606020c1309020301022802011d07030303020318120a09090903090e0a0f020a05090a0b03041a090c0301090c1404050f01050d0201020a12080601080a0507 82
    0x106d40c050003014200940354000d0f101400c003015102d484448440c81c2e0140e40c51195542c0c40210b040c003031012003401480e005103420b001808410b00000045410389010800d1401e01c0c60311071910341c2c2191070075412140b6411701554825a503c0c0c2102c523204130000b10480e0700005600306114030074100b01d0040c00030003246024004010382d40c9141d405074040e400c01401841214040c10780d00704020000c1c48004c0000d040c400c1010794030710021002501c103a010360072460a080c6001d040100103908903102300c0548424211140f100e942d05840b290180c000640882e0030603001045801819800c200a044440002c89000180319100ca410f1109400101c030054040614550b4002c58034a80d501e41c02d4000c00d109040d100601c4e10385000c2401d480d600901180d0409103e0720401016041c0142d420a0396401c032070074085800e10b00000b208000060281e1031045c2800b07020082168002c11102c0d44480d4000c0c2c04210804500b000607103d5882161000d0101c0c62240001e14002a144181c1e445206c15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 898393794 1250 898392544 898392553
    0x1f08011b110c01080105121e0c090c1e0d0209100801140111060f1317040905010503061501080601030b13140c0c06011211090f160c15050a110c010902030c0a08 70
    0xa2031b0410641b82a51580b840482c010b103148031100d92002ea0038050b143d400361004000c0310a0720014803424140050001424002c00c3c020070848580c1c0485a00841817100030315600d84000c0c06100707000744034140901c2d0344100702000008800b41c1000308a03040f90000d41804407002c01314401518003540210043e21203412440018941f41107080280d6080300c0551030020044660390b9420500f81240e80008007030000214042011024500541e8090074050300075002504106071200c00b509441c0c1c840f036060000b404005046c9034030940c032040c8960740062000b0071031f41d00d045030034004140c10f00c08003400950400000c1c000104410460f6800500400244126860604100117218032802c00321015289100141d50540c1d507002c0c0c580c01840711380382419280c1007a811004221420303014a81c18041a418001d0100303403500002800803400c1c9001080c0c1c0e40d84c400703400c0e0081044006500d2488004900c084600303505502202c4828030a03011145185030810410551012601c074240c8150f20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 898395044 1250 898393794 898393799
    0x10615080118060f0905060a06110a0303090305090301150e15060409020d0609110a09050f03030a030e1612031214153c040204030b1f08011b110c010801 67
    0x41c0992180d10005003040043c442d92100e059011011003544a11103480c0c0310801c1c02a03520300602c4180c020010740c1024101d5102003210a51075000040025051540d0b450041d410715000f613084440303800c0d00a000300031007036812169111007a03803809240c0040c01070400059000c040d548400203030359402031406040500d807032821400b0394007a494040c00d1944a0321700094030940c6004001c420811041e050740c84e803041d54401482000300d64003061045129900b091000d45002c030885d8100b41da10310340441d090070108c441c0b0340b81c0f4a01d1042001d000741c0700314000441c40600598000325600ca40d82d03460349112000307811400e5854207280025100c0c694404900c4001074140b441c00071000242044c0c032100340c0c4ca80d84104480501c0c603d25180ca2507102c01d8008002850b0310705100d180219011410603056895440f1220001031040d0340c084502c0203000766074404164084002d0251030002e014020b031540940c022440d032034607200e020503804100c00090004c08198182c8500d41a510a002a0b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 898396294 1250 898395044 898395059
    0x1103091903020a05011406030c031c030f140424020f040603020306183c061207080304090209121c030209180408030103050c01181401050d0513050106150801 69
    0x841400045003944140005034000400030701460100c480212506c45181c58007809060501c00107640c0c25220f50000110304200d18241107806024046610b80001d100e100c0c0c0480c100205000301041030443c0b00c02042008000c0074603120018680e8078107288802c403c062040405901500052500c101c00501c130a00607140301c1ea01035640400c004080140221050782c1c07041c0842d409544850100680d640601001410050340b000f0141003508089510560840402041c000140c040c3e44034044105102d484000c0c10041e0401074210ba606032aaa135681d01200c90003988121000c3d80121042c011b08480c01c5d001044045141220210b20380c442d10342e4013401c0340254001944c0b180c1c05142500c081e0321480b4410070700d0b071042d0301c00e46041d6a00e5055061036407600d150102d5036030400c4001456410b0441e600c0c031421085541c02a107a00300403034045e006035450b0040d4045041170514100c208821230f0b05103488184401d008a008014032a11000c28000e0a00704603600c60204844000400041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 898397544 1250 898396294 898396333
    0x10b0a050a030b06030901061e03020a290318150f041b170a02031002031e04062714030a170c0403061e0b03031215011e09060201110309 60
    0x140110b02d00020240300100009049070001c0d01c0102c95030b0341d00e1409002c40c0900c00c405403100c1510542800c9060714507070025030b926259000380a000f0950109420000c0c120030645544080100c1c1d02d0794480ca4940c01c84500e034032650b180400e030f5202d10700c42110b05050318801e032409180307200c040c0c240540d203039100d00c0c1001c0300c900c0d000c1d81c000d071101d50300003000030030030380f911480300b0581c00549500307107032401003610780701d03041203400581403042051100e05010802010843c1158440c0d0000c1e83c1d841e4140b0200812160782d00c3c0300002e60250785140c20403125100c1e500390603c1034940070b081d9040c40811aa80c0e004843d541d10224501c42d100d5a001015410503903072100000600900d481d031241c4d41c400a880c0c4072000811240c9204890180c9000d45000391007841c04223030300443c20300d512201a000c218601425901d000300d0042d2200003da4400c100c01c524098003803075000c0d860103030000001d040e800f0030b20504005520f810001a0b110565100b1240600c10440042118851500700406d20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 898398794 1250 898397544 898397557
    0x23010c020d05030c0102040e010906060c0f030c060f090303051e0a1d010c02010b120d0c0209040602071b18060833101706071706131a1008010b0a05 65
    0x101c1d081c01d048000503810402000e07808000800581c407140340414550554030306820058100d0b06103002070083e19800490403240316040b84179034009c041c1c1c3d03040c16210f120000001402481c240760011020001e10f07049441040e1080e581041280e035241540e1480000034100070340b1032884480440c0301c84e47e403600100000d084000320300c0d001d4200201d94a08507007800c107205015075141e4846081600c1c017810341800501803600a07103c880c070382d0100104060180d11300240320701d50070404542440f00039419680410b912040300400b60f541d003070000c01d0440c854814003030031003c0c103030080300d2401c505e0142004130742d0030030700411543c4c8120544441e44118180c070303640b031060101e8000c802c42c00d00c20b0569001c0e01c0441c8010a80302d04140ca102014001e50b0380690942e40b0070400c1c011600c0e440300030541e03030502042c2c020440d0f488620020f01d24219402c0720100660400b04400303038509000e8103454140404523148200e0300e00050040d2082402442144488a024081544800d0280000700807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 898400044 1250 898398794 898398799
    0x406061502031206041d03161101080705041e0803070f06060618150e030d031505010302120a0c2105011d06060403060c090e010303050705011103010b040506180301140f0123010c02 79
    0x6d1030150030b040d032840c40d084403c200d00114a241c8041c0305001c15071070300400740f450a02e0840e0851500c01c030040d04a1040e4031541c52480740d20b000070f50152214285000141000500740c980e20030b024181007540024021084d2040f900c0d00701c0010342c2034000e039420340c0c5684180240f00105413508502ca0700c0000410103807001c2c0304003890304140566050041c403d0040080d1030009941d50f60f00210040b80180b5013109050510410807150110142c05d070007a0f000384842804202101c00b00700807116890304500d5043c40354042c42040404815a030000ca041e20780d00c0002100b004080c2c0c84001003002c0039110150000c404000070700c0400c26a0f00312280c210110b0030b180e08041d6039019522441a0240c0c000da000490104007042000420300076103028050b40003489044d941410050907441c4124480c49104000c009910086040030034545107105000500800620499590b9900b080100f100c114209580d594004164941d42420010784040741c0c11442c101000340800664250450000690303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 898401294 1250 898400044 898400081
    0x3200c0705040203091606140306041e06090b040e01060e1306060302060a110d0924031407111908041a09090408130e0f040f03090806040606150203120604 68
    0x407540c60b5800254085c0021100501c016010202c400c00300d8201e91700b1000400000102c07144980171000180d0b0b40017641100c00040300e03404642c00965901c62400001c0c03072170b8103090380050b04c600281c5c000384805030300780c401344580030900f0b0b0302500f01da0781400b07601035640844001c600300c544d50208440c0c01c58410500002c2ca503407aa000180d05802c04540b8a002911011a0b24008030040c00081700c0802e070b0742000c100303d03824009042000c40512240300b6890342d20031001e20844d88650013025210003079090bc0d94042c00d10220040c41030800c08020503d40c81403039071181c040f08030741904c0818650030803852803c0a08011400d101c610403095202c030345800a2006006030742c0c89444440c05036205e103c0f05507903511500d20000314425a81d1100f41c4c078010120030000c50030003811810b503029502408010300043c2901e400c3d0740c0b003010768002c0140307403180c88104801c00495500c080240c40e990329216801d850100300c2280d43e84102c0c40900030b0340440c40041032050519800c40494000000c0f4001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 898402544 1250 898401294 898401299
    0xd0305030702070f09090204061221030225020a050603010b030a0207080c030a030915060803041419030f0201080a11090d2a17010605010c0305030a15090207110103200c07 75
    0x1494036484d5804c034140d859504d29481013149010700c1002c009008140300c4624020303050315071040001c9100c49404801012680b41c00d2002c0c440c0e03040781e004819003104220f00030503004949081c5141c0440480c040c0c0303000745000ca074074030707110003607034100d801e150032140c40c4d0b44c2c075803e25038041e4128000407140100140020f200b00ca100303001030404e075045950002000442c81c04d0100070001050180c0e0151440c042c811301900502004580c2a2845c2411a134410300410300807901d02070070317000300b40341d10b40855001204120014542901c903a000340c0c4c1c0d24026444080c0d41d1000c4500e12042d01e814a0003c000b0600541031408000048a0040056011100c003011495042040301d00340070075280001c200500a4803034520f0030950300f01c031820080056509040011741690340749040501480303000b00002c0c45128031170f04005c083c41c0e0304c1640b1000c40382e682c0c50024044d42040a040311200c0442400c08040c0d403291292810500d1000a0340c12850401c400b0840d041d8003c020f039444c1402a620007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 898403794 1250 898402544 898402559
    0x3060603070f09120b0601090b041202150910080a0c030b1008060102120f09120a020904030c080c0a030c030809150a0e0f0703140706031107020609041e0510140d030503070207 77
    0x404c440c13030040a40000601d00f00000500c0c0c0d8415400599a00b0300a00003401a02e00c100c2c4100030950341500c141c20700b002c0c00b500b401c0003070092201e0a0303480799100b88480401035110b25154007070400b008041c800350500040a50655101441c4107400111210305054002d1190f00703c00e070001c0703041c01542d10803051004254281e920102c0c0001503c1000a0680400d080000c0c0d01110001d52501502c1c040980da40050742142029202074100002d602c0d01000703011b0302d4000c43c0c2c065440401202d0074400300307190280a9010342c14003076022841e28400500710740004641c00101c4440206d01c140c0950312804044007e00c41c40300206d809100710b886d090380c419010800a00554000c001c45243e5400c1107420610307040e0140c00c200c081608104600f0b040724504c00950300c0e2541e04407051a1a903008102040080c06004058614080c2c0c0d5984041d0f9007020b83e000c68003907002c007003900c02030030784072400078241c3c240c1d590905800c0016031484002091003070001d59008011481aa104640c0d142ca4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 898405044 1250 898403794 898403819
    0x913090609050601050a08150105120f03030901201e0f070605011d0907060912030e0319060c020c03060c070c051002030c102a0e040e060604060b03060603070f09 71
    0x304a80507440f0400510042c0f4150b182e03940100a210002c0402070968003224a140006201e00317070042610035907c4038041d0040c42403340140f40402140d0316441c080780500e000e020203c829810950003504014050309852044546210802d2810031030a0340340b4402081c0d5603c0103181c0010103806108690016060780a180c0c000d050b084813105140d500009000803e21000d03250f000d4942c04110704000168129031500103e490301303105a504000281016180e280d803441d2040d80c5130241c0b8402c5240e0a0020861030195400b810341006040e800070b205aa680000e0301c04d20350326600c0075001034001200140100609072007603004001c15903845010814440307000c0e000c0d201503000894075443c4400c041000c0928800e6445c414400744c1c142c0024400c1e55141483c105021a4074585105103141c0a48079601d18184050400c1045945012046842c0c0606032851842076061600c00a1121000e00944c0c2c054000100011b1442e00c4000341524031481501500091180c0c00c40b000644003030425 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 898406294 1250 898405044 898405061
    0x1a09180a03171006090612021201080f0c030313120206070605130b1303080402210d0c02040609051506032d0103020907170106180f09020a090f030809130906 69
    0x841d0018801c1c5640600c60b41c040e0010410044900041c80800030b265000207800100c1d1820304140c0c003000400f41d0204003900ca2842203105240c8450000103040d140065402520015039094502c032040782c4040644034420b0315141d410302d6001000c04c2c4010084100035600462000303001601d003050503613440301660005c0303a000001c498021006028410480280769006188202c0c02c992450b030b540d4007401440e00903002900440d00c0c442101210070b4071100c0400c030041c104040390303040c070950754004242004c10001240114100180018000742c28041c41d03000d881c1e0709140c035001c00f4444040c0002c5410013045400305110009041140041e1a04001e20701d01c50603016503a60740c150700600c4140d880c0600918100100e0b01d41340042c400c0f02c00c040341e040d00d40d0b80c40c01000c1c40c2201c44060341d50351250740000d040c00701e100100050000c00359000713000e07005041d140c00c007080da81e0791500e1503002064440903125580401880d074007071030f00701800c454004031100d0000746591243c946101315141030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 898407544 1250 898406294 898406297
    0x62007080f061b0918040201030902040921110d0e1306061d0609031c0306050603090303040528020609041e3606200c0d030501091a09180a03 62
    0x4800b44004845a0b000e40f00d44402981102c03498a08500080350302c070840704014001a807a050049002c680c8603030465842d00d5001403080c0255486414400245444103001903402c01c05000249181c901954108950b2140c0780c001e000c40d51400c800580720002d03401601c075030020760389411201020b1284a500094005503403415208201d080c290303082c1216449401c0c1c42001d003403180307000d503650000c2c0e22400f42d0804000c030a410005460190040c1555401c05030344844007008003c046203001000e540f01c2e501030001c5885403101e2414418509882e220180320b030f24480d140f8200581484c030020b0a0900d805000000e140c0c425050140f002601c0150007201d445d103a08544c400c8000f4805044003440441ea20585d50780c94081000c6402141c000300200b0064403809800480c000441c40180600118159540e84d9800255401c0e156a4050300d6100441d20b400300104e0040450b1080b21001054000e00c0054054070030100420b01e0002071601c981d04a0280005100550922542008a200b07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 898408794 1250 898407544 898407553
    0x3060d0b0702011a06041404110408100902210703120918020d1109010504030b13050d080a1a151e0a0f031d030f072f1306062007080f 59
    0x40711040c0301c3d6000c0c403140c503215174000e000502c43c184665400501c10482200c0c001207400d0007442408032401540d12030030b280d000e00c0c3c000b9441d02d00540c1128842c14400c88003010004003510480d2540d901403a50840c0b0780d8425082800002c580342c00001000185090180c10365a650702903001028000c07030200d44540e0080380800809443e401b601507240c10b901d9040d0300306046d41380000c01074000c52001800da01071410104050b80e035055031034001030380c01009031429041480740103040a00d0a44800c58900d01e803592000d0000b104400c1c117100d074000100740414a02c20350321505a10b400c40c90f0140e01c172040d1f40003428403a00e186802000c4c005001e8a403900403070300140e00681282c45a00c07500c00c00c007020f000d020387c01d0880402210580700c03030740075015158020740c01d2100300700103203120850390000900c0c043d81e5613011100201554040485408100c0c1c10003d4550043e608148584e00100300c040000e2008584055803aa022800316000c440d0720903614511585485206801c84500760030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 898410044 1250 898408794 898408811
    0x5030a0204030f03170f0613180f0303061809050c040f1b080121050c01050c0322031106130302100203070203030f090109120f0303050c070605041101080a090b0c03060d0b070201 78
    0x140131182e161b020200c1e089012840c60080d010030524901e00d43d041940d16580e003203035a8005424960140040d4001c501501c8002d20703468041d004020b140100c01c00380d0007424858010200900401100681c043c0280c11610807210902c005803127011010008151101140645170b4451000c20155402c40e6666060b154907050780382c4103540b4000d11085030082e452420310041040022000c039005000e02e029541c0d5468040700381d00f9805100c0e84542c0244207911b100b5040091281200152030041e03481d650b000c1102d40400c03240b8420142c0c0c039034a00c10010070070009880c2c141c90300d0084c040d0600541c0c0c40d001007580064210360200046440c0750700e02051403045941e2000c11540905805001d040040c0105e446405c803600c2040700080c01c0540341c0c00002c2101c480c40080d40d186a030b101c0000d0000f8186413030103184003d2401126800140d5080c00a07041d82160f0285d280c09a0700301c940f4550301d84450070520003980c001010150403c4290f000b00000514001950380710741400da000041003078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 898411294 1250 898410044 898410077
    0x305030a0e01090f0503031e0c06010b2104030c170d020c2805120d0f0609021e03010b1b01090b180c03070f0e0a0e060c070b01091401030305030a0204030f03 69
    0x1520394000c10a00c250301300c1c00f800241c40c0001110f62949035070b40c0902403400050b20b1400284642030004201c1c0c000e603000000c80300002c1c409400d0020501c24411941c02d00b160440041c110b0807a1301500003009641003401194082186070360155800038a5031400b07101c0b08031030050380c0c00b0340150320711039000002080074001140080e840035048600c144881c212240c50310790b03035101e0900303a601e0011400038100b15262150307401900c8030303001840e00380300103541c4540c40002500503400b0007031099509101c1c45e80034074900048a040c3c40c0f503204504e0030180c4151185091241d08070060790707150f59600580000c10a0704048611907038107440c90f10030725144254018101211062a103009034084035050040d0154241030340e06440a4285d018807030b969070012907002d8000700814014a000720000e010400030264010010f00d07018694120701a40d0b200355400c1200c20b4200c800001c2140d6500510009204200441e0400460003026050644a4850704070600c0900e0307044000c074030380c807401a9524 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 898412544 1250 898411294 898411307
    0x212150709080c06070201051b1623220f150902210c0d270b270a060b0a080d0e1302072102010905010204140a0e1302040b04060305030a0e01 62
    0x6441c10b555181c05d0507074a600181c8507008240b00100302c07042894924103200401c2000003d0f6455014414a80036550f62064840c1c120300d101c1c0b032581007003c002c01851401c1c071480004141d09a0401132440c1c034000c004240060800ca40705480d105d8540e6007104403441407010703c8000d00680700006030740348a915810f001102d40080d1001010800c1c40400c01e155444100392070b9986c0e6030050104049408074550b01420400031510b003001c944a100100134000c405034180c0c41200d440c440e1074140e1924030248115203e0f03071044070740c003503004000d01c030700260460b088036203000d0b8060000d21038182c4600490b41410f09172040b540000302c01c3c5e4160071107441d00340005000c59061080440c43d0170329546560007002c2a040c00480c0c0da000c6104030409043c800d61044050b030740c1120007103494980b2813400203480c1090100ca544210544180800c2d405162044d0900130051052105401100d650030704c4094002404802d6000783d494400002242c82403004004484282e5a0178606038848170015002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 898413794 1250 898412544 898412563
    0x8060f031e12041e0614070f240501090e0f060a2f0d0606110307060b0118080109051501060221070204050412091a0406080a0b1503090d0201050c07021215070908 71
    0xc002590482c8106c0303451010880340e220703800141181c400c242c60f0a260181c0015100d92040d4205050000c0304400290347c062410703644001e0301400014400a10650764410308900c183c103d0300104041000d10b80a5445400901890400b98142020030f0040e480c0c01640942444031090000541c1020000f0354400c00c80503102d5070404200f00404030102c03075903038000d0250003044243c0e10041207070140e01444401e40c107880d0302050030b01420703120041d56029000c4600200c580e0312420788005e1034290240c0030b5038165078866000385480c804000c86500303196940111176902007005c007e07400c050780b52030140c548103034098803181c18000900384008140181e01e91110b80c1c01e66800c2c04480201d45082e0440303080341c000b450040001c4e1103240401009010000304681d00000c0110038100450f21000514801c4d83c129095643d05c2d45407500c16400e8030b40468280b00b8280003044400010701d003441d803d205c030310407220032200d04110344180c07400e50078070513190386002c40d5250b4001c02c00d21400300440d103076 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 898415044 1250 898413794 898413797
    0x30f100e0307080403080a090b0c0c010e18060d0c0f06050a02060901060810020f04093801022e0f0516090b0702040e1207060c08060f031e12041e06 65
    0xa0000543c0700d903800781c00f840c0801000300d440001c41081d042c2c85246204041e10030340325450303955002d200400ba07070b42c410307406058042600302c80307942da4526010000803050340d16080c030b2414503a184810402180030341c81040304c4d4101c0c042c41c0800c0c1840fa84680c50060f281e41e464041d40c03140d050b09c0113490040018080d060a030b0600710140040310003c01e038907180c80c842c100003607100c603500d10302c11f034050003141c1150600b40d240c07038140328181d9501040d10a0640c7d40f03d10a9100007241001c80c585240140b0a02c1e000da4014600c4003201c0b224114490544021b01020504060080307a10b802940c11410b50b200000da1a0000e0040c0308040b80e0031800c518415041c00350005150855101681c0a004000392003144d071420710b20010b0703005001c5002c90100010125684501914048000300000c0e0f0460000544284c0020030f1400d1101401074103030f100900821500340c02128140d0200b0002c6049040c038001ea4001c042d91400e0078029002514080055140400f044100ca41418249500050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 898416294 1250 898415044 898415047
    0x10621050a080307110f2d060f04020409020904030206090d110606040c0201092a050906061605011d060f0a0203010e0c070c0b030a05100608091207050c030f100e03 72
    0x600d001a50406855002030200d807255034a100c1aa2003e81c0d00c00f450780c090181001c50b140c0010040f50600206c10003914a1036075505080885050070a403189401e070715488400410500000301c403855a000d48010400f01e0012042d6001c40c1c0d0180d0195001c0b4003690011041c002c13118824080c0704040002d618100a00b03014648205540741d0303003e0565401141d4403888400501e2003034000c8000076410400d0b1465252940c0b003101c1d110350440e00640031581103007102240501d40584403500907071005212504040c62404140b0400400e03480848031507680e10004014075108100d0302c0b0000300c800e40074201714031301074050b0028600c0041c9901c103654070400c018440b220b890401560480c86400100351941058500851a0032882d0007080c000c010100c100510401c103034216030701c81c59081c1c020030045541c0780e00590b680e40042d101121180c00c1211396212000600d400707443e0f40d41c01001110142040360300440d0400301c00c411071881c10740102124140c00011400388840e96510400110b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 898417544 1250 898416294 898416359
    0x60b0705070e04240903081f0905041b030c3605130519050c031c050717031009240b0711090103080909100302010c061d0f0f010b06030f04060c1209050106 68
    0x2009131247c0227950750300344e075040410280203e0480d14800880c4c0c000c6000a01601c0b030514410346c40541c8203591010900c1011120701040c030805144014404c61110100c0d05100d0107a18042c040091100d241150740480400c041401003100214004401c050b41006009504189050074003030103400c2e00030350010b05210380c00007510514128074a0603143c0a41c1b1001c1d03525081102400c4030f480b10340050340c00310510001c110300910030401ca9022038020028003011224100c1c5480800041e10030741c10401c84100810b2003510300910181d40f0452281c20040050300000b1007484080c2c0098a00715070100e0900d0070b908000c91559001700001410030f00c52032a59000a004080001c1d0003024503032929400d02000f05240340e000d402d414800c065038240b03a08070b40c0040e40c4000d0002c0d400841d40c01c0420020182c180501280e010300105100321009981b070b82c07036000140512460010820800c100d80814540c180d200b0030180c1ca108000101d2644d240c44072181402d00441e00d26030480d2040c0052 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 898418794 1250 898417544 898417591
    0x1090813060c0b01050f120102070308100923070c0f0b060f030312010510030e0f0c2d0411070803010e010f0621150503030406020a06060b0705070e0424090308 70
    0x546045480850701c0f006c000903446e001c0740285040c441492072640c00440d50004158010080c03d101b0150200f102501c1e542d01c451020503078401c0440a01c820740c1068110090000c0c107000e10768041040d0030b203413181a0041d560b09401014840c0142c850121680c01d010b00e500d400803002110309000c5000350b0500301143c4500160100c10f100e61446002c5008510540e140260841e440d00d2403000c003960210340a504171640c81d00d9400b41d10501ca5140c0312441c400c44400c540301031071011010f12174413175540d0340502800000c091031082403480c44000c4c040003001070000e100541c042c102d14421070b0107651409003a4100011070f0341110060048040300c1c802617900502e4150032111000f44089080610401502481d10541d001140c01d07020000e40420b455800140315110a480341c101001030720b940708800c0429028500d00100b581c0c010203401c1002d590400000c0f40c10501a05d80852245030310a0f40c401c2d03040d20320501c8150103854800c0c04007490303040f4205a50046030441004032500280d0710 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 898420044 1250 898418794 898418813
    0x15040605012a1e0605070f021b03070f08070303030c0801060509091b0f2a0a02060d0e190201020c0d0b1b040b0a0c170703050307120e01090813060c 65
    0x11032000e00440d10080c0281140780c0010302d100e5600b0401400365200f0203007440b580f00c25280004c0d18042d04080204104a204c2c01e40029801c900340c0c05462040b414414910203004014440c42d40752144800c04500124038801e180000c0c48608010269203156103005410380c0d40c044036480a00c00c00d0700c0108a000d80041c200c501c4520115810b120f0384d6100c21840008820841c0e41420008000c12076035900c40c40705008000000a550910752035000c3c081640c80c400d4600c03c1040001e82060a00c4d40060604c60701800304252f0024020a01c8e00c516190513151001e0980d040403925001000c100c15960107002000c0300c0329065600d075602a0541c2c40d0000510800b40c413000001c40b182195101030170f0a07009079009040024105581e030200f070b41005050241e00b080603110700003005032420f845455907048440309580340c0c98050031a501c4020548a03c040000500c80701a00d0b241841e404500c2032050a083c24403411a058451740c040c024405409040d802010601500b028200045440042d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 898421294 1250 898420044 898420067
    0x170103120f0c1212181e08070609151103090604030e0a0f0909060b011b060b0d0b0a05010e0912090402030403090b27090610030903020c06040902031504060501 70
    0x18014000401c6607021104a404044080c001036001c059030601264011808000d120000c102402a0010450090300e2840c0c4104000c101401040d4580c0200706460020004940101601820000d01d5181da06c03d9404002c4d04581e10032002024001c48081886000c8202e05d1110f0f45600b1403400c0c412007591400054800303401d204a000c3e84203596903441407520041c10b0220740e030380d444a9030344187d0009890b020b08c2c00c0754500c1c184030004100354031400c0b46220080d400031100e00c5a098a45030103008100020aa40d00310b82d00d10100004182106862400703050003401c0010300c1d40c5080d03100207094402501100c540d41160030004c60307440e142401d03101051811140141c1da81c40720324041d5000441d540c090007490001040300120403d0010000ea00b4625131042d0b2001642e1240c00c010402d002100ea19038040720b101c00b1981024425400328903054841d0044500400c20350b0b00283c070340d0304644d000c4440780d6000800c10401d03109400d0844268039041d00c05000700380c10080007801551500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 898422544 1250 898421294 898421297
    0x3061e0102060f040213021c0e0f060114030a06110a0201061e0504020f0c0d0504080c060f031305070503190215030108031903020f0d020405010f0c0206030711030f030a090317010312 80
    0xc0f8007203401e56807004c50100d42c0300b60030070003196548241c3c07040000030a01d0050f0201c840e443c0020341c0c600704402050390306820207008042d04135070f801c0c00c00b0082d01d03000b621840b907010301c01c400c81c000003d03100e4859900031502010180c1e403980c0101c6002804e40310070790044090701c00100c502c0071032080494002401e0f503004403000341c1c4582c0d0b017905001c1c10f8050760f40309112030711911340030456032900306000304207445108044d01e800d60b940006010780e03032003108070f04130100c00c08000080040b42c9100004803840d01c990f00390b4541e95031380c10010303241206006229200082d004081d50071031a01002c0c0d0f00411224560b118107643c58400810785a005032681c05921014401c481c87c080f0348a030f13044807e202d0151000580318030303070540c2c1d080094000c0e01071140401c07900d6119941301c60190b90084465507004061340c2c91555900000c0303072480ca542071805c08503c0217101c041e409404400107103104641d00703000040c0071811801c0c0100380710201c008111840869000610101c1c142e40c1042d00030681c01d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 898423794 1250 898422544 898422571
    0x50f031809061807141e0301061418040b030c030114011e082508060c0d0e010504051e0703020604090905060c0a0c2d050106061e050d09020103180803061e010206 71
    0x4403948600c0c54802c0852011120001940201c6d61452100c090340c141d508681d6040300072451008030401c1d92040c0206070058451301d0ba1001501d06d880c0d0420a12050090255580b960b1104082400d554a40c80e4200303081a0700c40040c802c41007445010504184242100e401103407502d0304041d201c00c540500400b003140c2e078141d804052552407060b80c00414900307049442c1d52804640d5240581c02c11006459281c1c2002040b4940000500802d4040d68000016083c130300c007000b01d200b1b44104400e44203507003030050000010144c0d07620406030008000441c1c0100381850036290040c1884c00080440401010501410030250360005100145580c800300b01410720f001261400f601502e07a56240c082c104a00e0300701000c214041d08210115505030f120300c0750040b0580f00f25410343d0540351a4800140044c805601d141d0219040401c05500605001690442d40c01070089a00d64160040d541e00c42c001080c4445400c103505103580c0c1410006029810001c1d41c00002c1d103401001c0c14a031340307490340d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 898425044 1250 898423794 898423817
    0x60608060613030c0b0a0207330207081902030601050108131104020d0f0b090903310302060c15010617010e06011202031314030c0706050304050f031809061807 70
    0x2050110043c540000306241034682da4170120340e05030710000501d0014007491400050400003000c180038203152910780340f4004503980d10045400a0400900710442c41044000100c0d01c02c07d011080d091210404400f40c1d1140900505150900c181c0c01141040108006c02222520086441106aa10008000d080c0c04941c3c00900a402411500c550480c40c1041e142c002c00f0303281e0701030039107400241d4800159a88050001c1c1e10f9014009038202d445140401842d9200071940c1034100f1050140c0d50b1030700741501da80100c1e8854001020041c3c40d90700540740c2050046101003001c2c018a000d14041c00107000c00049001440c0041c803401c141c208019001c150580c1c042c0300c0720306914120305000c40d12460f240a51070f50104440c0b80507548808250318115a034000801190303050b0070417200a203003640c5006403c035070f150300041094646001d800741c000072144040c4018002000358a490070f01c90b0070345204001c4880005000300c2e20a000362602c010041c42000e6466900603e2401c00a440c01d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 898426294 1250 898425044 898425067
    0x4081c140c0304090c050705060a1b030e07030f03020102041e0b040302010c021c080d0b01030212060f0d0516090636020f03040503040305060c04030b0609061201021216030606080606 80
    0xe9421130404a400c003800032103103035800000342403842d004408032a81d43c0c84025802c3e0442c2c107400c04074002d0500104402c020a4000e42092510b0800d14044406075540c179103550300380c589088402c500607500060100100000751054903100041c48a8400e04280740c203405503464170691000070f040c0441084a00c06540c0c80c403005169041441e490782d000f08040b450300500e50752182c803407540782c0c92401c004910b1951280c03007a2580f00421501c0243c49888503400c100c1c8903003041c60300e65031080c284d00001c1e00240d400c1c40300118010700324913508a000e0400b2469015280301d40c001c080d41e49a04c1042c03e48600e0055460034803005c003031036003203401c0b010340c0f5080019218019042144400000c18081000000030060003141c0c0110300b604d9058480204124083c411444050300c217031300c100d01244292038211010b0b034000e075006002070702003e400d000080c01e80c0c1040381c190361041610410400b245a01d22801498555607140420000d410070382c004d080ba51002d07020724042c40e004140c12070b110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 898427544 1250 898426294 898426297
    0x7120f06020f19030c020d0c0b04020d0203030f0325050a0f0e0a0e0f010504090b0106141303060c02151905040c0e011e08010612030e0d1704081c140c03 67
    0x110350140c1c1d00c0d58540f03030246412070b5034110400c490000380c03400500401c0711344040391080032209a6610010000382d0783d100c002c010107002c0e000780d80c8a00c490307400c9001039504000805080c0030500700580c6074981010000405800c51078590515102152294040d540c0034040301e4401009040010504001d0041107406090020003103400c15028100031420a448090030b83c0700d408030110700b02590f0303203643c103020507140411030080172803801078010b016031800b17000341800303000c14082c8030341c20160002e00816125a603607000744e07036a683e9012507100d510390501002c1402801250740180b94144142d100000702901c4070300d6802c03260350304007040c10000c0b29030b203a10080c050902c6444455031500380c00003584800b01800c03488100044070000ba020b00c180170300f0b0200c5003050340b03c41e0b07400b2190300c0688403680302140150340b00207020f0107500041c24198803020000c15031504180c840341000081c07480c1075145500700740c806954511002100d54082000214400c00e580b103036858003c44000c45145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 898428794 1250 898427544 898427557
    0x50c160f17040306050c1608180a1d130506150d050d02030310060c080301061b050609100b0913030c1a0f16030504020a050603360d0207120f0602 64
    0x20300c8181d08040203016040181054a00901d001c0060303446150100c0001e10500d051068032445200f002c0b070101d003640c000742000b0200480b241440c5030711030f00029003014498101180c0c00d86000580581100e50622590380300360210716030308203800c4903110341c1c1d5113420040c01c100c80701c1003081d42482143c41c2c16113080c0c0e000b5402000c54550142d042c6000c0d40f681c20485000311103188003c00011a24420401c124845404c140c10514503400c28604903026a1301036060344140221005003800078108000a0340b0500750031014004003d40c9840a0050711620741c2103074410001207041c000c3d83e00c21648071401640c0d00d81402c1d8000885803030078010380f0070445040c1d98030148410400021138141100c00307101d10196401c07003102e614250801d4044880c00e0b500650824003003d003d01132801d00314009e517000a0074211658035000011920141d4152008805c28015018050740b10035117020400158241101c0c0042c100d0745091010403c04a500c2807409892400d40c20110000d1100e907504940d03a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 898430044 1250 898428794 898428803
    0x50c090f13200a08060d03080408130308070f0501110c03030f0a150321110c0904170d0f0e0304180b010e09012d0602030901110309090103030c050c04050c160f 70
    0x2e1a03600e21031041265081071100c403022480340300c001005440e003ca266070640d60315480d02c40082e221500c07081e21503040030301e2010f00440050008408a61a003000d400d115104203414010580985421400c1d91030350759030002c84290034000c0a41f0f01c5070100c1a2644440281905045541c03000060005007030f02c0705485000c0b0954840200501c00e81d8081206030310b0056455410803500080104c0b01c040d949100300009030007415030f044552500051032078005001d41d14600387c8492580321705c02d095020900008040340d0b1810100c0340d0301420301031800320034500800b450502d80f520103001503038103100c10040d860070368410203000568081c40b128001e4840c0075010103c503613100c05141c4a4013401d101c210321903549100009590b603030240f8088003518801d50245041c4080b40c4015113503903449070303003c801a02061010078841d131110b031030382030081d8007c1c2e0325400607a0701c0713007402070230321141003400f900a90a02c4101700b1081d40060444002c401c03078012a48440360705082041400711407240003030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 898431294 1250 898430044 898430081
    0xc07081207020705010f0f110f0618070b04050a03021302160303020301050310051b0703120c0806010f09060503011208070209090f0c0406030c050607080418090303050c090f13 77
    0x36100480e2501032032007104075408460800d07841c3c40040d1003086030300d490880000c025505003400e136846104260b5070306d401102186c0c04014901711080c103180040b544102035144005036075114500400c0204010500030048510307007411710700441c11101c80c81c00080d0040c8a03095082e02914010750465034481c41071401d0007031814043c07600901940c02071080314403e11a0810081c2c021455114141c0101c046070075060108816844040d510382000400340c0c01e0041c0c211103001501d1140c000d0199020203669110030510744840050010b0905032403181c20845140d200340b00880c2c06c801200c1c1503805024103140c1c3c3c003c0381e2424610502c00d5450094011640000384224800e000604807452207640007942c00800c03441c02400126061440b0241001204000c20081c40c1081801400494010880d142c41c1ca5211a00072007288201406101001d0ba20800f12081c10b6141c8030f01e54100007441d1b0a1468500034400107590306411741041341c03040d005050501c21140f00750344482c414525420b5401d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 898432544 1250 898431294 898431307
    0x61306140c01140130020f0f0301050f10080a080313020a0b0d06092d15080f0303010602060c04080d0e0111070b070204050a0b011407020d080c160905090a0b0c0708 72
    0x443c02c00002e2007001070384419082c088401c4540c2852065807a45120302c0f898003480950204459801f000e15810f400c4440e01c2e03517044054600303006140c81010b0001e04501581004000c00c00190425842042d10390030804501002401030000c4a40112462a1412034031500d400001d40545145e071100c0c40c14000040d50405180300c940090013210a120342c1080920449410440301c014054210400a40e60556013242034000b03274480c104001c51114001030407500c2c2ca4402e8501031034210000001c1d48080010049650704100b15a803205040c01011305091601c45000e41d10794401c40e0010500c00c1c000c10b404801e034419005201041c01c010104c41a01c0e6403685c021036517901512081c0e000300e00b400001200180315000b07581440b030041e03603048920b00345110001180d411000d001c80e072001561900601081e52040548019004900504840450f4030080071400d44194819403241d818a020021400340c0030540251940d004128141e5903515005a0100e82c400c1000c0104403013404940c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 898433794 1250 898432544 898432571
    0xc031d06030412031a0f240301060504032a03020607062009030c0604080c06160605010902031e06010f051c020a110f03040f0506070204020c0a061a061306140c01 71
    0x10011201c2044d2004c100b00750705c2e11040316101c221084031942008034001081458107100c141d0285009905600c40045088401114010350082c0c0c041d1000500c003107000e205009031801c0c3d2615194034504184d01186001041c49001c020074400070b841254003141e000d0a01c03000b40c226030035040c03401c1d0b4042c40316800c1d0001d9205a41107000101c2c06481a404000e88030b0804008540035144044010604500c0007020070210794054040921240c00001542001508901a050103001551030158403072a280c068800c0300e0324503a003149209400f100912180340d81042814440e4881440d0696035030a0012490402403041d00350700304294400107402c4002c9a02907002418a041c0c0270944008820b241101c5039240500d00034802c900d6030b400420401031030642c006054540c400342001d401d09400c06400d0381490701c07410040c1d821503102c400031003504804d071004e414194000c940060801c00c0041c440c04894842e80a004140003603001d450041100e88420f9840d881c0c0804002c1c4561140300c43d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 898435044 1250 898433794 898433813
    0xe1e040f0c091508030f0d020a0908070e041103010209010e060f0c1504030810181d01050406140a140619170a05010f062d050409300c031d060304 64
    0x1032485150b00b500004603c18101008640003500c041302c00504040e00092181f00950003c042e26050021036003000880c0007050000308020080290062107615150600b2090691600d840c0c6120ba44104406031650380c001c4194906584290703000da0311002c0028442000e4401c641c00600d061244642e0400881c5400038618440d034425603035140316072a40f280c0c162100350325024441d101880041c803048500c4075a03220489500100b00b421b000048541c450a00b1214150f40c20341c2d18603124080020091030250446e5000b2a103c0d000300503848104c8800110341001030b000912840480c82180304402e034401407103003e0240011000d800110701d50107580d40d410024412140d6509141810300d0350061440380030100c80401c40c5007100540368043e0340e51020406200040c10003404075012816484900c54081024415040c003004007014030aa001508205c1e0078408815031441d4204500711303404013001207125450f08008684511030b15023401c5e40c14035005059041a00807041000b444407400c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 898436294 1250 898435044 898435061
    0x30a1a040e0a051e0d050c070b03090d0f02030316030b0f030f150a090209010303050c1c020d02070b03040309050d05070312051206030610060e060d0f06030308010e1e040f0c09 77
    0x40b140c000044800784c14002d4160286400207400c0a120007203039038010002010184501010b07610816101d20a44155400c2500c0c184503d900c00814440c03111b4201440440400c014001103003076141c204820141c600898070818101910ba03400300a180d12484125540b00d03400a055980100d00c0c00c0885540b502124060720b00c107004407002c504001c8191040c419410740143c055083c030307130850700e041d29168414010381e00c940c41519114484215200b440403441d00755607019029500040070000d1501d07000d5004508011802c10510000030b8100c1c03c1401100c0c025180140600301d14107049052094661014160501c070107020282503500400500c14000c10050003015502e420b014544d8608084902a1034001412424880c060161402c11750100e0010000ca2a1030441c407001001d4446000e91034540380e031034040034006c05030402c071268098201250301c6011443c04602881ca0064910740d0904045484070118003441008042c50583d59040031010042651700e483c080010301210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 898437544 1250 898436294 898436303
    0x507020c01140c0a060e2d1e070302040b2403041a0412080604090f0516050904080f0d0b042c030a0207051903050604110102060c040b030a1a040e0a 65
    0x11410300101d0302c2c2102075500000210000744100021569010300510b03101115022500c41c036031441039111000181c007000418035180790319000b491034501d540341c9403c82030060780c92940624541e011200014080301100d8048a0205402001c1800b09480b01007100303000c9008141c4140d00082c0140b880002d40c09030748590342da048503070245000c0001d240340c281d03002031408810003500c00c0003522450300c0b5a00000c00900c00542d4400d156a104096030300150200d80c50780002160400e61081103d008004240a82c0e0020042c5001e81e51a440c3e44a0b0840c031800c1c08101140110b45c464569000700c20400d4044c004200040d00d00d130341e64000403d00c1e0803903441c2c0360140c01ea00100000100c19a0582070081c0c0040481d00d00b880d041108c0c52040c819080c06035040e0000000128008000c0710380164080c40745000ba8910345400241000801400d00440d14410041000b00803543c404881d40005590000600381141020300210f82c031410031040c1c1d0043c201514804034500205e02d0711309481c4036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 898438794 1250 898437544 898437557
    0x121002090a05061c0f1e0b090a090203070b0a0207121a01050f010504140301020c0a0f1205090a0303030506040f15140d11090408131520030406031e0507020c01 70
    0x201d4003040b02910a440c866003140c02611030594054509401c4503403028681e100c013081501c0740e424110140041526174030215907d07004402480d08001100b1900150b44e15030030b0200c9089900800e43e18100c61003414a50000028071000b0325209105460244c0868601c1c41c100d81035500303142e0b0621400280007030810781001c1c000507461901406641100d441a1910360a2a103440075042460001d41d200a8065408001007581201c0520012080900c1142d403150740703580b10f090200117516400301207000e01030100103214560b40c4d1844010216545468041604c0d034810b800f040c01b0b402e0b4592144046420b1000a03e52813420804103010b40c4c000380c02c40b0140310f00d0346d810060381003120140900843c0b44010100002e040000d102c0794818010f454035886c000030310b0b2a1420f20001076010354101561551004100c40d07004100151040d641c42d206e080d441c00307101006880c2c0c0300c0e902c5180180369940241e100b6528800c2001405032410243c00c2000f480e0404029403035030007440b10140050203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 898440044 1250 898438794 898438799
    0x6010201232d0c03040c0905040b0a020307030e0604031d010516020f03120705010b0907020c0901150207051f030507020d0203030f100b0304030905031009020915121002090a 76
    0x9208070020701110032004103001c545070740e00302031444941d0759420440300b940b040304020300703540b401401c0b4003031006001160b5803441d16003000c0780803a2880c1c02c44280c40d0305100c10b00021950300c80d0078607041110340200590381d448401007500109941084a44140100420402855041810300103818808186030f00120a44801103e042c070900407122030380e00400b0480c0d805414014003400c01b01201400301c0e05c4d400d0660300072a240707400500381203a05030f46890180e0718904203210f1440d00142c942c0002c100750048040010044d0105010714040d900c0c1d0317000b0480c0614404c10510004003c064015001d051062165003042c80d02040b142000c2f81c04c00c004594001d01c0004e1010f8442030350344c061070442d15090810103469030054000c1100080015001c58032040ca5002903001d00d219484985100f45021306041c24148000c011589a901d030402e0303100942c82d15003041c0c1e032040e003c1058959071407525001480100401e40c401e031b40791040003030141104d44107a00501041d90201d0781550000c1e07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 898441294 1250 898440044 898440071
    0x5060d270213090507030b0403200a061a060d1e0905030d0e0307080a18170a020306061f030e0a0f0b25050f0d0f0c121103060105030c070609050a030806010201 70
    0x2510204014119400505c0030804995410303403484d001342c07003881c4c25802034a14200c9080011500d9042180da500014491030410403684100c0303042841003500b022400e15000c00040d854001e0100440b0b845858000400700c4110340407035003a5140403c1c0301048000d0300d5091140d0390350001e14001d4462032030001005c44032540001590080d9900520151428500140031103186a1019900100b40ca001c0342c0411681c410706505280c5605640082034601d415004062502c00d02802190142040d100c1000ca07020605410020b411091304010803640590035003249032a914840c054442074460308940c04015209620b140208400174031500103170840c00c50b4002d481c40f9540f8001c082542001400300000c030800c05891020200c550005090f01981c00703143c162501e110004000421880a44d14102d24a201ba10500c407a6203640c10708502d4980300284c010703c0f0140140040c2c0101041300c80801110307401c91464a07a1100c00e07501403c0580c600500504000c0e90281d0255091500c01003030070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 898442544 1250 898441294 898441301
    0xd05070c080307170a1b0f1b060f0f020313080a02090109110901080405032a19021c0c15031d0d090315150b130e1005060d270213 57
    0x190066404019030002c0819038489510070384041c0180036101e40c680c2d440042415424294074007441641188110602d004541141c40382c0300e20240c908d000f4420f10480b903121420403000320850801192a48004c4426407460040030105c011400e040364000c030f5201030108414208074400d888110060340c07100d40810030f5555900426000d25018070140b00749602c00d8045980050241c03090301d107812040c084032410f864600c0c0029081c0364410040e03c004041c100261210110080e040e00b26541c00e5230f0011306101c02d02d01d4501c0b410540c0c45120800d00c00030440c107000516041c6a114401c0005c010003130098900010403880d05d10b0341c0f04640d0101c8101282610740d521003503440c140d0841c1140d4612200601c201160310348c195642c14080e01c01d00201080c0030160480c0343e05d45171a1440b206004441f4043e41e001015001c549406009040c0c40d13819640c001d03103008540641d25001d10b4540c6000400c27404d841408001c03034200101300071000100707084480d203000380e441c00c0303240b100481c0c26401d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 898443794 1250 898442544 898442557
    0x5030904060614180117090c15120a050a0b0619180311090702010e01020412050c04090b0a0e03070606270204180e0120030109060905060a03060c0905030d05070c0803 73
    0x585010440500306482c0f500d115a802c81c01410200c90b80c8074000b9414026400071581c1c1f040b00e42c003400b5522524948400c44540150403003019502d0300c4403080700a614044058410206540c58601180c0400e08640102100321005064070b510307203d49583c41002495132001070310104191081785404482c0310744241c0103807500a00c0a5111b00070380c0007403101c1c0d244000d100c80119540c4520a1032424820700041004011050230603148040f1824614207044203000180c1c0b103a0300e400c00c04000244810381c100d070301c6011a00c000918904241101d400d5119007200240114500400820002d03240320464060300c0a0f134111024080c140e103200c5089101d68002c00ca20300b49207102e0310113080d0f0b49030411070707219840c5000440d045011590342071000100c00c1c882881200007000501c20061180f0584000f4000c0740d10500c81820402c012488881e01404058183c50300c9076407405c45075004460b414001d00c00a02141c02c040d14070240100650810314048500b0907030b00c50001403150001054540c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 898445044 1250 898443794 898443827
    0x5060d1b0f0e0c12040f08040f030b1e011e030c0b1b0705060f0d0b09090d2c0f01020f07090204150908070e18010e0313230111010b040504050309040606 67
    0xa03080c0000b00904d0741000080045512111403140000001c280c0e0300680000c00d180e40820190605510b041070200d00300178810f000e00200d0192454008044100440c112020b804026604429074425000b4444c0030b5000980a00150900082d0f002003040090403401c05c40c030840440d6401c403039500380d11000c031445140c1e07010406000c1382801c003080c80020702542015450010724107200d44080384000c04129a00f001c00d800c480260702d0418ac208400600c000c1d00700070003440d44029407066046c02c0715403050301e90241c961840440e10a9000b00040d01465a80c80c0446103819503c00c000c0c00654414081c103510a480ba030b0402048501070415502514558406008400c3c140201181607a400400c086003003107001c0c2e08018500c80030711078480e803030703101c44040d6541700030045840c010310200364801003841003a248540200380740c0900491090401746030030280c9a820540d9a40501950024030360320900e48405c0c4000c0040001c000c1c000c0203800e40c0c00b40441a5645030581d12039044411013071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 898446294 1250 898445044 898445047
    0x9020f031b0a170907031505101d15060909041407090e03121f0303020a032003090d0203030903070b13092a052a0106080309030a0605060d1b0f0e0c 65
    0x21000040c20800c0e034840004021107040c51b56030780f103801160903580e00d2594456565018000a41c001d0500fa00c041c18410022074000c0d00c41c5035031040001001408203d0b5408101d03516242e03556450121243c001000700152107030708003407c100c0781101429000144a1050306000520307aa0b460290b03400b0441d03540c02440c1440c00c96131134259159030050140a09400b100c03041074044003901e03500d074040c40c025070051102c10814a00900350348100301003a045481d001a240d004240000104e84a005098945c004040c602c0c0c400b00340345005420038035605018003d00810f03520602409050200040f41001b440c40e0758a006001c1100d190b440144007141000441500048208000304141485860880c0c540b4980c050000390f200d580011070540d09070041c4d92071024080c2406840050850031000c1c51401c90841e001030740e00c2184281c01042151100300003410b542c0d83d0182c03101c1c41c503042801074001c10100ba40303420300b1121500070800600000a00481c0b00071440c01000d20910b5122443c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 898447544 1250 898446294 898446317
    0xf05070c0605100305030c070e011e23031b030c1009031712070509120606010210090c0b070b0403110111031b0c07031209080303060a0302060a0909020f031b0a 70
    0x5001c0e01c0020301401a036143d902001000460810040c9002c000a00150110f6030a1441c415405001a8800078920035002c11210b070b0001c489003c14219503034000785d500b08000304a6414040c80000291990501525507000021448100c00800c2004110151058180d290040040b118104005407002500100c410f2002440c10001e002034407103911174190410034013081c0056540001c9030030500042010078032415500741390500e960072801c01c80240461b07203400320000356514a460314804490b61079080000c00c0c000c0b5aa031401c040c008103045240c0d100200d01303004103d41c00aa50440014480a201707081c405418803c5452010341c49182c14950344031000490608a040c2c02d85441b0301c03c04000403c0707411020030046004520500320a56030020821001e410702165500000720380c1c10400030030445035548d02c0d500d42540c0c0d040b60300e82d440d10f11400e021036420010360400e4511900c00103802c000c0c44108005948900c4080801040c140121401101d41d4060360700c02101041d40039914 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 898448794 1250 898447544 898447553
    0xd15030c030f03021204081e0318011b060906062d0e0c12100806071b02060d090f11030d030204120b07031e021201170709020f1b100f05070c 62
    0x742c1c0c400900030320440c3d0031028075011250703c55206901918055100000c1000350300f040c40c40021802c0f100c24040c6052a48041c4016811050f900800e4100059070500300e504d16050701c40c1c00703c620380180041002c4045c9261017030040c41c041c000d1784c640d4058420561000d14211580c00e1501c00ca101a600090349001080d000110014066145c8550207000e44d102210303044040c00d03c5440340300c40303001000b45010865401e21502a000c0d03400c0294440d4101c140303079507483c0d0421411754141d989559440c1564040300c014600c4040091202c40341201060520000c1c07800940c014104409a035004403011078241d00300c1c882e912540d02c5419000c0240408114000070345039001b0100d050204091207842c803490b11041010303c400460550115201c2d0000c1110365045024018001d98201240c510310026030f59a2803e201d22440745070001416113000b04100103441780403a401500e021200380013007200c2c0c0c179644061400d05030f40b480d001201420b580140659401000561942c862034180c0380c44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 898450044 1250 898448794 898448813
    0x9151a0f151602010306030614040b060102062809120c03020c030c0a0302010c0f0507060f030b040c1b05010e030d1407080402150d0902130c02060114130b190b0d15030c03 75
    0x20141e0501d60341b83c5000000c103075a8060041d44880c2c1100050f0546005c2c68022000900500700c54110342c0080d0800c900000c0c0480c451030098100140079107030000d009403060103410b0154004080c400e40100400350340b9040003407803d80c14801c4e0203690f220620402416607804001c103100340c0c0b1070310b80401007000d5405402e680b0400c9008150b450140100c680b2030310301c0d0a0480e444640041e0201446095042e070511a140c11800c045800344540072000c2c40080c00700c0f0301200f4400a41081c1480802041400d42c80710340030500c038500f500d03120303003000c540f59008181c10a5540355a00c5941c0c0003400c0f803840707081c1043c0701d642d000300021030404203452001c4082d08500520000c40d0344d00c0d40003c1c09652601844018440c8008010517440c400c004003d0030701030182e1084080f03c8555410942e60f95501c039500305505050740c0c0002e96100c1100002c1c64901a0703040400740d01c860f40c4e0000c261082250f00928842c1c44a5105105000d2503d058241d04180c6d0f100107441002044001d000080a495 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 898451294 1250 898450044 898450087
    0x2280c0e18060f010f092306011101050702031314010c140c040203010b03090c01050c19230d1b05071a0906030f040303050c07020108060409151a0f15 66
    0x140d90303414107408104050701e8110700ba902d02e102e0030b0102004000e42d044050b100300140c552071009100b81049620f1105e81404a8005d0303982500b103880000f000750344902010503071010b2110003800305003458680a5100d500144006c1240401c542c0d0200f5080d03035040b5004003811040c2c2d5424506034460325600150b40d0241c4055425004030301000c0e160360396a0003d503029004400e0305039a81d0902403045440c081e1f080c40d445041c003000380801000810040354a402c103003141c0540c3d120f04103561030150340c2403ca204100409603100c0591090344040021382d110030713440340c1d01c8031551581101107050700c00400d000010196402880103100c00391a841e2440c6010f54128001c0c1e091100580c00030751f039a0000c0b2480f0a51402c180704000030b055042c001c69400041d007007241b92610341c0640000f8100c010043c403036400b03991940d10a07000c12001c0e10440c50240440749042000d00c0d0107040b5045105500b41c607241c4914400004444240303010340c3c500c5505405020220701c1c0514504030300d024035030401c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 898452544 1250 898451294 898451311
    0x405010c0201120e0d08010914070c0303091703010306151e031403040906030302030d060605042d0312050a020c091017010f060b0904050a1104090b1f02280c0e 70
    0x522405a504c1d5041100d10a00811030701c40e860650304011196044509460080d14071440100502c00007030380140681914641601e0701040741c588038144014078400540044058a400000020500040303a03c00c0110620050700526031700d07030b208001c4441890309041cac1c1c0c0070320b2000003003040020701c04030821002d03100301000d0300d09060ba1103454608a03a251750046d030240e0070001c2d2101031031003181b003070174003400c2581030290600c3c0c03c044404e541c82d0700d07000da8010354400c2560f8518426028400e640019035101c41c0c2d502c00300008042c002c1c1a50040440900944503035402002145051450b0741d02c500c00c01c880002c041c07031800c0103440e102623050a0081c0155619111640071042e20f00841e000382c0601408160b0b41e0301d02206200841d500203100046051504c500c105102e4806002c0b0740460742180e00100d60362000000184520340c0258021a20542200c6040302c201e401141c440c60415401c900c2c0303c40300604503421200000c8901008240b00c585013414000d602c0d01d14480c94024000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 898453794 1250 898452544 898452551
    0x24060307050f1e04240602010e0a0201030c0507022d06041404182f040b13020f12090706110d050a0c1106070c1a0a02120d0e032b020405010c020112 65
    0x184408242203910040e003100c1c40c1200c8010140241380003036070f444020106c83c0700811083c030812030413a856148080d0028109a218254801840e104c2c02c16500c07002e4004101c1d8018665410790036010011004004401d1410b914081100c2c0c034001003960101c0d00580c500102c515168820000201150060b6003d4084081110400300300c071a00c0c00b030fa500c1001ca0a0701034520b40e480143c940903800310b02591086060060f520a035803603c0d01440c1d4800c01d07114000d0713102c020080407000d1700d00440000d0b445202e5201c04003c0903e400240c982c040351000c1e150000001046801c0701d07203902e5441601c0c4040f40040240b5038505215480e40900c540c0100c0d0002e078065802800110301e903118032803c0d1040084c0b00000d020019403e005105450018a00c0c94500128001e000e5140c1d4101408954050004900b400c05041d0b0f9820000c002100c40c42581d0b03444d0760000409144114404248034804212044894110040c2c17003241c06641d01612903070030000301c80d40110385103039080d9400508a600c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 898455044 1250 898453794 898453849
    0x1031e0e0f030c0303071b05031c0b03030f070b010b090d080304021c0501020d112b060803070b0411061e0a18081b040c08160c0524060307050f 63
    0x42c000f4000140548018558a040111005003010b040c9060414618010070501001a000104688160f625220800c1003078424401500041c06c40d0405941c040c04005101440b4240680080c80024801e5100c0c0348603980781c102c08040e5010303100150343c102060b0b0040c0400318a115018581c0a4401019002c8066005c0901280c281040c9000c0794281e40102d0f600301c89400e5406485072600c5400b9113241071050107180f00d580c0d10144202c1801081100703c2c014a9809150040c4014002080499513260301c0352500c1d036800e020854050b00d0010800c0b10030b100d949015022a9101d10b00303402c0384030414030300948451180c2d10880c1600180542e03150640c040080401c44180104040c1c03010300750034090140120903818100c00d84c06c0c0326502d0108080e0030039412a800d960849041c80300d50308011820300c0d003510006801e01000d0950300c0f40c03071849548056070982036120b940041207440990340351101490394500c691b01890340d005a846140494608046d0105181000aa00d01004004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 898456294 1250 898455044 898455073
    0xc0f0c0f050a0804080c03061909050f030a02030424020705060d1d01020408010b040b180705360d0f061107020d12030c09080c0f130c0f030b01031e0e 66
    0x2002d0880072994444007240030486004140880b0041d04410f401502d000e181880d09580d104919002840070103907250100710521030200102d040462903803003240d5031441803c002968a80003845411258410f905131913500c021880c1007034214030710b240c00914840e0b0414082113415000100003c42e9103660303c012000385c0c004400010500c0c01300c07000040e030392424400558207490905000301d0149080000c100806e132244600c0c500d03a803141c03c41000050b11404411100e81c440c441d407801000700802940502c4c208565040800060116054400418180f085c4480300d016000090500051403141d80301049098201c41d043c0301445a0f52484d092190f8001f404540101c002901c0c4010341c92034603041590180720345444070600e07081045000385000d001a680300c0b82040d40ca8050310f03040061804bc1c2d1104c8215003030280098034248000350413088000c14044c906400400003a0802040c2559540a40b06030003144055404503d00002c0c10149034000d4030a4000c422180c0c4500e0004e521500e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 898457544 1250 898456294 898456303
    0x6153203040f0c0503240c12041a06121c030e0d030203091e031b0a0210080601020d08090c120a0203010903090311040b13050a06030b1303030f0c0f0c0f05 68
    0x503403040b0700042c011941c5090803520004540c01c854020740c4820b500c856440d0301101b011000d070042d00000c50b05c035078400d0752204440c0244d005481704183c100080c0410040c002d1810314244c07071521901142c03595420704006000341102190358090300000e0000c00040b50011804000c501386003008980b1a083d0b68110380f4002041c0342c000300103a404020300c1740741181880502c83c40242c3c414a08455000d00c4105516440fa1b000c01d01c0c0000003519005094140c103210700d034055500148801c0c60541240e001602c0c548088861500600484804d0b4113050700448007140118484401440c3d101001410f0000051000c0b5010030280300f8142d1040060b9400d005580003188250780f8288520310711f2030441031550b0440e80780b5210b642095805071440d02c400c0d0482c002e50200c0b40010619440344240c0034020000b5400c0900115550030802540c106000180b88403503100355410001003155444404c1224040c00d4540700040c0600c120800e44c0744110f9910b0900e86c0100c0c021581c640061f5110381c0361 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 898458794 1250 898457544 898457551
    0x702011202090a15120e161e0e0a05070210091e03020307051608100b01020d0807031415010f230a09210c051903060f0609020304060e0106153203 64
    0x44d6205030f11605c9069240034952888000d10000d10014501e6182c03030f41d01e001c0900403400e00c4003424a60034452400075403110000e00706503084149a0070b0100c9007101403d011035003213016215107500301040e00b189103e119205500501002d4007029801301480310fa0f08400c0d0103404511041c0014000320301d05100403400d0a03000c0c2030f10341405181481c1107040c50009424045d0040c40c115146509903008140940b040c5420302c0e1a82c001c0c0d030341a00c2a00245004071641103514a071204019140110b621400724002c0700340c81d08080c01925000458083d00c615622007002c00010400740003480c1900041e0035030084904000f2103d9440c2c0c04041e03c8030b81403264045a00140c103c00c0400d00134a000b901c40500b0051703810001c032110540b2807401e000c54512000f0180c40d40c40300d02d080c810440d07900c640043d111140096690b800c1a05145015081c9401408115480e191000070765203103400c505a0840016200c030303a46105000306040c002c1c002120903010400780101031a0728012164000d512 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 898460044 1250 898458794 898458797
    0xe0a02090a0c0906020303071d040e0a0c18060f1511160e010e0103030206160e04020a091409010f150905040c05030a05010905241309030c06110702011202090a15 71
    0x2c0c0341c0003485004141c0d9041d5070041c419504100148040503910980351000c41e0070fa05061102d08a4050204006040c44230030b5862601510700c40c5070410030100503010480d81c00300f4051481010728040c4404954052107408105056840c0401c101c0100d44103410103856942841c0030b1040a4560850800c40391107100c60007088140c07000d10403400c4c408041400345c44150300d000960342c11a038001c0d5440300060405115000c0810b41c2c41c00e0a4400c4601840d119800b038029501d502d01d40d800036000742000e0241c044840c9406903410b50724201408541d040b100f02c0700c1000d000528000d03a042c120001624003c04004a00c1c81c08100d40c1c50f54003e1101040040d40ca40b580c0380b4002c2c010008440043c3c105c182c1c0141400c051004405104241c641c02c00f010005d2804609800e00009142405000c005108241085c1071207090540101c4048022401100c0500410b0b1489050754034901caa24002808122101e001d03e0325035040303902404050301c01401c0d0708481d070b4039400da40e80c0c04074520b0318200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 898461294 1250 898460044 898460051
    0x150405180103030f1403060409050703051e06150603040308070504120f021306031226010807080708030a09090515220c030b06040302040c050f0406020327010c060e0a02090a 76
    0x1c10113070701c00002010319690b072414064810f80840151468403001e081c9912481d1540c1d5640f042c05407e0040c0002980d00c1030807030f01c072950541c44049210040c0100c03564580161400150b0320701e1404810302540000600a602c0d41d0f682d1703070b015507981c84003400380340c20400140008280c6040c2d501c541d19a803401609002c01d007061900c100075082c0100044042c80c1c9080410400000c2c0d0012607030500c1c0c807154244500710320380400d515160010b00440318030320003000c00000074400d1404110241506d1156042d0340c05c280e01d803503219549104058003040000c40701c1a08001d80b410a03030000d50440000720002210041d0103000515505490060008100006c100f2802c2d6403000c1c4140b90100c0042c0c01c050100403001000180386014600c03010780156101c0111001c2d0500c0303041111445032040350100e0300c0303544540c80290f0303903000326a1001c0010884001240c4040114400c560b20103c16900c0107428102681d8100c082d00d04132072042000d01c42d03103045034010703507800d08014801e00340c500002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 898462544 1250 898461294 898461299
    0x30c04080708150c0903071a121003051c02060703020d09050f0c0a0801140117011503050303090d050423040e1e0105010e041e0f080a030515040203010506091504051801 74
    0x2483e448000303840d00e8844c00c420849100107480125a08044510081141803105105a840d880e82c2c8a41c06800d005507032100300304865202c400801005680c0950200c5513541c0c003a000341300d007151000c900c00000d42e011100152216110b43c0051400030100ba2012074a0507442d9240c41c0741000d4010b510003950001c84451015003401c4c02214001d202010091002c5858441e00000340c0b0f9041c010340b1403005040400303409801c8250840c00e6000c020030100341c00f04c1c1c0d5034280180c4a030002d441c040300074002e003012443e03498865801c0e1000c0c0c0350003440c5d0344a0303807071058007403410f05010000340d507002034a51807221201c0c1030074060b40521200012903104100548014142103070030503040000744816507410301012035010307aa2504110361004d00030209211f02d040088070140724501c0100114800500c201e0039030780c541c014074002d410140188102252200421050707000c240100c0360480c009100051161a200c40c104410342590104030f45440c0d11040410038540840768400801043c09004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 898463794 1250 898462544 898462573
    0xb0108072c062101020a120612030e310b040c2a170903280b09120304121e08070c080d020309010b130207021e01210f0b010c0b040305030c04080708 65
    0x100b45030525103d02300030450810307604107080810078002600308440304c41600015200c6140b54921f844401020503580900303103c0e140c140d0080c2620100ca42e0b4101121003d00e4145401200c54a08a43c1c440c079032000c400060107040c00c00c0440580c034a01c2640c1c04120042041250940302d42d00186003010341e03400300340c41031620b001c3d08081d0f40049140c000030f1500c888030700f150103104130f9a40014401d17600d443d8403802910341141c40407134040340480042030008101c0c07155000c0301604000d8880341041a122140300c00e01040301385510f4040b9150b5800144001d03c209081c003c038078802c5c2d004070f0400c0001e00802040741c00464010011380e41d030b42da501c441032811015880070041400c1c41549012110381c0401c2c0754228044035031624452581c10715034240c4c080d070780701c07860364007071010700322091480c1003002d00600007a11f40340035810b1420f03044403003551007000380d00e40740d43e0007410341e607141d450300d540880725903000901d0003240c182c0c10b10000c55298014402c2070024010b05c401403100340b40c3c0d0400e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 898465044 1250 898463794 898463807
    0xc0609060c08101d0c07080708040b090f060c07061103040305120702040e030c0a021003020903010906091209051e1f0201090c0f1202090c0f070b0108072c062101020a 73
    0x14a013201d0b0000031100349280644602d0717022a00091807074440c501031500e955180910b18000707001c04070203e0040350b4045048080c0104603805c07100400011840c0301801000c1c42441905e80444c0c010311000d001ea603018115080600f65400c04987c5007036600d44071241091005080d0460203100000d09409514050140701200a20623028515200c003240340e09680d002c0009000780102d500c10710703690700c02d0300942c140d5640e02800390003030080790701c0e41c50701e5001042491403c94105d42281026100d080c4100c0c1a01c09451001c1c044c00309080c0300251441031025900d981d85d6003c09500c81a41858030950001c0642982e241c00105588072245800c4041d290540c0007040000a00d41c001c1046c103088088140c1c00b1034065800107100e85840d408038445104991840c0c4402c1d0703000800d0404c108000b0350541c107c0d07540d501074644154a940d0f01112000f1044135141e1101e0400364503003400c49620301400c0d04503900030840741c0750100c19992041103590544001440c1d0758040b6170207002c2030300280b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 898466294 1250 898465044 898465049
    0x8010501090506030f1509070f0801021e09010903030e06190816020d080a0f0f060b12090a240b220b01110304172119050301030b070c0609060c0810 65
    0x7030140003440c51781c41c070707a85d03032461961701a81d0105961000310b05042070510071a4050442504440c0104d502d841249000c0d501c880c0600740c1c603550076001401c00e258183c065804240b01651440c0c2214950340313045400c254000d140b154040c03020000c0c2181520300c0307081000c03c0c90301c5881c2c01e0a00c4c500800805480c803032042860080d0b400c07000c0c0c41e00c040c5074000c010307035030080111100054024a80584200400c80382e00b140303140c0ba00d420800714502d1000e00c0602900400140740c41a155034540c8010348514075128001e03c0964407220f845034507403003020788040505c000240010204541000900300d886a010300c4207070b401c400512554240540c0c012000064801e0811031701b5080300ca035a4503540c3c481c0e48221a0354140e8802d4081000c03800340710030000407036144d0394004009550110000381e0b901642d581040c003030030510083d0301e2a000740140c0c6e0490b43c100360380310b84503500c600c42550050f802d10b600b1200310780d540c241c1c2000201144103004900f5001c5ea103400d03080c500034a800d41d01c040ca1780c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 898467544 1250 898466294 898466299
    0x1c03090e0c04082e1113080f0a030e010c0803130c08010207050604110a05060310060206060d0809040209150d0c031d0709090215030901050601091d131b08010501090506 74
    0x10001440445000070722120341c000e40504440414081014141c121039000c03910b030303252174107141d800314031510004c026080c1000118017800000d613907000703c01c1d618020000300410541000072201c0200e40079616080d40048181044040c4400b20390360296180d00c219180d802c1340882e00030340d07020310030118075102c080c0c03081d10002c601c0d100c010346400741c1c2e45a0082000300a80000c81c4c009409407110f021600c0189005050301e504d078201074422440031071940c012180148502e80000c0c195141001c20780840c1904020558a041218810321010798403058000f03030000d442800f030400f24150f02c0001c01062203551000504800c641380300070290342010f1884d4610000303810200008200c0410f07414221030f030041002030800c4080c4085401110030010610109001204204105030103410940c45200240ea441c8076981d02d46119600704c5005075511804114440001121014001c200e0103909010324050a1001010f0b0303038045080541d50441c4500c0c1c0d4585004200040b9075019683d046a000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 898468794 1250 898467544 898467547
    0x40f09060608060f03010b030f0a120207270209060301030f050d140f03100b0a0906020105010b03040b070e03010b120d030f1406010c0609081225021b1c03090e0c 71
    0x34078400800e000e401504092150000d01d007915100c0c3d50075400001b0301c400103001d403010010390146c050f444440400095505e001001c0b92006002c0c80031503800140d1340c501546041c0780da44414401d451030722030140d0303c8209500700920f0030f240d600d54000d18001e41c0300d00d00345204007880d0318005040180103a422018003041c0244020010100402d9541c40055030b44180d0302d955075125900104030840d481003184010000b000e0008581c04800c074016140c0c030750000d00003a40c7e40c51943c0c144d40b0045501401d1041003a0104d0002c5205501075007492100800210b01c207052000010741c404d08a0905038aa07500140f2403410b501d4050043c600075200010042190741c02404820a610070010040c03030400652408800030440280e00c5a03a800e6001440f441d21007840281c0c40c030340948181c0309229400300100345611008210381d8854601e5029501405050f5080118505a5a28900786a5200e03d0844212032280018001420800c2c000d9696100301450030120340d06007032000c0c0c5002c0a0000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 898470044 1250 898468794 898468799
    0x30d0f230904140106090501030b031002160c0b0418090f02090a02041719020418081309051302130e0a1a06010f1d090705070b0907051009060e0d0305040317040f0906 73
    0x400c2906c0804480f001c0c00c021a5030300362003000a0402802c3c40341604054404142240b60154114260001610440c03110300c12944604200700180500e220b403456070842c100c10781504102541013910850f204002c00c4086d03841b2980002c6808108550014007140d02140410048529600e00800760b0542805000e142010703817554092400c0844010f801141c49402c5504000707000c802c0c6800c284d03040b0034015202d00c1001000c0764002c0300c0740f2070445003500b090b004c030700e01000b032091603a410750340101100e56203010800100007070525841112240d004684042c004503660a03050310300c022071034481c0215880c100740050220ba450241d440c0c10099042c0c150700c1c0c44035002d112044040301c22035920b0429030f43e00324102c802c0e100d4032034000d00b2144c04405002c400c0000058810030b4903800c9a034003080e1618200e04580f071030002c0c400c260000b0324012142c4e006091291101040ca80030303160152a0503125103e03110f204280c03e40380c1d80a2240000c0070030040901400010140048081c140309092 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 898471294 1250 898470044 898470047
    0xe06060415090c0e03030708122d18030706061703040803071b12051006290706020d0c090e1b04050906010e09091515030d0f230904140106 61
    0xd101c0c050039080a07610700300c500f0550f0041e1480e00450740004c007201d0f6203150600e441c15403500016004285d8002500116010f10a4801c80d03044c240c0d202c01c02c803810400000c2c0d10094501003e030220010096500c100340301781200380000c2c898540228000304500e807401d100d030340314410710034030f85c00b01074006000600010a02004a40b0100e4110100002a041c0d0581d0300d074400c0129485142c0d203108082e04002002001b2500d052501005074040208956a60003040c2d5602500d441000304030007101c2d241980c0c0103010250114500807280142840d1100c0104812160031001c480041a0603100070401c107420f8500c020303823200302140c0441c030038162950250004c1c022405950320aa11348800a145030340700d600208504140109080214188490b40c20b40710340811007020341c3c58400d100000c1684166000c03e0707200da00d0160040c840c28141140032604200c43c16510400c02c0480c070000002d0040301c21440450440040c00036a45014039001c0000703c4410b00384c01c0c080401c03240010810507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 898472544 1250 898471294 898471331
    0x3060503060f070f0f03061e06020d020109050304060c0c0e04080c070819110126010f080102041d0712020a0e0906010c03020d05091206090705010f05180607060605130e060604 77
    0x15200d003885641d6910120042e00681003d4010415110000208c100460f031141622011107080d81c003034400070350038044200e00b65411807101401b01c2e44200320400903103101e9844051800d006207802e4103003545903520305d000c040c400d840030760b500080842e110300d40144c24040d4100405603500281b200c03048400c00012030440515014144a4000300e540040b07034020b490001c0c81061400c6883e000304400c80c04010000002c0c0100d2454140100c00810342003014822241500c01c241d981002c01403001c0e074404c105000080540c810010b02c0c00d4508040c20581c00a0171740c0a01c4c0d51200502d401c02201031100b81c04000b061241000224200d81003c80d80109442007003103d07603c1e000769144480c40c0030400f240b245526040181c400c5c13000b0081520030104000c4182e8409a03250f951101d0181000c413001d0141504418285048c13500342c0304145440c2d0000d1040d244640740125800390303100e0000c0d680e400e05449a0514544500231900c2150701030120382d5000100711000c2101890034001002c09 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 898473794 1250 898472544 898472567
    0xc070308101d060d060e150c040612180206070308040b06040501122018150d0c0905090a060c030507090f1208130314030c07060f080c0a090902030703060503060f07 72
    0x40340070756001c80c20548136005400300703050b00700303070140802070a980d4400d603621101401c030103165600380b000c119020b502d5002c8400300e450a07a06d014100f86180440d0008000010708513005500c4003254200503114040500499070003512510804e1074103080181c003031038005000328883e0f40f60000600000c100c00c0307840c010b145c4d0025000e072001d28030140b0160204001c91510307a0703c0401060703030301099000642d51900c9000011001103001c59980140582400202c01c010b040700c0b00d0201c2440100b42590096a0209110b0204d03000ba1240d0b0703c0d101c040f1080280380e140065100c60030000b10503007160315580100580340180500c00d181c0041d107190345c0510240101545000a0100008008000c0680265410068110700b40640310106540c3e83d000700b1700020b00d80181800050268018402110714100c692150310241d40c1c3c0030034080c8144c0c811105141840494940840d030000c00d0b2010710b116502c01d07100011200e06103000c1524000c40105034003d01107403c0100041550f000412100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 898475044 1250 898473794 898473839
    0xb1f032d0b0d080c0115080a0201050910050405060708121b0301090209040f050106020a0b09010203160503040302030c07091d0c2b12050706061401171b030c07030810 73
    0x441d03805120028404940300d00c0080c156420219410405880651140c8031429a07000b21202c0340c1d07a1041500d4680145400180c0481d400b441164007606098000342600c4140380383c40b030700d000d441d41d0018240ea04548810f940500000c5900000d40c0c461101c0e035504003490440d01200061411181d1074284414062201142d8000c518a107040e102da4104011000020341d0903c00d41d0303107451000b9030324851100c0588130455103c003c14220301041c42100c2c000c402590040401021605003078409602c0070300110300710720003004021401c241c2401074078003400b5a0b59010030038050720803103c800a00301403c01100303600f03c0c5d40324041e10b50321010250380101401c0d036500c003940e1010484290030805000c001e4070105c1220351810307030035500100504a0038408c6504000a076114140290f52040c0c105280b070100c1c00303011402c0344911042e0841075001c07076082c00d440e0344c40c03183c8021480c9a420580300c0078910007000c645441015084004290f02144552a020340c80740307411154648002c2d002c06d07102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 898476294 1250 898475044 898475051
    0x402150a030609020c061b0313120c0b39030105090a06080f0105270c09180a08090a1502100c02071a0d0609051303050d0b1f032d 57
    0x40c8414041d4015800600706124110740380e40003040303415250401210407002407200d0101c41c85800720684103407070003180302200c00080098a0358034181c0d03000c000c1c02000c05000c2080840000980c04801052180100c100030304400301d641c2142c80e40c7c0c05244005007491608440d0b2211401c550350007035a0440d9011514000c55484600c4010300030580342e007190301c050003101d904d500142015001680507241d801a141217204c80d50b00071048259000741030581c5034201c40411941c0f80b4050b0412a0842003008110701c00e005811440d500d0701013100c2049a20364070103d5281c00a181c8003522000800e801100c4c41c20507115510000d440b40820158000100d55940864051902c200812070192414520442c40c41e1040101c540d03076a00002d905017507031400c1071008500b414940c010a40541901c135951617480009a13025104c0c0e40000380b07040085582d80b141c2c81001d940d00f01142d13400e004e001c2c1300c0e0201c0900845000b001c0d078554032090340390548800502074009030003a84482c0307003a08001c0b000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 898477544 1250 898476294 898476307
    0x80a020c0307170904140117032814030901060806090304241202042d060824090a020715110a0c05031603090f0f0b190207030b0702061608040215 64
    0x40c12a4040c0301e8860fa0081d10700a400e146c040d02440030941038403501c0038141c0d800c4981251903550380c0300320f01d4641601d1081e281d004d90040c103103100090075481c9038180845070051004000300640c000300d620f218103a445210800c4001001d00a140c3c000507820003840c03070309091920940320f5803a1510a0413004403044076011b4624400c400ca482c2c121525030f0117540c0c031582e9942c0072040344904c40c0f2550f503011f480d501080100504c0d8440c41d045403c1915a19550f0b5a41002c104000111061841960b20152802c0380c00fa43c1300c081c4984103020342440103840b64218182031040070b0403e00d9010012385072203500000c40d5810310036100f501c80ca514001601079098a04107040d8040c88000555503080601d24004040d0801030850544580000b030020803595000d9143d00c1000510030654661800c01c980505103070709c040b500540107100e0040700c44490381ca07614292140381c101c8819006801440600c414941401a080c492102c03030b203880030340c605040d00054002815500e030441c049034001242c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 898478794 1250 898477544 898477583
    0x37120e03090f1503160f0c0506060f0d05030d1d070303090306050a0605090907090e030f0405044d04150e033301050108070f1110050a090201080a020c0307 68
    0xf0b44406a0314286859007405050b500c0000d0001c20711201050040c0c09080685104540c0b4070300883c5c020008103984d80320b901c1442040111150f000303401c40c4800d0111400b1440c1000100310900c101c81d0005003841c3d00d0343c0b440412260301a2030700710a804c040010008a41d02592040541ea0000300c00540d94a4603500d4800610320385e0301c003d4100a449003000101c9101107098003c6807040ca40c05e01c000310088034016140c0c03040032140424414148024042c03410a03500c40000404844c4c0c0d1040508280c2c2c1182c04164a46240786580d44014400440d44c680d600902041e00415030b00114145800c0090a040200081407414100201c0d403248001940e010400e01610b50384a400c0581c00d00c48a00552017401481c0d45000d100d484000d00000310342d40303d80000c0384245541c5da40c030400402e0044007203402c10146014506144555080000b06205030300c0307401c1c00b402d203003040015401081c1c40058203000c3e000384851078252061060445c40d41000c4101c6038066072103500c2d1000c44414020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 898480044 1250 898478794 898478809
    0x40809040906090305090f011b030e0d06020309032104020a05011107031202030a110a02010806061326160e1b041208041a19030237120e03090f 63
    0x5018181044045004d25070464000d000c504010b482c04441a1004001034a00c90b41260050f020700003214007490202c0d10420f0404204903004108280c000c90b60344551040c0d81061f10015071a40000803052810b24550345100450740c1c104840c042203243c02d4000403001621031090506000c14951001c040903002d000c204007455200c0c400e000d80e2014402c000703540c3d4001c1c02c185008100700c1114044c600e00000342100c1c0d000d60594a01140380d8810050164a4000320011803202040c2c20010826418003000596607001064a40000190a15511703107800341690030200c17041905036090080d09603040c1700c182e0000900340404000320944102182600c25940142c02c0a43c003412100d040102c22401801101da0002c5100c0c2004000e484590b03003441135040600c0400180b4003a854824000c1d005082281c008480c600b00705904005421340d5a40c2c640064511000c051401480312500a904040c0d00020054100040140b40000c0f580d28896000b040c2c3c071420f4580001034480d41c4661 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 898481294 1250 898480044 898480061
    0x1502011a0405180703030e0114070c120c0905090313210809030a1505041a010605090904290f010602070b120c0403020a09090519020306070c0c0b0a080a1a030604080904 74
    0xc54613030950302e0600030a400c01003041140094103041e2000720010400e815222040c3e00000f090328014500400c010031484207102c100d411000c031174000110b0302c034684200341c4100d04444c003841c0c1ea4050500300601c01462504201035100e0580041140d41d5414541250300340da00000031a038a1001c100001c4c03402c0307603c0c440109015102c2d0a00102c0068940205000e42d107e925101610f4644642038070348800300b40190000201c05200350042c0d0f01e8480611030b00070f80100da04a64402c06004040c41181100103035500300d81c2c41e00240015900c485803a28014030f8a40701900b4602c0c140802c0020500c02c807104885404580c102143c02c4001401c1240c008580c0100040c1c0503680e1801e000d0090180c086d4150b600d0b00500c2150802c1c0c0302c00030001002141c0c024090703e802d946a0000ba5a0f158030700f0b0081d9980e620200022076a258040002c00c801ca24548840d80980b41511503007099640c2d06c210080424a81043c480d0b99441c001082d6401540c03007070502d9215201c03a00450000c0c20740e03c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 898482544 1250 898481294 898481341
    0xa080f0727090609050615031308210601110c011409030d1106010801020a08011205010b030105090109020a05030309061b1606030e0c0415090b03030f030106091502011a0405 76
    0x11a03409003001c040100003030803500e210b101406141e545040d9101181c2c4103d0360190440d01059010031030b400e03003c0007558005826115824100030544814025810814021020803044070386407291810015107503520903024a040709000c8141b002081e00c031150132115506022492520040218400043d54460f8001804403040c844c04114000c3c41544500550400c900584002207483c0206008403101c1c510719440d0840d60381d1800d0002010140a1807056a441d569080c2c94041e83d036080c00b8060040d500500041580c40090041022541142e07102c82d100b40e00801c4141640e840b818240c2d80c81640401038a0340818101480b642003d07201f9000c011038441e01031002c02c17144e07015171002c5205a460400c41d810010810b0922040b20022001141500d00c064002c105040765174002e481c00020242c15a41452446d0708000080e8000b078010b60085609031000f071205410b00740d4102d212141e144001c2c000020702d04944454041c0c81b089003405940c4032000182d400c2c420498041812850b03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 898483794 1250 898482544 898482587
    0x90409020301180c05090106030c02031e1204230f0a0b180a0302100615020a061107061409010c050f04140a030b0414010e0106140402090406080d03200a080f07 70
    0xf03510b80004645154040c8902c98040d00e0b0002c00e4141c070a1051060609090700207502c0c000404d5410700340411b2002182c00304103020010f090354601c1892a40340518490b01c4011401011408200100340000c11304100c154801d4101c2d20402000240e0b00344031580002000c0d68a0b110b140f00c0008101610400424034840c03500408c0030198000348048081c481c0f40305c100001600c0e401c507810341214102d00e840c0160720040118000c101590b000000703031043c1d640003130b1030b10040f5540c10042d100100c5030380d01251040000c10111510a001320401000f00d482c100340352006a65200368a03005501800c01c490711700010f00c0c00780d40c80317203480c4070003960708444034000500d06840e010103265004a03480c9010b508000e80e5580c924014021f0b00140c4408815220b82c038669a03050000030741003500c0c1c1e03951298032080000b4401d002800441c85188031036030301180801c2405100c441c2001c0801d4944001082042040c001581c0052044e41065061580c01c095444040302100c86410320306091901104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 898485044 1250 898483794 898483841
    0x4080702030a02090f0f010608251206030f0b070503040314070510020d090215160b1f03031d1507030f0e12011416020309010c0c080706030f140903090409020301 71
    0x140445c01e100e4012031180c004d00d41c3e218601103907042030503034042c06030013500190f110720b2091041806040142c01c0c40c000c281d0356488810395050f12507039803040c3c4880e981c0302c03c0c203c10700802510311a840341c01d5050070351650a05680042c441040303054600340c000000320b4010704002c030502040d4841013191000755112307004007001c5402031001d604220311a405080d5041008500b10341030310030103a210050101c5440160301c0381c0040c824001c01d050440400b12442c0101c050801e4117000245010756200c4440042c4940400c03420724550032840d1080d1840101c60510b00200005c07030760459454944403c45024880040d281003c0c80210030b0342c416009030f11742103090301c154020303090a800e01c021a100d5480d0007030401030042c0d10100707940050300300b0032203099254003070b03107191410521900d4009489669040000d041034415042480020b40f1060280490501c600504017a000d040340d0000060405000596a0784101c1c621503010300d4440c00d0030400e44da001c1d842084502e011f6603c0000088 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 898486294 1250 898485044 898485061
    0x1704080408010e0f0c01030f0605030a080304150522030507020a030b070f03050f01051504080f0706030b031c0e060d050a05010608090304120b0a110a02010c0f0509060304080702030a0209 82
    0x3046405000070707641c070f0452291040380001031484500340f85a406406522421030046010341520350602c40362640310907000a140e1410014030000d20b00a01240d078490506141c901002c0c3c0a40b411641c1150a0030248103246155107a02540c80490070011022010540340c162031030300903000041e40c420b0035503100000f881070860806200c0d2000c0c0c2d0340e16a600c021004107408a0700e0580f119400461040c00611450604641d9113034041c1c03000c00d1840c2081d94801c1e1543c40d101c5007250f250115080480100300d00758050003a841d0b0305500700c010f40110200520102000c071200004002004042600d038489619003004552184054460500403483c0050312000604400c0c801e0500007165070300080d00100010050b14241d609410502a01582c15100c08100f8003024054000090341c66003940854000340b4020041211943c002041c05080707070401800e51221650100148078003040f000d405903075400e080b2684283c0c401881621240300d40040703450049180c1d0002d402000000c280710250 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 898487544 1250 898486294 898486297
    0x504050703120201022a0109201c05210c01060306050609060904020303041202210a152d020f1219110301180e07260d0c080703170408 59
    0x807070154482c1c8294034041603040b402c0f441442c96410201031000070001d00729094104c5055480c041a0010801c8a501d840b81080107011500c91000462110701540e80d604103e19591401d140da90240140c1072a107846031500c8600c140c0c070401c407403c038008400c9c10308445d582c107848100b80a18001c0085540f60710703184000342020380d140340c400c0c001c0d0f1000910521340030001600c2260701a0241d41003502e13016940071101c0101d01c1c00c907440803101c01210f0b4076604041d83c085508890900400f00e2240d5420700601e24640c00884100c01c0341019240407101011042100060000030285c0aa100b030884441c8000d000f00c1c0906200c0040014079801407506440000740607a02841c20300c07100000c01c082e85400c48841c2d0803801c0607041e041c40108940d060345072620901055070000810300c00070113201242844102d030002900c0300c3d003850348100b00b0000c0726484000349040000800c540f413000d41010b4112121400d0003003449200143c040300f0907110b00821055040c1e004030612035401c1510304608607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 898488794 1250 898487544 898487549
    0x17070305010b040e03120a0227092518080703060b0112090201020c1e0a0b1902030903060103081b2a100c0b15060d0b040b011d210105040507 62
    0x3103600308052074045180910440e010030401c80000d520b0310409095600554800078842030019501707004040a0700c1608445000314030b032403090b52141049c018104040c00c000584041448004044502d21104031079208182030180350038148000324017440213064041e441d0b0045000e90041003c000200701c0b0300c1e0410658072800740c0301e10350000d051038001d0044444115010f0b006078000840065039080c08214294905134000d00c003074081c034205001ca050018564000c3e00c5440c000074009914a1020400d030100c0c92252015601e4140d40200090380c61006000107402d803440024054940c2c4204901c4500c1c480003042038400500d8074030101341c1354017500079154074202480d02c10300c140380c54068a0340d0041050b81d1180220340ca4162a90500404004e21462a016005d0000102d0b5503030350b409020003843c0c4038804181550200d080c0001c0d00d4002d1241c2e41031146507449400709211001c2d004600f004103580c103414584411400c0407090032103400441d910351804052000340400130a1700c509 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 898490044 1250 898488794 898488803
    0x31d0d060e0604051c051e0f07050a030207270e1c0207031101170f150a0806040c080102070312020f09120d0807090f030615030605191505090c13170703 67
    0x710054000c2c540200c403171a1280250024108011542800f1228000300c0d4001150000c250b003000784207803c01b162039011f048192065808004100109a810405031000c3d0000070020700c40b0305054421003003141d000c2541b104441e600c901308100c1c0035500300b0442c02c0c07801c808004140c00c92880310700a9112105804299403001d0044100b072402d501404400c011032804803441d21180e0340c1d400040700181030161904141040c2c20b28a203080e640c3d04407214010f001140050000c60425113842c1c40d0084a82e071041c015030b4014410800800d41040f80e100c440c0c08102c4002d03a0b50b040e003a82010f0b151040c03e4081340c0c811090300c0b540011700b81c0043c0303079015a5465101c4036a180c4415000b40c54108842c441c040c401c007802c001c1807000070b54981200c1a18464000d20540d541d46940d00c40e030960f80e044401900340200d003400300c40000941d00580030558420902c0801050400020480d0100000d01c012a14038000981100f4013000d58034140092149010203e452104401400d03100c0070503210544 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 898491294 1250 898490044 898490053
    0xb0a0e01020307030804061817091c0201080c03040c05061303140a050c240a0507051e0c041e06240905060a030507050c1204050a0909031d0d060e060405 67
    0x81940000103c032031240d00b603140d840302a641e680c2d03210301501c0507012205d4203038019940b05000070300c01042005c80c1c28903c01034503151400304007440380d010364032074024501d04a01c648810160b43c0100031550082e45890006039aa80e070f506000c0d04000c032a80c0081e400030400640ca1a50300c136561010010b81c1e00c20407074800321003422450503903500906036000c1c202d6000001c441001d8502102c0d219104100303e01101451141440c0c2d000954001c09400e00120307000080030020024280302000103c40e06210006450118a2060380d517811119044c50249940f040d26480404040c1400341e18091550414040952103074500103200b4564120801107040355880182003d014004200c2500c402800c0c441c1441c5c4502c5040300901009032624091180403c00702c0a4290b0600089842840364220190754030320341428451820000c1c3d024651540c503001d00e140000f540038103860015070208142100f03069049002480400c01c1841c000d11240ca041020b061240d0045207007032240b4005c800b0388 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 898492544 1250 898491294 898491317
    0xa0e01170f0a080322020f04020a0210020706060e0702060106090905272b05070206030a0204030b0408031e16030b03010b0303070c0302040506100c03050c2107171c20040b0a 76
    0x1003180150317560001d50042019600700c003607007410340c0940008a2588102e40c800400100408101d03844010300f40c400944410003400b10b80600380d411070300014944000c040c3c661600318010300c2c40c042c40c006c100900d0f848101140c40b003030748030154030075000107142813910541020200b0b03a91400c1500c020055942e0360380c410401b801d48200d07035108000c090f80740c440c5418255400c000c800c1d0310003841c411b6119400e210100201c0d8103100302d9442280300d4560700d682ca042807024400120403240703000c00490185000c009640c6000c50903411540c1050030046010400e40300001e0142031080141c03905880003103038290030300605080c0b20742100c0c001d580c00c201d203442d070700d041c0301807000100b0805020440c0036004c0c10020344224014100c510000007900c0c4d20380c0c0d866030030b07002244400300c1c105183c290204254060007144403080045400511481d841c14580c1c0c544600c001c4261040680100d540c3c2014680b0326890070b4946004840c2c0380509552244c56071660350454018002402c006071068214 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 898493794 1250 898492544 898492591
    0x7090f05161404050f0a0e01060f03050604061d04031e030b13090305090d060b0303030c0a020f061603020c070f080717060408030c0c15090304140a0e01170f0a0803 72
    0x4003030009030206100c0c581070a0405125500380340445c541e801c48418080002c040800d1744c65070703010b02515980c416444c40d070f02a009064030400f8041a00c524a0910f0401c50611545c091003468514240c0c0c407005551182000d4603031604941c6141c1041c0750715512034445a034035522000440c0401c9804034500f47c6507041000c1180d20850004010030400c109190152600880c00c140b681d10031140498902d034050042401c681090303e040324911400b06200c04000d40503c03410054040740c000601c15450401007010500701c00410702c501b45540002c610201e10390a0040c14060110741a41180c56aa182900759841005115003003604000f82d80140c0c4070303180801c0c45400b5175009048941140c40d2207095079034a5100c50030700300075885080074126241d14a0b40c2240e21075078000c0d000d5900d0714a4541d21006020801c0c03c540e203c1c0d80c0a0f00240300d2140041501030541d51078000078240c2c84965000541340c96a58a0904c01e6071081103060010052281c00942c46600744503021220300704400325 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 898495044 1250 898493794 898493807
    0x1050f010609080a0b0a020f04030f1a0609150f06250b1e04080d1e050105090a060602030d201204030f030603120309110d0b0919120c0507090f0516 65
    0x4000e110020000c04254440c0d1950082c001038850520209e1825540c5c0d80d94042843c1da5460481c0c082541035000a8403541200100b54000e10507105581e20b45018100c841074040b074061414458665850400025103070902502c2100350746e510340c00314000c0c00203483c280c1e40600e00011190b104261001404201c802480c10300980340300341e400b815a480e50780d510310481c1c00044103c2000303540c4020f28620702034045584503118101210008665041406105018100030a41100c043c00d2107800c01c201d6074008200c0354140842d940014100c159081c4140085420360720404504a000c01c94260fa40c04882c00303207000e540b19840d0740311041d1403200705506540051002a03e0b00410307100d4541d425000390440d441c3c0611034084e80d503100301c030480010303904d1103d07207002c0d01e45101542c10401000c00820010442411032020006100c40e1a6150118000400d80060400100f0003d10702080300400401010340701480003480340b03583e0207101300002c101c12030344c50380e90920000140480030301508 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 898496294 1250 898495044 898495063
    0x8040b06060a020a12021c0513170309090a0f0207030f0201060e071704240c08010e0609040f08040b160302011a060f18060409290a03020411070501050f01060908 71
    0x40107013036503e4490f103c540b017142e0718544440540c0100d110005d4507e851114442421000b03803503064460fa000c4c07244104800702e90b004011002550103940621400010035509800d0307007102d0510060395180510b002611b40c140304400709030300200721441016000031210500178100d0f0f00801255030360f403064070380b1f81c43c003994008081112011010fa0111502175820791007070044d0303c420740d80c0341034541800c400040350400d0460300f580c40d0300d100190b540c070401d07080c01085501030009090404c0d40026802d5440034000510130620b25603c2010400c0741025500104400030040c2c1d02d9201c28103030310781c0840440e0000c034010351030007501501603006540304814880b0b021386032604206404464003219070250541803d11a6085561011592503100900103000304c00705c041140d200700185244000b20243c400c076101c0c5001c007200d2109803100030240003120f030100c40c08501000a020b01d00d1140c4100400601294203140800994422130022281265010340c0e410401550319a032140c2c44a030000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 898497544 1250 898496294 898496297
    0xa0209060406120b03060907050a062f1f0902041805150601030b09131b060f0507080409091a010506071121031201050a06090825080d08040b06060a 65
    0x18007007400754510852050380e03005241400040e24028000009103013160031506440c0c15405250305001c182015410b03c001080f89042810421150180441424030100c03034814031446c004040b800e0030f10013000030340d0715500d00c1c040007030514521041c2c00001e4074143c64240d01079403c003961940c0108a030704007070080580110152031000c0241140d101c01c000d0241c07207641050786661022206030b0307449481da03014818031848002102c00900d0040b00178840e11142d07101c0b01c64040c2c410003504e0381013400c0650210461a0480e0b071058035190418440c01160054041d4629002030750301001801c3c0d4286040008040c02001580c1c0d0b14000c000c0e040c4038024004001e120f920720707507038038038140502170102030304c00c40721840c442000d180b1000f440c541154107020031903801c0304010031a504111030208040c00f007070301d858555541001c0003c0d41d9144030b1461a40c9410000c1d00351445013810501c42d0029295070402ea842c40b91040e003004260090960701601c6a0760f640000c980030385004c00484407007514a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 898498794 1250 898497544 898497547
    0x304170303062106060f0f040608011d0a030903080f1606140a0501180203060a0503060c0703180605030c090307090e0a030306090627021213030e030a080f1b03070302010902090a020906 81
    0x607401030000e0880e12007140c60f0841e614080e1180188c2d940c0c018400a0001c5200018504000142d4250700e0110021079113480e4000012030340c082540700400c03100f0749400403042542e603c00c00301480310a2054001e0490101202171040703042004a801025403120110749044040d1a09143c490489400b0712030038030b140c0c25526000b4140807003500610790091008054100042da503e003c6818000c2c1103a6a504007040000c0d103200b01600440e02450710345c1071030508004607044c0300c009000c80c400501964841600402d150b41d16903070400150000d003641200600c042e4103044512036aa02c01844114013082c2040d00210309444a17214082c01c4680500b5001c50010b424070b0003e503c0c01603031603404003040d000c001c640304015002d0301050088903503400c0c1003c6c5900f107040c01400d044516003824800d800081d44a408540d200b030588001381e0380040c1c102d95860b407d8003e24401809206500b0060002292900c02d15030190300c00000e43c3d00a50b45451241e172407081a0040740320320182c141c0e10140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 898500044 1250 898498794 898498801
    0x90609060c030c02060a0804170309030304020f04091407081506030a080f071b0501120b1f020c0a0810050601260408040503031603030b0f18090304170303062106 71
    0x8070340d501580040c001c0c00c0c0b1841e2036103a500403d501c0c1c0d006404c041c001c00c560b038048c0000c0001112030002503182c4080c1072421800c0c0400440d40743d1101030400392107038240e00e10f10489581d840d442107401d076501544540e001c00c00545055100c21451055648602548801c0d28a900004c260b00c0d120b903400401501d80c061440e07540580c0c6400851007482012410302c40300000034909034050301261002104841824500400108000c10108401c015039042c50b1504c802e0352240c84c60002ca0383e1200094401540c0a85000c03480c10182400040e40502c3c102e000007400791010404c1060014441410300031661000010b4030038600888489400d46120349440c55120a05508240c0107842102c1482c94a0340d01c40001c0d280d034100d1602d070b0759102c018250701010160584a0251491004da41c00b00d101c01501e0001481d14552101420035042450006010f030381040c4116005004240d031590482c3c00d85251050784c0783c00403100240202e0400300c2000000c41800316160760300080c0c500604140d503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 898501294 1250 898500044 898500047
    0xe0601050d05071502070906050a03020f040b03031c0e010c0207060503180c06040303030e0607091d0414010504140c06040b250821060604050d031115130b0709060906 73
    0x75080754192035074091102d01140c0c0192034a0072071036000055005203407031424a00c5c00380889000f036104a1007640c40e000104010f03164500072019403102100c00207403140108011034214440d11300ca40c4d44221051000243e0651103601551030003201200800510110440590fa140103901038a004030b18184002070350640e41d810f00c1e961800901060760084260300c4042034064005810842c0401d482c4e01e0309200080041106c40d50200c00d230306d4605c150619103001c0d08a000c4544883d07c03118144c81c0c000a003484404410802d5034204900200980d140134280044465403c050a40c103038061400750361319030300d046800d403003c0e03810344030b0460701d00180b514000000802c00300c0340d00400c40e05243d8201c04150044040c01e00280680e5181c0c00c54080a8022850504020802441008140000c3c0b003540c07503000c444121294103050034034440d910f004202e858480303100007a11303082a4601c10000c1042c0341c0998425030902c1001c081c3c106071a020001e444142d81401a1030000341050000c2143c0c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 898502544 1250 898501294 898501309
    0xc02060a0905030a0807051911040f0b060d021c0b18090f0f0d0225060e06041e140d05061b0d1b0207080750090a0e060105 54
    0x12903060400a03001c03507030382020a0030300200c50701c191000380d8040340700410b110040c030032445d4210b030b441c01c0342e6040c0390160340303500b0403e01c04148a8040d03961002d64001c0607581e6030184800000c000c088980b18066004944040d41c0610184840c2d1600f0001c142680c03000c6002e03251452500402e14103803c03882c3e4003a1001d014000701520030a1064081e200c00c1240140044180c0a0720b1002400380f0284451001c0d2501404800d6a0701c840002d456010700e9210b0301e103406066a4861174076802c00300c0c80c0000201503020306d4024104590885450451080d4440b134440d0444060701c0c4500d004015030010042c01d180d800700090003903046400007805520520303540160904071a0215420b04040f40e10600407940b000401603598031145a40c5410035404202843c000d01e5a10300604010342001c0403940c800100f51240b10391001c1c80d406400f40595400d8140b100a021440300204414690007e800100001569240038000e1140403500e0805180901074206c18404020201780e440c040c01e100300c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 898503794 1250 898502544 898502557
    0x801061403130602030a06060905061201140301091a07020d08040803042d0516091e02090105091f03060803090a12050a0c0f0617061c020315180f0a030c0206 69
    0x340b9090000e00000404a10145002c0c103044e130400200c280c1000c03000790180259400561060f08107002c1000e01041c03000400f03054450801e10030340405044004039000d00341c0601c0c000e0104007004040080030119180c5284203950f542e00301d6500900300002550040000d90380503000c04000c0000034041001050001b41c0502000302c00c4074401c15000c0c0c00e20301d107401c056048078541c1082803118108602d2058071000340c01150000c0003584040000c80390290305002c01c01010940104a51100e17030300500c165810380c207001d0310030160012403030400b0080e18000b4080301b020925005000c0380e4441d002064403d07005010380004402401d140301225004400601119680f080200e81d030009044038487c500281041c2161000c0f190529001601c10f01150b50100d0b50382d804201000308940e50549410856601c801c0340c9038040805001003820100102403501420f0040c00508c803021040300d100722038400d00c1d201601c950400c0256090346820300d28001400040501c8941005850300c90001d101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 898505044 1250 898503794 898503811
    0xb0a0216110a030b011203090503060f0609040c05150306030d03090b01050d11030a081207051305010e0102011523090108210412060507170403170901021b0f0d0801061403 75
    0x84080d40d0b07a03611084e0910980040d400080c18011035010550018130840180c5004c03000741080d45800c0b0365500c42c3d5540200130a109040c0c40c0b01242c10b000709104d0110140c20081d210040035504295204565802507400078040d20603040c1001d210352191040c4100e084d404100035400381d10304400c12070380c42c01004044c0c3d180001c11600d259903640c1040a0071900d840741c42e43c291507c124002031075502c14000d02880900008202a29110210302d207940c0a40c0e0003420f241c6600e0210400407801007881c0d1034414000c010749500070443c0740c00140c0803640c030381094501002d0900c0d0102400101d0000303114607452035208907581c1c50140003500303904141c12000302516003400ea40d04003085c03183c0000728007581d4240c1d40718284000c0c1030344420014050002201d0a0361182040d40d4020500c42085c8071410000001c0c40c00304490304003e40403a501e0404141403121810025034007075848c0c070340c5108488054494000c403240c100e0701035541181242d5050700c0d1120b0510507401202400d5000404044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 898506294 1250 898505044 898505059
    0x1060e0102010e15010501020706140a0f17070806030d020a110603071e030506010806330d0e03041707060f0e01051606051e0c0a030207060b0901120b0a021611 70
    0x2103c9000f0881402c207200c002c03907030044075454540064108025a00142e0403c54005c1d96503641103005011120049010300c1d01e050784542c00c11007203540c0e90f10355605024021080c820322aa280c1d01c2490b59004400403815100c1c220f413014016a07503a401e80500400c81e26004416a001d4641240510f504c210f03c2e060400c0d05180b222513691001d08504405000719590784248082035034008000c561219099072001600c846004550b156480580a1224070b40c100000d88105404441e0503101420603250050000c02140da4a040d141c0d0428018000040005c40c03000071844000100740342140d540ea240c0e10300c18005a4021600520407019081c1031250400c28844d40550026000201900641000415092407003080380303107000104100300038520240c00e202042164000311440c442003400e006039200d10328a040809000003001041d400018040001f55030449410240e8000f40301d083c60100958800750034804038090440640038900440030440000740520310000c0e02c03000000e203540c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 898507544 1250 898506294 898506311
    0x31608041407060908011506050f03270c01121505060705070b030703090311150106210216020120061b160c06030c020102030c0d0b010c050303090a02101701060e010201 74
    0x16282c00c1e01c5500010010b0441801001942400e104015060900424502040d85010b038010101d0154080c0d1484d032903030000102d580302c00601a40071000d0056095500150030141526480c2c2c8145078045000c6104007040d0300101142c2c0c480d10421040103185242c045046c00140705260708103a40894561017602404519400040e026600c600d17115607010030f1070840d0b480d0080a0300d0811100400d035512030302400f418203240c07202e6981502c20328685086034108650007100014001c0780c0da02e1101d0b2001403c001d8200e01b015600c0012070007a25001a024254068800001c1001c0e40c07074042ca4200c000031400b0160300200128406080820803401d20206910610780c8000c004011184102d02003400c003c1950140500720100131140021803d514000c051208240702e03244080e00d189550725038180381680109210603841d0307041000c80380c4a191081da216902e2110000c164814000c4010040a09100d400d0509111400e441c0d480e44a03460210241c43c1043d00c11160f0b07055541b2003070385 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 898508794 1250 898507544 898507583
    0x1507150905010504020f03030c06070807020a080d05010f12031d040e1f0f1505040c0c0b2a04060512041e0501021e040b070f260c01060b03160804 64
    0x2404580307030245000140f181000d104101d6034034201400a4080e810900a003540c604000c10000d03440360641c200750407a40c2d6400d01c04c078201112940024103041010400050140c000d03407015058454503291014041d0712240c041e207441920200c0200016187c0c2c0794034010f0702c01c1c6410003010a0300500046010300780f201805081c6007141002440d009180071480c0c0e02003509015030020701c02c2d0024204007104800d81240600400e03401010301580e09d4401c001501d520401d10000d0068120911b039150381419040000c0988000785854400c990f0308000307084001101049508aa40c6a00c40b0382c9407001401008460200051094941c140c4034079003544082498051550010b00c10700c001661030b05d019031405035404c010700380020500014001401507500380300c101c424864201c00701e0003c1d070300749107084100384450018134204810899600b04020301d03070801400007001c10700002c1c402c982e00e400d4441504c3c081110030004070000324800383e00183c01005801d0b0058064054207041d0b03034034030300d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 898510044 1250 898508794 898508801
    0x130e010303020a0215090f2202040b071208011203030f1b0e1c0c06120b0d0c2916030201020c0f0705090f010b0301032003100623150715 60
    0x3007640560407041000046140c03416042042103001344815080ca041c203070105500ca001d00ea03e40e402081361003800c0c0b55245005454814488000500b599141e856088401094210081c110b502034098034645041e20f008603a641d041c0c5105c4c01c102500c12625031008c4000d81000e21450381140c0e43c0d02910704032500317440000c40488400c1d0301c45010075101c03902445418500f0355404507010402d801c02000190714040c06004941e03480c90109a107000011400b0002e00000d140300740c0c03008001d444101040060340c100c00480b28001d540e8150b100d031402000c01e94081440410300000320800500403c81f5240c003d00c680729000c0d00c001405c0c01010b04401d0320b00125000d449903640e010300c40c104800c3c03030074407219030f40082c0040c6180e640c1d51600180c0461800180070003000440754a03440e0300f01c3d003001320100d01c03003190043c01c50b019030910040440040c140c600504e10707200c509442c0d0000c500900325440403c2d0002a284900c424854400c904054022403070460b11040c42c11303002d2142044500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 898511294 1250 898510044 898510049
    0x20c240910110d081e0402090c07080c1c032a14040b040e0f0105030f06130204140f071d0a050d081204050c010f0318030c26040e0109020c12130e01 65
    0x8071006145d003820440c0003480b5a4040c0188520f01c40b10301048016101c0031841074011881c01542034031035034949048031366409151448480e81c402d032003d82c0000c403003215400b5140f8103a510204020000d103843c0d00881d1201003802c41c0c4050000c031210798014800e46010741940300130b02c801c6003401d4aa04814205502503401081e103441d000c81440000e02c841101c00380103000840c02001000f00c0b8072001515900300a00709454281c201c00980c05540f40c54100006101409039000410326150514914440e015101d04c030000f0000d40b944140c035400c08200d2801801e0042500314454039010070000140c640c200c01301c45c000802c0c440b4070052180c00301480e0089114a002d0705440d0142d0000500308030300d50b16110101814030900501000d00a9890a600c0e82c1501d410509a04a81444500b00d01c500b40301c140e4410039088203035a10b00900d400350066410b42c40b1070101c0d513665070490380181d000f048150a00b03504141c0403071822443c0500106100e015043d6a010a559208804030348201d090f0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 898512544 1250 898511294 898511297
    0x10050301031505041e02240c0d0c12180b030108062413020c03130f080d0c08070b040201020109050f010b0a0e07051207021c030c021515100c0c0303020c240910110d 72
    0x10a5000010000f071200c101027621502c0c2440351200da40c6c5451001d62180400c02083c4910351502c8850156026004000f51250401c1640d807545e40301c1e603065a92100b12040503810b4080e00040c0311110110603c54105e000003001700b540740345e046210350006e500a080ccd03a1540c0c40100800148002021001002000420741401a8510706540141000603040d404010803144040c40000200300038140c50500346c120606900e03c3d600c1e0320040c3d0041140050281080c491070040e94a0314205401103014000b041e9000e04909548140c500d524510a660040114000703102c410144101020420380c0544240704407207080d01c5d1001260440d40c04802d4803030001c0c8c0c59003020304003140c042000303c518003418036103900c043c41c080340151100c0401c0c4071558403852100c03c84211184c82045c04030b0030180c002e081c0014050352071901950340c140320409540220581961803405000c05291080c0285103050418a0408003034200001044070612000c10f000346000d0084a01104100814010049 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 898513794 1250 898512544 898512547
    0x103110409230108030301180e0c03160f0602150402040b0319060501090e06060a050108070207050a090605010e03063106020a02060a0e0a022b0210050301031505041e0224 75
    0xc02c640e02500c1c0c441604680e01d075900c204010000701004d0241d901c111002240b000072000e000f601d0150520803800122645440f690b11074042035043d81c9003010403980d000701c0c0401c1c40740e40d0311016a01ca0322103000b03503a02e048041e0005400740c02e05803c940d0003001c0040503225056a0107102040d1000300e1241568519980d40041c40340003414031a03101140c1d00c602c020b11003490120001501d030709113401400c1c10001d0100c046541c082c000c001000151400810031100c2341d4070b5440140c014800e510805000411078a1034100904002c00c2c0c02d80130f512840c010030040340c1034034589518100b217410108a0300480e0204a00402d6682c40a8000091181e000d04501c3c20100d0080301652400d0509040c0364000c2440040142d480440006112011100070321000180750600c0d2601f00e801c08000e504640e0728104a40601d51020045050701d215141c510180261500d403881102c3c4129001814460b0385000506498040d1090b400210310080c00b94460700700d82240030780b10320301d4040203041c9000b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 898515044 1250 898513794 898513841
    0x403080105090112120e040906021e0f0d020f0f070302031908130312020c01110415050f030103110301112a1606080903090409031d04090b060103110409 67
    0x91105140380105001c58901e40194106164220068981c50000b00110b041d05841040c40f4003a6004003292035004008001c009180d080c680065445081d0010041c800a4008440071000d03a085e681c10b0000010543d003054002502c1c18000c1d842540070b0200640c1c140101c003010364211000f441c45602c01d0b4065a04c031490b0034010440781c400760404205102d10700302040501111032062800158162a1140f050515183c100b40203120b07509209075154240b6520031020441c00d00140225007800d05c1804503201d03c200100c405005002001203113420800041021800ca81c5024801d400d0050001643e141400303c0e0044591001848134000300c103245511203c2c030001040c50031580c0c550360140043e20105081c0c2c41d80d04c180360044070709018103200854000c0d4010410f40d1141c96010704208038100c890700340681950b10010454066101c0704090440303d0a01b400780c03240007a404060b001c0185c039410015006071440814641d030300e090070b100028070710ba030314060030144084043c1c00005642 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 898516294 1250 898515044 898515047
    0x70603090b16080606180a08150708040807060f0b090103060605030f030c0c0103201201051c0b0a020a030e0a0f210912020109090e010f1b0801031103070b120403 71
    0x580080114081e00311031001c540055400190250b0f004c1c03000c071540c940c0c404030700d81c0c0803405140003d203003508149150030102c0c1e00ca00000d4488840001003c1662840e510048120b407603400482e0014460402800b48400140068001d060300408081d80803079401c2e980e00102d031109500b6482554215101c080c20003e5050911a500321500c4200280d8039000702c00b001f5030380d981c1d03041d1189810140d49140320f01900b9120100b038055000071212040e40d030101c406000e94882030a021f103d126403c96401e2042049032906080302d041ea00480f5440c035540c070040040000d4105014640600d130300c07142106000c107424080e400015100355040804481035042680c1f05048013056044402e12a4042106040c0c220101c20200c0305050b4442510110b0703480101c03414443e660220440c1401e04116280f040c6064005a0034000e00764020040600c0090000d0408100c440000303000c14800d00041c0b000c550070802c04104440c010b000c50781d10964a4000606550103403a07806035000310141031100b010b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 898517544 1250 898516294 898516313
    0x60c1a070e040c1d0f01031407030c2a060f0e1501080c010507051b010302120109050402090609072309120307031103120105060a031d0a1a10050112060807060309 71
    0x1195203141c00e94034100203600600c0d60009a00e0706a1040c5182446030b80c5c668840d820a06c08803a96901402e41800c0842016002e06450450540451200380084500e0007040d115400c6c840003503c00101e0039856625240010702c032070035101204a440750411100c44600300040c2200810008841c40558946000182001d680f0100c5504100041040d00c0c04202c00117469072645035800508000088003c005034001e03c0b4520b540302d6980d00d04400040d58a032280e026602c92130080e0703940d00c55a0303604010051040012100c01d030114991180400d0b014100f10504ca2107888000c052038070380074290002405054406c880c0c16401c1e400040c0410800d58000c01c1c40890100c800010750078403ca13207100c468028014003079070b4041c40c0c0200d13100740010b100f600540c0a42402c65000464208a03082c410740310100c01c901501c0c2400701d80c4c072000c8000702c210b5000b40314001c0d00c803a82d1001070510004440c42d200405012400ca82c64081c00b0401e08020f02a01d401824aa100001c2111303092506c10401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 898518794 1250 898517544 898517561
    0x1080106080309060d0609060308071e020603130c080105090d12060e0105090712051801151a09190b090f04020a0905011b0c091a030706020304060c1a070e04 69
    0x1641003020400c44100008180d50003207030300300c481940344c291741c80f400001002294000845c16003004000018880c540b402040c41b540294044c500c1031068902c141504003003100b0007900321004100160b6100c1280d0400c0c40401c1c403034554403204680da404090b083d2002a501d803401e1f030304008242d0000d03d4019405860b07a0040d55001c1c0718252130001840d40d01d110521600b1302500d100800150b130b4070700c10780c020420b58062000c200010704180c0c602040c0e0301070f40229041103600e080f04141c034219142c442d200885030307020041140c8843d01950041c0035001403007519040b102c1d00c160310703050162088e1001c7c050080c41410b1616a000d000c00c101c802524040c116008600c10089024020b90100d14031003a02e5080c01d006405410700c1c0b0700240c894100c9800a4404070401c0c3c00810690500e4004607560205000c00044142c010000c0540300c541e0380c4030b2500940c3c410001003200c10701586110960600440420841f45003200c05010090821201d030400641c40c400c10542c149131030311a8010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 898520044 1250 898518794 898518809
    0x2030906091207060b0d0203010c080109111e0703112a01030c05092e050306040e031c0c020a0c060f1e1407060204090c09080712020d060c09030b01080f0601 69
    0x44070302d40c42603020b01d11030740002030b103c1c2d034903540b07180d0030745d1540001035942c6a4080e00030840c4120700e0b4401002d205080c000d0602c41070071b1040320180e074182001564840d01800c2a80c11030b40800344413207901980a03440850a100d440300b0810801d5000b0310800300140815805400240e024240f0803100814043d5014107141c50700502032807040d8401c042d6411340c02c040d100380702d002c034501d1041a240240c0310070b407107651003042d904421200d81c000007650080c101554180211802c0304025501d0b40201c1c038004000f0420070b0640703940b10038150801000003102e80166408100d0684442c12079681580050011524568202e035a042d07000c0345648018082c0d801c03c0f01d4001480100070a0508002a00b800900001c240349050104650459000780075028040100c5101c010004e8040e010a01c81c01a5a0203003c2d40094050742c4031100c9801c46a00078508400d102c2999942001011384590300400c001d040d0700084002180c3d060940c4c041c04d101e5000303024041d0002c111910b002d005070003905 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 898521294 1250 898520044 898520053
    0x6030b06070c03030305070c0203030a12061a09101101020d1b0207063f050103210f080a020909070302130f080c040c0513060914010c11130b03010e010203090609 71
    0x2c60160702010059940c0340c500458181c450401c2142c402c48094006541400000b5940312101d4002c2a1800c2d0309041840600c030b0103a44440c0c21281c3c0701ea072000f03140300b1501048504e0382440c0440e0440c80508950400011510ba0400483d01726000300708150710b85541c440e81d42e00c42d42c2980040f26219200c0f407000b400e8260070080010036030545150005800752100c1110501c11602900350301c0e02e20445c10030000c07a22044001c09002c0c01e42880705a5640d9400140903088c002d01000403a441e2070036803184500303144204400c841805009190f89a059820301420449a0310341c41ca090091104d07035000b60321041c1c21058180c400d0403a50190940429542c81040b01c407002003860f400c0c5c1002204d0000707211400c900191407920449031032a102140c259004a0469005131a11050792001c0c0d000c403441070a40801503c200040303a201a11064481c1c1c007410306454820f44099803018413401c046980d80728100070070b007521385501c0483c10b01c2c0d40201c100708400c01c08203e0031364081402002071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 898522544 1250 898521294 898521307
    0x50402031501030b0d0803040b180a120e0f030102071b082b09150809070e0601410405100206010308180a050a08010f05070f0e0f031e0706030b06 64
    0x440000480c0c0401c0e606242d00c403000f09410b5980d0417502c494a0303400002440e5a40b60030700d805105040101c50f01c00d65502c892684540075900000c0c101a4980d00031040300040441075010380308034880b1801c017684002c0303d601c0d0440c40c0d02c0a0018161041c824421503040114060000c10b940300d242c0c000003281d901c45483c0c192501f90040e6a1103122203540740b81411160490012100074450b90004402e481c6021841105580c2c0030500703d01c2039100c802650340540e159080609044002c1d1855400600b01c164413064a4020004544044003d90209001d40300682400400e00884001c8503145100c04201040541480c40108a5984190ac00342960790304541e0b0b030720968014220141145039020507203401c00c0d11000d4940024100003040c600006a803988490702800c808091091103605000118072100d0260015810b010019141c82c2d01c6840203105211207180d665030305036414806c451500410004000c00c8212008428002c2c0400b0380c1017820207829078900700309450180074100b004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 898523794 1250 898522544 898522561
    0x6181527202d0a0f1b0b090303091506011403060a0f1523040e10180b03011d0c06071b290f0f1c0c0e030c030c0d060c0513080a0204050105040203 64
    0x250030405051000c2c8540741d1a1701501100c2101ca001881c001c0c00c4814455295000406140304140e02c0b01156051201030741401800079054500d1030100d9040445041c03130802c000061640400003401d254100d50342c0b04049124041d155020b105410a0300120070011795102d61311000180da03125100c4140c00481c940c0910310701c141e12444144240201c0400c001008000821008041d2401605902e4a841e070180001f4003c621403c3e109610301403c600304010614104101c549107000a043d1010364101400140d52003850200c9030100d02c440d010039034421100040001d80b0340e90500401c0c0d45034030051486d4800c14403107400441401444840b94410740f8a0854201000f880c0d80c4641300e4007220b200520340c00c002d41d09100001d04218490b10584ea0100740340c05109030490440d5501c2c0e2805040c151101404134801d5044094003000c0f1006c500c068000400f118141e141003031a0000301c1c01c1840f10101c803038000d1400c0b034201c03854090541c605030050138054201142c0441c5075042c013130038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 898525044 1250 898523794 898523807
    0x70b010f050a121112070b040801050a06050f01080403030c0e120307062003070507020a0e070c0209010603021612020c0315040302010534020106181527202d0a 70
    0x30913502c64200c90301c60b070560001c244080c0c4020b0201701001038a658890813094060542114a030b4400c601d410400036039450425290035111a060716184069101ca46040f0080c0c003494181209110002c0da102d240ca4694660000c513041d4204086c503110f5030701d480d028094880b00c46582e049950124180241d1052180480b900000d090509550b582c60074800705541543d540c2c0441800c0300039504000005410803c10070410307108903a4180700703a0721210107404a0259400b0421200441d814460000c0c4031880664107003002801250000001300300001c0c90111047c04040c919034206090104043e024010b07a90042da0301081300180740050405290304127103d222031010004440744030150345000f03600c0200680851002403010810003c4140c02070300820441440c418252350300050400801040304e081c8612000e641c007405c0096400890140a00300b10380701c490240e0074080903910700e000b001030061f0300d000801059003200403001c1d010398105c201103c80b41900c0821981c0380c1d00d5400003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 898526294 1250 898525044 898525073
    0xf091f06031d0a0c12060906060b1903020a050405040209040e010501031406010f0b03040b04210512010506090604121103060a0f0c020d09210c080a0b07140304021302070b010f050a12 80
    0x14900c1c60132542c5043c0f0b1b60140400440c09002e0607d80072002c10180c3e940c80c01000081c020841c0d044841004c2c500032000c92048003803800c0083d20511050010340b8240c0c0003001c00c408018008102d0b0030a0a0040703084940a034001c964181401e00c4441700d040c001d0000f14014451242000503192902c103030303d242072000600083c1a500c2c00070020301000780080c00400400c1c0048038404454024040203003007940682c00141040c80c1003000055503140413012110800c0d0b020b0816800c0c50f00d0440910a0050110070440b0007280c004000c042e152000c21601c0c2c0300e40d00e030242c0410079084102c0100200e0b122407000104640000c08000c0c0b000e50000307040c0c8111503400e44000d00b03401404400045500400e04000d090706115000003900e00d100007805615240a0001211b145e100d015060343c24100001c0143e04041742400004d02516080c1400503113205894809803404000342d440d0006010260420b0310742c0c2400000600650404540c114007a085445004a0902054442000e90301014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 898527544 1250 898526294 898526309
    0x10050604091d0105010e013f0311100b1507121206030f0b01170d0c1704050d0b04060b19140a050603090d1d0f091f06031d0a0c 56
    0x10900081442c65002d403448101120304000c105550710346404914a030030a2180c0b20048030204084600c0000405080d40c00108078190040303002c19007903e0070a03112607100d041c2c0a1151800c04440160010300030f150141e841594000b411000e03240801069075066822002208428010080021301d203080e03680d00c040c12802c096201a010a202d000505019000106100402e868860030020f59424940c140c8980082d007854032007850340013503590b030355814900c2d00040c4a81c2c0d03c0301c0460080c00c11206564059456940390588807404164400008030045031910122010042400000d1040d40403003a801c03a041c00d4001c180d111000b401c02020301a140d00040107030680980d0385e690214203002084040d1216490b0315080b0f01d190340307030021806c81d4004200b404103004400000401418180c110080000405100707070800d201241100400c2c2880d0f040e03080d4035982c0096030f60b0460070300800040e60007051440c0440440071029501d09009640c41e4090746d60b010024995100c11415a180c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 898528794 1250 898527544 898527551
    0x603020d02040b030313030b0412170103120203091203070b09120904050a09050d090e061c08092b060b09161b12030903020f0d0f0f111005010e1005060409 68
    0x41ca40045e0451152040410114030340d484000100400d00c60210310031805401ca41020081920f0107855100700c0003c4201a254050014400100d0007000340b01c10a1003481103c0c1000035000100d26503000502e80703441554400320f216410010000d81e000c2c2e010707004034007401c000004c508a203402401094452407150307484100040007600c042d8002e4400b540c10a048580d08098a031003e000d030400360083d400d01d415038400141c02800c0c03441d20383d2606008400104008505a12141e040b03070004a01658030a144800812524080881c82820b002c0302c00703580100200305107011002c96001c040c046005100503001c00c01544840c00e6400f10181182c10401c4210300c106240d6280d40c04160780c01003480045040d103c6081d50b160344500e010510a8007220100d1402030061a074900302520002c2c009941200c03801c20f460b1041d0314106030f002030307402c000c00e8100201261701e00f01b00303042a201c2302c020740c0c0b0001005000d25600d9a00d80103240452000005400c14002c10520f00c500d00030900511b44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 898530044 1250 898528794 898528811
    0x21060230102318010308190801050f09090a050f030c0d260603070f15080708040f2312190908061b19020c01030b0618100323040309090603020d0204 65
    0x1e40001030b1180000d1883c0000140da100d04d001121a04044107404440c0021080c00d070181c0c2c0109100360695100501d10b04004002c1c000700540d6800c0280160441d00900991200040040100c1c242c181c80c1c10703000e192904a502220f600d0212000400020041d032002c00c3d800644030101505030350a50100c1140544e0355010211b807401c02c3e0355000c075801800040c00010361000102800305208007a41d103502d142c0c2c4854408950704202510040d00e442c61600e1003000060042c1b070081d44021103010030604203a40389400c5c03424000c0071414083c820b032001803900c55035000c000010300c2c01d44142c00c05504140c20102603968948001345040c1400c940b81128070010880740095420320214070003a1201c1c1c0006c40002500c98400c4000705000c41e0034800c160b056442c3c15810740704580d1030041e85590050038501040301010008040302c05141d030320540c1c2c13003102040c88580e15807505102c980f080d41d030a00b403038004c24600650f4000180103281603810700050303881c0340403030644940403900400c400c076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 898531294 1250 898530044 898530049
    0x108060f0a0e0901110a0e090606071509030201180b06030c0306010303171b07030e040609110a030b0f120708070501180e04020a05040f0f0e0304210602301023 70
    0xd00206a00b04114049410400240d000021f8103111205031211451501d407401484650300610000415141c4540780c04518119280d210b2540140240300202d000060001c8200310b1009952080d682150480d080010b1800c0801c9241e40490b01034000382255032640d1002803084243c1040d10b0000c1c00040049071031100742100400941400d00b0019545884924010b80596201c1c200c050244c1e06100000902c102c4a00c40d03003152040f96003034240b400022540c118010483e440150761b204d4400d01501d9400c1c0c4544a005041c180301d03c0040078810304202c8800d203000c2140c1e204d0350410503510500466940c105c40c43c40c0480300901070400150311580b00040b81c00035150009a0000d10740340b01410946a82e400c041000d842c1c0120070440c0c00d0b20450169100e1040e030240b901c0188848034541c0113109911803003040d40c1e01907180103040c0309411901d845036040074880102880141c052511041c000701b0f11854104807951a88a005403910411000030724400c0349004030103000c000c9414154 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 898532544 1250 898531294 898531301
    0x3041103030f180d11010e042318010207020319020609040f021b0a0807030804170a030218030105090604031209050609070602070f1206150e0403020c0108060f0a0e0901 74
    0x210000d0949442d418007116074405500003070045a2050043d011180c91410082041c0070010f4201c07018894418100707005640804641e0342031900140c1e144080030803141c02e0310601500c480c4031805449941040503000c424036405400000069104114450050741c00154560460418401c0c2c020242894000034503030303007c0d0400071a046428001036403403160300c41d0700810043ca00308032001415114502d50070f030380b10b034a00720082000004001c0240400c6c05488200e510501c203007146101850030380d154800b030f500032500c208007094000c03500004850800c1c020400c5024181c2c001c00c800d11b031034080f0315600d01c0040d0020b4140a8040c1e200009105540c00600401c3c2d0031408039206410302403640d035034403070342c1e4466600180100c04002c01c501080d6907409048600782c80300c01c110501c498541400a00c02d0740810080880c01c0345000030390704041e8a4045c850303406034010f0420007400c00000350282e080184118403034095100181160350750b032021142501d40300c0c141c8940d282d4231542d146006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 898533794 1250 898532544 898532573
    0x10090e01140d0b130219050a030b06060f07030e101b170c070806060907050a080f09070e010b030f011703042615330d0c090c05070501060f06050306060304 68
    0xc0500b5500304403a45407000d8130340042510076500c620310070500c072624001140c1715000e9280c0c0000f10b1002000420000c4400c10740001c0001d000e6403501e01c240f482d0080982c484902100444c00001d031441e0342d07240042141d82c9800340b40c146144200888011300d4004625050014100d44042a040030a4030000c410f407203c5504035011036080549070048036554680c225007180c410308040000510192040068800306d000d181c1354420140c80d144035120b4030ba400140413428a00c01e04c440000d0006403190f000307008280c1c0d074124075900e00340082c1001d00061f0503040392080840040b2381701c01c02c010000c112002c84d8010000d000c001c4e0440c0311070b26488030440040c400030744114a00901101c0c0c000d00b985000788548504000b840f42080205180342090004140c151100d82c40c0c004218103103107410048161107083c0c248250f60f1944c010f401118004901000099030100b58081040000d20035030010303080c0312050041951410b20018040d00c4003c0416024000200c041030412441c840306184 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 898535044 1250 898533794 898533803
    0xf050c15011206060b07021f051e1210030302030d0c120203180d171b071b17150403051b010908030f06010c152d020910090e01140d 58
    0x100e565145001566511000c03816115180380c100b00141e50070380c100403039a01540c080c4c01004021a0b0394480e40c12002003403003502c2800000c201c600c200594141c3da8001d0360b10040e40c915180d101d9200c22403a81c041c028158141d440b1300000c14400b007500002940e9001e040d4084c08103039581708900403541001c00c80c0e118139081e400070052144581342881c55080c0000d00900b200d0b40100070b2101120700c403c507540c1d24852215140d01060000e080c40c00e2880174a111500601c1c030b40500350b0340d00d105407440c407403140180c194944010704c00700c003041000c0440e1070303215401484070f0030b803040c41005d000e50080e00090a0041c00502174110b0700b0301020014141c2c841d00001c000880315401d00c00b0b820b0b402201c22000310055100043c0b041e41c00780450b5a01e55411031110700e40d13425410803100062901c044a0803416800791a529142e1800e101c111401c1b40a43e4000350321017034014140218002205006406d0100801080c03204a452101c46d0b0704507600110028180604c3d0000f1800c1180003101c00350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 898536294 1250 898535044 898535083
    0x901090305100608010c05122d07020d020d09080c0d0c0e010308030406060e010e0403030b01110f0a06060b032202060f070b09070806011d06030f16081203070f050c 72
    0x822440b41c6a1058089400440003444690301d07220080703500d44589407107210b0516144000c40c03003180303005451031003003500a034040c540083c000c26480b6484000710707070000050f031044080ca8a0654188490000070480e401c1001c54030342016a0161500108032441d40902105c444540030b0000c0c05400300d00411215800300c00719610b81c00c20310000e0784100c40a551690030141c00041d1890041c0f521412180303900e0481d145c0e03844a07601240581980100241041442600080c3c3c0c1c1c0410300c013000d10342400c01c0042605e840e051038a201511840d034070003015000b00f4000c00c02c0800010a00d5141d00780840080c4099800610002d00310b4058040d02c500101c101188140800a80340002c5004194203000c03550304d6a5925821382e0340e00401d0241c50301091140c0c65110300c003004007802c0740c0c01c044c0007000d403840c0c0151503040620344007c0ba40003040344030504000300603248042c00400d254110703202030355140d4501820050303c03420350141500704010300015000740d090828810102d0b90600700c1d0103039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 898537544 1250 898536294 898536313
    0x180d08090a15020d020a0b01030f2d060b040e0a080a26010314010603170702030309030102180907030606200c04091b0905011202091306180b060609010210020901090305 74
    0x11103542d4940032202611030301e080384080030b000050410181d60302401d509056070850f900d1a8185801103001c43c2c2e1490080b041708800500390300c1c005a1039000e00c01c0781d48800340ca8104a025908040d003210300484c0761a08001e4030000c0422081020b0780c010b0700041d0340d12000d040440749010113401207440b03202010a108a4550445001030490303003e080b120018056005205081380d000f0b00c4014100b075a482c000c4045072079440c018017071141c0002c06590070003954602090a80e400b0130384440d0f915442c0842240c0600d444503840341c2215081c0f804201160070068043c1c19061840e840c42c050301c070300302d000103602d103800c0052a644000c05401170004541030700d0121242101d4245140d00c1051501001c03645a07840c1c400c4504031000004001010201c035000c0c0000c000300a450b040c0700341c040740d8085c808038403540038100c6540e06202c00395103445041e04282090710400f603d940d110784000c01150b001d50b80d000130307120188a00303500d00582c1c4020b0100140c2c0c403103100c1d07070009000340035100c2d070b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 898538794 1250 898537544 898537559
    0x7150518011b0801150801060e190305070302010801080a03080a050411102d0509040f060f0b0408161d060f0d0b0a050a05060618010306050d050a02030c06180d08090a 73
    0x290785a4007080c1c460b40e140345d8860b40813010540d07001c4440c90000340701100400c0b07881d106901034100c0e844042c201c960f04480a240381004070081d40c005a80b940e02c00701c02041156407088959004207a00f01c003900511149a4004100c604090440b401a0351148085014020107082c0d00000e45801400e0280e69044040003405c1c229240549001640c540c4002c00740c00c52212000180400865664034641008034041100900c220240c0300045951030001042000c0411500c60141c20030583c401d80b150326006150345403188005080d440d0000303140742088503481315841120205a48484034120b6a161804100380341c000ba0f05d01b5501104508500742030003038114502d13008040142050040e641c1d0030448034107503001079440c40d1700700c00200921050030701c0c0fa613009480d0b144145408540e040e86e503400510a90900d010540c0c1d15005801c0b00380461070208441ca21140041d54840d01b01321020094001200d25201040d001d81d042c0c402c5941004401011500500c2c03004104601c0c254a405c0c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 898540044 1250 898538794 898538831
    0xc16110406120f030206060f0109050d081e04150504050612090f010219091d0402010804170f040e0708010621061a0a0207060e03070611240a0c050715051801 69
    0xa044c1c026008a03030108400707040c44180351400340010f0316415071141c94603050006203c8609000d941d9424140002c010b200300c909000107111540174a0a601d46042003144130501c4c1c598034880007400405c110811058460b08142e07245c0d019084031580711a0349851006092334580c205410582d40700240d0340c251407505001442d0907103010b076518141c040d1985005c1c18102d41c40d00d10810140202000500158800c1280d140d200b44203440407002e04a070602246143e80000720103110800b00428148440c3c25806801d0343d0200300e80c076284465524041c0042d0049062142c0720700e0000c06c3c520881e4104841d034004600405400d40e070540c0d079921a0001d80c04a802c080d040301d005018a10000400074402c0c920000d0180004029100c620300d030100c103448203102152944c0c028054140c00384950005805108030b04030944854a01c90310308600200215009444404140003091003900086140e41d921207002140242c000155500c509045003c0c03015444070304082c560810261441001e4400d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 898541294 1250 898540044 898540073
    0x307081302220c030f0207050a020616050f0c101701050436051603120318080a090e01060f020a0b0c0f041701060911071b15090503060c1611040612 65
    0x54040142d8110f0821705010380c420040e0162007139206004e0080503280140c028030071544103400c03081c001003603681c816003403104d1507a13420740b250480d0800e0061400c2a030340ca0002c400040c81c0c0740342e01103488980440c8548041c010507018682e42c2c5103003842c1304501800e0800d919903980c11000451450341d88005801c01048e0110782e80c0c080c40303000c4446007140850581c20390f82d12050704000441d51030412070040c071907202d54007620710761050200d02081050009041440c0d2a96400a100381060302c51194040180c0c0050f00b006100141c1040c2903502040d4140790f40e0f071023900390b0850307100e0340c9119080e40a05062540b0700440060b0001b4514580402c80040e480d0a01c001d2040959802d828003c8a80d8aa28860380303000c00c0081200040c585000803044000c00d10721003049907241c03030a8004c208d84104543c000308042000900c01c0d46009c200c400d601c00b805101c0c29181c201c00052411480620301c100500c88021040f8290032541c46800800140440600300c04010400782000f40d200403101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 898542544 1250 898541294 898541297
    0x120d0e060c100f0c051c020d060902032d06030709022a1b06090604090e010e120a020f07050d301d09060915030a0602040305010902150307081302220c 66
    0x40b0382000b6480c015829a51006c44103088185041ea03000f0316a0007a6000c84d072a0388801c4c0d80c5000c003080007281c070320156005442d6a81e000c6504219130305c0b0f807940ca1800c0c050b085002030000b010000a036a00290000958600030009602c0340c3c8001e4244510390710b107840c0c01800c903a440e040724009020002d28070b440c10b0303240c21680701b003c00b100040c054944a0540402d4104c2d4081009111814554021884030804d0368000100c0c0b100707070a40142015402c202c001b520407030020740110543d41c1003007941208002900038103c51072400c0009440c2e070a441c034000f014102c0c40c02c84140301c241c00da41c90880140035101903440c40d907a0071000070b1041300317142280110300c58040b0030048542000c0c20030074030821024215040300d490341005d60541c80009400b071b075403600c20050b8000000b2018000b07400250f00c00e00000c510018140704000c000f1340500503044250340d06204000085901c4000d46402c2607001444039805c116070300201c0d000500c465000c003018003c45e0080d01060072113074060002071615 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 898543794 1250 898542544 898542551
    0xc0c081506011409031b030a0b040b0a110309030909041b081c020115180213080f150906060d03090801022110030b01031211070f060e120d0e060c100f 66
    0x804081d0f4031540103c01c000342e016440b440d04900c205224003103000122100400315102c095003503031601e80407003084074211241d56921082c00307200c0045015134881c0f0034075144041d0452510f03080050780c134002c003118148501e04000128007030040e80c40001c0021842e500c0645481626541ca09a803511000d0111b0a01c2c82818211202a4810f01c42d4801c030011524002d254a49004503075948421030303078100d0040950800c80c801c9402407402c1442c2c004c081c000c001c0d01d10b03121074010190808500406030007418194900f000001c0d0000b01d0a6030740924125030310312607085c0d281000c485d071820a0300b01500b40c1d8400100556085445d954404032940c00703001c60441030b038a0031716110100805100c000c0506c407028005200260015030144010510351820b1840d036142040e40c00c2c5050010f030311550b1940d8071134070240302442e48840d5441494105035012000c04008006c140d948481c441103400c20042c0c1c102801005540b1207040b01d00d518482d0742140d11002055151034000d008241c0459a030a19 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 898545044 1250 898543794 898543817
    0x5010c26120603150c1b0f0d0e0a08070e0a021c0c02010f0b1507030503060301150605040f051903081e03010f0608060406080d0c0510090305030f1806070c0c08150601 73
    0x4689003040c8031721200a1054104407049005800c90740c072034907490075140184c090b1480200c03401c0120480c40d401ea951000c1c1c500540e5428001420129004074201e5081600140087c0d0004501190400540000140da03145074204034203040c1488003079140018182468a1113095054110362003400c1c40b8401086441415820445d01782c1141135000159081170180c00301103401400a1a800340c0302030f00110b0180d03249800d01c4078880382500182c02040c0042014018401c02825800283c142a54802c2030200d06110081200d0014031004040717800c000b0300015070440003030542d107000213800301083e10b135610b4071000452100c4600076040000c041e20001140c0d454540620800c403074040c0c001d0010010710503012a40300c0720b80c0e10103841502c91040c03d040c8444480c0300c1c142c0e1304d50296503101e450b810030360765080007200040c10035074441481c0510a0345001c80400c84a82000c10b034101064569000d10341940f070510b60b9841207030300d801003007940303500028030b880c48a05c504000d0b13176038070340140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 898546294 1250 898545044 898545073
    0x50304060f1406190b19120b0f040504030507170a0f0203030c16030513091a100f05030604060b1602010311180f1318031805010c26120603 61
    0x1602c07000980424a046408516181000c054003c64016032140e80301105440c0c0e90f0424459000c0c5e00144100e50f0001c545800c41175219040680710f00c1d6071031092045806e010001603504032031003103192207955141c011404040c007500465030151303030220f120001866540d000e000350303800c4400f65801041c10742031200003c81c808000c41c4d101e843d00b142e0032400c03c1110a40c1c0d00d010407094034201c0074401c1c1080341041c00400c1b241302c0c00c000e1070310002c00b040c01d03001c016410a21350100d106650142d00c9105807400c1c1d00303403c441d200b8849059868110b8a81d512200080d002d4500c662104413050b0b40020002e0f01c030900c0910348404d0724000e0b2002c0c045c804648001c810030748200c2c0c21401061b9001c589103d024507056807805489403008150042400131b00c0721410441d003401401c400a040410840410103401144203803101c05d001106142c0300d8644070006c0c15030600c504009080a00c0345604a000c41c00b9400c4030f40c1148845c0010301d850b600c40c850000d60100081d10340321b100c3c4c45034020126010303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 898547544 1250 898546294 898546301
    0xb040302011b030c0f050309210a15060b0f0306030c010504030c0e0417041203140406021203130b0c1206030106060e01050c010b12100f2a05120106050304060f 70
    0x2280e041e0340340e1061502482444908180c5088201c0c20421081c00d51804149442c060001ca05d000c0c4025564030b0340c070300c0c081045181d250040c1007012000c50701c0d4401c400c0c001150401a040e0416103000e1072040d02002200100301b607402c00b509810b0003041c4221800c2c010000f6510601f400d908444c25050b40a00540c1c080c0946d100041c40f00d00a03450a00060380d0107030301560060300c65150203141404015091781d040c5c2254118a844c82000003041d001e0581c4100300c0b140e154419181c5602e0076041c01002174450003803d4035003c050000001152000c00d02e0784880b400e43d904002c0e41041400c00071402202d41c3c1c80187c10040d0703201c401e000b0614620b810300c151300403507501d903c0f0b000c0e0189203040150307103c0c0c02c07086541080355038600104545403101203040c07a0a0300d040c006040c0c0c2c85400c42001e8200c0e11802074840b0702e2850b050b000001150000600e070104445040b0424000911700d500301c59520403140c0f8800344414802c00052440c5d0050040d600640c0f003140301348581280d040840048 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 898548794 1250 898547544 898547549
    0x9080609160f052d0a140301050a050f13030504120b2e0515161202120313081e0d020403031115010308030c040e040b100806070c02061312050a05070b04 67
    0x1000000d40300c2d0180031326218900e003e01c6501c042c0e0f00d144401d14000540c450545510085800b03603040345c8200a40f8080c42440d500c00d01c0c14008021505100400400c13001000300390ac0760042003111000b003454003580135580242441e003402c150000c0300b860011940e00e0152101134505810040b2200c8031141c03040310100c6a2049141d0300ea006280c00100480042a080b03400c10a00080021503901100d10419041450140c4111901c4480c0510000d01e0002080c1c941d522584062090162603692043d000400350b400c040c1c295241e200036080c03400d404042c4d81c52116600030004405ea451807842c0c0103403081301c0c0a0703110100541500d030181a11191121210814454884014000038113a240034542000e500301c0b2080c00c207512202d1481e035507241501c094441191140400401c803058440c0f250203400c00c4c40280243c0d003007850018100403c0c4a40081c03140d10702160946a0502d0712520f1030003800071039042081c85195003001911031680040503030741401071203000701e401030b145d1040300c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 898550044 1250 898548794 898548799
    0xe1e01081c0302390705010903081c14090609120c1905010f02070809090108150f070c020a060c2114070c0b0403080d0501060c0f03050a09080609160f05 67
    0x31600d20001e0110000e50000780e50104484021080b41082c0c07121401c041c01c3c044a954100c4407052941d000e541c40e0050b5548440c0c10410620000c1c800210302100381d840790385054403d01010440d850a20001d4200d00030650350700c450304e604004d0b1154001030514000c2d084081603d031403040d07000001c40e1611500f00c1d0303140b0700c0e0b01884408407003004c0c1808013101070b030080c4000540d508408068a0176680b08410560b41d5a00100c1c60340028507140056500620b00c01d80100740358400e00c0e088604041c0002c24542d0003600346400120320301d00905074002031640c028120200c094560601501400045406131a4003e02c5810300030050384519110142d4078241e00c0d80ea0b4030002010f40044158400c02084440030340e030f51000030703500c0442e0000d04043c5200700c42d0140c407500d00340403003c11140140e001c0c1c0e0422809000340008140c040300c0030203040f601450321980e1400b07003103000d8881b0310041d0b2002005100c0e02c000c00400321360200d990101545d00c0e402c1401c0c4a82d80e82c0d115a0f00c001640249039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 898551294 1250 898550044 898550083
    0xc060711150114012c0406090c020a030f03020708040e1608072f10021b0604080409020d0209090103051b0103090c0b070c091b091d0411010203040e1e0108 68
    0x440020044403401c0c0a1805140480a40c030b880f0b0a10140170030030164080d6910444203a107102480d060150130040d118020b41004002d0922400a5840824000140500000008001c640c40c03294048411040e04800c44a54603981c5401c02d14804034125175154004480080d1180400d01c03804481e07009590a40d240300400042c2a403800859241022148550b0317605005644146000d10007140005034501005072124410002d28008240d803400280964100c2402c1000203401c40007640d09071001c41c80010380340c103d68200340000344180c4220581c0040e01d84000020090001840e0b200140e02004c0c164002d034011780194292046640c008001c82281c43d01842210302800190200d64003880240c20b01641e24034580f0125560041d50034507000289684082d503036080000c2c40001e01c121039141c2c1003070547c218803081840000d80000d0001000d00740d080060780c801c00666024091f4003420b400b150400c41c41040303421601c4038100c400b4002c0a03000054400010903244481000301e00c000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 898552544 1250 898551294 898551299
    0x30b0703051b0918041419030f0e01200c13020405150a02190f05120307020a030c02130c080a0e010203010605030f061f030507080c19051e0c0607111501 67
    0x106681083d54010b0300541605400342a440c02901d0081c01240200214008180d860300650f007414601c1188441d10407880d0107000c00254004411410404249041c4005e00409070049950036440c0a080044001000154101c504003054071003508204a0315001c17603251038001401680500e00c540c603441008507030b150002121000c01083c6990315403040e0303489240b2030402005101511681134500801c80c04000b820000d08111903081d81074001051070541c940548001e54802070704800600b0000f8494007482191074401c51207810070348a4100b0b001103100300704010902c0d0021980800c1c6603003401d1920100280c1842264140c41d040d80d2039902d1076072020800862607002410030341d0400f403010b5416a01c4003c40c84050f45030081540c01240350300b409000140b0320a809003041308182410011030300540910a20b8941d082c00d142440d0340c2b506140d02120100c120425610500c020b0005125402201c021a4580c801c8000d0380300e10340e1161282030340980d6900340001701d480a525a0006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 898553794 1250 898552544 898552591
    0x60610020d1b140105101403060105150d0905010203090d0e18071b1e060b010306081f020c030403030f081506030f0901020c1507030605090624070615030b070305 71
    0x80c118214040e00c2541042c081046142d1300f15501111080220a4000b2051104610100781d080c19618100c1c000e20072541808001018280b608002103240100000c8949045501d5044030b1100c03600311000b19100c5c5000340c00e01d0707111101c00c142c110018046100b0300c5c0785454081d11044aa070307149001c60f081d598540009840c0c80320301801201c4481941c01c2c0880000700d9000c1040d0305015280000001c401140c501241030b0ac0c15003284038141420310205020710140003900740704141805072181d0070101d0301c16030080284a20114000709020024000c014035810551001000206540709070140e501e01a200b01c680c84174650441c1d000c84200041008100b603010203c0c0c0009101700010710740740c445030205103020980030151422102900401c0305194041c86040d00910f8156902552071078180005000c0304000ea41ea02c070031050428180e103c0408620031740c7c91035a4860f00c00c0110551902044a0103001807108031a19801800020300701d038403034061076010307440300b881a02024040440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 898555044 1250 898553794 898553837
    0x1b0206090c0301060315180b010308120609070f03050c0d060e04260403170d050708091b0609100e220510051f0e180103020f0f091605090a0602060610020d 68
    0x154440a41009000d59008c200c4a0102600862040001c15581c1d01500c1291130303420b00003012540300d0070342401004a0b00f07400c002c194020003402e242c00030b00c6a4583d01c80744120f01800b68081823803840d0980200c1c14171400c42495010301d01589064410074a88010a01c0e14903425043da400600240801c00018007000c403618082c90107031802134181407c02600d10110b81c000c036140300005001e0000d0024806091018246401d40c0b03d40c0000071451600c0460301d14400c2c030040e18014640f0a6800000c030b80300724030349411108005c00180e152a11302c203440103602c2200352100c4505160001142c0c41e004808000000c840010300889080e4216900c3d8480488807002114140240d03000c22034603650b15160031a00740e4041c94807500c2c03a0350440c01030016414510f0001c0d4021840b6603400c0840d030f6074941ca260751010400821a40d400c0c1d8200c012a038a0154101c0c0c2600f18581200209199401190051190710240c405518248202c0d030b049a0f500901400b0030042000260765582e482502d69 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 898556294 1250 898555044 898555061
    0x50a1506211407030c0908120706270c0608060904061d0613150212130609080d06050103200316180803030402090c070c090f1b0206090c0301060315 65
    0x8a04060200c1076140c21040d07034401010301400600b914100f1080680501c0b58410390f010760f142c001d030b140c1d00304807005594030305a9000600803074002c1440401c10082d90403030300c11003c90342c9a00194840c0351000341c00e01072644104842010002002248291044100c1da204400081c4880819204d070349840d0000d0480318141c01035071849903810b410f01041001024080c4110140c03514015045081500d0000511071441201d00c0c01080107107040303030944141e01c0c1c01800c900c4405142c2841842c20304000c05904400800300480803d01d908000b100d644030300100c50082c1c80c240040c58415000c4043c100c0d4814108404460500102c0c40c04003241660340b01c0e00c0d550b4145006100781c40c10805500901c4c6070700840c81e070b90001040008500300324007119008186080101e0403e10965180c0078881d00704d0082c000303020768424a2400407010358205400d511280c1e03100800001d0780d95002929603200b1120b86446208175048481e20341414400d50080300d800902c01482058010506000b0300342e02e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 898557544 1250 898556294 898556327
    0x81209011b06090c0626070e060706090609110904170a02070b22050303040308040302090613021c050105010c05060a33090615020a0f230709050a1506 66
    0x1008418001041c40c4100c2e41c1c0c1c0341c090f1340c442c840c0501e4144000c0182041128900440015041c68144030a8080a1540000c043e0500e1480d202042d000b0408074010321201034240c074201400f03001482196404501a207000743e090720701f0ba00b0347c0000d10030340c40e0068138010880c5640390721100c0f0072009413010b40f62407046881135441840d551050803c3c1e6803c41781c95800a2700c81848201c010b9071200200400800b025070107035061510359141c0d81c2241c06580300103802458034030001200783d074495209100c0e284005004540380c00144089410442c1200c0003e40400d04e004c0c000315803507004414000d04264008010305955813000c1c01f11001d00040083d83e010424003890381920311464613401403108181030b00001150707181070225400d51b84107511044421070f4402007003240c55404214070f000ea42c4c03c030b00407034164034451800440c0342e41503506040c030030300e015403a092107180c0115100c1d00f1142c0340c1c041400300d9180ca42d0103c02b01c0324001f00541c848030b0121010030655014046500078440031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 898558794 1250 898557544 898557587
    0x7030b0a050a060810080d050307030e0115030503130e060a0519051203070507060c03080a0e07050a0803091e100807120f05090d0c03080a09021302190908120901 71
    0x580c1c0105640c0392080c1c00039008580d002c4c0030002d00381a85101840205904001011800401413000c1d2840c4005000d803000c05486550406e6030307080c25002904501c000c08490780c0c15039540e0400329203c0e0402c2400981956200c0340005101c0003594009004460080040c8885443c00d0100944014500700c200c80d4010680400542c0ba9260800310524000032400b03584e98001c2454180d04081c0c06401034000c1c0101c012030039000c290302400c1c1035888500504009003410401c084c840c03a003c416402a030f88180c4c66540801e41c95004401f4210406040d101c1c0581441e110780c050200340303c0c3d032142c160040c3c4081c81031050300d4030900680340c105465050003e03640c03103140c022100740e840d054201000f030380e00d800a00076150020004807081215600d00344c0f608203004d0381c0040500c50080d190b01812130310380d01000f00b0b55a030307154140001000c00000319500c06144000c620340d40a810803540110300d0704040019100c001058001c0840d07144160541f424004000655184251442d0075654404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898560044 1250 898558794 898558799
    0x5100f06031a0303030f0f070203030702030a03020904241a0931091a06180a0b0613080705120a0c0b160602070b0118020c0a0f260c0118080307030b0a 66
    0x3c080c4015401188681d001081c245000502d000242001801c540d04641c0104100180e05e039020050b118090b156140269550b940140028050580c0d07405005a2550102c80e00340c06d1200700c1090012900c20a1030030112407406441280b45010365800c258200345480d98582c69007441000306c3c003030140604041e0107054141c08a160494506aa04440b0289100e8110110040c40d41090303510240c212a281a00c0c9000c841c20b203000c01000d084a8074098407448102c4295891000f50b500340640c2c0740c00354003070030b50b01c482c00d0b0359402151040c640120074102c00b40f00680340115030307103011a4001245050b0649865071030003103640b1070030406080d002000054000940280010560540640c010070159410123105c03410007440c480304020440c2c4100300b0700d64620700200342100030316041500340b0f0007940036040c2002ca05480000c02c904034000d041c2c0b9069104002c0b0301800c601c541140080020085010400c5400c0880d528003034848501031000884d601e20a4003c1c0401d00701c0a8090607030240e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 898561151 1107 898560044 898560049
    0x2130614100201020c0a08030a15030807080f09270a06080a060e030f0a080103050706022e0603061505041503020f120c030714010305100f06031a 64
    0x5084001d0181041e8000c1d41030302c03000e00c8010709542e400092031030315032a154030441300428201c0c13030524072414490180a01c4421707203a20005031403902140b42c4070005240c00c030254980c0c0d01d443c1040040215100c0e80500007160401440c8595a202e006101011030180200340901441c0740c50420441079400040302d0344030a4002400090700200084694114441d0b400e0f00741d01d8990004071280c4103a8003400445c1228010010703600c0c071035111340c012a11030040c032000144600e0750f80c0400e213281e5510310040d5100b5824520014030141d481c0e840c00160786880564200e130b00005202080a4107141c0500d2540000411843c10880c1c1180e0004003880c0c03680202c203004001c41500c17000700300c0080141d55011f81c4000c045a0095550765111038940040402e103a0000781088081188411160034070b00c152460881071500e0075090a4040340108401400c015107240f03403450400098 = true := by decide +kernel

theorem cover : BRFrame.Cov 898381294 898561151 := by
  have h0 := BRFrame.cov_init 898381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 898381294 ≤ n) (h2 : n < 898561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
