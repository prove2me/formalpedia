-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2564
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:58.445365+00:00
-- url     : https://prove2.me/submissions/75a79fd5-c64b-43bf-8b35-3e0c79e4bf3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 460971223 ≤ n < 461151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 460972473 1250 460971223 460971229
    0x509040f05010e070c0c05091305100504020a1a0d02070309030203150708013003020d0f08010e06210102030a140606030727050a330e041e1a 62
    0x1180d100001050402041d0316010002c40240c030003a18040c240601580e0000c2400600e11044d009000c02810541c0907013040c125141c00c4101180d001c0c1c07450b00070380d801400340d030440d800b80341d0017581c00403d020750207810410680c80e500980024a030241c88100150140d104550014112140c002c0e00d5400781d840c0707503006050900380c440d0100188030140d001080105a04010582d054600301061034999170101e403802c2c904040e403c0d8902c000c5041d40081907041540c0004c0c15007456105581d04140c220300e01c80c2c261803820b402e000d4a500012030500155150900c234550070301d889140381203107001c04400c3d40e00e942264402d42e007508059440d1003030444030303038000040183c00c00c0e01070301c41c14038610300000014501d16440c1607a5105403012072400302140c071f0903000b00010301750040c03456169660f01c0d060a10502c01c80700d802d40b600301656203507007461100645007058040c0a03454081100c4182c2081100610078101201d95020030494a0308203441030340300c0c01c2485c8540840400c180c000c01780c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 460973723 1250 460972473 460972481
    0x20102210901060b040e0406050a0e0316050d0f140c03120f0105090f090c0108090c1914030109030210020a1404060f08150d020111010e0d09092703121b050904 70
    0x131416600310204000c00c1601e0030f0110490303006070001c2c40080c09464104001d400f41c0b54652a01e0f40070312000c284e109203ca41c0941504c1c00511500c21a04480244070050700c0700c0702c41601160105140300b0011009143c910001c043c42c0001a003900e1401d0600c0d0050813980105842003d10100d0107801401141410890303160040c0c3c404070f20221070301c1c120020701c0d541c0b81312000300740c100010100840d007503820811001304c2c2104000d2100280805ea00c041d00c3d049140e9100b44010300e12200e550782445d00f010301c00c80c41d1603901540600b00319600c0300c40081c065030024110000b04900c50600045504031440076102410b80f69584003215400070750000d01800015016221540d0002c4c1c01040d1035a5080e244280e5580c2070038056403054007107400c10300601a12454406c1c900a001c906520703d0b508c98100800d03104584000c00c108452003d8080c11840030a85003408044003c2c401004a07010346040e00d210508030f040031a5668034107440305a562000c000c040e02240d80841c10314554074050007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 460974973 1250 460973723 460973729
    0x4170d05030105060d090303060306050c0a02010b1203040614040302030106030f0b0f160f14070c0f0e0720010f09390504270503070c082b02010221090106 68
    0x40c0160840d41002c0c00241e6901c20030041c5407120342e980e9810800c140c0650081002584c1010080019140ca040c00408582c0728851040065103480400409440c001d05818504000d00b40207600382818144182d900e9400080840e1060b6400d11000005a4003400303140c0c09548141e0f07201500901a10f0120b003000c00240c031a03800d81c5000c0c0108081c5410b0703440307540115801d91910610320904050240c51105540d145001c035414002440b20a00c800031010f4001c641310b004101101c01e944060f80d00704032005648010024084081e100c0c40001150b020034009865800001604411412070808480d030000e02160861424003c03441e10010703052a45085542e003401900b400200d0b0080c524240b2114094a48a550b865003584100c2010481900203482100e152180741031701800d05a6583e088201e007210064010031020551440c0480c000e041125080300924002d01181c07610921084000e4a00003150740c00d0016081e2a10100800d8000050350301d0345580702d08001d5019800e480380c5030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 460976223 1250 460974973 460974977
    0x80303191802030a02042310170a08090d02120d02010e07090e060402060304060b0306010603050405011a1f1e05030105040b0a0b0f0c031b0313060201050c07020d080c0304170d 77
    0x30051101580740400e000c50703080e034115000544801f2154545100208a00141c8031540b880410461071494104040099954102e14042036140d6421010f80d18039038403c0003018490309000421441c201048005d241c644000e013540c01e020350628499241202061507040140e445040c9400b84040034003002d07014007040c01050040f0182d20413820380d61000070740300074020a800030005003445000d5100d450341c40c038024240d82c99940d490380020702500080d1403d031415480d044009039035814402440700d89807000b6011124142c100e640d4040c240f00c0a01c109e40c240302515007414040307220045070010203200c1d611110388039410002440225280d941d100c42c09400d803218103100354240113080e502041d6000c0f65080d90b400403d001c150540c0600c202c80c1c40c03010f0710600603020521b000b0000d02003203440c140c4079103001d5641e0401207090b540300b5641c0704080401080310801500300031054401103030081c10581d24004d8200082c620f15481030b441a03800359140e0007283d0180c0c40901120740c01d40294 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 460977473 1250 460976223 460976261
    0xd1b1805101d041b030b270718080a0b0c071a0915070933050708041d0403081501090603180b040b100503010e0c09040c08030319 57
    0x45004585401c180e055101c00340048a50002e81e1402d84800310481a08090700600004800a04203e40f0450481c02078004c64240030400140d420010726250a1070ba030155a00700d146406c82d1282121407014148108011600c04129101c440d182103030001090f81c40c00038540c50009041c03404144e403001e032031040c81031420818038002c079001c1c05020000310031820380b0340d00d203468804101d8501408051100034000320ba504001c004c94001c0340020840c0c0003100000880c0646240a00c01401820820540c41490180106050740704601070140315100f03220840c903260b1500000b40a940465094a4409900350200010590700c960020b410207050003007200200c80b110700103880e600303190060804141e503c01c503c8020b00e15903461444603a4000c1c00e0308420303040504188106407002c0f680e001c901924a60002b039141414070808604000b6000a0401140c20408200400c43c0c080c0c0240d800c181c01c2c0d68081556041400218050940d4000a040c1006c55030b07610020354041000200400c800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 460978723 1250 460977473 460977479
    0x80601090c0e030733080f0a02120106030f06080105090601050114041d040206070b0702160f080316080702100f0906030c1e05041206020705010f050103080d0b03030d1b18 75
    0xc000b0b404415140b8070207002c2d1400400d0840795001c0d13181d25081c45c1180e040c40d440c0d855502d802800300d601800d05000c00000316179480010710240d01c121105001644003500040051038401d40c80b00220340300752880072035010303901c08485094590507243c042d400e412641c0100f009603080303d14110300001c2d4a00160510746455560164041c0044160052201040000c1d00315680c0743e048540f00d5920000e1140d042c1003c4000958a11200c0030400e4000c41120300451221003a4444004803410a03000b1480c058240001d4070b007500340702070115155501030203a2401030b40e43c9455103030b230301780c0710740c0c1d1a030303d0500481c0b0080c054252540440e007498a40700e00c99070981d40c414a00030360301d080d51400140d40140018105c0c0c5911455000c2030040c845401c2c1c0b5804c001301900140130881c046c8000784400d509141120007110000e200c014070001c1c0070020110904100d40011001c01030080540e03050917403c04520080c0c0d02c044080418000c1010200d0303202030781001001d600a1241c01c401c45441d81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 460979973 1250 460978723 460978729
    0x3050604080a050d0207110901051e0d0611071a0109020304080f07020d06061e0807080601120303021c0b1201090b06040f06030804060206010806010b09010203090409050c0a080601090c0e 82
    0x40040c102805003580018005000c500440480b0141c540480f4110741e6600e4505011030302d19840c0100500c62049100000b605140c00501500c09003a41c0071070242245105040002c10798140c2c00c1281d805850b6504543c81000003400ba100c45400742ca5405061440f07071104e00300c9080160420580c1c54414401c0c030011503012015540070f02110303c401a596030351070000a03110140b408000701090300f0301d00f01003540c078206007070500661980b0740e8003048581c81e08a07080e100c40c5603000c1d4600a5004c40d00410042c8600c00b070410403140a8140145008180059280040f441c0b6030140c42594403401e134a03107903080100e84540c01440100081024031010f170765405040340080e0400d4895503c1d4120b04902c510181c0c4604015135100f50074650300d40da04d03080030b5100c900910a0203502e00501c00000340c07031200c01c8112083e000e01680603520b0100745008000041600c50001d440a10400f6607109580d1900884080a01240c5009180540c500803080003900c0f110300020007004140780c0801e605031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 460981223 1250 460979973 460979983
    0x9070b070f02060909040c0819050d05030c0f13170a0b07180f0312020606010c050a030f050405031b040b0109060503010e060f1801091d1b030316110310060305 70
    0x603a101550790140c03401400080c502d40580a000355004c2c078220103010070000030410100072200701c202940d801c004982400c0d21a811417000241c1281c1042012031000c41c0b0034401164070503c00785030b0314284426601c4d0f4682c0790b000b910302400c008040c05c80030701141e081100c03603040d0310100f2001440403900b03503920070042000c05000c480600403442080416240201c074030388040d0900215544d0b18a5a80c10060105401004110094000c10010480355481200c404c00b003d6040310080808286a030340464840020501100400c1010b10010520381c1e1300f44086000c06480710304c188210092270f0104011117a804110505004104000300500b41e04081504d045401e81846a07507a95140d10100354140702032050582c0c804109a00d041d0220758101321a4103035150584108400c201c4100103180444118040d00415071100c4a0303808510700f107060103280041d002c3d041c0c904080312800414641d040b03548040311308084050303180c02c1c80d041c1000100824404001c1c240801440c540301d0a840d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 460982473 1250 460981223 460981237
    0x216030c031b210210113114030c0913060507020c01230d0c080f0106021203060d0f0c0f080c030616080c040b030a09051b060901030b010e19050909070b 67
    0x302042645044507009003d81c4c0002a00c0d0721040c0300249100c11644181c0d80410000d01d800345040014040c1311100100c0b41c40d225a00044aa028a040c03480c0300102000108d441541072095600251803a1510050310780180310280041c25507803a6860000103036030005142c02c0455000022101e1147c1e40700c00b00e035070508400511015046621018810640f0450400d1001e540c03c1440301c1c0304203903100781d03168841c1001d0080002c00e644c0340c104c2280c80382d00340756640c00c0b80c18051003c10050700e80b0260b045482807140140c03a03e2b03c5510b543e00300444045601170720540041c060100300c0c0000a109800111a04a01a11091a2511070714055280c4c110b00d01c0c0c01c10011400042d504403c2e41c084902500c46140216101d181025914026211050048546005144200105c1c0d101041a0845400000c1160381003160a000440007032003050340b81410400445103a510756200c108035006c41200092014401c00e01307060034880d10344009455101c8960000f0010441c010b60401a5060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 460983723 1250 460982473 460982513
    0x12031d0601140103060f0605190306082109030a03030b0307091503030f0908010912090605070b0610120f0509070e0118050a0f020d0605010207050d020f040507030216030c031b 77
    0x1e103502c0720040340101016040458079036894540440c1c01c90b0410050481007035061000701107003d40340001c42c25075040d88100e071219800794080511156400d03004075521000341200c43e09081091001034030f131030505030007600401c0d6903d502902504041c03201c5400781049650500a825505000c00900c2c1010321000d01000665000c1d020354030b100e0145d640092100400030300c030b890105d0814464070302005003140040381d0039000004001d4003620a94074400d801051001c610350746d4000b0b00c400f20035a03042d4070040007012204c0400755403980c821650a01d00e401400919440e01c262a00e01d030030401e4100f000c1c03403c103400c010090a0707409005400109882d401c045100e8403880070580140c000c080080c2040c03800810342200710001540039004079a802d0f42240d4515540d0020300000d042c2848002e9001502410100343c10704160b0882d0303800ac03142c1c1c0780040c9407041000820312003800180c001c80004400400e071405050b488003070201c6908410864000b503030700e00d40d10310b40c80d40c02508009803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 460984973 1250 460983723 460983749
    0x1a030a02280806010e06100e010c24020f070605010b030412050901020c0909010e16050a03030c23030a022107020f010c06050921040b07080706061212031d0601 70
    0x2140c400603001c20001d0601c4400c07141c0c1c55031140c0ca182c60301301c0215183c900421201054003441c1e07204600103592054180c440038000500350321991500c001000d005081c184880155012098851000b02000c0c09007442154403110782e4030b0b2860a403101030703212041c1c288040c030070b00000c078000400425982c80c0ca81403881d9143c2c1c080005070708040040d4103c076840203030781040046010043d0401409a4182c0c001d99680310030b107541408900c2c1081c050240c2100d009001400007038010320398a00185e00039014491800346903140701c5400c141d803030342c011619003001c501c00701644c3d01000310044843c000e04481410f0f0189181b41d180c0d40c029014040c0c070030015035041c0da440742d0041c0004540c164000c0018081c52a0000c012962140440e40400e0070880d5000d214041148038005e0707405541d4505c0a00e4074126250320382d80d00ea07800c10201513803810741e540300001c0c1e403000c0c04030284611807013000c000e82c1a011800020301290f140b800c1c50b4286800c101e4070205e80c0e90000c11210705450028400c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 460986223 1250 460984973 460985029
    0x51b01090611072906041a0a08010903080114060d1d1002031609030f061d010e070905070e0d0605090114100e010f0b0a0f050c0d031a030a02 62
    0x50140c245000c001d449503180070040324110141c2e600804041e40985160f0b00b1031662150b103419681c1c01040c400d0308556164000c01c5003880d0a80000000b40f000c0380d06a10600d0003071002525003122503002e000d1581d55070320381d0800c0541120f11640108000a80d0f14400c246c10340110760641320f807018014078160f0307038600f0030082940e0100d90820389003083c0845100b0704c80503038800004d41c0165019a082c0d68900c00e0714440340e208008000a913a40100c3c01641107220350368400140c0584040e042400d42403a601507070fa81e001340300e5608043c1001c4001c2003428901889841110301c05400300c0200035810104041545840c0820030411f41d01541c0080d49a54420784140106500307040115071580810a100b440304000e05681c05840c03c0703c407c24800c0c1d031b0305c00341032803424035910503008000b03070500a1b5015140074184c06460203140d410103e00e0181c03010491400d007281c0c181c003030700440d07034441076440160346011207849540000e400811840100760000f5801e09210580081da5000f00c03d540b03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 460987473 1250 460986223 460986277
    0x240207060302091c030e211b120d02060f01090c020316022409030d110a030e1504090203070311041d1005100c030210020405010903020f0a08100c0e040b0105 69
    0x200c81c134071040c80d4221034021040c0340080c2140103085207548200001c2002290016540151104010103d001410543c0412003400c41991002c6034075940705480d0340706121044401d0200407103104440d8090000c919010aa05460200c1a0044a030481c645076204885d03640010403960300010301c1a038500542a81d100041c401d080342c0d00355981c0140052058000440c0c2d960240a0180046041d03648c0d500d40300c441103c813003440302e0340e45c04294001c1481c0b201290185a0315441004082c000082011105d1810700150b80982d01c0008c1084d4000200701a190341803180d0110500502546450710b8601054003005500401c0c2c0200321100c0c00020454a01c44041d180c401400f002d0940d03500301504600c05003440d07100100550241c010b0030080c100c140f40303034421a0180e444c16125000c140c0c0c1140c0034441488440c840d000d81080f42110007042c5044200a1800184420b4802044030038015000038010030070001d280c2c0c080e03420403441000daa0382190a0390070601303280f00840b0320007a0205032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 460988723 1250 460987473 460987489
    0x15031a04061d091923300a091701020f0304030c05010b0907142b0207051504020a03080c010207061d07050402040b0f09030304120602180907090b0a0e04051024020706030209 76
    0x240c032841e407140c07409044410b08542e14003c042e24291a120010701d03000f010040c031b14450402c0c0200003c1c039070402403150b450ba003400c21a40d542d9a9000508003003803a14180c0711303a401a2016404142c0301c060303a10401c5802d00485107030140954580d280e6041c1a40080c129a03010040e400c1400004942548600e0920215564003501c14500c100b04100d01e20b80d04000354400c01c0107071007a00820407142c0c000b80c1c00c07581c52401140c6c081c05c078409240c51519102c800740c1003960100010754003000b07982c000c5011346c00758030440c41c48104080d821905911605103888240da00545c060b500502c401c10000d00414265074040d184990403542e20304000b8002800c1d40724a41007048500b01c0c40040707005204c1e2035800340c40107040c1c0100e0200075540e07900c00c0108007203040742d50b10b0014140c1c043c148081102c0201415101141e410640d1180c0c86000019042e140200c0d6076440940c0343c450b04000c2da4201187c1034003100d810070f0440f650383c200000029105c3d900c0d80184000c0c590001074054042d224110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 460989973 1250 460988723 460988783
    0x200d08070b0406060503160e040303060b1206030106170319050918072006061302040b04091b08010602281203020711040615031a04061d0919 62
    0x1949954584601d006500004207a82c01d8420500e05400442c3ca07003400180f400031240c1803c5440d0780c01d460541c91410f22400280200c04142d2103070700010700e080102e0b000e00071034140036241d60090710701482850300b1181154004d0500e11200d0b91052295040402214561083c8242641005c0c00114080c2d03103c1c0f185048035078201c4a04d03220500329640c1030643c036000301c0302c6940b59002081c2e12001c400d26160b09030f00300c1041e03405c504082203d600c0c029a0740300c9a513028401c05410f0503640c1c040704960303403c554003109085496103281205000110b040c00d40d0140c0508244c1c0d995410000b00955502034080301d44081c034240004821410030900c00800159400f191f118100c0d50000c81c001c2c00394000c450121007044014403074200301e29040c002c1d05c0507284050140500c01e0f80c0018220080c010400c020752110f01d802d80812500d07100c1d80a144050611031701587c40000b6490503481c4040c400514171200d5400c410a40c0041c0f050400c0c1d1301150341d8014009040c440c940c000c0310b44405880c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 460991223 1250 460989973 460989983
    0x10b070f050f190b0717011e030804060c170c0d08091609090b07021c0f0302070605010b1210031203020d0f051006022503020d051603030e040c02010207200d 69
    0x7030751403c280781c01c103102d00c0020b0388282158501034031840000d0707038030384d07056803805030402a00740051110b0010130300c000b8560780c05070560150687d96074031413040300d41c80f5401040024286a441d50b080c486005000403d07a540c0f030f03004038540081c3c1e00d0000d4440191030aa0340800a41002160b1844010004a8611001e1409203c001036444010000903d02d1880445a080010001422050000c2540440440312044221800d9400c500440c0e0204200c01e005050503400e1000e003002c100188580707401390580d004040d5a401d5100203003400594000c0c800101e40c4202c1c27005000051100c50120308030341403802c002d40c907140494604006008000d400c500880c2c40c0c1400c0128080d0250b8031241100c5003502650000c0c0a4820001c6c00241c100f401e103d01c080340c0301c0081006040040c1c04a19003070050701680e081c544000e804603482980c951081c3e0014600403540091460709205203030140103e40000c6162400543d54174481108501d88025460500c0e5404a001e8035070b0400c549510b40c1c03123 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 460992473 1250 460991223 460991233
    0x809010e0607150f1407090e06011b0506060405131e02010903060c0804060b030a0515090115080c0f0a03240e07030b09012003040803070e1f020f06010b070f050f 71
    0x3054a1000906139000940c1d6043c0c05c02020518004410710b440b40694174640e41d86a020b4240748001c0180107003d00810304001400506280300b000300d641842961b84148080c02880c00c01900300402c0d90b9004d030030030404650144104000441c1402c02e503104403840107100e0505c101e01d000603942040e503a4805441a03003818030841d5402d80c0031164030310980c81f48804000c400c03c44800d042d541c0c807652500034400d5000b03040c5030300300c114108440d43d0b01201440c00403c1298a0200054411041e54400e009941c4082405074440c0740811111085850544c2e800342050710f507407038614000c030180005500b501c2c1c58040e501040d1a040d0404040c0ca290202111812a070713034039100980c04004c4038060354652811510014030812261021030740c3d0043c0c9442425500c980e15090103a90001c1d0034007003031101039101c1c8090f64841c4903507000e5803900e841c4c450400c00320050001c3d0400e11311310041070781c94006030018050200480c0c2a54070741d0341c010050700351903040751500e01e01e009100e1482c0040b0b071141c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 460993723 1250 460992473 460992503
    0x30a15060b1c0507082809050f1606031a1e060c0a06050a05040b071404090515090f061f0c020303132103020d0c050c2e05070809010e0607 61
    0x281503110300510802d1040009655505013110f05c0032041d41e0b0648002022415582c03021404117030700e08540ba0324000011085e91613510f8916120580e0040b9a40c1d401100d0740b0105102c41d0311001c6c000780010305041c0110001840a40c110078500b1680c40d206500b60040700782038030300780482600e852030043c00d590b1fa54112041c1c0307a0340d10b1083d1201186e00d1424080000c041040d18003c25025940c0000a000c042d114800705541030166000c100400034428040055452140e006160186100d81740280400403102d0a010318200300510014040d1020350500410342c4030503074002000e507081c004c0203001c4811703034204407100c4048039006941880080b9803041a146101070071030485030030f004404c03502c038a51459840701081041010300945c0018803100c05090080002101072032050042d9081c0d0b0306028005040f0640c1500001900309048201c51240c1064502c0e6498000c01d508215040c000c0ca82d90b900c01c140f180036446410842ea22400e461151502015180c105030312001c103100c4102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 460994973 1250 460993723 460993747
    0xc070203010c030501180204030b01140112050f15010201201323040b0d0f08091210050601020c030118060228120b0603060d02040b15070b060915030a15060b 69
    0x1400c6c06405c00111144078007450304940ca2086a0882e541300143c42e07101d82c03824407200018109600fa0070305018015100f0b0000c400c55100e0940300311002c900e400c02034103080400f584292199040281903a142c101c03040c00b802564040c2c813040102c2c04071104d81c0c44001240807101103841d940000d016801d604040d5086082c602001d00c200002134404000d00451001000018488604098007603148620300c14003044050000b007890b00c03800703002c041c2c0d485680d03151240703890072100413412110b513140c0034080d840d07038144401807040c0400c4009201d01003080045542d84403510030001d0100f0350000d00700c20300c240b0f07800c2c08404204040882d9400341d10000d002500405560300c800112525194186e41d0a01e40380094a008550103820b403c6050056800c0c0300042c0802d052460b405508008800b1001090303000901700140700e00060071031030602e0010310060341d0f8040e210012401c0509a41045610005041c1810a0f00500ba680320344c0305086952004010941240a1000000410100d401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 460996223 1250 460994973 460994981
    0x1e090204180b090c090c04090b0406030b192f0705190c080708060f04030c06060918050c0a061b030905030d03091a0114010507060b1206010e010b090a0603050c070203010c03 76
    0x3c03c10064503500d11000e41008000e0b08200d540e060035100c10702041c480e94820ba8814500707014080d000003841030b284e0325081c2080104031030040b81401c0c1c00c4000c440d8031102c2d006940344c80d10000d407249840003101404001c5040f41542c0d07040c0507803010400c0340070b002c1c0400c5900c003807562100c000d00001842e8185100c0406080c0a81c1d01a80f040d464000b03513001000641d1481008a044000c90030745403603604803641c0b00980300940f1410f803640070109105200c0d100d549024208600301d8000d140700752601c03d05007100d101a49200314004481004440c0d04501b002c0d1a20302c000c1c0107660354080d10b25043e6400040d07500200e802d4890904060310164141c1d100b801302502135041100705820881c41c0401181d800d004030211400c012850a03075650060010302004c034803511001c0750300c0a25501050406400700070511040d8019001005426640801035015021782c0038441d113050710000120b81c98881b24410307101055500c20010311021220340039a100554001c00a00600d014407400030064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 460997473 1250 460996223 460996231
    0x8070209101e0b183f070e06010503060102011d0c040b010804170310030506040302161202030705060f090301020c0714010c0822080f06070818060a021602030d02030a020705041e090204180b 83
    0x1c45d1007500007080407180022910101c40400c0182d9040340e44050044400341c0000d0a02030556484212091452191107000000310600d04010009401d1500070001a103403401c000d07d05024181c130511001c40e1401c1fa00300900d108588409940740c582c0c0e05610f4901c28142c3c00070b01140a0034003403008069011071031403c1d0180b4036018258650301d540f901704607124184002076043e4030152080250341050b1015004015010741500d04040c13240c0082801d99010000c20455900009402d011220602d035021170445002e1800401c00c00103079450aa07107104080700700302901000b0806c0fa180c155805080b00c043d11082e41030302c400022400b49203649100c00e8030084045034056000503040304031a60740d9130081c0d46210082c2075917103034401160007d40c44410f0160704200030700303011005610100042a042c040c1c40c3d000310f9a03200d040c040241440c0040c0c0004e40702d20b05100300700180e885015282140c801141c48009092080b40c400507005041645410581d40c040c21001424080004920307485 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 460998723 1250 460997473 460997569
    0x301030c05040b10050d0504020f040e0609010f020f180307050a0303030533040209030111030103080a080901090221150a090209092808070209101e0b18 67
    0x402054404c0021401a040940d000240180001d04201c40f5603005203800038005800304072403c07984000b04003680c205003d4090360380d20907000d1020300c0c00c00f40300d41d40100c2d40240045007007429240500b401441001341c800f4500d8143d85507070352035039002e10a44e070050000401d0b0b42440345c3c0d2854040c0140200705c0b190b01400407032900804841c2182503074081111a101c04110f1100d000108000007074211140054140d03582d0185250282e50100045002c1d5005006c0251280c1000344014107000e00142000304036410f000c903c400503200d110102007490700541c1e2903c3d4040d04407407801e1601400e101d003018581082c00c01c1c0005402c0d55070002d9200750082e135030200c0079515480c5807030741c50f01710340c504880310025125848041c14148506a9805101e040c04524107a00b68000501402043c0c0f1188c3c54940151000c000c224881c902d154450101805120303080d82c40c103603402c407250260620034000b1101081821400760307a008011200240443c3c10804210100007180107140c42940c90510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 460999973 1250 460998723 460998731
    0x61404120f061407121401180f020c01020706050906010609080604021e03160f1406041a1603081503060402150d061a0a02010606080411010c06020c1b1f0e0603040807080301030c0504 80
    0x2c6c0341c1003180e04581070b01c4036994002424902c900c41800105110705100c51881e41c28400820411002c1c00205a850b0180c400071601d8144003001600300401a0f11003010710103809020041503001103401d42e44260120303003000d041c45251040300500d004d1800324039414019010303170120403580c24120b0710649014445542c0c2c03940e101c4062a0b41460303c0200158030440511081011510100051010070440704226003442d003108807400e2403903681c1100301c02081140e820000c001000d8052100030200481c020002e5090903004510030124000300020700a40004002e40048800d400c10b10080c24080000d02000380402c5010500e50002600b020055003001030000d54a0b228a05190107507070441c03540744400c01c001d001514068545481116100d400380300e33246100c00140440900d10803005540400e440c001d00400101d55000d4100c03070a109400304011030b000390300440f03501e50030380e080d035070599240c840d410700008502030060020487c010010000c820403180d40e00d02c1703084520a64040c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 461001223 1250 460999973 460999991
    0x70e010c150c020a230304050d21212a02070b0403061a040e07090b0d0602031807082413080a0504060f02150a23090304061404120f06140712 62
    0x1060300303080c1c005c1e8044c142d4403d10040c091490072210752071a042c800d0012126216035808a4009100d031100f1075800304203450305103d04190310072011400d411b190003003004403081d510081c40101d424a0b00b007142409408000c05035a40c001c01c4902c0c0908044072085032100d5582c40c140700a80a0300102d8042090040c8603d03da43c2410b01410001180e2030008d0f104490408010b20010540c560442d64000c401081b0000400c405100860041041c1340340c44000100500400b890702400b81d1000c00c00b54400c44482d0040394801d1244c040c80d0301000c40550058907000c03205211405a810081c001420000e40d007810b03a50000000d10071510241c851a42f000c2c50060240d889002c8040e00742181d85c540000650a00456441444008013031075024604c0c0610502e0030000311030461f0b0815203a4000502030001a400c240c617603002078403148849184c00d00305541c0988a0200707031802400c01a0390315140702040b416030440011221550303001c801b107242c50080100103c0345484000c0c0300700d190a43c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 461002473 1250 461001223 461001263
    0x71a15090a1a1c080f090d0305070302160f181e0b0a0b040b0403061107140c01030b0906030c06070503070803090a170c06010e0709030506090c18070e010c150c020a 72
    0x582030f04203d02d11248007035450742e00c540c1c0c40c1c1e5001680d04111002e0800258515542d45410b845415000303650300c949642c06403401074a0700c24800303a4110001b001c00c008000c1d82c0401143c11701560359400403000349807a9030301101c015280320310f0350014083c1c00e4201c003515800c2c650f0100eaa0030303100f200d49040700342d0b40340032600d028400d078091040448030401c41400420000d411440d022a1400d03422483c0c1201521028015820b900722000b181e00700c441074a600e580d0502a15035095400c55019486041080009a440002440050242030003080960030300200303009551142d500044010b0741c9280c4080040e4030380e400058200e84c0c4007860310f95286d0001070b44041c1d80c3c4454403d001414281d0a03d58800c4195000034491010802d580402000190080c480c1900640800c0001c010451200080140d9105900039a1351140110020030481c42d82c0b008980080329001c1c01c1a07203001d03145003440c030202d040258014070b40c982054062481d042d400100051000e006580004d8040030b03807046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 461003723 1250 461002473 461002489
    0x2160306200403030e040b120d030c08060a050a090c050f070809150f16051629090a090c2c032803140c15010f060203071a15090a1a 58
    0x1307400500345c0b04082005084c10f0f4441346400d84000e2418400440740a40b20b458800701e021403000007520303131041d420495084a210303074114204640c0f6616139814000442c2e07945e40c19204901c1225101c0321a4604140500c1c21120980401c0000c55680d201900704a54550b2001d01c025000d005164000d4a0304ca11100642d07404111110b41589044442034074001e801c070740c019051b145030041c000c2c890368520208940d8001440034060b0b4880503da07013800517040c81200641e41041c0181000501400c7e07441c8121103055403407201002800b0100740404446a00207003070f202c01603005610032543c03103440310420180740540803030454190440c140918100a10401d8500100c02003526840380024000c0c03079109407410000b00c085080001c0040594904841911884c011501c0d40005110301505200c00c84090440350004500d0048255120104d013100d8415800000e0307544030110b950000c40b0011641000802003c07844503041031f1000300300501c80d40c039519280d00c4106914441034181019 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 461004973 1250 461003723 461003729
    0xf0f190905011718010510050f060702060403080307120f0f051015050912030711011101020c10050423071d040c06080403051b15070e0f0f01021603062004 68
    0x2d500b40400550b4840b074022840d004d420a01d40300210040b0040c0e60300d092281d140320715103488490303210600d0a024404419006c00040f070164400b00f244d4405a11900c00701c0f402c07039600c1548543c1e25030f01e15004031042d0400920342500a41005840740c0800d1642d0813103100034801050402c0345484041520200d4003071407092500201c6482420780c2e060380120090113415101903c0480b00701c12091403e81181c2c001f803000c440043d42c0c456a0146940d005120081d1440a00021894001c03002c1d500d0355100211550000743c0707030b241d04c00501004500100040114100303141442190b41690010707464020386e014100006402c0d11480025000f60041c190003079820000c0100e00c1030402c2c104540c0c1080080c03040e0300384a0304000d425040d1409000d040a1005000c02130b02110740d084103040c81c81c0d078015000804100354440225000c2d5142d40c46000c0702501200e11803c1180321308010713070810442d0305e07254503050510341d000028404190080741c6800b0704507241207402640882d42e0302e0f50b4001d42c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 461006223 1250 461004973 461004977
    0x6030c050618060306061308100b0105160b04140105040c1818120516030306061b110f12070801020319140f100b0c03070c06320f0f19090501 62
    0x20b102d0602400c000004542054020745402d14010605203080c070700c20503691250900b94810301302c032aa942401d100740310202c20f017460b06c0c4e480c0126a280035190001c11110240480e415100480d003081020203081540c5004840244482d203801d051034030821026104000c520450007500c2c80681e800d92090b00340080407190382045040340c6031181000b1030031940c0c402d02440b10400c024440c06820a00403804a4401d9034081919801c02400409036504200355526004406c0340000000e000f444c62007400340c4e002e4403074000c0070081d480060417002c80300388403803030a0160400100e00d002042d0000c610a034042d00078403d50064400c4090115a18840655010f5280e900800c068140c02c903035141d000040508280111a25184119460703800288070340110750000500001300401000100300404140c02c1103114800c3c0c6410011402c0d402103030191902100c80d02c0d140c0b401c0039030015a0f000c01040b403130701a100d03200c04050580d01c0c1e0040380c449400c800c00e40c06c07520403140700d001303018203403041a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 461007473 1250 461006223 461006257
    0x60b0102030a230403081204031701050a0504020a031b020f060c07110d030314150126072609030c160503030a0c05340b090612040c1806030c0506 64
    0x515070480031028003030b032030043d8030000c00000000c40c132800b003e0220b2900d6036814062a081c02c0c540502076604505107065203044071801006165100c0714000200c400948016030784042020f021030080130207501c280c407030300c5001150103500da5001441003c18003410b02100e2035901c40e44c0c00d10032075000d81d40c00208205201407100c0d220b81011307a02001c4051013800c010844000f41103681e040140100c922520300010190b1146a40d80c0c4001c14560400c000300700d88004400c82c11440003d810010128814414945031030031560800074071000381114044a20411414241c2a042d1650300c2404102d00520444007000402d030005a10705040383e10041c021460312903025015903103c2640b88040d20030f8007814181145100400038205101c03290450300c07001d03842c0d0034810070080315a0398204510400050004407015282e5100311404040244600000e5075214500042d41510b560028840144141030768820403800c1d8111006072845010000982600c560a10901e40034285005048482d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 461008723 1250 461007473 461007497
    0xe0a05030901030e0f2415030604030302160203010603080304060b01050307020604020f01090305030a080604110405090c09041d060a0605040506060706051503010c0203041508100b0313021804060b0102030a 90
    0x2e40c08404074001e8401074440100010b400c0703e0034a091551021001182406c48008080d01d605003540e120500c440701820700d0ba95000070998071070f0000c02c02818564000b0740d240c81c036003140d58440552a4010000e000a41d2a8501000180c1050380e0403500c0350b00388000194071b503000c1e105a9104005650042c04180c0d03a980801240400c403042c0e290501101c5440400843d10500007841c030800350b5268018581807400511049842c05c2c541c0c1204101c09000500c0309542e107841460300301000c500856112075000700010014a1440b9228182c44401c0340306420509021855034800d6103460010010700b6aa030741840150355045540a603c184100708802c002421030380700300d0304100136003a591030715107414011908540000c021034015a1010500700054000e0200419402a0320324066225051200c10710003001d20703d0090745850940031000810344202c0e0900030640ca90002c010800e02c55200070403d003010000c0e98256105421b1103a44000d9500020840b103217103074940c1d01c04428030382c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 461009973 1250 461008723 461008727
    0x30d03200306061603120515090c1306050c0309030a05100b18040807110a1d0901061a0a1b0317090a05030f0901020f100e1e1209040212010f08010e0a05030901 70
    0x4800c4c4012800d2014103150303007501800034490135110703402c40c0414001c0780f000c1c0010081d49a400074545401c3c150200032142000b403071101da4204a66041c1800ca80300d001045145065001d40c11380190144554420401400000252541416984e000400046007000c0c180305580001120343d5a00d015850301080c0020340f11401007483d44c0c010700d04209034207d048000b4148891607071080880b502d071001c80b050880c1404030100c1d003081c40d441c0200303c15840c0800700d4a980b00d039805c00364400c1202160203071080c2c4c0111000843c10200c2c0c50300600900103458068180c1c494030394001600d080b402c00003115a080050742140c1560040000e50900410044040c00c41e03101d1800a4114040d10500c5140800c0c10000c1880040e014800408c286008210b407500c4c00c0700150107451b007454800305900ca1240040762490790319844080c0ca940d0344140f80301140203885101c09140e118a848400080c0c00400340e41d002d020384440c00001c1c0660200d8008440d5136041044000c1d0031078008000c040781540c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 461011223 1250 461009973 461010007
    0x50316080c06010b0c0d081510091a03040614040c05120c04050c0a1806052212031e03060b030f15150c0c090c07150b030d0320030606 59
    0x600c600c00241c5810000c8181d6410a5400e81c4600d14144c0c020480c130520281c00d1294490369101440c002100c0c0c50b244512013104560103089174007508030311074201801d5108054100260040702c0740c0100d00d9401c80950240d81d03008840517242d1070b02e003d0310f100da0652400309290003550000c40d66a00f5a0900042100341c4040c2c1d00090340920608034912103a45482c015544159407000c02c6c252540c0321041c4c0079248408a5800c3c40c5c0c60344502100f8480580c10105841d44200084814641d100d1110100e0041141c29000b04080803502c0d548c03001010742c00000c0c81854064a5648401502021010f5003a109940103a03030900e4801d0000a6100b1441a11541c4c803440c0ca4510380e000302406404030f1100000f4401d40c507000346000030f214403020303001c010304942008240c03a902d0061420013501f050740d001e07400f0004c010300e25031552410a6007081d00160781e0710400405a52030200500006401805061521081212070f40e03202e211075164041640d1103400f0250501e443d104510403099001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 461012473 1250 461011223 461011267
    0x106080609100f0e01030606050f060307030506031528110703030e0123010311180c07050f0706050d06090b0307051c080403240b130b0d0206030903030712090503 71
    0x1074510400700082883c002800403000b0030203000418550750440c20503c007581c2050b0461400703402640760300034079a04c42404407a80104a46070016690f05c424000900340318400f10603c000c03800781c5041c0300f0b018a100d0040010300c02040250304513042042542800d41e040c81303281640c0a1018003064010901980103101c0c0544080e00000709001c1e0607882007108079811651040b00c103001c0c1d0040c401c10205903c428640401103c440c100090005081c5a612400602d80840d40038081525801c1000400c142c01d6440d0079182605c500d5615503d009255401205441c1181741c00c1240008103c1c03018801c16007181c2d00500030300b0342107080c4421310500c6e00211071400341c0c1110f001c240301c020400c4407001c0d0002e035106078070000040000110352000c3c2c8003d62401d04217039160002d2044a41d407075621050b1416000c5101042c41048000010040a0f0442010390021000410000034920100003140f02d5a03032901d5500030303402c00ea0703e000704941141c840100140e004000041000816600d80d01b11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 461013723 1250 461012473 461012491
    0x206010e1f080d110708030909060f0f090a0b1003050402030c090702070909030f0314100510050f070503070507080319210e010603051e0a0f050a0b0421080106080609 73
    0x10352a030b6445500d15103142c601c03220000500e0a40d500032200003e001d8803004165040045040440003000287d1401014003c0c5100c0e450b080040c0100e6221150032074420384d030080c600101b81c91b00c0490b00006d42403100ea102c3c0b15100e400e04583d019030281c41010301840c1c015005040c11120078090041110300640a1025480366060004000e5554007a522000b88641c0d6481001d548580d005000d0700e0030300c82d41404240400081001007404842247c0450b041124148000c3e407a112007651070703205004801c00740d031900145440621030004014403ca91207038044a5001d0f5030341c4c0116480c1d0048070143c80d0450031036405203121500c2100e000044c01003098a0107506100720075550111140e0390108401c50351907100810511105010050510f000707903100100007003441d07042e02d0f2541e001e004018406038440e950581804005c2012801c0d05900c031581050500706402c062100d011717186101c1ca0781860f0a0f04103079a10384200c21282c12104d01b03444004007929410100a000c090003404142 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 461014973 1250 461013723 461013781
    0x50a0603020a080c03010606030507020309010309080f270604081203061c2004050105060d11070c0b0c060603010b060d05060f21160302031906090203011b0e010206010e 74
    0x4050ba58951509009003c000c00801e444540c48080c0750039604240d0190b0185440c5c08100410359401000f140d04404007407078000313034415441c1b80c640a00e00400b0000140502d000c10040040440c2c01d840a010b10341e100e981840d00d241c901c040250b03030300c954020310070b041d0010070011403003600340e0011b907403c414010300800c05804800d10907102c9641c144d00517903090481c0c05240d242082030b400d070028465016034081c0559030501c000300d840e61060940b064062950740f1516003280c0c5401d4241c514165000724100203d43d51190300d000141c020000484060144001003141890144101600024045d1846007440030b0300704d42c1c0c0d000742002441c20703400c080c060502800d541d541526400a200913034400c8071200a25809980c03070700c8040310451501e8845d08600707002598000442c0e995800901041e2881907440c1d2804001900d10004002d41542c24010354001c2d0444090340340c0c0a02d24680c0c1c0d000c4041c1c00c1507004a03540c039002c0c03064074101c0303c2c00004211541554000701541002c682d0b0414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 461016223 1250 461014973 461014979
    0x218090c270d03030c0e040c1b080f1908010602010204121103011b09171609050702160e0a11070c090b03151501080906040b010536040c0b0c070306050a06 68
    0x10b900000d07098007100001da48008040b0f60940200048085401c00d0f03c08009203074858030041c01e810003001c1e412524205160042c41000f10800c221182c040241001c203440d440b420180154a904110310324003c0741c000000895400d03c14400c4d50b080f201284200001c5120341d8852008056100c81e803180c240d502c1d403c0c4601060000d1484d00b025080594400c50b0441c07401c5490380400c24800e074264401d40100c0100f1446041043c0460140d0782005400515620750440070b92520725103a440700160060180c002030b0051010745070501c5510710f035405008c14104c2da50200c0c130343d114441c1d0040c4401c404950a10003038ad41031f4040980b00c5806402c0315074411042500005108003102d541901c1da4906c544030b204c6590210425800000702c40040c9100d09299880000c8088140103280c0140340c0c0b01c2a0780000390a581000d0b88102500030908645c2c0c0103401c0320800d40300103c03019a40c542c021200000c1c0c3e07403031040c1100c0d9020864030140580c18116691fa1000d403001400ca02000764880d4008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 461017473 1250 461016223 461016229
    0xf0c09130c0903050706020c060304060b01020a0209010e010303030507030c0c030c050c0a0f0504110715151d09010c051309021e040b0301090509070e0c07050106090e010218090c27 79
    0xc0140c4051501d510b40c6242c03440c03600620b03241940d0401c80c1103400c01000f004181d00d445c01500c1d04940c0c071040105204541c600100c2c600340d02d0003400b0750b1003210320000003503020000074442e0590303000c1e0b5000e000da5078402c2025025210368925010001d10107969006c080703442111140b0b034051044003910f080b200c040c000640074111981200c151040d04d24002c12203031400c0e1289034440d00403402500d0802c0002e844212516a503540c0700060740d9283e48180c501c0c442d030043d80c50064001d829011f0306a4441c0010413402500c21142c0c04459840d25007002c41c07060040c0c0945141848503100300044904016402c400780d0031410100c5600401011182e807021310110260002d89040209984c880d850401c0643c01da0302c1c06000e0007890340100c9418000301041d084c03c0c542c0800c505014598915441c50124010840c5510404500d0719190142528190640040c00b0031030809181c0310920582c4402c2004545054548464a0500300304684060441645000c03034424034a0090f08204518004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 461018723 1250 461017473 461017481
    0x403080712050c090301050a09110904060e0a150c08360a0f0203100605180606091f200316030c0c0909060e011b030e0102090d08040302090f0f0c0913 66
    0x101003034201084c400f1442c1070034440c8035400080c030141445213409a44400c42002e4031164058000c0c21480e0008040c01917030303003004002905041c200c1c1d00c5201c0030300b0142c84100c0300741550a074080c24401c0541005100382c01c0103006000e070001ca0421190704502c000c441203032000c020f0100d80b484038107440c4071060501070f002ca21402038180341c001060305c0c410141400d01009602d41c41c140b4102e018013a41c0c8500810005883c8440190007860302c0b4600007494070700450411039488403d80da5a0038044000c055010288070f01c503111280d50700170480c0407407884060a003d1000c5030340180100e44c40d8002c10103c1410503802814011610b0f511500d0341142e03c80190404503c541d110b0844500304a1180324189010981400800c50125130224400100017840d041404142e15240b500c43e0701c3c0c90070b604a542808008204116180c3d140c90203004540041c801640320703501c808000b0384c050901591440c0b0410308840700c03130025034580c0369907403541e0000e96070317240c201407088844c4c140b83c000c9110b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 461019973 1250 461018723 461018731
    0x12230f07050c0303030705090d020d02040e100506100206040f210e09060a030f03140c030408060103020909070806040305340c230d080d0501031203150509040308071205 74
    0x46055454210341003107850210703600ca4450107a030042081052080e40601621130314030003155104200c030701a000240c0c280c081081e02940c840d00c0c140c2e80e04240c0100180824444202e003005000ca40e45900422070703c0080607140401580101000074001503a4440452035140f00d54080c0f11808003e04e0741075000d120808000001c5808682102c0d0603160842040d83d102d54100ca038011243d0856a07100d071100c0703814100030180451111610750324403881c01500c185144090803203468036035950b15203540b01c07402e1100780e0141c000000452900c12021031031400781d84c0d0701001080e03552959034007214598040401c50002d07079000941031a0540c0a0380e203c08070b100d201002c9107411982400c1400c0282c100d64000a41e000c83d0094542144d40c40c40072002540c0401c94060005512a04100700b251041c21244001589040000f004000410b030004000796915a010081440410b0444520541b82d015507a0301c843c5200000340040d224200b91940a0502d04d8240076100110105c0410340310141c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 461021223 1250 461019973 461019997
    0x5090102071407081603080a05090103060306020d061a0306100f020c03060103060603020306070206190e030909040605071107211a0103030e27041e0b0406060f121223 73
    0x40f00030004039508110704003a40a940d0800301c241352540da9000301b1440303001d0707400013407010100c3c41c103420760301070f41c00400115003000d0305668450b030411445000b46254090b103800481c0d00c41728042c003800b01034103503071142070060201c104901c0d807007005480c402ca80200352000c500c070b0b041c0c1900c0c4070b85062217014029803141c031000c1003082c11803040509200000f007445046510803401c00c90001580b034600d10180219007000200340c151a4282d81c00e43c810902c02c180c00c084210144410881e10b035004522901d5255118001100708030502500c03800d151290b04078042d900d40c0b46060b8a52442e9000903554810b03144906041d0546816a2840000b40e005030041901e09124000c0d904040f014a4034481e4041490081482409800d48d60110b010f00042c10451724102c20b0070b401c42e40642c081208a8006028106e50302c0d05142c10310161100c1c0c05141071204001a002460400c1c50500d0903903954020506082e1141001c8202c51100d02030101501c512070980c1c0c254409905500144850a281 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 461022473 1250 461021223 461021233
    0x1909051c0f1703061f080f06030f0114090f030715050a020c06091f0b030715030e190309050a05011b060b0a0305010504060b0109320402040b0a110c0d0204050901020714 74
    0x840f08004844072801109241145c0e079a00310600c00ba031007904070368010f5201181c0442c681703800300424a0151441d842c500190710741150841081c041c258807503c59040341d4115112190214440e80d124080c12400604101e03400101d0002514260480750f4002e072000001410040c1c10300034589081e0381526000e081e50400c0d100101940c01502042d451030b000681e0901c103078900b02011a6880015204541c0c45401030605c84005921a800114102803030034102c40120b0802003d840c1400c0c40f14170101d02103a010307080000d00c2d003400c5c0010f40c01c80e0300584071038040c070b0030b50240f00b598090381102c100d13074260f6610f9102056645805008000c3c40c0105e00000b690316040c03070b0240441e0410840745045c81104001004410b0040c4010100407000300c4055001d00d10242a402d04d204100341d07840d50260000c9004540354805d0f4000c1c0801241c6a550942611800854030b42c991840d185080d4100c4e220040090142c00e140d040541c00156000c0014606401c544864007510741c5a03441f20060303000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 461023723 1250 461022473 461022481
    0x80601080f01180504050c0d0308010e0a1104120c050a08070e0c03010e1305160b0d0f0c020706140c010f060e010602070b0901110a02030703081909051c0f1703 70
    0x84940340c50740c084952040c9546650420000c030396555581ca107103201c0306071110001000c02c281441081e090450103002c0e4900e041c080d02c4e0240c0200024040d1990f40800c1d50002980700c8054083c08030440d032180b444614060034900c2c0710640701c40d03840081d03c885416000c0041d050712120f82200040c0700340c90240c50181d0912030042d03c0204090503000b2818020300061046400301014560405042002012104040d1a00500f083c4c80d5052800b40b40c840e5201c0010f5008440d001003040c2041080c081100a00607910001155442056100180d221035401c0c805903004850b8090011140e01285081c09845000e26003500c0068002828007500c5030380404c48002e000034018003406150015008807400c143c10b03c402030141c82003040c1040000316000d03d10305014007030300c000c0540160980701100d442e03051101803a4803044c11440880d02a80040c9030180c454909507065890003072982c1541545003502040707552a101050303400d465400d048000041e88a010403108002e800e14140d16464 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 461024973 1250 461023723 461023727
    0x6041410021b0f1f120b030319180b270102030c0c06030c1312050d02190b0402060412050c01110115090c030b060a110d1409120f120301030c08070305071a09040c080601 74
    0x201880301b0038002c2c0d2040c040398401c0c040700d1414054402c03c901d4041c201c0c06070303180c2e8004800d0160740060f24400000610565496018120000500c09e00d4801b1520003411001241e80703100b0b503002e030003c42d08103c5c0e5104130351918a000b50380100102c0c0c242030400c411180002c0d80215654004240d240300c0c6810a002c104040c40b01441d8600c0c0c82c005000040c00c0c0c1007402d000985003080c002e240840c210300050840d0740e24004d981c068107d04540e112215490310700703540d80d511646002e9011034602c101900810405000d641d0440204500312400c0340d2500200703001401c8912214400e16866040104203600c405010300881000d9980d0484080d81220982c0d050000e0324154108100303d40ca543c0e2130b900d16900407142003501c2038489540e0001c0001005090958040c0a1080d40c040c0621004165140c50040d605032402030208440f102c0da2410400d5950000d84401401600000301c20891040d40148020280c0880081c103484d1408000001c1c0c1100c80d2a062680440d0350b0a007031040c0b070b503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 461026223 1250 461024973 461024981
    0x150f040b090c060c0106180c02330901020913020405010e130f140711030f4302030106050405090607110a08040b0307030f0606050d0e070506041410021b0f1f12 70
    0x10490b001f080103604016180252a400d84c3c0e14050841c0d20500070030400d4004880a07102c50181d40413004005062640d48103010354072408005108010513000520849a20310884088a205860303a44c81c80381200d00b440203035110035100041160b0b9452440c100341c1c00c0340c0140c0c001c0402c5200b41021038500f9003405030400d0002181c0f070350154020310280074174100b480b08480048038004062002c0490825041d44500c42601020386000d2030250303070070036520b24a4854641c00340700b10000e1040c15101c00c18081140c40469440e43da682c00200400d80c0107008036840308d4000381c1c1100703603496603070f03540c5441410382d001341c0c00000051000020441c075541e1511420580104114082c80030f10710f40301c0002d040d800340040d1a00400d54508034a4030001007048907900902d00500a1600d4a07603440c42e060300803d5582c5a64022803407030034030000e05480840c035101d1102100242d01d04030304012040c08520781407602429000150480305066121442d100d240000090340c0d2280a8106c2c40c9030440305036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 461027473 1250 461026223 461026259
    0x10501080928082205030c0306040803010303050906040b0a050a110f120319110a020105070f08040f020d1a01061b170f040312030e150f040b090c060c0106 68
    0x1d800c282051050b400312812840070908039014a0903400640b401c00658920580800c46000101140e503985001507103c40305045400032001e5a021002640602d03441d140104c5004200d40c0c4104018000131b8080c0028144900000c1c180904003900c031400c0d54190343c404080c1c0004140b0100b81d0440140e801594020560f0f0340700d0107401d1034110072200c41e9449002c094195a0180048009a9480301c80c0b401034804c60b420200c1031041c0001100388650951107a04490b005500344800100118054100410a408242c0d100071302540c0c1d58903a000100710040c003c17640202510885000b044408800100a00c1014010b104075458004050640718449035440a030145c1035140c0700100d020403501c0340c4105050ba90080d030301c104405a070305a40c0b02d1f03a00003d00c000710410201c02a980e0507400290140c0b500d4044a156401c06007181e800e90400b1207602e40e104184030300040000f02a040007680189070001151200c4200d5000518607030403040809940c0da6503010200013841414850b1054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 461028723 1250 461027473 461027491
    0x71404020403030806010e030f1501081615110c040507180609050d1506120f0501060902030112030309021816080a0e03031f080304091a0a3b0f01050108 67
    0x25052031a43d01a05990780142000e06018459480d90a182c400340322558151030114103448084a0202c04090200401c0c01915014410710000e0013440d20040300b403200369001c984070b405a1611039002141c1d0011451100c1c5000c0c0218002421180c603103006082c02903070251540501144040922640002075034490810040044010880303a22190f000368000ca80221440c0000400088a030f0060a4146e01000d003032200c0100040511060009030b03202d0703030301c80c9009000e80c03a035603841c000503408203000e20f004130000800800c0000c0d02a601c90a03815102411380360b60143c450120f42850346c0c00303e806040b004900040113100c00e900684c215400043d44100b00000c2984c09040e542da80002000140c0003008140c140201004190b032030801482c5541c218ad903504c2e142c1c0900409414009a1080b0b07403401c500c1c1600061401c41c6441c0c1c26980c0ca07020201c0da584844117007140c080340074048805040400b80030b4200c0031061712159803041009600c0020309514002c0010203031000104030f580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 461029973 1250 461028723 461028727
    0x161103011e090503071403071a0402030c09180d020d0306060201021e07150f090b07110a0b060a2303070e0f0105012a051c030e0c0907030207050a0507140402 69
    0x3001d0805004015190290340001441060914220b0710b103200d94807018041e4454102c1040300008000010450030740f0aa000460101d421000c06c10307911030541b00254143c00a405c01400b80c01c00360312943d8405110820b01c0140840c0180081c00d11030024000c0d40160043d808400320241c150007460010015403008500c1c0c00d07040c01c080d20314002009100030802d80b0001c5d684003401000920311020607190201004110002c81c1c00703400524a000003202d109000c400002e8805018031070302c809200e0301d4000b800000b0815074400803c414010500c90f40a900c082002ca520f0340101d8141580018540d40c02012461100c109464114158802c1e0f80c507411100070001c01300e21aa41e0f0504449c8282450032080c4491901120385828180c07861028414070302c568404d00100145561580108400e610000d03900042c013201661078591070000709600078100302a907820049182c2d907202046d8500107041c420030390b86090420240030420b0302daa41c05400b0600814603107001202840c40308403800c40c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 461031223 1250 461029973 461029991
    0x402120d050d0f02040b040e010906051002060a0b12070e1b0f07060b01020a140309100f02032a0a0825150216020406060c11040b0102120f0c0316110301 67
    0x30708a119045100d2100d684803603810840006a4050314042c00c40d040c2c590361030b252503282c2c2444060091017409030041c1050307000201402c0031005908041c0040d40a4406a901c5245070400341000f581c0480c0c000c4640100d2042103d014410074025014030102c000c1d090400c03c0c0d0300e070030511100c04c2d200b00300c80e4204442540251900300302d60b01c0e030390301c0030020819092107001030b400c10b03980b0480a03000d11030300054601030341d60100050480300d400701da0410b40070700d0883c030460b10340c0492a00d050141c4e200300000b01c10704880b00d180311a0681b50280c0409054040e01d020740c00c18070b4900007101c0c0b0141c0420207250810004460841724601c01e004108040700ea5110007180c1c0d0b000e204e00d0209a6400205980030010080310901c81c250003400c288940d560320b080c010316858503d074003541d5204014081802ca450540a0340188480c141d0040041c032400d040700e02015030081c030719101d810200304200000d60006201420700c00b8581c508001c09511982410650305000e10700440c4203914061040d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 461032473 1250 461031223 461031227
    0xe0906040f141b0112110f09120f0a050706050702030622140606010e0a05060f092d01090603050f0106110a0b0a0903030b06030708010909030c060903080402120d 71
    0x11660140c0c02015050341800d16050078a03039401c41d442c0c2c0000c14040d00510b5000e2070240414100300510a980e410003898090a0070400c48100e604034141d49a010482c64055000a00c05001600c41c001c1404104140c41900a80f6120020b02c44590b99001100304100344003080c01000003d05850500514105d00c03540003d845100c003d00c2036141485811001d42c1c00d0280010701048030340d225049800d2051902013056580c0301c215401d83c00240e4134800c69109052402c0c0140c21620080d0055040110082c1148101d40203401526007110300b1760b0030065945010420000c031003031020600380c080390b0181d00041c0001d007640c03c190103050414050007010380039102e01e6411140309240404d0042040311010f4180307402d4280241c03d412001085c40501d000c5944407400e550300c03a441c10000f6144413018000c480c00219074040c00b003005000108058401da07001102082d100340740008220701c482c1c1c1c0d101c0449081c00419000980c6010420086050540103840c2c0d00011070004d005c8943d440c100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 461033723 1250 461032473 461032483
    0x14070303080f0717090109120e0d02062d21070e0f03070f08030309010510030512180d03030917041a1b060f07120605010e0402180301020c03130e09 65
    0x2c00082c6070500003030320052003840c1142c0c0b034010410240c0880e0501c40344207030107030242e15010358121241080301080d036402002014002e0b035000c1c1805100e4807050b000c00c86540c01640443c2000c11000034000704240f02100521039500c50641503c0d160139900799010527080d0940074200a4090040500810542004901d00314140c2103c408400124210210342825520381c0440c84241c81e5081c04507030164040051441058114020003e5590310101c5030316000040c4406400380e0400040a5090f010b0303d0002c10b5001d02460040128200000101d019480004800e90001e40e0300c4001004004902074030440011800c2c00040c14581443d010101494411000c004403041c00900e4000e650b0040c92021f00c02d130040803e852040c904041d108000344400c0301d040c80014024060740321000b14600c2840142d138810ba54011441d104d500c20704c8000c0d84a004508050820b0340d814207815031b000d0000301075200317020015540b0741c220080e401103901804d401c103108842101d000c118020030000b0b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 461034973 1250 461033723 461033731
    0x1110304060203070c080a030f0e0606063a05040201030b010c1e150906150e01030c050d03020a060609020405120102040305100b12070b04060f030b0f0f030c0d0f1407030308 76
    0x20042e901c0c4c86007030381607403800c210382d41c01010603001080ba264201c1c1c1681c070100003100d0f0fa0030140029480c201020b91191400c844180d8403400600206409204d1018041075280c00750070f124021550724100900c5200030341a50000040d1100704010841d6458018500402c4080c01d0002c2016841da071041c01310020440c1107044c000010080c5414440018034030030180f08800c504000b141c40d1030030014060025000707680d04506100a0020b0f00d80211000c00e8100c80c0c0180078161171070b003442c0800c80c0300c14031140c090f011442101c0000020503424031541d00100810700005a40d540703820140103554894003101c915a9205000401c0822400306d20100c020300002c0000885041900000f4241c5d9800425000c003841403d40100c0d0a038030308001002981c40944442d2902600c518044090302d48031001e0b69000841d0702c0c1c0103000e60400d400039001064000382641c3d91260105d000c150f10b40742c1d000301501c0c1010a10301e441c052190080810520070306c454080e000450864402900844001d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 461036223 1250 461034973 461034983
    0xf020616050d090b15010f081618080102120a0605010e0a2108040f060311091e0303190c02040b0d05190c0b0301180501150f050f090901150e0301110304 67
    0x101040d03403104075400a02140c4c0d1112821a40e41020342a00e0841025550400e010800d00c1015501660003941074078031820820345030220b5480960011140e4018103100450006030001c400b141e5441c0070b0000d42055406007040440500c0c100c11220141c540ca60711290500000d00d081c00a0381d180da040200580e200100c0d1400c01a03106d4426855107248080040e10b001c8021a012400c2c184803515042107560742e5a017809050424142c0242c1441080d58466104014555203020140100c0308a00121070050650341004458104041201d80c081d501c1400a00007180c1c25007185040d100307800142c90b00341d44580302008240d0f602076540100c03c4031000742c1c0700a407014070100068080501e0107414817107125522542e441401c03000510111010114950030200042010400c2c1044000d80c6c402c07640d5000c88640d00f04506840303a40c406242c3c00964501048842c8094031480301c150b00070244070550300c9a24500202c0200404144100d091003a410650000c18107030303404040d40d420903001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 461037473 1250 461036223 461036227
    0x30703140313060e0331050114090f01021005130516060206180309040908030a050f0403090b090102010204080105010311100203090f130902030a0b16080615070f0503040905070f02061605 82
    0x10200e01407a46c002c0b40c0400c107034080c0c000000c002e03560161607484071080c15482d44000d0320351607400645d410003504142d201070750403d0019444038600301424240b50001070042e40c1d11944600780540c251a011248403044041c1c40c4d400300101301c001c1191440721003050f51a982401d0502e20001c0d107914000d0004405600401c10700030b11810140101c0704d440324010002c02c05038070035250401458104940004009281030000b4001d68641050740f841594113a50380c40c1ea07941000c45601c015045800250304644d408d210200d034145c000d10a46002e14010143c10144800400412a0780d88010350a841150014011414a40c494000020349104119441209500c2941300400203160b4140d019501d0f210b48035440050001c240e2071136000f0f01d140b00902d200d41c4121201a03e820700c05851141d00110150030f0607034041800405880340d03e12030b141c5002d0281494480b0307491a08181c20030401a42c4c0c800c01e010b9501d41105980715a00c640d40058045860185200a032007004682c182081c4000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 461038723 1250 461037473 461037491
    0x20c06040b0612030309160b191d0306010b1213030e01050912030310031e02010c0206030402150a030c1209031b030203160c03060501050102030301291b03070314031306 74
    0x6080034000340d8a0055084170b840749400b500d0300c0c0ea40d0034800b40015010001100c041000b214510403a0200c03000c00048410090341c400c0110340e0310000c0d04da4076201a04650448045030f40c1400303658020622000300d242c03a4044101c151011840280405262920107a400c0c8000781e0881c80c400304c807000074285a920742a0140100f080341030a106010700a000000811520b50300a10944040e04d004d100f81201070300d0b41c42c1c1401440013050b50007901255040c0210b40052400034015607200c0c0c800f0b00303004003424134ac8a045000d03800c00e0044401190300d4201d01c1c3c00c0c0c60751140040e03442d031f65807443c1404108465100603240200f00d44082800300540440141858000c004440070580c0c9a041583e0014050424034881d030491f00080320352905110001515610010030b40341a15454078090383c842400a00c040c0d0042c1181c1c0480600311003e02040c50361104d5141d1450032058018041c5503030380c61520b0003c089480c0714030700070000da04c00d20501c14100f80c8080407152540c0d1041000070040a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 461039973 1250 461038723 461038729
    0x60e100605150304030c081210060201020c1917070b0a230708130b1512030c0624060f041d0411042003070f0813080901030902060904060b091201020c06040b06 70
    0xd0740c0b41001e012207c1c0050741e40c8002500b400740c80d00c584071103080c85498070303240e0f10200d080c4d00c1105500d49060b80002900d4401ca00d21381d40035100103200f80c44241960181d151110f01c3c607000201d040c1c403440040810809003c165000310304114401c10119a01c101f801054660511000380214080004a000154803400c813100c0c07540803250800041226490600403807000e42c01c80c0c01450b806004140901c440c1e10100001ba1180749104201270b003c2d80c0d0790740c01c2c01c002500c02c400300803101941c0e800300f41c1d40944034200240361041e0b00b8080642e0702e9081c000c0d0300c03200101e42244189040f00c200c00700004500150b02030f068a510803140840d118040811500c00c4035910b81521100c03401c00400e00100175000b071400e03544d00c0744039280d050050340c90000440544810000140050000700030f02c41d980e62081c2c0c03008089501c01000c0314141084440828202e40c0d01350044824194005110f034140e1401c9040e0180b84176603000250300e45810300444548034000940001e0080203202d001c00d020b95 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 461041223 1250 461039973 461039987
    0x1e06051608090406030c090b0406030c0b030615030702030306120a12121d0a050d090803030f07030e01020a02150606090d020402030603070305100506041409030304030f030b0d060e10060515030403 86
    0x1c0d0b0041080c4032407600d070b08103544070070050310500d402c80345802501e1070142441c0c01184c0c01ca940090126420f2840c1c8018401c06510060541e94400010340041c1a02034030301d4091401005a9801540c613843c0c41d400b0300c2000b1814a11010b81c551240b030050300028145403841d036045405141c00c0e00b00c00f945492140103080107020491030040110400307240d1980000300c2148588c001e030101d510300040000150748401071806500e055800400000d44030014488005400c104c941c40c0004802418082003030882e004075801c4001604880c03844080c44d0244402e05800440440b0400c1c0f8082d40080007442400d0b021900034082c50700400010843e50b02400900c1c02550044181c4004155005030403000700011503003144220311b440445e10702c20f655141310718840d0002e030b0002d500e07540b900e44064804a580301643e0b002c2640314508050a43c0b500300aa075883e9118503c04119090352a41060070a1030410b48800c1e05840c20070100001d83d05e02d407250f2042c0d00c2905840da925261400d0481c2d0703035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 461042473 1250 461041223 461041237
    0x2c011202040503010e01021c05010b0a030b030c09042609030a02010c0c080307030c1e1a270d03050c09010f050a020a0c0f03030813020a060f0203091008011e06051608 73
    0x141d46410381410f0445c4040d001001c10032000040d10101288581c151401c98400b03002c1d00310302840a0100f03e40d4a402548070300180340d0006d084407000b2051000142e4003520032a0115415181240c03086035814000700013001c1c04541d04601810b100d200d4010964441c005540a4100310100d240314084c45910302517000500950b1003a07968407101070901407c0303942d00d5202110178484569200c0c2d95182d400d0640225254021504980c05e2480e610954184002030141c0c603940308080103002c406090140078524105a4001912041c1640b410150031140010440c00b081c075010840d0320320903030340103c04804107521404c11944941c0102c40032461f011f04840c0003440c224032120003040a840f0b15004401f220b100360388101080c0c1d1464500ca902d5548010001c0d008042d4007800e004003401484c0300c240c004090720403282480c4c0041c000400680d102c8090308041003c0b000140a42e02d604100c009080312a05440e0601c82e1a2140c0104288240c0c604a0402c102044030f1404102c2d078030341180c1030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 461043723 1250 461042473 461042479
    0x3207060e0709200703020604020405060f090a0518011e02070c0801060f050901120f0809010509090a06050406060c050604060b01031121100b0405040b011403090d2c0112020405 77
    0x107078a481d840414014541c80c0740c00b8018003107450644a4200102045511696056014008a44503030b0b003070001401016041036070080031702620780190741b01d10301c80a00ca0007010300007158030b050004d0202d452003074080d20728004d0f074100210350385142c42002d22043c500880500c0182c2e5441c0c070742071a0a4280417504105000d500f000c000080c0100040180030a468049401200c603903a0f400c00030001020b4400d0041002c2d003901141c43c0400c4d5403d014045144041c10301038540040040055a0314508598a0304003a660381018030442c103062040c7e0001e000c050a1215160110fa11859500c00b030080000b481c0c1c0351500b0f405441644244c00c8500c280c00303040e4a140d1101c00c0040504544c048140001d402d088500000401c050b140d12089404c0341c284040b12454942000103000240035210b1a10f4140a0a0900c0c0800340858000840c460300348a80503041c00202000001c2085e0081c4900c0f1540e2500e13201040a0202d00c3d581c080d960450900b003038000c0e0000706900708040e000d103038040c5d54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 461044973 1250 461043723 461043733
    0x40f08070f0506100e13032d0c050f0f0303040807021906020d1d0a180212040b040c0504050709140a0b03090c0f0a0b0415090b030103080a3207060e 65
    0xc1242c0018164015400070852211481e01c6a00c40c680b141d40c1110918103080c1800c0c1c10074080b03401180b10035144410001002c082607070341c00300c61815005d944035140000d800b05040600b400424080780c0d0350142c0006c080c014043d05541c500759a4040070b00f019068a20000d1000215a01c5002c0000100c2440202041d150707074620010f900ca2002a004002042e00024044200781e107882840a22400090104165500b80125840701c1c50012110305049079080020300412480098800d106174802c180315030452400d403829846030200741d400640924208001c0c42042c1d9088a542401d99010b80c9101001c1e9090b140000c141c400564801e00300c00b040003081c441304000100d100c00e0403400980b17124041015100a22002588500c04c5052402090206211a41c5072803441403566180d8900b45007a240c0740c00da2805030380e2007a40100c50035080045e4000620383c2000c0800c161481d8610342003208903062251300006094020f40350091540020000100042680501c42480404089038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 461046223 1250 461044973 461045003
    0x1401060801051303020f01090b180106050402040305070f08011116030e1008070e030c1f21051e100302010e1206090a020306101809080702100c1104020a0503040f0807 73
    0x464400243c2c082d0014090701c2e0703a00151020500038100040e0303002e4844a00e035a10300c8a100d8101d20b580440003001c0d500c0703020028041c5d40d24000f5001440c020009801940c0c81c100803000c1002c001d0340161150390510f04403c621002070070954950002c01a2903c002e4012807400301e40c078462004c1400d50180020804016803a070207180a4420b10142d19210f1019800300201582c590440c10039550000c6004040b040708030b03090400040c0c0f00750714140f03414120a008017541250303041d54414412143c2d90000c0111141e00c000c002c8074070001c0e48003800700034280340c0603561548a55000c080d05100901c001d090203505d401c20420810000c550940390207082c00c0c00540e0301d4110302c00040e03109100e1000440c0c0500700115050084880c901c80c01c0014103a10b08024004e00005101130300d103000140a1000943c036081a801400c1c205075940b09081596450a0300c000300c1646407840c0103610500c400103000781c00200b2680c220340c00240301400020689410181c030700c40c01034010704043c00310442ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 461047473 1250 461046223 461046241
    0xa110301060305151e100510030209061b0d09030f110a0302060f0d060e0103031e09050d0609060c02060601080f1f0305100c0306140904060204030c0b07030f0c2003150c0c010e01020306090103140106080105 90
    0x6117805950341c000340d426290400100700cfd02202c0601024144078445400000003642e03e80c5a145800c0d40a058400304642c5d0b60006280d0b50405881c2524042002034054500300c070910600780580070040c958a803a50450301c000f0540032210503010044a000181c051070307140924090001020700a1554800040901d08280a013011640488800d410080c0034000c0706c0c00810b0940c0300380307810f03500e03140540d44d00c130928000040054200300d2440d9600f40041c007a59148011140914080c10041072000010103403902240c04658a030001c05160010900030301440044103d0042c100710b1790340e4095101c40c07c00c403000307201c0c6502c0289076000841e800a100d4010a000e411414081c2d120001458110102a40c00340b8140400070b11200005d001030300000700100c40b010301120054111082441d41303440c050842c1d8400d445017410f941c40401e01900c01c03e001d00488201080b42d00096003182018004510041c506020060180190550000048009520440050400000a004500b40120a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 461048723 1250 461047473 461047507
    0x20405070e060301080703150b011407080d090606150207180b190608160305090c0103020c0a06050703150605070b0a020a0215010e1806090a110301060305151e10051003020906 77
    0xc201d55031230b651806100d01183d607100740700798800c040c2c40e0070202203400d40c89114164000c08017103e4080080c451888415228407440c6200d91286000055079401c003922600304a21008030703c011584075a5040c07182c0b4540c010040456580c125021500407100d400040c3d8080300084aa041c0d080d0351240001d51079845050113010340800045910f001c0380781d400803410340c0c4c3c080396041d105521000710450076507c42d42c02041801480401d0701e41310105e0b41c1e9400e050720425108000060f85840381c11451805c4540c41d42c1c01030001c0d050152400c90326a91b0700714180030040c00c03400f102c0d41c0400d8105c02e4034001d01908541c0c00e01c1403281041c540c0c464640b08024003040d40d07002560000741d0090317402d903000021220b00a04040c00105007003050365882d200b1b045c50980b94290955250b0380b0000c0050380c1000707114000b051125840d1858035203640c4002e4055000310104812003140c0c02031000c00011060740006a400c142c40c0000d0707400c0c035400150003038403074a0304140d000440050244c2016106080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 461049973 1250 461048723 461048729
    0x3010b060c10060605160b0a090204021c0b0f210a020310290d0f0303060f06020a120e01140304080403240c030c0212130f080a0b100f03020405070e0603010807 70
    0x2d00300304a5840c0c01040301d0718007562103c0251801c20200341800309200004241d0300180254020404010a50104040c3e0b08900b1500c026495a010a003c1800f60b900503030200150a4922020480d180400200f0b59900c6662521180690344040140c80c101481401c4a198003e001c460040c0b20740c03041c003001050100d021044103079120104c17807000082031004950b0030758010100b89000c0d0094031201c000d01c02401c021070034581c0c0c50a000032003684010000000708001e4002e07191949560510341c00c1480c5a540c0041004501c042c07842aa85e0014101071000d200030800c10780f01d98952070141c40c5840b5682003c0c06003001603006120000308108100b11066811000780614100c2601c240c003910355a03414500580c0100d003005017a1003010340640960040801540445552600400550103031034001410f81d81200c43c1600c01c3c0840c02c0c600507002a43c405198000a180001c2c0c0040074180340002481192180045810300e4810041060084c50043c00183c2d41c0d41d44400c0d09070390740e00e948 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 461051223 1250 461049973 461050003
    0xf02031002030c04030605010b07080301090b040e0d1106011e0605070614040b0915010e010b070309050406030c06110c030c0909030909090607091a0f0c12070b15090411060903010b060c 81
    0x1f0010880d04000d5044d5040c0c1980001541e0540e42800444000751203041510b58105070384010010802074104003d0f4480e10741a02c5680781201c540f81c0250500c60160451086035111902254107030b100050410210f0b0388030310701903440303e6052411501078921244408403d40c05c5006110501841c0c1507030a014400712402c03580d00d80001d403101e020b8280240b05442c03a201d441001000402440c00c010710046101e894010303240c98507840080c003200c1040c0c0040d60180b400140c14441590040098440843e4030401011341e550000006592202c14051440c014440744011600040041090790030601005181d088145042405255118000c0300d6200003d044010b00007500e8403401814050b01c020114500d103010341d0034a06008039401241200340920a6119036040a41171201900040b4420121603509007015501c1c17030752400c103090f50948150040c034240000502481c6d00700000050589020f1b448444800006c0d00402c603400c451608840b0001c3c481810200110710070051003800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 461052473 1250 461051223 461051231
    0x20f0910091b111b091806011412070e070e01030e0d0f020c010f0c020d02010908070f0305010b06120f040c09090605190c081810020a050703120b010504030f02031002030c040306 78
    0x807019135110f144040041003000c043c41e401190381800c401c401e41c040914940314108240750844e10b0300d80402644401201c00781c10113008001d140c4050001c1c032084100d0001c0c81454240307582c40031440d0707014040f242800b0740040000c1c1c040c0d00139000204141000001c2d00e0b03444103049400390550340e0b150503400c0140920b10100b8020340c024070050319060401c0d610441d000420354240149421114026810700401e10800181d00d64100b03c070001419002020585032481e501d403aa00752080030500c070b4400c1000f0b000250142c0c440510a56100d074481c1c810303040d5500ca600785890f030524039400c0307904030b1400c0000c0309091100b580c100c180250305c1c0702c2011040d0900260380381d003190101d041c103100040b91031f001f00c0e40b0b243c0f841d08024005240a801d036010744000c450796070201d0b8407000445011130000308049007490f17004074040880009840b810f10400d01c0482c0000c2c902c0c8981d00005004402c02c00901040d914204402074040380e80040455403420140c101c180d8640081c4003c8588900b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 461053723 1250 461052473 461052497
    0x12040605011707060516050601060f120203040b0a0b01120c021b091303080702031603110d02070b03070c031803110901090209010c060f09051005071803020f0910091b 73
    0x2540d4100c41c030296000040e10165007044012104e90b1b104541d41984004095040008588140310701402012980c542c0101d080100381c1c0a8030314034450a40001036071050040101180035245610b5000e1485180021b540d816000140c5800142d040303051040342c51310034080050381d00010451314080e840702100c074140c001401040102c0d1403c48214050100da1111440064060704185412000300e00541e41804010010845448a0300d1000d400203142440d00300d0f1030800a22501d6002d07001c1d44007070319580b420199114581e1001500c4078080110313a2180c403060600c5a0503c0584103030041c11400702d103a9a00b82844030410080500e4420841e04000003881000c51007241c03944641a1110345e00c008094450400418144051031855511490b800c1d001070414440001d40c4c1c1042c1034001801e0418000052110111161041d0000780d00c0c01c007480543e82d1980940ba00200807600384105903242c01000a040c0140e61080700e4031801e0490b00010030030001d4a1440e08042a44c0c0da6002d114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 461054973 1250 461053723 461053739
    0x3080c07050f0f060304020604080d0806150a1d01030f0204170f16051c0f120807020c0a0905040c05032b05030717040606080d2a120f020c04021204060501 68
    0x1030704070b0a032544588000a00b45860402c41c024591040c00242082e081c039585412440c14a03c2c040c4007000010458010007010340b5003244441c0d1410100542c180c144201d00d80082e100000d0040800d800003a01d00c0f040d60b05a200350400f0030f00d1100c1c0042503443d44e80d2006414010003001d100c1803010302035aaa01541c41c080020741700a007168580c0c080d807409182005001c501c034000580c030701c003c04600e5031010102c0c0010485810b064409c098107400c611948000030451140035000b101150481180500e850751244403102c02c1d607081c0c110001d060303201c4d0b00d80095040e456074013058043c051082c960310800301e06446102881c1c0b03140c2c0c03104803a4050700c40888040c4003c81d441d8002c00e003001c14004d521001a50519801441280002083c91315010038924040e0341403100c01c0000c0d84080e01240001d410424248500c0551000c1034108069544540b0002d0800b003031042000034640442881510030403c0c00c1d02c0e0320000d401103640c0c4075a400e06003600e110445003919032501784000003031145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 461056223 1250 461054973 461054989
    0x1020a0c15230a0b100c0201030b060306030c0405130f0308010612021611040e120c1e1e1609020c060708010b0f0f1c02032d16050d050103080c0705 65
    0x600101c981858482100142078014070050318110344a5620944a0085c0c1c84408480c21542640e40b5014200c032050320004050f50040b04901d0701030f08040c004c1c03145540340000c407502c0043c811140031a0a0f03130380b440d1365004040008000307400c908485d0f10603018540c12000c0c2e2410384520340d890b003292400403040001a842a00c00900c004404030507000c2c081000c02050707040403600140082034100d8240d90040c5481c08100e0141134084001540b041d02c060104410203690301a8460321402808190310240c48c0e0800200100800420100c04842c00806003c64000d485200300f0400301e0716110b80c4004025000884110806c1c46800042a49203014101e02412a8a0300840700d18207030081c0040081c1d40c0201d01d0240910f04107000f10503d0043d031440c144c10007090880300580301d04e003c043d501d1182d6480340904003a000034000b10340d1000c0c044c400c2a039200c051902c01a58001c40208211414440c04285070b01c414942000841005040401407107410b1001003214000d54950080103031320 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 461057473 1250 461056223 461056241
    0x60906060904080307033b0a08070201031e06081b01080f190b06030915130f0803130212070602010b061c180503070b0109060e040209151201020a0c15 66
    0x40140c0001d00050801401190b2142e4645000b02c0e110b000f88840c1b00e00c81c7c000780c1900941d2030006003060140b8500c1c0b062402c240e41030f48010103e00001c2d4a03207903114410301c00c001e810992541015000e00d461490340c009141030404040044543e201c0010381c03101d42021214400313110f02e0464a815604c180f081c280a80306120001c212501d92000c0b106041c0c0c40440169022034541501810f0ad949550203103101d881440054025500e01400409900c1c0d001000805074002c018401e0000c100200d0031119504c0d8040d03a42c2c1d0780d035144c0c9840003107120719001c0002d5000b004d181d540d016512001c91075004a5083d5002402051185020015540252080c03841d0000ca040c900d00307040a00350f0400d100403d824415041c40440f680c503040c0c2180e101c00414ac03141c40342c110040040700c4280c0704140003022005003144141c01c0c10b9002403061b00020b4001c0c8141075800d0f5184a440c2d480c40400000f03a40c001c4021580c0e034416887c05442010508025100c0c044030300030b0700b400c1607080e016011032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 461058723 1250 461057473 461057479
    0x60e011a0a0f1b0b060a0f060807050705010b130e060601081e0402040605210607030c090b0c011e0b040612020108040f14060103061b0c0305030a111e04050306090606 73
    0x81c5003441e030040380c4045107814075804001c950011007603402e80e00c4011886503400307450074080398a001c40c01c0c82202000c0b1340c0005001780c0c0000c000c220b2258421070058004800d46841c583d11401428480d000d01107400082d07900c110444201ea061b84050b030b201842e80003440c402d6410b5941c40800540fa404002c840c0c1900c0d003035101500540703060380d02c43c240c1c0c0d0184c4007d00005e002500c403400b058200ca07182500e090410715070045c4888440080107507d901201c146410b00043e00300083c000c01e103480501c54000300381008600030803080429040041150400c014400c1401c2d02c41c0c0105000c4c0003000b0503940658070b80000401c0713030f1070031f5149545000c0c6c068460846540b113660302e2400540000f10b0654070300e41c8140c1d60041002017881500c0c0210300074000441d036016401541001762103054210414002c5800101c8006074100c0156035120700f05803000140c540740400c0c602898411600f00b0003003920069442001c540180380600103840e400e80455140c2d640d0140c5541d036481003990a0784e8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 461059973 1250 461058723 461058727
    0x1080610050c100c11100911060703110a290103023001090f1106090d080307050d020403060608150103050a1709100e1026060f13060e011a 61
    0x4106409580100020b0041e142112510000700d2801e50454450141090015101c0032202c00001d03030401c055000404054000c12450151f90744825504110030420b900a00b00401c121003403600820500240a02071000d40308030421500e0b1480c51a01d410b00302c1008044450290303028000100f080074140d036800f5204491040c110100601c027402b0091071184c0900c524500c081d1b40c030742e0030302a04048520904010f03041301c1691a08071a41002d044186014410a100101c0c16644907040c024241d80c000744815941d80b20070030101c80300c0c400e117084412414000540042041001d41c0f000084030451016070751040140c04040e0900c601c288005440c40c0e011009040101d11502c0c4100712850881c07a03020314000c0020b000c2040154031031700740c0c00071501d4100c0490326824501c045403420005843c010048083c08140200d0b41801e4441d0b4000c200250000514580c407250321003195844014010040051002d0145014004a018501181c4280000019180341c4281c1048880c4400d600540c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 461061223 1250 461059973 461059999
    0x11d0609060d0912051c11161716060509070302010903030509012109140606030d030b06040e2406071703150a0902070302011b02062d180c010806 64
    0x800d0741c0020b129408010350307664162001801d40034180b550035480b03442e11502c84241504520481480b203c001001e036044c82c00701042612004101c07010801118080343c1da007d41c07424100c2c440783c2d1280c034450b00003000103003040a1001010301c00f07036014400e0f20144070981d102d200c0161950002d1000901140c103510302800020b0040300904140ca03010725000c410003116041084a21a0002c5607048290703507a0611400d01c0300134110141172556030401041c080c1401d10229603a2145560300c00c0815030b8a06019060f5900c48080382e000740040d200c01c00603403d1842400400d07003410141c44c010b4102c070030143e9240e428448241c540c030513000051100710400f148140701c590380c00202508944038400d144950655110314122002c2d114501c00140c84050515000c3d08464000e4008a0201200b00c80c00c1c02482e40080c1440d40565200c090960300c3c22032007a84031400d54030f041501c0d0b14512042c100801e16400034000d9003600e0404045480381000c600040d85e070000c09541940e040300c0000c2c414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 461062473 1250 461061223 461061229
    0x261e0c040b010e060708091003090303050702010606140a0c0803070203030f0f04020a0603051302030a1110080105060a0e0105070c060f090b07030215100e011806050a080c0d02060712080402011d0609 87
    0xc0d04d00d4601903540c40d4600081100058072000d03010304448d01090340e600d06801819030511075a0350000044c002080058180030001d8000e4285840c1400070b400f00041d034800007841044d040b2003060740240130039241e041100d000381d125007080358030f8100c00d8a04c40000c0c541510a1100c1c0b400390350060413107003060b410018110302900d0b0007455041c208805250080060310100304800c000b0f401401d00315690713482d1000704114003000c03410500030829039400501280d9586411174418130243d0905454011031440182c90600500e1006031a00c14482800035880350045401e042aa660b40d4594a40a444400490b0700703016448002d0010313440801c101034095441203030650040b251442d05c0070215560080c08044050903007150100c1c0200c1514410aa08540210000f820044440c0790b01117061240c0591f86000340807942d4031a0700c207a03003000c0954841c001121125500204110035403481c01c4400b401d01305046c0c0d03040b80043c4811440c0a05844a90030161030315400610b6945010980010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 461063723 1250 461062473 461062477
    0x606040b070b04030e180a0506040c2c210c0d031b0809120102120108070501021b01050d020703050715230a061e1a13261e0c040b010e06 60
    0x208409000007001c5e428031540c0d9264125a240ca000500700300c60307150041d100e00513147c1c0500030390300584c14074284d4180150044241c80441040b44105031031322001da070310404120700c000c104a401000c0c0c2450034021660b0144101c903c1d00303c042c2241d101c25085424411070801c46000500002e455454000b1040c07403201b05800d906004079481c2d802c24080c1000200c5030441011690140d03940003a12000c9075108505e8140149080d80180c1903071071500e00042e484000c0190960340304c0351110b0b107542507030307000f5815203210240a070340464030340b195868041c20642c0608401d4a142184040080721034070326000b044000a4114040c220314458210f2041d08000060440f034503154844a010420501c0340b2100c0d00041d030610400780a2a241903002081000b400e00c10581c00c2008010b620174144002c013200007141d086101d030041c003e1030000103080500c02048514180d004110300094641781d0075112203050f00c0030505983c00d0f05450400c0000f150b40f40b0b00054041307004880043c80603d44940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 461064973 1250 461063723 461063731
    0x904080301050f1813020f03030708040e0a060306060e06041805030f0702030102221a030c04050609010201090c08070f140307060e21061e0f150a030501021308060606040b070b 77
    0x10042c1e01e0f84510114090130103104583c1c140c040c100580d0801c00b5443c20640f0003520b00c909074051840c046d503640302c05040d0b02c140d00a1140940980c004a804418035510000045820840400ca56501c0300109507503884161403092065040604051140543c2c03c2d100e020303a40d210340214036044448103007842c1038014000580e0304d5582488250101c3c00d0565410901103204528011001e0410303103101541503011188020701c032800d00400110b82c1d5100115415240101c030010b03100e160700030040340035110741c00005202904511002171011000030704035050f40c070042003003240c03a81c9805c801d00c06000e411340102d0341070340301050810025002d08d201d40c01240d0080d10f0310140d614900ca4138400300349515461030056000c842004141407591281d070500a0820022007030303034100b88002c68102c030006409903404200c4000042c044e40d131020103050096074800c0080d5107600d001c1d03a1341000f85600707105600c1e5030300a507800141c407458410211819680b05094050400703045803540410b80b64018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 461066223 1250 461064973 461064979
    0xb092407020313091b0203030405030304030315030f11101b02040b04020c0303040c05010e1e01141308030408100204120308150402030901020319060b0901210504150b0904080301050f 80
    0x80d51010207220340760700f03000d4035061201291084003914a004039144c407504c0306045410910900001801c0402129003143d01890041015030440000840710125a40002c0c040c0889180d20020482880a01203005404540d0442200e40e5110199500c6407015010a08911150074480061805922800c3c04240150005050046800347d041c41e40c3e10540c3d0544981c80e25074000c0040350b034402c2184501541c2545c2034402410528041850141480b01c024140403e182c0f0019082580308181d81100000720390715555a0f64980080f52268401c3c003c01e202c82c09140ea00180d01c0d511402110102d50050b04203503a000951380b401c54203074101a2a00b964281c6504000905a6440c00998003c000c0e03132000603500d0504018440b801d03080c2551582026042203c10407019050100780c1340302404c2801d1034024901031956140b40220ad142107151141c0c079010a000c140510b6017004402c5082d190b400300728403030301c8208100420104881c0103041100c1040140940d050410804513070a4000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 461067473 1250 461066223 461066227
    0x51b0301080a0611041e0807060e13050414161403061005010f020106050315432006040b1e04080c03070213050a200d0513050a030c0b0924070203 64
    0xc0c14001d105c20001035402c01d40c6c41c29001d000d00c0750141c207101510007060141403281c03444c40c03007a0106640c03445415030f201c401e9584000160500065109600028000b039040c0d4210200a01d04407140902a00641c04094040800495141000981c550140d01045040410f05143c000119400340c00303220000115500c0303200000706514104450300f0900e400b180040300900d01407d1680160901c0c0000059070f141020320f110404049020311a20300e00220700180d503154001a05a0b1441d500c0c201e41c0c1104540310012180d00c5102251450107944900240e1401d501c82d2075404034050012407690800c1e00c1010301107000601e0702d03401000c0300403035402079a003000d0054000669481da03020300301340820303100c81c2004400c54052042002051004021702c90301802404c01408901031603801a20490380c0340085909940742c0030700f8450480e03000048404010503807170002d141041440e011164090380ca000728003c0380c4d010407810400035040c22510a00d40494802c1c00c5203040142045080d8002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 461068723 1250 461067473 461067479
    0xe1b030f0307030206191406190503070905011403030408060f0406110307120c050408060a050a09150207031b082215051206010509090117011b03051b0301080a061104 73
    0x801c1c0042c1520034004d401400042c40c01c0d41959090310302c10f164a48005141c03850349a07110000c0c1c20030071f1308100280c50596039441c0340c40e80089060095041aa410300c1400d200240d56402504400d0580e140464108080601c2d00289a0b80c1e000300d01500407160044000100f030003585940140e4480e0052101040581500ca42c40c480e581c0240c0e5000001044640ca01c00c88483e00d002d518a20300c59460614506447d00740c00540b10b040241200700000c1d1181d0208503e1042c0c0d1704440001e83e0410f488580718050188507400951200311f0072004503c15282d40f01c030343c81501c00c01c9c40c2d07a80c0d0410581c9240403200c00821512a5038010b2050340c1c0c81e4201e03000300382c2000c1e80904107030043c000e403510b030350b10001c3c50300183c96a031000b003980e81086401c005150302516401200750448030b1014440b03c124851034001c42c003500c440d80e54001d00490000303905001c5a416045075005115411041c0c108a81707500d10815903110034050680035070702422a160005985500102c540314280000e40e0030151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 461069973 1250 461068723 461068753
    0x40204020d09140c09010b0d18050601080706080603030708040303260117010501090b0303071b150503061801051513030807061401170a0b0403050d09240e1b03 70
    0x2159850a0342c049009101a0200c03000130000c01e000075108450445030f075850f04001c51642c0c441e88040c0a50583c0f26403107544420b6801000402c110341c07003c141d81d019a11611001da0341d079514403c44000814490200d1311504001c42241c4645400c6034401f0300c0d103800c54400b0f85511140310f070160b0103014180c601040d104900801c0501911420b50b07206031241d4084021400d550040e084042114035040e40f0341001c0c2d90000c01c0381c0015034007008200090400c040d4a41d070300b8129902003030007245034039400250540e006c402140f10342d004550284111080d04100c1610305401d02886410416000c0c00e080386042001c0580441105114506086078403540c2d00103042e000201c2c11105940c80300c00180704030421180d00c034003500400010014140240240d180e0b10701c801407002e401c0c500114003040500d489030302150b10840fa03d503070600c02004580307070030f140200e4038461141442d00b511b5584041603455014007124540c2400040c80480c034440c9406800320700c18842e4941c14490386e850300300740c0300e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 461071223 1250 461069973 461069981
    0x4020619020f0c0402031512030409150501140909070509041503051617070303030c05040e15011b0812071115090607080105011e11070803071e0c0e040204020d 70
    0xd155640078110250b04400341c01d01d40a6501c007010710550040c82085000e038404404103951542c200c4240100c0d4016202e06400d41c81a600034055841c1003404600304180d00c0c003001d200700d0b10207076101e003c101a080b01c1201c06001d030005480e842903101001c00c100a1248015000030480104000349091160589110322480c1e03510407906a04941542c7d01200346e0380030710b078004000e400c191240d010210f14995445030385034080201450359031041002800d104000340d60240c07135032a5002031282040040170310b41c2c0003600c035a1800135440c00a140c1b038a2481c45041c16000713038411442810442c1d01420301750a0103005000104000c0b0007484c0e07141c11142046076040002030200300040c0303424460740702400c01b0001071041c0140002d9000400146c2da024800304c074883c1916468800c512580082210003071000c814410b060300c949440480c100c0000f00040948901c20703000d48285d11051051414804042840a841d19140034801c200844c040308100e98010f100810043c0f0b8101c1082d0004112 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 461072473 1250 461071223 461071267
    0x20403030207091a0306190b04140907140303090409060b10050304050d030207030e040903110d0908010f05010b0f0f160c0e060904020307051002120a17010b0c060708040206 76
    0x690001c2c0b000c000c05a4588036011100031044900461104110301281c2d480002920202c030100a82c1005001c1400c50350003907404c0180180284010450707900c2440002009135502d42c82801074000014086007400c00c0700d01c1042001d40a181008003100402c0010104000251001a01c0c0c808003685583d903c5000c0d04071fa60640c070f40a4803070030142405458940408050400c3c10b10401c41880402c0e0000346112507401c00300d801180c0042a85800c440155680b09492094414081102141c80e0454840d0083e909580001c2043e03100442065081c0c078003c3c03080c00c210b0481000004403d5140130001c200c41003103920114904926041c4104603134401070000d4601441755441408050244c11120390000383c00c035030200740350a04d500007a480760510b10a091081c0400c0c109150352900a010b00c0b144210507000464071641111005450300c007400812405d049000c00c00401d4201d0b1150a443c03c4c2240c4100230070403582e40d00ba00395003940c0003500907030707102c13000b1711031549103c02e003c00c41024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 461073723 1250 461072473 461072477
    0x702060712090b040803150d1104180c0b0f0c1207060507030b01080c160f0f020f150406050901110d021c0c08071509050303070201050613060608060f03030d02040303 73
    0x492030a080d0007400e2114021100d1038841c20010060003181c1032604003500580c000001d00d580703480b01c20702c203100461102965504a072001c41070f00140141041c1c0452070500564081c045001d04c10316040c60190303580d0340100700c03908e0444280030044075000030340701020000308034900d000d1009241c07a103041d03001d5002500620b00060a142000298003501e5084061030a0901040c002c0300c0010b0020303000205051901440814440c580503240e180301c2d4001504401c1c10b40b003000042c2020003059410410686c0290f0048080c1c072201d0800039a20102254200c0304203051504103442144d0960040380410f0401610740c221000d807210070300c00007040910a8004000c0780040e840080070b8000d8503140a4188040c03d500b0344040b03408401142e40d0307645d2260403d00b100d0340e00b0f01d008000302002c0101604d40d100203c10400d900380c05500c4a4003d00701102e003001e4502003805d055081d82c1c00c0c0d008907400110b800d000f040c0c01c0e0805615041c1081801000e0324248081151407a0480c1c10552080e40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 461074973 1250 461073723 461073733
    0x9060602190318081c05030708041205091009050a0605070f0308100b030115080105010306050612040f0f0f06140c1204170a0918180201140d06121b0e0105010c03020a05060702 77
    0x5a09130f450745407a05c584000c1c1816400c52400c035401510402d0020005402c0010f050b500109491190003140c40c00341000744050f8640b1101c5c1002040707405103005185c021100600c0100d64a030041c4181c0386001d51005a0510800b01690102c403000809000e0080e0400001c2011503428040d0000d14003a00c000c4250924440c500400100720320410303800b09040c103107002818000341d03ea1074111380c800c0c8500520003005032a5843d00c0e01a03140e01700e10151424410342d241c9000c21404c091820174aa0080d0380030f001c2c15030b411000060082043d41d483d02c00c0e0740c1c10845d0080354040a222158054080d00c4480748000355041c4a5549130b01c03400352100040c0858005010070075100060000010503200700300014946105c2c41e000c9241403010107410b20000c540700325140b103102c1c011141c420040903c140606544d034424400303007070f1010500300d810b80320100003c1c4401258011487c1141d59540e21514140d191000540d01701c400e09109070300b103000d44c8103c040428001c03c1000e002d030126500070701d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 461076223 1250 461074973 461074993
    0x1b0c030b0a2307050a11010e010b03071d06120f120d06080303040203060a110c010e0d09050904051e03090307030c14030703080d180506041109010906060219031808 72
    0xa084542a03884003082268038040b404010004101d0150b001c04942800c0e6943e8100c1101500d50200d40521880f080d82000c100143d0140306410080b000d0300190203c8506946980390700e1440c0110342000f2500e603110f030000130902d160449030100b540807090140c0d09425001d021190600b41d031614000b0315070360000380a4a562403540314501c01001c502000e18150308083c7d00003600c56001400c846195925003800c1c250680324001200c0000c28018000c0146144020010343c607000420102d0700410170180d0005814105051114403a940c4440079001010795000b1600c0c1202c001c240c20915440248408001900d0070400c2c50051070049280b94181c601d04000d907418070408a003228001d401c0310390100009100c11098803851004204081803010301248108100d91307a411015159220b140f0a11041c459043c058204c0840305541141d2503030380740c85201080e6a902e00c60800140e210b442441d502c100c2c1c81440d00b04a038405d14042d040c0a02562081c0c10441158211549079007001c1f00740 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 461077473 1250 461076223 461076241
    0x120c030209010501020304051305090c03060106030606020c0f01050901180f0b0301150507030f0e0105070f06020904050a110a050918010602331609080f01060311030601080705011b0c030b 82
    0x2803401483d01344021407600342400c010600710305000101c0c9006c951180082444144c0600803021a26005800c681c4150b80d07400008029060f41d00c102c80160060051030340060402d00c03151403018406850711854820103100440f8030505000d40030380c81419101011445280c0ba200c80d034020b000b050859603d0f54100b48113403500f4000c0364501002d000d010425080000c0c3c0156481c840550704c6e00705880c8100b680d50043e9011b102e0260010440e04140180d181008055406440c5188050b5804c01155a0f45a0208216090503a0340c3d203003803a003171110b43d00e842d1207039000300440720002d00303085220907071080c04094418080c0c00a00168100c0c03000110318009800c2d5039801c0c0c1d0b140c0c3d80a08004003e40900c000c1c02c40018020300312400c1501605d02c0e070680135903207035001012900121343d40310081c008050b00900b01404116110308000c00c014590b0300e80007900a040c6c80012000e0005d840c640401034854600c4400302c00050001c0584800120740b5003415030009502072844443e0030301d011600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 461078723 1250 461077473 461077489
    0x8030f0706140402090105060705010204030b1303180e0a15090e030a080a1a010c050a050a1103071e060507230a0c0b0a0c02091e250f0c03050a0306120c0302 69
    0x1001c40003203080b608010141c0c0c0d1340d401d0141151015203410759590940d043c5240644101d0b00040c05402c050014401503d0070014069000c84c003c0e920b03115150030080e03052104118911695042022030008a0018501c907405040d8040385031891415a541c1c030f41e005800d40b141c01184a50541000c2000074002e500198890707401501c5d01c03010082c09500c222281c0b850f25010f1001410001c8070250081000010440c40c2c2d10380f600711048400311031079803510180c07010075086058001c3c06804800a90601d440521921782c50340c1e0001d0340758072820300784100c1d22030700845802d4448100c0b04202400c0d0003c0303c5490700c480f13108200600b54541c2e041c140b0340e221031102d40c045d040c4110b007000403403003859120500342043c6030304440390038031901c5074450090105080080543c401c240001809210360b110301481e20045441c0c3c45c4862032015007481a1800810401550702103041038080c03800003840b910050803c000c00f81800035501e515505100f1107200306c03050486801d070a800c0e080c420752900c0300c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 461079973 1250 461078723 461078741
    0x32205010e160612050703020409180c05060a02190201020a08071109161b14010f0b1201230705070c180e0f1e07090903020a0c0515121008030f0706 65
    0x142d02d007000e16200000b00034810700d5404502c100e640318086050180b0a804a500404000406012101d420540c01280c01600881101c8109107460000f8541c240f80c002d4a60b00c44054025200c20b20341501c00840e00910314004904600038540c801000404510180854038010071000c14207542c82024086210809030100c000d403a0710f035901c10b00d802d90100350f040403030b0021140340040c141c0500e030400d04c0451494103c0c85079400c002c10000480c5103a4081180300c403046800c54001300244017024221449550161340741d1300c4040c1c40c04020000080c440f074001103240780a42ca050001d803220b4019184075000764004003810704042c10320f4000d0340611014074403403102903c842d01c051a62169208206003603000302c014030400f0140081c40034010381c401845010024817004140f0324000391201c0724041c0c216406040f4080101e220f0801e4205d00c0d021044010156140ca403041e030080d03a1804d402232404089140705a4045242d50052000d002528100d06030151502c00c2032070160190f482d400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 461081223 1250 461079973 461080003
    0x3030f041e150e04060504060b1e070b0105010f020a05010c0801080c030715030b03011508010c120510120f1704150e0a0902070c0f0f090c020d0e0105032205010e 71
    0x400070b00010030700e03414480003800700303050654100070508003080140409070711061b80945041d00008000b111a0000c0c0890325021500340395004801400d00003d005805010300744200010051210794000c5180307000103660340c01214900d0035180d0f038050070764080082c10750002d403020b40104030030a0100500c540d16182100941200c40c24880c0c140040101c40d01d0b9a810140c9400c111525901c003036100510001060b803040500545950b1414003805c038041c408000120806440c403446443c1d445580c3c061b840c01c041c03008030706190581d078004901c21001c06590b0f1280c0442c51200203507608240f00c01090303041c141c10703440354079007140301038400301180d000400d11a0720170039001e0325950071100d401680d550800042e213403d80c1c1d084c600d4503215150000c0a01c8001ea02002c50054444940e10342100c003915400d01000405c080c080b80c4a2001e40f010002190031208a0030482d8090409507a126080c14102034600101014820400406a0381070f102c1d655504420102c4803400d000c0e480e0910070203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 461082473 1250 461081223 461081279
    0x1e04050405071706101101090503120106050a050d0b04060504050906041401020414090c07170403150e100902030c0301090615060906080a020c030405090411090906060604091a03030f04 81
    0x24444628030540060405104034014141700d11900e0040742520b0b8a16903803402001442010325045a44c0e61010003010b68400443e030000990394483c00841c0c100503481e52b01c2a05013034080510801802602240c3c1380c1c02602c8603004907076070b05e0310721850780b00e800220b0042010303051a092001c01c03100e8140880d444e40e4010842440710100c003c86907200c2001c01c2d1003848003a656101030800304e02030803200801e589500c0000c0707601054042c01034800e583c00b84211026040380c40316684100d81804090b050541c0040c07810140c2d1194a0707024001281c0003800f601ca6042e80c0400082c21500c5c95801120100d5490190068840f0410b00744405440c0314102813160b641004070150440c0e400a01a17980781d500051041300e03494090098900030180908070a1260501303180c442510340401e46682e0107000105c0c0041e84121000404c54001d0030040e003c0b901d09810440040c01820944107281c0d07070b000003418101044d4508000602801140344100b5455038201040c02c544131114040c0c00000e8461 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 461083723 1250 461082473 461082497
    0x70f0818061314040e01090c0f080a12051308160e010506090303031b04050d0309170d050a0c14060c0306030d0201020702030c060702040b030703050303100602070b19051e0405040507 80
    0x41c0064034403c0d2410b0b00300b1030142821040c0060040e01c52000b50b11a59402c16854004226000c3c040038103440382c000c544441c268496905d21303034441d0b4002d00506000600404085054002d0008008030402006070684190321404811b01c0e1503400d0b901e00d0443c41e01c0d00010060010030002c010b014000c2142d220f842c00b5214000656640800350003042c50f04446550b0301d50103000340d82190010000540180403280007824060402180c5109501c0b41d20380c09101e6407103040703001c0b4007156198241c0c0c0700d00e414130140c108115001001108200d0311008005e0a8015100041250f51700c02c0701a80038882c0d44c0d15000d07041c5030424800304c400f5000d40e8014080c280050307a021403208020380042d20155141d484a00004024110303210b02141c140c080c2030804000d0010100027188161005400d800b07248e40d8900c0d00300d030303502c03007620030a030001c0800d0000303c641c000c00c801d03c21100810307850003034180030301800b5a8000f482d540c00d03001d01a00f800502000281428010741e1351000340c40c1015026800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 461084973 1250 461083723 461083747
    0xf09080f03040b091906050d0b040c090b09060d02120601020c09090606010309170307030e0f1f20040f0602012909040519030903200a0303050c0102070f081806 70
    0x42d4020005482000304040000d925403504048000166400f0106615515140502103511102d40c0350421410300400001c0303400d05000d1101e0840780350f40d0701a400352400c6c6400300303960050052503a02c66000c011f4a0444070f0540003a02854a80c4071810802d400d0000019142c001c3e450070301d80c0034500840412048070804541682e2110082c00c0202d0303400303001c0ca8402044407903541b001e030000101006102d41d90780d060307100c3d03000750f8603600440780006c07070102c000ba0b560140101c031040c01d5000c841036944058085d41010510040c038082c0103015000700507203440c040c2c11541229866209001041201340d030309004620000502494030861802c5004078110b8018002c010b0303601540ba040045070800c00208803400c000350322200d0b0207021034a140b400500c0c10b1300d03e1000f03031017142e003030381c0f1100021071010345e141d03c144001010900170b9031441d907082d08c3d680c1005e125404155800d00060001ca1a0303603600c69109440341d910996200318400391101c0d6990200d0302c4602507003060140001200c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 461086223 1250 461084973 461084977
    0xd08160c08031918110f0f0f1c05010e10050114010e0d021906180f1d090a0b0c070605150307060509150c030a20100c05190f09080f03 59
    0x8803c0380c941000d038580c2205070014206a02040c0c030050414403244040c0070300c6207510031421508491507410260020100240c81102c045010790101c040c40b00c04074070380f808043c80c0680a41001052094070441e8440034210b56084403075100e5070300640c1110190742c06602c01c05014048164422207078a04100000f0111646846014060100d40740ca0b4815569010a51683c51440e4103141d26410f88842c0000c0c10b409107102080c44100c00201c2c04515000203083c4502a1030b8603082019000c0c0103803c0c241d030007030b102034189810f034029a41d14401060300903203414813640090060b80d42c1c40070035140030b204030f0304000c1001c40c200700d003803420320300c41d1798049014400c40d042460816150109100010503111921461590440f8000b58242d2030700340c0030010f003140c440c0d541c99041401048003100400c03505c0e41c061146050700f04840e100d0301080d0b144e000e031403008024544142001070640f0802c1421040020040200700f103980840807240d48110150007410600010b00300c045000b005d110340d02c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 461087473 1250 461086223 461086231
    0x30703090506030402041401060f0306050f06030a021b03032809050705040c0207090929040f0213090b0405060916060503010b03130f0602030712020f120703020c0d08160c0803 77
    0x55030b800800705041d5038540c0c01c00c410600c0010240c0e00f05507035405000d0300403a4040304c001c0100b401c0000c00152481c01600c80405188054611071941e603038003c100f002548100e10308410090b0b004201c2e480a0010805184102d5281c10740140f41040d01c00c810b01c2c2021085103904c805410928040001000400c55000311030081c0e801040824242200740c2c03d0080d0f64014030b40c028509100360082c0690010225541c0182c500f859001701c1c94200c41d4024840102c80c00f07044206130188103001414500b1a00c2c41c02c000007000014180352950315600d90010656042e1681c4e4002020301041100078807900003804c0c00d8650301c008942c030303000b00608036000503c0340070709000000c030000c0c0c00400007841020b5507660241d030424080800f031400390003d400a580040001c0c140100c01619500c40748200c4001d010300501e83c5090519513007071290941c5d0300800c404101502880040a068410001d84071598296245d40000703103403000480350040b84401815041000101c250404141048110390704 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 461088723 1250 461087473 461087479
    0xb0c0a150e0a061512050709110901090b0c070506042c160804140a0b011706070e040e0114131509080301060c080f192007051e03100209120307030905 66
    0x784c01403003000b00b29a01840e50005a803001c1c00d17100f01d001c225010481c0c60030707075982540800108001d000940028002c400106000c5844084103001ca0100a80609847d020a400f00d5602036111808a402030301310f40d00103041c4414600da0407040c00d40d21542c80500c1140100030504a2030080107898140c0c058402c5a0244000e072400315050104041111078240f43c840304480f10300b400c40c5003039441c2d0042403041e000540017003554032400040c0440d8407400307211b9594808689011607010040100641202120650360310a10040060050041c0500c1083c4045c09203e055007142400d2040d904800858404540f070440000006081001540d05498003407512440c1c1d0700c068a0846d55174840c407490038200c2c00c0089200503109624101d4010a000140c1da55981d0b540080c0883c0e1901c141d00101000c29001020709000600305001c0f03410a10075000d0f26130251040b00c0000c24207011115040c8036003160001003803c481d050950304900030351401f40096103080d5040d10020a110780c035009480c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 461089973 1250 461088723 461088731
    0x2100b01081b04081e0d0201060e0115030e011a0f0102030306130504032106230d030f020a020612040b0622050c070b0f010515040b0405100203040b0c0a150e0a06 71
    0x10041c00c0841603c020b00203400841d2903401c0300f02c02652120142100f034140c18400d05911492141c418043e510072a80c0d80215542c0d103034246101a15040701d43d8161004041d910009080c004c013090150340c1c02c46403800d29011002c0d5542003840b1140b40030190f06810b45d80200244019503c4aa503421342d1019022000039464030390b4a01201d500e61a4860078a000810003800c5000d040258001e42c115040d10001c011304a281d120051080c607041e6a551b41c0c045404859140442d000b41d11042812581e481540c04182569001030403641000848680c4240684100810018005d8003940c0001c2c3c00c0303510b10705000d03040c00c1c1c0013002d011b01c072138601095885030081405042400241c400c6c16500c0740d101c0602d860030001c2d00903813510074424548160081d03a41c40560405c0c000484003910000c00d9800d2400b030074401407241d0001008061403c40c4800c10001841c1c04820002e080c5200c00400a014655854204201070345170000002c1140c500e06080d00d100c403840000d4100340c450344460046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 461091223 1250 461089973 461090011
    0x1b07080702030c1005180411030a2f25120e0d0606032108090d0804050703020301060b040801051b03070c0204150602010e0615010f0c060e070e0702100b0108 69
    0x6803d158071003405541164524454010903a04400a080100281c0c80150306142d0044108410f071803110700040701e40b900410100ea1190316a0300164900480c1000300c45000541800f00800d1042520040720342c07400c0072400e02014000700c2d458185a1102c60080d10007855a615a81218400711215105002100066100988805803d2544243c201000300700e9141e0703e08282c0e04002d05c2c4c000d0750115242c010600c03542103000310105800303040001c0c000d00c001c400c0104140c3c2c0c00c20000e0000c0d912807146010010050341e09010700300c0503009040300c2c02d0312a13280c41100707429200041c104a5106c075150180385d00352203101c4180da502006601e020040e0000c54008074008014841c88e800039600c000d2400f00f1100d405400540d89404584216101c940d1000d60351009841d6a03181180050b1786282541c0216120750000034065000320b10005003c0d0740381001c54505000e40d07024408901d44202040360300c80d01440b0181040651440a0061140141c002400048010700303011601080314851 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 461092473 1250 461091223 461091229
    0x2c100819020412050105060a2409030203030711102c0112090b061e0307030809031912090b07150c1202040e06090105180a02090d0501090c0501081b07080702 69
    0x31284109005011541c41e0746650b0049904891280e040d12150b080602041c02410030b10303c20803c644000012162850558049102400e00320041408010480d8400f00260f1703000d00081000e54030504a0550000d48034081c0102105409400024004900e0a00303da5109041d00207114140c03c03001201030f00c0140006a5603060300d50030801c041c9260100310000c00054483c003034000c0c0f0003100c1f5810b14200030004030200b0343c1003009542c4c16401c4603000700005602c640c0903258076000101034441d10001140804100c1d0040c030000d441c0301c11480b40a40031650400b41c1040508042244c445c54030300d01d0303180c0d610003042c100003040b80c055403850b480009a00c254400e1001d603032510b009564441da58121214906e405071740a91050b51014000110392400031650509402114010703801035440e03203d14402504141c0895030081030743c054100002d1401c0c072035070030010301c115040700c08281820001860410010241180307125018132642d142c0d407114080d03407080d0781e000004c242d0b103541500c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 461093723 1250 461092473 461092501
    0x203072117090a03031104050a030b150d08032208161103070f0f12030c0b0601031404060507030f0e071a0c0f100e0705010c0b09011b2c1008 62
    0x61440a401c0710414010015804146112020301030b03030f400d003c09820001158018465032080c1a403100174440f0400005294400840d030003008034808001035100f8401042d0901c601100031204058000100001400070541c03a00801242c1c6c0c00e201c031a2401540c0c1c81000d48640700403082001000c1640344108a080d132541e5590000140507140240c2d03590a1050b421300c01e500a14042042108010407c0f240441c00c2110940e0940c0e1054800803e6881f0100000e1024110a0401d91906c40141102045407400c82c05540300e800009218a03250400904403660400e004164031b08140311020142000034141c4283d5100240b02d80e550141c9502290b4148114002c0361800d02a071804842400c0002c5900800a9010441489146103000b8040e4070343c0b02038061580415007a0b401c040101c2e0742d01d4001c030760060300780300001030f28082e5180c4010104142007198001424440c5210b02126030341c41030700040c0d21180c145041081c0d51800150b00d05200300c60042c10404008001070080d4a4801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 461094973 1250 461093723 461093747
    0x150608030c0a0201110316080f0d060b1224040e0c0a03050a03091706010b090301021b1f140105100c0b07020303161b20060d0e010c02030721 62
    0x10440340d03248544954152542c108500503408109203400c0003c2406000c82110452082841f40c1076048005036a0782065800400c0c0034034100f6810b226007143c2c4005032141a000e400d40f04812a00e94152005840b82c50700014406410a1150000b440100899943e40b00f80c52400b01d41c0818010028000d051411802600183d07025082410000034032801040301440c0c1d40c00ba0f50b440013880c1d111513941080c0d0035195a030ba1131550150300104190111140030b007000c4140240054904000010703010004d42503a402c050607500500b072204a483d60720f1b0756501a84010040a01032190010340d048520401407054a001e488846550804144595604180d007580f00542074200e0504000080d03503034004680c1c280e4508010155010543c2c01217038038803010302e443c508015051040340e440d403510038900104c03840c2081280d42c25040c16500c050240c441410004400500c60a4406000742501c095000c03800c250741041001c40045480f036200b1500c0409001a099150340380c01d10100c8101070321070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 461096223 1250 461094973 461094989
    0x1f090807080301080106050613141f0f08070f170a110c0a0b06010804022211040b0c07090510030609050c09010605130f1d1504050103050a03080a06050105071506 71
    0x3000d40030006000c014606807030000c07001304045912241400700703e01c034403071660303400d201142d2003003090024070a001d00207840090641000c1480810310714020052040304c2d240802c11603446220015841811107a10829070318140d1500d0384502c5025100e00c1d40524040310003411080000c2d0300807841d4201d400c00300000030b00c050341c540710a81d500380c5885c4040700c1128511a0000401e0a81d0b2081d0b90850203141c0003080b0080d1800d0036203204801c2c01039000302d0000e240c0c6a40c0700c00305604507500a40b004086100185c2e40e9440710030100c42c1801038580254075a503203844140403001d84010200c405070703540548002860213240c10950b25260181c8807240e889812007002180090340407001d0b0220f200000d04811f80d4a40341d6100d0030f220000350054400380340d14a10301c1185084170018550700030303801111044c0407045e502c000c901990340c00d80040d111540140c50b5001019407150401e607001214920030002c1e5420403000910900c41c129001c2d000075401e070301c2024100707508d60010340181030f00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 461097473 1250 461096223 461096227
    0x1b0315060c0d03112a010b0406060f08010e010b091005040302060304030c060b09040b060607060f1a032b0f050d05042105090303310b040320031f0908 66
    0x120305503078500020007900002030a0543d04d030505a00002510340555103100ca25070750030911001d610580f0701c05240980550340724404042c194955100b104080c1c482ca0340c4200d06480e2002010f84400c2060340006211480400108008034409080d2010140100c2c1c1000b40740c074620108503528000e0750400f0390b0102001090004054010440d0902144075260902c0440c0c0d4100402180f80b00c21a40900082d030410300103800e500d403141c01081010b10560001907000c0d08420300500700d608074403c2443c18030040703241c14101d140030069014125980c80e1242111030307071611286002041480301c10103101c240d0300c010600602070070a0380c124111541d01045185080e05000e0488211402c95418a60302052400078052045c2d003280c801c041c018000b94940340c0b281c40850f1040384912402d150070107440c0780c003c40030144280107400030290190744944440c110f041c10425440041c000400e4400841010080350301e0215101c503103003119080f0b4014401e0104e00c08006003652000040c038132000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 461098723 1250 461097473 461097487
    0x150d0c06080703230402102007030b0c0414060306011709010b0f06070c0e04060204050d0303140109062d090903051c0c0503010314031c050f0705031b031506 69
    0x1101e901d01c1d20030852030381e09120051416020030846580200e040c00880b0000d0005009803c0504c0301e4851480b062030302c0c040c91045040030740f4850f00000c450344425081298104148515000b0054124082c640503034509460a04150074481e01001e215004a02c0400000e045e40c0c041c0c0d02c41901041981e8035403441c0c1c54801e40541c0203010b90310009101d04500c44002c900c6050410030740e01d00c241e0158622202e5818030364407501c1d118005008544031030302004013140e581c8690304041d078280d1080d04c0204641c1c0c810051039014010503041112442d01c0c1050402046c00300300c00140700e4056822240c0001d04010380f440072104603e40107a6081410b0000b0340080562000c000e1548011300000c0124140041901c50b0558190030004000134405200500100d402201c1c0300760100303c41d8085030301d072030240c9040354120301841c0040c02c529599502000201c0341036000c0a507100025180c83c525500d4000c0180704103854160000032213a501000040000c01816102c4c0500f4100821440c0c541c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 461099973 1250 461098723 461098727
    0x509060103030e180732090405040602040305121c15030f11040c11010509010b0306190605090f061f02030a030b0f0d080717030c0403080715061503060608040506150d0c06 75
    0x10008000840a10442448070343c42640c1a0381c020704503003011b154500503a10303003004094040038000b034070701c59401c000010008008101d00b81d03480c58654800c0791152000b403103a1a080411a2500c2001403c00c3e25880350842000d0030181a00e0740003590106880c504c1c1400741134009001943c03500a46004034000703c01c5c0d001034080d01c44c0546180280140d5a8200c009400e8900d14940e40e1740503441a0003241d55011200d00724a0403440403c0002400341e40e0743d0014180000954124400c4004a024003c82781450214100500300701c0c0c0d0303000d44a03188028020365900c25540c09004159071007001c04040e42c1d40d807242100c8240700605200b5a0702c054180181d90703604c81141200c0c811004aa0b80d1034107024103058a00c90030401d01c02d54101441c41d1030360921540030143c02c036200c101c0080c1641c9100f12a104e02c1001d010380500c140001c010801000d012140590081410301ca42c01c0200302c0010000900e1552000c501c002d01d40741c0420b25004203801e500104d80061480c3da40001c0801c0c495 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 461101223 1250 461099973 461099987
    0x39030c09031501150c12080702100f060504110304050d120603140f01050f01060225090c0e040b0604050a15090806070c1109010b030f2d0a0b040509060103030e1807 72
    0x13510b50503114240a2080900380d0b0001981c03040106032102000c8446441c9000e041415803025590040d6030200d08100d00c500b040781c0701040f10000207641c0c1e040900840c2013601c600341900c001a680b40e441e40c100b41d100d40d9550905908030b41c00300a54550070100020098002e4401154454280742006480719030f80c544880210700c0c050020362030000000c091f14030507100305048030695000b414403400c0c00c8000252201d26100c000b945090460000a1000c0c5584031340d6021401c0740d5540d24000c3c0d0348600304000d0b10b41c0c0c1d0020500c215800d010074041551071441d020100c030860f0905045003a0300c68000d603107240d00e5501000080c000d0800b00503250380c000300c860351940d11420b0001c5643e40910200034000000f0301400040c1c1c1814000110b040200f002004d41141000a20392041100c0200142c0c2c2c101003200b482d250014607000b88281206075000d004200d6000301c0f4140b00d80e10308818103d50b9680140f001508100c2d680007500d02644410150000a00d03d140d8041030b00d1800c400003820324 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 461102473 1250 461101223 461101229
    0x5040b181507031e02010219020a1a060a1e031a010e0a06030317060a15030903110604030e091504140105011209030807030c180305010539030c09031501 67
    0x509101c6020000008010003200e0b0b000c1e40c15195100003880e448150010030044c88003280942d03600304082012101c4040616407986c84941c0104034084e100d00d409071100402002c0450030204030020702c421562038605820948000e00c0c0e0501400d90000389035407400c1c1c480d0f4000b400c602d000030b21740d03031405c070a404132070b03058641820707030003103e43c582c08219000c460240c4006400101041c0c40c100c403100781d105560750040001000c141c01c0c15115a0102401c08200342d0400c080b0f9500c1180c03008168104c4906002c8071540c0014020500d450340b005000f600c40b64810910038036a9000040c40d22000c20751300c071420440540100040c04404001854800007030090070b011940b00d43c41030310501e80714000d0003542d942c590f1328000203441c0c0ca04150081e003500d41180e800d00c1030350400341007400040b035244001540203d0020a65045c202c10191400c01c2d281c4080c841081e0000604c01019000c0c0190654661a400300582e643d552801a0703d090042c0078031541c0c140074a21725050700f02c102044160503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 461103723 1250 461102473 461102479
    0x3f0203072102190501020303041e0c0627141504080307120306050415091a090411150a020601062d020c0a0605270402070813031203090503180105040b18 67
    0x6504110f01140c40700c0c1040388035550042e40300700300140004050341e6112800c1c50514820140c0841e0659a001540e415078100030006641c44024101c11006020007808003182900c0d010519420038000070403078026203900390300500101c80d20514030700d1a41d00b280c00900c448010741b03803604250314050305610f10700401940000e041030740210302450903115410b600c0e441404c000b4503062800c1c41070304c082c05130300b41242a03402800140854503141c1110042c8075030b2040c40c101c9a04000300b0204540e6941c42041841c2d05001800000d4500b030f000909181590384905000c0002c0c101900e81090503019816010800305402c85000512900001d44050b81c090817140b0b4410300e6201c4104890500980440400c03135080c2c0c884501d5046042c000255a010001d0b2000d46000100c0d00c643c0b007170390b0103012140011100b07500300f00180a103000c00002083d120b0300e000c0c041d500c02c9440b0155a8000d5805803018503c024840f000140e004500b00e60080507000d0299842d00408030424410845000400780 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 461104973 1250 461103723 461103739
    0x9121202070906060c110103060f090501031b080a0b10033003150b070c03080705030a110c090a1a040e010b01020c0307060f0f0e0411043f0203072102 66
    0x5a030040e68054401552101d990740c185214003a1106c01101c9481e5640328141592103030081420300150905170060310b203142010500b54075510b000400003807020075640700b00804600030710840724086040b024903a0000301c40611a01d9109008080c1500780e8002420a01c0d800c3c1441d89180c691341f06081c088650310b80030008114081003d50a4030f111003e220b650412480d0203000041000e400f034501d5a004e0008140c00c40d07100d40da604010307408080300b81c841e9440400d011101d940d01c450300d0121000341d00c01900d4a00708000104040000142030754000548a42d806214004480d40030000103a00600521204050b03011080c002c10f8170303014450042c050119034285900300000c42000f02e4200342c0c1c550001003000c080071074010302609101c404201740b90083c480140c1e03860103419410701d42c103400b035982c8038500100c1d000d030080002007660000394a031124444e50413100c1e0340c00290206910403e220911140b0010742000c1c0607411a408400160700c1026911001148100d8414400d8452071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 461106223 1250 461104973 461104979
    0x60112060209100804050d0801050609011d03060103030c050708071208030a02220602070e0105090106081b0a0e01090522231602061e1b0405040e0a1b0315020a0912120207 75
    0x441c223070b200b400340c0c0750401070410a5000651054400c0c025000c41100c106003402c0b40302c0d0000e801c4c40002e80c404c1c0c000039120842d01d001e102d028814003004107800350060200614001e050840b442c0804809080403801000003141c05070950100c41074005140b00c8200c107590140500620445c550203042c1c01842501d0010400d42c3c400c1030b445041e284010900d0150342c0c40c1000880b6441c00003031500e10040d003500c0f46d50300c81c29040b4000e041c00e10b00d161034000500003d90001000c1a2899205038031502d0085c688643d642c0c0036290500141e64000d00101d40e6092891211000100317401c841907242803004100810302068000d03d6181c1070b15036080e03458507200c40340071002442507035446012014101000c15001c00000d401c10180c800714070126130a0955520004080710584040c4407215007000007207004000310f40781c83c5400121202ca880b44801c1c2941c95003040c0c00f4900080b02d01c100e600082d6144000d0241d040000100325140440111964074680840c452442c2e039507820140c420601d000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 461107473 1250 461106223 461106227
    0x130806010909030c0605060102010e06010312080c070f030309050c120601091b0516170a050a02010b010203130e1e13031404120807061526030c060112060209100804050d 74
    0x1054000e81c16a9a90032058130b90303203540c0001d0401070812819076685a51180200c01d040c08414000c5000c1c01c1c04030520140f6070800b510181c001401040001c0c0100007100c0042d404030360744142c164141c0380005010002f031400d24a416000c025803580200604040000c400002540340c1c181d6013084002c0c040c0d00b601c00030b0600a0302c50f0008100200e40284042e520b0650040340301d40150f40519020340181840d41100781d510380c015031404002075170005007030344407135024002d00710000000c0c03009600d442c61204030b621050310307d8040c4104c0c00c5038003000318080c14036011030403451514481d80c81016040c90320a604104040c028220081204000d503100c0580145054404890044110703840f01c514560300d050f0594000582100e1080d540c2e6402d440d05514504040d015003c0c09184507500001ca007480c682091002c548950b444e032040258003049500030500750304507000810300c6280c0b07000d80d00d003001c00381c040d5801c220342284628500c41c802d5984508800e0142d8041c0c020b858000000b0741c82 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 461108723 1250 461107473 461107481
    0x40902090307050d080717070605130201020d090303021c03020c250e01050603010605090d0501050921030946024f0614040608070f1e08031308060109 66
    0x1e4074000060111b180410304170ba03c1c5c004c0e03040040c00190724042070341d41c2e10350450f0b1007610300800e01080c0007880c0c021941c0400150a1180b020306002401c1e0703155a50003551000441515065494010b15400441e8000c0d01542c4a03020640d05403001204c2c0210f034120710f29044030404181c421429000120f05d00982280b074180c80d400343c1175910310703800c100080d075030780d0700c04400b4030f82012000e04608003140702032081d9401175507150701400b138540d040c89111548480000c40c1088000c000c2040c044a40e10000d890504400303403121644c80920b548240503003241072070b03020318610900006031405e894a89121048018800c6402440709000e11002c180341e00d051041c400c02054166184065a0940e44546400102007079050b1035900500c0140000b514219401810007050a42000105140c5401003001425404006000c01d034504540200085280c0c441c04403803503030725400030f1031700003403604070001900004040300d0351245800340544082c211841011541e0080310000b0a0354843c9006d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 461109973 1250 461108723 461108749
    0x1e301507020d08070c0b1b07060c12020a02101d06040302011b091206201201090e06130308060d1202030a121802010e06090405010b120a0c0f111204090209030705 71
    0x3a6200071740c00503540d000e0310b4110241c040440603100a03421048245d1000003007003900d12825010030100501070300907203a801d0454214a401d40103009200c8803030741c002841411503110990100300c104840741040003801846072030501c42e000d00000c1109054054121a505503035403071090780588000321b01192a208180500c5066400c505d40441c0800c081d80c10107005054000701d138010f004140c8030180070f1030b07001c01e0240c44000580e90040111035480e12030340c818030540c2400f410b440e01d894501110a103290100060600c20040301080142e02d424038114101d035884816150701003002c0303d0203075407600250303180c03800220320a0b41c00d5102083d901079030000141c02c0752480c1031480168010340e140325130f040b03e803904240c0a021115140d034a500031070340240040458550790b40c0d01d0010510306581d000f001e801d952030030135404440322070f40f01110405a80040c036002034101400340c4486d08084650b0700c901c104504c04180403a4199140e4020700e00904c084048600c0d10b650b0703000b80529440d10b81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 461111223 1250 461109973 461109977
    0x7230c090402090a020a090906060f02071d06060c0c0405010e16110309040207062406090f0e010303030f0f05090606030d03060e010501050c070e01090b1e301507020d0807 75
    0x18010940713a1500d60064103200702c46041c00424141c0780d49540d001c4813403d07806070002941901810800340e8040c4954006084604120545490b01c58048208c980010340154000c40e000160703460080024000445039130300041c014022540c1d21803009803a08404d88014005a01800a000c0040c0c0240150305140d4100c0c4041c41c01d08150760f04000081d000b10ba1b0951700d990300d030909000500c1508080050900320f1800140400e803d00b01d005200013166008090030f0744540741c0038840e09410100c4107044a5162170003180410030481e52402400d00300e0890190385090400784030804c079000c2046442501d0a504948503081080340c100c0035a03003e03111300c80500b4000c0c00140074651040b0010212417058800f01d40c0c01c0c0e6514030441040200980c48801600d946000007000c0e45891114241000c0c8134a507400c07170003d003481c006025000c3c00c0703528000c0c0400c00200400035040c4558690802c0a41c0010f0324800c8400e4420039009800c1201c0c207400600885220f21109805511032034010300c40e907 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 461112473 1250 461111223 461111239
    0x1081b09040f062c030309070b040b1c09050f0703021009050f100221030603010c0306050102030a08040212030f030604060905130b0a061503020915180906040207230c090402 76
    0x2034480d01e004110410940c000c024159803004840e1204040308600c480d2031350020355603494070010907410404a9041040702c2701082008000c0480b130309040d1050414064500660752000d00340420081001742e42c010a2806420564041d10b080402c1002c1200c1c001d44040c3c3d5290550b00080313030003105a00681c0d0384010711f21010350032424508441c004a0301c0a00440da10b02d009202c080300700003056031445a220034000200040c1342020700409103501800d09080c44003071f081000103902c074003c80e020741c400c000d403a000090070b5540b10708510134203003031079420350703a4070a041902030445600454010f8003e900707014001403000c210b0700c07030280300340c403144000061780500350780d508607180014265210040d00c4030b00c04a0a40101c81d9004078440b180c2d10016a51600c07981170001d00c2d41101ca182c110300f0070901a0200d200207403c21610460000c458007030032a51131400060080c000c1c4903019200f00010000c02514003c120990700c40c3c0810001200c01d12400b0404102c040e68044030000c1d002200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 461113723 1250 461112473 461112503
    0x3060a0e070e06060702060705070627060507050703150b1504140114040801050708010e091c0c02010210021b07080703030e0d030e030f010f0b0105281701081b0904 72
    0x8070500c081c3c0146004106519161554000031f5064024010a5481d50449030b410001c00b600402415070560310240344220b4528407007903115011010f0300c030716401e12000180e03103002c100003400485c1c09954064021340742c40c140c000c0b104c8000d14441c103060380106400c4040f40340003803032001940c08445080007011149411240111817100d0200f089900d282d00501c004a0306840a0203000c1c8503000513942e1080a6241c01c02c5183c240001070200c3c0030701c0e0800b0300c0c1e912400990351102400c2019a0801c0350f00700b038440c070040f0318000030200c007a414144081015107641c0300c00200054111103910449141d40e8070341c1034090f2260b82c80e00c0020701040e00110000a54242802c9610b90180203042843ca413400c1d04000c00d0622040c0030003d51682d5441110048811940c82038440b140003c2c6021418040580c1049000c0c1590400c0c0f111500300c0c030100c00c40054400c2084601c010680d00d110403081d40d4541c0400d83d6820f100c0b008100020004500c10114240180c16510072904880710000c0004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 461114973 1250 461113723 461113739
    0x12020906040c110607050306010e0607050c010f09031e0501060e090a2303071220030d1a0307080d0f050306090f0709050411090306070206010b03071b020a031103060a0e07 75
    0x100c0b051070341c0901202c160307298400c90052204074031a41c540e8451070342d2803901c40c0005211101980c0340510820040c00810082100000c3c80318004c1d900707007020f40900040c1d11040c1d804c80309a03400140050f2035844110091103002410b0000544103000910500d070321242c1c2103801c01400c8030364090a5000090800119440000605040301180c0d00c8240e01c41c84240b489003594050401513401c4800510b107940d11a5200445001559402012064000b0743c084865161312910381ca40751110340342c2d41d21808503005100b0507201490000c00301c0707050380d54680d80f0b1525900c20080301c00204251715864002da600980c100c92044200038006841030395604405c10140398003030000d80801818140115141d22a403080130942081d11042c0c0e0786502c1c00504052401900412107030441d0481001004015030030f20907603820420a0401d0b005003508031320b1a050411000724041c0d0310004444000081c404041c0c25a05004410350603508030365103902128054401181c21030200e07902c50f4008100540c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 461116223 1250 461114973 461114981
    0x10e07050907120513060f0209130c020318041d06010f060302041815081b120705010c02100c0507060503090c010e1309020d0c0b040f320d0506150a1202090604 70
    0x42c051702020030141d041d039110b04c1c049070f07001d641180e809603002401e044d06150400c1c00400c070220820040c001c1c1d00401c4802510b034004c203980004604001d000c2d044079a92590850030742606041c1003a00c07801092601139569120a05c95640e0348083c181001c1100382c480d00885054a8060224810058103502140c00900c075408004007904070400c4045040c0c10240644078240000789249201035240504020750b0f20b91080c900e401a80c00201c04000b582d8106d0800c5001c0c5030100d5440c0c01c1d00c14000303816510241441d40082c21802000c00224102d60000083c60140460354225203071ba0041c4801918888140c8840d01c0d440100350384560b800000540105400c01d01c05002e400d800e1b41a80d0301c8a0030841240c0000e1860b000204042c13011445c4420840014110a0000c410042415107600141344100c0607809850b186070464641544030050f040390081d51050455005103031480700102d10b0b5940541c0b0750312070344148000040d104070a000c0d1070442500105110199164041000004c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 461117473 1250 461116223 461116231
    0x2208030a0905060907050a08010509060a020f250c080a170c070b04030609020102010b030a0f022e080108060105102c0d061413120305060103021b010e070509071205 72
    0x49600c079410341000510030b10400b4091103c0070002d00a8509103010408140c40e01e4000c400e10b40c0c504002c02880c114000b4109811001e403020050343d0301d00c40020207003a071240a440a5032000035403a0a0f090341d45100103001c0302801031203030b10318107500d8544454403105005000341000030b03003880010b0201d91542c001d1914400035011189020ba881d58081d6240e0050703842503501c0c503900d0308203100359602130040032100f800c100e010703180c1c52642d540c40190000c0e0b4228040e00680613040c0c0f8800000d0003188652000091200ac1074881d07c0c441002841c80e8024081c5844034007903c0000500b60810040c01740e24550280c403840c1c1c50080c1c0c0e80141d010503003492031a1841529490700d55110b500c0d210305010040780201d130f011a9500d02d5118032000900c028004070460002184c070000031800c04000d8160078181c030b18010910f5202c48004801a00075240e48200219060060440790401503101316850b540344c100f40c0b02429034600403c080c0100480344200418210400054001c1003070f8065544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 461118723 1250 461117473 461117491
    0x909231f12050c0307090203251418030d020106151d090c1305031b040207110406090605090108030901081b041a04140d02010207090b0d02060c030a08220803 69
    0xc03559490079440801c0950314281e400b40c1050540d080780b403d041c40000080c0000400561a60034814504109011164007040a800030a07002604a0744507401000641000c43c0185032a600591001c808550102d0f407194400d105105040f814640180112402c81e00d07003a00c41c4122007282030054400c1c0c0408149a403030351243c040440610740c0d81e0b25100d0f029034495034807070703448503d02c85510800100c1a08007a1003139111650410603420f2103d0380b000d401806560140e1162414905036003e400403d1400e43c0c81420000c0c0070504400a40c0301404680c03088071202d60607603035840529102e100d100803480c00207200b080001c1e0741c132142501014030710b004c7c0c0400d585007603956400d8003440c4960401640c280000003d00300070111800e9071455001c5021980d07407014101c6580041e690300d006100c0d110f02103484a002c044240d5070f4012003191550061b014580c0c41c40d5141c0b0050b184d0f884685080c0228000e0701c04030384002580030300003140c034125501050301d0f2011500d41000d80d03080242304030300c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 461119973 1250 461118723 461118781
    0x41b08070e030c031203040c0906030c051513032906060301030206071511040905010b09010c0b07120f02030103030f0c080a1416030809060a0c0504050d0c05030d090923 74
    0x100d540f42040b008004960180d84292a0705042c03415023083c80c5564805c2500e0303403c00310188017140303c0a503250221903084030090000076110b80380d950140150b001c500c5070013842c49000802d00000583d1000c44010010461103000b6240c2200e07201c103c01642d540c0e81002c020b100500060418200418001c0d0141c0480400484030500e440c040d10301682190804200200d400c105032104c03402103601600c41c40c00040e04080404000a1070300d110640040d1a9010013008141c041d4014000d0140880303159406014003c0303401000c43c0a0b5000703100850001c0e0803903210b084010f104000043d91558054410b51078404083c0c0d0444060140c102451440c95003007003400d41c40b25408820b4100107100c1d403a0345585140080c0c443d4104800200a5665142003010000f1483e40c03050490b42030f075a04948400346c00d01c0078200341c019502160001074151040c1803114900d96000003054084540c0030105109280410703460b141d0001010b02e9080b00040c01ca0080341a0194a00c030100b44100f01100d095 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 461121223 1250 461119973 461119993
    0x5042102121905010501090b06220f0303030218010206130f0206040e0405160b03060109170f010213090b04020a1407030e0907091707080606010f0c060f0209041b08070e03 75
    0x14104500808001020307042c1e080010104103003800764900501042c03104015180340c0700c0219149226031403005880540d40040c1c840c22403003403112100500506ea144142858892030701500039840380c3c880c1301400148918201c013035840051164840e00c1d8800005210f030340107681304440520740c3c900481c3d20107014440031442c0014040c906124600800081040515142808122a5254210009040080082100c1d030303608422113804882c1c062000f40b82c0c00c0c000d00202c50070b0902d85004010035500014840700300e07044000c001800d8945151040110760241410013007240725410000022070400f10202606894a802500547e03019081c114140c0300c106c00001d00a100807210000841c12154083c80b480e004007014401c0650481c00410901c0d0600b00c00f69920680103184a0400480324016040942700703c8490103541d5011006101c808003581c0c603940079411035800c0d00d019074a1701c40711030b843da12034a000c084500d1150322280c0341612240400c50744951900b0f034050700b51049a22403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 461122473 1250 461121223 461121259
    0x3020d051207150e0a08040b090f1c020306130f170d0e070602070501030b03030d0207051216110405271f0603021c031413082b05042102 60
    0x8008031440f0311019002c85100c0700d20f200484030b45107035100a591208200348001611601280c00307491104040e16260080040011005a17000d640140c0105100308a032014091003480c0f0213603a88218207450241d900ca107a55015200d4286d8040c00214900d200100030a4002e20342c405403c0704110840e00e440b500d85096000d03a144400b16100d00da20818003082101e41c180f01d018082d14091a0501051b1081c10010380e5038012404240e140360750024078502000340410411601d694440099611642003503802d51000e600c0080640c4e0107104480c02100d5031415104640c130030f5540000e401c0b1881d0307808681011100074410604200d01c00d40008901048941c1182030541e1820240440c04c24114070600081a808803900c80c0300702c0340c000e070002c0013030f8111008100c01d00341901125100d803902c4002800c601410740c0611080e006030000a030802408901448c0c0080c07480c0c00d41030f90703158488412100c42c4a03a2294810345041088500b40100c021045a020180010080c0b80003500d49001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 461123723 1250 461122473 461122477
    0x27060a0c0c0b042a0308090603060105041d070207090c0804030309150926070201090605090a031a0601020c0a26010f111918120c03050f010b19080703020d0512 70
    0x150784d001802c021841084c85800183c21080f10011040c0d8003003455983d0741d505d00c2c00742c0450544907000100020359680d11600c1a80e004150078805d0f40c0702580804507034012510180c41c444018010b411002c58008144d0240c803442c24215910520b280ea25034401324024480c03401c00315140d0b03408a882a4111016002c2c200e20030307010300607038071215a100c0300d1443c400e01d8414484038000c500707200c114017503070b002500359007140c0a0b801c0c00380c1d40b41c0c01000002c1c0302c44c00c16000181802d1040d911103850311600c17280e0b40d1140313000b0713001c03101c00c041d00004110740c0305420310903c101d6465210b806000c400c0d08621041c0e0802c00d407400450758018440e8010107584441c0050300350484e0200d2240d000603050100340304d03a1480d50034140c4001d51201881d4045000c0e5000c1c14030208030962001c010030a050208400441d00321042e07a81101ca03c000b01c601810010001920a032004603031400000015428001155480c00050a00501d55428010881d002c46425921801012b02d0380c00c09043ca030340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 461124973 1250 461123723 461123731
    0x20105040b150307150201240e010e1801020d020421150c11070602011b030e0318180a4104150603080415051602040b12030f0327060a0c0c0b 62
    0x461008d0000d85001e00d5042410414982e00181000802114030708200c001d041d10360307000c2d88805581c0e49408000200c01140301d0012150700c0000c604440a14030782c084c00646800c00c2005000c11017581d000c1d4880041804040d0001e0107030000d03404550010f40c003480b01c4450310309008032500a500152410483c0319403101025035112003410a01d00c556a450264006081c1401c0003001607902d020340e92400b5007082030440c00783c481d81b054040c0d0346500c061080c0881071401c600741d43c54854200320141c1042d075003007000464121282c401c4155405102d4840001200d2141068070b2030381c0511307a20880c080c0050790212000d5080d00d0480c0e0413801200051130080c01c203944d8480c03a241c05400b0405858017203004007d001d000000c16a244a4510703414150115400320b905d00401001035041c00072008200990f1200064440c04009400041c41c82000701e042442143c18040f44103941c1d1891110405005400034000592010340a0b03000c0e0380300c54064030708007400340c0e44d81da00d40900c124165 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 461126223 1250 461124973 461124977
    0x210b0102100501080a0b06270615070614010803070506060f0f10171003031d150c0c0a06050301081504050c0a080c03100b0d0303020711032407020105040b15030715 72
    0x10040320240181d00c0741464100384c007614500901c08040c5e00039014072603240608090b0319400c00200c1d090b5990315005554ad05460400702ea0340780e4052401c14000c2a0241030042d0060702940001000312001c010307520829082005406240c0d183e10800280007c1c01042c607a02c07140032408041c4c1034550400100ea428500d4480d00c1c0d444100c40b800183c004070051000d22030048034030080c00029404001e00d000341034100d41001038545c9042c00034950b80000749d00c0d61141440450345036601a000100000d012000303481c0250740710346581c011141072109020b0100a540f108000c052020f58824030b46038001e01500503100e482109c0e80001c1c0d0f2480e59070340034680781e5101e802c05025500d011301c1240b800791205030040102c5c0740758101180d0f003429485c90140a0541c00304200c014400c42c4103299080080040944144c81c4807003d03040050700d4140104084964060000f0b0162401403050134090341d00901e00c16413a5603001c1140b060489030341c0c1c0c0e00303815008601000400d50032050000310300030956 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 461127473 1250 461126223 461126233
    0xe07060207091a0a05120a02040f0c0908030a2a020402040905061c120309111005070b0f06091302060712090918080712091706070807210b010210050108 67
    0x8030700900e0a543c000c41034166264803e81c10b20345643d940019450440da416109004c8080400e120715003480000000a500310f030800d03003808003042055128000104868035480b29007070b10b6020255030f0740144500c000115031100d4001c020000d0990501504407251108040302ca44264041f0381039802690140301015225801c2c80400c2c41c1407540710445902c50690030003400d0650301e41468003164001c6501c285681d0307000f44000e02c089025846005078015201c00011041d14100900c81d5000c03103000c2d94850103010105031540c44c1907102900582c8002c00d10807194840e68200321154020785d0301240d1059080001000103112019030030400764141d1100d0404519055030401922007980383c85c03401c40c80391b041042c0007403894020340e02c0242c1c001d0b1038001c644411110a8070180c03c10f8002051810301047d5200d8011400030300207114081c90303600d9500701e40b501a0f00b03480004011001165602450740c98210b0210243d00400d4118414811141440103083d411000c4400a1b0000d03441034100b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 461128723 1250 461127473 461127479
    0x90e1605010203131e0503240708090a170c060a05010602010b061303060509011d01240522060b1c11070804030f02270601020705030c01050403080d0e07060207 70
    0x11116482005040a0010318508080701c90036201c1d542881c068000140080c014107600b030302c40110500042d0202500311074a54a09214400e1201c8905e200010038001000010308500d2084111600a0842c007009104c0010310f560f91f0b078010b103498051450000740c01c0c84100041c0c6010050107004440701c85001429506055009003911480c10f4410701802040010a450505000c1e940301142e800000c0021184c64010a03070340500045500b003000740090420f0541c440d0019404040c14601d8020801010440ba004600c1c2c41001032090641c4070380400302c00c0224034000e00c041e503003200c049100041c0007078880c80c1001c41a00282210b070400683c1801c00d01d101074183c850034490549103500c1034205222903403403c034548601c2c003005120032000c0c040c5404641b00c4200004801000210740d151480c840f04141040c0e00c1e045480600520414130001514100458404014081a0346032403815040d6152000e0719400524030540196442c112041100002d20101d00503119540c003901c05503103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 461129973 1250 461128723 461128753
    0xc0206010503010509120906040b0309070f0e060d14150c04180209030c1903050303130203010c1706060703140a030504050d032a02150c040f0801020f07020d0804090e 73
    0x120580003540240c2c03402c0148203504400080101244540188141d540d040030400f044480c00340350b10010313102c90080148004c2180100b901015039001e054542c010548e21003007070480030401e80e0004c0e00a61400a44c2c00400c402e0b03002d96042d0351603013040311040c0850780f03d245090300d0201d45400030030f04003280c14000b40c503494a690986990800d020743c00e141407800000d031140c1246429a1143c140b0300c010107007841c09030b107444005541043c1581d85900e404151a0390142c528a02288254039184030b44010750300500769030280711745081404849076149800c4c0646680614016410b0050303042d144900c4640000040c14562610b030303070100303003418246820f5251081d4030710823900b41400c0600700b40c0c5102e90882010094540340c0e520058440034510280d080106150222440c1002d07142048581c408501c000c10440b5020210088802c0c0e5840710765080f40942e03040c800d1002c1041000002514166400718035250080b07081518140d40d50381d0340412900c3c5042c003404075400034404004010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 461131223 1250 461129973 461129983
    0x307021504120c1406070302040314061b0d020c0123061005220510020d0206010b04060909050402010215040501061e030b0711010b040f05040209061801090f0f0204090c02 75
    0x603500120208180c202a500c42c0b040b1148941120200009407841c08244100101c66010302d400c040180c0381d05080044004001c0c0d0b01c140000e4410035102980584144400111030340710310800d034210094101140c090300029880043c5240c1096001d10007403460410030b10841c05066852150200840000f4074007009000c0d0090000c0c0c820104500c1100341d142d08042200c01c1c080c80c800040720301404c2d0351840001640107802c0b16030040725003079645030034a4000030f18040307001302e81d02289c4240c1e9880c3c041641c0c62089000303440c006400311401700b000140ca0741205402a2050040e11141c2083d02c22502e04080c0845066440341c0d1102d0040004050700484030300b1301c050341c1000c818003c0c2151110402d0042c042c005200b040009800d40016000039440404501d400900130302019141a150310054030042e10f059216941c000003250082c5041c00c20548000901e4031801c00c641c2c40e202580c801023022001540e0300a440f42c03294200c0101510040c005401c0044000517020405a0001e2902d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 461132473 1250 461131223 461131243
    0x41410090807060924210f05040b040c0806011202040e070b030f10060e010507030e0109180c1202070c1721040602060703110d0905030f0a0806130902090a1d0a030302030702 76
    0x131000d002c0b805040d42c0e0f0b001c03000702c40d1456410300749074840f0400c501000040c0740b04462031202d94034150520040000c1c021200cbd0181340249000e905464448212580750842841489000c03007030704e1303002401402e103604050ad50740380f44030a82d03243d19a1744100380702960089821141e0000b641c0c0c100312043d032090101d18050302940c50b0006e400419080040c00d1441656405418460041c0c0030440603072003902c400c0054017410f03080b1080120240c8014001d05042e054ac04080b41604e005024809081c0c42510705082e0400070782005585441000d081400040007040c1c1280161405c3ca8481c00c45c02c4c41840815105100d0345503140e140160003800d044000e1f040030109400d000c820500d034480d81e015620008011040003412071100d02c1d005243d8821141a052003601c0818001321241d003200040f4480c520940b104d64690107020115012941f4481000354000c525001240c0700da610f03640604034491240820f5203d01c8200f0303000926220b50300c0781c21400250004100071741c03c5d6042c0000243c1e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 461133723 1250 461132473 461132519
    0xc050901110a030801091113081605010201050402061b120301121502090901150504080616020f0d0f1b14010f230c0d020702060406020a170414100908070609 69
    0x20000c403c3d40c00908804040c0b2401e900340d91101040c046445d00082202c000541881400784842d030f5420459031200030016015010f100080380000301e40d4010b00079113119590041c401c628010780340103150b03502c984400078290688520000504c07100c01910045000e040c03105c590030082e40701417801e904003001c081c91205200340144040d4889071a1641c5950540b4003041d4140e07036032651524110754601440c0c0c01406284560b000b44240c01c4881e4041100151a0b0b41c00e4983c0821544546a40d490300740030745100040d8a2007131038000d2071107051200010740285c81c8500c03113044244c4402c0602c1501000c00301243c0d42d20541483c14a445200303100500c691900d14400d03882c000d2031240c0058900500e1301c142d03404006400e03c60854103038110f51354540d0051050b500c0b140c035004000d549858119048502000c802d03406000e14050100340d90881c0c404c5202c0711004204a4103222000011405540520a9414000c01ea074602808100060700f219035520ba040c1703140c0303a01c000c1d64510519018031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 461134973 1250 461133723 461133733
    0x80a1b09110d0b060d061d06030a03021203060411030a0203091501050a0b09060702150d060812160516081005160503010303080414010609140601080907050f0409060c05090111 77
    0x145003100c01c00c1c0d03281c0303403607090000801c00b8501d404900d4034400e40b84441545854280040340f4000207040000c1011a183c2084500359100c0f0281a034903042903d025015038071012004d02c03070400a1001f15480f0501030030220300300004580318100781e00180c800c1000c0d540c011040005014003008109402381c0020702140703541d45404041001000701d8020380c500c0240004a51f4641e49403a0122099141d024100c1c00d0300000c22a05245c3c80e411107020340024a0520a0014080c10700240081c0050200c1503c9460a4550300148008040d440c5003110380e4014048014000100385003003e0081090601034104100305003444003c0f2800203219407154064101d2040d855a8009c0030781e415654541441d8583d07440d5030809180500144003c00d1381c1e50309200001c0788580f1550082245503801180c4201aa02d88000544440b081100c4400850388540010004c601e440780090244a0000c2c000055111031600c0e81c90a13901d4884401000c42e00c0060540c60b603503803052218500c0c11100d00a40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 461136223 1250 461134973 461134991
    0x1509060907051809070203040305160518060d05060a0605040b01080906070e060708190f03020c0a1502070515010515030108060f04060615090306050a02090d120207080a1b09 76
    0x2650340e4501034880340801802144526440341401281d4100300b0005150303160500c0c1400c4c0096681d403290104956500a06201e01d1790420101c5803e01501d500400c1592041c00c070f020151001d8200403d01503115035104142000b003042032000501070103c084004c10114205000d102c00c0e00d01d011501ca0400c0200400c001403008003203601c4d5000019403502100d010700400001740980100f01d405071a46800142c80d2009030301705031101d00e031000203807a800032212807600e064049008011a070002c5800c01150000022080f504c011a90100c0c1c002c0141040e43c1611503601c2c24601c0404e00c000140f103d0300500c05072401184210703038080b141002c42c0c55981090585611958054513890034449a1408a02041030b55000007018128901c0e40c2c0066998141008080842c140300071ba855903c0d00d408038005c18540c2c000c54010403001741c040c41c050203403aa207160751141509950011030003a078602040313495080c0031091002c0d008889000c001c40f0341d14240d0a01503080e51014070b81501e010221 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 461137473 1250 461136223 461136229
    0xb09030a050f0304060b0a150e040209030c130609180b01080a050a0b100b1c0510080c130609050708091b01201e010e0c04060803220302040f05150906 66
    0x54002c03814142000ba1030351900c0c40c000c0c010741183e1500641c82802c50390081340c0185c0400c0750f0050465290780300541d81d0410b0090004a118114202c0e8240c1c00c880244d00290501c400c6020307011614a4000070350564416001c0119115003c4104083c0242e40d5900280035511030300340c2c0034052800142c0080c69681e40d03590f5031001201001000002660002040380340c84489650040c000d10110716640d4034500c11884d800a5504101c12440d1305d0305011450342080b944201e0240c440b004003c261540040c010800440040780c1c480924980701c0c2800b0811701c900340109405203240e5282d030500c80c105400d429003004d948c43d503080714a01401158145581c1d00c805903a214031000903a0042040351900c001d41808034100c00c90000b44070800402512910542c0a119400c2d05034080d1074014040604000135980710744101e4040750b005104005003041c901d5207551f48a2820020000303c1a07490f0b0115081c0c8001140340030809990300204604081c40b03643c404640503044684648500c2c1c28000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 461138723 1250 461137473 461137477
    0x170c04030b0a2a1b030f20030f0c0a020316030c1202100c030509041b0f081608090307060504030c020f030a0f0305090f03070f030c0b0c0a120512040c030b09030a05 72
    0x400c0201c14002048440c007503030810402c0059400f113000110032508002c2c003030a19020303c9000103544800404083c0d00450843c0280081c1c000203503140000d16600005507811000d4580e5490068091000059a04006007644070a800300080840340c9035090a420071044c5d6031040d074013030140c002080d0041e0758281c6040504112403c2000c0c003403c440c01c0458060140030b44075508a450005d014080311410b100900d030301d440130b556017518024442c500711400001990001100c5500804486801c1d005140199100d88150b00702e074209541a00c0d08004c0d1741041c2e83c242c0c04581065444820343c101420950854501507008004620950f5954041190204409010001c02244c10301c200c2d0382d20300340c034140100c5c02070854024584401140351101041e120458414080d400002603510400c010340f48141c600030b02074400618152600d103071880b003c20210342080000c10865190110a5080501030707070055a42020050952404d110011030107840c12a0365030050040c54602903105003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 461139973 1250 461138723 461138771
    0x105250609030e120718090b040605060a090e1c020a0c18060f0b03060f0604050a08010f0b01030912050903032104050d020f030403111309120305010f12080a170c04030b0a 75
    0x4c6040c690210300c1044001f00300c0b07404000c005034400300a010600c0b4403500130324056a82203e2580510360303240151021640380841e19400c1d5004030701c60311280203805149656900702401511000402d0f90344000030402a03401c22401c440b0741022a0960b5100341c4940b02c050304a5002c1d11440608001d0380700980e0100400c1c840c0f08110725180544e8580b2128182d500404003e480311140310f4580d403034a07020b400d041e5207903090b0900d446840586503101380200f801c4150802c00b04005844030b84e0048820794045080f0340d0700751008201108051038500c100d01c601c00700c4460303002c140381000d2900034103140b84681000219130010661104502c0e0101c02ca03401c980c0d02001203031484900501043c02a40c00303c8510200c21f03e0000941d080c803003403c5808034002045d650400a583c0c0341d4010540321a0103009410685501103015000140110300916030303034070b003800c00701d064a12034440352192000031a80302c60b590902040800810400542c245e40041c01e140d42031040c50f091184d052640740200d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 461141223 1250 461139973 461139989
    0x3120912060507022a180c1b1207062f0306060c07080a05150109110d0c020c2214130611040e04033504020105250609030e1207 56
    0x38001c21006802000590703004590400180c40744804040200c80d0800d40104150040c600c141c80881c8080e480806d4030312a4840704005410301044081d4030b5580c800841ca07690355842950340b98032100c143c60780900780362031140202145c1050b030307080400c003081c040503900306018003000012840c400b0307040c041e00da1003c0c0907152036482d1081002100c0c605459540103150324010b206238103042c41804602c0207656900103c01a6490b42da88946004607002d1881440c002941403101000310400c42c2c101480c80700061048800142c0d1010005501c410320409514240841e264030500620300c42c080c0c0c010a10b58504101d402e45442c14540400c000d13035070fa00600b415a0380104141d0408140b0030340303024090400d01101e1030b2a00d854050b102e9401400700e03010b1114406c162441c119138906400d87c030450100011461911a0750040d1a1600108148a054284e45485500076203507071041400460080c0e0021950b40068140035041584003007036107000340c0c4103001c010352860780058803400311103405c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 461142473 1250 461141223 461141231
    0x4081e090d030809101109010818100504020103020702030f0c010206130f0b091c1809060605070b0606190e1e0102150405191101120203011a1e07030503010312091206 73
    0x700c51010705017501018210384440c07406800340c0400541001030034503003c0c203072503845030794031121250000e0400801680802d0361011441e000d1994850b000160094810b04016040c030030264006410102510307070361a032903800300611412a681c1040002d42201c84005005050000b0b070721002000f4030300d020054580a081e901040c1e1a0004004224024820300005084001400d5008001a1903d010341140350341c4100c0c00706444406103d910b0886085440c4c02c2d1500b0300541d80c41c15054801004282c3c860028855885c0e00d0381240c00b9000251a00d566602002c1d2002c020001644000c00d00031504092982540d4041d0340c0018843d0020f0103000d41040d0f4966451074214070b00030009111400d55000c001e00d030810464403042c006040d02003626981195142da82c442c8080b40001d110314680d00090755400400119144010040040c180c858010040c000756a420001e502c070090840018078004010418020340301ea20000c81e0240c0d2420039252480e02c800b002601c00301030f0018168582d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 461143723 1250 461142473 461142481
    0x50d171f0b0f0915031b210403020a050c01171603090210030209121c1b21170903190908010213030c0b03161115010807060306050105030919030507060504081e090d0308 74
    0x6007981800b40d004503241f80c40c03821f00d02890003e4440c0340070001103c0a00c5090300c506c00d40e40c0038800b203410040d882d4460b044a5601c032a501d6060345513961500303051560751810300e030150711030001074490400d01c1d4034003580d05d00180c024003030415280d8010200d180c01401c5d40d103d448011001544803171406103020200c03128002c0411443e224005002003282914412491444003030700c19807220216a03031aa55007042d0120106c0c40050030031200760500340c004102c11646c000c0000414540c170661442c204403030355125842e680c2240c0c4110761030780c0001c0100c02c08101300610304038a82c1c0640810780921782103040110740c1c4040a20060190402c3c400c1d11510040041010804080e10f1751002e815506503503505d94640703071149804d0051038002030070908042460350242c000c680c0a801104005c0c6941400403c10a030740d050305c42801c03800c11000300556000306665005090155004142840d030765002c42003400031302c0f250036450410f082c4041c000d440c0c16695841603c02c4503601810144c0322035807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 461144973 1250 461143723 461143747
    0x30a0b131b080a0209180703080c1509031e0f0f0f1c09110a060e04020c03040f03061b0807120509030c031303050d171f0b0f0915031b 59
    0x107910411004034004408001039103000004038580540c1c000c1d2220075042c2c03148911154040b0f001d100c05480c0f94000030041002500d45001081010008800e5484042d025007010034104401c5c0c8441099a201080c9126461500f400208990000c0703200d0615100d03c80864805601519050314a00035020551700140c0840e00c080750341c4143d664804e4101014152322600c001c0000d0034003074940000c020f214100034101902080d0554081c0d850b2070320004180400c00c070182d4480345e400401d42c0014400000c0154102070040b000c5c5205540200d040301e9044203d00c9845105d481400401c010b050034004e80640195070744441a00a08003c0350982d14049240d02d144500d0310241111b100002e0701c041d84c00051102c00c000d0b00e1082094800051080c0411a000940d20f604c031081c00c0040c1d004a400da01c3c070f4802c91158020048402c138002595980c0c01c4138107800801c1c1d0210003060000f0600f01034a032081d11a0064150b0b02c2500c0d04500303040a44101888070103141031000c1e040040c402200c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 461146223 1250 461144973 461144993
    0x20d0e03030706050a020a0e030115031106040312051207021f020705010e07060c06050105090c030601200304030c090b031204090903020c19030b0c0304020d12050702121605030a0b13 80
    0xf0380001c2c0c03c2c8a42d050850f503810080d0300818410001840e251ba148400d0b107010b029081b01c0b15415584130100700c0c1591140056030035060f03a0241e000c6030400000001490402500980010a0f25a15103e481c1c3c4400b1002c000002000c0c2011504002c0310b82e20070303070020030b100c01455201040040c3c507200d5510300700e401440c484032120114072956000040c019403012038419402d10800080c40a41d0366401804000401580c4200f000f031001c0c40051041c0d4481c2001082c40f0407461030542120541240203030440c1e015130004d444c40c00300180d0a11503000180a03606041c14294018220102010000702c5a4002d5000341161103889032114400e240c0708102d60316040d88000d00004544581d65a00d10110318544000ca134420b42407c00180e0400300c040681e88255000742c00c0c1c44d009403069403a81115000c89210b141401014081400036072200901101e04407514001040500302c540d511501000c0e080d40303c40d10a0f40700150040000d00504c000c10b80010401c0884c100650540ca030485e461 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 461147473 1250 461146223 461146237
    0x1504020409140d0f08010807060c0f0606090c11060603210d060b1b03040b0418020d05090d020f030f0f0a093b01080a020f0127030b16020d0e0303 64
    0x31032441d4420402c001404034019020b942162515000009034440590f840c0748240328400d450b4001900400c100e9010310740c003807130640c0301d06c05003007007003165035a22804c42d8590742100c05120340c1d40a08088140c0c2020800c03104048600091803a0318112001942d0741e1515030b05a00c100350405c41c0319079881c0f100c006031040f111805005000003a00d48409152036000442400c4000701c1081300c00d00c0c002004012102681d0540c800d40c1c2c0707020300300340001b04d601e440c180810414030760800100310011040d110342d50003020504090300c00c4501c513207002458901340d41c10760251500b08200c100d1990049004440003408440d1f2040d8403214100800c3e10402c402f64440103490303d8443d50040e68045202010f440c1140c00c404180c032183c804400d039a501d03002409a643d07541d01840d031010251520344912800d400c014034000c4400e2021129503c003035000c1c60302d001ca001d0303a020400e008001c164480154071140d00ca0259110030403011000390341d0010b100700c49051041c0b034000b091040d1418000c07102c2c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 461148723 1250 461147473 461147483
    0xe0409030e1507032a170c070803071709010906140418091202010501080d180312050301090e0c06041e0308041509090c1e140711100f02070501051b01060f1a030403021504020409 78
    0x6196271380c8108a07140d41c0070703040880d50052425088020f00030000292805a08180c0d60a02601d007480402d550001e00540000c034448020b0000084aa00742d4828260040421002003007442252410003206102e0007404429641000c0061240da03400050300c14140d503044c64112500c0103486103a980d132408540018203620313201c90721800700c9600400154129030b818401089010211021261540444142c2c80d50201c020481008221190203101546a1580030b605103030960b0396a0780038040d1300944c803040800d240810b400e1075113900441c00d140100320f181402d002c0000441001032150200127500784c92000135030b0500003403500c500352500d51101000312040c2d50b03200070f0401224810b80d100c0407920442c100c990056810340710703181d44201242541c0041400d24140f400655558102e1410882018002c1c40c888007208024000c1100a00035034110903e0780f405c140032107150702c04458250000000801c240000a640002d440c204081032540f40c0007940c980d480014090170110b0000b501d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 461149973 1250 461148723 461148733
    0x3080c0d0e031902100b0901060c081b10140f0a09031e090302040b0315192306030c01180501050307050702100914040603030e0409030e1507032a170c 66
    0x10319500000e08110541549400b00d6000c2038281d0031080a490a0b10310650700070305001f004018407401203400700e80035481401c1290800c10402d40c4007141610742118026654440c1c08000701c5400284a1448404c4d001c0035000b0880c60028035401403040040d1122003407590703a02d44901031602c9107003080c40080c208003c401c40401c03080e20051850300d5074042a44160314000d000c000358907000076440811032418101c1070580d51800301122101c4c00c0020100c181503241c403c40196007680d40f84841400b0084412038040307050000c24146440e1156002078107020700e400c42c21400e0034510b182142141c0d024078000d81e49582d00c0038100e42c2c40c00303800e1000350811210140ca010454005244105560720000c00b000c00f24100e80822054601910010340400d01c0640c0d00400c4d0309140e000500c03018024245031424202c828081b8812642070600c43e1480800070030f80e18105503000c08026480d0700f011140e032600781d4401304030300e1319285160401007200c0400400c880c000c100300c0b001e80c1c002c141c00d078042c1c030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 461151079 1106 461149973 461149987
    0xc23031201210f032012130f06022e06080307050f03180405100b030405060106180b0306040f061703120a090b0f0703022712060403080c0d0e03 63
    0x10f0b045d11010100700c00121020824200d0900c0a00c000d580c2ea01d0b1b03a45104641c10b540c0b904404403400311600300f0405184c0c002003003684603840030304901c048640182c48444546028030708050356801c1110004000c10084040c00031540540300350786006c140c200009440341f1480c02e00d00401c1400c0e0b048943c69082039480203520100c60a00105400d444950001e800d4000f200c0441d4168030810040c440240d01c21408851464101190810740c1d0a000c058215400001c181c030b80166944c01c1712542103112500310100a11021b01d502044420440510392070b68401c40c11007000e003250b00302040c00840740d0301c10910250303007140f4140f4094031030132014200c0b1380300540039904040e000d001030716a070181e08144002400b00d4040030001c200c40b042c1404150b00a2405d8a00140c0001c01000003003604031132a154000031000e406d0b6030b1008503082c3e42c00200b80040905000740b01c085194 = true := by decide +kernel

theorem cover : BRFrame.Cov 460971223 461151079 := by
  have h0 := BRFrame.cov_init 460971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 460971223 ≤ n) (h2 : n < 461151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
