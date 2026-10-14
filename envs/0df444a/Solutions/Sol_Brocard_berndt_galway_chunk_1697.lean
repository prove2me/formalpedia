-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1697
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:20:42.750233+00:00
-- url     : https://prove2.me/submissions/5c996061-ea42-4480-8f5d-c1c97ac0df81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 305035971 ≤ n < 305215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 305037221 1250 305035971 305035987
    0x1104090f0501050f030f070612020d0f0606022e0504060b130510060c0305030f07020309031b090a05060d11030304090507180f050d080c010f11070b010801050f070f1103 74
    0x802058203003d8075010740141321a00703180e8180000c01601041c140c03c001c1004914201040f2010321048804200c407076004c011000c5102454000c0b80c090900c0004000f0b41c1c01e141c44c00180c5414405015061104080d1f07440d0100c101c0280400540440c0390103001c160b5a44c0c45c64044011311ba0144203660207a80704882c0c52074070545521580c4504008004070841c01e84620702510001600c440040004000b000066103000510f0b015941000203801141e00300051741001a0070001441d103070b900102000c1c1100a40c0d8a8440503160304401c4407042006a0b041c101c1c0890388400b08104090700001d015805002c058804000701d800401d0050300800c080e05002c00014507800f145160011200303c85000407900c4c1c102030481108449004000d80c252905507a908480c50b000881d51a0955680324000c1c908040e89020311886000c205075120782d02d00d074928061082c40c00c184c00c0107820b41e1409042002c01062260b800d900006503080c0000720000450086444080354142c540c12400003040c174030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 305038471 1250 305037221 305037251
    0x101208130f090f090209070c15020a02160b07030507080a050903010c05042c07120e0d180801020a020303060904020303070f05011b0c080306040903170106020a0b1612110409 76
    0x98241d40b800718080c0310808070084120240d400c42100698408690001300b00c9290007019a58249403007000e5400e4840307403050b02c400803600569140009600007071203820b4074038044803c11001d00002050303130382030104c04c0cac500134000d004240c8014500c500016038444494015400e0300c1007800010000d00c4590100c190041c00c903000b82c0b0807500c44501100c1c284d200707540e0017044a010505100c01c8014a83c0e50000c08079450140b022480c0c003904e58400005c404180c05010400d080c41e0542c170345440c0781400301042045480598040e82c601d034410300004a2982d40070040f03039080b51049031340001c81e4481e4000a41503110301c84000b05000703200c0c21014100034040d003040014403040d1980588440b0110350540301d0a0b581c0100070f100c640c04000050041ca055031249000e58044d203040440e080040d04034101c100000c4e00f060f03001d41e001c030f40c94404000341450385903400b80941c00c403580402c0000202402210341040741044203526842e00603503003810b0b04144c2d001843c0400e41800b010340001c6201c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 305039721 1250 305038471 305038499
    0x706051e0a02011406091303030f0905010e060906130b06010e012606011206050307051926101802040b190e01050a08060402150d1112091510120813 65
    0x30040403503102d00010610320f00021b942d4811412940c40c0c40741e810f810ba4007100100051181c248502381c0d990301c3c500201e9424441c1d0480100aa00107180c00c1c10030394139452402d000244000c02280101e46a000001c082c01d24440d0030400a08180032800351050050350040342c4040c0346e041340000241c8458102280210881c000d00c82a01c2d0420340e4100180d420007071b14035600401e0b406502c204410400390610348075036a024414014210710710303a20368903031742c100600f0040031600c4180d01044200d403002091100001641e07000c9000c20203440d0056026000c6060348030042c0c82940d03030b61041011f9490725051110344081c82d0b08004843c540710300c0d284182400a0149600504001d8404641d41e4070000d00c40c1c0c06150001d20040007030300002d62a0f0026400f441e424960142c480b00d0351601c0c2040f8201400c014102054618224a042c00d0b850b403510640d0340c00f12500d0b1f0180780900001c00c2c002030000c0140c550602000c140990b907810624500d02c2001003c04400905020004210a91030a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 305040971 1250 305039721 305039741
    0x1e170d020a090603180308040f05030f030a11030610080a1b0c0c050901052419110d020c0906010c2d1208100b0901020c030111030604110304050706051e0a0201 70
    0x103030b644541c1d15200c04070112400d0000c40c0c2c9107880000306100110340512400f80d07200e4450b1340901400f105503a00c240c25508100303003400c0c1640703022090180034001406030704030b90145807500314110700e0940300060b814001c4000c158280a8808082120102c0355040400c0340c1c615800c10400003021010020419200b080c02a43c40000b007500c046101c1c076150500b14102c0f00c008000f800d101041300c41103140f1a24070210302041780300810050709290008050320011480d42d40340c80b0300085000b000c103824401400486800c5401501c40c185d925941c0502c0c42e60892000c0c640701e01c05400e2880c00060140c0724aa4180c54051003174000e4100c001c1a80d0f1030710509204983c10050b140c6480c0040c2c0384400c1c142c4105201c0544140300f8400c1245d90360103818042e00503c100c40414a0030004282115000e260041800c0000020480b09040501410041c491000e03207035031852400c1e07213030151a00800c2c056042007110015144410030501690765503003081c9100c079203555496040b00a402000a201 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 305042221 1250 305040971 305040977
    0x12020a0b0f100515030105060a09170618010c020604110f030f030702040c020303010b040306020a2601080d020d140d0905070e0702060a0c0c020111120d0203150306041e170d020a 78
    0x8011401e403c04d50800070b80446000702150860742480200000754201005001c208a0240300008c1c00300d0001058800c1c42c008417001e4240c60030020f0039074800800c494a550b03081e80c100043c1f031004c590f0001e0450380c801c0d042544e00c004002c50b9000161113a51a2010b070b5418880d01c07a0b60035820501000503e00e16100311020080b444485400b661a400301b40b0440901d08020300c420808518550000d03c3c02d0301d582c2c6004110a03c08014a0030312444405514061140721401409080c008001c2c6000410346030000f030248245040c402850b1110700b9070340c9000d2440c086601b000850f015000182100d40c00b006941070325442c0d9074040c0d58004101d94800040c03003128081a0390300a54407030312850b44003542e02c8002190113034006480c9140113840041c0c0e80d2080249407002e0b04a00c0b400381116014240015a40b42490310b400c0c10105501c04541c2d110380c000d102800001581144440d006080c50402080c01d0202c50406450306c0c00c0c0b0807a105401140055020b050341c4065004000300e0074540c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 305043471 1250 305042221 305042251
    0x10606021b0901050d081606061202030705040b061602031c050d18031e0207081905010b030d0504172d010e0a02010918022203120e030a12020a0b0f 65
    0x20402c064441d0030702c201a000070380c2c0d05400000c00c2e4500020555030221040d00c822482860b030312203046030150340c07002007918010400b000840c43c003031045600800d0102c2e02401104804400522544201402840f410030084a81021900c06000300403800b0b050300c5001c07259002e0607401601a41c804c182018040f454080f841d41d102450001001d000354156641007481c40c112488540c0724400c00c0c0a01c802c5d841607000000e401002085844541d4415000104041c882490058290b5105000c0c040c070a0304007942c040301003a84541903c0c1103c4000f010020701c052200401400d2004d412041ea144110805444441004251050b411842940020841154464502d07502c901c603c68000380060b10508041100c2030000c0c503200c9840e00ca41000500c0c042c0d94800000c0c40403140c070350b4640c00b000c40300e108105020030300058804070078090809d8030300e0340d80410002c4d03140d2031401d1000702950210001043c1462003001490140f50340449604054140f403800200e143d10100ca0100803d5080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 305044721 1250 305043471 305043523
    0x20706022a0703080a030b19090f0b030307122102040f060c0b04080a0201180f060e030a05161a0906010504050a020a120e03070c031a0a0e0a0f020f0301060602 70
    0x400791007212000c8060241142950788900c80c0743c0c000d40c00f500405403141c4990141d543c0304014100040395070521101070905d0029a0300555004044d61171b480c03458031950031a0380e02c0c007200f10340d86180e0248409a241910340b41c00d54001800c04021860749010700181c00b4030f612298014400d858900e00048185595100c0071650301c100c0420044c102150301c070206001030500001341030712029034000480d86400d283c01d400f207010050201035032811032070a4008180310652050290140344c80c005140f6001005201805922510b4082c3e451030f102c218100c01030044008036070010001d501900300a41c142250383c0c41e42c4190a02a841c800d924010200c2c104030205d1080384c5114003561038a05860112442c018001d00312130400041e1400f081241c00006090520310a01a42c4900070346882e0b948041c100710101e000080481c41c0542c034056102031001d90005104100a50040c1c0718214002c00d4030200764041d0b282501143c04d0760070b0140100d909900885c4030020407103011104070550240d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 305045971 1250 305044721 305044777
    0x2060403200d180b07061401060305010b040e0a02120a0c110c150d0f091202010b010503010303050d0b0103090c080703021311030c030c0705060117061303120e010f02070602 76
    0x50540950707039001c4940c40150b6030190003000080159411101c070034658800e01120b43e580315217411076142c0ea13100c14074414401c5000500d40900805d16041150b5810480142601c3c82240101e0510b80783c02c400140300305580350100c0745100d04541122045081492502000d0020300c862140400c6880c0502c440c5030900007084613120900070310548815100488a036100e501005c00a40d81c5511441c018040040c03600408015600c40d08040501b0b1040f0100282102c0004010380d040060410040010960240580d0341c0008545000a404804a001600206800c0d078008001e01004100000c05202c041070b10000c4a000ba90614150700d54015140b08450101d44610a981c0040c070201e2040c800c44000fa551101c28501d00764901400ea0719400e180400991000c00ba80b0703541c3c2c80c00e00c1007040500c03909400219152000c440c0c2e5490b1394015244240340000340c00345555075080c150f000b40003500400b2000381e4640c411503842007030781001e08c080c0d0301c0881d41c0501031070142261540f5840d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 305047221 1250 305045971 305046017
    0x1603050c010f05060f0d06060905040c0518041101030506010201090c0305060106170618060310060e0615070c06110c04111e0c030f0f0d0203130605060a030f080c12040602060403 78
    0x4002884844030070304080070040410003151090321100e5236100c02003448885480b031640110700440d84024070a140c00c04000b000c60305182003210004104c028403001810045840140039001d090114503a511400103e0040c0b04080c4040c1004203044400018420085901e074141d0b10560b03034030f2101011400b80e4980f00d4105983d0103800c03c038071a51044d01c0c803069139040d0790000c100505a624040308080c0250960708543c00620007640008240703d018500452401340610310144040e00781800b40d11800d5403251144218010710131540240c115594050180c2c404052000340304000c0c100f9040480c00083e0400384061070683d14081460710201c41c41c005840400c29860019850001d58511440303c58000b400c0240110300c05108207e120741c00360000d107100345010601381f49140e00c07030306000c41650009800b840c0038049101e000d00100e0000b00300e103091141c00088040d0f59095109805241030a8080c1e055890480820081a203a5002c80c000380500d00956a201d150103000e054845054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 305048471 1250 305047221 305047231
    0x40b040c0503011a0d030314090c09150616051f0f0501050109080a20040e060603012403061e0204170f0114010e0a11041503060b030601020a080304081603050c010f05 73
    0x35850584c400c2c41e518100c010070020324407a140101d600200d400c3d8014030080c056450503001e42180c0c81c501c4690810001480e400360540c1507082455070304002184041c0301d13803c86203508000c45c40441e01404404c010780702041c80005840c51400a036040d02400030300d110483ca0190500f820f000040942c070419410701907a2200c005005013010a5131400501c0c3e2a0003039500c481d009800380760306142d81314400c0c10301940d00c07035000e8403403803400408041c00c4842d006510b0040c0c0d101c0d0101c8a0071054010500350541303030301480014100800301d8001401c010f860840c0724000713000003070124036410b129900c05105900c5101b10f848544104441c9426212251403054980c240c14004200e0460900c2e41260418044c0a0000f41c0307a50208005c49290b01a03000304031030000c1c0300c0402071001e03414442e24004040002115085040c1440003d49a0380800c00151202d0b002001080c1480348080448040083c1203030b88101d040ca01c1d14000e0274070f82180308025100d500e8146202c141d20000d004031403040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 305049721 1250 305048471 305048501
    0x50109020408060f070207030b0c0322030207050f041401032448020c010207090902031209130504060903030b1806091806150f0105040e010b0d14040b040c050301 71
    0xa5603465140d01c0c100a00800c0201180721300880000402c00c1c00270f24078040c84444002503640d00c4c01000b442903401d10498006840040c0d03c801101003a4080741c60f00036500101e81c4480345413200d00000e00944000400c0031400c50081000004004080f030141140c0d204060380c1107002e00b0761504500c100c410401d000791050180300324550700d0543c1c805c04450500d49a40c42e00507043e6076540f0010201c680c015040c1d000d80d0200b05401060b68040005000900c8000c07424400a59103a001c241c503a20b0b46820700b460760720046060702c103558400000521176400a5401c100d5850b107810f14078090b0a8012044e00803a02d001c005020700e0404c00d14140c07c0900c02c0b14001030340d45547c010701c880741400514000d00c41000c18041d07045000e0610840f8007484041d803c3c2640e0b824500100000700700c28041ca00d05010b8208000c0154405805440d0b0442d5010101e154443c6041030f00c410140c09001c84401074020244100003c01000c0c440d45401a402070040428007512441414200c9050395190a40f03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 305050971 1250 305049721 305049733
    0xd05030f04060c0504121227260d0207060305060d020d020d170714070b041d0702030d020a0c140d020307061e14090f010b06090103090f0222050109020408 68
    0x419100c3c0c1003030a001071907140c643d00d800d90300c3d22500182050910f040b108140011114140e0039070050549551321610101d030b880414059064129120040c824a041f80740001446200302c0072100300c50001400d51020b036940c04084420094407000140282804203240001141c15801c00c00031078080c5231b81c0a800048001c0b001d03000c002b40d4091624040701ca1621500a0f83c000040d0100980300e101c0c4504140014040005da100d41441025017003000c091802784020000d52031b041b41c03803680b02d0713448440c00003654584000c00c0f170441c82036040c8410074500016145800d140c0c030501c2c0c2c141c040d003e950065070000100f12600d032104540502200162310501800020640681c00349248104000c040c2c030360000e0303801541040c0d524804166010240140821803110000d100314101510408000c0050303c5000c2c000030080d00640d0b400d40e0406685480710404c00800c0b14ce07400c45550010a440301d044035080350520000b10444800241c1810300c400040c0da081c480c001d0750280e80140c0d01a0031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 305052221 1250 305050971 305050973
    0x201140411010c05070515040503060604110714030919090c0c02010504150c06052a2b020c12031b0c0304030308040203100911010e03061015020f030d0605030d05030f04 74
    0x40090300c01400361114000c811780042d0325502c002c030004085256001494072185424100750500d40e0003449240034a041c040c50080800e0708508a605482c2d102c07502030140700840014a156000d1046007a80141d080714501c01102c00c2d9104a0044540f0003400b070240e5564020211190b101d00c81000740852000d00c0148040010302d044001461494a003005410315a6119401500c0c825100c400f28681c1618182c18040440035990306c40400128005280403598402e1b24048585a15071401881c101404a20541c0d0260111104840c000045620585c4080900d5032203600544038040881b041c2c3c41040d07540c004c00001e4581c8150351300040d60510745983c90588191000800407a494010780d00e290840f65554407900702c4141c00340b203450382c0401017600090304e403581d980c941d28404c0e4000810410b241d44148524019109410440310101c1c441c02026881e02130503401184c09070102051140f989506644144d080b00e90880031a0450b100c440d83c152050b20040d1000c40030000601c000034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 305053471 1250 305052221 305052227
    0xb15090c0c070b030c1e19050f040509061c06060501090611060a0f0e0f0307021c05030d0b031009260301060203030705180901030615060305090a1506050307080d020114041101 77
    0x594042031015134540b520303a00c100c01c50498a0508a2046041008143c291079082c07e40884081d1803070504003075180c00d101c0c0580f00c1c42400380388076440c820141d9100091154590420503000d01500c00c109544c419858a0807401601c454050340c0d00049019000268491140300c8005e04440d80b1000380074240c80d03440c5400003410840491150301503c5048401421f6030400450541e1100e15002e182c4079111441007040c0c1003180c1081450000342100b060b00881c8022040319006141a00005803084803000400e00708020b1000251a0500d0680900c0c00d010a6002e00046803603003004800380750814600100c25400b080c01140b0050f8414000905401d000e00010560504c103a80e0b1240981c604000107505100c0980003200e00a031642c256440b84c40c1d2200c011000343c1040c1c201803041c2d207054022159164030204000d40126001001c5040a59040d800303031000e00f9016051b60542c2c1e07200d200d2550313981d2050708020300561800c404505d00c1802143c100340174950104046401c042458011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 305054721 1250 305053471 305053477
    0x14011a061b070f060f090605090a150309020a0f0302030f031603050f0d02031302031911130209040509010b03070e040f061139150c0c0304030b15090c0c070b 69
    0x6415403203600400319401c2c0600c00c03044001e00f03039075603030170039459422100500b001c485a001405206060000d01e500c0d03555240c1c918240d40c803039071410407aa00804000c90141060a8001e03401000102d00803d003a000c4245801c1070301d0003913003142c218031004503840e0768030700c10b043d5508a24100d0412000002c0c0c8100001c000c0c100214182c4c41c2882c0d02c41d01071744101d0348142c411410001e000c040c801c045007401d004070030b00100044108003c1440c141c4074415104103448805110300c14124600340a12a154145d440181c0d028004000350b2400201c3d4038000d00a1044584c030921070b0072000034140f01013001792403080d075000e180c510950143d0356409000e0204210942220907040c00038030000340c104040005442c00801d40442415a0202c0020540c06a640f211945030060320003009907000701000d85800c5207078000c40d242e540c014000028114011501300a00307020880c01800b9210080c5c0211005e455421181c13800b058940c6080070170141700351004c80340d0b180c0145c0c0c800c00c140503012000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 305055971 1250 305054721 305054767
    0x207170a0821010801150503010221070201150e04020108090304080d03090303090209040507030320070b07020a03021503310605090718020705010b040204030503040b070201020a060914011a06 84
    0x20340b640c1802c0407649480040c200340c000c0300c1c0607951040c0d030700703003500015040c030f0010507040d0000c6280410f400c0d10525910f0759204000e0360080c4500124002c94403d60040c4054490f65807034010aa898480703483e00f4036020341d0182c2c001030341c0384d0124030503180100c2207500312401e03903000709000d030b149840980251080e044140e00b45582d507014000542c540c01d084c54411842500a44512429441c0242008403d4140d030f10243e03103441c00000394580d001944905640b020680152100014800070340c0000568100079000107010951444002464000d5030088d0710441c82d4914030390700040d00c2d420305205490f00c0c80540d03580782c0d45040415080c0d030109411020501c155802a0744407250480c0d80409001e035000d4150f0b000071010300303000080c420f2000c6107104a0b402c2d490130b49180c031010b641340568065010010300004205045a00800100702c803030354005411701801c511428100e00060010204005650071f040741c0c040b0003a00400f68040b1281c00901050500d40d500c4e0401031104c2007412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 305057221 1250 305055971 305055997
    0x23010512040605040311010605180c13150f02120301050909010905030a021b090f07050a020f0a080409050708010302131a040203090303060a0e0702030a05030601180e06010207170a08 80
    0x3110140390541a00039100350300071400840c46040c5482d0007843c1400e04c10502e680f0b0b9160000901555640d038000d5a01c1c00316801d0b4040c2c6548031092549030b14410103807074100c91203125400040390030140b00224070a540c0342d11030400c20b1181480036602d0b000c5048903040c2c07c0f1410001845103140c1003040c15044240d0600004a0200c90340d24503182da403210843c103002d42d12040510b046e4a0041c60911035140301511005010700703000c4500e400c200d1002d01005c007404004640d0100c05403082000c41c04c071440702000c90700010700c13a0038048038a0f480b6004440c009810f02d000100014060030328a070499078044c180c81c000c0c20b9000c01050040034041c1011148181342c052100081d61240059801b90690b14041c5680303041000410204070800c0c0d0144400440341410855a59004400c0d030303070f80c00b040d418503076584d84c0c40c0390040b40e140101455103000d102e44800c02045803402d0700d200314407600d07007a000c413600c0c00c0d2500e11090007041014079034010ba5000700901c4001404030300c06804230100c2c1d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 305058471 1250 305057221 305057227
    0x30e06070c051f0f11040e0411060c060717011401090504110903250509130201031a03101407020c030a0f060b060d0b04051b030f190c03051f230105 65
    0x41c04907045080d00381d0b81e20b9403e44801d04e50384a004030384520444d200c8070a2580e80b40914124030200001002440504802c0c001c0c030540489850b03000c00c940d011591603040d05d51034509004083c101d10f80c100304841806500c2e400100f8003d107110302c0320341811016110700101e0351404c01088040e0a8101c0360600b0410301340300e2200c80d500d0801c01070f4940c0b011040d640700304a00c0020300e511448816400b29201d0b510520a008100308080c1481e006980c0a01e000f290100e040d4515800500500003541c0e054860000403510650081e4801c4410406801c2d0a94040e26860300480c5e0b16000607401c1c1ea8075400c032002c4080001d10111000200754851000410010716010025009030840307000358110f161540c1e0032110038035103885034903817206081c010600d40d8180708a5401c05400020f081d0555052100041400002d00101420511103000e8050101e001640c0008000d48000d950f81e45000b41a19403041c018004062003c0594041055034448845640102c8410036406115607041c41030070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 305059721 1250 305058471 305058493
    0x522120219231207060804060b040b0d051020042c09030403110102190b09010b130c1d01230706110703020c01111f24080607030e06070c05 61
    0x41d50300c481c000701d4042d20822140000010302c05407006008a10501d034006800610000340c205020f50341203600588006421484440440c0050002c0f08919500071402c25441040150001c1c0c0b5140c2c004110714140700036440f19055484404001103040078501081c0001d110601e0101300542c0c2030f05003112262130703804404d00b501c0c0400f9400d6841881b59000010180244088401a41e82c403c6081c40100305600084910309001040781600034002440000801d24000d800d4124604843c80180f24015200083c240340d40200314071101040402d000c1404e441034909040c1707030b00c40c5e0090b0603196241d25107400b00b03402d407032044040307100f007a980424131400c00401e03050701c03c0b092280180104596200d10508020749400c0c1054003103810002c80c92115260380c500451080009240d43c05000c400c5d040b0a0a4000a07000303111000ca010810304289000342060700c00c401045410f100141c2d50f558036001e1080b429105141031005107a801000410300700340c40b800c035620016024030162054442c278 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 305060971 1250 305059721 305059739
    0xa03060606020f070b160f02060702040f0605040b0102070b030f09070f030f140102071505070207031e030905101b1502070302060105040b06040806040b0c12070522120219 75
    0x542004005911004207401030110400c503a1005e005401d803514101050302c0d5086801086074a001040c0c080344008807411510b0b140240e0b286603600800901c03003030b448002100003c1041d4824a0721031420148086469400421b0190550710060080d07480d40d51800550075181802800003840f600c241f0500180c81d104100d1a48041c610071600d510103d1000d0070200c8981c500d100340c2000350f9104004010008034140300084450741600300101d0340c2da44041c4282c0c2820134690001d031502e8004164000c030703500c200014a42c40e0340304e51a20116640c4500500420050101c0b1110110b45c08940642802001d8403030010114400c10102100910a044080070781c0c100540883c056884a40107000b1450240554111075400342d4240341014034103403540d950360700042d00c080d04127004640032039100c2811600702c81e84405082400202c9003441a001000c0b80d016490111044941a0360b5040c01600352080104071003c603841c0c1704105031643c0800c4201500e99403910000c40c0310490014581034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 305062221 1250 305060971 305060981
    0x20a05060a0305040b0f190c0210061d09120f070c15030903021203090d0806040204050d0c18111c0b0901060f020c090103121b02150711030601030309060e0a0306 71
    0x5401c2c1d0b00400d29080c28503004603580000381c04104021807150810528551000130f0345c0141a650b0004180c0313049404c0241e00f0041c490a225602c141040004640f015890008043d0742290f0000b0000c950f49500d007894603505e1914041c002401f081000c201e603040207602405c4124010080d858240e50307a00c02c00405c803a110200c18004c240c5854601d001d00d07030140103207841c030140c010f40709280d45816007041351222400d0040300c0a119021004c0786541e16190705440241a020341038260303036910740c00c088e810480300788241054884004c51505154030f5900070089000c11324010b05041000c2c094058001d5075120102500d500e503a0580e07404256100e1f01e0341402000d55450f000300d14558034500038240000d000101c2c1c0500500401000020390300455092800324a1038020f111440d406045503d001610601a61261300702ca01d000b040c00c0150010144980f0a210340142203070350005041e00c9500c2484090301040c401e140401645008a60103a02800e0041001f4070f82501c030754036807003120 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 305063471 1250 305062221 305062237
    0x3060109050117070b0906070c03020a0e16020106080c0d03031811030705011403360c040501061d09070306180b0111030403110609040603230c0105160b04020a0506 72
    0x9038940004200402d6820f00700c450881040c0040e106007030074002030701054030506000314041e5500050460901102070355003809164000c102d40501c507544c01c41440c49030000d65400313280f180c000c560030b80e003503005100b2902141c540d00094540c0085080800462007840b0100b5010f0584440e0300c01291002440f400c54010700c10444a0f61842c840428589042060340007903051003461944240c1e02c100c1141500c0e403041403c141540d54010020f14001401301d00c040484002200b503607881c005000c0031510008115059508100d142c0e070350034040b6902881c904010b442260000b5240501f401c019461580c80f0056060204149035214005080030010359030542c0c84540d0f444002c1c405681c0214940c0701d0034003000095051504503200c410140018002d218400c8400062074109601c554100000554018408031503505807542e45d4a9010981d42c07241c1094003c1c02002c16103036014205072408651920320700340c00d0f124540e6402c901104068002d9038800b200c034400003429500e8400600c0d0b91 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 305064721 1250 305063471 305063489
    0x12130c1a0c160e01090902220207051c030b06121b27030607210515090103031e110d050306060c030301080a0b0109060515090a150924050301060f0905030601 69
    0x2d14010418003803140c1a0000c481c011b0501d00282c0160b034515608503840401e80b0344848000d241806480c1c000d00c40c0071402041805100030051500640c8800b242c48002a41c42c103003c940a107030204150b51007501200c1d01d043c40440701144036540c1400000c8501c0c2e54a000d00c500d491280e00ca0700e115130261410805c1030000002c0b80b607805040c00d0103600e40050003401d0010554083d80390302449055030311b81c8600043e6403200080c1244650b03035561400410060083c281a503182d040c0104101d40c1e00329034007800f41182c12070030719141c49840c00b8008141000040c11405604c61070481c3c0d1540050440d5500880c01c0c030030b03144882e80900086000303117400d100610f9485600c2ca8804c0e04c8101c140d20000c9010301d044402c0086480d50048540c00600f050321065486d111580011001c0e0b0b52500400c02200040000c14400e68001c08400d05481001d03100402c5920491440c2d556841c0f11082c92000500078070040204500640e030520048005081a8003400c1d100c002180c6021801d078044525 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 305065971 1250 305064721 305064763
    0x80a111009170c07051302041e06030e06150f06040e01080705010f05040503030a0e1215190911060906071b26120f120103050312130c1a0c 61
    0x2000340d004007103410118611800c604001c3ea5550042c0c4401301807007021300902d41c0076000ca110102d00c0d4125005449502915421a05041214a182403132400b400000c42d142803610400c401d00000c0d0184101c0c01c448150b0703060722130300e400d02201d200035082668101c0c500f4040424400d4204031030078041c0c01000c0003804403a01d440001025158074030025001c1c020f040005000c1c0361400f0084480707a08a030b091000d5140a03000103d5002d61100e0130781101030203105080300d01400b250800500803100240070b4901c0d0100f40031803404a400315600142070f8404c601280300c0364141b00b4060104a000280401d090100a0701c0e04151401c1000106807001c0d5102002c1c4800e800b030138800c84031040140f0f1000700000304544070316030700d1800185008121101169918100040c0ba007140e1000030007240c11011560b603490619681d8005031840360700007800e00d00107a0b10a0b4034400513000301d50046014079020b450301507040d081402628036955080c10410003040c2c1c1c20300070442400810120f80b04080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 305067221 1250 305065971 305065973
    0xa0302120f070f08070605031b0d0606030f060b03130f0b1e0a020315040f020c0a03030b0a081f05090c04110a02060a110d020c07052205010f0b07080a111009 69
    0x8104003142d0000c0c3c610039031181d001e01800400180341030903076105007410307035807616080c0c0503420118440003022001d101c005040b031440000c40d08083c003143e10544040c85005001103103401078030110b014041c4040ca06100262000003010201444507010b15080540c1c5000c0b51100800c102d0200d0740003810303000d100350760310100aa44000c82e6020704042030131402e604019120003d46600001000e00c1141c87e00b070b512018540c154112000010100e0031a403040c0c00d14034000d0040d182d410b401c00d00c00c0c10140f100042c18100812011800901c0006000000009161a000401001e0003002192040c80303068071041d260752060302a01007092001948441c0041030007458003070001d0090000e40e00301104510070203040c034295510410054809615028a601c1c2c281c50318070203a0100360700c104c1401d40607111070102d4040d0044024090801d20482c3e032241e0000300c03591b2140c0300d02808070710308004500105240302c2c05850405010701d4400c1104040c05503480c5480d0803642002c171240e0b55803841030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 305068471 1250 305067221 305067223
    0x1050f0405060403050601152f0c0a06030609201207030b0a030809040506010201061401110f070b03040210020111040614071406191b050310080a0302010c080601080f060f0a0302120f 80
    0x1c00104d15000000060f100030003200d0b00286a81e65008188090034040b4100703003030104ac080f501e8040c0041d43c1c025074032040100540500c0c4240c510592800d4030101d07403007802d280b03c40c0c5143c0c05581c8041c60010801128590000300030315110805503a03500300140341e03640c40d058100035802812081d48401808040108136400680020305580c0341c500100031000514640c114100c2c002d080c403c40441101e401c0c40c3c20407404010440c00ca014440f0085030050700400034501442c020385401c10503415200080e03080783d4203241031113000f96040c4070030070201e407040220040011418015504020321996075840080c04031150f100d281d00f01204020240c0400c0010400c80c1c42c01500900880d43c0c880041403c0e0500b04e110703041041720000015402d400d544441500400c1c5203004c0b01e41c0009107080082c001c0c5020b6507548001b60500f0080b40350342d845803103214014028941c1302121522220100000b040d15250842e0700016003240010141c2c1d03901a410003100707040009040e02d408064501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 305069721 1250 305068471 305068499
    0x516060906050f0a1404121824140301120807050105040605071103040308030411030312040302150114100309050c0d060b0f040c051204110d03050a0e0a05030c01050f0405060403050601 81
    0x3200d1651400c800340403c0581c4404886d0043d170840003181d41c050350b40004070360031035000c0603102c80c4031092130000540311010889003040c02c00e00b01c1c883c04038050041d000c88212002100340d40220034140300620048542c9600311000c14821000c40346484080e9551509403102101c007610b01ca82c0c0d030001c1020f2503801599a00c1e0000c5414095490a82140d80c0c229403800003400240500c1880d02241c0001e4400304111401c0151001c11108645040c2c0b5000303544850711038580d01006403140c0001780000c4201034480701c64900a0a80cc500704240508600404810405461901c00d5200c00c2c078064545e8800074056600a0034041500300d054800d0010350092030b00020f018034030b810340d4a90b006500078142c8105498541c0c80d011680c59605241c0c548110305d00c00c5640c81079401c0844010035420a0041c04484081d8807400c1c5101c0c2c0b10010000b00190354070501c0e41541084101c1042903200300010702510412003d5103080944400c00310b201c5400030340046415521500c0148441d000150f60 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 305070971 1250 305069721 305069731
    0xd0f080a020607410301171903140702031f0f060803030108060c03130506070509040c0801060203030c0703090801060305030a0908010b011e02010f050907050406060203030c0304030516060906050f 86
    0x40901d110a9200560848041d40510303002c50391246890000c04186101c4044c03007000803040d109850b561194000103004880c907503071007928400c5841d012403840301c41100c4840311707425403a001d100c0107901050100c030358080101241d15000700303110035901c008181c07242d9a13051080c1200203402540440c084c8101c034402c0c0c01985140d4424001000410000941d59601140d070104c00e540707a03100e451b140c00309609503c000900034040c5a0400481640c4803001c0c1220785000c88062040305005041611001c4081c01a20010b030820800078201507007100040043ca48649490381c6d0050b0748840960071030762075410031104c80e000002d082e40c42e5944207520340003030203e150080108040c00000030304018035034a01d445410300c08220f0303000c12038000e40c41002c20300c150300d074140810720b0056202d503121122402a0380c410f5150001c049a501c1c400002d89100c2c0c2c02c480240c52031600d841d28159061b4200f2441c1401042c80050720500040300c074020041c0d410f11418000c922410035500385040c5180c0180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 305072221 1250 305070971 305070977
    0x1401090605030d03050420060d050c070204061e03020603090f011103090114070915050d0c030608010e010207230a1b060314070507351b030c0a110d0f080a020607 71
    0x1c140b1021a50b141584a5440305261101d06501f440e58041140d0f40144440c840003540b070003041060343e000002c0200090ba200315000c0041e180c852010208417042c00d094880c690045410074001400c160740115003001e40e040c11950082c0300c118500d130a46030360199401d02824088240107850342d0034024003040c9899540c00311440d140071000140459010310031f2820704030308603c81d0541240600c0407912401038040e01032000c912410800b601400daa8840c410540d071802c20951303040030f0180b0950f50300d00c2d802107100d4501420014149020110450503000700d01a10040c40001202012045080c0c00c51484c03002810b86843e0014084420070105a80350062000411200b10750203011510410383c400c13004140240504491034407015140e845210440d01c50340240c02411500c0041c002c043c0304441003d005902d03e0034419100c1c0164503a89205a112030124400540040e9a038128100040c05610070a2910b4643e0070a00e44140400d40d85a800000d9070f14003117a041c00f5856001009003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 305073471 1250 305072221 305072231
    0xf0c03031d0f0f01060503120306180a021308030a09050d151415030c01051c0b090a090c05030703020f100c0204050a0209041b02030417030705030c060907061d0f0102011401090605030d03 82
    0x1000c80d2300e03101845541800d03028000f002800c1c0740d0b12440440e029542c071204203200c914201c4040d000a6110018000e40031421402c0054105400822540b0415640d55142c0300189031609206003045c0744202190418010710381000100c0c2e003407045002c2d07102001c20900150601c0d0040b100060341100e415406038106044c0b004886c0d80250403202041c0d858941c2041c0042503644000040c1001e0740d1065000c1c1c101000d1101d0225241c010f10951409001c4406159030b940302050340e648a60700c0000d400802012031640d2a2030301c46550f03000e0860f0313418840c98000541d800201103c3c2c0885801660b658040b4600003603080c01d1041d014014070b4015950040702d41000041c2d40c03406984200b1507440306520200c6050801807040e40c0c440c642c404101c1e6150300700074840f0381d1030303c0080301c2c94852403041c04d10000383c0511500c0e074101140841051441032003c4a014040c0b603040c44445e01d419992100a8209061003004074280203044502001400b60f042c00d00301810540f08480c814100750802d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 305074721 1250 305073471 305073479
    0x270212030909161101060311030d021504140f01050c12070309051005072001060603050c072f13050415150509060a0308030a0507021c0f0c03031d0f0f0106 68
    0x41008190016040310700341100f42081e040803550413002030528032555082c4a4000b080261001e420040044203c003030380d1050b120140101d03036480006c10407440c0d200194000c10080740c02034816900740440301050b2a900c4183c0450f56080d100e05488203c000c4c0d8000483e6407204101040c0349401c000c55180030f2040d84015182e02c1da4070303910300030026551513907a000300b00c0395805032014010350000c040308902030703040c140e00c014000d1480c1c1c031038000401c2c1041e00041e03009070305400b100c2c03000f03600031240911020004001c034845110441141034000412089074001d0307032210400340d003020110340045000d2910f450160190740c240b90600c3c8089007088610f82c5003d00440c241c00581d402a00d8000e070076520040010b101c2445640050022140002403280c1c2c801503070003651041001d90215a0418003000011010340980303031003039001510250003800316520810041d01814000c1c92f01040504c580c0c603040c9070740b030310303000c240e1500d94001c414440000009005594440320b121008101e40c505d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 305075971 1250 305074721 305074729
    0x10f0311120901020c0a11190f06231b0c101209061805030301030c1202090c030a0608030c010c270b072a06120501080c060c012702120309 61
    0xd00350280305140d90340c0001500702d110035419242a5084401191683d00403420070642c6d980460130503601820750007084400307240c0c2c512480c5040b00d60113a9014485031400600f02d45490591400d640c4110340020181003109100c00034195014000210b5648106003514440c600031588000d81e000e143c018100100b1650004040d8148200411010410680034039011005103440011001d428110100130000d110002000c2c1d0b040e02d01c9580500035441d11403810b2007402d0b400da44000d50102015000035035440040c405035401204401c030228189442e0328481c1e0440e00080f0b000102a9960290350060b607030300c1008440d042c40c0d107100720a00011010080450020a40160210a04006036901c10000007071007068901c066034510410310500d1214404204145210f80000505000f288101209851017610f040303921410090105c07074400b00a1001a0f00001030440c03941d580c88480980c0c00042c0c4845c80104105030501254007003107441005184440ca0f1a04200c07907000b8001401e00e511 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 305077221 1250 305075971 305075977
    0x806060d0e0a050706090e010b040b0307120b120d0306060e060409090510020f03010f08030315010810080f0f0d0c052d030d09050606030114040b0a150602060105010f0311 75
    0x25014030080303500c100100603185032590481000300248200f04000450340c0d400048401038602500301d40205076a41c4580c84000d00a81c02144980041003011031091800b810034100401841d007400300d020043d00001401407910803404101c0c03500240a940100c0e64144a034a01801241c202103248201c00c0c00071070301c0c0d4001c0d0b0080b44a125a200c425005014042001c007828040c40c440940d074405811441540c40d400c2886040c0d0307c0d043c2e61a001c6200400802680e00c20041c410481350080d04010046030001400743c605690a8515140400e000f8014001d0820032050301c40140300000e442800340340b40241e040400b00c10400f039145010006a8003207454603102e0300e409a454102908150075038203800c0006404d15282c0320015401107000001c0d00a02d400d903010b03009580080c0e03135500c281400e03120220700e9101c1a2400000180001d20344000040c0c00028980e400200f00c40d4400031a40c0c0c40c542500701c040944c1c0850010040c543c1e0107074102e800094940303011b10151a02c00800807144c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 305078471 1250 305077221 305077237
    0xe01020c0a0317130509010611010510050105030406050709150c0c0e04032118060e010507081b070f05010c11060c1908070c020301022704090201020312040804150509010f080606 78
    0x8440041c103505a0328051807460050003004006c00c60325655460702070b1021141000f030b05025400c02000984000310a5440c5c02201e6040c0c440501e0b66071a96644401880c00404100038485a0305000c01d4090800340400516003075a00ca400191121307082c1a001101113501441c0702c03980c03800800001aa0060300d40498501140040103c0d10000d031444d800b4107241d02000b090850780551003024056503802003810000e04100070400c6807150389003140e507924102d850030802c005d0300724001207544000d0014a004c6008400c0c81200307803101d0f55202d00b910050420100000c0300040e41e0141900c017030100340d0300020010798492030108180a8244032076401c02030391040c042180005004c49010b81c03c0b84250710b90047c000c6580704441c0c6812a1120002ca0542c41c1d11700c074800c40c030300c41e034207181c4541a81142c050700110b041001d01d19101e40c1c080c0000f04211841c000902000488111001c0d06020160050700c8060300c82d14403000040211401780d10f41c00c20800140c082c000c86803181780c201c071196 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 305079721 1250 305078471 305078513
    0x2209050109021b07053006040b070e040c020c0f0f06070605010627061110050420060c06130222050106031a0d0b09160b0306040b06070503370e01020c0a03 68
    0x10701541b40b0742c01d40240c0c1004c00c03c5540100010481040000000103100d00825116141051402801e00088410004801c405a40710b104080c041e4a064090440381c040000c11000440c0b1b241d8002c11080d401001c03048039201e444100600a040d0130281c00e00d00c0d0280e8450320707184604050303034140c8814403500c20801400201d0a56a50691080c0080c000100b00500300f070007642490b1800806003140d60a508000301061030700c0b013506251480403501c250100300001c1a01d0f848030034040282c0005400204d0380610b0140c012003441d03080250b14242c4031440c1c140001e00d98942800601907480c25091528504070194000c846603640c8038081110310f4100034111229501c0d4528140b0705420840380645080b00a003000504483e40002544200307070650703040c01050560418802c2500039032500400c10b810600a1081c418040040040021802e032380001c030f1081074040e01c0716817846800210f0006064040c82c1103071540c04200740e0414800964000c40c3d05031031502d410305c29107200d201ca107a0b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 305080971 1250 305079721 305079769
    0x10c030801050f040e0604200105120a0c030e370b27030d150906030c23040f0903031401050102030901030e011410030309060302040b2209050109021b0705 68
    0x8544450344003004155544088a46c182010b0030030f5400420b12042400001350743c092420748552064055402d0040a10200d18950b00d9a440c0d41000d416410002000c00d940d5010400c40c0007810080780a103601809550300303100c0405140c1c1d00c116414040300c040b00845070400c240004c2d8011001590001401c40c003085c825124508103042c1d0f000d04060510144008241c10400310075030350014100300c40c60510360813004d40d04d030b2641080d079203e8440035004c9469000e007040004101105503a881803250060010080790100240444200b078400e4145655240450400c15406100b00312a1100e1000d04001a601d00300000f0740d00e1162088840c10107441d031031809070901094109200308101052a200e16207406500715000c0c610520040c0e000603100080007a5642c003c5c800c0340d041d00c04000340d02e440c00b1400e02c04610f02402000b40101008419180000c0502e120702c100f44c081e00302c500002d6a21211005280e01d91a190b4000040d9908000c1d010881a076403007283d141da0310541403288907 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 305082221 1250 305080971 305080999
    0x3070c060e150a0c110a030e12070f060807030b01020f030406140706110705100504030e0907020a05010f06090f0608030d1d06010306050a0c020d09053a0b06010c03080105 75
    0x1061202c800c0020301c811820100348081c0d40381a0b0004040407199640c3d252405003e14001c40d905d010030040507000c221003400307411160501c000303648102002c6004503140b00c0c2e40e8074058568000c8540c40500001c040001340f201259042c00340c506004000d20003400c180d040c0b5100340761203204902c580c0c4180306011880d00c03103900961050300d0040e5001001006800000358905010f40c0c0301d050200c2d1140103854442c070082a03148580c500407501a0b07184501d03501c03440c042c02202c00d006403040017584180c4004100043c4240a42051910a07250206042d03203000440c0c401e548155a40c01d074141d080c07c00c14080f029000007922140000c114001c280203490715a840c4101c100002c465541d4040c400022040c402d06801c4140034100f004404c0014100e10b00080741c64025250411001403c804000c1025161242007801074100d003940709900c8094181504040e030108184506410b07810011010070300c14901a4240e00001c00e00308940b60300c80541d402000c0368414092240310b4411004806 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 305083471 1250 305082221 305082223
    0xe0919060803070f03260109020f070209090a0c08031e070c05031501030b0f070e04110c0703050c040e0316080705010209100809060105040c0c080c01090f0b07110303070c060e 77
    0x4004001200940f07541c2e0701030781403054410302401d1040d00485d201d0040b00e5402c1c51079102c03003070301461241a80303071507a42403420b2080a5800440c43d00d900f841d003444150b025940e4142058010903001d401040d4110369480c00c0318611080340e000a40310340080c803d11034580b64140300050700040744503820391345500714604241d400c60180c000603010320070b098140d00c0c00080030221605030b902070f880b0b03810241d0722404070903190007049030f00070002804045106000c0c01c05030061883c0c0b0151700c003586e062580560190f4503060b00c0303170300c192160b5210740140003503803c0610441140e040b015020310701d03003102c5140003002200c20850040180f0340018115060010070350595504050041c0f00620a140d0100c00401c021320564080c0d52901807078000080b149018494045051201d484490034100300380c40c0d4023495041082002000c0d525520002c001841c1c0c8299503034000e2151030624010304000c02c005002c9071400c03074280540d0b0300400c2445041c64100841c00e940c19400000031820241d030503216 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 305084721 1250 305083471 305083481
    0x109021c0b0a062f10060503030a050409181e020f04020301080606011413171c0206060d060f0905030307120608060112150e101103150906150a020601090b010e0919 72
    0x3404440d038071306500050303458004c21401360704090358400340201619003040586a120b960341001c003242c8104802c110704030319034001c0c401c42003500900e42c1610016886003180e150b0f000340310103c0342101d12a640210710b807480d010300700140244c03421402e66040c6004d03659100400b800b0740d810300100354000d01746000300c18110340601034403541206000351394034502c56000e07000d010001c50900070021b104c0340b03104080580e8040071400382d00806068440009102d2000e4604c0401d550781d64652205540b07440d014018800d140b84601c0045544c1d151440006000d12001c07440c64034102d00b03100c003c00902800284e000d0558521000b01018502e040ca4006444d0029a0850f280141822a41103210340302045500310414005402e2008004001c1d0080f003d2000700c44600b8006141000e40181e800e221080c280d0064000d81070f500300d04036400c8070000580000900c000140e1221005004105c110701079028030340790030300308910002c4020380000d012150003030449207401e680441c1000b481c0b90513084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 305085971 1250 305084721 305084777
    0x32406090f130f050103020a0510080a240e011a070302070911120f060102010e0304080714030721020f010c030c0209150607060212150d03120908030109021c0b0a06 72
    0xb040211064030310030000075140034030080c0c0c030500d1044e070b0000e00c60806d105030302c0c90040755980341d40ca0f5036a1541d070b8200030084900520139081800c0d00e04524542501d08c0d80700a0200c3c0c80c052201507240c80421400c640421790300c229903080071f010200020350002058401d03141da00c5e40109403550502d41c3c425481c021078032400d5034038480c1d20500c43d0151181c500b00e40260002ea00a0143c0081c0801507030307803841107205419955000c0340c820000e600e08182001d0208400400751003a441e550416074100020140a110040d00d8402044085141460700b012400b802801e01148107003003178078060728010003100c002c2e010750403030310000f10580021b07003055000010041c0391984521031814503030000d4025206500f503503c2040c004c00c0ca840001600c0e00c10300791004100c81c00c21560f95400306c42800c403100e0300011007911824054001f890810140d4003811002900580344c00c0348ca01c10000c0060054906500540b07011883e8503591910200401035406500306406902110030f84030310040702c4001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 305087221 1250 305085971 305086009
    0xa06140f0a030b03100209150d0905030a0216050f010c03111515030105011a0403080705030904110a0e0103051504090206090d0f0209070e03060a1d0d05032406090f 72
    0x541d01c90040c1e0183c1c00250b4106066044521401600014400700d2003258030040d40210b814000744030700581d002c01440d9130306201c0d5000c1024203180e61603925607081602000c001d80c01c40c9c0401241400346582000c000c0c1400c481102e00c020100b8006072448510050150070000c603040440b42d070744000c000240000724a8003183c4d00310300e4502401d90400c00c0760003c9034441d500b41000043c0030348010030410a145101c4088500d0076195940d0a04140d00220040320203010501c2102c4551b507071485100703140811100301c0c540d01c000b20340c001000410100b4115040c140352000f8044140381c00c4503600c1402009890010f4808080c0c000201c0501074000c085500c068284004000c0000400d6611001c034400c5d00c407501c40d42c50341042130341d0f0740001035002d5426910550003e081c034285900040840e01c0c20440d0b50044407a0510b505051034104004d5001141000061101c1503000d240803403051441e454190050080020020301e280c030030000414410180740a650604c1e581c0c0c2800000b140d07544403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 305088471 1250 305087221 305087227
    0x1804150f021204050106180e03041512051e0a1e0b0d0803010b040f0608010e0f0703090b04030c050706091404020901170f0a0c0c1101030e0c040606030e06010501020c0a06140f 77
    0x110b00300c5e02030b00e401c0c01040b40103c15402c0c10580151075000b030316640c43e8120702540c00e2034100811b890b500038603c2001c6040000452081102402e03a1081d60701416a0342034001d911f0304101008500000d020380b208400900e00040d40c0c118002a0000084800c400040824003038002c80000f848941d031302d2030142c031030940040001000700124009100311400850140f050954880c003d8030f140c1c000b44910249485200c000603d00a44c0c0a909070740b0071441d04000504000549840b404e440040720100e000c62030460500084c002c00300071820040260380f40a5008508000d01d50300c1d07062003194600e01881e004502ca0741260301407043c00c03c03096803403082124249005001c0c0c030000c4400b0345854800381d29141da000c045611480913500010b402c0014500e51407000c000450042c0b000580c582d4042c0904d45800a00e40d81da4051400107003250b58012640b120040201420084182e0000d81554000800c06810317486892100c0212200d81c101081080300c2506d0148542c407038a921240c00318400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 305089721 1250 305088471 305088473
    0xc0f130c0306090f0b010f081003080409090605061203120c04080a052104441624050c0307080d0603031205190b030102091207051804150f021204 64
    0x140d8042401c4401c3e003030742070007a240c0300c2182e14211000606410b000071400e40100c007003a4041e007583ea0704a48030b41e8040d06025540e494102d050340007504030031010364032103040c201441038074007030b56801640c21510b008424100c8030001750b8a00c2a404112031600014000464804001d01510000c14200050300d809540d1441e00707540300c4640c12074200920071a600b049002c6002013007a1420b9560604075440c0c0e29001c04846252031084172142181002514002e0500c60003625282e441e41c54908001c0624078501110b18245041e6904503102d800054042c3c0340314400c450051a551905504045640ba19512038142c110b00c20380f0350141c00301a0004400c580c1e928503900800480340256102c0034040700d11804001034a000359500c007030f20b0409805541c0030909543c00303050b03111401400103250007404400301d00b80c19030480401ca042d4200b901c0400072824541001c003101d1030040c0000d101c1b0b180c944c0da5104c41403940032a07008031541c2e4200c0603081c10740e554100c078609120b14003109528a8a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 305090971 1250 305089721 305089727
    0x10608240f0702030405010318121101061d2a0c070e01080d020a03111510080c010c032f03220801020a090302150f0a0e010f08090c0f130c 61
    0x649280415400d0424000360105070351811403402410035030b02442c1341529081c011400780110111034544100340050141c0080c91f1407480c140c403111552034401032403089451060846540e0390016044011650100809218500c081907020882d01802c01417500400e9403600c80310042845501300e804002018011507000282c5041160785071007142c02260b80312400a074300c561203902c1c2000940e10240e0f1620009000341c0384c0c800d0303000e0584200d500903010031034241d0340c02e40c003a109440060700c00c500038040740310184815400b0180c20b080003070740401560b034014900ea040f0038a22083d524184940684150b016200f00d88065900b011284c0710b034840d075500005142800c51096811a0134500040c1d0b5034410700944c0c90165017500c68190840c0345800344254219940480b01030103a0400c0740684040d001005807115440655400c403040145030000343c0520b001030510028400000c081080d0100000f88400c070480040d03c9070321200804501052020510121a500260a054034251503541c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 305092221 1250 305090971 305091013
    0x2f12030304050c0a03020f0d11040903030609050c040e0c0a02010f02030414010c1407080904020403061503030e061e0a02100203130b0c0408121e0708041412070611010608 75
    0x40900b055804240c8500d0400040720074600c0020341101c0340d0451101030340b40146240716124000c141c0e034883c0748203410008003120040f5604a01207580d8805c203000007001403247c0384e407002c8803a40c40c2e0310346401e2114680080d0b81c014882c500385500080e8002c101e6100b904080b41c0503d090700150345038181407030094403202d2030240c84040c543c038101100480b10f00c20001400b02e42100c0010b42e180028a4440002640c030540409400035000c03c40000020700384d1050f41100c1030403850442d81c4604500c0c00030000240001003e02c500810311003600122110fa126039211103284500365030780c2940325401da0601740100e5114295500c00f00800104820716240c03414120721812010f60140e07510155912240103c0c040d9490030b9000c8034109070310b05505030040c047c50711075030102040c200c041a440c503256802074104035041007011608100210403022096000a000c031550719540c0070351840d45da03482c5101e00c1144108491035842c41d440f95001c2d4001d202400340341040d0380c4590041d00d201c50140c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 305093471 1250 305092221 305092223
    0xa06031101090608060f1c030201021215060d090f02040906020c0705060708070b0c1603020102040e06011e1b06020f12160c0b071707020d0216032f12030304 69
    0x9126262101040c0d031140c0c54030401c1d203007a601c1383c1c1c0303054031504c00b0300514103207966450740c00c00c072910341c00e141400600c4030001346c16100f58000b598507031865480100d80c44000d005a941c1d00c070018540a807654074001a00e00441c0c000e6400143d03180e0034285403021100ea41d0000e5046482c1511803802c0c0f1280d50002c00e0200700c14021540150b03611010b0090700d1243c48000391402c081230121200059405801540010407400c1545c100780701540c41003000365240c04100c1c0541e41c00141085021303a40050306034020003d01b40000d415072400300901c050f8204080d60310801004004100e0182a0f1400f0301c0d95494010100315120030401c0300100d0158030186407400340c500000300103071000a0f1100b0510440c00c80340d8880764142000c0d918181e0192000d0300c0803040c01070854801011511100f002e03407156046034002d002a80301e00401904001280b240806070515030007050003c148201d41450348201e5403404911084145801c5840ca4400b081a00f9404407000c1c00500f60010b0001c00b03113004c1c0f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 305094721 1250 305093471 305093483
    0x60b070f030806010c020f0d052103010807050924040227040506150706020304241e020421061d0a0b57040303021204061b06060503060a0603 62
    0xc0c3c81c0c810064440b84000d040c000d511500c0c40400d901c40f81001c441e15041248910300b01c460390030303c07032001c581460601080e02e03000300404801040590340401040009000666032800b05007055400d54907080050803101c081c1090144e5001101c1d196941151303422660f1041c1c011070020301c030719a120080f01c0f02c580c0d540b01c2e03428071001c580a4507205002c40e40c22135602c040b051414500b03949544c044c1d04010000c3da1005600c9107000d41030060624080075031298460000360780c041d0322152003281c0d5041c1c40002e45032881440140030354040c2e03440c01d44002ca81e01d0700c40c0b44c0825039450060080c1403541c2c0707289410703200d01100740e440007400a401807910b449102d41c0540c6c4c0c0d45950401301050f00010850381c02c1e100307445400b80b20504450569180c04c0b50315108400c0d200350740c00c49007500c48803906100309003e0700150400c02c6c9507042c402c520981555020b290b15091a1200081076030f80c0400c1c20560861461a40740c041081c2d41e80024000e0001078140c4000345012034040000f054648026154 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 305095971 1250 305094721 305094737
    0xc0c120207080f01180b0a060b0414100e24130603060608070c0b0105011b47010e180f030403060b03010516031a0d0f02030106210303090303060b070f03 67
    0xc200e074117005002031080301c0c2c0d5514081c0622603c8000001030007409100e1110f58800d0301041304e02e10b03403000b44050203041c04865116012901880b4480103452020803c11401105510103981d80d46044142c00c030030310300c60700c014014000b85802680324116260b050402e00c00c200040e4a038243d04000119119504c0b4805140d8583d201540c0050140f0030051174001031340010b021542c040e600090084620b46074140f02a10240c0d100e00105003821b04030014620740e50f03901d1000d200c90242d02c110041c40b800300540c040807410180c00c030205041c0900c013801004140010701080f80c0180708483d154068007292050075a1402c040c3d12a480307408290391003820403220482d14101400707141e008007560101014010455041200100101c83c0221600074218185900603510b40900028190084510180c9185284109401c4480d44c0d03018100302e50b00d200c1c1d20300ca068440808001110f030541004a1042039501e011001440190003010740d20a0208416040c0036003102482e0125110741c4034200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 305097221 1250 305095971 305095993
    0x90c050603010b0a050a090801141b04030203101d0304031202072312030903010603080301210b07030c090f06170a02040b09040b24130501210c0c12020708 68
    0xe59101c240100040c40e4070030001091503602c60340041c05410034a2512124054503082e1312425903541c1e03d142c4111400103028410010450500904014800c107045450203103503030701180d00d03488884c00c0c0440300340c0d6644603024844a0786881803400d066035801d883d0344540702c0c50094228100003c2100040c4940d0f40b010608404034284045e030301c400d8083d24442802804100a00d1f58540c586c1007419000078400340f0700c2a18240601409140320349400b030303141c2d0705100c241141100290401241c00e41c1805072a00801c880a102d41c1d00481d50b4034000c87d00252115050b9071409407540b1803d40041114400038a072540581103035000d00414800315031b551180300540050b401355000f01d45250300c0401020b07090b8503190388401000d1790046d0a450400c28100c0500c9c0d025003803100c840d1414100066410208502d07180200b02030502400c06205a41c02d144004041e014900715066505656880e20460b0394011012002c41c554040e10004468400103c02903d40480303100f618064420401002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 305098471 1250 305097221 305097229
    0x902060c0f0105061008060d02120709020a030e0304060c03180f0e01091a0a120203100212010f0e0c0405010518040c02010209131806091704030f0209060d170c07090f090c05 76
    0x105c80940d030fa014290744500082007881090600c00f00e9004900031046413901d0400d102e40740080008a800586413404505c02074191000035859421541080205000e101d4010101d0f04400b40c06180241e903080000c80303010080380780c0344c101007821007a859000a0031100c901e200760691785906401d001c000c0d00b1900c405a03001400c2384807940261051014080e641c1950082030f0b49500081c211124014961180402c9034482c1d000050204584801802044200d80c81c3c00000c21920110092620b4070010089942c041ca000d0306041000001d070521074600219906280740400400c1004a041a090042d000394001140b59015200c14420030140c03000c0c038815080101e2100010380320500950f51050010011004100c9001a5003400c2e0781a80d006240a003020710b104513890075011410340104111f01c071000f000c562140d6940e000800c00142d844207103540c08034a0005a0f9210307460b174104c8c6410004282c00c15041d203854128204441d03901a040a01c00e580109002d00030705071114144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 305099721 1250 305098471 305098489
    0x62f0105010f1410031e09060b1002071d1305030c060a11160204050601110601030c08070e01060e0d060f020a030515010c0506130201090b0f030702010c081b07060902060c0f010506 79
    0x4694044c540800e400070290094000b1110718240c0780540700d407404070200e01c0c011101551410368a69542d44a41c200c182400711507000c0c201040d000074a0300c14586515a0641038000c43c0f2402000320800100301100a8688401e0503a030707110060f00d0312801111085650341e90119941208a400e1a55508084031010122003080c50041a41c203c0c2c0031543d000c0c0005001e001d070046041082140c840c0100e548103210040c0650b00c240c034281c041c0c43c60000000d00e0b20f0f03483c0d08280c0c603502d012001088031a0b08180140782070f0b20301f40c8003000c54220500f03010b4000c150382c186400c13100740001001800c1035032650101d48244040025100d15224080c011034880c5204031000b40b00e80d00c00c4002c5000c44c140c3d91450b50f901d0b841403401d40012921030000c0d0300942c10920043e2072110012007409170b01d580a015500754007501b460f09000e03615008000800b400310032840400010b400140280c280036854203e540e20340c3c0c002d032071305036100c0089046640e03985100a6252081d440c02c030109100307103401546 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 305100971 1250 305099721 305099759
    0x2120903070b130b030c0d0c1812020111010509031b0303060306040803090a050a06050f131707030e03070b0403030f141b030702040905010b010f02030301030c062f0105010f 76
    0x244881810110440c00642c07103503c0d2840da545496400240c07964994000390f10034050b01c3d44907505c80c4a5410182c05a40644003440c06219801010842000c98110180100c1e42076039a0a041381c0c07414001a00c0b800d016404080e040d50810b4100000d070140007004080180e124130302035003845d50401e41c00351240010380b034442d4541c001d8400300e00480c200c030019603040805803040c2e6050455507901c0714503221114000315811600e0340100880400c0040502e5800844404044140810ba030f40d0700b442c40685079031500c1d2000340840c44200b80f5110356001e105050014044600c0b940c0c4403c0400055003042c4400c0300040c480c14640c04200740300f561041d510385604030f0403a082144100c0310437400283c0880c1c141061009100001c003581e00d502501d10b000b401100001801e00030f03400010181601104202e09540c810401003000452180080040380d105107014040c54a1102451711451100d92040c0345004505199822016040d84118126500200d14801495460702c14441460f03010785 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 305102221 1250 305100971 305100973
    0xc01020304080d08040302030d02040e071707020a1b1208030f16050304201903060608150f090f060a020307020601121101080402030309040603050a0c0506030c0301060c0507050a0305010c02120903 86
    0x30000910071302402100790000c0c0b09005507030820011504200c2280c02c01d50080b100b03000c216051040564111490b81c82089407030480590740d140512010359661071028005141d614060000030244150041d4140501650301d92181140c64600b001110f9800c113a858541199000b80419003d910508a05442000e01d440e02802c559807916180c0c070311040c1a2842d1a103c1c1d0040c25844290385505071241d00f10300120800101c18114180380f001c0342c9154000580316401403800c0c0500720f44811889500009044004100c1d41e0b40c00f80b1141462603403d10101c5a100b01e8081c041c4040b034503005180315082c26401c8480e80da03600e250350141c6041401c2d010340518205170450f4500d51080038090351081c000703000c44c0c1c0344c00c002a01282c12510301d07034019940b9800c08030601040119003020440103120444842d41941020213074294a8403040c0b0899081c00300e400300c03820030003100b4010360004140c001c0c10a00d480d590703410103501030a140101c0344014000d14201980d06d1000d1070954103030886c054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 305103471 1250 305102221 305102233
    0x6030a030e04060b030703090507080c03100e100c0507030f08010501050702060d2c3703110303040b010608092d0f011a13020301051318051501080c0102030408 70
    0xd20181c40341c00c0d807600440d8001e0380b50300700030501100f40002140505c0c62681d00082c0c580c03180c24207905240342074002c0c40d116006044070501c0c036170b40080e8201c0c42e10309a001c001401341d00788815a01e040b500145e4209200d0910030f2070025140c021000d0000e040c0a0f8450541071528208210b0f1004024050f907030200d0030901c0684058140301c00604101120301c407001844040d200071040444840101103100707070800c1c0d4006500781e0000c0c0100400565a5207200e03c10007441c050b807815030008640c034240308072010250941414414544c0900322041c1c60300341c0f5036030b0516041c01103550809010b5400400d42002c013141020f4800103c031080c0d184ad450442c504400c441042039842015280c807056588600402005807500c2071003695112a11303454504590181c4e6000d0106140b4400144000d0500c18001008140c403070751068016803240200000d501989503040d424045110003015000384110b40180603111140903165050b13a20071001c40c0c5005210b0801240c0e00e01c500e014041d070941010b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 305104721 1250 305103471 305103473
    0x90a0f0b0711030c19090c050c060105060c03070b0403030213050108060f10090b0d150503190b0a0212090c15070f0b0603070b0f04051003020a050a140d0c020606120606030a 76
    0x16030084040c80d00c01401d5410035500540002e01c5e410418110240e071803440601080308854602c0389460486031405c10b1424000c499001300d03250f030300500c03e090050341d00180d40001e0050030701c112820300d64003c044204604250070028000e400400e50390200d040c003c03001065941c041c90100e07105440040c828503c005840090007040c9029040700014091202008030303036400c03284007800c1c003110f080c071000607081d0708208814003e08560780254020740040c4001d288224000300140107007504400000340c66261429420020320404030300301c856035400821b00c2076425020984811000044581c0c41c442c0c0110500c08510303214261005000d0100e54028100207480a600140d01502c000d090301c92040d590415203443d9809555940c03c0c2040000d0180118688001421030070680b5113001c41c103000d00440050200d00c100c0308120700b8418110ad04880c9048180b040756001c816100341481900c010345070103581c0300000d5900c11300c60b110740030f06441701880010340301d8030a49004009004490712 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 305105971 1250 305104721 305104733
    0x5070f1206090c17010e071d070309031806050a0314060d06090503091c0b130309090b0d060e0d1704120f0c1b140301090803073002090a0f0b07 63
    0xb8011044601101c030680019040084080024040403404004a100c00f11407400e1030601c0c0b0550000c0c2441502d00311340b614054940d08665900061500b4006060400707410151280906d005c0d60440f4000740c201c0100f540c590010242c0403840c00c6441c144050700300f070404441498800c0b1249a080f0200c4812039020034510780002c01543d01170016240703040f4421b00868808121200744042040f44a01d1440c100b12030b8070308603544800729000c112407001c0f007603500034400c00ca10703c06c1c0786100b030f1280d803000b03211359500021a2603190300c05000c018905080e42880d0700e543c600c003112400710318044502d520a44100350018441c40d4000c403900300068486500740e407450014800c420400080100c07010014205000818003061414501c3c8500303450700402d01019101004918020390421440030000381001090701d0b0000154202480000305045c0300c0700d443c1d4401c0c0c00065160b40c110740c1e1079554080d02d43c020040743c031040d1201480a5220007012400d00914400c2c0403103150100441c0001c214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 305107221 1250 305105971 305105981
    0x306060f090405010e0103021003140a020304050c120d030b0a050a03030f050d0e030315030114041713030c050405010f030f08030c0904050f010509090a0302250b0309010905070f1206 80
    0x8661401a800c010780a000700301158002d030018107401c0030050060084d032400300c440484043c2245014002407007c00145080c00340050850901130340c001c40442d0400c6014454441280e0002c0c100044124010701030b590f03610540d4403403201280c17505013401901d08040f0303485001c0d21409131042c03034407910b16030741100c2e14610350840c00100142400b822824500c01d001d030381450245080116140c0c104079400301c02d0418031500080c480c3c5c0c5440d500c2100503803044822079101e030f04203186607824a03006031941c1c59480f4000040d542d10100312004800c010102c220801901e5007030b0750400a5a032601c01d2442c402000f40009005140c5070807250002460340d40045502c00703078200380309042c81521000b180540f9000d9410006284c0300300014011410045a000d500050001c02844091155100603448842000e080354881c003581a070a0142408401148010800351a9850342d034600721800a00810040c0c8040fa214020402c0001b0350202c01600c080c00d44036100780c0342d00a10325540e1403030003c0c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 305108471 1250 305107221 305107237
    0x50f03031903060e0405030702100801120609030e100917060420040b0a0e07081f0e0604020c070e0f0603070f05060c0a05242505030c090418031112030606 68
    0x10f80b98000410200c0701d0020550049102c0c8009513111031b000c1c4100310041c2c42e031824100401c00c80c2c0c0c004100005484a01c41d4102e17410481c0050b001055007400c0717840940c54140103420007031844a91040da6800001003044990704007662107206002c8030000d84900c42910b02915503142c080113002040d1840071a02c052420050000615100c91404503008038050f6000341c03415400f200801c210550460880c1d6884041e05900000c80c0170080701d2040010104c2c0254203400e0480c0340050159211581128001400d071f6048680d0140d0700d808410700310740100c4218092440303c101180080c00c0005105055403501c100c034034a801d04100900110780c002040c400428401d000c044404910b09200e0340380001da01c05900d2208080c2c41251a112100142060341c207545141102034000100042d020032003a180e01d0010360326100c01c540350700d15009480c0507950140c0341c5001a0b0602c850702801511440c80780e21032144410300e080c2015290300209100015001081000030518600840203013564 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 305109721 1250 305108471 305108477
    0xa091107021017070309050613022404030b0f040212011104091107060e0c1915030207030507060509010c110a020f060c0709020d09140712110d02030d0315050f030319 73
    0x7100e041102405003c0c0650709100440d5803000508140402481036a5020342c0d100c02c0300c04080d5a40d804a03100011000000c003071209580201606000c5420480d401160440300007905802c106200415540302030310100d208103507000407180881c0303040c000d69282c00c9202c04800d003881c0c94a07a0380c2e000780c0b180e814000c40f0a0820017111700062024402c610700b41d8205402400042000c2c400d014105640d060811251440c41c0403c0040000c7d600d61600d02407140d113000360710740509203000d032024001c00000404050030842002003400c01548018000461541c4861150302c811355110784446103200042d40100c107541c140d650505041d001000f00107012800c6481041d40e600f1f200e000c0341c0005160142d202c3d10f4803401070900074011103401d11034103000064040c4502d0207002d0084120a0302e801842c40148012800f042c0d9640c103103096080c0d40103010390b001c59074440001001868402e11145c0005e81401001c10141801d01d00d10b1082240039005601e00b05441c607a000210204a1000c010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 305110971 1250 305109721 305109737
    0x1f0c080304030e1f0201050c04180b030a050a0503070b0703050c0702090c13080c0307092901030212040305090a1403030412020a080f242202030c0613050a0911070210 73
    0x1a03e8030704030360704404c0008148080e1040c00c1e0b08000d0079035801511b5160340900500090050107014950384030403040314140059401c0c1318001103409e010341504090502d00600122805111002c0002c0a005200e03c402c1c4455640d500816011500c0a40b1090022603050000100509040c980d82e5008015014018200034241310400f072080115088580c06411040c60000a402c08205600c0648120402881710b80342004131511012100040091070344020001030803664041d5045594510303041644c0760706841d050802600b03030750042c20b45074010185204c0005501203415001d901c0f16034001c0245161628004075440d1600020b842030360720803400310b40014582d80c2000790903e00c00242025041e084014291060040f903101108000c8a00c10400c10501001e07009044402ea80742c1c6c03605004085d40d0b800400c2c5001280501a078019000150b0394000003001c042d02412640d0407258211515101c1c2418015502450301000f2020001d0200720014035200048510891440c94907101c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 305112221 1250 305110971 305110997
    0xd0e010b0909010e28030813020901151e020d0c210201090519030c02211005061207030f0209040218010b0307091d0c0f0c030304111f0c08030403 64
    0x40c291090703450740c90b181c0d0f44203d01aa0700c03c060007000300d180b40d40a110f010011414800e4001c644401c000102004003060000394102520b01104c9141303500035002c410399684484480b14134404800504011408807280e000020f0001e86010110324800d502070584285110029540c0c1c8003209000c03249004410380340501e8056040669039118070550001c01c018540341071080c240703401d031b003500809e5400c03105020020a4010005030100d130f60541d210038440100b000c0b88100b401702d621411940e4002c1d509188610b0b075240c2c021601401c3d00f2160103940c951b003054010768402d5140301c000c0114010750748180151420b40c0002e5402130000c1c18850108004000d8400c003080c0c00d0b017002010540c040144404554004c0c0402d020f889003141d15119010203982170b24650b940100016542040000d0507154101c810090358041c48004007180d1b100d007041c0c83c016100c07043d1001c9240c094101141d1100107c1c0028046880e101d6058840d840400490788070b40304e066000600540910041c0c00e1804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 305113471 1250 305112221 305112229
    0x3070e06071101080c0c060c0703030e100b030f01022704021603091809260415020703060f060b032e03081306030c050f0d141306060801050c0d0e010b 66
    0x10303034288900040b22100c40010009888400041c0501922030b10130b000704500440c000810540004207000c040b5102c0d001440c046020341445c80404440b8016080c1e822513008507900300c44030500c000c03807e07580810702c07650095080380540c0128a40c51040d150500398178421000394114458400382006d0300c1c00a860404282e400720880b01140001c071040410080c80c00094002002c44489000900140b4503030703110940c070141e080c008804401350520740385007100506411640281311080020701080c900600c003030340340c400500c820f41e141c50030141d198420f0121889008140c41c00a0751450440e11540008240b40001c3d0f0f00b00041d200705403003030000740c046010540300110701c11000350750340d0200b007115913000b00c0040d4440420701d800c00009162003a000815642c030402c280c1503198403148461002e8001d040148510807503103c4076801d220100c004030001444c3d450007400184000d0f65560b42d818201c1d0b000311038040b5520028402810110281c0c0c2010790790144101c00445d40c462540001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 305114721 1250 305113471 305113477
    0x6181703130b0307030b0a0e04021908070602010b040f0212010303141c050405010b0f03100e03040b030406090b01080a0506010302040f150b0405120c0a03080f19050904050112020109060503070e06 86
    0xe1482c2c041e01100304152a85d242c0030f4050303c00d40035503220084500e0490204c0301504041c10081c8030700d092100620f68031032594550b03801446034000311050b566070356070040d0007000c000c04054066802c110507050180d045000b250b010041004004605a203503403822100a04c1c501404c031544032081240145840d007451034031b0342c0c411041100140741d060915140b42180c0e200040031340180c0115500030324643e0003081e10403040c040c61700042034203002601c510b81103105541000401d020040140000e110103540000410f03481581802102c0c2d0b02c07448280d6031056940401016130384070300014001802d043e000f0002d070480d00603020070103c47d1004864454207280e00941e04103e00460304000925100c01422081074241002c1c050402072480030035004041d03400b016088510004a605c10481d14104889002d4901f044034a0f0b400641c2200400903840380603160711440c00d2000109045a4030b41c056030b2607581c142c407005401031501741d065400ea0002032110381840300300488048207481c0e100c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 305115971 1250 305114721 305114729
    0x2100c060c030c120504050615010309020405040605010e060a03050c1e04050711061008060103080705030403080a0809010b0f09130203010e120c1e0d0c05010f0e15010618170313 78
    0xb0841070520743c801042241c0c5510920b8615041c03c0601020440c00f1883c40d400484c129107000e200c0c01c4080c0180c000c6c2454040080d001882c02041106000c501e9000d50b0588011061901d0f542c0c6a0350208404500540406485500701c80e0071001c4a00d420601e81032a40d003d140784502d038015010004d03080321400c40300700022401e01c0718190784480e400e0007090781c44101c0c109114052814004029900c10050200401641c4006a090140101001940e00940d4850700c8070b5600c1d002180f00915015050710a950b40d50b0a0204858003480c294103450000a0040c0c221340c01542d13441070411030107003412000da03099503840d4880a4285414030030b061005540c0007042e07a80705404d01e0410320f0305403a400e480710f040c102d0100711036a2901c0450b043c1445044e1f450440460640d40c20b1940c01008110b01d0401c10602e00b85180954440210348086040034044050142c0e81e600c80c4169000000300c0c016001c0e0540b0814140700c1240c000c0404c0c0141c00c200c5d000c89007070031403021f100d148204250b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 305117221 1250 305115971 305115977
    0x305340902120c1603141e0c0f061302060912010c210510051e0a0f031e0b01150302040b070804030c080c240705011506090e0105060702100c060c 64
    0x18900000d400b0000025040000010360600e001d28031880f21400000151006080202d900300003a0340400040c1510011900c000d070301c4041d000022640d80c05503014900950242c0654401c1c03180e0008040345840c800c40d0407510384115117081e54204203155102c0004168491100c0c0d400a042a00901c10001d00c8a41c0b80c9910303405501814001200060030701c1442c0d115407c02040000201031401c05c00304403441540d90b1815403050128441d031810041c460b00c1c1d000341d2004000685000e040008100300e81c09982102d007200064810301145d210903e2010303241070200c000401c1501103428065081d06d0042c0350060070305842e0380c0100b032982d00c0700340c0a59540602080500c00c0c813031150400c03c003c1076224002d0040035000404622070880d42c240704000d0149000d030318101c4041e00002c44103003a5108000b009102c04071107064050b021240540350001d0080c403408100c82813220003d5040e01c400400842c02c00c04030303a080000c082c01024401081049092809000403824002c0c5003500780c541e2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 305118471 1250 305117221 305117227
    0x10090b01060e0603060d0201030b0319030c0215030f071103071e140f0606040b0a080f010c0206090f21040302150702100c03050a0f09081203090f070305340902 70
    0x703500600407440c0c5140240f08400070000d0056a03525000907659076582800d0210346042c1400019050050b40e410300c8040080c80e0310760f0410150300001000ca007078030031205040301c03110006075868607000440d075680e040100c17003001c034035490b025031380d50b440b14404a41103902d407250302e58640c0388885007901c0d80c401107020318410108101d8044540d5884034403204c018022480303090a015034400010381840c2c010769640c490000340741c4031281084042c0000e40d04440102601c510803074001e05800416200500600000c0780c7d00c1d4001284404140c13291038018a908010388010302c103840d60030180d01e03111040c100800001602c401642c0124110740d241d00a46135481d90041c0035960315a03e003440200468035280b030700000d4010080e100011000d142503d41400b8130070003a21010413540004001d44034160107941154402c0e401944124214401c0e110410382c1600619520304d11030100078029003050303241440c0c042040ca450703591000340421201090b540b00c0c0e000b4800038502e030070204000d6000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 305119721 1250 305118471 305118479
    0x40b0f09040605030a0221031201060f021005100515041a04080607090f1202040e030310031a0702250506070b04031d030303150d06061712030403050909040510090b01 73
    0x1071103000000d002c00d901500100300e11b0380c0062160511300740c190000c1392010303500d0b4100c090200192000c0e2100c0400e080c0d07076540c4a00c40906409640045180140b00d4104030700307055940e5004003402403842010400c0036500744010050440d054001c02004140b060100040c0d10342d0013103440203409100c1c242e075582c4506019200c0c1c14988020050000d00c8a00c8000b00400701740b82c0450340854254814603480484148000f07400340c2890341c640314182c88017009000b0142001c01000302100d01c03440059002c014051883c40190b0003c46d0b80c04007681258607010008122a000100301e0308203151040080c0303031031300005451500300c1c40060790111105d004000c20035800c0143c0030a49600290420040b12003103000030341e2440002e00703000088600f10390b40f00c03ea031a488151140668001c0341409083c1c2c5842601400c41d180054907000b03445100d0310b2001541e1688111717802030380c0564800340b410a4140500501500c058000c03a440d204221840680c540c0c00d204141038648192103000f841e5141c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 305120971 1250 305119721 305119729
    0xe040e0114010303080a0c0906030207050a0b070908010b041a120f070803130b0c0d050c2119054608010501030f0c0e040c031506020d0807031404020d0206040b0f09 72
    0x200850021441c4c01aa0450203230001540c40c00c40d00c0903d0090390b5118030346010303030401200c00402080da02c3d101c01170000458002c1c1d00d0f0001d895a0074001c00c10130706c0341c604000541c0c1076404040b00c0300c045171200a51764100445110300d402c600d84121246413800301c050b03515011056021428680002c258410000c8420141c03400a14020905a013000c0e104103600c1e8998840d81240c2040c00340000b17540c2c02c07840e17003804520038081445039601c4654605c108501111390080c56624403950070b10341101181c902071801c0c0c038443c1c680c0c070711444a0b00307064002c2c00c96100003691907004c1c421369290300d11401340301c00000745151038070315a90030790325500d400005426200b00e501040c1d0418144403480541c158070086c04000b07100c00b21800300d00c445801500f60003d020014440112029480d004910242c00140035071134060b40c2d03078030340c5c82a030354501d012011034a03804400c2650410041c041009031800404880b07425000610b00c0b440c5c6584c1d0303001c01c0142e51103610084900003002c107003d009032030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 305122221 1250 305120971 305120987
    0xb030708100b04050f45071a040e0a0903020c100210050f070f050d2a090f0b0f0304030e041505010e06040803220e0c092d010e040e0114010303 63
    0x79100214141820400c0103080e4681030280580854442c00350b4240a18040f0048282c9200d81d41b5000d1040081030513409440782000d00508a1070746040d400303402004d403101d0448049601403240090f580e180d80c15248041c0c15950702c290218480d003c00054039070b40d8000304c2d007401c1d4000d40091001a0410083c4c0782030b01c40041070400210100342c10089802c0d0018202c402e2800c992a06070f03550350041e03416074000d140744170700319807007a20409022085c0d00703030b07216410f0f2040c5003901c0c1d0440142e9207241d94441341140e4000c2d09100307402484803c1c0794a14034006141c0140c0310f030800031445541d040100b0101e61505150900c1d40709418020005560131841c0001c0c2c0390000c0da1f156241c5401c0000036941d03442440e2204004c0070a1414038500d45c40d083d61550060104a80820a41e04080110189035004032200d6449200040390b01d01c030040c0c080ba000b0100d03100c91160200100040740065407612640e407542c80d0840e0700d890000341c0c03a00d000e02c2900480c8441d20f1a9400a5040d0704004180380303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 305123471 1250 305122221 305122231
    0xf1c050d11010c1110090c211703070906050904090218010603110909010312110609011a0103020715020f070c03050f0105060a06020a1509051b1309020904060b030708100b0405 77
    0x1128440b11540410100b905d500e61920032101084010003844c1c0018048959813001d2a10080145160460700c11042102e0010b030207032140043e00076002e10044002e1109642050105a10030020800103000311b01401010100038400118505030743c012445801080f100d0b045c00e140c8101c0140035240c0c00d80700d4204c0c421140c113000c6050000e1600803a204000601010701001d1180b2030038220148101750085000325207406540190801851240c0602400c03d401c550000c24100360741e0700c0c2d522a200342d8000d0303a00b24140c0104100803095807402940043d40c070603440b1908000a20211303070038407041d5000718032460081c480340400c000401d0031a603019090a20455584200f01b000d550b001801c40452500181c0c10700500403804e55480080000740c030300803d03e0107030700400c01840303c01c60b5140c0002c000503680301d202c0c1d8064020f1a0100d400d1a10b0003035129441d07030086030105006620140003e00e001d0110744109803219072041c9485001d428003000783c3d8840c003500d002801c1038080c0503040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 305124721 1250 305123471 305123477
    0xb0405010b0a081b0c0a030305010f051c23070305070e0708040c0308030c0d14060a060f1418280503030f12040c03021908070803090f1c050d11010c 65
    0x4500c80120050903c580a0000110300011010052002c50188103c4110b54900d8007159500c81961801502400d02441b0f9100503850701ca40000c0c0e6030400345440030f01c42c18144004c0345156007a50350640801d108015a03080c00c80c003170021030702c03640e410401c0c6c0c1c6c040c60242004003075003171030710480e00c40c241401004a010005440306000001d0906040302090325070205207140c80e95603c1d01c0704804c0e4002d03c068a04030b20300300b00c07596800c01d070705200d0580a4101962200c090944481040c2c403800d07100e90b070314030005891110340e0455085500250444c41c0c0310194500d0500c401d000043c801e045c002412010f448550940004d0080c80300f084600146030036400b0f54100048044200945d00403c081681c41d4541100010100310301105004055903000b0103c041039074401100070322001c1c81d80902240c610445201150241c000001d40b602c41c1c900801c42403924031040f00740801d002c90915000e4613074440d0901040014014010070039034038510782e508145041008040d600b134403010b030400c10034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 305125971 1250 305124721 305124727
    0xf050f0703150b06073801180e19030509060d0b031c0c02040207020f0301060b0c25050d03050706110702151c230408030f0603120d0f06090c02010b0405010b 69
    0x20340e440780000e0310089500101d004062a40812544804036505101850f6441c01e802c501102c55503400c02d1541614481c0c090310290351a450281c0341243c1100280e070700c0c2c54ac044000c1148075054442c64001c41c500c0b928005050a00d4580070030340640242d031a0000560b1201524421030170100b048161400e404602c520040402c403002400c0e60007200d00103801250002040e41c10b5442da01a86000c1602c0030740200700d4140d070f80d00748080756003004070060698090140300c00301e0141e5411500d480700400440e6000e01501c0c0108104508140d04030131424440144110030100d081441840341192605c5000c40d914012481003014581a4540c10300c00c207002807150140080749800001402e001c0380d10300041e080903041a28160300707602c3c50b420000c03241c8003040004010258010b14068060000b4402145d22401c04060310340c13070300020b2a5a40e8805100c1c03050398030070b40c0d000040c04600840c4001105a1200d0103203059881c2012040c0c0940e4440300141001e040506c14540184842c401c2681 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 305127221 1250 305125971 305125991
    0x20418050f070f090203070e03031605010c050408060a09030e030322060804050c100306080d090906080304060221070f21020c0f010309080c0304120b100506160f050f070315 76
    0x41107103002d000740840d0130703401b01c0040c401a020340c21544c00c2580c014112600d60a00d0303480f4004021503114110780d08e500300b050b05a1782600650558050750b058030f01516860303840e50847c10044c11014800e0302000701c201c00d0540136480c1400100580103030810554104150070725403003030314180b941c000390422000b9020003021540106175040d0300941120383c00751208035104201d001d8981c2e60004043e0340500060600e2068201e2000b400705d40100106108466864080c0c0b5168011842a100940c000c100600020f8601032141d200b040000010541810700c1030302c807002c90020010084071907041c0084516002c108034420381c00480e84920091081c0b0250801166180d075440c8520b6050640f25034040c1c040211000a44d030358408140212900d50741c0d50b0300c400c600d000c4003500c2540e1018205000c9000d002250a804060320f80142245182200c0444801c0c0c420498100950741a0f100c0d45d52207000032818040d8000d44a180e500804405056003401c0f00400a20141c0e4008503140148403d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 305128471 1250 305127221 305127239
    0xf241803050d090f0c0b04061404050a15090b1201081501060f14040905131b0806010303080402040b0918010c18030b0907080f1506040c1205070c020418050f07 70
    0x14500254841d408034060b074103403400220f41c007038940d8000c028045c59000868603003620406402258002c1d0784210014034050160318045c4264060316810034603100040c1300d5140102c4903498061920700e041714401d81e03600c000f49041e8109540c0141004220301c01041560400c010004001c03500b03030304840095143c94006051319078440841018801e1404100c2080c00f41c442c00d68004121210081c009850108c41c07074502451048e8040b25003901c00703424059070088104000c0e0955000c0ca009010523425601e056134500b80080040380d1041e215503c140090711422501c0740500101501d800201107568101420f40b85104050000c00c501102400e0490414450102c200d035044507044040b03445030400d0905000d0b268201c10034610038a10050644c10700004c82d200520072a224002c85500e4003400c2105483c022017114000580325050700c0c880305040c0c0c3c03040e40c20100038140310300540356903804142a1003c852203000d4018080201d2824400c09002c1c0d44190f110407400ba0100c181400c03909 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 305129721 1250 305128471 305128477
    0x906180a05061c050c0a080a080412021201090c03020a08010c091715010b030a060f05090a0f0e010606050903160608040807020a0f03050a0c090203070504030204090f24180305 77
    0x16501480c1c49801182c480d489803400d00b8040d1198100b00800c000c040e04100d940c0c0c01881408a0046004141c0003072458004601034851540c460142c0e45041e140c03208452100c101040e05030780c0540145d4006010031824415002c3c0c80307118200c4902c0c201d10750300400c80700348401e9102d440140d0600e140b030740780746a1200b600703410307200036600f80102030b900141014600160104030b40180c01d00c00c0c0001c6100119031014501c56a2b0700c0109124940e00c0d0f0701101500041c038411960040e0141e400300d02e100207250845c4465500c0c4001c00950340d5243d902d80c44c29501d2940c003200108500107440711490900303005030a00c0480020310f5a050390b2424000a0511400820107408854086100e808640d621070a0800800c2c0564000c42d1940e12818091344500c000102214000b690a01c0007034072036990300a4078810307995a1111400d007881e41e020b00c0064800c0ca1000c440c3c03d682c505444000070400c60300500f00650407010000c0c402c1804d10314a045075401ca03200c140b1410340b0740800700080d03400b17411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 305130971 1250 305129721 305129731
    0x91f06062705060a12111e1c060b0903010b06090f09150d061b03060e1f050306011502190b0411031005041115070210030b0a0b0f09090618 61
    0x9428201c80216000e0700451500c0d40015900010014580600a6011038110300c16100184208244d41004071030f0101071184059078100c11020707081c1c0408040ea080050b000c85a0740250701003000304182030700d004840141e0030004400790046020701d00c5003024494000d4030031060780d4403880d00b00703030a002544009511096038804e000000000b482d0a080701008041003601810190002040d0b10f8428040e00c1121900e1254890300301d050050203100e401040115848206102e403191556003042030010504001c40003041d41251000038642c07030800036070340200b0809652114195407d00002c6c2020703c80083c0c1c0f24084024103e1001007103240c2d98803a0071540c00ba500e41a1240d160020a00b00082c989051560510780b5042100348500700e880c034414810b0444042c3e00002c448040309a1502030110007072f40000f03190b0806244540207074000307056941c0041c0040a09a681c041c40c0c40c03150302403481400519001700305013599041102c5455088072040f0b0b80902e140d40b0900c0610340403040149 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 305132221 1250 305130971 305131007
    0x4050705040e03120112110d032c090c040503010c050a0905010e040618060e01050d1112070f030507150c15050403030f061d13080a0c020315091f0606 66
    0x500c282d2141081040352400e00001040701c0d8150303900c0e01c40c460003501b0580250b8a510544070301d80d00d186040ca09150710664547c0342e040b00d20101c030400050100c040c0c00e50708104c1000f6507900310706658400c003103880781031303010100d40d070311070a10f4141800c2d02d00101c600801d00400340b0880d0782882e002002002030740d50030300e40480b201c1e0702d031f500142c083c0a080c1c1c0b256040f45c2c00c04908012506050300000103590110700700c8440c3e641d8400034002003900420011b005031b2894007586080d450311b8106060072201d0350040700d000da0b4452403101e440c03200c29030084649620019040004000c0030244110920403030401140461058441d00100000380d8054502291340f00d00180416000f0b6000e00c607040c80f0000308009c03280d2916004410729110001c824000c8072940001401c0080811071444066880001300d400d10050301400e9400a03070025003264140606400e80030104110b00110f4400c8804c140202080e80023520341050500b1850001c00340d031820540140a016004503503442c540348550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 305133471 1250 305132221 305132231
    0x31506030c150c06110c07060504050a06030f2a030506040c08010308030714030a0e12030105010c1401140a0902040c17011404020705030a020a17040f060c080910031b080405070504 79
    0x1002c200d03140b200711403004014910340340c180000384070340c08080e1a4042c4001e084800f03180d250001501ca0780254491140e004110320b00500010744030f07801110402c841c07654045002c4040d0390300c400da040e0045400c0c40902100d4121218000d5050092035006030064078104030142c81c400000b008050140030280103070344004081181c05125907c01503501400c0207009450381404040d03800541000c8118040c00d1261059040d01c110380c0d041181d04132081616090a01d00f2681d4800e03207140560414100e15550314007480d03451426940314580711702515040011491803910421040303c42d040440c40c208415651070440e0221100078441c1175480500380c400314090910001400382c0b0131454018403501012a0300303190b55400003103041c40e081c45215411002003844015261500851084184501d240401001614051408001c00500400318907180c4a040d0300858840c91910b030444000a9592246000d24441c41d200d19000105511b481c03030840c02d054454680da25650300409110300e17a10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 305134721 1250 305133471 305133509
    0x10b040b030402120f0d02070801140a27060605040c02062e0323010b010804030f030203061302070506010608011505180604051801060306090207080a0c06110c07031506030c 76
    0x3c041c13a0362200d144d1104a56012030b000c11a242c44080c00c102e4400544507180000c1188103041c041c0041400385900f001001d0f503103204031640980540041c0c0b656084290341d01005c1d10b210361000504031405408086a00c81c42c1406000c2103030111004070045400034014031509400c2d4840000c0794491030400d100b1000c0707007001702e04900c00b100d80c0b00518001d40d90142c181055120f42615083c0100400204071401d0480c0c0155010700701210000c0001c1d09a14060305103900076401b031500020040c080380c80021a002081049912000058590748d0012004200c49580b000016015003140380b44451110301150000c2e12074018042070003442f602510304d1403200d4131004e041c2c03802004001c1149034202c0003a4007080d5a81e00178020040000c0c01c00c000428421403500840e901e165114a0039072420307003680390844035511641c0d81181d40c44c0c2c0f00d4910b440a03030034043c0034080e802c1280c0081c1c10454034600d05801666582c40b83c07031030020705054040011076070340e101810440700702c0442c01c0484450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 305135971 1250 305134721 305134729
    0x30a0902130606031407090b0703210501031115090609040b04020d0c0c17070c090216060e071d092d01060311030d08100b0c010b030109032303010b040b030402 70
    0x7169000c180b480c0140004000c3da02d6002180c1c4009824060881511190401c444c0040c0710300540c5c440810070040040003e00c40c0103503402d500c145640310010040b0000c07400b410303030310700307900036a0410800d1a40041600c0c00851448807038035030503865840d1001d80740104186000e2003440610032955004078071074540700c07501201d5189a01d1031041048004585c40503088500b2010103442014010301d0444245180760122601d164103e0100014640f030106040003960081860004014400400e100010f40c140101d03265030044401400d1518142048030b40c0001ea0b4006141034520054144650500b001c05d01208000700032a0710303207080040d5140d64003803801c114448601c2e90b02c0d1520010030b016290104480b501400c8041c0c171184068030504840103a010b84101d10000d4a0001c1009555200b030024000f90b0381c80c00002c29084625400242103904450060340802d0480c0c1211149a1110820020301d0707950050181c00e65041440c0d400e024080c60091445548000002c038ac15503031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 305137221 1250 305135971 305135989
    0x4120f020606150c1005100b0304021807030b0a0303020106080c0109120605040c0b07061b020303060306071b05010504060212011e0504090321060e0907030506061018080d0210060b030a0902 83
    0x24024205c450003c0701d20340c1000140011211003091344840b190201b41000b44804507800f0b03a400502440714508001d045883c840c6001d88074206042d079805104d40c064441e1511900214065000010064170b000b4240c0d04080300386511a040000c841c10030300000d120b070b03000300c0c420a41120000645a403240390555440300c00c0d40040c02d64030030110342c00c1e0030040300f83c2056540c0c43d962504000084c26034681640d40c3c1c0800d485155250300a032000440b030910800c21085450781c1086070081400e501d4444c1802c40b030095078181c6000350005900c41040a01020080c0100050048001c00751116100d006c00b50050b4084c44d4819500c800025060500c100406200340c90071401c0005291480c60001c001421688101e09402108400254049001203100c0d0104c0c0c2d0013101420090b5100420041102d840c00f481744180103440c1040c0c441914981c0d2080003400c200c0c0c1c02807010511404000e03150180c0c801c5200c0019090180500c04046c0c07020580e5080f045003940070500280038400528031308 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 305138471 1250 305137221 305137237
    0x3050312090c1f09090c08060d020a050d110f03061b0306060706020409020703020c091504272607030e0105090a0305030d0c14030402030607050d020c1504120f02060615 74
    0x10350301d00f21a11404030300701c1d580c2c0009102500c2d5489850703990180030080e1800590741c100403910003800200f660903e1105250080d20007004101410f03294400140140c01080054403c404440b6034008241420001048540c004400401c0d4900d0000c510504104000450183c010408030125903151550400e603007020b50301075000d5444503100d40c11a0025000707100290700506c10703002042d60343c0c107051030428000c9400c0c2845002c0424644180b00107001c0e11540d400103902c101d0800b00d021a0300c407182004083c401c0300711411800107041c0303405601020501d5101440c4041006500081d001300030921148020b00740540c59000000000d0182c00255102074a240000544140b1041c17040d440900042c1a90300c550070f075408800c1e00b12885002c2160000d40540c0214085004035000300d01070605d00c5d4980b8405071808400c541c07445d00b4102c10003980e0010003001400d1004000e481801d11452052a1401c00e101e041118002569150003805442c0208000c501c08448036001c01c044488003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 305139721 1250 305138471 305138479
    0x51e01140403051215010f18090204090c11030c03040303031d01060f061d0d0305070f06060306020307031b14090a091508070509090c09100e0420040603050312090c 72
    0x80e15150801030029802140c2c83c1001c42c02960000e02e007690a01100008442c043e521541074101016040d2a80910900d9034058140c2350200003c04411500052014100341034021484840c004030203800000003103800f9031143c00031701444004043c00400c0e1400c0380d40618000c5004001d042c458030315520710203240002542060008255040301000c2601151340d10343d0740c200c3c03a2554044070010051001d03103540d0300c00c84441190000c03a1194000d000c0c500d016003a081c51030000c40e0f03211803c480140d0710449a41c0d8022003006009038241c42031801504d14280307080c5c1c0f02001d4410041c800c7c001003c4102483c0e0000c00e8000b4540c5805180302d01402508004003ca81034000c00300315412880d1003051243d00c0b500001080906202c4103c82c011840000100039900b41c40e010820040402840303440070600664001440c0d0340c21900050095000d5101e0085050030b041c3c3c0d0700260038855a42a000b0703420407c040000520000403a2a481d001d0a85100144c541054003410444190141680 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 305140971 1250 305139721 305139761
    0x303030c1c060824070f0c0b0a060b160b0109050f0403031e090501060513020a050d05071e031505060309100b03012301060314151002121303050606030a051e01 70
    0x13058082c0c803181c8005841a0200b4080e0760748541046815142c08041c060000c1c0c407201c0c4041c0041c0101034441e8001045100108245031154420350740350700300000450741102c1021248003802440c13004e0f42e02400103003506001515264940800000380904010209941d900c0e0b260b0750424114101070346092480c00600410240d82006406021709005a51051080790f0221001c0000c038806c8410b00c981e50b40710f0604045006404074000c1c00d0003003507507080c0000d10034034035400e10285c0040c4000c12800d403000140007034135140181a91b5443c5d00446e0040702c0c100144480b04000059011008070648004112a0385680200f805002d151083c2c1402011088403280c03081d80e1036425070306a50f91540c2c104120304054140000d0000180d030215103012486211030102c0c14108002c1c00d60500c0c5004548000c0420074120400360b001038070840003010f80e000103008201d001e002d42500050110002c0002d07403807684900d8ac4866504d040c07039001c0c1d40300550640e8215002e4008688c000e0b080313051150303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 305142221 1250 305140971 305140993
    0xa120503071403010f0806130203070e070203130b0406020f07030b0c071103010606030b090f10051c0506070908070605070b010621020412030807110c01081f090213050303030c1c0608 80
    0x80818014000c6c428140102000203155100044036211000e400030014545a440c2a80280746850050007000c114002041842c0c0407003407030701d41e920040c01002613507580c441c584000242400c00c0d00075460055040900200042100e0142154020024045e66540da020525022104520103840f184e0075500b072041c005440d42d055400340311000c1040d20f041c1d002d0b68075069008000c0da411110744902e040441000c4c041400c25020311f41040d00100713681401d9400d551920752030301004481050028060301814841c0303ca061286c1c10040511781841c034103004969417010240c880500450041040c0075218004050140c486c40a038200281001c650326900c480401070010300040058020810480200da5014400e00c1500b510000030030180ca001c0307114000466203603202074072014140b254614a200d034003240403200c0000785a10000140d640c5002d41550500341069446207110382c006008201d16800d9107400c50f4600b00c6000d110400e64001d40612000409454000314220700c40d00d842c6039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 305143471 1250 305142221 305142239
    0x40e06040210051204121b0f030e1801090e010209100305010303031d06060f0a080f07030224070f0c09020f09120106140405130f0503040609080a12050307140301 71
    0x260040e402910b8018a0110361003050b91076101e0b1040500e84100301000280103d030584003080310341c44c03940c07500003d040000050a0b000001e0703140240c445010900d4500201034100044446440003500c0c0b100f001703c42850800c045e020305118886c4500d84070ba2032000c4402081d811264204001802c40f020b541d58180c0c001e000744024081140800e2414042010002007000c0e1101c0c8683c2040051407207036079010a001044075800d811682000182d0300c0428294002c0c0300604070891390000130706803180741d80100407100c0083d020030310340d1080a0700d800c0a07403041207017191682504032202c12a40b4040e4a841c400f8012a030b030081d6001440070905504041c0030300003e0900301c03c1110700d006400301c041c080c0c40c00c0310300f5407041c0e0100346080340e030280d424140f980040d940b0040b200c481f0011410b4a4032031049002940c50101d400360400101404540d41182c400d0300640300d200c000b04200610b40d0f03244005030703240802c0402401000710004204074403510070000b803242c0c0b068900d5202d596a02c145 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 305144721 1250 305143471 305143483
    0x6071b0308030930270a06051c060e04030c0c0e0a09020f04050603070501030f020702040c030903110c010807121514010921140a060c0504030b010501110723040e 71
    0x12101a21914038035078000c0040752070721140c4c4642c10842441c000241e240071210034032001032110f146840d0740607a421355580ca0600401002281c660382d81e074101c035032240e1134801c5a00e40340510051904000f4003140c110490881e90003945030801c000d06400d0f80c1000700540001d58800130800c0006401c01518440c46d41144460500c01d9840c0181240c440e42004151071040b02d815401d07600403181003180c0c0d07200f074000c03010742690030100610313007803070350f008039040e5540c40d07400c000403e0b160965441055030004203810b51032142d0300600111030003180001c1c00184041c006008000203d401444194899403004420700703a40c5044a09075a0396003004108030b451640c03407501040b0701640000304900c2004101440e0f85083c0b168500320b0101781c0d615031000070038002c0ea01d11485a0100d003000514030380310700c54000e80340b43c6540740c0342c600e03500d4030300c0c45142d050308014100550403400302c281000c00a038035002d80d4030f1a0608210028114480100b020b000e41c61258820b0130403c6200403102c000c144 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 305145971 1250 305144721 305144743
    0x12011401080a0911150405090903070227130204060509090606010f02030928050604030807020306060a0b03131110031b0e01050d0e0a0b0103120807080606071b03080309 74
    0x65030741507548005260003110700340c240142c0f0350130750702100c0a501d242140c501c842d550080700e125403c2c0390310303540440e00c2c241044414400513400054420154a0312401c000751204c0074126100c585e100c01e1450f0403041202411b02c440740a01c4010107404c645d22900040b0107020050a071603d0ba18080e14007580d195003d90b80e1070b0110740b103d107101da10103101004039504000c0240048040500300e140e08201e02c5d12a401400400c90310300310100e51540c803240180000d50003078180d40c4c3c403801e840c0100b44c00c0c04806001d103842904000e404000311007126050766886034058040d90b641d201c1c1750414407640d505074404580c0c8101d9420084100075019400b030007441003400342c1242141d0400005440300c069002e405800306105100b020175004e8030b500b00c1d080d0710903164181e5100f0117083d0b903840c401600a0b041100c1d807001580340c0003001940140450360040d89403400c45400d0030302d180415007512a080380a007603020702c583c01442043c2021921002103502c0184940d0ba440c02114030f580700d20940d80c1e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 305147221 1250 305145971 305145977
    0x90907050a170112020108040501060f0605030a0b03070e040618080307030915090b010b0d020c01020417060a1a0f030708100203010510090e010b0919090e0d0302040f0b0f12011401 79
    0x600e04074440c8010b0781581c181c858603c2c1c0400401030980041d2445c2c48003c0c07003224159260240854185c1611603c440200100d4458540b02e0602d4032681064035903c044840c003944c0030f030200704100d10715900007541003038000200091a1125200d0070a000529100c0038000b05000804c2c0000160705600681c02540181c05104400b00f500605205580a00401401036140c00340140548891000101034401c400e940040c640401090001c1c2aa00243d0085034801087c01d0315007a2041e050100e940d11201d10038041111300407201e03c1241080500c82c841c1e018079252048891a81c500b081b0b008050036101084982521081310044007a510901030740d402400b82c0c0950040c41c0340914008010341d0643e840c0c40308242c0c20460001c00ba40c0111004035401013500344003102d592501e01c21a0040d0014002c081207159220103490701c1c241038031781ca000405204120070040040b143e82500c045d01c0d6024040c0b40d480600c00c040b40800d00030f4035060180110140c1c0000390348450408141c02c42c12003a2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 305148471 1250 305147221 305147237
    0x3050c070f151409121b060108060610110601090f090503040905150306160e0a030212010501150203040308070b090a0c08030c070e070210051b0d1a120703110402090907050a 76
    0x903203440e244082075a0702130b130b0b070f074400781744000c1c0514940007a01d10740700302c0800c5080110b042186145012020703031011456410410602040c5d0900d0909115682d0450405003030202000407000d66a180505c0b61113100c60351500c0c540c02148944d00171100380ba0b0064221b03500c0329140e0382c0050060206482c0795294030070307040010346503090204020b442141f580c10019858115174400351184410341680a80c0842800404001a50b03200902c1d2800b02c48540002070660500a140034500e03034144400e800d5510600040000500f100102e0780d486500c039965000d103440d40201345140c02d160b1003004182061660003c144060004043c08419000108035081540c4e15001c5e00040f10f419264000186c116100305411518641c00c0980c102035280ac03111041c0001c0d40207a4000d40128100c0d04107142c940c2c44000720010b104802c0c4001d01d10440340c03d600c9400c00c2181c26503c195601c070003849a102881c8404071607485505807201e2031401381031000c061400d2072000781035902003402003000c00d00e10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 305149721 1250 305148471 305148491
    0x90f01020c150f0706020315090f060d02040207140102041d01060c030909020a0c02041109090108030405010c1203060807380405040f020c0706020a14010c090603050c070f15 76
    0x5103503601d41c60190000810003411000b032541640a0140345003a0039040001d4400110036200031445650744c01d80d4110803900e005c0030040040e10161440f078900e920001484001d550302c0c03034642c2415604031001a600c4003649011400c1c1080d40f032000b0407552011900007144920b49200500c61540c1d2001c49815a8072440c080c0c0b0030101c0d1000142c0042e803000018446601950700400c503186040c28001c1000304103078002002d60703422003001074442001241000301790a1620542e40034100c6000554141800d02c00001e1030245c2d40280900903056030702c82840d80707034046d90205000d000030760282d5500684a00790807100c405a440480743d00b68504010300601d044a46204090700d02c00300140f45443d14003803c1001400b0b00000e80381800f9820051034180c0b09003080303010010300e60354011b0200d8142d5070819034505049511024840e0b410301810401d060741c40150002600c00f541400201c41d00c40021314a1a80910031008044411b800301d00c405103c0c05005032070051100c0c41e03040c0010310003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 305150971 1250 305149721 305149723
    0x3011b020c0a1a0313051f0204051005070f0204021b0a0b150904021e0f0d1101080108030316081503101e0608030f0f070c1811271504060203090f0102 66
    0x43e0704441d00c041400841d0000c0907005100362000d0141084075025030079140340c4039841c40303a21080841550b00180801150410500049040301b05007030040c1480e510b030302d610442809250000717105584c00203603030007001d02c503200710b41e40c4940c0306045030070340c044130b00e00380d6801d5500741c4503614541c85140c02070070700340350070329405205690240007080c40c600d2407030103290394200d0b01407001d910003420501d540c40c5e5190f01040d0309089000350340c50404c0000b42e000140118006810200c55a0410001c1018420407a00c0b0f030b04003049986040200c80e65181c7c3c0c4e800f104411038210a50500030500c012154107001e4200054850300b240a02c4406000c682003030b8125080c2c0d129960040d00148154000e0000700c1c0c2c05002400464041c180c9000703032507a1080b0004903035030046801e00400745092f012291142c450511031030040b40c0140d240408425590f010580c030005a03040b5403450294950f43d948030741c07200c01280522850011b031683c5d201e0901070740b240c1180100c94050f05c071001d20115a588 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 305152221 1250 305150971 305150999
    0x80c010b0a17030a0c032705090108060c030c03070c0b09010207031812030509030c030312220f02040b01020c060a090e100e07050a020f0d12050f09100b03011b020c0a 73
    0x10b0007500641c40c14a0400c41658030400c00344060b014004030000b00642681e115902c8400b4030720046503014440c1c01d01b020030030442c0d01038100703011035445401044a0480754100b101d8003c11909a802c3d201d5035a00c2048403040c0001100804000e251018407d20141c15005402c031103200e07444603100306e49884e0001b01000702c1b078490102182caa121510300440d00600003042c0a03031010f07040c3c6240c140b144002c40d18652041d1024800010300104001c0c280801c1c14114164154404c00540c1e081c9940e01c80394400002c01c5406031042d0b90714003504505a00070070800b081400041c0c09a900d4201d00c0e4405080710500384100b60501704504005000742030103840c8030081c0c80d00b40103c150780391101c1c242100d06402800d541020b611032014141080d8a0400605c0d071880342541d5109030422600d40c0060a85801501a451150f01103042c0f092481d804903d001c0e40b00395041001075000c043e403000031701502003a03001401c407405400310005201d6011070030b500d201e038044c0da00b0f9601da551017204801d040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 305153471 1250 305152221 305152259
    0x40c020f06151c0c0e070302040302011d0d0f080a09050102060c04120f050109062016240905010c030507050a09063005100501020a0807080d0603080c010b0a 69
    0x74001c04006556030380c035200325050b141d038050120511800c41d5209012400d0b150780d030550f114003902108003c001d05441440c0d0f8056064a0150700702403455001a113a44211103070a01900341001401407a0348900d0a00321940750451a6105902003508010805502c02000c120025285020201e03040d4000107609d4001e42c40250ba551a05e03260100502d54a059018125800e401e062000300c0400d0090194400c014000d180c009045607502c031700b000016481c51011342c03110105010080480028032020180e00d41c00107030b0101640031040172400110801c641c04d2501c40d142c84046002d109055008910341e02490324100b02d242c680d400f007a289405502c1002c400030301d12560900440e485941142950645e24540301c50030302c0115124032103c0807214844c8401c664031810484c840d0050030b2500010700013030001d00321950340c0d41c03501c4005100f409000b038841c2100017500404e02000d9800b000007035800030a01c548030500301c0c1c113042c0078111444006210b10740303405020504401400c0014024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 305154721 1250 305153471 305153473
    0x3090318050108040f020406030b0f010e011a18012f010f05040c0b0904110a030c0e0a06170417120f100e07120e0d091a0a140f040503070b09040c020f 66
    0xd559660b07903542c07100c105c4581207800a1300e81400000280350000c1c55400792031a000050303072640c100041d40e5009001640019150903103004080500c2150a085928844460501140c41c0d03145d1070068803621424412205501241d03c1514660120800e2403c0c0d81e8002c2d500038480700c1e004ac07040c0c00c1550710a54011701500f060a100700501c61032140103141a54000d8400b041440022481c107003680c2040417901d010940300c40e646204140c0c400f23a20b2502d0942128502c501c2c9081080041c00311030300c2c103000b5442800450104052184142900080d044900800790b920f40132104440c8040b10103442c0e041015003c0c0010444a195090700c0e40d0642d02c030303045035607010b41d00c0b4030044402d9407001c0704031991155900f405c25104002840300305101080c3c3d0700c800306501d18000030486c1d10781140145104900f005e01400e080301d40e00c0983d8907010542c8051140c1c603100c0303a5001401522a03a441a90305204019002900039000405000305520480341042844036055041ea222039054000501c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 305155971 1250 305154721 305154737
    0x60d030e0d1502070609020310090b1b07020901060215010b0a02031801172d01120311030f0a091502030c0607031a061602030706301b030903180501 65
    0x1060400340980307464180508055950b02d981c0003041c004a07404204190341c81900c80303209000f0350500b04600040b00030400780c00c1240340c16035158018413510180c0840099040c4010300140c030640c4100340c0314070303a800900c4901656940c4c0300c040d54a0b00240c201e20310510307400000054035800032041c0c4d840c00d10035170041d514085640403001c2e03903107206032015414088241c0402e0250303001001814403c0003803100700382d6208000203100c46c040d25029901c16050345000d0040c0300c0c034101042c680310f040b681400d00441903014201d46500314007a02d0720680034160085600d040d4960700450040440d41c0341002c50303c91a10000080fa00c1344030f90703003a060300d81e0300074000325070394900c29400703d280c01600c0003129002008000008849900103c2d100010f0b6684000c1d410941c0350501c501070042c0100e041515480d00201107100a18400c170b440581e62054040035481d0309041908400c01c540c48454003000007113031b20740024000704003860050b80018070482e8014580050f04801b1011346d44140c40c3e10724 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 305157221 1250 305155971 305155997
    0x4080709110d090f02010212090d0602090f0d05010b130204030302031815040906030b0f04030207150302070b070503040b010603050601020a1b05030d050c1b090610030b1005070b060d03 81
    0x600522811501e02600400910285088500c14418500d2040c0c0703030f40c040469507000081c5488010020000300035000c2214400d03565910040800156200d0401360300d849105001070080c10320007183c40e0f0400184101c6100300007040d440413504890859565103041d89106215049005500004015910802445000c401c4d400c070408658040103000c694000c801c0d4003c1200740d001380e8800c4048a803240320500c100204402610380c403116072142c3c02060b1030582c0300255601c0481c801e030740d50b890322112801c9540d03120b43c048804068201c01c241d0034030300b05003000400b198401c071010b46242940500100d5982d00ca40500c5002d9901640200342400241e103a44048124010110240181c4440c0000d10f54a05200760844038680303865540d01d4070041d014003400c0100c80900840d80e0040c90810f800030f079850703200c001d420642c10b5400718940403000d0b81c254000c000984005501481c84c0c2ca02da40580e074024001d003555803207400e00120716100e0703c0c00e00c404526890b00083c04100030f180006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 305158471 1250 305157221 305157239
    0x1210206030a0e0c1905030106050f03150a090209070e01030e0a02031c0203190c2a06050d140c0a020705030a0506062206080a0201170708040b071101020d0c020111040807 75
    0x240542c002030058400c14200103000a418105c141c00c1c0710030912000707004200520382842140000c0806a0f00c0c1c0110081c541c0009880e031500502a02160000c14003103000d030078080c4e1100f98143ea0240c040c01060070180000381910034500e1584e03000031b0901d00060381c0c46601040c0b20448070340c042c1c0100225444445400c02119030b8540c41e40840c481801000b28021841d00c015407007401039294420514401e090020b0030107043e00d1088c1c45156120301d05038a00c443d41000c041210414605252030718658414038010348000c03108140e84d0581ea00510070714800544c020100000c454084401090750f99007855100d0f41444400303840c80e00440006480390170000500c15004013030b80404030014100085160882d0f9160300080c845178403800302d51003107507005840040303401401c14205440c0d00d0440001480e070100284010305805444012400b4980210452080000350a000350b40701d0f26005801001450b8800b0404015820000415800c4218208860958001001a00341700c0c0c200071410b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 305159721 1250 305158471 305158481
    0x90902071b170d0e15120f0c130b0a0507020d03092301080a0203090a0b1905010b1204030c06150e0604060e0606070816152307090e13081201210206030a 67
    0x145404c180200c500c1155a0001c1d00100144011b03240901c501c1c0c10800d47c85104c4500003800504500c1081005224101c2d5800c1903000b2152095201551810b50743c0003200d0764058600d0081d004507020301ca0800f015084003101c0b0035102001c0e0443e600e032045500310024444400f40d03141c08601404c1c040703450341e222500210b40c450101c404948100b9090340d0781403020582107034040fa41c0d10240307080c1201e900c9540182c40c014845001040c0c240360034001780c0264100050001000d000030b2800060420405400c80c82c200d4500d641c0042c1d0302d40c0d503005101c9050008407421882039140c0803000c102d60509801c010b0060001400850400300b4594442c8541e07845200380d000300d00101c5003101c00203000c400e501d010b4400d0400002c20031030f1030b50a503110f80500304140c0c0720b000c007503040420000540c403115090882c0e80180303094415448244a100c955903800700c01800a44000554071b822130380240c40e0a049400113101c032104054000c2c40b40300b513158855030080d031107181000860110480c0d0303045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 305160971 1250 305159721 305159747
    0x15040302150c0a03020703031803331508010e060408030424020313031806120f110c010b12060105090f0a0b030d0315050109030203060f07090902071b170d 68
    0x120b071a003458807030030a19103c5940c1044005030301c007100138820180d00c2400c3c0c140d808004061b9200007401c6584a250040c442c8040c07400c0040d10240380035018201d8035170710945404507141080310b6500002071581d610740074002d80c4119030908400c0c0c550250005000307845240c01c60945403c41e19103580d188500e1890281101c20044456041600541244000d50090168607410f030b443d01a01d140181040c158040800407421000720b042203601d41003005100d2004040d0000200c03c0039100d160001005070074400c0400c0780010075040c018180c1540300c0c040c0707098121411f184042207021303019611407090144503000130854003c10701034803c1107199030300070003441404500302400e10042413a140440355a640081d071140441515214090307200d8018000a00e0701082d00c60031030700400c1d03070340c1d4010f4240b40340800d120000481451040c3e5503400a803542a1040d55124460704100c16914100341031984868062400016003a92080c2300088070b002c60303005480c0681401c102a1609814001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 305162221 1250 305160971 305161009
    0x80705060310140d06050f0106030e0109021f1701080703051c091401110303100311010309050309061809072304060c060c03270b1501080a0903120501081b15040302 72
    0x31691001590134000c180c81f844842102503055890b0810040650b02c021b207161120343d2500e40c800025840c1c3c0032501101c0c90000d00d880c124081c1150040f81c09409403040c034540d100a400001c544204042104411640214215900031018806071401100301c0fa01110104401c00001c10941400d03140305503501c041410140284030025000034156442120340f1001802d80a07800e2042003008680c0c1b02854400b0310f010050b00303010703645240c0e403440359a107654402c10011030729131101c85544c00a280b25181c0078103541d005081440d4042c15980c94812038452680e0301c806c1c0b42c006c80e1700440a0b0307011a5000d40d40c07060440c109817100070090503001100410103446000900d0b050720020000c1d4601010064915042001070030200308801d0050090714030300702c0d4007129108030303a44a0144c940162185e032001a0082c150b250550700780c14021141461681060f000082d6001d020400891040000742c40101004d2100c04000000b144001c2501101006000900143c104291401c43c0048500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 305163471 1250 305162221 305162239
    0x305071e0519030b0301110c0a1b0308070f03031a0a1214060c0403140c063004030c020102010b240915070b071b050303040f0204021b010608070506031014 68
    0x41c144a00b085203004500100e81c40750140d1071181000d200b81503210042035111410300c01c0440d10661100a4031034054094100039440b03000b070301c404600e184002c0d07900c07110603a0358040d21701d0706426030410302c0c405030046440d001c16254040d01000304007801c0000200310b5038025082c1081e45601242c800010794290f680d5202c1e91154400410500f401924180103058440d495894100184007180d0140841a04030080000301d40d11a80103940421003d0214185580c00780c2c1c0151140c6050303140380703042d00b05a450a0206140e0004141c0c0398072030007030303000b031206100d490188910034072800c60140010452700a0003401e20880d0000c0d1004180c0203202500c40046907514a10540082c081503a0016100040c00302d440e411414120052103c000d41c0600c01c030103900e80d0382d16400014400740c18140d4003080e450441d607560b81140d00340303000c50450b28102c1e210b003e1524028082405018201d20441c007010075030380341c6202580d02c9020303c010740c4e070f4100e802c0c21440c0704044440400d1a4001700b40c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 305164721 1250 305163471 305163487
    0x60d0f151508010e090c0d14010608193008010e06271e0103080307030b0d110d0809060c060610110604060b0a180203060f04110a0e0114070506090d0305071e05 70
    0x10001c0047c4640590050312891402c1d201c024215050fa60141c4019800310105082d0107000f40b04489001c6e07000b180b841d2262003018080340c6a00001d0700c1d00d840c41091860f0b950f083d035410081030360580c2c0c0c1c1c4508206081e034400d030920090000310044120090205e1ba0100c404121041b1000d9218010450020703188070400d4031241c81004c00e03001128a81d00101c1040502a40b40c4181c0c40303664000c50f2540507505583e124418064604107600c0d0051200000d60303018051007100300c3d84400300c040c200c150740700c4000030180d8a0b0741c01551420700c9901d9042d10359418038420480700380e052134004050400390303c45540d440c0c000d00d00300460540240501c0c0e00003c488500f0a6000c5410f44440009a80c91402200300843c1408000e41c10b840350b8900101080000403c00940b002c091883c2003c04522550a0060b210340100c6129a02c072020001080780030088045469070088028074200c40c0a00e0310202c058080c0c80040f14040005400f400408035411070b0003c84510100160824514007018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 305165971 1250 305164721 305164729
    0x10b1e090319060e0d0915020106051309030f03111215060a020d11060f182503020312070b130f0b0103030f0e0306070f0e060d0f151508010e090c 64
    0x2d2500145070341103103000c0c000d05112281c0501c0080f04070341ca01402210505100c0a4181d420703900500310054004030300403c041c0c1c001d40c400000307014010103042941014210100103008014012000244400103800c1a18068029040b40340b611080342d44c01c0180441d144282140010801c01c40d44072549007130700082e101d02006081841d40e40e4040c00903006d00c140d01801702040054801e030745501c02c2040068a00703080c403160350010040c0c41194040d1004846007403401c4850405205010442909004028695180e401c201c9100303074140d0b200c030050424403000d94000d04c480600000b8141000650540d810000ca1030701a01c0b42c4246200e1007866210510b4400342604124081651400042c20b01d64000048014100040780103024900e442d25000380352070740d40b00031101402410807a50202c3d56a00040d00c0307030250b000a003000b00501c0718424001034110b4131400f07605044040000b24803403200e0b2242495400c1aa00c50017501d902c1c001400307410f13140081458a503070059a4141041c2e5031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 305167221 1250 305165971 305165983
    0xf15030a120314010b0901050d05070c0203070b2106060a0c020d140d0923091801020c1b030a0c150302070206070507090c030e06060904021203041e05010503010b1e0903 74
    0x101e00c1d80c001860303840b001142c4904101c10b03086000720f54014040c00742507a83c050200d07004540d42c0c80c00842e0586400300d058a843e414010001c1d80b6015944000c02c17408454006003248494401030841489000c401005940d001030b20480d4000c02d040100c013000d240501c403401044e51000c1c1c10b510315400c1c5a11108542c0300c110b444482150000007040103600da0002d2100040c00211283c3c0310079031020007200c0015401c40501743d000d04880b0000a5407441c00f2002c0d4440f04060074025582c034007a070a00e5644412000300550880210000501c80030b00f4009a90b03000d41d82d001840034203c500700800d042c052190395010700d04040d003c001c40001a142e50001e410001c2c820002081d110b42408a21001d9410284da003c04040c42c0007030100081400052803a0007543c1611520890b4442c0e001051090210f00b02e882c003180302c009400160004c0a0300c810b00080c01915042c0000c0c1c5d00c0c2c500440300e6100078841d03450748000c140980600181d01d410007070303040b00c03e1442c15443c1c51490400b20f0708210b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 305168471 1250 305167221 305167253
    0x9090316081207080114040914030d060305070803030609011a07020604060203030601021509102406081e010b030606090f040f150807030512030702030706060311030d03050f15030a 79
    0x76010440b0000d80000214071600316000e82401c586660510190f500084521243c283c40740f07407125036a03011310072400987e599809428041ea40d90b13100c06d4401d1000b4017140d100c2120305204803000040d5004010003174074014040285408485e134605185003200c03400c00c4011481101003080102c2c010b81d182002040100349680145481c0e03d09070002a0501c40c07002a520300b0407203404100004840c2c04120480780048500000400c1c80501e0294682e00301290444440b14000c12000f140040c0c1102080b48100040f030191624203c20b001580e03c0b4250a1003401237200040c1f0200740755240000c0034010312503020704211203d51108000034203070380a98024800190395400c00d10380e075104d00d08041e406014a04014105603103180d44150b0354196140d541c0790f0b00400403001c940c88510078401c4840a40d0055028002d468485c14000320030703940d00c2c9600d4400d00c0761440311907000d400390040500c1585480300340d0000342c0d212007041403001c80c3d1600c0c8907494003548006500260300202001451 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 305169721 1250 305168471 305168483
    0x61505180d0c09050f0601020d050a0909060b2d07140a052b140301060c0c03060e031801030b0a0e0604020f030a090c08061603020f04031e02010f030b010e09090316 72
    0x20030f19098114045450161030941c200c4482400c02c10aa40c0004041c50b251102d8030b07060703940f40700f051812601541550008800c1c5e600f4480000740c0a403011019149040700b13a000c017030b0a03082c410b018904001c0841c00110b4542018800e62020881013403403d04080ca21a041c0ea5130300c0c07a00c3d0344403424181d901c4800b13011241c0d4480d000900c0450021003082c4c11080b401d1883d422100460004c1441c001407141e002004290b540034000c101c01100c0f030b400155032002080c02210342e40583c094a81d004500f00309110310280290800c10743c424024070103444e01c058111510a8102180d040d02410001c100c10342240d020841c420031014205e0003513110360315510340000c0403001c51802110300c4100da848041c1e1036102c02d040c40031040e10b0700040014180c190400590340c0078076201012650141e5030018040382e11100ca00034808001c1003600c030280e80b00b6652410040c3e0038030b01c01e60031181c00c400039900160344c007400000c0c1420141e84880e084540340003264103004d03c5400c21103071290070303803000c90728 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 305170971 1250 305169721 305169743
    0x10c08030a0e0706020f0604150b03030a0c060f0203040b1302040213030507050a0b030420010210020c0d030e0303091f020d0c120f05010b0d15090501120b0a061505180d 74
    0x140c2d03009002035006426a4800341c005c402d081040540d0f0380001030310140100855200812614107a0341c00b40c0103208015081e01e8650140001c06012311100320010b9a034181000c00d80d8440d907500e0b10849114075449484011280c849890322040a400400200d802c154200414500103100400043c0110f106000400e042800d010a00074000b00c1c5a03c1540e40203000c0c0184800251010f910705403211b06041c020502c803204400403840c0203810a08030075200c7c030009000344c400c01c000c5109264a066a1420b014026000400c540e41c0e1108503041980e41d0003425005040c840c122400781c040905001c1c0150038070000e1482d000860744045405004100a1101149500340c64042c030000301c50129400c12080d858102c0c4280a4411900c00488141c2d07185240341000020b195200c02400080030104441d40c0c56119603500383d20000c8094034140c60210009070f0020543c0600c409445030391b48414042c070b40c48102651581c002c8188000814144402170189488807160028118050090422 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 305172221 1250 305170971 305170991
    0x30510051f02010605060c0316030e0402040b0306210c0114090402030109050402090a06030f0f030c120509120a1709060d05131a07140315040612051c080411010c08030a 74
    0xb0855007251701a81c019030003440810001304011081d581c00c50030010760b03550940742c00c0c6002c4416003110042164498408140421004510406980301700c10588019402c1c541d520020f0b047c00300d4202402ea003a502848401e00c0c594800e50403c8852002140ea131420211200c00040590700240c01c041420303607a80c0c0400c415894646000381e008004000100111421501c900180840d403200c05000701113503541c0201010b00c01c6034040701c040d0b00045600705d052035524004009910a51010380714103030313100303c200c1c2040010a41003445075012100302c1c102c2400040c02c50301c6030842040e05a100f1428010402e8429903401900d1241034800ba138002000c01c9482d051280c46034814100c0200ca4003281000081c507044007200030f030042143d640d16100e54131600803901c0c0d0f262503100244c001d401c0110002e102000d42603041d642e40d01c50015034144200e420003d10711071006140103030000310400301041c085214070042d071480d0f40c4107140840f461005500c40f80c203180d00c00d50700b240600b5a5001500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 305173471 1250 305172221 305172223
    0x60f0e060316030b04021c020d0c030b07090806060d020316080102120a06030b070e030c0414040b0a021c1512140c060c0a03080a150e0403080f070c03030510051f02 72
    0xb041d103042041c0b40c0251508507200e4403030b1642d008000070b000328809114104a605070400014203aa070041800c07441000c50702d0901241900f0f44401c407419001c076004907607035030b016610708010703503000100500315a5a134000700411980301805c01c0e0780500071150b11413200030418503070b80058000790001507650b460300602d1030054800140f2001c1c100f49030600c284001210092400d4000c0340c1d91411a0001c0303002e00000b414215034840041d40b03d480d060a2000c00715142c1c201c03078450782c002c01e107829050755641e0854082e0300c01c5521104050040702e440b0082c00030309500c44010201000440602580c540c150200c051510000c1607550a0551351444150750382003006807110744003a2070315070801c5030b1101c0e1b2a035141c581d050001c0c01d00c08644006000c0903019800861300c1c4c5000c80095554076592100038007a54410b450681c0043d40380c400290845501d034500394000c4145641c1c0ca28030b409036450480080c64043c1c000039403e40384040c0047c007580c0d034502c25140c40740224a9028000c020701006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 305174721 1250 305173471 305173483
    0x9100609050a0b03010308030618070e190e010506070501020f180f0d03020c040b0d021305060a0608011d091e0c01120504020a0b07031704080a17040203120a03060f0e0603 75
    0x1142c072030b80456900740002403610084d00c0c1100d40c0000340c00e46030b880d0440058605084140810000f540e54010441e88a034031401d81104d1070415690402c1c002100c0000740344680da02d005129003010303094010030440c14150003e000807800303003000506107024a8000c4c01d65511031410000c002000d512201882d10b400038510310700b014211801000d4901603030f4041d42342c2142c01c101600c02caa481c1e0000d5044d4590b0f40408039090341c028280c40070110f42402c400000e08086d00e0780c43c0190313090907000c582039024203c06816146a210b07104c0a00030b02e0410800d20a10041c0300b40000d0040041150607620100580d00e440b12920b0040c0440b07018060004000641c62850203c01500382001d101c0580c8540d98040d0175994070400c540e541e00814203056413030318907030000d2101d611050000c01c81440251406840b000e00c0039520701c45041080c910590b80c1081c140e8019506402100b0707001a4031540f540204911241410089141d0780e44070380080b0040030742d5100c04c1c172928456082021524050180c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 305175971 1250 305174721 305174729
    0x402091303080f0703061a0d05160207300c092706110f070605040b060901051c0c0f0305060405010b010203030c070609230309030c10021b0f09100609 66
    0x2003035444445450003064104054280b10424900101091045110350043c00c09403400c1084007514000e01010340c801035000302d03000f0340f0340351420010034141f034521440c1c04080b0400381d00038207250741424200b6001060a4424442072025009049400420f106e0406002da0060043d07080c0c151808075200f05031079203d07a0b15400c404809000c0d4080e6803158504807170141e00181c002074400c8507240089603500c50106a0000e110001ca451003c000700c5400403803041d8441c1c02024415240c40c010f2204048003809115405a041801140003420800c2003412f894086c148098825036103003801d0b418080b16400941c0e03076400480821007480001d00843d0001d0a081c40154554070f0311005c1000d081c02540307002801c1c1034807002c01308144066103500c00403100c1100210504081001d1209603282d1122880601901034040099220b1906184040c009007464000d801c5644480c4031084195101018040c0c2c84500b407130242100c0d88843c00041d2041445010b55005e05040a2010b0841e000701d1340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 305177221 1250 305175971 305175991
    0x906040203011d0706050c071a1305030715080a0605040e0c010905030705150d0e010c030c0e010903020616030318060501030b090f0703170c1209040606030e03030103030c0305070503030f040209 85
    0x161001c264001808808540710b501d403a5403247d00354410700b41007214991044522003550000c5c0410700c42200000c040100c00003000b504410740d03840a040d00c4003858820b041e1490512502054080e0103466699400110f66200050141e101c900080032904074050340e00003944803a80d50481542c0150316000030b86022001031411601d040001441c216404803072994840c1c01003007843c501011900140106814400203101c890071045000b001013860032441ca00141ea8503a2102655025004c11400d5a4024220300e28240c0c030700c0b45a800c106880101202019590018100740c100c603001000600f501c155804261035246003401c1004a8015108000d1904003048912030310b08001030708000c4987c00314411403e100031041e62030f5140038280e00c50050f409010300343e4600582e442d000780306c900301c100c1e000c01070543c84903400c03403c55800d0103140459620070801880460700400803094101c0c4a0302d412460003e881c5d0312182990401d031110552203074000d00340000c500e4400440c95010702c12035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 305178471 1250 305177221 305177261
    0x7050a2301050f01140307090c12060b090a170f01090f05150c07060b1f080405061812090418050c010201060902030402090402091005040e2b02100b0117090604020301 73
    0x4154140d4620610445865010303a42c5d80078402d88040c0858401481c168004004000b48030034043c208094040a041445c0c0c43d02201003520b141c4071040c1e9210500c003030422101d00d0305081c052042049240f03480c03c17092098403618070300e000c1e09016401245100d010240c0355948645041c5207000d2604204d48280300104041141c0490b000040d90003490300b00c100400d9004101c0c0120f0414024050700072006d903880340d4046e03060341e000035900d40180c0c41407080703d1051b55a510a03e8050500c0100c180b801e4102285809090000202922134404018800110f80201c001c00340c401e0014400103c42031f070080c00c1e03003542640e0288654001005000e100350b1440c5801d0b03001611a20005100038400c40d80b02000c1139022452600321000b42c000070b84108031000100b500582c0d05c588406080c000e42992034420284d01542040440c50700f8900d400030207030800440400e902410038039003182d04204c1c6501c1034141180d00803115130f00402c40d400c042d1480742000e006050940e581a404074070555015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 305179721 1250 305178471 305178481
    0x11010207060c030e041401030b0610031a130b0a030f0b0a05040c0e091c0c050705031c0503190609020301061805060f0d23010e010e0412080c07050a230105 68
    0xc05044001e041d41032030a20740151310383c1c000400505101901030499044200040704021300b00100314042e03c001c8070ba140200c0c418407002c03002e4514a4540c40710361748000b0304030082400c041c002c128810001300c4010681d2850382c4041080c1d007200e644181c8002e401e800c0b004051003a882007027138002c1801c11050000b03141c1354403400c3c0d00240d18820100e0300d9145d02d00040c1c6280b0144042c0780030404410904c90a4014200c00811440c40250140c2c1e590142140002e010300e40003c0c0503000041c094550340c1020380780c84040d81c03550001802c0044180d0350310807504030700201c0d208800241100c2c42d40140c0702c0d410150001c0c500721408003030380d4900c00d12020900c1141d50395401e0b0b503083e90000b8125035a030303580b03c00f412024080a081150a145c106c0c2a030b03e10200030f820045040c2c1c0c80040d00c02003107aa80e050300445044c0c2c00da5028148070412031031040310621980348103501c1554040c40610306042d580d110b078038041c1c100c00d042d40d14001d07101c001c802e5407a040c003004613004140030080c00b41e4106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 305180971 1250 305179721 305179727
    0x40b15090103110f09070305100821071b120b131104050c090409050703020916050406181509060801060302070c12111c03182402030f04080a1101020706 67
    0x2040c0409000d81050841056050b07450125840030303864050002d841745d0421800140250100350f5a0301d851256060307011524a000084174201401e080c0d01100d40c007908032034171003083d90210000340c0e50045100308000741d41d50380600f800014a1402e060b0203050255080415030140060300c24066520700c00f62010124003184051842104202c50002e03858a944200b042d442c031074485000d80047c14007003c0380920401255a10459000761030944059403620161140c451441c4000c1c401310300e084c8800d02400e07201d4060106103000000070810110748a100184800a44242002c0064044101440320650202c05240100701c1806c056051040581d0f90323031078528080c014020b003104080c00080c00cbc046034400e20714410301d01520f805483e02c080001c00000043c00c1c0000d40c041860840d154841c00300740701e41107040302c1c400440360400e41035207440700c8038210306a13654000f184003c0c4141201a2400c4c03000f0300040c50340c4001002021140e103021750500e07141018860564010b550200000c5070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 305182221 1250 305180971 305180989
    0x2100c031a010809030426061501050409051b030a020d0e03040b1e0d02073503011202010309080309071a03090705100c05060a060e0a060807170f0109030503040b15 72
    0x7024203244800d55200d00c0c0007841c50113180d0141800030f6540c8070b1510b00c1440b13041c484101155503000d0791025542c0302d48100440e20b00c05c40690026100f048100009411680701e1604502003001c0001644101c0307468141d203802c1a110b03401e00590029000f200030503184520090506594050b60605107031240b910818003130208803512103080520484446240b2104440c002c284082c421501d03039510741050f900e080b1600354048002c0c2034204500b401c40f0310b0301d80610b8007403a003000a640b85a09180081c00c00c051b0f524401c906141c0c42d6035000001481072030185201e0803204009080c00361400304c540c0140d24540306070354162203040041c070030b001d40046406000e540d0151110310074491449011200c0b0304d440b1101030002d00886081c0a0810003e400c004201d4034400396501480d26112000400c8400c00d1081d601140d11050080043c1c040350140c8940110401040e180d02800702c401c9242540c0000c3d00803000608000200020041c1c18001c16410001a202e4000394594400128580c0c403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 305183471 1250 305182221 305182271
    0x3170408040e06040b1e04180c060215090319210c0f080c03060405060a0914070f050a020a0b1b0c06060114030103030c0b0c07060c020d0e030c091f05030304030302100c03 75
    0x30641b000032002ca0301c031608400450700042d4400c2414000c541060740003181640518401070007a050b1104408804821090082c0c007854083c5241929003122040402d45c2c03044c0b082e00f80b000c0c100c5221100c4024410340512110355041c0414010140d00005001100f03518021f0148030302c81051150030b0400d0003e4071340c4040f003510002000c4e11940300041c0990600d501c14582035003000b807502c000c501c980781010f0044820ba2030310101989101c0040d03600d4007036440d0300300c0164009400d110108000c1301400342c0011240e491003d110008007484802a80090314504981d0f1119041c41781a50340088202c2c0c8606001e52410305650465074003d098a40071100981070002501c0454481c40e101c4049400307443d4042400c000b081a03050000c2e4546480c3d038542000b081c0c0d807510340030b01400d000c00d12501020009129544581d95080c00014403e035070305041880c0102203001043d10785040004001942c02a0000d081c90340716072040b4000d86a03040018010582807003100494884402c020842203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 305184721 1250 305183471 305183509
    0x609040614100509130f0f061e0903020c0a1d1503010e0303060a050d020303032d071d0a0b090103110403060e03030f160c020103020a020c090c04061707080402010c03170408040e06040b 81
    0x84520ba042023000b0b40b2403094102a031080b80c4540c000290015440207440380d01c030b40c084e200c00010103c00c10408401903c00c2540d8001c2800740864101c46810300e427584414070b500d41c0b00259114002180c2101e0304928000076030351000007402050701d0200b00850091104440180000c207550b40425100d000140c04140040140c000c1d81c403150803980c440c050800c40c601c03854040352500d00780052214800381c5040c410017002c0d00200c445424410154015140400a207030f26221080004500030000c0745c50800500b4420b120200000351140910031300c01030f03180011612410f1017418820b502d840034244a03800034059128511280e0854104500c054090070700584030401030405a0070203070481c0700c45900c41041d00801c210a80e070355001c2c1042d00c8030342d07640c1c416504074422249040c02c016203220011400f00d0300001c0056106009400c0c00e40e1203490140c43d9183c000f41e0a07480c40d031055030111003824000c1400d0022041041a142c0e000c07400316001d203c54220800841c080c07420594000c452 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 305185971 1250 305184721 305184743
    0x12060a0302062b090b010303110115060f05040f060302040e0a02090f0603150a15030e0309030604171c0902010f0314180102123c0609040614100509130f 67
    0x15141556450b0f58244058840c02d00c214400740c0790035102e401007400700300d01244454541c3d2030f45480501c180c9084042072071f80d08014070b003840030584815075541924010014200004201c40b020480002d000b043c4a80740962102c3c10000740040800d0014501400c1501c141b00c1074901d40d80b2821000c2c1140800e48110707a4a03164480c01282d51411510391a03008100010700165003400ca644103220484641d404003d0f00140c01000c81e203901c82c6000580d40743e4010004140840d410342805e60300034014901c441d29203200066440503041c0102c1c6a410061741c2d0b40003540942d60481101c02c0f03410351603d01040300e031001d40140e05c2c804002070900c94170324034008898040250b00350304030307140004220029441454408489591041c081c4480d08240440c0c004909503503504480301c20070342d2003440d12031400c0c1e555a024881c40c90001001510744a4035608064208100e14034010f0088040f03605050340e2038100002c0c01840000940f9200c200c4140e141d0820100e22603c48240b081070344a0060f1032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 305187221 1250 305185971 305186017
    0x12a02030a08060d080a1218020a05090a020712030c12021c0f06050d0b1902070b0a020a03092a082a03011b05040e0c1213060e070b12060a030206 64
    0x1070704c4001040010101c1e0000030300d0600158112010120194550300c00780134014000c0c020913569180c3e118001e4004140741e0301403000d40391101070b071039100c1800e9100604041c1c0f940c843e0b2a22a000081404c08280c0d14010f819100741c0c0700d051403103070201480040d464500c00e000075031003440640504000c416a145103200d04501142c200900074076008090394140800c80c200030010403c2550641c1c01e02540314800c0b50100c4090081d5800290070603481d25117641d81c0b003507640182d03024180000c101640d902e44140041d040700711210709440350314952100c3d04140b0308019401040c5411040e4141e0051100403154001201c0216202c0300050200e40a284110042409407460060131003101703554080c144000c80c1e0202c040c00407505a00031075090758a41d0704c402400c0344201c3c828907411102020000d18401034440e01094547e22a131800180954000303081428045281c00c162030503500026484000400324186540200b000c41e01c0034015851a400550144600d58900c1e6030252443e01141d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 305188471 1250 305187221 305187229
    0x110a050102040807180b0f24040e04110f03060114220b1c0206120c0904050c031501093b01030804030627060b0d14012a02030a0806 58
    0x51264004029512a9111000320b6140c0392117004400701803c0303203400780c04100340601030f410040502610750910010080103014002c46644407100310200558544104141490700400c010040000d03040d94904081c50600c0070b84c00b1910586104801810700c04000e6900840c0103811503601f2030020311003850081c046210008074039074510001a100e02c0c038220300e202035004591400e40440b00c08080d80b41001d4119400f5102c00701c003a4110400384000a0101f01901d507898004400514482c10886080005800d0b98001c44d0000000d03e0040240943c2070306504186981a100342032254400d030030440c4038140d50750703400405000e03044081031138211103103440c849242d044880b104113200c3d9a1207003888151540903200440d1514a415a030808103610100168220000b4803124104440103032100c6000e407108249482e40314141c010028002601d01c00603920104020f400404ca6000320303002d080c1024001c01e060010602100c3d09450526400b01c02c82c0d022030041e080580507034a44602103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 305189721 1250 305188471 305188483
    0x10e03150405070303080130020109080307150608030717160515061302090105090f0303210604151203051e030103050a0c17070324231b090111 63
    0x1001090300003030000744800429820b040e00e000362940c60705030360b980700211000c140050300c5070300100008610445646146c4240d20509005140200e0095100c22515085900009049503000d0f4140c030084282d444d6130088200404508001d9404c010040e12104030703000c100c011540b4007910014200c1d180016184549401a0f044002c541c0d10755101d15031441040030588041e4892414000c03003030a00b00c658003c45408082c1a91090305152001041c0706d5440d00344200a83c0c1030000b4070401030807203c1c00c2c00800700443c02d0082030146050080074041140d91070b268000d02c1c0c2c641940244900c0d40d070035142c01c244540c149000c55980600c07101c0d00c0456406022540e410b11000000002800300000700da6a181d030003040c2409002d5030383d0b682c61110260700315907140103411280b400c0020406001d4043d81c0340b4001030086091605000c840307401c48029110f000704503890700d600c402c0402c40c40c04403a50f0026000050000004c86403449012602483c0342090400000d41d40301c50500c8024401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 305190971 1250 305189721 305189743
    0x140406091e0b0a020708151303110a140a1a010e06060309101a030606030c0112020c01020903100e15150f0d02040507090501110303010b04090203071404120201141305010e03 76
    0xb0b541c40348001840251160014414224248103040e0402086201e026039540540c014924481071080541c0d010b49500780c1c0008404502d0207544504070200d205000c00000d05440f80700580010003540c41c12643c1d00142c8003440505074603000041c05a030500d0703101d558001e0403c94481c0c1e01c0f035880b404101d2920240080d501702490400901c450700300035650003072400d80030842c1a0780b150780e20740301810350340c1e25101501800503464405000c240c00710303980200f154840e61400940b9003d10034021030320b070002c02c5600681d4655504500300c40b81701e0500800713a08000e03e480c2c0510301c2c00d240a06842c01c1034000740704c0340700f8100c901c03810700780ba80c400c0c403149105c59004d88103010520704004050302c50300e0b09214423408100c4110311598649004030490b8140d401181509080c6410300d21001d0007500014008021710440003142111003011701d01500c018030540409000c203c0e514400101030300f030b146809012b0f904061114100485041d206d100684074203180c0501440b90460000b440c0203030003e8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 305192221 1250 305190971 305190989
    0xf0201061d040c0b041e050612010303080603010605191706010e161b03080405010f090302120a0306170303041a0601050910090b040f030b0606030408031302010903060615140406091e 80
    0x30b0005a6000f001901e9903440d500802c206d806103643c0c5090001c503100381d640b15000355161a00500001340141c00340c680164003d80005446078541022038400040e40c851040781e010340200c10002004001441102c100210000e002ca9501d421039a00e201c0030040c1041c040354511480c0210389611456190445003a00801085140060308020740f6403601540d00751159400c00008103501c5201d80104940356a05034010710361154101004401504400c072518201600c90b4400204420464440381c5c81e0410b0802075075884c141460a8540d05910b00e1810035800b18a6003040110f07a04801568a00d0b1015184641281914482140c3c912110b40102c0d59110f40840c001c00c031540741003118415030b44504c050f4011a02c640f020052140011a001006c5207010000205000c0d01d81c02c500c00407901c18102010341980701e998036416100d441c0c001240282c0401c1ca10400300d607008440e0100c081c40140c0719890a42060301c014822009401103800e011464182076400300350000c0f5210042030340c4a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 305193471 1250 305192221 305192227
    0x204020d020409290a0501030905030d05010b1c0902090f040507081b130207080301170a050a11030610030b07030e0715030b0a0614030402210a11010f0201061d040c0b 73
    0x72100d002403098039082158040200865032003104c6400003043c0e250740c0104a0b0344100d00d040011005800d191608039031a01003072114505c4134805e8040d2070b019081480ca00ca8030b0300c8081b0031a19400c9050080001c0031410b043c41500540c0710440c4150308040307010f04144580d600ca0900c5403070200030346c4c024042c85c410003210100d042a03554100310030724422900c0170041c3e020244908243c0c083d590001c2c0603440c1c2003004000150380c034410f030441c41100c001603d4046081d900e400e82006101d0300c05550000c0400e081d280a85403d00c0110307403090441008810160540e101c050034050010f09200c14180d965001c42a500003c100384001440300c01d403001150101c804c0000d0140445c5009280200810395001c1100d602070b1390003410000642a03200d05585d504e40800040c14070841e0748010100a03140d07c044000000d000b00500580902c403000800318100000412100850200f0400c43e450100140007008413072410304420780b41c0c0980c00d00300d5101c0c0c2c100a240070b58154002e100e118800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 305194721 1250 305193471 305193479
    0xd0224030703060b09030304050d15140f070329030a050f032a0c0121051305071e121707030e041116121107030606090e010c1b0204020d0204 62
    0x400080d4400c407003a5405002a0307a440e052081503004403d40c142d8540c10a11007440a070400c0520409840d019400d101ca00e0440309560008844d03c4407030384540030218804000040d108510b0103500030380b00380f60802091507204d0965100710b0028401c0c60800c4d4044141c41c00c0d0713940811001e005035801c40c00313494075910b0b0042e209130760307500412030302d16902078a1703110140c0000c100c5040da47c01e2130076002402e040c0c100d07000110b078000c3d80d081a4081041d03500108071115105480b07114801c420b45560700d0020391a034240300b032400340503500011001c844405080c4a0058a2116104039551282e2138200c01c030081c0343c8181303280b010154268540c8404a46c05080c5a407100d42c0859126003a00c00300890304040b4401101072107001040c44410010302c054900044208001c54071101e018034100500140c1d0f1040d0908003c0c90341e0003a601d1540703031035042c049513946200700c2d4a0701001000802061074510006049103c21007944611403c1c1140b40070305640b240d40454100d801c40030021503441c4d4603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 305195971 1250 305194721 305194789
    0x1505030a020f1207060e0f0a15031e0f0e07210f0204020702060a0503011a03040c03032d020f010f05060f0603070c0506240a030305041205030c1501031703070e0d02 72
    0x40e000b4a07e00c80c0b1008407420040341031614101c000d550207100318010181260605902401003807060b06412007800404007055071040c4a8400d0408140c9000300712880d810301042c5c68494030380c00c00c6c03d00544400911080e00100c1d940e8070501c0b50301c0031b21038080c00354600014000703001310307200a5040f420004003000195030140045059032040c40e80c06044200024050b503041c0404c503002041c101c80204140040f0340201d03034081d407000c24100102c00c5030786814005d0110500d403801c84005680b10303107908076801400307018000124020180070007aa1400c0c800152407040b580035424001c06c2c0020204117524803413000e8028054000d4100d07110341c01d100e1009284011718415001c4d131150310340ea141101e07142200b42c403400c50784c040d65860308107410158204482419840c003107401d4407042060965000c4240a482c6e03c40c141c40c080d0030011341c5181400703c0021088c40014018900800030002c10039001400d10940a80c21760711503203000b20910104d06c0421049030700114940c0c1d018114444102c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 305197221 1250 305195971 305195987
    0x18010c06111e1e180a08010509011127010c170301060905031c0305060a03060e151308030a0b131a0f0102030406080c2116031505030a020f120706 64
    0x320840600402980500008070303901410b01403007803c192007209801c00d41d4000014080074106810700d510301e4040807001a044600743d61000c200c85e5114020000300c58070a1203040d10440090180d00d2805170400000c0f0a1410648048800604611400c80316130348603100c2d902c4581ea01480c401000d9640003451451a0800d1180000203426400085041e080100e124000000d010844050300a600750080c1e01130900100740980156100341c0000c0800c4040c0514400500058050544903501c0030407041d0143d801012800102400108200042c1d00041142d620801881e00060b1801c5000b002417110502031444107040c83c1411103100c000c1000c0340c606000481c040303070032010040248005a03141e0040303101d50380c003213001040080d00309883c110060030440c000103900c50702d48e842080c00c80c503084c400b520125400103800c0a03205000350903229451101c0c00507102c0340c3e4030901d0030303000aa075642c0c003000c001d010701d21941108486450b46006191100c0010381a500c45540700d00e8001c000c06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 305198471 1250 305197221 305197237
    0x9021e0f041a090d02090702010b19090b0616060e070906090516110714030a12020d0207090219030902041506030209090619031205090307030b04121418010c0611 71
    0xa818000c16011030707002c402c100e41c00c1c214050a020750003072a075005c1100511005218000b55500c0744c000c003040e50744440c9007401c00050304900310002e9040440d100201c940090407607020b100108281400c040f96850b074840c010b41d0100c00420740920100500f8280342042d880074000c0380c01c00380003150000c0300d134000620070034030402118840310140d6400c448219001362071b50080d4009030b03000c0c0014103020190007404100a8200e804d0504903581c0c0d00d484c682c0c0791002c40300603009007200219156060040c44000c0040540039030400444d1400b10141100b10380441d400d040d520720b05030b001c54840c5d4101c0e00400d88411402e1500555441d809006582b01c205003a21900c88540040c00c40d1a01030304451a04040c030f4014070203103040d035841e18518008030544e03105220060021140c540c0e010021040510320488642600d81094900010307046034140c041014070800b07540d80c11000380080280c7d50941d00c00440d100412020b00016030300c0c520700a5014040702e007041244d000803c003120040c0616 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 305199721 1250 305198471 305198489
    0x1b030b1e0601031a01051e0d05090616022d0703050f01150807050103150803040b3004030503100e090c12070b040506070212010504050607120e03030109021e0f04 71
    0xa60792440118202c074004c000303036520801d802c60814000e502c1030b0098202c420b021175048940c800f01c0440c08045420400a07480c0b095110000c00c40309010501c000d07078000d60380301c2840c1032014a001003e910344009070040c5582d44c46640038038084000150702029809103800580d141c0540b641011a110141d10668402c1c9608004900305865000a0400104ca401c40040c001075803d020044001e000e03031041d000f6500000100c042010b180500c0240028111082072560700c1c2007a04a103c02d041a51102d00c0c032010a400c0440f000e01c81d00f070710b595445070385881c2039640c80d07448074002d26080c02a604034548100a04081001100d800140751aa020045401341d41b6041030000095460038a8065030400c61000d00c02040281485030103800c7c0680f00030010041040f0807011507003102c504a0f800e48042e0721070414828010b41240a1500210304d403c4284900764000d403c1565034070042c4184120305600140003000d401d800c0e0814105485d04a00760341d0b9503007005031300f80d15540050241d41c9070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 305200971 1250 305199721 305199781
    0x10020c010e06132108040e1005010c15050a0e0a0501090203060903072f060d050403030b04060b0a05030a18050f28020105092404030b06030d020a1b030b 67
    0x303585054801e5804280540d40c010801604040310a0f008100100007920410b64401d041d00005285e10040e10140c04181101c40303c0e4607140c1e450140c41d11040d8029810b00c64045285004120003900800c0c0d00f0b840464003040c6038030785c0301d01c243c0185249000d1004134001c82080c2407c10506400c491401d50080b0704075481902d640452a88900c5006c00044c25600700c0c11b090418007048100303102c40309101c1d10001490000740703804510b19034080b903184c440c00e6075034104001c00c160705807085105a03a1305076010803040d401c00c4e005140c01d00ca0070558600303100c40480000e000800f80c1e00000b001d0000314080440740c031801e1500a598500c8042c05030a94050a880c55003041c9800d0074843d00e800840742c3d9600070030003540054905901100d0304c0350f04140c0c1c04038030600c0307d5601e9560000d0b800c004000caaa4071451030605107820903000c1c01c3d5603c0fa4228100c046502580010110390080c0c10150b10500d0f4900c084481d000b520312a40020f040860034010003003000c3c2c4401d031901c50389142240c0300301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 305202221 1250 305200971 305200997
    0x90406050613050108070c06090c051c03020d1b021302070b0c0304030801032405241c060519090506160806130c030b03120a030c050f030a0c0306030210020c01 70
    0x3a1402100411100402c210b20308105541c420b454490b001001401c081080e814a40c071102c05403800040150b4620704290010800c0b401c0c010070304a0b483c120f011450307900c5849a070340203465102c0030300588200020b12800040c00030000340b6002c00036500401c0341500d04403881c5400081d40005006079412501c0000080516211400f26885180d040e0342e4010f0036800d66840080c1d180301c1c030100000d000d500e2080ca51f0056030511407140626261404400c200622030007003642c3c0200440e407280901d0500004400c511114256601402e5003e000411b0a5a5250b45104010300e80040156414100b2079100d041c0400881c0c41c900a4001d241c03d003085280c5284142c8980f08259002904008900d03482c441010184d40100038403401403801141d00484440046d1404d9070000b0301d1084004000b84640f042034161281800700344042c184181000440301c4504503601005100703002050715030b050704103003501c80d03400341c0c001e55030062032801881d46080009583d252a003d0145c00304031448a084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 305203471 1250 305202221 305202229
    0x905130e0c1f03050a0f020309061b04030309050f03150c071a0106020c0f010912081c0b0d060e2e0510050d020105071b0608041a0714031906090209040605 68
    0x7200c0c0c0041c182d110202400c0d802800c03402401c006008011584c1c0c1d0b2a80103103694200d00085000b811410b000701614200414070b00003500340841081c1203603204010420019070010194000c847c02150031802262401011a0038515080c6d0300d5950000e00c081080000b051541c058030400703004146004443c00e080740c5121303004034203014000141c0d100c800034000c1c501d814403903004401c40600d8034a08495450f8171441825442c40400c031003e040104985010725000c45c040d8401d004010004c0c00402c184101084400c4410308010b230180f500e0b200900113900007000008103200d90030703c4510f050a010482e4090b4004002c1c203a0340300038202070215481046204021094820003081e02d071400d10254010b5800d584040b8085400c0318407107103214100b88652a0400003001c40352a006103505e40f502e0141c4400d4600b0210320038000e403170400c0c094140d0340014001c0d01521425a0070350349403070b221141c46440d40b10704100c505d002e00701003003c580581582c0241c081441c0035102400b40544681c104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 305204721 1250 305203471 305203489
    0x80f060901020f0706020904090b0a090303140f0103020126151003050103170705190605220b0402060f13060203180411180a0308070309061403040b15010905130e0c 72
    0x10543c80003805a00003003801c917401001091001440082d0010702035440b418001d40455070110003d0b82d07042403005068050141e40c2158110a101000d00d150000100380c5002060001904010840c0410034210000c5103a46510f5141b0544505841c0f51128403550021102d48140d4015482141000030240c0031b805a81d0581360300400101801e60210081c014507000510161068844c241244100316480401170a0043c041e0201060514180c0e2400000000400f00310644044040e10070b800310300d0030b180d42030300a51f040712910342e01d00390700d840020325004144101d0b0031815440d6000900070b400100902007090260300c4800c0c03241c111000c000c1142c0c0068840f004000d800c101200c02c0040c107001134264060002c0c03c111802d42c80352544686a00084801c81c04100c035410248000c81e00b00c010b16007000004c09000d4518030301542d8240071410043c20345802924a03100d01d0180385e0081d0f03c01000b50a01401150000300103100e10701c06050b030f604180000b801008030000d2a0b081000721 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 305205971 1250 305204721 305204737
    0x201110a1703070c0c03060203060f03070e0a020a0908011b0f050a2f031303260901030c030b03030c070905100b120406020d0f02070c060203091c02030304030c080f06090102 76
    0x81004240c0c190540e0300c0780340d100070311440421103c4181c0c03c001400c0c00f4030300009503004003030040c0c0ba07207049820301800920318496140f2039440080208104c45444140540c0020240c40260f00e90000c29003d641d4034405030008a041c0d406d010469a000442d40d1003035524414658651100821642040d00e080c03140c201d03030900185a05d00d20f0100b200c40150840e1640c03200149061014861458082c1950803217007590103108c16644003041440100d0504a0900400300024602002c00c500a41403d1041d9150981490348550a00b24443e0080c1d1200004000c0135096035a280c495041d0980c80708000d0003038641c070710301d484003080407c07000440d0641039510318440c03140b601d0820011007212260050088404079000c00610184804030f02904030510454040540c4680e4107142c003c1c403c8042d500018215441807102040590369070310300e42c40030b010700b2002003010043e6001080c1948074580000d4440d50761120001001030000610404038814601a1903483d103c4e807070810b082c1c1c0b1504030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 305207221 1250 305205971 305205983
    0x100b0405150f06130e160906050912070504020319060914010512071203030c0206060103050f010b07020604090e030903120a09141c1115071e03020f0a06090201110a 72
    0x104481003820010b88a02904000030301403424002000c0030f104465043d9040382010340d50b0b090a001040303408002c16004216a400c20212075030812400502c0c2d030061a07038080c85000b0181d00d81406c80c4092040d00042c00020f80255038034a4010a100e900341010420701103c18540140040c1c459424420f0550000b1460401c1016900e05010010452040014555240183e801c00288030b03601c0d48034090041d20030b4a002c50141c1c29140041c3c00c084004201905050074101040201042c40c0e031202d040d143c06035034203600c4900a0010580d140162b030010080e1070316180e104003041200001801480c031080b0708403600c0d41407030f0020b5021030245902410200724100c100340175400550030440c906410182180d90b44002110510030702d5288071005682c52041000c4030506414004400d041c0800088c044600d40b5820340c1d1000307458207070150520724200c1e85110050415109020811408015000f1580c01220301d050100050013941c000301c0c0496120f4140c0b40c41c1c2d1502040d14110150484 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 305208471 1250 305207221 305207251
    0x81e0303270f1b22050405030c0607020717030a0c06111c09020a0b120402060d0905060f010801050601020714040b1c05030d1d0d0c0323090307050402072103020f070302100b0405 78
    0x112200d40a485e019100312000c1c0800c0c07081c221000002c20003588101056801003014a24018039a013420482e80d5280155800401030704100303d822147d1503881c0c0340e10000015400d0550000000036016107403410195840d610f650880409081d0040c00d4681c3c021184071040596608074040244200d643d503180030917100c00001c01600d0a000980889950000c003c25132240300d030395443c02d141c02207600c0f142e4610400010f00502c5000d02c101d903030000d001c0c001007041c41e00b042c124060401c1607a28031441546c03140a814825200c0044450504808900d00000304c0c1e518074101d600ca82112102c1400249001c415840b0f520341405019074903480c96018102c1d0b03040c0c0c400e0480d0250300b01041a414008070342001c1642002d801c0319489994030f40401a500c8682c42420581414065440030340320b640140003100105690801d00c0f0403015604c1071400600d000940c050313019004d001205840760001081c651f0906402180d50061940303010001c20241411000308402c0b036070180c6455070700040700f03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 305209721 1250 305208471 305208529
    0x3030103050717010f0606030c08090606011403150402030c0a120209061b2e0b0f010212030910060308090112150902071b080106081e0303270f1b 64
    0x5640f04032002025000400c0040009810105442c135503841a400a90fa480100582583c4003901d01d0b00030062101a001e60708003800024540460502c0c00e1004001c0000440e010102c11201e480c1c2d00c2c4405801552a441c4c094142000c54105058040c00714903c2207030700034410050720841d110fa120040019060004e056003c1804802a2100003103a1044c42c0b0740d107515943e0161002441c0004030020311020f000140d89106440710a04024003d008000071250907a03004140d030440380740034003140c070f0320f80d070b13491104502d01204211100e014510708000071003403000c00c2c00282900c0310281c030792028800c07048900c01c00b1503491030300c81e40c96800341e9a0f041c4411201d03500100046130060b00070481403840c0041c40080c041d1150b20204c0706a6403074400f04a800c00900c8502541c1040c40c000c250720b441d1048030309440784402071081e6001e2030803140104124510221032007807500458100d42c841000134032001d6951441074200f03001c1c10190000001c0c03610b040d0580c003204090380c0131a500d9900003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 305210971 1250 305209721 305209739
    0x71410030207023708030c0a030e01170406090b06220b1914040615020325330b010e04050a060515040e1005011b0804080f0609010e030301030507 64
    0x808030040307920510b8803501618140340703904c01c200451400004002450010b503880d40501c0402e6114044640040c0300180c40d1442c04175032104881d8042c1050302202c030312400129040d401b010715003442c01111a0610007405450ba1240390410300c549915041d60f141c2c40204a0000d040f040160513181e4903500140703500a50350080842c500700500f1480341400c509800d03001030011900081c20201802d80c130140a80b4040c02141c3c024610903000441041003a007009441b440341c130303019403c0b2104a412007100d003010034103122034150700720002c0101020074500740030115001902d1051050408803400c00c42001d02d1140700c518400c141c503942c0007030b6090030502c005000001d0407000082c1d52050002042d032102001c1c1c00d4102e03540d08c025036440d42411520004a4009002c1036989022144103200590b008600c600038000144a09c154034100c0d440d2540030707481150008486070007408420504035800043d00c0b4000e15504000740a19565502480d03a0390000f480b000d0301a5001400410031802 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 305212221 1250 305210971 305210977
    0xd031b03050402030a0219120813090b0612040213050a09030305160f080c070f030c0302010513080403231e1912080c040807030b0106031d2109120a050714100302 71
    0x201f600d602507503181d49801c5039640d0400700c1c10603150144000b54005401b501f02102d1000741141e013808015006007076010803018003600c000896814066000316081d559040001000c0c05a400d4051015240c422203000203882d92078001c501083c00c100200b46c0d070012000311014208119903a220440054070812100d235103018144010b4024200040d801041d100080e0100c2e0900a4590070000c1d1594035000307003150002480c900c50060b9145a01d40040c00920889080746d401c6410640c003296070a81c050240740602510004130310030031149500b6980d107136200d0b00000000a0a41d030b48954000c214110f024640d0b10001d000d50f03640c000c1260600d004240141e08890110440381c2465141c861304c918242c0a40c0040c5d82d0030781c090004024556040c02101c0c03a10f400e111031410000003442c3e10950f038100700c03900032150700c0b1082940c0e08516803007410f60b02e60980c02004050002551011075840300c800301002c0d100f502911501081f00315541030039900110016080d903010f003440020441c0290 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 305213471 1250 305212221 305212249
    0xf0f0a0c0e1810060e310f0506040c03090812070507060608100e01090b0a0513050114010620060c0d060305030d0f06170c12010b030d031b03050402030a02 68
    0x450707401258032507501c6880c0c4288048485022245075800d220100d41504001944580100008031781030786840d4480c0304c0b00c080903040c914045440001c03010304048120b00c1001e03504000781e140c4000c4d8031400d00e06411082c0117000640b0100070b0901a400b0480590302c8810380135200c0e25003000b42403c0d83c03c03110311955011116180103030410400342c0d5103600f42c0d030503a40481201d900c4104603000800040c400c070b058034001c680c02085484070903510000c41900092001d441c80742d5507000120107a40d58002d50b005294080000c00207010100c1001c00b00403420b014a00001d08140105600c420a800da80003528094000514050b0b8505140a0300e0740d104030000c0d01c1c640d84909002000070380c1000549144540c00310041050180359051900f110042ea11803414040f5990200a040078049003110b0a00c84c16101c0c1801c0301e0440c40d9141c09041500102a058401e9900d82015298194050980a441d40c18030b80407020708110220142c0790143d601a605401c1918072100501e0036282044d860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 305214721 1250 305213471 305213477
    0xa060e0120210702030105010f15080702070f080f060601080f0f060f0406230a0612090219030b0f1f1401110f16080d090b0a14210f0f0a0c 61
    0x150481d800c1c102d10200021000c1103042d10040340c114110b260070f00405001d0f0104900841005203488803a0174000a08074810040c8503c1c0d101050b4100d00c2881200068803003450614442c9503605909550340e036604800480303030b003d8031010811a40c415400c007405903c9408018845848030814280b0491016201c1c5600001100d15014581c80c0c60003a0343c0102010148100d0350714a50380300d00610303d240301361039208103d0040140006038200600c4403601c940c11000140c24141c6102042140035244510030798090240e40000c108002e9400041c4600440403509025849021000c50306295002c6884189407401c0014004400b405402041031a01490041c50490300c10300c0b00b070300344515000c0944664006075407001ca005942c44201c0001c1041c5070042c607d0701c1d129403000309280118001c001f405100003a00e005060310800c184100340000b5250650f07103072a40086c240950b2480101c40c0440440d03000018005810103100910909502002c003100359218800030000300800500030040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 305215827 1106 305214721 305214733
    0xe130803240402180a080304030f080901030f0501090f0c0827120a02060106030f02070c1e090f0f0e0d02030703051c020d0b0a060e0120 60
    0x7020700700031020032050200c10000c005090011020550150010820300b071425000b40c00240f54180443c0c80c40605503a440005841c0e001e01d1101800c0090100303840004201d1150092085070300500d030029034800380342d688004882003a08501100c0380d81d260680400486031184501180c000e003020724480c5040ca1030040d04000f1750000e0410f25900780c420201c211402c0152400c0034200c95070854030380340c10400081d03a130b1400b4801c1f10002030030030f400858202d11903c2107988080d00107200700c4003981089801d513008010800b0340320103003440b40800500302a1078824501e6044107950f000c181d00001148d6001075907800e00c03031042c0c1500007451003441e0503000030813155003543c1410001d459543c4c00710104055000c00d506284041c1c00003401d0315801416521841190340222407480380d6684400b000c40304200100c1c034031404110700040d840c0a001c101b20b07040015150400482e81 = true := by decide +kernel

theorem cover : BRFrame.Cov 305035971 305215827 := by
  have h0 := BRFrame.cov_init 305035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 305035971 ≤ n) (h2 : n < 305215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
