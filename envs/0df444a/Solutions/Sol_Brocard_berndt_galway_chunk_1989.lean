-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1989
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:54.123514+00:00
-- url     : https://prove2.me/submissions/1fec8680-42d9-42b3-a30a-2ae3411ac711

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 357553956 ≤ n < 357733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 357555206 1250 357553956 357553961
    0xd060807060e120a1e02030f0d08070804051b0604080d03050a0c0e010518150304050d020705090f07120f020a05071406040201120b041d06040605010b0a09210f0b04060f 74
    0x40f8204040c1c2081e06090040b81d07545040100d048250700d03c40c049040c0690129140040468241066412602041031f00710f901034901e60704400300b031400152504154981648400002c094680d0407545900c14000343e481e81c0058070010642401a02c00b000341c068809409000304032010404649868450075055000300c040c0c034006038041e034034503042000707d10f10116142040c08203540d02010344914240ca680070400154441c5210b88042d2569400d0020080c0c90048036802941c40360f00914100310320740e248000342c65417154840c42c250100158000c0418010030740d8031105110f45000244045003581c10074010308405100d0b684131840d811107003c1a40c1c85000641c2e00a0010703100442e412448200e640103856559070080c0b0000308048030002d40080c1c00283c440280680e00600104410f005091003100d005007101446186031000c045c00003840c0300000c4c028860524a4211100d1201d4080e205030f00c44160f00900000c62074446007040100000100e0b070032940c1c01e0070001100c50310311190 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 357556456 1250 357555206 357555229
    0x1509040f0f0e0d0503010f0b031905070203070606050303071101050a0e0913050f030a0206060105070302070801090606140d052a03030d02030103120513050d02010320030118020f0d0c050d060807060e 87
    0x125801c0c2900c8e085c01409603540e03101414ac00c0a40700104040c900c4000305204903030213039100f07030000e503900c42c02c030714046054684d91361115100390800c0c40714001161005510a09182d424a800c0b0b0b51116001da00381e402020b0004415080341c12101040010101c841d04061140e0280041b603101c4002c1529903170b900d00c0752000038001038000802044155000d0070240ca0f1062090054408081d100d83c1c4403030071600c0d21502030724000e1721800e04005541c900621071139544c0342070b1804640088192241030b503c100c02c011282454100c000c4012006038403600c0202030001c0201569a03600b5000200c40c00b07900280001d03608510f10a410050881c02002194004049034244110f1680b0344820403290782c1214005905050325036480600381031509114601ca20303402ca502c2e64a950414007035015054811281900fa684100104441500c8100a99003101000380d40840c01c4038415400301d400d4000d500c24541c800b41004404504804082601010748130503603600119284107004110202509 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 357557706 1250 357556456 357556469
    0xc030303010f140604090f020a0f0509010914060909010b0703020705030712150f09061a010207030b040b0c0403080d06090b06030124020106080706021f0b1509040f0f0e0d050301 78
    0xe11000c0040c805048880c0d4480c3d83c008040c41d007040d50703e041c800c0c1a10108811400020f40c0040c0c901c1d1101d41040400c000c0e4035913803500604024210700064109100740c050802405600403c0910799070307402003115074804000e0300620075543d48041f83c080036080300c5401c4001d030003055004a90b0f82000500c03c411181c4211054110120a40764005190003603051020180e40b600d15452041040703005000c0c0b014440c60340090103803d614924068100d03074207140c03411034102c602e0410218040d4041c09400c90b401c80e9401441d9141c0d9801e21000b0701c41c5a0004201c44000701c0c115110a007030358446c60840d102078409104580e0258100300c1544000d005034241103410340004500180320004034025080c85000014002d0744a01c41c45103400050303440000160301000c0c0818162403a1071361440312044070101401212030f0780c400984001902070b110800c81c03002240e86080ba544a81000004600b0808100013003400c2c504890b01030042042505414491001c201c00c006100b402124100c690 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 357558956 1250 357557706 357557729
    0x9020306040308040c0e2701060f060e062a01050c03191d070b040306140c07030c1a01121e111002240612160b030403230901020c03030301 61
    0xe45a80549183c4405030098900e2420780740c011810b46e94800920380079036028544d51596021196070a502400303032003c2c003071007a410000b00700302c00e600c0c08001805a48190030460024144200460003501440955000307011a556500b035041030302c02e42c143d035174110050080c002a80d449031581c0740351005840354001080d15940c1880b035900e1541c40b48a020f044200c0b018010520390803580e184c48250b404c04186400001410402c02403c2d2141c005a96098603a010481c0f404560309400d502680102805000a40c100390040003041e0825411502080c0e52110043d41c60f460495824694098110340900b010307404440c072042c01c003c4800409500c0160b6503620045423040c0301d600a4803c060405500ca25000c0e080c2e00902c00341c5072922025480030240040c5813030002c214060b01010b40300080e45c0c02c080d88001c0d126051030075400035142c101310490307541d48a901d030458848a01c820040950000540c0801e020f564500081401803426421900340030300c40d0341015180d00c402c1c8120b640942 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 357560206 1250 357558956 357558961
    0x403050705090a0902040608330c030c0f0d0c030b061201052101020315210a392903190905160810020304030e0409061112011809020306 60
    0x902504241d0f4865a030007400f144408441c1d020900b655080c2d0001031441e00b051135544413110f852000340c04029100d0000450f008401446241c0410002e0034405803001c00000290405024400710b40c1c0319411566695511200030302210000c1c01400c81103c001703801c1a1518440d45010320988050403030042c44100c0b142d00e0301c030420540c0343c0001d038003084031940f9454009440030284003442c1310700c03a411003941000f4840300070450308ca9180030900c080c1c001303500c0038101490030009208042c039034000c040c0c13031420903444030013040d45000c03d09403031508400c505c4055100040901007804c94160945440d05103881c16040806442c0c00d090142d544d440900000e01e034540000002d03003210340ca028000a6154454407254201542c44000c0d0010110400041010a00421a08807060701c820703400c40c15810b240e81c2c01000c4c00101d001091160780c4424103101800341e2a80903240056401c04c0c0c40395111480740400c075004100744100031400240345039401c0300c03100d50b0040107075603035004000d0445036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 357561456 1250 357560206 357560209
    0x2011205010e0a0e01060906090b0405070206090a3c060e0f0a0f0c051807080705090a05040b031213050109080a0b0601080c07020d0609210926030a031508030403050705 74
    0x24002c4000200d105c1d925840e000816000620030340000e01140000410001050000e001c02c1d94400f6041204661003001007004250006c203508d0a0320380d01c12440070240e021205c2c410105000503aa40003107840c010022030704188410001c01860b4810001401803518070412151100307007610420710142c0040d1600717000218008801c2e5a0076201d4030030b40d50703120340782c9020601c92058148806c80403a03014061144e21078205203025401501850003d26081031000440e094020510a00d40540d860f103000a005035010300129141210f0880c900b512072081c0d4172980c5026030a0301c2014045840b03182c0c00b0a0310313071002c14860144d541000c1191910b8482400465610400400c007490b1001c0c00c0c09030100582d20f40c81214840d9020f0900442c4121040c2003000d003041c410324a4071000e00e04644440c640d5a040344012080303c400700b01c900f80044d02c0041000207240042110b81c1e00307010015107041043d0700b41d480024007011200302010101c3d00c1e07030015940e0744034901003d030441c2e10120040025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 357562706 1250 357561456 357561461
    0x907050a0f090b030406091502070c050d060b0910090c02061e0606040b0705010906060b0711090705120115020601050621060109082a0d170318120702011205010e0a 72
    0x180701040c42c0c9240c086503101d000801e10340040d03034101e481d40c0d11440210140b1008800e4100046c02103181180b806110703964100d241c0210303210360f500440504500d82c06201c241d0384140b81d034050252130451249000001d942c0d00350100d0003980c600d14505482118543c0c030009a041c4101c4516088181022001600c6080084010300443d4801c004010110744c000021000c0d0440b00e10880c00441c040d40d0a14000050350344035002010003540c103000c04000314038480061020400305690007840c81c2c44801d0126500e10030b428162021030400740000806241c29001454880e54079803c3d118a40d8a03202040030b40c1c4100a0700c2c80424100ca40360010440342110038907000340050414a44150b81c0798404c90420740609040318800c00b46007905104481e82c800001380c5007004072a0f1400c00551592103059240c500c881d2001c440030007100003044026880555a0060480c0084460048035105082806e602a820490000b2485980c0d44c00100d840d01902c0c2c10780d0800242908c0c07907581d000c0c51100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 357563956 1250 357562706 357562727
    0x60a140c040b09041a0a0b040905130f111306032001050f030f0723310b07080403211706010e0603040302011d0102180d02010e130608100e010b0907050a 67
    0x5c400300342c0d07040d0000075955418900d008260703102503552100c2c64045200f00b254001061120201006510580003c2c0160440c0f4410399102030440c4401c2c1d01c0801150031851354050040d480b0380f42900100512104e00040041513a200e000f41d0083c41c003220045646019507401074680c1c044c2480890b03514003206181507403201041c942800304040c0e488100c5116903060070480803103840060b0388180c0c81c0c0340b00b40405460301c104007090f8800c100a90301a81a180c203205014040c000480c00c101003207200780407a00107613081803600070f81c65292491501d941c4142040e00001c03841c507005424a901c201200c8901c2160140c490300c40949140081c8605a0310040084045543e81c1c007841e1445040c180101d00c0c044211800162200403120307079010070940c03182c2000d100c0c4400500c6040142c1e40f04a001c280b0304000c0c1c1d400c018031b80d403a0f40110701404050700040924000c1c18203100d4061201d41c0b00e4207012200c00001d1040f908600d05024103a203080d69411f001590401c14181c00da80503100060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 357565206 1250 357563956 357563981
    0xa050610060e092a07030305090a0b07051b07090c09271e060f080c090c0a0302091503010806070816020c0f030f070f08070602060c190908060a140c040b0904 69
    0x440744d109207070044150100e1841d101001440811200b041c1a403603c1030a42c81030f00c1e07900034034403050580c95001c46c2034001420030f000c000c000103448103004200d5402c040f10740c001008407146d82d41c4980d1307524040c0c03540a8901c4d0000700a07402c00101e00c281503102100600d040c0316850b801d6621103900402810061004610030a5100514030843c040352203418001c280440d020242e680c140f503009803c000c008408148144490300500c00c0c00c82641c42112810501814011f955003054400700d04c0c40a0a600c000055a5000c00001007940020400e01d10522140d9141c2e0ba0740d40d64201d81805100b050240f4370010381c00f0001c1818541031481992501e40c0c002000c8603542d92464807440d107400f545030440102d8820030442000341c00010008540070708128006040b15140601e8084118010350040d00488030a006190110f5400b94800802510314042510418901046454003400c4c41c0300a0f83c0140c80035200007107440c003500043d41c0503580004640e03441e0903030bd8001c10001d408070010783c3c2d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 357566456 1250 357565206 357565231
    0x140705180105091908011a0f04090f05160e070323040305090307091d0d020d0e010309150c11010209130b040e0a1b1203050a030e0f0f0a050610060e09 66
    0x16030598940c04c2e500c25655003408290f002d18241000d203425a000311518842444004120150b180d403014482000b4120580c2c0005107a0118140203001c0341e0851400340460090305100d203901e5182024500c03e49010b44144801c81e2220801182101c443e07200b040e24035208030743e800c05030a02c0c0104507a0060300901d0014105500315000a08160a035030201c0d411356035a1890041c6030f28010a94001016140c0192450350f030325020103502e6901c3c1600c000700300302e90120709041603800386c1d002121250304440d065a14a0b038858030640140341e014100d20101b140503106407a5a0300500880b41850400b43c090510000700680c0500070303002400b143c5a0181e20f8000100340084100305007a83e85014029503000d94412000d00c2c0c69005c1c00b5001480a00540c00509001c41d400000b2134504046500d070000b541400107039624180350038212800c440d4010343c1d001c1c48a0510000d1090000d41c018400d41b0380a880d03104e440a103e500074440c110101d040540030309000e00d48100394a40c00038682404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 357567706 1250 357566456 357566467
    0x40603060e0c03010605060405060912150f061305090d0507020d050a08090a0f08031c0902030f0606040e16170709020304081207030c080a0507020f0a060c03140705180105 75
    0x14041075507490180e01d410703944070314050398952909004080080a050f9139840c40d00d1706100218043e4820f403501103000c1c20300c02c100c0b100804001c1100c09100b045100040c00281001c42d4204142c0740305540c40d510a0b95500f040006203032851007074034004d0501c1070003090b04e681030f803e081c2c400f0740000c41d040c0d0703200e164060240080703001400024001d41c41403d150740e4810601e01040000d000b2034100f98100701c420101032081c039100104442c0c820b003000c0c6203400340780035540095000c2c10034000000d415008001a0800c8080000340081c002c4008a9091124a03840180b2690384c84000301d0140f0b20741c66030700c0304201d1440008e8032001c80e159a07400f9501507944441a0b001a030740140c40c11544004001040e8a0700c0d0001c0d0b403d150010510b240501440114448c000c003082c5c8041c140801c20b0f80c4d42d90104400c14001c20070307444000341d807001b540c01c2500981020001418140c1c2c507180480c0c140302d40105c0e151000d0303881900c5603030705869040c1828010f055072840818040c0000713041c000704120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 357568956 1250 357567706 357567713
    0x90503120f1819032007080d0801080a050d050d0b060a0305070e040b0f1306030c0e06011701080a240c0203090f0301091505150a03150b0f06040506030c07060c05310e06040603 77
    0x6c20241c00490010006403420344802052104142d0040701a6000910108001000401e040c042c204540c0352082c4c441410051000090070381100780c6500c5240041c031101c0031901600001c0c8148115104d20000c000824288429100e50081c05c946c0032030400e03211080307464025800c00542ca803d01c40003400f20740326918072845220307a0304480c100244030030410915603404041810346041c401c070808071651400907401da80f91031a4400405e540d880502c96450030707d506800c20400d1042007030500c0b9190500c0c00207920f030390061490900425000c620042141014010b040e08150f00400f080d070241792089801c401001d010b0030103003201c405c0c030103400041c2d6100240800a0b60140720052074010354401148126070080000ca8040c0e85512200c00e81c9079549025902210000e4400a41e20b0399131041b10041d610030a800100240e02c0c05039440c00c410b40c000c3c0038040c240d080d0003030380c14406c2c207001c0d224280b880250440e4162501039242400070810000b0310307170f8104402410104441c0d84995 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 357570206 1250 357568956 357568963
    0xc0602090909060118060303050306010f03091506090f0b09061005040509040308090105090c0a050112090206030c070b0a050f04230616031a0a09090503120f18190320 73
    0x4070b2407121a400f8400621800420b00702100d4243c000f41d00030000300b46150380c060301a010040c0b0301818003145440072815a8082c0c2c02041410b5030246145616502e8102c0c070b9001401c080c050304041901e84030060407202101e00c240500300070001c0c040d0819940b07450420100015064031101080402e010008664a5070f00041e4060b91113603c1c1c010152030540562400c41e60010701c0c4c211180c2c400300182c60785440b02417200c0203440302843e0a00d03000d440144290701404481030021342110000003040003078802c1c54082c1000f03034481e074035011550726500202c00580c0e80c2034585003c00f281120206001541170402000e45020b0741030750390020884445a00d051507000c4954465011f08103090146241d85489180c007a444003580d840d1481d0041d10108070200d907640181c05403203170b45001c0002400340403c181d485024040c4c006152514081200003d9220b080d910751181040000030711000c1c1c0b0b008642900c80c0c0c40000300100104046441c100d841400b16000d003030011181c903c1585d4144000d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 357571456 1250 357570206 357570211
    0x1c06170c0a260d0f0e0f0d0b100e010b0c070b0408030301050d11030307030201050a1d15091216060b01080717041712010f05091b180604080c0907031802010c06020909 73
    0x20745840c80740304101135029114020102440d03202e020008024009940c810303041007440ca41110200c0c4060791281c4240c05000d0803038104000490900d000011148580c00040c01c10401010544461550b82c0350070182d00c0c080e900607050700d46c10610050105007800c42910340c039a4090810701401e06c0510010a06591101405500603512075003080644401e0340510314031404840c0304180302110704120741d91541c111115002040d92442d001c0342d65a501000340b42d03807015242c0c1045070b076a05058100181da01864904071207003420511144055801000c07000c0c0704401e075481e100c802240f030101548191703030001e00c102c8141180d100c02101200d0b15002401164044009031412541403000c0c0c4104500142c0c000e52103194000200203408201c5983c0301c1c586206626010b03140c1c0805c2c1c11034041040c40043d01a044240800c0005d0080f03000280e00e90203810a440b002d000e82c880c40c030300b2020381d020414250790900c0c18903030b060010b5120b4520302821a028200040c20100040005240064107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 357572706 1250 357571456 357571483
    0x603050612060606090103020715060b0c2506050903161404050604020703170a06051801150207031718090901090512120a111c06170c0a26 61
    0x122010001541014202160201d000e031005101da407503e0300c0000d07031910403591190704068002c41e1410400c17420440001800d00303c0d44081c0b0059480d64611841c6400c512a9500d040c816105e00107402c10700d65130380c2044000b588040004c1d09062540641e100e0b030004200c20f41600c40c010301144103c0d60b07540c6c40c0c0080c080c0020300c4600003415404201c01d440e00031302014440d520400c01030f40040d401c000d82c0d01c1810014140c1c1c144030360310103903002c00904161f8002601300902c080c41e80102846d2061145c1a5030b1204649915210034540490740c80f50f55001c01440c0c059140e020548405404024101c87d003602c9040400d42149400401d00d0280161080d0105a455a031743d082004070a0124400916000341d440c3d0030443c162138000034001c0d001d03064031036060355540d541d130f0b14a280104845020420300c020003a88014042c2d800b0042000b44a050300c030b5984008800d108800c0801e240e1588132005095000c00b03418924800913a044851101c00c00102d604d811550f60039003848410a440030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 357573956 1250 357572706 357572711
    0x8130501060b090102010f021c110714031b0105070f031e0204090e1903090e0a110a0c020a052709250603060e01080a170c03040f080c01030e10090201180603 69
    0xc88a00280c213481404201d000300d68018800b0b1942c589c2071401c8000f107940c2c442c0700411003200d00710202d0a144100c1034090f000d05811005400552000001443c0c01c4140090b0f40c601c0300e1701340c1405e0703003200c0040e40c40c030001960010b00c400c0e8143c031a401c03907a0300d20400b030380107c840c00341c0100c01c40880c0c0c840e520403845a03466200c4045031110a01c01c110070315186070004900548656402041c520107401004070040044010840c0040341e80d03c8a4002ea0003103600a646a040392009000325040e148200c1c0300e15100907000c40c49050100a400008070300c803218100d4070302031542050b41448000c0c404206413041010080903000c4e18240500502d14602100e1380003404c1580090942d600343c0c100f044201030034401041915400100801d040b6048140001000f400102c1c0381154840e0f803a03902d1140c40040f4010070003205211640c0b00f2618110200d401c51008040154151349240b50100816004100501d280841c150005040c0320f205141040c403225800518041c0400c07aa008031001a6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 357575206 1250 357573956 357573967
    0xb060d18020a090c084c050f101b08070807060b0d0804030602030709050405090309030613020913050f010207140f01090b0109021c0203090a03020d05070209060108130501060b 77
    0x10800c0a14000e084241c009008005001a001d06480705c0901003017440c103a5203042c0b10f04004002d4849148100c0103150b203c4596244086000d00310201403034001040c84110001414a4082d0200c500c0034800b509010405c150700300287ea4003492207030365490303528100030b50b4000034142c40c009024451192420540380c000d10b092540850720041e103000d00604036181e002000c60700c142e050b41c00320b0303500c104051f1360f171381c0d4650301150007111541c001c640040c2000b0030312043d103601002500641c1015000c5940070703503c07a45200701c01480c040e8040e40103020100441c40741c50006a003500102d0140c0b040340e203100440c0d0516422030340049230a03a8030719042458088110400e02240b42c0034800140284040022038407000700740c20303041c8540e6400d182c4c000761000c14018036113600044800c04140031512403170042c4480351510806a0110f0041c001c042050110380c0c000c0c01503800294014102c20b4ac07070368a020040d180c819024100b00000d041c90708060000030780c24010500500b210b21810f68541 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 357576456 1250 357575206 357575209
    0x60206090d17040209090f060a0218030a1734110105130e1302030f01090515040f02010309110d030306030c0506120a022503080105130c050901030b060d1802 69
    0x401400784008004041c0000846051a564450b40054045a06154507242c150030305182500c0580c029446010302801c000e40102d00380c0c0504500b41104003035441c0840c0d00302c10551180004000101610811420269852000009410400e01808407155040ca04ca28605524650701e640a20018103891400c3c00f08076042c040800c09640a007003481c00c1030240070140f112507005014140212200c40f000074600802c060780c3c1030b4001c7e00030301560102c008a49401c4c2c041e05000700180c9861051030380e410b614404c500c0c021481035811050701b11a035001d40e03004401a1800c0901960644030302210107825640c0c13560420704140c8240c800142903495854111040c62403540320741c1c801c00703041c8880c0010054114205c0c2d0f12035000c07a00169541ea180d003c80191404021a01940600d01504002019040700704241aa0821140c41035080c1841b480001954000c4132101c1c0000c006001342c0d1025400703500700c950341c0b01004107a01d050200c2c220307101e411500c214081010305182c100c4010150f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 357577706 1250 357576456 357576463
    0xa050913090c0e07080a0c02070b07051c0519030209030309061c050109020a0507030c141204060e0a0302010504031209180b011205040b0115090e07030b01030b121009051606020609 79
    0x50000f6001a225890031080180c06050010851008075442c2d200c2e852109100744110720103800e80d5002d0036210307034103070520303540e603a6a0714181c62400242200f2038074182d02541c251952500384101c07941b40034003241c1080300a03411400d40e8940500c03040c09000040e40c1c03007102510a0301c04a04052191040d1103840c1d4090707c106a0080d15910b10410900b8040e40c1d02400700c407038a582500303040901c10051b207000e50810704010001c1d40386000c4c14004d40041d10410700103008551144e6180e0f106100d0b00c0d010001c031501144030090100784200002c1000503100b10944481c2c140c607041041100741c0d5801c040d842d466040c091820480c1d0f85004d14151982c0280c06e1628891400f481040a440e040c0d64560300f404040c01115035103042070075126034061054844001603d407400c2c00420a081008003d8058404103103130901081c140061303031001c2c0c00c0035040d010000106400620b22a0540b1031900c0007420b01d5141504c80740a8203a07044691445007000b07400401080d0300500c0585820840d40e802d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 357578956 1250 357577706 357577709
    0x21b0d0c170c150a030f1a0d020a0302060a030603300e030a060606030203010618030f030e060c0a030c0b06040509060606031e040b1b070c03110d020d0b0a0c02030408030f0a050913090c 81
    0x141742c640f2400314447c01d071101400003d140250384030840130045000142405070b05d54002580503c00049403c2501ea054004104981c401c200407410440c248217003c030000c030011003d0107010552201001340500c240e003501c8400002800b6201850405e448841c2511a59040f940109800000400c481030381314005090a000c0c0d404a55411811075403480381e0704a11000141c01c0001140c000016503a9000444081028a104407100e1100514001c1e000c5003400d0f60958040c0b400340002000780c1482d01070280b24088181c042c00459a5250800c03240381c0000d0301158192481c60035500300d051000c8009401180544050110b80ca403a00c0c20f50080b1044840c04d04615505000000c0050316110b021800e80c1e5000070300d018003a0310440030039020014418061750080740c0211030b40c14400c0031001035000e150800340c02d03c40720003051000d0f40d4900c5644141a5150710410603104241c03d0800038000740f019030b240c514580f01820380001c0d1007680031006082440c0d607880d0640d0030080802540750 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 357580206 1250 357578956 357578981
    0x18060e0c03070b07120521090d05090612091f150f08030d0b06090a0626010815040f0501110307031410030308100b0406021b0d0c170c150a03 62
    0x150b06040001c0120303213001c2e068008003000c070206213559605000c0c109480140583c40300241350054401076045848030151103108060088805140340f1510030f4089940741c0c64050551031a002400f0090144513100920004141c011f1030414510381c1d8004c0d008884d0700c0001e44010520803a80b4840032a6644907500092034001480c100b080440e00c007000351110f06085c01d000080810740e000104401c0c1c85280d0314168050909580425555080303244401c0c2a11513481461340485464140c501400007030150100d141e0081c01e02c06044a4000042c43d031051045204205c020480d640d0a42900c1000380031059051000c020081c0c901e45c10705c250185101d402d00640300a040c103c41208841000340000350411948000081490101102c2e0f80c0040c01410884c0c0e554680d6410002d4a03020031054207e0349001c0f01c4c4600c9101d107044030300408a66080740c2e892104625082a2014403500b10501714040c1c01940c4600075070780d03920f60108044491000e107175a070303941280100904a680011004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 357581456 1250 357580206 357580213
    0x31509160207031e050a061e0e06011701020c0106060206041a04030509011427040e07080706050a180e07030f0515010f0504091e050606180105090418060e0c03 70
    0x411034a900140600440703410903280100001024514000002400c5003d403c1344280c00d86602003240c5a48840d41c01180c2e502e10b1103030302c3c0700b40c01480103480717140701d04402c3ca600080040c4507402281026900ca049100001443c00508103002425120554400e0b00541c0020342044107010380ca02200c11192100440c41c0c200b46070139503001e050340c01940ea4940c10000a105190300c5204080101d40c1404030501202010341c21a01c101c01d01110440c40c801c0c022170910030452550b03800040c6200c251501030300505132560400340100e504e5000142c0c50710801c40e28030694102031494044081c090000d541c80d030b084600e441d00f006810b5031800480c05484528010400c05020b00c5000c0c01a100a82440d04940e403c0581500315290b0185410212141c1e140a003414594490311440c110402c11559040c045a900c40d01008010300819490640c1c6040e1341c021518607610881c01000c0703954005000044440002c6a5004090350103c0120303a07407586c8510303d9a604608014150308544203c004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 357582706 1250 357581456 357581491
    0x90515090a080d05030f04150f06050312120a150510030603021e091603020f0c010902030712030c03030509031e090429061305040504080d0609050103020105070b060114031509 77
    0x1e049100090020203440144000b1408000c500031802400c00e4001c42e003441201c41302700c855801001103108552181c4100e110403101801c840042d14105010661542c101c3e60355184080090212186072100903c42001c0103e015a14404004601c0c0995070340003650314214814001c1042e152100b1607100b4220382c2810b07001307541c1c031044158032000c00c05201e0f01000081d2015000303405003040740c100105001c200301e880c03050158131034107074240220700306e810480d5200c1040040507070300c010190020741d900d5003940120b4003076040b80b038020024004880c030b08624242504540d00344c0f0038a480490b60300045040aa18280c000c49205509102c04102000e6101d00b0814181c100ca0a49502406010544007600010000300c80c3c01480064030038002c0d49010314094074940c0c0030101404d000c40c41c0150202c0c017021680308041c1038130380c10b0b11000e28040e0280c5410000440080a06042082c1c4000c011500c2000348091b500644d860b4015449012107501044200f05009104185031081d5026 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 357583956 1250 357582706 357582733
    0xb130e0f0d090510050d090b0115020c060f03070c0507050d03030c1d0a05100c06140f07031506050f0d0603140d260402030f0703230c010909050601090515090a08 71
    0x2e42c92884c80841c10030039942c5040c030030305a000e031080345000741c60300c00d22100001c2c1c40b0103a04500c41350306080d58280e8940b5501542080054001e0b20820141540d007400003c2105010b0047e10540c5070007001212800c599620006024030000301c411000280c80d1041a900c20350403840d50a25108000c0300740c94107140040110358007120501c00c5510503c90124a5518039008001000481c0d400c00414090380302c01b01c0c41100c41020a90b208245482d20000041c56940b00b031041c240d0107004005169051442d001c802c03203e68019000c00f003078480d41080f00d00d10615641c42544015031046c1d66001056010016850501060710b44080920203565015171a100c075011182064419143d034450711500c850021034a0560780784c00490307480c886c0910100500650084c0102e0840381c0d44038044901030784811a40d02c482c06030400314082080094240070b0148160443e9600903010315000301425602c0740000c0751030206008003070076100006a02c42d590b080100342113010304401c1009051a02000c40e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 357585206 1250 357583956 357583969
    0xe0a0c08061e0603040b04020f0d05250806090609070603020708090613030212060a050a06080c01111204030f021903030801030f0302011b0305090610050607060b130e0f0d0905 77
    0xc24603403150340103000d41c078004a040e9041c0b80103580040c080d035031070f032030240b80403034000300151401d80c46941400c11006061030b00300841c003540c942c044082d00406d0540402c050044000c2815100d503102e0344000071070414820840c0340c0c46510410000c000c141042c44c061421f02d141a0011001c0500410222000c5403040d0110b9a0762401a102c0c60b42e07800341040010001c06032031700300960200b4040034840d01c40f100003c40c1401401425000c10464480e036103441c0480e083c030300c0b8070a001c0d000111045441e41c040e520035040c1c070714907005484942800850303002103544a604100c1e50280c9881104095003008103101d41e03005101c4440b08501415134074040d2104605101c010f212015000507030003018800e4005810600039410111010001c003480500608011907100700d0501c50100010302040500e00f5000880d14003a00f0f040c5440460703110000600408002c60f504803204001d207616007402e0388607548034502200b0240c0500061080031074100581c0c00540402c00c5441d500a01c002d03694003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 357586456 1250 357585206 357585211
    0x10809010c2003091002030319050f06090403173d03020d050102040b0f03041511030c0c0106030b0403021c020714010c030c0c030b1005040e0604030c080c03130e0a0c08 74
    0x11542e241c125a040300c1c45859807142031240c54004c04510b400110242d0000003960103480356030030500004d280403404100720741e42203425809004000020401500303103c0c4000c2c2d0041c0c000d1416842403020100c80d1030525034151600b03c8a2002c100d240001c0043c0c81c0a10540c940c10440060f080220010190301c95441c1808043c2c4030f40b400b810900100700c02503045800500044118036152460b0641d83c201320b0300229020341d5108000000041c030050580314040b50114500d5800d421511050344081c4280c0050002601941d40c4820100c01314264510907413083d407080e0b005004000300741e146002e00804100c01002554010390f01445002c03030b10313000380a140100703281c9201d40c0c1c050390404031a03050007814040e008406d5224040240700408140a2050050340d100b020304550307802c04c2c8070449000102442c2070790003075000b15002a125502c10340585014101490508030300d01599400d43e880b1812440300e0b4000d5610400c220845109403075484010030004100200080c1c201030b0550800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 357587706 1250 357586456 357586487
    0x1a0d0b0907090e03030a0b03010b03060408031803030a0b0f1f2604030905030c010224151005040503070e061014130e011409040f120e06030411010809010c 68
    0x250400a01199010000140140030340c0e58140000003d03d8607068a0754401e8461035501070a081007e41c260030140280400000054010710144c0d6850329041c500350000742a07108110b070901d4160168090420286002d41c0c900d01002400003400e00410400030b01e0020189d00034048000910049003403511b4100469400313040c007924002a02c0034085480d100c020100c404081d2020621050580c013100e21419543c0c10307411141c2c1042c070000160303600c40d07101d80700c461003007800c20550900c00341c03003e111604490b540f101d4050b410165000035a051808503004000107001044c10030607450208808401403240280c8040340d824558085402c0f15007480c01c8030188140d8400c0304a4000ca681c08032840c51030558040236540d612500305405030403080c40b5a04200c1011208009640f03000300001e8007956200300030b40440800c5079102c411407101200503a0501c02880d0040c007482e10f5840080d44518417a010114440510a00140c4034440c0503109040070b81c5010a0320b0382c0c41d030b08021072100d002035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 357588956 1250 357587706 357587723
    0x90f070f081003141e07051c0f08030f0a06060801060804060207210504030501060504050c041208090d140d08070509010e0303040914190209030c012d121a0d 69
    0x10b8000c41c020404456510040c500007507140007000c03540e004200d0824a182c44440000452070880c003103035441e030207405107650108641055440c041c080c260607a499610070200d40035418402c0e00e43c0d02864004803030301c041003002c0104121070500c1ca44141c80c00340c0110305007050194101b643c0100102c2d00104001c5c445031b070009034a4240200d1a04100d54030358031035460300200002d180010306681040c84103c8040d0700308140829240b8003405068031030321008c0c12440c1001c0c41c040c040368044100a006944a00c800c11501035a0744410340d00e0000c1901905203030950100042c80c030740c6001e00c1c5030005400c008501c001d101d901c0354000f0845802d03c2092901d46409151000001d055105a50109140c0762600c81d21022025022490074031402909544030b9210524040f02d60680c0300389800c00340d05810202c45c0070340079802001211010f85892003540e07070030000001c80e200700c03804214240d80400c3d01d0180d0482c4504a90080441912250184154081c1c03d00c01142040c440366030700609401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 357590206 1250 357588956 357588961
    0x220b04030c0b07170d0f061401030e01050408070f0312020c0c0f01020a0c0504111605060402030c031c051c0906060305070605120a0e0111160b281a12010b090f070f08 73
    0x176a00d03000f41825881d143e030200052170303507001c2d45051850000c1149001c2810b00d403c05011900c18442d16104a0700a4802c5281026942e02c030007145a5152044003071011000c0c0ca205076030118400f50100300790b1000144010510b46040000100c64060740d541150301980c1018002508014810308031403069401251007058800030751214025000340b2006801440c4014084c06000103003135014a00075826a11032070012028991100316a0b03c101000e00d002800c6002c000e8030650041ca5001c03000117100602103818003a80c025689018020341d0100e40304c50f401c0c0300b444024444a401051603003412854003216500c0103540e150001d088513049070341c0d250340d840300b0202074005900301000d02c4a059602c509030300140b03020f6034008606072507103003070000007803207a80c000100c540030042d00f600c1202c2e820280c810804064200c0510302e20144041c40c0000840d86c440305503442665428400120b02c000c0c0c070109001960200a01c101e0884614005000c003240e0081c030030550759456480c2c1580307a603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 357591456 1250 357590206 357590227
    0x30702041a3d0818071203170106030501050f040203060f06130609062c0a030c06030b011103090d0b1e070804020f090103050c0105220b04030c0b0717 66
    0x21a4881c03212a0004660030000b070000ca02d408810000072199100704181c0d605403866601800800011800850350316408200c2c4421860b24202d4040030507070494042540703801d00c501d400550150200d001c9442404a40156620310021501421040c46c2c204265850040058891328407581c2260013582d00101140f200e40326041042c0000d00d025019680d00e0038004039029030010540310b40303400509607860120b41184112080c00c000d01c0d1204500078020a40e0b0500303c0072030380100c81c0340d61041d405100040082c034089450340041c441c41e2000101004c2d00c0c40094100000c0e1140030000d034000300083e03241d65031514400c05010790060031840c12555a0516102c1c9003400354082043c2c2c060315010811000d42c0a0001d40c1720310b00c261048064019440140540c820b020b0000038600c2e005960f00d0a8154840d101505c2006150001900c41c060788032291070071224260003e058801c00018113005214024400d1001016203202462401929403900001d408603260650f034210000900105d51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 357592706 1250 357591456 357591491
    0x10e0c040e0106090e28020f0f0324070f141210090f0203150f030a290f01240906120209180f06060901140306010203040e0103080304061d03070204 65
    0x9440d81d0102041007601600f200c2d07075200c821a00d808403507003a00c0341c100c01e013022002038a0b81b420741c00781c045501c03d0200010805150000c0348801d405106842c0e619401101007844c414403e09544a018204d003001100107021030030701e00310103047c0f010800c3c20b07014042c0d94404071418880c24900d0085140c540100c04200401180c0c40b000c9083c0c1030a10b4542a0801940154001c0c49000381d502c00c88540700303080c41203901000d40115407540200d80d00c400403454008100d2012489050310880e0a40c98100454140f04241c661a00005100005000c6404043e0800c1c025040d04500c121a14051400081a1981038081c21081001c3c031080400408880d8050314a4090000e1500c100312000d22134a10b0059011101031001c000b00b1408a00b80e400c090b0304442d40d041041c1e59110321003004ca040380c00740303030700291070710381144010080000c08904403c5c98501843c03080384003e03500d040c1424030b54103541000c00403a40b03030f2a040402400c1e1303031030020403a0035040e8140c60101d20710f2003d00b4040b10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 357593956 1250 357592706 357592709
    0x609180a0807170d2a1d01030f110909060f060d0b061c020913180204091a0103030c1103010513020108190203100303031109060301030b091c0c030e03010e0c040e0106 73
    0xc40700c034049940b500700c43c081e4000355045180c056460446a1505c0b10f01e0314850070b60072803540420488203000300b004201410790420f110041c10086003201201c0e00c2901160f0100c644134000b644003062036031240c5000001590402d0044491180960300200022000d1060007039034414035548650955407512180c2c29079004180d0f01d005401d035042c040c00b050000c0e40c41044910312940185045000c1c08109106038902c3c064006110320000f0500d81c24440141000b120030b681e501403e00c04003403c2c1d81d8048900e40a1446640c2e8143d80c184145001c02480e04290300f0345200b64148410810940201150800095024640798040b07880c3e104c41091000072a0799a01900c5000000700a00e41303d6401d0018210b07803080d5801c009400c024103100080303000d001c0d90039502400c200010000f081102250340e4200ca0303c00240c0d0318a50b0b00210002603140300c1040700e000f0621020340b98081c1904491028000f080540091090319449208141c035801d4115274903204da945e6100400000c10254080d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 357595206 1250 357593956 357593993
    0x60f12190c030b0f010305030d02090a151e08041e0f020915030d050c030f0304020105040902040f030b0a05070909020c010b0901030c09060b0f03070e04090b040b0609180a0807 77
    0x40c8503203014105006064242d00040d1100021440490710440956007030a040300e030031501450500343d4450130b03080694800c1c03d05990001c2d5140000c64403a041010344075640f1440d8907401c00044546000030100070041541d0b4003880701110401000c00c01c00204251981568854000860118505015030710054000650081420740400104d0203254a445402d000c04904443d40032200c110111554440c450840c3d00b55041400500001703880700300590b40040c4141001030509445042c114103c4e0040da02408075400b42e01c2042091010342c94205400010010050209180190020f0000b884902c503000c1d00c9580041c041c0d000e11002e60001903858001014a18196524105102c07210f1082c001d100103540350050014007020b90300100d484030720a0075003141c2195078400055902000132001690407503100d560403000246050803c600c601c0c41401c1c4461503040030300c18024419801046090000480326442480e20000500400b0156001403030320360320200352030411002e03070040e1440d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 357596456 1250 357595206 357595243
    0x1e080606040314150a0c05090909070806090c0406050f030a02010f050c030a0806120c0102060103030c02041d030711030c13090606120b04050f01050106050301050105280903030305010b03060f12 85
    0x80e0f400c100c0030621404404441c0a00741c034641303d02000358101c5e104c0d0f0700b410002c03500812941d2101e06140071817a0340314503800103541d006030351150820305103a8121104042900010852523261521344a044042c25090f1100b45502e4006000b290b614440448043e05000c105031a00030a03600c02e8048400c01481038003540d4a51145c0d81024014441c29203c591040c0c8880340084c0302d440c8001420a100041680240421791070750700d0944410742d85200c244c3e04a1b4035015a241c0150140d211100000b481da401155144d03003034142015204100492a80b0940007604001c03155591503405071072082041c0400944c00074940341c80002044181d10840c0c0040038904c0c0c402c20300100320452031080d409031003650107072020414100c5c04c8071824081c80020070340500050149521030009002c18400c00a003085450020002d61000303050f1180850000034050401070007015814001da03401095803080c04c0b800c41c01c10700300007210600d80c01039082c062000010911044081004001c4803094541c005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 357597706 1250 357596456 357596483
    0xa210507090e19020a0b0a020111031e07090807050f030a0203060103080406080a05010b0d0c02160315060605032e030b070306140603040b0406020306150f13061e0806060403 76
    0x110409861800007049a900800710b4902540721110b0f0301108442d401040c80300c9141c10b0410501c22034101100e039104541d42c529450200319200070007507019140409107071020000c10724240c941440002d00c3e02e8100011904c08101d034802c0041d040c410340300d00f00e9014072107400180100f032030440c074020040d50610810000109006030000180107441d1030344d885000980e41c8095a8064850a04c10450200010044158154116031100694240368410f8480e81d8200a00c842c1d00c0041540040d1400140c0c00074003041c25a49100d444000c0c040c0d400c149055182400741640d1148441c180c940315a06d01c401c880c0031010780c1090140185500ca1f000c0c03080707801c0c140802802401507000e2a000d518001000c620b50f8a880340c10750340724030385c014202d000703580e5141c0d6508080c1d08003030081c0ba0040c0c11200002110321032400036107140c0d0b0902910701e813140c041c020300034008441c039446082848010441c1050468405c0f81d103034104040c3c3e0901c004075845d0840412410b1181d03510140001c0b14080c603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 357598956 1250 357597706 357597719
    0x1170c0604031a34030b0d060b0108090c090c070f05070801150e04050303181c05092115040804090504060b0112020f0d050603010908031602010e0c0a210507 69
    0x24411080206010f404801e42da0340800700e0300070018a0b0703600e491444c401d40640940800040c501c9500505260105540c440310020494603180782500b140c80035100d250100c03d42d68403045031303a0310489a400428100200030b0108001c1c80c000382403c0d0f002480064801c1c1031003490301e90514219407000454501710340c0c1d90720a500900500d280ca6a0718205402d0029000d00f4400c84a8000c82d004400745103142c40d05824940c500700102003512460007402400764810b00d101602918a05403034a543ea0b860130031104104071b0901c0d0742e201125404100460500702d8000013103e000040140f000d4001d59261030074103460754001d83d032121010178101000c0004200d6160080101c191084e01d6030344100079011041000da000300c00c2c408840351800c3c8441100402e480c0c00058005c480900000ba04d03080c00e813101c82c8268000c4842804d920341c0b0650a20000e40e091007603502d0b0f0400c60000d4206000808001041c2059034460381d2a0700550458248560503022403d100c0c056118080340c00850b603514 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 357600206 1250 357598956 357598973
    0xb0d1d0610061e0f090305030c2817031801060b191103031b070f060e07060504050607290403020d0e060c07030224040305060103020a05030a0b01170c060403 69
    0x207401c07600c000e14070704000414074080c0b4503003103001043d080419030030181c10000f01c0340f10b0290310300802082803a0340c002010800510080103202c4181000d03080d090340100f1a501da803115003901200c16821040c1d001302085640c1140000c00c0003c2c0300c03880e620b40300c0000801501e0b21000148072554600600040c0d01207500005202c41c0504c1c402c14980e03262907060507a45e083c1c544c801694031b5001080042d0391215041202400c0401100c42c042c10003c0d5030700c1c1e48040f02d4400360200c640d00c1e51020065180241001108014601c80c074200b440c280c01c15000c01c466000d000b0004100145803000c070203e14100d4035500c0c916414000310081d0030301e0b0a0500075a100c40640140340458091080c6c1003c80c00c1003811525095003100c010b14100d880c560900c0040c80c01e260844d0498221040000410307141c0e4801400298001c90040441c0d50450042010740310f69680903620a501014180b0005503007484d0150454040c003854007858803610000d5410b2102d50001541d0040700020003008010310b20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 357601456 1250 357600206 357600211
    0x1208280305041e03080c030604111303050c0d030e091e090c01110a0c0510021203090a05010609091104050601050c19060507020f030304060c1b26130b0d1d06 69
    0x4501210000d0f40a5150301000143c078400900080c8415002400010702400115048140a400000d201601a407500c085401c41200022002c0c01e05d8820800d00c0000c10042606510480b0035090401456070084c05456010200324044e500c144006401483c2d211046503603441c400f20095030340d00c0c008008644460005070300394045049641d9030812a40002204805542e10404540206050104200360418020408800c5100e05940843d0118900f03000d507028640701001014a0300c02c40c0750203800d444042c1c014556040c130704071400740403032004d818454003a00d007582d00250a4031401d0040350300b44140502110b041c4501000c49444d4107071040c03a1800240100c1003000340792218202207850706440d50301c0750b641d42c0c028808100231905d0303540800164280307420305051140d40c44402c00100d0718044e10580700809682e50340308120340c00d18a1003104c400f140060358500ba0344036500307070407542c0d260182c0d8075483c4002c5080d810940c111340c01202400c1c49951030921301c0601005107555482d04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 357602706 1250 357601456 357601463
    0x21c1e0513090219050c0a050106030320010b0d02040b011101060f030b01090218010f03060f0e01030b070e031905120c0f0f0a0209011205030912030a090f120828030504 74
    0xc072800096046452003601c45a110311241310101c1d01240360101c03200c0d00500b1002c07445010f1070b54082c00042007413241c1d000841c8291118030a080750f103510040d800068001020030384e41040d07100015a6034010000400b03540c1180d0024140120b140100c2e280205980c2d0300629620380f44001c1110401d552010044070310444040020342e0301e07000791000340d0290700d041600560402180701a1580618120b004240d075030f1500040c040d076034000350074001e003650307205c1b4221400510040c014020304031601d40e4800154200320744030f01d4030440882d40c0d400a1640ca80102401d50000d0740c20404107010180040604621060315030440caa1817640784c500c401c6c2e01c03c005114441b20f01050f44008600301c1c00b00da400900c0c01c3c1441c7e180604e10000d0b101c01e094200d5440c003040140498a944844841c23034085903640082d900d032182444054000b85e100d4001c03086911004200f0003a590301c031b11200101c03580c011b00460b201c1116885e0038081a20304a145d940654110900c00a6150316922540c8101d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 357603956 1250 357602706 357602737
    0x60c030c010614120c030a0201050f12011d0105102012070503190906050409050a060b0c06090c191401030603050f0f06130b061e0402042301020d021c1e05 68
    0x1a04c41c03259032444084502ca800d5040528170a01641c060b03030181c12030035086c194051814a002c1c0108004940036080300c0126990701d155000300102e100d080030301422003518012010061044050520302152072400326010060512040701a41405141c1010448a1031662200d04514283d40c503a048aa5050351301340c0000d03140850140702e40024000c880c86925011704d1f090a01e040c081c0a400000d001910042c0c46c2c071380001c6d070125424014132180521401130324907424008906814156441409485032030341500003844c0c1c41d006006501200d981100003109100481e0050303001d030005901c050200d00503800340302807403000880c41520f1011040141e6400750340e41c251140b004880000040c000010000004a141c24140413038690f13220030500000141d01d00d24001000d80e13015170051019040ba0740c2c44400022031110420300051402d00107000300f0340010070000d580303150314182c01c81c00503001e100035550640030320b202c41c03408030001c0c500b01118044d401010b01264414900064070a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 357605206 1250 357603956 357603979
    0x2e090507090c1b060908090a0909020901090c12020c0c03030301120b01050d1104150506040b0702041a010c171e030609130c050f060c01020a0809060c0301080705060c030c010614 78
    0x5200e9403480c0100c43c0110305030b00c0f07100040c2c3c4071500101042d10f0221901c0c00c0422400c2525654100108010041c1010100d207400c01c602c140101084c06074411110340303092903441000c1075000440741c01c080c4400d150040e00c0d803001103981460304000300c0034250140800400807071995405141c1080e000d01500c41c40d00141d0742c4406000220041040140040c0c0c05d5020503602494150071098107290119220001c5540303440024100d0b901c0340d1300c129480200042d20340d0841c00c060241581203507107003691540780d85040c400601001d1060300024a40d41940720354500a01e46501510100b0000c108544030034030f0403914801090340140c2e00c2500c9805900005288005540044094154001e4a40d86083e1500c4140f000e174211644071140c2c448820b201040c5070400910181100d8102680d0324942420507050f01414400080c094030351005081006102c481c00001d0058102d0300180d0b129640d468003c20f0150440c021031800403419428803000148651071410300c0503003030808940381c00140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 357606456 1250 357605206 357605231
    0x9071b080a020115080718110c0609030414030c0a05040513050d09030201031a031506060702130203101d1603020702091807080a110f0406050613031104050402032e09050709 76
    0x6d0115101e046c1103c903103176004000c0342400c0c0d00801200b445541d211030401004070805428001c0c2100c8900c0349a201003020010a080d107215440590400d8010703001c441a40004594134074054000c26004036111404030352071501c00c184828a440d0440280d60b000e003401440140707107100d58801680002c0c244624a6103540100c0c008240014005004105051925017541c0442100a0507158412014401c1c40056100da15018074521400c1e880180d680c501445283c0060710b064000d800060384000d81c01c003588103001c07044e603041041e45114194a44500d00704501910460340000c4d0803598643c10300808444c1c035180751011074407170701c29a8019a103464620383d444000314006403002003e40504000340c101108d04400280700a0804200c1c647c071600450129070141c5240664080130078020014040f505145d903051071000c96040c8004d05260700040d644008040c08011110821041140030840814aa503180c1508560610a00c0210706101d500d40c0c000c0d1044040381820501c0e8400034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 357607706 1250 357606456 357606463
    0x90503040b0f04080d11030a0e032e0c020102030c040608090a02040f090b0c13032604060503010806060102070506031f17010212100f2c150103180209071b080a02011508 74
    0x110720b1b014000754104861074400701d803040e1501c41120741601504042c0140500440d00400000c8240d1201c07811820f400c4030341c10f04a54035040503d0440e4414800d024a400628040310b04503440da1501c04055224100920f04150b1040701c0254000e00c0c192514980132030350303080080b441d40116035040e0745030794582c0380361910311030a84075034014244100c0c14800a400028200c000a0300c00310480180918044100407a03441600300030b0219402200400c4030315030401c1120742c80780080c40507020040c60000413900b44d010107440600b040ca6104007001001c02090b000c20001e1500340e5815180e40200d03000360b4004d50050031420340504401d030026003001942e410031000c0314800f5240522261405803581d4401031100b0041c0e80300081d00015100318800c0309070b4180034107a007050b034594801a02c40090119101400810a03000440103904056600c80c2d00503940b0000030700f896800e030082c240321a44030340301d81c04000b0002000401c0d40060701d50705501c0800c0c0742401a0141e807030607440703006555a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 357608956 1250 357607706 357607727
    0x6131103070906082a0a030e03070807020a170a060b1f030608280209130f030806090708091f11070507050901080f0706120e011b1202040e010504090503040b0f04080d 73
    0xc4800984001004e142c1c1101700521000c82e080c500024880814090141154010700050b103d12102084e403905600e8005888802020780c003c03040b24091052543c16250b503284040544110340c0c03601c0345002074076141080600c10840c1d55142d20820320260024006145a0145e002a440303a52075030045051040300c02c4060311032b14035851922001c0740e800c001410000401544050700c0c8180c4d0b020025485e41c40122407031f07110303494034140361510f102482070702c441c000c060703800308041c120134401110804034509001e4000e00c0b1000154a04404040300074000000c0707081c076880b000086100c144000416804161607044500301d000d41d980741c407444ea8503049240e440500c0c1d0009031080118a00900e0b07110b000360092030000c940f88000b0800c560031124400c1034084a2a0706500030306021394071804400751504050400c50030035003030960300441c22005004050245945043c03001c14004100180c034010108440340d16624600131401c01c0894029100e044c0c9035201e00074054135828083c205111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 357610206 1250 357608956 357609001
    0xf051807030803101703030403020105070f0e0904020a0b13090e010605100f031b0e040e0712030503060303040f300803060105160204020412150c05030613110307090608 74
    0xc000c03070841e00c91085540c0040c00d000009251000001140360341d0813820704c12400b900c0c0180d034a034581820041d09640c802011201002541c40f0951020340d0018603003412a80156464106a0740702e1021a0210715250400005280d01050104410b594019032009030b50a0740400d1002d907070b10458a40c02e0f40c01c1406816800020b01c4d001e1107000b449110b8580c0ba0301d455150100e00380c401000100010041105402d001454840c201c04030741c00c150041c4050301c032024004100052600403116581142c064008007042400400b041b40b0380d40c100143e80242066090f407c003050307030703907190510351407aa8000820306c1c4003209080c1c0d440011a15544040d01e4020380c4407881c50740e50100450f0035500c41210344481708000f24259015843c1d80c4042d0001c1c08002c000700c0381a201c01e0804100c4c00d407224022001503070034401c40070040c940c45000d50341c0000050b604101e44074004076011001d08181c1e649000e001001100308140b00744c2c0000c070041102c01545410013641c0b00c075030503458110b4203980f010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 357611456 1250 357610206 357610213
    0xa0c1d010303230f04030506130c090c0522031502070b0c030a150602031c0e070b0f211006170115090f09060e0c12060f180702010f0518 60
    0x410200e800740901030400b46850451444141c0602e903c40c00641101040c640910000b207024410031204003c1d940d0080e0811801d4031100289503501160106280500d01c42582c54800c000d1100d030140c016207030603038041600200c5030000f01d40600407402c0e82d440203840d8084400400c5007150502e2003220720b0b043e00075010042c65a50121201003560014107055500e40d940c280d840c024040c0d01c80050043e040c140c0c061907843c542454502ca6030303840e1104c812003c03850400792050072000054044204d40103003050989540810202581c54015080b0312102c40241c0c4002c200403052039031060784205510b10024140319120541110808101f00180403001076081c01408540c1c00346100f4064141c0501d415030780c054480d502e04800b01c12030b40c485138140e03450b080309021607070400aa0076401900003010030b040600c411120f46130a44080c10a50096010601c4055151034003202900091821928000c9608007080c0081c002c000c0102140d148278500004900600c00000c515201404143c004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 357612706 1250 357611456 357611459
    0x308010618140f0301021305040c030e0c040b0402070c091e230a06210507080a02130e070306020a0e010f0801051005030c040519090b0a050d0609030e09090a0c1d01 72
    0x240c60500080421194007041c1000c1c2c04003d558240010103818658103101c2c01080c1c5414140820743d403c414140c81418149052010341c9a000500d1441000b03040f0780c08160110b103080401e00a1141c042c02401142c110b22000c48c01154540040c00541c510b00c0c49064200c12481c1280c080791040d401c00e000748502103207441041c840c890711458112164240026541c1d80c2c940b44d481070242c1d03203c003006000131503000b40e4040c440b051020301d00a00601003e040d000c40f08d5400030700f406906207035035408903540d0b0041080400b003c2250b50051070748401c00715915084031101604ca0810030b0401c40c00500700495070019103100c0c1d11664101d43e809071441c1c560f1f0349040c400340c42941008003400301d0030b2030900c80041e05a0f40c0d0605120070158134003190100c50b0070302040209a40007051864090188184100502d4443c0381d280f0f0103440d00002c000528004610342110800e4080d281030f6400304a410a01000c20340100360915007501c01c1d010442d05130341c0ca44c05820410348540c11042c1580d4000300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 357613956 1250 357612706 357612719
    0x209130201170108010c091a030c07061401060302180a0302011b0201050705070605030912093a0c0915030807020f030a05060a0609110c0a021c021c0308010618 70
    0x510a0006205040c66220909400945034550400342d001c100d040e034654100c14213554021102c400608840e05281c0384078407104d00c840c4288e00c005040e403404e604001503084d05005003a0311510302d0303078803000480c892075035a028014040c0d00329103031400c840d40d401285401c4618005c40042c0880ea4103840c3d030b10704500c21f140502d90b0910102d500382d05206081003000001541400602c01504e0143c480645030304010a02c80d01e014540f100d034a9003070400300169461039594007401c42c1c1910420b00201c0b0704001e80da00c45803620380711000d10200100c080c1c46460412054101c181d0656042c10b00800508106040503c10881d03280300240480b6010420300001d8242410910b0707003c0c3d00a41220b5002c0342a54505207044412604000540da07103400030321030700d500f90051540485044012904101c00d9400b529110200b00c5402031040c040204520316400798150305a42c66134004007004050400c1c56843c020307860340c540044001542e0000007144c541e00402819441d40c00b02204112081d0600c1ea = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 357615206 1250 357613956 357613981
    0x705060904023f01030c0302060a12021902192006090d0f0302060f0610030e0c0a0902041e0b030414011107140d080c0723070b0408100203040209 64
    0x120081e00301e6000c1040440314100c8031481000c540e010421075901c2d866000c1c1c1d107084011401210070910082e0303001000843e24036503141c41038980441d81c1c1541c2e00c0c4000380c1900d0414481c0016070545e030000c01c203804620000c1c0090342c4404201e030240c8200c0715940f000390340410386410000307000c00c00c001d4641c840e610032a0800d4000d00005450945048488030002e01001d2000c0c4084442d0052084030008040d070502c543c5400c010110048800307400d02000240f6004400d000000815594610f244900c840c1085184000c1c10003600414003640ca521a01000c0d44c06801225120010341101c072000d00e101010100031a03480e22101800c503291565602d11211482c060071b01b07550348031040e01c095aa00540148420307440740c0140380e40842c0d80c1000c5401d2124400703501d402d02104c4e4003001a41103000003103130720040c1c4c8061500600070714030000d1101740d210b504074104c0c0f40c8210500800e14180400c0108190345c60380782281c0750403085483d404103901c0226002508101e129001c40d0031500da19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 357616456 1250 357615206 357615217
    0xa06140411010201200d061d1e070504030308090a0b07020c181b0c101802040e0c060f0901110303040606030c27050910111305040506060a08091906200a02070506 71
    0x8010101c0d9450303a823003440640400c0980c01524000c800d00c01e00038262083d091108041d5041c08101f0094038000348040d10b9800b442c4005810f12803690300040024405001035210b07158825404006410f282c1d030000e5883c00c400604a010382010184001c01c0c4443c0e10b4114400d907280c141d00405d20100444002c0305400c526242c11aa100e160380003184420140600070034400c018817802c46a441c03600400c800d442c44a101d00a554000102061003a00c0b410210760048031400102551a4042c6004a4401140d5040040180808014802040300641210081740e0140d498001c1c0292501000760440b0045100881405044c5484000219132074100c198012411000c5c0c0307109e0303003403000d4400a1f501c00480401d1a0800000d15400c81e21405906802614060358100b0141c500040402c00c0d510030f8420708018414401c000640f016020000304601084000c820040d41c0200d2601e01c02401800202d4000705a24840d40140070010b00290384041416a00034081285088144051980007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 357617706 1250 357616456 357616477
    0x15020c06092a0a060c030c05010c0e0a09020702090106110307021206070807080c090918010504050a03030609020f16060209100503070905010c2303130303050403021503010e07030209030a0614041101020120 90
    0x300c031f4650002c04c8080c8200044040281c81e0315680807642810081d4034500c68000d0a04503205121240150b2a200480e50640d80b06007484d00842c2004110700b49103000b9030f18004d500510300401c50340080d60200e800307800b07002e03940c43d01580da0b200c0041c140e40c41c0c0f00032120800100400c4c0980a914540101100d401500c5184074142c00782481c0c88250a4800c11281919541d0102d240602019410b00c2010300500850104508280841140130510b00c0b80c035020a2110007007104040a01c480c81e0304542007410f0080154603c1d035151180601690001c41b140e50200b41400000205940521255292079900c4000d50070780c0506000c0484105060000d070201510090110300700d000c0904d800070003d9030003625040e858910354410000100c50070f058458040005000412049000e21040c50f00164603081c00760b01c44507a400030a1a00c003440340060825403c00b0558060046034901c801d014502800507010003c054ae4016403c1c0d440601b00b0321100c00071200003a5984a8501c040c00e8034400c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 357618956 1250 357617706 357617717
    0x31b1d060a0f080303060a060f0207060c05010b030a2004090803040f2102010603061b02030403080f09091501080a0c081f09020310051002010b0d15020c06092a0a060c03 74
    0x4980320944084451500090f9140e071000040c0034141c641214054010036140c5040c69000040c0f01c0029200c20291280d1014058001031346c4041000a421407460b481c0f0207000c9500e071914508005005c03000c55444401010f0030440d80c41d841d41041c1c02200d41080e001030030745203151900d035140c101144040c42c056805000c044c41e004010b4000b044440040d000b84d40c0049142401d5007000012aa154006203920300c5013100102c40301500442a03c00b1681c2042a081c0c840c100d0000b985250b00c0ba0302040c56208288004108810295280d031142d40710080ea908207155560582c840100ca000340d90000100c0c01c40000105425502c500640040200500e4075000300da4603248081030381c205881c41c13480c0401003072080c005400d10384410038200b980e030310081c4011122500890005443c2103400743c0071450300c803201c250382c0044c0d03012180315112039401c0303404601c0c110200e1600c880303001c0c0513901290350101704120400c1880c7e003020040d4070010018003950707251242c151034800d40d00c0340443c00c3c0103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 357620206 1250 357618956 357618959
    0x10c020310090b060a05010918020c07081009120302090f0f0f210120070605060607020d0f06060b1c0203130203030a030504030e1206070807090b040b04031b1d060a 72
    0x300307600600400b20b104240d10400d40c10140204140300d05150005810000d410408101207412204203146845248500580d80c1480841c081e040c50880d0300842c10600c940c1c0e8481c00c503a544da9000900644c0900c43da00b091102802e401c40030707445401c02159019070710a910414503d003142620062100c010070741c6000202540105520180e00f26050440909084030086180c0d828068002c6011100c2014040e101d40b4808080300760007207072800750500d907441001540355110001100c01070f0327400901c8140000031510300300b604088001c03002c50f401400c20f2000114842d1080650f680d1039007c1e907074100c641c1d010508a100a40004180400e100b281e494100c015032800c0c0000c1032007204941c3c0125182c070303040c1009421004031203040382c012200c0c01c0c40ad580c0341401144c240d030000c801d89001100741d25030b13030300495440480360040c400300540010000b0385810400010421648554404070480070019211402000284a400042002411184c09541407405000e6201a0040c20b910506 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 357621456 1250 357620206 357620233
    0x12301031d12040302030d02010b1e04060506030c070515010503070e060f04050108070609120809210f01020a232506050117161a07031e0509180403050702010c0203 72
    0x4440b0750300ca070602c8800030b014029403e00b44501c00c400c000c40e00090001402c0da10115550070748800031110048408d01042010b81e07903e8100d0300007407100821103900c0742000000b581d025440700404444502c544a013040c011a20800554100c607002005842d0041c0341010b80e0060010061500d54030001c03442c004e0089603661300c69a40a04410401800002d04003000584203c2194202405682c0681d0101c0000386110046401e0000150340c1c0303089029084d04969038040c1c405000b001c0d64040c515a0844056055001e000ea01070a942c03140007104010702c40000d07400c1034440100416100300150405d5800c0406880031801d0700d0b04403039914a086440d81c1040390b1082c1c00c42d02022300c94414803403480204109040040808100e5070881c00d290080c8050114501c20013031b0384030040850404140b500410024421741182c7c00381000303482c0f041c1c90040459006c5e150309840391144494840541500a00c42c52090707616444403880d22055030019544201d50b408200c2e494403c014800110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 357622706 1250 357621456 357621463
    0x11209051002300606181f030c02011d0a030e0102031e03191a010e0103020f07050604050d02060702062202031609110903030405270405060f012301031d 67
    0x140f801d9180d200500540c2003050000b82c004208460301400000414001d0980d40c1c10212400d424415881d4114240224080380f103d002c0b442658000310304000315640e40c150542c000d5211300340d240d4003c201b54000054100404810300102103150b41c8520300d2100024001d0300701c0c2c00304201c1401124101031000c500c00b1300b88074420018008034140841881031a000340c911200c0340e00d540f18418480406d9044082c4000c10b503205086040000021944145c1e0340a80d0488610031002c4120680e01c00307084c2801036130307840309a80844962007800140410140301251050281015501800c055141c07600c0000240309481d134500c4044100422204c0142c1c4c08105815202d041039841d0651185024450006c0314a03190707204060309400c001c103841564000c01114190385084500e00d0090b070203003a098500800091041000010402c10701050000004d40742d407090000c82400011685c80e642901001801c5200c014100c44440301684130640c043c1d0003584500b07143e10089104e842031050030f0b601c2d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 357623956 1250 357622706 357622717
    0xf090c090c2102371205010312140f0c06040c082b02151602010b01090b0d0f06030b040305030f061804020d050f1b01020c040b15030a0204050a060e0f03010902011209051002 76
    0xa04d84208a090071000d4101405440300458076000300040d615580754201000c110704241c41c10011a03044010b40c08810800355082968140c801030b4071200010001c940d9110162030039203464403003240009205100207072000c2c003c1c608102c03000c005040c181c030206000b280c83c00c00d1410f50041c402d94640b4070031803c040e10b00c9924000d10003056800d5401010742141d4a02c51214108400d4600602581040c10102c42c20104c000c02d00040b0f00d25070340c0e018001001e550704010f0450000f64244000d040d03003c0c0240d40200303140000c02200b40c036440108151462581e00d0204580c50001c0020301510f1700c40c4410525a0044040e02d0342048001501c1c1d0a000005041c801103245c0a65502c04a503410421100c50a000381e03010000518044005135445c1500195400e48c0070001001403181d00710b58056a004001c007805442840b40c6482c001783c400181144114054140d0030680c04983c40c050141c0301c182501a11070305030404180740404054010403209a80701e20400c5807031007946032584010070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 357625206 1250 357623956 357624037
    0x5010615090302100908031b030d0c02030918090c010305090c030a061e020f040b160c0f06110105040b060f0a030b16080c0322060f090c090c2102 64
    0x8604608600c100404139034005020410001940c0c824400728000000301c3d005030060118080c51100b000c10164618400c40c00d0f0400c0050406071200412a000805000d00c480c00716002ca0380c2c0761406a0070520705200312040c81c2c46034004400101c155000e81c0c02a03410500c800d090b10004840c100201e45000b0b6126421203996945498032505808003480308a10810045030561820b84640c1a4242c2800f49029446114500040c810305108490101e00005039000103146c3c825940e90b00d200721030070b030f852044201050350321103103030360000301849418429030703200030102c1c101c0d12201d0034000700e01030501082d500445841008004a10342905551203a84080c0c0c07402c500d41c0342d0342001084580094088540c52500740180a8100c40351401d42d049002c141c44011000c00040c1001c9001d0482018540003941c50580d03140103128107803084000783d450480c0c05001a90b44604129080c02519180c807030b240808141c0300300e803054160001c00398504403074020028020f042a0b80d0440045260058 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 357626456 1250 357625206 357625217
    0x6060b0c03070609031b1b08010b010507110a0e0408090f0d030f0c260c010c052803020d0f02072f040e030705010617010608011a09100f0b1206030a08041205010615 72
    0x3c80d2a070790944024000441c000cac00300503a00300000c0c0241c000e401e802005450b45c41c81408040e21884da00100030a000140d680303440c01c00e4142010700342d120440709402400e20f0404c0f4070150034072107090b03100b1590581d114082c2c2c0200300812900203c0c10042110420358003203140c07600c0040d80c608005421042c5111076550f5141112040c21a81e81340c14802c02e00ca0144188404140c0c0d1a00419400d200351000e448243c010341c0d402c40003845140e08022095150485040710a490b41e40a00000d0380701c6c45400302c84005035441701e0341d4403040700a6203d034001c00c0070f00038104d82495000100301c0e82e101401c4071305245842d0b0b81e0030b00703407181034020a0f44a2141c00c510744002c82c0074024040109070500080026050707005140200301c003e460b40c01d018802c0840851154058100000c00400700c0040030402503464070b4440c03040e61705c00c61404080091031008140c080c540461040501c0b46d014050314605454035001000040140000b40d429541c0e4100001b4280d10340b5038290300714403007580d92 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 357627706 1250 357626456 357626483
    0x20a030204082109010c0614070e0f03060f0601050c070902031303080c090a03030e01120509060718050307091104090c09090507020c091504060b0403080706060b0c03070609031b 78
    0x256850211455920007540700c801c180142c0f010b070b041045895105007880c4c004100400b03801c1072400380c0300c0c000400406452801c1000003641e4464004e002e41142103411610607845c02c001c1554610041d41d03804060181140452415070040b00101400b0310701000741d500260740c03400740c03a0072a001120000b42d1a40204140c10405a005d628950b10048d8041c02c1da051841d0480441e10700b034214000102800050030950310b0681c09a8517269a080b8900c07418000e43c54112500c40d2509416903205c00400d40c0d9400c00655198145904030940d2401b07001040803620346280e1138080c28514100c0e050030201004007003000042d03070040c2114010313152501001d0516103840003040311001015041103400040310194141e8070f01042c035410015091451101648600004006050a0f40b08010b120000200002044140f0303014009076800744004100c020303640c40f1020905e00c10443d11090700c2e0410024000080c0c1f96a002c05009806480d2014201110b001c5900303640f0050a400d0318982542c150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 357628956 1250 357627706 357627719
    0x30105040503220602030a030203100e04200d02091618150e10020d0e06040518090c0411070312140106030209130c051b010902030319030c02030f0f09040f020a030204 73
    0x11034925943e080401040003807500d1402901c03030003040c0d1100101600000445c00e04441104c00b08080c000580140c1d0042c10540b404507000015a19007103a51510b0200e4203e030352400c603407036820907500900b111b121503803101030001070050400c4000081c455000052641d0078904041c00c001303000501607203904040060f501509a200800050b0312550303d12200303500003036000c6400d4405440034208541261003072030000350140995088a500510350040301055101007a102070300071241d444c107031100381c2288010f11055030711070100d50502107420496540005d204001114151200900024000000c01600e64202e04203034003150000340c0104020125103404203080421201c10707032080000ca130f180c00020b4030303500400c400d0625410384403250104c90902904810307100c980c0181502e540c1c2c01440c95041c0c1a4142041c0b000002e80341240540e40d56000000700d817544001041400e0400351041c8215034182d004c0d906080d0001c2c1c5958100c0b406100d280080d02d00c10049440150705c0c1e40c04c0c50b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 357630206 1250 357628956 357628987
    0x150c0706022b05090a03021903140a08040302011103040801091109090c150c0304050a240203091c050109140102031504050105100c0c0f0b0a0306081615020a02030105040503 76
    0x11403604900540c40409a07030308001e031942c2496240d03080031500c0b0302c8a6800103d0103070709075101941010000c02e00f00381c50b03804403a000c81aa4810340d44600c2c01401858000d80e00e4001150040050000b0082400558010380c000c0443d08000402c803440c1c191580d110509450004c5421558191440c06040c90340c80c110410941c481080001880502c6d02a0000b805540d1441d40b408182071000403591008030007442220003906001c0e09030715401d80e668000b192045416505892641d289007110b02d08544048100d030020b000c010103406224800001d800030320115950103e8444d9601c03241e18001840140710800300340612400140c581c500b4558070904400703104030041c80303145000d00500140d80d0300c44401c54402070030301d001000c0e050070340341072020524560444110300074641000503a243c07800300101031180b1181c2d014010503580c1c030440b41d03a500c5070b2a404401d48400310030902c04120000c0c01c1d650007400c50300c1110446074483e0040303401c54809540a40d1207810000312071080714000e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 357631456 1250 357630206 357630223
    0x207030c0303110c060103320c0a06050304030206070305102402060901230a1503060b0a0e010e041704150c050601050604030b0708060d151a1f030902150c070602 71
    0x3001e0f0900d032001211400d610b941c0140401401031407065200c11202e00442a0381d1440203510015041c2c0c25851050075640780c02107103a46224010440c00440c0c0103105a064034022581a0020612522000c07800d502900c4014801e070340100c044100050542080b00110f210740907840300342c2100c224450740090802e2001000035034980c2c103001a10380f0b07000398103211015000c0c50360860a0280c5483c65100c2c090421046010829000440c01106000c002d038801d103003c02d41103c0c401391092360303104144001e00091103589440b0040c40000790210b84142500342040300b00b4022a40b4054a0701968004040e0231501f5400250441104a0400c0403c010403030140c034040381e58900707003455540e0704012840014603070010015010b000c2105134542d001419042944250a0750f00d00202c440040d000303082c01c03000b0103245a0442a01d01c01e03402c04038244400540c660884000c3c040c01a803086e0050101d904040340c06c500044559515a4000005400401c2ca00c101420b0781c41d140c00802481c04004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 357632706 1250 357631456 357631481
    0xf0a0c02041514010c0f050d0207060807020c13240f0e091b0118080307080712090501090902090a09050a050412050307021504050a14060907080712240207030c0303 72
    0x4020521031004410f0040b10202000d20740290600382e41e29113195030103030400005001e8814400710442c6160003107a807000b0303104c0507501c40c801076444040899955002610042d00008018200341c105d020641014981700360f11410480304c90b000160001d10913006501c115100c00c082041482005203001141e074000701032100a01250740000c2051010703003102e4003464103121100107400041410503078100c3c0145100005e8a488408606141c012076100e55402c4440343c0358a00841202d48c003580001090b5139040c2d5589c0609401c050381d05003303522001c01194440ca10410000c2c550006000d02849480c4056004c43d60b030400e0301d4403111400460264409002d818410003485550000f03405208118500744d00410b6261130900c07a0a20011940c064810341c000c040ea45110b2600081050043c400764048901c80380d600c1c100703e030f112007960041e03408440b22031086e0000b0070350401074401114480a03a032049207601e8403000303040fa44a01012004a40188803680c107041e098840c05030001c01c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 357633956 1250 357632706 357632741
    0x9051002070b030105060306030a05030304150b010314010612141306050f040b160c050604060e0c10090e0615180a06050702100f140403051501120819050f0a0c0204 72
    0xb03040042c60340b4001409424020240400020f100c0c0c4ea040201d4181d041d0054162641c03800c080c141445151034001880400a04103582c1d42c1c09540300f44100207010000181008060342020811100d503075809407103441445c0c8482e444502c51483c1105140254004139481e0426400c0b480c200d002d6600c0180705450702c116038400c10001c49d03100040180d010b4000d4000102c0d0745081c0c0303401d45100d07401d40c10140c89441040100710421080e40d008140301400142155802c00c8e540d41082001c25440580740c6c0011150007041019440c0034189a801803001460325011404a0101e8165904004154520441c00303022903002414005101000b41c2031503d44180740c41d6681e00420f01d1850103401c8401000005a401c2d40d040b40715030b584e4032038640e808509503035455407410401d40d6140443c0c0127032400a502c40000502e480c0281c80c40f00b00c0f90740401d50500f801d8201d81c0c1d0902c22140210200d05001c010402445201c0c0444010034004090762113000c926007160040c0800c40340510b185a21214 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 357635206 1250 357633956 357633959
    0x50405011e0201060e0c1e0c0307020405060a050303070b1506071e0303060f0f051e03060f040c030803040602040e10050102030d110913020c060a09030c03200d0905100207 75
    0x2684022030101c0850040718220074600c6411049005000c580c0c016011000741006129280010030b0041012910550044d0390a400c0b000143d080740c402d40b60b2600480e4810000341c001402c090b00929070102e80100501882e940c0c54000c241540e00000c0c080710414100000c08c80740b0045210b408480c0c1e602924220300700203a580d03450403d000b03890190a042603009007a01c00300b6109420001c0030781440303c1900b0300c0641c0c800d03102c8980229400342c648101c20f5080c461000c42035610a041e02e69200400810058a0701280c40c600c080010b002500c0024150b0400f2020030341c0c81c1d0055020342d10400700140d5407441c2102541c400080034005407a0014400d80c108016a8004107843d1151044e0b0000560801840e200d250281301e038200c41c5401140310a013030f4070a0f041c154081c24050403890252902075a82e411408200c900c00407008000c1078912a4040129201d1454002220b03041c2441d22001d160303410b40c09203480040d081c0340c0c0005205080034000c60402c42c21927650344000e80020b11119 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 357636456 1250 357635206 357635209
    0x1061d0402030a050f28021804060305010b040e03070b0c090d06381503090102090406090504020306060d080708030705071a1006320702120106091b02060402010309030905042a050405 80
    0x1b00c40c0c44524680703950b00841c41c00f203040507a22075060902c5000b00704100c5160780f032400b64068144010058400e078600b40c540780e1800800320840c0c0c645580300e40b01030750035a10702c96010200d0b040089030b2900600c20b022120700040c04c51003400f0402d4150901c140e55950282c1c02c4124080341c80b620b0070030414a548400da200e4a8022450b13a4508082c01000c1d240d64a0f0100f07540203004c0c481142e640641410800a0392203055072003240603500903800d4420540e07a43c806c2c4843d10810060060141c5400c0008001044201000d90381241c42c070300e01540780864a07100c0712401d040c076220700e4240d441180f007800003001c8002c1c408801403456080040700c5690f8079070301c052103480389010000030ba210344990510006066080301c0101c0da008180300404900c09024600078a580d00071241100e1528401c001c00717000e00804000f40d81d4240e40100039564550380114003801550508406003c621880440c1e0342d903481c001c0110030303d14420018035680703c0d900c2036403000c039a0710b20781014000c0400050000c2d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 357637706 1250 357636456 357636511
    0xf2515050d091103191a0c0406140f1b1018060908041710050105060711010c020f03030f0901031503170c031306050403060c1701061d0402030a050f 65
    0x340c1501e5580024056094240304a40e00359181c00c459141c014417492003a00501d0145a410302d5001e60003142c0100310380c2000380301803402a50001c19901d000c0c0010050184503078800c100200380c0c800ca180c20120009154812034200c0801d4040380006207240030360b030340410040c42c1c00742e102a000501104184020307006400700c0303110014101c03940705c1300d050060000d040102c1b00100350120144204002d40509036403500e43c514040b200040c04c000002800c1d15060056441c070a0b04400d10018000c982001510402001d0340c0407608841c080e40c07502007507501440a880e41106c4000c02c56078070042c490004080710520f400c90b040c08405d006003030000c2a480c8210740d4262084112441d6280c0d1170a11051450003014094407202800d07200100b191503208003d0012644500414048020001c3c01a11940440080307140d40e40c960000420155101e40b007261000f0103102c00c0041d4101c100c0c00402c0c2a60f00490340d03804800e80b45c0301031004181d540c04800e94070a04504a0110241004085500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 357638956 1250 357637706 357637717
    0x1107051506060f2a0601060f0e10120f0c0e01170f2a07030f0905060307140a0302040504060f030215120f0c0c0a12081f05040e0f251505 60
    0x105424081966403000268131002d041c505060f0714070b0f4440029611945594103c00d0003410300280380d0780180d611160184445030703100e000c0200400d8100785112021103015000507200075040c0c0d1690751401e100300161003100000266903890f0040951100000360869251907901d9548205500820100200780224503030001c050382c120f0355000025921030110201c01900301c0902007000101c1c001003640100d59484c4441c082d40710710010039070310402c020550008441d41d01c04103460400340300d05242c15070010312031103483e41001410140c40308081021207a56030043c0b031020300028024070070340c03424400ba11440c0008108051a190300c0c0030812400c5c0700c0140c03064405c1401c680218400c10520000c0c0e0303241b00e100d80111000b030761803410841d9003890f030422004007180002000c0340301d0a100c5140d41c0c122041842c01c45500c04d03d40000e00009101442c1c003414140112191388400d4079040c00607080691461510b2103022a00c140c4034440464542e00088031304404000e442c0156802405461 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 357640206 1250 357638956 357638977
    0x2070f1202060f070c09061a070f111302070507090b030d02150c090d060207060506060313020609061201180b060a08040201030b0a031e1e030c0f05010e01110705150606 74
    0x1a10f556501c506000c070b501950000919440000202061060090344518226a0381c205804c2c1010788441d0548610300c96136401074800b80241250701c0101d220001004100c040c0034040c8021921160424000c0f41c1020034200c0f82030700010401c1100c00264003031038412440031000b40000601e54503000e580c41a04901001405d40c961000030702284406007901ca2400010b445400c001519242c403100a43c4a580102c0e802407420f070101c2c900e81022000d981c42900c02c4003a860213a60703540c08100c626040040c4240c2d00041c04c0192440500190500038000e0400922207040c0c815000318034020740304501d45281c000c200600402c401194040c0301c1640058081c2000036008041401148030032001d81c0014094140090303440424184000c035900009000c2c080b8040d5183c500504404a03020348000070700041d40042c3c1110200b0104c8103a5060544582d0000031502d4480d0011400d580034240da20501c0c0c01c0120300311061003030170f000c514001a020450b17a44d13030346007190019882d40250000361 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 357641456 1250 357640206 357640219
    0x1091508011e0302041b081005030601090b06070609030c03020d0c05030a0305040f17090103060b12010b0f04030b0f010f08010516050d0b06130302040b0909030a120b060a0207030302070f1202 84
    0x802c45031010264409150041c4c42400105801d8010800d00e400c0042000c001828410014001140035502d00066410040141416918044004001e003c108505e607038011801c1113600002401c0f440b40043d00b51103901e402a0381d024a0034068105034000c64810140407071021040c00040000c011154850321501b000030b5280c82da810002d1400784000300040038030380c403000710985028803c0701600304190266070500c60302e80c41b001d0440c40740c0a0f02c00202034540700d541c010312501030030303501600d045a010f490f100d081076a6501e41100c200d90a031803d0344441c0c0000c1c0180300e400f060182000181022000034005030134a00070490030b00880200751030070442c010844a2108015400240180100511564035859455012000042d4520040b84a81e19010402406003060361140f0311801c1424041c6040c801107805c207a03144a106441040460741c0c40306e104c1030542d82d803005030804402c2a401818203504528002e0714020194000e8507046c0c03401d0348200480d6000f08454141c9a0381035403107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 357642706 1250 357641456 357641489
    0xc0b01030314070803150310020c0a080702011e03020918070813020301230a0b15030406020304150606080402030709200c011d030a0e061e030928020109150801 70
    0x206502c0d800f5858000f007031001e00009000038903921480240080600f201580c07050200d0750214001c0340304044038108180c110340503403c00301d0901c6024003e15030042c14210940c41c08202d00580310004041010003099000c0707038464050510029200d0041d01c1070b121603d05062550001d0b00201008280c0b8000b6501d0052400031500d003904030b0701d4010b0740003020004074907902d5040300090324100c4410805618040c085000c0746031075400f070300b040d00b5030070300a61858132507407101806507100900c180c6142c4a017424484188206106110003000182d60301c1c545410584109800c0a40320b034001185182040c40e03001c9880b503c0c202d544101000c41d48001da0310700d480c110f06805001c035098800600a42504003000151000c402081030002941d220001124403d04100302806054007042100078409240c02c4c9400380c200c02075410100b078008070740c501611080e070300c403000030510114440019101302a4007103507003004011010301058851029142103894006104040500c58404001141c036403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 357643956 1250 357642706 357642737
    0x70f060218060c0a021801060801062007090c0e0a0f050d110a060206061201060806010603020703021f1a0d02060a030b0d080f07030906020a02030a0206030c22050a05010c0b010303 79
    0x34081d041402401c0241c0300d00040c60083d8a860f0980307001d0340030300c0080b08500c2022000e1801d590580301b15032a0035019908007902290b0303002050f031100c04043d5810310903903a1440700f00300030001030410300310100703a4074041d410050004442050031400380f4011071051042405485002c0c05807101a10540c0b12182c0600f8124165280500f109800181d60303403001c1191580030480900c2000141da00c1081d582840400c00d080704c80307a11901c5481d8100e4401072218501c207400030700b011801b0744115524006800d41c1c06100450f000500910750355210150740b2100341402c80840c3c00c010460348400e0160325074021030564411180c0c224101a940ea0248245a0b1900d00004805822800b517503114a000c5554014a601003407041d00410180c03140000e0280c0300282d05050140d0240203064214010350074861150400b400c2c40f4910300f014032035200c000c15050701c030510412158003403040841c03408042c0300300d074140394001c0e9042040d04220000441c00040146044950618042d11903018644 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 357645206 1250 357643956 357643987
    0xb04020702042a09060905270a0f06050102070303020c13020f181801030519140f070e0a05060913020312030a0b1f020d11010e0a0b01140402070f0602 66
    0x402544a4500032010f40030301a280c015a62403084940240c1082c1200b100a862005151081100140c0402814031103420002c2d5180c80680301c4495504080c2c1c681003025061850803500d0183c030b10350b9004807028400090081e00010301085c00035140030341c00c43e240252201401d11400c0d000304601101000140e10079411590201e80f5041d8658588a5205001d490481c180018a02c41c600008403c914139084c1450700e81201c0d07000008103180000b0785110b00304802502000d403801c07110303e81030040c598410703c200c4513580c0e844405440d1482c140150008000300192222111504d005d081140b9511800100341c1c1040c00c482c03200106c1001880064070b4100a0318480f02d4840020046c404a61883d402c03c2d00101411a00b801c08004011450000c00070422003103001a4800409003403c0b500881031040c14121103000450b0a24944407070500d00070042600700c2e54103055000410903000000301030705141d8000c0b00c05601e0500e036521101443c1c00301a4025120f241d00046542d160071030300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 357646456 1250 357645206 357645217
    0xe0d08060d06020309030a080a110d0903021c0203091f0c1e0c03060209040c020105041e0212070332100f140a0e07060206100e0c070b040506070f0e0f040b0402 70
    0x10f643c0d83c41c1412030981ca903040b8104110129016501043c00350f80d0300d0140b070103002c0313048466a0800c0554161007020f00042041902540038683c40e1400031640e401c044040080540c0085035200c220000307204010b00300c80c14401410313143d07031000c16210390301c0744040c844c03036402042300001d0f11000c0460700c4103107080380c03402005454200b00000800c9140c1c1c000e000580f004071020440c10143c00c10036801c4c1c1c2c01c203c400038240740004600c0350658031461001100b40340003400309402040811031403850300344aa00107035203040c030f000c4140c1c040089170700f0840d0750255041a0344101981026003030740c1c5d4004011002000649400c000410041c03e40c3c0060961012080700070032a0030440500e40080401804440f01d5000310034005c40d0040c00003560038001c1d00505003c01e1b0040c07401e1749040c90315001500c41040c482c1c0c104540c3d80820004c105a90085001cbc1026040c281003120001e44681d155841d200c051040c40c40810181d030340d5045804687d89000e4030040b80040c4104c0000d40280301c1c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 357647706 1250 357646456 357646463
    0x40f080d0606230a090302040e0f0102030405010f0b1905040c17070309020a0b0708040515160308060306180307061104080a080909060f030a1e151e0e0d08060d 70
    0x501000080841d8001035900d10f400800004111610b0015502ca00510540e2508808901c85020410060038141d00910340c49040c0c1c4259000c0019900003142a81d00a80b000d03250785e034481426039160280c1e0300c24a140028201d60941212051400c08072420708984906842142e48850b045403036802a285000c0300150003040040c98548184c026005161000080e4041d0f00e0302c46002c03070342cac1305560200c82f5a503401058140c2820300d0b00042000ca0002003081c400101800d0100111455800400c40540c510a0301e64248602c2c00700241032900f0801400c9404802224424805004001c02103454240d0400404509040c440c0c1d0407411074403456010354218826140b440f01400000d10142c030882c8401c8032103c08507100c900c10000202c00cac040d140ca07450b0f08015960400154514580d60094150084040c481e4080751500b06401814003401c0d80d0441d103603084022100340500c0b888131080b588a000304006070710700d12204d5645441a0460701841040c80101c0d10707070b9072060b000780d080035072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 357648956 1250 357647706 357647711
    0x1e091303050d0e03070606060207050d060f1103010f14040203011a09031606021005060901300803040b010602010b0d120f020f0f160605160803130f030201051815040f080d 75
    0x9003c0d4540340c0e01d6000e6403084d43c4030344c0f0b02030780411814404114007046440040c8681554203858503020020180c2c4008072101a68661800b9048040c55011310b0081c2004d2105400302031070120f00045020b0045000c0d13200b40e20400050240f04850b80c8410325510109231110303159086c91000c0303441c0c070311440070300f40100a85040010722907500040b81c81c4418803280c0d00b071000b91503c5003484031310142801490100b40d079085403060303500c0c103045c0400001811651140081e40c100d80b82d0140a40c015603058401210341801400640e40900440c01340600984031b056480044d0b80f00c201c00c48c5110060602044a00303400c402c0843d20802299a4807034281c41a00c48800d522468181c0d01d11680c490426100100d00000904c940581e00791002b0001c414400940101e190792035040b41e5000502d4686541e00f06480c040c00302d601c8802a000c000d1007500001054103080908080032291142c140c0d00b5a4058040029080340141c2555046644035514000c20800380c51f00800c0c50040c0c0540260303491 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 357650206 1250 357648956 357648971
    0x2030115080c031e2e02040303090302010f080402150d09050f150601050408120a03023001120804030f02012604031e080f1b070f021e091303050d 64
    0x380d010424804628084088940d0b2149801203609038804400040c00240c005640080c00400052200c02c2201e00394100780d000d00c034102c00c00343c041f038015400640024603140414000c65800c8402c8140079086410802000e02c0c1c240d000410700152424000c00040001c650381c0e115184e40d4102400d52030707104c01680c44581030003400c00e0ba07030111001e0b201050b103101004642d0a50140040303070700350359000c0080e1000e070b440d00220350001c0d4022141841016420032001d04185411200d01c0c2d15100d03181070000120303001e040d0b909441001030300095200322801e05c00b6800900c00d04111000c41c0e5100d240d001c1d03900850b000603101c6072442d401c2c841e0010003a241e20f00c107640080084034403540c80398940340e8018608080903040f4482c1500d81c68042100070700451100300111a80551103c143d00107809025801800b00c0c0441d049039804650413a100c881d044114a40b8103900380d09200903a010302c0d0301c2004900011000000503007101c4003106140d40308003d05d0702c0b440845400500c5003070103100d90b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 357651456 1250 357650206 357650219
    0x50405090a0c03020c2514030d080709050907030c030b0a150809010609110c0d05071a040f05030f0c0105010506130501081b070b010806341110020a02100209030d0c02030115 76
    0x9040c0508800d42403842c081c04079201c042401d043e4030f0f07c1c901074000d000b0109001c000351070600300070740001e003401200c26000502c0e075220403405200d4a29a50046041ca00e030101c05015908030490440c440c018020050148101500450006185918010340d241e03c0e100141e174010071481c1c010703113102410100c4000002e440301000301900d01300e100444801c040315500c2120b0314001c00d80001c010740d10908074141442e010f0400d4982040c02900c6c540813078040c590742c3c1483c40d070100e90803410704003001c20145400c0c4020b1003802d00400c825034601c0d140c145140380e0981800307010300030207041c428103034041041080c241141d1680004a0100680d540682d0f04103142c0b0090240310307a80a0307100f1700c00002d18030141140340d418032000382000712080701000c55940c003402038450700110802220a04002854000300100da5800410340c4c8010303511801c00da802810700300e65285240741d0f1401003006e81c04548001500310b00d00c502d85e150619001000f4800a4007506105140c04070100d800200070402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 357652706 1250 357651456 357651493
    0x30a060903180b090405041505071d03060f04080a050f1602040507033e03130b010602070303051e0903030c06010608090a02030307080919150807050405090a0c03020c 73
    0x25802602e80000d0b24041074003182c201d08440c02005030103082480108000d040580000382c200344503036a201c0000e410200d148040300c0f4201c50000c0054450004c081c0c0201103002c03404920130003500a0803083c50045101c082d13004028000400381d0b8800a0b407101018408c0c400c4d00c0d412580507050070742c5c0710850b0401c03080300e00e01450240c0c0726915020200d0720240c0240306a40300c4290301c90b1080303500740c1b010300000342240348038402030803a00000c9500344080c070f60320000b1845a2080203002e0380100c00c5007000300d84000160052001d540c8448000d1001c240c00406032622601456250120303025060513002640c022220b441d6014480070480d08043d40004c40c040e070503a186540c9503401941d5205a903503560400b40d1010350144c10411040001c6041c1c04000e000c01c603409016407a08000502042845114550220301c00503803a00c581c1c003449034442d40f091b4000e074a51804a0074039040900040e042803000c0c1051174003aa4a10612400314000d4060307500ca17000c0d06068a83ca007042045405a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 357653956 1250 357652706 357652721
    0x2718090718020c0a02040f0b12060a1a1806130911090a111c020c0604031106060906010e120f061006030608010203090303060d061e290303030a0c0509030a06 69
    0x780351864090100401000d842074a01034030f1400c0007880480d0154083c40b00601940400300003080c0c5601c80c110494440c085420205402100240354918164070400100c44803070248501c1100305601004140e40d403030040045440e10146500000d0300c4410010300c06403007150f1425070660030603110005210600248180244083d140d0b40711660b00d0f80003c0d011121052400c400d00d40c000c0c8140c0513804804c0c0c0c21001800000d9100510f480c031080b6240340f4000040b1011000103082c40d500c5001c198040c8012074019005990100941c1445030010340b80e4548007009900981085d22140c42106080105001060700d03802030340c00c42d0804880035800140c240c080c40f0046030825200080448051080741c0c8100d02d0480550700f16102c1500700300401c0a000c0050700d050b600c0d800702c074007078040f0550030300314020004400080403101501c09505001003002096021052060880030301c2e1004402c50740d04c4803810100240403508072001381e0302400780d0301d4816098815120100200300e07079a401141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 357655206 1250 357653956 357653969
    0xe0d121517010f1104080c0a0506030a0e030c0a05070503070e04080909070302070219061701031709010207180f05220b070210090c0303090803030114010f090b0d0b0a050102010227180907 82
    0x340010b8610b401c0c01600c8c2614400c5540111040000440c02c807150b52180703005901c4001980c2c5003031113000716076107000b010359002c1d00c65811441c001c102c0c0d480c041040000034018010040d000e0700d4141c5518126006420f102e41c002c0100f04001a00280300c1e40c100d034562503006011400002460704071550850081c0904401718000242c400071354410b5909982c100d9500c00d020100c541c07081c80c2d140035250041c04071036040d44941c08002c240681042c20045280c1105400003400300d00d030030150b0040d140007030816100010a00103160003d01d21108041d04d21381c01902e1400c854440e50f004a14081000c10010300c4c952400002004100d03000071488100ea000c1c1c0d8074408110784a88605499100a11411210783e2000d90000201c2d40200341010b030b14030701070500501480d900c070340c07045055010110140131580e03104402422403519071008801749c0002c1c4021030415003400140b421440903500400c0f401701404030491000d0b5030b14201c40001342140d01e080d1181741003410496941d41d5103400744c01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 357656456 1250 357655206 357655213
    0x5090906040b011d0610050405060408100b040608032b020a0806182401032d15050d0f060f020f0c0106050306040b0f0702010f0e0d121517010f110408 66
    0xa04040303000880c2c07029540d991078480b44d03911160104403421850719895410300409010000d0699200300142c0005c04800b070203440c40d032004003283d5040364101c1c421030b03125500d444400d011054000007520802d80542d103601c1c40c4000030218210458508883d040600d50000540c048030075400f050460291405450b01c0405800b41c04265807444011070300701c000d1001200e400c03e0b040705480c040d600c0100c0117040c0000c40c0b1000044154520343c0b1541100117111010507900f1f0300a141d44200801d039802c00a21001c00c0d414240082c00e0b050780d0702d4024182201400d010300c10701c000e507803040e04002a0b0007011940ca421030113607501c040c0c205060741d40c0e0651810200013100d04000c259644684d600441d13540c0f0955500381c212035400d80c06840d01003190768031151034040094a00c80d0303000c1001c0020050001c681c071500010686100043d400c4510750030314440b0a590288940c0749415156004082081c10707815907406401088c031190700c4184070b41040e0102100485041c020402d40d045227040c3c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 357657706 1250 357656456 357656459
    0x5091513050f12060609151011060a050115050f040b0309070e0c0a050409020c0f062514030703110705030f040e1e070f030608030c030a0f140a0503040c05090906040b01 74
    0x30805002000103000c1684d030800b4000880c1c9240081800703501019041549000c07c2d85c070408181c408003442081000300382c0c1c2c000305407070410003049440e51012000206004642c180f20500344010418005102400f0022a20030075503004041590080c0c004044280d44070b18045100c181d41c2c2e0711611894400c02c85c06008a81144070040480301102d84035100c1c90714044ca0a25064000e60011104054a000e0040c0800b1852028004180a003030000c015100072402e0110303008500443e28800d03001d00c00c201ca20300120f0644842030780e0313005a0321b01380080c0c9643d9001d00c403451440344c584001c0042c0400191205140d0540340030f0000d45490301c140b05426aa41d101b0395184429022500c0c00b04120000010a814445d072003105250400d442c0202e00c1035942d50210740381d80c01016203070240780c1010422030b184691042284405600f1803904102d031016001c1e0840513803141c48a10402c00400200003170600c43c6e0007130a1801444081e0440031249402c8808544440003614100c80c2e111441c1c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 357658956 1250 357657706 357657709
    0x70207031406011401261015110609030901091503022101060e0d200f180402090604330f03060905070b030601090b031504020c0307170f070305091513050f 68
    0x502150400446c150300040c00c1c24800034007480d000042030b05455803036900c0b000c5201d1b83e05100403402024191a804d0300d5050150582e410100e0040829109030f005011040241c1c1c1d005c40e00e081111451303103494940701301c1e80804501038801c00d094401420051204c004460100120990484034156a95a0413001020410604c80c10000e8040c0101c640412204200c1c2070781120300165050042c25908100c00c1c500103d500d8004030302c030755070360948924200401d5081c03403803401d60f10a00450302007000307480507001b81c100300c410100b80000071032100194051b10400303600b41c030020b0a017000481e040b4a50b240742c00c101a0074221030031030312405400e00000300d006202040c4ca000f01b4050311840402414100c2801140c2c000610203080c02d0015417400c3c200307460f2440101810071520300607590358616410407941d844417019490380d00c0c5000300030454520a28200303658103194189411a500c0c0081000294401c02150681e0000c4400051004110f40303100480000c81d84140c2d28800400c1e030150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 357660206 1250 357658956 357658967
    0x9140d0306030b0f0a0f0c0c2d1b03020a0f090c08010807151403011e060507080304140c030f0d0f031e0e1f0c08010504050717070207031406011401 65
    0x31009203c0c142000c0400d0809000740b02c0190b00859004000403130580f8040080c00b6114008038038008902010b06e0b180030306c4080f0034000c104403480000154071408445005c4160a21020003416181c3e04014041c030007894080b80200554006008103482626003690309071a1101e446100e090604d4554035121890154500e241212a0744001e050150320703044c10080360401a400c64420410003405003112207601d40081c501900c000d2981d410340c9250340d04000184801d41d0448001c2c40401c1c40304100181c01e05c000c5a500542c424940c9136148040f04001c1d00d01003500003600c0d4940101780340100d580c94000740540010840d55039141d80d101b030a11055085a001080c0c1c046290300403266008042c405801032521101c80b0003c8840da04640d0940e0490130b086e51b4441660503031101c0d500301529500c9103286000d4503003103904200700d0070304003000741c90201550b401800c40ca07442400100c0795402400550015904000e041c00700e069400c0301180ca4001c24010b4804400100088420030351158 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 357661456 1250 357660206 357660209
    0x8150f0108040213020f13140a03050a020609060432011119081209010b0f040c05030406111c050121050d03180611090f1c06090f020409140d0306 64
    0x1a15441c000c0c1e103030b07602403091628000c3c081000e03ca4080002c02c08442d07850000386030915046954456107810040081b041c0326960240c1d9100704c016000c1800400c001080506800f0350483d0041d54030119980480c0c158016580110813103510000400c500c2c40e61030400105200c209001c9044011500005442c003845c010b0b500361842d4803d0740c00d00c2201b02031880010500303000d009081c1c107204c000c00100c12205030031a03002000383d448021005d987c5c2441d03c2003208001048a007844500c2e0443c100070b20601004001a00c09034644c0d185440440d404070484450700c601002003a000e82d440008540640001c0c8a10182880f1100700c41700803d8135040c601c90106c0d40140503104012203120110040c26982c01080c84843c820701007080010b40510418030044152001d007601c541e0707242c0030810018040913041d4010740d40c00311803c4c5a241c80d800b02d00030326603001e08005203051003070414050215144d00001e4020f49040d28203014040c0d440c40c54071140100b00c4c11101414030144045081c0c401070b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 357662706 1250 357661456 357661459
    0xf060a081816030b0406020702030618011a0d03030c110105010f0302130b01021c022805010b04050907120c09060f05030724030c1b080c16030b060103020304030c0b010608150f 77
    0x822003d10000360840c0c0320607001405140c01509248450300002e0800100b40c0340c10914804070446614101001e000d10014104030700c196000038014030340450395816041000404065603a110307079030f170340303010700d50b00c000d422000d170000c002e00c0d03844a880d9004080316000a9114220320f0f0700050119030907004541c01600c069001d03000b024000440c2e01114100e40d0f07641380c10750281e0b03100b954a402210440144554002458246500d100d050480c01c641c08400941e01650a24003000800c130000500901114107040e410b041078521420f00c130341000c0403500600540e07410302c000051300c42e48002c0c07114190790084054480043d550300103c2c2c040e80b4442c05560070b203480100d06520f004d0080e80310070002d040c5070418021800010303480c41c10380c582c1031400f1100c040340801e905012a00400c08148990310004155600c1d50442d22100141e510051045040540000000e000c0511410100241c29801503890020356120007005d07010200803261503070701c1122082c540d03000b85090b0702402071a040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 357663956 1250 357662706 357662743
    0x9070309060e0127050d0e0a090905010c030c030504050607080a0f09050d02060105010c0c0e04060902030f0a05070b0c06010b0a020f0f06060f0105180d080f0c0a0c080a03020613020f060a0818 84
    0x191b482041d541801140181c0e5400f0700654000160300b01c050042c4050580b1900000440b8110b800b806000ca510a07524901058600010400080c40000707000e5080203039400c00380b46e944c0c5c07012903400c06884030039601030328179050030380500401c20001401d1b8040e64844d000e0340c0030343ea281d1004482c41002c02002800280307440c0c2c8100b0624140b41003868201d8040c0c84085800045500840d1030106051041171040e032000c480e41040c440280f06003c007504940b45401c0c54010b00f004040d40d14003040c05540c0e07040c2000201e05080500030040420b1400c2040300351020115050740301501c40d41c0885a2a004100100741ca0003190320440450303221400340380605204402140500007810f104500840d0640c1042000040c41140000903040b00600301c0c0041610382010b15050f0290a215448901c2d40d502c0508024002a00404d210340d004204262001218540380009142208605d41c080e030400310004a4040c200d40c040c100a10900b0300442d600c0d49001c80245407035a0f00340009501c0c4140c1c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 357665206 1250 357663956 357663973
    0x9031a09060103170f04171204061205060f0d0803150d0f12170c0c0f010902090615040302100306060806010207030209280e0105040302160806010509070309060e012705 74
    0xe883c10b180c04c0e40d000b80200c3e41410100400c1040940ea03000d60000c2c004018018483e808200d0100080d9402501404101e410180741a001901c815551856442c83ca61030b100083d03010345500c100032001081c01003a40a0346202400c00029603402600c5803a1603038a6400154030b9801c00c0300c00036038005c0c2e001c4158143e0f01c1c066100c000000c04000107a00401100062001c50b84451608072405800900c041070341d5400780000c103a241c07541d0b07041040100e0741440040000b40e95420144c0f0b900c802c058800d81008100c074070000d070451042d600029400700d17590007a004000d905602a03800d448a61321202800d4079050010390b680d1a2a1100031341c045180400104d082e00c401d2803d40c0ca0004c880d180c3c4040302d20480c10b85090307800ca0041100340c1d179035a40820081c96810003425030740c1c2b8600654604858100208140c482505004231400343c6480c1c00030400c2c3c54860352140b00d1050b009a4108421058540041e0281001d0303400501000c5107039503200b20019076411032140c0141e00c10000d25594 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 357666456 1250 357665206 357665213
    0x10f03050c0723010e10180206030112020a1a0304030f0816030c110304030f05011116082a0c0f030d09140d0b010605210c07020f13090309031a09060103 67
    0x8000f10300282c40301121000345001001424010740398003141d0480030385a00e592500c090001c89110001d071580c4070030060440005a00c1301001c40e410346101c1102d446200103d4008150b0400007a48103400c008100030040c9840800c080107180103521030341d03442080c10028201124800c4054035108010a00000340f4010507002e81d10410207000c030b034204901d8400c010a015130842d0403543c020748884009510200401c0310a12403031088008081c011401e0551920500e1100d00d4005001030a02000044014040e000f000d6400420440d4041d44018046141b00c89501c1d4901d45408601890300c480d8881a82c0c0b80c00300340510048000c1da0f90340c0c103807803030302170340c0c40d0500c0c030000000c4e8200c1400513001010804012646000e401035480e41995140821186001d4402c03d20410060748042c4044c000c4031b1010004803030959030105d412140710039140e4000f88070060b406a81c0e000d12031034541c107141059001004101228041c42000e003c2c0754046000d03000c4d60100b2503200300150040300050002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 357667706 1250 357666456 357666473
    0xa08091e19020f0a0801050a05010519140d02210106080607020309011b1a072606040b04150f032307120819050d15030201080c0d0b0409080702010f03050c07 69
    0x20640024843d507031400d80200403814500b1150001d81250751100100074020041d800f8043c0107004c01e0f02c040e240b0051050000340000f42c54050175140940b100e00014240c1d072600308103105960001c3c070103108000240403441d81802c1603d1500480d50070010005020000415414480d15150300618580f500313480044554103900c1e1070f107052901001d0b0340c3c90045a052a0b003100e213480d891010341803905003250064010800b41c2d0302101c0d001213404000c40ea5040020749e00c0c0c0c0008043e1400700f4480390b0603000402421440052001c051710321900040c8414003400311108480c058044814100c0360000074002c0805201c002c8119580840070410200a800440f0b01c1d0941c022140b882c101310030082d0f45c0e46800c0600074004009040070500d1007401816201d259403030041d0328000801c4918560018040302c0380103028000d0080c1c013140b0044000c4150708000501312000344100214480381c9030413440780c3c00442c0c5c240e000a00e02d0615103038450180c0305075030180341c5644109003000041d90b1020300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 357668956 1250 357667706 357667753
    0x1050619050f1309080403030914010c080d02161506140f060c100e0d080106020616140403020d050304090b09010e040f330e1f020a0903080a08091e 65
    0x800640c0f80081d54129102c911802070003900c900c82041c0d94904c0d504009141031401e070080e6100103142c08841c1c800760b800c1006100c01e29804248a0745a1003600f00490090040d9100300c81d0100340c04c50548200701420068503040b8000880400c134154450800460b04075055084035007000041309002c41c145071480182c0081d200f01002c03075103410000341000b0143c6003410481c4180d41d22500c1103424075a0006011405815644001e01c01458885e410171103e401030740701c2d03106203d0340f01d40700e03181518400101c0e4040e68010300110413a41c80c51900640c3c079442445040480c1d850400e40205a18151007001d0480f00840c202900680722501d900105100c0018215084800c151b002d000108038285146504031100c0d5481050840f02c250a2050b104115090003064010748114580bc52200103d004e103104041c2c0e00507124245441c1c1502c2490140d0400340013403002060310242d5551006600307209003003a4040d40c5000d003d00034403292001c015880116240c000818002d040310b41801d4148 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 357670206 1250 357668956 357668959
    0x7080307110d06150801060603051510031505060a11010606020d09180b120c1011070e0a060807150e010201060b030c22230306090d0804050c03070b040801050619050f 73
    0x1601803805403410303044802d5a84080c0c0c1c0703a51150410420308d030301482107a034010f01c40041d040d001c80300c00d4005680c11407620391500c140340e500d60030140044840c604250241001510803595038885800c00303403c10400f1003100700950b007801c101003400391022070030452100b9a9141c1e404420308040310115a4a000f648140c0503030b681d0300d0b00a000365600c00c15000c202d8041d5006d07050550104042c418008007a40c050010701c2a181072a1062000c00031344003045070401911880292036442c20344002d400759038080f0003688070b00b803804160007615044c034510240264980c90240d01b0418016400c0e90b12900c00c000309034030240f000810b8481c00000900700c1580c9d11302d890312851030420401c0c0e0411603030341000c0e0a00c00740d031030212078400c0c0035102c40b402d5860840c0209110310300016801d945800a8548004000d17070140401c082060802011081d40c00080559a1203911aa1a001030380c01501c941d554540c2000046169030802e2806030f15240d40384484030010038185014001e0b6100301e02a001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 357671456 1250 357670206 357670211
    0x1205070503040b0418060803040b0c3310060816030f060e0106180f0302060703020708010903081e0609041205071506050f030f060a150803070b070207080307110d06 72
    0x60025030240010009440c03515441c075240d508040015401c003400c0c0b9080e48019140c58028480f0340c10000a807021200740341c4044d0b644000c030117061402c101c03c100c2480900c650400069a039441c1081941c411004003454400c3c1558a02c1c1c0e9008141c0001e00c1600081100e1701c01040703a482c6100908030742e110240c1404113007034515604080440b040e6a01c1034049001d180010320205a10503065140000403e86503507680c0d05040c0110304410807484000d00c252070010702d042c101802400540300814a0f20002c01610100c0d040150800300e04a944c3c0c155500010503004d001001800e00500641c1c01401c1002e682ea1169911035081b40301541c6281840000c0c800e820000b902202041988001039030003150b01c0785440240550341c110551503a209030807443e65210741610026440d91700880d40180842d0410a03080240c605459580092419000010b1904248050f1244407802002203600320307028181d0310441d0300c1d100d000c0e9440042001c14a444454101e260040b80b42d40103a0284900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 357672706 1250 357671456 357671467
    0xc0d060f18031b0c030828030209030705041d030a090503241501050d0204170f01050c0f031009020a0c020918210c01050103140c01020a0c0e09011b03020c0601051009031205 76
    0x6d4a000390030414020b00800084d0446001c01800544082c40025560400f5402d054006c80000e850740c1c4580221030003070348c3d1240c10844010b82d00d01155020408034094030b658198035070004050310b10750b0203080e000b44035948005110104008140451000b90314041c8101e46500900c0000c02108080c1c00f4100001407012110384001480103200038414460300382041070308802080d084c448800b0b001c96071a4545030401140b00504403c58015440f40f02c0029601c1c0d884e84112a080d20481c0c00c1142818804920441c03c20342192034617000074000c030b45054569980380700c4000e403413000358545c0e8032503001420004200c0b04e900d850000c280d9800814103081180c0c035001c41e403c440c0300340e009941410b408180e6038a80707442402540041802840603040c107985a0302e4071001d9031068401d070400304d56030000281296000f0342c03001e10051080502049002498a80100a5080081150524000c14000180d503180000c0c22a085115948900d00c11138075545440480340c0e0303000030480500404010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 357673956 1250 357672706 357672713
    0x90a09050123010f06050306010f0903080d05040b0603010605030c010e0d051212010b0a0930030e0f06070b06040510080703061e020a0914030c0d060f18031b0c03 71
    0x103076080d40040740408540204001d1030b0080d10070060b441610300c48001002071210940c40012a03600030000c0c2403190011170040d00407100f100d2194406002c620011800003c810036036081540510f000718210101521502e0030542241d08920803a90706503c0b010140c841e950162501d00d940501c000c02d80c03480c050054a600b414281110825004004000380c0c1083c41f40c511103047d40548a060515800c11507105400f5000c1c2d1031074018551004290b01001880d0000e00ca0301d000341803017030282c4813080c42c110b1078050000340b20300d0035803485040010701e42c0a05041807404e440760702e90094a043d0141c0c40d460144001400060244031462030301d00e0000c10301981c1000520300231481044001015102f801c1c180400c280ca0000301c0034404c1c010400500510341c015840d40644078050148002061030070002032030a4070550389903400140c01003001051099540c01280c03003040100c014040c4600b440d095030700d01340090f040103000ca40c405ca0518042540e0000400030103101d40d03a182511a01c0c0d84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 357675206 1250 357673956 357673961
    0x118020f0f1f0810030b07081b0c070303020f240406020f30011203030c021009080c0d03060302151606091209050616110a1a031b09060405090a090501 66
    0x402e00399980400240715210316070b00c4980c5952050b1007180d003076091415076645e451031002c06882c0300100526a00402e140481c4401c501078a0007041c0140c036550007015a1050b111030b0144001d071b000d40074103018540091070120f09009041098842c02440e1121620f11128203000504103940155084c00196040ca0384e000c0200000d001c1d40505000100c090030401140780c4001d0356280c2c0c21481d42c001001140b056145038408503505090105141c403003420102c0c60810709140f581d48280c01c3c803030644103104004000b08603081c40c003005e884114100c80015070130350704c5521000b900440c004071030303001500401c4041c01064092541165071440c941d01c03898240c41071554280c8064005100c00080316070032003994401007c0581d5002c2c24800c0000a1250303070310000e40c0103040b840820320050328030342d11807640700090218000030096000602421500700d400480304200701d10102500040284444002e40c1d040000080c01e11349050b01b88410b03c40c00c420058030240b03015403031f1403403080058001e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 357676456 1250 357675206 357675229
    0x609300307080f28020a0210050106050403061d0322180204051f0f03020a0216030b010305150118020d150b03090d0c0b0403030c0207030b09010605010f020118020f0f 73
    0x1a51001020304100807808866040604000c4c440d0001c5407498440700200452515200f0484c0c5005848114001080e410b20344514a050001c0e45000c00200380182c106025105681c0074060070400110b00014100040300142c400c1c250030740c01840540d400707456000c448015107960b00000c0c41c015a03101d403941000070000006884558021a01303000ca404c1c41040404801500d580700c500c070741c8040341c0141c0181781d19100d0104040d00098072a01543c020040c08400182c2c004c5c5121185950742804460311000707001c2140c59010b4000409000005a52428140c41c140c20240400e2440340300c40c0da0096102d4107503000079907250551210900079800340000288200424241d40f440c0440b0f04a0600504c0b0440a0500594000d05000f2850101c800d540c059454103001034240480d0000b80e20701510381c1d0008210388019000c200500c18190050350407038a080e04e4140c18401240002c1e82640d03031140e000c21041c81c00244140161922440c1d2221080014002910220100c0081039075440d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 357677706 1250 357676456 357676471
    0x1608040e06120114010923010b1305010906140d0f18020f01090620010209100210050f01050d0605180109081c05040807080f091c020f0306093003 64
    0x49504101c86070601084260445100d10000c1100002d2104022103007001805444029540c4082d4494141e0340440280b072a581a08201590740d0788d071300c2182003540d00009011030701c8001840300080300e50241e06400309848042e10703055007003c42c24015903869002074440c0b2013600d03210703044503080f03440314070880c024000104880014080740780140300b00162208040c5041017a42c1c04108078142d0f000440e04803c46020300c00403407402d00d00070041e0180c0244400c40c1ea101502c8110700305403640008500b18070071001c8005000e6035071000110031111009200f0780d078100c000c9120000024120354040e0358030846011320001c000402c548030340c0c21103d0340f034001c88007840d0000780d600455624002c4010014403242d414020b44c40d190791001c0b030300d02034100c0052001c040401c451400007540000c0d584040c202801c18140200e034400300025070b40d00010240e018054122024110781000705040b40700e6440b49004104403000000502e50f030780ca1150030084100010708044203800030786c400440c0039015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 357678956 1250 357677706 357677729
    0x103050c01141e07050c1801090e0102040608060906030718140f06010c080a0e180114040b06030123030109140715020714010c0c171002120c160804 65
    0x380d0500152640d40d1041d440c402900c1c1c1401114915862250006001c03441002d04030789400c00c610705180b51000c01d0340c3c00ca601203001c1c0d405201602c40c0b402128103c800c0352809125807000108160300b00d01c1580142800038114030002000d80c10503003281030700204c001d000c903014950703a0000401542201410f0185280e10781d41c1070344506c0803070070240b82c00011100e01214030342422400070380011007140b401481100086002e291650080e2900300c40140081c050354001d0381c5c0b1b0024415079980900400c06d6420f4070000903041070405110f80c442c0000098007041c5143d003000c0c148801d000011080282c02010207140d0000c54400f0f02484030024803c000a83c581c180e00024141403824641118040014103d400c5071100d60010706202103e03445821034107c900640012a1002c1c521036014028900d9802d00040035400c4d145010540c1c0c0104081c0c0f02c000c0c006001a105a2040d1909040152107103008508120a44070040c2003090320310050303604c0d20206540780b900380e401c560302040a8a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 357680206 1250 357678956 357678973
    0x20d0b0108030a181d1f030c0312030c09090e0c0414010504110c03040b0a0509040e0a060b0d0b0606180307090506030c09013f050606040b1503072105010305 69
    0x41e0000c00150004005100581a45041c08480c0d04062804480c20003480600320214002c186c8502c035980c104c1d245d0240540a481c2c4908140195860341d01c4221008a408509020017620070b206008054100355600b594007480c215015001e00030010340c0001c240513041d0a0002e59071a4401d030140040740e100540003c0d807600017000304a403142482c01c01030035400c00141c906620007004450030b96101c41d1403151503c80303a034000c0740d0501079101c90540061070311140520181c000580c80d844c10f0306c0b0703003014400380d00c0c43c03420f001c18580d00500061a40840d00d011418914002015003500d54590701440181080b03480000d103805040d078021150a9621310600800b03060901c00442401d0301900c03881000d52400c02640c498480303116420b08506641c2214022007040071708601d1405090380c402090740c422a040850300c4413825a140b5200d0380ca004a20782041c10002c207200c552036103800b4018119616150290381055150074054040115078280f21403041c03441c418a800703540074100402c14031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 357681456 1250 357680206 357680227
    0xc05010507020109020105030c0a0c020d06051501051903091a040804080714011b020f031006052d060d020405031f0b1905010c05030f0a0810140306040f020d0b010803 73
    0x140c00c080c02400459040a9400c00580d801078101d82e00195850011a0b0381d00c4140300440744038101c0310000750b0010f007090115080c048540c00c014040c80c0c4441d101d20203012458015141445884910108920814400c04400d1700903400000210f0092112014240e1551040006400c04030740840320140c012a0034401c0c6603042003c00050208086404486604100080c00700080000c2000c00d20b0310804200d021502c626210301e00360399001c0c0c02c42e48010580054100641001d004460144105041c40060003151400038030546401071600312400702c0020900902d5030010403c0030b0006d03000c2200003290344041191000c0140501c0c3c0c00150145901d84060949450743c000c10700c515445e02040001400d41c00040c0102c1e8000d00300304624500f185007050450107220006483c01a021480c1b6000c0c9410090b0103114420302c007500c1d91150346842c1c043c48100c2d03810328100c1d01544500009400227010758070000d110780c0000c1c04000c0000e100e50b100c900d0300a0980200f00950800314511400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 357682706 1250 357681456 357681461
    0x19031e05041a070f0501050a02042904061803080403050a0c17100e0f010f0e060f10120305041e0306050a0b091303030204050d141b0603160306150c0501 67
    0x26924185440d41c40c052802995225060303000340b1a407040c500002c0e180c010000000072130101164014000c0c02946000380842000750024810f5102c03408101e05203202a100c100c2907551241035451350181002d00b444400ca40e055a400e0211490000c00704009c4082400b2101810056104200034520400c4501d0a00c41805590b4807841000400c1c05121f0081400030445a030088030702200001c40d00509440a440c00780407a03960801c551910001050b40291904103032a61544c1e4004c848460320fa549244110600447d0619409540940c0074002200b458039a1911540646070007410103844030080c2c2c2c0c0104a800f0410340e40c0e240118200100403081c0a480c0d4013140c40b01c010410405034801281100c400100403a04698a4152071001c040c040ea040c0ca02502010b0001500c0d00783c00e14000c100350b19424164010f500c28091400f000580080c2d9000202a02a054500315200c0790340c440c04442e034001d43c00b03003070645682c0041102c00c801852800e0361101c96884004c0780000d41005800c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 357683956 1250 357682706 357682757
    0x118081c06050315090c04060f0510020c091303020a020612090d0e01050702090a1103010b0d15060e130f0f0902040b090103050a08031f060c060b0f090a020703021903 73
    0xc2580c1004410455540c002c91840072140000c4020451603540d0039043d4100f415080a095100c0d01d0490042460f404850f061019584243d84003180e111340c2260690351200101c040592001070744c8001803c020410b84d0100d620351280c011150b00d0441640011215045108007039940500712003000b40843c02000080101e24860800c4a03441c90f40a000030310798813a00001900810714040490309440103a40b12601440e803100d24551a56110315403e005680800f0810b8406401c0c40090084040032400b0300080f03501d80d44032304101301034880034032284601c80b40304002d61540e18228812000b1103801140c054002010300003d040910344100b000701d9109c1c80810b4002c40d050b10040c0001540016058581ba4000482680b00c0c0c2d034600550428003403688007111192041e6000148003a00100c1e02c0610910500051100f0031003901440f50448000e2a40c0354805100f4010458150407603000f452024003a00c180d8040745e480c9050400c0303580104501720001141e0160300d01800082d281d5851 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 357685206 1250 357683956 357684007
    0x305030702151014030a060c0e03100b03030304020f04090b07091a0c06010608040507082a030604050d05030c0d110d060609080a020103020d0b13090b0901022802011808 74
    0x20b055091801d2108200e02d03060080e1030500c00d6004811035250390800006580c1a844441400303d44500382d070041180c1c03100300e03190340207102c0c00d01c8641004000d1b005040491078060003c45c1103540355020000c01c00100d94820340c11035590f1081002280c4110f4955220b001c0c90384504d80142c0c07a0440700c0c105140740d03911881402800b409801010b44001c10a0307411640c407442c0c03210103620340b401c2c01c41c1040803940c0680400d20948020402486030142c00780c211425907042c200000304c00306d00345501c0d00d00071034004210703400200c0303003001d164050409035030401201c2c1d0901d42441c3c0111101001c40368240b824910440010440361040760050055078050300003480e0901401c1c4c507003a0f4007640c81e0901c16000f0b041c95004604500300c5031442c0c1c00392201c0701c03004002140c1d081ca540c41c00c80040c103032001c0581e00070341c1c4040041e010f00814000c032042100b2a2450b040750308401c0001010003020984e0f02c1d0110b54982001001d0140302104030648507010300c080c07a949080940c440742c2450340550680 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 357686456 1250 357685206 357685243
    0x501080606090901090b0307081c02071203080703090c05100503180109050604110402120c09040f02040506041403031e0a0207060c0209010509090c03060c09040f0207171b03070305030702 82
    0x16802c1c0d10745500107411180401170200f034600348200001c0c180206500b21030164401d20b150740c2c0c8425100784459030705010640aa031506070301d03141065251010800041e020a0350350000c156540c0c865800800e246004001d03184c2c08580303d60029241d1600c2103240e000190f0040b043c000440c003001015070071580440005c1201e146980c3e1500e0707d4840c01000039107030900d905a210055255501142d80b4480ca8050b05c4156180111549039140c000030800c502461800c01090316030110752085400f640c1d001400c05081034034055600307040400300240d00e501070209011800d4004035130006a4840c131407806115440da010203100905e00903690744000c0030800310b400032102617100c030740800c0e041d00da080d62048400d50b41d141c1c0480c6003860145ea0f40303425114031806c2010214004006c1c1c00d800c034040b40c05110206890103000243e000d00040500f4090381d00f01d40c41d03850000c03400201030704140500380100f0044e8030f00c000b03401c4d50405002540880d0f000010000000da0600007a80e82c01c0c0c030513590 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 357687706 1250 357686456 357686467
    0xe010e0703031d2110090b070f02150c070503070c0308092e0e01020c030609061e100501030c0224010f2108090a1e06080106080915040f060212010501080606 69
    0x1d04c0410b2070301d0b190684070320000c5600c03141d010074403140134580c80c01c00e020300400b007071460a41e910400071950100002c100724031520200f40301207243d10110346130076011181501d031414000381a0340820301c116010720081001d800015146801040118001c50f40c5c140c0f03588a16090100030710301c410504c50380c07074100a00014080c0d00f00103c540241800e140c4100003500a00042c1d20303045541e08641d50501c0307180b003007220f071910001e40d1512070100a208415031a00d00f410f154040c10042e1f404804a041c8504c050100f54802e901400103e09544101c40324000000200c55035001c82c0c0b07201c40c41c00e0b40014018041106d00034403031b0b0001d10380ba42511100b828080d400410301403602000400044d000a004a90796417080b0a0001500c2e018000018000c0819442403c810991041e0f401041c2107100025103540900f51141c42851500064041070f01d030404440c40045000300105d903503090200862001c101da07803000d40441210604203140c654144070024001e494000d1245120f20001c100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 357688956 1250 357687706 357687709
    0x30312040602090a050a03050706030c0309211202090904080c010915020702030106170c0f211c0c0201080c130b040b1201052704020604210b0f010f03030e040e010e0703031d 76
    0x5002c02110f0090bd00064518843c810840140c1408000a001c4c5080e181f499240814007000b400c481c40e030180c45100880d1070008a04050340541414554440000400203010a07245001030006140d100d00001e0600d41c00d5642100e02c041e10250310103031660119104003181424456003001e0298241c20411421140c0801540c5400c2d43c00294040c03e003440008406444003c413000b00741c01c500c030314010103e141c4201d140d034440b00c0b0348003070903500c0e08002400592070040e03c0b11808903406039143c010a075105203908409a00029062084a130118030016030000e402000d040500740760402c50750766800940c807c0d01601d0060308164401c2a0034440740c0c048074200100712031b101c8180d0b4410328855446000140b0a405680c0c0320920303010911880104280c00301001f101042d00c00c5010074410b0b2540300d1001d00e47d040900a0300c4054010700828000300c0d016100a00c44400f0040c4003040f0154111100c07400c0d0350050004079000d42c0894014020190801032200020200e40148040554082e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 357690206 1250 357688956 357688963
    0x90609030304120c030e03030c100513030503070f0516080415090b0d0903020705180103050d02010903021209030a12020610061b0206210103050a30030b030312040602090a050a0305 79
    0x50b03100c0f0a104501a01c60b04145c0600340300841c8410040980e13440309142d0340d8031500c030a5144040c003856860303e000210810214181810901e401d03541e003d007150f9443d039042d2101c8110706a480c0c04c1c8031091100c0030a01100d801c4031075629100348034080e11071345004900c960788140380740c156050058024044c040b0a010750f00307a90035410340140100e807490f001e040076070510040ea00100d41000309002150000303050303500d803207040380c1c85003007141c2d00c1b8024003404074220340126200a00507005504004c6d1800f0354080941140351004040e0380e00020165a0b01c10300801c503010000c0903030010810400300c0403c218071302c00182018100340d01d10303811941100c01078002c0000000d1080c031000c2101582845074141001c2c4150050460244551b188d0808586c3c6a4900c0c00c1214448468511800110740d214000305da500803000c100440c10350044d5090700030b84000541c240c1c040c0300601821982410404503240107070701907180183d503a00c070072003402030f00d000c0d54000034001c130a8100100005807002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 357691456 1250 357690206 357690233
    0x5060c190e011e090305070b0c07080304060801030605060f0409050f07270207060e030a020a050d17040b150d060e060906070206011e030f06050709061407061a0301020301030308090609030304 84
    0x2103c190030030390010003910480301c1a040602140f0400c1004030700e03481d030350740101501003964007280e114942d00d03109103980f445507000d03500006400000400008003540c11a42d04000b00600e000521000040424116105400260f1f2281d100c0d00d4440100c400c00d00206000e03041000c504203010041000c3d4680740c030151100c82008580c00640d00c028803400e58443d80002000c07105807940c40041103c02569100f0b0310200350795601a030021604018052601001c08210780040715040b680c0b50f803030710342125070002d1813911807a050380c0b02060301f5601d00d80c1c007050152040e000025410b5030300c00c456181142c010f01c1003000341c0c4100c040c8078104c3e40000e9442d044981190f01011a04403035120060078100c81c0c0e0004183c0d921402d030710401c00103103410051041105543e5900d40c0c030b96809007100c40c11103100c51003030034500c104440808613080b60400d603500165079440c44004078211001c42d08a038000d034030540000740c04409101a55405120140e0450081070080d400c504103921081c00c0b60061 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 357692706 1250 357691456 357691487
    0x1f1a040501140912030d050a02040e01090921030608071d040b15090103060207050c04060f1203200a1a100501110c0a0602281a1305060c190e01 63
    0x1007004482800e00b40c1c200c40c100e480c0a0254034181144031120341d640e8006410301000d80c0d003440c0001d085240c1c18400c0c0c0d400c4403106540300c10b040c0d04e84503c40004001c541c00655180758001c42501903c10318040e24001e120483d034000501a00d2700500700d0911a0707580116031909409080078004515100710113400582186c0306070069156446441c0d0300e15002d40da8540c100d00e810380000180881c41d03010b00010750252060750315003054003007003000f2105a8010100d46001000082c00410704641d0024012407103410b00c0f80318205000e03907200c41040a07483d945110343c4041c0380c10042004800c055034001e4400c81c040380540c28600101c24001c415405201d0401080c0024030403010010480001144000782070008400c0d2103c900031b484058290b082d0345016805141c190050f403181002007100d5800030713107140200d42c06070401080d020303000c0c0c081100d400ca001003040104505010340d07405100b4048000d507841d907080100f80095512400170b0014011185501c00150360845580001d0303510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 357693956 1250 357692706 357692717
    0x4050d05031e010308031021061109060706020406020705220b0a17010e0105060d03080f07020a140a1703040209060906150705011e020408030a21051f1a040501 70
    0x450b109000d0799100781c00a001d509466100c000000c0c003210b02d0046000c2c0c0f00c00c82d01401d800f5100d4006c03040c0c0c0c1504c0d030f82c00c3d903040456a0440010860b56405001c142e0344810b081c03841c100403000000c1c0c05410488040d01c540d54005010085540c0410050000704020342d109a220b54406586010f40200303e005840e015032520f81d01d2a0641e103180038040034121100c07030040d030082075001d002d00070041c1151a1240b5840d01d40418418a400d0781d0701c0010340d07410f035103c03d2941d40c0c615000c0500a0080d04079010f62068800075400148078003c0c0c102d41c2c52400004042000c0c1e20704044880080ba101e80c083e01c40010020300c405600d034103029030f5103d0b2080c1c0d0f8201d00b0342c803024003146050301c11640c41c1c1303180d90303011038a40200300d010340000c1a0038800f40d4004011009840a410880c41144588841548100081040709008224000008502e2000d40508800100d0120281d960840c2d2002d0700018111803c0b070762407446a54070003c0c01042410082c05050320341c41182611a50158078103000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 357695206 1250 357693956 357693961
    0x506031207020a0e040b1006080108030f07023705040b01050d1e020f0a08010504021206120c030706050408010f330305070305070303020f0a030e120322051804050d0503 74
    0x4550034800f07030081104005505044c50281003900c400602500c0000c882c0c84800d0300083e02c01e01c640710080c141c070740c130300055031410001038a41542070780f18440c100c0c0c01c010003e00c2c01003d00403650303003070f21607a002240154805a402316689410707503464104030f20072460928a041240d900c0001c0d9140380c8c1030307807600140700565021280d080800034244030710b400d8000070b01c041e20360296030081c100180d081c1d20ba040046e40c070303041003009038041c2c12100c1e9001d41d0a04009021468003103d61715600303007510240d989012172038010908012103500440d021500000342008011400d100d40800140c08041c2003040d03011440c104071640c1c404049540300305a002044000141079050001c00440d030000c11210070310707074a203011622481a84000e9000d40103518940c030400002007458403035103500d0390b504036a264200b0104a1500d01043c11019144028040c649038400c92401516681c1501220307120024a882e00700480c140b807210105081c08503503410710001400004007001000d040d401c00c07035201e9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 357696456 1250 357695206 357695209
    0x70b0f0a020f010f0b010f09050d0605100b072d0309060f0302090a241b1e0f031d0402040f050d060e070b0a03110903030a0c03111f0f050603120702 65
    0x103070380e41c0c5044816529102c1842002c2c810340e481702c9a00702d400c3e201c42c0c1c602c8035103400c03e840101d894451030740c000d074020182000151081d4440e0340c1c00025489140c410584038441108142c02c5600120f0389a40303409500413044200f00c0610452001e160b505015160f110740e0010301030103591207400180050618811013040c00b0390142c81c3c10740f03400703030100725031aa580125801241440d810400041c503c2c004c0241004d12554501441500450008d10141d06640e9940f4401c07104001440b2030300099180540003400100a04025501907a03504448604403100c0c400100384202c0c119102d10b20402c410042d024901c146c03081200d100f00c6c2d05050b11030540c205030016082d100780e001414011980003280d90303490724003c0d040444180d6000c101742d40208905e0201d61007440240e80d03040d4000e00204001070b2160781355030640d500c645051603100c80036080d010318010030802100d540f030b5505107000f01c01004510403c00f8a883c00c100600050803c48d0110382c660b4103151003100e81480005448065 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 357697706 1250 357696456 357696463
    0x702030a03030e2811040e1c031e020310050f100305090a020406031211010c2a080c03071104022d2101090b01090b09060d09080a0305090d02070b0f0a02 67
    0x10780041c01400100c008a040500c500f0014407541100e103c07484086000d01420541f050090304e5504100038070000b0403411a40c2e00c5000b03c149820308040d2a1043c80c81d002551040415140e25034480143c1c80781041001801400300c260000750044c42d4110b19501306a894401c01d079074142c1d8505000615032510000541826040c02c0b0180d0001e090040010402c0914074140b000c5201a907903440c075440c07a070700003507080e5002800d401c1d0020360340e218100c980810141904400783c3c02c2289107050503d072640c40008c80d030050b800700d509503013003c03502d9000d1064203488085601d404950840c034119254100141d500f6001c546078070410894a14482180550b00c1140d2410550000b0051104003031100ca07600b1040c24040d66690506103200202d041d40202028000d6a00344c40b1140e040030b07400414000160041d05111484030384a2125101041c4942c0091504601030342d0081f03560300c8c05010300b07490300d1158001d4000310b5110080811000c1c072b8a20603240c283c0300044c0300c41d41d1810500d0f400c074503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 357698956 1250 357697706 357697723
    0x10515040b030f040209070503040201021c12090b0a23071110022a0d0206150303040b07050703060605090c04090f021219050912040b210114150702030a03030e 70
    0x550002c18418030118a0b201e262045200310b8007594190f46510040351940416600240568841c000300c0754650b400c100c0858010b0084d20b80040c1c160031800360742080c0c2e00c000e038080e02d00561803400d119a920381c90050200142520503181c1c045407001c182c190601170014078034800c011031700e400818104070070b205804101140003070942d200c1d2800d5007600802d80001440540801003890a800351080101c2c100d0080c400b540c002e04081e6448501410f40102c44001040e4075000800011414141801c06411440e010750001c01d40da60440c43c2001c1182d101d5040035114134044420441203841c1c9600700c0d02642c0030000b012648400f07031600107001c0d0180c108540044c1444408110108042d469a42c00e49001c5500c1440720792118003460380c03224110030f03c100c503140041105008290455008014400d8000d404806080220700042c440398000e07041002c42d1010301c8405840c0d03190201900209c0d217007542502e46004d645500099484a60703101c000d09041c1c80c1c100440c169803051107803c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 357700206 1250 357698956 357698969
    0xc06020921151803031b041d0f06150403030f0e060a020a050d0504120b041407060216060206070c110a0e0a0c11281106070f1203090b01051504 63
    0x16410960610036101c02203100b0742e071110b180800020700c19088107807006403800061005545152500300880e0107035000c0140070403100a0411002801601940c90001c0341e44d410a070301c180500300190508003425000d801036105071131000d5002d03680102c1e0b0044600b140e905027491823820204043c02c0d40c00c1d02c10081001e5000d24045000c0310362035004144694040c7c030880955800106600e0103680c68007031406040c01c0d045805644a0000341c2c01d1010680042c01000c5884003101d0030500e41d8a811083e410110058000003c070a07009020f002002000d84039134005081c2c24582481d005142d15081000604604c07001070400c01e0303940ba61561103019110518a2292502d00800c050303024101031200c9100007100140312114035a070100c1e1404a2650100300001c1044002d1040440b210041d44141c0d890500c4e07001440300da03038070b00b030042903041d03c10705001500350f0840c1000589150001a900c05160401c10380800054440d0b00b010305503401254400b64016159444c500a4000d07030300701d00b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 357701456 1250 357700206 357700249
    0x406090e1012060906051b0406050d09021c050601080703080d050c1903020901090506090d03210603030807030509010507080610020c0a0e161707030207030c02090a050117010603030c060209 83
    0x281e0030f0108a403c00306059003e55014400c0d9142c0032592600d11005034541446000140014010540b0a6009000704440d03184e001c0f802c04080d4000a10024a1030ba0f852400d0041d4400003003006030a0100790b00400075040900455455500c0b000c4281c806ca5404211071a80c40e40080c1c604007500c2d01b41c440c10303414404041d16603a118072000e0000c0d4820100d45000c43d805010010301440c0000c102d9800c440040c2951681500c5a54180c481b4201e000d0f1015030f180f00c02030315000d030a2643c85071000030b6010b03547d13903a0142007500002d800c885014043c10b00513414001000505d64100d054150030241c260340b110032031a03040004a00342408080119406000c5407c001349002064000c54000c8a26002c3d82c5606043d000041c0c6a00e210361981d511040d00760b000085006c1d020b0b0340940080c5020f070910b019417407000e500003080c040085481d50409982c031401401060055681d40002e01d134040c0c020415241951400f03004880c102100400c81900040e507490591601c282c006032035074901c1b40c607 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 357702706 1250 357701456 357701489
    0xc0f0f150207050f1002090f060a030605030604030e10030c021b2d120d0903080d020f030a02030f06010e030c090411040203190c0206040215162003070b0406090e10 72
    0x42516050900f50707041c030500c6401721032000481144212019080c0c018002e0030303c4036000c810f000c030f550403103050401403603540c19000030a80c509020480c851486a6640c4100074010407c0024514032081200c0030545000058510a50005000d60303032020790004140c0000c850b0800207002e09d15521070050700000e80a8005440e420030b038802c40001008903031441662001800030340c0e494660806500000b00900d40800c003044003040240101034003410054034024038500d00c004542d109842d0500344590000800c0803000140740d980303401a000340780944035540400c0000c0e54904c070b03a1034484d11662040300850104032071146131240095000d00290b480f80360200e5901c440c039000034030040041d4205030b50301c1003852001c20814401d55006003e0054095150005a60740e0004d68126045c1a03400f900c00c404180c407079050440d0f400800280041c3c4403c541d05160500c403295116641da0103041c40140051900400745100707448841c1c10080c440d0ba2109010705c2030b00038607442094040c05c400038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 357703956 1250 357702706 357702713
    0x609030f010e0717030a05120c1303030818120d11040e0108032106030604030e13140126030a0f090314010f0c08070e060a0309062a0c0f0f150207 64
    0xc0c081c003100c501130883c00b5a41c10076400316880f8070410311a94000b403420807586520035482c030241d60f041040d01c641c840c141003a4003c040c80b880340f0382e00203401141138801080b00c0c48028258030f0540125848c040e00300c03500340b0101d011090198400f007044094845000038041000c0e2016280280310b480c000c1d03041c1c0c1d41d50b440e030f19807070342d1104a050072040c1000c04080b507580015001d4900510002e0010a50b580d5103032012503a500e0340c428807075404418189420948403aa00030003551044094050307909514202030425502c0340b0003080c0c0032410308810440c40d44240032068076400e08035070078141d00180c0780038002c4a09180540004010503502c0300d044c116102c055010720392225403101c0800c44524990000e0303030442c2e011950032001032503401c1c220080e410580701030300303450810f03050100e40500c461f92950300342e484410005c1080c000c0041e404800001d5414060000c810b40c0c103011325901c03040e40b1848407514210701c02411040705d8a01c041c04001c10140c03000e030b0000304c0c0f400464a4181916 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 357705206 1250 357703956 357703963
    0x705030d020912150c030a06081605120d020a02130b0a060c15090807060f1b02010b03150402150f19020a060501150c1b050406080a120507110609030f010e 68
    0x40b0311400b4100d505607064001000144203100701036041800511559070340f02268540e071004040540c580c0d20384100180300d007410068682c034208007061111000d8142030622000030291424000b295005a201d000f102da008140307484040c0c0c040d1402c144e855001440d03a4042c1000c2e00305181c00081d00140014466881a00300b00210700c0b820001c90307a0600740100c14259422008060852074082004400060003580300e40c403458030301103000ca1559000204203444800b4240c01d80e016075100c24003480715182c14032489054180001c103101c0d45042c1600030901c0811910b0590030031240007e08100c0011001d0b0030703201e10007042000341141b8a60710000948803d1465000c4400500b002c0000c22203083c034404190352000950364100e03440b801c0307403642c9002146022000c0d01303c0c151801c01017415201d502410014000000c01400c80d000e90389070075071303000d403a80c8446020400c0c188034640000b079101742c4800110300c00f1250251250b4200002a0400b0a90054407886603c3d0850b002002203011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 357706456 1250 357705206 357705217
    0x70803120f060405011a090d060e030403021305070806060a1101021605010e0a0308071b0812010e010801060803270405010807090605030f2508010f1a06120402010f050705030d02 78
    0x1d19411900d912030205201c01d40e0720070700804094070b182003c2c0780010070f105405484901e80c000c0098a040e070b42510745108650010b2000007560704002070910070f60418004140382006d10340d604024034500814010800440071344042c1c0300b0600061011841c51142008240b00114440219600d50580c40020041c2118400c02c880c69400c1c030411102600001c584114074030f8040d00d031002e0b565a100000c840340b401a490340c0c81ca00d40e00100c4030005c100740038090085502c2a802641940d41441003034401d1280507448075030706a0401c407050206c08808002c0e0340c1940051000c0001d03450740c51403001c00a0381d8840685410501c0c220000030740581c002040811030300310300010030245854100781a101c05c15082e652009074010400301740f2450110007400071101482642c03946a1343c40350313100750a440c0100541c424081d191000f00d03280e600ca8040d10003001c041212058900103010340012a41240280003a05216461401d009468058011140d0b402e0f070110540f550344044020100094002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 357707706 1250 357706456 357706471
    0x40306021611090f04020103020309100612050606090c160602040b0703030605040b0117011412191b0320042d060501090812030421030b01020f06070f0c0507080312 72
    0x100700c0101030b01d062035600c2a0207007070108020801ca594940042d000f9500180070101c05205083c2848000101449404041c1c2400a0406040c401d2401c0c02d5141400c00303404203210b59088401d0003210101c04c070483d4241020090000f00001050070729400030b001d02e0384109030b608170004409042513815480070341a10004c540410101d0ba05000455041d1f0915034100d1804000800500400400724560303180208000c0c08849106c84481240e070801100c9a001b01ca980c410843e4901002409a240d900741054216004800351440d1900744145101c2c00f1360b0700040c610324000b04115142d03501b046210000c00210090b1501502004c00603841508281c807409902c0c0c1100411258070605880086070203440060103408011044243c460344007410850709280c47d4104100c040c01180c2c0d00b0004a03130503450000b002009200064102050450b0301d4195070880c0e03041291075504011402c807901807a2409400903006407030711038075081d0070b508501043c0c030011800700322400d1080b061a128102c1d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 357708956 1250 357707706 357707723
    0x9020d0f120809071214030d0c1d01020312040f030c050f1006080c061b010204030c0e090c040e100b060f04030b06010212070b060603070c0219090e160b0903030403060216 75
    0x4500f1030594899680b801802000901c4800540100c0c21410b480c01d010f44845003503a1426289a0000040721800306184000c0742061080f401002140c02161002d0042800514600508a80d40c0e5040c031000610040202000041d4201814414102941c0351540402110051104498035039980d40e608500c590702e01c0d0070f206021030040000700315038020302006820142029660030800c280c0b402c64104810080d9405e00c40000031442c44100440140707040c0720f051015041031080c3d40d0a00000d8840c56000c1d40c10207007907c242c510300155000c80c0e041c1510001421801e403000150144c03296850200107030390081008001d004c0700642c842e0065601b6000c172003804003230405180e003078051010040c055031032041c002a100c0c100781d4002c50303011013240381100c40d5441690004400d62040d400410a40d10601c0c42800b0390076891041c1840c1440c824020800d901c84185840d1480e00c140c0200c00a20b48007286040c4103480810aa9003e9540300c071080d0746901080014135407000200d482524bc03000b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 357710206 1250 357708956 357708961
    0x50306030106210221060a0b0405011d01030206030a020c3304150c050903031602130603021c0206070c14010f0f050306040c02030904020d05010f0f05010203040909020d0f1208 77
    0x160b486a560315076280c080c0c4820b43c0411503020003045980004015003600c10703003161024490000e0000754442d4011340000180500510107220460344140c00103640c0c05c0141d02820030420074450401e04680d4122000c0e5074030fa0310007840202078081d030900d1050038401d07012401c46030200c8444644130284101c00300c00507035507074200201c0301500949000e0600c0607410441001107800b44c106941110250820501e0683c032b10010a00d154043d08052440300c5058900c101145002903503100724140c1e8000c28000d150454001502034070b01118603034040001c800c0000e00b15140c84007a1040c0d29001203801c229959181d25403d202112480500c1c00603060f10854900c1e40d0007400c40c40d0f0420165521982140d54070014400200008c3e00c44c04d0540c80103101c60320480e611800149804000040d000c1421751500746d003000030300c5494000d60103a02d827040050255990000070b940031100c4410300400e188805002291011b211640301918614903a0b8041c828055410101c90706080141d0f107040255 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 357711456 1250 357710206 357710219
    0x2030c01020f0c1504030503040b070e0604030602070507080f0304170712080325090501080402130c050d0b0d0302031207030e101d06040c15021212040c0603020309030d0e0309040c050306030106 85
    0x404d08440050108a0600200d00480d461003001b40d0700403054201070a0603e4032800050340384e000350740125140d503000100142084014032034140104124001009000c05807101c0e0703500c9010318082c05401c03c6c60f0208848108108114801c000c2c1910003100ca08450b0384d007400c01840d131040350000201400c4449441d1460310301240b201140e0407035a645ca949600300302c011608900c000d04203a911600c2041203540c00416403150b4100b0400684a80fa600c248a0300c0a41c255a1301d100c2c1b040c8520904544003011940200460352010003041d44280d250751040310a500500014402c004e91307218803ca90000c03241242d000c90445800c102d140c0c203d02205000c0380e03a503070f102154010284c0400100070880484503012040d0350f1000c0d40141c400e038a84402818540d0781004c00115610841c190a00c07003840000400031020f40364a10b0154610305c0c181e0980350b52403143ca041402101d513543d01c0d4940420092058a8a00748005c03c288010700240d030005105c0c1c0c00a4420510075460400c000860 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 357712706 1250 357711456 357711493
    0x190b090d05120a0504032a03020d0f0b0c030603010e0604170f0c030a18090b10030b01050f0c01090308010e04080a050d020909040f06050a23060a0509040507030605160c060b0102030c01020f0c 84
    0x40c81441f00c0b510b80074904540c24400c0c0140c0c074601c101c4141110300c021000150412007813030300c1040250200c4c0d40380e01d0400200b5003900c40482a03203609400100c2804081034074200f107182d2400740d001065a90381450094078489200d040300b00d10180c000480d030700090580c45034401610701841420340042584409000d0103d8240b84a8543c1c007945142aa40744503010707030080b503004032050400c80d040c030000c0c484c000c41a0344020441141c60350342d0b0242900b095080b07450903001d00f40c4c0c003500441e01c0c0351581d2141594070075078050703400307111011841100066a03501101c68880c000341c0340b0811410146840071003541c612408840190400340050b0200c40c151050f40310851000310b00c0c01c904160b2520b001410f010160510b43c2080100c1000305031511040074080c0034504c2000100704041c1765003050000c6480183c50080060034a0307103103d910701c3d8000d4500b41095004880050500045c00047c0d103584520781c9800119400812100040505100038040904c10401651301c411805041c0014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 357713956 1250 357712706 357712763
    0x905010506090d0f0c0f09020405030f15040311120c01020a110c0f060d02040302040612030f030b2815021b0301020c030304240614190b090d05120a050403 68
    0x411075900d41c3d0310004215030002c4901820301620844402ca40c96100c02c0200c11196005548015000203081046040801c0b1800451040c0c0d002380400030b4000a20181c4d030701015101808002e07035003035481c20700007050196508510000c1d011a0383c2e0414449094081c0d004580e00602055050301d9444150101052442c0103420007455140c40807040740800c140c94109002c43c048103a0300f40300200051b00c8a102d504054007104006451108062800404020041c20402c04050500e1960301541c3c0310000e0901100c440c0006000b4680ca602c1d44551035000b980e400758005014080013024995008603555040d0802c400070426042c50500034503007030f480703660300c481c0c000d600810002d000701d903a0101e40ca0030501010598049030407508098800d5441075041a00c2c9403c10700513007000e902d0b00c0304c0008003000f04c0000c8001d0741441d0809181150041a03045405018421528020071106101d071074158501d00e064240c070380c2d2500304010000e030044d0108840d4210814040d000341543d003400720a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 357715206 1250 357713956 357713959
    0x1101020f07081e0a050f01060810020f3f15030f0309040c020304030507090203070318030207051309170702150f0304061107060221010f0305030720031006090501050609 74
    0x100035020041c4610300f003200412000e416014607000b000000d139040c032045551400040c00450640e0a00c10841e0400740301d40020b600891040008030b10444820058500c1c0c9507996a0b00704840001d040041242004035000d0421242010b40703400e004041000074a0040003001d8010300403003900340905503039016805210717449500504c14562a882c2980108014105620649052540e65585e0700c1c601101070308000b0240d5008010002480d92521a0380c1c0c1600d4400744e104001d0280707850107074032842640902e034024082d00000300e248160607044919101d034480c5498015141d0340150780d41c1500507150891007907043c80c2001d40b0051010041d600150380c0c03280140d20307544076583d80038010401810180100f1405010f40c03c04281c15101811225082800343c44400b2043d09a00d05845416005404070015801e000d0010030400001d42d036840344c4c010b012403c82403582103503c15402c10203d04541c14480c900d0b02903109412a0031801c201d8010410601481c2d03240e80c00c001c5c06014441010303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 357716456 1250 357715206 357715213
    0x40515010501110c0d02031519051b030708040206160501020705101415130507020f010c0f020a060f0605120a03030b041b050304061410080601121a0403120203041101020f0708 77
    0x25960340c0351824000913200d100508442320488200305c0520015821120103001c0018100c0d83e260326845400b502e5801400f10895203101c41c076481d0149002d0001800c0182003100c8032001900715154041110000c00803a00403a96010307170b602d0300c1e50103544030a0341180c5074055841400002803007401503141c0c41070f68020500030f40d03403220b14003c18440d00c945e031198800c01d4249049099070041c030a05003d001c0a0303000e041c200102c50061829251980052002c0051000c02c14500315804503412207800d81c000c0d80031074100d00c81e0b440140580020b40000e507000c141543c4038120290b001407070342d80c942e120362401c0c01041e080e1020481211a00f1808140c0f00d182000c00c040014030420085501910850001400d4054960b2191002500301d0310910000c094603410b10120f601000304038010b180b10a40c07034401c8040d503950586030743c503072460f5420180c04042c0800c04050044c80300809001c040c850840d02d07803409003000d200c4514000344044c09400b9080c0c0c091040c1ca4041303078040943d150301004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 357717706 1250 357716456 357716473
    0x71703040e1308121f03030905040f060e09031c020304080a080601020f070303050a0207080705031209120d0e0f010c0b06011d0a0b0325020c041104030b04051501050111 74
    0x28000709071002488101c0d01c141002c10100022014005030041d514080c00b241000d10b440c51090010b4907401900851782c0b95004c0041000981c090441320a0700c0d070564000c6003110484ea0080040d04098001c0001c540000e0104241e8610000280400c080c8021513800b040a00c0080d400c02c0703200a4602a00c1c0340f03001c2108100450080301401d40058042c41210401141d1561040c03e2820603001180010700000310780c1141d80d4100708000140030480003030212545800700099891600b00c02d020010301d400301c0e11003859690000340c2915801c0080c26070300c0725140d004005240c0c04044105601c540b81070000d419807940700310a918425a8000c0e02c4c03d440e80c60b004010f440b01c5000c40010307103042c50440c80a10540d10b80e030b46014010402c0244803502ca0030302645c004480c05410400074590b2606a010030003260b8000780101801a00303807800201d108240c0c04500851146e608040c0860a5000a00c0100203000a0001d8081400441c0c40c0c0140d0300c0d1001100c0d0294038001c0c160f12035010541c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 357718956 1250 357717706 357717719
    0x1305030405061b0a0b0114010216050d05031911100621080f0f0d062114070f0b1c1a06090f090c0409051501050d150305071707170304 59
    0x510400c0c040f101190660903d288000786820458034007103401150100040080c20500070052202ca02d0900162542d00341e24100c22000485903c40c02d071040280c004128103000c0c0501c200d0300c1c4001e038201c122038902d6107006e0142203184000d410010510074400a5000040a8480c6000351902e00200ca4100d011403410020411040c00064810407000c1040c6560102400001c1c0f0311400c644030140d44078540c485481e42198441d51007412840301444000048082c14100004e031568800000c046d48562890003514110482c2c004a001c0d41c03400c5800301d10341a140016001c582e110410042d0304094050101050302c171401d980003c1c860f00020710081924100b4060219044090180811080100002040700405403101d4840c5800043c043c000c035404d500415034020036400c1c002000f500f0302c00c0020f11510030710910f949000e9440807441300c1c1500d42d00024009680090440e95656120b04007184069029485080c040c403070070b003000803600502d10004510186a40207541461324008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 357720206 1250 357718956 357718969
    0xb0a050a02151003020906030105010b03011505041a04240203090f1f0905031006120303022b020d0b031c03020a09180504030e01050309060619080a06141305030405 72
    0x90110a50044410210782da45151103941d21501c0c2039040c0720101031460050041e6460041d158600a0341000010301c0a0403142044a045071f000c010302c804a07005001d0700f00c98901894002141d000c0103080c030fa14803582100081d00507200000600140c4000942c850410300924800d101c0c003503082808400c001d880c00720741c840342008002e440026040b100c50801c1c6044001102d2040114186280a01503410b0411848120301058882080f4290501200c012b114441c82170042c02c05400003031100c11501004020825140405800303800500300450f6880a9040f450038407084514102e414282454005001451120200e541c4142820202011030203544601b020700280861000001407035104400c00e50004005070200207140d00349460010040c000248841e4100241801030040d40f12000c9415a04800b0496800c403110b4000d040d80b03c003c0e1042d80c081d600902620b204281800001d802440c14640c0d94121081d6035039030300310808070702e03942d5650141c1654000c1c082403150381443e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 357721456 1250 357720206 357720217
    0x5060d020a0b0a1101050901020a0f0206010f030204050402060f031816030f1419031106070309240b030f030702040506030307081215150702030c011416060b091806010f0b0a05 77
    0x6241002c140c0480202d01800d503031042e10000c4423030791b00044910540350301190310744d0009000e10260205514014410404103000e0001034450351f56071000c1001c540c0c61004a0702202130045006490b40f0b0b1840a8003510404005101a00d0042030300d2420080740d8420900c059940c00380e00900f103890300b51600c220481030302c8000102c3d4801c0515030184101d410003210600e46c820303a9030072500d044110708541808000b46c0228285414030914100041501d1000804001d04000320031079101c0582000c0060205411415011301411100d4840000c01200524645000b40c0e018080c1d0388480b01899900d00c01c0e007030094241e80d402e02ca41c20013252044e00302600444603180c1d0006000e28040016111b02c2030070302401d003204001402d103045090038801ca50306000242880350400c80c00c034501e10054490491901208981d040641041080c558022001c649026010b604a45841110b811210f00801c4201070a40319030400025540003000c660000e80303500810301c1d4240800000292620b8020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 357722706 1250 357721456 357721477
    0x110a090b0f09030114190204060c030c3e0f010c080711060f0714070620031b0102040503060f1608060105071403031f150c080d0504050c0405060d020a0b 67
    0xc100c10b205550b02405904514002c042003140310f0b061084481d0072643c07520076100c002c140180010003051790082c0c0c1800545815040081c240c40f0b1602d018261410011722455607084041d40307013480158540e4082e03c5001d144068541565040003c01401c6d00d0014140b6000030700200608000659900c0580091445550540465001c55000600b160481107006c4400c078004100002030001c00c005c1140e00600303030f0018140711418400c0080c0301c20500c0300041d0202d490503003e030b010302e1010021590285460140d81154008031408070b4040e60091107000c0c460f1040002040201c0402c0103594065001032145040b15901e83c98141c814250007000701341481418130240340480c1c14410361000119401020350341d40e01d0140d1414000c20b400e0304a201020a0202051240514100300c4030342140107414945030500307040c50b004419200d0410509142403c00d42484100700b0001421045030301d046909008035554074040c02aa442d0040010358007000d25a800c00001039048000c140c3d6885 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 357723956 1250 357722706 357722737
    0x30608030f1b030309031312030e150d180b100b160204021c05010f1409010e060a170a0201020d0302090303030a090501111611100f050c19030c06110a090b 68
    0x41024a05080d5001110709030100d4000003000c800001087c58898042d10002c3c0500070102d2060720020000b03c011400180204800e856045100b80c4100139204040803911052001030140c841c1140d1010342c2d4902240d61000b1100441c04a40340d9080360021b0300c06880c031081c00e05111140000f6440d581c3c140503600140c2c00c20107920b00b0640028440841440f954020809506d0007814101102d00c681c4040406114000c64440940da4003160303c1c11180d0380c0350320890607240c50000504004080e880382494640c40300400007103240c0483c44408041c002d03000d9401414010900340c05901c03c01644560540003080040d504101a5200c060300fa8000c8000003041040040b841c0e00550100c0320310390445641c030106800300b2007009000d000b100420380e03442e40d004c0a1943c000c1c080b1240e400c1020103010000c0350340e0000c11420000756003100c00090888029440500b000b030045d52081d03c0507035a190a140c00c144410411104542001c0712603030b00c110507107262208009180c2c01001710b401c04601c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 357725206 1250 357723956 357723997
    0x1516030c06110a03050411040204140105130e071107090b0619021e07090501050f030a2a150f110607050d09020306010621140c2115030d030608030f 65
    0x1c8055003e4040300101d038500060340c0c1481d00b000d03c000d5400e1a0680e01c500c0c0100810300031070391841030004007404e00303092040c1c4400801c544082e4008841e00990011546401003044466021f01c299018003402c2068404903600c422040c800e0f503c4514005402110420014480c40b20704019a0003080407807068400d000006001040380f040c500c001c000e01680300160500c07140c0d62a11440d401000110744c0000c805648901003a101c0a0014000c2d080300a6a80e82d03418206c1007100003512a42a00880a120342c0c4542d00c0400d007010401a600008038075001141e003081c000c070500c0382d4034110172006110711b0341c0764903040300d050340b00303203410002c264841003004010f07101003021038042e081545843c1e650940050b18000501c3d01880c0c1c520750142070109240819a069092a8201c0301041c0400e039586000e00c1004209102c07105c2c540c2400c01c001040103004440010014260348048082c0e078082c1c0031200c02201074501070b000f01070031070f00308100c0c440087c181c00d03000705102191601c50f418943c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 357726456 1250 357725206 357725231
    0xa060f030e060106090603060b1c02090102070801050a0203010f05090601021c050d020408010614061c0203040f080c0f10091104020d060308040308040905010f0e13020a15020c1516030c06 82
    0x9900ba4130900204400701400e0104a0309405070700b0107812121358041c10b05201305403400c0307005080c172640040140d0002d050745159200f845148007034904007000740100c1c2812550200258400d2042500c5d5020f040c00228640c070300f1143d01030050405034020460440089405513465082d2410202484410000310440545c580081c100910070301000103203807441c0070340c24480c0068400c103040c4154400c00014604038032040c80118500b0320104010b85a95507072603c24085999030700c0103000c0d02d4000c240100007602c00a1354030800310040d4155109800300c9441541a1240c091004021649002c1d40c1394aa051640c0905406546c8101c04a81a943d070388440d000c5900c144c00540303104500003424030050400340103072801021760308a0780c803155141c111259080040a00507000c001321110b40b00080d5034031514104090f02038828124001c100c0c0c403901941c0ca040304800c05000d20b20700101c818402081c01c0503601405103441004c1802e1500d40e40480340c00b000d045080b54040d5603000b450014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 357727706 1250 357726456 357726463
    0xc0402031e0a1e050a0b01020a1707050a23150628090203010320010e0f0f010c02060a05312c160320090d02030a060e1e0c0a060f030e 59
    0xb844000b40300001d01d8107101005800ba06c1c0402141030666209420f0303040040c5280c80301c03015040203401c0c080e0b11040385e071502601f005409000a8550b003400840300c891005840001a400d400281c1120300e1f040003c0b03c0301d03840c0d10b021100e203540442c5d800d0361165003c41c0e0760714440d0f003200141a4801c0190312031440b842241c00030703082901c1418805078402c00710301c2185440030310707003174242402c0f904650820006030041000c10141409a010120618910b9000d8040c01005035070060140340c44144018000b0b260390004032411407111258001103503030301e0a03003944a036009101500d8032452405c20a26960580c17081c14240324113103450085440c81c5030203401003406075908689401c4000c09207940281912100e003503031541d010351000000f241d20a0f28045600e801e9043d02d0b042c030000480c0c00043d0400c0c01c620000340245003040c505003042e0b20003294086e510800c3e038030320642901c0c542a8003076448140d4403c054029400c40018008540598090203c2491901d004542e8200a42c00c2505 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 357728956 1250 357727706 357727751
    0xc011d1c050d050405030d050702060301182009100c0f02270709170114071103122e0308030408180d0308070906020f03180f0303030403050c0c0402031e0a 68
    0x40f408207080c000c2d0320b014060075040e10b5051614908068407900014403600c010301c912840960856580d51000440d40c0125400b03c1445071041d4042d12814400002a448140c035648600c07013042c00d0040d41401203079a00000d6410800d803004544040c0e0a1000008000c6402001c1540b1003a10f0061a0300480e48107104041517662000c02c94a013840405600c0d0803030760083c80d1359040104580005501480c65a8810f0440c80c1c0720b1a90031600781614210321a01d514802c28004040400c0f26002124184548128210030740140f1b0441c040341c402d202d4036446c00000d000d80030410104020649140c040c0c21107040320001c0c0026488400c0002c0c80884c0b0700722080b000305200d6402c02403000d810102c05d400414643c00503100c2c0c10b1411b9582030712445916035002c0d108a02d164286002d03101d2000c0e0040aa9000e002c0369503e060500f000740c010b4002d00c94891451040011000c5d4a08040c02541d0080008007224120f44c3d01200740320b03075003210080c16600207550799007440041c2013a80e603002d00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 357730206 1250 357728956 357728983
    0xe060d0f2d051f020c0a0f031b06050105030709020f031f0e0112021207050a050910081510080307030912051513020109050a050109230604090b01020c011d1c05 70
    0xd0b070303041d01d84248000004003886036603d881844804030707010340800d40c40d004c41c1e4840c2404c501264903207800c1e83c426500c0f0001084114040c44054200881603020354140da108038100c444550762003521400307900ca03035009100c1841050000c02c0e400b011500200207840c40c0f01c48005030081e16806d034049104401d0340070006400c0028414010760038401801010709a018002c0c01030a42418041040c1c00f0092240d1801074842e4000510201981115100035000c064241d40c54148181142c41d03c4ca03c0907141600841c1182c000081c9050740081107408056241c0c40d00e01500e454445c0d4109440e003c0c10094a15001d080310100080043c41e483d070744103600d5030b2017030b507082c020a00005040303a040d60802c0380203400088050080340c0c0c000c14058101d50741140750341d80001201c0300c1a034502e01c1d8200010340204004c50003107541d0301e081e003280f01545420703404c403010055803000440e601a0480d441100e0304810030305070842420242440801c42e0944150b140070020300360749151070180521a000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357731456 1250 357730206 357730213
    0x3070e330d0b0616030e010c05030906220909032606040903020a060915060b0315060c0a06050f040b071706120102130f0905070807080f0406240e060d0f2d05 69
    0x108200350701b154074080040380a01e48998000b004d665034075034034800d036002c42c0c0c4900303000f01d859410b03480c003005007940700310300f601c803048401d655907072540003a20020f04100e000c101c000820a005c06601030318030b104124003100701071507600e90ba0103020040c4010902502140520703074511000c54400d0190640003480b55011300c2d082001000102c0c00c82d42c40303410590380e50001b0000d014104154040283c04a0300c100d4225540702c4500803464907208002d50020491400d00042064010300d01c00c410303108070300522444045035a900c2c0122410306552180d90314a91080c004903010341040e259103031409a42d08001442c15000400888103007845074441d84049121a205000854031405216005099030801500da0305150101a0840b0002803048603048400c4000a00b0701c01c25030041d03880040c807461212a03141141c0c1240c4500c112902403003441000500c0410b0141c00d105c1003800d02c3d02c2e040010030500078a241d88030500031581004001020185d030f1010941080c0b00d00007036020234440d0004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 357732706 1250 357731456 357731497
    0x60d110d051b10054009140103050a0f0503041d090f0a0b0c0d0f06090c02060f07021e070e090319180302040203180303070e330d0b06 59
    0x1044800c0159140d5004500d521512040d05822078240c1d05041040c141548036224412440507200e804020030f906003801d070300407900c400c0141641890681b60606414085011b076a060102c00d044203100003890355000c1854080800c03440e0004480d03036032040059a2400e6507607a500ca0f409601c030500110600124014004809001c0200d000d080c4403c50240228040c180c94030000488004c0500000840000d58007488958a52140f882c041440c42c0400c5020740710340c0c4d02030082c0001002c06001d4840c000100301140d1345842014420900d65000340202c607040011410020f0010007800094032401030040f40800e10103840c14030039001c000085854000c440d032501c250f0030315810010b060103c0c00440061070b15103400305400381d0b50103960260b40c1c2d46400880e0b0300b0782c0c0c5000300107064900007c418841e0300c40e803000b00202c03070700e40450b001c05031010824010114805066480c000f00500c51000c06007100b103000151001302c0c92118005211441840481c00c55444140900349034540d5586 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 357733812 1106 357732706 357732733
    0x1201270c0b2104060b0112050f0705090f030f0a03020714060d0207050f01140603010c08013803010905010f12051f0b040e01020a0e1503060d110d05 65
    0x515440c1d8903003400d0510050034580002c5001a21110a12402c800b040c02614001c5003520280c907120b84a01cac10a035080e0340034485054001c000e905199105a40c01d212151600c08064082c02d50150203281c028248100340d003250903114241003010042d61076804c1619049100c0030030040e941d031440e081161600090407824006582854040500d0b08a118802ca0042400340e00a0003040003003035090360182424000e074050008045e101e00340340f442c0d004803007040c080790210001c40711b1039805000020341d00c00d800101c4450b44a4004000c11182841844000d00000008040e684c60b10b60b100d54480c5454601e1104a8440c080441c52105407540a0340b0012030040040060780d032550310b054081e400c2151140040392459484e001c4605104010419100b0107180c007030300d540c1e140010040c006441c1c02066405c80b4080c0c403170141b2600c8100710710107424081ca0080450a05030302 = true := by decide +kernel

theorem cover : BRFrame.Cov 357553956 357733812 := by
  have h0 := BRFrame.cov_init 357553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 357553956 ≤ n) (h2 : n < 357733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
