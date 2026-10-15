-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4324
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:15:20.346626+00:00
-- url     : https://prove2.me/submissions/e25137f2-6672-451d-b446-cb2dec508625

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 777517985 ≤ n < 777697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 777519235 1250 777517985 777517991
    0x90306010b0304080f030a05090f160314210a1e05040b030402040f06080a031d030a080c0f030f0d051303120c0c02040c08090601172a0d0302101409060604 68
    0xe50500303908501c1144040008145c0010411803c1350403503001c01d0140786000d04613902c01c00b811010947d6841d455040800c101c1100381c00f00b0005a040c1040d0f41080b1100c01a510000c0f000310803c140c61205070100e041c60500855681010342e803000311090011300c80b00c180545004107020240540c4180c1c0201581804000000f07010f5455940007039020840d09a4200042540e03000520381b50020001e040740010350b04040250186020300391058181c2e4018083c1015a03810781c2e030071602c1e9200480e030301414055600c581c01014414000b4020501105511540d034280d07000450085680047c420f414011380c5001d24030200b40d00002c914500200068000358003c0c0c110b03801d83d00c07a40c40b02c070001c1d4441c1c10440440020fa41c044411401503481008485499896403122440e1024403803c0010650160013a82204401c0207030001c902203002c4201601c020450001c41c1c13041c02c210f8026400359110b840350741781c06940c9205140c07000c41c403442c040080d801c021702d62940715000501f40071320540e2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 777520485 1250 777519235 777519241
    0x12150613020712020c04240611070324050a05160e0609040216020f120c0d2a17030c10050702151e06041e050903310605090306010b03 59
    0x158590444030450f4100c071466034000d04108000b9980e8000444560042d41400c13000e2501000000d5007102c000d458004100215080c1942100c039110940740c280903030b109486c40000811031604103150024402e0082842d5681d41c9115a4155a00500000101d600c0d0600304000c88500e0010603800c26501e01e407680058001e003000424501401c80820741c4544000b421084d01c0c114488090505842603484040c10b240400801400e01241c9200c1115508092039208071460070020703010030a485076260000039004c444030b803040003000403d4000c070651304440501c6000c41a171034025009821600031454403284a52082c0c0352408140d1520f0f8050b120801300305640d000303000d00c041005207003425818919140349245a40004070540c3c00103400c1c07400104895040074041d03850400134003002e010714814891590001004e0052034440c2c5408180410200032207242d12045411008400c215414101e10f40309030712007401d581c0008144402009150002d0701c02240441c116811069800c2e00ca40d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 777521735 1250 777520485 777520519
    0x206180616210e010c03020403051002071a0f060906150409230c0a0806030c0604050f030a05161a07030906140903031b100e0304170a0503030106030902121506 70
    0x240240d100c454008008100364035080b4020350003001d00c00070410007800a80702400741941288114040544160001a0503801011050f001850704a1017019200e0108032034146050a040040d01c003020700403e5041840250702d0110342c91600844205c2d6402099220300503041c460380708911617030501c140c035620421044041914402d4401c851100d44000600d4242d40110481c1d201d0810000400c4490000c43d0880c00d000801441c40b0030302800561400c1d003001c04008100014440c1541d02d403290019181c0001e005019240b11031004281008400d400c001c4d174800d0a64103070108200303021060001c034020940c00481101114030750b050480009a49503072071a5588120309110740c0510000807015806014034413041c030002104010f0f90541c520031820201a0344414100d00c40701d0340284424056a14919200c070711601c500000c541011840381d0350b01d41190800d0f4481004a9541c003402015428014050041c88540b40d01805101da140782da042400c8c200a81020b00415040340c41141c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 777522985 1250 777521735 777521747
    0x150f1f11150c0c070603050f01093201140f0607060905070b071a06030d021f02040e04060902100c0b15130213060e040207030c1203060b070807030206180616 69
    0x20240200c46101c40c076140001c0445503000603240d070303054414440c0000f02c051007481024002d003101d510380c0341c840c0d29002003503002e17000001068003440d01c402d2881c402841c480070104411200c1080c500c503d50324164500f00001107080d690350140c2c1c4d00c03c1c2080e10700d6035020b04480e50305a011000040e51031040c01d110b8604101071700315280501002440d142841910711519003051074444103601903075610424591518030080003c0003590040f411035004449100722030060f070f10f560300010306103581c0e00d2401d2035294042d00c09660b407a0b40c400010055043c155034000308071007141480107000d001130741c034003584020062280c8281c420410070450555100c240e88952000710260541d1629807005490820011512440007ca403030b001d1202d074141460700070354051b290184c40b04150a507150301e69036446010f4503950802c040d0b4450b070200f144100030010b003803880d01865456032520589d213400380c076048010381a0000c40740b43d01c1d000300c01c60704005100d0307501000f0940c0d2048480300d001015914 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 777524235 1250 777522985 777523003
    0x316030803010e1b0409020c0d090e061012090807050d03050f0f1003230f07050105070308061306030506010608070816110f0102031f0f0308030f040c0e150f1f11 71
    0x420311300080010b140c03400c40d0080c18003402c1c10317025684000421181602d681b4401c0c85500412a03444002a4003843c01d160203c00400b028205000304003c1d00202004031050740c0404c540201d40032031b225081c041c040001000c1c40c20142402c1204c0e041044000710110700040a440c60080040005000c82c0b00b000c403030b0b2009507400402e02045849803010004500b0030008601c1192040d1482c1010003c03000a040044840685880b4074001d800d0700c007150490780040059400610741c8040e801c450601d032180c0e4cc0118040c401a024079410008001c0040c80f028080108024900043c403d1b144402191000304e60424204114000d040c858030906100382959090306075480841000720540c0410120042030041c02c400c26440d940391003010119041034000a00214014000500c8010b01d40707104a1b0024011080102152b640d00207051000e40c040314050101c0340c1b0b40080c0031590034441e082140c106400c60346038086012981060060b5042c0d0211041004842c00a2032900c0c01e05000d0520 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 777525485 1250 777524235 777524281
    0x3010b0705010917073315150305040302160b04060806030115090b10020318010e0a0e0703060e0108190b0711010204240f170c0f0a020c0316030803010e 67
    0x8a1403920740c0c181d03180f5002a4429a01c1450420f611070703900c80b0109620340729100440c4044031b9401034904501c004c01c1456209005641400070205480e41101d20700610f0300825907011078149040d10f402070504c0c500403552008070310700140602c0101415000c0da8180c610328945005c0030b59900c00045e014241da0244184140d5509902164800b21900021000303a8251009111849411030403640e070312921346002d601c00402c2840802a43c8a080d1788a40104010318955000d41c43d9400a028480c0c02c1c1e0b01440466036402082003c40440007075a1300404800000e0720111003800307456613404088242c0180703084a80000148000d010b54580008040e011008540700c0d900c03042c516400a0080e00c08481c512085c0400341d01d154403805441040d404195510000c265440e03540d981d0400d0060040e00c000c90052200d0a449409640640f0f0808199070040c9520b030306007030905081100d44041280901a8503000b88041414901103034110381a9521078800c0d07a4842d4902d10605520703003d000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 777526735 1250 777525485 777525503
    0x31050901050a0b09071b032f060601210203060409080f1207080108060a2012010e0109020c03120c21040b0a020301062001020408060702070911090a12021906020d12020f03010b07050109 81
    0x3407080d054a198400c8e04d600784c541118602c3d01d8407070054403089e091501159030180000f00162034041d0301d401941d040703840a070000c40d17010710a41e20f4118582101031035a1030b031030f8081980204a13003190300e4a90004042d00304103085504140c0701c0ea440313a8000303000086071342e10b030460400100600120b0650324100c1880b0325031215403048032010828421301c24507800c1c503140030010507010b0300341c4220740080040c41f004500c0d00e141c50542d401c1140004000300362800e0140206100141020200e001441c84100c85c94a1840d040c030b0100c0e2040c1c00a490400309a01c140010300c5180d410188455002c400d400101d08076000f94410540a032040e9081141c650056070305100d5000d8001480c0c4080e1080050148510f4017231030300f00c1b507281c09501c510720350111110004010441d030000c101d400d0907001406404e1529080f252500c40691145e0004005a10859002280c0c5030300028100012800740820740c600140e42004c6026800180240081c49a00064003404c1000c00d6010070240c59001e500c2e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 777527985 1250 777526735 777526787
    0xb06010212030907170105090c01081e01140418030207092004091b020d0e100c0f0b0115020a02032d070e16020c31050901050a0b09071b03 61
    0x1c3d501e49520703114000000746915111030802c00107001b991b1051606030001d00c2d00050843c01142d8500c0064500403100310304105800328507a103060818040c00300b03032081d40d110702400c406000841d05511103503140400b503d00100c000035400310b02101107804016000c01c001e00b201c1e4854001451000744040216000180006c480d100790301700768500400c0c503403000b10000e04803034141d031281050b0320104005007242100c04c06901d0700070000a0040c09524103506800456a1031500380b50301b5800a440072400013004010142c40c4540011040d8482d1026210311181940425600c1c50400004c2c080c00207130180401d00765507050398000403051004100c071002540d503c0c00c05c90034003058890b050800c803000d1406050500000b00d5150b80100030b804104121402e482110745840d0360f451440c4540c10001125041ca08203020342c1d0b0090003d0800000c0c903090404082d0206c4401040b000d0007241040100720800303400005081440910501440d181e10b001c0ca4100d0703260340800c0c803503c1d11415610755 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 777529235 1250 777527985 777528001
    0x10905040f0f18030e0303040e070f050405060c0a0b100f09090f1b030b0a0c170603100c02100e0c03120a0302070f0f0c060e0f01050708040509010e100509040f0b0601021203 76
    0xc03070003403c0d0080d1035a82c0345200980c00e06d9128425800f40540c0105000045009035104c3d100d606420241031610078106070326040043c1080d40509a07520086c0d12002c103190074000d11350441500500110340c0e400046140c4403421490b51010b205203200036aa50307401030144202090300a610326405511210040c80e4103054040c2c56110303010645a1000303220001d000490503215643e210341c3c0340d4035007842c0b401101d1440000480000c1070103030075025188102c2e43c100d0090080c1e00c14808540c01070700f0b90340e01001034501260101072031a04c00b0ba00141c4c56100d50f803800301f03050301d03810000e020f40e590b109503485d000d4010340300e02e21000340a092051440d8050240d81c1c1300c1c00c1c0c50144200b0540300000d9850030f00700c0d01c1c81c0e42c0010035a80282410017000856001c0c00003400c0e0390380300e0307080a810b10780c3d90000600b40c017000f40c0c04074000820082c10046400d507503440c2940980000c81d00d142440c145511070301041c0106100042c181d04824010031950381c02082404586916460403a0b0b0300d1406e011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 777530485 1250 777529235 777529271
    0xc060108070909020901090504020f090709050102100b060717090d12030e0601080d0c020a080303010e0702101b21060b2511040207150515011d010905040f0f 69
    0x11030011540603045001c075801c002401820340d0703e41c0080440006034241a405002030001a008070b0380700c3d00ba500b868107540c88130a20184220442d464001e080c5103000300281c104a00300c101c520701d59240040042d11356598100361000327035402591814458011030b800480d540303c1c8000a590000b544500708080142c4d901c0e107030b501900c0c1950184600304111082c03d0380c2c3c1500780110700c4030307401200785501424407942c11403481c140028400c8c50342950300c09405055502c00c0e08074007a01642c1004002184c3c0d01040010900e0894040c200b01901c40902548481c1a011122208000038601c00c61082510003048200f00d0000100821440755280240407999015a00100041c0303114050715070f9040e0480410840c00d504070f800800f003024041c0030080290300150040314641810100f84240d883c031445034034490500740d001c1c880e040340c50a00240183c00c034582a203002e80141d10002d86103991145e00f0030104d4501340d40110300071014407040310213000500304200c0383d9440c11840d20345800d4225 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 777531735 1250 777530485 777530489
    0x40f03081801030203150402030606070f0c0e0903040311131407020607090b04050d06020a18030302060406060b040503031614031c0c0507030f0507030c08160b06010302031306110904020c0601 84
    0x8050a88040040015800d0340001c4851681d9034000e00c886d01c00c0f5081c80d80045602c400c00604140c5080c0160b03070340d14401d220001c4291500c410802c01408a040e02c5c2c03003d603821284100013941402c1c42c582e80c000c0d0105003c1c1d107041c01500b91004801c1c60341002e4002125040808115500601e4461402942c8441c101c3d040400180000000910f83c0501d400712016101d0140c2840400552900c1e010b000c0d41c4020f04240c2001901e000091801d0f05440d0311134041c510a82c003032703d124105030a00d0015640c1d02d82010f07500701400c000800655a0000882e81404207007898020700c5c9425080c03c1002c40f500040c003040500000a012008021ba5021000c0341d8544d00010050101e034164126000d004140009003c00d00e607400c0002c3e400d00820250440310311a00d4422a110680e80e107605e0182c104c100c0c00060490403e40b00002c001c106201594800c0b000e1030f0443c207500d041900001c20071030b18200900310607694041c0503034981d040c10403201020006401555601c2c034400005036110024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 777532985 1250 777531735 777531757
    0x303050f0705090d020f0f04050103080a02061e060909160f0303090b131a07020a0608070305240111030405090c07260706020906120a020c15010b1905040f0308 70
    0x203100010304990007201030b101041d10180114007000e080380c0c01c3c0240c0e5a800d1902c01e501c0100d4880c03180d02941c0b80d000d51400b8500c180c6400361604565400030b031400300c004c0e000c030034048608101607100300100c0c402150302c10801ca403410010f4840b14081e42c10b16840c0107542c8010351075804089022400302410750201c91081d500c1c2c0724801d0b40c0e650560300d2070007550703800301d40901499000c00150605844c0d8408921041041501d00b00c105c0e40018071032010355000201048c011030030030150b546c15215450380706560b201e51710039a2000400c1c0d0361a080b42d4035866414070a4407111344900030030410545007e40710241070b10314a42081600040107030400c034400c40301c48026681c03003a03808010024100c44044008046401d182203942e4135000b03904020803243d0040e40500100095860001040d030141402c50350050760b400404070018145001c103130a40310924035181c010800d2030135842c201c0305c0d441d40341e902e9003056811078901110b042c881e55001e4410203840c00404414040034a00419603c245 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 777534235 1250 777532985 777533011
    0x150106090501080c030a090201170108010501030b0108161502250305061b0d180f14100b1302031003080c010f050114010f080c0913090c0b0906191b030305 68
    0x166000450b0f032000e04907070280740160140301290004081e034024010b4184141450003525a05c443c1d01d07800701109a00501082c1c0d1284010400c0c00b9661800034050002000503111046500c03035848131251251056070400c003042c942c0340c07961a200b40020390200c0054003050140d921201d030394403901c055502064459003e03000101d402040708070b00f0786805083c20b5001a041c10501c08281d030040500c00100741e006070a40801070002440605070305076103445071000e48926100841101d1070190801c089a104c54904070f9800156942e48604010100e00c0110142c7d8030740d0f9181020180c0c1d4629403000f0f110982c04219030000c1302c0e06403c03a0504c0e80803001d041155a0360340c59a44205000c03442550301180f100d8005680d000d1140e00c10a90220700003410500d8a1070003004200c408049800c0c100b1459904d0f5494402c100c03c4191040050000341104e82c244103100d4000741480c0314801c1442001000002c080c4981030140c0804642c1c815080000749a00e006d034100603024040490305080e071044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 777535485 1250 777534235 777534239
    0x41a06120a1e0e0d03140f090a0b01080f0d0503060a1403010f0507022a0d080a11030f070201080c39030a08040204150303080c0c0f1b100507050c101115010609 70
    0x300c13a11401c4211b0024500c07110701500c031800c00804005010700b18215138098400a03802040c0105003c900030316070800100135140340207030043c0c2810b2058443c0000c0110420031b0003c0ca0703955500c1c80d000d42c2c03104034403103a040c0f05000000b8014010070f085040f4207130400040000c040d40104840c000e500c8050213820024400f80c0821f10542e00c00313000954403a00b01041031002c1074180300600408802d030704203407c10b41480c000d82855600080c4842e6903000c0300041c80021540d103e203000d5000480301521605226103000107151400322144100540d40c41b03901d03061444100c04505038040848001600c2d52254041001048140111401e0303010fa41000c041c50b0b803210140e680001141c0d0159104681521000700a001d242d1010310101e149110700703809201c007030109200340c80300101c01c880e060451006040501001e00303181c06418051080510420000ca4804034400500d01c0741181e1010402450841c1518403103000c500c1c001d140d103e8010340c03003007810040f0301305416201c0d0342c1c50364040c00d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 777536735 1250 777535485 777535487
    0x1060e042907022109032d03030108060105040207081c15050f0f04020a020106181b09150309031b060b1201020705071e0e0403030b041a06120a1e0e0d 66
    0x141d0546a000040e03100e40300002c2d141880301180d12103000703e058414942035225000074544240784400040c94030501c3c1032600381083c01d0304500c0f010b48080340130314250f6141c491102d4840750140305050140350001f4941c005c0002c281c040f08c44440141440380000e503003502854005001111000e900c00062103008125403900062800c0f88440003412818075003c0d0005000c0a500107403a024103542d2580000b00d440211060300c050805d054680000f18410085140034842a40600e94801c2c81030034a4148030030014550141c080d9025410701050001803450708595281c2d0110b02c401c1202c00014181d010054190441941042c0440d505081c04480022040c00c0b8480c001c0f004006601c031360740030024107621a41070604010101c8034104116642c4555240d00032048404a000907540c0056040c14a85441520340f240a185101030040744a800858500e21034184100c1000500000084a0300310395040400002c3c100341c100c0c900120100240000341003001e0402440d40a01d40502600d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 777537985 1250 777536735 777536813
    0x1908130e0916232715040b010f050f25060c02010b010903020904050c03030c150108030f030a0f090c0b09030721030503091501030f11030f03030c0c01060e04 69
    0x76814842044008100f030440044544061103140354200d80452050340e01d050000032000504180000540044d00d001c49601e010052241600d51199180040c283c0c01641c2c445126801c412141c02d01c01d036102c04410100610b801401010ba9007640410f600840e0440b40c00d4101c02101d01c100024010b4dd002c9001c00d07400d985500302074a0018401c80c00c10409458071104041d0045d01a90a4910700c0b8001170100c2c2c196801030785004600c2d03010782c503d881800c240100d41d600510800010b541080d945001c28803075071101600e0b1150b00341e00c0d0f031660411030405600000e43d05a0140c084032845a807141401c085030400e80c80180300c0d02500c54005071103110300125103c110107944035144d41c02410340d0169607035003019285842501c500c0b1000c0c11450401c0d440c0d24081e44c01104140341c0d4801030310703048155152800e2480e00941108180e144900d100100baa9000340d10018406e440b168140e51241c010301c8241d2020259131001c40521060224609460405088030080c10300400d616000000f00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 777539235 1250 777537985 777537989
    0x3020c2205190c0f02120d060806151003050c09010f03140f09010c21090f1403030604180f140a020604090c0816080109050a0204091b02010e0c031908130e0916 70
    0x580c22120f1100d10080784080101f294000c00e51000586548455807645030940c21a80301c860600c02c11b0b0344016034601080c1da091500300a240500c0305207082001c042e294040c20604606010522407204075442c01307030300481c0403a11918510b004a03d0300d401c401280c5541640e54003a01c0d46089482001248641110014400f000303121641e10b138a03207001c5000409036240c0c01d490380700c040141c4000241030b1100340a08101908025901ea0503c0b40800c01100c0c0510240314122820300400000a45c010341d404038590b80190030700c2c00354000710308110300300380400800950040c00041c01103420100c1d40c1c4800030000e000d41d070350bc605a071545442c218003480e0f030080c6000305503003100402c0301101315080b0036031144141c100541010360342d46134001a1a0380c03031101e405140304039000c412201e40c2446510351324241040207104c2e000d001d1b40429111720071402d03112002c481030740c01003041c040c8501c00c4541e40c10b082590f0000d901d80d6411601e10694040d10310b4481030049500d5114100044c50718202 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 777540485 1250 777539235 777539237
    0x60d020a030f051f020a030510051e0a181b081312020118061a090c0717251412040506090a050a06020705090c0703020c2205190c0f 58
    0x1211815038645082d0700360508402c80d10303031248100f008614540400c00c40e074030070814100581c0712600d004024007a03441c020411803190803602c00c03c00c03040ea54003601c94404800301100e1b405203101c200105401420070340003005447c16020880c1d00100d0580d0201b10801c07801c110320210540401002ca841c29010384200560141644492021aa00c9a24403401d00124000054090542c60094403c04900501600c0e802d503500a0602c07114140348208104c1801250070320182d1920701c034900c07418000c1030005018891aa060400380402a6040f42c01c4120709060b007662a258400c1c0d43c4201e4120040b0459003804020525030060700d000818000003099a50001d0905003030904bc0f11154010b6100c0e141d10950714480011140c030b452003c20043c1c1525070151407001d0800040c45854540504554401d0904000c070f800400d90202e804012298100c5210003e00f00621031451100351300c0010094142c544410b00c14840e510744c2d419104244024001e010b244101001551680e80c0c6040f071038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 777541735 1250 777540485 777540499
    0xa050d0915060f14060304030e13061a070302010c080103081905130f030c060e0108070e010e040609020a0201151d18030d05040b06010e03060708181c140408100b0609030f060609060d02 81
    0x15640f40340c1950403844912b16a8400a0010740d44c1d840c0044140310015501521880005d100c800e040d828014895918028180304410b03500d03568600700d652140c0902036090301c10309103408600750311440440d0b600010b41c40004020340c1c0c86e401c40e1603100045100413101001411800501e0038016100941d00017416150409140c0e103081c402d4070100030003116241040350030514030392180c2d12072203804040d000304030380107031074150400c4d000c2d003100c3c000e44564062400f001c6042019051461154411740c0d0706c0c1e03e91000b1601c54500401d64121701c04201100c1c1d0102045101480e0300c241e100d144554007a148418a686419005644c0440c925007010781503005480041d00250050b1000364001d0100503034141048441032078241031a150018110fa1201c0d81c44c2c0152025501c20014680e58542c0f400c014605864547c0a5540b4a0009046061980ca0701020443c6036190402c0e034003881000b5061f41e203107420078101941c44039406c480e0603106400d071310003264407400c140d02c0d128001c070390146c010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 777542985 1250 777541735 777541757
    0x30809010f14030a0b0411070b0a06170714010c0c0602030903150402060d09211106010b2703010212040b10090507170414070e0910020a050d0915060f1406030403 71
    0x140003410403914500d80081e01e4a0301c01901f020000020150640107020340da909040002841095808550103081915030140d00d0106c00c0c200401e061084903c02400c2d034048200890040c0c50004e0140c00103440c25103403110000701c2940200040014213030440964001c070101c0003071142c000c407084e42c010303400100c2489a400e200c0c61607401801501c2c080c41030001c450102142c0c8a5201d01e40c080c0200c0020807089007507051070b10400c41135014001f00031810b0305154000b4811441440c112403a03803001901d4020301101a282903044410b101c442c1400c121051400d41030034100d682040d660f04440c2c043d50440002c603410380d17100360350144a207540e800011014010142120700c1c07020b0001d8030381c180081c24031990158200b00d01c074000d1251300d02042891800592981c00d00e441c0328030001c06540108000400607038003500701d4079000301170302c40000d4602c40307400c241c41c801e200c020081041c185840e0020809030705104111040369000111100c0c446800c4052045500080c0c0700240418860020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 777544235 1250 777542985 777543001
    0xa0b0c070f180f1514040f11030412050d0c030b1216060e0a0b071a0c0307200f100b130b0d06020325050d06051c02060a0e0406030809010f1403 63
    0x1004000f00d9850002c1340c10b9504040c0f562000000e070b4001c0107000741480e4403c8a0741801e00805054281003c001c10044030003c40010452100400041c580d07625940500015030252003641c032912410a0304108030300744044d0250013011510b9415200705240320325601b104400145071040340c02000401041c0d03602e00f0000745c841842c0300c6100c984c000d01960340821190400e030080c0040a000f41c00d402d0894001714501940a64007401ca42c2c4011003c004000a00750008202d1f40350b4420390394281000b0520030a0141040c000382c0322003189004a441010f03104040d600300c0c0e241c030001110042c01482c6240340740421600050b5172035400a8440c1588008a07400d0347c051a880410380c1c1860f10341c1c168261030004500c0c400b5917042c1c0428030100b0310308140310951281c3d001802003500c0004200f100a0107900c256042840c0c0240704020014a0607a1a445410000d10305c5201410034800b5585030325000c00036411090b00d40380090b1b95000408000c0d881031900d00341309855400c0d918915160a05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 777545485 1250 777544235 777544241
    0x30406140417130b132607060c0303020702031e060a200702010216080d0914130905010e01112215030b180a0912050405031513020a0b0c070f18 63
    0x14114208540d45540081d400344c0c0900281012000c4d016000b00311800c05429a52205824219005110010380c40c2007051b000007582d10141e0359a030410400400300c901d81100688038950b8029010b000e500611740030f200034001840450b20101c0196201d56540003007030700490b000c61140000071039403002c0200a4800180c0189985070040c415540040c4c0b8111441c00d50810b15449034a40d680814800c0d030703010383d02c20041c1000e400392070924801b900001d07001070007035000d46100f41201c0b551443c2d2581040025401403000c100040000e01101a2200d03d480d082c2d003002c1c2c02507040300c103000c4200c18800260703032030b00e4152a600705a50080c040a40c100f20020050503007595000484441e180070200030703a00d03500e841a20752140c049448110361800000c0e00c21007405110600c6014841401255404a08100c8802800028049583c4c3d024403e840c0c00c0500440030703401020380e2001103000000f400007003128459100807a44000e81e0b0703031204402c420a6110381520103c012076901d0b0581c0b0320360 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 777546735 1250 777545485 777545497
    0x70902130911040f0b0c010c05040b0301030605061f0906030b1903080a02010f1802030f0c09072a060b21030403030c05010b13060609121703040f080f030406140417 72
    0x402c225080546540c490300007107403507030422000b07a04007081280c4007140900401d40076060f41d01c1c010307040614099441d040d6000c10700004041136150030008804d5125503031b03e400d41c074101900800a45405160107462000e0500404001138100304040707403141000b50590199107007003240b003000e00e0325540381d4004580290840c40110b548480820000615900410244240d403600d0852455402d2041501c2d00601d8588001160003519080419035a80010503500c05103a00300104441c0c0002015034000c0c91035941c0055907212322070b0340c3c0240083c40d44080c0002d88186c91454a103200484072080340d000c0070722500c0803640300b04010710001e40326000d080c201d40c1c4908000720301c10f0f045034001201041c0302680300c4007172035070350700c0070000d01d071380800a28000c0804400721410407240e81c961024003000f1001c03030078040c280040400c0420641542c034201c820380005146848403609202c100b0a9401034a0950300141400012132032404010301c618015948421200c413060000080004550041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 777547985 1250 777546735 777546761
    0x1e0307080702030312011e05240a03020405030609160e090a080904020712081b131406040e01060c1b0e3601050915010506041413020706020a020709021309 68
    0x1805884d11030086002102d01921200001500700b094618000b10340080e16405203100307280d0742c03000ba100b41c50499409c0140c1c03c80030781d00540e05c03c20004141d020b4401c0341c0c0110382601c02c1c40104141801c0c0824051600d400b407420341039140d541d8451089403018203813801c91003a000071101100050b0700000074049844003400150520ba02170710b13480b20030f2040c0e04440d400319010f00c0410070030401007400701c8500d03140405014200030658102c0095441140200c080070344080b490f0541507964101a03c006103880d0401c050035603120388004217400f049100444440d00341c00d44020b5107010459030501600c4a0546440095803184c2940344001c1032403a014000c050800310032116901e02c400d00480c1c10b0400d400110309410500c184902e4184645d10f544440052200103200720365806c4101c0d030454110601907659602110006a000e2071500c100c1181d0520000d002010460560043c1050174401c1e0240c8a885545800c007006034807a01d00311801c0b500c003a54080c030081600d54840c0c4075550038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 777549235 1250 777547985 777547987
    0x309210601140303040b160c033e1909020406020a0c06021507030f0b040513021309030806010c03030f060909020f090f060d050f0d02011b09050d03080601230301081e03070807020303 80
    0x81501d41c0c40402045420a8480c1c1280e02183c80303c858011640741c0c00104041c03900ad0403d0340884450404e1204003038503034407031007602840680a280170011507029160070f040031503549956607000703940c9401480089404c48441c101c0010745038004201c164920340d90100400440e41c40003001c500030520b0654681015a550856034025121403103103c2c45246050400b110007600c9004000160101c0d041d4512824201900040040c0d4072200c4103402660a0030302c1082d003d150315056019242100000030b07504d10307002001600d1409600f0100c0000d00a40d10038010010354014820103403c1220718501d8103007000042001418118240c520403809502503e5500d00a161520704148140c40c0d8400140e440f10380c143d46140030689180f1a011450620080203445e0a001c2880701c010400081c051000005c00201d0503405102c4441c03040343e9203420f07410740a40c000c030704000c50b0300280a4603c4501c200c00007550200303581020099244d071040011f50034552260340d01d00e019030000c1c10403601808 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 777550485 1250 777549235 777549277
    0x6050904021b010c080703111c110408150a0e06101a070c0b030609010503071a090406120c06020d0c051f0b061204060f020a1b02030309210601140303040b 68
    0xa00c11071001d030700659104c40e11410004402070075101e02400c2080000303000c101040c240100502d14991203c011000400c4d915a41089440e0900bd0b0354400101405a40b0311009a484a0b1075964864442c00c0c1041151402ca040c0065858500b103500c0c04500341012820301440080184802400c1c501d581d9252400e2a1aa2a81c421a081e0f0b842904240808000d2050700c0c41d0840310140900f00581c01030049524240d0f088921290500d45200c15000008a0040a858681100016003a10031040100200720310f0006030f250028030503480140121003404c5541d500c00e411044000d50130034010100040c501c030040141280710140c0300d204542d18241c0c22801d80f10a00034142000000480780000d02c0c060078036400303840c030a60318128860302c1000342a5203190084e40b8541041d550710203041d441042440440d245202d00080e03103910207910080c4c000300210401d1000c01000000d41a100541d03a94007030b641d035070b5030707440559640758206200600c01901480064000380038000100c440e451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 777551735 1250 777550485 777550537
    0xf21010e0601081032030f03070b0c09090411120c06040b03100509090d1b0206030a0e01060911210105010903150f090803070f09080c060a0512090a0c0f0605090402 72
    0x14178410b41141c2c103404104100c000b00008a0584a15074054029148900088100a451303204e4101c0040011114102180001c0d42c20015a400e81c03c02030310300721090805003840d18000c5200000380c1d20820300203002c8000c0d0b0401151040401001404490625050090700c400540004001c1d0204281c40f810001300c50740d465420602441d085800352906042001b0020508041328050103800160340721001c2c0145c03a071400322540000c0c07a890000761819a54801405000c0503441404954201042c0100050b0f40c14010000383c403000701c008110350301c0da90362304288080900c24580440c16440702000400d0b00d51800c032203034849800000030054070800d1a1022181d201105840140b404420000701c583c10215910304484a4200210a81e103080c101c940d89a030381941080c01900c011451040090140094a050700d000b20404a0189801100d0640e0b0f80c000c4102600d04414450002828809640c6100240c138515a156403500307280c034040c88042c0d408080380d840402c0340105000840 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 777552985 1250 777551735 777551759
    0xa0626030910050901120e3703030b03010c080112020d2918010b03210f030c0901020d053c120613060810110405060f21010e06010810 59
    0x20081c02e850f02c5407202c1d484800102480450545003800918015580b00c45070300009175221105600d03940380000041040e21080c048503041142e070785000da810b00400406401da0826029050103038003c00c404050f100d0304840b013000030b00c190000f1041600404015007000c0c50501443c900074140070410318003030a69021151601034251a080300c04c0720901040001000f552412203180034000d006031142d00000940318078106000c00c44402c1580c9440903032500c0d4000741e0b06072001c070140407a202d15155100e122154411000680180200c8942915040c0544142c41900b6040d059091400c400f82c80d04100002404440a80c1120380e4070070b40d0719142004004194071404800b15034143d0800d03200b405110007030b004142510764103004081c0084203000036810084000300501242e0380c1032005850301d4a12442c1c00240d0401000982c080080074040002c0c85800941040d9981301c2507995000b022840703080c0542010071480328089a61903110307400da19000f84d079141101d18a259904401d05103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 777554235 1250 777552985 777553009
    0x203070e040302071a030711070902040602071706011a070c0504090f2d0611160b160315142b0201180825030b011d0a06260309 56
    0x40c08503084100401c140d41440044020400948490750150542402500d280402000b42c02000b08000ba0081440000c02105006090003803086540e581c89500c02901c0b14001d0245000c4010400c411000e22500010310328103c4e000c661103002c151829150058881c4d21401054540c51071018021a20b50303034a1003215007041c441d50000c0c0508e040c624011509170505030400f640240540c1c208000241007508680229510031303c0009e41e40001c1a400071a03000703d0b0f040c803195207100c508500c108415001d80c14040c860b40c0c070030101205c4c0ca903a0110155503410720314242c1c07103460078001c001d003950781d4011819116000f0091190000b008280c0c00705001c3d807070302c1c0c083e824000b16158815940c014100380300000850300e01c90074481c00c00309107903a80d6100614600e0400c80078804d0030946e0b0401410800030750307480405da0440d940d6909802d00c02907548800e50354000107174400b040940c4158440d6104550303a4150703200700400113180c104c05c00c145c50812485e25000402c4003814075940c256001c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 777555485 1250 777554235 777554249
    0x1b010e010c030911030a050c1908030d1d0624030309131d0114010618240e01030b010c020603070c0506040f0605060913080304031215080c0102031c090f020307 70
    0x43c0f801503030308100000101d401440c0380a90440109400450400f08640706020700a0350714a100c550700c01d42d401d041034100d41c00400c0314000480c01d8071149005400c007601c0a0300e40001d0248400031000026118001960280c155210b41e2130580c0c40340b00141c407006c50702400102a130b81414a00030200c0c810000f4201c03210211656100b07401705044840001900c0030094400800041608203000f28020006004050900c4150a05065130480901c480c034082c16203a20164450708201441a02d00310446449501007041c4070203144255220340318411601c00140e546035604d5070300707800b4131907554000342031442040600c000c0340d0081002042003c0c01180b0480b41c8002100050501c01c040300e2004e4106489050032100b4000c2c8884865600002290048001c1d03075039484071701e8160392002d40405500105810801d0560f040034411038040d08a480101c1500c440c070141c80d004a0f144e1054078003114594007070355404a00700320903034041e003e518030a040c80038061207142c0000746040d605d540242 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 777556735 1250 777555485 777555491
    0x31608120403120c0e090609060d080a0203120f04020306040b10120302060604060509060d29460915020c060a180803070503060102150c09120f031b010e010c03 70
    0x552194892140d0500c10031039103040740700c421048002611b04940540007520903203ca0000c181c442d41c0b80c0c1015000d0070340c841003895541280740d07000b07901d0780c1080510041580084002907400c4d90a5010f403442543d00901418483d0340d29074a200e542d1b900074000341c20381980c1090100300086103030821440e59000b60010310962500904000a640c544d420060044801c841481141d44607204040c0d0000c1e03208014150a549400070029443d0300c006401400c0c05421041c071011612100750212400300054000381200e40401c02440301443d4185200c0d01c0d59511540d40080f60202c1d8020310005104a4003000107005c0360401209a070001099940b10390480028845144601c0c4501c1c0160018255441c1088146c1c0d00c0340a0b9600008005034107000c40040010b000b60b1080c4440b240c41910041240e903207080c0f0303428081454204402041c080c502c1d1a80442000c000060114014010100110702d0000c240f0f880d8001454440085207076036484100304820790401303005603100e2110641d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 777557985 1250 777556735 777556757
    0x3200406050c061003030905011d0a121a161812030e0a080d020607030902010e03010f0b03100207050717070306050906040c120b0a05060a0f24090602031608120403 72
    0x2403c10202400d8501e410201810400000760008583d00c202c0d0000d003032040300d0000d01480510400e80e001c040640c840e84500b00400c0c8051400d800085950040c4010440f07000000126072800100342c4101c414010001c09010032f5620036901c004400c00e5003014030380c059603103102a440e07059001c01c2c00c8001c00c1480054941c13505213014031800902c0741800401d190300020502948803100948190105500c40389140c00b50390044211003031150703001e402000613a8040c00010001d240d4130020780c0c802d0080100c0802181014020303900c4158002015160380c81c41c0803031405940e40414401051402038840020205020b4817406210b05882c101070241071501c1e182c00c50303100f0141e03084428134820340305650b00401c10586001e41c0c05400707000001016140e100006014030415880094040b01002c0e02003840d0500c2a0800c3c0e2075002400a003030100710604054444d41405d003c0c210040e03001303008004281d00506d41e040e02041c00340c001545425403030050908d524400301c0e4140c01080d003070080c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 777559235 1250 777557985 777558007
    0x30b090706080c04030f1509150903030c0512060409140615030c0405040b0a0e070f030c0302040e070e040f08040f1706090d0914120106030f110102010903050a0320040605 75
    0x50b09501c43c00041d50145032500310b41d40d4000e482001c0384e001d88001002c070f21000c030040a0340c0c804554150031000c0c01c131140181403013100240524110840019041c081e082403a01c1c041c6d01a05d00b01c41c1301d03100c01440c950381e1800340001081c0d00d4200b5140f0751040c0e03007412a000024003105018200b031000701c1e801035120f2410705280c01c200d040d026000c2c1d441c0008010120f0380b912540380d0000c010a102107851003038103104918004803a04640280b2004150020401c00094021802c4038420355060100000e40f135000d07900c444251144803030752a40c0600140002d009042034900c000e00c00c1c0c07107540c01c107034032807101d1500e5060316001400e02c0240b012115080308020071000da40001110000c00c1d140341e451200074100b58551140518101240000754505c4d82c17440401e80550034100000c000e42c0ba5242456840303041804010368210704207003130b001c0300c42d4818011117565903019100d040c98030403d103000300c0c010003014026200d541e00340e6a00c0500c80b0741c618010401807040341d0310b99441e030491400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 777560485 1250 777559235 777559247
    0x301090c0e0f01051008061c021e0f06130303120f050708180d0e0f0409060f021308060403090506090f100216140f060309030d06081b03011404020603070504030b090706 74
    0x41503110399849031784120010361200106a221500f52041100300fa08402c014070082d03d401c000035808596400322082c51410202070000f004012111030100c0c8900c1002c0c002d4078401d5180301080c03844100c20510201c0d009201420514094590000e440302c84066074204481c02502c01500003034000307082c400f50500750400006022521409003c2416041002400300600804d95a001304d040051300f840c41e03a82c690100ea05960006c0080c0030305240400540020b5200340c0068441010250010861110014a00c0c0c803544d4981c99010301c160402c010046e07070390080103610798810220f04d080d0351240c4490b141c2402d100760503002821070180303d40040c4524051600140c80d40e10808203500c04d169120036000d03074a20000e4134000d0b929211101c80d00d0940c841c003464254402d05182c0d001a04100000700303103683c0011102d038460900a2038040500703880c1109250042c000140c030100300941341170302c000c1d0382060f81410036900c0c1c980d4071346e13031088101011140d602d0785030480e070703010440c0c950012 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 777561735 1250 777560485 777560489
    0x1b0a060902090c0c2a03031803070608220215070b100b090906060304020a05120303060907030204260709061d0a1b110c0607080d1a010207050f0301090c0e0f01 70
    0x6010740c0c104413002108903614882d88131112039040501e0101e08600c20100e04100038040d0180940360f8403c0726202e85d1450382a200c8245000b4800c128000070410303c500c108901034803182410004e01800a4900c98181d89040f209a910840c1e003044000c05900c40300c000c0c42c1c22072013008101e1795440d1500021400c03681a51020302c5848081002c00c00d182c0e6000708450b44000200c6803a5240d403100c0c0049404070403240c006a400004496032400038841c000007071481079004855602e00c3c1d6907805800c800341c0c0030354896020b00c0c4001c1803001200c400f20011a10900341c8002c00c80384c0c010b580c0c0c01c0c0d101c00c0e82c20301d5224010110000b00300c01e000a02c0782000c240c0c010410001801503122032100f116105148a0042007008142035643d0285c0754180900b18284200a003180d46074030480c2000f511b260f20010b142680c0d030b440d1a2000c6400c480c0304802c1c10720444141c014000c018580018030500560306006241d040d566111040d00007440c528554000c0d003070340c000000c0149400c58590f81d21410603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 777562985 1250 777561735 777561751
    0x90f070e010e0312031306050c0d150303140a030f110403030215062107032f0906030c010c030201020f07110a06030204050d060b0d0209150102070e0408040b1b0a06090209 75
    0x2c2c007807400503100051405005004c50200035036a5495655400c4008803a540045c4144c0c108003c2c400b0040942002e41042480c40008009450400c00f1024400c2c0c06480010040b03081c0b800307103601c2c0041c3ea4018043d000c1c03480c02c0224a000c13088440800b19503403141c0c0ea044100d8081410300c18140e04000d860704000900100e207500e400c140b40011505440540d4818240005c1c00d01206002c078103100c00070085a002c1c0f200b516000300c0c01481144c02e100020702c43c080c2041d0307068039045460200e1007507006070000303406030200000550044038203941e85201681599020005d00c0c0c01c02802900030400c880c0a150f1408004c00d21a08000c201c605070b030704c4a0f04060040c0028400341c3d50303805000b909d09501800004000a544010500d41c078040303c40a5400444402005616031781070780d030415220401d07400d59506c00d1300c0303043d05070120300d05481c05042100d040c00144031038000d601c000d0a411000500e240017400c9101070365450044149001c4441340d0f1506d21140442c2050344200f40c04c6861 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 777564235 1250 777562985 777562997
    0x1801080c010311040512070e0f010e060f130b010306030c030803010504050c03010e070c02120d0314090a170c07030804090e060a02091f0306050607050f070506031608070e090f070e01 80
    0x2d1000501c1140641c2c021207105811720f01e0b26200118042100d0740c001c00d1216102e000b62714007020f5100d0317464400d1052405003074031000000d09610342120cc00d09045801007804203511161041e03800105a00c0d803065047c955518800b1008c1950004418000c3d44078620503584c2c2d42c100000e200071b40c1d10180c40042c0e414410302c0140701c010345809010741c4c051558036010904060f140005513031807103603401111705030092030104502aa4035822859020514820300000703900d609001c160340c0c04122401070701003482c0503c42000f01001c5401004090002c1c002c90301243c1d200e03100c10510303605c035502030035990b6681c1c0c1c520808500184043c0b40d001d800c810701182020025404a0707410030700f00e052900c818005032900c0030401d000e54804006803001806040d1174807101c1c508548e40b030301c8511074420b583c403503404006403502c0c100b401c991141e02c61072802d15615803250025120b2060140001040c0454012a01030740d44443c00344a104010456058407207086c0300d0000b030040c07600c1c140040d0400074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 777565485 1250 777564235 777564251
    0x31150209100c061103150102121c09060212010b1b07030c030b091c0201020c07050a1a0c0a052b020a261303030804171c1a1801080c0103 60
    0x15507895001107900041c2044010841d02d45009001000a0b40c05608000f2000c0240038444107034004242d1a0300c2c2c00e8085424070346100c00703000c0c1240201d900211400460000306042d0200d02d401036120148141000f505001c5400760040c44c80b1000d8000701e41d0240081002211034004050008488003030002606a0600310344400500580a0001034502c0381e410780414003000b82048958060140043c02c3c450810761207000038007030b61101d00510940e10500801007540d181c0b070162002140c80960722903c4011200325100c0705078111200781200703030180180c4200450400c0c840203c440b41000c041103840c510030400000400d02a041220442d4000d444c040d0016032103e0015070322204510250f4070b0b0341e0440041652a21840310881d21400002c07100200300342d0001c17650740c0900d200c1d421140f06103070300c0680d071105030140c11003104841e1207506000016000c180d1145100700c000c4031005540c402c051000c80c02c8103401501c604a098030040c010000c1030310900c000c2d0700c884000d02c1e06000500d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 777566735 1250 777565485 777565489
    0x2a0c15040b090103050403051207080106030e1209101101020d05011a030f0403052209020307021c020709112119181419030e010905010311030f31150209 67
    0x1005000c0c0b000d040c07551310780108040c140110300313a60b0010440c5100d003160b80352221005000450070700c92030003c00e0130f0290f244900d040216003500c1c1c1c075000b403041c035090903440d00800c04c14951000400c0c003400004111401c001100307000502ca00340d40c0920200c1c641d4942241058002d42c151214445080c05000f403241c0c0080360064190065010310f45147c444e150000d286071800e00500c1c00e40c0c41c28828482c001280030441d0007841c89aa41c940944400c2c8803414001d02d440d0103941281001a040764100b4080c0c1d68459018000a2440740587c07400c084c1c3c42c45a9440ca084850032110b2000c40c1d1000708000c6150a0400c40d050301403801c828800c0041040120041c43c07203039a00180035028003900c2c00c000c0f1000300001e00e060fa61362406a01744546030300700540009205270f801800250341700004035865009010b03601c10b40c8804405103240d691102d44c03500d882d01c6d0142500c41c074401105480c5203103c2d540141c5e9a12156a58140e04d2040c0301458030200080b2148000c1d101b050040c0301c002442d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 777567985 1250 777566735 777566737
    0x1406090334020405150a03050a1217010e09030f041412160504051509040f0b0c070c1e0504020a0908160819050a060c2f030306062a0c15040b 62
    0x1c00d5041d0303400300d2152689044000100641c1c08001c4d00034540b0900042400000941a90039502812622510071400703442269003110300c40c01114040e10f401d0040202a070504c1e05a42d00a880c6000e4038240021104452007980c0f143d8080e241c541c07001410101039141000038030314028800c5c4001c0403602c030301001000b0400b500e4800c80f40f10355131754800181c4c0b921540345c4801c4001001802c102d4980350510304450b071003002190645041d105640010340203071091b01146c229540105040b05264a8512109140c903030b4040300300103030203580000007402c3d2114009007001c400507454264106040500d02850581401a41d0f043c0e00250703107080211220100300a0341d2405882c1c8126100145410043d140a0305004010229890301c03241c541500c1e440100070f008280740b8a4050503611002c015120160b0110558940941042001c1152407a1000060494143e40341144102e1803420040a240c060400702c408856085074661407143d240c40003a0700318030b80304100003d0030b150030701107a6486 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 777569235 1250 777567985 777568087
    0x30c0303063309082a0d03170c031b0904090b040303022508070602091504081c0c030806010f020a0804031208100b0313110607060c08060406030f02090414060903 71
    0x35420038101703040f500c007140001521350034030050300510f0440420702e4018504000c0950741d646001a000114520b40d0f25030702120700030700500b40607065000aa800c2490998400554940d0007070340e800300c0c40d001840184641c1c0c0b140d802a00d0043e282d8580141e480c0300740e20b9503042c010341030b404050201c00140b602002c2c0c03610103410941c010703100d450788070209500c03101c90244181040400300740000d480c0d2000911691500102c01c5102264800c08829209400c0322034000700840c154800040b0554480c007024280d444c5e240c4115000074500c1d4584044984c499041030b1846007105582da4416a003000040303800145130317421640360618040320940f0a01004d89140ca41c0440b0140900900c01954014486030000030081c51741e400c030034542032004142c034642d0840440c0026001a809150030710844040769040507d0a00c9615141c0c200100108001c2049640501c8a03588402d00c0c01c3c10414940302d4841c1c07200541ea908000d6a54659120044072040c01c841e02e8400980000720142c200c2e060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 777570485 1250 777569235 777569263
    0x60e09010e07031805010b0310090201201c080f010f0501081f030804090b010e0609060f0906130f081207120305070c12020a020909060402090103030c030306330908 72
    0x21a0740310444114040d04010b14031944000415010105001c41035028500d6503c04238111100c9500e04107000c0c0640b501d103000a800f00b020080004d4114070040b10310840c107088001941d1a803090780241d041429000094100016191003c02c00c8a568848071a80504101c0740c1c08405540782400007400310500400001c007440000e070540e041c500c0d154038050060340c1e10200c0703d503c403521040e03184010b1424180310b030700041d031008005649007407400403180c401d00f010f808a0b29007c01c40150b404954000e00b10f0070b801c514204088411020801c000300041c0c03c4411100703c0007445e10344100e2612006020040f51114108030440004a81c18240369801e0024107001c10b80c0e41c1d0740c00060300d00e6411820081c100c83d40d49071031031840c04e80c041488010319208880c080d4086c0c82d2001c1d226030350201150000d4104480500500c00700340208000343e204e61081c617010507443d84a940e0310700c4124000303e510702d0415090407a45260b050340d910701102c00c0500d1070708501680c07074000c1d102d682d0829140009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 777571735 1250 777570485 777570509
    0x51c140412033b060411100c1509110109030c1a070206031312020c0102060114060d0501150207061409040b0d05010906061523090102240709120503120a2306030601060e0901 76
    0x411f0460107110a400c28507080940c3c044142100c0310f20001410001000f10744020341415030712001c5d070040d401d034402e5030f41103086440003d00b8454107445501a440d8107850602c004d001c10001689d850005503c212240040038403000d95502d80000d02290401d0410f080d07401c07040fa14000b590380050180d04480094400001888076171002c12000d215200b00d0400303290411002040e1505000310400b24403515030708441c00181e86803400c5840f03101c55078407002466001c00100044e45042d802c403811415000300501a0803c540ea80c0d1803c4540d2600100c0702d290300c0c2c0d801006122010030002c016000c190820031606484100204602c1e1400c000940e003900e4003250790080ea0744200044039664452400f505c01e8201e0041c0c24809075141252040001815034102003145401c0110070381105601400460400c40019422000c0308402005c0e00c490710703507807000341840c0100300b40701060117490b605c5482d900341040c6062606200c01600401c0c00c1c016820151040d80d160303142214115007095000c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 777572985 1250 777571735 777571759
    0xb030f0a0f0807061410030201090b0c061503030c0709090302070617040b250e0a41270c090a0603020c010905010c051c140412033b060411 61
    0xd40c01058079640c2c100f0491441410400a4906c0e1008041540c0c001d03218040400d58a244260061081c048036200b00d0700040081400565180e0300d0752000c0c00020196400c0c48c0303101000038a006480d520820201e916501d18505150701800003501418851910648603c2c20200198103280c020f8001007403581207000081241c8400301c2c0c40105140b02c800143d07038044030400c0050541903444403ca01c0341c41d0352507000030403212903214951400c01800c1ea242d01246540e040420031007240d00844680f01120340011030070340c7c0c0c10a04d2030380c0200880251030b00070403000b1790200c0107100801d4070000c585c04002d40421940c0e00c58050781201c1241ca0003580d030b00c07240169140541000c50006040e5800c1000e007480140c0c028018109004103081030940c3c0c0095408460150b880d01c9110382c03265040f54000c07a02298074090240c0c011516402c0100d18004880751203103681c1280e0042c2495900c422100110421310103401242c40b1056400504a908060702c0e9071120031000f40c2e40030b104082107810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 777574235 1250 777572985 777572993
    0xf250f020603040c03080d09050601080604020a260307080a030b180115140406020303010608090105040b0c090120061608010308030c1b061e181e0705130b030f0a0f0807 74
    0x10135010390b0b480100c280d1104a243d124a024010030b29003100c040c0501c00021503d03841c00200e60b48541d03001041480080d02d00000309482504441e954269448801d00b419440c3c0300c00c20040048911071945103946894024000f0100c8410424082c0318a80c8079030640c241024442c6403506440340d542208030314900141d03090714180800c00c100500150040307000141c0070b4000c0302850407103c01d92501c41003036840e06840b40c22070324102e500600c20455900071409034402c10024140c21072040c144144010395080c4080c070290590007401040354811001c1203803000c03003140141c0c15500b072801c08013107550441e907801141c0c1c00001c24584404102051540d109a040001c40c0e880804a9095034100d040c00182c403840c403c10100c904941c1341070a00451212500d5542008000c0800c2e400381180700f2400034000c410399a024000585072041c18800b1a03030381d032801c00314007590210240c0018031481000506040031031f120500131064010340600f001040094080012039640001c5040d80d5111502d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 777575485 1250 777574235 777574253
    0x503010518250203040306060e0a1d0a110d1a07020c012a020307050a06020124060816030608011121010501020a0807020a12110f100507060b03010b060f250f02060304 73
    0x40081c0040b130900c100021010384460209001c0e000e140d009200c45040cbe40e800704c481c0da21b82d1080c0c107010703800f804060300410711003000400c25542c020102c441c2441643c4030511421103288441e06008485800c0c40040d540400100301020020300348141d640c48042800d4030001c8048006103190081150f03480e045640130720540001e400018403d441c49900e03201d000b4001d01055580f0071140115501ca410b80c055040d4858044400c00d0b541e6102d2603582c1c00c00314601d40c0825641d44241a103d500202d030301034081c01503085050080c940b040e12403074207580100c1207049066038241044404d070014000c2e80d80c081140c1c03651a4029210726560401e500c04141480e006500200e610b005006a90081042031000702c1000c0c8411104409007e01d02d42c1000743c541480d5100c5004514100f00c0f2000290301c54120200a00000700001400700541e000f20742e0b0303540441d10f041e20649001035000940104100c0025a10001c825074103641d80e07160f520355202118015010b4811600800004c00f0421940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 777576735 1250 777575485 777575489
    0xf0503040801050711010e1b10031e2301060207061b0c0e0603010c0e061b070510050306090a0c050d090602160302030c152401120507050301051825020304 68
    0x480200942c1c60240d04c0141001c1449004207515424594010080c120000d10000c500320810000580c00b01003d0800c518803a01c00003071800d26403910111010741c1010390840075504515400814028211821a1400001080701140644094006000701640080e006050f200607007003189200d10007104246402240c840c0050444011550100d198000400e5040c0121415002400240b0804d00700740d6030f40482c0043c054110b242401002591001e48802e03940075901c240640d40a25121004079541500d0b044040001c00e60000900140d400c24090050b07206c955000c04100f442c0401100406078481c84c4c82a100d11529510000c0c180107040c2e04654410420070090503110fa10740c6030181d103c0d040304480c2040c45c05030300b0100e5070b4280521200e45c890700c0407164032050080703100c840b09420385001006a0400880b1034030a54056024440d003405042e0075250350391070350303d05020800c450280075003080c601050f1000b4001c104007480419070318a2032a5a181810b030b08601c038106c0c5180255 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 777577985 1250 777576735 777576749
    0x3010b03011202120601140108180c0609010306120b040309050618090c0408010507020a0201090902120c07030203070803010b12180606090402030c0d0b04060e0c01050a03020702220219030c0c0f050304 88
    0xd00000d82140b01f8540810441c0b802c0c3c0f04d03d215a07460900408100f01c8111582c0b0041d0010710014000b07103800001441010030504000a00f00e40f204004506450205011100001c00744207000606401c50904001803908441003860202e140146c10302860281d28440e018141c810007042034011800c05035000740140100804c810700e44040b000b941d0b41c1d00070005902051a181d000302d010070480c001c440d50840c400c80f513002e0303e4840b14041152584407004c240e00710702081c803040c00001c6819004600812500b840385454420024500350703030034000b8064000c42c00d040000c40b006801c01080c040d901c08000c4860400310ba03100e0001c84c0c1401076403542d050784103900d04010420002c40c140c1e00d900580c0202c108122814800380016510160308101a020035007c1c018480d200d0300c01c0d001401701520141640804803206a042c0d5144a265441c0b40406500032428901a8103043c5400d4001180c51070203000e1405006006010001c807130802500a41c0701258050a000007001110001c00b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 777579235 1250 777577985 777577993
    0x120605060f04020c060417032403010906021612050313060914060702011a0a0b340c03060b040c080c0901020f0a050c01080114090c0a020109050a08090a090203010b0301120212 77
    0x5130080d0710784600e402c450455501124502a045c0702248070181c83c41461118203400c0401e2483d0350103d03c1c41018800c4644c0b564170f030b0240400086560000d428032090b440f0880300880f450f45007903c640d602c00311303661041002c10f00401c0085100c0c8182042a96080080054141e19600303103003400c0d040b40c10342d8015901c00d900511034016415031050902c01e00c80410117021049000030080d82c075040e449144141c24040c415148030f0f410051820710411003915490751440810011074070002d05c080000e44034181000d40400612034a802003201e20301049400300910001c600c005000c00c44040e0901810603808204c18640e64020807031a0b400004050440f4034082036407800c680e5440c2109009400169071100010f8480d002600c0d030640110009c14485265441c61421a801d412a40000003159254580c8401140080c81940d4003540120280c0c0d9076951024284105440e0992140e0f00ca0752040004008526404080d01d05603008041402d00781856800016a5100c184030510343c9409 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 777580485 1250 777579235 777579247
    0x9030f12020903010e16050607020f0118030f11010809060603071503140a09060b09010e07030203040c0b07050a2121110301090e010c0c0f2310061707120605060f0402 73
    0x41c0010f2940304001004070091b420b54450013400301e180075119001350800880082480e680d03028814180f6585076540c42c15241a07035075101c9060341e400b02c0c0415110101e00c0f1443e843c03256031000e510359100034007100a000d03904001000c00d030703136807000d118034580b481965880c24545e0b4440e42101086601c07550181000381010031043d4020190700c0001c40740c4514040c6014a20305041d81054120340040005000307a0f540d0b840140c010390720040080b0f90664101e100801d401d040e400c0540b01c243cac0100c00601a1010b140b42a040e001fa1480e60140700c9006600c4021013507a0044041403020701c00140100700302001c020a4000e014007501c1d100c6c407600d021001190b04541c0f41e1212140f6800c5400900c24041e10030300980c2e0300400d112004e010709a00f19412004600c00c0203828a00c10704482c064a01601d40e00005030402e031500c40e60310411a203a5008000d0341008502c2581d900d0321420180c11128a4982c0b1040c1004221070024140d94443c4000b80c03c503a1014414924400042e20566540f1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 777581735 1250 777580485 777580511
    0xb0408010203061806030303010303031e0e100c030e0c061309090f061802060d1e0c030c030b03122502040207240e120d0207020a080706110109030f1202090301 70
    0x141040b90168060303100c0144c10310006062004d060300400014019625503401d54800310060b0030204014144040840b900407407241403449054000352040c0060020340c10b41101ca00c2c1039440d00c4104400705401c000c0c82104489002c11010210700c000c40f0340e15035440b80069031254485040d417000403a2807800d046001441003201c144101c4600c075070700811249920719500c6240780c5c0d04000194100074107200500440c0560b40c4045041c0c0070031061011105d4a103d0148c2c1514107407804071000a8454241e07401181e0940140541c8400c02c5000d4480c5d07540030394584145001d550b00751400f004a00c007985a9187c10301c03410b4400789801510070b55440e80181402c1c641801e8074625034905845412040741900e003a40304221601888001401840c804071340c2d514840e0700100d400c00c110f2035003007011000507a100c0c02d0703441c02001e102010308801494100040c046109690441d02d29074180490710380040d50007a0031200c0002141003020070003500f00d484e1030080c000e405000c0d826620380080750800c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 777582985 1250 777581735 777581737
    0x6030c1023090102070f180f0f0507091a1215190308031509131106130f141e010309110d0c17070e0f0c07050304090606180303021c0201060b04080102 66
    0x76400a800700d45c405076407140e00c20a0040641309255144099401c0c0340200c00190b00028400d103502d14000c103070f0401040d0741380d00311074081e6502000304d440c1c2001040f064844126510041c0d030003024a5052503041c1d0a06461400c0007013001c2ca10032a42010200c0c1c82c0d80d05440f101056002a69004d406038507846c06d207220381d02c25a5901c1d21040f900d03a0f03010f003c0ca03104600074418920301710003401d010060f41d40c40d2030360050042001c8d4400303802e1009900b010080744201c00204082010849060f180c00350030200c000d8540722060140f814280a00c84400111800500c1c1b05800e10700014094100d040094100c4480d030700d100e601160842851042c09480110f500940c1c0c8601a40042d21000ca05150b03666102c1e840385003a1100304500145207056000c506544c44448402458030f006083d07500c09007990b0054101c0240301c0d540c0c480c1440750341ea001100c0c41050842001120136182540c50107592007400100020644500c1d0329040d0a1070310030340204004041c811782c000d44650b1150101400303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 777584235 1250 777582985 777582997
    0x109050a080306013c090b0a0903110103090305190c08070602030709060504080706050d02070204320c040308090f0a06020c15121303030b06070b150906030c1023 71
    0x7a0b044031020b00c400380c600424658174031459580322409030510b0b2440a04002d100d200700c144600d243d070000d10786041c84001c108a82e6180d80d04040c15055261504021980e400d230316040520701418000041d8118003152007403000c280c81090f030403036250000c1b0349400001b0002400e0301d10200700d013400c00000390090740c0a1803260b100e000c5071030f896a01c112194080c1d031041031407030362082008001184c0030b840107002e02c028000c0d0151130507071a90081816a05508500384120501a05800d2400c6640c00b02044605517810b5410702400e000c400070a02d07010318040580111800140951282d0310494860740b0b4803806000b43d84640c0c0e54080107034445400d001c2c80c50194081000141c603146d07218040314040340c2c44841e0000c107038441c3c604082c060190b14500301c09141d95410b20200c10350751200901401d92150104085500e040034011072a1107410b05018081d0020000b0700000c0c1e80d0110316200341650946e1441e2030035403031140817181c0d11109191808002104036441464492310300080007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 777585485 1250 777584235 777584237
    0x30605090a090503090415030804291c0b040b121f020304021f170906102903150d0c0914090712032c040c050a0219050109050a08030601 60
    0x803181c0d40d48100034265000104001d0594101300b24003002c6240640c46029011a40202c1c0d40c0366680326510704030a82c0c000c0d0030182a403014281c070820080000c803080c004041010f20110304000e41e0070b0340e0507000505d113801c02d0801c5860f40c0c0c5101a988481e0b01020161a004040941c80862405000d0b1214461039441c0c800c0c510312100301c6005d5205000f180d0081c0c0d0301400741200c4c6401ca92821700e251500c820300104001c000ba00323501e00c6030409481c480c01209200d02411250502000300300080c2e40c5d170380c403200c4d02d581030007031410007015040c0c0908210340c5c0941019540396240b680c50300544001c910040d80c86044500c1c50b10a000c1c19010950954000708802c0046040800200c0840e010448407141c1650150006202000702100040742152081c1840302c880071a03054031060082001e025003482c40d444002c4c4080307928240c0584480d200076414410700d003120f2880000d4951300e0f08403014008411009551041003002d6020044183e00700040c0d5040003400d207820200d80e4000e603030b024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 777586735 1250 777585485 777585499
    0x50306061c020304210302180f040e061e070918110c07080303103821060f0109181113030803240105090111070e090a0b15030c060d0e010c030605 64
    0x5d61141d01a100f2580340c0c03c0c00c40c03490744044d11360208110b06070100c40c05103500503486030141001042d04110003405511200c20750002155400064800c14000a201c10b04001d1400c1040004400a40000c9007100b8190000f04940c00084c0051038035108004518080b481142c4001800c418040051401011a158080c1015035180420390340c401c180c030049581d010024144d9004142c02a46204203842600100703070406410601d40718800c401d014410b0302203a00380b4208005890003014940e94480c090a00003805800c010011003d20f071400c0700380300740c590388185622040000900f560102611424900b0340c072a00ca03d400107940c1c000751000b01111002d120030003850314103007043d0061004180e5401e401e00802d800111440303c0a2840454a40a4640c011549545020301c65102d200c00030300070144605649040418030340c009000500d668480382c040052035501092035500344804032040c92b240d8554402c6d10008080e07918606141d507292035100758100750150001000c44200b25800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 777587985 1250 777586735 777586793
    0x1d09010b1804052211040f020304030e0306040506160e0a06031407020d0c0618050610060e0d020a1a0c011b0e09090a03030e01020c0609010b041b050306061c020304 72
    0x220054450540302141110313080031480d0040c07442c070108071080900400703110394044d4031400800c2c100c42c881140012200d400104001c28160000b07145d69502c9006c1e0010003151401e901d8054503400050000c0482d940d035800000d02083c41201499501c190040c002220f8903a2404040d0060003c1940600740c14003250002d00c4441c0086002172424849448181c0800007591300d04000f0640301c0101c20b2090141c1c01648081081040b03843e1048244210070042c80d410420060308081c0c0c080060340c0304020408901c070040e2070b5580342e0740440714428801808510f0015855000b4000c4643e009141d6203419014400e514100304844550034080e120b05050461600900901480c2200c0f40a010713804100c5400003c2d220740c0c051203d94194400060800b4034824106040c208180c800c2d0341c5a03034503044846100d1405100303100d003a05c42c5444100e100708041d0b501a0550000034460345c0320f102c0c08500d81031281c0c00801c88004680300b4040440d038030318091500d04007030417800d01f540c0007410b008020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 777589235 1250 777587985 777587989
    0x70201090f0f060813120c05060a090c030807050307050a1b15051614070f091103160e0f04230a0509100f1103280b09071d09010b18 58
    0x41d01040d18a41c1c10400e03681030030b0a0b01524030050241655081e13a03850500390003c83e8003014006800a1035036504400b045a0341800351400c070001d081c2c078444620b40402d080028410180c0401240e511000094071030fa01410305900714041c80c0d1025003240500002b40b003c00c40c180001c0302540c080c901c1da60705002c1c0c071501241000710030300c080580420307004c000c0002e030409450360080140344034a4085100314201c034219820029aa40108842c10100c00240454001c6005218400a030540e100b0b04519240650700801121341046005101d002c04002e0780b00d031124000507070f00d075101400901c03200c0304a860158603c85180c1c4141e001e141000082000302e034081c0a407500410220009091049031952884c0081450072422059075039202c2d60008800e84d15400b4521840c07200c10089501005284800d40700703002c000e10281410f280c01d00162082d80d42d1142d080e04046d441c0b8040170700803110108001007080c008101c40e4001c1804000103480c5000d400281050b0b160301901c40821904581 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 777590485 1250 777589235 777589259
    0x80609120909040c05060a03020d060902070c0501050f0c010203011203030516080c0906071406070219172b0b0112141303230a0f02150103061e02030c07020109 70
    0x2181640020200841c1460349402e03880160414000c1018142c8265540c00294250b03214850460100e23801043c240c003903800c9417040c600141b40002d010345c85e0440725900d900f03244c0c0181c040e040c14440d01007440000b2011020030749a0503011400210769030b585801d81808006c8585a0032000203080c900000e20515900402900c100b15940303d410361030700d85c94407020203074000c000501e800ca00709002030408990301409481b03030803050202801003802c0c4400000e00f41462034030440a00b915a001d0300f40001c10008011070a07040c02c100c4981c0b200c1a540c1d0500060000032450500b42d841410346200e0201d407a80007243d030303031400d80b40c1c02021032000c800c40e03080c7c51118040014a101450014805d0346942003548401c51003403a007040350080f8086005d0341e0a041c00c518070031010002c509015000d4200203490420145070000704031801c282c41d417072030140405001c018603480e1a43c0010001c000e20100c0004512a148006c0d0b481c3c0c903214446021540040343c0580c00180c94070f42c0059404a294 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 777591735 1250 777590485 777590503
    0x40e074a15061305060a030b030304140907020f030d0b0a091a01110106120f051e0d0206180307060b0f0d150605041e180b0702010c120e071205070b04030b01080609 72
    0x101007100e01c0741c41c4c6020001d054100d025500d040c10b840329003010040e9418402807018001c1c100b0819410000c407021704c06490401041c41082d940504500f440000d000000e940d0b00000305040400c08a180380f010402803403caa02000f0680d0070402842a00700189100b03e80c044020ba070b54031504546c00207803a00b641c200e0310840c91107482000701c031404103400024000340c1502640488111080811500900f0350358007001c40e4041d08200102c0805070b5042c0040d83d001420306145920300e40b00760295070745910800c20000c1103d9030301e1819003425103c80c68456016030700104001a0864281400d01c449242c1c000c42240c12440c1100c003040300e2601d8810348056074042e082e4407405215201710000246591342040030380903515000c40000504d0344182a10445403a07001081b400b0502d00080d100c10010035855603080d00304500d140648000040c060115a11041000e90b00100390030220b060441c56040820aa4400240841441810742945040f1a4400215901692000c4c900d03901e40d0340342 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 777592985 1250 777591735 777591757
    0xd0e030318121c180302030a02060709061710090c030e100c051605030c101b0305040210140c0f07150903080423030f0c040e074a1506 59
    0xe00190b0199204440003644110f0701140000f01c100c070b544a6110701c9050380c80d00301c1c01a03000041c0b80040b00d0b410700140e82c0028071400e04000c00390514501900903a82c081c1000340361104a03000482c5240300002040040000d010704020840c40b0306c9004000e00040c102c44a43c034400c030440190110154400d1f05000c00140d40c07032b903003082c000c41c0441c40742c9018500306071030901c01404500140c100c203116040c000c00f20110300040b8070a0704054581d1100840b440403051520704810080580c403030b54001e100804451a10344441042507403242d40c14040d464160b001d5100b180d003070544804c00040d01c2c005a9150940780d8140c002884012210010759001c000c240301d0091100b00700ba1030f484080418a0b4403401c0c858000c0d0064540440d00d0480300c489604001e602400c25680340c0e041034426040c22101c41e6016042d202d061100141c0b254400c074101c0c00800c000d00c108060382c5001c08140d03001d00c90080101400a1822102035502c2c40000d84141040040c2c0a03080c800d14038000003120000c3e040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 777594235 1250 777592985 777592987
    0x1b050111071503051f090903030608060f0705090a030b040f06060e1b0a030b0310060905011415070f02060403080706050c07031d0406050402120f2d0603030d0e03031812 74
    0x507041c220041d00010300401e040031080b4007402413017400c1c55007540142202d003900046103007450030001c1c01d80d1242c4e03110b0041604080c050203268100e680c0c107568440044d05100b030342e90b00341001140c140c54a90740080d0034141d40b80e00303010800c010100ba601016005400910035207440310020041d61800340c07051211b904510744031701c02e1440c659001e4070250096040014015a0800109040421340c00250041039030322202030011170000d102c6c140c0906943e03030f0b00c080148005004035203c401041403200141c5004074a140c1040750b4580300350900790307028005a4a5a03070302d150604080d000010101d900c02e00f0000029030003503001d020f83d584070b600b40d070350300b000e12460303c040c0d11185580e5949681c1154580001142e10b441d51300040c90003001c2c034249419140b414a4881050287c05402110400c0030101000c015900184020120b9002000003000745d468020010b0701e1072058811a88082c0d0414901c4181d000010002e03620030700800c240d06010710014206152202d070b00e002c6034039034240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 777595485 1250 777594235 777594269
    0xb04020f010f1d010302121302040f060b0d110f041503060503210c011d03070314030f0c13151119050304141302120601091202030703021c1b05011107 66
    0x2c1a0308003800f40300d040c1401441c0070030103071100680c0e00044400c07108441d541d8815804506091051414003c1c0d4800c0810072981401d02017800b610034140900d18558448045012140914084480c14008100c035503030f44d40c1da186418001c01c100040c0c601c0c0424030b44080000c0701d05010400d15000258002c90528010315245800740e1508003c210144039942c030f492000e81680e41e13810744041459804020b42d103070001841c00900f50050410025800401441400500003451035401c1d004000b02480d140c0310b0690b04121003501c0c0c1e41c2c1c0e001c007800c011900c004006e04c58202d9600030007113525600340c544061300340710640c2d6603d0b04044000c00c1c0303070710808c42000107810941400005140c01003810074201d600d285942d041c2d0b000384104291640c00c0b4014001ca030343c2c0045800005010007e0f0b240003d0180703400280d240c04481c44007038011000c0358010b94010065810380c0304410f900440f6080c003500410301000070100c00f4010356001c03a54a100d18450440c00080500440c1d1542c0301d510b060315 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 777596735 1250 777595485 777595517
    0x30c09091104050c04051905060a110307300c02030d08180327010206091b01120e0f0d0c02240405060703080702061308120415090b04020f010f 63
    0x1918000580044801c050340c490140340d004e501c640d8019034442d41004100421a507014440c0c0c907000520f954100231545644e01900c01c400880c6c10b04040f10800001910b0075840340c018014011084a2200d42491b2401c2c40c84038800300000800010608196405451456840c0740180d4154051648070513014401d07540c03950b01c1240310401d030340710321401c03a5541d18580180040407000e503444c20310850340d1120661b0280104000344010091410100210ba84134007013080d8034400c2007a0703180d0030400350740103549048580081040400040c8182858541c80b0111440260258013079040035040040c40342401c0c0c2101500101404090509080c951254120181d013000403140c041c4000989036913a0400383c0b8191b8002d4541481c00d12b030503000282003241c001c10a41401000b405200d000c50b000c1002d4461600c1d0078241804641c807035007080550a80309001b25034a003030070884640c00b0080c052143c240198070980e00403100c0300054005681c1d92101c9084500090042c004841f100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 777597985 1250 777596735 777596741
    0x30f03020306090f18030a0518150304080c010b0918010b010305070e06030a0e030f040806010605073201021305030c0f0f060a03020d050a1d01050c1806040b070f03120204030c09 78
    0xa40646040c1c2e41707410100c0c1198255000030070014086040031507103c03904a03482c403500103030042c1200c0e0400b81c144c52280c01000d80c000504040c050810100d001019543d09500500498000508603003640c50210f00d0301c4414880800f1150f4a035003004030030302455010b801002d01407819900c400c80344003030300010300006800003843c108516031100685450000248001c20900c07880c10f103010354031400d003503003140741c1073741039010104003c02000410701040c0074556902000260752014043c88a40000c0842044550014468554070018144411007100c104440880b00180d050303c0050070110b003040383d10130b40180c0081d000203440400c05208d260800050100440710304006090012110700ca0007266012104c12840070313900d502100300c02c003200101c4424911400028081440c0802611905005041118040b0047c014481c20695955001e6034050b240a610441d12401141070a048160709054142e0128110a040c910500c4c101d0003205c068036001003034019103902d044135010007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 777599235 1250 777597985 777597991
    0x9030f140f01060b042c1e070906020a020d030c150204140402040b040509090a17030618130b0618090705120f031602040e01021215100c020931030f03020306090f 71
    0x10494001c0d48006c0d2051141c60f4280902e8001c42e036542e8103c5209108592848082c10210038020502e00c01c1203035642c005201d09403264140d0b104000f0010074070307003900d450312440c000030032005441208800e03040c01130340500111442140700410800034141804200e03c100e0148000c04d02c001c02c805d00c80b0b82002c032011500902482c013255a10f4405071100c80d500038180d4a20010b0810000038807885107000303a0f108500b4189408003282605203e2209010281d00c500b00400002384031001418954030851014811004a40ba25646284c60018680c40b02024040c1da03124005260016100803800901c01d5a580c1e905001145458108004030b050545094812a030082d01c40e12914031000d820b00280490b146005000c3c012410300f0a1054040c507400d100ca00e00070040d26100c000d4040c0c0c04514020810707015915400d89850786924801c055401140d14a429503203d0047c0050620034009100d003d802075954612900c00c810341101a848161842984504a14049402d0340004800700390 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 777600485 1250 777599235 777599279
    0x30b090c030a0305070209010609120f141e06070206090d05030a020706020d0e060105041b12021b160504050f0105011101060e091b100c0b0709030f140f01060b04 71
    0x4005038510340060b20b4040078a41c02c400045005c03034844118106400814054242410b280c80c2041c280a286046030800c25006000e1034410314405003840110b000c0700d10952200c40c15107040d04403019100c80c0c621252030034016148986000aa00240b0128400e40659080c001401c0740100310513049580741c10250040c030313405a0030080d000024519100500c0318070340303802d07011403040d1901024034144a4140c0c40035000380d0800326a5142c03000060343c03a100440050408400100e040c0e030341c41000303002c2e000344000540212000b0000c0389000003880c80d080c1c2400c2c0350504540d6200c4090009981d81030700c540d900c4910f0b130001805150b0140a0b0881180051400000e8040c0d13214007603501001d098551203003030340092040d60740000342040c10040719070003515003080714036103800300034803260300308001810307140c8400045800300e842020000700554000411100200d054202008441d0441802c040c01d41f20b450f8040c2035841c418000d80d01260902d03104503040502c0c02480050206000d8100307a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 777601735 1250 777600485 777600493
    0x11160803032406030a050702100b0a120314040807032003031206010e0a03060c0210150b0a09080d1e021603080c01022502031207050705010e0f040c0f180f030b09 71
    0x81c0d22603c642d80030b5445503510032400b0a80e42814a4040d04020640390705601c0242030000b012a13684640e0040e030b0846400b42502e0785048518201110011035031002c030b8082400c0000c001030b40100005d4990281e80c05011203001c1d40304100e03d500800a0f0022055030550802e0003500e86104000007507a0744032806050036103100c140c01002401c0160706800448402da0380e84412101913904100010803025103a804001c8005030f46400701007035129200d42042040c0001c1c503107000e244140303041f0b00180390000440d09501e03202000a000c3c2c2e0309900e9480328000c51104c903000000d200041c00c0703610303011203501c14108074115122046aa030100d01c5c828010364082103402600da01d40d0310042038420301e19100c414200741e50310405050040440b00350219200034450300000c2800030502c0021102d090030031030130120308500071403071401160b189281e1091030003242c082d94940110700b0620350411076640341d40b052903003080040754031f8907400381c268900d1020006200140320f016850360020b8000c804c803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 777602985 1250 777601735 777601801
    0xc1d040b0d060518120f04141c061a0616023c0f0a0806010e043003050a23101a0a0906030501051513030803071116080303 54
    0x8050b82c0e419030700001114030840203c2c00c51401030261303076480750300c1d900c00d00d24003194001c880c1b415020f00e000d08200440020007009840c0d85609400c00e1400d684000710070300d21010305051009006900d002103400c114201e24404a1800c44216110107003090784602090300e0326024000b03065188180c2c001030380004030400303480340402210050302c2d141c1082951051107541d030900011103a13500b149401860100c0082c0a4a0404503c107415910303c207000304280d54483c01c040c1d16841188100100380020b40c208861581358411161400c03100685042c005030310350781e03114011542805625010792006400c10f1002c3d8041400f8950000c1c190b2640c100195200d000080122400d00700c1c42c82c011100180e0141d4258028400000400c4c3ca81003c00039907141c10049010310400500f00c1c4040c0780002104c140d80342410940e04095a003045500780c0b00c0c070b001500940356550a80c0803c81500c50807008200ea07200640d50f0000f0307684440017860450b1110075070401c51050955001c1c402412100301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 777604235 1250 777602985 777602993
    0x30c03030e0a140a03110a0b2e090b010201180b06150418050910020a0207030809041508030c0f01020f0a050f0c010207060911240c010e010f0f0c1d040b0d 68
    0x2071a4a0f00c24a0001c0d0000b50450b15000d00504502203581c90242c01060a80002c1843c030002ea641c000e0007002c02d00ba1603030303404400195900740405500941d001040003c14841b41d80e0384007100800081c0c000b0810340600014501420b08960401420100314400050340ea0405100d29580e05c4800180e01d42095181c0d4404031a0030001404103c01c6943d8104201000104000c80d050020f028242185003d8000c0e0340292147c0d1036010241c00400c0004207c00680c9866200d12080c294805c1030701003013038550624613146c2e8800b403581c0303400f407003155595104014184221382e014485070000c0c0d4540500c88a090341d00b83c0003a0b415809440c01446100306012080c00105035041c415840041d014925141c806005007903401003501481860a00310280083c40d50030010100e500c01c1c0c0f558681141062441c0505501143e5074499401c03c45411078604c2c564014034951a10301c4000d002c880e07414042103500c504444820501d22561000c1d180e400c0c1003030384c840c1103007030030140c09144114000d4903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 777605485 1250 777604235 777604253
    0xa0309020a0e09011d0309040c2f070b0f1207030b0a120b010e0c0d0b0a05030703030c0c1d0a020c0c040218090907060c06051509070207060305060904030c03030e0a 72
    0x7202c1c0050010807401c11520780b00030b2003400030446010501e502d15030f000b0340d0003e59074000c681355a400307181c0d9801179114060088500d412020748000f130380e459080b44001030b0705902402402c001c50521950301d0200701080035034142c64921728a0200d1a040c9985510141460f6201800741400d2694a000740009915000e4901c030140c640404071070314079411446c22244045059004014112854091298070b11700300f02190703a605013483d80443da000024000400c80d049640c40349906210f0680d00108150300480200507150040040403a8503945440719051020380b800c0d8408000e9030f5078000703074115800d54084c0045d0302c40c2c01e0407100d820504102003030490b40040703001c014040c10b200d081001d91402c0040d01da400048103004d001420310341003007e403040440c2c401c01040d15880714005141144503810005051000514565403030074030540c082e4131881a03000f4900000c0c00d100000b40c860500d80000e0f4013881c1c1c5503070358a018034283d8400710024104410702e11000d0048034001004162588 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 777606735 1250 777605485 777605489
    0x40f0f03020708060a14130c080319081e0c03100906240903020f061c0212090d0206101203050c010c0e03010f0513020d020604091a010e0d020d080a0309020a 69
    0x240042400d0b50401c00e903280707031080081c0307108281c03810f03d5428910000c4140d107050f0000b000c045000c0b0328800610b44118820f01e1500300c000e45200208801c0440340341403d540d01425202e440d500d0254540d28541c000015002000011038845240491084c0d44404004d5900c1030a0700700f9509000e40390440007084d51982d501140065001c126842c5030140345082c0700010000b2420041d40d0940b03150301061078a008038040c580310760f502003010903440070407910820412800c3c0c0c1c0304559035452030100301b85041d0183c0b82048a846030b2840700b5003050000035107074050454014615071940c41c02100c8940c9410003002181007000074414409440340900400e500c1104076144c1d020300400d001c00b03040c2100c541c60708408510381402e0a020302c0140e0a0100e40d6100e8041e6902c1d06443c0207400880c002d0b1285a224003900780c47c1182d02d03252092508000d2419a009030b88696003890007508002034400c4006019510280500d8040c001070940001004041690304002c148207443e80c0005500d58116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 777607985 1250 777606735 777606737
    0x1080c04360c0806030615010806060f030405010213150c110409050115030b09120403061508061306110c100b041d1e0d020d0e0d0609060902011d0102030909040f0f03 73
    0x50114404040c1c120f5003c0354004429070080c01c41d40752038910085d007595003100b00f9050085140100c0c2e12034541408079101d0001c00306015a4074103242c030b1300c01e0007940714121008001040000c00315680100404d1030b52076030120b035a03000408440351540b00980403850483e90f4429941ca060320f001923400e001c0c480681a4051030500700e68550b042ca407080c800e004104281b1500b1030003c0d6002403500d04155001d4a8022030001040d60440c00d107070030100c40139041544280b143e4410840c0756840752900018403031040030180507141051a21107014000c1e00e0440d41b094000c110402c00400003540302c0c000c13109c002000801d03440140440340c60034094a91203c1d016030008054901d04d181c241410041c1c0d01035907001031911002505c2c00941700c0100c0168401040000d280301c0342c1e179660300202500940c1d0091020040605185271036002003042c65001c0780803545250b1742c0001406211400e40809906030091403805920f9020804801740c010b008482d800750b22407803c00400e401c4410703e16020700c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 777609235 1250 777607985 777607991
    0x7030b09240105040609061808010e030c10020a1d030c09070216051c080c070e07030209040b030d200f030703030b0a080613140129040b01080c0436 65
    0xe03000341d0098559990101034140007040004011955001044008540981c03524000320502d109441d202e0381c90b10b40c0440d041d503090500344491244003000a1802081f0700c41128400348544951009a00410400c9004150601030240c81c001903c10f1900c08180c004007940e06c98481c4000083c1c3d2200180d82140041c3c4c400110342c150004100d000740080c0400b154a0741c05400e0000f0003070980681520003c01800001c101d44400550804c03250005d0306104100c08124540884005e009400c0340000324462410080c82c3c04480c20702051861142585581d031400c015064040301440040402d00d0312618480c1100c1a2101d0505101070004507100ea540480e0740d81640e010001140b556810182c0640c001c50305001c0054040c0c140b82c55110f500800e02d0380c0f2142c04184041c010442d80710306000340c85a9100255280070346005680914000f12010000760710000300442e10b010382162903100c602000c10007030000912144071141f03030462071054480c02070740541584000c1c9440001035540591 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 777610485 1250 777609235 777609271
    0xb04051207120204090203070305010c0e1f09090c020a0203150a050f09150403090308030703091e2f150301150503060303120403120606090801051b03070807030b09 72
    0xd0010300c0d018040d40d2030350003810304074100b00315110003940708180248510b03940c1c4081c0e81191000e0204000454105e070081000f02c0081001420100c0714480b158842c4c154004c0501280301c0201c40351000340c0c25640c0e650b0543c0d040010300700052055011060540c41284115401170b1303810000c8482090649205041900b054403000d801d40318041e010500c481403c000b00502e00304d00050500b08100188042c0085443e64102036a501e0450b80024010400000c200500d0036019044130903903034850b05920007008106a940d14041416100003070545801c04040d0714084540c020040341a402568078a9444111000090045140545004401c1f10120040203410502403680c5049566801c000d407031460401c000030f0300c0e480307a6280880c081c00c03c040842c0a05100d105441c4488800d0442004040c2d260b40025081c4a01c92041007000c0d824000014000d80f40c0b01b001a01910201d09447c1c2180c4801000f45e4408800600d00c90405a072024200040d81d036524965001c2d281c40186000014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 777611735 1250 777610485 777610489
    0x3021807202104150f1706150d02071103060108070e1f060903140105010e060d0c08030c1e031303141c051903050615071a0a0c02060a0c080a050705130b0405 69
    0xd60842c1e418000c5c0302ca020505c11a041e003003440341c0e41d55908005007030310b00c4c6d803000c0010769900c0c10505040d1043d0000f11b18500c1c1d443c0641d0040c040d13180160f0429603000e9054040655505003402142000d80200c4004c102c1603018200142d00840ea503a4510520b4000c407400248185469200a00040020a042003400810350030003030b1124090303000f80315a606044071403000100144c00d00b40a100588038032001d0101180c2400c01030030520054981c1d40c1c40d050100340d0741c0c50a0101d00512180b149440351400117001080700c3c0107019140802400c90725544900c0d030340c80041c40d0001414000d150640355140000c10b03e4145c0c0e0305007a00c48580301d01c0f00703060300394005a070300c0403503000d03d45000c080c00110740c2d4201d030144110000c0e50a89955182d5490014030301145a031700485800749045c188658207a4540000d08000c0385070382151181c0c2d8583c40ba0500303440b031410304103007c14400c00224942031f110781c0209901510a0420b035181040502d0030481008003070707200b00741c415070209061140d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 777612985 1250 777611735 777611759
    0x5090d17060609060d020d0501090b19080d03150b030118110309150606090d0b0a05061e100c050a030207050306011a0d02090d0c09050103021807202104 67
    0x305140003100601e8014003040e1648070300555a4414400403416180402e100e404654010b81142420700c07040d41d45151090240881003900c0d4441e020345409442d56030655110b280c11518002c00174882d1456802c810f038000d147c00c980704e40306215811804104030300c400000b98001e290314000c55000304014071042d0115081248401301e01241001400003414001070711080749800d24041c418a178684c00300003400c1e40308041010b60402d2581030042c01f4004a079031581d1240c0c600c40810b0240359540010000300d000c00740314082090204407241c0c20103043c4030740c5d00445404c0c0e608010f01610887d803160341c6801a032900450051740009424003460505125081c0109440c2210981e01c2a402d01011101e010b5801c641d105c3c1d903401300c0c5230303501030b0348002c040100703a0341000e90454000e45a640800103041c0034002030303000b003585400c0c0b04091200210200d00c0713032006545012600d24276604051207965800009038061003001c0d10808000200720081c0454070608818580c0c1d84c1c500001e50b104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 777614235 1250 777612985 777613007
    0xf0c0c0406080a1209150e0f0901050904171b0f0c060c1002180d050304090c05070b0c160507290a080f040f05011406120c030c0613080105090d 63
    0x941c01d00c030080019070400a014181194008080b02c5a03414680c4120b4811640e40e010800d100110045882d80c6c070742018014420807410703542000d1700030b80b40b02400f00e040021b10030690004041c1300041d010500381c86002010072150b5038114074214106241c0303130700f0301e90b0a0440b010680011141010f450ba0420034260107507401e903259410304805060054417a0380300c002400c1407580000d814010389485440c246101c5e00000c14000220800781001603503070700140500d140d044e28000002c0c01242c068402e5500b0b0f16806005c054150b991024140c000350809000c2036007100b201040710000403014003a250113040b460035900c6107840a0b1000c01401e0b84440401d24801404124400126502040391503100d504070107030901e1a151460244404145640003500e50b500e000e5004201c0043c51966600030007040b01e5060290100114554171640d403030100b00d5055010705203181c494180301000d4254240da522030350a2195a540e0030790300799003045904601c6608050481e844d8583c00000800e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 777615485 1250 777614235 777614239
    0x20706230a030f0c230d090209040f03020607030510060c03232a102004090203101410030b041107050105010303022506050304151a01020f0a0b0c07050a080f0c0c 71
    0x85c0c01c000b0003905041254942101c94071400c4000750407003c2c048280c21440342c2c0f40d400390050b09140b500b03051100318030040481c200c005000d40320100706444d2180c00f48034010582182007021440c6809415140024408804ca00380891506030440c07940c0407466402102c602c814010381d96545141310b100c0c1400016840790f1096a0105003c4c42034000044c00412403140c0742d4001402441d600c1032034258043d280c80d003003441000001d0210318110142c0155003d02c4a151120503015110800f940b11182501c201342c0d004526090100500c03486a000740c002403e01810000740c2e2001d505010051b9445408103581c0c0303039141c1e0300410070182c2c100950312a0345006980040750000784440d804001c8428419401000008004030701885100414080100d0340c46004111050856440c8003030080f2070566180036004511010319200704c0850b9840d0881c0e8410310070308841d6610621584141c0180209503118800d00d0144d000040e800002420410703070b042d9085448500004603103150110031501c01c0c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 777616735 1250 777615485 777615497
    0x201091508010905101a040609050d0b1918240509070605073206010806010f090905071509030b0a1404030e0321070302010608030307020706230a030f0c 67
    0x918040e074804082815540310000104094690b00c6202c1c540020981225605050a04d04110031400c6a001041102e28a46540048960300e00400c09681c90b0114081c0c482010b2030000b49911030b0140754110801402d007000540314101200d906400c1074810710031101d0f40b0180c8a50700c1c0740039918001c055071402c81c0c0c2c0148002c2c5450f100c0c2d00e45801b21841100300380600814100108495a2130b0f0b25080450f1610301000c07000043c8155000300c2d030540401540340114000407403c00c00c0440c503079040e20717801c00840025501d0001c3d4440280030440050b00c5034015101d0205141c00b03010b03201c0a05000c103945e203070030450031400e04100d03459014001a0003945052424001104041360503544580c26040c625849001c40c03000c02e040051070b640780e03620000340d02e51010641c1441000713052118000c0d4000c01c101916020320a69a00c0b003568040c001d6440b003038080100e90b128682c501c03070700c11940508840010701164000401e801840c0c04101081e01c40801041a0302e041c45010444055441d0131 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 777617985 1250 777616735 777616769
    0x140d12050f07020a0b0c210628170f16060f020f0703121808030c010c080603061b0d14071101090317062103070b06011812060e1009020109 61
    0xb070743da105628001400078010034000344502e4046d00a841c0c04010400c211104112007403041035014804681003440740914203001d241d41c40e00348014440e8004207007101043c003400c20307034031000c001e0051a01142350b129020850300c841100303124400020407042c601201c0c650500c0805404e080b58240b8060071503114880000303111100080d880c08490300a0002003440c007142404454045181d0b01e6020300d904035040002d5601c80c0007000304007a45450000f0050400d48040485440d4000e0b02c03002d9240d480100881d60132042000e200d160700910b0fa0945150803010003008054490412070301c41c42104900803c6021a04807500c00f400c40d5041c002004490900d1340c0141c6090445a04030100e0781409000a400c0d8450040d03041002c1c100107808442e07421400b004c2540d039032104200711482a0380001188043d4001c100940a40c02e0620300d500c5498101a082d480b00c00800d207003600c2c2141c96000c0450101414000b0034183d2804003000f05617200305000160144090b581300f00d500032301190b21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 777619235 1250 777617985 777617987
    0x7030201022404080a0507050a0c030605130213051f061806030606020d0c020a08161406070f06090206070f030503040501060e01180b030c0324010b0a0e0607140d12050f07 75
    0x952090340440c00d60b171102001c0c0d10840c4d0300e0244400082c0325100300d107403600c140145014140112441124140305d95520454000004090890001e4102c00c0d180d0fa00d0b154559260081944062402440f5103d410581800301542e00c45d1f40c04040440e0b241148030900e02d07964842d44014000608083c0f00962500b80000e6980203040018410846158070310380c210356030400020010b00c0f0308000c54406031040d118002c410043c0c0d02c1130040455007810082e0041c01c00368141c520b49900440c00340762002081c0c40d03103000340c12600d81c100e074000010803c20f000140030f412102c2070a03000ea90384640300d207000d240150840e95240c01060302081e9000040002d13201602030b44929010840700481c044c01030300c0100340740511a44016906008542048140480e070107400c0005090003140204e045c0d913215020a03451240303c1000c3c0001e82580d840002c50b050942c01001014070544c04a07025580c0b50720003d08060040c40b0000c00510341c0e9606000101a038040d480d000508001140210300b04018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 777620485 1250 777619235 777619303
    0x1050108061311010e040f02042c060603070e0604030c0302040b010903240e190c140d032d02011509050921040803070f02040e010506130509030d0e0703020102 70
    0x94020b0860303550040c503ca190f40b248100c110415006403040c881043e5130002c05004e900300740265408a0b80346003c110508115021312100b881d01a0f1820703805858071003c1c04420ba0008207554207008a000b0f80800c0f58480790000d0000f180525280d0080c1805e602c1000107031004800c0c440d0403c880403800f80089070500b0008004100d4032a9500c0d020300c004640800500728221801030207004504501c2d4601007040c60410940d44514600c1e0324050f04d40000c200f45a07181c0c0d01d419040505140c1e01c00019016044100084410007013510f228440c1d41009014400d03842c5c00d5500503511500036282c0c82109640040c0a05006841440385180540342150355100c064900c11004141009041c2508140000c0b40d028080307280c01d807950307090107050911002000f02d008074011442c04110841812040c440c0c0f80c0109401010b4051221802e59910003500780030300341c004140010840c81c0104c98803032158082000c524809480030368070354000607042290001c110189600040d8880340c103422004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 777621735 1250 777620485 777620521
    0x708010504021c0b180a060501110d02060601050f040e0405070302010908070506090402030604141519210309050406230402040e04080a0306051005031803130e0405010902210105010806 81
    0xf04001441062800c0000c0e0003003060703100e0305000e5064505001140314a80c000c1030aa40c1d080e20b030b1301070301005010f0040d540d03071480440c64016000800401c1056208500818140390b20007620307400c0580798070800d10450000d4030100c900798401d40f0100215604041080c0c01820b450300584581031034000840c0302442121402c41c0720b181d0020010b0b140b5a45d582c01003041608403442841d540c0f5100b20001038840000c46241e00c40c05035091b00940b03000d043c05041c8103a440c0c11b480000241e624440303000701c41e600380d08114240200e0080c0070925803924468980240510400c850b542c84c01d00441c1040c02c000120914041c034010001400001c0300120026005a80428415a48d48030604214014000ca811280e070127403900c00f20301c004641c464080c40c022170f521410780e02441c0704c02c2e515940e81d2203202003503c42d08a00000401c0880c0d11503120f1907100b40103800106581d5210303800242061180c144000030115a54000341200c03a0912600d0701400410b401411181444c007050643d0f0035000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 777622985 1250 777621735 777621787
    0x1e0a08090705060a0c06140c0406031401150c0302011b0306210b04031107080109081801020604110d1704081c0c030c0206070302030d0c05041a0313110d080d05070801050402 76
    0x181c8a94401c000301c0758848047e02d501b91401946904144a0003490b0303600c10303c03900300001d007451504009000f80600e1641200c80651440c0194543e105040c0d5921300c814505030150f550351300032100c0c850f0109454181c8803203540e500088076400c03c000000070000003501001d83c2c1003101c0700d034000503030702409040d00503030103082464403200140d841d5031401016401c901c070710f5401d00300c00e03004120918028140182110004208106040c40120390369042254003800c4600421094000790805801d6000214054a8401100c003040120950319901961040d04a9889105078605210148080080201d1940344c4108421050703200100301a095180c0644150f00004008003014000c0041303c05803984140180580000c401001c0c0898001d8403a05024003000c03c51070000d0180c0c1002c0301d12401da209844a80c1c00010b0300c0d0381da005012810b0313840d000003902d0120404604500090b100c010604580400c692600d1380e0010101c1c5010f03800540070710b0040c0b007030011100720b40794107010361122 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 777624235 1250 777622985 777622997
    0x602010501060906020a0803070c05070b07060903030e1b0405070302070b341e170f04050c1507080c0f1009060f0606020a12050921010c05070305040303030c051e0a08090705060a 78
    0xac1c6d801d0040c2071500981c0198686400042c181e070401c200c1d5007002010b10f0007030320108140030001d80141e03114290101e0840094a1102c20b00d00185070a500268002200d480d0060800806960b40c0170350140c1607072a000c808904503800d4848948002800c414162140d01c0080f080e01d41450241142d43c0c0d0b002e0344c000031500305890803103203841890309218801c590313020700c0c585003454880d1608004040c1d400b69520700404400382d41c41c0c24039002030600840211031a914203403030349d103a011142c0c200d02030030f100e9809010301d01521440e0401c1140780c04070131910b0004131881070b403801c50308540901c0750f18210039082070f10400c01c10790041003c1182c50b8002413028000091101d08035107d1250404581c0d0041411070344901082c004100c0000002d107843c001c00c00805000420303500d50040c0c4030002c0011380204000c1c00040d119400500c8414a141440340c10842c80c144803150400c804504100c212001082c03040500d80e000e0800e980088603c0c010300307582400c001c003103142e621517000e24400b07103d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 777625485 1250 777624235 777624257
    0x408070206070804060e0406080303010b090f062802210412060f060803130f0b040b210406020306180702030f090a03021c17131203030e06010602010501060906020a080307 75
    0x7150812200340e56484960f05580b280c403102d016000c102c4807a070843c000d030324000e00480d00000003c11a03050b102d04507006802c0c001e42e00100311615288070355954110741c0c28041c4000140303501590f21329518203c400c4003030382d04240a000785440352008042e50049501d00c42100c040c0c0300ca07001c03101a6044550341c0300160103242440c1d0007070000380c014145141e04d844400034071100040060140c0071515807808170029a0b4581d42074400f8500d0068070400e1008000402031080344800520020b44030140280e18a40d0f10340010340e086200b2102500d81a40010801c04c051401815501c5510200d50440c2003074100490300070750300e01440c030103c5078444001807039084568410a00f40c0007954002c1c003400714480e40d8005d0080c0700c80d4040d41201d00b6448141c0807080300c03000300306540c0c04142ca002c0e0100c42c5498801050f00150b403000e01030703052507959890701404003400e0040901078503071600049801e500d8401c0081a10080d40d11007030854004030714401c00600c10070202d0f90030480914207001150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 777626735 1250 777625485 777625489
    0xa0e0405041a09061006031413051207030c122303130807050106170a150b010c150e0d0c0203070317130609050301050105060909161e120b040b010804080702 69
    0xb44054848601c401000c0402c00340300340008115104070400b80c40183c000740d803a60f0580039039001001e02081100e607840043c40d400700c0b94884902207809903003140e0f07420401e0f003078281d0540d0011000350009003a07000344109026810302d0307008401c0060301e03140d40c4001c150000340300d1400c0e1703040c0c0380000e110f00017000c144c0c10446a08500f1034143c2000e551940e070400c0340381181c020801403180c12442582c0361000c090300760000c1236144841c0c0d04452100c000f212070039030510080100c45082410302298844503008035552004900345a601201c0019540d484007450703a01e0080b41d60030300800c008510191000586000c00c04c8000c40b03511080408960818511030403450042d4401201c00480703a00f0002003141e40704038581c0456100342c7c001c000300d98803441807101911494a00a400c0042100425001c02800c001c000c0c00d03e10303a190100002c4403562010020b000301010702d40002d4009054030842c4031491181c000c100c034089504000100c00c4400185c00104003c01c01341c244040400c03420195 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 777627985 1250 777626735 777626753
    0x70f0510020409020316020d0816120608100b030d0516020f04090807110f060415030902270a140f190203011d18060612030c060f18030a0e040504 64
    0x10886035102591115103481e01c900080d0412074081d1103810240014282c41c2d8008184101c9151040eaa00c00e820703030307801990400c468410070181041049030780051b1400040f6101d000b0180c001d80b0050210280e00030038000c2a64406e030444c5200e6001610590030154004084540381d440b401d04208000140d8000110100c40007200b0903046030900d108281001050b90040491500c0341d03400c1e8030400708642c1032100001495500642240c0d082206201c9070728062120142d1104914020425103940c0c0c1c0802c00700603003c0b260032201c440113554800703001280b100c019403000b180310041040300c4640d540b9644050026224040c0100c655022454142e024480e00c1001140301c2015581e03940c6d02c001100c074038000e0280241c8007041403800301d100221041c07a0345000345604401006161181c10410011543e09010747d00c0c188000c21440481d60010310005206220b0241c25070b0403807800400750b0212580e48103403008580c08c2000200522a00500190300c15901984d0003e403650304c6151400c46 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 777629235 1250 777627985 777628003
    0x90f0515091c140409060302120304030308060103021b0708062a070308041b080c011403060915030705040608070602070602030408031c091a04031d011e091508100614070f05 76
    0x1c1050024000c00c80300c54a801010441c8e2003901c00301040080c68601a13200e01a600004001a0b807210115034150301c03940141554883d41c640042d004004410503e280c03080503444204550089401c00c4620310702000c5448800c20f03047c1c030882c10701d1080d0300b01c005d19120b9658000c0c14420700c0d1011800340000d50325603d00c9200c99084403d02c0540b680045a030f01c90081d041c0b580000c0b002d0004c01e05082041c429640110700c0900382903401e03240c030358600652991881c021382d05440b4980000800703543e5405000c00910401003d031807241c0c1080d40090420030f00740c00040565100f0041005028800412280b20084048200d00803112100a24002c0c000005010701282c107412a02690801c0100100340290b11a4580300301d407a040307041c41c1c10124a400022804119011521012a644d03900040c084803e545030600348503482d10908804070300c0020660001034040340801c0860b03540c00c185c80016103007a040016002861066998151081050060101d40c40c80080002c1040420906003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 777630485 1250 777629235 777629267
    0x70305150d0605040227341106010515190e041406030d020c100f0c0c030305090907030b100318020a0f030309050d080306010e131a04050f0402031c050409090f0515091c 74
    0x10744881f42d000018180e500344040a007150152100000303080c80c0c80703800c00c180b05450920460411a01c000301c00b04080220617003034103000c000c10310200b8030340d206d00c604043c4041c0724a01012504ac80c0307051605e86072003110200d080d5417081c90201a20340d240c40405010000c2890000d4003081c1540c8121640851140e00500c00520b02501000305608203020f0900d41c3c0090303800412650314420101c0684047c2c120481c5c100318200c03100c074442031003504a2100e074402c5854080420050f540455500d0310301c0ea11012903002104804c1c402c16a2280c4420014641200d014010102d03d8480303e5441c030010307204905000d0342104910381074441060184c098025184100151000304607a44080d91402c5102c3d44144e10b0040025038101d403403407500e8003803500600206021005070407032100042c440040f42c3c0a02105101c0011111528050508185d102d920348140b1950140743c41c510340900302c50601c60101780101003140c2d2032030005d000341246490b02d01d143c51114003660152100f10a00304042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 777631735 1250 777630485 777630571
    0x1a1204050a12050301090c034d030105030f12042102030604060f0e03040807050f011407060f180201210204031a010302180f070305150d0605040227 65
    0x45140390003001950480c0c0d50303c00c2c2070040071f0480c0c00440c1191000c104040940d50003450780100e0808400c0314640f0102078480d06000380d88805181d925544003042c1600c00340c0c8002006110600342801407103848070340c01000740303040b40d240640c80c1041c0c0101d01820083d040c0000c003110001000040321801c064018040c0e03142d0b4101828110f001d0040310741b09100b42800c009440b03940b0a0000101c500303c0c3c1980f009415468213040404c20120000c1c201241005010228030603074000220040c075005111780b000040d25100e044168043da2458451051100000e448803000342c0d0b001040c0307200c3e407000f103000e40d8400151400048000d010f15003024004015580d03501001c0d0948a0b9294143e038022215102c0072108032101d2180040201c6400c5040d208503004140c07905e000e6046036400c01f8035010116020060b007804544088051501590800d4894044c8800e50400f585010344015114901c1c3c442804e141c000800404400b4000384009103200480140050105507840d8014503c1c2c2185 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 777632985 1250 777631735 777631763
    0x606141804020306042a0207051c0803060102010209180f010e010506090108190e0c0a050301020310060f0e040507120b060a1403090102040f08060406060b040e0114040e01180c1a1204050a 82
    0x5600e501c1d06d900030032000351150701c1c0082900e10300400030030781c8400d410000f075040c46842d5407031f500d55404c081c02d000d0540d0f4080c06102302664a400c1d001c04a034404800404a625216074039000701c0c50180c1c0401c3c88100070750014012038403104102c9041c20800e0030035040645440181c4080540a000300300c486034500020000181004540b0304111a0215040388105484400705801c030b110640e4103401305049080304021080c002c290004800c81d150400a50751001540854192403007104d500e40020300b002240e2690500e1032140307042546043c0c502500b040c07401e00c2d01030601002c1809038207600b94088001200c5200940481e40904034140c81122a0703a0b0b1201c1d003c0e5150030a0341c085441900b030050200301400c1c144190380485500d000303204020303440c001000104070387c0780700c1c0103410030b440d4006030000b001d0034011010800700b6007614654020090030504075400781030b04146800b840e82d007540102c140000d0103883ca0640c15034012a4540c81e1840d00300c2c50b1500301d2030028034001174000c0d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 777634235 1250 777632985 777633041
    0xb0910020f0d0501050306070801031b08070b1213151a0d06090221060103020121050702031803030f0d1d060703140a0905060406020a120f060614180402030604 70
    0x41c10510310500c02c1804a40d072118201510741c40d003150000c0c0040d404400400c0403400001107207010380903075060b0307106003622800c880e801c2c2019900084803820380051000080030b50b0b079160603408010411580b9500700c003a928418030610094410801a48130030b6140c8803c100c601d000301240f60020118181104545800d902a01e080365047c2e00c80c560b149580c510345601c0c0d2215540007182e44028083e9a800c1d80e0064540b2810b0029040c0c402d41c1c0301c0703900650b81605104039400350b55290000d50b200c04600b030820010300d50082d4003500a030024410090b08141940550700745407850040403940c440c600c5d02d0f60700b4408802c141090781340f180703070140102d5503015440741140c40ca50030600656942c5007080e10060319882c074001840f5601c440000340208641d94085d20342c0ca040c42c074240120088001e02c03003055541c003c8045054035076a8500700140c0b50410102616200c084603c036041110300341c0c41c2800390610303902c8c81c3c4c00f80380c0000020388596900ea111500b6501424000030000203c1d0300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 777635485 1250 777634235 777634237
    0x8090f1515091302101403070c12030204030b0a05060102120f130e0702150405010e070e060a0905010b0421080f0309070501031a0607060603080c0f07061b0b0910020f 73
    0x2031885100c2a101d4400d000e141810041144507500e41902d103840100b9941c00e0000d072103403000d05001046078410410070225061301c001c5019141a42c0c80c160821150b0070603d022038110745100c020b141c410442000040e101210107035111288200006840d610400140e003003400103030040400c5c5d100002c00840c0408410040c00184100158802e90399860740300d0011601415291600941e010401c603940101c600304a09502030b02c100c0020507591500d101c05450700c28a9000000408a0101089054200a41100300500d4410802c0c00b49500d401d0085040d03102d10700030320700402da070381500140901d60207002034030340c0ba80718002c4c503500d804403019064990030aa80004490088041c0001d180d0f10a01981b0f05e80128074840307001c40354440d41000f0450340135583c2120100d44a20b00000403409030b0020301041d880040103001141c50a010607401c110a0343c10803c1404508504200d40104002e2640d9040d940925104542d4a90030141e605c0c1055800c038013540030b800011044d0490002c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 777636735 1250 777635485 777635491
    0xe12070515042103140711090c0a1106060a150c0506010902030105011128170406020309130510051e0307090c02010f050105061e0f03040804050109060f0f08090f15 72
    0x1804072030080010101d0703c00b007840016003e00001c2c001601d42408500042c0108000b03489842d0000544401e03502040030740008a620f42c0814501081401c0c0003a00116a402461314000240009103004030000d0301004403400740c00c51800301e000c05281101c0c021000d81d046580c010317080794503560f90351500e10302039842400b4450002d00001c000010004000455607410551341e1040030306480d01c20780d60b0410f244441c00a90b2b0803103013000803c201410b000c0042c4042d08440c5d02841e900c001000138000d032a04070407680d590240c60002004030a0310500c6a450603194101d8400402400001100c1c1d001903109487d90b40c0f6008000300007555224a07030080c1c3c40900300b07400074007010b00f8a11002c0c084070300c24070846070482010000340e100340e000300134803611072000c003d06e40e8100010945c1d08401504101ca003141d150000042c00c2c407080d03070410080f4000b4291407405040d02c44103c000200b1030b41d419040b0009000a10b00480d9507803900780244440200480111400c10031400800640d049040e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 777637985 1250 777636735 777636749
    0x106140307270510050f090f0705090a05060304110103050c040f09020a112d19020d060e0a0b09150103080a030c1b24150b0d0207020a0905070305070305070e1207051504 74
    0x1740082c6e40c0b090504007003207842a240002c2c00003295450304d40c25611540300e080010343c801001200460705644950242d40130354002c00306e024200618000140c11500f01512210406509010401010714254050310688020380740c05a2511106407040c0c48035008220b003064140520b0150016441c100029001006028544441404a0781110756140c52148403080c809402039020003025052803100c1003540c034403400f00020000901504282007801e43c3c42c0032140f988600040c00203614003048600445e08400355408090b5165650b110420f00c5082092014541c80720794a0400d14050116030400c0480606da500b040741083c070f02590300b0a4800c07210302203260780300141c55000801d44a41c20000c5a200c0901d0442030409200c5500d640150060200c4240c0070409040140c84012029005001d1701c403010626051002c005000d030b810003014002010f150400f0070031219032110300d0383d030302e01c805807180340c00b00200710303c42410304140e40c0100ba00002c06942c880442d8140a0040088900d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 777639235 1250 777637985 777637999
    0xc0105071206050117060d05060c04080705090f0703050a06030212010e0106140907211a030d0804020f0613030506070f0f02030406020604060f0e01090311010614030727051005 77
    0x780125040031a01d090085600003015490221304c108000032410350491002000d181d40743c144c079a03601d442d0540840e0500384a01e0081010001c0040c104084000380400310340c440c60f2460000b10700002c0440c01400e0348205601c520114071200301d59800302e005136070050100c0c1000440c100078140600302c501c86c0c500f00c6600e0b185002030405100d1400c0e07501010010800350080d01c07803500c12035481c694082c0079810000500103c6651203140d205189a4200c0c4520000c00d0340100800c0509110701482c120081c4480001004010303601c1c41c400490a240c101e80e402d4540c01c54000980610605402c010868400e880031300c9030040e00030300d014901e0405030741c5180200303106c010204d0326401248a0400035a05c0240440d00080451300442c0028662400020354184480159030965860001c25004108106440c00c8001801c1c060000a402050361401c1c0b5510a130700403035035078070680c0304d0052208600d10002e000812410021500c40c0f014220a000300d080540c0c8400c0f10003050300c2a24401c10f8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 777640485 1250 777639235 777639257
    0x7060216050d1a073c02030a0f050c1f0506151204031214160806150f0c03042303150c030609060a080a060506040b0a030f030e060409020c010507 64
    0x382100405402e80c0e48400307460400020014030798030464000c3c14407810f00409003004441c25219918540a0880c120349507000041c041d200303808032040003409081150801c100e03601d04690800d44404060b4240e00e00550340e03d40441140e0f00f07041100c81c0075103540c5081d040910800000d030300580e015580031034400300340302c880109084c0030b0b1150a070aa50207011010004012078000d109036094010071400c041055010800c44010219003210743c902551454504500340683c000c00c05a03100c00160340b0400e91000c5081842ea0318010f0079420300180500003041c41c01100c0030b10580b4010031711110364504283d901800c59082c2840a4a824002c0c8a80c95032480e00c0011254028021711100440c0c52075511380100b4000c519000900071504221035450006007183c01308030281080c0e0143c03a0000b0b540c200042008281d5100400651060a20000602c0450083c642222142c2d505080220104481c400841c3d4540229440030850501c080780c1d2660260b4190401c40c13080509503584408a2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 777641735 1250 777640485 777640489
    0x20c0303090709020910050f040918050606100c060f02040f1517070905060c0c090a090c1502250510120f1109010302070203030c07030309080d030c0203030f0402040b030706021605 79
    0x102620080640c8801b1000a540c0d41c0340c0120700420000501d4a20a0b25007a2038443c464196000b025000c1c4d25050a0564101401014404031350042e204849000400540c02c100901081d840c00000e45500e80c3d03410310008030022941280c2c000c110100c0071280780c642c5ea4900c85800b0010142000c0459030080071420100300f40a0990310a003070b551038140340f803424003092081e95005034034070303000500c00c039620701038035a0340c0c1030a080c400e6020300d0b00814120f11602e0121070100166104205d00c2c6e01800009103116004070b4070008801030420340c19207036003840c041c04841c43c68941c0aa900011076002200c00c155003c145038820901010003400f200300c0b02c0c81d800e412111f05424614825009002c482002d40c403d0b0000d2841500040440e030078178980004241c00d103019a44210301080b055441080304200500c0b8400450005042c10048890324079006900c0e84001450340c40c1050b1060f000404541c4ca81c0c2c044515160f0203002c0355026600e0b960040d503146c00c01e030f58100c180c01091000107001c3c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 777642985 1250 777641735 777641737
    0x150c03010e1302040f06030b011401051c0c02070e0a0204150c170903240114010c050a020904020d060207030e041a011e03090b072a050604110a09020c030309070902 72
    0x9500410369000c1d030703a8030001c04410025820104076030140c0c40e40c00703604409406000d0040034601507001d901465240105040d581c2d08002255418844207110404d007450321200100c401814000700400c101c1c4407088100e003007030580c0c1c000340c0d02c0c06024000d02c8040302ca583d000d8029551007454250395404100310680303045101e0071004016480d9021520070748207030003000d42003c1e040a012520428801084980c240d40070480f40080c407202c15004000408000e44544000341081c00c210058140e5a1681c0d52142c88561010340650900d4000c10304541300d42c000d44258640140c01103403143d0280ca401441d03243da0600c1217214505062004100e034812108442d902c0b40141c640c8131b45068004900c900c03c00349c201c904018150b036041400f01041c0c2c00d8881134400c0455540b5000c6d18407a0b620300f030008240a16040c14040c1e00a400300000481c0060401c4c0c04c0303604a45070000103115040022020f80841c2c21000d5943e0001c55034243c0410b0001c003542c004c40c07920055401c4191500c0c0c0100817 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 777644235 1250 777642985 777642989
    0x307060c0e06070f05070b071b09020702090a05151c02010201150b0d050901020d060602060403180e01060c021906030e2a10111b040b030714010e0307030b09150c0301 73
    0x2c0310000b000041c0000700c01e400d0303480c421441201a6801140c2d141c1c13500945820504040e5001d03100000801c0c100e010014404c00505905141113003824060b4000c500c041e40003c01c0b1150480d039503400b027081c1059500c0c5102e40c0308030090040e0007518141160000c100c4040320101d0256003007a42d40411640100161025607104502070b034140301140704008050003010f815050707595400c002803e000f14060280344081d00c625001810756040900c3c0c01040700071513420072000080c03403000074001841d245020504443d058170b00071071250558000204040c1424660301941602c2440018aa5030150031111140e034403c4241c0b40b10441101036400080441c00080d41a43c511080d2100e2038a0201800d00e0a1600c41c0740000c8400c4510b5485840c3c600d203c20309420b101002d40c56040321b85080d000e18106402c003503000d0050240f400f11103003050a040b00c4058144181039401000742d8800b084120015604808521090b0500510132078480e203026200d10701c1405134500203055440e03801c08580c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 777645485 1250 777644235 777644239
    0xb030f03030a0c03060308040915080c0f060307120e0606120c091b040e04110906030d1e051e0318070f0612091b06030608010e03071106070b0103050307060c0e 70
    0x3141d6900e42d1036220041c42c15041e02c4003071503900e20b40440841e11a10140014107000d900001c4e686000581c0180c01840c9076002048a03404900120090340b40c0205400345980251a10303516a1075941c0c3c185c0740c00c00d41c1e20500403a98505074107100f0119000814601901059480030441c081500301581c5400c09001401d030441440004210440b15040300c83d402820300d141c0e400e080c2500d508804003030031410b480035510440c403007000310082d10303092010781d42003d01140100140040800302070703d4000303044002502c0041562000c0515801102100c034110440310440d0000e030803c2501c000707550400d550300c00310140b12031008510450000b5034031041d20050079200b40070350701e808021941c801555600101d42600ca0700c00a0001d0511001e032143d45c00310051480005040044c02022183e0750b601000b001e81c18004e51080540011044940f5250058031036085901c20380e000c50542c2c41800d5000384411a0007000205110001c03002d02070b8a4882c5001340701c1e155041404403140103400480325 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 777646735 1250 777645485 777645487
    0xb0f0403020d0201020705030a050d020c060408060a1512050303042303031b0d0e06150910061d03121201050a0b0a08340909050702070501050706110706020702040b030f03 75
    0x11001d4036080c1c012028451051048030082911100800d042983c100300444603a44403d040c4c032906038050091004952040d00c0032414a0324020388150348010180200c04120b56549140c0520300c1c80000240c041d107035055001c81c550f843d92078a103035281d104071416140781c6000c903160000c4404c44842c000841400500442c1507031901d4400080460300082a5054403400700241194605540101000f02c10130f0805001146020700b60442d002442e90080c9100c7c0b10a441003100c0c0b100e0f6840c10205030340d00780c83d0850030b00040c650fa210406410003445a0702d440b0341c00c800e070707540d09034000207000c103500d94504135985e1303681ca0080c045550020300510344000700030712100050611a41245510007a010007114120500e8500245e0304081026802c903008014041200d00d5034005552200500c4507140030041d034913004500030f46803d2540901070401c0000a02d0600340240d5421017450006480f0344569a0062807910034001d5100c65000c03401242860045800c07440d011544071201680d880243d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 777647985 1250 777646735 777646739
    0x1003061d0a03050c0c041a0108060405061003090203070e01152a03320306030c0105030417030601120501080106090c05031003030e060f160605010807030c0e07030605060c010c090b0f04 81
    0x3e4429400610a0300703082c0c4101d1540d100d2070f030389501480100d4403200f11f42a401750144800104040b070001d103100e00903030902d0240461511134003503000f1103035034503d800105808140700082c2030000c40ea0159544114100000c90340551124040c2566103544c1c6409a5880d0b01645101058401401160f07600d03240c0441400424041e1800d0360f24008802c0741ca8110000c04201e00708a050301e418440d1100002100f0000070b070804026250001c00c09003001410362500b0f135104100d40c81d415030340000100020002c07512a900940703103c003454043c118140400d60f1560011802070130070f072290040b03c2e800c01c9040c9807034600840450b40102071190781410b01508588060300c00c0e81440805030303086001049078955140c581c6026124180b101c5a0b1002c03070700c800d804c00209642c0103820000058000a2081000500356031188084440c0d0498134407440da40c0082c168000c000131f51007242c026800040142c100303030040d485845040c5403501c03289601c40c3c440d01034402c0d82c002c1070125250450100700c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 777649235 1250 777647985 777647987
    0x801061208391005060a05030304091d070608100506120a0507050f040b040e180607030b0315190c0201021602130b1c061b080f0411091003061d0a03 65
    0x20b40032035290342000000c0c60100495148000d0714041004645500900b4000070082c0c0140103064001034100ea03c130b4012030400740002d440348240c0c4128a0a10b13680c10301004007100c4060006c5858013140181d41c200c6540c0c09019007080800c13031303103008036030811400861240b074180c040d40c1000e076504000041c4e03951100c01ca08000c00002e00340009000c3e0600c1340c40d080302c00500003000a0202c20000c103032101e02e85100ca9415a001402c1e440a45085002c0c49020920000300c090f40804c0700d180208551580310003003814489514240c3c0e050b02c1000040240c0d18403c42140c210700c0301000420072000346440d000724201e01690690507105103026256801519103240003200d040c85501c0001014801c0c94001000d1081e03000c0180b6810349204402010300406200b01c84101a0f40341214100e10004080145081c5e40108105d9070700304814049400d0005040c4442002800a09003412a061501a0940d01d1400d403100711039280c240b6414602c0c0f0b00d4903140d0b4191000784d510040c507003031142d0350b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 777650485 1250 777649235 777649267
    0x1116030e180a0b030f031b06010801020406080c0f0c1605090f0106020705010c0206190807020f010c02070e090a0501060305161409040807080f040605071205090d02061303050a0c0801061208 83
    0x543d103075041c0716030034110540d20818801010688003040100784c0a0540710401400c01005034000344141c8d02c180410031026401c540001d9112003040c0000c5d5482185660303081c1c041c020504001218480e4a03d205440d40442c491a8159242110b4032040346d5100c01200060803003d001d000010b81001404120a50045000c850340324402424503060052000492031002d5032120f803000000c40160604c01283d4043c0110180c0008400090002141c9002c000e5541c0e510303403045d0307140307001030300b0000d0b808003020303c080501e0603403010080c40125520b003080340d681c03900605038a07240c0100341c01c0054008921402580054000b03064580c00c1e5445803100e50030758000e00410b8850401c20400e40141030040c40c001c10280c2890340310280c40e0119420403c0c0751032142038140c420f1000400409003580e0b02d401c01e6808940d8101c0e0444c0e0343c2c464a2100086142d203540c0028003621a5400040801030900301104c00c1d20b10700c9008002c0e403661440d11020445082030302a00200e01003044145c4608148 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 777651735 1250 777650485 777650501
    0x303120e0a022205100e010e0108060f150301020a090509060a260304050d03120f0b011e0509030d090314190809210f0d090513050405011116030e180a 66
    0x10101c0036020340f0550180c05440c01280c014030300820342c034000e001c0000c2480802d400360204a80c000d640d0b6060861055075644c01a0600e1104205240080c055120710f04440c2d00b2a10040c000b551a261405000f42c0418040e00820b4070590903000040c5d25401d003299203400300c0380c14403170701da03624040210030580c51059008020914001080042842d0f00c0d84c89092030910320a988207140c920094480700b003203482e141e015001d0346051454400b03044c1c1e071290580b0014003801e072200c071000641c541706581e54403521030f006415001d03510312018140d42061410045034043c2c404401d04200040140c0e449800c000a02d650804042907010080f445aa0103441e1103000500700031105101d040380e0080c200c0400d84101800c1d070104404204804081c411211142aa42865081c8904117030001d5424144500c80000c410358490002c1c0900c0025040400d55410000c9995640c80e200c1000a00d40c062403542900803440c01e900400d41030400c122892043d4049034130b2050161034107001c0e040500f001c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 777652985 1250 777651735 777651769
    0x40b030c060d0906140a050906060a03030e010932030d08040b0a150902071208010602030412081b030a14032503020705060c09041107082a0d02070303120e0a02 70
    0x182000c000084aa1003a01560001c0c06549001c030303d072645106c0d081c0c50001349090419000b0364140000c903201c841c1103078107480e818101290307113140d0a001291207004c2507005068000c1c8580e085c40c03031100e055000081480440c4124450090a2024541d4410196a40d840003480020000d0086000d540d0456000480c5a0002c5141c6030009040b03081100f064220300b0385158002411800c20044c01d020b0b00e000c6000307041000b955890a0380182d100c0c00f69104045000301c4010803181080000000c4560744c481884410920151854440d99240c00c80c500000105c0c88410f01e41c0002c5c02100d0540f807003210000d04003407001e009513010803176082020f080e1206043c1c0910800c00010707000d00001c6e2045009501c0c175a110001a410070040d00c1940ca44240340e00c10401c00c010103d485c4400b290444903400380c1e140b0071140d2146441c0c0d40a003800c6400c4c0072070b0260101180c1110703804038094003143c1c026a240d41152840981000c00c44003501405031003903010040360801030502003103003a410014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 777654235 1250 777652985 777652991
    0xb01090b03120d020a0e0315040206030a09050703150e060f07030c1b03030b150a360602011e0209060a032c030301030213050603251701020c0606040b030c060d 70
    0xb0681008403540000c02c103844865004500654202d07030082880c905000c1c2140200344400c115a40c4407e492000360000c0d0044200000003421107065030084000305034400111051680d60741000440307014214036000d0118103002854403110360014125005030540ca0f411030316900d4030607003680100104034002080c41140280380b00c02c0c105415449050600030380b00818580c0d01c110802c1501605408000c400c010140050154190f10031010000b03a40b440c0c40180c0c10031000011100c40c0d80c2891106641c07043da98801080706130341900820703441030000c40382014040c1d071440e4000c142d02a0710060f6030803280c148070b2884028801e8020312606e06044c05049041d1002d00c003030340f03c1e40966000011949c1d00010040045081c0303c0d4403080c20005080d005c02650a00500181d1200d0400201001011500000d16000d101c14607940c030086c103481441411013510402c12601075041074580071030601a44000de0441d06003402000d00e40b4a004001e44580f5030391900304a40b5800076a50303e1801a5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 777655485 1250 777654235 777654253
    0xb0a150e01140a05130602120a08060a150f0f080c0d090c0f090606020609070501080112030212070b040203010e0c030304170703050d08060306010f150f05190f0e09040b01090b03 78
    0x500c0800070f00144001d036842a94808084a50700e462210540c400400c56108036420142c031202e00d01511580e0140d4600205252035400c005002090345400031500449000158a219900100c154502c10017030345072800e0364a0089c0080e0361040c0e0469800b0308111041003003400c0c151141e030001c43c085126a001940041e2940c2080310b8542c00781d0082008950f0340c030400d000003a0100076150f0300c00910001003058a0404000810511041c8100141b4031000c4820008040c000e029004002c0b401a800d59202c40c804e091140e1240d5003940d040e4000d5103000c2c500c0e058a0000301c3c1034a08030001600031440e0030b00c0c080d054100120f0b052120401402450300105c0050406e10108842105954800e60384d403c0a10815007440810b900521007007103540b1003000386516141e26100802001e041a044d80708008005a610f4854131640840e0701705486041281c8a400144151048620340d8641001e03607041c8041c0b115041d400c2e18080c154170103a400420180c00160411294200058183c0b40b642d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 777656735 1250 777655485 777655517
    0x206060a120b392106030307080702030a05010c0513060201090f12020f0a051018031e092105010c020f0c04051e0f01141e01180f080304090b0a150e01 66
    0x1000c40420903500c000121084c1c0b00e0000300c2c00c0c2c07883c075040201580c158100180069078030311a81300010318800c000b2541c1410b40d9401d1007505e0450740c000000b0310501c6082c50300108030340d2000110040c40c6540310400302e80c080c4144100112140c2c07251050000780702c940c1320445503500d442c1d820803c40c4100484490402c900340614154288683c4c0100301010768600d0590603640342a00d540901020300c9004008a5031204148602d85042d8a01141c1c00000d03580441b40568036800802c44200035a404048400e01c40341903030034041c0158002c000e1018243c400300c0e191025000c000403030740d200000804d024a41a0f00480d000300c1c1000d084d20031510152190750240f442214105030f01c07200e04004000d0007869401620b1001d40440341102404d4690081c10400417102c1c00d410304100e51150b0342e682074007461104d000074040010302a0303440740e51112126036036031080c041ca075001401d00e00141d00904040d03105006035a00308080c20715030300c1e001c41c088580b00401c14201d4100880407081252103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 777657985 1250 777656735 777656821
    0x3051009060f09110a08060601080403031a0402040612060e0c04090e01200d06060c080f2d0409180209130602070606030614060a140f19060206060a120b 67
    0x1041c0b186002480130720003002007000d4032500380e00003041500054100b118a0303074014191940103038541130000e07121191405103c0c112010300b02e03594105200041c041450303a0802c5c0e102c4400d8050001c10f0003140e03100e9061802c0d09806544280c80c4000074401031068000da5040150341540c13840001520140611045611101100d0840e401a40c0021401c4c0c50060501900d03000c2c00b082d0030600460319895803440128440c1120074030301040c0100b061700c030480440100800724803030303201c1c04044852012242e40d49648144507000301d0300d2070302455907206007020000d0300801d500102070081e580e8a101e0101c5002d040c103502240c66903800c21200c0001145445003a0146004000000b01c003a075054045500b61800f0344520f2107104c07004400c001c044a010b8034420303450800c4d10041d820320800d90101d401101007001c246400e0040110104800c2d0740000c00785d125080480f82800c2e056a00d04005010304500240a40701900443c0003c50042100082024201e118440e40e940c00076500c1c0f21f50a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 777659235 1250 777657985 777658001
    0x91207090501030b1003030203070204090f021009061b020a0e1e040b010603060503030903070618050301110c0d050a02121e0c0a0302010e01020c0a1e0c1410030603051009060f 77
    0x35640d5140103005000131010120b600030701d0028882c1026007161006540c90017000390083c81359440d40410340c00c00c6100d41041c18000d03805003145090070002c107005015a0428041e00001070380005180c7c840c118080700031483c158010f03101001881c2071040300190602c1c0149500d818003901202c0b20f051004c0c0300756840c0f01c1c40c040c80f400d9400d9410440c0050660703042e60f10061184e0f0040c00340344102c0d50040b50f0441102c040d41045c2804803c107005d0110001280d0703203e00e03450b507e024690140180300390b004008405010080d03070710992402c907081c2d5060003905400360040c0d00451a07a000700a0980040034041ea04000c2e14465a01c109042d01481d0b00604100031b15070000a040030030140c09001385002c10801000941c145040c16940660b0b41e0200400a020000c40d845030030300c00030301494140b040640211741d005071251580009507070003465162450144040d0326035000c982d4400d20401d415a503005e03002c1c1c20158120500140900303035000307080c1c0c0c01558031400c4034451140c0740700d80c8407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 777660485 1250 777659235 777659249
    0xe19080313031a2502010b04090807060606050309060c03090705130c03110301080d0c110603011e050109030312050601030b0402030a060609090c051b0c030618010e0d14091207 77
    0x1c01c90304601d0301c09021400e81c100c0303c0500c601c0c00144071040c0c0348a150030381507003d40d00d1041c02c001c1d8590412800b52010314603240d003080c90550314809000022340205a49800703040c3c14841d259840000302c429120440307109034960003034030204d82c0d00d0a2240003035070802d20304003c4502d5280c80b400021580c1c6000004065443c0c0d640302c04044c204d0b050b00654071103101e44c60b8410309546c5001c5400780c480c0c8403111840c0c2007000d00000002089000400b01c01410300c0503044c2d07a05c03503860b096808100c000c0502000300d55982010f00240c0c3e5846144900181e80d459901c904d400511f21034048060300e40501540d0500d40c07110503114040c1c945201841c41003141200200741180303000c00290024000b500407411550900504448242e0040c0c00c51719007030a8100703a141550414480079080503200000290706000b0002845004500c11040d001c0d5241c42e14003c02507000c0c51840301340d8561200e580f15000c140032102c50484411003401a06050902428240c4044800b816480c21315226400200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 777661735 1250 777660485 777660517
    0x30c050705100f0219200103061805010e18190201050705101d010213050105070c030c0b03010603051f060e03070305150a1103040f0f240509060601020109030e190803 73
    0x10b14440d03410001c1042500b5a41d51740200030b00180c8800511440384c4900d44583c4c182592030708210307440ba0b44101c00410140800720001d124000050300076003000c0c800c04218100c08408a410f20301100e00c4600c0904290008200200e1320176007081001c01421002d0303061240600c100000f048051003039130404035103100005613142c2c194401d2600c035010784203900703c1070b0b2052000c80c0d024140041030000391a82400e24a446a0701850144006072841d04010002c051918002030f88c3e48030580510305940c42910700341715980c0d4030740d009901c9198001c0400b4000f0240c4604020301809a03460510141c0007905076005a03031241c503a24603111861010f4450044584108803086580380f2415030100daa01d2080740c44c60130f05807141c03001090900c50180500c1c03003c0e84403400b049480040d6000c0d110050000707442e1040c015203103000904045822000e54000c400c0018465881803094061141c0e150f2240307038410070014240056805445405080406081d602203040c2d0001c102070504001510880 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 777662985 1250 777661735 777661757
    0x15080108060106050c030d020c030403051209011d09060409060b060c06040506070302040f060f020316080717040b1e160c080d030c091205120d0f050606030c07030c05070510 76
    0x3091800405034000720402c401400403140c601e0f000320032a12003800301c01c03000d6112a000300c101410340c8140d60004080d031113007016040c803000d103102c054080c3d988262941c3c1c0d042684400c442031050001c4814541c800500390000d8070030724041d40404410303402040700049400c00d400c08203030f280c1d02003207040342d003588010b00704000c01c0420409a0360002d0f0a190950070700f4900750000c440129180101c800344841d001c190100b2520800540c3c1c0d0b00881c00c0d10341c0b0036080050600c00ca49a02806090701e140040640c20221489414120b50480301026421440c1c080000c44401d01c214407a41100380c110001c2218490b02041e16800070046030144000d603101c145400354683c0303003241000c480010f15042050b504040c40d08189a501112401440e1f05c0c40707039206203003540c00c1050444000031032041c0400d40341c01e1400140e01c20740400380a03500070892a16503104101c164001142d42c81c004507010020280024441c0c821440004d10440403506241e4403000003c5200c240d00e8554400580c10b03901e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 777664235 1250 777662985 777662999
    0xc050123031009050603010b0d03080c122401020c030d0e011205071110090308130f0c091d06130305210906041505071205311205040e060d0804150801 66
    0xd46500500304800030030823114100080390051244001c00b41c21b00c030342c0c0400100c1c0d030060b00741290715044580540309010b241640002084000c0c1c11284c074880204111349407060350001410801454004005010902e0740f00000c6030342180340b0f001281040b40e4000c20a101060b10700819018040c1d6880d04444c580c4010b000916204400101148040c20103600300d0120390000d240940102900e840c0380042c034480c0c00d01c00c800710802c070001841c1540b00780002907403042d240e000796500c030341d02e66445150a01800d00950b5036401610390300051856003000d100024003500c01848082c7c000e0404070041072002d8000345984100311403400c0682c01c001d08100802009240d1455216084d030000c00c203600344500018052040c00307141c005c038580c1e07500100e8500400e00b00c864040402e2510001841030004040c102c050001010803180401030410101100d805941a2815141001036101c0c0700c0d1340d644100700e10000c0c1100141e9084c1020070021400440c4006070261140c0d854403181407551608003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 777665485 1250 777664235 777664241
    0xf090c0215160e040e0a0c0510032d0618060620100507201e06070f0c0f0c09050f07050c030d02071a010f0806060d0c050123031009 58
    0x1007a101100c03401c003001000702c4030402451144006181a40394808030342d010400a19814504607018460344019504011110703080d1416100140c03145c0001c9042d51005400b5a010304140c1404507416450b4100c0c01e03041c800420403240b1a07c040842c0541e42d4040d4000070011901c171150803651680c00a019203034005044800708904100d8011811032000c00b219160090301310410400d544550124035150710138070a1040a0f401d02031002c290840c0fa2004541c0c4842c03800e034802c0740031100c040400c0b056601107a0382c1d100346802d444030b1886101100c0111514285000101c403007050030856500441d00ca030400c04083c0c80701410000c3c041c2000464009070b00340080030030040250800074a0134010010080c0c407603000c2d0750600541c403603041e0324003038080400306040881c840480304000504a4060008102150071850a581c0d541c2c43d0301051006207949408087c2a082d1054005c016551003500e40c84400b0180b0708016070001d078803e0b0b00403120b51058507080780c8a07006030420300c003050441c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 777666735 1250 777665485 777665503
    0x9021906020706181401050a1e050c0c060304050a030c061413031b020a210203030d140a2d0b13020405030d2f100c0207030b0c030f0c0d060f090c02 65
    0x4d000c80781a01c0c000b6818401807840d14101e0402c0b90101d5071503a9140a20b603000c0005e503860130980c02e1100541802446600801c6d4418114883c8a00309942c0c1e050080031640981c0c0c0100160580e501240ca081c0c0345203c4003001111078075660541c58400d90460300c1030a0003143c071a041080700e42414113005207455203101020300a0410304621400695800c00305900300d070080304090285c0303103030784041e40c24002e042c20010b07406000005a010a407019079105d6804c05139440346c0c04400f0b89454404608584147d109043c04140d0a420f00032010303034904400060140500021171136940e80b001188100c1a1440c50f640e009401240600c401c1c075042c010b600080d0360a20f80807000c0110052303091400c203502001c2c2031120241185520220800313000d102a008481720041c4503c4004040c000d50f00e0b0301f42d1109843c2030300498007103544000c42a00b12400344441ca080c02e144c030b80740c42002120a40c0100c0360307002d00d40e544910010f401310007811010001e2004100001c1d0300317044d014000e82045040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 777667985 1250 777666735 777666767
    0x506010f15050c070501110703060e01092f19092a0212030c0901050c06010f0905010f060e010e030c1908010c0e010504060e13060e04060b010f0e0409021906020706 72
    0x3400f11030280300d40010000103c40b02444c103800c60481da42036003404c2c801d2503000905030340e0900300c11180d040015080507044500c140d030030310320041c3c00a0500003804092115102c0d90309500d00701003003030310301038810b1207001e50700c0310108004594554a038003c0360b0380d642c000c6c0000700e648410261aa41c69203c50121000d450010f08010032802100ea1414800200003012442c0041f0702c140b0664406c400792400060307040c04480c03865071116100035091950303103d10308840f400c01002107000c0c882c030f0b00d10341c04407405515107200c0115008019103502a002c0411a09842100e42130203250756807001d500c00312001586c2070300145003401d0000e400c0d21251140e0201788602000343c92440d0740c1c028211404c0b100c142c6401b000c0c21403040b00044020f0b11455115110324200100030911810341903205004600c03d400c01c0196600f600010748520798005007007004100030026001c030300e0500760020000144010821804010201d00c0c00d914289140c100c040103078403400c02844070380d8114005440c1000340f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 777669235 1250 777667985 777667987
    0x3050702060105010903150914070f050d02130218100e010e0316030210030b03070b0909161d06071401090b011a0a0e010509100f170c030f090a0506010f1505 69
    0x1020f001814058041c07000600703e1000314422134040c9501c1c5d00024902c7d81c80b000f040c0500c643d00342d01607500d40c80d074000c0c8003110030102400039403403a00b11003541c80070b075000e411410440002d180010003500007103024424040081c3d4070340580c0c3d682400d0803c1800c801c0c0c5900800010742400180b48180b00080c1c98000d60241c86901c04c080b01c41517005080707030341c102c0e4441c002c403810030002c90181c500c0d104e02c41e415205c0c2c0040440c072107107180c1c05003500c2c050a480e001030583d1800200d09a4410482080001c105c4108042c480100303c080341003480b90014200501d05551652124000e0640710203580b00769640c0c15688040003040c818440c018018200700c0305c8003004006c1c80a14505c41c1c0c940e140305102403d41e01c9110303a406481510340d4800f0003044840360318403109015000261101ca910005281009920021b41e50010042c0c05401c485180318107540d43c0e0701c00144402e4020b8501070240c4501f45083c40040c0742000300e18060540b41103000d442c540340402c4140c0700c4100540c0f8100307000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 777670485 1250 777669235 777669239
    0x20a120e070510170103030507060c05120105060a110723120c060915070b040c0906080709020a02031e0a1d1309030908010e011d03091f120203090d030507020601 71
    0x10000d61442610380488410164000d40f10702550b92031100381c2d5403281d8120b0080008149a08031000c0c100403805581709000c0350700040000c842e6485441501c110580001d0010b008030304000740981070103903182c1411082910004452407030080641c0c4441d0030000400d821030340c5242c280b80c1214102038142c81d100c0c116440e00f03c8164941d074083c4c44140c0a2000400c0a1a8554960000383d0300c1408200c2d040d55204000d0034016001c0408840c10399000e08030000015501070030744580b6048a403404068101c0505084501d4040c0d44080011b0302144014001e2a00140303181710400c82c01c0542682d41543c840070300c40c003c3e16404d101842c02c1020b50004038040c2d015100da0b035003280d40601d01080040e20056a103016a0040025000b11100c0d62a000c1c40d2105070074158003031094040707103111000c07500c50ba284600d40e40e80f261800040d0400c160100060b2010800f17010640b983d256800c015a0312012542020202c0c0c0003194441c030a54004030082c4079031609403050a0b000701d07080c0302a01c2c10398 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 777671735 1250 777670485 777670511
    0xa061e211e11120a0b092e060902031906060507020109050609010c050f01090209251b060903080f060d0b070c050a0b0708090d0305090c092701020a12 66
    0x46800d081d0203032500d0720341c012501046510101480e20315070041207141d84000402045695a858010882e11461040b02080400c1000600c0c01e851b000000820303081e203411311a80c50f0607402414041041103441d000701184160081c00039500c186440300c4125400c0b00250900800d89841c0c0e4030030340500c1010025080540d030311455000c1529000c0d02e56075035508810004130341e0b070f01007000098a6400b8108112030818419002440100c0c000c8880c0c0f4a00e03143d40c0b00c101d50200340c51142c6100740f0151801103007090700400c0c240540c100c0c0ca00058a04c002d8a072100c009844450f070080300080d021100f040003021a009107103401c81c0c0290350ba0200790700f0030380c5d400e01407074005080a030030303c55414070b0141004010489403010f03590110b0b100603607084c900000740006105179144011401f8900c03c0c110070340c4c0300b8031406104500d54002044101c2d15131082c0080724002500072844484d4140d4502d4102402e04a000300c51240f60300010390740d50403e4401130042c06100c8540803d103042500150313183d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 777672985 1250 777671735 777671753
    0x1c11011826030106030c050d050c090f0108010e131415010e0a090f140102040b1b0601050d05030405040506180f060405010803070b19090c03050c091e040b0a061e21 72
    0x150345a1704001030500103e9209540d14051031064000b06403c000030066000c2e030100107081801c030140c40c0103590b0f092100055451039800d028020a0608040018802886c1010189a0306010b510005030022011007040e00b000301070345005800340c103140010480103841d07604203940112081403c028002072035032a10b00000b407000c000750011800c01c1524101020a40c11039004080d252041c40c1c0d100310f00329412100342c81d41c0c0510038040c051400001954104a00500d4000354007a01452900303042504000042502500c91600000b100c1580e40c44d041811141034015403614040f0801c1e0f01e400002c1105884050f008090250800c4c001a000a040008c54039084501080e0441003642c035040c601c0010300308808040c0c400d0759140b6001081c840c01040c040040030094030541065a41e0840311511411a04012220600c90800240100e80c208980c6034200700d102c40089946580d4031618400740300d10034010300b0f4000200d2001c0089004813521844ca0500703c1aa0032030301e43c01c0d0340300da07920 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 777674235 1250 777672985 777672989
    0x17070906030f151d0f010b03061b030c070611180307060906081902040608070810031e050c4203130804030506010905190b031c110118260301 62
    0x4103400c0f02455840ca044030380c10529044140c0d005075082d080406000c243c5d03590f180254204a546003c00070602c1d8100424020700c134222883c801c054120400007090a00d901c020a80586110103014940004215001e82101041026102503d41504602004004010301c2c40345200e607100910400030a90001a0441100c0c11801c083d6501c1c1e90348084004184c42c4148004130030b07840018085038075504019040e0040c0d91580e0707191442d6030388050220940f001404090b0242900c00c0601d0751480ca59024403003510b00c11030540e00c0300c4000343e000c529200a0710072030300c2800c859119400c2512a410000c2102030507445400d0340900381440c521035040c1f202420b01e040d82140f00d22400d0078400141c088400031540401190003647e90354102034018070301034a01c0100b85980124050420000d40107404052500802a1000d2441854a004507000d0211a401402100c51004a14050a00c100c0e04500f04075064000480c103140360200b407081d2500080c881e03104035020702c142035a2512041c0d0341 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 777675485 1250 777674235 777674243
    0x312040b041a0121030903140a0c0603021e0f121009110909220b0405060f090a0b072001020403060504050f07080a020603071e1805010c03080a021b03030117070906030f 74
    0x4c0600b41070404841c2128544c1001d0320811a98111f01a10500001c080020170300176002030955a403545c40443c1684a15030190840c600c0c00309020b4600d8030268010b045036100013040624001da09810200c503000c1c2103803800350443c908a800c0250b815540502003080010001d000c0c41c1c1600c5030002100001e002c0c095103050000649501c1180070301d1821040180e41100b000d55a0f481c0510302142e40b2802101d8019009482c80c01140710040005500017510341e120300007015075565005d08840500200030340c10400803070100907454910082c40100069802680c0210340c42c9024102145070008400c849211640f01401c10414808041125841950b0440342255a41c5130480111042450003144206401402d684011500d801010000301d540c040f00000220b0782d42e500040da090000808007a0200fa401c4000482c410807a074000e160004090494100038000c000c941491034009810030800d8852030100c1c040d000d801004050001c1001d000c0a010306030a40c2c4c1d4184040c088028018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 777676735 1250 777675485 777675539
    0x1c09090b04140c041d04121112131e12062a02060f06010206070f03020d090b0f1008014d040f14030a080c0312040b041a01 54
    0x103025a6403900911000c11000a00750418280302c03610304600d900c5403040d40140c51381d4150780c00035401e80801ea0f900c0f4640041c540d940d502940001a1503000f60503600d01114003d130b001240b1400d00400c060094401c8820070407140d503081c0b58101c1d05c9118a8074080101c000c40d40c1d400c011072003151070121a101e40c40030b00882e0502c5502d200340e405141018001c0000070308000070304d1405600103041031181451010342455601e03908010f80e01e500c0b05a03441c0000800d19403660003186e0081e0001d2014080540300040e461507a40c40b101080642911015290040a01844007500310840050f0107000020003c2059105012000d1000e05403241c0401c050130b040095807110382d4084034001104808601c0b280294680c940116207590300a00820300840b02204000c41e40d00d0343c44200c2c213000180035008240a03242030300c40e641d071074200000781e081c01d10041103410010304168105e140079510a8003005400c0c01d00e40342126201020541d4241a4100380004101c1251a0144a01c00343c010000324 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 777677985 1250 777676735 777676751
    0x6060912031b070506310e0a0b03103303051b09090c0d020d020f04092303090f010827060105010f020a02010c080c010905010516031b2106080f0a051c0909 68
    0x621190020340d884140c9655907c4100b003c0031520782c101034090403040b000d94082d0340603451118211201080010300c4c0c10464412085106400c4440e041036a00d504001d00b021079403691614a000c1070940e050031481490440841141000304e040340d0029007040c05001e980c4801030114004407101d0700c0180c4240e01e8180000c0a54455840d109002d41018000344200e01c603504041640491203100d69044c43c440c0c0b0380508281c4404025104c806600030440e80364039000c4401125a8000601441901044a034103054030701e010007408070340c0b0b103400030241203950b1502001402441030305a000041d500200c52550040c0c3e888940303803110580c8402c1c0c10b500d4140c4410b0301d600520707400800502940c40c01c0d060101c1c0c0c1c00360f080454130700d02c41581c0502003a101400d440a07003a1003980c03100f0209000d0081c00c413000782c1135031104840e070b000901c00040899071038840a01c1d000b800c43c4000ca564000103110002e22005015800c440d03c2002c1c2c02948460034a00700400008a0340700d4040140d50342d03008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 777679235 1250 777677985 777678067
    0x30f0d0f03180f030c02010206063309030d03050106080601050a020c0415120308250c0305032508040309090606020d1808060717060f0906060912031b070506 69
    0x59040c4054110b0140e10880f107503494050011103220100b0fa0261048000142c00c0d450202010f000c00030f4104218800d80d004401310481c45c6803a142c0140c020740050006100c1c9441c20000d404410b0318a40e00801d942d40341181c06016000b001d00311504101d81004a591380c19000103231181c02407000c0c1e800207450360310707824a10020075a075044031411141600800301419030044909015484907010001c0c450b0b0006c3d4480c0703d2515107003e06d40451403000145000c41d0142c00550b0b8410404100300b070f1014402c042d001d0703111080070304110108070608284424154001c422101900051100f002031a052482c06507407203541c10b803081c00b002408800c0d0903000360f0b01171040c8001d1981c00121151400e1900b03000e00241c004030740c000c56240c10000000d4840c03400c0040070740448800b610300c41103070f01c0e4003040c0200b56000e4241a82c000f0035001c441c1c2030000d001c1000700035072501e80c0407400c9209035109a0a0410040b03902c0103105040a000d0b0403c0b070301c83e442404032490000c143c0074500f02c1003049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 777680485 1250 777679235 777679271
    0x605030f040f0c050a09060603240509130602070f0b0f0621010e1c1101180f020315010611010e2409120307090603110a0c0212010b060705010605030f0d0f03 69
    0x26540007a98885d00141d031941c65000041501e49945080c049030b01040070794200c41c1025503500c06c03441412601000942081c0440b1508550410039a40e2804000c3d00c440e41680c0c401c080803501c440d00c05000b207040c40040f20245030080140c101041c0c440c10490001603108984c1d07410b15852303210116042090803803d6100342c010504200a56200c21042580304ce010700c015006000428248030502e95000710604c90b0007100784003510203101441190308c641d804000c0d860307405c90305881031350101008411404800750003045a82d85000c0c81c4014070480ea401e44241b000701c41c0d402c2e4058480c1e20b06241e848000709507a04c02c1d2222203103c0356501c0c502580f400a100c091070f810203900005015040b0b600200d80b000744d8000b52000d0101c8010a812490144520702c440700004041c202d45c00300515012030241e012001e50f90000c62414002800070f0302d42d03070088108030384980d07460b10f0800036410180001100b0141d888041c081d000341156001d4102c90402c6519401c055407140c494101c440b11007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 777681735 1250 777680485 777680489
    0xd0605060f090a0504021c05030a030f021b210705060c03040f0c0e0402040c08090a0f0c08070b0304050c0a080613030c14030c010b0a0506090613091401030c0605030f040f0c 76
    0x10009a60340c00c00700f82d904002c000c20344003680a0007070011103060414800222135a560380c088021803600301d07000411002040d9130803401000c0c580030803100702902d800f160f0707085840035864003038107800b0f0031500b200095054140094041c18400c1c807010001c43e00c0401c0d0241d015042201c10351385da0f500c034900f07514a4240003100808002144202250b10b40030108064841c0f84289ca0411103039804900a80d040141114680754903030110714440d0010342d881c0c0c0d84110b00d0b0310841d030805229444910203418642c186d0007c41c0f003800c0100401060110030801519030200c280e4003100307154140341455440d680c00030300c0d0031460f0744200051401c01d4071407a2401050354100320452446280c4900c0c0e50749903400038103c03a105609100c100d502c0c52074414201030841d40014403c614060501d0148403040d0444100800c41200070f1200103000b010074000e000c0d0403501000c111510750305618004d1050201d03500044208202441000344000c40041d0701074100d83c009181c01602d82007840c0c0094514215 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 777682985 1250 777681735 777681739
    0x40911060a02071a042105010f0608010207060f050c0703110c030132100504090c0f0b0910080112080d1e0c1119060b060c0703030504051e0d0605060f 66
    0x1d400310020394041074079001c0d5149072540c08824040308013140c0c1070340124020071039884d8020884034403060000c0e21081c28a0321800022511405588404003120943d81c00030403541d4002980d0810400184542000310245900820490514105000c528064150001d0600000e03080c0c220824a0400440c44800d100800a200038140b48004d00101d41074100c0070f4007200e8500d000700d00d01480700c250203403050f04142c1c407088140c0d140000308400f6284c01da00c01e6130900060386011820441805005000d00461200c5130398421241052101c3d48511400000c1004255801484025505030140303100c3c3d50000c00440d100c41031010140000d05205031003400545c6480b41a0328100d805802c140791120894542d851199402d15401780c07260039140c0c00d0100640c041c4c0d1041c0000d509680034501c940e0024101e44e0a16a003100154035206003608160041007000c5800c01c00c40c80c1604100e00010782d007a02140da0b00100300301041c5010400d01d80249442e8545d400924a80c4070905040800000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 777684235 1250 777682985 777682987
    0x3f09030c050a06020d0f0209090403030c0e090c030414030f0403060f060b1216091a1e040b132c070e190f080a050a1e0218061002070b0904091106 64
    0xc0c03883d0020080d40080d0850440d941000c40d182881001c2c1e10035240c1c0305074041c004c0740550fa900e68044000b03110007124441070000c1c0c034070003040a446803c4a5403280c5c0d2803075100c654908040c100f05106001954182d2000e5200700f080800c0c0780ac241d010b0340c08580c0d200744042000301d080340c1e408018041c213400c000200700c0b001c103109007401440c1501c1405841c0b940e90100b505080356004a0303180804c2c1c0111f140c03c0540040e241c01084e080303030003800304500d800501001c04070344811491a5031f1203a40840003076400803034040669070380207500f50010000540050b00b07114801c03a008000d03d0b030098103244010425400100000d001d240c02507046140240401da503200180d00710320f011040ba014640304407049100100c1d00450000d0200c0c4440d40210040c04189003d44c1c5041290f01e00035010740c05c1c00d0314034280c2c0005845e4402d40c0502c2c80400402d0000f549045000e01c540d11450000c034108650064200b003004032103040449090303113000d41e400308080095051501d65521000c0706a03400c071314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 777685485 1250 777684235 777684253
    0x21e0d0212130201090801051b0d020c0303010803031603090c092c01150906271b0e1f05031b040f060c1a100605031f063f09030c05 58
    0x103100b001101e0350030f100b603d884003030540f81e204060888900700c42038020706100c214071300f0b8500b80400240042074034101c001740c0350510404002d8219002a800761016a00c0030061110205840480600c40c5000346002c1120b601107846030522010544a50b1103d03507940d4944c201480c0c00320406001d8450046424240b0b450907080313490003804c5040c090021045010030110301d690281c0148011601c01c2821150a0000b00c46d03194444c00d00400403d111550350380c0c4188000040c5c00100100380d4040d107409184032010014880c000d4000301880d030440481504120080360040c0540303030410050f1440c145100c0f13450100c0a55440b4603009041800c03015400050429840f00002d0140d521600015489000ca2416502ca0a2080e94119000108010240300d00d920840141d94002340c0c540c0c4180d010740c14602c0440e80741d2a5600407400284900072010f041408094540340083c140e180d9903881d5017070540441c001310f50503403002000f040e01c0f5114041410b1290611783c2000e500001070710b87d664 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 777686735 1250 777685485 777685501
    0x10c080c060f1905100302060a1101110306100e13020903150f010303031401120210030f020c070801110a0e19050901090e06180322120503071401021e0d0212 69
    0x100c002c0391004400010070f900c00746441082e0040c14021310450101d026131034251782c01c1090542049a0007000c0000c0000054541c035806d025566401148200386581d03400c0820a01424854201c42203080c0044048045104d07100c45d01c50a44000055400603181c0625200090400910310b80000f0151054000d0000c20180b6500090480c2c3c42500c1c104110f501c40c0c1c54410030b02c0300902c034400460329032108210142c1005403803540c0800b200d140000310041020b4800c800c03a041551000c40d203a10101044c01050340034402c5043c40b9020980d02d1b81072005c803031801001905461552130041c030700c054000e0f003a070701481496005440002d051a45a68441c100d0000421900311018110703c110004503044410608007480f0021004000d94504080e1035052510419070340321140f04120380340c00c00108004107a080d41c900500c107002655440485003049518a00082c03200f101503481040081080710600b1030610140c2c0f0314011481d101e05004c00048020701500b6219000001d020301044044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 777687985 1250 777686735 777686761
    0x24180f08100c08041505040303020f0f1809130f0c030b070c030f08040f110f040c03020c0601090b0a030201140702030316031806140c190b040c150806010c080c06 71
    0x74204208001035070070200304858410013540c0140040c54a00c40307008901020b40c10090b0f01c00c0c02828054540b41821500c00140e80c41301e40354500c4000c020070a610540d0a40398201b0902d28122061141810f140c03203000713010081150001d10001000003003000708040f000a0000840d00300c0b05210b0301e4540700390054940ca850b01c804400095020b030420a4090185003100e0186803c4041c00913480071643c2d0b02e0650800d461446584060410142501c55556024910505903036503409602c460f48440361500c0e104040c3c1100c0c2000342000f080407195100e20403c442103a40920b045034030b81854000300c0f8040e109520000e500f5000020701c15068a89084403400501e12990710344800281807070140700f100700c050065500040402aa41a0a030481c101030002d590300c00b400d94540704900c001111800f201d14074100e9080f4403000c201700901c0803d00c11301c00208900e45400c615204c0c0150300130902c001c01040d1a061098080e20340c17043c845c0300303010350341008654021100c0b0f5040c01c0000f80d10b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 777689235 1250 777687985 777688003
    0x160e091911131a0c0d0f0309050a05030415110d080705070638010e0111120310050307060f090308070606030f0302010e100207021c02010c05060f06010924180f08 71
    0x8103c248201903014106098211103000c4503500151080e8000d43c20211040c0060180d41c3e0b00300340d01d80c0011b0307011650501c90300c113441e8801c100440c0c0d604d28000710748620440c0000d4440a01062211030501d00f4408503400f000904645003140280c1e5511b801074865000b40400908164a0640800704101c00c1008a8519410054a100907072007501a12142d50080720740240c0020b0f1003c1e40711907594001d10a120710810914183e64040400c1c0c2168002030304204c4d8416803910301c4282c100101c0c1410b0010710068011450318010310314001602030107114007840000e061090005200d800e0041e6075000201456001c20100e9000c0b00500b00280a0400b04008154074000c9611600400003a0310031038449a03070107480c0c032182d48107403640e04000e00c074280c505030706100101140301e0000d8800c1c80554031800801401c050182000700c00140928a41e030054407401690701b080317a50701c1030310918010842ea16032030244420074042c240345040d044241c0c060004142e002e40d000c00d0003e00030400c404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 777690485 1250 777689235 777689249
    0x1609151101271101050c15041109041a070513080c031b131802091602062d2e06030e0111030115090f0e160e09191113 52
    0x142406040401000b09059014510344010095030039000070b5044074202550780d014181030303082c0104110031a0402d407000843c892448845c1b000c00c800c0050b81501d80c030320030106a80c0f00c03980e80b6060352240e14240c640f04d04501c401d001d6100061003140300c0c00481d0301c400f020704030100040340e5450549598681e034840c0184a40140308540180344d01040d008030031031000401c19440c141307030349403004002e00d80409580035102c1003049441c0943ca9515200c2e00502c42d10609800100118400a081c1000948414042e05d00340402c980d00310b4074541d604441010080782d400140d01c500e40c001b901a2103000c0c51490411a440c1021007410070b04500c2c0301110000d4a09218496070010510700302c5030b4500505c0c0000c2010300051002509050007407821a186042a282a07501da1022282d61a80c4d680484c52009800081050100044440074a0b40084e400c000d00105890000a180e851000b00240042c60907003d03980da825a0030b4214a2030410704001140d0380700c001c3c04403148921403900fc1e0359 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 777691735 1250 777690485 777690491
    0x3010e0a0b523605040510030302100e03091002030d0e011512020a0311011106011203120b1807141605280f0215030a09060e01141609151101 62
    0x2c0d11031401004181c0000407910b12040d014030340a990b880d07078078480281500100c64030f031202103041e40711803244502981600c01010080c61a500c1c0003807070440007001d421000d604100c034006c0d10b00c20000c1910105002104d92483c1004006001c9186004001072400d24a00708078041c01340076130641c0007030038907032040704907040b800e464002c40790079101e011070020340040841d0f4007000412640e0600d12480541490400751501415140c01d15141081c4c10096460009442c3c207410507030041c0580f290a44c0d0240d06111840a4100080c07001412580c00301c841020301001070352a40c4200310301c011410000621541ba8a0510300c0001050030f04031741260b19224514000d582032240f10b4645070211a45042800da2a0569a070400315105041003260890b01c142d54101c8050300030b41c081c42c8540840c01001904110030700300341090780c40680450425925199089c812110341300c0e0169803002140078120705024013260121000805503200401d661900701d112241c1e6940039810341c5140283e10f0082c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 777692985 1250 777691735 777691891
    0x627040b0d0302340602010b010210111209160e1503010e03040b0d021303030521010b0d180609050601060f080705090111120a03090203010e0a0b 64
    0x40700c0030301c840900160160344813400041e1919081c1d8003c0511820340e0222101c00250042200d456020b42d07049000035075142c0001d1a00755a040018003c540306107003051118400b00710110206100304a08a01c0c0740209500246800c0070400503000307142448000304210719603502e07180b401802d080c1e4030b500c42454403c4558443e440c05004898004155002540c81c081c90124403c0d65584040305180b40d10340c081c0004001d035600081d46c000214003a80b11a95689451150203500c00b11441c9260340000d0400014841d000c110b10a550b0075200035540002c00e45081d03036000040a89000e801854030b03042841c3d4108008000c10403a040303d400c0d486d03010382181c000310107540d8201e08507540b20005074207112980c825031145c805001c40ba503020303050301d030107650042c00c00740c103a403180308a10042034488141208508091007076090001041c0040d2079a04e10942e101c00403000e0107060f032485602c84442501101140c180a01e01300720803c5141c03103409845250060340c04407040100c0c541c1090040725 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 777694235 1250 777692985 777692989
    0xb03130b0c0918090f24180c0d0c03080a05091002010b01020a030e01110d08100b0c0a030e1c030e0f030105191508010f060e0907060e0f0627040b 64
    0x2d0350102e007002490503a641c03541504101c0c01c42e000a10b4034506208100d80c829032040140a00507281141da910401c1d1804c58803402c60584001409031200410741d030606403460030b070101780c1840c03210086510060072040ca0074520740050040e04080d280d1500003920103100e45d00000140802d49003903c80f482600344180082c2d089503001e940c0180542c00c0340240314006441450052440d83d8141420345c210131440740e40a01e40621a0540c1d07011a0b210700511000080ea40d41c884d000709149280301e4604681d070071100b40c6810254200034280024044a8901950749032541c54401500400003089509581001807035080082000790050b0010340030b0384e55506041c0140c5104800d003090015171080180a000006d14240d100800d2440c00c0010204000000b8003902403201100c40700410b4440c28040c030040c601002404c1c0d0700d020781c0105030070003215070000500c5420f041d0840791058030740100c001285c031074442c414290044036041c2c440c5010712040c2e41d00d200c1d00683d00355000c111108001c41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 777695485 1250 777694235 777694237
    0x30b0105031005130f050a09140f0705040f0605061606050f01060e010e040204210606080708071206020d02030a02071109010b090904050f0a051b01050301120f03090b03130b0c 77
    0x5684211242e203040203000320704101528a600f080a003800050350054a81030170100d54040d1620705096454107805400d201e180090781051003012406060850005215540c0e21200b9103d0980642d4640141d6146880c055011000629000e00000c2d031764280c4092498000c50198070803913085107400013007820f5000307982c1c0c03041c162815900c4907400c1d101c6502c01035690302e682d0065144d2040d001c02002c50810034102151241c4004200c1d400d9048601d894448140c54a079000040079601840040103601700008841c002c5490b40f280c1c00d1280209810100b02034420038508a0505000209000300c03100b156004001c0e25001c0d0f200724002d00309030006c00880c00003e2264101201062101c010180b5210b40003940192040d0201e4914588402c3da180c00d010209400fa20103030810004e0041c02080301c081c1c1c503241e000c01d107071407441d44d8101110a0200c02c0480c0e4040c02c0314480c1407083d8100f501808000010384031002c8403949900d0101d0f603d08038054441011641c0d80c040340d0100700080d002d20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 777696735 1250 777695485 777695491
    0x5150d0b09010e0304030f06180c090209090903070b07080928021011061816060203030712060605030109020c0c031b030706091802070201021e03030106030e0c030a24110901030b010503 81
    0x12980003101c7c02640340c400181109481c42010325900c0020343c00041c0b80404000700805000102689820b039110821800020040c508182900308100080005108590095011a0b64103000c0041e40703c0c00c40251030980441e540380000250a1181c0c0b24203486460500070007482240e881c2901d981e2040101d03030f85d049640d10052158091b4000c01c900703841650180b21000302c04d404503900c3c00410401402d400440341c1c09500580c20001c2070080c81940490200c2c20000703101c0e0240451490030030300030110b120510030000c40750b0b40418503684160083c094409080001007c8809410101c29000745540c544413a09129101d418800144140541c1032603088880c20861001040740142c030740b40c003a600c0960101d046000e801000c0385100c00030f0300c208214401460007140c4a6052080c040d08441460012261540c0404629601940d00103800d004480e44049100310720508145588080c0c0815889109140c1c00c01c0744804601290f0307405440c41103001da80c10f0000740300c5000151110b2000f0307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 777697841 1106 777696735 777696743
    0x10112d07120b1605040303082502070608330307051509030111090d03030b0a1701020c060f06030d0e0609061204150b100305150d0b09010e030403 64
    0xb1402c1240c1c4040c100c10849900c0c690740c0400350143c041c500c001010061580001140b082c0d8180360703048811041c144440c140d25524001139201c0d401030103081300040340c000020340c4502c0c1c1c041040c0c110207c0302030300006607001d40705402c1c51070041c4407400381c151165860006083c0c61312159400d00e118021203d030307182d0138807804050170b503540307405215040e20051100f00420340d509a18500e0255050030005248a0900042034000d0243e030f001011011214000e41c07403d18040d002000740d0350b400c0c81501c44990320750010003854941900c0054040c0d001181c4400410f025100351643c40e0300040085050000010008029a02003000f841072003604d441444100155161980a0384181c68070a00c200000c1c0380100b44441030031400f04040684403008640201c403190701c0030300c2c1c1080c080c0c94802105500c0c104030620403010b55402c03550b90303c1c0403021158040040151030540e540 = true := by decide +kernel

theorem cover : BRFrame.Cov 777517985 777697841 := by
  have h0 := BRFrame.cov_init 777517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 777517985 ≤ n) (h2 : n < 777697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
