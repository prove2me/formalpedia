-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0766
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:39:54.800666+00:00
-- url     : https://prove2.me/submissions/525b4305-77fb-4e83-94ba-be17e80616c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 137589928 ≤ n < 137769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 137591178 1250 137589928 137589931
    0x70b0a0509060601050703110c06031602010b040b062505010c03050105040b01090e1603090501110405030d0503060102030d09060b3a151112070302070b0609040b0a051003060212 78
    0x2450400540c0d440a00003501c1c1c08003210041e000079020850302e030000340129109000003052000300d03040c0044140200388250701c282c07060094120105c40d890b40403030742400341e450310301d800740c2d400c3c4920b1543c4004102e050064294105c0c50700c44c0c01d94494020f4004400421a40d50810020b1140b208540c10113002130a080c003c95010700d040600e03035009035000382010350484040c198000c150340d803051098008500c01045520806445130f000d1800b10388240901c00b00c908c604002250340707500d00300405203800c070220100805d002080c000c12149a80100c181c51500c40e12a00200b042041d0349446401006181d1500d5440890b0641d000c030a85503020b1a071821255a00d9501c900c4940170300d803080d4548542000810503040410006244100e036041040828240107240b414940c10300d0014060010031118800001d601103810003c4c80608120a07410400aa400b0102c60030300c2c0e02e8044500000805001c2e0703d58643c4040b50034203122100000086070041411911820700201c0f80583d03290 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 137592428 1250 137591178 137591191
    0x20a03050112150507031d070618030b0601050328050106081003081605071508060114040e18100c080f06040c1e02010914101b050406050c010b06070b 66
    0x40c08001107582d210520030001030070b40144031466030103041580f0f4400707808010100010141c40c0d4004420060381a006130014506003409400c081d400d0240c02002d24009032408420320300c403540b0400101c3c040c0d0900340c1c1c01c02801c1c0b811950304e40e074125424001b081d501d200e05c0a01c4610022106603098564041c6058a916035a191a961910215199000c060f0300020301501800c2141c002e07550781c2c0c2400c8031811840789083d030f0305480c0d48801e00e09000d0b00c0c140d1000003180058040040f190f80c030981001031068090111424203003001300340c1107400b5008000c1e642ca500b100c0c65036000404200b22090031041401c400380003030111960010305180051b81d84002135500e18000c00d01918050103126588242966400341110b41c03042c100e00d4040e00c200110055568030000500804d00802c000100c80d8800b00042822510030b40001044030340d90b0403114064500fa40180300060750143c11502121100d180454862a020b0b00031801018000c0a43c1d034840d00c001103502c1042100a107552181c01d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 137593678 1250 137592428 137592431
    0x1a070f0201051609050108040c0503030a02061f12030c0c0905010807051509010221090a14030606010c080f0706020c0d0f080708071b080c0a0503040807120507060305091f020a03 78
    0x71281d5650f010740d000c00c004603d01041c110b04090190b135103d2032074a94414000c1c850241c1c82a03841001c80e0031680520051001070b000101002201140302c030344c1a040d81111914161700500c6c04044d80008000b650b001020072054007980300074041100c00401c042c0248040030881540e50310211075481d03032035103c1c280c010740c04000c02004000400058890004041e0040e054081d42c90704803450240310703650019525041440007050540750048840007900604100d42d0702441c045d03081614056005080074100b11860f0f26540008409a060301e04051150b64805d880380340d1840c107000640204001010280309426915203400d5201403150503e4610751500c226603115190101d9102800316909070101f1892480c5030201c14548030110100c900560200d070906005141ea0b170305128045600303a81551010030148880d6005100c0c283c010500c1c0c08889401d1035460756420348424441c4514414195114002902e281040c003a90340740000354141c642d015040c00303c0044c000d402c03182540d00002d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 137594928 1250 137593678 137593681
    0x12030b03070f15030213241b0c05091e040f1407060e060702010311070b0901060b0c061611060c0415080705070b040206090a0306140a0209100c1a070f020105 69
    0x1c04002e22010546818075440d95881c400740c0e1007034010b540405862a203a8052500000d02110681000c2200c10204030010b10034546c1c0c494010404c2c2030500c01c050b00c2854900c080710004230004c050104403681601c451045039181e01312180c00e01d825200900c28107081004110030030022983c800c0e10284914010164445c4201c9002c2d503507a19030003000041008035418160504d0058081c11010b44145404102448000000000d03a0803032003040b0740c2c0b482a901031040214080c0a0000501540024a420014852407040d82c4000160074010700e440741040c8005042d20800303d180c80c41c120766040310503a0400725403954555216204900210a22902c508200c40c800d14442d0301499859482d2800d0080d00c0e229840032141c0a80100c2e0f01c214100a81e0352180c81c0d0108110086000d00c0000880800d0f40903400c00d40c240040c84c050b4198810011000340b503503010301c030188070a100d02d0100c1108003680362910ba1840d2220003504000c80960801c4001544001c2e0500041000e600a1105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 137596178 1250 137594928 137594939
    0x40c051201030b091204090b130c050a0509030a0c1502070501080c190207090606050403060b0306040c0e09190c14010c0b011707030c03030305040b1803030402060c030712030b0307 79
    0x60040944004402100d4001000401e030038040c510f4001d1440d00035920008a0070410038031981c466482034a0580d2600034251852a010904403c6030020300814003144080c014000c00d2807150740000c0041c084041412400d03500c0c1000300c07126042d4080c050700c4c101901c0742840040c4d00102d15840700140310310078000c14a54841c0c2040b0f4001d8254001c0a400d104200c0648030411500100880444c42440b400150049040c0117140c020901c4be11516560350560500c40140c6440c0345115001b0380c4032806000c0051041c45946003200c07084002071341d40391a90042c42d403d0201070241042c0800707641050350280322300d8842d08001c4400c040140e041020f04003005640040300303402c0c05404446082c00411044080781d407810682c1c0c610302c0960b10240e48a40d00c2c0c3d18600d80940064000981c0d42042004204a001c48180c009080c481c0784101d40400702c0b20280e480c40f000b04000d0080f030000c80e40d50300030380c41081a1103c5940c01040d10301c03c400c00c500000c3c000c144080c8003a2080c800e62100240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 137597428 1250 137596178 137596187
    0x100807030803130f0501050f01180e1e0a06050f0a0e06190e0106080f030406110601080723131e0e0705090411030703030e09010501090b0a030f06050310020306040c 72
    0x3180e81c03050310390341140e5400c00e030032403200030b55182620103425880c0c0c00303c0013400a1041c1441121440503110342c650500c99240034012808145c035810074a030200c1c04078082c074006800d0702c2c006002541d00d4841b9802013483c2c2c0c20b1008880008206030704100500c00d50a800b000a10311408400c3c0c02001a4441144242e60380d80302519124040d11001c0031503846070100f1780050244032441800440c0083d500c2e103c151a0144803c041141c68001007402e01030b45500c0f01d1070004101d013982c004c1c2a20750400c420142ca0f2040e900c01c0c12507104010032141805507483c4000d01c501ca1005192800b4480001140c0b00908062a00d41c90611741c4c0c1c605681810a6900c24090b000640d42c0040041c0e03401c107000e100b8800000740013510f56903650f80c4406400e5038100700c524043d510968407080e082840c0c0d010b00205e0035068021030305001521006010605481c010b0791601c000d0303842c0100c0c0324030080054000070480380d08207a416003e500e02049a4015a070002c42c02240d095400b0403d02d14000d07000c48 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 137598678 1250 137597428 137597443
    0x210e0d0201091a190905120a120506150d020703021c0e010315060c0f020f03010912170601051206010c02040e012403021f030e011a030c01030504171b03040e1008 71
    0x40003c0d00210350980e031051340d035214a0030079200308110b032594203c1c400c84022a81220150f00002803641c00b4000c0320100900556400900940c3d6825000b000302d40180c1240c060600519946940840c4103c01d0510070018070106884441c0407a4044284020080c0034150b52a18180402d007043e400e41c54140c2c03000a0641181c209a45080d2041c00030380c2d030071491515100069900040c9010502c440756800e03c05c00030b12a01c20143d81c20b9900302080d01030022007000d148400100342000800c03c0698021040340c4205c000c000010074141c0d00d190040c0e0b5001400711019411074a00364011599100c1548111101071040c64094100311fa4036010006d0052940402500240301100d903e492111415240826186c04d0401140720303005640f00600b1907aa40d04404940d00d2416000d0340141018458030002a20271311303050040385800c0d02d9101c2d10400b41da003032001c1000c002548041e1145019070b1407040803c0d040c04d5079900e03651041100c14600c0c09036250b1201030714102c0d00181800c030010300503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 137599928 1250 137598678 137598691
    0x121407022e020a0e130b0307060903051e01090c08071a03100501030c02120c01090b060319020f010c050105010f080606031605040504081210060f050a210e0d0201091a 73
    0x212441600200c408010f508006200d009215054400708256520884940150313200303031a0020702e0030090b504061410501c1e902903400e020400205102085000c40c42d21f0403024220b29818414100c4005280107001100c0040c182c9021100040380d10f80012649074100d0b00307145901c1410007815030f01c2c02c075144415200c0341c091500248040160303500a0b00b140141c04203d0040d07510340101c2d107150b0b0b0380a6100f0100c8652503556100c81e1803c001d0082001a0002d405038020040b1088011000104200352800640f16104032204501c5583c0310f210350300d00041c0d02034000d0005503980d100240c030000c40c50080300c54902680e00001c4050500249c90042c0141e000003100d4402c3c60041440010074000c0d205030b403130b100d040181452401910b041c03a40101440300c280e4903501d2421400400d20700c000c100c54020032104020441099501030b2406080c54146800b00c8010308106010200610406103990002e0040035030312441c091701940106149809000000e4500360500c0400140b00c5085807203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 137601178 1250 137599928 137599993
    0xe0a0b071706151308030a09090c0518060f0c150f0402090114060d020c0f2104090b0414042402040b04090903030e030301080106050109050402070f030f12140702 71
    0x300c16241240d954000102000c1c07143e840c103520b11003000c5485007550000800303548002180d0f140e0580c0812054010800d01c0300030400d11340b51000041462049503901d006400601c4001c6545d41d590904881d40003413420001c070350780c02d0000d4481d925501c2c444c085426040d24400013848445801c080c0520a03540241030b40031603800c20f500d441c0181500d100d91600301c00c09000d801d010242e10b100911580380904020405548400031080c03500420b44030440700e00c3c12240700140c4c0c21700034006035000d80d50781c4c0601007903120000010400070142e03000131110228444045c04140110b00949007241e0303110b81111620164441c809070180d200d0f034410f402003220700300410409640031350300a5000d5032103850089807040350b0b28039003031554100384c01c815816503441c00100059a0032003954001884151415414044151180c2c460786012400203400e0041f803003a181d0030103200d441c0c0e4004040ca000020400702c10030340c11056104000302c0c0e40707102501c590304040c885101540d686148580b0b81120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 137602428 1250 137601178 137601181
    0x7080d0203030402192c151011010b09010b0705060703051e07020307050d0201060504061a0a0c0311010504030201090b0a020c0a02061b03040821070302030a05030411040e0a0b0717 79
    0xa100c10045084170030341d5814510100803030380103001d8440044034564440d07100070000304040341007031801001d41909407190a2004102e141c0d25204900c1c04452062300303203080c41c1020100300034050021601240d6100d0b15200c00850700806040c05815854002c0e821221550b9a0820950498005640c0158502c0440540d1007100c1d40750000c030342e400f00741c41c81074900b021001d80e20140780204003124030025035150401481181001c1c421040100b48812041c1c05408583c29402a2031150180e803008016511302c00509241c000c01100203030540280081180d0724150600070b000380100d58040b40e047c4c0c075000114020310014000c0c0d039880d0b0307498805001e41c90036907420041d00d984a46d00d0881c5031885105541c00111b000d0020b00011b20001d80507041960607240510b0085030090040050303681d0500619003c02d500000303a036640c00003400c0c0541e0ba80c88500303014403442d02c40c00c0300c103034400d013003501d0072024440119420003451303c40ca04d1141e51b500c5071a0b090700c9040d2801e0482e45811034840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 137603678 1250 137602428 137602433
    0x60c0503070e0f0607150f11040605041401110d02010902030613020f010c02010e1804110306010e0a0c120915060503010513081b0105100e0c040f0b0c100507090807080d02030304 78
    0x303003407181c3c0031000300040c0c40c0c03490b03d6641d440780e03910394004d4441c0315585041e5600c40503241e01602300d00c598844125441d003820168041c0446c001c81c002c2c40c1801c0a544040d9503581d000b2600c0f05a40d8220904580003d9101b2900078003815030108224001d000c0d440c041441d8454010b03840c1155903000305090740d003d21020044600020082040e41004031003d429601900ea840b64042085040c0700d884449185c03c0c100030795144404c414080c02a4040001000132034089030050740c12a40c07140b0041040014200c4c1122081800100114100e00c1c10381381101304070002e094001414081070042c030005c0e55481c01c040c200e580440d8004420604150100d00055041004180880c0c00703507a954108809003800e2421604103d62030030f406441d40e1003d21a885680200ca07034041c070a0944245000d0504102c6080c0a02600c20155600c8000c180450002ca06012036502011000002c01080c0b070000001005c4100d507225040060007400d50100340c068001c5040009035615400640c40e54407a075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 137604928 1250 137603678 137603689
    0x1912021b060a03090b01140f1f080405100501090225080301060e0d05030c010c27061b051f0b01030501050d11060706020412060b04050f040305031e0a09060c0503070e 73
    0xe9207080507035485500d00090b00c0660018007030025021303541c820040312020f10080342d17210345991784103440c00c1403071000c0c064219083d49d1b03400003c0d2809a03901d448500d08a4a03010582c032004146d11304000011404440c154003414400c1c081d002c3c40c05541c02044804c03076000c040044080e2070300c201000140406806422810f81102d00901595048ac181e921402e00310303004021801c18694450700d500f580c0682c40720f00c01500c1080104404502114040300d128422103c0c402c80c07003031005800124500e0707014841d5810b50b240c5c1000690f000b02c2030000703e036054105034a03140c4901a281c0b00c10903040354400c1c41414185e8101415094440d4055114240080301e50090142d02c100f0030005680003074420b0001e000100409040d003000c0f40c4051a0100c2584c50103408540910311b002c04104283e1442d806068009415040c90395407a00c600c0d10582e032902c00c01401c1800403983d20288485c04003940d00200040e4042c950800281242d4882111584402d541501c00100040b00c00031151911 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 137606178 1250 137604928 137604937
    0x180906090705030c040f030606030611040b04030618080c070f080d0e0409080c0a030206010504051602060403030f02040f06020309030d020304060504140f04050406141b12181912021b06 81
    0xd003013075400c0642c3c0d40c00b40030000d00740c1d4000b1114030361194020401c01c00540190b10780c1183c80356086003403e04001c004042030241c5d00c0040c1400e619486120a030b011211515514a50800340266070b500d5040300755903440c5814071800b4546c4030748030340000e04400b000c610080d0b040020f50321070180101c01e004010150540d164140c50384082080f042c1c2c41d0907010031000e80014425000b51201c0c3d89010104809c660004180e51a0358100240803e04c1c0e90780441d00561040e41400c0010307081d110300c00722000900642c1c20855030200c402d203000c1111600000988840f0004400302c0d01d00007060042203807280110f105000c08035030305001c01d010100040005051a01d40034140001c0c0144210004007902c0c010740301642c03581d9482881d000f0a101d041811070740080c86102c120f81155820804030340c10301c182c14214a040c1c050784045401e000c0f03607c00c4542e6202d924821a035400c4100e811031043c0b00b500c1c060071600841103294040c101070000c28007500807452a80c00c0501c0e1464003003030080e41d600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 137607428 1250 137606178 137606191
    0x8070917030f03010305101109090601030c090504020412140318091f090c110c0307050f1f0807090f0f050405090f1209100c200307080109030518090609070503 70
    0x41c8240025810b81d40041c50085020344000c04800c8a500220421200801564244404201312211550310b0300f0002d950008000e1800140140b081c000846820b803141d040a40d109000180c0003402004100805c0e002c07501441da240d1200c0c544410740f40e52446589001c030380f0700110701d545141501c2d01c002c680b58030401410703240b410494024601d014208851f04060300f40f50342c0d0507030001c545501903c500061b02c0008d00614580001d070000070b60b142100e01c55a4411080340506d842c2c0c3ea01c4904110321444d5500361100720f0000303460009003102c0070442d10180010310b840800501c001081c1800c00454110030305140b8024200001d0101a140007480c0c143c551003402c8944965010405c01a01840b070403548580c0c490b1100420007078280d200075120010014400710040124021074a540808042d503000c039000b44034254082410a484ad1741324206030b520b805102c074113042d0400c00074107280404070b81510034404440c0400c81604400e0b07540c907030030401207800503200d1030185000f10342089 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 137608678 1250 137607428 137607433
    0xb0304140f0a0c090c08011a220603050c03040b0c0f12040b0105011409060313030201060b03010612060501110a02040906060b0703110c0a15080432060708070917 71
    0x260103030199803030160306506070741c400c0d40301100c410188085100f41c04041d003181541881034181c1242c00410204c418004d15107200c4d00d0800c65241150100c1c1240ea05109044454106e004852100c60a41c201849010080b071300340400120185035980499101b29030044060364540c80300c801c00c0c03c558000c21400b02c52004204804009481c6400040d88258402c40282c42c0075810440010400080c3c2501c1004040c01841315074019078079001034a511040007461074030110120b0604902406141c2d00061481c0b04c0000085903050380705800980c81540c400c1d09101d115943c200448101050384a00301700303608140c1c0083c0c0146066009200b44d140a8080403400d9500c580780700d5000d81c80a04c084000c40c82072941c1149101d02406002c0e491041100c51440062a0104641440d04039590301c03070400c0700c007d000904014401c2d0701302403074a440c0541c488034014090380c10f43d038400011030380c050507200f071f5000680e00503c90220640702d0404c40d62109a140d10b00035050908003100c0400602a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 137609928 1250 137608678 137608703
    0x80409050c03041401020307020705151207020607090501050f030f0604110a0e010909060308071b0e0406020c0606040618090201020f0d0512011d0103111207060201020c10060f0b0304 80
    0x48a50003a00d00815034140c0440e920f040a240c0f16103010060200e5544030b034014020403000c1900410807c080744c2040d5031071111011800d06820f91446202d00c20503c2c81c25200a0060480d400030728a442400d0702d0725009061500d42c001591907010342e0303050040b22442003000503c0000d200c900301703400c5032020b8070200350080d04142510043d0000582040050008180940c3c290780c803400d080000c160411381000760608503103c2c0012481598006071103524001003041d103a40954030184014910138902d2155401c1c01c1c580070000c1d60115048400d07521590000c100b440c070b40303803003460110f80301903800101000250a1400240c210b5410036815802100041036000c031003031013841120382c040c7d500c0f50342e12914019040c1e040708040e00030325041c588603108018040001c00200381502d0308408207800c008280d00c002200c2c8858105100880d00600000003902c6130150042d1402c03c0c04075041c0c41c121841d82c00814100d503002d00c03402a0150034524100842c414034801160000d02807076600e2540c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 137611178 1250 137609928 137609939
    0x1020c0904060f060e010b07060504020d0b011206140601020d12090602071505070813020103090c1203020a0302010e0c030a021309021801090605040203060d02010e19030c0807060201140c070804 85
    0x224182100d042d41c0b0103450300b46080d041d0303001d48550070203410310001c00c16084d4140b4202c03990303c3c01018001400c05030784201040541d9208094502c08a0b8405000241980c442880718007000002500b10344040c00c100382c961310180700a81c541c0c03107548103a000700143d528094088451141b00d50100145603a121a06000301c0c003280001d10041c0d00400b2520004480700c0c41c17402c200c4200400341020060030106000042143c40300d652146a02440c010400440c5400c141010300d1950b40008003003920b004a40c07041580201342140824040d4000700a60010480b64035141c02c60403072404d1707040e04000b170130f03200600c0e0010001c00c0350791b050710000541541c04d90104802031410030b280d04d076000131400108280c1080380141005402c040e2410f500b58145200440c01082055400a05100c0003031280820742d1607112200d204000d510040e40c1d5415641d05140d041842c6038000e50700280a801004580d15005001d8401c14040c000e601e10000e5031414510700041d001a00100c42058080000049 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 137612428 1250 137611178 137611189
    0x1202030403084c0803040509040f2118050102011a01110106050306190e0c011b1a130b1e0412020102040305030406090806130804050411070b1302030d0914010e01020c 73
    0xc0c150408124403c03520110b1111401c0680c00c1d84900440e501c1040203110382e40710414401c1d002a070002151440c541145400b910b265030f04a9a4085e543c003110b1500001c1d6031140380614443c250301c024031f180c2922000120300380c80c07080c500740e4400102544170102c0f0354803a4102984180c1402c0000030041d448400081c100030042d00c2814101e485004000721801c407610808180100c028001c044074010f4400180540d80c5d0205500d60f812000c0040b0400d2210b0b05100005170042c407582c185030340ca44041104400315005105030b88a5403203400141621101c070000c0300d214016881209480e0f07445540d40c12020210354a00ca003155000c0c030000001400410140000d080903071250744d240d41c24046039901c0c01000601096040c4415041c040100d42c0540480e800d4800642d40072038500002d00c407a04843c881d0200041c52400c110080100740406011206003031842101507a100c0c0c02e500074200c80c034084a010300d222012010010040c150300481105001d20010f00540e031000c070382c04000a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 137613678 1250 137612428 137612521
    0x1f02010209030703030c02030d08090a06180c06030518010501050d0803100b04091e09110402030709030c09020306030c15030f04022206050a060f0504050d0c080a05030a120203040308 80
    0xf80424400341b149421480c0501410000c6980d515000c0c0d6a85071a40c8090344c0c0c0c49143c0400341c04580e032048000c210540b4071040520b65a04a0345500c02aa0f680100400410086941401911444007207040030501802041c2c102d0b0b07001000c0000040d50303900c501c4800c1d800038207607040c0c140c1402e20005100d015079000d40000c1825180010b0030041d16407840710b0410081c200301060602c0c0007030304030006019100340745400c0c00540c0c005840c0da076030440548059000d90400752282448400004811080340c00862081e142501a2052451084103020300c105e0780354081c991000301070000540c002d1924182036070003400101131491000b00f03101c60b003040c2d9400d1000c090500c6e4680006214500302680400002c00c03045c60010024200c00100501034000c43c09040e10a0322070a881d0000d2003180c000798009000d1440c107403070644070b091a005640742c3c000081000070074241d081c040c92001807407081c0c2e88600d030551603070041682c071059460002ca000c00c0028980e00b07084607500801024108402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 137614928 1250 137613678 137613683
    0x2041203021b150d0e0106052206090605060409050c0f0307080f010806070c080d0603060c050a1404050a06210c0f0e060307021207050c040c0906030e07051f02010209030703 76
    0x40014041c0b8038868050940880c0340c581c0a218410b80700000041882e00f00e8205120074900041c0d100c4662441c5030150a40e6440160f00c211500d84070b503009100d20462800f1000c0011003000070175501c43d00c04050301c0407449107070342c00b00c07041c0010422030081d41c009540c041c205010352403510182c1145180c141d0400d030f0b03401c0c00080b004c800300b00012000c280c10702d01502e000c070020400da10308900700030005c8141c200000c0481030007090b900f1028080d908418050359001c0c1d01480702e1207204000502c40e800076000d1100180700300000c414410141700c01c99060b288013515884806080c50000d44424086450840743d034111051141d10030441880f0b00c9100c4103443e80c84800c50400311000502c00c4030081c100130301c210b1040041c0500250000350041c0d030304451a401c03541760402418113500308841c02c10481e800500701001d5015869100c3c20820984d1040d481c20440d2816001102c0e03901c44190040711b0700800b81000c4111003084000d441001441c0a200152a040950010a04040155004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 137616178 1250 137614928 137614933
    0xf1205030108060906090d0507060b031005070f030506010c02040207111203030601030f0213050904050f030c10110a020a0b06121504110d0b01050d150219180b0702130204120302 78
    0x40c011103100f4007010750000c661400411041c00e003901015250a00400104240500050598104050380d08001c00d010802421303a200080855040700c054201114404000b651212305840c4150083c49002c2c020b00040c0d40b807610244403030b8240030003544005025601010000900d64295490714030100040711355901a680340c3c20807034000b6064032032240101406d05c1c018010300040c02000045c403000c94500303c2c0e0707888041e1213900780b80341401d081402e0301c1600c2c04001058041c107840003650303080e1002d145508102c403010f92203d400650140c03406100c0160010101c0f0408500100e081503081840205109014000c40c6401e1345040540078000602c0054681001b0511a000b40d80d0640100180c4200800752003503510000d8200c014080c6504c034104800d01c0c1004c3c4880100f4501c1208581030003150341d071a90907a101d0300000c0711403003031002502c607191541c6046400a000422280b44520850038841c4075030820030301d50316540101803103550a020003e20380c21018000101240039030007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 137617428 1250 137616178 137616181
    0x6050301060f050603130f05190302070b0f030a051005041a03010b04060f170102090a08011a010201061404050c0c0610170c0a0306090f24060e07020303040305070f120503 75
    0x14142901c0309a44a81c102502040080060f40c55440450f680031801c082a803a2014013880d280450007035110000e052441401c040c01c102c1c85010b040d50218034000d800301c40820f9a9004102d11910904908600b07442003031000c91200b011581142d900302125000c209621619603001c241107500080f0080c020401e80c410308688e6003020b219407809050152414821181440006c40105c18944200b961035002c4000c40b2941304400e42c1a07e9041c203008010100d010380c0e819245018002007000f40c0450301d0702d280440384640c0141306034011500c681d9942d9580c00114000c0100401c07000b0807034100001c08000d403525060702400110302c100f0000902c40c0c196030600c14000e990020001340103110741d020f8001c81200313903584885042100d0307104c000810b51a040303140021342540b81e01d200622866580504204011129101c0c1d400c1e4030042808000c4a980e9001180841400b601d100700503800030008900820b12503002403400d0780c040d0880c2030700d2240e16550707136495a00909e80400060340100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 137618678 1250 137617428 137617439
    0x30b010c24060f031e0501111908060405060306060409030504030501020f040f0f0e0406020307030e0d0f020f06060d110a08070e01140916050c010608010f0b01030501080604050c220e0106 82
    0x218078000b0f440d0b1216103290380e5041d60395600440304c0c000110040e0b4007800d140d00d020000250000701503405154840307902e50030300c84031307a05060310340d84040f0740454201d1307000513806d003440d204d02440340c01c00030700030031241d140c82e000e00c00244640a010b608210081001102040c403d00040030035000c12544660707035618020102c0e541d146142c11200044141c0001000244054404150826048280103031b0300d407140c8900360000c1c4980152540716000301403010440c0c6410004040c250350a9030241c0b034400c1802003089444500859039180d01c03000c104000c90118448615400c01d0640c0a0001da010700d4440e20000c1c5020780503400100340410041c01400b9020344440420904d04040d140581581031135910044022940b08070402003260115041c104580c00350001c40041c40140002c0101c8050b114000f07010306404405180442c1c2000d0000810600009440b807280c1d80180141c00c50440e440304001541c481d140000d0322402c548404407400e88018854a402030804c81c0c000628a031808 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 137619928 1250 137618678 137618681
    0xc0309040501151205220c1505040b190e030a060917030403051206060415030b12030301060818010914100c0801080a020d05070e0c071506120201030b010c24 69
    0x143c01c0907412072602c04210401c203801c00c03554219460000c03400304065403540c26030302c1e02003100880101201a074590303050504c2144003c10b0240c0e2001d07000741c4480980c43c00280c0301445503100300c56980d641088460410b0180c1068801e0342c61a070300e803140c3e00c0c0480f01e00107440e00d00f01c0c80d000c3d80c4c000d54400d80300007044151580400308200200406046142c1074602808500446440340007410340c2400182c3c0d031380d41d5002110090081489179003450407941c0130090007002e200030b1481c000d0300d020b036156203500c0b40042528100d0b90311780d03118141c655640c1d5a000c0144910700701d0240c01d40d200e10144000400c130003919401481044014031024403071107843c0050301c21510900301405083c000500600e000400c2c88105150190782680c1100400e14105180c5003540c0d0015580b10311302424008485a0080105901030090203440141c0000030301c02002c6a029106071912000c00200710300055000e03400815094405040400a0303642ca6166140c001560980010000304030400440490340503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 137621178 1250 137619928 137619931
    0x318040f0504080d06150e0f011112090301181101140f04061706010906360801090311010501050102070306050a0b042406020f1225030306060912020d060b0f03030c03090405 76
    0x42c644a0508108510028200500f0000c407107015200002c40b40f04940d0044c166144083c21400840d0040c6c40c0b0200740bc0c840d50040b441c500d22950920049800440042c40f1211446800c5074a01100e0180709005441403040c031040341d00780c07540c10b00c01c01d0b90310100100a04001d140d19101c19050312411014007115000041819041c0500f188061124603408100ba64007001c82080b00941d0030b040540f00000f550f151004041c0f800c0450a0214090798103400c5004d0007403094842c40c010144646445080c0c800c06d0240a006902c940010804140560005908681e12100000381c10080d000481c043d6281b0071003840c5001c0078041207900300d1003c98960030082140384058070b201207140362002d40350f55000a220307440420120b030040031504807084025100c0c05696950311404c0e454a4050080c0806200350070106209290010f5002c0e522140880d440c0d60040c41c100005c68030307541e01c400030b0414031841d5800c0740c2d0001807902240c07000c0008240c0c1c034001a0095803034552180c20441a80c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 137622428 1250 137621178 137621189
    0x60312134103010209041506020c01110c09040303020c030307030504021903080304080c2a01080c25061104030b09010c031e050402010e0604060c05060c0c0318040f0504080d06 77
    0x203201200034000070308221001d580e501c80c100c501c80d180d0700c00400240603014111145038000e1400103250301031441085420b04482940d0203441e0740c0340c84000103481d00c042c000701d420303980d4010011004852406509456000e4402d040050809240703000745403850300103d40762000b080e540c17010b11082d40350401d20781d44028404c141941407541199265030240c040a040105444030100700503203051800d00c0b2090410303005580c006024400c03a81456964903000c00030501189900c408140101c034840115002914001c44420000c00e11500c0300008841210003030351941d43d11041c0140323780700c80c0c0060000b5405209140303803e040c4140d0190844950300c107800103240c1741c15055481603200d01c0c0e078080321015045000401c0e44c0c550005817100c801c24000c061b40403a0004001c5403d80d000845142c00303e0061003122010368400c203102d41244941c100000941d40b00340700140b00808040700985440101500105000d00603184040607110250360031110010081000810b008203131049200800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 137623678 1250 137622428 137622479
    0x10e0613060b04030206031515040e0a050417030603100e0f10020304021804060e030a05300a09150603030207063507031b11070e0603030d020306031213 67
    0x2490b2901088480c802e901c0b0003405400003000040801c01c0845400c0c0c08100d000d0b25140c00790781c04a854100c00d900c0f0340200204440044082104140c0324270501d44140d500c0200900c42e0104a82c2039513081e04014031107070f454890440300d54003000c1d01b80580181c00d2075038001130103000c9401c0d1440e4145500f011000026910610400002d607440d014131404200d00c01d4002c0381c05841d2410000050200301c40d02600a1200040c4650203552120040c68200022040101d0b106000344000c0b6503904034000d03221540000002080f2180702d2607012543c003511561400010960000f014010785032154400d03000758002d20802c01449400c84074910440032689241a030480000e40c2e404500b40c0200498204244181b00003502a0f000c0d9002040d480400b5006158407059000c2c010990081326140e000180101c6c84005880e9050030146402404010302440c02c0181d01c2c800403009400060209a00d8450713003d086940380147c0000341080072500c03e0190001c0e0920303030301d0f54540c1c08480340d105050707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 137624928 1250 137623678 137623691
    0xa05040908090f0a080105040503120108060910020f1201030804080105012727110406060c05060406050907030f140c060301050609040506030106180204050328031404030b010e0613 79
    0x5001201180c0e8849000c448a080520f03480c804503820f010315030040c031520740c41c4c40c0030700c0240301d4008090141a40000b0360142103a88500e03510391a0b00c41524111025403200c41450f002c40965000303000c2c0d10300d10341e40c003070300b01040200017400c203c2c000c0c0c2c410b4401c0500040c007070240e90800e014550141c03890100107140c010501e0b40d000c0f1000842d60403003440a03606c0c000c4540f050750041c42c0050400001710781c0e000d54001d5082c501004510803441d0f0f0b116624000000031001c1c002d50b400300501790004043d02c80c40d69507031902c2c0f014010080020301035005481c004400034011116802c1c0c840e00944c08101c01c80c42088100745001d120107002d9115803000d100402456440700c0c2140c2403c40d003a900810540c4030580400d014102079008800c2e103400c0000701c0103c1c0000b03a4080c1040f10011000c980c001c001424691044c2102c0c00c080c9503001c0c4501542c040424000d00665040000c00b1940c0c40c90035503207840301c0d2182c0c8402c0c2c0014807524201c0042c0069450400c2d2000f0040e4020032040144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 137626178 1250 137624928 137624933
    0x623090a111206152a070902040b0d150f091d060705030f010e060a0524031f380f030a02040e07020705100f0201060b13030308010b0702060909060d0c030605060a050409 74
    0x601980017190114501242c0411030800f0900003400180340554055403610345400c00c041d1b283c4c1000c04040310082c50140308040030300140b91a0400c0b54000000c21000342d041941d01406001500680890905007907004545118200583c5106903002d647d01c1d5104c0c00d11045001d08100103034409201e0500070001d002c131556400d40c941c000c540c41180c0301c150b040c0030802c9038140041c11044101c01c04002004102010301c01045000100126920700a0310540359451703e4481c0b206035110320030850b0b00c40c1d0503c1090140b114202040c0525000103804d08007900204800ca40c07045501090302070300420200102100d2000607600045103001401c185800e1a003c6501c1030340002c1500d04211405a42e0b190460003035003c00081c0248841d51603458407041583c400c0e1030790720321044001031651800061110b0b40c0314144c40c41a41c0c001c20040c40e0550140c20440814400750545500c0700c1904414070019110010290042d80f20381004a4a80b406204100c1c200c445076006d103008a082c0a4040700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 137627428 1250 137626178 137626207
    0x11202030304140126090d080c03072304030c150f020a0605060126011706010602150a0605090a090303050a1104091805070305100623090a11120615 65
    0x3d48103141c8080300006038080040703426041e171000c06150200e08407150150a00f0308004548502403c1c0211910009800011144054201c07402407121005101207260140316a50380241da0707031003020a483c450204500488a03901c141d00031078440148070810040c0c0131007844090604507281c2020003045402c0e0300301a4445c582d07000d008184590321030018034076a00032440c030b401e0081141041803010341c0c00e11490482c0b40d828010b503c4440280800e4003824200051258180d55040d0702400e003100d0f1412195039060805004041307255240d040220b10703904d956942c2e51086580c580042005aa03d04000d070403140c0240c030440881d800c1c000c00720320a9914004482c22603c540c20f000441d1517807904240b04414050304014807230300a000c4001309020000034920b24151984d00304019856556501090307007164100500c58582c0f4483c89050304e403030300d2440c4552040d000c40c400b00f0f1344502800030b0306140d40a8200d00c01301c0e030103080a0014505041d121940b030400c035500c4040c50314949200403030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 137628678 1250 137627428 137627437
    0x11a07021315090c030e0106051f1409040c0201020a03060f050a03020d051c0906031104030f24020409090524041e0c060c0203060a05010e0705090a120b0f0112020303 73
    0x181c1c80c9485034000580018500c85140c001d04480c030342002800c9080ca03008000d041513803140f0701c0540c2000390108661405061140710180e004412100c3c0c192408003d58017140d02d5a034008825800380b013100300035140d40c0114010b50300c107540010f80d5941480750150440300e0982040c8004640c000040c0425151816a138003038076011110b51251012502d41545049501c401c00710b41c003140802c0224409422000c0c0c0400d50f501510301b4011441d010a240119019620002d003c0c2516110341801082c0c200d004141020004101d020420b960f055104040ea4002c7e03000d903450f03640d10880e00060050078091190403200b0011401c0c40c403c0d010302c0c41d50b800b04c00584007030200081003005540c0c030f10200d5080c009903680800b00c51082c954440010707140185000e0160b00034080c40340010780104c064032559060301c01d0724030014800d442c1d0304405c41c0c00380c001c481c1e01500241015400300d076030b01c0c10004401440d84188084040d40c6040b0841180d0594181c0c842c41c1d500380c004146500680c0d0110a44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 137629928 1250 137628678 137628709
    0x90605030a11071b08120703020c060a02010b0d120f080c07120c06050109020d11090a140612040b01290414010e120c040b0117010308090d080a08011a0702 68
    0x10070800d80c044180340d92403140c0d002c0100301c645408050b8401c0500e0321307100011200c03030740142d44440c403008001075024442d035400100182c0003d5603624480c68140302400340c03101d103403000090940342034001c20702c22880c5600c152a601f03500c0f0000b900c182c0d84201c0c11300218070b281c50a42c000b810000074194245c017030951300600c0c1d03e400c16046042140302d100514030305d80c0c1028091055581d0b44450f00001d62042c0d071711280807802e2046039100c8003817900c21078501c00005400e5900702c501d02111918800030520b03032541d00c08801c01c43c40001d1840c030039607603014501442d10440da5500d408040b61005600800701441519030100d16002c02c2e4040054808403002c2080d1040d81c41c12070801280c0944034002d081d036001654480700700e1034510003c1c4c4248144030540b802c000340c00740140103551110258814a0354503a0540061000668580141803444006002080c0c00207903641c40b46450f400c0b0300d40020003e4403010040040c40d001d000702944c2c200070f0150702c40c5044107a801262550b0038a45a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 137631178 1250 137629928 137629931
    0xf0e0703060e01110301090c0906090302011d04021e0316020607140915070b0f060f2101020c0106080f100903090e04020f04021c051501080105100c0c1212090605030a 73
    0x40602d400400c3d0840200843c84c0e0039265070740c3d80c640d1488402880ca4002100c0083d000c81e8000ca174403401070260400740e0b60141c461070425076141f1180e61750220f400c10f80c00e81064092083c8940f80e010080d00c1d0052801c201041a101d00d0300322003003a00b810185041a04561280302480522034100c3c0019401c0c02e00c400c52503540d05800380110355000300c040000c1c210542c0004079913081c0056804018040c0b45440e0000d600d644500080110074001c01c0b032210350282180710441c0c2d0f010050380442088451110000d4200708078610070741d003194259070000e00310f904400b01d100c2003d08148003030f07000320902c5582000040720917180280110b60f40d014100350303003d1141c040b4040d580c9140c0440380707409005206565a00b10802c7e020710300d1404440da8200079050001080d500c10001d014101c107900183d6039601b85a180204028500041c80c0c4881c0610100c0a10240480c6501820070043c010941e40d840a191541c9000c00700310300143d0a4a040002048060000d40c1c1e0180880b500314106c02c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 137632428 1250 137631178 137631191
    0xc0503131e0b0106110604050d030903030b09040f0b0106020f1005070512090c010207062a030c06020307030203191803050f04210c0e04170f040503010c0c060f0e070306 74
    0x108403061501d01c604a032421085039034020708116000d240345059512a9030b030307202c4200000e00f019903078041c25200104030790800d48103199a24840d034021000c3c00d00030324010514802c0c00c0b000c50f49402c401e48003580c0c01c2c00640c03c185c0c14045612a01c40c01020f03e40f0041c03041c0510501c109464001d203140300d400464480c0c010500b128421800e0710740f185082c100715615420480e0b04291b9135004418030a026000b03050b40010014010720341e0f540040080450612505115840700d84001026601141804815200c803004284680301440c42060709460050b6a42081403070303401d020610440c544001c3c0d05084203000f42d01c00124820b040c0302d515080581c0c90b03403091074194140307001e15000009810005503800c01203400c50581d4841c450b0089a801d50000d41310016008640c2d011074028200500011001d406040c401001303050000c02045060b003010348900c002400c0d5207100312040001b504541d01034041c48841d00c103481e9000d140c0e8008106100c80910002d89132041c0d4800909600d549a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 137633678 1250 137632428 137632433
    0x70807060c11010c0309171c1107120c06060e09151801020d0603021c03021902010512090102130f06090501030905031908041203022502030c0307090905010e010c050313 74
    0x240005582c0006000703001e18100c1c020024024103180f0700c1601c0711082400107500302d005401c211902002080c491000c04000c019240019146d2030520f90b0084404000d21004600704402000d070078011a501c007484031246081203001e607601c03504401540c41406041c00724050340003507000b403031403103542c2e66035070300c1c0e030b507481c0c04043c0c680011b9400fa210b500010b04010f07010708580c85542079910888140f00000310440410300e24060000e40100903a20480d0f41c01000e4032071181458040d8130525180f4074280d01000c00002112040c0e62089550707401041c5400c4e0003050b0f01d038020107405401c0071094110b180506c002d119005034801c0605165480d184881404401d000b01c0c0d4914110581c00c071407280710600b000f004400100d9040e05c008800172040341449100e40210307608480946804a43c4c2a101d110440b40c1d40118003040ba40f51181c4458001d16807400d205220041910070350001c1c18000a00b0030600f0744180c4000c5007903d924104030700c0810394000d000c4e00d412000030640c0400300c04851 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 137634928 1250 137633678 137633687
    0x10804050a0204050c21070c03080907031505060108070e06031605041203020d0f02160506161211071d1b0c030304060b040c17010b1e030c0a08010b070807060c 70
    0x4140030f034200381028104a5800342241c0200030240c0c02024100d584a5188480f07002000180c604d140010a901c1c103840c003203886a0714160704456003e0036079001e0740e03407a56a1002c0c1c4801d0700442d24810384a008000103581c03c514900e42c050600c1c10000102d0307200d000080c5c41c41c80002c3c81c1e900e022040e1046140852700c1141a43c01a0101c072503041003456030b90030080d64403031241034502d00007001fa410114813684080b48004080029104460300c0b1402d00b020004160000d040201d400e14900c0d0000740800e14038501c15402035a6921840740700d08204060506001958008611000a03a11400038224100c00700790750101492009550902c60441000403510501038100c3c0d20344000f03c00e000a2180382d03480f40111003001c4808002e4403065040c2a00c00e00d10b140c2c10400da240800004005400c610401000314030600c900c0196000a6a01d40141030303002a40d0300c1d01c111501050380110300e900600540d004d07005140c41541424107556401e01c0310320404000910144d180c041048019008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 137636178 1250 137634928 137634943
    0x5090303040b31060509010c020303030a0b010813031b050115090c0806040c0509010c05160b070210050c07060f05090d030c150513030804140a120306060503070504030201080405 78
    0x2000d8036a1a41d070741c03034118910740089041c11503030303100f07160800340b000e80d04a43c00361460802103029501c1890402e00399456002407150a0610074200c840c040103a6003400203500c50002d0300c81c00100b145003000014150080184001c1345030300c4401e054000f1030340018a50b0042010405140c0c04d0003a00c1c501140904a6600d00c40f410301e040d5500803034400d181d41c01c00e09800c40280c0c0c400742c1d196180320406c4183d540030130411010850410030120303d07520580c81c400c00b03240500c080301d8640b044418440c06003005a409000e902d240070401e00c0440c5422800b00c0c5245070b162400030f007081e42c2414699100c00080c070901060002d80e41541b80c02c54019029240d1090004040c101c0b14001824090701e03402040303400f16505419400b1581d4000101c0c0703d003e02410b1442012a000da80c690380a40310480050019680001c041034684000c0504104a001042c03042c0c0c442903006500300c03c040c05940040d0040400d20800b442000007041d4828161021281c0901e494034040d1104d04126040014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 137637428 1250 137636178 137636197
    0xf091504050c0319020405010c0b0a06030b0a0b120a0b0c1b01050c0304060f110f07020a0b04080a020108010f050904030528180e0402090105040b0102190f1101050316030c05 76
    0x1480c0c1002468542e0703001551140301d480d04a400c40507104c81d8042c08038821802060b0108249500100c0130400b6580c2455104200d0403002440360b80703c0e2241c5030154011030300c40032503d880d06007115160a00c031003851034541c00d05004128034400d913980c40301340350030040c60801c8058002c00c014400105049405c100e84010400030044c0c0d04245400d241c40f40e00071581030700c10500307000303401002e00654031603a41d5002c01c0001403030910305400008001c5601281060780c0c050240c003000f003035488c03100740104000c003034103001491110b51754400580100d030141e0241c0e2892a116408020b6901d4002210740d10a5251500341c1d40d40c0c00c00c00c4003501e024000b5a1820032056845140c04400b034100c603111042152400321058215a11000f030300c074003001154003d41140e40803004102500705074122810031401401034030380e140c1212080e61b130180450300b0300f41d41c801d03c01d0300700405000040e00310000103602803078940e01d940340081c2c0300c85100ca92980307803504040d954001540120b10941c2580c0c5500c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 137638678 1250 137637428 137637431
    0x4090510090f0201080606130e130c0b04091409070311210c03060108160504020901020a08030c070b010603050c0a0f090f0f03061a0a150909090b0f010806060f091504 73
    0x18900d040c80c42d03941d00c02040032070220381e400300450700301d140250a494144182c201c8c0c030074505042505281c41444090078404c140708151034080e0000700d007034003240081c001005602d40c07a540713030010f0030301500d8407621220740d00c01c0c903d03041c480c40c1a804101a030079240c00013201d9094507408004180c1c03205007601c000000301030803500080b60740380c0814560b01c1c440c8110103c1e112a602ca0b201d407910744492640a2a0000f90b501c1f0810103400e0903009000040014016100c03c410340351240011070f442220101115103001031500200030b1f41c0c1c40140d01402d43c900c0c0401043c5000400b00e0f0851044410348420321003010b01e60300e00a441030b203402c0c4c09840d2000c8204502a950742c2c001d0b206821134001104e800f818402e1419042d070f6604066410f95400419940b4020b252185c1e04030303e44945036518003000500200410f460009005090900d8401c48494489281c1072080c5803010f40113070452100d03034100505101107542d410718a01c10880c411162600c2d5916500f0001d440701c141c821a01d0b4105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 137639928 1250 137638678 137638691
    0x20a150509040f020705010507020f0d08060303041a07150c05040b1b19060f0c20030d020712020f071412010f0e0106080d170f060d020d060b131a04090510 68
    0x50f140c0c000d002102e119100070b0165403a2110140e0700c03518503110013a0355602245840f024584103e0160341c0294001c1d041c1da03d0181c450440700c20283e180d5192291011340000c0d90b0f420800785c8040b40c42d5403200e8600810100024140080440c800d52289820804020580c02c40307560b40b11407400001e480c004e0480c0c243d00c1010200c6400001d00d95000d4400c58a403504003032580b0400d0081c070301c0848140c0d42c0c3ca04c0b5000410401d110b0001086d49040007072000340401d40300d003d660b2004102841c000c01d0540000500c031403000f032610001000084d02900b092104202d60011002140050402100da0044083d00071099078010b1a500c1c541e51066070030034210800203841035200703000b81c0e1b4041050781c0384461a50001c2e1011040d1880380d17000040141d00081e280c842e01c072100703a0000340081900070b400d183e90b00007400c1c2e0028803105032540ca0390351694075800d00d00540300c0d045045401406121186d00750a008015500c940c242c0b41c00703a5100d003092001c10809000a000e541c10008040000c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 137641178 1250 137639928 137639951
    0xb030105010f0f08030408070501050c0a0605090a0606150801050f0409020307030b0402100903032a0f2102010603080d0f090804030503090f0603090307030f09050a0602011a0607020a15050904 84
    0x60b4809104440c180740301007401040581d0040221b4082d81c10140051100c02e11b490011580c5512000c00700b0b030389000e04200b080000300300b8002c0361f00507046000201015a481d080c90421108227a000807075460013040c0707015460b5080210241100d404603141d00510801c48041030142051100095060140544c04020480c00c8866603015900a803040035a00d0070880701604c02901d140030107000304064204168008480382e04110f903441a1400d00c80c2e4031a1342d59a21014098446801c55a8409030f55010b0300e44203600c0303007082c1c0c03140040c80248032492075074684045520820900c400055210207201800c2c040f103410591040d82c0c410f10140c3d545a4070b0805d15180d070013101e01944a149260880c5070249820f00641c0e024060300800b035490412070755005c0d2100065030804c0d9040c414030341400501c0d0742d0f40c046054014100707070700049100207040c1d0104a5000d03000c407035136100e40780c140040320140e00e601234032506842010b61074030603e19600f078041d0f0b024081c28010075030207420281b0f06080e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 137642428 1250 137641178 137641199
    0x2010f020a020a17040501051b07121103060901061203050c0c090705040e07020307021c050a12030c0305010510020a1401021608040e0a1109040f180309030512031b030405010b03010501 81
    0x103840c0104000c0c13081c070754140000011440343d480381600060040c000000305405609202c240385d1054011a1800350791902c104490b07030324514041d02c103881d1400340b840e09420b0501005512401c40300c000c0081c90f062080000f101d04140c40d0207000c03c400410401d140407802c00080c00c81a000400d0785010780f4110100424507805030148041114004011654450000098442c030513401005e0055900b200b10184543c3c46c280c081c01d542c3d034403c40d5403603c0456400c3c3c803021328201b02a07030040f940c20301084020701903807410791005020f80000e0040e100c1503503010aa007002c032607029020224504a0503030342400f901a45000f4a56406003181000400000c1c40082c82154026000c2500720783d0341e00782460849200f5030340d001501600b00f101e000d89143c25444103a540140f0100014480342001d071014001e108280700700c0100b1031040c800e0040c81005c204d80c0800080010259282d0314203608100c1c05900c1030081c40d500407a01002040800c1350a4110324031000025000b0400303580c2d601343c00c0c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 137643678 1250 137642428 137642443
    0x509010b030711010608030a0c0510110301090b0a0b180d15090308090606011706010512010f0905010e07050d15051e0f0a120b28020306030105060108090a021002010f020a02 76
    0x1404600540d882e40c1d00200c045c01030400700c8442e0005036080103207000b810b5410440b0000d00302d400c1d00500d04040302c864203520951102d005c903d5000d5480350b061188940480b0302c004002c501c03c1c00710035401c0041c004580c2c22581054458402c038182c81e1600004100211707106030005110b04c210049003151070a440c5d02c0000814065512001c40d511030301c0314543c1303909081d02c286001458071201040f00203d440d042503040841890510b10340421074006040141d002e8109600d03a45c40d0540800ca0580c00d07004590140920301e01c40c1c1c5d81420711402c090034911481c072700c0c0303102c50b516141080032080c686c4018200401c000b402030000185819040d030014410b28019500c80c48100500f1101c1e402d20b99645d50aa55924115001a0180d03407034003a00c01500500e420202910301402960b40c01c0c4840e0000c540d41c8203c030f8007503180d04140c4205400d41d4402030180341008030280400000e4600010040038464055400388800d015446040b40505444034040920600029914110b02da0014400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 137644928 1250 137643678 137643691
    0x7060206150907270b0d02040e070e090f040609021002030706050f060a14060d02040605030a0b190603020a020c0603131b030809010f05070b2d010501120c03060509010b03 75
    0x418004440810041c5032001a280c3c2c2c40010046150b485a0b005030280b81d44980c1e100001d020030036503541036031440c6588280d030b0341810b03a40c001c03c2c10000000051030b9103801400e14101040b04e03a08100110f80a40001000d03c00640281c001080921181f41d0080018035006441c000c0b40e010709a0010f035032984449c0c0304403011072030704000075a011041c04440f4000c2c00010b00e003c64440c50031074024804104041c0c4541e10110407c902e44540041d0300c0104011315554403082d0302d030314064a0010464421174038543c0901001c00f45410798542520212068804604005132203400c02036049240c501d014040c550030400020a000d0109001601c0c000101e1107003254241034283d41201480b480743c188002405d582041c800d02e2400d6004802241d415a405e19040d81441103e8454a08440064581d4000801403640300c9110301d400868203000820181101003181d458203000138050020300303041c150120b5481e6550f102c8140f094102e03c0040c1401070800b549961509000c8000d98802d0320031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 137646178 1250 137644928 137644951
    0x21302190e030f0d120903030e030a03090b13080706182301060504021201030f0203031c050a2405090a0605040e06060418030c1e050615010f02010b1c020303040807060206 75
    0x28038220110004e00401c410743c0c40c3d5101c08041c40e01c8580e81c0007810018000314185034952506801c502c5040000d4280012355a038081801c4075641042440300c80007a250105850729110480d0104001e5000c030f914480c0e203c00b000a080781c1c00701519a10911210004000a010002c00d14203201075a030741d019088200c100802400b6643e4013003004034404c070800403c846100744010004250042d401c400c1640c005070640749013102000031410610344001103021503d03542c0042c08101d001510800180c4243c140e00600181c1482c03180380c00e2150301e4410940b01d0041100002c1000310550868002040050401d01c00c50684004031a21050b04030341075030149142c007500c0c8000d00c1c201e0f02030385001500360302e42040c0004592520303541210301400c40c03524094510404000614100b1129200d24807c0a841940803510030006226207600084401107a05044640046079905041d5500381e01c01d034582e480c000d210750301c042429409a079001d01703014099881c000038500d0f00422900e01c1580c3c200e02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 137647428 1250 137646178 137646193
    0x3030405010906060b090a090213080f150c07030225080f0a110d0206030103081602090106260c0406180b120109050a05150402161e1b06020a021302190e03 68
    0x50000301400751b041c0650340304030100400c01207507005500074480e01e0392603003c082c01075448456061408950401d0081e040e8803103203540c042e0008030095035400410445181389085a40d0318020354030590844804000c5054507140c20300e16803c00300c508014003007801500c00c2030341c00b51296503c40050344402d98022030003018545982c039000c2d401c160300300d40c000c20705415642552101061901711401092601402007003000160b5a075903a164003c03e80c0341d0f01c424125044c611000089030b5661a1004110310200038482e0030442e003010b4400392240e9261040c0759952080e45144808081d034804210500006445024400c040d106d84c2d040c0c0302280c4041c031203034554040c04000c4500032910360b003440020024903170305850300740c0081c4400d5400e41c644030f11100d01c13a240d28940980f0600c00302d550102c0102e400c0200001041c0c00d0018282d0b1101c00703200c036403400740041d40314290b44800030710501c00c61170341d030b2a4540158144e64100310201c046076050f10a12070054032020120901610911580d203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 137648678 1250 137647428 137647439
    0x7080606040b010f050d0f050a0227060a030902010c02060a0e090702070b045003010203100e180106060306051c050c01050d02041715060306070507030810080303040501090606 77
    0xb440c54801c4182c0d40c1c0400040091012a10f40c0c10022040c02c22a85407010407200384d20f00d020302030044182c082c00503910200b0300207440c0309c803a0004003864550080040c00b4070b650b4a0201359007011155007004150400035200483d184840e00c01c000354400c8000c9115086660b1000310550740e03100c2034070000c8040d01e407100140c0c0e03608842d1140d442c2822040006000c401d185005203440032071f0404040c54182042188450401c028070805444400c2c20007421600c0d507203a0340c107404170384e0059008600d1420076000307404607180c19005101691080e0300102e01c0310603100b000c0080c0101c03481e008211054a484009000d45114882c0f14400d0361129510130000d008600c103c58003990102c02022481c1c1848015078051300404c0481713085941c00c0c0030004644844c030524044840000c4080d00c0d505420180412054a0103890b00380246e004c4402c100790560031000b12004180c05080510311941c13000401d00d86204141c109000b03a020200900081210540211811070301c260400d028068994 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 137649928 1250 137648678 137648681
    0x4020d0510030b0c1c1d010c080a110403171813050103210e0112110a02250b0706020c07050a0b03040311010b0616061b2c01080a0c031d0708060604 65
    0x1241016501d0554981e83e00b4100c080e5000c0b42c4055030080c09124400c071b2100c952400c5500b803807200c1011504400c104520702c6c1c0c0354442c01d142581038442c41400c00b0b0840d119030f800e4406614003909c04400c0010700e24400e441905400403174081c010141782000c00403a100102400081c07008803032a1200e507180450f25000191014024019656041c2d0200c03001c800468480d003010368000c4490340d58541800c0e44541c05001400500c03902d40080851441414204414132422205001d55808400003031141e1102c0d8400c9030442c03500001c02507100c02404002c0d500b0030000354011603008007810000203001c2c010781d0140d40f00394000c2d1248905669021400c1c2d00780c440d031840140e0b004070108214900d18050694400b8200c3c01504002031402d0198032088150f0b01d080d0146000c100c0c420070401d11496140b841500700d030700da00280f01461310050000313402501d0162106c010251950380c191241442a807005800a500101529803513000344403441c1c6607161402100014003581c1d0000e90a41401d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 137651178 1250 137649928 137649937
    0x5010c1407020405060a03080408070f0807030201020d1d03030307120b31090602030703052202060403020d1e202e0212040621050402090c0904020d0510030b0c 70
    0xc00c60149044680d41c20800182001031185174040554440440410000000b902c05802d00c14018121701e400c003c211413030041582d00500c2194011201800140d078003041144403800c1e00d003071030400c021404101402c20a61000c0341501880040104013185921038a00790300308007007035420040309403030300140407440c0d0112030300da02400030901d6080320101104004520203490411300007104040c650301c9005903842660714600003034540f4140010301100c6500daa801002c0344c582c0c804010000e90218401e03004a10000c1e01c10908810000240204004d480704c2010401d0003070407062503a032410388902d440c409441b030030700c001d03d0040c41801c0c1040b920083c0c07641c0c1440128134a03400307544054060890b40e842d4503411806041d88880115031401d01074030140c426500ca00c50305016900000c860f80721038402c05a8094240800d003c0503840e207240603500400c10022036a582c66a403004100070344602a11405114949820016007919084030f00003035070700c40c0c80c140819485035201c04816004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 137652428 1250 137651178 137651207
    0x6090602040509130f14030f0c060708100602070504050a0204050607060f1508030304020f06130b030601080f0112141f02090a0501030501320603010b03150402030910110708040f0305010c 82
    0xf0005ea652022071408107170000c000c1c40703510443e4500891a00851a280c000420f0268568000014040c0c50be400400d520751255903031060f0030080d4039119009640d40c00360300c81c00f0301030359442002c908014032a4044501800c8040d003001e960320b1261070711400900d595903029580902d0a100c1004628051071150301700c4441c00700031821522503808000c0c00c00043c1503102c1c2c3c016002c03c00101811402400203009149902c04c0c2c2d900d9181c440300162101d00d00802c1d0751075403800e29005114400e590340441c4180703600001d43c1d8012920081010303150003024521440340015a40c038080840080740c0003000300c280d0079100e003024a50781e08019801c1d10800c0c01804040c4401c1176040003d050050300040ba8800ea651400c0066402c90012a046500c02c2c2c01c100703250080002001703000341d48068a80c40f01541550110b1940c50700c00c090541f1130840c1084100c0141d1941146030003042032100b030741d03021030b089100c1a5540d0743e14102c800700d21440d4807084806500703154180071164001e5030700f58038405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 137653678 1250 137652428 137652443
    0x70504020a0905130609060b041815060c02040f1a0315150108040503070b04060e010b0f01051b0c03010e010b01091203140c0316030302041e050a170304030609060204050913 76
    0x9003443d00b04850003da90b00b0012200d41e44000006001b001409050000e03c81c2e40501582d90b4100010030f6041648020070202c4a42000c4503681d195001d20008070403684180380c915503400c0d2602c00980600841e2115212090400d04a00a01c05001030a003840110840480780010300700d10314128103a01c00c5030f0329904880d11842a1525501480043c0d074010300c80d0043c0d0f4900f420340c1c0d4a00e28175501c2603405a440c5981e0346c1640f00610002d01c1007080250301121803400034600740b0002801031040e0303101c01c00004d01070141c0c0c82e040e00c8104200e00d50150000d0082c0300d06140c2ea00254000e040d881006400203001c124005009400c01540c5044d99405955640c00319100c8410400564072003040740900c2c0c8001c001030142d40d0114412141d11902c02c0d900035a070380340340000031940386003024280410f00e5225075082200391344010a0800311030030075086d2415014425222802c50060f80e001034196403c043c0b00c2000c01078940c0c01002580e002302c51803081c5498040c0717418000e020144c0c0080410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 137654928 1250 137653678 137653697
    0xd052409030d1d01110a0905030309090721091b0f0803030408090a0801021b06070302040605030609100302030d020706171303030b2202070b0c03060109090b010903140f070504020a 79
    0x2445036040048050750b240001c0328002403a565075400c41701ca0701a000f41c0e29401103814460310b13611a404100400f8100c0003941403641c03000020f0074140f4050000c2e82405140481d210403900621b0495454404006003041104114184803220407648124010642c0c40040f012840720400407001082d41d440704025405c5545035501c50710300d588032540047d8000c0010b080081d806209000900004140203805129010900c0d0614600b84000d4114030901d070050200707010700d551042c103681c1e0015048070440c0042c0c0350942802c20307050140d08040d4160080c42c0700150410f4000514000b00c66243d42c07440e40340424081280c490301c0042c2c0c0c2c22100789800c12003520109100f40c02c0070030700b500010315082d881c4d021218005d00781c1540070115608183c020030250144030540c914180d00c400980c03411380c510302d0f001d4002050b002245c013a100c000c1d544d40a56180c203900c0741c0c1d484400f0355845050011400303424a60740d5555038503a0b100b2905071040036004601401c103402601d091424584828548 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 137656178 1250 137654928 137654947
    0x15200109050a17070f0b0912160507050a081002030c07060c0c050708060f130c05060d0e06010e0f04150608060f0f1005010f0f260601081f12020f0d05240903 69
    0x11b01c0a011103000d441492010341550110f04014009115504081c4c2e09140e8a45070040c00e00d0b00d9a4085442803007200c4081007503c50118600304510b64100f070040c0d036030b51b840101c1d4015018013940a0011803519240e0400260803041e2980d42c1809102101c03151a034035101e40d41e0b5454225010010300c002c2da00030a81441010f0000b2045600c5916440f65094481012510b6033304204815580c40380c45200f03075145888144055400b5056480300d08003640350035000b06000b000e003e040140002c4007004221a0448141d01100140c0110001e55166041080004000b14002d486008510807800c010074a84250042414102c0b00180c5800b02c1c950140710059030071440b0125882c0900190385056103030950024121801b07200381c01110341e001d0401000040c403100c001004441d00d5141d000d107200700805034212420480380895544c2805910520105150320001c1c5079494004e40c2e007998000030403d011805403200402c51344942001c510481c1c0301041d60400340c1e00d110468204100e02102c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 137657428 1250 137656178 137656193
    0xe010207081b030f190309050604150e010b060a1b050703060f18150203090106120b160216050402030a0b06270607082208030a030209090a0615200109050a17070f 71
    0x1001500c03030071300081001658480d5810030104403030440d88bd80c800900c2e4080001988507034048a481200200200b04103100840c00341d01c601031480f410702400ca68030070249105401941503007a4000309031000c49680f4900140170b882150881000c441c14006103600302000c0702c1d90000141e802412410341a8501c075001c0e002584080c0108410755207411000c60351494000144000510400e8000380511b0940030326044a03114040c10411500000038443c040e81030100c81200740c5008a40050381d94886c804510010841ca02030207412031000b041c01c58070306101030f2810851000b200744401c01103a42b40c5c00c005261051060042c5000403d11004061216420844075904010010701c0ca0b07994603220040c3c51038011281c088002900041c0100c075071304140b1600c2d50040c0c481c200520031507041020001c81c105000d000c030300130000c6144000031890f11003a1400510100300008004100c03a034100310b030306c94190f09000c0d1107440790504031003218034200046031a85070300306030f68400600360380c0d480f4403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 137658678 1250 137657428 137657467
    0x6020d020c121009151805010c03060513050705130303020c0111010b0d0b0a0e12031b03040308150102251a0403050a12020f0d0801080c18060f040e010207081b030f 72
    0x4545030740c1c40240b104540020312645400c0c6c40c500500304007012181c541030382980e80342d11101c4105402c007101003003240c9030341c0c1140e034806080500208946c1d445240448036070058890084040c8100d040000a058020035040440300080c1e0300c491b50860b00c00b000509942c03112000641004800e20070f00003142ea142c0d98150032000d00c03c0003055200c1500c450500e8030200008130281881c00201b400360404205841c017512002003110710b411842c10f91800303041c241c002030801e0401410340801c101240c3c400c0c01b0b081c0b16240c0000194a4400480000e2111100f140c010010a10601285240580e800b20251011654408000c0180708140e50314030540c603548450320300942c0f06000640208140a0003c640d4510056171389400543c541106a803600d2100500c182c0030329040d20a800c00c00d00c1456029901c15000d551503041d40110001042c0101140320702d0300340f154408501c44c001c201c01c40c40240750124001d142c0780504900348285607100c1c4211140240d2400c003c00034078920500e11030005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 137659928 1250 137658678 137658683
    0xe0105100603020f130e061003060501021b0d0b100609091803050c030f0309010213051002150907050402070b0115050a02030403060903050c16230d0209100f06020d020c121009 77
    0x10360034412005d8002d00c0111282d04410145110b4004110641c2014030700707001501c4044c83c0c1440307481e103000000b0351140354504907011601e14110030502d003925a40380426017542d0220844031540703044070344445c201d8980c1c016580007510300c1c000040c0040715400307035000344c030100745101d2041c0202d5175090f0f4035544250b0841340680800d1054078084d01c1c056015520a100d944005039031000f181180c0a00048180c0141e0b10403a448000d54802d5607000070500e4001b903241280b03124a46904054034501070740c6601140d40305000003552400c01003814146030423600b28007a841980c0340240301c1540c9500500413000b006074410701c001c0001c01c09942021111034002d090051800380b205a0310b50904c00c0703101d45904601e8560204200c01840704003810500500083c8099407000e00b8000101401c840c11070191085814201003014918107030803403401400044110a0758030340e80c03840030391500010400a4058001c0144d00c04582c20a00088142c425022019007103c000001c4100300400d0060300c107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 137661178 1250 137659928 137659957
    0xc1701090f0b03060405010b0108010603110d09110d0312050c03160e0d150203061809030a0c060e031b0d021506040507110303070504210b010605030c07050d05040305010e010510060302 81
    0x55000f903c050220038052802400081400c445200025001c0171060b80b00314101407601c0026802e061010040d00d00103203205130003103001c43c0303941840118a0083c03c0300c103500400c00d003070080400d5040400e0030b000590940c000c1c099036994034024801c50100321400b41c084509418440380e480d2242844d5220010010a01e0605042580310b9141c0c44001e484c42c24800360b07002003482003900d0021200a68207844140340720261909000041c0c0701d02580000006102e200b81581d0b081010a4000d0108401a00300302c03130711140c500d070780311201c0102030549500900401c104001c5140c07005c124503404403a141c01482c09601c900e020f0100409008000701d04014842d000140c42e0b40c0207100031409071740131381d41d1103440d1402d102c0c01041c2a154400c00550154031804440d000440740c00100d81121903600304185c0b81ea403401140b01951041c83c200400d5802281c482c40c41e8541c0101c0030340140c0b4040d038001c000c0d509140301d242d4203d030001d5980240c0b040036540100f104030711176001003803804140e112 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 137662428 1250 137661178 137661191
    0x403020708150403030b041a040c09050d0c1505090306061216030305030601090f030506040f170705030418090b061201110c280b0601030902040902060c010c030c1701090f 75
    0x80c14595041c04000c18040d0b0385062000f850760602a04030180c00c22030701000105039003d0200a56082000998001ca03210041601000e0142d82c00c40c0040c031025203c2015002c06103062000d44001c0c1c01203814401502562500c19031040c4180d40c1c0444010380201006d40326081004030048407120514240d21550b00768940454181884400461080e2211034680c28050009855464950032681d610f0030950020004903500080c42e07a08035400c00c5910942c04254117110308030f04010700050184c1c0350009590820810300100038404c4602440201c0b903030030b00380240c040580f080400060160700f40c220100342d0900e045120199106846000001c280c4400d544130026030308142c04001e41600440004107654021725111038170344450450074100716445540310000c0c114003400d564101680c40c4800002c41d100c81d030201d101560000d20242c2c070b44051410680c045d00c00f559030200064282020240d011307004002044120900041d1106980e0030442e01400404410ba01d400d042601c451 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 137663678 1250 137662428 137662439
    0x108120909190f060515070c030b0702160605041d09100b27040b100f140604030c080102070c0503070503070603020c03070605091c05090a030206070309030b0a0e0712050a0b04030207 80
    0x42811404101c41c01c01113038480c03501082118585902141c503100e5441089034030300190440c2103103c1541d43c841c103000a5902e41038000c900e4a59000c0c0074901c0c140c004800800d00c181c100000d0320071100c0081c02c1d61070f18010380210029004054a28048950101c5200c03511040f440d005515000d50203490080c1e59240080008880048101e285480c1c00100f020b107c28480c07070100c41039111101c03a552106040c03818160300d82040d1103105856000003400c90380d2420340d50340b00480b8002d40d040342c8020b03d0f0f185c0380c0318018000e6000400488030026981c00c001914100414400e0440d90020080c200c070910340903094000c5d50081020301c201d0700040103880d0001e001846054041d541e0b800c012700c12000840c03480384181c6e004070760110610100380041e81d0a655841011015680d041d14038a4440d4420f2505403500d0513a500002d2900601c403041110024059000684a5080e981101c000c00d176105040388840c007080d00081c1260308625058004210311200007a0407a111f881180e0b951603691 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 137664928 1250 137663678 137663681
    0xd050a120f05180105010503010b1f09080303010902120714030a09020a03080a0c0201020f0a020a1208070605010e060114040812070c15080a0507080603100c050d02030a020c06010812090919 83
    0xc0b0b0f4145845035902c510700c88500c000344078141c0540000c0c4d008010b29030b804d000240c41c22115420001c082031403100b10648403441844000002c00840003181e4a0f96103502e0404082d4010000b40180c01e5092000100390a02c10b000402d510b9609942241c0b454982240e02c401030121000266041400d5440010001d0304400c001e0140c0318055444440c0e1071040e01c002030401e04604418000c1da170142e500340002d0394600f95094121101441d00410304e0b040c0e0b01c1e000c0d41a0042c10383c05010307149003800004000f041003030880d01c290426070f00d880d54102a140480c1a034000e501900300103512800c6203840c68007840d0010000540250318070348031150344130041c180600b05010712200180541c0c0c2445064004d60095030b40103c1e45050070022480d1000c00b099542000b1448191516103605450300002d021740201c0d010100c6401096649203421040c8401a40c0100600000c0d84104000000c10100202d2901c40c2c1803002c072405482d0010403400c0000d5180098010561080b14200300702d1150b202c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 137666178 1250 137664928 137664931
    0xc0601030b0f040c09051302150a02070f080c0607030309020306040b0417070302150705040b040311130b131104050a06051209010b0907050f16210206090a083108010e0d050a120f05 79
    0x22824402e965070b402c26030090330b2080aa1140c4001014848280b203054400308841000720350035104070781c503590a070400700e000d030200e070340c0c041d405000381c41c188814042001005c0d40b21b18080c10386032180115808540f03049104942000c2e0041e040180207585451500741650f4020b4420300d003150901c1d442e0a030240d050381c416441202c03143c183c00c1410580d820958403404020483d02020450382d03420b280031a280c1c5800728102c000c803e554040b00b50100c0c400c001030710007402d0060044000340e034648401805643c0070030400719440d85600005039164405010348008000b014083c160f9a07203848200b61400e030418003110780880c5050200360b800398014035005400703e00500742c039101440b108160381d070302940740300c03c2f1801c54000c0420440c0309140015844019988403001980da160490380c4014046041c8c1141408052144400380e0400703084000c100030f83c1d4150000b0410035010a8180340daa5042e040080c011501c1070003412189400380003992840c02c0110b00c0440d01c2e052000c1c5100480c1e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 137667428 1250 137666178 137666209
    0x6090a08030c0106120c0303120e010e0c010311030912030c190f030c23130509010b031015090501030f140c1c1413080f0c0601030b0f040c09051302 65
    0x10208450b100e800d002d0080200810380f004841201c01c465440d60174840e0700c140000f40a1007070340765542d001407250764806a03c0040341002000340c0400105c2454070380d44034242050000e800c20a690300b0100303c8504490180d50114020078403480c02c1c50900e1610f03000145800e00d010030610102c2503108140b0b0900443d807485d070385c56446115401c1c0c006002c480c00340c0c081e4001c00481c1d16080030320700411038806a81484a9843c2915054035100b040311050094020070b8100124000016149103901d000e10b0007508195007080c451600c581e4542c0800074514aa44001504944100450350099004044101e00d15a0103d080c000520f04030b0f865101c1513f4001c005000001d0042400e2a2018110140ca0f00e1250a001060941c108140c00103400f03055803040d0355101e4580030401000804480382c0c02400e0154a0f01e44040050164880c5402d100548420100034005611106c044901034401c1d54007040740d6606030b0900d4403000042c000100075860207600440001c0150b81c811902d01450f14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 137668678 1250 137667428 137667433
    0x12030f010e09010c020606040506061e0a090e040812040f1b061e050304080d0b0901030f021809030d090c0503030d02040306060f0612150e0a05100b0a170606090a08 72
    0x51400d15208031003a07004103103203041d03407408902c003d415502064442d0030010440703002c2117a844490018071940b00380f4003940144010403d18903040c143d4103025002c10034140d103910032015981c803800d800d16582140c0051079081c04000072082814101901a0024010860217409402a42c0c40403510940407100f00b50800544104004903a030000d06042e05080e824400421850b00a8004e02030b0302020300020300070705012440c1c40030102e0036032120382d01000007081040e10356940d052140b05444007000a90054401007641c0d02c8a442400d81140607014030002189003030540449100201003401c1c0440d10528094000106540c0c100b01502c4d4540041c240183d882d45585424001c843d0658030170760100c130350802c00b000221742042003a04811182c0c0b1001c0342c4081440081000395040b0b412001e00d821402043c03202c101e0041e40141d201d00707080d1448503011341d1941c03140891400b821401c0000168540c40001d803203261000981c0d004000030b07201500302030650000650700a42c6400209056 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 137669928 1250 137668678 137668681
    0x2120d060e0f06090c1317030705010507052101030f1b0b0301060e040e0109021807030219030b01030e010b06030109020c07030204020f1306090b03180f0f010b01030606080606070f020312030f 84
    0x2440c003d044d26400078012202e0525100c0d082a100054000c02d1043d00c3e40005a5021120880307003d0003240e6056a104008100320710304148090130036000500100044445003001c42c1c40c054038003040b2410303203811855080210149036110205001400d600c040f500c2c0240c040040c1c0750350488059030107041c143c1c80340e00c01c50b9299000d210886204040d01c20b2568108a0810003503142c41c00d440b2040b8900f000d14200d190384840d4154060310034001076015102c24100b01030301e040c0e8582d220301d640703010076038044c855122480c0786070f0700341d820084003e03a111501300300402c00322005a00914102c0000c400380d90030107a80f50009000c0380c000020b040107141c000600d1180440308610400d001d0001130516801d81414030080241d0390100401e48203003c21464081a5a0354003000b00b50300300010f0b00102c4404414242039a0f001e0010500b0782c0380841d061810108102d801200701900c6510050185130810b0f2881d00c0c0c641c121a018002640c040c080c501a10039103011175402544103298a034203074141e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 137671178 1250 137669928 137669941
    0x2010e0a0c050f0603061507020316080604031419050c0c061210060912030c030c231905120f1e030702060604020c06340e0909070602120d060e0f 64
    0x4210002c1c50444c800c010030400c0080c99030307a800301c0c00459403ca620341502da88040c80400d02e0482020700c0074001025481c4005020300c400250103118034401c0d521141d000c1528406007001d4011080803000b4421803601d965115803150010344080c1068504079138100b00280003050f85544001c1e203250880580380c0412843c0a030a6644400034046858592105480d01145a40c007075905803004041211080c151000d040c8030318015200301e600704605404903031804116510000a000c940b5809004090310010303001c1180090300400c64110029103410045040c0c140025405060016404a0140000c082c2d0742c04c54400d061100482141e0f17103a0743c1c140301d48084e01e010001003103d84a10f00400c03018502c0740300401e0080e00004500000003800030700d00202d40f0403c440702c42c540030f81610031a429071a6030b84012180034842c4280c600428507181c140c11542c0315580e03400307100c0141c5d1004000815000e40e01c001480d100c107522200146940e2070f040d83d5000170900740d5106040040e01e0b814401d0b03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 137672428 1250 137671178 137671189
    0xd060b04031202030a05030a0b13110703081503030d111612030605030102091e01030608030a03061d06030303041e0f030801060e18011406090303030403081807141002010e0a0c05 78
    0x10701d203405000131418560180d5004009200c0140305d2052151540309610f00e5841c1c4d0342c810b001e050f2a0700010300c081da0116070403c0d055000410240d0005681d44003054a401048032034010700c0d0b902801031440c0401d039000e00c0c800b030248184d000303048600403c4510080913681c02c0c4511050301c1b4020807080c54465100c0241550801c0e0003541c400d074410814141d4544e03906818510b40b07481404464804601c03000140c00800c07440d40516198080014007900390b5a059001a050350300e201c925008000310450311040201085400e503805034800c0010a0200320014501c00d640814451004600703416560b4007803040c052644100c0220319100018040650400c80900804805680c0103040f045454842208000d040c0306049805104e52a2840181c5444040b58005034000e42200e56034202480c00603d0410100c421104030031440c00800c4003c80003040300d00440d00c1290b0f42080d080303004030421201d0800c1d1602001990b5850202500c3c0071818083c610120340150341003200185030000303110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 137673678 1250 137672428 137672453
    0xb090708120a0c0201050c01050109020c070e040503070803180a030201020d0c0305040c171e06040203010b030a2a030203010912020106060507021804170c030c12190c0204020d060b0403 81
    0x9664200c0d9040c0c410012076442900c0e0300780030b1450881c48103019400141c0d00c030b22800c3c1c84080b01d5400c120021443d048603400429910f9441411900390954401541d038903d00f041c2c43c0203020360020803901010404080141d508040030156810040005c0c09903540b03000109002100907075004900d11180b8100b40c41000030410b01410700744400c0c50a55a41042ca1009004140c140c0480030800e40c0500703020400c00480481c0c100542c101c840042903084c0d0b0719501154200e200758205a500c40702406c0c08504039010035030001e01d01540c1c0c102e01c003a80e90f40c1c4200d4001a903040003402000000741e40c003401101500b40c000d40b0303011506442403c0081c02c0d10041c1c0c120700c05020382040140010784450348c00a02521440114a00c00c1d12940741c040344000e07078a180c1550840000c0b48031604224084020310700320744100c0443c0e40c0140300500000c12400ba600c038a9015074603a06003030502d603000d541030b1041c541c0300800040c5010b01d40d012400c21203940750800403550780045014010000c41c5a40c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 137674928 1250 137673678 137673689
    0x130905150f060901032a0c0516050112020306010c0b040b090114070c170f1314010305010b09040b01201e0307121d0a06050726031b040306090b0907 65
    0x301108503207000c0348031481403000e114105542c0b2500d011400c07200e4280c42c22021100404084c1c10f81400400400051000c1000e607644d0048024810141001e422070008444040c4c49075844098440500e01c02908000c00c0a8103001400300003000250942400d58440c610883c0345811506100d40d8003421203c3c03038240804012241c405006829801c040005106a440360164002024a0b06044441e020766068612040400b08210384411070486100098a2402810148680c400c00045007658802c0c8a441200c4400b04402101e5040542041149034018140f815030205602d01c0080410307101c1014080d40c0e041001400807164201e0442480030070703440300030b42c103101007a1145c0d0444011481d40d842413000c0300213041c4c09440c89940702c12002000400c40c3c0c940c1583c03003070041e1490b403123210126000c4c601c807058546440d90f800b10b0008401c100300703400c1e42160340304040034040000303e03040b0355230000b021f020000000302d0f079003c0d018809104500c08001c1d0b0034040920b9250480c50b4101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 137676178 1250 137674928 137674939
    0xc10050d0603031e03060513020d1401090c140906040306020901020a0c0807180504120c150207110a050d0b0103030e060702030303010f140a060212031003080d0603171201180213090515 81
    0x410055442c48021081e23440e048900598034031b00c0005c400001d000c001c02407020300c2d0300c02000040c0b07600c190707001803594815500e98280d83c1220b030102c0201071103001480340d40400113100500c0418a254080e01d610803043c0101e40c0d0358840350f00c5003e840d82095000c0042036100c40c105000c100440407540e60304540602c0f0034403150600e5911031a81d161130301c0140c010894100888002e02005449884001002101c00c554a100908001c0c60b024181400c05010701c1000304002080d00b0003040d440e40c4541c000c10b41e202d0300d90030b540d81191914103404803507a00203810702039000036071382c11b100a41c028151000001d2503e40380040c180f00702c41c000845284212082d00040200c0358002c0348980c8140c10124455030380e0398452901101c00d040340d0300003030480b1901050000b07064000b50703c00d900f581e00561503c0440340201d20481014401c43c10074005420309c4200400482d03007108110491110492405810302c940000041c24031000d41c0e0200e0923058a800031301101c2c0741d080411843e00c034801d848 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 137677428 1250 137676178 137676191
    0xc010603050d03090c090203100b030f07020d09030221010f02160203070f0503060c030a090c06021608120a110c0306130b060609060f03060414100303140405030c10050d0603031e03 79
    0x498080d08501d40c860206d64540001c001035101982100480280240b04240c0344c0760b003030030030780200010700848240e0054030501c40060400c60042e800c82080300c0e4001e0030312409104a0701c42d03440421410400c40d543d0740d203d00689030344070901d001070200407045040d0000007414600405181220710380c045040c03c105480140b00ea0f4038045841c95215940c000290303070b241c440074480402400261000b50803508400401705110358081860703008075140e015034503d05c5403204607098541844218190041a0400107095002d02502c2031040d2031b140482981c100d040d0f81404070741001012075000e01c091079240c50850402c00354041060f0001029a40542004913120200e0024400d5540c1901e11f1080031000071402c1d581d581200c006145085c80c25860b504100d480502c1400e481e000440c04284008000c10840d81560141c5013103503170042c01010f4164030181440740541886c06071b8810001c08118004d02d0344254080d81c0c000310300c20382d82d4020300401c44d4020040070700b0309500c01041504080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 137678678 1250 137677428 137677433
    0xc060a0c1505270a081207030c0f090512030f07031106130302190602090301151403010b0a0e041425050415061d090a0f1407050706020f0f0c010603050d0309 69
    0x4811290743d403c242030140700c0d201404410f251001e4888020724120000924030742101c1200006401007840b510140310300d6488020903110444034021110019408040c01c011515042040c1490240000203a914100d0501860356003603000c12400da01042c9000e0010805a00c20002103600421055241c000c40700c555400075180c51000a15030200700240d0411010f002d0701d60704440483e60020001c01c0b00c0e0b10307a180d10302c02d00a500c0c030032259100b0a5202007010390606010701071210030001e0800701c240c0c1c1026150302130701d039000c0c00c01d039078031150b250906441400803c9620305100b0304030804a5102040076030b4200d0100c15411031409181040c0005000e14248070808042d10801c0c185080d5410155032004095840348080b05d0344901480d0620031030011b03d034403400030002030210500c1454901901c1c1042108243d0704200091420800d0101040150307003c1d0440c60160705c0120328040040d540600c07541c0103407504407050395481108108200c4200004c04043c04141014048041d943c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 137679928 1250 137678678 137678701
    0xe030a050709050c09030313061d0d080c241b0c0613080c0106180b030118030e040204091a040f11160512160506090c0d12020c060a0c1505 61
    0x520a0607241a1100003290a44a10001752000c1900c05400c41361200060300c100307030726580c2d44c2c414040442c900303180070200800d14040c2071507082c4d0f020308041e18450203941c4410303080d0721540c603102c01401044486100340080541017810303550091a00121401c2c00b07003040c1414036001401e960050820080b41c0408107000c91500ea11424410341843c2030419410240710a11078071100d552194603003040407400c0b00d01c01c40c0c61284207400090410800c080341d0207140c00c840609041c0b850422440300c0f030900080c81408003000b800d03805440542050f50f07840851003a26a0410b0140300701490030400c00d00350505100e0000485860102030049070004c40400001d44590f9a0500601203010452030a1050420044180d061400042556019a00706246410b111001d0894560107a04049201a040084c814203039080c0201802141d0f42650b0341c070480c10181054160070b501440c4001c081c00d0f070350f80c805008045800d03110040b43ca2005c0c1b5101c410408551210780c1c1c881d1402c401c2c0200c10650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 137681178 1250 137679928 137679943
    0x41e050a05150f0a090c0302040e07080106090c050f13081203040b0f04020a05010e06040e073203010501030b130501091b0809330103031806030902010c12050f0705010204060e030a05 80
    0xe050000440c3d459604120a91b03410580019420504120032240c2071000000d42c44101c8174904000c1141e240c4500a40050b200340c001050300080043c004c0b9203105c0b0101004040d008541a101c064856039a203c460504c40f86600b054180c5002008200520100e002500d40c0809085000744003442c1c5a80003c000366218018681000403814211446440712811140642009001c40616290481d0002c1060540360001e441c040314107196555200d0103840141801c04480b140c0c68116800d12004500800c04075510651103599031445400d140c45501c95240031700070b44240440d5102c201c1d1140038000321801d1040c0100038506d82004080754000c03400c0c4c140030300038610b207039440d000d0055440002e2503000c1c44e6401c2603c1d0900004205900300c03404c21076801c4650042d001165503080241d04035400d105000c0d0210f20044410000180548d2910a400307103103003056410440c1902c0345c0c5002d900849000c44880e9030028087c0145501700251044007501200146540035080c1d4505444809 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 137682428 1250 137681178 137681191
    0xd0906080906040b2d060f030d08010504052503050a0e0c030a0818030d090305010c0f020d21020f03060301060806070507030e030c1002060f16020c09041e050a05150f 73
    0x200400482e01700701202c1c0110743c001a400c0007055a260314081e20702d001e0700302920700600c102840c1c1300d40b200500380400d4110401d0310540342c1c504660310f060140700280c403000301600c15501d200030704041200c80022005a4803c0e01396000511880c00e8800c0104070f614280706924140c2c800c0d8150304d020b40d800a01c0c001d941c0d5004c0e10762503d55170202078440c550800b030440564940224252810019031255002c4112801172000340454205004c0513200d92007404001e030010381005403000ca41d28001e004807003480a80500c000c6c80d042c84240e260341240c018200014900c000041407181c0d0f803a09001761009080520050030481c00d02c260064040d101d283c0c030050901c0610030040c2c54566052010401448000d411145281d1014500940b1104111454070143d50340c1c502183c2200300c011700701520201117400030000e14040034100544c5042c001c2044035004442400170004840e11980555202d104000801f907814991603c1414000301e0045000300d4141c01041202044640399040d80203038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 137683678 1250 137682428 137682443
    0x1e0a0f0213020c03030702010c1707050a0908010204061809060506090111030d0603120809060906011a0405040c090320010c060513020301050702030901032a210e0d090608090604 78
    0x4105101081c640300114004502042c400720b0512940b8102000441c13041c146680200840c0c041000e0540c1d02c080b40c254043c0f10400000001000903010b040200586501030600d141e030140d0f611007460aa80c810340000c00081e40040c0301c800500d0301a44c80354081c00d800c400c00d001d06c50508021499030300034103202c1410082068440d100c490414022106050100e81d818441541c80742455074518000043c84400a8018400202c000b500840e41500940300380020344080d1340b811860240d15000304d0040404000304100001d100c1c1d030b5500ca802030000c415181c00c4041407460514000030f0070144e225014a901d841d09080d066039001500c04442903000c180010182c59030520164160562407009415610782020700103c00d400101405204009a800340042d9401065070158000c1c100050b07a0b0341c000c11840c0800c001d01071000220340c0400c014072400c4025112a401060302d01030100d60880f07401c01802c0c4c4011585c480644000b510340c80c200b0411500745004480ea552100420180584 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 137684928 1250 137683678 137683703
    0xc2e02030403050d0327061a040207031211040518010602061b030613090605040c080c01090e0429010f03060b01030501060e0d1707081b0109051b030a0210020c01021e0a 74
    0x21b1107445082c0940c0f4000d020401000403e2a1010007842c40c80c0003040104c050451107041460a80229003a440d415035401d0220700410011078042d0000f444409030422080c400454552202c0900303036407002c4c1c902d0340d907103140d40b40850207814441c1c00b511260401e80c54140011400d00100c046035042501950040c030485598500d010041c60340b840002c000d5400c0c58140000d1101900078141a900820705403000141c400c1d0064581c00072600c51010001030001c00500410b440c19403a80104484c0341e4130391b1040703044104030120684260400b140f2407100310000e01c00d010ba01e00c81c4482c0620f0030301b402c10055040c904050560050420f0383c42c13044c600d0042c01c0c1c0030030070b0070035641c0f01c8402c450b40d031341c0d498000e64901618039030403142d40400040c0b40204020b007604814002c4140e029004005803c900b60080302600810120011580d018421600e5507030060f1a002c80100031201c080c0c3c0580300c0110010002810610401d50469003000c48450346402080040748012641c0c0e880200401071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 137686178 1250 137684928 137684951
    0x8030601140d0f06050301020406121a030601030b19050402060426030f040905090307020a03021212030f0a05060d03080703020a030b0301060305010905060109020f030604020c0c2e02030403050d03 86
    0x10000000341400c01000041030b140c400340c82c0381e0009942c024070140f0a102094481341418203c0c0103501c1814001024080b61070712481076948400101401600d902070082c041c10302103803401c00c0a80c8103c82888e001020480034200d00d10100007281030413401404a030900d50001041c502a40c040c0c00340ea5200d20b2560000d00e03203180e01450300221400b040d030f0b0319508040003146482e0482c2c1301c2d90b0601400d001c00901c801034003004441010360b0090000590300d0541d001d0204091800d0a42800351044004103941030181c84050344c85407076030400529241c039088203184152007001c0c1003039000e009800c42c2e000c0081d4004441c0e50f4060241c1c40c00688540319054110040c040001d082034255203000000320920006400001503d070080c81110343c146d80e1007007000704910401075840074605050000c2180c82c80c141d00200b010b5100f141c21910b550010b140001c040d0482d05280031030001c8091400c88404041e070103480d882c0106c034006103040500d9078580c1a203031905890031500b01547c0d42030380c180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 137687428 1250 137686178 137686187
    0x7050a1208030106111011090a06080c0d0b0109080615150c0c13090b04140106060903050c06070204060302060c060709090e10090525060e0d110108060111030a0503150103061208030601 81
    0x510006c6018488051010744001742640034010ba2030280c40c03403200104100780180115070081e40c0841c580352620380a20b54020003090303000819410022881c400240110040102c2400340c0e881d0601400392101d010100b00c001c001c040061202c0407000e1091000f11100481c40c014280c034140d4000340c082528002240051115001c001c0104e0140410b00050042000744004840c000c117000f002a55121481a02c3c074841d1888000e04641c48440070031150b040c54805444aa88064004100281c0b658001403903900082d0304d031a46036100d08200500b55620031000b030003d204a00080000003c0c0230040c07526410342c0881010306940300c5082d0010040208075840c5041c4002d070039007500c00310b4010203c0d00f1110030304c50f80c00001d0481c008480366182101d04840d950354030894070290750103004015542c0c1a002031003d81400b035421000384ca1100203200800c14401c007035a64130ba8030316192803400603a0381c0c15544641014540072043c44041020f00e000300002c3c2d0000102501da556600c01200d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 137688678 1250 137687428 137687443
    0x1080907080f060907051c08130906090902040b011d090606190c0c0501052110081e060a09020a03030c06022a0c090919031701060207050a120803010611 67
    0x1500b03102d00c2002c400c0b1580301064042c05107130f000c0c042c2ca40e81d40e85d45003000711420701c0400d160035070f00e01c100c80c1a00160700c400c014500b052001c4009001c984da03400341001120840c0c0d20140d541a222103046086103014813070a10304000c00d081101106030401c210041d00410001c02d01c2c091598003004c502075545002c207031540001e1980501c0b01801038210020540c0100001c110307900b11080c6004501036000f60144c0c1c240d01689030150070140c0c14401c1241c09040d0242481e17800000415022803002024041d00c1d0940c0229000c00195208040c03806d4500100144540301e152b20b805044001030b0303641e0342840c00326909450104142c030002d0620400a00c9400c40c400b40300c042c0140c500c179400015101e51120800c0840590307940c0002d0809000c110a011a42e002c01a00804101076070240003080e4442c80c0b600a203440c1c41e008452060403008602c080c0c201d00c01590103e2350801441c82e00d022001e000d0940d1504e0412544070581c0c03500280e0006000e00c07400d0212412607c800c9660402004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 137689928 1250 137688678 137688689
    0x110f0f100f0b03061008070e04021008060d02100f1d060403030302070305040f2301020a020924040501090b04050106020f19082104020102190308011502011b0806030c04060e040201080907 82
    0x5580038180000705c5100c00941c4d10550209020b0070700c000911000c040c03c03192143c0d4000c0c00c080080a6140000c40f40383d01c1c020704883d4099400561140940c07249050f8484100c101c1c0c0342c1556410804a0240c001d210384514045e511080b460300c46007036244d070015181240e925082c00b68643e1442c1c41c003516180034581000e004100660030004102c46400c0252152500048540701d044200c1401284c480c4501c00000c0d402141d08000b20351045e2030303d4200300f404a11100a41110460b0b400040c0980b40d0a91241200c20313112540c3c071000e07250520806006100500090000c0c51700c02406a4807800380c0980555100f070000d0740502030041c00c0d01120301804080c000303500311909064400c908200d050f41e00740e0044c8a400380305081d5460f01000c40030036640580340d4008907881e000501c000c0d4000e603c0304800319501c03512543d940c1c040742d501c41030b04030566031540500344c6001d005040ca070103414080c061165091400402010985100f01a08240c080c030348000c841c1e8a0100080c5400803a5111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 137691178 1250 137689928 137689933
    0x2040c0e0303070c2c0420040f0212010509010e22150f0605310b09041208070305070e01030b03010e0f07050a0503010608030f070f0210110f0f100f0b03 67
    0x202041002e14003801910010b4000d400c2910078001051185d00318065010007a40f640e4010401251504103590800b0b0020403d11503604120b102150a5601403994100070680100e0074000c03c150041d0400c0c0035000c152050761080d8074042001030340c0c40d4041c0c0030020010b08148014807125160031480103140c0c100790040301c842c80c82e014100003071605032200404d092400c0d82c0802c1c10700e481c02c4080c0c03440784c40c12182d4100d030710a2070307411400442c03c10781140d00c180e84911fa1050760310b9071401d1038821406095404c01409001034041c00850000b408542054940700800584513000000c0400d014403c2c41d0000701080800c0202c0d006020400d4040580c0c070540300990071710140000e440307050711780a40b2103490b500d50b81e00c18982a50114080c0c0041d9400910a00f00305080710005007010b103000e43d100f029500d08580216141d81403135004a00040d500d03401d0554035010421540d00e003044624000d0012003c0f41c01c01c00e0300ca038200280c000c01c40d902e45541c0b92000304a50001c1e06580c600400307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 137692428 1250 137691178 137691187
    0x10518031204080f0607050a0f0201021c330e040f0b0c091903110105090607170d0507020f0a0209070201060f0f03030f020a03020606090a09060e0a050709061202040c0e0303 76
    0x2071441a801c248103001c0b140c07040c4004810004e1000c12554011003a640f25a420300401c1c010076154000f1480594003150b40c28000b1075905100014040244140c14800003400d803c8502c0c1d4402c1c0030300c4a2094224102e283d6100708003c004094084110f0b10242c540c1c001d0b80d11540703010b0140655190004d02515a51402e000c2007085100091420090880e80d0160034020410b03411410505807002a080601551018a09500034402003000a100502c224a080402d540b006030480c44080c1080c086030005c0354500c4003c0c03441c030409270003071788034001407400c202d405540f107070f4807114180002d026400443c081201d1310f00075001000640b103c85c0e88900107642380c46c0980728429481c401580022030005462950030f0001c0344500100340c059014107416a61541885402074000d008002503c1e036420b081004101d0038454480501c030310390054544040e4604016141c22020b0300300300100d5160080c10082d845000c0410038102ea4181d40114400b40954000d8492070b203030b00381c01c6400d40070009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 137693678 1250 137692428 137692453
    0xc0301090911032d070e340305010906051e101206081609050903030a0207050a0206071101080c0901120902040f0c080a0c05030601050f0705160902120112050c01051803 74
    0x224219030303a2288401252500c601c4410540c1d802c1039104542640c507002c001f1a040640d00700c0035a150400c50b40600381e0b480445d0951145e11300f0007502c0b94002980da10300503c04000341c1e001c0e1600030802110342c1d240080080c0000201d1004d000001849405000d80d00301c1e0150081070356001c10424901d08100c00c507621001c0b00e8480002d40c84004be19030b070034000400e441d42d051080314001c2d03840000940c210343d10101d0b034000942c00031405650921408650900581c1c65200400352903202d141601c03580c01d400030014055010140c202e030300d520b80074059040c05981c010702c07a070300c1c0000103800400c05200d03d001041c020321700c00849074051401d050040d081582c02440303103405151403040800c24918125402c850034081510f0150008001304150070103006000081c019007801181a503841407044c4015040106840c3d101c5212290042001c000c0c8851046020380108444000344079101c4650f035425450b92206840d8034180030b004a00c403410104031045c65100c004010302290a6070a080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 137694928 1250 137693678 137693713
    0x8091e0115051002210c03040321031a0105160506040b1b03010608010b22170d020f030904090f12020309040b011d040c0311070609060b03060c030109091103 69
    0x18140031020103070300c80c070019041c00d00701d4100b0f02c140c9855010303003901d41700c42c00c1090b020002d281c0c0246181009101400500400740010700045100d03512859001940003c241003400c1c000d26160189858001c8200c0c1d14001801482030407003003440c0c4183d03185101003002c06d041c803020601900b2840381e84108803c01010090240c01180a56000741203601240c488032554482401680001200580100031004031035000d040c161100454248030b4840000b02d07007c075032078a03030f000e2421580d1030501030400c20014490a00200f600b4405041c400074502d0b0180c2d628450160418005c0c0e03540c810340300c14020540c0c6130500d03003036202e03028071b07213940341580000d649410107000c1510483ca41502d80f901c0358050000440000c1a98112410440e10002004000d02c03800c041401496101d041e002c459800b4800200700145c480c0310000303640c2500d401d0000c00c403075075100c040340664044070602c041035003050700750790441d0040d0300e0110310446149403404942c2c40c0486000e0b010f00c1035042c5240306030180b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 137696178 1250 137694928 137694941
    0x806061611040501050d0c1a0c060403030b09010506121b0405061215040e0a0605070207090c110d08221a01030803180316032303010305150f060a050108091e01 70
    0x121403c0c096640c82d601001542407841034010302c040f0804c0c00403c41c601e1700e0200c040522413604440b80c10600142d203c241420412141100081e84d90224810b0740d180c0488168058007050303e15900304003040c250784c981d100c0f01501003541210505000c64044c02d4002c00c8802400c2d0180c40710744c5900043c0f0303100d40090025144903034100c40da050030503490705041c4900d040400e0100d004200902c00754071050001c105c01b034030442c1140203c510200301104c1501620000b80341641d5070b0f48000100020007410481c410300b00b181004000002e01800c41000304010801502601d81c4440c008068039000c003c51359542030301d51030507070201e000100b4032031614041d500ca0f020f0b0f0103219110154000d4955240d02c1590a500c1c0c0111520000d000482c0c411015030b0340700e60014101c0d200c50f2106048403209500240d00458081c1d02454600d03070030601001c5125000a9511400502803c0000018900c0000c5020f000d0405c901e0b40c001900c040307401c10002c1c400c0700115103005a111075148045018200c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 137697428 1250 137696178 137696213
    0x30313060801120804150c02040203360705090907081009020f011e0e0d05010e01020703090602010c0804030f0315060e030c030313050607080c100207030f020c0a030308060616 77
    0x418070000540c10100c614244999030740119420f18190038522000c1b001c42c903600030a81002000010500180c4a030701c01140500340710310422840300d04c0ca0b424100580e0f004049609080b90710100e114001030009100021750310304903000241991100e80007481c055041e805210a4800c0e60300101c0340f02a1503000c000354034000c0e28a0311041c0f0342100190b0303808065005419100200c4004203c40703611808000500c00ea00030070245000300c058889500307580416042d10800c2e580040e9220404d0340041c4460020000f500090082d800300d04000f92500000500c09002d2000c03000c040c048941c4268088040b8954a03081156540c1e107841c00100303a49a148140c602a100c0d120350941207150000948040155800c01003040c28284401d1103803e403c460320442c0c1c0094244680c011808003030040000c1d050081c64016100ca421313090082c10700c04d02e02840022340d040703401c0070529611144a1141500d8240c141680c1030344072000424990303c144044281c079056882800c03001c11200c1c035225503c60743c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 137698678 1250 137697428 137697437
    0x1204030609030e010224130b1e0f04081206041404030e01080c040b18040e101e0b01080a0c140714160f06080403051e0306012c0d05030903031306 64
    0x101c980e401079030f880812040588200041c842d01141384201b40c4402503012255212059000f2002d541e00341488600790b504400800b000310660101501c690ba40607406405000001c02c00d04050b2100d002d0740c85001251035500f000d01d00003e807503441d1a0800c0e42c00c00d40034210a285403030203090040110251104a90000e02d00f080420007440b0080d0030b0300d040d42d030011140e0b4540b40c1016400d03007286450700081600107403600020a040780d01030100a8450200e10800f04402c850741e0401c0136000c80802c0310309907440c03600d000b942050760f1180c58660f021107610030004800c10341d030700181d0b100308980c0907807000340100140e480b0800c240c41240e10041200c170400c44081294003840749043c1e10240c05200100c928145080021a108400c100c1d04a0300070704002d45080007140d0070386881c80d02d010088030725205c0002800f5403568001c80b0390040c07a02d41c0d400c0350b250340d81e507032075501c010000203c00130322540368a1102c00c240801401100c1305401e00604503551a00c0b41d60505100d00c103035200d4000800c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 137699928 1250 137698678 137698697
    0x90203010c030e12070c1a1b0616050706090b010801020a030e06041a040c080a0804080d0f090902340215030402090f0c1b0601151d0f03120403060903 66
    0xa800790040d04000c0010001500c00c44110f111140d006404c05c20065402d2040040000741c003d040d045e4080c0c6141c10f2404c002d0b5a1100200712035180b04644240e07048580c0800204486034208211540007050503141090759243c05042100141c030603a200600a586100000200064154014a10090241c40600c462206890420b446071001c49000d00645030700791102c0700c2544038031000c0382d2052041703220151454990703605c18a448510f03002240e03c014005001e00008204000d80c0d0000030142c03412180752200280c008143e4640782c41008049a00802c0f8005040e440803e440b4100d0246008001c558150528084140c0f400d2002a4058180001403140c801b040400302d9115070b4009c1d2420501d0f031100403e51000c5403000344003628001d001d0042803003c2c0d203000300c0302000c60b80c0750004150030b5042c40c800304580c00b11802d40b941030200c0f091000e10f03030703e1910b007081ca0210b174122005403501910f42d010a0501400c03d01406210000240c048100150b50744050342e254065550b1040c0c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 137701178 1250 137699928 137699951
    0x30a0e0f070f0b03090a02010e0d1712150112180b0c03100503030f03070c110d0b190e12161b0603050105060a200f03131a0a05250209040609020301 65
    0xf14402511445515048081c0503c00b650080107000240440680304203821601c64842d80c41800d0300d1901c1f4038008400040010310514079000003074200500342c0302c14035618800340001e0709002030380100039900b40e1580c0c84e40ca4400208000781d90b001d80c101074000010f10381a491030038a07510031501c803000b01464000c0400d103410008107944401c01c0303010700103183da210b8603001c0d228040c10440448a10300728080e414482d1700c48602c2c00011030300c100b40e1071046003002c02c2155158020201401015850180741c1e05e90309000064010b00c503c3c5841c0c0c080d036218450444100b0351403c2d200060583c442c1c40c80780741b0644440c00c0e81c883c02c840e66984c0400050362030b101000224408e46007140c2c0061800c1c030408000103001040c40846460349011190344a80208040b41107820030851490f401d82401c50400009040016050b60007c450046a20b02428194058090300a031400c50f01181492401108281c0380188001805078004040000c5460140780072000340c08a603004a01035401c04c0d00c01c024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 137702428 1250 137701178 137701199
    0x706060f0b070602340c08061308070804050402040b04080c0109060c060b010915090501020f06010f030803150d0b0402041d06010b0901030b060d06051203030405030a05030a0e0f070f 80
    0x80e00d4590003002c0c601503440c0c031000045d4000360700c5451003030103085452441c4440210f40e01c5c002c000c41a0126003801440c10094480aa240d00240d06074025404128800220200c540561a0302001440d291030041c140704100740520340100f070b04103100040c0840c4c040310500261027140d0b141e01c00c40e0780c2c50802a004580d1604580319001c0400e500d003009400003400340e00840c04482c3d062500500d01990b402440e6000c1c0300000000000c2030142c3c20911065034140728030000d05041000600761545480c20a0301d210503244000390454901101081000541c41c0d40d211340d40c0d4008100e03a525222605000c1c0c2819016241240f14601c0c006e0f040091503d60303100c5000307501d004000740c082d40c1c0c40c1490001280e440344008a04042d0780d0100008103035120303070180408803486040020f119092109011880c1d01d0a03a0701c0761154814410040000c000108441000d0600e10780f194a0343c07224004c2d800a402c000300c14403801d0140e10070400003441c0001d03184049441c4540e40e83d0881e5640e10081030f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 137703678 1250 137702428 137702459
    0x90c0503390603060402180a030c0f060219021002070b0f0d0506030a05070506090301090606030609050f03030c0405010f0507050d080703111c0216020a06032009030a030c0c090c020102070606 84
    0x2034001c82c0038000070b42c0f24030b461b602501a000c008008070300d15080701800251403c00640044911013070300c0360144011030041804401801d1980001c0202602d041e22020549a05440013482354010920440020b4802c1c003880d17001b050b041240588412030612842c0703158004c0030740400c079540781c00300044172841c001814004840d008030241580031b041c1011f0201c25441401c01c180c2542d201c5405000003026446501e0045000e50000a40d55000d4640641000280340b4900c07200d1f4410f100344100303200345c902281d0860700c003404c0020700c00070f2420050355140600c030405865409103100c0ca0404a4001184900c105a16541007141d401181580215401589a41c245070001ca1604003240358a5900600d50f00d05228180b5151601e5980090b0002e039140e000b0340c00107a16600540c00e1000922030345403c0140b02903c0c0d0713082c6205c6102103030340c0b420440c502408124851302d1400a000d80001d08002420800c0c5041c010690b500074040d010f54010101200c110785010b9000401440804542 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 137704928 1250 137703678 137703793
    0x309010c030902060d0e01020c070602030706050901020405011d01171608010b04120303020c010e0706021c080f0601081306291906080907050901031131090c0503 71
    0x50a00e103075041724100508074215141500c0d9420400d00340a65010800034004141c2c0343d0013555603103082d1a1840c00d890024089640c107030300600043c40180c1c1c000902159140059904020104017140100c50841c411240e0428070300c070030400c2c0000c46200c8001e9050194441e1103800481e60b8401e0020903a11a611440041560241f15240001d100e0740040c114804100300118891104903126400d01240d540709a0141e0f0010a080c00c203822a0307071810908071142d050600c010f00d8040c03034005001400504490400608000144280501404c1c101000750800400c12005030428104c0449000040e091100c001e1102e0342070600341f4114682d20910400c1007001c80b445890220181d1b00c90308090940506801500320200b015100c07451814000e602136138840011101030003d101d090340f401c20307840ca0b000b50006407001c0da2440000c610000d0301405040010b0075101e908040d001b461160700301700c0e8180500070840c040103442040000c42e41c003c01f0306018072107a044141c0410f0081883d101e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 137706178 1250 137704928 137704939
    0x31204080306120a080d02091908010e1b0102070311060717031806040206071b09022b0c081f09020c0c01030c0c0308160309050105180118031202070f05070b0309010c030902 76
    0x41c013032040d9844c0c000c2c1400380ea02601b051241054110b0310843c401c001d81082c540c4bc0c1d520340640105180400031304240f40304600201159500c0400000d480e04414000070301b83c2291408a24466101c030343c00c40c4c44090704065000351041c11a400140550301c1644e0703801e80b02c0d08080d0b8441010101094090003140d0043c0494038001459941c0009213054204080c03918028034800100a20320740020050b87e2040c100e01c00c11840c6010785108450b214000503101d851815031040501900050029005034101001100c44c4000a002e0320503100740c0e4101011030b0780003007998581440d0001e210318010300e09032801c0c002c00304c91150480e291800300320081e0000b0b003505c5c007050000030042c250740300e500410314000c62010015100c070b9080d07071010b03151010302100030f0104189080c401c0c0b05880d0420100115030f0705844098400030010360b02118111074483e400030b0500200840002e1724002c2640c80420f4511803a5150030900700c1c1d81040380c07031280550130400f44a8240b031081c443d140110303070300521 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 137707428 1250 137706178 137706187
    0x1012021605060618180102310608040f0303150b041202030d032a021c0206040c060504141e0405043804061d1204030204060906080a08070302031204080306120a08 71
    0x2000701c220174003810031110315582000b082c085098060b01100c003c41d140c00140c0320342820a14070540c4049194003032010082c00b0414000002c0c00c04640421107909498045104041510a050140800c0e80014864003002030b00094610414500e40c2c40b050007201910105104820180c2c00d42e000302100b00780c103003100b03082128088003c5600300050b4401d441102c0490701005025040c88425280c00005a4820810001001600e07803100c2c001d02294a081030505240041d6070f005044120142842003a00d85158492580c1058586100550060050280713007010f05040302c40045144100901c825604420300c0b003d20b001c11b0000a403020500744c010f1a41c1d850700c9010041041c4035038210170200341c00540070150170801c11071000c00c0d101c00391941e6403883c52040004403000b40d0b00800049081820410842c9004104985001d401c0455503903100b03281d00e412410b601c00d07829810f80c81c1110700c0c140420701c15588007451007240141d4000c5c5a200b110851140d0b11503541c03100034200c030000c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 137708678 1250 137707428 137707441
    0x903040501050f13090f09050c1005030a110d02030103080a0206092b0c02030115230d1211030a020d0306060201021606150803180301060e0906061012021605060618 72
    0x28010a040c201e007660840c42c4c140c44000403000c0d91044409151500d40720300112061010034440c80b95209004c43e201540202e881c040034085010081000c501540e0312000002a100c5d0781303003180d40740380503540115a250b03100e06d0441b019800040400005115280018860130b00000360303c1104004646941e540084070b01c018450382e148640d00c5400c0010704c403034000c016142405841c030380080d486580301e48030f410300402059810303111104800c10402914030001c152112100d420080d40c2080680680c0820210181c428041d0340e141c19080f40300014103005166400b03e44940c03854655a001d0180541d2100124240d010b0400f100c0c00025040c18120005403665014488044000003170940307082da201c0074542150091805c015800380c85024604035417501380300709000f5011155000285080440e0300c2d990310a0010992406004840c07420403845001d054400048102d01400b55540d8802c0c000c0d8004040e000310080f1060303c40d01010070691703c0c0c41d001003400000c40c1c5204101070340d100c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 137709928 1250 137708678 137708707
    0x70b0307050c1006050103051e04060203040206130905010303080a0908180a09020a0306170a08030c0a05090a0311041506020a06020d0b0405010b0c06070201110a05030a0b0a06020d08090304050105 86
    0x50012018010200000b0301846414000700d10031000030200000e4041c505800501a20801407041a54080c04400460058038105181c3d8006401c03c40068490345d0b20710104200784a20500c0c10507074000f0b00350000d85000c080e00b0060589101765603020310b5899507482d2005840307014100801480042c405101403000e844540c1d41d4000004010502c0c0958400c940e4007264488140c0100103034850300c00b84842450714444170010029500280240c1d44a0744482c0030b613004c00b605212403c800068ae5280880c4110155044650010407688601d0f542c0d180c40b908d140944518140100e042c00c45800d11030110000510840e485074028004907405551007070000d40c003400301d8001701956680f4108050f11540704442c0a4460020240e9940c0c1540702568603286000b001242168103008010844400c010190768141c02d5030306100ea120b803610550380740a0501c6801058108070700d140001400d6900040807030f2541c000f84c03260191030b120303019030a0301e81c803c90007580e0114004119608901000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 137711178 1250 137709928 137709931
    0xc020313090e0a020a06231213080c060109050106020c033d1107051e03070305181005030709050a050a1a0d0912090b03070804020609060c032a030705070b03 69
    0xc10058030f80d246619400034510000ea600503400180c0103110341e06444c0c060482413038a407012468500c1c00c210000d0320851f07900300f00400f80501c0740d003220b00d8442044800d0040d105154150000d0328011768446000300024a0240315440045c8200000513480d402d011408050030034004003e84031207135a05a4000c100d6002c1491448000304801040058802c548a00220381010800d40e80d0340d5000c50034135600e0940d0011804054011010800040c0360700001280c03812981420441d840365491707001c040303509442a41c1550401c20048280e01541d0380000194401ca02076154030318801e440c1c5050001440c030754050305404c0110008280420141407030100700041401090030300c0d00c3c6100f00e00c0c0d403d4921054088a45c04400600006140d812120380390107040c0c1400d040c5d0a510f0564001416203a010707001a0242400080c50100c0381c541808544043c550a000c41c1da8a12400400c0a142141301c01d083c0745141c0500d0740300d03481d820044200c0301900e4020004058240c20f02104a1a5500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 137712428 1250 137711178 137711201
    0x3070302010516060e0d14030106051218010509070306061d010506030a0608070308210f06010e040f060b0301090b010c020105191e02010e0105250e240309010c02031309 74
    0x81d00f480c094002881c42c0519118260f00b4400782c2080d200701140603040c8075844d0701074801c0820520041c0031007a03102c41528041814a1200305180e16500414440480d20321030117005c03942460104141030000060301400c884c412107041066980d41c80d0202c407140d18180924515400c43c000411407441d191f400b4503044000c0000001e074041d03440640510306021603104940542d0041034108007584142100070102c01d4080e46d02c596454410902d485201004002e07605100489030300c1c91164482c4d5114a10343c040314401008030940f607544540c40340d0030034801c003140a402c15040c040994814080c50450795810b84038907003048031809501c1a0010b42c00300d16070401c07d4410805440003840b801841441480350000074a00c41921501c0f403d4a10081003003603400906400d0b01721409407007020345544946450729074000c01202002800c4d403005070504801160740d403416214120640070080d40180c403100000c1001306880c8070113903124002c0303903d46482200003142c00c2083d20110f8109011102 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 137713678 1250 137712428 137712457
    0x140a0f0c0c15110c030303010e010b0a110f0109150e03070f060b04050114040c0201140601050c07080a05030418090209010e070509030d0305060307052e02160303030b090f06030703020105 82
    0x544036034282e040c0740912010500050402e50841d110304109012038a5810700c1500518515810040504800030b0184074072000c40324009030006a41344a0082140c800d91900143c80310a20480039540c042c092000c4280d07004203000100c4d9a000116220b40c0c09502c4d150000340d41006801d440319650030040c1e072420746031140c0703c643c11815503445210741e9002e41005910030048242000500c0200c58004600d0425603240c4021140a1220754200d140e100c0c0c2c092801983c0c40003000f20150a080003640715003038600c1808294000c100010020b8029100440c8200c2c0501009151420030b4800d00c101c007a412100d00d500500081002c03040703180e0f110000d410030b14030b40003562010078507094121180c080042eaa500a1003598901400250010b00c0121600c07100003d80003001190403201044078441c40e500e144030369140e83d000f8850fa05503a020000160f401e6552810003a01074011010b106104984003c0000d09403c2e0303200b0b89501413a000b50091210908542c019512684604881d003041c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 137714928 1250 137713678 137713703
    0x30f060f18010507020106030c0e130b0603030d060b0d2003010b0915070303050405010f0c02031801020a080703110106050901060c0b0405070b1b07050f0112050411040615140a0f0c 79
    0x900007401010b003d13a10341d5000050040c43e60420340c010740c0140c1c10903143c444040d4240304400c0548401c1740e00150f00502030060980b035a1000900c0c6200e00e07441c450401d41440030004446075500082c2580c06550f400c24071108240440300b0b40804030140d82c803584510240700501280003548098280a030b4050a0301502c0895004100d080d0380080c441200000e448004000401c90300b8014200400140395040c01107040882d400b0703403280a00131040600d400c0381181517007180c1c03017000021f484a4010704016641d8089042c020207035685074410806560820074001000e0410003001c9040b210981d450f03e4030904256180c442d0003001620a890500c220000801c50b800c81e040108011a03445103102a0081d0300440242008802c4e0301903841011070721080700030369820420b211307045001d0000c009040e540d070346004400301b001101550b4009141050200d1b803810340f045203d8000d83c0c107403034a8052400300482c1031034034410340d4a00380024000b100c5440b10140a0904205541d20070010101c64 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 137716178 1250 137714928 137714971
    0x3140711010906020f091905010f050705011b020a0b090c0d06020a1e0909060e010b12070207210b16050f0f160b060907030501240201090203010c030c0e030f060f 71
    0x690b00705170407255042e48000380d000c810385088408400440c40e0381089501b201d1030400068428020b44042205100000400008003c020360202c0d000400f07a40300c0d070240b0b086a0320020f569980c030700011104000400c01088a0b420000b1f008200f046004098200218840d6911400f9402c6801150144050074144000302c54000090804120f65a5200c811441c90b2401e480700361402e0b0342c03284504405540040c44130401040440e401c0702840441c20040b52540f1070120301e0b0070003d070300200114001c90400310395000d81c01c0301080903038040d5001c04082e4a44103202c40d0125103440f001c80c00704000708a0b11801c1030003500604100d000342c80071242003a42455400944101c2e06204850b21a0480b040000500d856145140c004c1713860b00e805c0080c0d42c14489005ca10114108000b0100001c40c00d01ca031609200750402d00c1940d034041c0090040700f48c0e415025014100c4400c404000c82d10107602c850290400080501b1580718107002408a43ca800244031800c400181102107001096180380c8035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 137717428 1250 137716178 137716181
    0x60c0a03150305160e0f06041e1505100809100b030f070806010806090a080406050d230603010507020c010507060b01090e070906020c0f0d0b10051215060103140711010906 75
    0x15400703078010f448104604481074940580c16002140516200d105210042006c410784a611603003d46000842c4612072030403075043c0c904240340300d408078140b801544501c071024216100b1a0300a0f03580d20b80e800400c06081d01c0886003101ca4000b6a840b1108403c01c0e040e950b0401c0300324840240940b0008013001c100c0e1414400700c2d401c04442c035809040100700651301003225a0340300f00004090407040034140d8405029120f24440c5904003c800b2070381070782d9110182d10140030850000d9150300041c490100b81c069444089032064480e52800d07001802d080d00220b50825412016918030345040d01030355030382009040210704141000003825020810241c001c40c400e00420721500c600164034500741c002894508030907030560082c44000e840503004d0300c0745900c004010354011b6800b102503440100c4410704003001e17403103258041034107100c05001100210f45d4060018a108880c1c1d40c0780c1d6040015010b0f01e44d40c1030007240c81c0d83e42c0000150014800c4050b00360884030a0300104001d21b01351507500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 137718678 1250 137717428 137717471
    0xc14030a1d1002071b0506041806090504050a0210050414040f020c0a031d0102070b07080c010b130f0506091018110a0807110105190b0a08120306011403040203060c0a03 74
    0x2c1c000c0c1d0005401040c400d4101240502111019509070060300306800702d80103000e80d100c0c950b40000e40c0b008000c10100140c008801800b4600030030082d5141906016591b891804010b0b80940c00d100781300b07138080b40315504407800d440302d001c05010070840351001c0c0710080c6407600545990365800e008507462448103001c1e41c20440d00039035401c000c1500c0f1750a406a144204400107041d0340c05000100600c43c0c8903000c0e619402c3e0000c242d1078a400c00041030602500000c40034583c0805024901680700d0540c0d8803000e100a2484c0c8100400c0d82c0b40d0040c8800d440003a0b50045803200a00410070100c0c0e01c1b101c0d03c84203010a8600401c5101480004807141d4110016501c0411480001c10040316403014103031447d000100d00038405800d11070303041240c414950032114141c40e01ca40250040d507c40206c442c00402d030040807a909200350102507103103900309490817400588000c605810089050095034003881c0c000300501416103464403030790010ba20440400e02810f8482106400e59507500c42c440c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 137719928 1250 137718678 137718703
    0x305060a060503070609051804110a09020c0d080103050c060c150c0a0f0f1707170c1801140a0503131b080607020102070b0606090d0b0a0f0c14030a1d 66
    0x8101c0509040030141810850342248007003201107401040196520f6041c0c01e0340700f01e00e100980c095240c0d82800d408911441e8506600700402140c000b4100d24194000c04400d80c200066514141d54030b901181c1664003031102070701641c004000b004441ca8001d000b050b80c00d420200b114820080303410040f003540421690342d806000046003c0341c505400c548074000001c0707545000c0b00704681c0807030083c0c80c490803405268411007070a0002107449005843d94210401d201320445d41920701f10621103004c2c1d11450a40c01e442d03080d0400740350a5405141007002c188207082885e400c101094800702d407183c200802e4050b0382d2a080e840d45000c01c441c0e40d14401c0c102501c04543c4480c03818420017500d080005400720003168810010360b00401c00f00403417250000c40c07c8480740e0381c44040e180000e2032100c60a4000d84090605010311003a40120703441030481c94183c501c24805001c140400f074071300b42c640316003130b07013540b0401c00020340400a25071144000c01480c84420080d44c0c40d40240c02c0c54901d401181 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 137721178 1250 137719928 137719931
    0x12090f080d083102010e06130311030309060307030b03010906060605070203060106050f0d23070c11101d150f0909060a050303090108071205040f120305060a0501050f040305060a 78
    0xc1010740c6500c0055680d0110310030304140442941039198001509200700803403180f42d503441086086a11a040b0804044c400034540d80d00ca100da103c5100c0441c001d840110742a040c0000d0340c0c803d5003408002d807803041100502d01410b6035503035201035001c1e0800200c080c0c0e165590b03910800010300c052090070701a140640d91152030302094414980781200680040c41400414050381d580300560340200c03480394a0380c00c00404e03c031003c9000040701c101c078207802c50842d01d4194100480103501034035045200e8020409880c100e1201801e200105060219000014400700c495550500300c0d1403503600050009040403d940c00e42c924496103d40000049006001e000500c031003483c034100070350300d4011104403101c0001b28544070009989104103c0002e05104801000030501c03401210381a0316008150340a000300c0c0b615150031303d4010554a42110014554540304200078402c1c40b68911410004e0140308040e81040d00556094011000d900c448403010040400064010302c8290f0140214420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 137722428 1250 137721178 137721193
    0x923040c03290f01210206041a0703091409040605060609120d110118110604030f0f021806100842060a09060311090d110301050a11040312090f08 64
    0x1150054100050101a001c3c0303404070052102c07184113210081880c2c90b124408402809605c04034290780101e40c0031811100c40100b050380240c088a00900f02a882a921450525100c00c48010340a40da0b42c0401d80140c0700e900060000303403642e803040f908407030000c210504100404c00002c80d035030010f03400d9010541055031426140b41c0c1040d440501011044028090300b00b00c96280036240e83c00c4c501c060104a600c540c0748050ba26203d0840c2c0156403c1031803055100703201e0404140741020240d041b402138600c8207810700e030480400119401003800602012402000071811100d074040908410b022540c401d01c40422001c108201100c6107c204041200615281400da5040c2c2d03070140b00c0c3c6015620800481d41c003581d20100d10f0041d140d07142000580641d2035a2014070502803011856044080100b4000074000380318210f07210b41004038000d10150365426090303c00c0d80c0c0561806c01903000e003403005000203042d800b00e5401f884c88610f880d000480d9290407207192030074154400d84041c1c00650 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 137723678 1250 137722428 137722493
    0x1b07050108090c06030a0c0504151806080f060d081b070f1a040e09120403240605010c0803060d05011103010306061d0604150b0319060923040c03 64
    0x5115403002d050300203811000791020226000f4400240740800751340d039402c005007825020b00180d0300a012001c0ca02500020300200c00740010f5840302c0542050700192078002041c900c0791031094031402550f52412500c0d03d4103070a00c09000e14412045404c040203000c2c4061900e031014034194030348240401044280c0c41d004010707101007401e400602903011942c1e5010341c0325121600700ca0454035054113401c0c1355a5401d10950400031090b00300380c004030340000c0000034003220f030380d2009508031085400910006521180000c030b8004d1700c00c03d03001c940520307455004507100300083c40d846100501800044d000541d1a9400c4030f01900452207201300200050007800b00c28032884001d08000da807100010040580c5e9855641d80003880c0611a507186e404082051001d03c415000a08200142c640c40b42081e21109402c13071030305051030f601c0c14030300100000c0391b69583c001d21188004104201040940001044600d01030040c01a1850071506c00c00000040c2052184070a1246400c545041c1e580c4c3da1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 137724928 1250 137723678 137723687
    0x3100906092703050409062d050a05130b1008330f120d02030d0f1814030c060405060610031a011101140a0b01030507170f0c1b070501 59
    0x25000204600d28148031010303084840c1420112485149410020b0001c051600304d03020310464000b40701060a200d40040e203100121031004078072000d80c058003c1510300e08c0901c181048284206984040390036010040c0d070420b8402010040c01607100454100d6416010901061401324407800049800341045502d0945100c5000800b03580c50803c514a000c05030188144082c079000c00b031045141d12031140803960f58481c2e50302807480340c1003500c3c2c40c600c400704040d441790440c3c0342d1604c01500b0003094040c80741c050b1049075421100203c03a10b9001541e40c0740d00903501000b01e0360440e2440300f0044003406660820140d84110311410090000d4580101440b100c0307403000e8511424941842040c03200c211388800006000d40c42840d191455811941c903444c09440c1180c1800d00c901500301c1403140c0c086103a0060300200303000b071320140099107030010704803020788440101c00402c4410744089101c0007542c1d496250001c200520590034400804525051a030108804a040340d2080504101e1540c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 137726178 1250 137724928 137724941
    0x15090c01050408030d050c0702030115210b010b090a0b030c07060605150d090507050d030504030b09030c070306022b020c0606010201110d0f150303020f0f010b0a030f02010c08031009 80
    0x2880c041c0d040c94940380700a552801020100102c041c1c40e0400188050780e590283c07904103030000e0003070000071251040c40b24950107038080c4542040c5101034004e050164000b42605643c0e0184908616a18103120804260080f00305580c0c0300c0d8103c41c00290011640014500801d0150200c030707601d84541c50188200c460f15481a802800b038103030030158680100d016186252132140c0c001c140010710b841c0003401c1035604d42040707902c0b100600f0b115003410341c048060001e40c1e101300f41d2442035460350880c0b203650740614032500c1201d80c4502010720004119401621200d1450b90b8800c6403c3c250343c00e040081d075540301040c02c2441d0b01040c086441001001400d4002e5003e00003009042e0b042a440d414a2040c2028004041d8030340703c100c40010955403282d0344c18a4020440c203083c50700c03031030004c0d2985110031401440d44500c1c0041c1800100620070490840c00003804045080d103550742d442150202c2c0e0500b80d040c0002a8491710101e000c140045108840c40c052038550141807104a10486c2c95 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137727428 1250 137726178 137726203
    0x2070b01140a060509061c050a061d1501050a050705010204120213090209010603021c060602011d070b2a01050106032405090a02070f170405040b0909120310081509 72
    0x8442c1001c00005401c0b10860321401419a50303650b8844056040d4581740d41d0401a401400e4a84400c0011040c001c0d4041404e642c1600031052201d0031080381441e080d401510101e5866417100746040c03196000d00000e012903003403414454141401c0f511202d003240c0040d071180402030007080d0385404601e001d80c2e01626840d0042020420f5828640101c1d0b00f445050280c6002d050b4001003078030303500150481162030003131110014031009031940c3e00280078011181e015018511220001c2844800100e690000e40d440030303813101d062050b14110501d80070200001c0b035031004048122440130040a025450107030295031000301d00600300c0b982071020105030141a180284108100f4495655002d1095812002e106d0000d62110b03401e0800400f421907030f00b4010058503075111000300c07a0807040040c000b160403c8400704641c211a5041c41001c034000c40e45c02956801501c0000310300072502c400384da00f100e2130003240e01402d0340300c0455919100c0002210301310403d100041082c4540d041107003552814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 137728678 1250 137727428 137727439
    0x9060503040c05010f020114010f03020a0b07080d050606090d1110020309090105040c0302130905010914010302060304121b0317070201090c030b060d0b130605070206060d1707020402070b0114 84
    0x3426441d440080c400030f014180c10052140440c0341010310075008418403426102074031919507519403180024948511080340a42001791000403801c0c081002d0f00c00d0103030440c0c0c0641c9000f03420040c1400400c001010a0b50010081c04a5805600d8980f2241200713486a640d1404c4130480504002c181e0020f50f01300011580300304407440d45911017000b1241120010385000c141d0280c014070540190142d00c00540390101140000510109a42c01040c12512030000422081d050130044400400003408040d42004040001c1400a18408000f480c0c200c150b14040c580500c0905809038002200074064001a000e0304094801481c2c51604641141a0380000c0101e60026524801c400c41c151001402d106038100015aa945894007002146036001c108003c0b145000002580c94410503682510590700c1d000006000354000034140e40100c2000b01481c03422800c1d0340c1e4016000c0410000301484c254140440001a15240080c00b01700d44900c00960066041c202c100000c1d11030034884c644100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 137729928 1250 137728678 137728681
    0x12050d0e0616120e0102030c0324101107050307080a0204060503070312050c012007051009030e1903050a06061e031203020906070510060f05040204211a070e0109060503 74
    0x40714010b0031064102c660705054100310032000c01d8030018a8a403540d00d205500000802c05441900341c0103501c51144d801003440004c4240c0b460720080380d214103406030090000700e000040c041c010000300690304858000c61f01400c0d00c44020a090031190f40c40503200307a100d040c0503c01c52820f03004d01000382200f50010a0b02d03900e140c4600c8d680700d055102000c240300303000820458455080d00030340f00320384407030305058014000500d601e0401e0707000702000c1e2002e01500702c1c10031034102e140c01100c407100d8065139400d0740b80e1907031410001c61124000070901c0d48801300300000006070003802402e860300d005030000591186403032410940041f4807055111031100f5107500348009001000b645014000d01d180041e150b07500c40020945a20420002819922840741c2c40507219111780c01801c1560851107050000540e140d0a110503030250303002e413a540310300b20250202c01d804034038481541d440c05140103d600182c1042030020404081d1a40c400180d1a12014203607540c000000a0041c4072234504039155 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 137731178 1250 137729928 137729941
    0x30d030b040b03011b030b1305040f03110102120402060a02070911130614030a0903030617011e02090d020d0606030b04110315060d1101090f06080a050709080307170712050d0e06 78
    0xf4444034005020074103595042525207910f81051081c12303510203500c01c11442c03d10b0b090526642580e4407003203000a4000d6041c4020340c6041c001c0da60800b00c14181442c070b41e15640e00f007000c60340104403502d0462140d8040024101224018210398030100001c490342c54601c41292341c3c1c01e0065800250034405080b030b08503820541d0004403035000340030000001f04107000345800c4025090a5000c10003030011a00340c2058028198003140106101082d0071a041c00303803401c90f00c10b0b07000b9046003a40c410490030445d405404c02e040701d2030718144241c0000400c240c480e5900c4a618209480940d601040b07080107500b1404c04000c1e4004c0600b0a421441c5546000000070b04100a0184001d0100301441440001071340100e40c08030141a400e01400b4040e921480001e02403141226581e40c0d0724100f000ac2a80d444c0100c040c442980c85030b0005e180b8189450311201421001200317030002c42c0d030080041c00046540c4038012107410384140c0d41d4a42d1210f81104500c199020b00f508046250481c0c03041c00b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 137732428 1250 137731178 137731211
    0x270907020d14070803042111150a0f060303091503050606090618060a050a02070e100314100f020c01050609010b0315130603050a0507170613020f030d030b040b0301 72
    0x9102403549001850304030219181d1402d401224002400b040010041c0410403d03891480f0760540c201403005000000c103000c046903003c0c1010380030740301e136041440d8042850b003000a840350b2008150070003040031a03900102c01c046501c198410780024882000902c041524407003003000d000e045146c14003d03810b2440000d4a04c1c03003030303400303881c440d01c000200355100802c42c5000700c4088000915181d12007900000140981d0302900c00200103001d0340354085025107100300801c1c01a0140c44032094140d0a6640d07401c42c0c911099203403102e42c42011182d0b0380901c900e0242d507480802000e009a11941502201400d60f00b025080a05ca28100d0006204210b00703001529403014452900c00d000c100c0d59000f00301d249aa68040000036420030f84040284034001440f5080d580c8180d00325225580d0301e0500c41c0d400c5515051101580c0c010f1400f06a41220007980103200c1c80c0000c21041240200a00080c64090f03503140b410046911503044071420300d050311802c10249425002801402e146110011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 137733678 1250 137732428 137732443
    0x10e1617010b2809090b090c09010507052112010509130206030a240501080f090a0201032c010f06080a02010509040c050405180415090b0411060c0327090702 69
    0x14195040802c0f0403100790b030f40380c0e0714207001a01640d003089003424a0a004000604602039806042d040840d00f2040b41844002e0b14410031580003800d0400384260011910350b030241500fa04c25120b2090b64100308801c3c2c00280c001c004030b10320103a666040101501d20394100590000340308404807000c014001d10015402c80300542d040300d00c0c80d547c0d90b45450b40c2c401009260140343c000814031001c441c90380c031164024010b4440903214001150344428800c01c98204c111016450350704810542801035000f034002980c4078091414400362030158618100c41c4810011100500b030391208007410040305a0704c520070142607114080d000061a0b031700060030768130800c102c1500481d07031203c000324054490f4080d81d0203010000c0089441031403410408079041005e03141507584a926404110210441e403040f03404455001d515104151b4841d1140101c12001840312038011030708004440305030310b090005202541c004880381602610001c08020400d10300b1012a0080aa45040c040025000980300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 137734928 1250 137733678 137733689
    0x60f03070e09010c1d0d140109030c17090a170109080d021306050405100503090f01020c030301180501030209070818010c020a0c0f0f120302010209030703062a0f0c030c0b010e161701 80
    0x101c144400301c0c43c00c0c955601300400480c03848e5203031041070700c2091307407041d403c80c001d03401081482040401481000700078070442080c5940070f2003080041025003501c01007030b01245195000003c26884985401d20968800855601050b6001401e5150f510b000038144000d040740380303043e03030800741442c010840014060b52041d044c010301000041d207050042103443d901c44940002991901c0d222000c0a68a030028000d0405150000b0940700808170b10344116030407241c00900ca00e2031030300c0301c039006d460070003015080001620880c42e440384903102c240030f8030202c00c2d416401000540005e0600111221711504035101254500c4000c202c42150b1208600c190b070b80c0d112003220201d000f032a0581c024400c40d1031742c94060084a0000081c0440755004c2004d2541c0c00100c888012042810f01e00040482031809010909280e140b6081d41e01c40c94005001c64420b0808440b1280541c4507800060400d900c84e031302520941c81000240900007144a004200341e003448580e8040c14403a40d25600d42c14001c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 137736178 1250 137734928 137734939
    0x9061121091201290f060a0c1401020901120c030b090907050406081f150e01090506040513120e0a05041803020c1804030509130c11070b04180203060f03070e09010c1d 73
    0x982c500d036214294407a0070400101203982c2c47d04000c3d400341061040349000c4d1442020900c2e840c2c200c61042c02201c03440742059403038900002140350204001c2c0b4103404a20101940d4110800c07441c1c440059660041103010700510b0b1103031a1204100940f50b541d0001c0c41d0541001000780310100481c84c00083c04084004040380c80100c402c03401200c21160341c0200107010f03201c4000150168590302040c0a010103680a018aa6400c11040c9090203490001000203003028448006248a02074119001c1c00c0180008040c90ba03410024040d2500c91043c030414012100d02641091340412030401101400d81d00032180f0601c08619900300d1000a00203410300000103801076040d51520702c0080600c100060401094407114030051940100d05040030180c4911900841d603994140306031011030305240e015844101545102c1400780d04040c1c1071a807c54011406040580c0d424030189000c0c1204403010f10092a01c02c29003070030b44074441f040205005c0341d84505200c0c081031108140400e001542c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 137737428 1250 137736178 137736251
    0x5010f0605090f010e10030b0301061401120b120d0302090a0f0503120703030f1d06091f1107170d0b0901120f05070801050106050a020708060709061121091201 70
    0x681e1180120f4170615030008070140010501901a030105e06040d405030001c10031292107082d0f407210740101031f003e540030454541500115007102d8020701c4000401400c404598080d89060514100075800300902003600030858001c2400c2401800c4010480203440203107207031070000426182c40e1480900c801342d603000500f420070303d806a0044d505102071580100006c0441208608842d0a0007220b41c00030b0055501050100301c001411078101c9101e0754200340070340c410b0042c140013402d01182c01106981c1c10701400010811040000400c541c0c54014150740d00b00e40010101160400c08030700d4400d1241d40014800030303441e080c001451950242c0c024158a01e1400d06600d0215554007003101d5601341800810801e6110026040d40c403199022543c40a8882c01219100c03c8210b071403400281030070f8001c02a41d480390b408440403203441821354101204135411840003000421029440d25000201461181000318510062885010003040b41501c81901c2030b10b89469103403030306460310f030020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 137738678 1250 137737428 137737459
    0x7060c0b04050705150c010b030d200a0213020316050a0210050a090c03230f150c0403060212010501090e06030c0108100801180c06090609060f0e03010203180105010f060509 76
    0x603d0182c03400816841440072801d00e010000c0c0d000c4950000da95081200c45202c1d804c00145c1c242000b0529264441195849400c0f088582c00150074441a441520410000740e1641c04480d00445421100560b9a2500740c240004c0003c040581c8400c1150802c101c000165010404083d43c80c0f0150300400c5a4444010070006400d42d00000f815181a2601c000200308010545840c034486460f8440c00c1941202041070300d401242c20108c0464008141c0703603040500180f1a903600c4440030341094201526521795804907000445a0081a499400140459a00010010300401408804101c9494014040303900c0701c255048160620003e0710205000380c00b034000a0019003040c6000704214550110400f041c0c0b50010010340700340843d924046025441000c000042c2d82c60754440e104110319000c8105c450707038041c00c0300d6820007240803507a4049aa013800250702039094060444c40ca0b4070745100351400c5590680c0700301e2101030042020041aa004026034030444030840d00c080c803032034008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 137739928 1250 137738678 137738683
    0x30303141306050a0b100e030c010504050d060906090b07020f0606100203160204020405100201090618050304150509100c020306090d020a110f03010501060c0b070906080606030402010c02060a0903110307060c0b0405 94
    0x902d8181da0241b0501d0f51500c0080d44149548007a18044040340ca813802c0100041d1400d210710301505400030909501440030030304540011408a1041100007103020031350304e490b0b000303807030031307030380c450050300403400c4400400c00400070190880390840b120010841400c2c0c1c06545c07482a500410f40600e9186940010f41d521079050f03800404010341144600c44401800038000d1044c01000c0b81c03c68507012101d0358a203610005580001d80c0000114602800c04c15559030395107810b03070701d01d04109040100c0c00c81e948a020314907074008002e03201c401c004e0800b80704050421500525240280d80480030443d8055070010305080c000740c0000846061514980100d1401c10001c8900754040d82060b00004c0c02c00e51003107050114500070034007106c0a44500004413040c0c100c6200703207030010ba140e41c046000c1e8501900115000707403050500b15020b160560101e030040e0000c000070008146888410014004d1002c40c1d003100c48002c40103010a00d08000010700b108104080242444200100103000c11004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 137741178 1250 137739928 137739941
    0x70605060a0b040902120a06030201020d120e0102070b04051c081506070512032e0e1302091503070e01080a0f170c070603060e0709170307060e0304030303141306050a 73
    0x410702400e90f500d0300c1d006843c019502442201403000b040d0000103601c81c80354030480007629416406400002040c07001240d01107610001118034550f241030001292909100901203a44604100000d41c03915091060814404001c025191003d034100848019401201c2c6680305a800f840400380e14544008a00d00f4052008010401d101d08a01c6006540403980598415091004040c184a00b02002000326103614403101c112030010303000038003000080b05900360740843c2800c3d03140c140125a80018180d018251100d6890031043c20041c0654201806184c020b006803024011155140c0020641d40c3d50740900701522442800d5044000c000e8091081d80091a801d90030945a41d1110390064650300355115120100780780400001da00d415100340b49100d11038036121058401d1803c40140001e040f4041c0205150004000780b40010300d60b031049482e0722040d00000d58885065282c040c0c1141d401c0304089408a070428108101c0421010601c01305607440000070440343ca819040c031025003070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 137742428 1250 137741178 137741189
    0x61d13090b1e06061213060908130302040605060406020c0904030e0a030c0e070e030a020f04020d09031707090e16020712030206100911071716050a0507051005070605060a 75
    0x101641805501000b4819401c0702510852080196444500400ca0b80c0d104400100b0981201e03500029083c203080380f002e65541e401254007245100c8569541c0e1000d074811880c4882250f50a5024020f43c2018455040a0f14042e1022031400c0c0c01c00c0000780d41d800b0360004007403040da9904002800c00d8814008100c030540c01903c00c0f01c0c16912403900c2002c8200a0154003190071160000400700b62017841e84105002003e405010b92031401d80a100400303072881e8459410580030450704000c010340744201d283c1c3c81d00035039440d40b034070780c03480110704202d0b0014144104101c2c0104040c4a9003416540709a007000d40c5d405060310890440c2c1c030a03820003220b903111100003280d140c0c600f03007816000700c1c207180710305400355550741400c3d240c210480481c3c88427000366502e004188207040015441c1c8020540c1070000c3c180d060705003201c5114100302c000b4480c0c0101c03003540020780114100700082140d50081c0904441e07180012040304002405801010b50141c00152248040386181d254118068090103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 137743678 1250 137742428 137742443
    0x290705030412060c02011a010c2102010903030e01020c0601050918100b03010e0106081f02040f060306080d05031b070303022107020f0a20060c03130906061d1309 71
    0x10b42d180080b00101c507000c841030fa009030034040c5003007000e88103129160b1a021211740b01d03070750307110250011550024848821075040300c181c030711442e43c91010707505120300c410140e0012620200500e0000e0540d900301d120403d040e80148082c601c408004103100341074540c1910b450031507030b43d280801d400e80d000d0b107807000341907000d4171405169100071a0000c9100c4d44094000f0320903900610103403401c2f920248034482540d0011700c26800f40b10381c1c0e041040c140c00e64200000d42031646a02c01d600c411031190344070740080707070b0b0b0703030404210b0300038203118000007a0f40c907003880c0781103203020184c040002c61960a102d09a180c00030300c2d4400c050090703054901e000e606188208040240c82e00071019403006580405c054481c8600309605c0e160000749400c9480c0d4004900804441a04c1c01581070310000c90110f5440f4105111400ca01038080001d403019098524141d80110300d0408000c089a40941041003044099052040303240c1c01152170160210b4141c81c096505503500b00010001e0040da0f03401030000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 137744928 1250 137743678 137743687
    0x40203060d06060f030c0b0a17060a0905011706091c050702040f0920030a02060909040f0813060306060305010501051905090a08060f0c0702030a0b15060f0d051029070503 75
    0x207a0724a07200003502e11900c1e0101806d6207403414000c00d809818410400552110010300c4d40030781071080710f600000080d055018031a110000a001c0d10001d03040045640c0102240051021003005643d4101c0e4996010b0311360b00c104010642c842e07040c0c80d00107034140100081d0110842d02c40764044620118544010043d400062400d629180541c0b0b04141a0b08d85102c500d0341d0501d8046041c0d14400c0c0e00928075460468040705201000304021300a1ba0703a1009150b652012500305001000c1e407242c8101448900341c20694082c04444094014004040c5400014806640c0080031200444900001510a60101d50341100d0a200f1640400d4010049001c001414000010564011850075030307100d800341c1c1c401113014158090a04007a525901148840009c55010304e1a650032203403400d212810b1401e04000304416a2040c024010310030030000e01c0c0354100d551449440c1d08085507101c900840d510b4059480c60701c00b80c0786031400d8444814480c000c4601071113002c481121f980001500c0e1a07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 137746178 1250 137744928 137744939
    0x215031b04060c0611180d0501110c030d06080c0f0603040c08010f0e010e15011205030409180501380301150902040303021905060c0a120624020a08030105040203060d0606 75
    0x1a55080d03c0211625402d1103200a00302030520144c0e81e4942c1e402c4000b80d6945082d404200c03040035810340544940d5680d00f40c64441104110007000c04608800046540d046001d0307000c012030744c06500091168200d0f403a51006a0b55154103e500d030034084400a40360749540c103000c45014405d5001e051158030b0080500150b1150b42c0003143d50081d680c0c0204080c000020815441b000ca1601c02c0c54590315240043c8503a0600490040f0030301c1c001c90031241065100d5036040201d641c00701d40c0ca00c4015120200404016090045403d10f14038800040381ca214003621141007442d5425030241d0514400d10000150f071406d520031055a600150943c010307540d1a0051030080d40140401d400500600040444c01102c00e0006040c1070f5204005113002d58801820310400c0c0c218000300b80810815400715180c1c045a40200d00c040c0c44000c0011140b0741c0b102e0000d040e8007c6142c2c04074190b4000d1141c000100d00101c0a803411138000352405039481d900c110000300c003c1d0112200402d1986440d601181 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 137747428 1250 137746178 137746187
    0x809040212093901050a05040b030c030f06030d021c0e06070b18030301030807060510030b040c080f1501031b0b033907030c02130c080405060708040215031b0406 71
    0x1d464400d03071440401d040e00190602c00f450b00981c000810192901c0f042c03115485000104245001450140e05041c0c0314424240142c0c01901c0480c00c4200100c14858092410307a5101d0700600c00702d00422001448000194860500301e001d00e0645c418111b21000060240780023101a01340104015512074803403402080300c100039a5411207000410010440340c1000100303d906136034004005a0403ca5150388140107420000e00c2c440210320030140000014041d920942e001da840360501c501154200401c0c18900f402d240001803a0b980005510800b030204101068103482d000248140030701404000c14040e0301c80d550103413401d80c4000040050b13445000400003003204580340035042502c40302883d95000e840c07102c01d026044800f0014100003d000b00480003c40d8409402040c4042e10494044220784a810000c008145e071304082104100c42840380c55030000460401040307508290300407860f070743e907100e40d50400e940c80000440c1c0324800880100801e034000061442e40e45494440050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 137748678 1250 137747428 137747443
    0x40b130c020604050c0f090a051b04090917041809020301090f03050d0e0304050a14040b040e0a0c050405090606060706020903030a110d02011407051c0212190c020307080904021209 79
    0x4e0b458000d0030a610024940690a54210000140340301000d40b2098400d0001f0a0050308542c908000d880006205088a41c05403005002c3d4403800550466241004405e2070403c001208409504200900402040d5170705224030b02017814001a00c5805032000c2801001c02c60300c040c00410564019408066000c40201030b0f001d40440b00380607220505070441c1d900d0003140034540e0310a00546081c010120154151001c2c081c00030004268158281c0110382151b001c0207002d81143c114a211500340f2500a8a66004200a8804201c03616021582c5a00d4420183c101c2c4e104090019022080c0b0078580c06a03014442d0040a0b00d0f501c542d8004090103030310b400c1080071040d008030742314202e109006126009070f103a162005e44500d87d4810703004940607070080050390701d880c51140c0d42c0001041c452010b030a007858210380c0c003220b905091140c1030400c1d82d082d0880401c68240402c88aa150b8007105a17812943c0c0200500d81302c08201000401034002c0d95100f1414400200801c1400c2600044d00ea = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 137749928 1250 137748678 137748683
    0x60f07052d0706091401030b011b03030203090c0a0807060e0d080c01050f010902090906011107080102040b0408070b0c0312060604120501050403110d020a08070f170a030c0507020f040b130c020604 86
    0xc2e8481d6070380d01d0302601c0d603010f944502003011800c503458a1040d40039400c83c5003154414982402100844102d20106000c0120240e001030780c0801041003140041260740c0b94110b04403001c4558603d02000c0aa581000f801144104485414040e16548500d00c45110159002402c207448003d2102d00900030102103a5807101c604001000240081082c0300300c0f0b9903480c02600601181c0d440600541e14890042d80f4014503120301030001030034180a10140016060701c004203681c5a190100c15850001e450b001b416068404000800c5010000000c070f5a112244103d49085039903420005003d90003664071980c200b900240540307041040c198400c40c8664800c2d182c0f0303400c4c4080e4024155a84845d030070441c0240c0d002c0c018160109018001510f03640d88940d041804402030f50782c1e2580c0310446030444c5c0030022004150407001507018025203d00660900c6e01d60b08056160b000a5000c8200949203030041d507070b54440403200c1d2500e5100340445019050b082c0104407121000965800048406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 137751178 1250 137749928 137749933
    0x11512050c0103050c0d1a0d0b01052106042402040b0a0206150303040501030509010207060c11101e0509010e01051501120e21040f062606060f07052d 66
    0x803025030007131192a0051030340d4481d00381131050030240744d402070820019800f9000240250707100a1394694000c1d40c40036104000311540f6516010500950050403090b50b410000c051500c581c0242e00024240d60240d001081c60f07507210540300b480000c1201c2d851205418900000f40407812280301001891036403803690890b01583d64107031006c0c512100303508090b40d154004100822080d8401c1e00801e41210882e03000500d0166942e40c0c8204440410108401042c0c1d05910410f00c07c0090020010300c02074660240309043c0b80c2151050007202100129611558440104a1442095110b0301d141ca1110b0001c100508083c00300c2030322040b8000f02e507070000d080906003241604241c0100136201e030f4500000c107050b40d10350a84030220400c001d0501c08400c02070200042e0740388017010030030040003076489942824100e5036121155505911a1510040560062007441d032100022a0b02414000020f80d45803605441c000d82010080c240c18868012030000790015016440d030400d101500081c05c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 137752428 1250 137751178 137751193
    0x914030313030c0c0e0a1d010c020d050f0f04080708100c08070318150209040b0105040b04031e0c14120609060f0613110a090608090c060d0207020409030c020a06020a050606060a0201151205 83
    0x1805403c4c1c8000c403440b02700581161580d6800c10f4003d901400812004800702400e0030000403100c40a80c020354842001540945402c1000c89004d0003004480d9114031011300c0005503018004d4291100544000205903450080031544600c01c0180e88110f41d1050280a43c0100b00d80054060342165081901c603614181d00480c8640c010001c442c200e0b18140911414646180c07200c801040e10910700915071900b580c14600003c1c10810b144020300513900e03035040d003110754405000138070340042d245802d20741c040c038140701c040f1500080042d0300c1404a00260308555a6102062022400c0003c0d100710b10f0410f1303410100d4007084400f6060111960360b40b407071460f41e164000c450b1000c00381c8a040d00c40c0c0004080785402e0030058000c01c03100814040c050710386032241d030220b400c031040c3d900d017a400141c440c14401d04520306003140d04020310152004101041d25503c415464520242c1400d01c5004001244607061f8000c0d001240d11007140d0880707034002c5a413030804516481004008517094028803e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 137753678 1250 137752428 137752481
    0x9050102011a0d060203060a0f03030f021902130b030c0a12020306070807140a1404092003060109060c020f0d05030a0f020313090c0c06050a0914030313030c0c0e0a 72
    0x24080414500c010302071511403e050311303104000c0d48042c240035001012090301180100190b0110b400075440390360b8020310410009002400e01d2030400000d01020010441100540c4c0c81d10000d03e00c0036000c20001401c032441100081ca05038108504a80103e050140060840f450500000f03c4500a9040d00d400d07680300340003126810341c115025000300b44c402d080e5500011642c3d002c0d00640304c450400840c905000182c810080d00a40d010742c0c0a20b48408104113600102c01c0000c01581070500036604500b0030074006007078600c16024143c1004050300b081001d554807640d1950182e0009000d421050340316040142c0ca0754000c1c10180040f4420320b59801c51284000220390400810001d074204950510500001a10440400c10201301150991a01040c1e0745e00c1098042d042904000403c600e40b86015241c01c1700141042c1d00e542c200b4003c2100030800c0c5130000012070341c18507002c01e406c002c030f240843d11402035800400007040a10201329481d840c96010120130030301042815064800310 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 137754928 1250 137753678 137753711
    0x1305010e010b0307060c030203070f0c060219020102060606180901080c180f34020607021204260717060a18020d12050f0c160506160f03050405030307030905010201 72
    0x40c2da442d605a88400da0821071141b08800710240d481c42803050b17a10b040c0d50303078440c110417480241003503070301e0b05914008108058040000d801008036440e0b001803442c140340c002039200d8a0003404c3c80d0040b03100041414101005440b2056480401401c00702696156055980c0d240c032902a489c1c01142102d000c1c13980603030000052845030698903e1140e0a94418140f1210b10027500841058107000c01a480d140d4080090101d0084089900806040c035049000030700c2c040030481143d900306c0041000f8012560484c2050f0030300510140c84c0715010021032591440d016450784000342d0008030030110001c41c2c0000c6009d0f801064200403d02c051a00b40c0ca09804140300201c000354000042020500000c1c03441c0c0c5c100f81ca116481c04d110341421406442040c4a501090400b02c0a0f0010116004451410a0150003405050760303801d040220064501c088905240300150804c808500314a041620607012103001d060080e099076200c600d81d18000e014a2102d000351809542010350603c2c0380e0240c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 137756178 1250 137754928 137754941
    0xa030c050408060105010c0f060203070305060a0609060206061002070b03090d09170307031d030f1501240c051207061e11070209060a08030a17061e0f01171305010e01 73
    0x840301400f4103900c0d2a00645d010700c1020306c102c5e0781c052080800c00108115101540c851001502d011840346049010815a1031207500300c802406084d96040c49115800a07070594454810b03950a6224181d1500507840c02c0a07980c401b01c0d48000010800014180100f6100340c05110b5489041c40c0d00e88448141e2070307149185100d420706904c00e0040c030000c00c0c894610100d089400c5d00080490720440008a42440301c40d1130140d2441d8805950305801940c00a00c450040c030118400740c2d4611840346245990300c01002091080100c440440703028000107105808030085019501ca40d0750105140c044090701d0b88239225803202d854094000540701c034a00540461842c450b400070324010080e42008800b05002e000e182c3c011001e000007140d03da00c10001414112800d03151041e11044c16000d10406100c0145524003580150048020100d60034100940c40310080304d031003203101c0410004841c4149018107440c030950b20785051141100b00301403121455801400240041140700d014582030341c0300c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 137757428 1250 137756178 137756189
    0x190e0102190c03030e0d02011a10140d020f030703050a2406050d0605040e0609060709030b0612030c010c0e01090e27030f0c0601050109050102150f0c070f080a030c0504 74
    0x20344038203840a02c144601e1905a2103803d000a601180e5518a072400f41009403200250b1764a0f01c01c03007105800e503803000402c00d0048622400d41492004001d00047e00c601c0f0b01016060045102500d03004c040e0180c1e03190001109009440380b400480c001d0140c41c00f136415804003894508000308041226441111701c2040040d02602989403141c125620f6126a00300e05c0300030f0766240e021800d660303903000e455521401c940081c8503a0411002842c1402006072012040c000d0140307040000809201c00315601c0340089602c0c1d6141c104410700d041c218400e0b0a0075103a10351821402007440c5400490b0307108484400e9a952040549501d1083d076641000c0c1c801c41c00c558089001031420415078600c03441c090041c1015242404844641d040058011055071001c5401c21b000600240d42e00c0754400e0004e0800344000e003a1020f50f61300841c0501070240c001024114003200003020310b8840c0782140c030341e29440186030300480c441d81010012504000c0c10600001d0818002c45100c034032404c01e4605568 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 137758678 1250 137757428 137757457
    0xa05280302060c03150402070501020703140a0e06070309030203240a0b030307060b010306030c031124090409030207080f010204080c010801061709010915020915031e06060c06190e0102 81
    0x32102001081d0031303040284004000d42044030319010a0300d980c006051030500c144009a1554203514001d05040398090010610140a000c00500c15912040c1180e880c0020b0702da5942c0c80025040c00c44034000d0f5a0406034051082106c40c540da081c0005039a0f901c50000c2c00c4240706915a01810300958101305001a8164020f01c1041c0205126174010712000700d05050000e20580e4130341d900040003100d035009492004410001500300c0c14044402030070700d40d101501c200700b81144c1c0a03118113400740d038100d41d0045903100c82c9102014000c01407507000d07090400403540414600302825010354003c0c042c0b11ba1900415509005a5003e440700d80c3c180c500f645c03261503a806203c0c50001001c40018408640380d034a42d5480e43c04103a26040081070488000c4026950726840c0c2c040c803119900d5944020b220110400412400c40d69601190201c510540402c1035141c0302e0b0000030b130140c054888030000d2401084240140f114180c500d40540d184401024000e0f2860358800501301d0040449103807005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 137759928 1250 137758678 137758681
    0x3150415030f02121c080916060c060f05100e040c0906080d0e031506010f090e040f0201080603060f15040f020c061e0402030a030311070f030f1b020f0607140a0528030206 75
    0x40c6c1c001c10110317501c005041c00b10740c144054041400000d490561007400811112540c0b10280b000a000d10f8140b0a005442400745052030122040301c56010300c80d1000c1e28800002140c10000c024500d4401014180428409507480d944d2030b40d211002c0940c100007240c04202100380c281008110300c055542c00c2184040140d0b207041c019103850790408030410030054685401310f02980c642040a0245014401071040b014071440023400c015000b0f4203a900c264000c2042282a0303d160241651000ca0040c800d2041d0007104082000342201c3c01c2c00d042c40c907002041c0c40c0e00d15072002490700c3c869410400342c00c0311060042d4038a040d0341c006807000394154018104100119019400414070b0040c0908424070300a40340c2c5440ea08013800e0b400032000110003644c8190011340c84500d04142c01d000b201d03201d000c903005900240000040c04001d0f4042c500c0440c40501f03000b04161441c10312113640c030a5500f0000540382c00e40d10340c407034401e154a02c0d8809402c042001c421002152250540c150000c0407607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 137761178 1250 137759928 137759983
    0xf170613141906051f03030f03020702030307060b090612030901050306011e030c1107050105120603011806061d060f0d050c0301020d02090901080a0803150415030f0212 74
    0xc046031280d080d1048a8240c203603284444042116110404140180d24100c40040c606101034a0020301032000003080c1c105c8185207106485030150849500d4101f1100980c182002640607001c0c0381000b0354540400302e9060184082504580d42911003160007108542c0e44008000343e03c05040d084861a91003800840000d5010724020354001105051502d0342c1040c200740600914072100c0d0400009490b2085180041d0300115542030701913800c2c000d4003d03a41414002403150082d04a030320056803007a004103030640c4082d440840c0411002040b542e060b4203c0c1801c40c050701e558440d1814001c2c60101784560390946407900703409904003d168080800043d0104905404100c0c4107a0f00c0c2d004c0c001d8030300e56641c3c09100814017588405c0c005a1502018410400f5003c01613001e40c1c0c2c0750b00003070311040001c0c08000842c4c1c0d11601401c2e86400d1800c140000c038000b0708020200c03403120281c4d03d8020060110014103440440d208841c40c0d94103200c0d01c074103207803595155001c1070754800051103483c1b81c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 137762428 1250 137761178 137761201
    0x8030f0309070e040516090e030d0f1407110d02030301061209050c061903061502061b04050a0b07021c0203120906090406090501061b050c0d060f050708010f1706 71
    0x1c101d0007050441c0c81c02901c450464041160541d4101d07115030200021003106640d0040702c40081012000c200115010205000e440303100d0056000701c03040d542d4100d143c804030340f51f200702c2c1e15615551200740a40b41c01c61026028510744042050703984070312221540001d20001c02c81e410385125a40e20300f0041e44086000002e41424442228640164900d4508544549026100052606103403115807407505502170200d40c080d400020066500014008440342c0001c1c1d550341023540d4841204140102c04440b168502031504070341c0d07001100c0c02000804000c44000b0303040060007129070304d202d401d00c41901c1107240c20b0300310f0094040c0c00074407400c55407940795405442c80e24005031201e80f62031441400203040350840e801030403c482c0c1e01c0f401849183d178041404144075620590309800500e60f07858150b80c0741415481144121012014141040843d41000c0c002c40c410260a1019080004001e011000240202000d40c6001840020144420350380c100e001d00c2200302520303090312107080951 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 137763678 1250 137762428 137762431
    0x30301050f010e311401080307022809020301030b0f09070b090f0a03150b030a050307111807020c0f03070609090c03110c0106080c0d050c090703110c061f08030f03 72
    0x640c00110040701130a8501640840d10504903080c840e0350001041c2181e001c115103c00d10500100d0629034014002444000201c40d01250102c0c0d13005081d040e000c0743c002404007062108902c8840f500c03400a007009103a00514103981c40784490400b5541c41a0070094018022a200070700c03a408070301c04201c4107a140c801000075a0000e0040d45402c64071b480481e0300c01c4a03540c030072038200000440c0c0d0072860015124054130103004501401800c20a0340703900d981e0f0f009003071010340200051a4442e4035a0b45100c090f0a01c049402a0501c852074444006503c031141502868041c0070b0030b00a60f801464040303000e0013030b00c00d1520f59080580c14881120001c0454100c410241a070300c200204499000740c0107001101545000400c002e41404812400d149414014a005080c120f5a80002500120300c506d2042c0066450300502c2d41d5402c42103001e480c883c0d0019040341c07800035039403614040116440c0c0c890400880c80e0348002c1441c80d43e012031400303107200e014283e0b0414080840d01c26a190001d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 137764928 1250 137763678 137763707
    0x3040b0702070b0705030c16030209180118151b0903030503060303040305150403020c0405040215090415090b090906041e06020f0310052701060f020307050d02070f08030301050f01 79
    0x2d8840d19181c0500b440c090b805520309a03101c0d4408110312082e14001c000c030b4503100c000c076500c1140745481d540c0458100301e0f01900440f4010086696800081025031080c41e640d045c2e140102206199030401421410480b41e0044409050840d4207a10545503c485401703000c80340d5827041c41500d90f4408442035040640000c0d0700d40010400000815004c101c1c40041a440741021a070908184c54013a241c1001c0402044c003450501c410000569962520207150803589605180c0d076001210005008020000301950007400c0c0200210700540d055002041c1c880b420f0701e2150361610740030303d0590b89000444e00145040052001110113001c0060300340c41c000d115040150414241c441551102d030002c403411001c0c191001010029864204540d0819404d0503082c04490510040c00c1d601031801406400c0c14420003000407030a0034401c008030f070b50268201d0140c031102d041280c0000d443d1040c1c0d2042d1281140c0d034000115050b01e000c01224100e940081c04070340c0d240420340064650000d04002c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 137766178 1250 137764928 137764933
    0xf1509060703022b02062d06010e041b021002160f030903080304120e010509030d0518030616020f03190e010306180b040f02070507030f020a0f1d010905070503040b0702 74
    0x141308003032403a1003400c0c481075290258403104605202009103000c03030007401d0700f951131290301a80504a4a102c00d503a40307101c2402043d02d2643c1c454005130b480203103811845030050701d040200401811104d100104020040d800d582040007000343d030070103a01503448031102052080c00d0b1000044e0311034080e9640d0a21900740181034954940b26039501d90811102030f500c080800d45d2000c1d40c3c0e58083e01707002c0d4003442420020709188018001ca5a1000d100210f2400d1102c0003d02005000e1481d510b82000c1e24000d003210901d1030240320100301501e002036110050b10a918145460f04404400d40b203000c10010b42c00912a00c5414ac02c50700300d81200c0400c2d042c1652548007041b030901803110b22180c0b01c3c0181003c12040303598010322085070403100029010a20501581000401c0482c0080880303400030b040300f49292442c000500c820840f540f0146004030004800600d040004032070340c01064044003003000c103a03618440d140075128100d0310680010003c00c00100000d0b600d418a03504118503204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 137767428 1250 137766178 137766193
    0x10e09130b0f0601020114010605030708100b0d0e0d0302041a160b010801051504060b0904090c0b04030b0708100605030a0e160b0705070906140d030c0b070504050f150906070302 78
    0x212012641c0094482d800040342d628200440d65809015130300808003d128803030003642c0b4001000304107001c0900044100521640071441e540614007102001c1c000f0100a0340c0d6481010304203600a0044417140100c42c040c407524001c0c1180070703200703540c00c0712aa2200714000000e00f49075801294003503140c0e20f81740402016408040750f01e0442860180c001e10000058905001521160202420403003501c19030400b002030000744d00110580700b040c601580c001c40c59120614018614220342e40000e208540041400001c0c484a0249640034050301c2d1104007481d12001003031180d04689008840200b903042001c242d040c040399200301401a56902601c0c4010800524049559100e60099110030008285601444020302008008027400141000030b240b80c0403090040041024030513100d844d01d40d00c807000313050080c5900844550701842d0030315107141c03081c8041c0c582e030018084e840c004d40340c10362000e9640c03d00e11035210f84003003406d0103141060300c07807000c0181560020100302c00314042c114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 137768678 1250 137767428 137767433
    0x40b0c2407031404031b02011b080a11011401030b040f0b0103030909110306100813050d0807030608150118020405150307020c01090f03020405040c0e13020307050f010e0913 76
    0x5298682480030104444110305050100800b40e0340c0405902d8005001d800038080040e0300405054616030301800e41c15001c00e010b000684441018400380c800d50b026401d81c501c2000803d10007000c1c00c211680328944d10001c0f00c5c444030300b2a1108803420b14541c81c190010300105070440700c60340d400703481545ca0a0380186103554484c05e1800a238011808902d401c40e091040311018002c48424142c02c3e1001d07805d502e0064001000d11500340010010300c4401c03004240141042041e9070110707608041280c08540344507000600e402c90071a600b600103032810201048440d0049910003031241d002c0040b42440e400e00220711a07000c0c407481105421740c1d08100028503501e94403603400540c101c9581c5a500d80c030f0301010103403c0407031514409040001c3d20805003c4040d00e241d080003034940503980044c991340e440c600b1a02d101000d4124482c43c13040002040031031078505a1440d4100e209409450100303998030184410211144800b90109000340b05041981c148000403684c0607282c042c031121110300a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 137769784 1106 137768678 137768713
    0x20f0c1c05091c050c191e0815060112060602100609020304051c030f060803030601020f01112d0301061101060e0c030f04050a0206030c04030303060f050303040b0c 72
    0x22500d003050001c00c1000280c1c2080145c456181d11011b04941141d01c201ca200b4a02154189040a408100c91150400c05c840148004000c1103a5444c14644840f80081400d41004031895002c2541aa94001c000081c05035401030501c1400c240076960580c0d01c035070040114180100103000014a002600c0b0b0081908084055151070355004110003030100d06805100440c00c040011402100100007180141402d03000c440080d206404000e0a886580392070250380030060184548003050b4148900005c81d01440701005130410103c0351641c1d820a03080800010005440460218400d22480d8040c2c0403508031110320b450800c1407041180f000030440407941106e07402003400c0141c1000046107150f802040240c9a24243c0000c0708a5005448240c0029017064800900c0803480104841603480241c0034510702800c04080b120b41c1d500000c9141450b1292030203e000c1c44400 = true := by decide +kernel

theorem cover : BRFrame.Cov 137589928 137769784 := by
  have h0 := BRFrame.cov_init 137589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 137589928 ≤ n) (h2 : n < 137769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
