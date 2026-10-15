-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4360
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:22:09.146988+00:00
-- url     : https://prove2.me/submissions/30f7e654-7845-4d3b-b7e1-031198dc3e64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 783992805 ≤ n < 784172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 783994055 1250 783992805 783992809
    0x71e0e01020c0a0609030f050705191a07020a090b010909150806150d171908041506030803180703050102030c033306090d0b0f1f0e1b0d1505 62
    0x160b81408288940140502004001d5100444c5000c4c3c0303600c9070b801e20108155242c024a00691508020360085c1d01e001d20b82138001c42544003d04560b40000300650392503444201101074810355402030342129043e41d062080000700c0e0041181c491041c50180f104943c5c4407184000ca8070075075180e0101d541c2c0034004000742c030020003845400c00d034403e601c10100304103a40021007040c0f064900a10700c80c0030f00c1c4070381c403403104180030381d2441040d4140341d5002e084045402401030000725800c44010b000b10b03017003220320b0401c4c2c424030081c1ea9000c4d2200d40b80d80c50380b1070407102188580712201064070a43d40b010000070b10038009540078561040d0400e0b201d0400180d02c1c180002503c010600c40a9032203c6824215011561640200300070b42ea61030343c6d00f907108082044102c01a030040c00180c110028083c2c41204801e0305441043c601c0d1101d2013107a01c20501c0a80102588146448040c0210101c0c080048003c0c220b2170719a803619403903152500f01d50b61242075841098080c0541c04991030304004c14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 783995305 1250 783994055 783994063
    0x2010b0303090a12020612010f060f020a0213110906040f090e160302040b150a2714131413030306140616051002040b0903011b0c0b071e0e0102 63
    0x4a00228003540c20260302d2804211200c18500c6420f08000f035000c02081035485010480301d1480b401440c07808030f0768484000098085040c85940000360214001940c400d10200b100030340558002c0c13000c010114444010f0010304161407004005030b20405c0082c10580e643c100a1009116803072103141e92038600072044089401705440022150006840c245202c1c255a040000b07603541140c00090b1451200080340e41156022000c044e0404001400e00c0d401d5046940003142d80b003c040b01c1c0c01c1858074450b1103031814420f40708110a08480440141491524291490081e405003c0c0010303446080c00450103482c0040e15158410100f0895000c00d041d454000c00f40540036003512a080c1c0d0b401000400d041d4811003040442030b0307076003c0c0003004104007404940c942c002003400035501c543e1a40d03803090320750740700520191080d1300c0e000c00013920351161075204000010700d81f54001d103040da130317142c0c13030843c00d402000301d000c20050380e6040d05c00045920280080407026695000529030030000a864 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 783996555 1250 783995305 783995321
    0x402160b01050f0303190c060608160f05100c140d170c040b030c03040609050313050f090c092e08041401060f05120307120e03070b0f09041d0f0d0201 66
    0x1100e03c010514003d07180042265140000d80e16280c0e220b42c100d03802144e00c8250351000a040382e081c071100081c141030000d940e080d43e0409440510680340c2c1d4640a4403511140d200c1c00fa0400105021041210f01034008840154000d261080d0139a2004a546050515005408000c20704045002419004910890b03074001c11240350149010b041039010b403000c1c04010038146413850004005800c014850700001c1200c1e501c0302c1165103e11070100c4104111005014142c041d20010444034110b1629090031802607200c841c01c5454103060b1000d01030b141d040509a840d910700d0403881124a1061414461006440c580e1054550b082071318003a002c040880d0204003460703051907028000c5105002254045980445403124050100207480b4198014078401902c130f1a02c3c0300c180c1e0b80641d0403a2000508070310807025100d40c20346030030a45d883d60065401000c2520000c2c82441c03501c0c2400d50000365400c1071009480501c5100d4045245050080c0c03002c003129400c40040d05039481e40900070100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 783997805 1250 783996555 783996559
    0x120f0602160c080a0c090903050c100c030c02010212070507020d0f0b0f090a0c0e070c050f07210c18020c01090f1e0b04080a140d060501180e240402160b0105 69
    0x442820f81d616018510416401b40c4007005a88882e10340416000303104492640740450161804c09501c0072820b0000e04400c030019010a04102c04419903138418804c40c0c0707011080d25100c1e0750702c2d12031010842e0607811a2008030f800c840040702403004a405504e08001e024420408501c143c903180201c0b0b403c19001904821703161380222884400588080c01c55820340d403249207050010798409000f100d40d0f0100140107012030044030358843c4150000b191000941d00d080b2182140c00d994079542c1c200e000502e4401412030000302d41d0034418008024031540e0540300041e405401e18241c1c8a1131421540b207400220b421032515100c060800c50758140414036030f07100003500781c1c200000c2e840702c0103a0b041c003c00c000c0c02c51b03c00181007001507002d030211003142030801c50380e0341c2c946109254a80080009000b02804681d031400c0c034984001c40301c0904016600e403580740a1454491711500c0c02540c0c05980a180d40b28440380d904203803070701c40d0b1025100d2201c0b00e800b2500001340906180d5140b40040e00858 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 783999055 1250 783997805 783997813
    0x3030215150906060f0703180803030f010902030a062102010e0405100909060e0d08040303110414040b120d09140904050c100c02060417060f01050a120f0602160c08 72
    0xc0d109401400707914145800d44003030010760384801c0000c03a03501c13410a6011018401040c0740c028075078003d000341c052421803a4031080b021788a504c070070b9880c04200e9000100d403034140014000c0060503005507402100c02400802c2403900d1310b07440e4090381540342414500498034030b400c0055607030165108012580644d010003e500300706072446481203c074040d1444098641d4040010408a030f84208402c1c0210000d84200768080c00004007040020707a030030340010781401c0d51004003100d80380489003100c03005049403101e501c0e070324103210250094a40c2654001d000b17903180c6040a0f42888039102c800f41aa4441c100035083c83c0c22040151043c108081c05121154100000107500085d040741400085030fa002c220b03800408101c5d00ca400764840250400e04c0032130001114072078403440310a000ba0f4142500c03000e0369a00d04d41035144000b442502c1c4e100c580c16a04001030100000c404102c80e0182e030382510000301c41d407543d005980c48104010401220301404009000f40c50400b43c01401200c0041c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 784000305 1250 783999055 783999061
    0x51c0210112808270a0f020102250e0402130f0c02070603051608130618030801050d030f08100b07113118061503050d02030906030a0506011103070c03030215 69
    0x2c000ca44010324139144040c2c3c2411100051001a400d0310180f500c40e82260000f0189240c210943d01003841d00328094031074a00840640032503018400a5a030480140381401481d004002c803024001400c2641c00c000485002c610741c00050180321144821480d010a2a42c5000c2d40240b5001007a8008000c0600c1d110a201c200c0c112100c101c615801e80c0e1422803015160400b00c010052401c0b10010040c6103402005640f50642401e110540740c000d4542d001241e0742c8800f40240410080401000942c84040822802d400703241c2e4203801c10307644400d01440c99110a030608840c1d10141781903030709501085520070326140c440c900442401694540b0701c204030402103200003110491041c0b1801580b610030800c4214101e600b10074a0316000311080c050030102400401d1070301c00030300058400c0d0280315150540d887c00041107680c42c4001901080c5507a9030490844007e00011b4110745c104940540c000361041c07010405405143d0103203500e07a282610318500646440040e4000b8010201c00c0420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 784001555 1250 784000305 784000307
    0x12c130c1e05090a0e0a05131a0c0417100f14071d090c07060507030b10030506031510080f060c040506031009050108030c19051c02101128 61
    0x1d07500c8800c1c44144024800900d098007690036000f004880d42d0402c221000014070001d10103082802000d01050401054681b085c031500203200300000507003181c00140c000070110a07003c045540c040c0c0908681c6041640b01c2c40b1943d0320b51001201501d80303611402303445501c0d10b072902c070b050b481e003e0030242040900e80500c1402000040180800184001078500c54001c0800070b0405c501c035140200f40001ea446d05420048664016500580383c5c5840c083c0000c0d64103001e8402c1c10720b0000e00501c00400c80c0b0710741c002100a0800200b13600c1e014001e1000c884141d040e11002140a05101a0310b54080c5042101d034a00d000051900045581d001d01c05008031010704608880030f0301ca0a507002941c1c1c0e6220074107500d00500d19030190741001d141900018602c40d020000c0c02c40050001c055444003a1600c0301c2907120301d40800c014003950000e102c00c00c1c1c1c403401d28940f28046151801900c402164041c140c0c011036010144c2d03034504140019048500c4900d01c2d000d0406170004d0310b8600c40007425014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 784002805 1250 784001555 784001567
    0x3010209030c13060b0a120c031104120c080a0809010f020c06030a022a010b01030606030207110d2907080702030307020d1805031c020721060b012c130c 67
    0x91124003c5054044483c8007880f281c01c5030000e445000744065441401c0c8000034003010401003540c000c0f40c68201280e4240d4440d0280004070031416900e01d04050405582240c038040034181210500b03210b40f800182000248941551a4000da84880e140c260007000900590b9642804004641261410123410ba4507042540d420a04c00280140c85e40b01d8408520601c0b4101440c05014092078003141e4088a415045120114000e85e0244011661444190281d0240410051120501000021843c05c0008800e0480c80c01a41001c030b88440300440c03010f100c940001c1e08048105c1d840304211845400070034668012180c0d2000703500e5480d090000940716a10401041c0801c00786041e0096a0760100d0511405001c2c020300b540c80103907604010060b44001140c003800540500301c40001c009080a064500c003c0107451050140b16140c0c0d01c113070082c00c2403000780d4180001342500d510801742005000d1681c041c00360500030461502020400c8000c40040700700702007030904440c409000c0d4441c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 784004055 1250 784002805 784002823
    0xe040605010b2106130e0718140c070609150e0c060a081906050307090603140a03050d021e0c100506060c0d080903040b03090706030b100903020621240301020903 71
    0x2003103420a0304c51100081080b00001a0044100e0a1140200304a480400d207181102c084035900d0030086020b605d040241e9440c3c180c100754054209000540c1540a9401031007424428040003070008416619100140c0050541e21801555038613a40101c1a0400100306220f400301d814908064160300000e0070428001c0c20f05080030052030000090304107a030400009058010117943c420303a10740c03403c1c030014642c034441518035000c444001c0001040108503e00c4a981540d00d0501c0c190342000b411010354003500d0140c25050b1070340701140d800300840c40600f1600190802411030f603803001c101c010642e0009406284112010440a01010b400140d86000c0c8140b070709110b0066074a40503030f40e0450103503901194441c9000420001d05c00d501241c0701003901e14a031000c05c540c800400600a4000c078400b001004034403012070510142c6018405081554441540c2c11500b0411641c0c140d10444180c4000065980040840c07035211001c0d20111000c807000d400840c1410101000a0f54400d286 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 784005305 1250 784004055 784004107
    0xe090601031a030f0f100b100c03050409090311010c0206150d02010507021009030b2a0c0a06061404110c070314030c07080601032109060f020f070e040605010b 70
    0x109010540051a041d20500c2550018184e820301000101041c0e1500703440c60304000580100602d00c010300c40c052096002486015241c00d946411898050f41c8003808014150705110052200107410320003401040103651081da100d52400866640142c251740100b122402550005401c100308400c050500000c641000c5a290b00d0b00082800140c58a202c2d9800194001c1c1c040c0d40032000080d002340407441220710542c42c441450f501c3c401c07181030520100303003200c0b001312003400042030201c4e0007001340c405c580d0040186d840303840d401e130344100c02c8500660101c00d0002c0a041000d10341d00d840d1184010f0341e180160703204e180194250740c05031030b02c041307020041c49000d001c92400c0c800d490030820b88080428600860308100e8945804e159540ca00b44421105040180d055288108203944001d0560a55846041700141005400e603903601040c140b90045209506001c41a00820044031000780130300320b100c103524241806d0907001d552050f042016041d200b04103038101c004500c11a00105800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 784006555 1250 784005305 784005311
    0x30f04080f04091d0d0906020604201206010602011109030a0807060908041805011a03040308150604031419020303030408090105091003140610020a020112020409050f160e09060103 79
    0x800907010580c000c80e00100e03000d078a00a842d40b070101c440d11112104c043c00004482403c04d201008440302d07080d601801005822000208000510001e000304e482c8060701c8241c0451000e80c80882d1203069007988080099000500401010360203202d51004200310b800c0041c40c0580400c0402c3d03880d000341d40c0c001c101c141c0004034203040c0030060740010855940150f14640d5281d42e60a13801e007010301240c802c020545010000603895244040881c82c1c1120100c8103411a035481d01c040c0c6020400030a9080c01c1c41c14510b8002c000d5880000030310155102c3c0d42c9810303950304000c20b0f1601d08600c503102d12042458203402c1c00c0160b85d00005480e8020f91000b0020350310340c1100c0c01218240501d01406401c44448a652504560160080840380780749a2256007156194002c120303100f2030420040e00035070804100100954031648219181e901101380c050f02e40340c3c2d07500c00c00c4222101161106901100740043c070000c52010003090001d4450303840c05510014400d000280c0b4a000034140e03d052540d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 784007805 1250 784006555 784006567
    0x10c020d08040b040f03210c12140a050c01200f0a020a050a060b0f0f1c080909040c1d040c090207111203030a0b040e0c120a060e15010902030f0408 65
    0x1001e10866003d0030007403810070340f180e82d22207417002d038a1000d020407109000b003140140c21808002d0340305042c1d00d070030743e83d244060a070302d844803104049404690302c03c0011001c0340900841c2c946008101c002d959a4540380d82d0324400c1003142c210f50826842d64600520500c18a4070310b05440152403030301030088441a52842201d5050f490603901c1240181301c0c0c024900e00e070042c48480e030f11010a544040e175020201c0402c1c2d404015003200c1c540d01180d481401507810b074006040314040d200140e44603801c1c261400007c10001411003c0859084030b148030311400c2480944119541101318864000c070a14807800c003640d43d5203042c44d581c0581c0030b086601203038800602803204047c0b08071050103032544d22580207800c03416490354411660b800c0003904040c1001c1c054201885030303100c035412090240088483d4602040b000d02c0048041c3e924034030a5008201c0461603034421418444c1030400100b0320018200c0703d06003640e205a007c80101032040c0100006a806840640e82c0a980010b0a540d41c20f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 784009055 1250 784007805 784007813
    0x14091912200a0b040c051c03082706040c0834030f120e0a140d0218011d07050408060f1f080109020411041503150902120403120605010c020d 62
    0x140386501007003810700c1500c500500b40b15000c800580568010490700301ca15441d4000d01103a0000200b8038980710302c0000b0310801291044683c1a0001c1c108090080b01c0d500104480d201c2000901c4010640e4101d00d003408200701102e09134100514200b030140a52a001d4854490a054040c61a00c000382e00000221041c1080d2046c020155502040072082545070741084296500d80f114203001181c034059002c0c085141c01090103086034200002402401c81c00018482c0a41040c00103c1e00080c0c644ca1424409103c22419070182c150281d4005044407461044102d0030406400f81050240401080c081d48a02262550b070100302c5c03d0403000701d9110060b60400d20030381504004240b006000001c40d0402041d0018a01c00c0e00845040c001c001b07108003070138034501ca00d205248204500e94200760440e8003c1d0400f03c1182c05503202d1a440d25901c1d08000701381e80c0404860700e210003014080104141d04100301228400307840004010305418440003802c01034070110040e00c594101c0424a00700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 784010305 1250 784009055 784009097
    0xb031306060315140105010801290702031e010501090203190c0c0209091f020301080705010c06200901031b0f030213080a030905090109020f030105040b030a0614091912 74
    0x19580316a018005050625050f00101258113864030503481034000041d20b9031181000d1810b035544a0b4008207000d01c102480130364111200cae00c500d0825014044e00000d41e4080c4807035030b00c11050402400e095550b44c1e030790b00e08460050b0443d40c0e140303105005002c036201c3c400c402030802600345040001c42001040c001c1ea00c0820300c180c020b501031095010040c7c0b660340840e441c0540742d1a01c0c0d420300c444000c0075a41d01070b40001d0090041c40d034070040c010490380d0320803810100490300805c000107502d000603060804040308910542e010031030001b10b843c4207507418401c0444030400c110541d1200c0105010080c401001c00842d0010144c012480105004007082c4450080103100115100707400589400380c588101c901c580c0348201103d1000244000007030084540d401203c00d902c1d0f00d141c0c28907003000010525121243d406200712890b00b40002c03550f21469002c030144600d0421245007420280349040110b0714124030000d080c2c00300390001103225100030401c1509080c03107050700721007041e10144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 784011555 1250 784010305 784010309
    0x16020909190507080c0411250803101809030c0312020f0301030b0703151202060a11010e0105100f050310050a180303050402010207050f010f030c030213180e070b03130606 75
    0x2280c03000c558040c0400c000010000120303404c040c2510070400700c4030b0420040381c2c3c10f0388064002c0130041154140c0d46580c4038092125101190445030001aa91502040c035041111030010044554200703102d004040d18070542e032110780b40c6040c40054400c0d41c0c0140b2035200171740002c0a10000c1011603001d110076070142c1c3d10415401c4242900c0c0d43c0d480c140105115800d442c0794020910700f00d901180c1002103085a004c2d103408102440e001d000540c24841e00e94051210032080242c4462042a1360500703000d030520036110000040b0b058184450f0b100310004e06640a80071208000d0402c01035500c0114159224666808002030f982d80c40070303000d2018000000000502842e001e2515040503007503401603000e0b5000383d080300c1c1d159032544c080c841c14103031500e030450214004003100030206100e03400051240300b0703515025080402d40d44030581c41c2c1c0d13016081840d415600d01500a0024154032a0007240340503040200100c6180640440542c80050404680f400040e40e400041c44081e41182c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 784012805 1250 784011555 784011583
    0x191107080a0309050a060c0f030c050115090902031c020d0806030f01020301060504140f09010e0a1508071a040f15020f06010e0103051504021018030807140d02010216020909 76
    0x1c04000925000300929218060707503206291300c010204045202d400005e03400f561003c1d400300c8185041e1410740f51850304250445440d03407290407410000c1812904640184054100071921800078410141002c0a07021074010812142e40e642100590004072001005070074140700c5819103944005c02e0a202c604099038031650700000001604660000c0100112003095042c1310034030b841c140030000040a84408254032104800044c00451054056250071080e10000040c00c0d01c0300e141502021803040e4400302040d0030225041008c4401000e002909070322000c00da500d418140384e61400583c4070b030b0040a8420138003440c0000759600130042c0341081c0e00c1d11400c65003a580c3d079400403503400d41709001c102c0c0d8600406460610312078000301c207240225401031100e00700a065203405c42d06080a42c10548415454160000204030b06100402500d07016a0102000ba51045456460540403596000c00c583c4108001c000c0514030388118542a681160701d1080c40c2c8603081041e10b04414410300c03103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 784014055 1250 784012805 784012813
    0x14030c132a0509011103090112020a1b0b0105040b0901080a080a05040e0a1d010216060b2b020301151a1b06090106060f030209090a0b0a0e070206040507050619110708 73
    0x440780c40d0010b000d4000c031102680c1c0c84849582140c4000c0d1640903070350b907823804500340c43e102e28081c150613009007160344070782e16101086540040c4006c1d494404034400b9180008940c00600150034140190f074114130041d11144100d504d80b80340160795401e001c0f006844c42a001c0b80c12046984107004880040181d141700751030078100410700600500c04192180c0d80c105200c6036901030140c043c02951030000040d40a200721218035103865025042421400f6030180080381410341c40d00083e000030303040c4940110a41c04a80a0b0b04c141821200c01c01561040c1c1c0c6c17a801800c0044201e64120408400350b0003410fa6181c1607000d1903184d100203040001c1800d8050300042041c81441580510304a030340e81d0365480c40499010b4410b504034860a50340c82d40180380900020b02000041d080003000c40e81c060187d51903650390b90b00030402d5040c1900d40600580050040c0000c1c003c04000e080c7c0070342001c807000391030502c6d602800c0d064003c10079401000c1c80b2003041030300501d600500c40174000740503060076070b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 784015305 1250 784014055 784014131
    0x9030a0212010b011206030308060f030f010e160f08190318140a0e10062102030403050d200702095403161506030b0114030c13 56
    0x10b400381608661190026264525051003007007107000705412682c160f00c0f400e460343c4406d000c0c8826082c2180b0050781600c50b81440003c4140244201f20445420501501c00b0031041a0100020b956030340c001000f01b101c1d500c0c1404a50700c0803071700d8280001e002c0c00c02000c035240340c41e040d9006664001e01101c4080d801c035002442182c5034031410501c5000321044002141c40303090640c0d041d5802e50360046240c0e00d049003402001d001d00d0f0001e407120018449980040110b81414041e41c1c01210100e00060303000c10500c0340341d07045010760340941042900b1400c2241d010040d07910940943c3e64064814980d22001c1181004444040072103185c02c801d00c03610034010b10742403010122440e100d1780b800001c190401c000041100e9102c080360034825002e14600307011080c240c0000002d008083e03501030b0b81181440041585486104021446074107a0b0020350b251082950500e8180341a6030700070380080c0c408480740d6580d101801c1044141c1e000015a000d15902c0710b40020b100600340034001100c107281 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 784016555 1250 784015305 784015339
    0x17030a0b040b0102062518060e1e0f041d0706020102130501020c0a0509040302160909030305011202181003060905030304140f0307110f0d0c151409040209030a02 71
    0x4184410305850500c6010a8540126a81c5c0d000b280d5804403030701440148049800301030b00c07480030984107143c203407201c4024910740c400c0b6614640c802804151592030354171082c2030400c001c0003081100c40a00140c4800c600101b2085440c80700a03910407079a580032030311040d80313000052000d6040c010443d2440303070702ea03100039000798060b030200d5030300302105200040c0c1c56200003200000e4072009040407109501d080c040c070252040247c030071030650007041000030040380200070840c02840d04e0390300452212210b003009402c560301170f00407e80e07071010b02c1501405030b160030040d800000b803d100c480519660b12041c003c81b250305900001c22075808d0000394418840000301550259002c1c00c0c01c8014041c5003030400380d4541c40012004625001031140d00040342c3c84950380c600121014082a0030340301d910380021503c3c1e03d0604100c880841c0000207001503c4034414010b801d80050521003c04070206071170890034001c03040118070440c1c0000d800e00d09510103100c01c4007051b40c0030341680c00061803000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 784017805 1250 784016555 784016561
    0x7031403040f02011209051f061d010315050601050327030d0615080603060c070c1809030f050406051c20120f040b0412090503100e06100e01060c17030a 67
    0x103034002244051180d1702803041e0304c5800c11890340000100640a604400c0070144c840d41c0c0f004e00031166545c18001500200342510109280700c8400b85003035581180303000f150701c018200e116407801d0310380703802c000a80e6044811281c0100c108580c12071100400108560201c174255507513003880c00003092101503500c3c1038000100741c5050045584007030b5407a41089504020403685113515602400210b031101e840700d80284074a0b07004e20a640851034403001e1420600070b25020208225a960301c3e15030034146d00141e200c485410324601989028a8158001c240340140d240c0300003066050301c51000102c4d00c070707440050004084e0341d2070354001452000b00f11094201c5a00d1030000d0203060b000402c58415007184610807540300801c0c0141d61070b11b49502ea01c0ca80880c0083d03013400303020075001c10181c0d400c0003002a13043c159280451944d200d0719000d81050340203000000c0c2c844081405000480c5404c00b4141550428509214240c0050030001071621a0b4091041c20002c0007060000e204c103550 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 784019055 1250 784017805 784017833
    0x120708090a060608210705030306090c0f070819020f030a180905090a030206010f030312020c0312241804060b06040b0f120f040b0712140f0402030c01080103080f0703140304 76
    0xc60960421702c00c08a03142040d20445000400704e03041000011882d2502c0906160006081003030a4100400c0301140991544401403e50b102c80307002c03a0780c0c0c1e445601003c01c5040710609101030041441c2400203d03a41e402407507041d00c18894110b010080c2e0744c03070001c506c10007080001420f0005041085040340c840300c803200d041e40140114800402c201030f105440c03004896056032000100e099540401d4003e411072008041c0e1400104150380d0002943c0c000c003801034800200107850307894a00c01d00c038940b642c1c03502411302444950804480001012459951064008101140c03d080300d4001415610490700250300000300803402202c0545d4401c0036151042843d400704000f6120308500002640c411603004010709603e0b4001842c0a02c00c480f8620b50118803d00480c000040c00c040d006a0f0781c00300c0d160541480210104015480d01300254030072281e0a0030020101d5045071541c144504c909141d0b084808400070303441042511070819114000c00207070550b43c481c10903250246a01c4402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 784020305 1250 784019055 784019083
    0xc0d061404060e1b160209100f05180a0903031418010c030e0a020103090302010612060b0f1f0807020c12010b0f0a0f140f0a0303020a0b070302120708090a060608 71
    0x2004500d008206000500039a054504403000c4007100d030903600d040d88a10105008054507070702d01c2c0b0040e1982408203028400104e00b07801109e0900d1001030041d015640320502c5541c000094006036541080982e81145031000041061b24040c1004c1e07014000c14800c5005410141c0104031460006500c3c6103444107182000b40045c065102d000c5003a00c2e40182255004d0b041028400b0056010b94480012244030340000318820f41ea80c2509400c3c6150803109441311600c521003400145016003040c401010300f01c03030703142d407450340c040e40400c41a41144100e414000b00c0d0011410031802000003c00001c002031400b002140d0200c51580a8030385040414026407000121101900c0d08403049425501780d80c80c80c0011602d07200d00c41c4420342d0880922900203100c55139101c1141c0f2211622000b86000f03800516080c0200e01e080e002410300201800100341c4140013003541401c02c40c04003a000011881c1120700c9840b0f00c1c4000b400c0104504006000b42d2a102c2d00007a24480418000315003592 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 784021555 1250 784020305 784020311
    0x304051509010b09010923070c03021501030803010e13061a030105090c090c0901091a03041b030c180b1003050115020102030405100504050307060507030209040e0c0f0103050c0d061404 81
    0xe6a0001070a0341c4112501d03a81c0802c0150062002e14015408107e10703d00542c40e0300c425115040c1808000002a208000003d11446051080c55010810b031031b03005068144540d030561540c1c54120359400f06004d1040884401c0d004901180c00216002035050f80100c070412240c046120b80401e03001d190584039010b5401c00300000c82c404800b01d02401c1c008809001990984d41c1d03d16210440d40c46514141d044c8040b00002080038a08142e004210340404043d00c0d40d00e08081c189401c07840361074070700d856804140550620000d88007128a5080340d602500c0b4240012008100c00044c000e990303c000c3d004041c0b540d0900350507a054010174101ca1120400b45401011003004034244c0c441110701900395800404240140c5030303158000c59215010784142c0381000c00580e5107500340c44040da52080001c0d00414034042c1c5150602c1100c0a00040000410101382510301141d552038a24178034606040d07540d0001003001c59003c0072034034000d03d200700070040c442d2a8000196031100101c070150103649 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 784022805 1250 784021555 784021561
    0x709060312051e131a07110d1109041a090a0b0702010b010203091513030602040f0906081b0613060302041e051807050714060a140c1803011103040515 66
    0x1020740122200c0803d2003049580002d0b1984240c10340b81d00c100030402c0c2c48407052200046040d80394080d1100c40683c80d94440d80c502103820184138507501e00414a00ca106280d01038400503000040607401c401c01651810400c0c1d40f141803c94001d40c82014074001080c448007040051540494500140341c85171069103440d40f1482800c90032101c2020f40b10380075a104005200b000d15000c080300700c0c1c01a8100d01140b510341d0080103981a10100e91040700d4141c4c0210f014400342120031a041d000e0480b04000300142490603082598607444002d0707500000740c01c510440c040d078440408448084168042118281c1c0c1d40e90b40050007544030f4820303110448030f100e44414100d0001c03500b200850b0741c0207051144a0320030028035900100068000c2c07092110412401d0001800000119680810000602981d00d0414003080a58505d130110a910602c40c03010000702c40b6501060b1152214031801c55030324204010042401400d5600300d801402070b005c0704120420600054002c11895231a54210b09a2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 784024055 1250 784022805 784022807
    0x1507050906070212010f110d05070e18060f120c15031612091b1d011a220801051f080604170d14010f0e100302010e030f0709060312 58
    0x300032003000070341c080700c10030490025180c0922004218103820f400080d1840c5194060001ca5105000901702c40c003003c140281c50b01054031a096200200d4208031b440001e6076800114006019480d040c0e120b045c1a020507490b486071500c0c00c45014010740400d41651500c034900c0d50720926045031a10a20150b600c00b8000000c1a045c0e03401201c2c0c141d0305403891120114195a0380007585101195035680e2283c0502003801840b075180c600e5411059004190301303102c80d48084c0d221010815008180500042005040d42c4980590303550400c1e20301034440319100d02d42000d10b0900409622560741c015004039401c0010740c0000c1c0110340c0c60040d44428824001550755040035445640c032141c0040c00041c0c00f141c03664101c120041c4149640a151118480003803040340d1040c030314410242d00001c01800380080c294182d0020f0030301540501c9051603c40c480048045041c00002d04001496221142c1c07078404001d0014204524816240010b0f240d0328408001d000d1032205503181001a0801c00c91a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 784025305 1250 784024055 784024057
    0xd051e0307050706110a06020d0f0e01090b0a0b010c06090503090f1906030903091508040b092a0604170d0e0402030601050d2412060f110304030305070905060705150705 74
    0x1841d802000f0b40445440d0800603240c03503844880c6080e243c0181811040052410b2005091000c0200300004088401c030540d0421103c41c201c3c44011070b8502207260780490003c40b5410703401058540e01107256a0000012a08081c20351401800c0314181481e142c204200400501907010050340d084a811142c3c004014000420841d40b0701022140030007407001d54400c0d0010044c26001c0e050400c00f55685000040b800004a40e414000802c2a03040c00304125290031915040309184004001040f0506000ca0b0035044824000d0300c000e071840003108140d240c4009035402010140c10509048072219a100c1e1100740e00e1104800241200e406d0f030100745003c0c401e8030b01070031040e556a0f0601000c442280b00030018442c50905100b03407036400002d60240c80000501418190000350880040f9103440d1052740c1854001d02501030618407210790b442109016a98001e0300341c500410561100e0700b050300c4c080c140e80c00c83c41d00444001020800e100c400181d1440c0704411640c0011903580708101140c035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 784026555 1250 784025305 784025317
    0x30c0411121b1b01110408100f1a1e10110d02060f181204060f090801060b0a052d040e16051611030601030b16080411090a0b0d051e03 59
    0x105510611590001c110980704443c14a501040000f130044540001d00c03015070440d46c000d81c00b641c40b10040381e0341e0080d18000d00084641d05641840048119401500b80089900c1064010504041410280020120800f65501c0c000d011440e0307000407594014400d01c000d140e2110a0b118200340d03c91494400920540310360200340b40303642a0740742e007044491401108441c1000501c205005118403080c100004d000030812074070740c12025481000050104145030707011070003507450030801f00400d06840045800e10360051815030340c3c0f8504182c2070710100c1d52100301803500c01008400322181d00b00340c00081050751b002000d00001565440e50940740d480f070351010304c3c002503414000109508108034408608a20968006076140c620501003841c10301e00368001d540c5a010f1a05006c0c160b4005a05051541150319003e00300386050740b61807103207410101c0818061140e5500003a0101030300d07400360281181c01072807614081c00c541881d0303594184050300a00a1070038031181c0e0050400010031a81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 784027805 1250 784026555 784026601
    0xf040209040f240c02071a030103121103070309170c01021c020106030b1311010804170d0207080d0e160f0302040c0201110a02010e0106141c02030c041112 68
    0x10325036a90380d40c0c0c010410381d040d0048546016410442d0b000e580184659041c01d03403100c1c0c00180d00758035104002c2c40c10080c0e40c01b11440c2d00300d0480c00e13900800e1400480341529007025000b45200d040440445d0014000340001c1100c0c00089034150415601540182c11500040f41d964404007140da46a0f8803244100382543c05030344404c0d62049052200c0e00001c8643c0741c10f000008040e0358036101c040031804115540b074000400800c03107204008101658081d12402840c0c42411880e107942c1d080c13000d1000b0445840e140314042800603080e207090f0100c2e941e16521421090b2a003248110030800b416001c48180082d000312991000200c020b011990211150082d440300c1051542e001c1c00010b100f80038400046540754054241e1860150000304120700b050b50000407000582e00600d030860743d4517000701c8110085107000d9042981c40d000c540c000080071060780c880700d0000d440000c0c5400150300445822030304180440c008030070101c005e02000700d081524800c07565609808900c00e24224000c4070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 784029055 1250 784027805 784027819
    0x61b200d05010506040c1d010c05010b0a0603150f06080f041e0308040b0603010e0a15020405030d091d010506030610030f110915030403022d060103060f0e0615010e0d08030c070b0f0402 81
    0xd47da542c401c8140300d540c18080e800018014417400d012540d8104140c210101280d1200e40305041c151005066800502c80c1004158003c7e0800b0b90042c202c0310040c00b88202d911020713010809000441c400b0f003003561019031281851540724500900198003c840c02d68010075180001025400c06001301e031006000302c4080c0c00402c0031903403000c00100020003103030000b0754244004207042c0c50401801141900703d0b1107401015207061044044418001003038810440008010884d640341d110076641c0059080ba8550601040f0708421002072803242d010000c1d0906040003a0000c000e01c100a000c440401d071121143c0f10102c0386207403440c1c171003500e00400603800780700388043d502452500d10849064181841c2c0c0d0035065583c40c40c0c901340c400c0e04140d490966416501007049124881c034459500340d28050701d214540a400324400c1c416401189061003050103504100b0b81d214942d00c550309a100c0111601c80c00c241c64000b116030813042048421040c030a0110b848070707038503c5095202d664000c00310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 784030305 1250 784029055 784029107
    0x3080a0b100918020c0318132d020c011103010914010f030308040519030e1c0f0201031a04050a0c09060c0b04060c1103070f020a061b200d05010506040c 67
    0x10b651400540f00311110704aa0a10841402080030b02c000c1c10325010040104400f480e1070350820420010011545800902d00400c7e040741f200c10000c2c1002c280d1040941e4908140d0a1040d60080d12441d07854813129440d0040340c010040c00312020b1416100d040000b000600d00701220f070800c2080a000b6403011640c07040c0104000381c071070128590320520cd00c0070748603051882d0400582c10b401e038030740403404140383c400908050304107030452154901a0404030228121151a62207500d480d00c4000313810181c89215081fa1000dc00c07620402e401806482000703546080c0d21114020881000081c0000b10b44600001e0401d209036143d8812a400458070b80480d10f035079a50100600710300c0058400d200d226100034581520610190801d2406170240d10500303940b5104203c000b810030b8101c04180001e110700c120301101041c0400c0b91050740f00c03030741c1180a401c24200411b810403001d505070703211008602a00822106401482c02804280c9062101c54048103060762556211800101d80864030509 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 784031555 1250 784030305 784030319
    0xf041401060b0f0a03060f06170f0115031d0a0533180a080715060e19020c1e0f0f0d120c2c03071e1e0e0403080a0b1009 53
    0x1c1c41404814100050280d80d20001e202d0440c0903903120101003800907041068061809d25000e80c03180c00c0c90341c0c103d419810070035502800d0100300c61030300801d80d03544401e243c42c0d00d12291800394200c5c4002180d0804c401450700560711402810700c4902ea40307544102900c49400c18a03180d41c0144504d0300d109903035803080803c2204500035a0304018a00c611050303100454007c9008000850152020741c0c0401181104601a201035501181b601b4071910100451422142d00400d0030341c3d0f82220150b0360b0158030302c0c50351421710070381e440d511a940d01c0500c148001c2c0b0b0000d00c00d840d1040c541d00307640710844c0c03542c0c0803078441031070b000103c010451701013000408800c2daa001d000b1400d454182a06100d01d0190400d00580c507080c80c070f2010700d40200754980c1900d02007010100034408400c0460b41c1d000d540443c2901000c0301d1041c1072842015003410420b01c0416440a405400b00a000c2c2e445031501e4240244035900581d4030442c1e81d460701075080b407642060b5a0010141c0f400d502c03080101490125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 784032805 1250 784031555 784031557
    0x20f01140105010f26150f01050d02091815130c0c03300b04060506030615070309080d0c02040c020c09011815080d0807110a0b0c070b0f041401060b0f 66
    0xc0c1003080000071404000b50303041c540382c1d10750000e90b035042917a9685411041c08002e03030428020380e8800d6100701c1d82c800070341e03920a00b214221500c00030096201e00449001c01c070050358406080e51076041d01000c018007642a0540540d01401c100d41c0c1d610002c5a041d0604101c0380780344440c00000740090419408a130142c20989030380084203d00b00242010320701407940c0d1402e02441000c0444d250954121244ad0074003655020b0802103c6003490350070080b001590034152100c83c1d424010b00464000c1c18180190440c900609804083c3ca40715290110003c006108611080f40300f5031426008481d0300d0300c00950200348040290101c40143d0924049141c9014004410b01c266502c65008654186440c9111401042460000c10000142880103010f0503c0140020100a540008002e140400080d07155405130481e04854080d120f8911031074040c4a0190040c00c8003122006021042c2035543c8540c1c0b166001d4044000c4030301c02c01180600343c4032540700e0044940b10502131980c1d1590054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 784034055 1250 784032805 784032827
    0x4150504020f031506030615030a1202120d060807120201080402010e03120c03030a0b0103020a09141c050a06050a0b0105040e0c070c08070e0105030106052b05100b01020f0114010501 80
    0x60034003034502034010000389072101302214500c0c0130b51008280190303400c0030400310350084024001c80c0000341c48180420758455058002078071301380031544107042d100d000703209070400d07298820702c1d2a6a036508941000e018154a1046000d9481000b90008004104010b03110a096059440d600b540d120764004640c01200c0c8410164940100300b041e43d0107261600c020300c0b10001c65400756840349042c8078101e08031445a02d40ca81814010440450610341c08121b82003509c020740c082c2070003640003002003260b000c4603000180c00c00d80301d42c901c0018403a00003451005070b80303e401c09007d2a95449003606c1901d000b220a60b0102e41706000900604403054813299020100c0c132030a6040002c15200c59111281c1648a00c0c041d420410341440301c182d00c40e910700e014020603402070000c40e103000007041419034407d2401941190031040c4890500d4180c4826003200d400208035000d074840241c0b01c1004020f8060740d6400342c460500061038190060281000705940300390099010382ca001c0054610401305 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 784035305 1250 784034055 784034059
    0x108100c210608010e0d030e0a05030a1125150c0b151305040602210907030b181b0f041401060c02060720010e12060c1c140f0f0415050402 61
    0x8500c00700f81601e09220f100a580d410a005041e00d0b5403080d80602210452851203001b900716500c4640411000401c48010318981c1c60080caa1041c01c00c141c5e41020080d016120003180134444169180d500440414191003110000301c804490107001620340c4514540001c081074110360000d20340c4d42c0710009080c000344014280c82100c1404912800840d403040350304460b8598007180801384c0b074442c1d5921070038650603564500001c1c10020711142d62400c481c80003d100c10100030014000d000309513941092040104122158031280d0085d8a0220109010540c0600030b071101c47c50592910b07000328413111840847d0703220241d007001c0303044441c1c900d00101681c025100300510400508043d90054034004215a5140120310420005140c904044a024810050300082206602011078400d0f002605030000d40d40e5680e805125500f102d400441071021603181034a107446040915021602c6002c00741540070240e0b441ca01001458003080e14040e000a101000c00b20800c0b1075030740310b540c0040c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 784036555 1250 784035305 784035311
    0x1050c0304030813080606030708060f15090f1501030b01050702090c04051503010e070c05030315011e03051008010c080a020313060603061b0201062106020c01140108100c21 76
    0x2d94540340c61940c0004180d0031103244c110400c20080c041401420b80095049001d0002c40d49080c3c0c5c6140d0300c00c409888019007126620204440c4800c0214034921628040c0c211881e61410f43c01200322078a0450b45041908241d000150056102e4400d0841e800c0b0161a102c1c240301d480e4003403001d0010010007851500e02c5c10000400d441c0c2e0b401700c00f040c5540d002d4000c42d03529030402c000b03149101c05c060700e11001c0c403001824540002e0b80120a89500c00d0712802e406010840501c012034103a00f01d0101115108030010700e0100d09a8903400c40c1703200da510401104665a5030784e2000d07080702e64880705980029602e501169401b03000c0d40045401c481d0700e9455408c800c906407160b0088034611b0b40103c42155584104038001090b0a201c030a003c0a180000c22866241c50120b9242400344181d8034403907412018281c0401c260317503058804401500b00204070843c1a03000031110f03510280a003500511840c11010a80c070b2840c00b80301c1c1c01c02800e84d2044003c03010f034100307000024041d660804040392 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 784037805 1250 784036555 784036559
    0xb0a0f0e030d02220b13080d0519090509090a02090f0601091a0708040909021e0a05040e010216120813080414060c1f140103020f0108060a0f03051606030c080601050c0304 75
    0x3d80302503100041c0030300460340759036681c6d8507101d0300c800c2d046640144107981008a90540f01038000c01540c6d954035440d140700001c04043c0c50704070b507910711903040300368020b81620500298807000905061507070f1003555842150b4840c004858100942151505c2c00209405000c0c4a031551b00101c0101c081021007aa0342014806d41e180490381c0c01641007021200d603184580c2d400d614101004000c050203810b44680490000700216108030710307a002d121b01858544004c881c45010940c1210b100524501e4100e041c0c108034a081c0980c4440c0c004480c001460344400f241d12100c800e07642000203984032580600d054501800032407050800e41c131282d0300400038480b00da082c10042c0100001c03010100c030403c6640e000c1d400f03540304865241c0f8018800c0b030164401800140c4890820500d003103024200a000d507541c0c040054a025000d4108000101103e240082045000145a0101c94100b0a0314041c661142c90481c111001c02403094001090017011074069405100280f207240a07103419240380907 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 784039055 1250 784037805 784037857
    0x31e05070f08370b0603070e0a050a0606140301030f110414161b064d120609090f162c041e0c030b0a0f0e030d02 50
    0x300c510750212410b50000b0503a400302a814540344490b00300d07140c8600b1504007040c0c2100c4111043c8202c001c0181140c140820b00d070781d8041040700000c101142080101d40303001410341014100c0be6402d8030380541000b0020178818020681402c0080c9100720440c20340c2c0c40d544405200c1c0040400544e220880d4841c0d452158486014120b00c51101c6020352895090200082c410081d0714190581080740081000101d0a40e86004050f4141c0244010406100d0461010300c46140d0809003032080052660305045c101880710040c0c9000e0b0107250785d040c480c0600c4d001a00620a400c5d03051031010460002a5417481c020004a030421503136021103400035420728801d031070105040c2d60054824901c65040101018402d05803145c01d45000b00800707090b80a590440c3c5011000d0030003042484110304280c0f00309840c480d94515240c01103407400714940d80707003030220007800181c031604042400c03e80825121011801540c0000c8001c1c0021881c03e42030204001c025007084508503001040c184d1301024030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 784040305 1250 784039055 784039079
    0x220204090b04030f0f0f05370c030e0a0b0304080d150f140a06050f03281d0105070203091009050405041103060a0c02030712031b0815060301031e0507 66
    0x6610035140c1c0d1a15030403e100c080c002540c0480303030408001522032a400180e40c03000640e150344c10304101d031084123000c4a035400d0500d03140d00b000d050ba00910301d10b0b00c014183d0045004000502135201c0c100c1c409489803c2c401d1a508034000c040365802c0c208007081c005100d1100500311003401036400941c509119072016540390207548030031110411b207082480864040d190481d03a8501c12196894042e00e4440050041d010312214210b080e0720200000704000ca0446d078004581464024000d10a0f42e03a452000040043d40c0b203146900103c900e4260301c074101441400e000f241160029802c102e8604e0401802c41001711210042200d100310019480c0c9503030041500680c03081041c6100303c5080c42c1418903190001b80760114183c14103400c469015000b10442d00300703d03004079981c0030074411040300764050a204c928007140010300ea25020811548822014002e0041043c42c03542e180d88031080212170b010038040588455101c2072203030a100001c2401020080c40713132040d661201d544041843e61 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 784041555 1250 784040305 784040311
    0x30201181209050913060b1239010c06020901180b0a02010b06071e030c050607020f0f03040e0f060f03120306031c0507021e040c090815220204090b 65
    0x5100c1d40c0301201411a80c01180d9200a0b20081d02c07100e02500d081c20a441503041840d0014100f503035a10400c0c030941d1281941e0001c428800000c403604005d5000300c04189108050100071030b0751403d561100c0d901011030005280d44016034071200a485e058a80c03000a510808c405410302010b0900610f0020004242c0c0c0002c01c01c89040c6600c41385001806030a50700007800c040d1050008001c214000345286984001e21090442c80d14910707152890185c401d0054594003070a079120b480200090242c0c0055811450311030101a5040c1c11040040d4030398a008a000705155402c20314005400315940f1105958030000c0104020070751000800468144004841c12003078014002003000440d040c100316560000184a200c40c403c5d10115074001c20500036200024800c882d885030380c4d440201c030f0180c44100d81000800801c210800c10b64054040d4103d0b115011190050208200980e411498014464058841d2103021040d60070b410241d0502c02410490b4006d41c0e548811010800c03143d94a84 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 784042805 1250 784041555 784041563
    0x1506060d0e030d1d06070f020c1206091002041d0c0412080d05060d03080a0209030f0f071a131701020c010203041112012c071707030b01090513080703020118 69
    0x1a07111102900784064419095020744042c4922036103104c08807000581039440741c1c403454801a004d660500881c10445407017103455001d035650b400e0f143c00c4000810458001c07007003401142d8000728150201026800b0354480da070840c41c0d1110900c0c4045500f44000750340540440139041c070300f0792200007404555030866415944a80301260201c002c17221403180b20782251017140c21000c00007090341c0080800a00400224440d500030400f20050b807020420410121101d0017514802c101180460740da903502442050106940e010b00c0c04503025040040381ca200c4800800390f12038604001c00506042861501c00c0901d643c00c0100c4120b000003840950b018034030072111030070f912041030208440008030900803401790b4500003800f900e178000ca290800240039490480f44880d159444140d080c4010f0740e102c418200d200050312009c0b40c80104a41040c1e9104007034104d8140d0321008981c0841e0002c4410b54170307000c0c06504610101d02114094060b4074400c0c40080b0712040d00420601c1e1452017664115 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 784044055 1250 784042805 784042807
    0x4080d0203030f1b07030c08091509011808063c060a06030c09170708010e030d2405130b0d050106090e1218010917030705120c1506060d0e03 62
    0xa041e809002d10640000c4000d141108021600000741130510480f030004091001c09200501004404010365562150080212105103081d00440c2c86590010f0b80544c0050354440c5026464041d00920105071460701009101d04e660b0300890f0020391054000d8210041d82001c42054604010100041115040340c105c48090600380103110420709150010000d060610212103242580074185034100d03415407003008005001408102c1c100302c002c2e0428807040d400d0100310149441c0010040003200558002004010305e5000010000b010002407025070743c00070300e01086107261401c07207004a842d254100142a4985000250117030a00b40012181651241020401103215104454040c14000c01a0181102942c68500948184401c000810740240e5140702c850348150418006002040c1110300d04000c03040916940c1e402030366040704e4501c00c00500004a40390a4180c6100d000780030300405140c58400300221503c0e000510b07480d0409020700200e03900440b1802008841c00c1c5481c00343d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 784045305 1250 784044055 784044061
    0xc0c0a120b0408181c02091803120406020c190b0115020601060e030102040e070f09061d130608030307050c0c060702010c112206030c050a0f03022b080910020d0504170304080d020303 80
    0x40004100024148518044102301c1c25102e034502104480f01030310501d0070b1645a5540d403615100034050404034558611030002446da4511040d0502c40b0785901407a1500c015aa84034440c45a091080003c40016089140100f00e0706025034440410050300038000f40c20035444100303442c0c40c8002214035800103181c280d10302032000d030040440030180034545018a40404946019019081d00980b803500901e003001c400200c4840a600902c0a011144c007030b0303996400c10501c0141241c00003541c02119005504103543d081c41c292041301c0102e64184c68509070000780f5150b00c54040059440990091440304401c4a09001d40c6c00e0020700341c460f0340000900e0b90460a000b200284c45400650003808000d0f810300540d098000d840e021a0790440d80d0381280c00b1005980b6082c103024505040f4501c1160a000d010032420308050324412100751040610150102800c90752a0001f40c1080c010038000c000a00c14103400c0c4001d04e898030340b200d007124a0555a140c00301d01c0c04161380703d0030005030004402c4c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 784046555 1250 784045305 784045309
    0x1021204060212180310240806010b07021201050906041b08150a090c06051c05012d0b0403080417010b13020c0a050303090105040311070602071512020c0c0a120b0408181c02 76
    0x100c15503411f10752401c0401c1d1403c1a950603170701c49060041402c0032001054240c01c6549d2991200707400314414000744181c0c202006000d03603079402940d00b241d001406151007040c02200e40c0083d000c403007511004200c020640342e030000811401038512001c0c3c90701e45036603502142c1140c1c9140700a149a590383c81d03465107000c170200b0418038403004201e105800c000040007d0348a0202459040c00e8141c0b01101b12040031552841d2400e26912103403031001e000c0303400001d004854002e4000c4035100101c00c842d080c24600e805080780c010f50041e03944030b1001064a10700031616805041041c02a0301208c1c2170304103644803103103035400032502c0815682d114020001090741c403600da00340c503480100060150604042c0d001c0e480c1d607158000c10b410060010740000065104070746681e5010101c2108540d151070054005854258005509000f13042907580050f4a84641e5610703030040e500444414669200e903904d400c2a50300504903a94100c1c42030781d52100507950326405d100c000c200c0780b100f0310850f00b003441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 784047805 1250 784046555 784046591
    0x606040305190b01080a05060604020f04050a031101140307020d0c0203010609140610030209010f050d060b040909051501050609150702041103160c03081305070305030a0e01021204060212180310 85
    0x5d43d0701908621048000100c0000307140e50065001c54002d6114208480f40141d540229404654001d401c0c48000082c070022200304a81e4020030f03a01e035291520042e122408031b00c0191201001030f071200c0004070003644140c0c000100d25100030000308942d695102e88405550020004e96021158082844258138161110f58a200309904040d401d050a400c00600354030a90b40e0041c0c144400080c6000c000c0d811544010058000411480c0d02d80c1c1c0c031200030710003c0c0492501110644075030204084070142c101c403528101c41d0002e0007903103020307400310511024604407502c40050350424000c64005a03218040d090a80c40c80c80e60351a2645003034074808603140d44012551042c0085808d00703a02003584114241e0748200a14940070382c022071858006c0c50606a680080c0c494080411003d0600c3d03881916120b09850903030072144044000200900c852003141f0800002d41e00c0b0404d100c003400f040e000502603415100552802802030580480d0420303c03045244415581c2d9000d064001d6080d50b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 784049055 1250 784047805 784047809
    0x1020c0712020f010c080702030a080705010c031b0f140301090c12090201080c090d0203010c050405011d180702100c020d1709070e0c130f290d050606040305190b01 72
    0x40110141407038281c01089403061520300140c100041c041300b840c24005400d086400955020b000c030386843d50b590601c1515500943d0046a5a50170405c1191400d882400f480402c0c14003019501c841b68030380c100548040c0060400c480c14001e030000c9034444054030201640c02800f0302c40020408100c91a0002e012800e01800c8140d2030f0700d80203801000d070364065082d0303901c91686800c42d07076500d10801c00202c848255403c000d51540c00c00d0301c070710440360740600508111542030300ea02800910301d40c030f07200424603880050764111000309929001d44103004110717a040000340c015180c600e15250b024000303032004030402c4c3c400740c2d004400400c032a0f548690140c80040101d00c6c82101410442c032926190201d910443c4501745040c000325000810745400c8619482e411241c01081c560b0301c805032481030250f841015000c403000194207403404d02000c41c0010400d0030b8150705250814081c000002040c018240300e4000d1700c24400407002400421400307a46010840c02161800b8040c90181070b240816 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 784050305 1250 784049055 784049069
    0x34050105011d010f0f05060a0306051e0310090f2604030b010f09091a0408130f1a160f05070b04032004020a09090b0d1a0711010506092a030901020c07 66
    0x40800700301000b00400008140d81b0100c3d401c6560340321002045024140c1600310039800b00c51405440c2c0b416440e22032a00340b03808150203942c03103404543c1d1000704694007401e02402c00082080b070800002c800408202560310701a0061455010005a640d000e4001e900112000d003e02801844030640200c001c0d4001e103140d10084c400413a25580c0c20b14140c10b00b11106c1e00b40898040460704224400e802c1c1d800003c900c002c00b401c1c883e5110004012080144911040140000000c1c07040072a144103c0307010144050396802c410006903a050041030560b5810707106401441f03004101180b02100410056010f440b0001c83d0300810120b5048100d10301905608c2644100101044c003500529800125000c0400010b003040203800860341c140740b07a81000700164441d400c1c040c0d5800c4400e8004e030003000f091381c4040d0703070304205002d0b05c3c00c03181c0554070141c0c0000804001402550200c81004050722203c080c150020802da031801c64680007038132141c190341d40102764044816030820480005143d0307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 784051555 1250 784050305 784050329
    0x828080906130219151d150405060a111903200709150306090501020c1209090a020f070b07020f3c150a0902090c34050105011d01 57
    0x1c4504444100c0e40c0340b010090141e01104044070510900d200480010030088078441c55103400c1d118010400c400c3d0000c0c030902c0482051300d080090401c001842038a40500a26038942400d000030020303190020103602042180f541c000301c240e82418441200c202c91610007c45404410f17140c040c0400084000c10120101a400000085070002410078200c55810340700103980081c2c04401d111109040d007000d01164102031400007042015401009580c0b1501c0c151254140a00d030525018403529184942c007800d10004209a180e50740e0081c0118400c5004036840c115140e42c40c800341c0c24044410301e0240e080324900d40940c803018845840e10700038610210001b241c1030001c0c100403172100400004602e4a12181d20941401008441000000c00f0100403040c50301304200f6000d0840311070104d009240344404034480c028880b090350408801d40f9210b0341c01291480000c40b01c90380031031280d10342240700460103001c14428410036020780b443c0e840c058801c6960021040ea40041a4420317500c00007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 784052805 1250 784051555 784051561
    0x51903060f0f1b0804110103200c0601050102031e090d02090405100501080d02101a03060415110a021504060627110717071a0f04030201060f140603040828080906 71
    0x980065015800342d40030640c031b40a1302c04040100c0082110944200c0d042054803200b00c1a41241c40280484c0b40700101281c2c542e0f030329000126280c0c010904034007000924a1403511410310201c016020b03161011302525202c294503000103030700410996003a201904425184a00030105000b0580503140c00b130020442620203a50003581c07440840c12070b00c5c0b0203a44001003510542d01240d40180128020308440c06800d1508141c2d00c004001540c40d444503190410043c03042090b042030700ca948000d41c01424140300e0031000010310a00040c400c40340c4690b24200850540e00494040508840001c40e08500e205645050000c560801c42000c1162342c040c01080c0000f0b0f50207450303005d0840d81d20801511155145818220002e81156000e840103240c8108040c000705500694403a50203580240b04281d82c41501a90075640b5020315070130030034158244003480c1054402180c0040c811a0102c1c0f5151754000988000151b05000356202d480c46002e81182c6a4020700c0e464110006a0241650f42 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 784054055 1250 784052805 784052807
    0x30c010f090506030c0903031b010507020703081921020a080c0301050616140d080415110d0207030e0301020a091e061b030201020d0e031c060f051903060f0f1b 70
    0x40e9202d01c0b4464540000090312004078030080e10000000541147c0d100c1040e00329a110100035510700e00c05640c0f07031600080020703100003503032400ca9070442c644a01e015100034041080302d01540300b020900c001c0041c4250702c80307000a101010507004000050b15804200c000a000d88409084a90b103100b0500050150350358500840d25008054030941d003804c5090b141020b4581d11009502c031a5000700d003680c5503801c2e0014281c0d0310036403140c80349404046001c0e101600b1503c0007070340c12501c00c1052084000d6500e1680c000c01c070850203030074400000d618400000b426a4050000c16000980707241301000b480b0459012000000100030076180c1c243d051680082903200000342603804204103014500505000391b040b038503100f008100c240140b800200c5002d65a52090441e04240c0c100d4119a04520300d00c1d00c41d01c000e4989110b85800107910705030802c40b4400311580d401c1026144c038140040090f410341300b0500344a0240e0804640003e00d00140c3c0201d5980e030040f42000b80520f04164469 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 784055305 1250 784054055 784054067
    0x10606110705040245060a09030212030405120f16030b0708071b120f1d09060a18061a0a02030306090c04080106030b040507060c02010206190f0c0509030c010f 70
    0x260307209540060315000b10802c024203001740c00c0c00301c2e08a00c410b52007a400c8906000140f402c2c21840800c5200d130300d00300d0403e00c04280b00e4540031600140c2102d600f40b0041c50145015022202050b00f124182500d90000511079881d0051140003a03001c6c00c8070121040e0244203a4042ca038964480a070740701e1440d1211110080000c0818041100301d40000301601d0003a200410500541444200b11001c0703807814a5848a0305641c40d80490341d101c8041d49110b200c2c034042c5d164800f004040d0078002d2411028001d030300c030000d04596441403039244080f9a902988000e48507403400190f003c613506150a005410440c3c591500c51104a8200000040950000200d030380080e0240c03903610316681d0f16925050f850003280c100040d194248400002031008480344140642e004205450340300d50f441906940040c0c1c14100240980c202c0000105040c00392040d0001000c1c1d003c00c08201c000d03081d1803607400ca8648001c1100855008a5580d5050a0411852000d401e080c2040c00c00011658005001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 784056555 1250 784055305 784055309
    0x18091005060d0f0912030f050609060f01080915090d080601020307110d1407060e190e040f060213060f03050f0603030f0706180804030b1605120402121006080106061107 74
    0x2c031600d0320000c5410b2001540980e40403a08200500e03002003d0b40d1000300503003116041604a103003080042540742c40c066120394041e943c0200310421040310031005450f1400010314030350a43c00b8101418204100c4c2810721482220014007a00d417138405110003400c0d08001401460441d0f00074440c000000310110080103040c20111843d011703000c0149040300381da440101d600c2d422402104000911240c1020039207450030000c4802d1022140e0b14003250030807510f241b01e0403403083d008201003801310342c2810300043d5650249002500d4881d460880c0d0308112000e5101c000080c0c1c1080303620034403c3d4107200e11504080079035005069400c00c0d80009680740205c0d281c0906602c000544001004810361120b601011003410720301d0038412509005100b074100e4842510b00885580000e0400b103c010340f40079011449495450400384062000c08150b00002d004070382054540100428203002040100c11040710703801301140250420403000c0c00c0d501d43e070380b2000c10b1100b24407020f10855000300d45801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784057805 1250 784056555 784056577
    0x10f12020f090a060f0c0f0f1406151804080901090e040803160c12080a0e120309010c090803040306050c070807060f0608010c050d02070503090d030c050c0a0e180c061809100506 78
    0x4187d4840c107241e01d001c00c2c2040014604400610207042402d004201144102091048400100460014461036a1494011200070000c00c40020001030300e01001e014092030614003400d4168942021480740031065606440c1e00001001300b0550326000c4502c4801410030740b41610a461907a91402c5201d0507a41c5a030080c0a02140060800c0229074401d07003200c8007010441700f41e0000c2c2c050041080e8001e032800f074065401d14040c0d80c0035a00410740a01202c404c0c10081d4138291950300d83d03c1c020a0080c0901040e0039080180c0700103c0d2a42001e0312102d0b0045900242d030800000c0ba00d808c40b10194441c150503410014004017081d0000b00381d543c80034000c0f80c00b50f9194040c5ca85242184141d03040c65034005c05141480c01072541c00059240c04602c50000c441000300b14008000e503101892046c0c4069003000b90000302d6030029045004000c0c1c0c0c042044420740f201a43c006070054100d4086c03185245032400e240c60640c903142a071a50403a80d40c030090398659042c000868810300c60805450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 784059055 1250 784057805 784057823
    0x30c080c011e2003042301171b070b04061d0601060504090504050c0d1401060e1009090c0305070b07110604060c0b04170a0302030708150a05010f12020f090a060f0c 72
    0x10f00503141c2180b003c3c10390a0703901c2c142c0381e0700c03516a00d0015900240b010800f000d06100f00c00c2250550082c0441c405019400000258503561030100914100c0c02a45000303400c1c9043c4000390004005001d0346010b60b00c100c1003c180360055505441d442c2d100d620362000c055100000400c4640c0d00642203c043ea01e000c50080f038159200d0401300d103031103508060b0701d4210b074002c40418140441b0024000c0c500c80004002e00036a603a440710300500c1e20040e82c540244a4040c2c00402c000c03440c03980000c112511440d040400346a072502c40074100314450348000d03a518800a948003c10015246003e814242242c0ca541001e0400c28000c24503000d00200414150b1142c0202e0140118800300447c501c0000030000e81d00d030b24051000340690815110308010845980100c2d07108450305e800300010b8100501104a01440c0c44011500034048520400a000040d20a03d400848500041c04903410002000e696407140f00140944910b203a40042c0130024080b2500000c0b5900544840c0880c2c0c02c09042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 784060305 1250 784059055 784059077
    0x314070f0302090d05011b02070e012c0a06080d02010501260f030d0219030b15030703060f0308130602060f0c030601171305010506030a03120c18030c080c011e 70
    0x1c0d0001c0c41039580c010b600112441601d810004150010310095582d411000583c22400d441660b40c0e03000c03170181d4440e148107600140b050850200d4120064904a504030185500718460b12000080030307140500520f4503914107000303111b8200410440660148004c00c519171401c620f003030509240540c3c5070501d000d901d07901050f100f006c0292400003201401130fa03554240001c826002540300c03c0980400c80b114407001078646000e481a206108070240a01c601049203139494070441e030008282c80c090595900e00400e494480035203800140d07224040c110341e14969030303007660151604d640c4482c0441d032181c0104108022a4000d10b50805850400d40380c4a448030300060b110340400030000518032011500300566031500c80051801607010700020801910f41006154884c0b915050140129080300000301402b4420384c480d100081252903e004040f040c01d000c41c10010380b59000b40d40c0d081c00040c090003006018400401020006d0804c0c40c1c0c3d001c0350162980e9181b0500a40000b400030400f45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 784061555 1250 784060305 784060307
    0xc051005090f1f0e1c0201050d09080c011d10060f15050d140609250c050a0506010312020d030911040b1305010803070309090e0316170a050a02010c0314070f 69
    0x6020351080e43c0751111612128840e1004000346821060702d0300c43c00038142c40d1040d0b4403800204092450701a550382c2d141c20001c0550304040c10f440d0380119200d182c10040610401c5003032085803c3e04140036280510074254500040c9442c0905001002007480d2020810070354080c900154201d6151451501c1c0301d501b00c0d030058032035026500705c10a045050012144039005d030b03024038070b02c42e600440300e12900c0d0b20b0340c007109450a90002c140b404a1040130b0780080d0103e00511840300d080307100300112900032080f960b400e400c0c0903081e801120b14054081e40e00111a4050040d40031100303861804106050040c0c450201c00c0741c80c04401d41c00349541e40c9030038030380e0f07240c20034201072540c0c1303120080c40749503520948199242d0014405600040600c038000c5400d851a01851625130509001142041841c240c440070b803090041d02182d030010001d404901c5605540050107a44800351510b64035115110b40107820340f90400a51001c0620b800c1040d590203581c1c1c4600d54200c4403601c1e00d90594000800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 784062805 1250 784061555 784061569
    0xa0e0316031a06010c032001140105031e120d0f0908030601170f2d07091403030306130507050c0f03040609061701030602030709080a08040311090f0a0b0d020d0f0c051005090f 77
    0x807100d061f40d42003c401c006441e5121207030f581214806e6085800382e01003845004510f02031440003e00c42d4000e0f0f011b811a1070500d43c054660300c041c008001408410700e4010b2000c0310300c0140116010007000c02009407a60300b08095804c2d42d4442c8204003920300c1c065480084102c4018001014400300c1c03010b000200134807490904518040f058250340c2400c110b40040c0c041c2000344100b5446850720340701340e0510700b00801601e014220142803e203001140d903101d1400750800401071010484288624042c00f5020041560281c1c20100655511404d00c48002c11003c0706412020900040030f2600319440d0034006020704480c0c100600580360340300d036041100d02041c15849100b644c8208410342041c411801c0080041320b201e450304c0300418251806002d4000c1d000c403020500013000030001072401019421018085200924052200085a0004406800b0152706842a4401902c00300401c204490340301d01500007240c00350034040b041280141b01c0c1c070400c60050300412125000040d1034555030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 784064055 1250 784062805 784062857
    0x1c09030506090717010b1c02191409010501030614010c03091e080f07030c1223010902030606060913112814040605030a020a0e0316031a06010c03 64
    0x14080e180396050000040750b803500300e03019107551081d086080f1241a0014415540060b00240012680c2c0c42c7c00840300c140d0184400050381c108855242050b924501280400b01038884a005c00610001c0c0c80280500da4505030411810b06140282c18862400104525010b0f90700928004400405a1500f200c8200c0181e201d00b076603844c2c03c1e207090031651182100c80e0030b40ea03000c01169a021085000196505510321028004101c150814461106421119121036000d60070704a90001d010503910600c1c000e80745140c4051755101c5150046140621005030498411110103003405040000a218201c071164220341d10350381c030241d00074002090780c00d1300c0315120030303800440004807001c14410000c100c982c20000005d841c15000300320720701041c00f9541660f201d596441d0541c0d42d16071079540290f01084180d0140001c0210152459404028011200f02c00945143c0d03c20300e585090007890007e00d80c40501185100c040001c03d99102d00d05588458040c60070020140207480d00f001c240d1440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 784065305 1250 784064055 784064063
    0xc020d0c2919050a0603031e020f03030a0e19081c290a061403010e090102310e01140f1305041208090109032c030604050d03060b0304051c0903 63
    0x1001c00c0080d00c0c42207110701401d50300c039508203002d141e45401800007252001d0000402150083d0003600d4109a2120a0003004101d401201c04400038402407a01c0c503001201d42c842c03410b4451030a20100c40f414030030883c071240590f03c1c01c03044002640d14003550b4050352201c102800703103e4440c040380c4042504492103003c84403008004e401c40c54007104500d1038001200c2030080c1d281e513000150340ca2049071246800d40000c41094103590034000902c040b2800503080385103645d024420b03074020901b111000082d4000c40036100e50707818010700d00039600749415070100900e8050b5800400000301d103406008a5007404481461220410000203000d020781c4000d14038821745000d01f0002003110a2280c480041542c0c2c942e0300190740c0c0d50f000142660518100200001c1d07150b0401001250705040410950107040c0040e00d21454040200c0e02d4410210f80548080d4032206020117100d4043c4511400703403100245007851454140c4407a9520b41c1c80312003140003070401d90121408103200d000c0400282d644 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 784066555 1250 784065305 784065383
    0x5270a0218090d0c0302100f090506070906090909020f04050601021603060501090515030a020d0215070c050f06070f1b0302040f0914071505071a1305010c020d0c 71
    0x814035428500035045030229040e1107a030004450460049400c1c13909a80c4c075600401c42c01003c010300401411200f0781d80c0c2c600d82d8440490400041c0d044c06021711440842e9100f00f100351a00200418019a43d84040d0601d403400c540c0d8030150300ca070404440c52880580c4d02103020f8941d100100d04d0000c080171030601c0a164048040200300f07854100504807110810107014648821185600041c1c40c018140d9240d0f01004051005003840017100d12914001007001c2403440d00c20090340215404003000b203464040804061000b0310b00030802c1740b6003d0381910428100401c6035070b20105101c2e842c070050700181140c00034080021080d20803201459002d0b209204085040d5001c202500440e07108807504c4001c221030007501c150010b0b56900310b500141e8400c443c0300c66100190f1f06030b40050b909903040d400c80640d409510030003920481c0214100030089440f41d010b82405802c40340d113400a1800c642200d00c068100c9a40201b1000c15560014003500d98142c1d000c9032060500130f101840600b01ea1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 784067805 1250 784066555 784066579
    0x80c2701081b040522031713061407080c0c01090c180f0e070621061221020601090c11010f050a20031602030c070b0a09080105270a02 59
    0x2601055040040e555103885107120b54903482040161101262200c4046400556030403151165402440c3e8041c00303414003030805d41501c47e0101c0403050460700301400006003807800e01042454828040041e8240d07100c0c1c0d48504202c00000c1178400050121040c0007804680c03009100c4007980f003001c84503844001455565920402c0e4508084001241d140e9a4a00080c130014041240500c204603aa11400f0385040c0c2c2c01d01c102560741d20901c242c1202500240320301c03001007420512500001c0d100840c0c041c2303100201c51030160034114500c0c5228a6042ca00740c50110026000120541500c8020601040b044040c8404a580341c5920b2200305080d030030030100e00516541e5038001800741030345030703814400500715110742d41d0039229103d40071004034400c01c00141c5c2e240041e40d2625403c0d2076071054910f800c0b00c41120b2481c008850304031a81c00e10300001d0b075208045e0445403610080141000a101c240b030042c0050b5080440400c111440c0300b00025502d50a800c20300406450590041c80288209 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 784069055 1250 784067805 784067819
    0x60c080706091b031a0702010c120515040f14090d300510080705030708150406060305030c01022710080c22050450010305060609070306080c2701 64
    0x80c007000503c050305c0410004507080318818010300d0b820b541d050f1200c42c02108010100402464020110f10100b25101e0500c100ca65845c05192000d058003e404241c02c1540d81c1d00c2000e9000280403821140e0102060742c042c580c01480202d600380b5903003403802c1701002d403001c1440306508611074014030910f0601000505207100071030380c0c10b641c1004101d880342d0352908141950740400c1e003e04c0b41a94003030300e8000c5412041001580d4807911490000c40d00f0f40c1d50b42c3d101c5180d13400c0500c880c80e07540d4002c15880f90104000300d5100040a40071500240340c0d1080010460181d0203080340c030204440b80d0002110140b00c2012a240e0a2041ca2281c5101000306140813107200d20f40520707441039050900300d0b211481103052140d50307000b0045101d052000754444058140d01040340c010040c3e0080e002c003d416610f8004154025401400548050702e0100100301d00344030700900358818903240c41010b0026030300016140000c4c000640d1252060b040c0162440a0034810328843c00750b030011200045488 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 784070305 1250 784069055 784069073
    0x120c0a05120718080607021b060c031b190f080309010912210c02070b031506160317040c180b04050702030406110607050307030b060c011d07060c080706091b03 70
    0x140c40c08010b1a83c1500ca1a8003512001309458800c0164000c1703011410541c031f00c212810005400600c03091420748070300e0016040d900030300749001c0c08151075070080403844800e110100b15280d100382401640c0d409aa40c5000d103500620010301485804000074580032025484421266007103100100d080d4100701c1f000b00b03020340926003249200d00050131181c100d03580e401501c0c072030a4580c01900700b06081c64805840fa4000504000807801050340300700300c981f00e010007001c8000d10003000f001280030600707020380208000c401c3c039070b04841f00c00d00708000308180010913010b4961900c5840d03105440c2c8003a1074040c042103400d640d40703c0d00d4001440070703107500040200204c41c81d913103c5004414040d805546c541c841112030401140c41000040c030303264880c0e131012400d048000c08541c1400103400889085400d24000000d07200e40b054041081d000c802c0210718028801c07403a05d2600280c0b550348070038080c09118002422151111102c0c820400c1c41e0313610311100d150001e5002c0b10f0503501d06140d00d41d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 784071555 1250 784070305 784070327
    0x90108011a0108090c0904020a0b0a0302030628051e03030c070311030303040f020f06250c0b0f0403060e03120708150a050f0108100909050114010b120c0a051207 71
    0x32000111100107841d4002e0401c28400d840d61000740034844415000d00c04907400c0141708990060b014000803c56601d684040d0196686640d80141c4910304402440200d00082580c1003a1455055280d000b060f0341034034550030394000352503001e0300c081242501c1d070340ea50042041650601011034100d040010026210040768000c020b40c05070001805c05051700c81c0f1065502a0000000c18111405030520b92425804484050681890980113240f5040c45921101d0a02c10880c1c3c030240d42814070203040001d401400c42d0035401894203d402c40b0700c1009220b68440203050329240c0084910000d420b00035108a00d48800800915240000004080c4002110400d0610010040c0e0107000d041000d01201560800341c00000760f10104401510f1000f0300410540c80c0c1e03890090003007001c103000e000f00350b8801d104d480007003407203030760009404049072050b041000c26184c180300b0f01ca6041c00101131f140e0800e00030421169141c21500e0f0031903591107842d0001101c0c40280003880001c581c85101084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 784072805 1250 784071555 784071581
    0x60815130b041805010e0c061215030309101d0301062306090d03210b0109031119120b0f0601050703121404080d0b04050103050c01030b03010902101106090f0a080703030b09010801 79
    0x141107c00302003040c03034010401082e54014001c000203110f454040c0c1250708421008080b2410704c580c1c4000507611000d0852543c000941c0061000d06280b000c40000c400d00c44c0440003801b80030304055030800304100e6150010001e01c810304c003d401070340303a80c401c58504179006004601440c1c0d0300d0078042c0800c90f14042e0315020b05011030000c0f0010341240706503002c81c0d2050390303020740c154619160003901040942d4030300c2d030110030258400e80b01444200316500401091628502041c09400d044030000d41c01061b00041d00380354401c00c507040c0c0c0e01800f1503004941c141840c42d185400d131000c10004080150f00b4440440c0e0500c1803205200100e005401c4c50180244103110305240d520500060300c0c403e1000401d6a8042544600698026003010100c03040241c0009206407182e00001c42c84014986401c010483c440c00715401100d041c04500d510440d440000d140001d21903000c143e8981240c44058102070021480104141c030135001100380402c002c004103001d5031500e0240307000703080100c1c1c042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 784074055 1250 784072805 784072813
    0x9032d0a1707020a17030402120d0e010f03052a1c0f0f02070b06040b03010e06130201030b030a151d030703020706021c080a0b06090316060815130b041805010e 70
    0x1202d2500c0010345004050b4480790388000048040081380c1c03503400141c01280c0c00024000007074600c0038100190104406242c6d00c07410180a8071001400200741d08220008141c14142007110004843d071606600351840324001d549018480002c44450040e0804021520b04501030f0940604a03038201198100100808215001854800508070300c2128070042a80070107100203030301841c1030345c003441c11800c0280021500d035407941c050500300a0201c0d0800c40c80c3c00c411101000f5035071306204000320030310300317400a12510009885000c0c100075048400c402c125118498400c282d004070600f070b10880580b10480e510b81c1150315000e5181e14160042c2c400600c50008041c1c03251010041c40d8030281d02545604e626501c41d01218009040000c0010f40c005808108120f07058408001118460100b140c0140d515402d201c401444400058a24000c080c0f00350420f1744141c4d28004500c1d00002590310008541c2c180740003090281c40400d14a002440d202441e0405105064115919100381d1320192 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 784075305 1250 784074055 784074061
    0x8030117070b0703200c03150411030c030703120e09070c060c0503010f210b01060c11150316020a02150a030510080c15071e11030609032d0a17 63
    0x16140c0b600070100080d000400580514400708040c040b40c0b000c0703070415002e070340c11202d841c008207180c10020590344910403054002c00081c001210a800c10108044020700b05c10800f0345c00080e41c503030b01d03400050262105500400c443c076008507040c806a00300980024211701d8a000041c14040c290703102507810034100381056108600c51012a4143c0e0229480036080d54107140c0101d030300c080e11f4688402c4016401e502c06010902001c00d0301d00038403090f990481c004e0360618210501041c1003000714080d54a80005c00085030005060301e900124000308842a00c04540c1304a00d400200100607401401d103010203445503004100501800c20142c50512450304c90741c0c8c440c010301159105540b06a00300c1d44190301a0724195419041c42d041e00d031031080c02c0503405c0e140c2c0c3c0c400c0d441c0403004085082c00ea1780ba450811446500c82030f42480c00701d01501c205d150407900144c40744102210000991042c222080018070f00ea000e19500209058040b61210030881c405031a41e07581480e108454881e107000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 784076555 1250 784075305 784075319
    0x9031501050a061101020c0f0319050a0c030305090309090c0d1d061b04170a02090601030b0f15040e09010c0207050a12080a0c02061305270f040602070803011707 71
    0x4550304955000d80100122403400d401218034100000c60303403030155020400440c0300e03a4204642e43e0241400e20164ad031321002036541c40420340e081c250b00c0c41841424010042500d8008003008003c0380c1500700400c2699603400c04504500c0360b1000d05078847c1081e8140b240308402c10000d02203800070301030100011180e1074500703c40d14500900550243d4031000001e4592505150200c0c1144005142c441c10a92176241460b41d01c0c81444038042c80703034030441c002425490000c16060700b015003820100706106200000c00c00e0503800b0782c1d0480c001c060b162804c034103945030f240c200c500500f0001d2a0356502d0503c0a020360292640840700030041c81008004901c518011001c442150344840c0d5114911016607030750b05864000b4580308007440000041d03900940c441400030f2490703490540d2040d0005060070100090130b0310030110111440b440c4400285500c0d0312241e283c0d041410520440d025694600e011400b1384521100142488030200c00040c80310a0304107130b0070131400020103031040c0c0703500d40355 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 784077805 1250 784076555 784076593
    0x2061b1308030d05070306120f2d05030a021e03030a0b010e22060602010c1205130206030718060e0312031b040b040f0618150e0306011401020c0303131a12010b0903 72
    0x1e00720b0301d040342e00c0200064002031902d40142c81d1f10341c02407800e48020a080c43e00170903102d0552f655080021074801203079044c40021080700910900c21007001404080ca5580e00004100d0b9181c295513600501c1e050b070182d1010700903d00b004002942c4c482c1d50f12140e29400b44125500c1c0c2c08982840790100300381d8018011070110411540d624045440105100800342c00701502440442561184010240c0c031404021882110a078071405400d2500d1440c3d103540c1c007116800402001300d0604034650507900440d9500307034000c44020340c9842e030321416815001081d50b659000d01c0040b00280c0007031001d8401001c0d000b19107518a034410300640d16801501c0300e1158100066030000349440500070000d1101c0b106e843c0e21014640880100300b00c4010030f1411800b81c004c40441c5514005a110640c0d0400c408a903140c0d05601031402c1040d000714008030801c041c0138001c01014900350030310800380c802c801d41d540400c0c040031010317803543d441c070b42054540d00440c0725601038001c442d222a00704402203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 784079055 1250 784077805 784077839
    0xf0f0810060b030c0d0f09030329030309010518040501080a0210080c030a0c030b04050702010e12040b040b0c102406110c0f0103020903010207060b090702061b1308030d05070306 78
    0x10a0b0b9881c2d0380d20400ca000d41c0d03a100d0442444920303900c0c1e010803c0d240c014170032580e14500c030341c80004800d9605c864600702181090a50a00441c1c04212000a0b46001c0103a5140c1d18080c00d0254841007603e08203c0d40410722404250024584400040d6081c400200c41030076500990f80500240e281041c2102c3e01030049074403080b402e20401c04200980c80307580c400c6003020441e150000740c14031070000080590b80d0607281100140c1d158400b213039080030107000d4500e19208110303206140520300801da62490003284174049503144d01180508202c001408101d49003185c0d20010007461003421080448400d6001c81d8442004092a000c6425030044821032907550705540141b240d851000c041044441c40e100c1800e04041e024055200503450900240140078422800480e000c7d40100601146560041107402107500032018061080702c0500c40141c0c00c2a0511080c1d50780e0100c204007030140c440c035481a00706200003d002030a10040342d10240c042c0e00156000d100742a0754281400c0059803d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 784080305 1250 784079055 784079069
    0x1207060206070c030509030303130b0a060513020c121b010b0904051024090920100315031202030a090f0f06050912010203070203041e24090f0f081006 66
    0x807502142c5118043c19003003601c148a80340c100e00e4001e56001080c00c5070010f0fa50a415800444984803c00c59101007217940501c0c54502000720525020028244441401d6035224040d400524200c5e140b1050244403001200403010550784c2c607500031019214480c5c52014801540f0b814045111458030110350b07405543c00100605443e41c4c5444440000c2c907603407020030b08649a003114080d101040034041c0008018200c40003034a41e2441c200f1402c00c00c0d044d920043e641241d13540c5030b40319540360306484003211451700e00040c03450724911044d50841b042d0340003d81802390703859010724116400002803c61446555440031100d0351402c501c1d002203c1405449014442d580b800d1140c1403245010b0030550360b00a02c0c08444207210004a400c991040d50141d0040c0c0001170b003440040c0ca906032039000c403520840001041c034074001d40c6100c054980c1c0580c00118500c1c060350420304e0300c5250031030040c0281c900c103040116900e00d40c2d0003214100b8030039032815024441114290352524171400b0200e8a503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 784081555 1250 784080305 784080313
    0x91a01031b050405040b18011b0210061d041502040306151e0b0d020c120f070b07110712020d0c0905151807030213080601060507020111030307170628030212070602 72
    0x7d800070b48101503c60450780340c80d99a111030440c0c526030000402c44507070380550040c3c130900f0340d0444810305840c883c1d081084101da04010317101c8128070811285600c140c01c000022114980d4450f5000a48102d50000d4142400c2c040c00009100c4072800c40c400326106040c0c107251032444d01041c5844100f0358820403120110500500d02400030580003000300000400035a4861459040e007201c0036040708015007400c1101064001c100058115503e8110031a41420080301c8040320701c050351041207008071006214070104030350441d00c3e0600c80b0490b19601c8018000340030784130000340c8000c20b01101c170034419140c0c25824140d14182170f40303121803400005e11101100c0da281d0301c2c03e40c082e5001d48108a000101000001400030090000e01d02070103680d5107190380c8041500005084031a102c49004080e04100107106e0f000d07810000080100340e544000f03902d00e517501c82c00200c044201c049040b001d03030b06e466071a040c3d003a000f0310070740256882181d4040d004803a580309141da41405005641c05640 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 784082805 1250 784081555 784081561
    0x9080301260c0112140901051e220c0504231501021902030a21020c0406081005100902300103020a0b0f19210b13091a01031b050405040b 60
    0x100c111503214080e0001c11005c6034181010b00741e20b002140480345e44d42c5d031341d6554080c4552001580715122700358031284003c101d203040028100120ba4403d142c81c075208200c09400070204401b81c0135a90003404020310070800c04001e41407903981010005407200040c81c0745000141aa600c002c00e0b4803081a06900601d03d008a102841e14500e1076184141e0740741c401d08941d8000103082e50341580710580345401503103000c100020b01034940b000d507c041c244680d060101c180039200d000640e80361a03520365880401c0580322040c20002503d030a0704101c504900024840c1005100303061701003000d1030303210305414113a60302d0350081407003400a0000a51140d1356103401c00a84043c0c001800d0090300303452400b4903b0205074086068808548061f0011a0108650b06000c0c01601145882c180400000744100810302c400212035074170031314024946070382e20080d5006001c065000891880c1c3c290311021580d503102d0500c10220b510700740818417003099207680403499060a000f8940140ea0084850807162 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 784084055 1250 784082805 784082807
    0x120c0c0b0604110913111b061312050a0e06040602030c3703050d0c030509061305070b0a050c070e041b03020109030b2e0503010e0304080705010f110109080301260c01 73
    0x2c2003040700380280300e03101c01b02180c20b00d415100800c00440c40c1c840b0b00201046800145051560040c040d03244034a95041c1c00300400c0782c0c9001010700160918109036030f48089503003690107503402e034000307501300001050204409800000805e4142c4010049030206145884050f104900355003146500300501c5080b12078000c6ca0981103202c4c2c9100b420304a00304911071100038115460080c074200040c2c1c481c03090103001c041c10311145400040c0c2c84424030f1500c06903110260750b03e24a114484035000c0000380c0081c2c8500c03c1040d14a003071544015030b000305035030301c00103540401c05580c241e0324010105211305402032800100021694107840300c8080c2451a1210309280303400800303038140e090700040174140301000c0c2c5111405000c64895101c8000e401d00090500711511500c0b4040f01d5401048180621980019440c0407179409191030f96026540b03040444403101140c40b40c402e40d609100070303d02000707030b04400395040e10940c1054417540718400314038040410295620b100c9030f4000700c4101e5429 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 784085305 1250 784084055 784084069
    0x607050115030804180902060910170406091e0507032301060f0611070e060103090c05090702010f05090a0b150612070906020c06030c2205060d0905100e071203120c0c0b06041109 78
    0x105402d41800c1c1340c0c500140342f00d01154403040b1011100d266565201c90f0821036600380c0c4a0581094030800c1c0d0201e21240e44140d80c550040c000506410044001c800f91101d00104440346194108002d002940d03942510742d0a15999008140215a04803540c015503900042c030f0b2021030708202541c0c0d207541c840744011340081c0032801d020f880c810210000070540c0d031564098035008181c0e035400040e00c00c0c8032502010485da00603000c04201d03040412104049814900d0041c3c0010780c4000c0c880c1c0c0c0002440010f44184100a05a1a241020010040000c3d08964014111a555002e6808034811b83c010043d4501c0f00f201d0301a081a410311040c1c81202c00d1000d03403e0b032082882a06450541c5843c0003800c96040b500301c440c030007a1035200000c00c10006003c820104051003a0070300a82d55144103c50f01c0b0960341c000c1c0d8110301140703101082414440e03c59818101447e010801250b00760107002095180300c82c40c143d800e01d07801c0d0089074403030505100e0640d003038001d800154104800320081045c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 784086555 1250 784085305 784085329
    0x60b2e12060b0f09030607111513050f06012c1f0b0f0d1406150c0a020405070804021f051905040503030f1e0301050f06070501150308041809020609 65
    0x2016038607000454021021002010071000c400341c02ea840d442510100342c03402e10010708500401181c4160a244a0300010341100d01da2004404102c1c2955941505098114800c001400c14850a4419500ca44010807054142d41c40f01d0300140b03407081c04401c1314105601d800c100c0110308500a0000d050900d03103880c00356410146ca50307000a950760f40c40c14541603030010000300700038810002d0a00f07100003043c481c00c030091707490003441031040c83c000700012091180301c00141e4210303400050401103081c0904c0320800c2c060f4010000c00541c00c00850017400d08004503005c0f8028042c0c2690401d60300d0291a10040b51452955000e28041c442d00400500c1541c0c42e00b00400c0c41402d12003c5082c0d038081c005480384c1c01c1d20400b41903c600f02d40c442c0022540044a00150710a0100018040c944a40d1505502140295201640d641c0c50740f80441c014203010b0002404c00240040210800011000600c00c9660903602954032071100610f0108075409040000c1d881482081441100d04103407666142c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 784087805 1250 784086555 784086587
    0x60c0c072304060f05030106080c0d080a0912080910052a0109150e010612080a0503060607020303070b070f0f232b110a0e040b0319060b2e 61
    0x74003100c55000c10309490250700300f4203080e4030300e01c4184500e040900c2413800910f4180300624440002d030010803030038030024101034111840010b400020600520105004241180c1601100e035420f003040000c58022548807445002c8000ba03110b416803207013081e200c0c6c1c13a0b0740300e07045882046421101144030591400d03000b06035403500446004105510f00001c0140091540807605000c0e0080c0f8508403802600032549400500c0f07002404036030030006407088400d59081541c0c0d039884580004d4181c0c00f602900035814800041d007a0200110a81c001c3d01a0900752543c4080101d144400c4d03034802504072050380010455000c210344039906014242c450145101c5c124030303145480c211041654006820360386000000b1030b10600c0320246102d00c50354007410f08000b60600d4280e01c00100725405103006035100c0c544071b21468003140d600744004541c000503200b040790030907000c0c9080006442c44091262040503003000c1c004580456481ca1841d444000140f0082d460402c081602e06140c02910f801c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 784089055 1250 784087805 784087859
    0x3050c1615060f170703080a030b040216110108010801020a140702040b10020d0224040213110d061403010504020f0d030212280e1005181c05060c0c07 66
    0x81d4103014500ca80c5019062041248000605142c0200300d00440a00b940c84180d00192080020030141016180303410780344c0c0307808110320b48c440001070040d000d41c0030030150b540c091640c0281045a850b08a80116400307880790348603603a880207400c0c02c1f07004a10818012540c3c0c00c00b05903000d5141402800d486100800006030303010103001142a2400c042503a5000d40c0c0b041c203400807456010001c046d20724088550100103540d1420500c450000040d1000b03010307040070107503034a070b07101d05400105604611080d241d031241c016130081400b50100e40301c0c6404400c2c0c80b03450060ba6041c10f008240c422500900b45a1401d80f2035070910040b645034483c04d904600601241c1c40b021a0410700400e00408000e440103a5246111291201111551060001d008880202003410f8891040d245c000e050380d4145161101401005411940b4050303e016511030088800384c6941101d0a688402e9140501c049a1840d51600e10b581072520410462032032030ba110341c20800180394055418004896009580303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 784090305 1250 784089055 784089083
    0x60109020918010e010513022a0a050d020102131e06181d040c05010e09070815091f08031806090f12010504030e0f010c0803071b060c0f03050c16 64
    0x80d20b030444003030700480c0401101c000100450700c0e02c03c21041441140c080110310f040030325420480718000d2480016219803208205420079007003031081c3e01c1107130b8000f4191440203d004900a001b544004149540080204070124119107a8006901c20450340d4405404040c103240c03044d6050b03920420181c0c1c040710f16000100e06070382d0b11020141e01121960001e042824585803007610382031070350801410801c58100c0b40000307070380d50501e8a822100a023021225a200e101072680314102c05075085805c2816002884400c8140712803050110681e041d41c01e0b103441d100c0041648034815244c071044443d0401c800140140b030030700c0c0200785040004000c0841b00c00307120082802d20018401d0009182d54035010001410b4020300b02001c403040881e2400360800d0441c001a00e103058000c3e01420380c9102000051001c0d000e032030300709807100310300e8006070ba0b81d0468a0240046c28080c110240040d21900a507010240240541c42c05503d140440320306001896441002c21108482c0548aa00702a124 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 784091555 1250 784090305 784090339
    0x21510030218070905100c031d1c060606030c0c1502090a060815030304060c0f170304050d090e0c09090406150b0405010908030a1e090801050c04081b01020601090209 73
    0xc2c00440d00703052414000d1440d11070400350000c2015400280a0044200d6245000b07034840a2880d104e41d040c103110000310b2280c0c6000088692091109801407010407207000445e10728082030030113600c00c000a203d101d480f50011000d58810021b40c0000c01c0c3c00454800000d40c00200c81441d00c65066001810600e5020000302ca08407651b10501c04600307400e00703100c444502c14030030454000003900114981441e00400078030b1a00c0c0c5c03220141c0556808035200b020090003001502c804440840503e80368102401c285071140a01c090801c08100220b07000070b5441c0c20407821a2040c03405074207980c2000320b110103010350240010022551141e4a8020303500800d108561400078000b101c0d22642c584d8180000500b801000740c100110741c0c1e01c240859088103500c003015042d19406501c3c81c56040710501c909076034803006900045055420902080200342c4a807000d00101e42d9002c040b61a50718444005061100d10b08015500680100707006000c056215001000c010314050b000d05d402d4070407190 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 784092805 1250 784091555 784091569
    0x906060902090f010e010e01050f040506030c0a020d020a02010c08070602090a08281509080d022d0903251a0403060605150405130207080307090e09010c0215100302 72
    0xe169595011569601500340740c0801d80c4088400e081c9803460070503660010308202d48a10200d4100000001d4010511110030159002860003070501074480c103146000d15880d4100c0b40703084c40140706004103c03400d50f10004e00039a034640c0684464511b600ca6440d480d01c00e0f4020101074820342d408000d0036805841e0000150000d1072030001a02d0043e0b012444d07041c041d054041c0d00b020306000b4460000200b104c2880390a2402c903510360000e00f0001c0c900d01030990b8000c6041c413040e55403000c1095600565200d005501052041e4502d42c0c24284d5032100d90100d01802500c01e07010303848800ca20080b8140210310100c40281280345c4507a042e134944240b0a2403001c1c0803522564980401c0400800143e402101c1c00381c00d045034200d940080000950405002c0c1e8440c3c28402c203020b44400f00c00c03a1050381200c00403a00260265540c1c90041c00142402803684281c2030800d0715540040c40401e010703c1401504002c43d03001c1c1090141e00c010341050300001400c038100701240c405001006a0382c02c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 784094055 1250 784092805 784092809
    0x5090d020628020111120a0f0b060304030306080610180b2412010f05030307030507020a050a08030c0c09132402041e06020c0604050613210b0a140c0d090606 69
    0x50000303041c8004007070b0080c02d50340e1030805141220024000c1d6013403a02d81e07885903039000700d44107400541c2034064480480a050380c42e40154001000209101c24551302d60064030a407044d88048400d1600c40001d07064014100c0e00c01ca004110024005110b182a01d4004881c40c07000100803034004101d01d46080c043c035500701c803000270020b40050703a035104440c0c00c1e20003401820548002030341c661400d00426100e10811400500700000050070008654810071040701510018010313a41c1c460b1960801076581e40314220f400100c0c4141c0c92103014500e0681030062040c0411869806c485405a9234035115030014800d00c070700d0034070381c40c4140500754a0b8809040181902089075480030035904440c0d10480c02034018000719041000c0c410701a44841c01100c1c111103050303919035505c0303040f100842c20000d0720b1f422045518000300400c001003050300d210903068a0013003000d9103250320365680f144110395450895110a04031303240029050001480a805020360809001c00e800344c9a40d12107080b16029 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 784095305 1250 784094055 784094107
    0x3030a0309050c0312070b370b040908090d020103060503060c031015020304060809010227100509030a0201051e0a09062601090209030a0f0c05010809070605090d0206 73
    0x769a06000c0c41420403030b001c4500b2007a40070300360b1000764041d05109486484000f40080c40f40001040b0581196640e54064284800303a20a00c005820903240c1e4030600401c001e1001d50401604000503d414420039031840c2c1d0060b076a5140140c010148006010725403010382c140b69594000042d44c1c3c805000191148000800081d0b5a190019102e503400b1a90b0300107400e0040d080800c90368858000080b5810b80d0756900305500d4a0707a403031000134003901c00c42c0c0070203441c000304014016078030b9041c6401c040501003c40d81201d42e646028812641d9010b40140503606911100b010005540210010b00254803102c8032003010790080c0020070400e5204400c40c0000a8500404102e0a41d218001182001c00a200c0000380d00c40c4c00280c2684034010700816410a134009103a801d540c0e01042181e181701e90003203100c1002c44440c10b04111501080c07042e14040350b42e010006015000c08560403060340c0c5e8545905017003040c6e8100f880090040328008a8100004001001010146950f1145240e800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 784096555 1250 784095305 784095311
    0x60b0301140907021203151c12110307021c060b0a0b07033c020c030f010615020705030d03020d110d09050f06091f06031a0a060e130f0501090203030a03 67
    0x204400707028042a00410110441d0400164107031405d034040202c81e040040554042c03580f00b40440050213620b150540000b02c12098802c0750100803030400700400352020340e121441c0c0018250280e6480c0e03c612800294401c0b44e80700c0c44c41d2001c00e40030f6000310b11809014001919026000810010400b50300400c1000c000801e00d0010194071965201311072140c84000300e070701e6481d04501c12003550400d05403651903e503003a400c1c0c2001c1c8200520a60400300504035090382444c0c2d03450b14000c110900920740f560100c51025007189000150400c1110806801880409000d40d8102d00a4019050220b020358a41544442d9030310100d01030140c1000b4101c5c0064100703c1450700a207048011050720010790045405c1041402001c40d10010500820000d13080e4814033082820042039aa08010820f0300c003001c501c7c0c21401d45e4a900c0d4440c0c0c4001c0310801999131609044509071100300d41ea03100b107c0c0040a0040000d084003212208184260b00110341c0c50782a50000f030540d0000400040000d035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 784097805 1250 784096555 784096589
    0xf0111130506070b0103080307021005191b051b1212091009020f01140f0a0c020307090603080a050c01090b01140f0f03150601050706050903030f01140d1104060b0301 73
    0xc4600d5034040103280440c1d44a252005a951300d012550f41480050300004c404400940c4c0103000b4084c8107400c0b14117036010071040c6405500d160f89141181b40d601e41551410b0030300407642c1e0000510085e8890303141c039204c2c205095600032402222425081041d41d00440000700c44110014000d444e4003403a9035545c420070710702403c1252a0000c500c08004201342000158800342e1500c80c049100d0410138a4110a08001d00300c11010310310803010720a942e0940044c0e011031392540400381420540c42141510603040d6900041d1041d02e1850002411800c410041240198026002425039841d110000f2031007144c1c0342c441c440711030400d0f4803651044007000458001c520b030092052180f048211120901c3c4e2580e040882d6950034140d03043c0c55102c400c1c00c040b8859a0242003a154050351224007030042d860040e10454803500705486400c1c8254882c000407074000d006141e0048403181c0604852401d00e40e40c1c03500c2d2914402038540c4c54203d607a1ba01d011908401c280c009501900e241207680c0c200343c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 784099055 1250 784097805 784097827
    0xc14060f07031812020c0d060603050d050c2d0d03050106030c0f0c0206031317040302040b1f0c080d2a0e091305011107120801081903110f0111 63
    0x10038000c00034000c040c500704210780380d1180f120300d031200e03035401c100080c107802031816003039240800b605442d56100d0501c0307405100f000119005441540e20642c280d60041052050070381e0240902045202a034110740182000d140644400031070301c41c04850007140d03500e0034104841c10302c0040c0c40f0850020f5210700045c0312042e01401035440c0d1000c07030316005c04000c2c5110070081910001c844001d1143d24000085040b01007842428080603411450b0401504184142c1d02102d51003840708a0156003400f603102e040c0c1c03038102d28580c3c00d24035101c003181c90401c80a03812660703d00c882c0700803568403130305001e00d503541c40c80b9100c0c250040700c04a541404c250301c08070703035601c403a030382c2036604070800c48113081d0f01e02c41c4e0321400300c155004040c07200030041c055107600e0b0080c00f502d40c40c258030f20804804914a07040c050403014600e515629a15030742c3c441e98940310065201d035017404244809600041d40741000910942080c4035044940f4250789101c3d0185034414255118142031100c0182c002c20010020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 784100305 1250 784099055 784099081
    0xd020714010c020303010b07110310140708060a030f06092d1407030c0b030703060503011a0906040e0d0e0301090219031703101a0c1e0c0102030301120605070c1406 72
    0x2282d61400254215807404070b096038a48501c010040100e8030031310040403983c4080068410a40e184d60302800b0039200452500c056920444149001940d001e000c83c109052014000c1d0a0701c0e000045143d04603075035160040030b031201910172034400202c8031207401c40b03810030151600d2507244d9020740040100c10f8240f0780c41c40c51142c6040754040d0044001040010728204140e0100c558000600e40c4940d40d10ba025001400e8940c00540c065003816224403091003c40110341031000122112481501c1d84014002212078803025071201d54803194a141503240148141a28400020000308a6a500b41d010503481400c08101c10032045d00c0d400d060040000100702c5a0007201d4981d9141d0035841c006002d01c40034030712841400082001084040c0ca009a42c4044600329410801210b452460348800402c841d90310304a5005940142071300d5400562020080340e04950000c0403081d99000d0700d44032000200700281500b010b2244c4000381d800060280300c8201042041d55015060528040e0246140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 784101555 1250 784100305 784100321
    0x30c091f0e040b0901060c14030c03040501090902070b0f0c16060203070311071124182715060705072403060506071202031c09051b150f0d02071401 65
    0x803460814100f00625201d0202d26411554140b030036000d801039905216060a800788030180083c0400158185580000000ac00c01c940b001c0e42c5000011f40c0d91407000049000e080e038003d11803106140412000c3d00d072817882c150069414140145070004901d80790035400c0c0b40f04030440341d140d0040204494642c00d031203140901410000e0091410030550b845c195129900c494081c8102010509401905041e140c030601140c00f5500f01c075a9094113281c0210300c0b9180f03480b428444c1085000b04003c01d1800d000506d41e60000f40d40104e02504e07041c3d8a01e1201c06010486500003c0500481012070000c0241900600c0111610601d00d01d54101c004a400012032100043c141091400c04c030b207440b04d5084909550b000354034030310911941d020072800d61084408882c041035030039003500d00d0680c2d80d900c0203108901c91012121074001003191080c556140d040b4442c0c1c0501080001140260008000c0800d40801c038110ba1401e50701d41038000c1242c100c40707002e444107512500625040d60f024030030008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 784102805 1250 784101555 784101559
    0xa1211070f0e0f100918060f0506030d020319050304051002030c040303031505090103060c0c2306010e13020d110a03030905041d1b01030b0303042c090d0302030c091f0e 74
    0x403403030b01040080d8204d5491149007003040e522103802c07001d1201d488a4030a400d0b0300540c1400084a56405040546415a0214401e000300540c1d03403041030001040346d0300741c410480300c00c0550201c0c403400d480310b8200400030703500c81c09003400041c00740714188002c5207c0e4030087c011546031815400c000b000c23500324244200800f1100c0c007061180e5036580000504407544810045190915000101d5030101c201e8030040c001100b90216100106007005120b4903150040b04591150303980c3c064440c0912000c0d6035006031007208902490140c1481402e500c105400b0751000300321401c50034085001e03580300d54020340006050440c184424030302401501e800e44000400a840110741c1b9840b04e803104c100758441c0615440e40c030b02103012070340a6080b10103104401019642c4840d60b80c0c802d440c41c0d105002e40400451203c0140035041075040d40d0041c0030306030031001070450500581c0150000e50001d0800d44101c1400d12054100c0d0b5104444104040301c141c1c6402c1c1a0311402c50068060102d6866486c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 784104055 1250 784102805 784102831
    0x1e0e0f1201020a02070e1e0123031002090102100204030f0206090a15020307060c0c240605041d0705030a03080105060d020d02130302030c030318090c040308070605041e03020a1211070f0e 82
    0x144508801d0a1001d040d2040c0300c2040d91018161040c00b40c07142700348894160140900300031070000654035030141070300d01400c0e000c2d21410f01a102e5010100d200d503000040098441c881c103c8003504014000d0540d81c40003402c00c00c2c003640c170362001480907000e01d008580103a00006208007000741600030103841344450b007000c0740c9481942e40e4190b402c114040414400950069004c03e000d640703038000c840140341c00b50081240074890b0300312018541404844a42d00d105110000405050003d2194060f03a00b55449141d81e900380401c1100c2540503030780d440b0206800f4406c100c10003016100030074030400034079a10b40c0c0d628030754414107041001d42080c4d50b22941052003d540110428031900c0a150000c4959240300e681e00e1030298080d0141b40c02c041c1c84400701040c0d0a0410005503c10381c0039a0141100742c4510451940307140313424078400001001a040002c0c0d42c030000e282000301412030b8289003001c40c40d4910902d4500e18100c02540301030070318400030030100b01c480301c0030f4a00b5401850045079a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 784105305 1250 784104055 784104091
    0x31006062613080f0703080a060f180209040b1807120c050a1809090827010c08160b0c1803030f0717040905040f031e0e0f1201020a02070e 61
    0x159004600801c2c20414a10b0001030004011038a0200c8044c01c80b003045094441d407190a0040040c0300c1190285400e610b004001301e0150b0040071007104603201c1c0c0d50700d0305490036003020543c0a500950400c0d83c12588540300404030f691141400196980490004a8985020301b0000c4c4807500b040c0d80344100070300d0000d00c040c10582c031804950800e0078a08008052050312101c0d003e803041c0a51000860b1443c0003e51020006002c00801c0d02c8200705101150039046480b4503009c100c0031180c66800300d00d80e490403c00243c1044040c004ca44222044050045080c1e101d02411940840e03100701e855000150030740590081c035500d0300e24076005900440c10115000c82d8000544038041c80506004c1e40c003170380c2c030359242c0684007103070003600580e0f2003440300d0304040c680541906007491049010a040c0e5040c403071aa40d0362014100800150341d00c0c00002c2c21100288003541c1c82410a40d90020b0400c448868464400d000405001c403c40e801020007528180307900fa002c0380040d0803011004084120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 784106555 1250 784105305 784105367
    0x60c0304110f01090b1605100509100e030412061b050a0207090b06030a020309100606031506180311010203040e040f0606050d0305030f060109030f06060501121509020702030c03100606 81
    0x110300646040d440c1155881c0d1b20b0b011502c081c0715142d03200410034880c0c030002030140c14048c1c0115029031a80c03001c0300c2d15803e40611810584145d881c0c016038130b5100b03001c204100103144c0c401000c000c0c0248000215501188182072540c11011745090100d440040e20000c2d560b8100003840050404010401894010710300007a090b21018001e408095000300110305140800e02c075114201042200400c12140e6401005d03020309040d1a00781c0c2c0000c000b001c0011140e0254003040300340329581400c000c0d41c03802c0d03a5426200301c41c207082d07044c1148424000450120400301000c1e02590185003603620781000c9140290541d01990003060050a40c00e8182d00003d42207400d42c0c1d00000c21000e160b800c0e640702d000403034051034a1350000c0c086140b244031140601416034031a200b0346602303a13541504c04003a4003081080d40c0f182241c0702010340c50b8250070000c004142c2d000d0141d2600c0101601e41d105200b07000241b80046079a00c0604d4580e6440c400c00040b034001d1b5510080800c2e15105101503600014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 784107805 1250 784106555 784106567
    0x11a0a03050705060706061d0f01090b0d030c1707061b030204080a0f020316060507110303041d06062107030b03010b090a05040309030b011707050f0d12090305060c0304110f01 77
    0x4140c0780104d1011860f10200803542e0000e001130403640601d81c250003803c0c030f801d030101c3d241074030325000c801a030b2000800c44102900400a89600203010700c001440c060768100c4602d900a8801d5400020003081243d100c09644000e20045000b4500443d2075900301400511a1402c100c9030b130241481004100650000441c604042940107190034416801c04e0000c41d050070206407004400e11041000400e50540200182210038042c9070305070f040007400300a0603074900c0380e405510710b100c1c1c41c83c03e4490924610f507603542e806500607116600b003540c0c1c2400301800c0c1e81d01100c0030486d84851404c000c4415414801c0e0044250114000d00c80890320310301040e08a0009020244e07840e4071800010203040c05407011600035980314010087c00d69503001800c420158048200300e05d4001c0010005503840d2010340b268003a1002041d201503210280c4e0740c803002d08002c0d1014030070301180b0140040895010300c80079110301e845840d5280d4a1900345001d25407650781d03460b40c45c4614003003101141241d82c005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 784109055 1250 784107805 784107809
    0x2010c0201110f0105270a0b010b0a0509090a1e05070504090e030c15072006070e0d0f03020d0f1b02040b0d02120a020f0303070b0a0507031409011a0a030507 69
    0x308003403402c1045040014244180f08161070115800d1006000440410141c82d940d0302c1e100d10601e00002034030103002500c1e664444c0020701040c1c4660018842c06241900a050848860814a26009409010a80c40c100c200c0c0e9020a1580c1c0d1805407800a0400c1d6a001c04865224000c00c01c40c60000c0f00904507004a015081850360f8404044038400e20410407987c00311240d0007241c9880d403540e8040d0507203070717000c594410006803100c0718040d0b41010010910070074112310300540059502d80604032240040543c7e050391141d240306040b404587da210b000582e082c000c2d80600800202c03d407010380300388800a0090204120001c0c00300d00040c1002141303030450350464000c03e102904a0004845800383c3e03001075807104981309210f078081d01c0010b003041e06910030f50b0103080c005200e00406407280140107001c0c1070075010f03000041344000b180d800a6404296810001011001c03100c9440d1626004c4a04034104d0b9036442d00c01c8080704800410074015001100c415010074215078549454100e07038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 784110305 1250 784109055 784109057
    0x6010b030903030c130902120a0b04020c03070807020f0a0906141c030c0204020d1a04051f0e06010903080d1d0106180f020906070f0308091504020d0201030e120405040609050402010c0201 82
    0x226400000c405c9084420008181114056403181446580c2d4000348900b501ca040081303140645036881d905041c0203641000c071800019605000080e2640790407580050303401c036404507020494112640c1c500c802480504607000002440905004400b00ad40c1559480f8038410403000031103950944900302407207141603043c507290850158510100d4080d000f92203010240d2410b01d4804120440354a6803080310030004c80341408642c8a1403540c540d501d18009280007034002c0d83e4414840710200c0078040b6003090b010301d419240307295a138881411541001b1180c030002d40d11060302044641100e034990500c141c1840080056900e0304184a810980801c500d10780c640d25030130013000b40308850341902c3d000030740034288550b5103410746000c0b94508401e95003100814140004600910000180180b080d2038017490700c040c9450315020130610300d40c0b40c0e0089040584410482c240c1c45414000203107401da51206841c1c07614245000c200c1503031441d4110051240c0f42c00c00704801350303900c505813001c201d0702 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 784111555 1250 784110305 784110307
    0x807030b0f090a020a0923031c080f0903040b070305090f0916030e070f03060c021b060a11010e0d021b1203040b0702012c21070e090f060907060206010b030903030c 72
    0x51545c00340c07480d040b581d00400f81300b200b0903042c001340c1c0344d942403921050300110199403005901d40c60140d602c01384040d11200040c0a0780000300510024260182c003c842e2604036030902d903031030f000301d0400d503c8050700314001400881c80748680d00b007030b48070110700e00d01c204c0d69100725103003440556402030b90f01d40d202420551141440d2981110600c074403409002035602c106c140700e8032810188040d020740e2401100511600242409a013440e8000c1301d489540105041e160500f1560216814190031791091001c2d50b8800350b4030f071407030020490424100025009066404086c02d09804143c18803641c00d405000120401180340c03001104450030b81745007108080e2550040c0c0012600290b16490100501c16a4040604a1540c0d81410100e0b02811034180340e0003007a44d4043c421014040c0c40e80c0281c0c0d4010102030041c0c100a00c1c400354042e50441c100c076607180201e1030451408a081e51807d10302c0e041a00700744841a81400264050b05040d00c209285080070100180d0720b2000405010030100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 784112805 1250 784111555 784111567
    0xc15020d021506042c070b040605090d030504180605010906050a0207032d0804090b2205150a03060603021804030f0f0504180c0e040e0a021513060807030b0f090a02 72
    0x40e980c1c1c00040040050305d1500420562840300b42c021843c20f0200340014861044c0004a012100d0308031000d03078025542d41818100c0c00f505121014030802400c03000e01409100125003000800c5d06041410000000416a54030f4000013528808054000008100081003c1c140c0300d90009440c0040b01d50120b60313524002038000d101242c1c485034400124062104444400c00e0140040141c01629041030080064145c2142080248042e6500c903159400c20402c1541f40c81c91542d21040d07010740c030004840b40c51507140000501689041c0c100303c0f035107565042d0038803e60601498100c00080c850050ac0058107140d00c010b0110b0110140290421090341c4070600c1e503510400680b00285440e1240030038251b490034030301000d0440d08809100040f02008030140704d1030a40149000b0081110261000c0c81042c0c00788078070305100050741415004100210814401541ba2007401402e01c0d55070b8240e40c0c1015100142900e5041840301e100301c0b03c20a41d008199180d501e40f6400840e0102c0c0103075181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 784114055 1250 784112805 784112809
    0x9081b13021902150c0712030b040e03040f0303180b03041e0501021308060a0507050d0b04061716090b130216050601062003030112080a18030c15020d021506 69
    0xc407441c2c100800c015105802c4800098000800c0c425024099200140507522150710f0380079401a040080c01242d10b40040c84121030003540f144c400c401c0301410100e950100007100d0ba10f0356105904c0802c0324082c5800c01c00915a0082c9154400f200d4800142030a5103041010a494000504044d061030300c1d0000c41590801c1c2550099034040c0d02000230f545901407100c4403e2040b040344030750010360140600146010507603200d498440d403030a8644d607091042c1044103400804d07031080a83d8000d0740d206800700ba803813107110a011540b070fa0301008080d0000d4444c180d21007a04030303a0100400038103250300740700c0325501daa001c0d00502080480060300c6203648041d2940074601d02401801074040d02c000840c0e059404801074209042064403552005034000c0610f50300c1c8001d105001901804c00e4840d030004410b00002c04101f881442c0800101041450f0284035a6245d8011911405504002c04c0113960062013a2040c00403400a0403082048010181d01c444140c1c1d01c2c104025132290000c0c40e10303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 784115305 1250 784114055 784114057
    0x1030c092f0309070f0306090209010803070c17070305060a0b1036050d0507090c05040f030b071103040801051b03070806240a02061f211505041209081b1302 69
    0x5083d508051805c0300d0340ca05154005050020081e40501e01c00c000100317941400204031003125500a40480c0103500d001d201c0e84c0742d00d11402200909004d20507000000c00c1040003054024031044c0000030300e4210803400c1003e105620030091082c041140a1442442c0c07911885003a14400c840d548480c1001e003510000909605d500030383d43c8261001d2060083c05400140c8000340d402d40300040008100717661090300c45002d1442801c0d0318144510046c40080c80701010b154000364a4240100325000c1d1010150558200b90024911a9543c50801c1481e03a110201c03c0002141c040140d4a542004c280c002c1504000401d0a40106034442824405400d408800e20032130382c2c140405a111020f000000f512000c9c02d465034596005220702c001061044000d1820444115620a0a0072881c100941b06185002c900585403038600d021050341126840c051144aa0300c0b40b0900050380c5c4100601070030780d50b8207400c0b803034079980603441241c205c1c2e5100c118010043c0c0200c42028080c1060000c1c5006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 784116555 1250 784115305 784115309
    0x40b030c040b1b070b030c09040e010f0513110916110f010513060b0604060f0f170106050705010524040b06190305040b01060f0e040c0c020901030c092f030907 70
    0xd0410000d0805907001c40750000c540400d48140c00e03078413400c4c2e4030070403500540015143c10200400805c5101140c0c60709601c80c1d050b0035460350001c59010380442004084510444042c4042086040f1200c2000403104038980321035002c841000a5003070040400b080055807003003280a0004c0b80b0b1007001d601c141004610800140c01c0024405480d00f003040403000d80e940c0500b107915a080809080c1c00d0314080741500e068481540d01c0c908120390241048444041010345203040c000403800ba51201ca1400d46814003801003510780b00d0b40c401c0503240c0f0714211003005000c409052030300028a0403961601032060502d403012200461a401c244000820612610f1902e105180300341c1c2c1c0181c0b8980d0150081d910030b6000d40040319103681e990900340c2d1000c1840304603100098082c10144618078090f84282040c0041e1314101c0f00880190340412040d840030b030010740c0c0720b4150103c200010b100c60f00a00c003600d020900302d000e86a060500c00103003c0e00b41100b14448039804000103a05020030401a40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 784117805 1250 784116555 784116569
    0x908090406060509030f030c0d0f0c080a09060e1e06090a09050a06030606080607020601030213020d0c031b020a03020a02041a0306041a01090b2404080a03051b070605040b030c04 78
    0x410740d652202c02415a03400010f60764068000c07004942c25040000c804d98546800f80c0c0d02400c41030720400801c4808400b5203688200b4404281c0051000c51441c82c0034000342d00c0035494202000703040000c06004101c0c80a0104d101790101745c0806200340c81020b00324101501607802130b44824240d000200e11686d140c1158040038900010865107000316000502103d0180804022090b00e50340c1c0e15845090441d00c1c0c4025a1002004000600303011070140e0045000e071710014245541003500c2019941c2c400d400c4400281c0759070452003054424406085041d000d40000c0c40b10101e165400780d100c2504000107480b540d9030b0000d0410000d44d240ca002c3d06080001c003580c2c503510341441c2c0365003142c0e11b240c8640c1d40e0355a0b80700003094219441c45112410031004007044000034900c0d0002002c0503120110000403d02400005200780040003000c2a0b140300343c0391140c0300c0d00c0104108011140d401140c420b60751241d801081010b0b042000c43e0305031070303406400a6680d0f9611800012600c55a88095 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 784119055 1250 784117805 784117811
    0xa03051b0120010501050f040908040b090303040b070b07090b0913020f04120b07021006050618131a030c0d0f142b02100b0a0b0a0c0c03060506030f030c1009080904 72
    0xb4202d07040c10360005040e0388044917900c02d4801d103541408202c0f43c400100410507042003000f404042e4820010f00071100f001011289020740780d060305030054001c150125900016802400380b0302e60401c4441020349034800009003804240360000f25150b4290a4a441041c0d0001d07280c1e82640700d840807038000c0d2680468111880416107002010200100c0e00d450041c050350840b5800303a0101e02880341100c4004020703500380f00320008a01d03001131170408407990240100039003d007070b030b01c0c0c90280c980300c0300046401c10749004580d414141003400c1002190300c200348241c0040f0020308101c2600200c180c2003180c40c120f074810441504d145c0302c040f42e09200e210301420b08252800005061346c050031000d541c01c0d10042e040d595a403c041c5c0c2c00c82a1120752007101c010003840424414009801900e0983c508001105520340710380d00d0b034030006c0d0400c2d1110b0740c070f540400a00e420308100b0240d1902406000314078198084d03c03600c0e1120744a03407040c20501e07140e000c0c40050280240941d681200014820 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 784120305 1250 784119055 784119107
    0xb07060e01050403020a210804030e0619030605120102070b07180305030d020a0e2205070509130906050906010e0a0b220902090105030727060b0f030a0b0a03051b01 72
    0x80d590b0803000c0000c503180060b105146420407112050340d40c070902a0340342c014840c1c0309d50382c040e02d41c4940320014a8101e00f0a03c61030310918458103840d0204003482c3c60004101e820941400795084011080000760b07801006400700085000812951006c8240b40284111003282100100907150740c0c00075096200208101c48241056401440c0341011601c41d02c000d0501d10003802104070f5080300050580e0804c250002900300c5c10b0704119400f55585c5401e52801d48050001203152101310589200c1960b21804030003045420320590fa005040000181107941c900381c0008001c501c02410301d05501c0c2c9034a100300c0103841d1030f011100421241d0422150340070001d400200140071a001c16032150618900025280c10b0105001d030030340741c2e00003050154103145031710940a1581a180103d02c0313a51204009040200c8901030a050b490341d0307c1076a80c03418610f48000079100c10bc0c2d10f040c4500380d4071004100064002400c4152041c1d0150ba00745040c046400580b0180050107001e00d20754014204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 784121555 1250 784120305 784120307
    0xf09010c0c1520060406090606091d011d0715030204030204110c12030c09041a0a080601060801091505010309050c041e050a0b06120c19030e060702010b0a0b07060e01050403 76
    0x800d40040c010f5035030010540201481149490716840c50003410381090010402040e00e5400074006207015400100d0301990741c1440c41e040780c141c2070615041441356845074400301828001c100407004441518161840154500ca07111002440341e01400c0002038450b210683c02038041e00e0095070003c2003001441c0f4031421980c880d03405109022998040d00d8100990709a81d44103507801550f1072189a400c0c4004902072000510aa6100c1d010404030241d280b9401da907034131084005402d014010304825403400101403d6404182c00240c074817428a50908084450382980008559091a011490780031904290307083ca22080042034000e030034450501096405204107110f445c19a050400c0190746007039075407046410380345200d030b40004100b2046241c4d0561a01d056000081c4051140c41c1c4440d081c958071014030030401600c0440c0c8c480130340b00401d81d0180304556210400c0d0000703121195024000034030241e4580155201d5200c0405c10005000e4030b0ba10401c040d6801000030052400d05042c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 784122805 1250 784121555 784121579
    0x917162c010b0301090b0a150203071203050105220f0c2102070b04020f060c0114060901290309030c1b1c050601030201050d0f050406060e0703060b0f09010c0c 70
    0xc00024125008080030140e51a9440c503040700d0b00688030758203507401c101c05036000e0002c1c1d00700542d02c844608404100089411041c803441d1000d074005540e540080c2c07510320541400845410249840d0600401c12034072003040206840c090301d250449011098030f5690010501890905100313481c0010181003030350414a00380c0c2002e40306025802d100d4401740b0300f0040e8400c481d0018412480c000c08140107080c8240c0c1407070000300050031681415103804000d4210386462800c14070408140090007003505006281c50b02508080da40b0300d110400490f8440204441e000068121410020018244d94810310685008840720401d841c00d4074030740f225908107100c0c1c03210420700c0744590700054009034000410350100d090703009001c2c2807682e29507001502d540e0404d0400c1399005480c0c02020300202c0182c400c00e4455440387d400095030343c1c10842d00c1d00521f0001400c10091510300701c414401d840201081d070b1201d02c0d440051942d6050082d00489061000520007001507114510104007066115 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 784124055 1250 784122805 784122839
    0x10c050a05160f080705040e011e0906111224030709050f060409150b061c0e010501060302030907030209090c062109160b1e030a0b0f0907091716 64
    0x70b00003800742d1a920700c084198040e2003403400d03940c0300341c0b800c000702e041a4000405c20400c8030000202c54804250000303a4090921001000c90350360b840100c1000b00600c9003940c400078110315507042c0142c107280c91500e02c2c0c0252000101050b07501c000d8194240d40260100e500b01c01070156400c1a81d07421088025090584058001140103c0042e0b032a08140c810311141075000024440c540c410030b01114002d00c000f00466801c0b0f0701c100404c0003034460b0303158040d1980905010004a0380710b0a080304c1e0031107006800035010580104144401a03400064042c281d07501200d0140068482d105010b1405020319070240d0000408038070005030519924044c0100c407040100781195903111520140c0329101c013440d50707080d50214003082c08452071f0100504610010f02020070100c50400d0307071191540e001140c421500c1901c44054900b1410070701d002146d107103002c1d140c0500b5070410540c094400c04041c003c2c8610b50750120f0b000c06400318104603002c0c01006a00c103d003001034640d10301005c0001c0e20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 784125305 1250 784124055 784124083
    0x210c03020c0f0d080c071106030711010c080c09270a020304020102070b0a0f200a110109050105090d03050c030d050103060504110d05101a04050901060303110f0604030806010c050a05 80
    0x662000340403890202d0210403c407166681c251017560b45c50151103c40d000014107444441408480c8455a02c0f410011401641d860307c5006044101915060a44540a900c0000c00503038505001c800414082030300c1050380100c60307051350000c0f132844020301010842d0510108102120521070940c119500443c0100e00030b034251510207489000e0350311184651444800007414030301d8116010391041905040c0002010711500e83c20414502c2a40381140341c0d84181c071010026500c40d01c9540e04184c1e40d000608081c02d07e1810440a01d000807104504000060140280040c2d00800490140100c4200307815a02e001c10083d41c4909000300204002c039400c640c007040e40c1c4110b00d0940703030245040c1c0350741340e05c07000a00154921014103405050100341c104a60314210151801a0b50385001c2c061003031002100006040d451070030300400440248a8400b09508650800300484e0000320394140d1054150504d019251100f1004075600203040c10060142d01685102d0000c021002c200c0c501199a5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 784126555 1250 784125305 784125313
    0x3060203010f0e0f130c1e0608060a080c0904020109120b15010503040803181c02010b13020405010215130f030c0201020d08090d0c0c1a04081902060703210c03020c 72
    0x5030001440ca415080e580c06400d07000180c006201584450b1a800340188904100c0340029562a41e040d107407440c094585051f010340e04030a010096000d0107055005004941b06c100c141c0c41c0a10b095241d5010f80c60240c0100f502030300040542e402030b603040c001000034901c184c8031048903090020314141c0543e07150b42000d2900a254040758801c03020f0300d008a03086060b062468641c2a81d10007104d40c54201d0b141103000380f180c0c03c10070010440c2411005802e40e000415649520700030450b07080910909600c0c0c1e103105210034040e40c4d0340010303015403511000c0e099009d540c540b41076411101003000c078010105901c1c8542c0c00201644100d10400c81071003a022200c82c504c400e10199100c4004549400fa90b0340105c01040d035403031180c01103a80c0680107400714503400d0740340c8182420501240302216914107000400700015081001801040e80c2080f000407142c08070b5500040181c403401c2c40c0035003040418035103211202c0b608120110f90344940302c0d003088020030406015029412a0380381c0891801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 784127805 1250 784126555 784126559
    0x1106161209030b0f06040e100605120f030714030d1d01050703050906070f0e0d05160b030420010314040636120909230c09010804060209010c0203010603060203010f 72
    0x80180001001d580d8094085001a511106100313000400184056440b40d1a0380f1060221a001e00080d018083d20306401300b1981d0a000601c061611101d0210b2380a60112494500294001c404d40d0409503010512440000d903000f002442c5002d845110340c00c1500d0003020650701c0720302c482210111004200203003c50380c0c5600055045030000c0310302140c03a030042d400240c41c452060340b11000d10189810252070400440000c5400321410710f0048030310780c0c4040d05881c05c501c0c061840100600d118030b022859403406170f55802c495114a1840404d950300b045c4030f1409a0300030742140c165181100080c011510345410164094101c10304c8150380d031a0305885c14840a482d101e65a60020034076440010000310030340e941c104083c8259200070800080680c0400d04150038041d00c3d0b1120095540b1000c940500700100e46000f00c0544000f0b0185410000c84041703907001050709900c150040c10050b1110420401660501550340b4001d5040d440d04002104024507980510f05039404030070743d80001c036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 784129055 1250 784127805 784127807
    0x4060501090e0703030302030c161b08030705030a200d081b070c0b0304020f0a090209030c010c02010f12021b0f010c0203090d0b151503060925050711061612 69
    0x30048150514150400407003800806e029030015900321412134143d514110004444151803600f964003159003085002020581c1d00d6441c6002025000c80320241d4588103066072151398912801c440301c001d01044581d5003140380c00347c0b40082074881000b0195074002c0c11203c1c0c001e228100c00c42d001c090040e518000252101c002c0800da840c2d80303034018054480541418050000c80e08000c00881e4441180000d92031684c849070640c100414049401603140c0c40c81c44201428882d60401c03090421044810003400b607030344026035416601f4079040c40041507400a079620040d100d101c0c0b440194060640403c0300c0640c0004032800503260340d2008000c2c44242c90800c81c5c60b440390f41816075110f00d80c0c01401000c00c005081003500601c004110440700020781c00862803c91508071961411800401009800e091001020343c0c07040140000801152041c105050703e8840390310541c0c204000852103c00704071185040240c0d5810040081c1c1c0c5645101d00803022941d41c000b411500c00280c000d002902e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 784130305 1250 784129055 784129061
    0x50c04050f090a231203043809010e160e061f050a09030609150b03070509011a0d0e160b0901090506220306020306210c0108100f0e0406050109 63
    0x1224408041c04190701d45846030302540c0341c1c00780e890700307200d41010031071313100031020007603200d001440314940340d100e1415040400c102e00c0c0c017840c400c000d013000080800c2190002c1103460345c06d03564200da80007640c0f80d1101d01d43c018180403d014020303225030842e281a01c189100c07910704840150300741501c5555241d0620030008038004580d4003120074449130b860010700407006031010314068908200c10710740e245c64640036607803440030170303610148880c041241114003801a00611101600148800c52900c0c01048c80120148901c1c0c078442584840c440343c040e600421100722804035a07088c41107802c01090941c689440400d0782004100c50b2100249041040098070b00c4500305071100702c0703418135107070a114480d40102d01075840440300d4200403942e105001401009140568401a01d9181c200240408211085c444c4084100c1d424880303807c403500020f240107600420b18094240f0307180d182c010a0300104940000105170214a00820381c0341014902d01e00c2a40115020301059903918401411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 784131555 1250 784130305 784130311
    0x92e020f0c0f01050708031f05060a080f0601110102030f160813030e0a03060c0906030b030f071202040213060206150f01080424111e041212090b0304050c04050f 71
    0x80303a0030200c00d0491034949501009a840700c107040040c40c00c1240d9a401441d684100c4600e140c008680c250b03942031000c07810b14007028147c103071450b41c40c01e03916000207401c8460003403884011454010003d031b02c59100d440c0b0050081d101034001c1d0344a0070809504000e400c011112415084190010480d6091096411031b003c0c40c034050410b034503810203440440b10103608006080d000101e90000000180007072091b0006071040340c2d55010341d1420544028240d03014000000d21903030040c0810143e0030404101c40301103444a030405c61200792580f02080290040c42d01c4c2ca4074040d802100060810340104030700f44640b0010460300d88100c42441000403406070580c9250004d1012400140000c40f61804124494039880e111500026034844110a0386c01103080c1008050001c24520010074400440d0500600280703061828903060043d28550340f0100e1030040c0c240148030400715805801001180042c0030040656940c034070301380c20f10b0341d81c0304504130b505400b0b54901000110980001c10080d40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 784132805 1250 784131555 784131583
    0x50f100b03070f030b0a0e090d09061209020f0909070e013c081b130e0616030f0501090203061921060e0706020d1805150f092e02 57
    0x20550320340c0d01007103546050a01d988002d04d680e8102c665101d5540308980801000d06458041c1e40d49001412075007462110715891b414410806018000c0b41d030455903c92030b0b8600e41000080001c0e4600000d03d030f810440c6036280d0481841400d01c00c020f02c01060900559149142515150b6613441e144e200400c003d900c0c2e03010640c50501e0101710030000c0711501c3e240d40da814003000c8a00c0d0720b4030a02030a001900c52428241e448240078070040307062400e03030f081358010490310410114000400d041c0e2510b5004100c001412007483c45803d080307000e580100104c2c1480c40d0300300308540c0c44a03419802076009980d800e2280500d0b409403625108100c4148081d150040c04104c0c12410781c902048410450410446440340c49001840145004102d4000240050b900510001014040c06010025442c1140743c544641d0346052203280c036600d03041c03444208821040fa640f060b2801c2c10b01035600905103501e522400040c6035440018100f26403101c0c0400080c010304114409410aa9550700044048a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 784134055 1250 784132805 784132807
    0x80705070c0b22230901030b04020603130b10050f0607030c06110412050a03110d0f3e060603010207030e040207080702120304090c111005091f050f100b 67
    0x4440d02d42d0340c0340a0900000345008441c000b9503400103102107580c940c1c0028141000041a002e1221360900442240c40025588030b4020b5042d80c843d04540c460080019004500001c08100403800c1c400c3d0b103100b5141c001da8080b446046c03d0000c02c070700c0c1d5101d106043c480d416603101c1501d20300d00310040b26003c3c0d905071205098101142c0c1d820010307051442c41034010703081c24800060240c80e04011629040d1141018003040c501615020340348540f02c00c088041e50f88109030700703403006401c0350480c241180b10f4103050040d1404411110119910302c0300d0350398003032545100d40442503603150030342c0e950081c0101a100c0980e11001810300301c3c06030344400b4000550004c3c600c51107050590080c40d00b0b0b80982160f600d0000242c0124030b00400340b407420791480d41300007410407044805210700303003891a03146400d205003446403074100d0b5122010040461580d90760404543c00300d008124144001e1030391032140447c01d4110b6080001060100e681d41420514040000c1c10004800408029214082c3c070403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 784135305 1250 784134055 784134059
    0x90c0102060a0c0203161e05032203150b040b10021f020c07051201020c1204172d0a02120706030b120706120b060d090302011a010806011112040e0106080705070c 71
    0x3d6a800c42e07845509580d801d5054a0300c2d444000d107c01d4491056020b440250b61711580381003d81c220b01c5001441e001d441c120803c05000180f892051020400c0c00002e0106010510100207002000840103169100000c00000d100c000d4022403c030200320050b41c0078045000220221f80d050b881441d0700c40c001e64102c940309102a2402450b00b144101e8401b0006007450908050b41d89030402400d06007a000d2004941003051494403240340c010303141d141010b425400e240c1884024070200f609120640c01d06c07801ca50040000041000300700030340e001031504c40300a6012424986503000d600440002900f440c403170084c00e04244401c0d11420015100800740c0d5464101c00b2a0380043c04c038a91003160391074644174616079031204090245600c081a001943c4034040c5406802c44401c0d010002c230019a00140c140c03542c2c1c000307041550221007802d08480a511800b07405051500045035030391038101c040340224245000c1c12007103060300d0b000d80700c42d01183c41d103406c241c505025000009000000305041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 784136555 1250 784135305 784135327
    0xc02090702012d020d111c06030209130501020d05190b1905010c1a0405031314091f0b0f070b011703390a051e060a1a0603090c0102060a0c0203 63
    0x280c043c1d10143d4202c01820300c98030026082c2070702c201c0e106a802e004800f1401c1c18001c990404902c0e05100804801c200c4149140c0c0410380c0500020113649498030301800d0b000501000790100d504802d4014001c012616043c8515440c0d02651403030080410314003c9440750703134180150305001141d0036003400441d032854000110740007001418100c545500c84004400c3c024440035070345024500c070708003450302c030318000b04520700341c5110781d1114502006654420100b41c9030094a960421000555840c1d484d05000242d11104c7c1280d00c071000d04500010000d0441c6c5a1001070000280310720a40d11459907294075155207014200540d1a140d0000c00000090001c199190110250347d0400003c0252030940e10030101d012000b408038a03a04138240b110104a018000e40030414800d10b50881041c942c101116506d40340107189161480d950141c1130f12484000c0c0c90101050001840386903681361104446480b2280c684940340940b00b81d101141c0103135141d010707004002610747d006608004079011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 784137805 1250 784136555 784136621
    0x3030c0c09040303061a0403060510150309020a0b07060203060906030604120f0219050303250c03050306041d030a0215070815010c05010510050f0d050c0d0812070c0209070201 77
    0x11014545e54500004e40e00721101160444000769669040d125451400c2032420b40380c000305503041e50101600705006440c0e900c21118002e000d5031800003440030302032010488101040c0c000c0b01402d0b5021502030100022900254840c40c4180c07603a045a4407420113059503464142e4004203a1401d003440c0070400c034450f02c0210104416807046407156031414400c0211861041c0f401c5d111078000008002c3e20301c1c110000c1c2904c4404203885107004c9100010000c28074540f001c1d00508000f03000010036079940d96508070340c21180410900c20000400d0180841d601d51025a000d40917018079004124200030034810140704031100d03102c0040c4c40d5615a100d00c000f04038005103c1c14000040c0c40382010500911401d44500c60b01034004550034100740030000004d4902100610403440e50654000151780411140042d51701900c920318034103032a140c00e140700c0c011613032082040301c0c0450401c0348190b8498098007a0394029030f03464043d5181c3c0e0038200e003038441501c0c07103400501d4480380c5410f0b1110001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 784139055 1250 784137805 784137811
    0xe0105060f0d142403060103021302070c0515130e06090103060f0f0c08011409090d0e01110d0c1e0f0201050a0c05160e01051912060e1f0b03030c0c09 66
    0x301d40042c900e4540c0c4040c0503c0300e02503a01000c3c5298001001c40740050b10840780e0841e18044005010640c955400203c40c0324030b80e140c1440050300841c40c0b130204103640348401d02600c4010a0803005000e0b2540380c0f0601c0e00540080302c15100308040014806240c0c0c50b20700e008000c041c0400140313a00315104c210151040d140c41801c2c0d165180003141c503e01c40c0e8400c01303100044581c0e0b82e07400c9500d00150101c3c040403a0b14681e00c0f03107c1680510803021000901c014050a003800c00e80294105400181d601c08100841c6903041d00803c0790103945192302c14142070b1040e10070451264143c00d07600c003400504482600040083c0c010007000b01c09580250042c01401c1200d180521550065654160501d444d4807103c031841900305000340504c4144040f0f10b4090038094034040030030020602c0e03e002c0003070103103c2e0a03110300300c40444d501401a1900308040b140e030050102c81d091003c031310043c0084010381d40c4c00c4200034980200400245800710807141d10303200c2000208080e20000c003c2241a220103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 784140305 1250 784139055 784139077
    0x11010f1d011d06070f0c1a09210a0516060809100f02040b040b030906070309020603041421280e0f041b020f060c1e0a180b070c0e0105060f 61
    0x2c00e418600641c1c0f0b600c01081c07654170400a900c5a03051a01d45001308641c1500048007000c1d0381070242481410310f1080c2c847c3d280d030131190010707124032802c404041940d203200c550965004003801c01c0d043c050005050040c14420440d2400313440d41d24141241c00030019128109150498100414660080e420066404c01680703c014500742e0307034804006c00c0e9485540142d241c000d0100404c8a2400c05200c03165011019060510007001d03c0d9001603560702c80108024486200085442c00c400f0b000c00081001c01b0034a001078000015480300607096801080100b617803140a96040171307089103000c03002c0c04000e0b45078440d0151460950100040d4070f000340c0c412a00242d9500d902c00045c031440d01003903d000303803540207440e503096101281428100700400010220008104004100d44a5003801100301480c2e011507844042401c0215100c0544c1e00e00034044403075450000c03407070f180050300412565104a90805800340d5410003034080d02001d21406510150a20030b1400145d0000010700e426409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 784141555 1250 784140305 784140347
    0xc030216060207030506130309170709020d0501090e0c010203180f1503010f0e190f020c010906060503250504090c120533040320060411010f1d01 64
    0x2006036030406050469010400581c00650104140074080c4501030304041d2242075502506000c6e10701a2401e515445059045194124079113015802800001c01078010701d4019590f4480f02c00f0020060301d070078000d405c1101d03d0000c1c2412015800a882803040c0410b8000d58184001c07000c1013103000c00c44203c4190480c0300301805034110b69400d0407100ca08403030629035580382d5040c82e860480d6080c2c9a00034240d00103100050118248011006c41c0c0703007000030030002c200c003860300031544040c0c020f1034444000f940c01c0c0440c031030410005410400944409504950f20105a001c8041e0450701c0b003281c0400d144036004040c0a242016007281d503140d0b01581c665001140d54076015500c03903500d0502a03456411007424ae071f400145200121b03c1212200602c02034058041c40e404d6030314030700900b004080c803075844102404884880603604050817183d090704c10a20701410300020705511060010b0020f4200074440e0340351802107410040c550260072a10014660b20380054030466219403540603035680c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 784142805 1250 784141555 784141573
    0x4051c0e0a08030c0705010503040530031602120a080f0612030c03090f0f100c06112107050703080103241a01030b0427300f1404060c0302 61
    0x4415400320002c00d0444000c1d0340d5291100000350910900c0e070032803410030100300305020115500042d0b03042641044650712584031010000403104001007140b002005502100300001b480005074808111b9207190241d455400c44900d080d25188124031080011408500100b111680c0d40303801c0c1e50740414040c003101c100901c400f00c201d28542040c00101180d5000040c00840c030300741400d440740310b090144c40d0003080c40510800070302281c0300a000d0204002c0c110340030600f489000d8014040607105491080d954202c04600d080d4690350242242580302640d00104110501c19030489d00701a0b016036992034141d00b50707602e90491034541010034000780044501074004100c00d202d0184480303000368502011450000015065402404525120741d1612084204c801d9180c0e10012941d008142c0da080c510b40285400300d8803503003001c0c90703111000b50500960740616414581d140103903129151480c8140034000201c0301d1454600c07074071081e0300051200700300940c018020480414803a0040da21010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 784144055 1250 784142805 784142809
    0x906060602192418110306043908010903080c090303190309080307080702100501060519031b17010f060e010c1a09060a061a0403030509030f0102210f04051c0e 70
    0x64200c4e5600d03610983c014130410100b1079001d2441c00c4508064003d00b507a840c20780c40c0c2145100c9000c200002120008000d9105a042602240512051396410820a6454648040c000c211000b401c4010401500114215400102c01c0d109041c500400952401038106401200340c039038545540c003030540f50350b0b09000040164000c4c601c00c8200799200c054510300740704001c3c03900030040702c1c1800040c0f80c41c00511031503a0090458504104141c800130801d04201002c4000709140c09440d241130210002d900d906035800503d480d45035441c00758401050740c84a0808600384060300c0f034a40480c661500b44145940141248040a4000c841211500108031401c02c0403400440b45101c03250440300400c08901c440b4803030040a401d07080b0940d00e650007001d003501d081e84107a000140c14400042150b040507030b4200001c200761005000250f4a40c5415004070300c040e0840310200c038400c0c0001c00059102010341400c144030302d41180050040180d0000003996103c2050081c4c0c0c208121344840703603826 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 784145305 1250 784144055 784144061
    0x1b060c0a0c05070b070f0b0f060102060f06011808060108061e0f060103060b160201023c0f0d0503042d020121020a0e03101107080309100c0309060606021924 69
    0x5c034002d2920254900007844c0c00d51184000400000d001e419900074030855913130010b061940a07440e04c001106d1515050016280d0903481d4550300402d40da004d101040640700800e00300d04030341e00c060031104591294110174041000741c0710303440c000c0c2e045480012250880d402c00d150f002035040c1030024442c1d48464014074550310502c528034501c0001e000850455a0400c06030004418401c852942e400202c44c00031881c13800c0c103034003100d8005040c00d0409400e805200d4400d80c42d620104551041001a002030319582084509a400200b8201c8101c0640ca069040d101e24540040f0b601103500c0d0701d640103481d0800d0f01d032076140b1501d40c01009002500104d200034041c61140b0b48500c004043c480b02010b2504000340010380030719051000164982c0115170a481180340d0191202d612650340e503c600e072500d210350740543c0e030050600b201c0e5070095805900000000c0c4c09100144a0140c03186016a5246c1018a903102c1b25207002c941500410200c030740340c3c1c0c000d110362030b0654000a01c0004243c00d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 784146555 1250 784145305 784145317
    0xb0403030c1205091503180d0206100f0605030105040e0f01110d150303050909071b0c060f082a090a0605030f010e0105010518030c10051b060c0a0c05070b 68
    0xc104074680070018010304540d1692800600d18255241c0320010012507070020040c06513040450380030010600c012012401e207150188680e08a40501c40d5104000795204010784002401c54056100401c10741c8a00e4500010360302903072100c500e140d1170881440300910082d080c0031441d019014043d0201c3d4020701401c401e55103501401c40e01d40401c0003843c02102c0c03040c3c5106024015181041000030341282c20340380c100c1d4040710a1000e40d500c00710305580141c09040c04100600b10b0214800410062114480540c0c40b1640c6520f85884000801d4803201419110a03480100b030b0700c5642c2041508050501c40007050101c0d42e030801104401285a030701c900d82003003010840200400035000c00c03d000f4240104400c42c1030031819407500c000a0213610031202001d03403182c510300410445803020040c52200400107824410380d002840002445c54200c6070f640300c2c6103003c4008810145500140450123528048042e52a214070040d0079643c2c2c128404003105d00b03003d440d4001a44010760000380c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 784147805 1250 784146555 784146557
    0x150f07021f05090709020c1002130e07120c020d021f020d06080f0c0d03080609060d0503071112010618020c1905010605040c0525050c0d0c1a0306030d0e01090b040303 73
    0x142d5401c284070018107045040d003242d001e0b688180140c01091000003184d20801c00c2c815401a940c110300b409800d0451100c0d004461214070010038000c4481d072101c54a8040c90002c0d070204003c148080e41240c603003421aa0000045c0e012500080e02c20700000e07000e000c1c00e006050b0062514080f202104207880d003652042e07106401a880080d000d078000e10078400c400c9000c0302c0c2084c48440c2640c1c0070703081c0e503405848a800b5100b501c00082254446500d803d072a0303a004400c490f1205820701d03201c800d0702c0c107001c0c840b4000c0381485010790340c42c4014020340040e510180c207019104e1055101c140c2c0250020f084882091060071185c000340510b010155268034010000451014100002d000c191036101840e80c080001c200000c03000750303610721803404a408038003036401505000c904040c0e1074a45410f00060340540094000c10400c04001c40d00710032103a0443c208a071340d60704550b400407103000c200c2d085c541580001044010581c4943e11301c128290f41414480030013a2100a5406a5001074004074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 784149055 1250 784147805 784147811
    0xf0f1002010905060a0e030f03061504090207030e0604081002160b13260304110a0308041d0a0b010f081b0a1205060d1e0317040c060908150f07021f 65
    0x2c0140702e030910007203a000c40782c40014410103d4034880540d40344a200da00800118020000c50300680c0d604071035103107481e07880100d40c0d11180c803181104000d40c4240300460107e502c01e00e032200c4074200081640c04850007840a000400c040b002d6480103035010400012059000803e420b0009002001c0c4034010320030310303070007842c448250300d03241e40580765804c0491503000141c1071010407038001000701c991041c6d22800c020f900010440100710524001d4200030881100840d0100304007541c04600001d20481c0301e00111140c80b1410590200c81e91038250a0001301d40c80603545c0c01c0381c001d000b52a04800c007800b0780c1d00055034255000c0c007113405c00118203000607080a90280007064074001c484e0040c0c1c085941c0000c0b0300360f035030380c042002a0381281d415280748801d030b01c2c0c03040c180591080c9145140799441c001d058501031800200318101070050401003000f0300b102058060300001c1e50070a844684d07010740c0d00758a510281c1000e02100030159011442054146624414450032403806040600404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 784150305 1250 784149055 784149071
    0x6090218070f0810151e050904061406090d0804090f020d060603150501030507030f1107050115030f0615032f0d0201140f040510050c0d0c0206090f0f100201 69
    0x51802c40c0c1d02c03915208001018003402003c0c00b02284407421207140708a4140512101e81045e01c0000c6001c0542d0004000201940880d5400000900450700229030401242d03468003e4000030b5010400312542203e41070011442c2c03418848408130070903009501450410755100b251100780c0360580b50800c0115008124092501010300401340130b403845080522440c403a405000481e41400d03c92141010384510210f43c1080c02a482040d840b80c000009020f03544815461302100d91140b50304071754944c60581250034495003c0c243c041586d50012046d042d0036a5a00e400c00900003001005503d06107540002000421186030007042d410000b00a41c40240398031400d110070380c8a0030100d0b0013903109606520050f81c1c42000c0240444180b000180c5624501c08a0301d800d0059403c00398010380c1460040e0b150581101c0a41243c0d100d030012034020813200001158a403e4224000390094418000303441280f400480ca401684800f400b5441a188001c0000701940c08102900c0e0160f5900d40c91 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 784151555 1250 784150305 784150307
    0x509060d0b070c03170402011b0804091442030312190b121f06120b0108010f020a1202030618100e180a030c14010501090515040e070603090609021807 66
    0x4610b10365120311190100c4c0c2c81c00f60006091808980801c510650359009c0d41c4c2d0403c2001c0c0280d40140040c0101004100b00c0d43c3d0101381204000d4a60301c0c01411000032507845043e2a4040d8031a07414560302d01c0440c60702c2d0000c990302d11640f01d00d8032545400148081c2420309690400c01d80b080000303003904401105030f160320304211a03001e001c3c035009031a1803031001d0720b510001035510300454200050549050103a14900003c2c48079400403010030388540145020300245139446810f89115900800c000c07202c0240001c124410f078281e0401040051141d290034021303581c09142d00400213062a900c600c0105072584000700704861540c00b0320050041480780154041c043ca510a8054000660300800e44c02c0099031020760a800408000b84594584100800903601405d034180c88c1e0028002561102c0304c2001800086551000302c040529030700e00203242c24095040380b0803c002c00b41c09090700f049422000f400e0b002c0800d946c1c26441307454400040e00c400a404101240c022000304803800c1ca00742c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 784152805 1250 784151555 784151567
    0x403031d1513091b0f0f0206011205070305060c070309080715030f0b0301060b0406022107060203040f05030703030f05151f020c0a030b16091406032205061008160509060d0b070c03 79
    0x712100704880c0386814501d03547c002034124152600c51406030040005441c0c150719015050300b000307040d4002c900501000740d00f0540504482842503c41c2903060380c50710581c5a4850192181d1240f050703a1a0718800101e000f0342c80305840c00542d103c0032031070703500e0900404d0075180740b5030040200440000c5d0402146505000e90f0a050b40103100360840e0701d881e40d10810090150000280420b98000301280401407240c4084d1320642e4030038160790316000e2030f080140c0142401d558001015040400041d000380e0803840448520500400701c48400181078000c941d0341508142020561249290746000340d540c00200e00f0003103104441d0a80f03146400d4922074441c1c1089041d4400380622040305026a04540004001881d41034409544039640c0a100d88e880500c1c40842d44200b0b02403040140038843c0105119208103403243e030100c040f075502c1210a07590840c103d01c8840149000d1000e109500d003040210f500b0080c02801c00c01c0c516030503202d002c0648000c1c1c03824000301d02c000044804041d0002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 784154055 1250 784152805 784152827
    0xb01030611070f0f060c0509060405100c0c090b0306150d0b060103180b0a15180902060d0203040b1510020309040e07051203042301080c210a020403031d1513091b 71
    0x31801602300320707641c0c0200d0043e01032030003010b100c2d2210903040344405100319180017000c0d401c40d85000c040703952403d44d0801010a041d1090080c000d2500044c5450110320741840e131001d01810b00c000304e1010352a0007840b4035000d0411810540c8840e0324000050082c0032987c88140503190080d17440c18850300d10313070848043e048124a0310102030002c102c4183d1001e25072100b19540c81021500324043d200040702841404c00c9140180c3c404001d00051007202400c47d0310804056080744030301c202d54006c202c03100042100020040c0d00401201c08141420f410286204184c0c00403a4000b03a201d400182542c41c480091510642c404a410805111464000c0c88484451035a58203075041c940002400d1000080c607460741d4060018551003084100c200030309074107450442100b0b09082c00a10440a540309110980016880b441c0000310403184550242c3d10170001050403c900600000c49182608200f043c0d030307000c1018460010f6500503d002d08090140014928810260707100740107409030a6030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 784155305 1250 784154055 784154057
    0x110c100e0a03142203030905040b04050402060f090d1a04030810080703140c13051509010b0403060e16060e010f2c040f0e0c0a120b01030611070f0f060c 67
    0x184190042604031203942c0380f00300b070103000981e60000d0180e50200c483c90244500400f520b030884c0001415400000d40c016102c0880b0300740103030000c0c803041006551094a019600100c2040f00807040000d020080c00740d0f01c0081c1c0300741c0142465444000e058140580c50000b070300c2c8010100002c140d131001400b40d1105030301c400013214500740340340c1503035503a030300d0200500d44001d00d034400c800c1c54001c112011036584000c100c00b146a05a5a050014100940b83e0101e5510303114201d0740180380221905040c0c4084480c014181440d54a07581c020382004c40c210240ba000d410158042d4400c808005806049140c8541c40141d0703070000010003c0e82048078400c01c0002085015841c1c3c0e84004481c58403000703040c608021000b103000010024544210b211710102d1800308402001e41c0d0201d51000c040404480100030301d5542c00300c00002c1000f1000050403294400014000222258403881c0c10000c800081800c15034142d80e070740301c055880f41090b1b4403a1344076804a400c11070140102d018070441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 784156555 1250 784155305 784155313
    0x9080714090c0301121101030b09090d020d02120706231608011706040b0402060c070801060f06140a2718050a0216030507080c1204080106091e0e01110c100e 69
    0xd0805c004022003c2e0904c0140382d071001028810103a84203400a5100b42c9006180c4451420008201a80d488410301c090001d4021001c004162900114040d03811382d40c90480d491070b040007070380d6070350050440754503c4107141c034140b404048110359101054402c1c16100e4040d01c00310483c0030060950701c4140d00c00c1006000c2960328100e040c9021400301c5c0c00961180c84a40d072134407580700284c060300544c113808c3c50758400c24100141420054022500b2a00303036040c850318032515288120b403000030700150f480d046403080004000b15403103014030444880c2005003142e64020442e81102c42042ca962005200c4028107a02c0aa00f60140c4900b58210f0305100b0300f1031a254000e4800c1c1c54218481307401909118001c01e580307007406080030407200340220040641c6c0c58101c41e0303600c3d6402c0d41c20500600c03403135620308a0301141c079048600c280c00340c640b48401c410800c41d10a610b06c00c0540401c0045440075500c40742180d210200d40406080800d0075840074201e0464034012040c115216044011000e40c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 784157805 1250 784156555 784156559
    0x1605240103030c02041a040f060509010e06060403080a020c0d0605330f03010f020d050708091506060702010c020a06050301061101090213051e040506071d01140a09080714090c0301 79
    0x2030040f2030700c2010341e816100480c44000c1c404001101c01c0c01810303559000760522103070b40c020300da20360f00517000d03a00212008031150f600d4681032050180c0031903205421980401048c00850380050240000480c1171040310361a80358100400c810901e080c1048070480e446400344088580d00321000400c001c4804003810382c01c00300700e140c9603000308001c0205000e9410208481e0181e282074101482d15844a1020365480100150039002090125030600010b0314a0000c0341c840000800c13094187c0c24040d00310351103038507000708101e0380d644156001ca050164030103100c00182c94400401004014944a003501c0c0d61402c6000b80012030161101207940c1d250404080040e0744150b004000706000c2000001c40741e41c0e00541044a030701c0048040210543d003000c120400000003461071080c2d240d41d0340c0d076003103d50104600601005105c1c502c3e01280c06400c02c21001c101306c40107440c906459141c60406075075110602810440d90350881d06a002468010090034100003031a55044030444003880d00d158 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 784159055 1250 784157805 784157807
    0xf120c020102100c031107050d020f0307050615060921070b040f030b101707081c0e011817061b030105010906141b030316110307080f160524010303 65
    0x51142440030016682d02c060b1464850312039030201000c510031206c541d030b680d83c190a000f55212960300c4040014410100f1015030001c011041e5051a13134010b006040586640380415160300700451316542080c801e000e0f040070303a980c041245101206101241c1400c45402c84c26500300313480f42c0c001d520b040d00f08020030000007900c2d241503000c40b500f06280000075142d02e0342c070000102d4143d0100340c24500391030b02c04c041030390301181d88822250703180126490109604054484080302805030004141e08a940b405954010a41441510b160422001e03c198450146104415800c2c0104101e0ba00c41010840c190854070202000343c0c5e15620000e00f958500740c0000e01150035801250300300591072003050071000e030600a50355844060360394010f05900c0204e40e2503981d00110703913450080c41003035000e049840c0113195035641125054065858200303507480712030295001c4640501000c0b01080030b140080d03281a40c5458040c80341d0040c240280a0411040d40c1200e41e00c40b83e2031030007007040104006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 784160305 1250 784159055 784159063
    0xc020a080f0307030e0a0302040207150b011d10032a08090715120908210a0515040903020a05060108070303121b0f0203120421020f06060f15070f120c020102 69
    0x103d640751801c20b4020180102240e10b6044031f9200a40080c0041010800c202400365401030600c40310904110604000f001101c12000c0c1d9010004d007a002002e141070b241c20a200f400000e00717102d05010403841407201c08a146040c0c0c0c10032040d854800d07540003012050b0711040264020400c00001c2807002d040c8070189265444c003240000511403d206011081c1405401041420707421840700c030b8075402004107902034110f604070800200414000003400b03065840c401e050050703a01c1c0140501a0202c00b051000410885005400b50f01c03540204c000080c00130004103011303121a0000c0c0c04a0703455441d028200203100580c0203001410312007a0008002000c1d0207000c208520301c0c0c4200301155503041030f07040d4400e050308150060059001c1000f48034940c102450b008034691103603621542c0d5440b00320784460410b42c0c250400d8010002161041ca016400040c907040c0042c0750f045554030180d0400700b41c1e400703c281290044d03200b100000500c500c85038003908000031820507241c40302da9940003c1d00c0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 784161555 1250 784160305 784160317
    0x10f1401090b120303040b060a05031b0f01090b0408150609040f020112110a02010e0d02010209092706090606091806060910080709020d0b04091509030302070b070c020a080f03 77
    0x501d665140103078a0740c1d100034400c83c4042114060303a0392801d05050042c184d1004554443c0a000c0b40000040c0e603050001e11600384458003501c1c1880c2101d004100040502d440325440d04010281402080b0304207440001c00040807a0401440b2002c0d651014074803100300107046900c0707030321b00d070f42004042519152281e0b562542440c203240014680003d640c000d04148041e0f0142400104150102540550084c55480001c0c030844039103e150784070480c240c0c440c086940d071304520310702d012030f452000b40381080101c804070820507444400c9045103d450b008049400f50346940c009400c0c81641c0c10210a440d0300003100c00c010760140105410a1591240050441401406541d00080000c2c40f00000000030b0060351060707034070059030740320a48065084004c12540240c0f51600c109203a1070540b0408402584c0000241d071a0301202040c00010400044180e0900d60204800c00020b171074400f0b918852400d0341c44007a0384140500500c800c00071141c02200156010f4141401c0c8500700005030383c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 784162805 1250 784161555 784161569
    0xa020a02030c010c020a06030b01051201031a0c030c0a0305060a08030307090617150f240408060c0a2703050a0c03050c090c160c0302190602060c0a0c06050a0207150509010f1401 78
    0x1103882c502780040303c01c2c0c801d5a80c51010090304074008000c000e00d0b88404a01180740001c181d161713446180c146142d40c401500c003104800420001e83c07500310300a420450f482207000340025001550350800700d007154403c0729940009000600c00340845030b0480341d0100c454081c10310480c064a0494090f280103410000901c3c4280d83d99520880244d0380c0d400c401c6844595094800d41c2c44840c4070b0340e0619a0814010103041e07003c0d107000030301003805030010703034860341100c0c0d4071080c0c450508416401402700200200003034601588000c40031030000c01005400d24411103200101902d103042407030515651030a454410104c240610980e40790b04801c1e180341c0c4107542801240c004561600414801a951000b034100030320700038085c900480a200081202c1164013614402d6a032440307054094441d014030300012517102c10a102c0400d00c16801315500c64403c8a0041c5801c80310348890720510551560018690303183d80070004001020700449040103044607040c030a01010840303828511005010f031803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 784164055 1250 784162805 784162811
    0x190501121113080601090b060c0c10021510060e06030f070e030c03070e10080703050322050415061803110d030915030f11030601052a030a020a02030c010c020a0603 72
    0x1625035419403040b10300140038000d5902e0099610f40c035241c0c0390402480b41d142042d242c00c03082138140c24088100c3d4201e04d00540a4194520f190081010240f14050312508501c2503024000c9143ca00b6403403140600c10980c0d015015500d0443d000b4440745007207041c940141400d106100d0045c0e240c070b1071203400c1a20740c00e01c110504415000300317251007840510315602d440780c9040014118420008a8001c5458400041a0503224a600b50f0b031106944001040e0340e2040060800c5040c4078000c0c001c009012481101c0f0140d82d4100050940e2690005203c0704a0307451810030540d9001241c0c0241c4080090103105481e01d180c90f0454641001003096010311500e0440c0300c101072003031421202400345d10b43c08654081c82d4101c01401046440307202841030380380c00c140d00c00b01c2a0360400d0b02e2168105a403001d14000100c11030360800c8204049200010341c106c010003410840900151000c246035500070f0640a90302e00406240c40210030741103041c8204240260f0168481e14075100a550242c01c000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 784165305 1250 784164055 784164071
    0x60a030b07032004060302070b06064e0702060702010507050708090a0e13050c01090e0645130f0b04290712050c0d0b0a0b040b0919050112 61
    0x83c000700302c0c48034018103104002034040383d4190554040d001450161142918a07640c0d00184903051007201800e060515414030b150410549600c01180d00e0000040d100a20448a0304c0803809421440046001c1c845c4450800c42900d5040081c50b90001842c40244090704000c0005011031046040103410318a001038030110310346a0341c06401c0103082d400310000540c60310501d2031540c0b0046100845660140c1340c40342d800c540c030401c0303003c09032004400c03403100320307101d041c01c000d0411504407a52243c18100d406d030301040c0c4030312882c0310b170180307a10103040c000503d1100307802040a13402085c44a00d540d10600a1010a04c0d800e4080b6140f6030004e0321410030384560070000c010142503103560014510100c0c5045000e612485018000c000c03c0d10f50f10344903012012010306584c4103c9500404503401d112062400080742c100701c035010405800f2007e840c1d20303140e1500e4036502c0743e003002880e07030300020ba11041c5081c000f0611500501d40e40703118030114141800241054610a50506015118411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 784166555 1250 784165305 784165331
    0x6111c0801060e060403211215050405041118090c01030e0c0402030403090b030405030702040c0206060117071112030f0c04060c03080709051e031e10020703020a0c0e010e060a030b0703 81
    0x325006181c00c42e00c52504014001e40c40e4084042c02c0116000051225044103908c49003030040d01c01900f0071a00060300c2a0a00082c88014a0010420364000c00b98014611103a100c00c444d00b41281c48070b0322400c10f9440c1c028001d5140840071a402c504041c42e1512150000402080f00d141003041200e0150380e035190f90a00300c6620415401c0740484910010502003003000000040c08058801d80d002c2c45003403040502682c681204a0380d0502080c606c4c8030b044802a0103031507155000c805801c007450444070960481d440c140d411224500f0028002041c070050001c00402e4652150b00c520b41207140504204004003109070b100301c01000d0080b148082400140500c84100c05003001a0900d00420007960b0084000d0056840c40d0f030080c020368140ba0402c165904110342404803113402460400c03413841c0010000d51003020103030114051740c3c03030075000207020742d03070841c020544070000c80300300d50401000e1a041d10740588030f580700d1166040100006000030f000107038003522504001440326441c0380 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 784167805 1250 784166555 784166557
    0xd05070504030506070e04060f210312140a0f0e1203100b0309060412020706140717040b03040605010504150e1008011d120f0f0f040b0406111c0801060e06 68
    0x8010401e015100c1009171042c0d01184405500c1002c46040c00030958556030213000003407034055868039000c6d48100794074005002d028400395070312a00d0082000c0c4000c0316414100c402d010380109540c50b24a00b4406000018014901d0343c01540c5c3c0c04102c04084c91340d5556480010400d40300482c080800046d0a089d01501c2603002808880b58650b42c0c0d1400b200041d0715000100e408954a03070352004060185c9200040042c1501d40c2d0340c6890481c0d500310300880910346c0106804451a00202141e00c85034407078031000e00f0003004600c44c8240c0740d0405240544c00c3d1001600198011807821592016003a4224443d00440d10746480045094440c08240303413170401150000c1c00c45600b07040c0d4036454034a00420303030444000300205541c0d106481134032400303d921070000c07c001059130a000f01100c0b010300c4402002d890440214081c60030341d030f402c00c903412904103a0054000c5079580110b50410542882030800f03107001010146035022604070050300000d410f0050504000c9488a61184c9480d014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 784169055 1250 784167805 784167809
    0x1201120c08150f0f06060313050705041802030f160b211609080a080f03090316241b050306040e0109062301032d061427030d05070504 59
    0x1401e48034551200340710311403081d5040d03d440c107042c0e0041c00043d07034034602c1000740d0307001d950000c00311851078492028200b021221080280c54034020000001100e03511481508040750700c120291442e141a40101424403c804030040307946d4006100c825821600c40c2c0f0200292000084a2030722036481c2c000d40038014626400d20803503000e81d0bc05200d0b4600d00d40703180c2da040302480c0c0d40d0000d03801d440e02c450300c3d20359a010000030304a2500b885903840a41056001e075900a00560840b42440400c151020300f0309031480003581c5a143c050004006100f5048003016100d502400503c040e0b500d003103400b402c90070f800409104010002c0007088290341c50380c01961303003c0c244000902a40c00070f810f003a0002c01d01101144001c401c0c103440d0200700f003030342003442e4100c0350031550183d0030160108004031021081c0c40403580c44002004c0c8000003c1041c0308031000d03c2c80a840d13941c158a00381c0303042c062620350750b0756084014122039181010000000100d4030001c00300c02d4041a0f90b1255070303081c0c6c1c180c050b0b6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 784170305 1250 784169055 784169069
    0x207330e030607030605090601050a1b0f3c0203210405041103060a21060e0c0d060212070228080d020307020a060506060909040201050a090b04060906030e031201120c 73
    0x9000d0220f000c0d8150420f80075103c00715884441916943d00544440c480d0084001c041030b000103042000c5000b51010f4241c0501030400d43c996400c1640c0c03005102c02450400c48003403003d03800c5017145a101c180300e030344410403480d00c0d095012034142c0000e41e03202005003030121500009207003030729030000c1c2e00c1c1a90028034003e4014000306540d09051100d94000b2503110340a1000403900041c0e02e1950315880190780061241280d0901c812788403030029000d04d039400d5a4034807490b039070400242c5802480f044068003030400141c40d160f0a100c4070314010400340c6081e08551000c0107020b400b0980f05c0104100525a48142d80580264a0203800e18024040040b0010380301108100e005c1e80c0101d00c002e00d052040708204001d40d00c68040129a029403080e851700841848001001035026074001d144480b080d050000c21a079517906052072641c05600940c000401e071080c10800c140d014000d03840d101d6091005141004400d01d104441804140304031485090021049024030008010201c0a0101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 784171555 1250 784170305 784170313
    0xf050607081305030601091e1116061b27060807200d1e03050c18030102070203010603050d0f170c09060d0203010b3609070509030a050d0207330e03 65
    0x5514001300090191801a5901200700708400c07080030352303610a107201000100c40082c2000036020007035194880c00e12007202e900340d03100d0b400e802011640c0c00110030310101d41e58000788443d01c80e9400b420f90946840203454401560010b2040c250082d40c43c83e88490186003d906003591542003d007002155140c031811801624680400c1c0381e071029855032400110f098404485a07034075011011690b04070380c440002441031100090451080312103445200c00100090308180b00c5e50006421500d281d481124282e201e82030390586107420005030004003000d41010314110016507455203d505004040402150700059030b070303000f90703a01010703036149081e41c0400f10b46941c1c55240040c510b920030201c091b114488903098800064425a250304002c0000c500006d100c1c1005060000008001c0c0510080c000140662112078404228000815010301d00800f0300c0d44030130074040d04082083c0c203d100019982811041600003217404a03468010902d802444034a00c2d00080360340b40c62662905515011b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 784172661 1106 784171555 784171559
    0x50105060f040e07200d0206150d020f1906080702100908181f03020918010e01120f080a0c120306150c050c09040b090105010f050607081305030601 65
    0x2c40741890558805d914051804007000c401c5084c4c003952050044c1e1701c1d0503904000d129000002101a011010300c2d09000c90f0200c03203907c001030f0080c3c0d401c5100000341d07114401c40c040702c0100076010a21280d183c4400500310074003503c100340140300388805101607130721600c901d0b00d80f20307804000d803481c1441e8252118883c00300682c4042e8450902c803c0030315061407610148010f42800e0f40e0059440e00740c4003c004100c03505030700040394400c070031005000a00f1200446415102c41604c1041410014a040a5003c0e1885002815100c0126020520780d40040c0c20034402c41c4114507000f040038108100720304031080d510444c112400e5403080d40080340d0140e00c109000e00c0c0644c0564001e198540045900c40400f03039012100000000b0070086008001e204240c050300140c64000c14903880c00000031280d0040d140c1c05800e1813030000d0b1a02e07501d0340b8011910000c007130140030740d0440d60b = true := by decide +kernel

theorem cover : BRFrame.Cov 783992805 784172661 := by
  have h0 := BRFrame.cov_init 783992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 783992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 783992805 ≤ n) (h2 : n < 784172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
