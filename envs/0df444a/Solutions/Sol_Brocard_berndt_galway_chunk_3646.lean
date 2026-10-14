-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3646
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:29.396919+00:00
-- url     : https://prove2.me/submissions/f7d5b066-d134-4857-828b-cfd3a360711a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 655575539 ≤ n < 655755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 655576789 1250 655575539 655575541
    0x40c150201150b030c0403083907060f05040b212701020a12050702210c061006020a03081f0f053a0212030a11121801030f0b0306 57
    0x2401a00900001c2007603165082e85180c0000c4501e0f040d01141d20450303000c0481403c00e440e55072440c1d040d4000700b40c1b01c02d5112401d041c070b49207041c000304612805036018000510341c0b85c111895505000c26074008108010803500c80d500c880c1c0d08401101e04881c41404080da542003840c5030b0070045040020b030103841c0395402c0107104410640c1c044a01c00c0e488150443e0042500843e002402c0b03200308911040440e002e01b21010b0340140c0d65000742c1d44030380a4010f55500c1000d4411180e00c0180743b1414840501d00401c080316001010010103510001002030601c1c442d003020030103580d819505900070200140300d00010044083c400540e88910512841080101d41381c00210384111201d000342405640ca0b865101c0e1824141841404003041e40003042da107142d5078401211440b00384c032100743d80000b425194010000c1c3c0400c001c18098204c3e540d541041401d1113409801c044c682c214040b12901c0501032260600c2611b4100320110000b4200020351141c007a50000c081e00c06041c2c1142c0c0360040c80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 655578039 1250 655576789 655576829
    0xf0a0c0f0e13110310050a0801090b0a0203060423181f1509050702011a030a0c1a0f070b01150f0212031801020d0b032107060e01020903030d0e070b0f030f040c 70
    0x3505d055450131101c6078080e035211954075089401141c3c001d4009640000820000d040ca64002d54000360b01030700105840202600012101c0d01110000040d40300d00303020000b00c0d01500d0f000f01d02d8070440c04081d19a0480341b1a08070384405000b42e580c05055a640b11001b003440001070414010402404184540e1900c1d48000e8020003903c10360b1900608060704070132823880c001c00c05001565000c0314828859044c078426003121715004c0c80d5507030641c1c010403007000c0c08540c0702d003c2c08440d88030384641c070030941c100150922007100c204098000e109498007c1e401d659001304060060840035480203480c1d680342240b0320503540e10302c1c074804800e500c00a240200051540c2010001113001e0301114500060940421500e22030428010000541801070000060050300500340440700040098180102100003d05540c00900104481c0f941c4000300d082110007845000002c00c01480600e0400e110710490400c81c3c0310080007803101003007520004040015213840070000c0c001c095903e070460280c00f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 655579289 1250 655578039 655578061
    0x150f08030a0201060b03011503090543031a090c1309030f020c011d191d0f0402100c0c030501050a020405040e0a24020d050f0a0c0f0e131103 62
    0x1e00d01c0000650810754046101d5803600100c038102e4864400c11b400240168000b24000d015194088920b07000d8120900100c2d501da000344100f030b000142105542c070341d1180e20504010f030b04039141e070404041c100f02040801e00d0b00312030b4100c10303086200318a0712340e0b224060241001e0b60101d80359403028585c040c03061014515813010400b64880d0700e400364641d00c040c8c01680d5030a0002d159500141100300c908a80c0300d2014144a00200c000d80300103107a189080348100007051f2a0410800b10802100d9070069401070601e154008607000c03507120740ca0400c0d4000c20801401303122400b00b4480008541030810590140b0b400040d074014000708141d081014881e00603500500c9010b1185082090034640c10a020410250160340070b1000d0855414141201e590541049001e403555607080c03110000a6145001b42445000044084642440c0c101c40d008221000356038820304005a48010444098000d03003c1995404100c0d4031015400c050917044001c0d007400c0101c40150b01012041c4201e041d10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 655580539 1250 655579289 655579297
    0x1003020d05060a18020c0f012a030212040209070e0d05030c070608010e010e10030807121b0b1b09180402010e03060910090309090e0705010801090c050d150f0803 71
    0x103088091180e0380302c1c103040050300041030040e803003030b2103500d84040c0e483d220640c01401000c1c0818150364040e004000d140d42100c07100c04c402e03240383c040c8081c2120180c50805541c40a5586400c085050a10018184081c1c074001030000340521080c3d40810183c42c058408a20302c2480104894001d040300e1510070346079044072980a60610501c1d0b00865140d000302d0400e416900350600c900d416070700c5d00d030040782182001b810300000300d40d8030310f0701001041ca00b400074941035000b980d108010084040000b0b06138a503074000f500500c00d0700c1d40345000007583c80403000c0e005100220482d502005034000d00406200b00a40e041d408516440401d00d250f1000a665203c1c9000b42c98003c03102120005058a0310700485541c00300d40c02c4544a074001c507440f68440c050704c901900d4044410354840345100100c1c0c1041c031240d0b407980d2210504009643e4402d02c3e16000d8079140400b8814072200900151443c024502c0025841c2d8072180004d00070600d80c4101002070141c2503003010300503680c04c01286c40fa80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 655581789 1250 655580539 655580557
    0x2090406091d06101d0a0b090405011e020a0e010c03270305010501170715020a02100305061e0105070204020d0b040207030519020c010905120f06090705030c19050618100302 76
    0x1620001861319013003522400121403c861200c0d000340b42c0f050001a0122000305050748190baa103404030749a450b000100e81c8510f100b03000001d001610016124155038503500c06010f190b004001c401c2190b944441c041c0c00d44031080c246040c582e00d407482c003920300c68040390680181040c0c0034110850f0301d5003803110380210703800384000704a26600c4000c100e40381c41d5007104207a000d9010f054100300c0c0780d0400c140c110640a051042c1c07803210380c555002641d440c041103038030000281c40f901884030514010381c0c40c1032050008101c002e1940305503000a05140904038000c0d11440c0d010540344a800210b4000e2444264014401c542d140040d260151441e00480e4851030121112840381140d5400011000c1d0050016103030301d247c5624080c20001c5909200480100c03902400034200c0c03003103408000b0f26000b4094103020b007400e50306220600d031802c07400b404094460015074480100480d000100b84060740e0054650b5a41d8410120010310842c565065460b003080e070303010b0741d0100c03a545603000c0d00c00e0718 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 655583039 1250 655581789 655581793
    0x30c070302090112170a09030b250c21050c0109050a0c06050c0604020409060b1f0f090f1502031207182903090f1e070602070f0902090406091d 63
    0x80d0321000e51342c80d45044400000e1990894031a0b82862455000103000120032924011204a40f81e549050f0300c0d4509a80c2104210301d0f1100c40c1d82e80345410200d030101c45a580c584042c04241e180c48482002d12080500300781e2500107425a60740c03070b100304101c0c2c080d182050000d0192000a1400039070740c04491805030b40e003010503a000700360980300f87e08440d50584c003400103010720f072965001c210007805045e10850b5440ea40301c07204500394441110b05880401ea8a0880300003600c0c000025007041d0381203098074100000e54070240810820311907075a00342c41c0b072868403442607400e40c43c09074503500c522104410110045020000a141e0140b032200004030f16040c1004050394644516540501030740301d5034000b600300314550b031201300340c440030f140c1c484c5200301101c40420514070b445050003a0b1064606184100c5e640d28013018100f00000d5008125603c010700c80c0511348500d091214460340a2260241c0c0c0020700040b040c1c0d83c580090010b0420b060041006428900c01c080c074109030341c1c001105034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 655584289 1250 655583039 655583041
    0x303070e09070210020a030b0d05010f1803021e070e0c03091c020307260d0209150301120f0c0b1c110c03090105070f05060711070806160f11030c07030209 68
    0x181c2000d6401e0350244510b41c009140741030340d80344868069013204000000705956600b16a42c1661144030541204e40504000100b2410140c0400240c4d40c101d02110180002000c480e40041d42c00a103039420210710000e080c1044408405450030010980e100b00b01d032198040a000044500c400258040d45140b000c4403120844103140305003227000e003216840036800c00d0003000c0105001481c1a4501a103121502200d260300000700034031a00501c4a81e03004c0366001c503c8401c00e090aa10518400d0305d8100301505542c0740c0703500140740d020451402845031a0a000701c108102d40d041034031010f060f088103065111002c0300c00748006601007045640849040c2506038440300c1c1c540d000c0300c10041104020318600b4408400640c0c0d0b580c8054421100420440d0380c0c10041348051006900540306940c4850100c502d41140a2610304150000781035a007020041c000030213800c5440d602040001d040007041c01c1040782d02034821a200703610591941c0000291603114410116259003928030841d00300000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 655585539 1250 655584289 655584317
    0x2e060312090e1b0703080601031e0603021503011202100e0a030b0717010b090114040306020a030204030c0807150305090c090403020d020d080c03072d2d12051b0408030307 75
    0x8551510f4001e2032184204401004079206868013a40314806040c081342c841c000d030f940140c0d400340842901020307541d10303d000c0c421403a000384801ea1191003d0780150455042403107001c0c8c20f120f179440080c0b0500c00b600c40420140c0c01903616404101c00101000021a80c07070801400c08d62084946500282402101182c01c094004c02a0b05031800e109025040c0403500d0019038a400741080510400380701032000000250442c0000c006c100d200740d0300035031610b185160800588100c4e41240080703403c07441e02071004078440381c10010001ca09103404101e5880309140740782000402018103401c441090300708001e058000a0841507140c90ba030803a03105010801c0100d6810100703461030103170110100089207005200d0001081c90407103c410013a840d50b000380e20200500d5241c580c820120301d01d0800d086d801000d51b08440d0007152400b80d41210714400b0400100039031064440c0d02c80081e40e803000300700d84420603001d00d1501d11f4064805075076552960035441e0381f50001c81d40003000032298014240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 655586789 1250 655585539 655585561
    0x8030f06030307030f0e06160507140303040e070318050d020d1404050901030b04030201020c2a010504030803040201110304082406120d0f02011b0f0306082e060312090e 74
    0x25243d1380503a1840c101c540e9003001152142d0008546583c0014244004d9200306201d03105030020078400c0c0020003025140c01d014110046040d10858400c1d0028001004051045100f040d48011a89000260107542d10160040f1203880a00130b8101c0c82413607003400006030001003c000c0045c003601c448140340c03100300400305a881680a00c1380c01071401c0780108000b03a0401e446540180c401d00003d4100046803141e01d02d419840050341c00c00c1d11000481000c0701ea401e406000103001c2c00e107801031906046803140702c100c0c8000303400241042110f030740588205d5414010765001d040d8002c10340302d07100d494160f4949c1c080f0f400c40440108041d0b41c00031405034a03100d500c5190208203035014021441c03501906441003070940c4000c4c000d6540f901022980f4000c4c1b401c0c0c8100c408810345504200c1d081c0e03094001d01302c130301e140c024501603485001510a401004204c40c80d40100c81007114910003440001078001c0c0170070340d000910300384481206001c2da82d00440341d0005d850030402101030907940e10300062 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 655588039 1250 655586789 655586797
    0x31a0406050f040f020f1207080a20090109270b040603050a1401060504060b0c01050f0907050d03030902062b0b011d2e020705010e030c0d05070e0408030f060303 71
    0x15804000c0b00940d55041c00e01d07804c0080c4d0062003910042c2001d89420f19a0001e52104000c0c890300c044280c1000700a50700849440e81001c00c07030034100008101020244949004603068000411010503600781c280e1058510202500901400f041e64102e210300d220a0b400c0e02e01c030303a03d44c070b9420f0020302280c03030034513201d408112500301009020360315a45c1c4075100704480e5051182c4195403a942c000ca030986950045400511000303010075581d240c0080b070319084440113011450006002002e000313139000002502000d403802140d101025241d281b400b5002002030a0000f50044000305a50071070209107440c0c903035010140c84662269206248160301240c91010300075001c02c440901c05c3c2512444526411000c0d54007400d940e0440800c10301d02001e100000d0003406480542e40c070004007090781484840000d200a0070300c0036004510300c0c00240c0310800c4410703c502a212218001060000c01c10001008100164410402d8102420b141202d9802240c1600040c24003501203000750500004036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 655589289 1250 655588039 655588049
    0x60b0903030f09060c011e0b0d020d08130e010f090b0901081011090d060509010b100e042703020f071a0304060c050d0c02150c040617061c03031a0406 66
    0x1d1468406048044600350300a116041d400200c03d0044000f6402d003442400d094003140d40030301c000c007607102c00c0c0e0794180c0c1d07060b241c0340b801603440d10083c00044e11107405408103264404d5000c0c0d11121501029454800d496009175503103050980001400006000c00c2410354513890410321025100d0701c2801000c0b10207110b102030310742c44501044510b80c46076005440118622540034070380304c003000004618101540003980e0441c2e596041c030182c40000d00c20760b00140c0c001d803124040c4514405010700300d40c09003084a80103a4454142207000c0c2c005803401c0d80310284000c1c9501c841b5481d800c000b59500d03003a4010f1201446110404918100840b4007850f5441d0f03038030070851640d41d45560f06000b425085d0840c1003482414449405d0500b00c50280d200f04502942c0240503e80f40000411440032002c0c003004840f0030108018022182e12030b041c81c07200c650322403181d5101c0d1500f001007242704203140c46544c0352003078044c1894101540341d0842e00008101904103009a0314020420007111521302c11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 655590539 1250 655589289 655589293
    0x11280f1a040b0f0c030d0e0c0f0906031b03030d0612030f090b030a0f0603050712150207020f010807090e1603050a0519180209012c090d08090c031f060b0903 69
    0x1039401d1a4450f0b01c010036444031082d054a060a03031001c01e400a0300d08249003501250001100c500309800d010f00d54184811088892090f141001400703e526032802000c00440340c1e19031829079505131010411114440c164000812100e955001079400040205000710001860741c070b00d0341c00d03261003260204161006120300900d9a1540c0e60028020704400030481403950702d501e000000329506103d80d4004190a00031801c0009040c0b40c004500d200d070042d00109180706012401c00358540000310b41e1004400c0c20180c2840d02c4e2290141da400ba526400f14040741c0050003085525005014210300030388854038140b0098480d51501015180104c42d60a21050001103c03040a40245c104c0d010b081080300704403114035000c0c4c010403a008002d801030451081d41000280c140741104181e0712007445401c04e85089414021050f0b52518803006000c02000440d001095840005204200f1071b080002c084030300e6080b00d00038020001011204581155182000018408803014101c170b0759050f000340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 655591789 1250 655590539 655590547
    0x3060a02030910050402013c050a09081f0b0a09050c21090c01030f0f060b30040204020f0c011406041a0603010b03220b090d0c11280f1a040b 62
    0x241c001041985090b9040024024050b03014002400044003402c400149e51740c02d41e2204400c50140c17080416038131111007680400351410054110045030b8841c09149a404100c2c90b9110000511212030740d000a400145007105125020740c10800070a000310b0b04d40d507854002540d03144140511007044481c10499005244000f54540c40303540203030810302c0015000a01e00701c00c0c45c843c10458a040c1c210000e070360b50001c2c1440b10700c454852142401006c50340e44c0c203842403a8120b5003440b1074000d08024000d0360003007440200d031400602940d4900100320000c011200100304c22078808002666041d010700e140542c0e0000c048800c1407488131800d00a03000c5480d59280071000805580300402044200710403001840e5030040485028a503a405969411298208a072406042001541041045c0002c2034409000998111000e2309000006ca4400405410360980c105190000519182542000c0540455041d00041c078442c1500c0b0710440c00e04e03030498001402003640c0304070f0180c80300604040c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 655593039 1250 655591789 655591817
    0x8030703060501030b0402122e0e010f0803160602092205150907020d080a0b092a04050109170a0819020105060301140f130204020f040618210206070203060a0203091005040201 77
    0x710000800ca80381c3c01c400106490358004180000c0c9e203940040e14100307240001000786501108920f030140c100180a189409000254500310076402100140f04d00d4020903505140c0e50b8400400c000c1c180440d420700140d58121882070003c01c41100c40040e1404080191040c03401d08941d014400d260640043c00b504801c3c0c201540d03c00002410b141c0314548880c100111034803103540007030141d480302005003071400e4089196000b0b0411825005100348050004001d16079100c0702100481d6103a421a90b00d0365108024141495007081014003003a400040a0800c061803e0028503040003130382c002c00160703c80310304240c240c601c0129030f108035148083c00302e901c1c4482c498550782c105144500002c80900c0d154089426a0029851881c1d40440400e0412010360800d201410f0341100d1043c1c00202070500744005d580210048600841034440c03070024045403219011202c44980003000c880c550b1030b00c2e10b80d00029600444415859015902ca5425024000d0184c14021541612500c500100f15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 655594289 1250 655593039 655593061
    0x1d0105060a050d15020a0f121505060a11070807050f1e040c0903140c090f06030a06020c01020f04080115240c02180403020114010611030d150308030703060501030b040212 75
    0xf032001d4440c415019807800c890742c0741c1d1000780541d8103e5140c1001d00100540c02900c140c0210362030100c00ca08164103003c8901c0745d2010003055901c12948907481e050143d10494401a000740d040b0054800d19001049240d0001030303a03011210304869041702d0401007000d00840070050400c00f10f200600344514003403440c25810000c00c03c445441c00070f00f4a82d90362501101142010884400c5400c82a040300150920030301003544200c20403100a0641070100c0884e0b40e4149480c405089a6404030f81025502000c0d01220840b00c104c82146496540b28007002d4000c01d21070a840403030340044400041c405a8244c05c6514606156402a03c090026142a00d007010100c00032607110400d1881a081c2044850709603000d540070703a000060416404c44003101280e41a041507040c0a1840c05542c00c4a01c0007003260030039400040c000c80c51038000c8189604004503600000d060aa020040110995159226904640c0240d0b02032246d000088107210807880381a1209007843e4031900000c41c440c482c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 655595539 1250 655594289 655594309
    0xd08060307151209111008091e2a060705070f0807050109060f02120d0507081b0406032301030305030a0f0c05030402040213050a09140c0a0207030201081f06031d0105060a05 76
    0x18640e10708004d6a044c5c00200750f08058584c10303000c031b2006420300001c00001c0114405034110440c580b40d410501e10f030900d50b01c8035142000038001805084462540452140307082e51340201038003140e1903940c2c1c0d00d00b2540710003190040c2036808404200004000b400000c541d800c486043e1288039046042840882d0343e90304207100c00b419881100f1150001c0203483c0028110340101c10b6001882d4140b9820083c0000405000070184031a0580610034142444040342c00711281c5003800681c160f20100744182c00026220740210003522200000305041e0804002d600c14512081d04114400d080300815085410300c016400c0011020300c001401820942d0040950301c2d041000c02c0c400c0381c0e81780c0020301800c86607000182d2498940040d1100d40846643c01c81c1c0007109509054104640084000e41da03174aa40b00c0a030400c1034800c04291642c5e036071300c0103011009000030400070240c0c0740c10001d00a03180400c403422030ba202108410001c0d86040c42494081c0074001d10307140170745152004000310084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 655596789 1250 655595539 655595543
    0x10b0a020c030d09090f060605160c0503150103051e060f0a0213060509010f03110928030c050a050306090c0f040b06040909030e030607080c1303050d08060307151209 73
    0xc14904400310581c2c0800149421034460b41c0e5040309107003081e480c40161040550031160180c00c220042c0101e81d04201510600045080d030f070300d00d07940381e03040c880940601503021703607091b0081400003581e41e200b034080380c0c2c1a20301680449455060441072406000e0f10f5003d0440381c1e8020f0000f0501a8401c1906140c210604c20009170800c1000840c0c604071110a074400c3c0041040000c0c40026540c200130050900d0600c0c0c1410080ca046005098406121781c98a8911541c5240c40300c1600340790050441138881094412100030644a15210f485200036006041c4202801407002940e4500042d485110b8041980506805484e80c018000103402c0c402115500c16240c01401c41c0b0f6450340d4003d80001c00480b400801c480c08c0600b0041d0100342502c041c580240c00c4841003144140d0072000c0303990080e080e40b9000f039943c1071034050407982e404e050704001c142e402144002000a0f51084503980103420450503210310705d55a2035040550000d101e59a40450040905821b5182d82d6031f225400d054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 655598039 1250 655596789 655596793
    0x2030316090b0d0e0f0f100c03060b0f2d1b03091504090f0225020a09020313150204060905220c0815041a0f030c0306070f0224010b0a02 60
    0xe8070360540300c00300d40142da20f219881340c3c1c8078015003041c3c0b0200924100c11600b2805000b003020205a020f80368015901c00c2c219481d212007881c968540b0981c0007400816107000d0b4240c840607101d51118148d80702944801c06043c50340c1c0ca140240b0411a030b4151099241c0d0807292806011082e0041c100c6482144140c2c1c1d4001809046030644a0340c4522001c1d860b1804101d644a041c58100f508480d203d5100400085c814090250200e1201142204280b41166941d0441c4c1c2e40f48002007044030030707800001265001205021412500c2c941031500e261082d0700000d280f0b4045085d0074200d00403445184001001c0c49070401070340c140304d50040d45404410300703440102480350b4100c80c1603031401c10511000074060410050f100ba60551500c4901d44102c5040c00384250a00b004520302c01c6003041a840b038807660402032410780e030030480c58508071400f41c01d5a5039403030079007406050120308001d420058000d000c034100141300413108094818014605001c000d90808100c4842a040030124500394 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 655599289 1250 655598039 655598057
    0xa0b12010c0302040302190303080f0903070c032103090c051e0a06080415090b0708060118060801050a0906030506041e0b0103150c030b0d061e0f0209180702030316 72
    0x626000c0c0141d100c020141c0d00d0160b521844c2d0302c1030007003494000800d15410441380605100213980300300c1450b0841c0031484035810607140d4080d50b070704510910800800d141c020450020402004411940d40010217490505e901c4410302800c1e01581c600100040a80d41c040c4000e2049240056400e1503424005003042181e4a0100215415403429008a004100d0f0070041100304010b00b8070b000c0a03403840b20028042e0311304030703644c2c040a18400f4020380180252100068410b03445013141e500b545507900391915500e0390f201005000880d0038050b19020345a004004a000c51060245104895000c00100940d5480e6201c00b01c13820413200c8181d85e24006c5640381c42c041031607410b909020714090720910380342c0301d10100d00d2801c035204908407034141400c105801e141c1c0d0341e624520400386600040046034102c403c0d051003010485020120600320b1401c1c41c42e5032002c0040d0301805a10344241d510a100ca2050381258802010840700400141d000700000745a50020300d01583e021451400c09101c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 655600539 1250 655599289 655599319
    0xc080d08160f0e09280f05010611070603110c1c0908030a020601030b041707060506130b010e09040203010e160315060f03061109090103080307020c090121050c0904030c0303060b0f030a0b 82
    0x3c05010000c40809560b20341c51140c1c41c06d200d40c4100d5005141c0f40c14140d110640030090103480e030392140714601c2816510740d01250034812090440710100a0700d815155403240589103501e14a8494061100040041c080401c540c2d43c00030858a2603c8240c004080d203078a180c1c0c07285810783c2e0040c070440d40981d02c0c240e90183c01d4004009858030070300c1001c0101d002e161010501526404107041e100119040440001843e600b10310500310400043c0d408800550752030000c03a0160a2807286048248038511204458040b02d4414030143c82c8211340c40c1d85c01c2d50250320b1150035542c050041e0366005549210800001c0c02903400321225562030300015051180410000b210148241d1056032400da00004201c8250781c14064010312403412288a001d6504004240b26013660300602c0700314102844100c2d20a011081104940c1d141000300031003038615161400034071701d802c44401180843e043c00d00104000da002d1b03003a00c5140b12104016401c643d40d205611011b4a5411449500001400841c243c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 655601789 1250 655600539 655600591
    0xa090e070f08070602280206090102010b210c030d1403070e03101d06070504050613030209042301060803030a0c0314010e10050a05060f070c080d08160f0e09 69
    0x30007410301c034014102c004c0c03038801d01034101203614892400903e404010141003201215002c1d45440d0141c840c5501c0e00007a0300140d0040030300801441d82720300d1044c802440300e611401d010200032002c030103a841034000c06080c1030b1384641c20203080380802c2b546009900c0d5501244080c42e44a10a89030a50051102801180c03e04c08100042035450342c5510440c03100032245040c43e0442c100f54002419145000f0fa0010070380e0041d8090184034200004d11a02c19400101c1484007543d002401070301c01c2e08091400340d01c01c6803004c800500c181000c0041c07280140040c4180e41c11076a034031000d50f1540e13481140100040070080303402028181e5580c00b100a0403202a001c40c0601480c2007024043d0408a044c502d458841d9808248580304650050001c0e0301d0b10400c6d100440e1500d071086858000c0307841c03d10341d00c80e810b410a9071644180e150703403038100743d0100f00c05024400b40301104e09041203000c03088411510401d03000d0085040d5690710300c003c1c00c09044041d401f03590907590b24440c20130581041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 655603039 1250 655601789 655601819
    0x90a03030b1c11011d010e090a1d0c0306070507030801050f120f0f120903030405090406320717040b09030d29030a15090309120308040c0b090a090e07 66
    0x26030054100c6030100b40135600b00041c04902e00480f80c20f01490303902840000c00c103007050031140d40168811004a0030b0a131503034009090030502008104208800381030305560740c5000052192092040c0400f090241d80900308941c0107903015519850543c2c00c1c50300f4010300780203c0b1100d6400403000e1300c503010401300c10310050a052015001600c2d0b403101c007000292030010120110603507080c0400c80c0a0050303a00204a80840e2016100800c160341c40742010f070010045c11a2009882070880d01d052f90380889003040540302400042035610646641da4100c400360201e4421140050f207000102d0041040800c0d200e0b4002c0e404405c89290062040d101c5050b19141c80c032400c44040360300340003000401840c00e483c081ca81c0580c011b1101c1502515180c000704003030040c03001150750b41c0c2440014503105101d514040e010308800c5150748800c9143c0207044100c102c80c02d644150100381c000c43c4906048003100c001a03030041416800c01d0501032400e0042c00958115441072080020006101c09030207144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 655604289 1250 655603039 655603043
    0x30a030c05190215010602122b1401061404030c060833120303070c0807052a03100b0907050922021209030703091503020d1104050103060608090a03030b1c 68
    0x151440b010318102140c2070980c186c01070300c207540003070519401302d0403c9400c0e89d030701c1c540715000b030301c61100c111940308a2000d298061462542c1003080b070250441408a10324100c501d180c1d00c91600c11b500c81110b81041c0994000181f03509441c80301004802c1c0f29000054004010b0190540c03801081d240084a01d0308429400c50390201c2c41c0c0e403064480c0362151900c2d810a8500c40a149149040ca10090081207000001400d84c4400300340791060010800003501004400c411000140407003084c0c10750005500e518051092040a81c200e0b156560f43c0220402e910303014184030002d40710100c0c15502c5400443d1507940011368185514952085040718480f20800c0d030070300603a281008960030302d40200041101d0781c180c0c0100081d1001030340c450503150841c2c554148010281c0c2c054070741113000e4800c001a440501d420800c4411052004a000f007044580980301000541e90300c11050703852410880b050f80362074020300c1f000004030b8001c0c2c00c0801c01c02c0d4004d0046400c9621540300040c649400c03081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 655605539 1250 655604289 655604293
    0xc090a06120b06070b01120f0c060e0406090e120c0a06051608061801230301050406060807120b01050d051203070507050106140907110106050d05030d0f020408030a030c051902 77
    0x1407985a100310720940307280300e20940b4243c0c501100c40c0c0710640d80d42c50610605504200100011007400000f801c05e0a89680c8110800240703960361000501c10a0182e0b0000e1141c0d10b0000300040d03400383d81c03041c0455204801c0150080b40114640100e198010758480000780c09920407000000b12980b0a0620503085070a5059030046417110040c00c902c4000c240a004050404420b90608400f50600d41103500320203c2030b90400c0407580c1031311040303000809540c042d82803009220400c11990000d00130394500c0001c84007400c4d0740f00000d04036050622400b8000140030001840f882c1002211410480d015404441820795440d201d29015401264081d0010700017250f03c0040180a0041c0002000945280d1109120802c0001c10f842c81c09050303407052004c0340c500108405801e40000c401131100a141400250a81c1041512035200310121030445190462502c080d81032403013514161015000110705107040740c44d0a80091494429860138010302307101d4000d0074900c00d10707407034030a60047c1c2c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 655606789 1250 655605539 655605557
    0x1208040602250b06030d09030f0305160503120c0a09060309260d0b04020f160218010609091121040c0513020a110a1110090f0b09090124080c090a06 65
    0x24980c40c00320b0007a221314806e81041840c9440c42e0fa0101041c01902d41007416442c1f03090343d070301e07054403184140c00c00c50b04010080a8903506015010020700814103a0f00140051039695859a800398030414070000041100d207102408000d01c02e41c008807400e03104004c10350b9114800d4235980300b2011100e01618403a040041d90403c405414020283d50440c15901542007002c0084418945d0152103d04480c00324500e079264150754401c9038040c2400d400802000071541c40d1034000300300c540c6038000e4030b010a080c0b400355040c00303940501320340300007443e039441103d00120b000652241c00c9014009980407850f44002003516034a01803d0020450350131001030b0f0700c07130f6004d401900c88401241502e00503049805004045811001c10a1a016085a0607007001e1807182003a1a060056045500800e1030208041040900f00006003a074a00c01c90748040540e03601c0ba840381100694098060580c24050340140c0030740e018104182d00039080140c080d0416404502058243d4404e5225400041002c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 655608039 1250 655606789 655606793
    0x10c0501020f0306120105071202160c0b032d0a110f0d02040513150314030d020711010306051005040e0606040302180105011227060e03041d06010c120804060225 71
    0x400217115030100c01c2c0080c00140f501200150090a08202584c0c00940025034061440a4022840440c603030010340741a0003919a2002d15498200721100620300751400400c407071044a001c40b461030700d40101c2c401081551800321080c090008800c1c4180728030421700c10b41580c3c00300c0c0c10143c007944240c10700050301c89103843d08004880344525519203140b4540451901080390210300304094a400072100c482074a07240407181e2551048444039030001e40b021580b0001c01980d81e40751103200c80c090340c0500045488404111a01d201c0c0c010a00100b40704000c10030074084a2800e099000e0b500414150419960707401203240c51006c0305035064075041d41401881a503070064601000e00c8021801080105581070b4075001c00810980f5461041800812030010044640c2100c0055840031003583d8543d96691040b10b91060980380c881203a007011000103410b548100c1085082d00c1d08045003545441903618240c5c0e420b200030740251084d41d001c20501d906001180c4a40d028030041b804808400c00fa03074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 655609289 1250 655608039 655608049
    0x4061203080f1006050a030b0a080712050105060f01020a0b0a090f30020a0f0609080c1c0302090a050f0f04020a0e150a02030405090a2403051009031d010c0501020f0306 74
    0x103003e4802c0d02003402e4107000c1c9507805015640d115406042c001107602c00b90300003036003103042940030000c00c2c4190382c4085411420320026401c01e0740318a00910203a2901340400000c15200300303241d03005a1000b030300003002c1140300304160f420031103082c40001c0e00441600e4207000569000416030360712001d00918910100301780f40d14010022204441024014507000c029191103114001805249040c84404140b110035400b0000d560b60001903035540e030642001085e21400301031640d40c4002d00bc503840d401c249019000b25128888010b0001e81e03143e04110400c02c5080d100000031b6042a000d0340104070035111403004140c00c840d992924482c03000b502080104180100203d4604200d051101d802e20503000000e40c0c098410446030b1141c2030740d41c40b500074020551980c2d5a008245540c00340c0301079105400b28a002d4a01074005d03184401c0d5451022010390b0703440d00d4000c000030056034a030050800000d8001034400014034101d950b01045840b0786003680c01c807084410043c18008180801c1d03143c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 655610539 1250 655609289 655609291
    0x80c0319140919020a05042004030302070609080a0f061d01141b1201090e03160803040b070516030f020f010e010c1707020d081005060703170606121504061203080f 72
    0x110f40c01c200202030b030b40d40c041544402244070b607601441d00e0303401e08070780c00e0b000049010000812400c0903032030b20354070f04000355100d00520540c0301086e040701700842c0150000c1140030415400000024440c1040e40e1180010305d004100c17050120340d902c4550351450001c0c041c04c40c3c8050b0041142415041014060318045500d0a0341c10380c540040129084001c542c100e02411203d6042c000216540c6424440d0b0851007564050031900340d0b1a9194400c00c2000c03006140124003461a20440742d49444003910244a241c520004600380c195116000901c520030203140705040f4419116202c1c8604401401c1d0354246040817250394684541c8804254404055000092240c42d0031266081514000c0c1d25a16084124410450444009000030000202c140d00174040504841d948402c2d50900604c801e4050500550040e0600e0105000c2c0c42d1a0090302c0583d4a11a2900f80d5600c82540031400e0a541052054100d40c0b100000141c6581701245802030501945981c242c03851300207407203c50388174 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 655611789 1250 655610539 655610563
    0x30a1d031905043206032e08060c0c0f1005041505010501020a060b04021e0301180b06030a0911100201020c01050a0b030c0d0614040f2114160b0112030e10080c03191409 74
    0x11f03034504002c8210000340300d5401ca2411b04846a8135100114000c1c18403200e50318010f22481907204903010100654095031140f0700401c0441243c20500b8281030668200f0b10880740140c0c0010426070128140c2d1340203003241d00300100010314002910740038410f03a400c011000000440003100420000a03244400c01e04510426810405200c241c0009a00c0b404094142c40c0c9542d035542500f0100a0a444900c41c488401444000502c4407554001d000c0e62100304800250350034000881d4849000b801a00740c0c05070001c001e4400000124203005484a8108080e1b845545441840c81072001a0544501583c02201d11005c802020b051452645a0640e00800c402940c1a0351340c2007c1ea200380300800820710304a1072030703644040081003100301551800190040103040d0000581d90030714528940810301c03d442e10100a080c404c200020101c4604017038000c01d00d040300146403084030308002c1d5802500c001004085421081c944000c131114001000c1c400c803040420b0006561040200b404052 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 655613039 1250 655611789 655611871
    0x602011e020702180a02160b1501090602061605071a010f0f15031a090f070215090705090709030803070e01141c02030a1d03190504320603 61
    0xc070302d6901007840030f54100d02d000b041064503030110310206540c0e01154405039115030ba070710340b110113400c0080e0050703020740783c1d240304d1520984001d1a41d4018040401151055009806e02d9903500c20040d109411248084081080c00c00c00724002400981d201e0703c00f6228003150100307079814025000148003294011440c13001c0400410001114801099000050035180110350101c101040600c00b500c405c141551102a00c01041101b68102d242a44501440e0382203a00e54040000966494001551109603a410000003440a400c0c101c1c0045d030841050718000d601e2035925118604035800540340800001c50050ba01a520360b031203c3c80c01c40007a0801d100c10b01d07184500c103820108171001d1000c0f42600c0c1e00840024030100e4507502092600c94000070000d200a508400140c5035400310205403030b407440030804045420304c12025901600c4001d00419049001c0217600008103005011450007030b0082c19942105440d0b05029501840b00050049510074030702850b10240c0c031551290300000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 655614289 1250 655613039 655613047
    0xf06060e10030618060f05100504020702030a060e0304080303070206090c0a15030b01030b040f0e15040f0b0c040320010e01050a0c0803041104140f060f0d03050c010b0a0602011e02 79
    0x1070041154900c01c0341e80c01200003500360381400900c90088525903028000501e000d0480340103041a801c124030584000e4086104940c43e6810002280214100070350141d01c901040030004031240c0c8641420b02007541100c1c1001e0780c035510f09103107900440d12640180c004c17505000c108036041202595000c002c0352320140e22801c144c1e450b4684048031b030030300041540380c9a070504a0307401382e0300c111680800a0403c0c40350407410b08a140217810040c2a6480314440d002462410b10718449003a4041d690000c41403002d20002c0c3c45041e070071040500b640c40021000c200020005030209500200c141c2d0f0300488001c038030541320001d8040c40400302034506012041094880710b0707600200c01c2c4c02e103540c010708054598030346082421100c09543c81d115046890080320440c82c08651040501c02c50220960004585d62241840403c10700c8081017900020385542883c0020300a0001d0708031040c0c0c2600008004401400144c2c21002035444800580d40d100c00f840c0e4186a02c0c02541480807001d1000c0d40381c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 655615539 1250 655614289 655614301
    0x7051b060412052206050c0c060c0c27040c24080c0a030f060f0e01090e060a0c120525030501050604061b0c0b040e0f0609041e0f0f06060e 61
    0x1580d6007120020010006407181c00481d40304075003108070250014004d00a030315104040c0c00386d4081c01c02401d2600c07031141c41805610f03145048403201086d00000d000725003000020704c0034400100c205100c0114940c040d08448040c0061018451401036040c0f0318030b10725051000c000e00c10407041000c22504480d0150007115040882c140d040a0203800c110f03510050428102c0040040312060501241000d20025607560b01c0e09100050700c45202521006d6645c54a010040358501d2079a0b4846ea0003600008000e01c50540c040700030707400ca9003442e000c403041e1a00e1b1003044070411201002c055411540a4411a166011210110003e401c0801030f55040100160030750203584102000c001e030301d070b0380310302e11020b42c000500072264403841000005480d442c030700005030854022444c4e201c000030001054907640c503c040e801624080d00002513030320f4584807501c000c400c0c03509250000702800c0a050000b24010710808103207006507407030000c2400503e071035015030700c10360301c100342010307181046c861 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 655616789 1250 655615539 655615553
    0x70b0f160e1903050106141c021011060906070f030b01020c090603070f0e04061503080315150403050105061801030c17070b070609050d08241201020307051b0604 71
    0x480036010708045400c0418240001c00360b690b103141544541e260000c000041001c15084074003521000202100174520307060a101c8860702d01480c03c03c50746180302c2000054140010b45e01d411005030b00c0e2010b034400c9641c03071152800009540c2004a40c3c007110070483c08580c0016001500810361030144414a15100000d503920016414540328180c1d010100343d407640c04004050041c2040000429420394880c04a40d14400c100c405461050500b0315070071841d80500c4041058a50101240c0d081d03890780d01c822801d0720310707030019640c0203050a80715601e01c40070728000e00021071184001103468600391040c0400c09201e0001e0310600f0b20703840b00602c00107202110b1f250994821324007102600b021426254a0104960701800894070b0018884e003d1041a401c10840703280210201c80341080319640071221070401f194000100e1030010440601703858a0744031070000c540001e10003c01c10b00968080790890b40141d46d031901003400000e03a036200940240c030740d09084103003001501241c0707400d469040b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 655618039 1250 655616789 655616821
    0x305090a20030a0c06080604091502030402010e0a260106140603090309040c0903140714060a02010f05070c1709060a03020a1e120f020c0a020d1e0503070b0f 69
    0xd24440d01ca0304214a0881140001840341c840141154000302103418104401d071114014003000a0110002601a0809001304040d1590020980e0740500a900100e4020f40026000302c3c100b003880011f18150390380384840310014080c0d18903290141c1d00d40c541c03c050450048107030100b059041030410865046c082524040481e426038000340c0e6030792591451130542c031500c40815881450868824841a4480001c03001d0324411040c02c180c0070840d1034074690b0b401c118451b001c894000001c481c1403a0504101509480845000225118820080c8030050b210119400800507221403203400c20b2000044035445070a00e0180958501240328020600390720480e0046014190002104040b4601c10342480c40c0030306c03181c00ca01060050040008244c080d200d1310407480d090a04141032000e14440c800c0714605807415000340318034900b503800c3c4a4500c040c8042500c9046040c03540e20000740401015106072881742e4040c50703a820b402e15182d51010006000c6411084a403030400440f0406000c0035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 655619289 1250 655618039 655618043
    0x120e040920031b040c090b04080102031602030909070f0512090a03090b1c0506060c1510050f0d120e03100c08010b040308031306021605010b0a060512010312020a14030d0c0305090a 79
    0x3152482505d60240c0c0c40e00200d50200b01004c40006d000110200191701660190000c00c1410b1042c81c0a000304a03528043c42c07240d507511020080204c0d100c00e020b034501c002d40c0056803c0c22400c041280305070b001c00c6a030843d600c90058020b09000c4040680c048503d0b00a015158103041c10412800103000740014048100d24240b5584c0b40407842c25950130041d111103000c690100d03160340307000e120761503500c913015102d0074950506940041002c0c60407001c55100d500003d412145a1034654a40c402210504180841407001807200c031106603c0a1288000c02642080003042442903140c00030302d2868140c1c041003c3c04402c1c8018000180700d20304403501302c086c0c807283d10403900d55400d0440081c450002c3c001802c802c2c01516000708141034010314000c0808a55101c07160f541c4a90079180c03807281900c600d015009002c0140b000444070441420f10521520456038140b11540d111540100030b50b00300b07031141c7e001003480c846031210ba001c0da280030207003485c00380101e04192000b150b40c1c1018800c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 655620539 1250 655619289 655619291
    0x1509020a080f040507050405151509010f05071e0c1e050904080c070f090b091e04020607030905090f2401050f090609060301090b0a0b03070c120e040920031b04 70
    0x2c80c0c04e1040400c404805000001d10812441c00e0030400c1c031030400d03401c0c440c0e90b0003038183d1101400348094040c10b41c0d07501281a100d001403508c14803c101c44550250a04480313224580440c8140c400001650b0140a4894880c03000d0301e600780342c20500000948004056440c0c002c030820300250301c60702c2810350020303400342050307880d00c07004c00081d4280681900500010442500b00240440d180c2d0070081c229882070301c00e515161120101598881c21400c030010031081c041d4003003801800c0c410005c0042501038540584016215000140040c6003601c012000d10310310400e208680e100031800b02e01600d5044001c40500b07041400107040da0250482080f01031401050034620b50b1180411031794810760090560380c0d65038407080024002c1207150a020b00500c101c480c0410500002c5041324010300d900e45070040241703a00d5503030f1960b03a00c6000c207101c10401c0340e0820000f25242d0303004c2c1c519414802e00380440007412241100c1d0314407030301d858120301ca94425005d03070300a42c040c25420a82c000f01924 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 655621789 1250 655620539 655620541
    0x907081509030d0e01150512060f0c160f020109060804050a031101061a1b060403120b060c19021512040b06030c22051506030f09010e0f011509020a080f 67
    0x14105082d4001d85848400890030414900c01040040d8000d50004105490300360707a50b80c8840c14031688545014400555a01643c04100402c580030340c4c099000082c40c1041d860000824014a070200c00716508031104640702203c54115a00b2410807405401d00d80740008961401340c40c0c00c2e0750348000380805000d100307001000c0010700d0400e400050281c0701c400b2400841e6842c50301440081c0e07010540701c0d44140346071010094001004030700c00b4000d41d0599121014080400c65507002400c002c0d0030340f58007903010000004a141c007404840c003101c01ba00d0701a00f040d601e600510285a00c24a40f00100030010002604001d18849069801580020004a09980312404a403514012101c0321740d00031329501000391503034501009141c00f100e854005104d25111088513903000381c14010034a52004040c800561904085440140d100a0100010170300603c88131505040010314401004665100c810456084d000303007000384010100305000f140340c0040140001d020400107448a1082c100d480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 655623039 1250 655621789 655621801
    0xd1107050301230a02041a0a0302040f0b0d06150f1211030c04140d030f0513030206040f050a0812091c05100c0f0e01080118090b0a05010e09070815 65
    0x940000303400d000c0c0c020410240062140c107400814000d80102e00c508000021340e4000003030094a007100d2030144144442c070010002c5401d160820105c0d10708140e803c1c440002c40c1207240032440001d00c81050030716a21040070081030309561054100805252a45010130200c80c1d01186640b07456000f8900b09035500c0d030070b600c1c81d00a000da4181c1c64441103008814448482480801041264034400e164070141c1d81d0035089c00700400c01c604010300451480c21000510134050401028807064400c040c40302641c9a07400140142c00a0b04042c0d064110132105001c6170030180001c5c0050301c1d03000c0060101c03018150000350315120b500320043c01903100c0150141c21810030001c001c1c81d154000141c900303164008020000070141919503500040740c00112080d0399010300c903000040c0c0b006030750320f1500307a0800601400080d41c2002d41402c1541c0c90441d100451403500758035005205910010445500d0112401003000d0040d110610f1504102401c1200007000201710102c92040741040e012a52a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 655624289 1250 655623039 655623043
    0x1e03091a06060f09060705070806070210050c0702040c020f010c020f0d0306211a0c090a1410050f0c01020d050403080f0906060d020112091b1a0f250804091a030d11 72
    0x1b00e800070100e01c43e49101003101032021905e24400c040607400c8412085860722000180c40080e80c0780b4001c5041004514050300b03190b00400c080e80c04c1401200c1c545e0100c580340d103084445e50305880300181c01004441e8a004c5003070001056000e920314044c02018100394030b40120900949512604040d01160b02d82001005000c3c0c98019003168102c0b1964940a200521035a0060000f80c0c800c0c90019808900ca5034544c141c840e407407801500255002e01111400c0d505644818001c0c0c07203400d400d0080c003401c604240010300e0f000352a0f070404252030803c1d02d00a801320382c016116485100c41c0c141003141440c00000c0c01a4448011204810310094900040c0c2c2c24501035400b0703c0e8040d041907464004d00c1211050b04c0c000c000e080d80040000c90b070322000300311143c099a100c4045440104421807140c0b103420050f280681c1c5074490440041451002d03000c04d5600c0032002c50320702801007130030800b03250640b280e0310300781ca240900600c1a0b000b80001035100c800c42300c0140184580b040e2009402c03070302 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 655625539 1250 655624289 655624297
    0x10f24140a050d050612030702010f090f091d030a02030a050d09021804030f031104060c0c051012060b0f090402220902221a0a1e03091a06060f0906 65
    0x400c040c0c081d03890080381d070018907552018041c072100e0707410800070810508281e129041005c1c60b40000d98140412030b4011281c1488021084040081e007950108024248001141c001d14101400080428400b03a060340d0b1141a8150980c1540080c00282c1c41180c0210841301450810300e400c0b59140c03648038450340204507151029400c41c585050540803284441c131031078040c130b0007500c1d08050300103404401c8082e12650b410481042d0428081000424020040b41603044d100380010452181c4460100742c0140d0f20070019000114651540d400a00e064440c2002030002c2185482c90304122070b40200c0c0c18459042c81c0e5000360303800521025001d5a2051f070b1060021f01ea04624151550343d170308000039400c10707402c0685108000d041c071b144080c0340d11281000c40d83c024800e521420100c05201459401c918007140c02d00c07186d0389092102d51998803030041141015280003540a816003072260355420a01080c1e401d0070b0034071041c040d0a550704400d07a2070340d001c070a03686540ca0350810301080301c03809 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 655626789 1250 655625539 655625567
    0x120601080a0c12050d3b031902060913090501050405010507080702030309031c020d240b0405130e0a080301030515010503010504110415030b090714030714010c02061917010f24 77
    0xe1a146994441c1400051b9000b07420b104408072840c3c0c0e111250018090030700c0c000f000f0740c0004100a064400d050003148640c042640c6400003441000e95142c050030340780101c0c0c0448840c4d5541b001c02000d10742100f031550300107601d07200650a524141c104641e591040c2000101600c40043c1580d561000d60340454605c080e000400307118503400145d003541c02d070802c04074180d0303142c0c50740a003c20100000c4080e00c0c225000140391404800c10340300108c000b01030440c079484003805541681c4000c5500e040041d802144500000d154400e0a41900d0200740d0068200504c264100301c2400081451091034843c4284100ca0015291038070280c00103240a4940c00245031000c600c00304243c1110100c0c8c22011550001500290150f0100416488907200d01410280d080c210b5101911944a0780b003507560310384090840ca1030408040320002c1b03404454081000090388100948400c90150240180185135084508001c6801e0a100220752521603d000542c00c1141d80c4280c81c0310b01c68130310078107945 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 655628039 1250 655626789 655626857
    0xf01030c0201180c0312022103220b420415030c05040b010c050312060f040c080a0b060702060301141c06020703021c091406070b0907030c0807030b15120601080a0c12050d 75
    0x80d22841cbc0100c20b000d04507480004104a00e040c0110b036040d048201e81c050fa000441101d00c07100d03500c40480914603061805820a80d144500000c20040c034810300040c1d40205401c185c403038603140400041d5117605d04000d04106011180e0310000c0c80c0002510100c00314000b20459a03510302d0081001c49503018000c9903c2030502505600c0da6401a0009001d0303001000d092154248080070f03c542445047c000030741059041004104000700d500001201c40002400c4010325101e021300c1441c1028084029950340358002a44c10403d5010090405030324107180031203107403c0204030050b000441504c54001c004a040f003594113070b035845000316119154000806119410311640355a9130f100a40411100207010f81b0b03000c110403000052460441c0e5110700351141d82c0d41c4449102041c0008040c400e500076044080103441183e00b80b102e64040c06160000780910811802c06580982032030b8006119004004d403580049080403c241d804000c40f820035001024060f01622003e00d103001044105e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 655629289 1250 655628039 655628101
    0xf11030f010513060b0604032424050915031902011b12020732120d0315170c040e070e0708041205090f01030c0201180c0312022103 58
    0x503c008201002194014007003005200c0c1c017070040c404540b20f00d00000c1c0034904d8000c140424218070001c03425980114060103d090011340c0302c250403030740d8001d0b4500031590b0811024000c904050034825405030f01e04119425604c0b44001194441d04164564018220103c0860003035901a00b0720f01d003001078141c4454903003c61424550b0002c0c1c0200c10f00d070b0050184100000d10311030308004415015004550407801c0000010581e48010041d0900c9a04503a000030786a0b00d03860180700340d80303503001591404240e40920640001c2c030001c0320707000080a4110f240e00043e0050002848868004094500041003001c1c810001d01e401c040e540081d10f80007900080140c00c96000384c450740201d00c07822000c05c11100c48101501d190207160f580b5600110b400d103c1070301e030798801d030050080700342c50307000005060700840c0500a600510000546082d0315018040041049001c0c494407029028800fa00009a0b000c031500d08008202c00c010240341d9000c804505000d500204e1030504100210000b142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 655630539 1250 655629289 655629301
    0x90b03060301090f0602090f0108150d020f06131503020f12130807030c060b04060503150a020f041e0e010513150504020a2c01050d020d141014010c0f11030f0105 71
    0x280d4014001a4095015401003403055401030301c442d4060302d4bc1200320a002d1443c02d05000e003c60000da000da134013000c41800d580c000d48440c801468501b644086481820382020450880e00000160079810144100011001e15003640c003a00c0c900001d5a011041d08e840305210012800130141019005000000e811810136402c420b1403010907100b0031051200c20354007410003044918501c10690942c1210079112024000401040e904c1241004010b081105054034224030390401d4100006500000015181c0c04a90300c0c0120018585840008010360610001c6018041901c080c080619110486080c1c030540309501d05010703040c090411511400c0c080d00c002d140314058540c18154401d000c041e0404040a9060310303402da00103848051810f05c60042580082d07000001e202c5040d680c5110301031248020080950080c400040e449070f880e814403a5510155805040036030608c902c009112001550440315100c4a0390070016060540c01800007007402e1085040501200b0b5107400304001c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 655631789 1250 655630539 655630541
    0xc09081603111225121226090a0c0e1b0d0f0207030807120c020d0c11031b19060804290a0204140a03020f120a1e030e10090b03060301090f06 62
    0x90080c1058030f186020720340d00c0802c0302000c04400001b0300714412040d1303000306150080040c80d0707080200d480480700e4501496034410b4070000030740700c0c04a41e810114080041c49100300912006e08000c41c64130031282418808004084c0d800c2c9208030702c1c40c5003c1401016502643c1c1b01d0041445c000c1300c10340d5070310910b00d40140240411507071140400d2038500c0340100f1105074403e04103c0c0d603560b0000d104081410509a0710b4100e44042110014016903a804c001d4605010520718400c21030f2010f8035031090401080b1101582c8000c80c8109000c503401041601d50000c40e00d40c00c260441c4e2800b401808004d400302c4603174080c4001e44001c0809100303004a560301a80144100d4940762845054450583c040200e0900c00b840301075807282c01032040c0710192a1426010405101e04011034602242e01d030b450390048c2100000022000d01424400d100707040e0082c8629100c00412640310041c2030816801600b402010701a01e00a00d50110014001d901c095000c0307945144c100c64060f03c2666107144c490 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 655633039 1250 655631789 655631833
    0x601080c091e060d0c0905190e0604030518060d0e010509161509030b0702070302040b0406123c150612121818060501020604080f0304030e060a030c090816031112 71
    0x50f1240d50403e07032508c0740c0c400920803010059503000282500742c6490f00c040f00e0b070340c02c0044a042c030004c1c03620300c0359241d070b441078000c1400301e8004030040b4180c030010b07071000c0c21a50000c1ca44401d50700075445401d03210304a2485130050f00c0d4150303110020480502c1007258043e0042d00028010082c0d04148900607400207050021a4403c070390030701c03058025100303100036a5101d12840894201240321100000c202000304803205030300081c600c0721003144c609240320207855041c2020200a03814580d0040c01702002d40c001c5805a00101840060300e41444164210395504000d0000351950b40380d00310083c03240004010100491140315082501c5201001c240320111244000356880e06400065550000c140b040c03156402c0070040307040c0764865150386400e030b000400c11010400200e103002016030301e0101500300c04441d5a0000341441d503c090107031021119820403ca580d20506000220510003c5c0035000c0e20391100344c02c100141c100e4003042100160300e00454140c0a170300c2070401c040901003203207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 655634289 1250 655633039 655633051
    0x3110109140a0b06031b0114070501050c030a06090c1205090c03060709091d120a020a020406061707020a1106070f0206040303030903090b03150607050316050601080c091e060d0c0905 80
    0x10f03070003500c58104042d41d030a10024900c2d03592140300404515580121041e181918125000f01e2800205590743e40c2110300885003100d14050110a01c51860f030b40384941c001402c00500200014074010802508800c540b8414a03a0701c0d407100c0c00185249002d0004100000c8003800311002410010030240c01410b030350152100861030018682c06203070075403885840c4255000301402d801c2007001540403496000c036440c0340940c031a00204100685036032042030002e203d07690b25041d228003525070b0356950303c40141c814402c6500258001700402c3c7c000764981c507002c4045501e2580c4089506e00750800410001d000b07540030101240000c00e050b010f42003400c0b2a4802e56501d0912626481c01440500003a50071405001000d101c045241c24034400601d0300900880c03c80f410902500c01000784d840341c150301140c0d83d801400040020100c00c101100c2440350072514107940c1e2402c4812100034881c410307940900e4000b1f00005c5801c54581c0c0410103210341c0c020a002d0032160f290503103403024080079151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 655635539 1250 655634289 655634303
    0xe061f0e0f041b11030c0303070206060a0b1c0f0e0102030408093102030403121d010605060a1d01110609010920090403030f0b0a0e09070501050f0703110109140a 71
    0x203030718054070740b9104210501601d04003a0407400704016080722064240d480301d80c51448100008080c100040024500c038013882e900030856461b2400500c254150306a115000c1d4280901c40b0111032507c1d4440c80602c00c10300303d00011311403409510900500304408400c2c810354800001e100c10b001c0900c00404c09103005807066180c5a100d180d484c902100003024050290510003c00c0007582c41070340085030094002d141c490003491269012800b2501020b042d654207200c1840a0717203100c0802c4c050807000f400704541079403c00c00300e014060003409034214500c200000382400035080d60b015400c14104c440c0403070708440c0545045480c850082c41c039200103072081000010040c1c1099800022280070079400790049034035403a00c3d03070190054212a00308088060302c502e8404140d850b12a403c0c0001c1038100300000d81420007021041c02c0104c1a04003904000007000050481038501080352502c9a0501d0b15a174180030341500713140104400e00307008001200002c00110300020024540b1401401089 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 655636789 1250 655635539 655635559
    0x30e03041d0f09030306011e170c1b0609030a0c0c0e100e0a090f1401110313060e010e0304150e1302090f03010e0d141c051801150e061f0e 61
    0x82da0f03a5607800112032460008001100c040100d1081043c49004078407181085141d1155155080f4045e01085511140202c800b0682034280a42d10184128002040002d020b55041080300d00c1d4803807290700c400c401400b10440040040041c0c20448800074080880b006510b0305040011a80032070091140102c10340e50314011440100d070300c1c825060140d80c4112400c116812550360407401d0300200791025425541d0b045010480c45240000f5031041c990310400d00000c040300e1410130212040703d0714074081c3e40c0c5041c0780d28429000020407141929002000b0700030443c404801200d0700c4078a038a403980c1106100d140b0140700200c039000340030100f00480d1590602468481894200c581c131800d107850300e9012801a08440c1e008801d1503043c1d01c1c10040e910b207000740600034208813801c003d01d0703084101c1e6500100a00b8000e540907006c01800c140c03009011025982c02221030105550060805695000000c98815541c450607111210102451414010825071000d403000100408450003039041c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 655638039 1250 655636789 655636801
    0x1015030c09110706180c0314100612170d020a030902040b0913120203160b09060c0a080103111201140405010506151c230603120c0d030e03041d0f 64
    0x8000d503010b034925880541d080003110303125080500719000b8040350b00e0b80f2480d202000b1605458618000d180250b640160b100504042540b5060328015101c400c00d250030420302071340284000c0c1800e00d076086841011811503901d601ca60602c1100e00d0364000f544002840142150543c0000389514000c807020005844404c0a000c2d49a008540d10500c0011b0341481e400000d201c0f1131a94507810b120710440c1d042c9100e00c0c00c1790b04240040441520384520b4001001003180003044050750107000707020207d00b409000c807400b9000001c103000003409000c903405980c0c41502d5442d80d40c0700300e0380078500038000000502c80482c2007140959080d200741d424400029080e0902d00010078103841c111410301d280c01c88400b214480d49040020000da09030300c0d40110b00d0020443c1c0c0d030020355128483c2000e1968140442018a4000d1030920506685801c0c03101302101071010541449145590402050048034000c000341580b007150003100154441441411034000000d05a41c820301081c4107a0360191111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 655639289 1250 655638039 655638041
    0x1b1211100f020307032d0903020a0b07020d06020703140301090f060f0f09020c01020d09080a090e07171504020c011508070305030403231209010305060a150c051015030c09 75
    0x440707007030150780308015800000c0c0c0310b081c4030b40120800c080e450548130203400b203d100d94040e40440c0400a40811030a00079442c00303d071501c00421004c10034034507140055011584164600070080c0020340d021840d44141800303800c0c1d0004001640748859038941e182d020301d8000b003075804482010715240c0b01d800b04d40d4961201c40f070401d98181c0141d40807031500d4500840060f610641c20344800c1c3d5000d105140e0440164004d50b40c2030b500ca036480307603202d1504503001052000b040c1c2c060400007103d01b06001c48030360408013000a05228012003d000d03900cbc0000040c052224850407a0080e1002510070780c181c6065004580d00c205052000e250780c0e44e1110310a40c0d5030440d000c0a040c1b9041044100001a03e0031502140c1407880d45444200008108856007050300048201d5070041001801d05138943e458468258804800c07501c0500c0a8140506401d0300c1407086281400c1c095540461801c0c080100043c103444500124140807031091170311300081c0172100d0301c01110811180800425401d1903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 655640539 1250 655639289 655639307
    0x70e01020610150e0603090706081b0904020306010c050f10140105032d0706021f1a041a030a0c0303020c0105030f0c0a0e030a030201141e041b121110 66
    0xd15512802c0160910841c04024491410b41109020304d2610f40076041d19910013451082a0510152514514206002d8940fa44c014001012038a184925038000010141a1a0790b0002541c005032680d03101001610500003200001d005849021114008100d0000d242c2220350080c08062203a106240f08010401d01c0c28058103500d50403520896100344c201e054410740050005000081101d441480c0e107080481c90740210300141c00c031044e10101100b01800e02c011010854000b0444003400001d1450901c03e0020014803070b079107a042080c504030120040f038030710650003000c0e11541205868011300f0b84d03a407803104074090b02034424402400d60050096a10580c013485002c281a81d84000c2c001d141d5100c04032640a01040801043d09501c0801c10082e44078880c0e00002102942d01000c2d0a50310801403c9a41d091030101800e1612416481c190b500941d0200b0440d19800303030280c001c290149960070088001590102c8031081c001c0090040c00400c3c002e40d00d00031425030ba0b800849034502 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 655641789 1250 655640539 655640551
    0x4050306040f231213031202030703020d1d011112041e05010309030c03110a0602030114130605061c09060903081b0307090e190204060f09080a03020c0607140a0b070e010206 76
    0x205403081084c840300f81008001c40740d080f01d408040e01c3c0c0c50b41e0703070200342585041254005900102d140310405030104900d0003851020b0519560304101c1219030003d031613204014030b04108520f52003203074407001045008459442050b9550700e0f903460f0200082d8110b07541c04406c90820303010400040715406032242d40d810301d403d9940c800aa0400b6181905d282120056040d254070801c460500483d00c58805540601000000505904075110070054909125a000c400d001d1906c40104250303598242214001c49850244810724440f42507007030000e0806641c06004207003080505800c0542c01701d03513180300384003984080c3c410b00d1505001400714041107840c180401d80300c00092140348031022000341d100400307160740100480c0320420001a40c125501c9040800d0303092800b543c401390820b00304409400300b00d008000c50269900e000703503aa1440c1702c4040c02404c0000307200050100701e29080c0c7d0300300b007400129000162545021344a40d00100d8070f840000300b109052003695031021070f040340a65 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 655643039 1250 655641789 655641793
    0xa021309061214240601080610080114041803050702030d081504022809060e1e0603041707030c060b0d030e040e0c031207030305010e0906011a04050306040f23 70
    0xc0c401d07a0f45401c00c610206507031a0503c200e41c42c1e120100204003200440c1c4105014111103401c0c4000050310404028020760f1181c0041d40c0b09480a50303000e00207a04540310b071690070040100010214008151803124100f2450340301e4121424190403030b005104041c0b094080b6808002f100b4412100b544083e0341480702c100e441c50780001507203041d0700a030036020b6482c2100541d200b040100700114200203c440742c0800c03c425420091640c00c9251b81e42c0d100700580b200401b030044146e00800c01360f40e05444511030308010020a003130003d10000000310100b180811640c8075040d060241c00d10346100d00c1118002e0600440b01c445040c80c841c03c1c81083d030f06407913a241150b80001000003a00014144903120310407000c0c41003003540c007081140030f08080000c243c0d03a030b5039243c01d004094a0f016005400303140c0c155804e0010194001805504440201131a0580040c00c81d540c0840fa1060340e01c6103034584540300500c000c0c800c0304046c1d00b103501d01c01c0010182c44500026269600b0300100035100380350b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 655644289 1250 655643039 655643069
    0xb070807180312090b031302030c030a050316110a08060108160302011d1912150603050616050d0c02030a120e0a020111010209041e0b0f0607080a0e0402030a02130906 73
    0x400a05883e00810200d080c52440c6a88481644149401c11180344094180042c41c14041d42014001104210703c154003401035102d840c2c846d950b0760b1141c120000321000c01c211440040c4082d2031088020742c1401402000416500d003001540c81100780200304a50188112101840c035030f0702200c0c000c1381d90603110070b240501c0f88280c5480241024034440d8001b204207160702940b140700741e1000e015040c24a01d80800032690305048081280468130927180d11716000042c0041000041c1c020340c840124040301000b000600d504850328040d00c0c2c030585d0000e041052070203500c0d801201600d00241c403691070401c11691009258269126480080070076000080820701551240d00144e841502c043c0000d441d00981e00082000c4981600310074a10f84000c1e141c00040125a0107144204030045814000c2045440c00181d0184078076900100400c0000522020f1240600300080580710010421516480e01d03d40c140007a61000b640500c1c0c6900114000ca02d074000340c131901081d60081d050159903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 655645539 1250 655644289 655644293
    0x190b100614090d021507050c0d1707080706060e060f100e121203040f031d030d0c020f09180d1103030103020105070c2315030f190605030a0b0708071803 67
    0xd950b0042c0c2016421080f46000b1002680b035801081031114910f1005950700d030441d0400390f060104002116106466107c0c024010800740c07035200150360200c982c1207130b0f6904240b0b42002030340f1417a02c004003540c1c10124000361740500c0e0302c0001c4c8a540282e4113441e80a902100300420800110082d8010900c081c0d4500b0007410103211000c0304400020032500b92805240c3c60103281d4000700c0302103500c01c4c082c030041401c140d880a15504a149401002107440d015000001c0d1104e440160540800400b90040b000b036550f501d02000140c1c0c0050a0b00d405400d0501c01241c411060001c220000d105e4035034821030880c0b0a4020424065100d1301031811a425a8011601c592100006940c00b4203268400b06031581144806c800e031090161000c00103103003843c01c1c0000c1c0f42038404950a0214140204285481000c0515900404241d0302020079980840355400808481d000f4a40600c518035252081000d40356100d4000d46c40ba886a54007907079a284201c690369001400e40207000a03010007000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 655646789 1250 655645539 655645577
    0x30106110102280516060b1f080f0c160506010e092e020721030c030c0f0825020c120a05070e0c091e0909190f14190b1006 54
    0x111203d241c9001c0d0302d0300c2d0001c0c1a02e8094412a0b01c103841069a0f0303035541c0a0341c6010240c070410b0b0ba00d2180020568040030390040c10451008200c208540059000580d84100800455080c0200841542130728032550504594500c4240030b840e00c400f03880004a960b03030b08001071a43c6e0485005a01010104051800008841500002c402c0803502404001d001a64214140710441c1c0e03940b100c1c1741500f000880c02000d070740c0041844010f051a221440d803805900210344203940300395051242c5561103aa03035190709d0ba489500540340708082c406900340d80503800b10301c1c49201c0404407a0300030b8a64045000b180c80d4070303803070400418980c0044010065100b010700304651010310910131a041440d0350340800d0801c2d54a243c400390400d002d81520401d45084c0100b10b42115062008101765240052021101a40380401074024450300c41134000f00804000a06841c04203001a2100a1410700301c0400c410182c600845016010100080c000506281c11b442203039055070f9504108524505150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 655648039 1250 655646789 655646857
    0x903031b010e0d17070320072609130b01230403170a110c01020c1509180105102a02010c0209071e030504050c010e061608030106110102 60
    0x10401d5480d080002108501440306031032504044d00e5144603102d041c0400074200000501800034540390442812010110b01e690b152020174048034107a0b64005030820070240080c0401600c035540d01c80e070220b031340702e110702000c0c1c81c07014003d550900d0118228456101a108580500d500260303102102004410354001010b65070b0180c071f0061868292641c4825465055035800681d040c080056603036107017940211080300060700700e0003070092440c02c440001d448180c1c0e40744080c81181c10b020002141c0e500f0104684c15164000c3c0750fa1440040b29406d00c1e041d400c24441c50f481044c8500b1140d01e000d00038a260b802504001d41c4d03841030a80c5211490031180741c02c404c02e80c1001100004100140c07626281c01340512526201c2c0700f00d401078215000c1415000000200806052900340000210000f0b1590181c000900781140010100b0021940720300945109254a800042000090040713102c02075042c1c3da06a505d1003000509180d0300c9090f8418204690381042c401b480d01c3c3d00d02c1403417945031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 655649289 1250 655648039 655648087
    0x8030c0901110a0302150a09030905010e032517070803030604150e04030c05060601090605070206030a020f0a0302091f2717060609061009060311070f11011202090303 73
    0x2e805440c02840c04585062030a9000f28051380c00501142e8418403990146a0300407203213002402120705a54004100304642c3c400d040c140319132002504400d03501400a040c3c00c0368001c7d4440c1640e642c0c02d5421540300018030a4030741054480381a04600030700401c2c11025504258010346c1703151161f0b000e000c0200048400105507043d8040041586440f604009004500075070b520031140c03c29042c2542402809002c140c1800441c0342c0400449801030107841e45031707404070746d04c0c8c1c2c5030360b9908450b401034841c069038060503803000254680d25942540c0034101240301a52000820030f4020b50140b0459001c082c90408240c105030002840d1400c03200d0629604440d10f10f41132600d070b450300003103c115000842c2c074506400c071100700012400c020f0b9056a000700101c91100d80104451005820705043d03010f820105500c0b042031000000c00c8d203045450580e03204410311a034031524101030242060241d9154002003114290384a0299980203503000359034000c015518001d40100010100d03880c1d8509 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 655650539 1250 655649289 655649297
    0x1e010207031b0f14060613060f1a1e0c07080105010e04061d0601090b0414250201093008160c03230301060206010806090c27012d0308030c0901 63
    0x80c4a00058941c000b02d48900820304c002c00d43c81c1001800c10003903403404114019181c0c605501041808610501d4004480a440134078200c410100d141402510524060440c01c0c0341004010180d038290368000c082d0742c80c4020984185c20f03220684e460903600203228660800d240d050100300880c1e000e50040800300100f103030100300d24824920380d50411609031301003131800b643c1d150100d0090030301d405160380080140403980110b142c0400e000071400014212002003c04800007040c0c594000d6005480780c5400c00306d54400f9072800e02011388181028981c00d10440c001b1002040c8850058230110700590006081034401400d4213005c5070001109602a0200b100c100d04001c801e5117481080f9903880d00c3c89000903035075070404401034a0034106a01400ba0360b480b09040107500c940114030b0b400406012a08003405074488051140030750070345601e121031151503c000042e04207680003041003444480000c078110384001c0d25070032400d040031300c00070740380c000100b0005070320740c0c0a10000d00302810305040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 655651789 1250 655650539 655650563
    0x611060703020909190e010606050d0e0a05071707090e03030a241514040b040303090803031b0a050c010c020a05210d0c1b060f05060f03030d0b041d1e010207031b 71
    0x7000c509451080e444080880c80000f880c4210720b0b15800cc02201c40108070091003544403e594072aa079030300d140700301c5401e07928044c1c040c820440705016000050008000900084c0500c1c0c0c0c1e101c3d00c99205440e00c0410901d0500190210600c02c00e100480b0304c0318020011566281050390811483c00c0810320003003001d118803884a070410701000d08050015209115103845c01c52602603c1d90203280c1002035554004d104006140c000c1c0884c5d09081081e904c0102e8541c41a44000d90312030103401d003e0031955080020050705a0350014692168034094005c231503408144064180c180c25520342030344c078010030401a000350f0b841d00380c10000d0541103d1920704000800d4108814404810304011210709031a15081e0080c400f041c001d840d081402151842c4881c40f07410300107640ca1182c0c0b09005405522403117400d070701c0c4d07031264031200030010711101902004402200860f200c6c1c8065204030341002c0441c2d143e0541c80300500c00c1e1100e4941c180c982000c00b001d0380c0c440302e0513981c544204455200d0340c1c0c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 655653039 1250 655651789 655651811
    0x1a06030c0a0e1e060d03030b04021e120705041d130b04050f10330b030a0c02120c0d110f1203070206130c0510090f061106070302090919 60
    0x2100c07a400810384014002c0c098188100012a003030b1103107401c0300d0514503400038007415a86505040420320b905040029001c1c40480100e00a40034202000680750201c0d44022254841d4000911841e1348000904505e0350fa054001d0b03031203006034061b005942c001700300005100d03c0c3c61100e440d008102c0a141c070640708481d40c0c40e40b0341c1c008120f40803506c941140351907141007201049a8039400b10020028044a0035401580140100000044003208000030b07020b0002c0c15245800c0002d80940c007000755491804103014000380003c0c1d554900184101000c41099910708010b444502007904040c040c4606c142e81c0881e581c07482140042d070540201e000b408800030040100114172041020750640303e19103001301038202080240b180140d07090000c9400000b0340c58117a08001e560b012102c8200fa042e40d07800c01c668040554014003c207400217200071881d203811a41048010080800302c4810382c3c2d842404134164001c04041e01d402050031808520300380c42011004844418a4200040c6000d0708 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 655654289 1250 655653039 655653049
    0xb13060b0906070f05072402060103080901081801382404180b09060913060c050708040e04060621020108071215081e071404060506040b03100e041a06030c 68
    0x2d80c0c010300b50b80405110000c04401f0880400c510a145800074202e55851521540164410755020f10304000e90003000480c0300c4d9451010300c1c00c002c1c140c1e000b00400c0c03000d0300c908085003203000804040710341c08182c00c40c0003200f681c2859024a03800381860740c040c1c0e100c010190403030030000350342503180c0404e000200741241500c40c414030100d1003c4000c00d41c000340b2018802d60441c0604201e0241031400c0c200040144480031846c0c110790f002c000010b0002c1302c55003c4440740103008004040b00f000140004034000c450031074602440c0242c0042120a40c1c030103001c0c40200d903013010b040d803446120305880003541c010281a82c0c800c43c0e07410146100751021580c00100c819880090f81a200100340c10b02003584100803244010886c480700d43c1180203910103140c2d071000a13118058012071009a0440d040d10b42e50001c00043c94050450b548450b11190030b1005900704980f004400c4088960010354050b0a58030070b030055130082d800074194103c0b0450b0011542c401001c0c0b6400d4460300d80d030003400e6126 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 655655539 1250 655654289 655654303
    0x90a0509070806090c07080a0f0905060a0504180c0c0b060a0f120302010501060f0905151e04060e1005030a0f1d030a02010506030604020f010807020f03030a0b13060b0906070f05 78
    0x45540310b075041e203400c00412000c018054140f80d00c0640500064000650600844456031000c0c01c07c0d40302c00301d01c2802103900c80d109401840c0c010a0110b0380c0d02d45a50004042c1c419100c040341400322a18802c169802200c480340300080c0069a5926510086161030452030340046001d0448401c1036107030782c402c410810a59000111201c8059028024580c2c20310555000d0106842c0c10907520000f200d004209580d42c0c002d246c403a00c25007454060035030b01d81e411145114082d048801707404400300086912900f041c4510750100c1c82c16103d0500901c0e105040821460244e01c490781991143c129010003044c504602c00c4503c1c1c0c5c0d400c8424519160748541c6000401024021555062458002801c0d01c101402c50380c0240c2c80394041c80300695400000002d42c04003884c051015980e4614101c2ca0b00d250a000c107400d9020000610100850503000040380716800e5810500c00190485850304441c2c3c144285280d44105122a194614008000f4600c40d400b665070904030180d1502c4550910070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 655656789 1250 655655539 655655551
    0x1180905040311160515181503011d010620010902030a0501020309010f020309030703050c250501170f010509090321011e180507090305010c090816060203040902090a0509 75
    0x240f868100d620040c0300700000310070001008a101c240318a4800840c2421680441542144402240d121102601050540ea04e034100a00200044407480c0d60300280340c0c801e000f0351001d01c036400d526002d80c2194204d5181220b5036682c4003c5d68801325048000c400b1151240f920042d5229011980586d17800c0050084440c0990700043c2c3d2070509841083c2103500ca101a50310b45401402000403020001c400d450495816050480e6071b8101c92071080c4c10030802d500d520b4152000010300011088501d4845030685d807081e00c0b0007940b5061300102811091049555440c0b007e4000014001c60508520040d004102041160b0419066088100724098401000840c84921000400081c40188a04000203105103450000507007024100d504a03813007100540940790701c070b0010a11151007007850704000c64001000300400322007400e0060010b5050700c82c40d60f041c8100070b0002b840c50b40340c000c40012900160000d620702841d0000d00b20103034010100d89130380b100d000900003800344c0302e03e0b9407548626 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 655658039 1250 655656789 655656797
    0x414010e0120160602010b060d0c02010b0619030b012a030e1002010510240f090506030c1804060807031515120501140417031305100c0815010509011809050403 70
    0x75145043d4102e405110b44d002100f1a810034843d41038548840d4103d0300c00380248040031514915498040e405440b005202503040400002c031140692002c078000c1c41d49071081d039018095022050011a000741c1ca58034424520003050146800c0c4140c121400c0c50f842e0702c01e0902c80111b0300918001540090320000c280d0240c0d44500400c0b840441110500000d09003950b035200e080e00c01c54040c1d004a070700424692082c450740e502d00f2000b2501588140000340300042140daa03c2c0781c80d0740c0d4441c45810407001041d0010f020b0340081034500d0180150700948205200801c0405d1450310303248000000441001461aa159045e52030f01e598400740c14003800c2030200e080860400380c902242182d28918110000c0840401070000140c0e44021100b1110170720554252203840723000d000b05101c407105200034458801d10041c23050081715604030181da035010b40c9603640b60342d40340070601101c02004032010703000403400c0011054030360044915601e411079860000307401c2707511640300381c1c21079409503000e030041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 655659289 1250 655658039 655658053
    0x50d08030114040f0c262e12031e030e03030610030207050601030b090d09060813031b03081803042d030506091f0213260304140907050414010e0120 65
    0x206c0c004001000341d10307811883e039149000020084100d0002a0005040b03603080c2c900b0700c01c04072001091006e00181464140301c480d80d031030040c01040341d83c0340b5111529400c046009520340284910307e28101c440024519507558501040303020a540541c2000f41075090040c03101081c0c04115050217580700d14080c080380e040c6448558a049034852408c01002101d0100380000b660088400d03401c155070b44015410713281c01c5c1c034041e80d2213a10302d0000c040c140307010905002455030109080340650008554503021000580c03d80c4e03103034801d070f00136041c021050004513004520307009103045203603403030950a0303c8640c0c50340d44482c1001400d8480c20f491390301030040d00280103101481b03424105d00074403086160089001400080b0500c03403140c014080e56040000400c20351240f540740340140d80d0016281c2da0743d00d82c190101820004141d160140140000040d00c20b4022000c903419030313040e008118080315003003004659042d010481c0034108144d80d6106c02c0b0750300400c03200c86030031085c90000d0440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 655660539 1250 655659289 655659317
    0x91107020307171504020f03100c0806010912080702040e070303020a03030b0d1110021024060302070302100218040c030b040506031f0509120a0908010501050d08030114040f0c 77
    0x1400b62150040c603000b0104001250311500c000030300200c00058086a00d0700340c0d90700d000189044550090842c0c160203000da4541c02a10203510455140f0036540300c100307968442c0c00044805510303600a500048406a40c02d0000c00e2150300646003031407000b44081380070074034924610b061201e260700407400340e840400060105034140c01440500a02030783c0840c04404142c4600500c080c400f01007074084c9000c1c0c2000e0751341d41d2080c082c40000c4280c0c140144000b6921951503401400240e4056000540301040031450318441e008071034406415900900c8012940d10100d002903000c0000558007488100c1041003d850302d0082620710f074626100000c500000600b8403096030f0005048600c6034010030010503201071803219500f810b00d220b0702d00103407903503420040d070b890400c09601810074500d001c1843c0349150742c003000c1402034030040300003400b0b141d985c0c4040c000f114018a500410401d4140700500031000a0300c01020a01c400420118048000c3c0c08410100ca4490040c0300000c0c07511002c13034070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 655661789 1250 655660539 655660543
    0xb04080709090b0a0b030c06040815181c020a020a151205010806070f0c06090807022d0f011e030e1e0303040813030c08060a0e0a0201020a0602130911070203 69
    0x308001d14062040c1082c41d910b8110888005014030319065442c04440100d4804000000d140c100140095655a807240170705a03a4081405500b20b08074035550028002d640d4240c8020601c2d4000801011080200380c1030713401101030062490110700c079603448800541c4d220406000207018002c0325a48610710514020217400d250451460b000382888010000940c00007551540b003e5149806140081511811113640351700c1c8001070440f0741049018001d02031b0082c000c165540c401c541466102000c442032180c680c800004e200354041700540b07040040d00b030240d56403032071000500d0400071107079450f41d00c542200407400c11400000c0ea18491800140810880d0307002038076250000041e0004100e003c0c9030780c0c1c480188010501000492811401d10a22544070090750340080b103003003410b495011030756417244115203a0340c8841c146160b020304d400f0046804004590103030f0241a0541c51603c40c0ac029500810701095619045000003424241d02d01c83c000e6000d10011030166102c0031401058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 655663039 1250 655661789 655661803
    0x14010908010e0c1c0f0507081c020601180f05070e041a0a09110720031501030807030809070b0a020c100e0604120317150a0f0503030a081b040b0408 65
    0x114160380340c03020900c0b21a41c0080c0d070103401002103442d80030b041d0b5042c01c0f00c0a500b00d002c0000700414040710300781d01084000314140041d42c82d401c0441d620701c1c2110f50384c05052041c1469801c09600040018001100084040d61340d00c1c00702e60001c1621415908010100d68080b105280040e8001c078101045182ca8041d20741130022651540c000410391380c0c0041d82e0381c962407060079102540d81c480b604481d82c0401c188d541580d0070039503d01008d11005c040604540051081e18402e004145158a815041c00400c0d81a01d4200c11014240202950181c03100c042c040d290702c505106900000941e0f0300580000d00314542c00b43d0280000e01116000d100c80b21000049030030911141081e65100d989800040d00d040b100200140300e4102800e00b016140341c100c03407050850420500703042010080103080c0c0c00c03000c1e0304143c81107a001a51125401d0481d6050301441d075054104000c43c444d01c9215248140d0020561201448420b800000000c1301d5409079009586100c0f0200b0100050306080c0002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 655664289 1250 655663039 655663049
    0xe120307050d0e0a0f0b0a0509060121020f03010c05090307150206191407170901050118020a0e060a030501170a031b03051224010c02030d0804080d06140109 69
    0x4508508100d40060201c0c000c8501040309180e86007030020750803104010180b0203507042101700c2412401400c0451000404480030070a440c14000810b450388000641070341258000c42d2070f00c9282851031040d1100300742d0b41000f640d00c80300e01c1c0350202c42c0356028800d0000701e19a503140c142e0359a4001050606020256010030b45107035280941a21082e00030594a6000580010300f58800c10041500c1d4018604210140000c4c1e00290820a420b500700d50020f24600d103440d42001c8a540c0c103001c0c14280c820900035040142d601d8043c141d00601c098000c1d012240f80c5092602401030f18001280480c1c10984026000139240c2004010854a004c0b244040206143c040c1403106600d441c00382c0107a0142c1821100b02c0e4003424900d040c14821070641d5231610031828144214140045c1210081e00303111140301e05010902c0c0c80444641c041c80c0c22500c242d9001e00902040032a0700801e450a0340001c00540d0710070010131100c0f900a03014030844024180032681ca4004691030000184a00c48680103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 655665539 1250 655664289 655664323
    0x204140f06010e18070c031211031008030313030513050607111008070c150b031c0e030d12090c050306071d060306060d05070e030a061b0305010b0307050705010b0d060e 74
    0x160003100ea1540d04c0c1d480c2c3c000624102007941c2c3e01e440c5002c03505540c10040360344400d0320744101ca41d4083c41e503000560180c141c81003c000b965445052681c0c49100587c3c2c1c03c1c28040c404100784000034001d00140a601d220941107580341507035080854015800180122480c0b0514960040a0b15003500d01410342c0086141c012014600107070068181940c088002e081c1c90400341083d400504681c0011300010005419605034046002c1c9030508074000d04114004070310301c00241c10880c00c002514650405c0d07503a48103500305220311840401090304600549200382e0048020902e518104886401900540e4954030300d00071415500f6824003080300300a11400040041c04155034501c0103840344031150600c00100c0c1c0c1c0319100b00b583d032045141d004030b8044c042d1041a5042c816154008000b00000c0d0000070a145411102141202c10901130a0b0f80c0320340038004600418420006041020b104200000d419200c500004040c0d5165081c11940305495001c051001d94060001c00e5100440d0070b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 655666789 1250 655665539 655665559
    0x31c02070b09030c0327040c0807030501090c0918060308070f142409070e010803120a02070302070e040501090803010f150f020601172103061005090d0f0204140f06010e 74
    0x40ca06032170740710b25860345030315001c040080d03281145007a05210802900a02c00c00a9000c034200c0a456600115a16404a880c00303000083c40052400703100d000c0f4402d580c8040e0003034140004081c030030742030031140320f0103d42d500360100003d29031000070007449004101008042050740b03072581d540700309003070200c20580100c04041d0254000b224001a4450a0151180782d42da40840903441c0c440d81350b000c40070261500d0000114540b0100082c074062000512005040e42d43d2604c0801341e00c646000100183e100320410412910110516900503104100114190085480d00061030300280c000c1155844214020410b4008042d0045a0341c0e03041c2c14080700c03070100841c01a4980a051183d1020821a00300440e03180409020b1104110383d07030804015061008000c001803038000301c03111400380881c2c009484101c0e014800352031909000610681d03a03c041703030ba0350754080c0c0740c0444100c1e0002c4e110b801144118161480c0c1911690b02d00072107043745d1030032600050104500168144c012a1081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 655668039 1250 655666789 655666807
    0x3100b03031c0b0d060c02011404120503092b030507032f040b03090c030708070312050a110d0305040501180b0a020a0507080408070315020408060f09031c02070b0903 73
    0x4015154204141400030b0505a003081c1007030064039041010780e038400702c1401d0200400c40030360b10403001851650700810204108482c9055032a205603009003403070210111500d205c92207000150b6004e4254025142d442e0b008070310054840c0341c18861900c01e04003c0700380d1516154540704499104109150501c1201c81305104d000701d601caa440c040c02c042041401d151040b000002c1124003d00704448065039910300070b1a43c9480d5401403126521900881200258082001421b081a05d8024000700f0712001410f400b615154842c940d04001e0016407041e901c21b034481800040025062a100070820b40b03000c1c98104c0c2102e0719044000a503c040881501c0031a0720740480f690701c08415400183c7c0c440569506890074020204000c010360307030014000c200200c0c0404e00d801101d02c20040e0780c00a0442d0700c6a1004c1e400749014000841d0700040018804051100c00241c10038183c0054a10f8400c80c1c00c82d401100c00161307054181d044c3c0004004041011070b10742d09074858410805903080040740 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 655669289 1250 655668039 655668043
    0xc03030e040c051224030709020d0f11190c0807050f21311e06021216020f09070302040f0902091c170d06330c0c15050903100b03 57
    0x30702800285c401d0034400d0340307144035441c985a05980c4000c049034080b47d035a40003000030358082c4407480c2c1c0c5282800b00320011504640184a0521824400241819460021450540c804402e04020400c5000a82d008a1800001030400b07a0048000c0c050b05180e0a100c245410603680090125903d01e01c40070a11500d0b040580b01e403503c914500070200c0e003540c401c01c2021418041e01c08001e00003800b00180c000c09500d040c2c080341c01c040e1104102c040c0c0e07601c0140e0712089042c0c0c164401e00c01c01c0081d81544c03001c4600342c85203d0300c0200700034640c10801000c10402201211004042907001500740004c41301e894840c401825416003c2d45042600d0010601c0c080c1074440d20714071000e80015060400020b0b0f1022014a03440b400c000703444501450914010303051500c42d29070542008001c503074040e03400d00344000c003200d120320030b4141060703111004464440005030262400301440601281d0030540d90700300709510a8603950143c0710f00c0410101400e1000303c800b001d0f006868000710b0a03442e100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 655670539 1250 655669289 655669291
    0xe06091507050c030d06080a03170c0304020f240d11070f060518030a02030a0f08060904140c031b0a050d050715091502061f0608180a0c03030e040c0512 67
    0x75070315005449100840c0e809145001d10f590006065003821804603400c2000110160b07402c0c040d03903542c0740c40e9010405e402120300c4152140e6501d10380420015001d8104413604801401300944807a030755440c0e40c062a03041c0242d06e01054400000011885400c1031240100c02c074520031029a10700c0c1c41d605584031091410000c0c4014501e40d22040011440ba00307028980c0c280c040618190b07941c40b112080025220350109a03c1c0010036030500503100baa0303200c2c4c0c0605200d008003510500464940352030f1107420040c0c00d46000b40d030b88101d8514114030344042c040000c900080303a80d54a00001d0b40e004100b13080c0c10503081140603003c200590000325030009821000c07101070100f168501c42e8400302c120f034240401d030022003010159443d000c9040b640041d005108508881e000c000000084502d801614154403c02002498690108507000c400d0300310100d05607040c90031202440030981c0c40740003c180f10b5200b940803809410541080741051b0040028400c003618100b480c2071840944c80d018440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 655671789 1250 655670539 655670551
    0x71104110c0a0209100f0609030302010c030c171f172104031103070504050f09010506150d020d0609090b0106030c26040215031314070f0b07050102070606090e060915 73
    0x4c0e000400e6000c0c6807201540d01824540c04c2010302035840f21400b03000010743e44811801980703010094070481e4840c1c4110000b0305841d80d185401c94180380040e00d151400508084810b1040460a0764100080115407005041c204840f40410180400e400d04100c2404480e841c114554483c400a8401c40d00440c0e0079298011842260840c07d50080392030301c5940e400c60f0790054906000d0000901101100e10300c00c580100090109990300383c02d11506072015a50190030703640c10301030195418269009401d1400050200082007580d07545901e054400c0c441051b180700044c40018070100354036000d08000904542482d010b0500d880110304011a000d5003c1c1c0c80300d032001c101103000c540c0c610aa440f040300380720207469102d0034004840f2141d0349d6100001c0f5034016608489902c074940119014040307581d03030300d0907a4032a86003a8800c2c58070b40c0400030032501550700708a6440060218400c900150454040000d4003004500d400340c900344000e808001e40c0d6004401940340c0d200d401e5a80e40e8801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 655673039 1250 655671789 655671799
    0x7021e1609060f0510020703301419030207050d030903270e0405010b190f0503120307030504240515060c100209010c0b1801050f07020a061808071104110c0a02 70
    0x11701c14090481c1080c010760801855210f1800e02c4042000070140c903844c03104c01c0e0300b02400703031b03c80d8108055500d2420710400518083d81400214011046900e0440d40c0980c50308015140100742c1d520141000c900d44010703c0401e60b500b0401d02415889024118460b0800d000b9a29492250703102c4080c8200d1031181019403a500c00c00101080b07000c0d00824050000030380000086503c042a0b08122810f074001c5408015103024001003a14002401602d241960f9184506d03640f1125411005000010b000341c03401040f045095407101305180260b00001101302c80024581400c4100103841d0510307070900d03031003a007003402138525103a404030310300e01c018240d43c83c0142c7d6180e9580050700c0010109002500c5154020100030741c003555500c18141c101c0700000204800d0740d0700700080718461000d0744d040d80180c1c40b000c0302c10000340c49641f01c5407030582040300c0603090ba2126900c0c2c0c1d0302940f00310005c035000300e5005210001d0342028001d104062080d0521181854003d07010240d98000d0030001130710031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 655674289 1250 655673039 655673059
    0x801050604061b060626190f140309030a05010b010e0a38040801020c0c01050c06010e06060d020c1b0307060507020910050d0317220b07021e1609060f05 67
    0x3040076803141c402002c102c44812061484080086c070f104143c0d107903003082070040c21104926890700d00003050b200c9a008051414040e525103941d2400001910b2100c03651208001d82112031381c0030060f030038906201704000b207605e00c1c0100005040744034150303805002e8851b505043c011880b4210890400002416001c5450f0441425100c8540700211a01040c0da50000b0040761811064000301a5007000f034007150b80e42c1c403080004503411b101d1304200c141d83d608488014012080111002d540100c0000e0501c2e04200443c25842c08903030041a01c901e243d03110221082440e402c030070710595080c40803000b8001291403c20054024460120000d00c500c41e150005031041145018480c084c00000d000072080786150301c3c001d426503060307e55000074010900c00060845500b0070500410b0034904641c94500e010320350b92043c0703e1101500140950044403482c401c000707070891410760324a030f03080014120700ea031800e500c100c2d0442039001a070307403542031400912582c00e11360401d8007140c2c0192610b01070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 655675539 1250 655674289 655674293
    0x8010b030606090a18061803020606060f04050112140109060302011101150902090d1202010606080f0603071403030903060f19150b091f180501050a0c120e03060405010c0801050604061b 81
    0xe5000c580d45c0c01409280391100c10b8042c50b01075804000f00c54400d4003160070f6900c0300350401445020b006284c0e408080100020301103035100d41d52010081d4411000841c4021425130300800d10740c1c00760080807103240da8210800541da80700702101042003001c0000c10880e00c0c5881208440e860794041d01c2d040d140c000a00e926a030311141084014950440c100070604000140000c0c0600400d108480006208001103039002c00341075841406884007c009000f4640f03800104100c070300d020700896605020a00c541c200d1a1014001203201d070181842d900c0480c07820540300d1800c1c0e81a141c0c9400064580340d031a4045d404500f913540c0c2a01c00914080e41c03503044480029112010440382c0c8032a40c0d5445103e40021034020b02c07100354490106030411210340c0c030340004540b51301500910740b00040c400c0c081c003400700d090090001c00107030040c0b4040c1041c1c0d5581010030f00c0c0801c165412105607641d48a8541c2c00f5601c100f441303024000865505103012316101c4020827010a9544c408032004500740c101d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 655676789 1250 655675539 655675571
    0x2111010509130b0a030218070201050124080403032c01151a07212c010f0c0c1d06210303180336060a0c1401090204051008010b030606090a 61
    0x4011075004081180c0041503032840041560181c23504000740d801e080c0040b8501d640010140c6441c0d1100900b44610750b5540c1c0103c41424001d00150145565159003580c1300c0c0f0481e550066140144880ca0105c00c042803c007802c4030200140350412440d000c909000800941030208400c10300900140d40768040b03400e00314803403079503070200d40c29440f00034118074441500441091003540e102c0b0203124010382c0b00294042540458005240000e0b01e01c40d409101d0307402061801c0d0010300030350b55084590740b03c0d0307421a40c00c5900490300a032100030500f0842c0600c0e1103845699210703040911141280000c0c40c0880d0b4a000281074051400d2031074120340d0032003402300f05452420100803d0940100c5200c0600f80350210741940018207007141c0c41c00c2400a0601008466000c803041c3d03545600c044480e21074640d0203645d440640415500d40c40c1000c0581c3c0e0f01c0c040c0502030540d030940f01140d01e10b001019400c542400b45880e000fa001441045216540c00100f1503000c0400b1401040e119003130b500c910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 655678039 1250 655676789 655676809
    0x70509090a14031b06070e0303040e01150c0c08100f060e01210b18100b03030a1116030305042c1909050610170a02060901030b0a2111010509130b 64
    0x1a0205813008501c81980200188450094849440e01074500400400f40b5407a88698051041e0200c0510f00420000132440d0324007982548c02c1c9080d16442a480d900c0d050040c0540c0e0004074a44d00c05108440482554032403050307030312250842001001d181402e0030f0a041014415107910081c00c5010801c040c01640c00c1c0080d459100c030040465151000b5080800380f8450319002041c8503c1c4109044890341d40f0964255800080041d401c15000800c1114001c401d81c2800882d8001e012000150f0803017681d01c2c0d005144070380c59003900d9900b4180001d100307d0043d038800c00c03c1c07510350511101c0414400440b640080310209008900f03215031401501520b1407200042c5284240c03000c00000d55a81c19806013a1010b040210140d0580c03260075980e140e81c0800d019500040130483c00407550b020350f1009000c4100a44614102ca54908040090000c000c40b1044801c0150b03540304204041a42d40325070012003424011b0400a8800218041400701041c034500c85030f40da004004696038400c115 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 655679289 1250 655678039 655678057
    0x13051909061212021b0907090801020316020f06010b042102060d1415360a15122a1e0302030d091505030a150305030c070509090a1403 59
    0x1030150300e075a00107000c00c15007440b80c195419114903000480c1c241c0b020409542e40c0c20099180143e4401c060b003002100807000e8400018085c103c00d00182e1082d0a00203941b26015181800c4422440c83e2006420301105100407807a0b0b4019000601407050100c059400f0303500c40f102c10141c44541158031181854040c2400b0b540400017040f500f9201d01e0a030403a95002c9110000024141c992041c10200c0722403600c207840c1d0003540b81d44030b203049410040341850f01c0c0c0b40305508040c20f503840d801c0c401d041c08030135920001c281c2c0c4c03144840720320940070f000d640005000038114001d01050715181d4001c15400b0b8492403913403080281c000007002402c0e040b03801c05480f80c002d0a0a0411004000d58070201140c032040f8000e00030015902d1701603001c0d408040c2210012582c0203404c3c542030340201d8440c1e0005082884142e5900c001038803212805041c1c8018510407401160703158100c4020328a0808a030380b10340d04c00c1c518003040003d0010085014604e0310f604c4000002018841c4001600314066003921b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 655680539 1250 655679289 655679291
    0x81f022101141302030c07080d0f1e15051c06060306051503070b03060607120309080706020c0f0a0201140a02010f02070f021c050a170904060b0307120213051909 71
    0x115401d502d4501d52503038881d048030452691103c400d164002e038001110300300041c40b400d203e441c010800d008000d02c41e00428110010701c031250451060120707030203070700b80040a92040e0144851864244501c25401c400c410100c980e86180100080ca01b0824524170032019424504000c2003000c00c0d04414040c6a00003014800780c81d081a50fa800543d90101c024401d118120b40000c000c26480201c90140c500500440d03c0e0401c25101c1c00300e0700c14282200d404051351400c088012501c540c001d011600c2c4258409655158421204c0f85030580f042c6102160f42c0241181c900180c1e00121844c08081060102c15228090408140d005082900c003a01a85000042c0c84080202c146501407169208070b03203030401c190f1000504100b003012120010550303407050018001080c80d00c054811070380e240d01641483c01c100b4501240544032103500000305c410307001c028040c2180c0c10142840d851300d04c2410841c20401c2000840481e00f1081c40760f00e010f0010a4450803620a502134440003404010744 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 655681789 1250 655680539 655680541
    0x5011d01020a09051f0e0d120302120108242a0c0f0601030809090411030a05070302090c13030803091e0c090a0b03060a0c03020c25081f0221 62
    0x240980030358040c0708442c2c00940c0e103800c080394500d4a050030196200b0302820300b40404207182410340384150300300500e85e0f001400e01e5224000600000c40008502d14580c0c002da1a408140001416148181c00803d00d0381c0011450508403804d0b840c841c1507142d442c820121b019201c140d040c1120060342510b9044048181011031020581c1c90024024142201c08507480c0800e100c0c10781d41c0329882800b0040c41110f041000e201246050300c0f13030503005401441800d9045800c0070019107030401c0e962089860f90400e100420652a140040542c05502d103121145810000442c0700310ba1020790000800d46c0c0004070204200a40400c00c00c608100c4451008035070411103411f0980c0e035944660740700d2090711110b00052340441c03680200c001c66507000d401800692035008145003e042400c1143d82090303070922041641c841c0810034100c01c45480034005882c40c1c2c1402542e40f000c4010380000c0e030345a1016002c1041e12035039203c40c10851280480050b07d03240f1128144014a000c0c04014541c500600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 655683039 1250 655681789 655681841
    0x150a0b03190c0f0f15020718050a06080d1b06200c1b06090f040b0402160b01080d20070b030106030e0c0f1c0312090807021207150c0501 60
    0x1141d00101805241c14400a41e61140385071206111402803a600000101d42001860f1000403085008030050040e500344a49500918680010b0b031480201000d0311401403200715500c0d1b11414014001d10b501802c400d6041503409020003503a0805000c0300d03070180d8020020f00c180e44e0b10507203180824020f0032100d2440c00c0c400100320780210440070198016046408414012800f004882c210040c280500385551441040b409022000100e40c1003078658101240302d9503184020940306072030a10300d450070402d0b41415a18840144c00580c056844201070416007034102c1c00c0f185060300d40c0e804145186034819611424207181e6405000e0800f004400480e17425016040012036003203980c00c4552880400f010001c0c000c6040106a4000880d001c00980c2010a1600910700d030f0f0007418074103000300d13401080f0340c11030300f00010a45202c500460120114905000c0b070552645081008046050038400d400c0907801c0031070b40380410304c400305810300c04002c820741003009102d510760f41910518440c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 655684289 1250 655683039 655683073
    0x1e0902191214011206180c08010f060e060904030207030602120105090c090a0308090406180509060c04030c0902090f04180c0503030418021b250512150a0b03 69
    0x9891000118603180c1107000c070715005228848500080c1040c9100c0307640380101c0d20452405400c410f0b14943c1e2100850f900c83c0d119030a1940c026403190745844c8407286891089030031101040329449250b0b04281c01040300d6460901101d400c21421078240d50241c845280581c40d02da07080e40300a160a00105000305202105161681295001d840c00fa08076600e004c1c45200e54450100c0a941c011010300c01440801c0240d0081c0c030b413404d405003000032026140c106011202c6010b00c00c410100c1d407280100511080103020150700481c8040c0302d07034103283c00c641d0b500102c590a400340d110030a6000c5100c900c16642d02c05049600440548104405041c092410440c9440840c055070760b40c00c610070010300c0d810001708035030465003012520100700d5004c1d042c9001035400880c01024005251000144074101445081e007498401445070714002e1024032049002c004546c45588103260612000c0d410020104125518440640038802155034900c0c84000401c600010f0507098414144120998805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 655685539 1250 655684289 655684327
    0xa09032405070c030c0f06150b0309330604090f061a030c0a090e0c030106080d08060a0e0601081e0108030403060e0604050712050703080a0801031101020c09011e0902 73
    0x200d2024402070391038101c10344110702d030910010001130700800614080f0324141c030001941481441d002c9400303034040044282d020520f80045100f0700000052141c061301c2000001214404001d205602d03c04589403032000880380582205212000d2001a00c07035a203030340c010408998030080e04c0c4003003c3e6900300320005000414010403100402e0350404010f10b000140f80b503802c503005060300010341c14000100050680300da500c621a200e40340340740c0044e50b02030080c20060503108009001c21241048010044071014240d18040c521050062010040994040c1c0d0300c41003c2c01c241e00c9584503c40b80c1c155000341e0b05045d040c400d041400203d50745801000400889002e8807052115118071004540c1340da400750340042940d8400b0f04108004055042d900340f42c580188151002c1039500c1d11071203403a40c4580d0503c4c2c0081c010303000600c20480708070700c40d070000a020701c01080c079400d01e000480d03071121040c01101c80480751795003090f0451807403134a928091b0941d01000c0d910381ca00d4503510303d2000d00d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 655686789 1250 655685539 655685603
    0xa0e01110d0f060506030c07020402070501141e13030e0102030702040f151703040512190303090308071e080c09030f0c3d110a1a150a03080a0903 64
    0x106204160b8803010075402588180e61008003007518548400541440d294814172040760030030b03000c1c02804045075082c403549541040d0042c0c2d004036407400040c4001c50480300100d8145501505051100400192888030016981400c2c2516a2000d101c0140e107180a00e0300000c0d03129080c60b10341e2182511310f801c1018034194041030b00025603110740c124004c1020160003658181d001384420000f52818002c005003604150060fa60500100741240b0780103160007006078042500c0d2a40041090752101c0b00d503034410303058a0000f0030710981c030681c0c07144140c0d040700c41010000450049550280c0d84021a01e40c8203000703084440601204902d0b50301c41d961307483c1e4684914180c4010500c900c10885100351815034810101c511044202c03075458840c41d10080b030404100030350404c0340c41c1d28020404800c5032802242c0c144011544411200403440703006058a100110880c0790b107030280c49441a600c1603962000000d92240c824001c11902034440d9440648a60015400e01c00394080058040060030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 655688039 1250 655686789 655686791
    0x18041a06010318110105130905060a06080f04021527041a0a0b180a171614010c02182404151e0b0d0c17010605040e0a0e01110d 56
    0xa56503400640032104041d0311030032040010810400051012100c480360303040141440ca0624248940c440b501c0302c19030b000050b009070303104244030b22460303d800180028205490440400d1501c1c20120100c680c014000a001e200126140a42e0040502c140ca2200e10800d40311070036442e102c0380b01d1080250840e00a4000ca141c0042001c46c2c58820f0005101c190000c0c11000d00309152205156081c0e00401082032580c203854400c134038555407a00c141c80180002030100550100904426042c0391007020382c0070301c2d030380038040401803041c00716410440c42c2001d003045509046940007041450f1840c40c004400d50010100304580101480300c481c50580c04e4010204175102d1200500003200c0702c04450109a005080d41000144c03502d5285080400600001330171155407510401a26000307001c08001e00b988035100000703000d50000318402c0c99119400c1090595160030805041480340d40980740300500c045000503100e0459803c43c01099010b0340c0204056000a80c0000e03158200c03c5c00d071506a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 655689289 1250 655688039 655688041
    0xc1710230405090f0a0b150613050f0f1012020912010603052e09080d0f20030f04060c091205030a110f2e1503120504081002070218041a 60
    0x3c04001190380c01042403400070b140c1da041316111080c0c0c004004000484c0b014032031030224195100c0a014103000758207550603a078528101410001d5040c0c80450b41c40c0290307010b550b401c441e542c8100c81160100d40b1420102c1034025407440380d40203842079202e11600115506006031040c00150700510480e80030304155141e20070740920840a107455840d0398518510301c07242803096020301350301248907a841440f00f0340c40e01d00e5411a0750182c0703100007001c4510507501c608501c4290248092134070013000c50442c2d18071798640a0050303e0f5491006c0c2000d81803030ba980b04441a6180500103400141085129007042d5040bd4606039a981c0d000c00303502000552821103510790f40c0800241c24003c803c010000d071018000300c00821440c020382e242c0c03907050aa80c010100706013070450321540c0a00c030184071000c407905046080c410005003041c01a02e04010041104101c4514081004c114035040900f0150f034840240c00080c40741c80380c01101a907401011014001040300d07080c2041c18020300d114040303441e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 655690539 1250 655689289 655689301
    0x20a080a0c240f090504051008060114090a02090d0b0124030603021c060f0612060b1203250803090a030207170a0320060705040305060a0c1710230405 66
    0x11181a410301d00c440340b001080080c041c0c41c015146010074480714076000c1c0403280e8900009054450588010b00980140b01d0140042030082c0822800f41100c080f02410580c416000f15138014002400300c1d402980c0031422212030f584041d541d40c84d0235000b01109030706586580c0c8116031038241030032280b500761020781034008440c06030042c401181d4004115007100c85042c440c00e20015a080b0702152129035401c0c65030341c038038254490040a400c2010f040f45a031492071802504569129494610598103010f207030300150000000c5507410000c1c004130100e003000b001d440303905203249070400404e078070408410001052400100111458020340c00c682030a84e55203c01d950b03208060000091580041c004880841e01a28000b0005504a07410150101001042d5400c000c02911500005140040c041051010400205401c152107082c100031080c005c01e405800c007010b4030545104201300500090300b1014101e407407070003041c0c09010600e8450740d20100c1079805840e021103900c140d14060100f08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 655691789 1250 655690539 655690559
    0x120f03060d06093905040216080307030c11150c0f1c020306011e050f071a0702030c12090a060c0f0501090320150402060c070b0f120603032113020a080a0c 68
    0x8600c13010500280100343c206414840030b5400b00f4000c107401c0008051460008203400020761103a0070316900011080f2120100520140c403000d15030310554455801c141c14920141c81480c0c11800030395900755690522030f1200b02c1e500409414404840c800350070385505514540065200750b009a9544100804021328002c50b686028003906c0020401d1000c40102d10380f0000070300c2074600504006000f140c0040b13070207601890803620b000c0142c102040328000e0391b03020001d103c80d50b03000902c56424000e2040c0402c050182c5440340c602040303901340c09541408060200d9402c0d598210000344103001d254103000c1c1c8640201d4400c40404114221511039100740490400441e01301300c40d00484540781ca4080000e181c1001c0042072250040c00d0300060205030510003006440d45110b0120740340c02c400c0049201600009042c00d00a802c00c01c50f851843c1d03000c030070b1907104040d5540340d442940c8075514482d07011203e01c400290020041e5001044400c000100700303200510990f00c03260040c4c0c407242488 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 655693039 1250 655691789 655691873
    0x1905091b0103021603030f020c0f0a0210080433021231021314090607090f05030c0420070f150b0603040b040206190804050c0102120f03060d0609 64
    0x585070001d51380440c0d000038801d41040d009000311040141c01c15910001081c180603140c40c030741004d075001d08801d00850038490401c00c129a841c0c10714414521b8651260007080029144a81c4480610440d0342c511465807100300d80714602510007152242100080188008010344d400100420240c0700e185015440e0207032003000c5030100d01c510205107010750a0060381603080c1611210300c2d4031002009050148811940e200340c402900414203410400740103040c2034959000300414001440c400e208580f0001001181201c0654000600342040c081980001c1074100c0960005000095008107010b05901c0c0e40c2202e6000355400381c8014403414040d401c8900004c030b0300c6c2e00404280300040228003244040c0f41e100b4000b6205130700d0103c400e546001d841000040d08400300784a9000e010900404000d611013208003800144036140c1c601017015064015401d510081c1ea90000002e05680c840321050b0400f1540200e05020280321858101d1098a201405490742c0100d00050300d01d2901d01b0b2000d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 655694289 1250 655693039 655693057
    0x916021002030a060b030403023306090403031410031401021206011d0a0b1206091915030209010e04050607020105010b0a08040201200609120f121905091b010302 71
    0x144100e10218104501a40006200d003541c90368a140000b0080380368001507214a20030b82c050141074480c000f050940c3c0f100362030684410325608401c0e603020f9081e03050441c1c0009045801003e03551302c07464210060015003000c1d000850860303050003003000b10503207a401030380d103e81c54800c0c0c68403034900e20500301c0c050080116940350100c1d01241d515402450000342c0280888900f951400f85000030482c40e250030351044414410000d00721079841141e103d00d40c6c00c00360880340b00c151405c1941840c42c0e80d80300d045060355465503a001c0781c0b21034683e543c804401164090a80700a942c3d6484034a2011a004c41e42540c9900030300340082d02d418810b10070141617820344400781d0f050620703180c1c0485210500400c00c81c140b000d002c00140c54401e884284094a05007000140030798a0070070101030418482510209030007109100c5c2d20412000c2c00161034880301c80d8004504d00e03554801000c0040c00c03030783d203104250718034003014420034180129035101012800034400d01260740e644011801c0344240864 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 655695539 1250 655694289 655694293
    0x30f040b0613110301030201031109090403030f0b0d0f02010207150503010603020319150302120a03090905150d06090b01140306180715050c010c08040b070f120204080606091602 78
    0x50000d0408031199400031406008000d4540030701c81c500c001c6030000329542c034503050040b004104660745402400d1508192551441c1030050107000b09100c500082c01c018141910b0318503e0301c044003241c0c040c5918210041080700a09030314244000910100002a801800386c01b00100f401c0000031440504446290346186c0346070708e4114104d0080d0805401d8110560b602c1030081d4485003680180c0ca04040c0001e142241b0030300c0d510400c00c00b154409a9034100d50006245000070a81002d0603000b00d82c0c003184046150f1b44c4a0320f4411700c0c1001d000c4001d40c07241c2c5102c603104c1440203581c0901d5006114400300340c46a601e848501540010746044c40da811390003000000c0e44940851240d140030320f030716070440e0000703511503014221030111640000c000480105610f00000424060090841640c0c140506241042d8603084400c001c014052018000400c20700040e80303124901c0b241c0c0f000000501191900d44039040b40d40c44080aa4115200d00d0400d0042104003100b400b0b14443c010305030300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 655696789 1250 655695539 655695541
    0x3090603040303050901141e090d09090e010908070b160201021602040b03010608060a0e07050a03020307032a0308030105040506010e090112110406060f020601140d17070c14030c06030f 81
    0x1504401800d80280948111b54030f9420034290384004a602c6405000441e102c8814a400c01000015a1030028041409a4400d08540030b01c1a08500d0001c1030b500d0682021038a4115041c4050160011040c000c15590700016074109100c114040d55008060b5224036240594403803c0403030a034003403801401d452803c6040301130014035103a030080c03541d0700740a800030030840c0d551400c00381040c030212820030005403521600c440401041c08548040c00040b0b80380380c2e401e821900400e544455071300000780741e01c0081c0d4900300308010581001030210710b5400e0a803055a100e14140310507800a1088502990909010030318a60245d6021b800307014000d01803800c0c580c42c2c5500740504841c100c50503103858a0034000a030303680d1550f018810182c1303000c0d01e8400901e880302c44001e1400308140d0110360380148101c01500700d9035130002742c2d00c1540d41069212800c030800b00c075008018428004002c1201a800078001000455502c240003030140c03c60940e0104802c243c2400341c0740c07004a842c0c1250907041c6c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 655698039 1250 655696789 655696793
    0xd030c020607200a08031e010f12031e0504140103050411100c060e0303010302120706050f030606040902181903111201020c06130c06090324021c06030b090309060304 73
    0x1058005000f0480c0030210000410501410300e10181d80c1034585641c00410002c0e800100000000c00c1e600c0d103494400550316140d03d0b503824031200c0c0110103402d149124074105141c0700e030040c5075440c100301038440b5080300e20b0a4098407542c81445664100d100c0200002402d60103807045e0b51013290483c2c050641583c0d0802042010100210200d040c05803038a00b11001c00d00c00d10401d141d0f520454002c582d69410b41c010040320180640c40c189840d4008a402d210242e440026149c0744d54840400a0326600c03100001629402280c0200e10382c1880070408400c10506403104086106040c0c5885000032001c0790241a08050340c040541801c452a4601c3c1003420700500600f100f240d10400107007404880386086003864025250a89000d0343d02584038103000b02e030245240100007500341001645d01e180da840510203e105403019211500d200c0803981c0016940441c1c0080d4100c5c140c0141c0c04200c0070040008002034003040c3c400c66030040004800510000403240c00160007000181596965 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 655699289 1250 655698039 655698047
    0x2160b0f070f1529030607020312131208072304030b0603070e010321020318090717090d090f030b06090703020c030a0504080c01030603031b0606030b09030a020d030c020607 76
    0x1c0c0800711400703044219035001d4403540e031107200000e8064030301c2c0443d4204212000c2c0c0380c135109604100e2190300b000d0103104200b90000112400c4100d508c07074908013a90b6507034943d813952911106c0641360315803699146504982c403410a502c500410b49588681c4d4020b13110440f01c0d000c5401400da5441000c00003030010880700100241c0c0544020111601076807a42680c06800c10280d10407203000c154161b240501c075080061564010999100a500f45400d045022a000c03801c002024003490114011480d150301c54140c12031784a0b01016100003e0500024095544800c20002c0740000c12a401c0400c2410624114204882d00100f80000c55100c620400540c02006804581131680c00c2117804c00d880703401d00241c40d0140d202d80355691518984000c503400c0c40e90b000c85581c10140391201c1840000c2c1c001500d28052440070381c1c0480e0049883c94200300818050300094110307843d0b04d00704400311034008014010901c855007921050f8a500909a050b200e80c01810005a042000065240f81c45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 655700539 1250 655699289 655699313
    0x702010c051c0f020616201009050d092309040204090209180d051201060311270a0501170a0b01050c2506020624040f09231612020d1202160b0f07 64
    0x440c00582d2303a402a01401078003110b0024404450640150104c00301e42034100e6050390080480c94044c149000303000100064011540c00214414041c01d00840c1c00c1d516a54407010010758086c1c20100a82010b442e41c3c079490f8550b04c036420f518411035100c1702690340f107003003540c40c0401c45450442d0142d0800d0030540141c2400c1c03252404840c001d01c01e01d002c03400c141010140111680060140c41d500c100140300180f00c26070030550500c109240c10811124a41c00b1499228916000002d00503005800480340c2d0700c500e070000c403a02c0c0b04484d1068041e44040080c00e1641c0310340c2c40309403001039a030282607803603000c2218030584920070300070080440c01c1034178000ca40b9600e00510008203c05040c8030304040320750b0b00b1010303070300003404641410108ca9040382a0040e0b0701d4150041101c1c182412000850301c01a01031011401e050400e81811501d036454044202a40481d01c4500c0400b503000003990f5015041c242c0c040803204141c0040d9000f081d004032007005100b00111032a18809460322204004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 655701789 1250 655700539 655700597
    0xc03260103420902030d08012321011e020c1b030303040b060d0807121101021e1308010504080309011109151c0615030b04110702010c051c0f020616 65
    0x6181d0480c43c0041e503061283c20b5688aa40c4c46d511004d5060005c84048014140384501c00520070018100c0c140c7d07a131101b002050f000282186c51160803801c2d10701d024200340080840840c2d0102841c0c421814aca4018103400c00001c812102d0000f4444568540340d440898100d805400800c045000b0801c15212180d101002500804094400c1e5840c4006544840d2003514041c80015500d00400d601c400306801d4208008001e50414a60b9260b280c0009040c1125101e5180001241e07165956020f00c103200401008008015074a482e0070011116481100d10702c20552902d0035181c484004102983d55080019000700440d011200c0c5c0c47c401036210001011848020341d945295105260103414060460307040301a1a001c0030880c040c0c195010504294880d41c03d02c0c04a00e0050b1100055030b12041d02403a105142c1e40844c101035060022200075000f00e61511001800b10325040340d9280c1c2e4000c0c01d5130803900c50741d0310703204c0072000348003c00300510010b1b4201c1c1d8444031441000c4030400d00c0603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 655703039 1250 655701789 655701791
    0x16080103120c1203051812030c09030c150a02190b070c050a0c143109080d02070c050a08010903091e0e04050c19060c030c0326010342 59
    0x21a1940030f5140118021440000e072140100151607a480c0030103111a05184010500108040c1e000d200340d0000400c01c404400000c0764034803056504100c050305004016064202d02010104c030b03012a58480b500510140c8251542617900c006440c80e5007401c10b421400d17402281c1c941c00342c200c400c0b040b640b4061310a4401c05c02c440c80843c040c4e9001d603009004800d5103800b070403101c000384404a0300045850007850f80e0b19203034111101e01d1540c148104000c0c010005000c101c00c7c900419207002c1d000d0008501d91005c1444e6040152504451058072000c03035428010680d00e2200d282a65082035000b03001510201d01041038985841d040c2c02600007612407103001907104c0a242074000301c200d5003030f2501e90000c0c4400e101d17407d000e002d102c10040c0850b1096403083c18440060440741d86018014100240648d000040c0361140d041440170800209100183d149585030131307002480d080c0010342d6402c000c014118074103c119692a003d191503802c5c03100b42c801c4000c0c0c80110342c506900c0f18105e46 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 655704289 1250 655703039 655703057
    0xc0e0604121e141501060e0a050409030912080d0b060c15040804181d011515020a08032706060a0b03061207030f2d0204020a030609050702070303081608010312 70
    0x42d101c29040410041800041c00c0900300304c49441100141a0702001c1800404001340c281c0b600c940300a0f41c2604c2081c0c601003036040052604440b56501c9510245e0051081545842000070b80401401d40448031001800742d0502242007007500d118504207a40190700c10340e2004031102104900301e610500032080c1d1805d2a40d00d445003210003040d030806014965842c40940c1d2034000002078424041d0354000200840700c1d9803048002d8084640c0070b01280140303800d0404c4400c2c0e200700030003c1f00c2caa0000b15561641400840090490840f070065030341d6028005260320f02a6002480511841c8018092141309282c05030311800c690000d44050781000a061191111842c200619001144a881101c01c3d00c811410110100089440f1000c604c0c1d40044104801d84803011405c0000c940485006940d591885800d40c01008213034010400c9a05000030007503407540108138001142c1c081c0d240d40c641c3d0b5a0300403030b0304803030740310040c40c11f0106d80d84000501c04035109001c03030301d0454590f00705a960 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 655705539 1250 655704289 655704293
    0x601050904240c2606030307080c0102222405030705181e13060605040e0a2309011d07120305131e06020604020906010305070315090c0e0604121e 64
    0x43c2c1e5801408070001c10850f00d480c00d0000b803200c5100105140c5120302803414200100040d44074465100701515242d00410408207501080d411034894854210020641400608400030900c0451007501c2441040f580d018603882001000c0c440c100f51a6a00c007440c42da0b44020603541c80e00210074820140c0062824a00d068589440c04440748610064807080f0428010800462415041c41040c140c0d00300182000011381010607141520406446400c00e0344e102600702000b4001001d00c00d85541c00d011035070314850020489240906a40360090000741c0c0c440f50144c2110910081010055021040800441003030480150b6203a10a1411601c2e06181d01001420340900750810002e40941c1e0102130030b400d0b9490215001080c44d4000f034134161030180c000404440e401092141850785580004511500c207a121804100c0e000050040031602c401c035600080610400301004540d8041842100d45000c1054904903401e08550000031911503480801d44101c2c0321000c1240c03d915040a80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 655706789 1250 655705539 655705541
    0x1030507050c0115050f01020f0d03050a1404030305060f060915030901110a0306050a0603050f0402150c0106060c06051312030f0b0a0315060b040f0b03220503130503060105090424 79
    0x3481c50390b40403181151314140400c0007040d0340c50b01d40d900e0540d03010204050b90480c5c0452400d001d0400d40c100003459940c0c11154002030704c2d042004100c0602000c003040200341d0507500070b41c0101c005079080d22900d00c0f840240a02845100c03001a4046544c002d04058084220000c5500040c8a00041100603400401303001720b8004405a402098440c4414416424a0300481c4002c1805240034005410074000c030310111940030700b0190140380342807403104003240b80e04222101e42c0f001c007000304445580c81a0003048807460702d03c05c81c0c0c12410800440c8458211107440d00d856074001c0c40340f010a45010005030000d00008001903c0c0d035448544030400c4c1d0307440382e00c0400114050b6007001c1c5000c4a62010f03200b200d034241c010107482d0500384402c0c05078080e00075060081d40c00080107139640e0b1720fa40604003d040c281003003c40c4940c0082156208100012012300782501ca200000910b4a8642040603100e28090003129080310404000a01150705811030a01c0244406500f0034958150b901d000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 655708039 1250 655706789 655706801
    0x40506121306151e0311060904060b04080d1403040b16030603050d0804120306180e1002030720060106050d0209271b031003080703090e010905180a03090501030507050c01 75
    0x7030070b0302142c3c03080101041c0240c007034408001c4603d510b80d0840c1155642c10070140e040d01d0041c09402e02103400111a08d07194031000207810340103046600c641d540e60900e82c0c0c9801801d040710000b4044640415191074180603680035035400310648489580742c03040c03400f002d9442c00c00b4004240c2c45260003c0403c100740165040404a03a0f1012114075143c1000440141000340c05d0007058503041080106040c242a420040311140c6004a08816080003c0d4506212026455241480002030242042c0c0000040300540503001030b0204506a03844402c0e215603007445184041801000401100c0e545a4001c205900d0000d0011103412002c43c0e0b0700840004408440006030801418400d014541030048403402815014861540c40c00d600038090054a03840000d0141d500494a41c0c00c1501409048020304241c440d140180c0da50b40100754007400003a02c00c0c040e40e0001d950380c0c40900300042000c0b000990035803034011070a8030b0b20f00114020140180b010081203414400b075040d09000b070081e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 655709289 1250 655708039 655708061
    0x405060a03080309151602071e0305070b0706180305090402090d06090302010507110106140907140703120c050a051905041a070c060809100e0a0602120417040506121306 74
    0x50440496610100e1784803800038083c000300d500745440c001c2041d540000e038802034803092580825020708400d0000190700c1e00d42c00017010340c0101d03040800c1c88041031001d003c540c0e00400080c00a02d90010324095955524440680065020403080102e4142178001301041c203000341c0505812591038840f2803c03121400c90490050351910b0611444551009030584060a020b0080140f44d26082e41c4400701800140240d019201c0540011071881c081e071120b50661000f800159a6108149402480c4604546402407800d03c0d1511031216580300d0001d848020f29144c54482c6081074486004400070324170340d030460801c007080201081d061600404000d00868443ca0030b92207400604d001c00c0100c0c00380d00f006040104ca174040100040c1c0c0000c00780406a0311907000510240b09101c407905140c55010090b000d40d000080d40d409000000200701c0c401d6001b5252400c0c801460040089548141e1042036840141072001561b4050160501c1d0303002449024000b0041119aa443c0280c0308041c0c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 655710539 1250 655709289 655709293
    0x21302090103050115050936090d051206040209030c041508060912030f092103070315080c1005070b0906010513050609040b04021306090b01030e0c030a020405060a03080309 76
    0x10010303196010701030709016201e03030300d004082c82c903031803500401074026010101e210b4503050030303900404c01da500e200052188607084604001000104807003041d0005907905141d0348104035030640c400c0d10440c1a00c0d100c0754110700320b84094641c141000b02a400100159a047c0107560f1424260381d5030f441130a3751600030003106411689070403003042c10300d003000b03052206540101000800300704c50402220382c001c00140640702640c0302d64070010714040c90429510f0350018180c103216241070a050180d0b10880003580c1c1408510b10303010407001a45514407414036140c0c404aca4440c80c0e447c08a0380c000309000d66280c06403d229040d210703010030130002da840c124582c100800510107401c0500d00540e0340c0003500300a00c041c0c10400c0200d2190000204040c0084c1e85c1c1c400070408640d44c3c2030500505200460042c050103440c2e103c0c020007402d8031140e050219107400340c040c403007400c00316044180c81002006041c00d5030840e0203100150000419150b440640b030480440014001c0300598003c000c1000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 655711789 1250 655710539 655710547
    0x322151407120501031a0c040f18060519090c020f01020d0e010e0d0e041e0e1c020c1807030b0604120201031d03030712021b0a0b0a14160507021302 65
    0x18015003101c1c00d918100e660b2a007040014070100781112040c8017401880a07001000d507880000c032103c0c0c1d0141e5081082d1501010a0004042a420411560101d03844100f001801e076200308020840c0c100c2040107041e084031100c01c010410465200080c0d21600b80155540d0364021100caa08903804600c0d080192513aa007020b2104890034403540c003083e1203000080c800ca4031400e001070201410f441140d4810f80d20780070080132400003040044900a0706050038400311400d0512580c0700c10641515400c42080700040700e00240c4000340c4000c05a10281c41200c1c0d0b442802e030f1402d40c005006003041c082c10307150701c0321400644038140100000c0c6290039281c406007506100050989000d003c840001078010480c0c00c01c20390001c01207a070803490900302403000f1844060000c02902a007680c00c5070444400000c00c6402034041629401144100352107002541d40314921000c40c0c00c604034a1014000800005003500c0b85095103005501c04c40c108242000200da0000780c0214458540988040d0045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 655713039 1250 655711789 655711801
    0x606170a0512040f03080f0f0d1b02011a010c110604080304150905010f0815041518020f0901081b2701030606051c0e0307050717010203221514 63
    0xc0002e0911001c0e28103079624161070480342e401095020f00001c1e04246c00000d030f00ba41008050107c400440450440f25121000da00300900200000381d000c082140d0f00282c21b402c06807061081c11105442d00031005440c01c00800110764410000300301306c0d0303906080c40c020b02c1140d135a10040e100801559000750750380e50804c603134030904281c514808418041c4c10b03002400140c0c0c0001030f2401803201454201c0705a0381e8000d0841003000511500e64110f031400c7d035005254000048000242c41107481e94455002d18440081c040b442801c4c0b1282d0321031000d000400c141d621803401c10750440421500c20500c0c0c81d540c24201c1c0c840d0301400d88961400910f048000300e030000d403941c2d0740ba40c1809090402107e450444040c00e1486250b5410014124140902507c168141d00c040105071000d000c4030340700d40d414988a556010f0038050707055400412203031081410014000c9134402c41400c550010001500100e02c2c40709408000103c0c1d90140c164030070000b1180c203108c0c1080c2c6d079180441034426800e1407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 655714289 1250 655713039 655713043
    0x130201090e1603110910090f0602032a12030903041a0c0a170f0705010504020102010501050d0c1224050103110411030f0405190602040501081e070c0606170a05 70
    0x25805802224120700c1008000552032124508070000760901142802041030000d8203480764808441d0f20043c004c0d88180030a602c920014181e40010000c50350782034540d002030307035a40110004840000e00c000015004030414000890244103004126072413401001c603030025135002211000305541c004141001011601c19000c0c075107040445c11507150460008803030b51030b01c0c61181c0240c14800211205a2408070800c2202c0007862185061a181ca180c0d00d0404d000c3d000c2503905a0040d800c1c0400403e8620303051788082c02c12070744019104bd026103400308420b011408a0030a603010100100f03840304102000310800c840b145112000210380d0704600c1d02d07102d08044c20012901880c64007555549540b42c1d14122034012402d500c2a148550301c600d009480c1029152804454080303440348401000010b4001c3e005480c803d0300c1e8030f81076640300521402d024902941030b840c54044d0304046a000c60084851540c4240035100100c0e00760745a05090030f04030b10309149051a5480526200244801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 655715539 1250 655714289 655714307
    0xd29040f0603120804031b030804260d15050904230316031b080c06010e01090c080a0513140a030206090f0705011101140a020c0c180c070203070806130201 68
    0x1040c400c000060858440030000e652500d400001d218046000c034040c580603a20410b601c1c4d054880052460502e4640109805016a400c503419402c10078204540c8451400001080d0203518072142003800c01101c0704007901c07200001c1c4134003a450541c00300d403603250400340f00d114901401000c2074601200851110866001040c0d120b150410b2205e201d990855403451b106150309450f042000f12416000d203202c02130740c0d440040c6202d900146903081a00040b0f0030038102c2e1074400c541c038040ea0743c0b004003a00365000a240c030400581000b0001e0586002a03010a402c42002d42e0941180802c5a44072000720040f14186031b66984601051300c02c05d40c6c100b03e03981e404180340d00900110403210500659400031400f60905000d0b610032294031820095006908511900c0e00f1400d0398140301a000009604c40709103001c3d14012245400580d061040884900e0000d10322036006035900c104004149c0d801aa604070303814000d07440d000500d44810400c460045409810200c020701c0f15200140203580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 655716789 1250 655715539 655715561
    0x40e0a0b03150c03180c0d0b0108160e07030c0203070c090203060f0a050a030206071401050403080f07030903090605030711060c09120d0504030b0402010908150a050a140103080d2904 80
    0x81c200c0c00c000071203c24805407508401440320322059038498500040c202010282c010b0380014015042038144a51030040c18103c44e2450103440e130030300c0c1080070b01c21300720040d0040214a104100c08a0b4109100c0d5100c656800300c184142d03030400e4070650302d48400c1d801d541d200c2e082c00d68001c0305001c468909440d408648900032606c2c008101d26042c0422241c000b40d10011b80701e50710101780c120034480d001407100788041ea034800070441890725103809852070000340c84000115910328001094203010381302c0e0f03064168240d220003420510b882004c44059000522a404000202800f03a42c1c3e424100584e5006e0710382562800d48501d4400e041c08081c5980300d04e0844994030080070041d1841d0800c040700d041d280c200741154460350f42d0b400141d03210820f80d880001c01d0310880c0c4c02d010410201c01c100a005602c078030b09c00e20550f211002030380151820400e0001d0f003646c8190042002564000c014a003c0c1a040b00100c0c440400c0301d10044c0c40781f041c03000c0c800e01e550440c0c1c0510b050f181520603907007802 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 655718039 1250 655716789 655716823
    0x180a030909060f05010c122703030f0507050303060d0804050604060e040b0418030302180a09020315030c01020c12121c2f1602060a0c050c041802090c040e0a0b03 71
    0xd0314050009041704030301030018040d0705107030345041a620300c21070441c0000020414100014410308d54817a4182c0c1292005900081142c440050030030b01c00d40884583d40d0300000150f0554075440708002519406d080c04a64008040100103020345908c0c015200170a20342e00c0791188080c00100380f006458150041074440d524005080351741004503041c1200041d0149001a101d400302028003c940e0540007215501c144003030800580360000c0e0300198424005040e07100c0000d1850800d259580c9a0a441309002d6040000c18030a281015580e50030b0325400881100c0600a511141c4a410381c400a402646540d400304000c61a2550740071340c50141022040d411107000c000720060002301e06940c4a0406a100080d000840d46010b41c00600c415030024419035481481e1080078110f001e0a020859940c05401c624440f5882c00d8400c1e00c0b8644095100034068440f56804c204046e44020072803004000d0030310000c00c41e0b5007280407051085404400000c5e10314040010035107080301280e1090128 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 655719289 1250 655718039 655718069
    0x9030405060301030816050f0a1b0b04180605060f04090f050609060d210207060f020703170703030f060b0405010e0303070c060e13060b0304171315030e1914030c0312180a03090906 79
    0x60740184102c40031100b033752070310644c1c0001d01c0c0d03020400307068154001c66000e80c000c01c030922460a0840100110f82800c02e0800c94000712603000b60030b035030b0119881540f02c01d0351000101c240c2041ca45000803584a41b020901c002030000034407114410f03020148006034048201403200c02e070807030604000c820040c0000c00e01e1074074540e40c0c0f0300003078055082c850881e0b20101e081c01c00c0500036080501c3c2c60301158003e010483d01d941003101e44d50007920545000400a2100c00e42c5418080300702c078003070794100521281040c00d050043c2c603aa440e404580360071000101c00d10407440c500d40302c2c13200a0008164030a0b40c0307082c5030501340c0c9103002940081c1c146242c200a09200d200350740242004840712401070350b40c070803e5020140c2c0182040f1140e01e035140680b4014140844800050809041c812607070700e070360300b0b04090b070142e038174006c2c0005103202c2c0d4420070995003601000d08419500140d01d081d03510051900d03031091803c1c010780210403400304507540828440701d91240604006850569000640 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 655720539 1250 655719289 655719299
    0xb03040b060103090201120e0607020d0306080a020d0c0e13150e061801020f0424030b03120717070501140703052e12120809030405060301030816050f0a1b 68
    0x2014101a101d5814960340700c2c0d5460841e4000c0701c10200001c3e0000c0d0030020701c011340c41c01507160a800c855107401801090412440c481c024481c0400741c618600040407180300c40c0d070a0000c0d00210784002d9a0115042400048542c401780450b841861048040584a009071030328081c140ca5150001c4c0d0103d0401d03921103200880090916405100b10791024600d207a02507455009104420010b640600001030101e03505034400618001c0c0c3d8100c00740c1014841212008804848003a061243d041d00265007603400b0030200c4002e481c440b80a03508010440390000140030065210900c00c03280d5035154501e4917001141201407a42c000d500c1e041c01c2c4030514082c8107203000c0d08a090b031080e55144002d000d07941910a0304802e4009403810007010310a96180d800d100300601003c02c000c00c002100e00c400030f0500070707000c07041d20304641000d40801c0c11a400c59035100803d800c00c0b0f02140c081034552580710007140702084440000c0c44138202800c07444a09007003c0c11a003080310a4125200311214040003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 655721789 1250 655720539 655720553
    0x7080705100c0801180207030c0c090c0e0301020325030b03150f1602061906120809130c0e27040305031e011d070c0b01030638120c0d08030906010b0304 67
    0x1050303902c00140140d4980c45442c040d00c1c8000c5150002d003d071880c002c2cac04a00c1800d1035000014040c1581c4581d44a01d1640d0109804d07440708a51060050501203000c0d4003c400f224a1601c0c1c0c80304504020900703c041b5070100f8506002daaa2544250b2030410070f100300300d82801017036508400c40d00304a10b00c0c401d030b0040183d9640d10141146000c0466141c002d491402142d0200b1b010b460320041402c100c0800d8140181c154025403841440717902c0c28510f040020f04140325005c1c3d00c42c4191118551842c804013044507024001d41c01c001d000d44c0f846900c0b681a81c41c000010300c103d1203502c0e03258803401c000b9000c0c4445640d07101d11603a8541c0020050280000000080f100100307a014003a07156a80c6500844202002c40c10007046107100200100422910381c111f02655100881d400c401055003007208503c8228462843d5015044000d86c00e655081080d0400301c2c940e48101284e6503408140040f802c1c00841300000d45441c18017000f0702115a034184040d600501d0110320301030460405807989a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 655723039 1250 655721789 655721819
    0xf0e010905120306040b0a090509060c070c0b030703020c060f04050c0105090a0b030405070f03150b01090302090f09010b130b0901060203030601050d021318021305033007080705100c0801 82
    0x14110307042c04400070301c00341c0c0d9036000307000c03402c4018100e0301c0082ea1b41c1c580c2a0140000b0750b4152800c1c0607542c0040d1600e40c0c0081907699440d000584052002d107401c070f5190141d0302c080d10741070405400300334140c3d010b201003200a02441580c0040b407024641800c0060a101c5110b12490402c8002c000400c8650b030742c21400c2c81a02d040c050510364a07110b6260481c0740038403640c0b240d044440010000414071100d0640900c0200481806001e9004000d004440401450000030740c00301030078010400c841e81c4107410940c401c902100001d201110140000c00c10130006804240f01c075102c15092115003020544c0c40e00600f00d03400111f086007014000170b00503010303a5640000d020b9010600703040034841000c4a20060650003c14101c50008000c0c10f0065480548515421084250005604d00340003500002c001410803440003803500328505846584042517401c1c00707141051003180c002c602050000c0c5501d80c8a54003c040340d40318101c0041c20703542c800000c0800d04c020b030001000301148076551380d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 655724289 1250 655723039 655723063
    0x50f0a020a02190f0e060f100f18152714032826070b0108240a0b0102010e06070305010609290705100509030c010b0415140a0b0c010f0e010905 63
    0x80d42c861ba46220100e900300d001c0440c0c45a00c8001440380429030b6400c207040e01610340540e511030003910000e0001071880d032200c0c4aaa040d40107031030f420600c1d03907101e8002200041200c203410700d0500c80d40f001c0040364501941000c05191011100c0d640f842c5404c208400f41941407000401c0e44502342594502c49025011024080b0403e500f0840b19050440300d080405001010030039840c0c842e41e04103007541350000d01800c0151311840c8402d03021046940070440021446500e242d11642c0c4401c0240c01800600010768159921650440640c403420b01641c0d100f0103c07940c0004042d85004401400e1001c0340e4800c200080b403a9500362124001c1d403000342d521b0324040701c803e40c2c0d179006454218030700034103050446011441c0ca014082e45002c040010501c0c0780c807400090200200e5401000115506020f081d030b501d4401e228200b08111040c40400c04040e001040014800c3c0d0f10f5211a0351030380544004100c0340d55401c11803026000c94402c03148552800b0000300409155650740710f5507a5a1031040b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 655725539 1250 655724289 655724309
    0x605090402012f011d010504020d080903120403060c0e0109060212030c0c03130312031503060c11030a0903062a1d0d0311010c0503100e0601050f0a020a02190f 70
    0x80c03191100340210200000390a0466402c401004603015030080820301c80304041d080d000e85d050094010140a0079000c0c0e1780050600c11101c400c0d65544c803c03903201c500c115805008602041d84e03104d000c3c0b005030006600403d000300d404421004010b2040001081d41c50512101860034440c80c5d6001911780300451040c804541e40e40c440941c044564040d504d404030b002d1000240248c44510213101100441e0321034041e074141d4100310002038060750300b890001110910318220070400300c0e1441d006503104c1e1010f800d00c44a044001080c05003140d0103003561001080304110f0802c00c2200c81c0c0b0500350760006c2c00b6203851090f00414030944000505800702800c0180d0301d04a4000380d00c4901080c99048030007400e039000104103240c0a070407140d20621b500d119500e000b0300012202e000e2030882e80f00d040015100c48241c0c2c14202500703070852000d418181000000d10441c100d1110b1400101a00702160b001041102424410013564554011604001a040d440100034808407038800d0300a44210f005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 655726789 1250 655725539 655725557
    0xc100908120103050309011d030c0613032312070f060f060b04080a0c0902090102030912070909080903010e0109020102100903050f130509010605040b03070c030509100207080d03060509040201 84
    0x5140d81940518481ca64800452a0000007040000001050712410a03200e40300e8554482c560b1140200c0345141d80d58154204600d038078282e00c0c120004207242c40b41803c100303a84585a4982c4841c034102001c1009900f9000d01400704600005c200342d2441400a5020601c1d01030607944500d5820800c81000f0324454441d00004c132603030001c4e0404400b030b107816100291a03035a50281c003942c890b4030b124281c40ea080c1c0d200780403c00742614001c036803c121041e002140b1307210100d82400318400d2644002c400500812030042080c1000380100688070f801745811a4a86a40804160071161070306405145a172510440c40c0040c0d03004500131b1480c00c844540010162100d0a0660341846115000d1030580000609403207410400a482d406584c000c2d1040b0340710b6a26204140c0b8140f169002e03040c900d907c01d000054410b880380f00300344103e078400d1420f1400c006418002c03600e00c6d80241c02000c00742c0c021003400c0c000101c0400a5980408481c82c0c1448041e29140200e4a0b2202c0600f019040007000a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 655728039 1250 655726789 655726793
    0x20a060b0301020d2903010626031902010f05161706030a0204091a070f080408160807050a15090f061d060709030203240708060a150201020d0609020c1009 68
    0x94144c0b200400f60303040920440340880441d040c19881c0080b1030446405d0741c81c1d941d105050507c54541038031031080c20000401e40d052100d01e0000000b1400c07581d1440304200003044003074141d070341c8403030380760107400200306e9074a1034180b803040d20802020640b00c00e8000008411650b803004000c0c005410100c10381d00300d030f15080003103410240c110402035089801c21480c80700b08030401316200315590010340b4002c103d03158a68100d0310760b160303501c81c000015440f5000c070f00480c0104000706070100400b40350680c516842c0ea01c42c4003a80040c607060b02da540168144505002c41c40514140c031801c0d00c00100150001da541e442e0301c035100c0e0030000e44401d81d41c1c03200c4c1c0c8040b0302c0c02017104000e00b008002c6605034600075100500c544214041203002e0b01594101c1e828030225a062203001d00304200e90030106688909049400322401400e0590010041e440003a10301c944541c0c1f10350170043c0d580090f80c2c503075054840600f0f03a415070380000380c2180304201d1000c4481003c0351840d00c0d110181001f0601000318 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 655729289 1250 655728039 655728041
    0xd09060b040c09090b0d030512090c0909160e011a030c0f04170d03020901080403030b0a03080a02010f05130b0403082503061502010509120c120f0a1d01020a060b0301 73
    0x40361006400a260a002c04051034000005008481030f881d02880311031015002d005062640510050110340c051103088103c00108844560000f00716003111308013040c840c00a00481800d456480041d048540602e0480080ca280c2001600035450b0b40412540b41450300070548403e415118403602001c004580950100421580076503403060107142c540f4ac8804151044109448001303142e07200f4800c1845980303019009503134520505031180491940c0c0d80c2c5041e0007802d031031250194402c170020008400240c407a0301820046615600010301d500180c0c544030b04542c0d0150103800e0502144805900260b015201c00d588540e051030302c040340c0d45540101e03207a00300040441d9180a02e9910803000b2480d07041e0710410440c0c0c00d031f1244c0851200c40c0d41040e4221002620901083c1d04036842510191000400410210304902c1c201c600003030241c1c0c01d0148680201d07554a40b1850000b941e11300c03040c0d1180c82600002511020700721540c2003440040e595003078658000f46041d468403900001c039542 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 655730539 1250 655729289 655729301
    0x6010501140d0f0b030d09030b0105040b01020a0f0516120f11030a050a060b01030605010c020a03021c0501090b061f05030f10031202160b0913020c030421030f0e060d0906 75
    0xb412002e004088080200ca406040b1401450303020744607450307400d041d081c40384e040c0303204072a0011007604a076401c0900b8030010b80201003105041d44118088440090108172005030440d0050001e48881d8800440040004101c2d6000010303d108483d01d56000c1404d0110311503c1c968400e48408a0710404808203041080030704003c1c0c0540203d950440610400d07412207400e0203c00da0382000311980752030054030107010610001c3c1d000b008600080c001401c0c40e01c2c015080c40a5084003071881e80f42a50360b2429118031800c04c407040100d000500603d81030030260980c0c80b0f14034034054007100c104001c0040540c00010400303007070030314610003081d5019000284440515004145c0002030103030544013941d070f0700d80f17014104428001107800052100c0200705a50204400074110088032482120703400107904000b103040d06070300003000300090581a1900c0403032006030460240d1156807003410b01070300d04100b40d00000c09000d0100762030507295903640101d8a48504034032001130003030345600f407407070041034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 655731789 1250 655730539 655730557
    0x303040b1b01110403030503010f050a06210f020f070c1418040305090a080105100801150b090a0f030c0303030f090b040b040c0b0c0a02120a03050708030a0f11091009080601050114 79
    0x120018001c8141b503404001141611010205544600c1d6204240071200e00d0034415500061540e507a016154400e4a40b040b46201c0822804120400c20005140499104500700c200032080021001c08110485144000a0483c00c090080a8003a44082480c46220740b107036480280303807180024109400ba40507101d44140250040140380d840e8001180242000c1c0c460400d002607a540c006601c40d4140940802c8810180c401c000c62440c041140f1075542004d07003543d81c0030130a07003400f1640c4807a41109500550040448444280c918203018046841d5600301c0c1c0140c1c4d08107144003010503425185940c0041d0700c500424030302da50303034105403141c5089a0407811801300002915100c031200002c40355200c0e03000300c4d0318980040350f4034802d55443c0c0300024001e0101d0300074040c0b0008607055101865002c01040740210b104064803204038100c405500c0340101181d07010550700c04601f0a1f040c2250071581604000900300d0410000d01d645660511a1a041100d103001c203540c0645032900f51000e180b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 655733039 1250 655731789 655731821
    0x4060516050102070b0c090f030d050f09030a080c011413110111100c111501180506010c1704030c1409010b1b0604350d0c050f03180106050303040b1b01 67
    0x4148480c000391b0561007000380f148100a41040744a5520f0041a06042d01180d0707150b030383c83e1081d80302d0140d1094004424043d0b05010300340003500496040c000034031161260700300010743c2004041c0315081e0000083c107104450702c461042d890016000c0c5090007046442400c0ca5100c86160300081da1405a250100c0b1040c2c0e0704212510322540e400c02e6011042c02d1302c40c17068445015003128041d0080200f4401d0400340152a00000c0e00103400e54819504200c040c54440d08440c1d0070b86a01d2402030344c0c0c6020f2807601c0e10008080050140350182d4070080d0840b030001c10000c460000c0021250312040c010f40c42600c200140404103c0ca9105450b03103103e005400380c4651745040d00f8007501d0300c8080c81600f500300170803c1c4601c5010340fa146054115107001020582000b8610004e4002081e2600f98042840401c10001c051441c103000075600c03601e051200c41c0400a204000142921034907072025000394803e2000340311240b001010f503040d00c86601e940d0050f00c400400725901500c81852814041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 655734289 1250 655733039 655733041
    0x90b220219090f060e061804060b0a0b1314060a0215060123030a0507020303060a030f061e050a0b310b0603090604110102061909060b09190b0604060516050102070b 72
    0x1000a6401c031300100d0b00221060300301581c2e030b102409190395001d40e60300c00d00c540d40c500040020350540e006182c1000d020f40301650060322010a032025a11407510002c045c16901300404c19484043c040c18092202680c04034100400d1643c0a592100b0302d8611764208441e1500150459200d14004000c010164101b08005c80042d0442c0d002c5a005552034012941460700040c5c1c080e00000880f4010356014200721a0540786440780580d80c030507031004444141d00c032854005183e40f0b2904a007100404450700041341d041100340d00b81140c690565841c0110b0300c7c8040b0780112000d500f10243c2d440d03882e1840404ac4501d20107010010f18002c0801a44842d000c410300c0b862000000311288039622503072120441b00c952000581c0d503448100c07081f1103a1800200c0c1d001c02d1902a410101c0c02501c55040459070040a00c000340d03511070215152011030400b4000e20412006501810b0b003851819501c5078034150806000070018820500812a1000881c00c002c003001025811602c60319040080c070442 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 655735539 1250 655734289 655734311
    0x5090409050d0302070201030b062104080903060a050105180103170a1809050f0a090f021e040c0806010f0318030509030f102009030606090604140109090b22021909 72
    0xa405c5844117a0000c1c2c030b01081c40d901802c10900726600307900058125400c0c040b0320304110596210091044a0b6050f0034000741c0082d40f000c000d40303400341c42e5000f004074556041c00180104000c140c481601466600c20041010071070001d20404a5013004280a50301c101c80c81007030f00c150320700c03400119030080c3c0b0b84800202d440c020362103240200d14101c00f1141d20345400e0181c80613039522100180805001ca60b5080043c41c01e00e0750065000d00e1070000b05480d0b04114001012110b61100c4c40d40403820200401120b0343e03100006001d07501e041e0034104050602a4a4140c5202d18450000c5c02c2c018001801201079600b0058804800080804c64003040201d070740c0c030000380100511202076400000d41410840c0c20820586040d403c2c0034005000c4e9075134403020800c0040b80900103c3d049951882c0d18140711506541043c040c01c089240402d5030b04481c0f8000c007564070028094000160360041d268290640340c0081004160111841602080e0a030b02444803026250301c84502d640c03900c2c204010b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 655736789 1250 655735539 655735541
    0x6110f0a1401110406170a1d0105012606161e020109150e03030601120f0f020309070f030803040b07050f16030201050903042105030405121005011e0605090409050d03 73
    0x900d201d4480001d101000c60716000e8a034038051801402c021420b2072104400e03010560003041d901c0304500342c01180448032441d080f204662100e10346455a5190001803090046480c0b0880c05400380240038030260030118402502c03100050300c001301403491261081d40c118421600d0500e600710a01c000e1401035940c5801900900760010704903003200c4000900140d008207445060303188101e5034040c510b590380e10001112030969420150000540c0c1c1c00c8040d219000a02c00c500791036281c0100183c3d28185072000e28079218080d40100082000c844041c40060261000d80380c000d64042c05a1905480300f80c419aa540203c200c40e0303802020104d4002c401010004403c11014001d80007003025440d00418103440344540e0080f85810000c803141540340c000758142c250b00c1c150240080d80c2c1899210400240c8000510340d80b000382d94401084160b0801c103a11507180100300201e406030540e02480c15403100a080340c400c0e8000c2c0200441c800080340c0710b6402c500c04c00c0d40e01070259220501c1c080c1001d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 655738039 1250 655736789 655736813
    0x909090a0b0106170105040b0d050706020a02011b030c03080403030e161514040506070201030e030d0608190b07050304020d0f030f02070801020f040b130f08060123010906110f0a 78
    0x36980041c081c0000490900403082c0c507000c0f4004800003401d980c24403040c08003410020348000d8114000d1088400801c0301401f03448042c0c40603078060001c2a082e0300005003001c43c44801070f0789800c0086064400a900709041261259042c1044e403e645c0c0e03181010f81c0107001c2c00c0030120140c010030704071b400304202046014040c1c0b80f803043c0c140300b45a035103c41259810924000d041c1403201c10407050016113411400751215910500d00410000a4202c0080c150741040c101c408032141c407484103000c0c4010502c03804482901860700c0115002e21038881d440700c03030070183c026030a2000c000046000d40d228060881c1035a41c004000b112030030950700d0000c0034510040b840c0d800600038040040b903021018004c440442d1620001c1c00e062a0070880c03d5030860744080640c81c803011498200103040891611014000c0c030400010785060b40c9444013007075440141e9025505080021640c1c05a680e070049203c0090b80c0c10f626082e0510780603082027914240c00c1001c00072843c4600aa0701c0d0800100390312617 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 655739289 1250 655738039 655738043
    0x506060c0f0c011209030905130e010f0209030c0603130201140c0f0a0b100303020a150b030a11010e060406050d0b0103061205010e07080601031203021c09030e01021b0609060d020909090a 82
    0x10100c0c070300c1c00c0e44a13881111036603040100025001902009589001d06030070040f015541400078104501040f0142120f003200414a03420380c02040c0742a1a20b0180302020042d40d09031150f614600c1e11544600001100c500c000f41407000030082c040342564483c040c0d8084401c003004842106900c500c03855603415030090102e404001400004181d080260700400849906800410346c40309242d4580c6046400b450140001c9681c40032240c2540d0303001c00a039540e40d0f000d1101c00d4a01140c0c803000402c2c441c2000c0a00d402050100b004200169100342214546010750380d002640300340e0403004901800166010030945462492480140141944400e0942102c0022900c410b60744000c9503440740d000340302c050500e0001d5100108014029001408200c2031804820700c0d005100100d01c0403111500e406a0000b8114007a900055804104e84001c1e11418488450700c4400000003c09a108422b000c1d4020741c0040340c0b4040200040d0150703001080000c1c0601414985a00e200e0364691204000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 655740539 1250 655739289 655739297
    0x1b150203010e042a09090f020a2414030c090d2f100e0621070804110301092f06120f01060e100c0305072a08070b07060506060c0f0c01 59
    0x407110701004086640313400c0c026590b10460303646002400001003044440584003c02403502080c0181e03609010403015112500e036140c40c10f21120302121501071014081d1080c800e441e06c3e003401410f10391082d203600518500342c05980d100c0b448040742013281001001044d100d81104a042500c59581e901e81c10103006001400d05090301108100020552030b0140c0081904015a4403541c1003120040c140421822480c02802c1441030305290055411580d00e400100c984092100f040701c410100320904000324024480c1204585580d94220024800d4043e60060b0302503a030000c1d1450942d86007440c070014001c50302d82850b0501c030900203c084a01500040f000f0001046543c05604001401c940240424240c141070000a40f07601c015000c09405020040c440080054821071a00100003600e10280d41141d80c400041c4100b10102d80000c540303030300300c2034080c42820001000c1d2010f69800000118080d1100c40118107240304010f1a20450b002d014820f444c00000000e004071504000e0761 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 655741789 1250 655740539 655740563
    0x10e0402030105060403080705030708030f070914151309050901090302060106140f070816030e041d151b120f0c0408152203031d0109031b150203010e04 67
    0x41200301e00c02405a07543c05078060000b800030454100c00380030fa552203802100c0c64801691107940071078208580d0881d0304c103d030008000805600070484402012145a41d9007440b0000300010031051a0508242c0149000b240b0681400f901c46a054010544a8070420007400c1c00c106042c00b800c103010042e405441103400009800b44200300c840750301d50511103031a040047c01c08040e0195803220400b9202c0340c4061042c1030061003000060103255120303454201c50b51050005000c00c0d250881e00c030310b0304030050030300106102c1008a0480c241038076000103180107945440c90038000346021580120907400c04180c0c400345204000a4500035940c10120325966078a032b20b00f1214074031850080e02c1003500f04880084a2840da0100705401900c0400c4410546e50311080f00510010182c50540c0080d0321b85038405100141c1203c4245080c20400c020b21407041140c0700544400841c0e2003284000d01940250400c0c840c10b51101c121640c51380c0e200350b42d0307543c0d610240c07840c040003610240c8419840c10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 655743039 1250 655741789 655741817
    0xc0e0d150501060f081b040518100b030c09060705161203110307110f040b0405190b092502100504030e090a0603030801140a0302060c1e0a0302190201051b010b01 71
    0x100c904c0300f204105545034400d50307494003210841520b6a5402000e1090180b00102d42039a46441c0d0f40d000c1c208921180000d484e040d0580401c185140d40030200700c6d84104144259104070782c0484d0352018042c1d034696525406880c1031440c0c0700ea410b54103180034104040c04500803071b1409048a009029640b14a1200e0100003543c0d20b900c40c2000007006c45d1301401c641030742814141c48403001c142000b400002c4401c480c40c003040641e20101c800e001504042030030b5080000c0c1601ca41c8103009020f4541c05410b00d0312242c1c0483d00c0c5900014110f1015030012140c000c00c0c030030400b241d0441c2d4004000d000c503052901d0701404205605070002e01c1007a0720000585521400c0c407604040720381540e92800309902e0440b04580c48156001031a03085010100c000c400b5807512401010400c104c0c00c01008041c60000360040f2000c2905901c200300d40006c10032002099001441288030843c6016080c0426094801038030503104080d95810350702051030b03100c00559010340c4001c2c5954400e0700c0302405400d40d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 655744289 1250 655743039 655743047
    0x100507180e04061a030604060e0d0509090109110705010e0a02010f0f0804120c0501110a08070503040b192414040c090e0414101e02070b07030c0e0d15050106 69
    0x507004619000ca040000680403c00b140c0000f010006940d21920b058070119020074104141254282c440b19200c008103040c220703041000740c00ea1015407030254202941d48000a21600701881251411501d401109002691034003c43d00c115a0002c0208070341c940300303541c51b51691545030341070303021641440d18240c0d018000c50260529294660710110705030707126500c180c4404030b510500b40c10400d40040c40400580700740315002400c05880402c5486061081c001002d20078010138003403c02401740144000148200e0030303550032843c48044020b50031501040c0c44003c1c8403496050b01001301d40c80c0c2d0003005e0541d491a000c02e0310b1071002c4900755044100c0502c02031794a421281800101c56103010018000000344180e081482802c000c140001c0048006240c0b80e160341005183c2607540092503080d0700403120507445058041800c1d8103200c12034a82034000b06c0000c2800b4241601c0d8a40303100348501c1915a040888401010302401503001c3c204101e25000d00c034121080c1c5d43c82c0c100085032076401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 655745539 1250 655744289 655744337
    0xe100e0310050604062705090732030a1e15090f020301050912091c051608070915060f120509070e0a020909061212191806270503100507 60
    0x43c1c1e42a203040716503046800f8000d010080c00d00c0230318003e038203010450b20403840c1c00401c4104508050707409403190046803059030344a000c5140c400c0d4405c81c1e0039030000d504203450030034400d03501c44010500002405c0c000405000720528000107840d1007030840c10012007000000c6428000c0d0001c0180e0342c1c0e400318140c0d4603d41c17404c1da102e41c40d105000440140c5080b4a48840021b081d0500801e84010740c2c0d02c080c603001ca107080041d100010350500f1701ca0071204020700b030020305103103805204c07400400d408103150414138003c2d1002c00c0350104040d1410b901030240e1201d20340d10307900f08005c01d24021a45984581003030180512841e221808210900304500a4800701f400c000c0428030192605003c0100504904000d01e100e0300038501d03c01101340014000d0410f000c1800d9107614000680c000c024000011a1102e0080f460a6181400003a0f40038051540304000380c0080d9942000c1980d40c03904000d1298040741d81445980c183d8403503450a0341115002c1c4c110303503c0d40503190a141c0c071200c0710f10f40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 655746789 1250 655745539 655745579
    0xc14120a0219020a0504020a0309060504050d1d060f031528050114030c0304021302031014012303060303040e012c0712050a020c16030c090c0e100e031005060406 71
    0x100c010011703c07440c9420340c01003000d18401c0c24001441c462603075a5005684c0119401d6400381c111070307500c6409542010150814041000c0c69110240e070620005905001c0c0012080b0407840100000d403481500051280c6440401400905403c2c00b1410250483d5a5200340c24450120080b0004195005d07404e0741e60605045448203055503160600d00704030b9000140141e82c0b2094240500300c90b01c0480c40214000d00c1704030b8202d41e01c2810305107c4ca0302552410384807410050f07051580049a01242c50105c41c81d040b22207225a00e8482304002884c0d4005c07900090904c240303030300000805041c0c41446000100802d0001c1011348101c4502503440380f02141d100000c54508041c0d41084015075000b107900c105205001828200c4141c0880c0c42c00c2070741d590310115500074040910034822101d0482000304181c85c02401103985c0726800a221102c81c0710421b018201d011082c443d0303a8026501c618402c1c601804855400d40d00040d11406024242c0d101c6000fa4a41040810140848506407007801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 655748039 1250 655746789 655746799
    0x3011d2e18060b040b0306180f07021b0f0f0a05042a02031c0c05070803070e0f060301080d1407080c031309020304020a03081305060a05071a0402010806010c14120a021902 75
    0x38079210315200f01e640024811580400b903060444142e2880c038100601805510103101030512b0110340103450300740081e0410548010412007021395607100c14244140c903c003920380880030b0413510081010921990000b0b90300c6401c103440120300d003004005512250950b170708950340444089100ba42c0740e2041c50f2034417560005aa01c2080004801c0c1c001c0141d0503100d00d885460000c203912007034490340084d18200c0c002024140580150718001c403584c01c440f00220360541c610b52400481c2941d906d407a502110a1141e005614a1007103c1002568101600011169a0b8004509642c0c1d10307070f4803602645085180041000c2803c03111403082d00d22807640a02109511410350b01c8401c0ca58108258a80d0b0b03401c18060f021549072641302c064000f81603551141a01c8002a00c0c0900030070f80001452803000018408000242c0e030b0014280e81c2010003030070102e0096219081202c0c8690541d01e18441030b116091404000010180c010180d200056081e03a201c41c20000002c1101040408082d42c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 655749289 1250 655748039 655748047
    0x50a0503070c0614040b1014010e030a0b0a060806090307050c01032408010605041808070803180106061e021b04020c010204030614040606060503011d2e18060b 70
    0x514024002507402650a003041240c102595031694181d820800149081041c3e00c8140401c00c00a0003000c1e4010341900c940b20161810300c07044a2182c0c428980d06410048884001c1c2d04030b4806110001c40f650300100a8051854003100705405420540300d800400d110303e100103140e00c030012055410a42d4072001802c1f02c43c0141c4011800392801c605120040100c030400300ca18080310f1641c2d00010100b240021680d0361410041000702c1d080b054902e000c1908a020100c0001e15410450b0805584002126281c2c0c44800d102c0c109004240400d5200b5031074a103020074015013040448020904900b0795000b240501002203888650399a89a4150041200420250301d45a0041c00c0c403a4910000141020b99070388030002a40d0b840001401040c0700c9206110510909001d50005404141070451545d417415071103100359220340100ca0a0000044003044200c3c45103901c869207038080c0c44005800700c0e02e561060051a446104440d810a240e1400d28400741c00b40c0070300b40489034010b07203080c24 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 655750539 1250 655749289 655749307
    0x70f0203030f15100305180705060906160c0602010605090a0605100c0501241a0a080708040615180c0e01020706050f0f070c0603050c120a020703020c040e01091a040305 74
    0x80302d10081c051030500c5030f90a544203200e4540000c8880c0458035540c0104035420150b2040e00e0003118115201c00d9600415418003003601c0c0c040071554906011348000c1e944414031108548401c038841e00007000210740030300000d4185d505400030029208200d440c00e14546401c503142044a5180c410590403107040c5032140c0d41d0310700612452000d640282c0000c240c2018461103030000750112184200740c0c4070404014404107144c2240000c52040304400c0920b444482540580184402001c072410442c100002401f0002c003a08011001d85092120591040c2c40d10902c034034414a00106418542c540341001d22920300c1554410050f000680203042e10500f004e0045605920035014804088020040b4007076922891005181c41801010017220341420820020140c0b03401420503503410f1070511a04403080005000107401c4014030b60300503501d4025103001e2742041601060284e0051811880003c101019001140e1941c0b041158078161500e80300d032898524816200540090414000101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 655751789 1250 655750539 655750561
    0x60318110f030304060906080a050103050601050d060b13050f060d15091b0602070302031209010203091216030803010503070608130b062b031403060f06090d0213050f070f020303 78
    0x181008007070440c40d0410a0400030a00d5503010307520010018450260800c142540058810742011149805000552454840341c2c1d4800d0180209489068100102d2040069540c04620f075030401170862104188004920b1008180840d0132000440f043c0f030020b00d4900d4240e2000c0305041d4821070502d26040e041e180c00c4000d1540da90308480210f0700b40c03404a5800f22030302101000b000c03981d00605000341503105142c02c00f001e0940801001000f8001c0280c2da0780c012058401105e0140d0b0703990012020822603601d844000c0303a401a510700701400100510004400640c1652419412146965034441c0f0440b0840401c8803682060107400041a0028100900060700100010022140c0100714015082844800c44070b40a4454011902404244d04900010360040c54101c4007425072520030089090100e043c6006403207042d00040301400d940e00c0384041f8200c150058001311482c924043c4000080c0020f0b288004c441a4140c0080d00d82c6105004489013005141e01641c03c5440f9088040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 655753039 1250 655751789 655751813
    0xb03030a09030b1b0706381309150516141e040f0608040b0f0403050d0509031603050705011a0d080a030f14060915030a03110a060207050313060318 65
    0x2100b0150440d0441d460f003132030300780581880d500412000903146c81c989034980c1d01203929a548041840554032242048481b010403903e000030646464050314009200c0381c000b4013011600404041035a00303035400c2810564415442130422a055229035000c6a20541d40348807880303021801054100058030000000c800c001d2010814049280d04090316241c01d02642c5001e50042000140003000300814010f1500e84590007614011801c45039090a4400504a224900c801a60140c0303403800708607051001c10450703c0c61540c940b001d0340303801c4e55494000c2c42580522001c8d965582402400480360010410307641544070014200d8401c4142d031354a40e0215000201850103142d910340d6600c0c0e03900c459016101d481340e09040505858034122041000c4207001411455000d40d1444001905480000f805c0038101c1d090304002c0c6507a048484118903142c103115009080500108140c010014004041d09800c00c144001150007502d80c00d0440c2100c212102111244400490180100c2c4040c4100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 655754289 1250 655753039 655753051
    0x80c012304051e03120a090e1618030623010e01050f12100f020d0e01111c060512010e06090303060d031d090c0c0d1407030f0225090b03030a09030b 65
    0x420049600c1c0c5000a040c4883c04980303121500002544291b95075204410030080c2c091401c10b5856424240ca550104910044c0000c09120702c0401c000b880e80300725100c0100550340000e0030f00040010400041d068103041c88082c0b000e04030034001117040c292469446040c0c0d6801351000d4180240f940400c40c444010703049401e040d008006c0b03011000007260240d044000800703c400350344e840f07660364040b040314200b82c05018164500701c03100304620105000c5864030f109006070116995a421b180348020318403a4131159110743c0c061141140030301c064011f0300d9249001c1040e030b40315940f1141880d031a0320088491680c0808006908400a801241c4408000038048440c0d802e01300020082160f0202c1aa140c0020720700114850000c92000c0182d112a01c03220b1900f185005a03d0b00604407a0140c00c0c2d00605028050743c4c2036150394400c10241003035440c02004240345c40340c0d44102e100c0090490254202440c1440c003080c80508000080741c4507841c0c1c0d1b640380000c2c0b620315210000d01075405050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 655755395 1106 655754289 655754329
    0x1051204290108010b01021e0a022202070f050f0a0807080a1713051c12050711010e030408010f06260c0a080c01230405 53
    0x15038100c0d6100860102001c0d0312580c0706148030080c4140250307410507000004450005410018810310217070207460401801000e480048181c0c04030903101039008080760001070a000e0541c01c0f204c5845030754803000080c08003104c030503a80318410079a2202c90718207600c0240081400b803a40440850002850844d68960f1070702d2160082d010003602e070b4040400e41c5000300e405010b00c00342006a90314404694070b04007031120300b01c1c40240002e544c0c512034250702c6513003082031600b28481120191103403d03091501c500d05101030403000b04100104801141407413515403090280005003c00000a107444504000005007155120170f1003c1105060600800c11401d084940f00c0001d00b507210900380e4111084003040c03410600c079180c65049a14010000780019020440d44580c0c1026644d8000019100301e010341560103501000c1f03500d40d0100003c01551411000c460002c451380c0300 = true := by decide +kernel

theorem cover : BRFrame.Cov 655575539 655755395 := by
  have h0 := BRFrame.cov_init 655575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 655575539 ≤ n) (h2 : n < 655755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
