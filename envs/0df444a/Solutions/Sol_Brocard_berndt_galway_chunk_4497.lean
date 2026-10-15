-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4497
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:48:48.572983+00:00
-- url     : https://prove2.me/submissions/8ba6ef35-e0cf-4ec0-a1b2-7ef98c320d92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 808633093 ≤ n < 808812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 808634343 1250 808633093 808633127
    0xa0c120c0618050307060e090a060b1803030909070c030909061a221707050904080708130e0702100b120c130b0d0b2505090f0a05040f0e0d 61
    0x2410400c64144502c806500903403142210400e40c50301c03680000c0c107100035a4089070002c0c1c3d4500c00800d4500c0d000c9440d46e0060582ca01c1009568500040300034280156004508220841180e0103441c0d01d050045680400e070040409009180c00c40c809043c61240040135400140d9401c1c0114140000f48242c4c8161424180700310780c40500d03001c85420307560040c40002505010343c1d83c0200c07000c450082c1400030f8a40c3d4031010040504d00740c03520b842c1c000700394001d40c81091070000344008102c03100110b901f00358001c0718240d506c0460028820038100207034081c8862400e140100080d880d03021400080d003680d2001c4c04c1c009070314580704004120a00701c1040809400c00e1844101603d00b000403e400e07103141880100752064444000b850600303038240c0640301c0c480141c040041140d800b81c141c91005414000f07402900c884418003e01500481030070398081c401d8611900c12558600c0d83d65001081c000b013003030011041e401ca014000c2d21036407032008603511500d01d144017517070300890f07490000c90840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 808635593 1250 808634343 808634363
    0xf07030e0f0601120c080f0106030302010b0102010b060d0b0d02090112120f120c02010b0d26040b0f07020f1c0201080106022e090f05060106140315040c02120406020a0c12 75
    0xa814840003a0303020004480041c0000b00001b41810140560211405a1400010118510706003c0c3c01c1d282100c0d2658116403400d803003805969504010b445684000260004a030700100f404102c04092140003c0d43c00700c4940000540d040c0d02700c41c024002841950001604121910b055400d00c611009500100b00060403402010f20954040400e200c4c603440041050341b202d070b01003200c1411400c02500d82e42c0040303280b010180c1640300503007611901e00345038602d01807810840d40c620340980001548002400034818040d07503900004403c0241c001009100c2252030300185180e21b130007441e4101c0c00300760791000010b1200c1c000f01e010b130011030300e203007030200c844029442c4500c03031842442400c19155074480f00800411141e80c03009075031620840003003440d54101000609644651035414090040420400400c0d00e403201c600d0b400c282c0240d07401316020045d1070040e82040400d03800c40c0a004004034000801d40c3c0e00048040071280a19101c000c4a600e80884019a1182d1603014180c1045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 808636843 1250 808635593 808635599
    0x2806120206090109030606080307020301050903030c030c07030903060f0e0c090103020306061003060308030f0f09032802250501030e0c030a0314040f060314060303070203060415060801050f07030e0f0601 89
    0x1000082c0340c1000140340003103001ea120741e10f0500b02d0781c498000d86803d50001c41c100c0c045050910a0f942c100200d0f0004504500c2d260051000901c030091003800b211070003099680c04c0602036a240c0740510307400300080c01400c00b000080720080c01100204441c92240314080201820001c14642c1070340d8020300a4150755a81005104940c12800e03005e9080603903a1400002040c038050145004044010300c407800c5062600203802d5101d40a0700000b4680c0040204d42c40e0b5500040d441c84001900e212110807410b00c1400607400d050800900300c0d5003400280d01441a039900c020014241c4500340c07810010245600112640d0310711211400e03415038031180854002c43d003d030f01c0340312002411160151419460f00f07061a44518150301030302c00700c6c7d11010b1103403141c1d50526900768002e206600450600f0240c0d000640c2d42c802c080e1002d0134404160b00740c80105096034001d41e003d00210002480b080c2417000039000703005011260500001c0c03800d2880196420301180c03200e1124921001081d00381d003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 808638093 1250 808636843 808636849
    0x201020a2d0e03190f1b0f3005070905090a080d0209060403080703170c0c03120a151d01050a080303070e032406030d0504080706030e0c0928061202 65
    0x42c030549882e45881403800150150740e403a1101c0c0086845400031007542c0a02d40740141280b0043e04048040b6880d0b940c0070300101c100a00d00c1c0084032001c84c08030702c03103d0320720f44116001e40b140c214803030150180415000c240a000113401086561440d401c1000e035554604080e280d8048240041116000300b156410840003a0041c01500000401c502e103003070717940c0c0d840c0340300ba61209100300d010a4491502c01020560b94071202c0e401014401d81501d0007080000e072580700c1c4208800911281500c0340442e18010840c1c0c0941d030000400213200c68095103030000c81001a081c1080056403d11801c004030705810101c840004503403004000f942161a100c07000e0342c4e9004d2079a505a0944140c6003071114084005800307007040908103044042509021050500f090f041410750700034440104000c00c10900c0010f1f24000301d4180340781c0000d5588940301240e0506448942c01035100b030012080c0070b02c82002484c22082148031542001c80c404500b180b08095414500c00c0c00e0450b220003502e100542 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 808639343 1250 808638093 808638107
    0x40b04060c0606080604230102030112030c031e09030b0a0b0d0f0813030c0303120e07090e0c040504031e020a0302120315090405030c01150f1401120c0201020a2d 71
    0x34403a0002048072130b22051010300c1d001045406480311588a01640d454611a110450401c0428802580f03558106016a8000101c8503030040400460003180002d240c85200c04000c20b6082043e19640f400603140002c2c4401280d01007900c528a80001003036040f8010700c149026180058407401d144941030701c541c15070140c07520064441c00710402000f090100b1450121001d584100841e882c42421420024501845111540d54031440e040d41c0c90047c400004803d004c59104150100ea941c5d41072a00504060740300300040c1e082800c00f000d000400d030b009819004181c03003581c50700c66403242c444000c0f43c0e11288040080c02503000020521130300c040c050010741e80809861800300194541e00c0100c1c000001c111400c1e10320745c01c08500d400329030800b8000d5580c0d901c0400d5882500c6d6003401131681c0c034244107208111499080030300c0519140d004821443c280b00f80c540e41000003800c8400c02034040c0d4840c0000c1c1c1d001403019207586043c01040b01050b03403c4494903015605002c424101903a0103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 808640593 1250 808639343 808639367
    0x13090b0a05210f03300f0601120513050d050403030804060506150a020601092306100e060711010215040b071809090503070b01141f0504030b16090803040b0406 70
    0x3034600d080420742c8558108940504890404001c555038100009800890320038102c50441c03503000b4803072050580042c1d9a076541c02c840045160880d5464400050740d003205200100354805040800704140359840c20005c0d11039602540035140030301050f220407107540c0300300c1c08000c01041140000c9004120740b0750160b58400300180c06880000c04030a1000900d402100400006901000c018891075040f8010782100c101a091002d10a060180c1d50341c0050b01c1c000c160a0003a03145014140c0454440c010015180402428132555240b0300d00300304d070341051031940141c0036100e45030200429030004041c440c032854020b0305840c0b494950b0381044078590b4803100c54071101c050b607183c0464051403d10035134901c40d00c070704002c42c0c1d10100c5141c14880c140c0168482d80000e0406682c20b074050b160140c01e92a0b05000c1049003108114281c0300360b640f130281c0e801c05009240541c4c00c00c070380b80c400702c40d00d0a81d500242d101c6000941c0e40e01c2015a80b0710980c00b81006c2c1ca0018082002200d00a0380ca078540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 808641843 1250 808640593 808640629
    0xc060b03070e0c07050a1a100f1d090309060403050601060e03030a0c0201201e010e0c030a020d0c03151a2d04140c0712030902012f01090813090b0a05 66
    0x1c0311455141c0c401c03684501041c3d0040c400c0482c0c10700100230340741e6504c20010403c0c550b00582442c0751240f00c0303120121580e0150020940d5500180c00c0000900480b03200c5200101a16112612800d160395100307800d0103400300ac12850b0650b00c980e850000162404540c071556031460964440e401100d04114514a0b01c00c6640488001840c02d2801e11002c0300c010503180045805642e20441c030390030340d19450225410f0307401c80c100e4445681c8010412400164040c0c9074212085090701d049190311480780c1c001b81148220061013000c4042542011042a1401044a9050105604014010f6403400c3c10080241c020188140c5038018500c00c2c04014200800c001120450440d40305000704086805040070100018a941080300c59034240810030501d2900b00b0040106a00207400003140000f180e03588030a0501c101240f08040d2440d481c40b5200c2d0000348000100c030310b04a416a04a42a0701c031840107034800205803100d1034442c0d01c00b00d0780e0091810a11520b8502400f408251400304016 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 808643093 1250 808641843 808641853
    0xa0504020d0e0607031a190e2203030b0a23010305090312090705120f071214030a0f080a1401030f02010203091e010f110318030c0409030c060b03070e0c0705 69
    0x2d0841c0d81481042e21030740c2c0c15200030507065400031048444101c4480a18420759440c0c209000e20304291005500f6500c441a059626444400b9a80f010511038001c04010040d00c8404000f01a45178100032140001a102c6050b055101c03c0d10b41c01c0180fa41c040d003042d01000501d16074103503200780c02650304180c20409581c81c2c8110300c40e072040c0e950002c40d06402141e01c0f400c000c10003400d00e0706030f4091840452000c0c05000030281e1703500f40c030340703c40c0c1c800c20074041c89a0807242d0602c0300111a115960608100701d940d52001d016000d0210074601c032150001c070310340c00002503c5040c5130281410382a804203441035a1b130301307550756200442048a03083e411844180840020783c1c403035015a4803060a0000308400104201e00010180d07041d500c0004100060320114036043d480c0001a0396581040c2d10006070030154010110b40b40641903051b15510609100744441490f4000040e60300c1a03000782400e0001020841c01d254ad038210078032884526528030b50001e4050000c84000e4003a6610038001d540d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 808644343 1250 808643093 808643111
    0x2106060c060506010909181e0f06050702030d02041707140d2d200d0b0f04060e19050111030105031906020d0203040b091c0818030409050405031c0603020a0504020d 72
    0xa070490301c1c02c10900c07040d0030201a26805201c0f035600e0423217000107641e40a0000e600c030703503071120f41e16490118002d09003074540c404181d1980c024800d456105141c0102107440300d0391581d42e03610148000c0194452030184040104898490540e0110480c1015040e070b0301421a59035510800c0032251401c0c2c0e111900c401c09110b403d0041d040300340d1118011540c040460030140d1503d44401607005240380724600105603140029401429140c0c0010441804c0c04143e03035605000300684001c0000311414007891100c00703056804015082900c40c056002005040c4c1d06c1d10403911548000c0c0140c2d070b8154084541c5240034005070390f250000503c82c0d078025082c041c007000302c5000e90b0019241142e12000c3d24080207443c05080120003c10b00c034050198904654241c005401054050304212540d140141240d0009804100300ca00a248001041040d480c1c43c1c00d0003500d81e007010990842080d49804105d03202c1259008010540b40c0082040a009250408000081d40a0b06002828903201c002c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 808645593 1250 808644343 808644359
    0x70915030209061602090705070c0501030506060903070905090f06040c12080c15180d0f0809071d010306050c0a08012702120105040b010203070305070b0a0603122106060c0605060109 80
    0x13030700c0100ca88041410380c0760800d104008a07181c1c028040070401c4000d1140d4800704449002070b00c1140c000703003400282502c0d02000b0038034030301c64001d805800d84244500043c040c01c503584802c0c49200f064080d181c2c0c0003c154860717600c4440a543c068483d11000e601030200c0042d080345819810320401c205842c01b504802d006061055483c02070607038804c0302040040101001c00c1c5c050648110380c1c05400341003032864000c2e003248401c1c4800c0040000c440c0005200300d204115041c0501112090302d100f981e0040c1c0501801002404215021800d150102e500c00601c0b40c10b0314080341c410746030307030490340e0a0148420705221811981641d04003c900c20014010380b92009042c840d14038800113180350304040a01042eaa0207408990465008000145c00300b030b03005c0c00f5603a02591103800b43c0ca041d03d4908412005d04590b400262044c05510000101903810500000c0c5481e100302c80070026803440c94080d4100e440a2103960081080c4580301c40020780c05c0c0d84a10343c031240506010141549403c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 808646843 1250 808645593 808645597
    0x70f030606050a0b0f0d0b0402130b0d1103070c0b040f08030c0d0c0e03070303111606050706051b0a03021e0a0e0a05100c081c0504061a0907091503020906 68
    0x81614415500d8406010700d0501441032405000c480824030b18080341014915114424103140d10f15440d555440c500655070340750104c3c1c0407030390f032910883d6005445841140301d660001908840651078154050200541f00c010b903840364080341c40e082d136180040d845240c019900184120b4102203180410000540401d0140d406641e04980c15501d807a5080d1210044421032542e6209114403a0500c41d0380d9030700000e041303041e280e2601d8a000816100311080d461728480c041050050480312801040341d03980000038090703150044d0b01c01d11030f42c2c076402001024511042d81c120081d800401c206284907002e90010f004480c00164030800300344180040c12482d8010300f1560700050650a040c41c49481c03c1110300025000486402103400781c050340180401d0003107040285064070100f5034034048a10703000a400c80c0c40320491b00748502c1c90b2500d456002000d45100d2407904006120703680060f400d1003500070b4400c05840d105c50842e10704107104500600c04d441c030004105902000301104980714100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 808648093 1250 808646843 808646849
    0x5040605061206190b0319030302070b0a020f04030605040213060b03061503010b07020f01020709060308070209070c11091f080610150e01030f06030812060306090a02061b070f 77
    0x10006207800c10404100381c551002008800b50382c440d500784102040d040c00010450702c080c00380020103244c044082414150004948032040c00401070100625030560010200c0600c140100c45099580c081c44800b02c1c02007400f400b400150501050000885550009400c180000c05017040c0380c42800e1507038140c1c4c0c51034000c3c10604a000c414043d29003004948a54690141503003503007103604104010f01c4900a2200c041e1080800a85464241c3d001303010a901600002c3e000344040307600d90a02117007503480b90004a000b0480741c1c000451103072027006138040301c0d64094035400a90b40d842d007c008030040080e04251000030010703103c200030700e00f40140070018815100a451180740500350300032001c45603802518101d00301d041c0e9070f000340c0e071103054054001000d08000a00350300c50380c00e500007484d00c3e0b08002d0103010001800c000d555602c41e1070520a4008904079103140d86e03080d48003034941b200010020b4100c00180450044240855004044c4500c50b5081f1203545a4400600c0040000b40d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 808649343 1250 808648093 808648103
    0x40b0d0609060c0905031209040e1006050f06030105011d041b020c18041502130b2d0a051b030c151b07021008060a0302040c1101180b040803190504 65
    0x8901d480070030040d0f002e00201c002142c101344030801d20300070200c1d13280d548491010003170500004a1000586e01d079485a400304050900300d0f00140002c021340300041960b4010705200b440212802c0701586007131421241aa4810303960400385141401c3c460801c00cbc030008503580c0c0552a513050540385106401d02d0300d221800c075130007050b10005040038040d184c0440310626480d14840130400010510040d025140200d1150380140c1e12071303414502c0365090125801019121030009003007000702c001c0344044102d10060801a880c140f03e0300c00c0204051181c14102030100f07009101002e0202c2d08a000c60b0b0441741c1c3c95054038688000b80c1d4116003414000350140314194071980502541d03600d5020005548030000c171640346841882e80000e1030300310658019400308501080003440e0303502d40d10402402158003030001c2c001801c900304040c012003040403428049601c8c1c40c40581c0c801c0b4500385003d00c0c1030f400ca1229a4140c50b961220750f107680c4001c049000340a40806120300b4a0018481c041c4107078028 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 808650593 1250 808649343 808649351
    0x22050a0222060f061704060207170a0314060306010506070f02030709021210060e0d0f0212100c020a08090613030b0907090b100f03051b0705010614031f0902040b0d06 73
    0x20305032107084403040c0d0000c912030491410309000007074000c00e070f1a441141a0310388074100ea03164a040c0d0302910039640700034009180300507410091048500508943c0301c094500380a1100580c07840d45000804440d003650590220004210506020008145460244003108407001694020030329104141d0302c1045220740c0050000007040b1b04224840c2c06c201e0000348015480c5c50121300400a656100c0c02e284103500c8600e203c81000484e0440000751031740945140e00e01a000440e02d902d0b9026510105600b034181074800401510108502040641c004405400c2c034880005020301c0c0d81043c0500842d61001403008001f140302001130b80d03c69040400241441c904100b00d000541e07180c050008e024a010041461440340c104900c500003034401d141c0052196108844003141c0c2c00e10854404ca0100c000600a080c01011f40160040c1e44c40d50040d91b501004180c203040c4c0d00d0310039418001da5030300082030002400f84950094002c2c14001000411031420701400603c2142003018221209980c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 808651843 1250 808650593 808650649
    0xd060f03032304031712070f020601060309030909050711031803071203120c02071208030604060602060f0403080603010f18031d0d06050a111b0f0622050a02 69
    0xb000820140200103490b6000c0c01c05030800301030000d40039501005018013104c180800b4401d180e5810b465480106030b201d84440d007030084024280d0707410a400403006005840012440c28080c2c0a01582e455142c0d07250b0142504c2c2103840c00c02840c01809071820055401c071f03901008202000980280c3e198104401205000107007018036106250748000301040c0d40f003030900007181d00207150311404034010201144c0a800707208224203000e01c50f00309a50100d220032800c1d05024100000e144604019141042520b4035034005a03601d4000b00c035208000203c640004000a00c521801c07604210060000b290701500307008802d01703644444050740b601c0f4072074410403800d2650004d0003150340d10094800081c00c006803004511401b40c400d5014111035155000304494a031154413040c540c062450082d5150210751008181c64205414032001e288110318103941d0a00c0c1c04586640a2102d000048115058880715200320241001d81501d42d8019060b40e03401507140c54040c0b00f405000c8200c1d903001840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 808653093 1250 808651843 808651847
    0xc12030207090c080c031303140d0207060b09060303090127120308060d0201020c040209030307140303010f140901061b060c120e0106122d0302150a09020306041103030d060f0303 78
    0xe100f01000c0081240611440000000440b03030480701144108104440314181524203895101c01c00c0c160200000c1c0f20f0f030071210540e0152280c10703c503540502060b690b800401c5054502503481690680003004610184d41c09aa60010303081c074040c2c5031180c112080d413040150026a940880308040c031000035001010351021200e0b6018008482c0c4042040603500000e60310b2105a81085c000c0f5030000300b02401c3e076020415100c0c02648120008141910004070607200d420a00c130f00041108900c1021030020603810015100c010003405101d0b1603860901c0480c0c0000c07140203070006016141100c400844c0382c5011b1400c084105884008811070400078010403a0305100b40310282c1d03407400c41c0c1445500a02070302c101d20310b80c01180e5203882c400890400040c46115401244504e07400d00d42002c00c064000c00c08142103c00c683c00810254cd034020180d040d41c0e508000250315402c800009070014440c0030f190003103158040c00300c0e8104103800c2a48011101250030151440c5c0c40f013102001056 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 808654343 1250 808653093 808653101
    0xa02031b010e060615040506030115180612020706090b13020f011107150315080601150507020d12020f0109030309050d23070203030f0304031d100210090c1203020709 73
    0x542034500070041c0d10344507a041500d400002c2c064030720400c0000100060500c100301540c1c0075100040c1465521f580d102c14100c034003d8104140b01c081880ba13480204944001d0460000325082600caa40c040c907060001d00d4000d511201040b140c1c40d59569030400414010101c10f4401e40a10f410b590314041c1c0b90041000c05084c1c17805042c100300c040c9820b9180d010010442d04110f503400c00b401586020744d000f0540c090b04081c00d0041081c661b09500240e55140000da050403180410500c41500c0d2141e4002c0f03c051048503c06900301000082c41700000380c0204801c180e400d01c61040d20140c046001d196800e40303400040913030009440741030707400c1848801d00810003103008504000140d110207950752000e1440f01d590b51032451402085030010340d24240116105d200f1007007080ca50300d240038540982130850140a03808225841d00d1060030720304250849030103c440d03a800508040501e0141c1c1c1025211101045800c6a40b83d800005d03903503550700c00000000d1003a0040e160180c204020f0744121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 808655593 1250 808654343 808654387
    0xc180e1501060507061517030d2a05130306051302010206150904030f05071a2409010504180b01092304020108010e070c20010f0905092a0a0203 63
    0x440c01000104440e07504a0102d60085600081c045038151072100441084841c9500140c0745a644880b1604480000f00c0100611130210b0030030803000c0c200b80c4030200c0260141c00022080c00c41034032030300c44140c0103801030079050074800c054120040c1c0b25503840d03003510b0003560340c12400c03400b55100030308541e018440d140c0d1005101d4100d6a49509801c00540c2c0302d00044c0026003403155444100d0040c41c8205c08480f603450300201c098008000902c01e02d8401c25003110034600300d8403c3d8140c1a4025500128260f8003074001f00304120036407c00d8204401805540848111a100b000e0030030300055500305450300900080c2c02c0060503040007506100d1b0056150102d04160300d0001c00c000c01030f038009545a0540b5018088600c8039502d139041654080180100504210b40301c062000030400900d0001701880c03001c0c0d8a000342d107159030f10281d0319491240101e82d405003441c000900304d188140798403032500c0c400080c143d4140111389000c0400b41d0100c05058016000080d043ca100c034100a90044a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 808656843 1250 808655593 808655623
    0x1b11011e0219210b010203040312080a0507050307020a35090307050105070c06050304030318060c02070506040f230a2c0c030a151505032a0a0c0c180e 66
    0x303290301c2e4119224034080c3c10084200345952011601070741e9100f01709490156900010507400f0151160740603285200031a50800306909000000300710b28400c000340d0740a01101e800070014401c2079611a00c02d800c0520701c60301c03002c10800c0c0940b400c82400c281c40c12582034803a0640e0381c1e84900c109141c140400754103c0c5050020811108000480408240088031010b10b049600d0303480f07030324040340070b0546112004c51200f05400d6910600815a10031641440e6603003c88814a40e07880900189008a1240103030f40c4850b03100402c07504000410340010344d520071480c0000b14401c04001010402c10f0341003008400c02c440e00c0130307460485c80c000381c0a0152458813141d41e949424030711800280b100034181020310361034900010201480c0030800000d000d4190441c0d4454065140085c01a04210364a00c120000300315020000034a260080300325442c021003452900d45a05030036511125402c10031076144070300c101c001540312081001810081d40808000c030341c543e451254186030682e0b144181c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 808658093 1250 808656843 808656857
    0xd0815010f021c090306090b090106150512040c050414180109150f09080301080a062f0c070b0a030203070e01020d09050f060c151006031b11011e0219 66
    0x1c400c94000444101c1003400600e500c07a00f0b90082d5044075070440c29440209101d092003100c0040042508103640b02c1d03111403008210304c55903800d100152000000860740428010803800c00d1481182076805c0e8460300841240b841a030303680003c58202c50140b012307240c026240006000002112074041120014a2030007800400683c1d10b48a60008e81400740c0c079103045d070b203038130307866601e0034680100142e00c1d0040d042980301e40c0e40b85c040300d444d40e094040403108c203403500b49840b070243c41030385c98003809a009505507030000311340f030140c45050303408044411550f1003903220000b0004840030081181c01c515075130143c0c80341050b02010308004803410819040d90020300d140814540c0c4190600b0031140110b5220b40000c041e080410540c4c460484101005e0080003202a400800b10182d680a0345e10300414070780541c0d660704110304075104a18101160725940d01d28400c03203440b40c11680348803408030000003114409441c0c022040e40503560801c1c1030780d4002c14450405108007030004070380116400c1180d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 808659343 1250 808658093 808658117
    0x3060a0602030c060c180a08031806120c09130204090911040c0e040b0d0c1211030f0a0f1e050a06110405010c022803060e010609110a0f030e0d081501 66
    0x303071103070f070010100c001750040481c1d0302c00440a2103e9000320048003030400455683c990942c01c0d01da80c400b110306042c4003502c0b080c0300803605001044411820405041d00b2598540c844a43c0e9947d02c5900c500398080c228554105d41800d01e44000e1009100404c000643c079142c0f450111200310340a04174620030380c50020b01c00300150f00640a0049200101d40c00210004400000b030781e440100c82014006c2203d030b183c0464400604e41800c4107090050703040702ea40540600030540c0d603518517040c0c0c0406403c61004040001c42c240070b241d1081c4e100302d00140428036882c04014030441110b8041c0c80c40d5010344000401c1c0304d0740e8414140b840c00c00c2c00030986054140000600780c1906600024020061481800104001c0320000c41001c0329100c6144007007a80c1c3d0070040003802d43e8241d0070129510302000040c0342000e5200302c0022241a03403025007054200320040d584e4103071920518090503150340c46d400c1c0f918802e022040007010592201d810328100318400d01c0490b14590619414031071b10803005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 808660593 1250 808659343 808659367
    0x6050a090206160320010b0f0307150f0e1c060b03010b010903170c1f0f0606120b031002040602030c150709121b060306050315010b041202010c02130203060a060203 72
    0x481c94001c80e110103480641c01c6160880700030b2205e140c8810302220341c1a540c03d8900064010104a50303049414503a000d1175001015214001031144455802c1c1a82c00e00300d02c940548207807800246e40f414078000ea5604800440c101503880190300450003481000384080084501c80c0302100b501c16002001041e107210700180c4040807a0101514901810001031000c40200e41102d0b030010394002a2554001941c1c00300018840304050a52a5070070240d9115102c0414414442100c0c045da548030a000d0f0400c140000070415001040c0d05801210240f40c20a03800b400100010021640190b030341d0205c040c4c0703483c1060582c2d50440c41200c240000d100000d1341c0128208191a00e01e4003c1a250322507140148444040b04201d00300012107800020703070a501075000700d00711035059042d82e00b900350003910745962035000d000300070940c0c01c10301080c4014208401803129140c81811b06003030500b500e03000598400d00302e40b4000c02c0e481d000002c10043d0b0405000d180000c2071940015410040d2544c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 808661843 1250 808660593 808660597
    0x2040207081c090b1909061d07090903021b01050c0d08220c0e090a050105190e0606010c1202010b09010905010510110a03051813050108060601090605070b0403051b0a06050a090206 79
    0x402105c19030110185844904154001b6078a1544100e00304441d0b001180181050300b203c043c580407034000c4e2140000c1c0316005000e80e100c1d4941c5070703020b0440707440c00c04c02c8007444026140640e81005410301c80c81c1e6060750200540d0a807000036481300c50781494008058420b000201c0312031241c12030f100030450000381c0e14604d8581610301301c040c40141c680d00d21a03400c0c5000c542c0007002d40b03591300b01400c0c00700e028084940c0e102004c2c641c02c1c0900c001c01c80c0c00003040d40d074802030780c165000a80806096001c51054030f40010412064400415184480000550341e00420f811901c46d2680d1003004000602e803c156041050169042c280350080031206099214000d03500041c0500000141102e4500c2900040d440a2130009180b88452001881c220000307190901402580d4421070001c101190300603c0b046003141d01c1c941c1c2d113524000d0641d80c0c40c952654094000c50902c281032112591428042c00c0c180d01c1541c0c02d00060400388082c1c00c0c0f030000d40e140944080300007454244810050385848003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 808663093 1250 808661843 808661851
    0x105040204050f101809090506071706211b030d020706020d1b06110706050109060b040513020c120a08070e1507050c120c030c0a080a1e02040207081c090b 68
    0x82c20a2514086030f1045d01d00c00104e00c0c0616801050480108014809502950303041c2c2c0201c048510b035135280381050f40d00c040d1030701078039080e840345200140d244c0c502a41c40c8100340c07180c441c20345e4072004400aa2450140c0c890f10100b11802c502441d91100d040801c0310f03401e0365003684010f22240d8034103500a1344036844481e6840c1000b581c1d1500f10881105494038404041d841242000041c16400b8600310903006160221592420203000051546950050f034080c1d845002800d40f82c0f502d03000420210a202e094004515078007401000b5607040c0a11200400f1501a0421640e50360312103001000004020094020320104159002d103c0d141d0020f48400007040001569845101d414246d2801c0ea0318504e40d87d100520742d00c00001681d0108100c0061102a81221802c4078103c007003184000d40307401440115444984c0700c0f004207000721070b01c10a03001c61039035103482c4101c0f540204050740d002d0001941c0d2030324009880c401801d900d01062071584100001002038150540d1580c0081030054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 808664343 1250 808663093 808663099
    0xb04022b060e1b0913090b0604050c0d090516170609060108191b06110c0423060a0b120f07030207021f050f03041529100c050d080604050105040204050f 67
    0x149a04034100e8203030129072130031100408041803a00402c01980241544000403284814901d0208070740b41003901489000754940701c560703400c02020f840c11400400b00a0000d403510b10807a08d10b40c9000101e03200c000d02a004d00d0941d520b55180300603029107040301c050101543e60340120010420148081101441e0301011007803031100382d0260600b00c81e040f45104018280e01207130b000000b010f640003082c00c50401c3e840170507070360405280303420441160100311007001040500742d50208041407000b001540f0020080c00d0340d8545e070b214408805140c01c00c201c2c5c9030340c0b50144018480643c98034103180358042703481e16055150442d680c0c04114441d141d0712100c904100181d41c007481880c00758040d0385031600401c0c0e010fa22407034142400d4141100c4044075000081ca011095484115a00d0f03030360100c2a03000005c03400d16580358050003491150030b581c000070000100c0e0403d00144082c8100c01e14204141e503130800c1802c044082204444040e071025115901c1048100003a895003540045810011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 808665593 1250 808664343 808664371
    0x90501270c031203090f212309010311120619080a080c120a020a0501140c090409080c0a0c0f30051005090d08010e0106021506060f070510050601080402061801030b04022b060e 77
    0xa10b005038003906210000d01e82c2c403500814400c0051200081d010f10ed102d00300c40c4c10741c0d015501c1501c0540420707103016224242e0424406030000c01c071080018006400000111107034044840306001e4207410108451006802034013114080c00401d000b4400c00ba08440340034502802d110600380c03180c0c880d40d600540140e403588100028041d84030306480d1442c1000054030744140c568505040b070691303139002e83d40c182640c01401051361480d00580010702070441c6e0b0000c1e0801c0e0a40c03810003210a64481c12540351080010410202180380522030003030203e800100803c00042c80c01410341d0405800a4280c002c1c1c00c00100005a80025500001c00d4004c80d2052162503e40205e440c0d48a406032040419200107600d0080101c0042c1160001d00364030f50070031030340d02c690004560b9031900303580c00b80d0f105800340030008007100d40c00c80c0100f851310141800507400c0002d8001c10160381280f4401804074111040102070f84840048080001e14005000c0002500f4200701c07a106c80f40c040d240209d0380d104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 808666843 1250 808665593 808665607
    0xc0f0f0302040506040906052701021206150903030d1a03120d0e070e010303210e031e12010b0301050a0512060f0910090501270c031203090f2123 64
    0x120b034851b88071a5081282405036281c11140c01070b0480e90500101c400e80c8010140c0545030506100392002403001440500c00703a03d454007005500070011710043c030000820030040303a1030382d0100b0007021a0800e220740421050540c2c210450103040042d880c1e8020341224840782400354100d0101d42011004041c0050140c4561061038603080c80ea8001d000490300d5040003105140d04010f810a0415000c16003404140301c0d122501c05417810300f100034510b03920902c0944000a011800b04031780d1034003040244d0030107858a4110501d050282d01421005100000601c964100368a48801a0030f0958140c806c1d20450184141d4030300004242d807090891034000f00e0700000c0140700c42800b60746107000c01e025076030b080d080160003024902460300801002007050b0030218800010004159000b00c0d0034400a80f41d601c840300c107040729404c0c1e42d080560310300da09000111507600c4030b1000d80c010583e0400c0100c000c0760002d400060101103505000340c5030350840e02000050360503100c41c08159905903d88803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 808668093 1250 808666843 808666849
    0x50f040306060803030906061f0f0e030303150306090a02090c0a030e0f070519050607031107081006090b06091f0c020d060e1002040b04050103020c1c0c0c0f0f0302040506 75
    0x4035000248a2410300100164415000000c0e60061000009544ea142c80382001c100c1c550141610113203000c2c401d840c000114600030781d0031085104280c10302617100c1c10b4017000241141d000702c40403903030f01a0107021801c00342030801031030b5440042440180700c01039042d0005440c681e0010100100c1400004e020003406200f0707081800395031400001c44103007246010545031104003078090a0b009a0707240b2482c2e0b055002501508044650190146140068035181141c1c0020005a550060b00c60f5110004070090304100d0b2282c03690001000194450905000c00161210000028810242030140c882c8507603480703032425801c101407030100750b4000704000256510402c2090107540907001041d0340b001c0c016283c0000302004c203000b05030b0f444600c4004201003203000c0c6000b00f81d0300d038100f4401804254026401080600c104030110348140c4801d820b441885000701075043d0008083d0856082040144850400071b081c0c038060103400c0ca4103203542c0b12045041880003900c2a80c80c1c1d40801c030726031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 808669343 1250 808668093 808668097
    0x110a110a030c03031214270a02030607050a02070b13060525140105060d082506330305030d020f070f03050c0f240603070e0a0501060f020a02030d050f 66
    0x16600c182c007111481e07501c0c10050590961280c0b2040581d01304444480050f0f043e08089100c0c403400300420403414903205110300485500d05001c0300038410210301c100960341c100002442500c0300e6031003aa49400d080e00007800e00ca0142d000d9107060f00280044542000b088000c14141c030310910b1b109899203c140c0001c0c100d5124120054040c4215103550f40c1840003454850000070f071740e10001d119a444000600c07032004a100c0001c0c0c803101c010f11140c5207000d21582803482407540e60300c8115030300b40c0301d454441c115900170000000c81ba001a80090300d10443c0450401d01c0d0000b10601c10b00c0915546500c1c0e100c1c407036a41c079011a80e500058070b514400c1540256602c05400000a80c030311802c5180c003404650000800d40003074440d4800a04d00f40300001802d243d0303542400e1809012410030595250b2400b805000c4580c107014605000c0350080d40b820700c851089841201c041042d5141040c042c18134074450b105076046411000c03c10025890000303281070440c00900d000c90b0b407441c1001401c3d070a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 808670593 1250 808669343 808669349
    0x281a0405041e0501090b0c030709090216230f060f15120d020c0a050a0815040827100921050717010917040812030703060e25110a110a 59
    0x2141d4800c107030b4050203815401074040c0c40c8110324003e51511650401c248034001212a40002000c1401c10302000c2c4540d0007070700e044094050004507131003166540c004c140b1a0702e00000702c44820702440e560800e40c10000000c10300b150001808050a108034420760420340200250045031280c9011042a1514000d54114280e48000e41d4164000d4000003900d03840300c1e2801611070341c010000401c0500c0d003d201c440440340041c009140036054800b0714244030704001e1055555100900241e10302d11603121403181c80c0d2040b0351102c180a40040c04110200c0749420410f810410001001d200b44440c03200480c0d80072040343c0c06560481c2c0580303000340c5000c0490708404a03001c00504000500401500044401072040318902210b0406486c0c0d00494041c0b84a82a483da04c001d24629030f05800000540c1c002080780340100e42c0310b46030116030841d8401551306000c0180ca501000c040c203000b522135410312550a140072020780c40b103000396a94078082454058403000b48450140300e02e170703646400d10000f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 808671843 1250 808670593 808670633
    0x20301080d181814181902040b0a0b030a060902090609090415020d0204050a05060c070b0d0b090403120c0f08010b16140601030201110c0102060f0901090b281a040504 73
    0x90f16619041c80942000001c0d0104151180702040405c50b080d242d502640c0c094600030011400c6494005081800c241001c0e0b802581c1c850385814039407910b6074070101800340c0d01c2130f8139a81d0610049520032038460b0ba01140d1300501c10311600c0060740e64882203841388001154600265111801d21804035003034140144021351000036a81600358035a0058401c03540c0c100e0f1022a620707a2034042c050148a03151083c480c60704806070a2001d103004c6401b80034214410400000d03100c8110b00426a801c0056a0980125412016442c81a860350007000031002051802d82e4a180410001404852060041c1081c011000c0f90040301c1880144481940d1500008022550144904002e803180c9003800180d0000e449090014804000010140701c1d00d54181e00901896803202207482d02c4201c0035098030059501c9426600208031111710041c05060044504040c0c0141c800851041c0c401e1544502d601d1410711020b4000c030426076420119581d005d03900824590388510300002c1000c020030034412 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 808673093 1250 808671843 808671869
    0xf0d020d0e010605190b03013005100c031e0b0621010501020613110d03140a03050601120e0c0409020a080a2f09070c030504210203010b04020301080d18 67
    0x2025200c150072034000c0784c4003a02e009658598103000d41c40c00e02031318041c2a0b104041040100202801e140f00381100fa9007110031034000340c0458100790305291003000e068565900084100c1c401e2004c520030918440b2403401d042044072034150703180d03150800310410800d4050f5555000c8070643c4030141180c1e003100300101d420b2401e54280f02004098002070090b180184203c80024044d80644080600c0c0c181c1c0041060058044450800100d01d885900490030441900105282c4255660190580000c1614007041038134000d00010b044402540d04203d41c03604080c051031007100c0102e000345104806903000710301130307000e8008105c40411503030100c0628410f2061401c14441550f4014001d219400004942075021202300e6482054000035180c0c414943d90116046030f02842d0320a202d07034843d084c120304241d6906458a01a2801602140e03d1a8811800c408503c2d081c81400300200c4119400c5042d541030a160340d5581015901507410321441503809111030760340301d0030340000700b42c800c060003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 808674343 1250 808673093 808673111
    0xc120905160b1804150312090b0a050d0e1c1413060512092b020708030a03060815012d030605042108060303271c0308011a0f0d020d 58
    0x12143d44641c00c103091030031814001ca005131070302e07005031200584c0c2d0081c6003003c6400c0d078a48100ca0882d07030810b5014000f824600040b00c03d000c80c09401c0950030b944489895205c50031070f035030036100000d503030100c2034108a20348490640000b0055540c0c0d0850f203400d0b0f404607000f01420314684501c02d100408580c007044001000340c0d000e80242406540075a41e4911612112005541c0c0e03a80c811409029010b069003104203040b0141940102d000a0720446809590707a24226081d41c0c850304000300003d80b01c0b80280301c0c5080c108030032080c4106403e0280105d6140264011401294010362030b20964180c80c40403108180c1c03c0d0304809580c00010421944c00d1034030b41180814544030100e007104407428444a07210b4083d550581c851207010340610300e080504c1140d4848010b5080301c0504107000008181c140f6116068044d801209200344107541410a007006007050005910120014580e002c0c02580c0002c03600a8940800c2d81d00701403510394000b020720070040e01811081000d00342c600407a030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 808675593 1250 808674343 808674359
    0xf0204080f0d18030f02010804020102190c140a030825050d0503040605090d080103060f020c12030f18070b16200a060e03061302030c0904150507030c12090516 70
    0x80d08820140c42d0f100104805040c402e04601d01c9100c00b6003028546841c02d009540140b035490ba10500c140f069032440c480c03242c1001000c41f07046000b5181c010340107001b80950520758054170350700301d012030b04004810301c0d55031014841d00c035103418044682045080a04407170b40c08800340062a03031001c01d540703d40c02e15010080040d00115001ea55030b80c140404141468004903281c404c4000c5507940400c0d0341c0c00c3d501e598002d440c00d44060890960b00300800220b200d0284113070140602c2d0080c41c10f50b2802d01c42c0c60310035003800c0035002c00449040c440c08215440d40c00903403117040310b0003403580f680c5418030f140c4528801c20124102402e51400082ea6154076075400c0d000a00000046801c85000da480740c82c00c071610090361826540540c001000306880c260305c903540e01c403041d00c0107013110070f40b02041e8007041e00000196002c4402e03181922031042c0e183c595028069000c0100d14082084a440c80d00c010a0b0410f2101c100040503a1888680e06001c0c041c1b01c41d100d408000c00045040650356281 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 808676843 1250 808675593 808675603
    0x507030303360f12051e09060304030825022b1e09030c0e060315061e060f1b010c030b100c140303130c0f050a0317121303031b0504090f0204080f 64
    0x12443e40201c425886c000603d0f80810b0301c0340000b0140c00941582d8031940d050b036000d03402070607100c82c0729050a20302c200300c402806003c00c00743c03041d80a0712800640750503c4c01485082c1e000c07000c4030030126074003458240d4010072a84003da01a241d0b01004e405514050302c04003030a41016010200c0000c000c18400c0c2e0030717807805000c2d5800381d0448060070418480d0741402c00042c0e034010f5000c040b0030400c0d820385502c1d00304080450002032185160880c00a80703c0321340e5006507143c418001c8603144800c0201002e01c5889600129800c1c04e0040d8051140050304021200c1c4804003401102220142402801c240c030011504850044030750707038100100c2004040c1002a021a92130300043c0d00841e0488054000400300d80c0e020340302401d402c0c155651400d240d0384a448401c0048801d01c82654180058402c481c017580300e055412039640e400d820010292940089501c176205402142c04000302d41c440d040b9011110040000100307010302c01c004c040a88078a41c072048040c13040ca14150011840412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 808678093 1250 808676843 808676857
    0xa02130e010314060405031815040e010618141318050c10180302060903120301060e18040215030a0b0a0f06080906070903020f18040507030303360f1205 67
    0x10911607110541c0307205130340b4a404c5034003d125800a005420b4642031029800c47d001c0302c01420002c0044815600300349540281d0f008401c0c080c1003100401460ba000015803812615074141079107101c0c1420011074510210000490140c0801c038000d2446003120f92164402a034045420f01403c803c5003403042e5a0f01c55110040d21619030040c0540c10f060141e07810080e02c000c6081440c102c00d10715001c02001d07801170780c1d4064140c090070701c51241c0016035a0003140607022030348403e42446074181c00c0c00b0190321030b4414051000084420301000d0398841001e00341c00400d0607003a03982c035625040b80c81c014050100d900c03a00709000c1140412582480245481901c0785030303035010f0f001ea0303483e00265030302d480a0382c1340400300d002c0c2c40d030601c054245929000c0ca0703a070003c4c02c90380325101100d083c507107000780072181500e29401644080c070815600d4020100310101e81d03c046403201c10622101d401c0d50207043ca8050855403042842803c001580e82c2002506400000c80d001c40d0765000f0f00513103150711540c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 808679343 1250 808678093 808678103
    0x30f0906070614102c060d1a0f040c050402040302011b020f1804020f03120a03020f0f0d0213050303090a12150504120f050f04090f150807050a0f0803120a02130e0103 73
    0x44a001e805d119101d0702c610f00410f41c3c400c01001d448a2007030100142c1e210006440700c026903445011074400800142d4060401c7d802142064545400d0542d038284035a045113105500402042016070b0344601d41c010701c0010a90404040c114610008911000402030203800c0802030b0403500840540300b2034648914000e03146801e08442c0007041640300c60407552a103007030306010301074007405034400e0307014003112134142e80c09518003008100d81240ca030300a04503c0301050b4000036158040710030204000c0081009500950030810400b0018030710320001d00402090030000d1002c20240b03c681d02114602c0310944004000f1828103050500804001c851900d0102c1e100030b4252060300c2c42401113400d4007032803c082c1400c0c1070525880c1000b0740001e0f142e100095440346200016040b141c0056401001c4210007060520b10301001c0c0700c03940035580d02ca1518860100d0301085980341c04030440b00c1000a0310f0221842c0e5440c040c40d40020300450b583c400305040103803c042950740590403400d050b2802a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 808680593 1250 808679343 808679369
    0x150d06060f0612090b0c030405030d140a150e0a0b0d0c09020301050306090a120302160b0901020c070b07050a06150e040804050a0918122d03060602030f090607061410 73
    0x548a46041d200382c144d00901e108200c200182d65044034001440c1c025100304140d070300d03100442c081c0c17a040e0b980c21100040c1c0390000703605206442e1900e21800c541c0f03a0910640b038154914081d03210500007002011070344103c0c3c881e4810a083c0e600c68448400540e440400e040420340c6454031080290400d025441c002d10521000c074006580028000528a6010244020300e9110f090708074065080b480d026a044400d2006002c0050020075400b44903041c0718000603108c0e85042425032414000743e0110b8050740c01080400081080481d5011086401810218144241040c03820180740b490340400b4504180100344020400b2241c010300449800320f4810400c6d0b43c581c00002c0450303a0f0035000402841404540c0c0c4001414107440c042c21010504140380500d0240b001c412032100f07040070340078180035074220080f803482d090b105040c054001440158100f00310050903281500c180caa4032446088046299400c000046c0c1190318282c0142a443c4a2410010083c0e4018281401044000050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 808681843 1250 808680593 808680617
    0x3101e0303020f0f0601120c122d0203150907080307060b090708060f0f031c110105010b0703023a1107270911030d021501050d030503150d06060f06 65
    0x40001c003134190282c8a400741005918114402c2600c02c071040d030803580c0840c00f2070001060080b402e08440d0706402032001c1441e02030001d500501c58080440001c104078004030344800541ca0010304040303000c0c4001307000e04003522106065840d1401540c004500b07440000707550341c104121a004404902d0081d5206600b0740c4510400351001030040720410b402512404407082d41c0e01d40381e0703081040c0c041c1c06410750320440344032602802458841aa05d030086142c2402c0240b888800f48103079401018800122410814241d400a4440003034031080483e4018200d415401c0001c0c603407000c041100049104280c1e01e44011001d040000c8088004042d03008242d000105958040d400550610b1000c000d020300900f0007003400001c00340010151100340720034000071a00d840030400000c1066a41d0010600c843c1d2240310b1016815050300903e00554500101d9400241c02009698004001c1c1b01016004c0705601d0114a000e078405501404150400500280c10026180d01606844d01c59540c1c02c1c070541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 808683093 1250 808681843 808681873
    0x4051507030203060121240503070b04080d0c051501030f030e0916030f0207080d0524010203030601320a0201180c0909020105360d0b070503101e030302 67
    0x4840080c04103428a07075501130320121b5040e080440d10b00620014100c260039002c480082c07642d440941e4601c00c5080240083c0c50200050001003999031040741c609828031101c1031302da5550a0068003030008604c10f0780200310050204511000204080d09159a9241071403d0380d8600c2a40540c0481c881d100118800e00300001a5032045040725102441d4410600e4120002c01c100a4404801d039801e100600001d254a4000c1512030350780300000ca068101508800181c81c0c4039000003c0c5010903400310149640c011041d44e80c800c109090148c80c0c485400c28140b00c1894080340040d4444942c0000d40004191401403c00c0d204564003c01218000c140382120112509502800300c44015100300001e0035240c000050162061401c01d090501080b1050401200c90216000055032200007a800403c143d1a03d11030003421590390701c0100003512012040c03000500f0050421000000140640c1742429a1000601682c5016140d035044a55a1100818140401c5005002d0310039040b41180c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 808684343 1250 808683093 808683097
    0x516030c0207051011011503050d02030301062c060d06170a020105043507030b0a180b180708060108150106020601090b041d06070311181e0405040515070302 69
    0x40c0268004103102410441009a010400301d00c500c100202000288403e82c42801500074998407445d0032004582186001d40c24402c10071001c00031540b003071004120056014540400c0c4e8140925116603140c03040c00e03007291444c0300c1c64030142c00040004c1d9454107840c40d5404081241c0041070300031100c0340d010b00b541d5100c840408001c1c0c0080d0044c0414810740b000c0030322107440980c04401e541510188000390a4145003910300c40d00040c4c03c052070030030034014021000d69000c40740d507404110702502034860500c1030310304a81c05094901ca20001842c05880909a003068000c0d41044407080d0360790300c0b42195110400d00407030240b8020703d030314003180508180700d4038165070701500507060700c2e030130010203400504055024540c01382d00c0d1014001c2600e8035012140c52038806901920141c40c0c0290064241c440204114135407002c100701e0809015140b40740c11013202000c80380c190f208403c2d204041400c0700d000e40c00e554480d191130180001c103c000124aa441c15600d00e10110503600e489003a401c038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 808685593 1250 808684343 808684361
    0x203010b070209060406050a080f0f0726011410091406102109030305070f09050a06030b120111030906070503040f0803060d050d0e0f04150504050603120a0201051603 73
    0xd20000c1c44032400514001c1c1074168000009070002500b95990310000e900b090043d4031221050300250032041e914003061084904071091000188610752034103001da000f5045001c04801201e0120340392100101c02908a405281c0441d002c4a0303440c01c000c1004801e1039828407070001c12620703096900360801c40895040d44100401030400380c40d08400703881a280b0203140319600207660301d5075079040c848030414421810024000d0f5000125494550000351010840440b58801c0c032015203c10007466607080e46440998000380740200d8000d10740030201d03d041f450303c0840500c80d402c10080c1107a000141e00074520486021044403107640f580c0c402514070f84002c0c1d0300a13040fa1040c4c80300202140c0500e000f10b800c05000b4015400250403034413520b04103c880501400042c007400c02c0e0441c00d01e440490310103e00821a005c00c1040790800c0748200c100103a2180c0d41c01036442d00d002501c0713594140b0213000b20326603510803569203c0c584800280280b004070340d040100740f9404450312100e0b200740f0503001d507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 808686843 1250 808685593 808685609
    0x204080f0105060d110319060207060e0c0a090b211b06030411270907051207180c030204081c1806020606010c020a0915090f020c2a09040b19020301 65
    0x4d007503458841c14103201c90504003940500c0307032546151150768807078038517080c070b6002d80d00c0182c981381c03240340a6042c0c5180381c401000e00d510211200f59a43c1d50300344900704503038241c080000e84480650100da0540c40c50035841c80040002c00b0461205400491200d2546480f1414a02c007181c0d44400c10450f400251400b41c411050341203210000d003447c4441000c9229003060204024180200a00109104441d54007254200c80d40400c25401c000c482c071110000586d024011041c20445803c040c140c3c0c15520905041c0c44000944d0a05d00960490300905500030941c7d19100950542c00c0d210f4000741e2140000030340100c0c00015500403d2442d10640e54903031b010b4801a25160011618101414000c1c1c2e80803140714030000f611250341c4621450022071702c803607800c824a801100401c4440010260146d10700421124410302c034081015058550f200040f00d0000008030107611900c000300d400290003400da48144030600c441b20700c40c203100d8007078440b6081c3c00c400700703445010982c002031080c409 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 808688093 1250 808686843 808686859
    0x3041a091c0518060a171003021201090302060f07050a0c020604050907020d1419030f0605041d1c08010b031f14030d0e0f0d110d060b1009030b06040e010213090204080f010506 77
    0xb0382003401a000da41045101f542c8115154903138000640700d2100c0d600c00705041c1e548407100000c25405101d032039801504403d0140040c540440c0c00b038514032407080702c0c2d410410003030411021551503400b914007134840507140100510302541c0c042d50b12801d1059182c0800e5010900440a08001003242c440d8081c3d40d40001c09400c4400b0203078060314010840c10309590f01c81c280469103484078492440c6d440c040482d9040742e00c0d131081e022401c0081464034110f06000c00b40441d038003550050040e0b0304640720080c41075503d5a50190010040c00072808281002102c07036000a105103500d680d02680220480c103a034089001c9103015652a0440980300e030300715240c4545038525160911881c11140d00844549841124840002e504501405030440e0815a10641c0c2d110500341019283d00380d4280d418080002401c584800d14000d40007808680710b16140c40c03056950302420b40545000b0400a400209030bd61618031140c00794020340250301e040c0c0715064810b03070865014091a03004450180c0088 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 808689343 1250 808688093 808688117
    0xf13030311123903030a0b0d050712051203040c180c080f06010314100e011203080c09060705061009050730020910090503060105010503041a091c0518060a 68
    0x1a500c0c101c3c207007008002c036012041c07041c600c100402d40700041c00c09090142d956450481700c10b0003124148040360b4000d0300b076544100005100042c255042d507069100d80c0c0c2030b1003407500c1c01c503103414850090205514000720a01003000004403698042d070704504550540e412510520208441c021aa10000960b82e800443c03070740b5003405e46081d0800410f14001c118520740540c040f07040c0d5825200035a401d06580c0f0100102000c8021082c058a0300c4100c880345040c068900405140b0042d00902003454001500b818507a280d074103c424640d800415035099151111003040008410f00c6030b2903460342004000760348140310301042048200c00000b9000c01024940c1c00c0044a02da11082e0709099030300b00071400362075a48160340c0038800400d60740c0f050311600f01818103090400c10b034459410300c002401071100003000c4040c1050400d00c100d03200c51144e910f0711186441d01c50030200086000d100c8400d408000765214000b00442130076990280c20380d9146000b4003015203d5080798100203541c00c203410f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 808690593 1250 808689343 808689367
    0x9060605120604020925021509030a05030f0a090b0705090f01022a06041e2301080609370e0f0d050705010209060d06090e011a040e01020f1303031112 66
    0x450340085c182d0070410603146d609190b00341c0080c007082c00c2e900540e010003006811032a1418840350722406801c00345081029010780030340140001782c2803002c07054dd0310700000c480c0c016552003140b040707400c010b65603441c5c1800d0801038119070190078824020500035503000c056500019031110070201460a10b591841084000d400200c8102c2006504c03402c100800a00300e06081d000750545141614502c0d4160724118440d104400c041000b0340f4040c200111901d0560b0300801c0e45503200c00d0a4400c20303415030314002c00001c02d03004070088c1c030a1048242c6900d1014080301100c0d1111b1404c4807020415002c0c840e003965070f901413001802c03d856000740c80140040e0320803009004502d224034000340c01c08400d40f00160140d08903412100302141d59500400c00c03040030740111451450518020000c21082d1045596440e039a012982c3c011620f4280c14218030310258103d85014050084c03068030b40300c1d0092400d1800106100070350024031080781d9003982c10741c046500704141601c02ca030207103401046000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 808691843 1250 808690593 808690609
    0x20f0d0b01140102030c0a0c06081303080f0a02071401020307180308071209091a09150307060e0d02181005010f0e0f0a03050303040317090a08070204020c03070f060906060512060402 80
    0xc040c11408240040c2c0c18000c41080651200b9101d50740d02040d0f07274101800208110402481ca0b07620002d124403030700219401c03000c4150042c400303407c0300c0440e41c0c801000d400a071040c2a801001c040c503544441c000104107602660141d60195600008000740004d1601030500300d00015145050820401c0b000812a2448400f20740d01d40c1000b21035241d541e40b0040445500c41400440c00031096845400c1d4500451265030005080300c0d548418000c103408a0394907003e6008030020321100145071401d541e95420060100b0f42e008002a00d201e00126401600034410745800c07490040e00c11010580c2e60107021030f03a4204000342e40780e01500070b400041000c940300031003070650098080d11000c07005c1013040c40118410740c040e07200d48001080109070701c1ea041100610620311504052414400900231008032815190119000b42e20b4001507028a81503205440c0300511402103890420304110141e040720400034040c13601080030651740d90078070250000b8550058a150007117070009006240c0210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 808693093 1250 808691843 808691879
    0x50313020109050604062118020f150a09080d030b060f0d200a0e090c072d03020d030506040510180e100209030105130c03200d08030103020f0d0b01 65
    0x1402d601d03116507600106040e5032080e007240e03002030028450020101c507000000e1b050107054007810031180d0510342c130394400110880340082c803914180c40c000e03000b650f4400b018100e240b0380c10303000e541d0341ea00501d01a016681c039124034500e9000d521611300c2c526000b4404c006400310b000d81460b14104c6610441e001c164007020341f100c41e86541c1d01c10324401da00c40d02101d96004810031a41c036500c261546024100201026006104649020400c16428034460a40d5903090b400f0440840c4010540c540309503910102c04c1e000c2001491540f10014103274009507100d40940191010840380d2140000d00099620840310403450301c041000820501031098140019030a0b490710004501d88102c8072a41010080c00300a0b00094010a13840d030039140c02e1240c03d4003c0c1c0c08203101d64542c501075603011444800b0303110103866a040714203542021050342e030f010700000c88020010301c04080750f482c140115820a00050f4061604151b2000345401d00b2a46851031720b400c80343c1c509950703280950084884a1043c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 808694343 1250 808693093 808693097
    0x2060105010c052104030b280c02070504050f010e01150507032706080a062306091909020712020307020f040e0106030c0f0302150f160206090d0605180d0503130201 72
    0x8072030080030004004c4551303601100300070455600c030300e54208806580c5016000c900c2d1208003c1400c90580230103404021101c94000c07001c40e1000d0a0358051b42030008507031106401c14141410442903500c00300c2018169080c5034040119641c840c10781c1c2c0080340074a035044d404107400300b0113140441e002d9046c2e0098003140c1c0c4116449001040f0a1950380c2189501540104400e0010301c00d8010707441c00b41302c3c0a014580040800c0840d170b5980c2e0426a4000d600e510b0041000040d26201522643c0040001142c2504280c0080b65201c00000003540f044c502500d0000c00e03c001024014804000c40308541c0d0010400110b024107901008014440807104600ca503503204000000180f030341c800040200000604079590341d1560042c0b2551480c0410b0204e19040d0400c01500d914555800795141d100c15440b900300198564400300d401403103100142039008454018003810083d0542080303100d10702030024a01110003c005e200e60740c5445104440100328184009102850b044003e504224014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 808695593 1250 808694343 808694353
    0x901082d100b0c0105090f0a410c0a120210080709151e05040b031302030a0b04140d0207060504090f0f0c02030a020c1c06050604290108100602060105010c05 69
    0x9800302d410782c2d0344081c1d4004010b9450b2820001c00b418284080c01084e2103d901070a0071003a503682e8003d08002d00d58001300c3c5040401c2c1c0c01c500c0c1d00e100a0f21520f41c01103204d24100442012a1032503960011548140d11036142e044020800070b8599481403410380d4050100500b03000400d00540d4810001441e040801614140005520741040b00840301c982050b2030750280c4080d0340f003010600080c400240b8090241c06c0004200c040360420889074020785c00d40188243c4c80c8038ac4002824990760502c0503104288140500041c441019000c1100c0861003084544403013809106a0329401c8074422440841c0007440304006c40c0405401c000c46000b105240019003010207400b031001c41c0d14a84c3c140380160300108103c001f440d010041d060b0032180c1105c0155016441d107104c0452a807001c0743c01484288c4840103c1c542d43c03141d402c201d400c01c040c1c40765542945030020039003081d504a4500c6034005582c8901040b46640a9000d50090f40c216a019180980c03c11300191202d68104104440b02c0c412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 808696843 1250 808695593 808695599
    0x90411010c0b130605010f0501020705132c06150303093001050f1f0302010507050a06050a0e0d030510030b04030504270609021206010311090a0306020901082d10 71
    0x100000b40e40c4900394800361110160240c1c01c1250803900c0503042480c1c9026000410710a50781c001030681c00700d03803046602c000707414200000d000240203a40400f00c041092180710382004801c0300c20508030304c80407408403240343d681d1040200c40030051700000c41e0540c10170041d1022600f4291800c203244680300104120354075803012081c2a00003c95840c107103e940d110b0a120341c03151101c402c160004030520021250482c11000824200b145110003414032100207684400c1100610005801715001002008589400305e0f07001d01408004143e41c403035020b4030303210144c142c6c000c1c03080321301980345403c8480c201400e44d034500e41c503a10041d1050b4144401840001024051000d2003076180100c11441d1400e900d0082c12034080c0c4031ba40e0001740046e40180000150f886002801c10f601c00d40910f07011401d1141e041140c200740c4100c80144c0d4000c0d0f20704401000344041a0010405c021023030361f45917495926503003c011004030305d00d01041d8104110b4261402440c058200d00d42007a4081070031031590743d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 808698093 1250 808696843 808696853
    0x42c151215040302070503070305060613060b160605070c080403260f040905010f15120e030424080405030f0306010311041e05120d120902060a18080c090411010c 71
    0x8207010710165440074500401040540c107019010040c1000d60040c264503085685258a1354030092003540035494545140030704580356086500201142c175112969400021500c1d071128494400c151007445c140004100b840740301d08080d020068000c0055404d0600796940d105400600f4545403000500074002800b03d02903100013003a507880307d41903159035980b800420100380d0304c0581c010035004540000c20402610a003650310b13002071807460814213000c104010040101960b0800c84d000380304c00f03c1c000c00c2900c07206503404110b42c3c00d619106500d015560041b1a1800c0072900145103402c14000309070702507100d00c05550420414100403418841040c05081d050b04a944501c480c1c03154480f0244500c00000c3c04500a13203020b072640184a051030740402d980d141c07040c1250b0304101d4401c075204c1c503022442d404403606650081c4401c1e03031882e0516000303204002400c0184039882000b0000610f014000541c4941104090b060301c07402d6449807103071541a43c044c5501414000c41e41c202c035001030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 808699343 1250 808698093 808698103
    0x190f0b03030f120105041b0f030608060c0703090b1e0a030b0402070818030d0503061c060e01020c071d0f0c0c0f1b0a1a0705030717042c1512 62
    0x241180d468152070b410b01803e0f100c1c0410040e880f41e0b00840c40c1c664a545e1a00d100d91440b5010030b5941011030304507402c1d00c41100203041e42d9111075618084c140074803143c0055a0002c0c034256009641700d9401507106c1440e0401445502000200741c0300400c03c44600c139030980e000e03120485036802c0c0018035050241c0071405a0703100038412940080700140114010420f0780c1000e0301c0c0d00040c0c008111000301d0741d00140072888007400c0c0600c100c4402c001d4200c0e4044500c407030400c541d88401c0c1401002030306a1900c1c080d401c54585564a4010180c1c045860844048149540c40c04c0710508201501c400545c034001070350251a080e24034031b040110b840c00b000c042001c2c0c6480c44841c802096801100e085010039502c41980ca0340c032421108104010f0302c00607209440c144403000c03110035650501490020300c1d61080c160020060307144880c0c41d50a80524001401c2202d50620364440d01d030741d441c840a03001d88500b030309200440402d8008181c2108030810390035011f40340500550303200d00d10084003d16007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 808700593 1250 808699343 808699357
    0x50903121f03050a060608013804093f05180414010602011a130b01050c1902010207050603012103050c070308180f1c0c050a1410020303190f0b0303 65
    0x3550108204d1001c0118610448008001401c003c000c2031001514014004504072541000150a5001c0034a460110400c0095580009004000c03100d074504c1e1094100c3c1c28051104100032841240300780010f00c1d5110080246105200c5103a02028120151025084500a40000f400790245440e080d11640b1848078000c14100c80b24000d0346c5031280003030035601c3d98500c09040780d21001c240d44d503d4030740c01300007030190341000004030700c48845100488042c0160303240c421481c4515803c52180340700c00b4407024210b500070790075a01c90b1501e41d0140200f0788001c1c07240300090b820f0400c80007505101c030700b0061002480f03450030a192035a83d002145c904013194001f030314080c40015121422002c0e903680c0c4807501c1c2d415290305160802402c0042c50044041501e40c03525000f0703c007001d04010100b036080b809071400803d02081e203920f54002c812080c52241390f6038041d414031144402200e0000042d41d11684250030791110800401440c1c10240c8803041d2800840c984039108082d169409201821003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 808701843 1250 808700593 808700603
    0xc030506090c1e060c0a1a040b070315090b030c0306240a030b1902070506010e010e1005100e041401090905100209090a0513061d01060603050903121f03 67
    0x42424107022039400c003860256000d02c00c08410030001c07012110850029503855084513000c3d242c0e01c400084d1420882c404c00010301092072004807001c11848072044030b010b2801000200302d0360352202010303400c48122003100141511070314020400325419030006e58901c0005810744021000500c042440d1103420b9507a4040d4025003183c40107078103910b0201b01c1440d0802c44903d4022031543d1110388410201511803220908070f0504d2505055141e01203a25443c4e114045641541e50b405074000180707402c2c001ca40249111401081d492031108807070109559004282840c030104030003013075400d0400c05500325041030310344252082c822444840503000781044840810a0440c0e894240d0500f903030411550388003441884001c41d1626031582c00359200c484090009007984031204038840c0043d480c040180450b08114000d400c3e40d41c0308050502045800b802400b02da515080b0940c1900e8044403806105d42c421700040c0e44407144403080e190400c00e500100c0300c004a0204070000e401546400c2540c6c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 808703093 1250 808701843 808701853
    0x705061503010b01140f030907080a0f031407050714180411010801060918091104020d0c120902060d1802120f0d0801080c0f03160609030212010b090403030f090c0305 73
    0xd5241000c0c01101d6142034240781052080d5108a06501c040c02210000d001036100480040c101c1c500401550f409020b0728030465100d2600751401e00d140a00c0000c0c2140024881c1d40c000c00c00f500f000068400f420350020103020900e040c00c240410051003454074a40c46800d6648071082c108484841d240a14092805042040074544c005821a1010303445081017040b20314041246403944008640e040c1050080450410028104280c0a40003041c50540c458400240e08621000035400b48203001000c0c0c47e26407001c4074594400e007c6130303461440650003100410040e071003c061984541c800c80758880c04660703005495000300c0c0344000301800401056106c007000ca01c441004200e41074101200740707001e030481e42c180a40c0039100c540c0b8207442e9010b0103030754040c42005da400f070101d051032132401150110010360ba0f1500400192242c4001d902420340e1510013100d405040c06100c802c03080243c84801c95868564003240201810141110116a500c950381e0014500c028a200154001c1001b44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 808704343 1250 808703093 808703131
    0x90602160b06040608030c10050c0f0a08091c050d0b150301030b150303040303090b07060f020a0903031209020906191208090907030b09011a04080609031c060501080a09030203070506 80
    0xf00312961504101166801400b150026500c0090307090041e1000010108040d240d650342213000c1d00450b00b80c0720358494045030305025240e01c407006904c2050084104c0d044070400d005903605050f000c0c0981c0002a00030414060340e0b41140d040303003841100140c4100e0708201d00c0c19140034290400c4e042116070090340414402030035989842040d14080840245150030300d156405403074001c0c82d2040c41026040490001c00b84602548241001c500072035041d9a03d2007145402412910b1600007100415241010391034080070501c42c81d1030065018215400613203501040004050b2400354142e800a40c002d000b040b0400000c110810701071142000c0340c0c031500c00808112400b40d00030034100c2094900040d05469941d20b50040e411030b071002080d01c80b030013424407045805220300e400c141c0545c4a20340a114070014000003d08010f406e04a05011002550803650b003034078074601c40e00c2c0c001880030f804500e6800c407583c40016401d119004480c60b0031443e40ea003d003000c00890705280c0302ca148105034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 808705593 1250 808704343 808704349
    0x20f0d090e0705030903070b15040e070510020f060601050f13080a03170417091332010b0d0b040902040c030605035208030a030b0f0d06090602160b06 66
    0x216030880042c0c1005403c520b820305c0c08030f59130301a070380b0302400c007108590110300010b545850443e000507025100703005480c41e40301119544c4890744520303402042e210f48003041840c408100c0c11482070760300c000b520a58035070400445054001c05007640102504002d4081c0c07200c10590004010035020000e4444030b508c0b802c0250401054540c00e08065009000f00000941540001c0c4241d0942d11406038640039442c000ca200701205d80c3c03180c001710b480c0000107201111009050104900001c01100540034050500900c00f0403e101d0450b06c2c6a0620002c01119400d03000401010b801a00003c2c82c0e071007580000d0306070b41d41c140310280030945c1e401d0140140e040920882d240480104240903212a500f42045620f03d140030b00c0003122030b100320701001c0d84050030038400006107402048070949521101265101c0e031049454801280c034003070350124182403a81c60800d010320000c5c07169481c250940c94460103480c01d02c90440c0c10315800c1000d001d1080020800309041d034014003036001c89107066018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 808706843 1250 808705593 808705619
    0xc220e0105040605090a240314100903020a110103020f03150a090b010f111207080a02061509010b030405210406080f27120d0509010b010c031e020f0d09 67
    0x81d409039080c400c0500458032009013031a0001c100040001d4585901124052a40303501848240072441181000052043c00e8406044000560064550020040ca5260226401c2081c0100543c00208040b00850450030440c210725406050152400248014a007041e600c22940c00345560102c2d007010a050401c480400c0c00382582000401c144900c500028140c82c015843d40010807041c1013104c40100d8040c4000c0c5441c1900424194903142580b50442003600042e001d0401803280c03400152068000e401013458a500280243c85640d0812410342110f61004005803500d10440300d100c44020648c041319043c1d14800c1d01120789071030401c2e42c01085600d01038207440420009070180625100054080605d400a0950140f0100c0c0001c4069040c0040b4160002e8000e0000c20074072214242c5070821842003c01400801c0703120384c20700c0191000b48070444050b0004012949443e00350114007840070011100d40112900c01d200c0300031662800c0c4441c0c040500003640d40701c00308880c10a4202d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 808708093 1250 808706843 808706849
    0x902060d1e0e03030c0f07020402070803180d08010612020919090e0606100309020a0906030813080619020a030b09090a03391514070806031b04050c220e01 68
    0x5000380c211115038150740e80409010890745150001d02e8001d82c000342c1040b542c00e29406000ae540318500d5003003000a03600200d80c0200d15801464184000070004115048200f80305d03201c10609900f0150219030a021662a80328256400c0243d60700c99035640d41d0a010a118825480c0030441c00e001c04a020341f07601e030004040580c04503045c000e00d6924a40340543d490014900081c01e29460700018668011035840541480c2c6065070220074040800001c0c0301043c0404040c2403000e544841040d9160700484040c0d0150807500701880103000107400030900c10707160385804108144c81200003121b0800984a6400c2c03a841540368004268002c420b19001304911004096005000c500080100d48030080c0c00000c86100200701c0104a042400d421070b42e61642c2080280750014040c5007540001a82c6050204551000003485e52500146500c90320407c116800714400c0310205020160401400c00102701000703010001c030298071210002240201001c4044c02c01e860192807421075201a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 808709343 1250 808708093 808708151
    0x1a251b0204021801180e0f100e0a051b070503030a05092118010e06030f09070b030c13050405060f040b0604030501020a02061b040302010903140a05010f0c0201150e190902060d 77
    0x602c1c200a442c0000c2d500315405503030548219016681c0d0108d0301c008034092382046c0f43c1e194003002841701500c45503101910421000e1140b850503011803004030f205008001000302a50300c00c10004009a055070009900980020129041c050b01c2200030007010314240c00100e20079001003030031208006160125510b003042800c0961448024101044241c8030040c2804804115540400d80c40641041650010b10340c0c8503002d51203080c004d1401c45c0c1d55010b44407200819816034008260b1303181900c81e0a010742c00080840c0700c000b4248003404043c02280c07901c15400311007403100001140c0280010142103813198080d250500d000740c0d03142d00030301c1c4c208460481490284002c0c801030760841c8940041c1d0b5000001c821400c02141ca0440c40c10b052a84024219401c0c040e0300811002160440c42480c0d810b60004c0c4500017256685260b20f0005100349450702c96008007081e80000c010300c010120320f200c400041f44491b9030f038000c20400e074420b007605100c56035200180d08800328404001d5550002031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 808710593 1250 808709343 808709387
    0xa0e010e1c23010507050d0e010605100f02010b09040c0510082701091211330405120c0a060e0609061605070203010501031a251b0204021801 62
    0x441c42007420141044000e250001d01c4520028186205400310386070000d0384003d220314030309610020700b2500100ca40d201d005050440c550354101307042c0a40c8003a96005055007450042d000022151904440c20711404e6540c0c071141d4034101c0c0c441c20485480ba6000e500850f507135901d0441030000c1801c20169074801c0000c0310b02800b42c0302c0d1078590401d807a40d03084892a0000210030280300d0040030540c000901d0b140c2d100d6580c4804e0394000d40030051402c0100140d4a0f1200d0348803244002c0c1e424840008003010741d001c03240c2d4410216000040d0024007400c08c0f14004070804460250703a6010301040c070380d242d002403449010001d0a00650440c1c0400c3d4026016500b0510788c416503801019200c030102c00030310501c10600034415000d640641d40c00400a0285594038200f003200c40c5062803415199803d0480003d17010f4603001d0000350000c0528840002d51a04101c01302e030035501040d21200151003203018400983d8581c005011400000700401c0211450180050515800100c0780507800d00c007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 808711843 1250 808710593 808710619
    0x303020705060d060513050610181802090306070908190809040c11031611060702150a0c020409060c08060103051b07051005010f18060b0306010c060b04020a0e010e 72
    0x808035414007160025285030ba00e41c00425441c2e0301070051500625040b884c03140c0350781c85c88800d41c1c11842c0200802c2d100040b4401c12100200c9402c810b954003d4648091650208080704640d882e00b03076140030301e0341c3c01801e184c1c40400280c1001020703900b01d00040d4801c4010310280c0c3c400e02c08a10310403a90051450740d0901e541d506d007801d028203101c8a20450380c906200d00703602e000722501c1540b4a20f400075a607542d28804900c040411540c00c090b20014900b80f100820382c10f0240c11294103a40041030380300070205800f40342e078841d407120401000f017214158012005880d24016042c0040c852034011400080e400001050303104000c041504140c00c0c4000d20408216040c80c1c0c055041c400340d429942d580080c20224030b015000c241c05042640f4004c00058148281e40583c8150b40d8884c01c13482d60440c200600c4803c0d50318500803000c256030100046541d640c0035045800a0364418040401ca45c030000c40050100d070004503514000c036600c002c9103401c541c0e102c1c4407058a120111805031960403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 808713093 1250 808711843 808711847
    0x1030503041a1206010315030204061205120a0804021912080715060302100e040204030b0c030702060a020708030121170322052d060a060306180b0c1b010e01020a02160303 75
    0x40013800d080e052603034030000452686d9110803108007440d0040d00620106a80e5900061412403500080c2c0d400e0090b003010001c40c130900c000b216018041c1b035440204a031555004c1248031280062a440f48000b5050009150414a007150b40d0080c060140321f40ca0300b0483c2403087c4600018050340e41100d161100a2005030350703155517541450741c513103000100661903a0104000f4030440c0c102401d8038006404204801c03050400a51042001d0703801e0720410749802500380164003880303100a0035004140014001c50302e40c9082c0001c6000c2030341401200f0703006502d41d003101441031021008201c200108200c070501041b4103030704192192070300c09815004a43c460030344490543c003060001c04840c0b4144a4003181c5000c000c07402c4000300e070540e0010b040ca442180300908480c8022a001410143e40030000e544031554543c0d0700350041c014180544c0c5070350b01003949612018000401c8802420389040c060300034403584003031090a0000595661041002a2615451002525000321000c0040c00042c0e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 808714343 1250 808713093 808713127
    0x501061704120e09090102070c050d0b01050d061103070c060c0e060f030702010b0a060306060912050a151b08180307120809030409051905150a0506071a01030503041a 73
    0x81d0700840341c0d250300c62842504540ca442c3c050b0900b44e22091010502c400c40c032040d4003c010180c80b402030240fa02e40c0e80d00903c13081c0206603801400309018240100100c0c10720350301703886049205000c0020450000e050a0b5520b80041e00c880c0002140e042809041014038424040516000c0c14410901800cad072002968521410848200d03125020012404440c000d40003451030080c020441c0d4a0316807038003802002401144141c8001590101c0001441d42d08020090313040390300f02001c0c4c41140c02036110800000800c001940146070380e0b0060070f0780d050040031080019401a07440354a1802c11041045580000428480b10b581013001030000140022402105003101414030101750303640c40b004d9038110300440c2d115000a0f0308146c104140b103104050302c401d010b007242008218507118280721b02d03525148183c2e22038108816590501052030b00e0300203000030500c10180340310f5000100c4003d0f00079100a0380101d55540c4089814002aa10051000c240f05d41100340103003000e0a10156480381 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 808715593 1250 808714343 808714351
    0x40b06100503060d031d0a0324060b0a08070c020603090d02010605060a300c032f1c09060c09080d030b090f130c2403150302150d0c080a05010617 64
    0x2100c0c003a090703513159850002880031b801070000e118031074142d82c9080c058100b0596107101030806c0d1310700210030141070700e900c92002510700e421655414101d0b104410781d01204041c01090034031000120040041e540c42d0000d62007004240d014003070701416100d0182c207461060b0841c40c4100350600031082c54540c000c04040c541d0401c03d20307544118803101520312400c0030b42c030581c03202c0781d00300b5529900f200c0c0c040e04881440702c495598400d104140648488001d0040c00c0c0b1502d40a40800c0010010f903007140e8240c00e011700c4c0320800501d9844960b00c40c022110a5a2210003081c0d6800040100c044140301e08107102d0300700e050a0000e0003402c400691003030300040480d004400d45c0c07030114603822142040600102d0740300c0030301d2000c162200181400a03036000c0713218904440c010800c00e4114401d0050000d0024403261544131682540c0c200300c41d5000b050f0468054800900000c1400d40d00d0b402115071081254070340d07007041e0400d40d07145004d4a0f8145c10090902000c1c03030f1003004100035009440d80c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 808716843 1250 808715593 808715597
    0x201110313110d0515060109050d0b04030509210627030906030705073504180e0a0b0103030c031d0108040b07051905120906010e0c0a090e040b06100503060d03 70
    0x300d5071468000303a80e9035443c0302c020741148075049464602c00c0b810101140280801d80b40e0714691a81c4404002401c241c0100c01069824110046030000c2e000c2c8000d840012802004e004407001004a420b42c440d00b000c0c5d0110300359000070140600044041402000c141c0b1903058000c0500c0a150a15076a21500c0034482c015070707001002400c5a88107200703803031b0941c0d4025a0142c2d0451141c10980d114a41d440030070022922642c80c15040248081c115411a0449050b91502c214600c03080c500034103d0a041003060b025040c00e8200040c0d2410116010f5072107a200d0401c403040a0030010324400903103114841c142c0080c650010341d6038004680d00e6100c0e5000302e000e0b80b1f907034901008552038050480548003890441e41f00e5000150040c1c00f8128136520081810f00d240e0341d00d144e4039541c600c20701c10402c000070010b020913134054130700008040c11070590070b0510072544e40f001c00040d090004c54041d01e04207001002c0c06004d1402c05a42003400d480c80c44d1040c00c500b4038200040b1488082000101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 808718093 1250 808716843 808716863
    0x6080c07030509010e060423010305190e071e08010506061602100903021302040305101b08090111120108190203060a090204111b0d020d0e01030f14070905010201110313 74
    0x20f910381c4a00210a801c00001d00325544441d030310320500c02903017552403200340000c0da82c8071f20070b0665110744070701c91040901903150080c108010320450000d004008111138580290000400d0051902800414902c6441340681229241204450850300d0107000284903510400c011042d18a0981b0100302c40ca8044602e840c480900c001c082d5846109980000c0d0000c400c070045030b00c03047c0c0769030203002243cbc02981560315607840e054001040b981d0900d0105118040c0c010900d1010748155100caa0207280b41e800016010301d0411100d4440d0400c840e0080310300e800800610440714140f0504904810001200b040e08000307600103500c5403c004c0c86120071179624580c40040d551280c00151080590b83c1c40d950342c640c00070f4a654601d46e80b8041d07003085841902d9046507030301c1c8001521458022990b07211100e8031030328030044015060310750750400070580320400f50804001c1c2d00100c40c0562800c0d04d60400e42d529050019003503410f10110046038207401c0c802c202c1c802045646080045500400c0c0203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 808719343 1250 808718093 808718107
    0xa0f0501120e16080709110c0318032b1e1d0103110d021b030301060c150605031c0f020106051f020f070b031905070215040c0512010f050106080c070305 67
    0x42c81d01d00c0e0300440b9440f01010030301c006010302c0c0c0800c454040d200300c0d11040c0403061184000380c0b03051082d041a20002d50041181e11980c8001c82c41181e00e021004042e10300c80d07035920b5800f0307046258548490b1207130f0065504040d40c26030070800e100c45825031191000e200c103091080c050300009994030006451208a02020544d81c401e50084900740c00400006485900c0c3c1052403009410031401c50f8608074000c443c010301e15400005580c100d0700180e0b034a5400d40342a550f9a00307080096a403d0903007503101c05d00400c080c1c0e000d009111242104840c03c03400c48008110080003603400c11040d0f02035901d0907005010503180c1c004044150000040c82094800308028103c0c1340c80c1c0c4084080d0701c0b0740500c02c0c02240140760340c0000d6001d0b000e902000c100d015010b1031007a04490302a1451409070b88180d0080ba4514007080300c03103500c07601810701da450665845010404408501c512490542d41d41c11030761045260764072455016018925000640b460300d84503000d03c500c509540a02408800304440d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 808720593 1250 808719343 808719371
    0x309120305060102161d100e0a020a0e0a080c13180f0503042d060819050405070314030703120b0f220219030b220b040e01050705030103020a0f050112 66
    0x15040c0010b59074070200e049036142c0c0380b503800c540200c11005046d40c0c3c001c04103500210f844040d03402c1c1d8050498002180d154100c1c104020b500400d154000c0c403084041c000c19a560740340d03c050050210802803e0940c525a04114101c0c40000c54402d03454035040080c12044031f01c5941400f9158000d021200500786810b1840c51070091340d00c1811850210360802c4041994100f80d114091400f4412040d03603a1034407030540b518082107900c075400d01005540c2c1645102541c01c8a900103000b001070b02d101988a0711241041c1c03611690b23010303003036000182d000109030388954003800014100c01c04010508800c0e0000301004007004590b0300c116012802240c0540b880001007281d500300b9142155510a44520302c0d541655840c51200030903d811042031442c00d2141040480c40c440d0000c0031511500c0a440c1001850700003096a081503a6410301a1014400d200f0300e4040c00c61600c03107903201e62640c410010080b442d9040280c4060006900304900c0e40c0152503901d4007400604041740400b041121 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808721843 1250 808720593 808720603
    0x50d050a03021c0b0a090c2a02120325050307060c090e0403020606010f0e030d0f0203040f1d091515150d09120e180a24080d0309120305060102 63
    0x954901143c501c00c0100109541d039009140c42041a9610307031041e035407030051000712096001c401000c1514000c0d5141030342e10b502c100800340e00070a00b148030340981c90340104255049421401409610003c3c6401c203802030b46201b18542c10820a05080301c0d003c0380e8a080d102d00600c14007c05143d251010000814020440345019200500d054040d03072806040083d5610019503000c0d01146042010100952049240d50007001002e13005103d801000703201210b2003d40c04000608501081c0300c04a088500142000010040c10b070b05101e80100300c400c00c00f90a1000b9140e0080c0b0742c807400038411080602c100051f4031580c0071a12060a07044103000c1000050134111141c071884000500a610b040f880c0e2000c070129000f803007124961128820191020071540a19981c02008140a070511703500c94151241c2c0a10803590118294816034188004241c6100802d011018041002d00034091704001c100c0c0e44044510381440469416158a00b040440c00e804800301511200090501c1e402001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 808723093 1250 808721843 808721857
    0x1090902032502010c12090b04260d060f0e040201080403080c0702040e010e070608010b09090405010b0301090f110a060503010b18130c02010b0904080417101409011503050d050a0302 80
    0x910032582d229007009009105500c8640c0209414080e440f400c003101d4401e0b501265844540e1110503161130710b03604103049011500c3d80b10701c00c02e4852a0800c1c10390002800d5800c07210300000c01c5550038070a0b209080d0341a81c01a0410140f40000c03c000340c0c0c1d100c10919080b80d01414084031946440354440d14038800c030080690010f050110041a41d04154060b440a084103010f0352200d1381c840c2000c54000d002882040152801408604d4807841e01d80d0141c1d401c140f1801c00060001c4100300407c0c2925040c2c07800313980584242ca0900240060f400d0560703250f1504403040201c0b40c2c200400905240010b000303160070364034089200b542940020030303007192708200104105845140548240050a00d80b0b50801c010b508240220240741007101c5200d00882c2c0c456206420b20781400c501c0600e150b1058908900340c0f01d80c1c98030300c0350b00a551040500c1c00000440ca60325910b0721082c4075082d91041c0b0030462065884040820108101140c84c00da205007078a400c0d0368030052950101e0181c01442 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 808724343 1250 808723093 808723141
    0x301060b040504240515161208180d1b0506040809040e0606090402040b210a0b06030303091c050d06090c1103031306050c0d09060e07140109090203 65
    0x14004550840d000c4040d01c21160211003d020040111030000c14008009001115090100030240680d14205e80756446410810100c18105807000c17550b20042c40c020701081c2d41040306060a00451a404000e207039015030009809214821640c50007541e036059011944208070142800d007001c0c61904009410351a00701c01204d41e94241420044800d0380f001401600c15880c2149003c1010004100c55200b1080181501c0d402d17502c0380c00784070203401100c1c0130707070fa0201c2860302500440804894404030511f00a0091074003249510b0800c1407010050007541c030036403085c03003004201c0f10005120040240c40c00c0c0e000c10b0303804c0b400c4c0042c1d80c0e034085d00c000c00f8a140d09020010461035003030760120988081c41d540302100b4149400b0550344a00c01034038800100e43e035001c501c8002c5a0030b40c20860300400702525041c40d140c001d2a01004550509a080b10166282c1c0044800540100002c0307028000343e041c0200d5640800002811145a80c0b0a0b01c20b0b054000c00000c8054101c141b00c403040c2c42c818 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 808725593 1250 808724343 808724351
    0xa090905090c1309150b0406031509110a0b0a1101020f0c010f05010509040b0f060307230102010b01021207060e010603060912090902040b0708070f0819090e0705030606030405010b0301 81
    0x10018042d15100c084070300c14002c2407082c41c0034007020745a00130034414a40111500010300a80f1508001a2032894000c40c1c2098481b00f001002a02c00c03084003000e404221400141c0d4803141c5041c7c00c00810039100b140c0f048410701e0003840091074032800c45030981c440e8107000c15105981485580640200055400354100104620840d640c0c113401c9170300642c4205100b08100d0b80c845080001e014402c0e1002760030310800c0c00c005410703904000c400e19001040201158550f0780d1300c1060b01d59590080c0341c0780c0c0e052402002202c40f907503024090031a4141c000d00103071038880800d206000850081000c041c01240e01ea01c0c080c0d42640342036100c10003540e0405800d01035580c146c2080e40020040d803003440d0010356449400078040d0498801da0302030700e10b106051494501182c60b500803c1d003113004262004030701c444036040081c03521001045c1c0306d004687c55072901c05880c00003030041c48095002e003190681003810410003583c03241c02c40b42d02c541c0864807a6180e842c1c2c2d00b03156004001748005039800d5071034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 808726843 1250 808725593 808725601
    0xf030b0414011401200717010219051c0c05250b0a05160c0f06022109060123030618100606021507030c020a02100509060f07140607140a090905 63
    0x1c1030300314400500c030a80320340c86084c40e2401558017540d000050540e168000c0c403000c0c80201d104040c6140c0c00c04600c40050f05142c2d1440704000d124504803075420104d103000888582c01c0c0e10501c00d00444504400c4104806915450050528030400d010300c03005149500d1404003080072140c20000341a0401c0c3d501e080c03440d04241c508001c01041d110424184410030007080c02602c56400010070503409281503070032800a40d501d4029401200e61801c84000004800b001d40f00c0d000400c500c100380c0e150007820300e54508420118034034070a45590301c1d520002c5071912140c2e1400a1440d4208040111420340c040340c4034080790804410350281041e43e801c2103000a6490790014100886400a124115040d1200b50040e8111008203103000050303001031034250090301c0c0c4018034059103813039800d241d490202d80c2c1000031565440041c41c00084c080114401041c003a440d180a12000c4c000402446541405171015041034034113180031900e4500000e14140c2c00340b0442d81c0c0c0c402030190860031301850030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 808728093 1250 808726843 808726859
    0x60c09180a090606050d120804080405060d09020103060504021e0711030a03050a0801050111062a0f0409050c03011a0708091c050d030c0e040203090f0604080307140306010f030b041401 81
    0x2c0851050300d1003414102d010500f0315122a5000107258440121a402148500c0594414000400503241c284043c000010b20b502c0d0390008001c0f02c02c416000241e41c1c1960701c005000c50350107800c40d034000c074070500c07650300306659000187c100e003020340c20015250000c80c07410310b0040213403015280e0580148171b030701c3c400c1540180113080c004012780c40380c090503a296801126164103c0c06d0032900c0d03900c0b50000c12a01c40b00c0515011040000e000c900030114601c0d030700d201d01d030341c800c00000e079003048005801c000c1145507210303c9230030022040c491031565250103030490300040d80c00f0049149941c0061603200f00142001103459240c2c010b0665011840000b0b00c1c00b01084007000b00f918140a2103010401c0d1600c40d00c502032400305261901c454810120040c84001d41008001c14403034401c0118404205000b004100e104a00c0f5041182e40c0b8a480c507030040880c80740306e81c0102460307020b0090158580e00f1500010f122061441d0009880200b0000100039107109002011040c0f06840041355041c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 808729343 1250 808728093 808728101
    0x31b04090c0609090c0206040b07120e070f060806030606100f05071502091f0206150109081204061b12030930030c09080616020a080a0e0f0f03060c09180a 68
    0x301384c0d29040040c0c68080748180d843d200c01300c8006002302c100c100002c1e43c550003801400c0c45ca400780f5000003080124001d400d86070489075041280c0000b5240c00400a1944c07018a4a03407294080d00074041c241041e10100c2e5454200d5896541407241400c02982c159100300140c44a241d00080242d400302c1c0c1c400b10300c400070f600424043d4060350720300348040c2c140130110200c44c9a501407075004004944c0e038994003101422016140504010303100d140016100c108000316000c0d60001d0446941ea41d10b400c0c0090611041142e0307141000c00f03080c0800e0086400c124202c0b4001c031190401142800c45458294a5100000110881c4240362040c00c81e15801d0110610322520990f1410045684041d40c181ca003142c0911038001d1fa50b10080004035030b0384902c1005240c80e04e082c0121001401580d403407140d1070700041045400514480c82c481c80500d0501c01c10480d0020556800010304d00c1c40022a441c0e200c02444076901100c0001d9460b880d84461140d0350a0411400954181d8200201a00064 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 808730593 1250 808729343 808729349
    0x92404030f0837020a0b04240203150f010f02060403030f1107120e0d02091302150d14070f120b0f060a02060f330409060501060e030615031b04090c0609 67
    0x90340303000880f8000300c4c0c0002400d40305a60890f055580342e0759180d03119000b10f203d050720210303d995000268a802050f41c000f440c080c1d500102401b080c0c03c1124248245030340400140c17030400c4032132a0420038041e004a116500542c00d4074020072000003c141c00005807540d504900e081c1d1400140e5507003409900492001400000d50310012018500c90400055550540d4041e61141c04070300887c00350420403d088000c1c0380701034040d41c5031502100e500001d61b04040b00040000792513a140c100c200b40c10b90080d56000c4c0c0d0b1801c0449001c102810001c2c2149a0b40001240709940e80c17114400c9940d4001850541d000028046070303a07041c4418001791070f080b05803500c0c1c146294445c0410510001c1c0e500000750000080754500c42400072011f0300040b8000c3d40825900540d4419562001c942d00303028190180c00591541c449118411040c54a070003002003120444a91681c101c1071195000708603d0309a145141044014495240c0024010b0039121780060100c0d010000004145400c000b0000803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 808731843 1250 808730593 808730677
    0x903160305010903140913090606051206090105010617060103050711060a0e1c0c03082d040b06012f031c050405160501090302090901021608092404030f08 68
    0x203140030410300d144050042051269210280d1001c0c45801d07c0164400328017103000d0400410200d42c1d82001c00c0082603440400b4000303402130000c106210b002400f5540c010125841c1c45140400f084903a0f522880300641500d0405d600c0b40042401c1c5803080300388200221058003601c01c981030888160005280c80b51202c1414050340e038a8194404038000700102d00c0703846484001040d80d00c1d95003154003600040c90740c0600d542e00104642104200310180e24040c42610310715105040606010400c1a0000d002c581040508035001350403ea8034a01c4e0305054002e10f2448482d00494000f150560180f203084030385a5415003500081490641c211a0246000303005a0703c1e41d6403800c0d1075811100743c1d130182c240072a4000104100505003218615840003204000609083c1d0540d00e104100d5800d0f0806d0340e08850208111955140403044000c802c1400e561202d46242c1d0740201e218980210300c40603007800d400800761001e01c00d0b080211088010044c1101d052100e03031071004031002c14102d40e070f414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 808733093 1250 808731843 808731857
    0x130c02030c0f120f03060d14010203070e0f0a0501030f0e0a0506010618080c0609060c0a0f0615140d020301020408070803041806180c02011b0518240903160305010903 73
    0x1009001c003086843c000303101070700d8892804042c0180d100d01ea030f00142441e45c01601c002c44800101d101c03019103d01407400000056680d092000000300a00030b00d030f0700c4900c1a508100c1140a5907a0b00e01110708543c0282030120f0006400302e003040003007080d07100b0001c0c0b0707000c1d01d00441c04120001c1070300f50688540d40c0310b1848040d50003241c44121415401a22400e078404000c002d1300c0c1ca020000f40140d000014082032a190500b05490309040342861708a8a9242e10f103403010400c0014051550054003180e0034078180b07032400f1030100810001c0a00d9500890f80c844980d02551400c2d01240c000d004000c0840d00d0304c2c1d07a00c581c11566039020340315840d40b42480c003940b805104110300440c001c55280d00600e5001a01000c015401008400707034500030b641d610803e180f2001d03c20703000d0f0341000741d8039142c20b40c40d940b220b913035441a0341030080050b1007203c006010440c0030044420074600c1d00720320940c1d1a01c4d82524408607183c8070b641c0e07015291104804c480003041000c15080543d103680b0941e540341d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 808734343 1250 808733093 808733113
    0xd09050a0c0902070323091201020a080a0e033c04060305150f060310030c0b0c070504090f0b04050109021302180a050609041a06040906061707140702130c02030c 71
    0xb03080340200302c0003c000500d403000c3c0d41c0d5040d4049900d0514804100e80ca075107050b45010008103005203554004506075004980f00e0906a00b00440075808649024148868a403002c0e41030f450f03206128840328a1082895508821281c00b100d440d010841070030310108410920781c13083d0151b00240b080400007802e01d4001060001001c000e01c0c940c00e0b0140c1485002c05e440d00400c0003580005010a0080d500f0110010126006003800c1d40188405910540c1d1100881c40003030400e852601300300c0c0207a0401c40e5803400208185401c3d20283d4000300300241c0c40e21145031007805004104c0e000795004182d00c5a1290101e501e5004200e410341c91280d0b20290803540043c000181e0301c030302c121a4003079030a00112141d400c09811421813158000e0403c003070600600000340441c3c0164122100c01555902c3c284038071900107540b10152070305000408480e150581004060103010b0009a4002001099100071921454103e441031858414148003d046144000b5600d400030b03002da074141c0c81361507810 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 808735593 1250 808734343 808734359
    0x6110c060d33030201030c0e0406290408070b091c060501260c06180405150405010e190c0905030a03030e1605032d030d06091b0c0b0a020d09050a0c 65
    0x40034030000b9446120b02e01c0d1442d00103400508410f501c94040c000801085a025070f1140301d24405041a00d400c450711384400c42c480050b1711a4030b25030800d5124104002c0c0705081000814800b1520380d080d401b0750718004a40841c10420f42000300820f40c80040f82c01808100180e00014180e03221202001050644505500031007018004c81000542094614080381d09112001340901c1c803100140c0d400f0a2a0080481e04484084640304c507000d40610300f60f201f40c41c1c6400355a0041446d040b2480d5141400c000882101c9101100080015a202e800e0541b4600400028009001c003c081c0c4000d40443c0c14007602a009020301e410403809003501e410030204186e4510307000da502c0507005040540d042c14090300300e9071030000790003803440d04016000a11f1030204000c140c260210b40010a11502c0d10307100701c0c1a18102d0744880c074000800604100e01030361200c2d40140f040c1d080441102280c42c1c0220b594024407480000006603414580b0031400c0c8000001c081344090f100f103c40320344540e912054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 808736843 1250 808735593 808735661
    0xb12061908060c04150e10081803161e05070e04021306060f0f0302040b0f0315150c0712021518030714090c0301062708010f050f1e0106110c060d 64
    0x18640e02c020720f8040b01080c10310403d68a03500081d058800610209d041808624580040742c144100c005802200c80410001e030720f420f0500048162001c4540d10f6039521161500e2190064408a810000028043d90741d411510300002083d5001004000d03141c02000f4440260800c485000c2060b16120b4002a8881d200700d60841c0c038030444140c144144208010704907400503001d40b004000740322004100350780d440100c220310450001e4043d607174003040d031815040c82100d030b22035460710b44014082c40240c2c0314030355080703e00304102c081c4540d43d4104a101c9407800c4048005e80350144a4240007044000240a880000ba1000c581c081201c0d52800b45032083d80c80300b4010200040e603104a0000703251066840c50010304000340d187c48020351180003090031100f41129901013a901d841c103001182590b4a0a6600440c14a003101c07098407013451090410341040c420701c0100001d240610138620402d2260500843c0010481591284500501006030101104c0300d04e0400d030b8850403281000100300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 808738093 1250 808736843 808736867
    0xb180609060c0f0a022401030317040b04031b0b09030c011d0c010e060f0a080f090f0a1e0f12201207030306030212070f0b12061908060c0415 62
    0x80306903c0c0c054265045841900701c4081d407000c0d4410015825540c0300c0302c0c0303580c2040311000810481250f245041c000c141185092002d01911014014000800c010b21203541e8016003500f00041c0e003d01040c815540c04001d0480070f000c0c0700211041c0000c0301400f000609840646900900011183c0051644072110070b64040149a014000c0f00d8425401510840d6120a00070b0465041240c418880310007640941030b40b000007504101006144084503880300e420001c1034000705028144030240716a10400164084c0c080301040200b011030002c0150407101c0c1d158060075604050300549081d0140c0220942d1031030201d491204030f400d410105130006005141c0309001404c14020000485113140d2010000350101600d803e008009078076a0298950181c12040080020510300b940815102d1075541002c1203400e400c0002c005c443d14080310540d0031450840e000004084a18442c0002c00c1c1e1590141c03200d402940c08228074250b04802a004542c4035031248800d4110034002207481c0035061b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 808739343 1250 808738093 808738111
    0x6091f03140a2310080f0a03030c03020c060601080402120a050c1201111e0f04080c0f041107020f0406030b0c0a180303050a031d03040f050f09010524070b18060906 72
    0x40c04041c0f1107020111542c1c00c80683c120400505071a001440d040503038089038218264003a02c4201d00f01a40362040c4001000f241c40d045041c0300c1354100c031540b284000b40c0860f04005c4144003080540d1b0f1042d258003041200401181c0000801d49009a1500c2e84100024420605803640051424042c01644600c40c403042c03200e071801500242c241c500c03040d041d001400203034003408001d010220b19402000a0a5808024540d05954404009070b008510f5042030107942041c10381c9511034000e100b40e07000517604442c0d084001701170720081b4004001945c40584003241007000c2c001103003911002422035290b41d58816a24a6a12902c1034901145e440020000b9904209000c0c501e41b0940c8a0752688030170507403071142440c100c49107500d1900150050314143c11402d404015514041c200300d200d450041e10008400c3d072401c00000d104000350100b0307074500100104074100c04a5503c04856840d51300003503180d040d04024506036004520a07151444920400010481d449800607041d07204d42444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 808740593 1250 808739343 808739381
    0x51f0e10030209041a010f05041b02030f220902031801023603070603020d060515121314160506070b16170405060a05070c080301030206091f03140a 65
    0x55080c40740c0c1c400020420740d84440d6041d1124a4148012001d031b0003855040380c1c0800c2e03541000c04010840e22402000582144200130300b403159500402607680240000c0c041c0e035112200d1b524040420000100c03943c401c2d5030007020118565585601550085400c003043c424149000f030a150700300d1007648013480141d501601d40c100208400300201e004420f0b416a1541180c84880c0464070304070310f0b074100801098000c200020001001d108800003010101c0717100305560074000c50201c641c816940c103101124041000600c807518030070145003110780d120303103003403c0b1291998119407600f8140c4080c24000401e003600198515102007503a11894000200c401d81e41c5034041c01c144803041445100e000c2c49446c1c4801005825030700303900391050b400b078005400d00f4501591201c045038130090240090004000700c07000401c041409886c1074990650300c1d00c3e9030300c41a01c005006254410520042440c040000c0981e4a525822076044c820155402800d59100c0f08101c5003500c0d12840070462940c2c0c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 808741843 1250 808740593 808740599
    0x601210b040818100e091014060711060705010b0f040524031f0603050c0a0f140a0b16051209060d0f0216032706050409020703020c04051f0e10 63
    0x48680203120501d16890002c141080941c003003072103042c0788074141c2c005c00e5010180b6103460814405543d41b1a0030141c81840481c1004a88038100240440d41070050b0400700e03403401041280c40305003000e80c0001340050b44403000791a040d4080c0403589020740c000c5d103818682c1c0e131860800e0300806024a407800c41403e0340590701c0c03803850b091105500105501d8458160340420700c44c082001c00e0035807120107201080890035400e029180c0704007804041e005821506081110080054440e01901d4141030001181b01e0701000103100850983c10025404c600081c3c03507841d007000d0965040ea014800e00980782088a02401c1c44954040c0c030403103a401c40740801c0100850940750740b01164070240d052006090143c0d0f80c11640440c028008202c020440e40c003410002c00c89003900c1d42c6400d80b041800001c2c45803e00b680288280243c4c030500c1407494022034404101402807201171440710700500200302d03034588000e89520740a5041c00c40e800c080c8181802045200c0020f80083c410303c502e40742280072381d203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 808743093 1250 808741843 808741853
    0x3030c050a0e0f0321070b161b1a0a05010611161415040f030c090203131419050106050a140303121e040b04020103141003030e0102100e0601210b04 65
    0x1a00140103a8103024170303000c8414001c104c0b080c10440d200503000713480d1201154a0600312504002c1e1040311544403448400240547c00b400d0000e020350055000b1400000300d14146202c10300710180c980da00505501042040852607020318100c44031956807203082c0005560107901d03401d0704011202c800121030020b1008101c5040700301c1b0110005480c002549411101c0010b41d80c20036040700302207808a031010400d0002402e21007002e0051841c00b1407440c00c08650100d40c010145500500c01c440c030032042c00e4124014003444000d0501c0310b0aa81003200603103403150013049140542881440841d1000c1161402c0c60042080c842e005402940307803842203505a4031a5800a00d0b21030440480d9072a0b020380703607000d201c070b5000358411001301406080071720015082d908071011518108050b442080801c605801ca0340d0101d91705030401c035082d10740542c0100c0c10000b035400c00300f20306030405030858001030340051a28122041810200012100222014129941d00c0300140c035404001c40410003040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 808744343 1250 808743093 808743109
    0x50409032007080f01060504050c2809030609120809030c060103140a080403050a0209010e090303150105090409030818030705070e0c04030f1514070f03092d03030c050a0e 75
    0x802100403102c00e580d8500c0302e20b14042600d1100c0903165140e070820000b41c2444c0c010a900303d0400d1b1900d80c18103c02c11030104c5a26004d503180164200ba05000601150080540d03901650b001602400307003500c141060640b6040340c10310580007400c3324000030741031100442030ba5820240302c805401d0070b0b442d60320350603544509080840014010f0a00030030000d004400108021442034010f1b2000150320700400c807032210141e0003c002c0507a59410008001000b0040725440000ba10072040041c1c8041c004890300d000f0186200c2e00245020703514010315410110340b910465075000c0c1e86c000316640b03401c002c1d203038050300d00700519aa0182c0e070140414030700100c91607407218030310200d03a0030f0640e25100c0401c0150190f90940c0c0359400c0044018911015014580101034001002c01d06820503010061410391078800e1282015551003810b401c100f40342120070445160b8243c81c42d000c2d940c031101d10a2281c900b847c22030200c1d25024460403203500410544000b510740d5204c2003c03c42c3d50f041407000d51 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 808745593 1250 808744343 808744397
    0xc021b0a15080f01060206190509120c0a05010f1104060c0f0f080a0e010903051002071a040b01452306042306010320041e05040903 58
    0x110840120100e240d07051215080905803050303440320810b04000b441c0020100044e000030003103412220422411210a108030005007000780800070b40d40d81d80241045c24684024540d01103c03400243d003661800000803680c580314000d400070400356a088103814203d9403090021441144288030402c8118025a080850513004000c0d694a40c006c640e03030f4200c02c64000100b21034078800411051006d503486003404011789404c2c00c024a440c1d003581c42c0c6039aa558003511a5030f626030009040410016803900380740b440e0601001d030710000c2c1418a04162025800d020b006492000701c000036a0000610314032100c980c1000003032260444000092200008081c00d582e5540c540b00d0141c818080013007041c891071004c03985140200c0d03081003020007007a00c40300d50710104020148044c1013400411006201c0d0800400d007000a4000340741c2c145030580142c0c15602007503084000c1030014114080c400d49403071606030300105041d443e07250820001142d4000d00050700140c1020103a0481e0a0b0b4041300b06c040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 808746843 1250 808745593 808745599
    0xd0807020a08010f091106120406020d020c2a1e011b02120a12020f06010e1b18040510150f0504080d0e100212070312090f0809130c021b 60
    0x141c2030302c0300c540c542594540c85a100c5181d60742c68514040c40071754102550224012901c0328640809600030100e4944050409440c4903030000310b01002503003941c100c0301104c101109649040b840404007103101000d01c04d211701503482d4603860880d5450070b07094948a40704c01800e181d200e0210040115000562243c03503025103600b05555102603514042d211000740c0d640401000500f11501d0200421620170b54041c003035501040b8400ea00141c0400d45074103458030811a400343e540c41e114110f039412403d40c2101c403100000207641d10703001c03294030307034105511030942c2c043c031194599a000d105009142c0c810a4070312808680058540b074414441c803000207000781340a506141d15040d4550504d18034806010206207411110b60107403c00300e0740904000e4640c00640108201013407420f9092080380001420014598440b00b51684036074000d56115400c4141c1c940c07040ea95142c584941d611034090117104c1c110410021605006034010883ca040d0560f0150030603903420340c551407401050380403e680c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 808748093 1250 808746843 808746859
    0x1c1503050f0606061e0a12021b0f060702030a14040f1e051c0210030b130b030f030c060103021306031509061a0a0515040b03041b081615111b010f08060d080702 70
    0x901c106503800644600d00040703445003270740c441c80440f08c3d1414041a00c1c60440390042d2041128142d004419580240e0290401154041800c42c4405980c03086401280c0019008080420540783d5000c0c002c4005150044ca109026103e03010881c00c080b58a011484e460020580c080040c1002da4402e80090300741e05001c01d4090713000c030000d05210b172580e040401c403603074403c040c088914042181c0e9000300c7c00b80c0051858100707181c0040d034079140c0500010340103003241003030507807125081d6004d0740041d81c010008425509800301482c010303100e040001d841c40c504240009410118031000c0c40000840200300c0c256491508040c0a0b08079019a401441d42c00c052100081502000c0005e505c541c0c8111100001c2a11100301e181281426411607035484e400360075240d4071440007003a83c0c0240d40750080ca580c900c0440001c1290031110a402110140c000c282c182070f107801e00c0c4000d44c001f12100741c03110015203185040456031513500f02e884641c055107441005c0301158130740c0000c2200c9400034201107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 808749343 1250 808748093 808748117
    0x3070512090f1f030b04020324060c010c0801060807210c0311040902073309020a17070504060b0f030a0e0a230c0d05031c1503050f0606061e0a 63
    0x141d107540c809045410300c03180c0c43d00c061190702d40c03500c00c0c5205401e04403404c45c00d41c2003030100300241000d20380b600c20001402d801000f02c1d41d0707200d10580d0030803c44070000380640ca150310745c000c0c00c4003002c0c803940c0c02180c3d11501140100d4001d00002003102907110540001807030004808000d030103440d090340181a50380c0341105813500c03400010006403290b2100540e44114501e41031a01c0003541c02e0b918200c0d80c240340c00300204c84010108030402c1c040014041048800c500015800415981c4696941030400d01080c107080c5000c0b44c1001103d1084030100516591000c490616120311092282c0620f01000003039500d280544c030654031a030a6100f10740345400b00b507686142210501840080c034220f81c0b8920004000c080010700c69040095402c081805407995a4995038010303d0400150208644a03001d0450030369808050a041301c040320120040d5a803c0c4140c6400642c41c5407859402100006111802d24208542211060000300c1010741c815074604110768000c0d448903400c21508075001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 808750593 1250 808749343 808749349
    0x2180f0f180d051b0304060215151f11010c020706120e03040e090111070c06080912030c0c0601050a0b220504230a1119020312040c03020307060203070512090f 70
    0x12618025241c40c0c40b03583e0f02050b80404e41c0c2c9210b90714120039991041000303002203980401e94031290254800e2000240d16018030100d00d0040c05400c59412202c1c10364521264224007140406030034698881100140b0304070700040c01d0718540c1d07140700050781c0051000c06c00544244800c10582d00103190000b080800d0b415941e0541e801130380017074000304082d0306002c88203030284502d045400080f040e0b02e10300a104e82d170700565801648942c00501c8404000100d4100c3c040c0542814880705d12030741c50f030701e1400ca2a642d0607608001c2c0d0070300032407103044c00204040c1001c60382407060300c004582c01400d055100c0103055241c41034161501010808801c001200c2e00c544c080d0b031300314000c503400e44080d10070b401186813051003006101a22450428401001c84c0d018082159030454059618860b9020a48401d80c07031440b4400440f40610030b584104014400040181c1c41680e2088040d680c2c0c0c00c1d590b06080340c0d68080c502c4090496080b8411502d5000000401009410390260140603001c01c01000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 808751843 1250 808750593 808750603
    0xa0324140612130506160806044704200703110a080403060c03052707080a0825110904020f03060f0a050a090309031104060f08030702180f0f18 63
    0x1510444103c1428880c0400009000d03203940f00d103035107500c00ea501200301c500904032000076000e14051551a40301d4030030190008450300340e031054052014142045480c08800301c60f14817075840039128990001400c140f802c0d008800d001c06030714031151208030340182d441c40740ba8840c000c01c80c140035030140c00640c0041c4c203226003910540500c422540342c0b4039604103502a51841403c1208041c944020400841e40742852680303001c0c042c131000d8203000045400d0302e1502c407441d00010301e00d10a0544120400090714000c1c6160540c441c0c45110800300103c801602459149008001c101540c2800c015420041c0c60203a1183c0018071107074004200e440442e0400c40f040d80e6a615180a01080000e4008031b800b174140c02109a10041107112010784006203521490b00006101010041d5110110741e901d40004000e810b2295220107555a00c103c140d030781764440f120882c052220300090001380000414020b1041144a0b0b0001c0c50390b441d1145101101070040c10b02c00a00400d03444140c1825040113 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 808753093 1250 808751843 808751851
    0x310030c06021b1008040f0201051c050115030605030a0f02030c090703090c1e05090417040807080105090601210302010e0d0509010306080f0a030809210a0324140612 73
    0x30302000243c07080c41c3c000007181880c0c070b42c1c0a107004a141248640d40107942603441030300500042000810791004030741d00d105003401900c1c20103c80c44041e8081255030720030345c100c84810019200414121005400340ca003130780710b6241d0542101010b07002061444c0e0394038032003d05c000e00366107145007000c2c00110514005c2d1210800a039032074124400308184940190060304020036100e00ca5211504020800002d90281901806a91000c981008030951400303543d042c0c80800c0603100c07502c4481d2141d580b1024801c0c49025030904022170741618010403101d06075410207500a009444400500c1c03881c02d91850120110740d03031110301c0050041d0900c201000801d650b030b1030a507500500d60004042d20141d40001d4429085071000c054065400500f40903041d03418180000035541c0c240b440b9040c010b40d441002d408400710228003e50008460061840240a0b1000c1204801c0a600010000c1000d03582c0042e11a4407036007403010a000460028a038038008284510f42030040300700c0040400155 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 808754343 1250 808753093 808753097
    0x30a03020a030b030a050d03020a020c15030f0a022701120f0f0b090108100b1f090303140c0a021e0d0807050106080f07091a10021e0304080604080310030c06 69
    0x1040500c14154107024040c3d400e00201c0081c0403900c4c141e21025210070001c28054203041c1d00080c0c84e035001e0300900014203007240003400c007008692449003804040d4002c44a105404070800e0000b0140c0ca0f8500c01d881144006c107400e4689240c00c2c600e031204d40c000030101c9a061000090805844501d036010f21011aa0044808591000018050015039514101d10340c810141d040060003256070000d0440700c5110920300200e030801020011408000804980300c140c140b9005103e00ca140c1c00110300400c0f01e202c0e9450803040700510310a140d031801171071050002d94010b90000409440d01641840b00580750340071541040e92418006482c600b4518002c441d1002c0200d44041401030a100f020700030401c0c1005405017003005078409482e0170050044e0b5900c540c0e80d814071b0404140c400880503202401a00b00c06000340703812400396488619000050200f4111080c40405850102c142d8040f21001c030300808480d111590b425001d03403c01050201c40e08640440040824801e05000340140340507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 808755593 1250 808754343 808754347
    0x605010f031404080f1c0c09150c02041521150b06120702430b0d0509030f1b060709050907050c12041e09061d04060905030a0302 57
    0xd0000c0a0032000401410300d041e1950100b101c00c00d41076a84554400552903070351103e48029460b502480300383e9000e04854042151003001d07980c2c0113041c090380c262100c121a6a8500c601c80c10710b6070051090340026032400c0c2c440b005042c150400e003aa480c8211941890325104c1502d0800300701000440c0483d02c0c5001041c005200d4080a4100f00c1e5902e44000c0c440c824103400031940c1fa200d4100800c0c82108410001420300b4401d100c40d9010801920710854040001c000d018007200241901620042c800740304983d44044070f0800354111069000d00c1c43c1004004400c03480248001020074070b0307a0004005580203c61030400601e802181942080c010365811902c0c2881d004006082d4400d11162079003d005e1665002141c951244040c54140e0b62070034858066814041da01140b280304120102c0c0100c1c81c8040b2141000000070540c1171441060703910352100003680c1c028072420460381141d041120040342c1041203658414020b2802080703080640c0d84481c40c2d54011072401d07000940c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 808756843 1250 808755593 808755599
    0xc040918170423010c1b12030c051b03100207020a0323070e04051009111509041103060a0e1f0e0106030605040209010f1b0804091a0604150e0105040801050a06 70
    0x2120320141c04107a802e16965080f2004000042d2643d003011001403c42c007240d0144000c112a003070900030141082c9200e800d00740182d860701034015140c503802100c890103902004010026244596103a1f01700040040088040200204009600c800805e07608288025004070109500c6002c0000e04040340359aa4108480b50750a40c0c20f000654000c81c0c8843c1d000024403010820000700382c1992099010002440e070034a140c91b041540045074520740103ca40e40480c07211140300d2000d81001c81094034140602c08205844d00c100c0d1004851142d80301d0b40c000c40500c00310000241055010743c415007204006081c0d111358001e00481d07540708141030186c1c06c0060050a40c1750044000911007038405505140829001801e269051080031041003031844400b1040b0502900081625401c510324651720b0b91a0701140e0068207040205c002d038515003007400fa002d0b04000007118110307880081243c2190304100021078083d9a5524002c0c100070091101042000080c41814040c00000c10000740c8140307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 808758093 1250 808756843 808756859
    0xc07050c120604060507030605090a0603031b15020a26060f01050403031e02070f0801020702042a030e03070b070804151a0f03010603060c050318060c0409181704 71
    0x92010082806104004a007481007400050019003095001c00041140ea4405e10201c00405069215950203c0d020082c080681c40a6208c0300c02d80b4040d0343e03403000e00220140030010305165820000c4c04075600950516110310582d01500520000d03141c504195500110000c820500d115920780d1214100c60501c041894031000c0d60300391550a00b0a81d04041c91a00c02a04190f6003440101103140030300344d4090380303034800e0021101030b1035404c0360380940c1a02c800d0114000d4000b0172007240560316044031100030701c0407404142603176040401e0300c4800c45200d141c100c0103000910fa080b4030398032081c0309103800200d04017050751003141141d03603000440c41c042c01c244848582c8140b1b80c8217410b10304003005c850b04010000c81c0d210210300769800844040c4140110380101460303440545910302d08100400381aa10900640c007540041c00120940c0b2480c4990356100c00c0d09482401d4442020401003000f6190340d0420a1176080b078030004035a800c015100c0d0a94400c1403100940050000102407080d58 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 808759343 1250 808758093 808758103
    0xc0a050d022a16030b0a020702030f060108030409050c091513120609031e050306010e01020a0609030216081b09040f0204050c09210a0327060801170a02010e0108100e0c0705 76
    0x4118005055400789142c0300d80d0b0404170003806a212450300090400e042d506d0802c200f20f90041500c0c101c0d00c0f03940c3d42e00719007501c0b40c106006000006040c2804206444203a2041e81c800e20350081110400d0401315540c0320896002d03441e0a03180904211340061030043c0888900f5045024030008650703004185402010b2f40c13480c201682c45102808039114800c2d03400070a50b64441400c1c2400011418010300503803030039480b004000c0c411810b00700e481c01056070100e011140700300710784c141901e82c589480800b9150602080d01d03032140d0789051403070f21440c50071144441c0c102d8002c03030170041c40c01401c0e0007003819a64100c880c8042e04400160b84d02580c1840844403002e03500c00a0810001b407441c0c035409485000500001c4d00300010030200300d03e9035403520341d803603200c00d0401100d0072002d076a00d40c00341550310700340714080344014440041401c003a4085840c42035a64169109000c09006000545131000c01900010000f070f0301917408941c40020f00391440c000d6801050b44d42d280c42051804a20f44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 808760593 1250 808759343 808759363
    0x30d050606160605070c0506040807020f0909060a0209060c0a0302060906010b071e02040b090708070215040302031b0f073002030703030c1b0e0901050a02030c0a050d022a 75
    0x9034004101c4000380c2c00790503451000166120402245549407120304982d50280814090124081c00d42440b0400c11010010b255843c400d54801e00c00750f1a000c200411040e00b03c841c1a0103420001c0014074a101590080c0700c0500c0003000141041d009404507860002c00060031400b50780981c05111080900b048031034010080400c8682c6005259540d0603040300c4040e0144c110103d4440d540411940c40d41c100018001010307080415a00d0f203003800405802040d5000000b5019130315840105c0e5509420746849160036400552501e0f076000d0100c1c03070440e04290b03010018080c1d0752520001c550140080d400616141507003804a80720f001e010040b03e00803c417090090340100da4044011385022803500c0c00c41c2d406060200c42854607003001c200c43c0264000010080c03032000c0c0f02046440d2810030300340c018800440204215994807650313034100e10050301d440c038001c101402070a15081c801c4000300f0001300c0c80c01d805400c1c031402c116401400008482c07164901d001c0900354880c811000c201c40300e08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 808761843 1250 808760593 808760599
    0x40303151503060e0105031209030c060c0604030905100e221a03102a12020a09060e0a05010e13090506132006090402071b081c020c0a0504091e05030d0506 68
    0xb15524040000355103643c20311480b12030303210210b07404827199024090a1400b200282c64299100000d44a4503240c4070101c5044010610f00305020819040404094814920a45460364650886003c215016082002103074541d59490030101d4000e449006001a2000340e5003400000c18140c2d00b01400d00310304404110700c0c02d00d84040f100100400582e194448a0580b02000102000c400103d40c0034641c017940c420402e0000444002c2240d004844000700d51b16a528004014070703020801100404174411a400103040b508a60320750310741000070841d1b920a25100044462071030b6202410120100ca1804040111403000030900402c00388103000344030080ba000f503030300899030700245c503d004400e0020300075580402c802003040149450a8014001380001c0240c0300e03520502d090361120242d2503400c8442402c0c0c0d0f41d90401d4000034921518040041000f900b0900300b6040c880103101b8100103440e8005039040904505403050070503041c03a402400550303030710621034000b070098407406000640 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 808763093 1250 808761843 808761869
    0x3010605031617071a09040c05070b0105040506060c01060e0906070c0302030d050a0609090c0609080f071505160c0501080f01050d152c01060608061804030315150306 73
    0x441c4800320740e2041c0c1030301d21000c2d42c3e10f020b20340c00500324644401c0e90082c1d054120804000e66840400d0005001c0b40401114188075401d03404c0c0044605005418000b008440070100611551034241c20840c0d00c2070380a007a1a04100545c81c3c09402c0d80e0b0340b40c0c4140c800d900307030900344030320480e040c080140e1100c841c1c1000f0b410781c149594002d5580c420001e00c566515510b001185c0144010f810802c000c0c80352130310500aa09117801e106040d03020ad440341300d000c00e04200300000d080001154441d001904076028203201d5140c0f929508080d0040c1020b8402c0040030803a0300880620740a0750300722180606000c5026505282c000741020342c003d06a07900c690001c0c80108869030312060800c8070300b54050001403810407040300c010044d1488610f01003080a0314050303c000c80308064414400280c84000070f00c580390340c4030401d031844801a140503410904c84040390400b0070280303d4039a007103440b91600068040ca458211501115990030050081240c040c0c0c4641b0640c0c980122000b070107200014079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 808764343 1250 808763093 808763113
    0x1203570a0b160909020c060603071e12060b060a1d0103271a0106030c02010f0b0120030d0501060c060e0609030412110603151c030e1c1b050301060503 66
    0x1000050040c07007069101c0c42030030218000c40c4903e103c00010030541e0003d5484a038a034482c0754580504541081c0039120302c120004420401c09008440052039100402c002818008040c41e1500046016148103850305080d49480e101d040c000c0150412a59903500419003030200701c1114050b0004840c105401e04900c00e545102c0c14a12581c112001c108070542c0002d249801c04441030000701504240c060300000288060b00764014075050304441e4000c010b4a6000c1941000b1034401410150000b0700c1966510401c0d411100101d44d02d90920040b2802c10081110910940b00d00740c212900069041e1000000c000440c041e1035101179040c4090034061606039105980c0340524440da450f46404013040d00c00707000c001c220f40c042d41c01d005090303d0380e20300d0b00110b504c00c1320070100b26140c091440c8008840c10784d0050310800c0f11007030381640c40481480700141017040c0703456070039076100d080e0407080c40e0100000c1d99200c1023a046c000702d02400f0403807403402c003c0600716080740c0e11641c020b4000308000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 808765593 1250 808764343 808764353
    0x61e0b0a05071a0a0e070905010b0f1606020c0c1503190f060306050405060403020f0d14070314222903151201090b061203570a 56
    0xd11454581840e206884a099007020f412424034079910181c1a01c01c2400d00051400c02e0f0801140f803440c4034200e902e07181c0da4000388421644244902002c0c4503050003540c0740300b41c550004001248035516094011145512400200d92104581e4102680040303100c0106081c61084118500040c41c20f04c3d0540c5403952440811361a00204981d0b06a036071080720020415961010001c2d54001004004600c1c0a24000d603580308192415405841615040380007210f0000d009036440710a0342d500d9844440d101c004c0403e54101101c1101400100201601300d010443c0107070003c000840c000403101c115000d8600054021908109a041d034014407005140d045861502400d580e038002c0c0036640d43e074905c0140344904c45444035950250b0300707110244107a10150800218180241d00c0c504168883c002003008030b207007211804215070028481d86280c44600400312504003ea20210410b275151590303c2003182442ca03d201c1c11601c0750b000d50001d207860109110392a0b03404a401814074408a450f8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 808766843 1250 808765593 808765597
    0x6050c16030b07080417071406150a0b07020a0306020d0b01030c18030b0903070f0b0f07020106060e090a200703030510050a18020f0a200a02010f27060201061e0b 71
    0x40b0100340007002002c071701000b000010f40400d20f00d0070740c0c000d0346501c46443d06d00418001181c00c01d800e0312490f00440d1072199410348424040d00010b0442c0251860140b03040c5d950340290344266801804142c0000120f11980005c041d12003007070600061200100002400b2510340c04055420030a00c00b080621018070714444001340c0360081203500455403550302007403841c4540907005042550000c0703108204030200074080e000c0d2803c4008402d10350348102040b8225405881520002030323440c03840b201c1a0400e1030120750030008280e40451300c001540c000b40030328072a000000e0606000001d017403061680c90320960f0f4101e02c00040400d04d0034a800005040400c0030300a142c120038032120481c40c0e49625904403030701815501140c03511581000805031145210481c107042941c2641d108000d03100b00428244001d59058445d001c02c00180001103507400c000708800014020030303110708403084002114000041805031300101e0b0060809054401c01c20789107030b00d4062103c03000360510081c804101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 808768093 1250 808766843 808766851
    0xe0a0c21030e06090406030501020f040e090a0f1106072406080102030c1e0c06040c14012d09030507030506071106040c050d020d020d12021c0e09090c090106050c16030b 74
    0x150b83d0361114094000a0000d00496100034441d41c03000510030700444e00c400140040760342001c0607580300d58404520704c0d01d403040050b00500000c2c04025190000300341c20400c00e80750310044e1006081c00b9459942d02c01e00d501d0b8507011121006900220810014a401003d0140044400950950400b5070300740300507000380c00e041400b082c1402c0040c1e100545c40350940d4551210542140c25905050420080d024103070700601b403520420555109007035029104111540d45818007403e200102020042213803034018400c0c0082066440b4000b02044041040034080c50054003c0d08103400d22010180907400d198503e58501d0b0040c10400c0040303a04018617104844e825034052810243e07030301c0018404103580200950005008070b615041c03141c10101058101d0031602129500b0944604600c0c0c0d40151064040c0012405002c201d580e00b440c8146540044d0840c0854800401c0040041c0130b0002c01d0300020001040401c040c4400c81007004503008003240b900c0c9011019085403990503041d58020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 808769343 1250 808768093 808768099
    0xc0d020d0e060a06063c12140103030806040509010204080f030d0513080403200607030302130501030203060f0f040e01020714010606050901080109020a120e2118090a0e0a0c21030e 79
    0x100103499910f0b40391801c00a440c424640b00408117119030805010714007c18007902c0c101c0d20b0180c0c44620203000c1280395060b260161680105560349000b040081c04c1d00070400c03041c0c0c0d5024080003614420400206000c2e5803810061900c1b8034442c1081012503000078001c5441e01c0d1958105004900030b50100c0d0141c1e50068036100c1a04690052030340d40c9204103d45c940c10110014803641850fa250b40904040300c415803844203801c1d61040110241d000984a4941c801c11940c440e007083d14280100500c00040600041a140d00220f4590b0891300300000c15184c100d443c5013204a0018280714103405400c441c10410b040940c0900000c3c405141401207413600e66000842d00582c9010301c12020701407010042c1440304182100745281c50705180850421004450901e10050740501c109490504940c01d0380c24010280c4102001070113000078006444240e9030716141c002e000d00134490180c2090140d12030600852600d00c0e45c0c007a00d80369800003120a20044132020010341d0000c586c00a02c1d40c22 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 808770593 1250 808769343 808769387
    0x3090d081809010312031407080118090231020403120c0f050d020d021207110103110d0f0209090708070e09191d070503070602070b030c0d020d0e060a0606 68
    0x41c4a00540107012240c0c07641e01c1082d6400000c00c00001041807032400b001541e00703002003601160000300242c010f40e03803d80400c0402c0f0051100100c80e41d21030200d1180c094003c0b4030285940c0201c1c582546441e41f00c2020501c10503840168640c2c0704a1188070300001504502d000d1954643d98217900c9070701560020464040015000d009241c154007101a0704101038408000107000040c1d500c03489008002c000d80a580580082c21241d801552460f540140502024044c064011002006519180300d0003410034841d594082e510303481036151f000520f02006030b1b504180f20801c0000349000340003c0070030241300c0410420640c07152b010050a0010f890910aa864103801420b99030228444800da05142c61200c0c2030a40706120b42c00e0043c1d0040742136420164071181410340320b2800740900405688807035010070440340800300469004c2001e503051030804402ca0340d4802030b40d102c42600c0e0107050b10b4150310503601c00180092500800c0302c44080121600c0d01c800540011030041c031642d0007001c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 808771843 1250 808770593 808770607
    0x40f1d010315090c09050f070e0d03080a15081e01060504020a0c15060503030c031201080a0203060c0307030f0f1a06460c03020c0306040804050f0409020913031103090d08 75
    0x1d54101c01c0041c0080d00c10a00c000d1404009107c000101142e9101c0016210b000810090070003c00300884a80c05a0383d180032507079005072540103005a104080540d072030440000594000500041c1c0208048104130f400b682c2d9000005800d4549175089640300d5803040194211458016490072034403640030703106142c10f440c5100d43d04014412980b10030b4140c00000358034451828084000c1c0945d00d40000c03040840c0e600c0c0c0d00c1c05c9660b020700d40d80c025003581c86034001c1034038084001301642e40010030386000b14184201e840c900301a2030820310072403005034850702c4490150030241c0b07100c3d40806058940754200710171141301001d00c0031607070401000e21400800b00d004884c98590b0003c1c810041c540e0300134410082501c0101820051341c400e0b0010f00404980c1c020a00d03020841c0350085801c000500d042074240010800821000360282d540140d603403c1150050710380601c1184180c0183d40280041511400d001c0c1c003504014001c2441a0810020303018159240141c1281d40c90300404c3d41034941c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 808773093 1250 808771843 808771853
    0x150e03010e010f23040b07122007060b040c020304050d0309091a0102070b090108072007141018140105040306020f0405150315010807050708040f1d01031509 69
    0xe1101d85121254202a400302c3c141c042038000149201c1c0c000c041503507050000f40714103003404d001da5006011030072a0f004503a80c03900c59038906020000485000901c00440b120085070000b01c66195031020310082190014088944620400e20340e05480a001d540070501009440c0c0c03056019291194100030800014507101d00740413070152584410800054000e000416182c20112540ca40184610302003c42c28200d507105440e041501070312110b4841d242c00d03405a80c0000814000754003840c8403100c2d485645010071500e0300070401c0b02c070030354104003410052047c8140d0b40d00ca101d05028029200508800e5100d284004036000300c90410907408241c40102d40134410795001038210740c0042001902c0441d070b100100300310f41c012a01000b500301c94280303001c414002291401c0c1440d0000694905e65401441800d07481105031a00350325003407070340d544d0446542080d00120505488034109000c280703180300c3d00142200d002d9254021940c91580d9906c11040c0c0c0c01100c00f51240c81d00009405c000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 808774343 1250 808773093 808773101
    0x60305090309030703201005040302090a020913061502070305060c09030109080d0203010e010e010e0402220f050105090105011403070e0f0d051b0603101e170609010e0304150e0301 79
    0x100003404d54054036503074149603541480c04c1c3c3c0c419003e0140c83c1d60301003551401c1450011002c0598444905107451a000c000004000078a8046041c0d003c204050302c03a83c0344a4041c0101c1d0400d0000038a071800e14401c090805003100302d0a09540c0104402d00c0403c80c00699941d0200007900c030103617104000e0000c00d015140c40c502c01440403001091010418400350040c40c140d40400098500580e60345001005060082c81a05010b901e490040f40140c2030418084502451126031015500c92803504102280e0480c0ca240b20003540d00d10043c490351a02d2120280180004d2920040000c02c00050500030b00c005851401403090b2140381c0d505035161005035103400c0800602801040c1c12500780b00d030710b6641c4448a48003125400502d0f440510382081580d0094801d15000704241d8100f40c1b60300c400d00c0e0207615105002d01d8003000002e0710b64540c5c488003c1c10248001402140c00d100325010301707440103540ca09069410602040c0500720700d48003c101003058500d448000c0f4456200801c0c010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 808775593 1250 808774343 808774357
    0x60603100e120a080106020c0405070c030302091801140103050f040209160903020a0b0a0f02010905030d1a030a0303090311061b16060c031505060c0703030e21280c0603050903 77
    0x40d0b44042002d001007500404001d04035400303a000d40c0c21100b003500801c000c03283c0c01c4a4070000f00b41c540280c4000b00c3e00c2603018088280c0b01400901d4143c1c4010082102c0c4502644400361100110b4036049040d40c1c14001c00d90018030300000382075181810b40c00900780c00c20003001809001c20180b00c2c1c048441c03140140340300545c0c02405690746562110402c510f141c0c0007140e10070104106594140c499071052040001003a04034000c2e40c10513294801d8180a45680c032102c07120b0000000708403007265014001d0440180c801e0318000f07452411840c003c2d010f030444258544080e0813031001c1014060711404c0d44c42c4c0041805070a03d0307449840000034a0fa080e140c403005040140f40100941c88543c05078042d61149000700c0985507283d5440c1d0401041b403040f0104240c0d5074005c100c0800000340101a4465400302c01404120b81c41120986000099600d202e509001d901c4a490191040640e03065007100360038418000392882d065031208581900c540c801e04041641ea10002018080c0238002d5402c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 808776843 1250 808775593 808775623
    0xd1407020f0328030e060c0703080a0320030f010e011d180102031f170c0607060e030c0102030105091006020c0f0310090b0a05070e031002130f03140c03060603100e 72
    0x43c04084030407500000343c0036408401040d03694188015514003070080d21903004128000b060340b01d003142e4902c0d405030040d181c04c0050588076840c180403044c28914142c00320051544032078483c944685680c64007801a44031060180380c210050040c4e8200795001c0c1c5000f94013a20203000c548440c03a00c40c441d5610210360408952020061001407200d084105410860700d0490b00056603c844059007143d1803880c10026560007140000c91604000024250341c0c0d00450703000072401604000c10b821684420b0030b00f03615950000040c040c030304d0701050f80368000300e001503010040c50614001075613a40214203ea4032801c04403480f640d00756000c02654090184100051150724820f191400c400c0e00240d50120205091030b0003ea1010711502180743c1c2d100008005051102d016100280298440401c10450700c042a20200e00e162511802d00005c612520717808084222400c491810040c81016841c86908600284a01c0d035a0010708a102142e001e0760005000c94085070085c60401c41d00d0100e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 808778093 1250 808776843 808776883
    0x2180d12030b0609060a18050414101208070308060f0402040602030702011e0c0f14070e0618011a0c1903032a09060f170a0e0d1407020f03 61
    0x41091680c440115940d203a10180109000c078010080140900d81038184c00100034400d04d0b1110703215140c19034030002074860070440300ea180c40101342943d0b90302801d121090300306000d009074807050190210003824020904200b14100381c2e180290307031054001c013508020315800440d000703648000b210605107500900c110342d1030340d5a15000e03480e1b070051041a808500361882c103180814003000d1585042110342d07181061022a0396808180d0a01480e0940f010140403080e55038400c002c0100d0300142c03510620400462a04c1010003083c1d540b400700007041e50b40800010003561503a880c2003501801c00150507501d43d0400c1e403299103810419190361070703015981c050020a064255121010228070410600c04e02441401810555100000e0600000e80c2110007000418403402800e81616078500d0a035807500200440c6452581050300e10000460742e4000c07420345880c3c108030302d40100d9018208a00c41e800350b032020564070302a030080a4001e010041844801c0c0e0b41c00d0041d0701e00d00e038010b02c03101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 808779343 1250 808778093 808778119
    0xe060616050606030d05030105090109091a250302190509030f1002030f010b0304030f260709150f081819080705070f080613050c0303280f120218 64
    0x903500c600550b40f260203405189003005a25202e241142e0580308040c00c00001640307001c0340d0b1401070183d4041998800c02e4040c2a03103000c40f00102d214081c0901e051b00c01003442594241c2c0f0001d410500f100340900d80f04200000e803a03400301941242d03e81c400d0400796220f04641c40400e003050030351242084240075201ea032411030141ca40c040c40c01000032203950083e523078031552981c180b44019a00980400d030251010b0184510841044a03007010701d10400034220030100c2d040b104850f040c0d07042804140020402c1c0184036803803103451041c0c4007074604410388404984000d04031500181041d6841001251141d02c038410130002e05500b03200c1c801c1507428001c82401c2006044c2c0061408940c81e02880400150954524020300c081c0c5141d50081d08103521007502c03c1c082130b102c0b88400ca480d4010a4600f00d5940c0e024009000460034540b40f45441103416803e41c3d0a916407462003809002007003000d6884554000a2181a444514070050781e40ca4085104410b0401114100d0761010713004d4500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 808780593 1250 808779343 808779353
    0x2060402221d0d05090919111801080610090509090a170a110a0c0905090a081602040516022a060a0f030e0c09060d031407060b090f0601090e060616 65
    0xb0320b9607403a0704252414240b110004a0f00ea01c070b01c0810543c02405040800c0e00c4502400c829800d041c001d400001e241a00d04801b541c0c01c1e00400600420280100340100c01c41d41c00060031980001d0443d04032103089180140a0007140082c001d1134005c1c00c1070b0002804021042080c8141981c0203180c0340550700001a48580c40c0e4444190a00000d15061a2010021001800000c0300d980107140341e0186080c00786079402000010601c40c402c2c86035049031004103507000020a0444c112442d5410007801c140148402d8610203003e4411500c89640382400540d40070a109140190381c5605200100c02e020044110800f109019036100c03070001515480340d900100525051601a1018881300725180481d0307031200780d12903c803170304074074120b00188903803800c0388000721890311900300704002180f2190201e150341c00c0705a0844006543d99581e510b41e15041206580c8036161480e18425890f007040001c140c1e542d203104041d41e00308101c002c03039400d079a01820346402d5220200200110035140c188 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 808781843 1250 808780593 808780631
    0x7060204091e05010b0d050c07020d060b2b0b060102070f060903020406081b01050d060b16020f0907021002030a0b180106110724030b0a170d0305070206040222 70
    0x180841d1509040b8a20a06442c90003840e0403a44944426810401c072150040090b060040c240c82c4423007001c11003580160348404c01e035207200e03008a00004500303410b0814000111250070a40030b0511a4400505a541181182400e00d59124800c50001c1c0c4541005030300d0450b6581040c444c0c1003c40c1703000304145501002c00300859008640c10b000382c50b51801c1458489090307003800058102000d14203800c82d4020300040809581541000030140c0c0c0d1085050360a0b0030845034100c090111619a9007907103001c0742004c000725012030303800225050840d000383d690410400401d14107500480003504e0764005511003072041c100a066003610b154240c0e10b031500001c0074002d60010603402c41000c0d44082e40000c0c07080a84500d0b42e080101c44201000c0344075600e010400d020704240d2100e0f0300440e2511614080001420300117107a01c0c2ca04070340c140c1e45080018000c2d0380400c1520323003820010312641c0003032440d03040364041d940503080390130a443c1310201c0241940e84112407400e0000000090143d020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 808783093 1250 808781843 808781861
    0x13141302031009110d02011e0c0606060203120a09050304150c0c090c12020705031b0a120c0206072004020a020723030303010e10050d0b0403030f092301020706020409 73
    0x415110700b0740d940512002103840c00307200986800d0703880d0810700300d600b021918003000390300504007415502044600500703031003a1004824001000310909a0411a05000300800741c1418000b46081038000745403503140917002040a81860307255424603003071140a208a030098058000c01c3e0304610305020024000040c10320040350300c2c5015080000c0c01c45641e114402c603501040c1c0c4c2d00300110704441d41c10006074208402c262480d01003007003a0194414000840f1884040361320217080c0d1070a45040944100001c003180e03100784550780704403100680c0d510044800c240e6020011940d10007080002544000081c00103a800910000c2e40a03d0700d900021408129000001e00207020381c0c1120300420b440018081c555050382c81400103116001d2044441d13a4885500d40c01d030007180f03507900002090040500d1040d10085c0844003880103141d498000e80c0c0d0ba0a002e84000c1c0252026660750113a8401d44200c0414091108917580052480a404507481550070000554495460f568013a0062841d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 808784343 1250 808783093 808783099
    0x30c1c0f14150d031407050322180203060306181510050a0603020c120a0c2108090d0f05091c062f030109230f0109060b0906040513141302 61
    0xa14481c1081c9403d44094103259410303500c480d05158100203044654100c24001c49090000344490030161440e2200640c0001c4d0300040ea00240d03180070f5400d1341c3c0b4070b04508215142d500404c200405910002121a005071114110007403520070b1111301c0307061249500d00b44007582201814130074040030b01d4000c0300c141c690489114024594030070f0203408a10401d05100c0254000900c00740c00c04070584003030981c500d40d038100740ca400c1340f460340d8411111301310701c0600d90f01007000b1403400707074090b4030208165024000308002c001404441d840074081c465030481680410400054054042d00c8400c0a40030a030b08020801c00101d50514003900513002404655500c1e5181041007160002d007605180b03c00ea13020f1507034624507400e100003240544901072218200385a44c0121b01c241c80076a58070039200e00b0100f1302025142d410501840306030f60080c0c0c81855007003820701003450b0a070766001c1140c7c01c0307440c200c0c0d1000541d618010000041c00e01c41002d1074514145008004402c070003d1003540b0304074421 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 808785593 1250 808784343 808784371
    0x51b0c0a050109140609030114090a060614240c1609050702011509200706020a031d03180a050301020f0304050d0912060b030c04150e0c030c1c0f14 65
    0x601c004480c4401c2e01d2140c0210741e0b01100707201c090340c00c200d8000c2620090180004c03c201404003034030704200e44181c890021941c0f000000b42c0601042e4401d074005050780b074050052050380c080c00035013000e107801c02920f80511980a904007400e40d03d000c5844445030902030310765030943d965031014885203c3c031500010710b052a002405092040c450341111303800c12000d1003071450500c0c0c13908004202040c0d0014840107010759a09810042c00050a8800e101d048007580d21130b0491801801e4a1140302c00d00e120030610380340706000900110907544884198122010058400c10000b403000341550b10035501544001401070950b06100300441c03181c2d01500403243c1d2900c9555084812440c80d12500c0c0550044004030400030785540c020400d082001001ca4a011913644c00007000c8804060f030600c900c214407041003212510354440594007915868a150540c500180103800c0c1e07204aa1043c503100100e6101c1f200b112a19622150503040c4070401002402e02118940e49000010f50b90b0038400e03484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 808786843 1250 808785593 808785599
    0xb091f090c0801151107030818100e19030b0907030c060c020f37060f050702100305070c0b0c03180c1e0d021201050f091516051b0c0a 59
    0x56004001c0a20318030b40e50b001090b07180200e8004c552522212a804114040044c013400303080810080c00030314041c605a59941040c4660343c03c100d15810034103400b9000010072614100d4009241450700c00c2c090703d032000705840c01041020120407903040204280303c184180440c00100061034000d0340d20403941403807455180c950564001003620402540140c81004400540c00d0420840303901c03140703030580592828500072080c1100780f994400c04801350803200007001040ea01c40c03440348035481c1a0410710300c0d043c800e070007003120300b10340f204108c082c135841d200802c1e0f0ba01e21802031604210307041902d200c0c8504000c082c80056910a640c8400c0c00070381c06c040a50540c01c00305081140c5403004064100f5980b965220f03000290f00c190a6540c09101d00c208080540c070b0740e00500d81800706072000002c1d036103009a0072085201d009060171140b40d020801d400900c1c10355121094202151189030711040d02508800c49030380c8606031101c0c0600c0b600381c52800c081c010014510900080c1155984d82c0e540e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 808788093 1250 808786843 808786859
    0x2d12041509210f0c08010207110f100801090b01090509070207060215070c170904060b0d0513121218060c110607090905041109040b010e0c040501080c030603010b091f 73
    0x31401c0340b90024100400d000c03400049041540c1c03e075040c07043c000c4000066039881540c0c00c9030482c540540e1803071036180350701e000c1d890409005101900202c8107500d45401c1c07094003d00d54001405091101036442d075422520780c2c0504100401810001e00d00c250528140f00020b4541015210f008054498425460503892406c01114411901303030791824600000764840e21180400d43c41008000748042000d0041512580544070107000c115054540d95000d10708040100c0f000104661100d080800e103110020340705001c544505800c03803411100d0001c05182480040200100740040400810050b00402c0966046018200701a4858031212064181282e032510400c80d8600c0001e04078002c1071200c1c070a81d901194100780a80070301d49041c10302c1c00200d451000d055070700355040f40f500c41c01003247e03003078030086190721154440e030090910380b521001900e070700b80181212000e9030000c00043d0311600d0940c009040050000c0c01c2c1600c1c1d04001301e482d10405800204401c5188a4040204081c2c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 808789343 1250 808788093 808788119
    0xa0504170a030f121b09140402030606040302010c032703061d07060c140303040b100801021303061d06040b19180f170c100e2d12041509 60
    0xa40548070b8900b4070a001c4402c03940509000006404640ea4100102e017140100111240d10001500d590803007a082c45240e0404075801980c540c0724600401c20051180c48480584049a90a00f0081d80440325803070700751031240c0d0981c103001e5110548150041104684010401124040c440403c0201080e40c000c4170f10028680d0151810391204404216113407103205c40c101402e00074185425045c050800c410b00f9030784162816900a075103e020310100061190090009180c0000218a13102d101300ca9007601007940e10014040540c0c0d4400e9500c0109030014454443c10142c0c01c0c1c0da010319140c60818004681642c42d14000020030843d03e100c00c00c1303486209080f0404212502030348078075075222180c2c002164401c032240d001012010040f6501000541070010400014000461104100c1e0301200c01d44889030700103034000c0d05a00a1903110098000c0b41c040008000c0081c0f0300c8103015285070040b02c2c10106036044001400182440c210200708030240d0881da61007500c1076452074604400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 808790593 1250 808789343 808789363
    0x9030c050103051e0901090206030a0608120c07180f090f0b0c07080717091f0e0108010b1c1b0210050117030a0819060b09100809070b1e0a050417 64
    0x60702e188540707540707030284003445540e00c500301170004209854681e003c90190380007031f20540650758540b00107100c01c26040c05440780031000c0030340b030311300380010300d5102c41d0341d241a0702c5090b03001c03994104c4200410605820002d034141a0700e005222488092074801e183c00e100c031100740c03905a40440451004240b102c102ca1200c0c0d00b2500c041c0c24840551600d034003005600541100121003040f4015241e1503414a40703205007140c030125840190603d0000c1d01051040e00054100410300c3c0050081c1002001070701c0d80d11981d450310400081d42d0741907030700c020850f8440030002d100103046003103031441d0f00041641c170300b000a00d01801544da031030307040f10f010388800c2d401880f00d6041400240e20f1503100c0d480c91584600d40840100b076601c4155003c1c41207800f1038100301c03007140f000203040c1c001e8101500c406420300e00c1032a0031441c1c0e00d8500b5900340c6841090207074401c480340000707413186a41c52004070034a0202c00c24242c2d59580a50107000741155015108021518ac3c0e854031201d00e8a00c0440c2e01203030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 808791843 1250 808790593 808790611
    0x150f090c0a080d030e1005090303010e010e551803020307030822060c031805190807081b1218040221090c01090f030210050a1b0309030c05010305 64
    0x4902186058026040d0102e0409042c45030040d00b106e1507216000f01c0e4000c84409010315038950500400900343c102c1608044115164030303041c401712000b0300c0315407411072160102100704250061581040d90040303103003200e5605200080c20f00c40d503199182c500621100044100b086000c60107020ba0030080d00b800117405600305000f40320101c2d0007800a5035004800b110f0021a984400170600408044030f030054400c90b0383c03001c0c00c0769101d0b01031081c042d850007115040048030200395586603032103007078070382a440301444200c11400300a0b0074010744405079400800c86465000341e650840d054204444419918410000007280b107285440440750000344144910758200644814031010317600a0a03800807003e141013003c5070700c1400c0d0340840d000d154420080c088002d00c11000416070300300b540122807805081f0303c042006070f9500d040b41000006a040c841e80390f0484030700c191180100da448806c4070382c00490012040540c461a55401c1d00d10070b0f00071a050540320001101120390448541c90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 808793093 1250 808791843 808791853
    0x702030609102f09010504150503100b0304021003230406090c0501170a0b0d051b0a051002070312050412030c030206010905060d240f0506030d020105130311150f090c0a08 75
    0x12500e02d103c0024007560a041c10300f03e19003a510030b40042000340b1411180d001030404414410101a800d803280c006144020702c15003141001d8000800c5403400c01e240340141581c2d0201510b40d1220030300c9038800d5400f030301d059820798075290a003e400341107503801c215180e003e41c11011446601403502000c1c00104d103c2040310f00c0e65039140c0b0100410f9010903440e4008046445000010f9041005851042074030805094206480b014442e4072281c40d04014882e0000320009003000c2d070b00203103220489400c50039100820903000030030f130b505110f660081c0c8640304103810082c00b8150880d5071b03000303140d110303a003120301e181c0c0c2e140c5041c02202e1044c1d07559648203d0924500c40458541c43c181003161030500b0034101500500382420045070f606801d84000740340c442d003c00810f031805000321003180da141d0000b840329207020786010652601d41e250050501180204a14000408000c0b01c02c50090019080c1007030300b001c011302c0180b0281150040b080344240f2a03800d041c0d091400b4802c0882c1d0300a00104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 808794343 1250 808793093 808793171
    0xf050f0906030709111815190e0402041e0b1e070c080a03110d0915120f0615020f060714030a1104180b010f051b0331060c0213020c0102070203060910 66
    0x481070230320000d809041011048260710a9910380c40144003c10401c01d4441159070200b043d80600c100c2940518034070f080070b00c070851000301c260f200743d60802d03411080c4503540c401c00d182242040394982c22009640c4103908031b041c20180c11081508100b006101120600c400c1180129221010350160b10242c041c2c200b0744c124071501502c0310982c032480b070f03240224510b00360a0360041260115031111a01c46041c17420250a5901440203641000150020300094584880c01402c0003040c01d1440401000000c002840a19a41d02031801003884d401450381d51766465840381c02002e4401170b11110030b07252002140281d80140c1c04500c11001d9605c2d09400c1490340e006400d4811240074000009010401ca0007080078014041c0300208014141c101496007880c1e00710510001280d0000001e00801199920240c0d9403401c441c0c1c601004650096992010740002501a000d503010082d0075108d4070040c85022000403500741e8007442030f582c0c03c000f202c0d040d007124456603420002c00c0841c0741c0941902c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 808795593 1250 808794343 808794367
    0x70201050c01021c060515071109040f0503040815010b090a030209060d061103040b090304080c0d08250b0604290a0e0108060708010f050f0906030709111815 69
    0x5041000d070040c00040c1043e02800d0640c03e0120420031030a0400d035145420f100e5894824003e101403030004241e6420f0040550f01d074602c60481008442c401d05080000904000051503130090356640541030740e40b2240d071a40e05c00c0e598002c0080303080710320f00d0020021481d5440d500990b107100f41c004240200861031031702801003880700948210b030414030103840000480c3c4d090050130f2100b840c003240750f66289400c1c181101306860161100303041d600204000c0002e000c00103030301c1c40400c1b012140701000c3c1845140070b00081c424082100741c0e01629a49401000c1102154140303070a001c2c24080c6441c2e03840034200000c80b0040000801607080c409a5082c0c51b0414031301ca03e81110010740500585925034103c0303007d054090703111203038039131000c1c0070803400ca98403000307a600404466824100d1107051600254101750361022440c000c1070712000051159800f001108018036501b6410414001c01002d40382d01540305420002e03003448402c0140140341007905400d00030505070b0f1442420002c6403c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 808796843 1250 808795593 808795597
    0x6050f190302160c260703031809050901020307020d050a020a030c0501090b04050d02152502210d05011e030813050915030c180114030703050d030b0108010e090307020105 75
    0x511010160300340503400305460a07100303d56506006080f8003094501c0c1010036008040305400303008450b000d45100030101800040e11401383d0758181082c481100045442e000b100f10749130300032840d450410041c008203100640c0154060391460382641c501c60b59600003903c03503109451041005910030300c0000c000c01d20440c0a10328441c4204c0c000f0503150921b860309002d00c801901d003554550040c40d2110716054041207101c9102044451016051130000e03c030040a081c1c0b030304140500040003050715001407003071012120000c850601c3c03840e80c2c50007030303904030654020014040b0810b19040000c00e500040038692146241e414500c6a84141540c0e540c03441c58000800c0c000c5100d10401c804030303880c0d540c3e800180c8038440300341508c404c0c01181000c0614058030894498082c510301d4070790039514001400e41070705449421108511141d45100403c1ca0324240e5840600b2a00900018195450781a001209500402d0382ca1911a0342c8502c007800c0040c0003550505c0080d8400c020f220015400303000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 808798093 1250 808796843 808796887
    0x903080c0c030c120a09170a02100507021203270f0402130b0f030f24091503030c031e04080a1104060b13060f03150909172206050f 58
    0x16242481d00000f40e10385080d050200c004201d1801090702000580d00034207240080076004c10081d81c124084410701d48840300312902901400301140b0190302d1038001c3c02201e82c819400f0740002d280e1080b08004680701c0c1c114070070712110042070340c414020403206c40b9003500f90524001c00913a503512009003044000d41c030858000190480300080003c0002600010f05001c7e951895400d560380ba003640c9542160400601c800000c240782039007000b450444444000c1d522a00703490b842c0ca075480300c02c03540f03128101c1c80e40030540c144070000300300c401c422010000d0505100500301240513825114821801801140a0f04417242d11003103042c000700b141902924a1800050070004495449800342c80d080c5e4007014007118003000c2a102080a42d80c0605042c1149001e45800c200c40b041341001100c6900d0340d8420820180d4a41d00b1a01c10b00c1801c0f00c041d00450302c4444055960f0a80c401141c440607028001c21000031030a80000a406018004842e042000d07510740b80d00d001e04000c41c00010000d03200d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 808799343 1250 808798093 808798117
    0x70f020c21060703090507060816121107110a05030a05101109090c07021201021c0f02090409050a0b010b041503180210091e080604140a0c03030917010903080c 70
    0x1410800040401d0150300c1c0103902960f408500c406950910507d040c0d0543c0c082010040e10304208810100a003601900e805d66a1404510021101701050050603000320000300c0000c001905108100303040070b109101500544407074040c40da4501c100350712050501d102501076044027800e210712151a41c48643d20f61061440d03c0d00300140c2c0008221007020440303111800c07041c005070f883d041d031074030f00b10b450007580c00380001354070703050200700395103198140b0a61040105807942c6148501440c0c54041d1411820007a101700000203c80c141180da409000c1c1003581c484644d0310022842c5900c0b0300c02c50f0305540702030301701c2e6031600e0514030201d00404203d074402076020900c001000040c0e80d0300300c256003403224681d18403410500700590001c6254500703450240c18044804100060702c00072030410740c800c1d000f50b0700c0389051042c410564244814020024280321441c40040101030b00303c408131055500107883c1107140812081c4241c22201013800141c0030482000003d681415a18002c085403d845 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 808800593 1250 808799343 808799389
    0x5030d1b0501091a04020102011b0f0c031202130e090607050702130e1c0f0207140405040305070f060207151e1e050408040503010e150109020d0e150f070f020c 70
    0x5859013450500078009500d0001045018030003035603070900030015070050b40e101c4040c1113289000b000c1e0100c04840a140c06124201a01070181401341071940c2100480b00c1701075549400d40380e04c01c03c459107640903030701c1112083c03004112031085c0042c000340300e031000d5141d1368900342a58003044882d00c0b80c880c244805541b161021a003000090000c45806a225080000d41000140014200b403020f04100802c40d44400c6040005a08401a83c1d030611000c0d140020580c039541003c5546100300d0402405001d0b4440d0b40204000c441e03030042021038020b40e0b8610584461b605810b058038444504201008484083c0c00c080000c20362244626603041030004894480e6841100d080d0f800c112001e071460300c070205081107282020700510700350302000c0028000c8102106106949030300107010303082c100c0341d002c120b00941d000190b01c2100a00f403154200c50440320045400450a00c0481e01141000140b02c08035071003a001350035045032510540c02409119241c00b050011203100300b904e0031242060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 808801843 1250 808800593 808800611
    0x2a090519020a020607030501060f23040b0a021b090408090f030c0d0501050603070b0a020d050306031608060712050114061c0203040b0f060102060c090d03030f1a010905030d1b0501 79
    0x81c0300404458080d50060000c0e80381084000d401c4800c140e1114042c84154644a2800c40d44034210003040442c02c4071130449140100d004007007602803900070b42506c3d280002c1103500d40b034000440645200801e807106c3c003100d031000c081c01103c003800d4400034466402801aa4418035040c40e600118000190071900030783d040100241ca0013506075025200ca954a80c203000040c00c01b880203502070b00c0001c02071440c0c5241c0c00c00080d50f07992030110f600200103021010841c560340910105c0f42c00040030340342d806081c2c0c03210b0120f0b8a8007001c0d13a004001c204108402000456940103440c12503182d12056031540300010700380f0040b58810a0b06160107040003031550340d0107a00e48051802a40035072844807040c03074040070040c089000a4622810342d0300c0350080118008242040300c4281703206070344810014415103000c0d0050610034407000307600e90400c90400c190b202881603062041e142641d9410210f61f642c000d040e00c85031279003000c2c0300051040e00082e462032400004000740900c100000614810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 808803093 1250 808801843 808801891
    0x10212040f14030f0606010c050c0d061a010815010c030509040614030d021c1d030706030c02071a0301030303110c1504060c02011a1c140105042a0905 66
    0x441508000d5241e4441c500500280c02041c08801d2801010f9006018080994400380c1d51510b0041106040150202c1d0704004c100c0c1c00c0c01f80c000000c10240003801c000a0900d03040c00036141081c508098400c080403164030962050102d1800b07000700150ba880c04104c254011520b000c40c42c042034080c040c1c10030003c851a2142c0c86180c009261194000f12031547ca0007c260038400b00d0903c1100315481130007800c94014030709481e83c0090015040a0b031030300304031203015a0b00985040c44242d05010b10480010a0390b0103030442960302981354213844031141c450b08004002069865203811690043c0300503c0007900990082c4d40590648040c00d0600711060300312807801794220150310b144810f00082c0000c210301ea00a0001c40d2403c2e000038812104144c4a82100c0150100014814161440040043e01001808512458221a581d4681c030b41100384a400b03080e00360340803110102440315601d181041610101405500181e0f8210f4051801100070041c00300546003070340850000310a809045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 808804343 1250 808803093 808803097
    0x9091d06100302040606090e06041e020c07050a06050c060f07031e0207021329210f0f06040507060e0a09020c0607080f15130902040905100c020d09030809010212 71
    0x4089100d4628518114814131090350000c0e4000f00a100d0080003d00c0030b2941211003503401035003610300041401075643c80b400215903d0f025410090f01c0010040805d07800401d000e0b0582e5402d48a10303040d00e130340701402c0f625172141c000b001225801520100710040d0746410078a401c080c0d280f0340841d01e200e00000c490030320105020f5104c0800c1d0300040d0801141811703840d9020710329101500b0040c8c0361800ca40180540f424560303c01d0203d010020031495070f40c550400600d6240700000003460040c08140c02541c070006203c02001903c14104260b043d03003000a04148220380c09000b0f468500d14011313043d10204100f084460b840354100b580842da0307409501c0640010001c40006000d20b003041d83d00035103121005014100e03241d400c9410820b080d98095203604010500f41c0342504215a007000000081c080c00360002d51003801c1541d41ca0501c0300c0050454214004c259040000d07005e0340700107903611a00942c0340004505010000c1000c036900c0c4000c0d202020041c01598240c1c210416200525 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 808805593 1250 808804343 808804351
    0x20907050403060b010c030e011803140a021203211012061b020f03090f0a0305150405060c090d030507021201060602030c070603050c030402210604080a0e010e0109091d06 75
    0x944007080410030b2114a0080540540080c00c12403441482c584005101c841c902e0b1b1524144840382103045080c8042018180c001c41d08030503480441a154280680c80c0c1c642440242d1290758201c000354104000401121a0200e619400214070882d000da20703c649400142601c2c0404014840002d01c20480140c00081038416100002c03003112041400c4050440e903401c00c003c40d485440c42c580400400000c507404444101c07095500d1000103400606403c0e0f41d500005d042d40100c200303440418029125490013203100d0702c1650101d645000001016003c2c008010b50304c15640c0300700c50007080c040d200500d038a50014107403000001c00008242e0a40d081d0307601020060b8400035100f1440d20003440f900d0b02070070300d9250610490400c40c0d80703040a40800340001e07102d850701168403842d0100c4401e190429401c0310058a40a180604210800380c102400080119149020045049d03103d030b0f40759441004144c66140c4690308080381980102580d001101e00500c01014040c032940c8100100c0b486 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 808806843 1250 808805593 808805597
    0x1020703050d030f11090d06050a09150605010206060607080301260a0f030809010e0c090a15030c0608010f44030301030203121e0d0b1c050708060c1204050703020907 73
    0x64000300b00c0480100c2e1008032621704c80311424051000c3c0c0341d6500d4030301110543c05c000041503a0b203980350b14400600110038000c0010001c420320311490300980d0003075070450788242c081d00c1c029036402d0144a020301c50b441c0700920030b1800b0001880b0681284409550038900855440003151408200c0361401149a40034ac4000b0060001c2c01d08056000d60007540c04280d00c8024820700d07401c07070304881c1d90700700d00355442d881a860000092140581d03580700b03105408201142004880c0e0300c0c10080c02c11460f030300074a0300144004c400414840d800041c0001124020007207602900d140b0f41e4640c1c1c1405143d4110328000f0b20801c0c0c4980c0740c1664002281c0c6c0c2d8003034200910782c0d0703501d54810940340c03180f0ba0203941901c08013802403811007065102c0750310284004603103072a5a440107420220003488180c10095204484900c07a0014100d102404c4a08a216400301c0d44040d440c2d214455651604584120404504100300c00203070000c070f01560b410038852030498170320341c0c1c490740042c0c62051b044502d040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 808808093 1250 808806843 808806851
    0x210204021c050108010b031b0613060504090c030204060909150504020f090117070e10090f091a0102011103131a010923010308070210110f011d010b0f0f01020703050d03 74
    0x7803107960610400f40102184802000746000c0310020985486215044032000081581d040340c1a441e00e04c2206e046000807107a050341d607500d6020140441d00319000b4a103109203000c4c0260307e40c5000c0d100319001d0707407020388030307080c180d4a030a82c010007174182d144d030724446038013032007000109a291800540860410070340c42d1030316681c010000606030000409005c804003403030414018441e4011269158415095610005000d02c8260503143c40d210356001c444c20001101d80003030754003000d9011844400c100e1488421004a41004a00307a030405080e200b0703000c1c0e0800110300d51004084440610a22400390410301e92030050034031841c0c1900364001c000c2d0603100c84845020300c0d600d00c0c0b00303e915075030511205210750458072005158000c609000b030080c1044035060900c14059548990f450340d240080340e030420003500c0f0950191840c02c0a00c055802d51804075004000306000700d09440d0800380c52010002c0f062400c001e126003800031001c0c15400741c2c3c24003201160041c0181a021921520042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 808809343 1250 808808093 808808137
    0x20903010b04110f0307200d0f11120903190f0b250e010525020102210d090311060a0b0310020a1b03090f0608010e0f090721020402 58
    0x142035400800c01a80700e646480d50081030342940304141d40440c0e08410304c1d95101c0d5600701007a0b0f911140000e406001142080c03030020344490028125004007007030f40d0340c408440b00740369003600d42030344000141d01550071a2190405074969000034110380000202241c80650994440a00714900342c0b20561703440070a81280300501034550a2103400644480d142c800d5114064020f041c0342d503c4c03581c003004101c04501c5850301ca03072007074003601c68400c2128040c0060b0740b44481a40c0050b024030104a016004080c0702948600700003c64071481d5195440646c80d000c20800700c07400a0082d8241101030190480105500d600d00300a058422540403600184c0682e4440405141c401e180c000c3c0707040a80104039100700340b6404004e2520900600300d11095002e007610b01a10084501e401c20329034135201d8600010090f500004160480b48440d251000c181c54507940c000d40000300311038004c007960041c0300410104580004020707001c00e2007209110007500650014040c1cae130021b0801d00050100302048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 808810593 1250 808809343 808809349
    0x4020f12061503120304030810170f280f020303071209060e04050606041e0506030703090b0f01030f23100f140601080c0f09040504030917030a0504141c05010209 71
    0x31010050b0b040700100051a59580ca035000342c840100700070100001e400120f0010704c0b00000c400003030062881c9000d01e184a00440c55034a520142e1007407541c0c4100c1c41072004480c00d0381c1585207481c00c40070740c81038800030f030361907207140c1e81c0e104e85049030181300070403001d800b1489041c00000102040d9440081151900600429551048009030310540c03070102401059a1b811040b1001c03180001a24a80e40182c0400507142c0b0380d1076400150003841c0001044441d40d41030380003290f03081c131851071140075450f1443c81c40004a0240001005109140c0110001c6070f500d1a0b4601d0068003440a5080305962a1001c0d043c508010302180e01e041e00e900403280008000e0041c0a12415400c10303944003464400d0000704030b1400900300c2c8020080001d035800f00c00000d40c040307540d6140f01800034000d80c01d1601d402452112140700b8102d106000c0700d1440e00307540b004001c0760200941c030307aa223a04050070500414942c007101d40ea101d6000c6200030b28610320300c6900d410338003450f020308d00041e00d4440000074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 808811843 1250 808810593 808810621
    0x3060c120c0215091509010c1d0306062806081b090a150c0204050c03010f0e0c0f090a120b040311010605130b190e04030e04140f04020f1206 62
    0x103190300500706020480401d500240c0c414920000200182c140c0c1c8a84071007600f8056100d8002010b480c00104000540e441508404d001c04016a100201c102580c881d00c543c21820300300d00c40c0e0603003102d008100e103407902d00400c01c1c20b290a80000c541072034440d42c4000100501c1d82c820404118200f0401c9041140c50b6003a0b40c0140d907040c074051820322803000080034900c01d070140380d60800414981c88002441003200300111540500204240c2c106400340f901c0c00d400034460001e20802c0c0c2100400c0d0001b803141e04a00800181c0009030804524151285098000c41e081c1c1e9007002c038105000076600c400c040400342940c0604000106800d1a04005102090001801c402a030514000300320307a88510a4001019810060025204803070000090b4200341c49056008419103008011481807080c9907000d00880c400c1d00d90341c02c0007070114203120941c2c01081d681204074500b400060088508000740641c4240700072f112010b60581c43d4000341c207203140c5107828041c55014808101e42c0c845c0c0407030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 808812949 1106 808811843 808811867
    0x80720030c01020706110a080a110d0507050306190501020a0206070c090c120f06030c090c2003040e1008060412030e010c030b101107090e0a060603060c 67
    0x2020390213500024801c2d10080e14201c0e0300c4501448580031640e81c80e489464154480e5140c40d102401840108401c154685080206481c138091903c1054845c200640710151641482c0003408400c10502c946d1802c01d8180d07000070700c6103030380000e241e0790210360442d00035a80e261240b9010155101c1e95100d481700070f040096101c0502e401c200011f810501c0d4900070809031005031040070a1b685903200c050070329424031105220582558201c9205007141c1c3c180040381c40d416080340d04400c00030f181081c80540001c281440300c01c0110b0107090300202d021042240290a00442c2500c40310054802007050440d0f241620095000f90880214001104020004451000700c00350103441e100c614107100b99056240349500c1402040c05004129203000285865800e11880d14000d10311f030765201c5100d10414085100140c050300440001e503206c0c0e4008220742c4500d04002d0100e40a1174 = true := by decide +kernel

theorem cover : BRFrame.Cov 808633093 808812949 := by
  have h0 := BRFrame.cov_init 808633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 808633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 808633093 ≤ n) (h2 : n < 808812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
