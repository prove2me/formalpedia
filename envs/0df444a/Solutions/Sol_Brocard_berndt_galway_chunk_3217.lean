-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3217
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:00:51.208344+00:00
-- url     : https://prove2.me/submissions/b67441c7-d0a3-4930-a3cf-ee797b128a31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 578417266 ≤ n < 578597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 578418516 1250 578417266 578417303
    0x70306050c0418020c0f0307060e011802060306010e03010b12010e0c01020105010b220306050a0e15070203250501110a180302010503060f01180b091f0f050a050d0f09 73
    0x201c40445080d0714841e042c65280f0241d0500030f41c0700c801d07032034405c0c42496907a40b00b40c9014009172003158000c038000501119a006214251080c00c440f0084004181e60702d580140ea5110a0340c4c0c00002c01c0c6044060441c04c40042030040c200c0c1c0c0020380e03101c28410440d0a40010540007a0840314850059030b0000c00890016402c2e50307401c0c02940d05205c420b0044003117030070602064403109154940000021070756a110141214816552034034150340350610010b100c10200200d04060340090105402450101e600945030300607441e5403000245910320a804a5034254a003901050300000204001c1406100c10b113400e5100b0100d001c082842001c50300c00b4940500d02d860126601030f15264556603503001007203025040014664140108920000355600e40315240101a292161071030f0740d0780800908003c100c42070707408038140740251074400b140c4a6074041710301004543c01d4189251100c2074030600b6039540c00343c00200c00c80c061500d102c3c00c01c03601d816040440c0246c001c07600701068410910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 578419766 1250 578418516 578418541
    0xb07050f06011202120129040506030706050d09060219050703090608090a0303180c0b0319060506120910090b18010905070e0c0d11040509100f031b051207030605 71
    0xb25000308080c45010b51400345c10042008000c000350780c3d0000a94000c0221541561041c0c00c01803842c91800c0d88006d451030a040c03051070f400c000c0441c0200803640c0f80080080483c4504c0010040440e2221442e404100c0301c0d4040d2401c11040d07040208180c0040040103081d50007682c025000252025000141a40100c44240c0071380080409050b4010701d90f1000d0b0007038403807058400200c0b11540b00410104003020114409042c002c410241e50313003040651080c00b06070310911800c42619003842040659504400c658501e844105650140ea6035403c03c1070500d01c00c1541c8100b0541030001d060200168072964508c100369040c50a507485020505603400c9845c40b030402056944030300c4041c0304803c1c0040d4540e50000c2c0d548030140c9001481c1030840140d90fa1143c0a140350880031130300380490710380800f40c1940203079800c003020100c43c640f41030759030600114400038210010503664070740540b0036214550050040500748011003541c4808807641d03000c05203c103490441c680030108a007480c085 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 578421016 1250 578419766 578419769
    0x11030f01120503030c2b0504030305091603110a1a0408070923060609040609141605040b0901030204030b04030f030f020a091a070501061203090b03040804170114010b07050f0601 78
    0x42c000e6046075900d5030303104242d03400000c54007900c0d1203001407214078040440400c42c14401e04c96001c00c80f414945000f03020344801030010019034002c0c10541d05047d13235901000701100c2d0071000d801519000540881c50b501801d4020003041c0e43c40c01e020752102e07000340c0018400c4030070300c0d82100d800507507481d1002e00322105088102c080d0046c1c4110b450070802c04401c0c0703d4000700028800780c0340c44440f10000e030071a00c0680c0100c030010344501120725681e0110b10f03425804010140381e10141a00c00740c00803c0f911441c02001c520300808112010b00e40d10a50654000d564002509081410503040c09132030b1f88002c0540034002410102140e190320514001e8035000c011a0f182e01c24614107041c0440c404034200800641d02810500400c0c02084007401200001c107000c1c05040200d1446003001003084441e070b0040c258401082083c0000504508120350031100905a0362034003c2940340350901400781c004d1840d03500f928000010031080c41040080403200d106074201e0341d075004950283c98442009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 578422266 1250 578421016 578421023
    0x5011e051014070c090c030e1e0307030f09030602131509030809010509010c0501140f0c0408060a050c0c0a080a090518060402300103021e030a110307030611030f0112 73
    0x80642c410503400c0594041c1c50142d04c03030701c205008203031142c1290702129100d1055400203521001140680c84080c00000113502c05407210031040c001c40400c8070341c0c0c3d106d54040101040002e071940c2c500740c0c3c0310703101e198041c2d580300c1002c0d0750342d01240200200107811070182034001c002d5214032010481c0582c01100459501c0000c42d400e0011002c01500c031038000403112070611440c09507800006600b88100a40d034072a100301da000b5410641d2800c00e500c400180500c0d8424010030041c403208000007081c96110107040f4001c00e803981c0e45007000e6624004d00551000703500c112000d580400001c02c001c4c046805580c0d88801c1103950b5002004078505d500641000015000c4010900754103007a0005c0010a03e070018140207070102282c0629072079021200c01c90312180040043c41180340c440c074921001502aa00120002481030009031600034448000b0300c04200f061418001c1d40382400501d00654000340d0401c2840000e00c4800e280b90700071a04501c020780c50100100e041c100d081c4803450380681 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 578423516 1250 578422266 578422277
    0xb010906080703180c03030306050303160b04020f03060a0e011b080c091c0b01050315010e06010c210c060f02040b07030e191d06150d0f0204080105011e0510 69
    0x141150980740c80d80c0c081c24060405403640c10440c801c2c0100015004940e20401035000e10514601f00102140c400f5001140b20b42c00c2084121041a106082510081d821222041e016180c038400140f00c000740803000740e014002c001c1001160045648441124074143d002801550310340c0c44150715094050518201182c11400803405040c11070010b406982030142032441c192405140e507445006100d10121520041c21005109c0742c2030900c030010351400c14000782d01d299410600e110380d070158010443c0c1c0c10846050324910500400d04149041007203200003151050700e4044004111451040d401d4544500348403000454040354402c40e801c80c1c460002180c2003000782c0c0d908031006000032004541c042101000b0740c0c100140d000011009001c1c148000e071101e0064600c8403074881d801481144500801e0351112100450b18003186c801090700c400000e500e02400603548003d00860f0041c034015031074403001041c200d0010035420038103404c48180c050115511400c0204090107021041c0010f903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 578424766 1250 578423516 578423519
    0x16141e030a081005040204030c0614040b0a03020a1403091b030a0b0f04030320120901050408030c0c03130f1a041214030c1b0a05030a0519051504080d0608010b0109 72
    0x240310302d9045402440e54000740c41d010ba52480010180d0f0825002501d0901a11381c08200075508030314500f40c0c102d1b0713282030242045c0c0744c80100031031401801c3d000340c24141c00081158a082c032030b5128203182488a0f0100340c603400c011529950321960b003034549200c0819414502000e248c001211200ad59022420a4507a6100c0c030000280c540044e104809041c0c4a0a40640c13002c8001c0c0c468240c4264085095200c030501a07184604080143c4103102d140d2428052201081a01c8100c1c2d80c00101e001c070195443c00d540700040c0c9907214601ca44035a0001001c008100f00880844800c11185006400302400040d02490f20040c8124400ca0414408502000001400ca51008014001d011044d07a042c401408403c50174012100e0360b01e88091070419401c0d441c0e203000045000a8038040e8001c00300b0144541d035180d5161140328041c0f03142e04012100900f004000c01c03d03e01c3d481e2070902006003505003413a01810340d420040d641d500c400d05000700810750100510542070728400507074aa10404c0e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 578426016 1250 578424766 578424787
    0xa03030b01090806090d0f030b0f010315030803011211011d090a09060e010b010306090b0a1806030c031101020607480c03020a0e010e011502010216141e03 68
    0x280510500380d414418040c41c0003840d0b071402c2c81341900c00c0c8850340182442d5000d500005200403d0808040e05041c5004a520304c0c640340d0301605059203800782070005a4511020600260200350341c0000c040391400000428060351581d4030315002031042d418480801c00038001520307010054404616240d1610020100a02d480d20720190443d98034540010000000c1c3c94907400d9034142d111000a0341c0d166525161103590510400b001803540941c01c20007101b00900040c0034022038030620604201c034200380d1813044100e5100100950707000b100c0c10280b1759245031480040541d004118094000d450010302e0a40c0205507400118802400300c802e000400c40e0680400380c102084040400166001d5100c0c2149401c0303d0080ba0340200082c0418030300d107204112052080d50848001422450010030202c84c1030355007207040d0b45914100b041c0820040c0380803802030040402c201c500070f10841c801002d106c0b0798514200041822025600360040c500301000700800300c5451011203078000c10181103171 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 578427266 1250 578426016 578426021
    0x50c0a0809040209090a0905150114010503040203030415080f01050901060c0305070521040806160f1d0307030606050306090616032301060302210919080d0519060b0c0a0303 76
    0x5001c0000d1005040c4444c00010403000d00044510b801282d170341e4012003003417003000c002c030b035403010303209000d028044d81800d054101d520005c10101d41888400320201c0d0031554240155009003180300c041d21b41c50b0400310300003010013205980c89200107298000125140c2000d1011605075000317900c0320400e007103442c3e4007210180c1c40108192030502541c2c500c205a9403a001c9031820000c0703505440c684403401d0100c040c1c1130980142070003003032090060000d1040c41e00080011003418950402c8440703000403d505005031414447c110b82d15018002001c41001265030008081e19401c0c0d0840d02c40e50340300101070350790b400d05844005500e00400c0dd0341c0052031181d040200003548101c0011000e404079191880300c42e500b0b0700700c0780100c0e401043c40030036560032513108681d0603503e00740e080490500104a544407070030045004414042c100020090200c10001c5420b2015040d00c02c004030300c0d181d00200c040b40c0c18003000c41c0206062031800a40a5103100c01d450b0603140100103030220400c1e5a509400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 578428516 1250 578427266 578427277
    0xd020405070801180e0c0607150e0705030c0301090b07081f09091103010b0d082a011a090403050301030605100b0a200c1e040912030b0a15021e010e0313030b0601050c0a08 75
    0x200400180700c5a042000d41307002b90700801080c04000d210b9141803500b01814502c0ba4050075010380e141030004004100074035403040d0424000d0801c01d0b1562100703082d500d044051000720a9021010050004801d00180d22035420300f070041020282d103000d510201030a9070001c65500d5440b904010785d40b804508100004c1186480340114550039500410300c1101c9051000c0881c006070350744c2c4600031900188603005074071254045401c0601840d0507074024110b800706010186c0900d607104006880440000d0ba8000074088110120340c43d081c4100c402404011100c1c025803a0316640070080201d440001960b8400d49002013000c40300c1a5510200c540d490013a01800e40c0c885d44802d40e07400401e040480ea00c80101065802080d8011720800340107500344241e100038660551082c10000750342e80444c000450b14241c5030440741c5801c40c03601c0c1c50701400428030074542d5030000240718000e00040c0d92109085034404e2030307810000d40d6a540152058000c04e004a12960000a0030301c0000d4103d100421 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 578429766 1250 578428516 578428523
    0x13030e04232d06090127020a0c0f240b010c030311040b0304080c0c011b0602090d05161d01060c03050a14030a0b0102010e0115140d020405070801180e0c0607 69
    0x2c50310846000151402190002e80d1a0079030907070301c148150b600b00f00c14014050301c1c9640d0043d0707403590012010b00701e5a007404003003c840d96012035009101842600b002e5500c9800c002e803010814202c0c200039402882194500320449560b2a41521482c0d00b03010b500e2054005840d580540141910150081c098420058240240402010405c1d1411402031800f446c090740d4540c1e03c9025107444c05192440c0d510025050010400e840156201041311100310580d010034050303100c0d078000d030101d00655041540100b03140103081ca071840481100c0d44440441d0b11345600d180c80d5006113680748511241c04e000342400076414282c3c12021034020002030030300300c2d034500c1c2031218826003642e50b04847d00140c82221120392281800300540da424050350540d28030082c02009024004400000003505034070607107543c6000064042c00c00e50720840c141c500035030090800c0c8407601d0005e02c003c1030390100340036900401022044100002c01ca500c200d400400d0384100426080d4460401c010054000c0301d003c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 578431016 1250 578429766 578429791
    0x90103110c060601022b20010f051f03020f04020a02070e04050d03050f0f010e070e03010e0a060501080d050d0506131d1e06060d110913030e0423 64
    0x4028425000d00514500150001411850030074100082c00c107440b0f21000b5104403040015110f41080104800b48201440c4c10004200e040340b141c0740b8506981e603680c41c2441e518100c841042c04405403c0030f407150301c89454400450f20300c03a60408108010740806034101c00312403840b5620341820390003481e24404500480e09640d03a40c403403a03460b195040318219a550071065000c040726801d40030740360304039400141c00402d901d414038200c0d1000c14140704a4040e41404004919018002c0078951015800600240300b8100f03c0c1000b41e0780c90307c5148048030038920342400091071745000314090255007115540c843c940070030102d604020703020152032254003442d242400002d035080c521529507400050714100500040c0415082c5c2021310400310780030b8200010003a01c121500110340154000b07401c0350400180800c1d410582e5000301d41e0100c030351300102c0c0e1806001078092010303a80ba88203480b0341c1d107815250050200348010394070050004000100d0305003c0740601c0c0d20703a80515070712082c41800c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 578432266 1250 578431016 578431031
    0x204020403020a18060603050106120f0222080606060a0819060e040f12030b130e120c0615010201360516060206090114040f03050705030f09041505090c090103 70
    0x6403c403940d0350701000582002c42e200402901460207800000c0519040c104043c4d89070031030180c00c00c2c5446001e0031445075211000a035990950341035460803d200c40f418200c009404119101034a070070301034101700d071107150b0005403146402c42c1214803000d55942c84043d540c035203140f10780750391501c045281d00980c1c8440c0c010500802d60b1155038403035400781041051713207002d506018060010446042007090b042012640c0706442d158009803040412000c00610020040c00c21401c0440c02000481300d003000203102c40344001c000940030300500607046100c007600c664200682c01c0710606041608001d00c480c038440c81e1150203901000a6071100c0d000344c2c00e000e000390f98003810241c0b514400701410704030807000c1c070200740e04102c0342c0d600c40000d1008000811090300c2984140a004000800d0840484044000c140c03181040c2c0d9042a4410100c0b41c64602a00b0310080603040318203010301840c81d1003540b40050036110950022a2030190420707115480741d05a111740c99010021403818036841d0005c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 578433516 1250 578432266 578432269
    0x618030a0803160305010821120106030605010210061a030c63060d0c0206010302090609041a0a140a0b03120a02031c060504020c100e0102040609050904020402040302 73
    0x5500030701c940c50741c550782e240031003040e00c40d203c00110650825291000602c14100b001802039580040ea0103041e0403460b01910f201c44034880c54424020044c1190300005106030190004004d80704241c080d03602c109141c0400c0012100103201d154015590004003516200c2c41c0c000540d0442d82003510030f403030a5101000314021445554013602d80f60001c030141c60400c41031007003200c017401c1942511082103044504034200030803801c0d050007501c800900100340e0303944d48401301c5103002c0ca40002480a541c0e842e40c0a03444000074442130340031302c8a0500041031481d245907014816a40032032510740c007140c44595509441c02c01017a07101c580b50f443e20641c50301201c40280034852100d00d03070f020442c071710b40c00b081c0350814080b626002c5021009014800c003017030b004000e48108926881e26040d400240140d82d03030103405550701203038100f480003030200c005040c04100845404107810701401100e4541050500700d02c100e11418000900010045c01145042042541c000d400107201609040e00c980 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 578434766 1250 578433516 578433523
    0x9030715091e050601090e1c200105010e0a0506030d270e091c17040c120803060102010b010207080703020d151b02010506180103080714070b04090b03030408030405061803 75
    0x90b601d0941c50291081502040300800089024044e100030600c1480d0381d581401740d4030307038100c8921100840d4001c1d1100156200705900071412030a009500d42060140c50000d008140a000b0f40580002d003000040500c9070700e0082ca4040c12001e0001c00c2c42d03248188044950764064500c80c0d80010043c01c052940719a2a40c0709000341410203040301440c103021a5a07443c1c0054980301d40e00c41d50f041c10150300b00e15003001014080c1115240e6031002e942e20740c5450f101f4400c85070032080700c03500075074140c90910a5040c055441501c00780c000b0050107001d500103a0340d80045200303110b19640312580c103000600b85221990800c41c4a00c56890396408022078a8040d1416000348074100743c41c807206a8501c0782d090040301d070408030960341c3c1e001e0b9201002441403031010500002c2c0181c8000a101c80421100300820111045088292070303100362500010600380c1d0140c41080c1503541408075018542c5008130407107040714001e0008502c0c00d4505014010140c010400242c418089501c4d10328040d2400d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 578436016 1250 578434766 578434793
    0x3030504030f1a1807050406030305070f0c0305100b1e090a180204021801120908030403030c0203120f06150415030c050403060509030a0909140f06040612050f010e03030903071509 79
    0x1018810302a29000d640d25140070714560000c0d107d0b03070030403d081001c203410030b040307031117894120f070040c400359103d07040005560846900003821841401841c8004012541c04071042841c121a81c10540c10340083d1410280b201418080e4818808004251441c426034480e02942094003000c0aa9004540000f400c0f03030011071080b2058007209001454035039020070f145a0103641504100085107a584078074519000c02400142415550140071804a0007003040e07480106604100308101d01d405000720240305000d4075100e0003031f81d0700c26110b55540c5000090384c040d104000e40c2c1a01030621f003441280030789218006c10051103010000031010a002c4e000d4580328bd10314200440e61440c20000050108001341d1101001c2c62070300010f40942715040c2070558000c40b00400f080800e4560038000790040c01b060340520729025042ca118020000d011038402400d803130700002006501307805c40c1d025850344001ca8640905800c00c00074000011440d5101029099841c10001040c40d400ea44000303803500c0ba03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 578437266 1250 578436016 578436031
    0xe0108150315040b0c0a0c030302070201050919080c10231605010212013312090b180604051213090212090d14180d06060605030f07020703030504030f1a 67
    0x902d07041100340020b004070b5640008142510902e0050185c40090007250940c03c010708168001030264203581c07189040c4e803213003440203200c000b02c4000d6001107010825140703c0c14280b8060381914990514000416441d0030325075171100c04010040040f41000b520740c1141c1c042c000041404411035001041400c03c0380f4600c10000103984050480005005d12016446a00424001d45404840c9400c41d4285940500c8903031102000701c62101085c0e4802400e410406c030098034040c900001e0102d000d0f00c290007600c81108904046000b0700c2410707255030b0308640c0a0070075070280c01c505904000c04002050000e01202d900c0c03030200e8803141c85006030381c401c0b036051090311158028000c0d80c51090100040c2c400c87c1e07040c0303511400e404130f2450280d4014280c044808010b60354005610392640d80e803415001d60700182c1004a2901c50138081e03e940c01c02d40c0c001c070414540b80c0002d51840d0000441e00186c9826031221418a131543d5100c41c59809844000c6441c808601000c0650a848280f800e006109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 578438516 1250 578437266 578437303
    0xb1302070b01060e0303070c150909020a0504030b0f090a172203030e10080622090b011d04170a0201180b06100e0a090c05070507031b050306070e01081503 68
    0xf40c003d004102c40d14604285100b40c01c00c00c0108000b8030000c901c1803c44854821884104100010588001d100707a400980c0302400024000c200d41c0c2e006000b0310a0f60300c94603802030300f41c07900d802e644c030000c0007254249107950020b2101030214400d002c050b8a0391401e03504442c600b90680a040c3c0905843c40042140180d1200d001d204264000003003045081c004d07542d5207081c550643c801440d08901414030340c0502c0303003a0000a01c401c0c01860a411103280d000f030074003404e40c0c24a09406900400d102e9081000b0351038940c42060584030389014011038224041c200c1403008154890810f40c06224070a00755940d403411400420946040344041a0050102c4d038814a858803e10424004888216007080b501d0b1100c00b9075a62440c95074416500031403170000b0010030704a03040c0e5291180803030141c4144079a0000000700201c40d810f044110f244140c140003210380d00d90034540d4030360083c0c880d0030216500050030b00d1300b544200561680101c003168008040010100030030700301241000003000240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 578439766 1250 578438516 578438519
    0x1203041205100e15062106090d0e01020a0c1806030f030207050f0102071a070503041a1c0515010c1b080606040e0d0206070c030e0405070221090f040b1302070b01 71
    0x310b0394482c01e102810401c019142103101481402450840100a40d203d8001d0012001c0c0000c1038103c000c0901202d10b04484040c180742a4aa95440c82640c8200014001403c10300f001c0d480031a80030621540500c05500c65810207440d10030015003001050000340d80c4500000101e4203981100d40c81c1c42c003a4000d40012800e14007405080040000f1550555100381c0341040316401145000b040481c1805031103448040c1890312a056100f5503000140701a010300b850250028002d0041080c2060701d900780741441e030f0450740402a40e07011551102a10180340c031501d02035004403100d414042c8141c00c40741600030b0200d105040500c254001c0c1950361700290420481c2d04061003000d0001108400408400d140900c0007035488200138a00d20030042700c009504101030052100864a00c030080003440180741188009507600c410302c5c60410384070a601030740b061689544040f6210708402400070302d1001c80b45003d100c05818000340c4550808050b6600c942c0d02800c502c05000403502c42e0307001c1d60065 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 578441016 1250 578439766 578439793
    0x5040c09050c09060c12070302070f05011403070f09030c08070e0a051b1c11031f0f1a0d0903200105070509010324060503090706031a1203041205 64
    0x42050340110048600e4007052060a80548040c3c1d807003c4022100c555842074200328039814411542d021810040c004500321080603004600721055030554450911010759410044601d800075050460140c035081003c9046940304240101042d100781c00c1c0541c000740da03592102c000c0070140d84025a160004842072007000801102c09401050051041c811414180d0a004030321040c05851110349800082001c0d1041d071b031100c80040c0040804003009240464802c2745400d52007140c001c00c1101214440e882c5118601210390165a03001c910701140f5814600441d940c001044144145607100384104810114035001d41620a44243e4500850103003000102c01525800319540d60b00e079050000b000555079003d01964401c0c603007483c002c1442072607403c040c00510982c40c3c03e210388951004004c03640740d401500071401082d0400840e8049075071807004404441403e00c0aa0400709500e100000b40d10382401d20001d0018080706882c5080d549031507800751907414801c100e911b50482c4890100c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 578442266 1250 578441016 578441033
    0xa0c06030e0d0c0507090b1201150510080f04140109061a0103110a0507033b010908010b010c0803090f030703030f0b2b030201180c0f1e0306051f0303030504 69
    0x1005282800d6181030700356580c41707454000c1070083d000d11540d031b4035072a0026600c41c1d04d9581811414002000000c80e8119210f8030620f484c00342034010702c0c001444c0a07400744205d000500c1051442c60700b0580d40c030b41c5c1c1c0c0e80b42540e0b80c254500782800d40d2a01910320100741e00d882041d003404003004007107900800140000d000c0d60021940e00c800b40106000101c601c40e045001c980240740d00d40340682d800003011600e0085500c140b5141136990701c504e000ca00c0b91303002a8a5500406a0980701c0500441d55116451701340c17586054614000b805181c0c02d807000640f6800919041070711041900d207062840040c1600e1030700000f80a130002030700c0e00c00394082210503101e41d0a00040039120b400156001c800c040039008001c02e04003411750654070700d60341414030070350021008280c078840b03410b14a015820500826580350003180818410035400003006020560b40e0a070301c1c240b11509056a500e9621004020100142102c03503171284201c03030810054801000c1c202031072007914002075608007402c140c0c28 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 578443516 1250 578442266 578442283
    0x103050a2301030c0f06140a020a0f120305090705030703020d050705100c03030501090b010509060d0902060a05040f0504090b51030d0e060a030207020a030c0e0a0216140a0c06030e 79
    0x501e04a0040305018051f44030304500c060308405100036980390070410040b8940042510040c100410300500c410401c2003030700540c1d40d41001c40d0b505202c01e80b542600985c940c0c901c0d00c01c0359072541c0a44020130041c100071240303209440c0200c1c1642d205959410201d88190350002c105800076821082e07082c20141c15209003800340400c080100603090b000c0f0000303800d910414400d80d102d014007088805050800c0d0308000922640900b20319145d644c0b4800141c031581003402680740700401e40b9408141401c080c86000c0440c0d400411421440c0c5544143c1c00c00e43c0200800d0203c14200310199840390301c400c00341c0c0c1402d20303a90403105900b540001a10028105c504a17544d10a070007030070155031010303482600e04058020840382e82d42d45020101054000b849115000be401400350507001041c041d4142c4000106c40902d481500c0c19601e44040c50100e1007400740d1012075014121041e030100c0c443c8d032805001d24000b6070031642640d4035602c0310b85c0c612016a0007400041c2d19012014024a070034840f021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 578444766 1250 578443516 578443529
    0xc080d0507050a02061614010f0f09021302090a0305070311011b1a090304050a1508070504030b01090b0604090f051b0405090a24090b010822020103050a2301030c 71
    0xe0801255503181d54450402d000084d110700d101042c1100e1a172542c0c3c13400441503607c4403035082c460a0b0700040c0c50181060f041c03050141840e005c1d140130440440c0c05007c0d80030382c0c020640d86059003107442d01d000a412518a05800a403010700c040001101080701c40051405003a54445c0e141924000614400d40c0c088004801c80240690b0400520144440d900c0084200f00f0710b40103070b45046a05156000e0366120581c0850400301c001a1010a1060090410b1582e40c5020403a80ca595040c0c546100728403004208104042c010403100707220394800000e5600c0102181c2c502a9204d10355070071b440300d500c0c100b1342e21903507034090000008040790b80c005040c00c002951800e19182c00d0014180f03400081118400907103461700417041080c8191912586124102d00401c203507120004100107200380b00300c1e540400c8019006c614103101902d041c400400c00300d03410282c591003a50044003e8100500785140390358482036201d41041c041400340c00240a19101400320b5851410030b016454925888803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 578446016 1250 578444766 578444777
    0x3021903020f15031303111f1407020d12140c030a1d0c240a020d09060e1309020406030b15010905040903050403030c1a0103081c0e0c040c0504050604030c080d 70
    0x1107614110301c1e00b685d40c4180b6604c0c5508140b00309080c2a141000c003100311281d83d001d40b01500303440d1140020b0810000710124020841420428110045058180c4825000d81ccc000280000640d20944070503038400000903000c92241c44505240f824407105403052b0000c0c42c6c010080100d072182c0d901ca0717498000c01400d0340490b5020300f1004141c440350304040b80c90140725000c0100b140740740f00c2d15628031254044203a040d035520807050000c0d111504103246200003480340720005502c3d0300c81d40c008115840300505102c10b941800500100410301d102c8102d80051b203c100000100e2a5002c20a22650401c903954441c0c3c000c0c0d00004042d5440790b0421840746140c1030300c0c400421703403240684003966450f0400a00203002800c0c0702c000074514200e841c0a10302000d00220400800310003514102c0303c401c0401d9409804840b2050036112a0390402d207055110115000301482c05820a15a40440d803c003285441e448001007681f40d03001d9003090711200b10140d02040110310401c903807078003502140380c06d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 578447266 1250 578446016 578446039
    0x3380a0203150d080904020702030f06250804051c030b0405040501060f06020105040b0f07023a081b091c260c150705120403170903040e0c0a050403021903020f 70
    0x86810900400340c0b17040c0929400309056045480800a02e58540107120403104a03107020031051984c80b000035003251240a00400140c0741502840c40a800b07154440007400360403140072050001d8030850b034000c0041580b506035600c0c10b5100e601ca400d000328000c000104205013012030000000440368426011607140004100200ea0080101740d0019510140d000150700c074150200d180c4410003007504242d4000b4680c400d041c0440075801034220051032040441011341c280309590000c400c031243d070540b000344000d4240c485d000100820709002c0c010080380184114468000c4002441c4078103c0311201100c00744611114882d650041c0a60126078a07072a250500f8055511000304182e841820030340340c004680014000c40640740200050603840315146401c0c1001040ca544401d0610310780034035031010031020f000200031541511a00458030701c80d44c450b0854103095910036085001041024030002c00142d44589038134072901032080e1030000c402d081d03004001da030900c0800d02c18070801500d41c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 578448516 1250 578447266 578447273
    0x27090c1e051e07030201021309060317070b0703090201021c02030706150605041206020409090b040c05010311070b040c031704061404060906080a0b12010609050c0403380a0203150d 79
    0x460b40d01c03224501c500540360350507460103a02900808103c200f480e220044041aa081940d1010741103030300504503103600d0002e040b203840441c40707200310182c00501d03040009021381d4006d4201e00c40e41e92040c030403607200f40e40d48141c40c0412a4030150803c010b0308009403e07070900101e80204641507240a1740d8a0145190141c054040d1040d40700c0c01c00c1c02e40200c000403040c40401d50503a0300404a82001740101821803410901d80c2404480885d1600c40001e00400d055200f0702c00d00380b007011815031442c600b241607221409030071401003007144e0307403403203c40c010000131b080204220300111848808c075115800c2800181c13008903a29210460458140020400710741e001c5040c00c11180503082864880c1c603a0401100980141400c5681240081c00388110050055001108440041c2e10400c2107803a40081c1c1c02041c450f5200140103075408112500003650300c0d00042525030501000d01413180d210010310120940111900c000481e40841008032455082c00f0120a400c0111242c60034580b065a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 578449766 1250 578448516 578448547
    0x5070509011d031915060b0a0810030b1f0b190818070303030b0111012405011e05030606160f14060708010b09030c0307030605060117040327090c1e05 66
    0x162021505480c0c00d00c4c0c028400032451a00d080c0e02c4580c410300c80c80343c0b11070000140fa070003010010005544880020f8441d880c00190300d060340e40c40010920301c1d844c0c0c0a16611401d0030000a82294400900c1c0000c985483c0f500520481c10115051f035006001a0409045410010070300110802040c1d4280a001000300320714003600d601d400d0019803000e0390720048450310101c000000c0d0f25860310209040c0d04030056142000394144001c0f88096645a200450740541e011564102c0440354465103c10240a040030f158401d02c0139003400d040419241440300084c0940605442c5c410718810040c0a100410103441122130884000301000e00b01220020003400051003002203000d00455010b000d59800e00c11241c070004014111445c00380c0300e04040c402808240d54640c0031582141c149800c4401041c4034500c1242c041d11051815500388100c00d10b6152503102104c0923850a070400704123404548101e10070ba080958582801382c507100b04c810817904030800030000713102052040f01006c43c903d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 578451016 1250 578449766 578449783
    0x20c0904060b2b02040b01090e2d181e0a08090303160b0105090c07020d17040504020a1e090602030307180b0403080d2405060d1d03072f040504050a050105070509011d03 74
    0x18ac0c0348000c818524103140200380800504c2550107030f15814002c002048100e96107420440d4400d071a44400200380c0480f03420030901d0280702c2da4002c0c040140205010001a10b01880d01400392803505610b10340191488402007022941100c0940c014003880c140840002c0d03001481100c19454401c00360009880c202070083c006280469404001135040301c0c0e041958001c0601030300954483d403000310042c0c14820898000001ca010300003540c1c124500c903c18100c126501e0f0f4019514685680c60101d5002d04411492118170780c40400016038003201c00010401180240e4100341c032601c07a50080741c140c0307021084040d800e240c0c40116600b0139a4200b104821600c040f603140e0f9481512060141c00b910f50001c008450359800b00b21024900404070040c801d4a215801c4003c0c4c1c49040300c0001d20340c9450700c07c10ba80580c1d0b0160058620700300780c1e02c0b8503049030290049900c102c00c1540d46900b540e00480c0d40344005500030030b6072403865030498501e49075600441c90044481c120480800e40d070701010b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 578452266 1250 578451016 578451031
    0x21804020307211a0906060f130b0a050c0c011812140102040602070e1003030e04050601030b030f01020405040b040e0a02040510030507030f12020c0904060b2b02040b01090e 76
    0x210b80ca440c05400000403031540c406140c010f00152482007030081c194009800c2440c040b0500c400d1407031030185101d0b4418078004001a0900501082004254010018003580304131924008a415101040a400c19002036580e4a549804100d682410b01e06198182c1d810300c5004240003080c000480d50040070746030703881c440300324048075400c140c20209012401c071502c0354800100400d03516400f0620a0640b200e2294030700740b50b142d80400111040781032002800150211548039104c0c9425040715412880500d4081200411400000d00300020b0403004001a9070004042110303080c00c1c0645120703070b41c1c100c07400c00c44180700703a10b843e4a034024140d00030301c02e0b591540094910480b9428a40c007450b048811a1940323600d924100040c80034810301613400c0c0c1d8030300808011040c400112110380795806411804e15494958a54021740308400300705a0000c1e000800c41c1e000020040400450b12418441801132403d5005005c212200c08400c03a041214046083c8407004103200d007035070001c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 578453516 1250 578452266 578452271
    0xb0f04020a140f040501173c0f070306091401210c0e0403172203140d050402100c0f08090a0b0d020c011a03070e04061503050a05070801021804 63
    0x81c20700003268426801c58000e82c8411000c10070031145040903020b0810764800383c9610507a2a07105090f461407660442d00085480d40d20501d59a6403582241c042e07040320b0032075a840703059155902105083c0c100480d0315000c001c48204c104078400b80e140c0105c10090404007805c0116940034051f401c400c0c8e4050264a84203001c00c081035540040d081141d00ba12600103c101074003588542c0c0462000034255001c4e00000c6007082c60b00d030b88440c0051420700804164103054a0003400c83e5071204c0c405d01a83d0140c06000c4502c100a4205226000801400341c0e000d60018940c07500b441000792207010060800d00300258010030f840000c1502d0784070400550480e84180c0c54a2043c00020454051500034184401c000310708a643d002054002e003c134200c4020003848810043c00c41c0c0c00c1104900700509030f0551110000704154031010002680081c010340c008074039a800c00350207100001c130540c1b089402d03500ca070402c401801024451742000c0d00300030b0000d51510a000400282031424551309500c1950b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 578454766 1250 578453516 578453527
    0xc1208010b220504023114040f1d010605190b0901051b16091d060c0c01020d09080405030f0f03180d0b0a0b1e060d09030c14030406030605040b0f0402 66
    0x240302c90281c1c002400014419035844031400d21104016a4030b02a00e605240405001d5910307022801545040c0d60100c015200000c1240c401c000141103004841b50146940d20a454482d5840303000c2c2d0702d11400018000b2800c2c52502040c0038124041c06459914a200c107141408060000720407142940300918185880f44a444410000109110406461440f901000a090b19402c0d214201240e600420030801880d440da00c011180151511050017500b28a00054450308100081d05542803d0800103003840242c0001d40c04464080e0000d4441c0e80002c81c0c01c1140d4034080041036414121200a17040d04101c043d42c2542c0c0740500950780000e481d48103103002154a030300101641e510342140807907004e400c0c01d0110701d000b050b65181c268021550203402c40c540555015004090007405410715280280104010000b024502000c41c10042d07216000804940c0880b10840c0310301000c1c0180d0354461515201800311802503000c64019400c2072607200d200d40e11b81704004a445425200941d550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578456016 1250 578454766 578454817
    0xa0b01020f1c0906020c0306010e0a0906020f04050909190201120e0105270307050703080d02090303030703142202010807030204051302071203050c0313050703020d030c1208010b 78
    0x2900501c18a846100b0505507104510807040040510031040c0c481084281d180d101c00c0342c450401524403034140c1c2c04807004001000c0d2444250343c1c4414044000030b255000c0f580e4038010380e408000c42c1010024081418003c62421034245908280d0340c030010203d2100f50301600f1100c0c00901000390501030a140019a4004c49400514008914000803c800e01d441450240c1c80c1e01d565180d51031520f10b1604a00110000000f21384516030010010a0403a245a41300440c5038001c64004070b08d01e8090100e003181391002c10186000c0d20700c9440c00708040c10f0340c0490380d04540008185101e220721000d010999819812400381480f80c0a04c1c1c803180565600600f6030207449154400d60b0800603d40b4900c15071301c142c0c0e01500c0910f00c2003a08031480031041b8001c40aa81047da568804e030f12040022600c001c2c02c0005284425201d00140c070342e02c03a0703030b9000038400f2040c3c0d9500350301092070003405000700b01804442000308115410301604039418454107160358003816003102c00c918448100d2003400d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 578457266 1250 578456016 578456023
    0x210c09221509020406090911060a050409180b07200c0609010f0216080a1a09070b1803120316030903020d0e01021f02041502010204151412041101021011030a0b0102 72
    0xb0740c01800501929540750200e1006010300c5005841b80700303078520400424508541200c01c41421903a54904050410002030000d002550140c8002a1040e1a0200048241c200c1d00d11800d602e4454011102200040140031101405d0165007038200c60b02c60782c0b42c1e5917008162201c6030003c0c60801055038003400107074030340058010400c6010a900e003000900c07080010300520745511401d480380400c0ca61240402008409a4036441e031900048400c0c01003030210009000000181e441e000349640d5813a010070f0030160b0300a00342c5d43c4c00d00000308000902c0b0648501400040d07052404003c2404035440003900c030a042c0101c4d40c10011844030741101c0b41c2c0f003004203a0b1b034000c40641d0442c607903801a940302d00030340c05031280030398401b085108070304828018404c0d18111035503c8074645c1c81460340601111140040d11400041c44000c3c004028529545865544503a1046a49205040c417500000e03142034141c0701184612424080034000c0030310000305503508543c0e007100110f681c004800060b400d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 578458516 1250 578457266 578457281
    0x250f030515041a030c060412030c02060409060b0a2c0402161502031807180518010c0207180b0a0302040b01030e0d05190c03021b210c092215 62
    0x10702c40d0030940c1012041c010031004440c0c61108034201c40c0c40e60500c400f48050b42c0070300e126681a80c040304070500040307400f56043d0004a440180507600c4c00381c5030340c1114200d4100303401ca83c5680304041040e442203600034208650b00c415000402891203415183c1c00101c0d0380f4002c5a900407034010441000b02d07100d4802c40059191301900310070708140211b03c0da00094100f25658141581c14903100194141c000c524503060391280549102c0082503e4000c0d805000054141d41842c4c44141203040b0060003071040401418666024106491808107400c4400c0f04004a00c501c161400380071000a984001c6560100c030340c10b81d4085410350540005078010701c1d05540c00303040303400340c0b0f841a1380d220340c400700405400d02c06c10030910211000d6401150000d481d020000c016900c02e0f1440c1c0100e4818445a07183c0c0d8200502109803c0c00c09189580c5942c00c0e10031740340c07803540081038101492504a801b282d0002c0140080f80c1c0103000c0d00300301103480c1095000941038030240704140c5d0100145401c04031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 578459766 1250 578458516 578458519
    0xb12010c170a0501060c030e18090a02130b0a050d05160e010e0c091005030a060b0a020102041706060d08030a020706050c070b090105071e0903060c020303250f030515 73
    0x2104841501019103102444102030a44440900c0020101480d43c880c20307058501c03036980d402d01c4030401d98040d07840d580c0b030025040d8045409140324030001d800d80c88480c4100b6400c805417030905d2403031050004c0707076180c824110702807030030840740003103c0d20b030b40ca5404102c43d02101d0003c02c000007410082c1c141610380d80d00b082046143d58000c18030351400600d45040318035103034084030302d80c1e03035070711032000c28018400c26a6004010000c10041244100017035904500141400a1100d82c0ca10700001c3e5035114071080c50150750042010071045454031441100b800781d000c0680020b00d009000a06180b0054500070850080400850200103440d81650ac0756681301c0300070803050a1a446518054010640896042d821100001d00400040c090f00780207113100e8481142008084c40d140300054a080d8248040143c003800c004081503850003840b0b03501c085500510354038200240030300791b0444610254100f40c840708102c969a80d41c00010f00141e1103051500068607110078038984005110615490f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 578461016 1250 578459766 578459771
    0x8130f0501241a030417090a06030b0a05010201150b030c0c0303071809091104020a020c2d060406050f1c2d15030f0201051218070e04150b1201 63
    0x10320060020400014089444184182c192552000ea02441c5842c1c8100450041d00520100c0c0020310002c4900c41d40b94030000169003811001c4002c24005405075100034000381d110702455049050480f83c400141c8820b1000781b180551903540c0d054031311090301c58255501e40020005005803a01400c3c5d500d65100c2c442980d50b2400c0010008000003401102c618089045c80302c005984481c61003108040c40c1c0c010b035100c0394141d621003000020b4100f04052010b5010741840c0581039600e2072400d4480c2d09075060400012038492031900c0041c604290310b240100320810040c8007517034012040d101c481106016540c2d4401da0034407141000326003075502d0400c090420001b1018040301c0d03aa1240442d5000280c0390854078405410300c00d9482070115900207480a00007400400c01c8442c408816500605080f440c4c1703810107001d00c0c20303003108031490b036203085554882841c4807809100440042900a0039600141082d488004034003a801c44a210140d540b100900070948400600300801049a03008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 578462266 1250 578461016 578461031
    0x120c0c0e0901060f0e130c051908100605011218080a08070e1c02010302030907030b010b0703110a0c0e0601020c120f01050a201803070b0909100608130f0501 69
    0x2111800041c0c03007244a0707508080010803410b4000840408403200c0300c5610469450708000d20061044a81c0107583d4107800c000085480d40b114411244030004040038071524510380031840b0300700119001e40800560500108111030b80c1e22840d0089241141c060009200c001c001c0041c00c20036a6030801401800d02040c40041590003811440c800c58072912020f80c980480700c100f05440c1500c4a0420740d440486000c07a0165110303901031a40700745948200c444864413600c488a00301001d0b8051818200c00284440401d80d006030800b00c0b5a4402004040300855a83c03804103410903406410030481c105d20020b00310b07078030800040d0001c60020b06100200c459218680b40c03a030004030300c00c03a4a50f0030403010400701403a03032291240718008204807030310301d00410b6003005040c1d10080c4501d1032101840c0d000310f401c2c1d8091100000803c180c41d281d9549016860902103900002006500070b000c0c120400c101460300804400c4d8803207108006c0307900d1b682181c58251140c0c8500d0340040c0c00c640ca0450b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 578463516 1250 578462266 578462279
    0x1c05120903270103051003051f0e0307060204060f030209130203070e10020609011a100f1416021519050a05250209060d0302070b1602030a0b07080c120103120c0c 71
    0x95005507804e81c1c042c8015510a52649030038100d9202c02010355200403011100a216440c0c014401d030207000b00400c501c03603598078107807035500180c07000d5600c2907000904108243c1c111015050f2800b950400350b0070920348000003a8540b0840503c21070154000000074461b51041300c1c0910038641c0100369041d0b02003400e4000751b648008581808140d8078090f000c030260612840300514000000345041c4100034213030381c221280b0100280c0001809402e4030f00d901c1600f01040503140c2d04e030b0b0303c01d0088201c01c9035004005d5120980c1c402d1102000c0b0030420310b200201c484081c1c584c1e9860700d041c0550b54800704041100d0754410340300410380700002d400309001203507000750741c214003d4001c54001d001070721030204101010348090001400b40e408240c00304401150031001c4c00d01c6c1c5818910940410021f44c000c0fa0a09038900ca04071070b510100307020000e4203600200c0307481d00310508103103490428070002c000a40c6850306000150040102c2219900c500b8032031110b400950350300c0f03810303802c28aa070ba9a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 578464766 1250 578463516 578463577
    0x17091e0301060b0702060f072301020307090b071505071407060204090f0e071203021903020309010809030f1204020a030606030f0b1614090a03060c0c051c05120903 72
    0x44450300c01e508001001444003800c0c01078400c215002403440d480d18000720000180c0390701500c400c03201e481c41d088452034840500ca21840c051903d10b000942d4901d000403000700186480d0f0008400580240981400b1908800c5c6000c2c0800c0465000101d60301d5400d815903403148000b00300800e54000088180c01c000c46034015200322510204144928108050700d2801d4843d86200c5926a500104042202134800c00012001038000d0054881c080001d400b04a212042694140d001d07a100082000382075a00c01d4416901c211300b00301a42c2401c0844699a00d18890300740307483c1483e88010045003c1d555400040c8005540c09241040025900d00c0c0a900800716010190741c01040000050064083c0e40341032200c0b42c800380c0d034124900400c48070390010707a0400713011180c1000301c8900200c0000c0d824402d0480740e600035110b0703c210400700e151151528041d1b400740d40c0030742528110341c006150090700791441d100c0c00f51088101c5a50f040300051a40c000c00c800c0a43e50046080d200e43d2071040762 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 578466016 1250 578464766 578464819
    0x18051b0409020903120906030f1008030d05160903120f09080a0f120305040209040803090a021905120a1101082e030c0e060307031b0f0b030f1f031709 66
    0x16011703140358104045e522042401003078006900800c04200281000703402e99542a880000303840c01404550b01c0764000f9285420030215001c10aa580c010300601c400742030032041103208203180c03000c0341604640e5000c08200040c080c0700c040c840740e4080c001c0043d004e40040c0014203000300450304052594189032640300300001c42503840340341e00c44144003460311038003c0c103101e6900500b038a0450384030341d0b40c1d0381c0300c0e580010107005840c042d00b4103c00043c0d454400394601440c0101454040070700700800c0050900780050500350507030007048140300048450381044040704090a00340040d43d40c695044036412681e07041c0c0401e60b0a010700d101140940f07081c204083d83c2c022900420301d01c3e200c51f4000d100c00819500294150b00c028802c0001480784440d040d582c0e84244085080781e9910500e0108001480d045a0003a0300048200f20100c0701c101c50896100c61801a440180010b400e2117860803140b500000d00303080c14104c441d218815809048500501020344071010081e240036aa09001121 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 578467266 1250 578466016 578466019
    0xf0301031b0b09010807210c020c0d020d021002190507081204120f031107140907020a02010f120219200601060f030e0f01140708060a18051b04090209 66
    0x4001d00320301a5a2028006420364440034a40d0785007a0307050005454000700205418100054160fa89007140040c040d80865803640c0f0401181380d061110001c3c0c00d18498040c103500811070310b8000c00259542c80c031141002901038885181d0441103410403400c4c480840c0381600803104401602c8104240001d6200469041a041e5802c00225025843c09842144170362105002c44101040c045000d810756541c0040c440d0400c4003414034401d184a08148007035000d4210712480d0b80005009042c088440c6078028841c0c400f4090001c0d1590010f045c410442070f01201f00008840d2800140c94964121540e0714819101d00403041800c50005044500d10360305c2120f10342000003101c0c941c0000080c114113031160b640b07400c88441101c50044006140340c2d205007610348520141c2e254811402e00c078183c80b0300300f412040509841c0c041009401c1082c0640204d00410b51100f08004548640c16014845412101c010801b0344524010840300131305110400413041c00010001008a81c980c01092040030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 578468516 1250 578467266 578467283
    0x13060e030c0d080105010909020d0f0609020915340506160e010212030112060906020307020d090803040b0a2105090304051002010b030c01230301030c051806012a02060f030103 77
    0x40004007141c50640c203201d198041001f110b02400340407281c4c6c000d8a81c0c00c5100c01d00140185031503010398156105c540c072800f102680024804e105081124498544cd0040302c00c540c07900380101c450a49d076503d821b19003c81c591809400e10890804100300240540e00a0200e03102c500704405442e040b01110140c03a000316030204a0940e482d4004100203001c40c29000202c0c0c1035138a44007900700550002c0b241103410302d80e42d52103500010980d2020354004d2106074010544c0a034118130160984030143c02100160b030041c07104010403a200700071550303040c0303062400c4541c1c0c6684c07181d11a02140d1240304003070020b05000800c00f0060002000c0c208641d81103a650040c0c0008040030380c00c0360342088038103415801c1b200f11444194000c141c03424505580006500002540b02d55010198000780c0040320340007a010001c010394504202d10015520480507140200d0038504000380004480c8030174041c242c09501c0542c4003041001d29841086078003c0c20701640c2d000204000300d4154400d0004a40a00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 578469766 1250 578468516 578468533
    0xd050609190c1107030b07090803040e0103150b31060305070e06031c03021e03160e03120a0804061d0604060f0f02160330020313060e030c 61
    0x241115200303000d8101104440c1000705500790440180070750300d1070201409000141d184001c0d20801c0444019402458008000d0070203070b43c006d1461002d0390000340c00da17005020a212032001881d02d01c0c1103940c4140414010b0b290610b250b006410101105c5601c9140580049032003000e450742c03c0000d06e80004082c03021070203040000103d030854080030740181c0c041d0740140100389a200d00a900480010200c1e022080300d00021300c20108805c62040001c3d80210307445d201038062644003144035181c02c03110380c1180382c03a6185071707d0f041700602890200720300c2c000c1b88170390b039102400448107a00310311401995516000c80058400c100640781181c82d1071070825602d042c0703040c8007010000c007600b410240c010742c0c446842c3e40c4050948203e008050301e680704c030010481481480281044120b040310040c486032581800b4008a1000ca080410f000401d003400349140d84074045c1c0c0d820f0f034030200c00041c1c403030300c0f0800321600c615418a00186918541010500e80c620300101800c0641e040b101120001d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 578471016 1250 578469766 578469769
    0x100501051f0e03011515090b0f0319060b0a020102180a05030703020114040801090f0b101a0d091e12140706020d140f15030102091005031017030d0506 66
    0x2000e244140020158541040c0301d591440307000b0b441c080b510020008280056400980c4801c161564006044000e180228075092a00b245d01c0310020710004507601d0410315150740b40320702071100804401000e02c0064401d244001c241d4081c4000c1d110010400741c030b400c03202030083d000f50b2240c014040702150ae510f042080d80b0300041e002003581c9018010b000e10610310390056800342c104200a61000c2404c0c040441e07007510034400c0d60181c81c0903045441c002002c1e402d0411510502a02c40c4404502c185002c3c008442004491035521852802c07055603150341014038802461211802050b00c3c1980c0c0084440075852070105a00501504c081c0c0022540360b8801d81d0846125000d900c0b081302e040c405080401c10366030240540080752a4040b8210911000402c540340044420400100c498018428514500b202c1e505c1c441c04190001c501c0c003200c4000045403440c112201c00e04000b030000001700c03029410380001005011603031407103400c002d555800d142c481e086140844466440c060019145 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 578472266 1250 578471016 578471029
    0x304060207080c0609060a0512090a11040912080601020102040b030a06080f060115050904090605070309050706110a0221191101050f1204060b060a090302090c030103170a0e1210050105 81
    0x3607180040883d490700200d179061152a80010801c041404000d10010940150084070300303200d00700c00e8020f844400100c1c0790205425a014400502172480d00d420310002840030188a50b1405460403c1c4007503136180c800407406031240d0340203c000104040144098008590004001e44811009440d0940280c00603141d94000910a121a50301c0c20621001c1050090b002402c040b42c01038004100c511700c40e1a48816200e003620a000040d40d10a0701030140a000d015910140003d440d001003400b0140403101d039107031649000079108508250104000e030b880705a2003a814044003041d00e80140180307404a25100a4100684480141c00c01c00b9030598400c40466620040503c0054140806603004801c400c0c1d000b0000c44030030342d46000c0760b03000e0380e1614041c0450a84640d02d92119904520501403c0320018001d440508401d10040c00002c1214658101610700301d6405a100c3c1d942c00c40464400c61700184954212690394110484240c0c08100c130381c00c14200102c10301842c0da0b40d1052103c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 578473516 1250 578472266 578472283
    0x60405030f07020a0b04080c0a0506040609060e040e060414011a06160c030203011e0e0a050a030507110a0603140906280b120a1203020705060403141605030406020708 73
    0x90390001c0005041c2081d400002d400c0c101c0c0080d185240c0c1c503840c1c1034034041c0b40d4000c2c0c1201c509548540390320549454510741920260000307403910ba04203460701e04d01030a0150640540c0c0b01b4000220803100003030f140c56002c101e0020007501102d00604050802d1032203104a09019140c035420002e0421007000000510018644090025032030134050b0103441c5d10004c40304000b146c64050503000040569824092098034900b8403d0f040c2d0845d0758000402d044490780c103088680c0307402450090b40405c0004c20038040c025014140b0316070799419403821600e29082c1045040d400070010102051442d4142c0c410500101450710803800c540f2810070f03040e5184801c8400b488041d0310401400c402003c40000030301103c0d8110004503000310814005410380482c41500307000d036400101400180120148001c1e40c48450741030440c50410389859407510303007000030700140c2885518840514010600f104035103051003890404400d0701800e290090b283d038058031402e40148110b500105024030003040b40c0c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 578474766 1250 578473516 578473523
    0x30103030f0c080c0106080709060e01030210030e0a120c0b06010e0f040c02030903030d0e0118260d09120f0509090a0f11070b0f07031a0f0301020f180f030604 70
    0x41d8900c040107401c492105842a0031950508203002c4054005402d008403000350130307030b0005400d07401d050804180c225a5540c2c80304000c203004c000100050380343c0708001c8040080503c1c0100c1c64401c030900302485d11a42c035030001c141c0d6029120484215621441c0381841c0b5106002d01c91054a40c440110b400220f208503c0b0b5116030718109003045450705a01074200b2411900680b800c081c04070002a04640204a05032261901c402c20b1b860710510a01c122006449082c03204401c1c0645070f225080c1e42114403030008480009240c031a400006104290398103a640b103241805403c00500d4003552070072400b00c4801c01b058110840e0004036014070142c4070b16903c040c00c600740960300c0402c5200030788114500d040e9401c1d50360034040b500560040092035240e02072440d030348043c04c1001c1d9071140224028545070806103041e002200010301b00000414032401250200421b40342c00c8006402803007080940c8403072040000d4072404442c01c0c03810304104010f0840e8074440300280c4005040d111202101d004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 578476016 1250 578474766 578474777
    0xe06011d01170709091517010e0303041e020d1109070503070f0c020409020a0f0e0f0115120b09011d060603040203030421051005010801181101140f04171203010303 72
    0x1440781441032004194003c6062502c0009540d480c0e40341411941082d40d0310070402d0020301e0038003100c0d1001800c0c002c0b04110b01e00030022070300c000d50415260301000d400149154424400800d40c403815403c482c80705500248507040803c040d11700440f0511030361100c00d00920340440000c07044c900130b805491003110142c41d400000510300808851180300c4020403a401680c0784081400750720740b0143d60000d8a001aa003113b800d040900740c0e121030000401e503c03070518100c00140000c250b0b02c2c0c81c414400f4140d040282201000010100c007a144050080d6000151100000f0388082e403403071a030349000103202a258280c0c0350f00050003410701c0f044801135003541c020081085444c060010b030703030400d80911445290103009a5a0a070901c20680444000d1988403070045c0190503003031050300b0360030f600c0c428918141a2103076a291011211002d4060500000c0080600c00c019000300325550b1604000c071040da51500c0e009100d00d11900b2496002c101c2c400c03600b1520300d1141c0d110442c0e05032a090f4850 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 578477266 1250 578476016 578476037
    0x60f08041509050118030807080a05010501140a022b09050a0f05101b0501060302090c13031b05040204030c090c08010b030f0c07050a0506091c120207110a0e06011d01 73
    0x74050301555000f111990750320342e00200300101440388240350f03c0c880c2e69030306590305120800a080c00405042d50384064039000c0108950382e0480300b0050b1074a100156981c44170001542a4286242240051924a281c0d403203002582c00c65250b0a41c1b00b0036035100d402003e07071950203010941c69180990150368900201c1480b651525145204c020500707032030403001c20000e920314482c1c00020101d00f2500ca030345598003402145058200d84d40d104281800c40350400e1070710210105084103a110151018110041c842c036011190070010003d010013030002c2d03566031790740c0c609603102d0029442180d00c114600b2121080c030621400360301d8100c50101c0341d40c034110f8486080d030610742c48000d4000c0340300300d2080040e1000110140107010301c03240180c010386110700c0c00405040c01c01211103516490113040900d10000c40c1d80014090940e204040d01c0141c03a04d0892500c40000307100c0d01c540e103611042152000030313110170500c0020f11030300080e0b84045005441c0d03801d0040310b01c41826154007085070b50a6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 578478516 1250 578477266 578477303
    0x2a051201110912070f0303231912110f070605060f01050403060c0e09010b0d06080c0d0f1a0c0d0c03182901061d0a0503070b0309070b13060f0804 64
    0x18021843c40d811401d40d0b107070b907684060280701c3d050765034011804a699410301c0041250007a032482c6852911106e50342c0303044a0241042d81c81100d036031001d03003448a00b0710004540c9055910138080300c0d050f09000b6540d140d20300e0076450240c0142c003084a0250402001664500382040c482c491f443c0117031161b030b00782415991090007034088050702404000341c408401310103541c0c40300c009000342000d64000b9a103406484101059a41c2c0b908a807003544e0207040e001045c0d403900c664140c61035401841181c8071040742e107860000d41407100c5018682d0118a0240800c00c0503440007480007040c1c0c2c8900b0801825050001d4007601c1407640d10300041c2e0710b4240180c0c04224013040810700c07400c05500701000c040212000c02d1201384213070003000000d40000075607842444031903640400000229004401107140000003030382c55280d401202c111036000b001107003400b001003140c1c0e005444480c51a035129801060790764941e21851241e100021448070a02144a0140c00c5040c05590090002840c8800035103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 578479766 1250 578478516 578478529
    0x3061f06120f020304030302040e16051b0a051c0f0807020706110120032205100e030f03010603051006110c0f01020705120c0111030301120b042a0512011109 69
    0x25040c40c40720b44074620b80c040280c252009500c42d07442501c0050b1210b0030040c0285002d44000c1c00404024400c840b45501290030009031395130801c40c880c02d2802442d0408a1a08015400000410601c40c00594251802a940521200761030b40c0d507c07040e01150008003101c1e5007100751000c80245e0030210090000e684580d08a0480d60003401c00850030a030103512441d03012141c08102080007202106011900306043c542002c89140b00d5420ba0007010692507a0307403690100100c2000341d656460b40c1c2030000405009541140c800300c160f032a2a036030755000280c0500030440752201c0c503042070368000c14214050940c40e20342130819002024000f00d60030611a0130495460200e05520401c2d4000031181d6429044040c3d10703866001600c0281c00c0c0b0300c00035088080a00406283d5081440144401961f030895070020079003143c1e0310701c62502e503414085503005070300d01c03034032990511120760540303481d9000920f5046070700c00c0e6043e2050803104030701c8600722405586525000d90007004020300518003038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 578481016 1250 578479766 578479787
    0x6030706121a090f070801092705070e0f07020727050c041511010c1e08040213021801080606042312070608040515011a0715061403061f06 61
    0x1515201c61200c5074200182400408452001c4c00030000d404100c01240d201d00568014841e1b4030081c48140c070892121492055864103a2403c851001d19501c02e0117001c1081d000100b1004650a03d107007000c0341d05140c031040488210000d07101d50080064100c242c040041c01c0441004c0c4001d0110420320845070150001a0004180040c10b0201080c980c008811016801c5a0380c3c5452130b40c0c18482c0c43c40c03401d4980c00d58500301440903820524109d0721404c0c440d0340004c4240e10300581641c1d82ca01c00621032903c0181100543d0340b001c140103550302540d411006501c0700c242c036680c545560742d030304101c05031140780159900684100310038210010100b41c00d000055009049540500c0c214984d40c0c944cd64690100000a80c01001d020034000e0030300c0b4404000e10010071004082d0305220302e0707100080c3c541b0184104690700080503414441858a020440e41c1e04400911500342d807040140e2072602140d00c018428014440410000c4960404000e03e05080c000d280e40d82600d070810035510007640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 578482266 1250 578481016 578481041
    0xa0c05010c141c09080309010911060c0706180b040e070e0406050f060903010e061005100915051b060916080a0c09181202160e2401020709060b070b0603070612 70
    0x21104410001018040a188900c7c4c0d6400005182815424a0b041c021030b032507207283c01024204050031403c02d0206406040c0c0341c00c0d003009403880190443c24003104903a540011034006010401107030700f100b524003503409041c159031581d280303110003010030088824a201e0341d90301414004215201d4245030b0043c003000c04004000207481d03418440d402d410010f04441e11006a0001102401a854512800c1ea21400380307241c1240000c0c205032a801d01d83d2a0780900d032091007404516405c941681100b0b02c1130840058043c0c0c1c21500304902916501c0181d00d049028001e0384110200d075018002905043c2d407600001603400140ca030040b040d0003032007141214103900014600c140085812400400b04580d5160b000701400380305155070111002d040c0d0011250001c0507014410070320b54020828020403054280384180840103030060340b801c001544203103019403d220340000e41c410100060511030f8002d00800300755aa9000c105611a1100c0c014100170070b034001074150f01d4040380d0380b00b000b5000700c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 578483516 1250 578482266 578482271
    0xa09050f06090a030f02010305070503100e04240f0b030a0503030f1b0a0e011e300e0609010f0203161407080d0506030114090a1b0b0a0c05010c141c 65
    0x104030000c03441e6031400350815902900780490185c11542d05200346c940c440802d02d03000b410b43c1440c208030801c0c00c01c203100c0c0c1645156141301003024007640d9202c0040081501e0794900c0c0010240702500702800e00d0f849004007087c501152140709003000b1801d03071070050b4000080e528650b00c7d014400110b00014005480c800000100c0d0901c1031043e10003410460180d0700c4038404481020001012024410081c00d04e11040f0000024903a41090300e0048001c0d0741c1d6580d442d001018410403090041002123451085e050410120309a240416418000c00300d400c02400f54070099140b0200340e21041c2d40912485904400d0010f20303600c140340c090f40140c00c510140f458a0244d841c0e0f403e1b81d40010049585c4140d5840502805103424468540700e041018581c03a11441e02c1451251165a5208047d004451040341c0800c07000b8101c03070b2500940b02d4131507215128805644024824820708d001107032590304e0008203403005401030311504041015080380c01d00d0881c0701c6121014080b60b5240c072002d4582c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 578484766 1250 578483516 578483527
    0xc121f0e0106030807171c022110170607020d0f031103010906140301060f1202030c0306043c0809010c060c051c0207080d0b0307030804081605060a09050f06 69
    0xc402c0c01041c00850141410340e884240382d04105007800d0031140440e14043d8100031076810200c004219410412881c200182c44141340481c140c0d03000990001741103000c17010300411410b01c0130b000100e0150307207050840640742807514044980d250340039254880564803603100c14880b14446c102820890400c0d140c08548410b444c00c50b15090303002a00003101090f1034100600ca42c542071400340d03011103421002408000c1c80c1039140c0b0000b07145402200d05d00c00d03d0320307100710554508100070341511501508a4680b8039050034450000c2c04100c805001241000704492101100044a0280b01e03a1a00c52981e00e074802d6030b104a040d510410005040c03110f540e40200c00300b040d0303110380c40441d1030944646581d0701c2c02d8820390742d60002d00c03220790082c80e1040c00f00c540820071355030a84002c00941b2100040f03814004000030b161215952006000e080c000601044651000c9048480c10000d070b40c0000f0031584820401c181da01604401400080002d03208001b0b40ca084504410155809003100b4540b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 578486016 1250 578484766 578484791
    0x20102071206020d0f0b010e040f1d0d1b03090b1c02120103030e0406060507020d060603051b01031802030d030c21091103011401030f030905060c0d020c121f 69
    0x25480001e4030b49580c08121200404118020140b102207200820460100d000c40040c050313403c6604118001c40c1d551084801d8009a030380841c921040300315011003990b161a45441c0c0c2e17418070014402c001102122078502c69811000303600790040d407540300da810003418840e040c82281c002000c2451441081500c10f0b02c20602071008100c40001041812007940c11400d02070141c8070a0484c16018600d000810404a54010b086d11085541126020500940c0d0b050060150005801c00382940c00f92917204806590003a1003280e9004d82a00c0510000c0d040d46030b80d516100c0600b2010350180c0005100c0e01540740700341d20590031b68100e0f062920f05140301410302c0308030043c2042000c1412340d449940703009100c9407076020503aa40c0100c2c006e2102d10042d0038101c10b410b80601c0014015060804103000309401030780d00d6409010041c00036a11204000ca8080c2d445035500008009402070101044442c00c0210100110302440002000904220012006140210010401e10541d5030b004002e40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 578487266 1250 578486016 578486039
    0x30c031b03020105072709110c010e0d12060302060304030e0a030c0b0a0201050108030415050c150a02091e01021b04060f03050105040b0c030103050a020405150a0b04060207061d0d02010207 83
    0x840e070003540001100c3c501984040e210307848491300b00145000301c2d40320b03a000031310b401e150109a0710309500201c0c11015040d06542c0030700501005034000c0d42007034400c0f0710b88640010301c00c2054170103545491003010301445440465280b4007010750400c004000180209000c0d28010329003244c0900030170162503581d101c00c85003680c175411143e41c0c410001150028280e090103018054a80f08018602e003518103044640804284841d88040c00008100140c0f0301c0010300605940720340c1241d91601610700264034000a41c0301404203441161990307103040e008031001c4d85052409206800034142d1040034112207003030351144c40748581c1c4141c0b070b41c0d4080342c00c02c0c1c9404007100452054001040c2806c00349840c070f1f80d131074004004043c1c4980906c010804510b00007980000315030103070313000181da4680701382c003003034281c001c2032007542140c80d40a00040b0080c7e09070081044030210fa0075281e8240d1078000495402480111a109262440320b1079001c074585200d0300d0040920500494070010303521501c070f050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 578488516 1250 578487266 578487317
    0x37171303110d030c022401030b07021203010b04030201111606050d06030f110906240a0e101d0604030213053301030b0901030209150418111507020d030c03 68
    0x2c1d454200c503c1c003445d010494032010010b10610000003800f80380d807411580c60148405840c19040c030020030030460080c00309084040c0d424101583e00e68440010750751342c0e801031200301e0001302c900211803544803001c5000c0300c04081c00c03203000601030b1078000115401e8200d60642d406059a98030b0020020382ea000c65084003500c6400310754040c24082c004c00001c618000c01490041790100c01b502c64904c4415610308400300c2c4c4210b066100e1010322821200e000080e0010b503000201070a840d4061a00004c4050b032090400803a1103c02c070964003840001d0046110080d000300040f00c83e01d4000f61603400042e0320445100303036404003035201c4020040310201000d650241c10085600c4008550b40750140c0302110385c3c15256500340d03500d140d0100e1014540180120800051600c018545961f80e800c140802d1300c0b90810203401e403016091080c1420300c048059031146003110b810500b202510000e540d5030b80e800400a0b03082c3d01d40d507203054643c0c0c04000d10807020002d0340081c813400303090203081180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 578489766 1250 578488516 578488543
    0xd0201050114270613020c070e150108040f0f120203030603060705160602070f05120d0623092a0d0e010603210918020a0e030109020a05153717130311 66
    0x80152803c1d000005050019003e100160580c3d4518012640c0013302e007508558040c40c544552011820078024418404100070105072210007070f03171007169000010354000c505c100d043c0c982c82d0303d6034201038038180f0614038120504000b54031014041895035000c1c04500e0b00416002074501d190781d544504001d86564000c1c6145404110350b084110188100b1024011001c01e01891010000300030301740003612601c0600c5900382c2c80001d181c4c03612504811040c800850301510110080e200040380079040310740303090344040c9010903884a9280502031101180c2d0040000c2100106070021402010b182045103014130291010000b0071100240c0b01072125840750800584810800c9001010343c000000c00c540720381c1c180070041002d40d480c50707041411101c040b100140540500312000c1e038103001d900204a54400a00d044001510070803880c4a5003d00c021840900080c02541c16140800301c00c080400c0ca84032100043c021108800450380410b01a04110703d0091801c01270f5031804000602c183c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 578491016 1250 578489766 578489773
    0x11203110102221208273613020d230109060509010203040309090b0f060c0a0203010e0307051005060a031415060d02150a030b030d0201050114270613020c 68
    0x96001956000c3c82002502c0c9800c0c0c68090f400c842d4850918a0007100141c1510000c0403041040f6403004850540d1404006442080010342c0100c5075002d40030140c20b410100511000c890201c414816071091150075080c20b11400c9040d15000e1000c1c58003030740001c0703e07030008030045501081c51305a4100c003000007030341c00851542d031a841c0c01000c1d40c2e800b03006c581e0b40b40e0042c400d01c00002d4005071480191800c5a000103080c120384070011701c40d012406209500140c1c0040c070345240440100e0002e41d03030360003a0300030b0100c0340300348512035a20321482c1d9018040f50020b00c0a8010346003103030842608410000c0c11041025140d0b20340300c680d100c07a06c109010340ea0085440e520220000c402040e070040c01103850b445a801290041a20a40202c1200c1d040c0c490018201c40701d9406580600d551040c05412188180c0d881d01c0c0281c020102802100018504a148038100d80f50492440b03903107075112600101800070802c6070303a080741c0b00944900e078071902076100c8806040883c40500700112181004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 578492266 1250 578491016 578491057
    0x20717060709061d010e040b04091104060b031303260a020a0e060a021908221a070f030f12050c09040b03030f120703020c030307031b08040b011203110102 68
    0x540a142c2503402030f4288480d140078403804a103900c0c4981d50403902800d014800702c2404001030010545005c460b544545000001c4c2c05100a410018107402000c0d43c0402c61a0744900500500c0c0c0000c640f4070003403903071290205d0002481507140b0b8165845500c0c600c003010080300010105400101c800c4815150b010030000d84580d4000c0290003210070607a119441e10301c101d0340003500c4546801c09041c0c181061070400c2c04001c14482220130f8494012a0b001c0d54820f20200e04030152030510500c803040c103404451580d501e1300c0b03008461a0982c4800c426424406c0c1e923505444e00000103039090284000e072101e0b808002c0e03081c042d480c0f00e1003555032416510920041080304981d00700b19581d000c1d610034040c0100122460007140c802c0c66801c8500080780d518188114040d1040d0401c1180d28040402800003807605504002ca00240f0100302c1402c1a912050482d52400c049070080c2c003514a442c0108000b41e120010740d140e09000e031411400045043c46658203903407050440011494003580d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 578493516 1250 578492266 578492281
    0x1605010504140c0d0206030a09050708010609021b07060806090a1b0f0315122a060306180203151e0406170c09310501090f02011101020403020105030109090302071706 73
    0x70221914a040362070804c3c150164003c01c42c10f0000a02d014103a658a00701c2800b441420000b0358000c101c400002e0181d41d4032109044013030b40254000003d400044418400c030601c0125011080e94110b40d6040b041e5520074042200c00503001c0c11443d0b40d20f50340d14244000f000181000c5541c2e1034036031141d10948085201c0182140c00c2141c000d2040da42481040c001040b40b240c0780050700d80c12524042d5000c0c00440081440811202c011482501040300094902c0d0103400c00f4040f28151605000580700c5051440280e1100301d50005056141c820109840e1030141640d00001251905c481004c407003444c0031a00303c841c550401c9648a50b0000308100d0030908101a500b44201a0340d18802c90801451a0519190411150715442400341040c422480f22840820b034081c0c21070001d1204480d02c0c28500511450040d00340e00286a8101307900070100140200c1d001c50f941a500c040c51a80717020700400c010300c8180001c5045000b00d041c00075081c00040c21700c014500b01e07640070380719500709005d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 578494766 1250 578493516 578493523
    0x150e130507051c08091807080f0f16120b0409060b0f01030e1504080d050115020d020d050406030b06040f03031e18170708030f07031805060f160501050414 68
    0x42c80103110381ea00a402060390100c0403140380280768451243c940b10880d034400520100c41d520480d5050720000c00030484200e6100c1d0059010709403510b00309404c1d4503030612034807400348101d44c0d17180c101030012440044039101c0d6a40c160503035400c1d000087c07402c0000e030000307098030307103c1c00150740c0681c07100f641003640e10380600b149040715001d0a08024401d240202a51281c0d96040b45c450070b02c0c541030000e001d0141100803203040c407680903c00c000542e15400681c110400c100000c100502c544403050001074000582200d40b004981c40d2181450715020003200070308182d0071450780140f000d00c000100101103039104005984607460b03c84454000402d030300b1142c2e0f00d082001e0108100c514140b02040c2c03101080001f991240d070f600008040c04404800d26182c180c1d440340f81e1900c00060800a80d040702d40c040c2840d41c1c8070760790380c103001c4010388600e01a403140c60080c6548030345d0070008a41000f50200c0200050782e4109082c6400c291151103490031030b03404607420790340e02d118890528809402030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 578496016 1250 578494766 578494769
    0x5030708070e31090201140c01060305011b1106060a30030f0206130c050915030a060b13061d040f05030c2817090402120c070c0f080a0303150e130507 66
    0x1900421a24084c0d400003807031148540f00c59108031030002000d134141142074214101650704440207101c5003150a601e40094990000c0301c80001d54018610844030001084860181100a0032150344906000ca941d200e0400d401c16040e60340d00140c6103503108000c0c500f007441214040d4442d001c01241c44c9034042e080034401010b1920410141c0e440400141240d0914800d60f034081c0c031824880c0e0b841282c041e1003402041046581482421084020451150002d510081d000d0325580d0803c0100c05082094800341c0c00340601d0400802203003480c0300082201140d20078041c42c03180c0250202511102e0071503000076800070850300100f00398524011031000c01d21440000340100140407615896010b01c480070800f00e40795a00000a0b407002c180c1e51038065525988481000307a1442c10714140c100c146610140c42100c46480d51100010800101c07045402140d003100017034540b00f12603940440060085c0411010b02c181c1c075610100b0b080158038480ba1040019550301c05030450750342442490300000c0d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 578497266 1250 578496016 578496109
    0x30307053f0c0f0a0510050a0f050a050a0b0d0317062101020d06230d0201031d0109060c080609010b0d02070c0801050402040608070503030a0c050a0215030f060a050105030708070e 79
    0x100000021702e00045498440070031501c0000c040e103074400d442c80588441c484880c0c00e00d00b40001d00c621708045502c03060050400b5102042a45c540c07000707204030800d4203000a80800c04014103490240e1302000c040790700c00c00080900002440801c0400114102e101c42c00e1150ba50208004070046580d1007513002401015800c070207180907042c03c9207403080c0c000f5407150140c4240070f020030440e4001e07001702190110707010f401c03e417001e01c03282034074000c182541007030b10850f007000c2e04160018041e10156004240240551480da07007880c002a0455010b80003c102036a420401036000c00d498211100191695000210701400c0c00d004100554010f0f0300200302c02d03003103040104090340d0004111400d42145d410043c0041c9041d04219003231010742440690442c070030619a80040c440c1b0401548289200360b1403609a403102020320401310001c0c0282808920300300003042c1414018842640d10140601e00305000d6201c02020600c80303154150198140701041504210580c41d0180361200da510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 578498516 1250 578497266 578497273
    0xb070513050f30010c0f1b0b01050d15050a09262a01090b04170408030301090b1c14010c030209060403020f0a0f061805030307053f0c0f 60
    0x2409400100390204034140002000d80101403078a443c01264021103107094400000c202043d40003502529050000002000180c80c004002e0392130030928062a0009800c1101c0108a078205400c0c0318215809100540717008800040c442c07407000d1070b40a0b151181c2120040401c0c12081032400d481002961035050b90b00208185415081482c51019200c11441c144541c001d1982055441140b01c00f407029640000e50034118600309210360843c800d0b008502c41d0304403500e0814010140302d860b0207103029000403a04100010020745165030850488400c009200200311140070a0401290070030180031140346502c4191060a648280304050300c622550400b0340c500b28042e0300044032807041e404000e20481d4150030001244e00c032802018050a400c01240c80166120b12000c1c19440707030324118aa6040501c0c00c045810b0a02100340c1d81480da00400a01d190b50041d072817000d1b4420790805410314a526005a2650079818800e180001d12081002c55074031002c07420b81c130342003415a854500440d071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 578499766 1250 578498516 578498539
    0xc030702060703050c091906080105030d020d031a100c030e0d03020616021c0908190203060a0e0c060a032307020d050f04050a031a0702060c070b060a030b07051305 72
    0xa0300410065030185051900080716528040d00d201c0c0ca0058a00b4140c01c100039803c0354a1a813045000682a200c19440341a0180c0e610800c1640d00c0c182c091001006800000c202500c1e00c1c06138115005030380c80b40d281191440300d80e0001c9600e6007403510125002030102c160307600500d13401012941c20544207691600f81c01c82c894402940c0c401c7c01500349800d04081840c90b0410034828003807201d501751201140309036101d40200c01070140f11a80900190750180803000031450302c4003001003441c01d6000d005007a40d540c414030818000c10029505001502610a0286007a40d07440018810fa00d880c0d20000307010704008188081080c01c040c1d82c401da180d51903040c41001500080c0414420b070342890816501c6003600c1c0c9504040c05668005508400c4404002c8108001c03403596114855540c260070780c0503564800d0407640c410081d20400380302241000004081000c203020700e81e02903400b0307140d0b0001d0f5540342d44190582350200c4940340081ca0105000d010341071025000c200500080b2041d08126 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 578501016 1250 578499766 578499781
    0x12050d0c090f0605160f0317161b05250e0109110f03040f0b040804380c0c030318030708010b0112020901030e060c0316020105041a130b100e0c03 64
    0x102454060f000030b1041c01700c0c0201600c5596031001c0501742e840106902860340d9482c2c05403080c4042150440b007840c00034009886004450740060b030129450756128001034046461fa50484113000042c5c4603401038864050300d07040f0320005515040304100c1d028400b980340c10168060400180c01030001d4a05080246412040010035034495040c0070398425a01d4a1f50300d06146480d0078154001c00241c2d1000401082c049454080d00442da014040e01000c00c008003450080c0740240841c80070138001e0050144002003070b980140842c4e11016080ba1600b0820f5800249590010703a8444442580c910001e802070909000c0c0c400100041d50090200c202d42400180c54103a8045e100c10b81d855010030305404c5a8425044058040100c0044c0c1c1d205050000e00e0001c590b0003125008040007600241c00c04c024414802c00340700f550025101c0e060070902030082d80b5000307800340c905642010030f00e10450101d04050f548501508506e01c0311103006d40b8091b04200e005074010540071a03a0014030810248 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 578502266 1250 578501016 578501039
    0x140a30050f010f0e07050616050a0f110f010212090102030d02180a0f0e0105061e0313020f1e090901020c0f1b060711040b060d0f0b03120703230712050d0c09 69
    0x103407101103500c5600c42c09015500414032100c2342d0081d080d8446c07180b400c01800b48040301a500c03180105002181e004d240b2040c401d0140d03010320090b0060b44008054030720190030070302030445840148151392800c00d0f10b501c0c079002d0380c101d4101242d00c500c0700d800407203440c603024508100078400b011082c41400e143c08402c0b00e003490305108450041c080011103071a003000742480b1007601c14003c508c3c2502c0341424240326007081c1a0400c12030207041021405030321032818112606c40007801800c1009503c41c81d105100081001a040340c10964080c069869845018402c00545070143c10041050907240c50b007050646200d107004501a40d0100503407030101c0d131004002050315409072004141681180c1c0400e11520502c188508864038040d1803680d11201c5810084500c1c1c0c0480440303000c400c103101410050b01c40e50714010045142c920f011b02c1811980d440100b11410340507990740c20412170792240117059000640c4180094030004401385400d00c2c500c02c2401e041d14034600b01d803000d070500319040032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 578503516 1250 578502266 578502269
    0xc01090f0e0702100e1e031606020c0307170706061406090f01021005070c0b0a18020909070510050712030e030a050d0603200307140a30050f010f0e07 66
    0x201c03000c1d0006400786008200384581001c0e6190104410031007540259115401030509101610714031012848203440003065410382e16400c2c405081d003107900d40d181f0001750f002844401e40360006120110200700600241c2c121208222a0f10f50765981503d088000c4401d2078120032040018141905010340300d0406032401c5036410345003807000800c0301c40117030b01d0b140240c3c00740d44d0010304040c00c000075664890b10080c0c03820720800301030019440721401c400544504400016815103000c6400c0054076015450b00e0300100405c041e20106911040400c10905a0201d0400803a2001814404011082280c0400c1c40200d04e0200603500c400c0c14655280c1c031950240508002c0d011808003030200d00c980c0700e41c0085a1000b0140a10a407440c40e1400b01c110004000f4800d00800c400054002101d007000408110000d00001c01c050408041c04440050b40701000891f044442056540546051946600c10301650081010000d41ca0506094401c40da041d4410141800c10504046800092060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 578504766 1250 578503516 578503529
    0x10902120a03023f091014032d04030c021e0108010501030f020c1006030501051f090f0f05071e090e0115030b030d0503041509050a0f061b09080c01090f 67
    0x4480c00c9210000700e502c198444449549101d4004d468683d254440020319078882d00707880881d043d074203103041552071071410010200005801c10004164000c0e1201250505000c039440d101c8001084a4400711680c00300ca04a010030f03a0031a0010651400303400c1103109024241e10001141130080008101040610805052544401c001054030009805485000c0340d80411223004440074020380014045e10311054a003946441c1c017280714460b00f845210307002c00400c000403c00ea0700c2c02d83c0c0b40e801844030402000b0030a5079035000380441030b0f09009580c0690600e0703440340c4441c00d840c02c180f1003100c04a0000070901004100800407500c030f42c10920b04641c0c51a115140b4030145034000d8000e4a03920000c6641409482c0e4048503064102001d1401a40039000c0d00ea081d54030303509900704460032401c001d006980310032001c0e0b0014903042e021510b4944a80c07070104018940d440305030000d08124101401260b0b080c04144031201e401c200d4000841070034a0411134482c5000302c8690400f001d4085c01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 578506016 1250 578504766 578504803
    0x2406010f0309051e0c0a1520010618090209070e030a06270308090106150c0b070e120c010806060703080105090907030c030b1504360f0302010902120a0302 68
    0x2806202003402141084c024a41e283d0100c0803182c0d103c50b80742d10100707144034801c40b00040c0201d40080f680540090486064544503201541001071081c0c01e4801e5009000d0340d902c130761001c50700307404c140286c510482d80844082051b00c6c00e07104018610200400c208100050070080c1e4580795400a01580740b250000d00001d01041540b45d414801403100092581d60300785074121308101540448050311035a0290020001c0e6034480954000307944c4007e050000240aca0800c500114800d1803615400104a0a00b403010424420106090b64807580e0110b88540144850601d03a580090109500081c1100c0c90381c07600a85a9000e001c502040c05610700502244c400124010800c01500c00a550050510205140d59151900b801101112040071120080c25850441d080c94007868208004010341c20390621a00035804460400301002e0300c1024010248400202d0502a5404080d030701030383c008241040301c0e0040c064201c002d21039019403580a2400100821380c0440c0201a081204225 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 578507266 1250 578506016 578506031
    0x3050904021b0d0203030601110609060a05090c0a0f08150c0f030705040902030a0b010f110a03050c1e01020309010c111c030e0f0d1101110f03040c030b04052406010f03 74
    0x401c0305111002141c8000d103e440d5081e2000f68001000d50b216107401d0740c51804104080c061980c0320034043d00c1c4040c1c1c90740401c1c0131813001401c076003119a015441c0740031200688040d00000c0d68001640c1c2c00107841c1b100620060040d814180002d10390420615041d415030305003c040100c16200350300054404000210100e0034a503c0742040701c1c02440f0780300c030a540f0790030305c0c065240007490b07a075007164046a03010000120182c01100c00b450a8860030780504840c000340d4609454551240c50002050302030030001c0c0c07054080c15040c1801308141d05000580b40c0c80c0804044e0f0849046280e8030b81808004034440d8a50003002070000b0845c818681c241c40710700e44880f402d902802c002e6a130150a409501c0f014a403001001401c21030010f116174030000e200c40d50000e494207d0701d038880c0317850b150b84041294540104807900150f41161185001c0c5001c241d581c1c60301000e00704140c40c12102e680241c0600384802070180e61602c000400740d80901013600305040007910f09800b846190040c1070300d5428 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 578508516 1250 578507266 578507287
    0x1b020a0f02010507020a0303080906071106071101180804091104030203071419030605040b0109111806091008150f06040306090c08060702240f011701110409050406180305090402 78
    0x256016558042d1081b0070454482c0317000760415004848a9440d40301da400007404081c440d050010b4088565809461580c5407144104c644112103103040c0e0947d03480309503c1c2c4c1d06c00c188500241c0c4442c0a40403807034a690800c0c01304010b450700300403100125441408140096680800c40300115100c081d51a01e8021094010980043c8128060444444031b4034002040c0041c2ea0081441503100790300d032104581e00d8841042c120380c0c8400e03400e00000400d2002541480b801e204a04450314020142d504150900000587d9080c41a0780c92000400002c140030700040078140344a854a802c46110381240710382c10106030240a85d100150001da03c0b640c5036000e0024030080ca901800646054a0340362603c01400f0f0760304c1c40340c006001c5001c45440c4072607030518007000496000701542c034494500c603482d08151006003030720203000d221155070350150030321150003d0700200001c0c00d05000102e25032610b810b005045501d00d82000515000b081500b10000b603100c01240c1800c1011100142c4035100f589 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 578509766 1250 578508516 578508527
    0x309030324180b061324080a0b0103021b0f060c070b040b06010509031005270a03030c05160614160807050f0c07090203100b070804060507031e090503011b020a0f0201 73
    0x3451941c1105000500c0000d05c1542441e040c292000c4c00c9108040c071500d842145a814170a10403940001ca1100202e500f06805800084003d84149005424040c00d0354500341140c014542d9000140d0000b0b050705003640090242a90100004881d2414100e041e243c0c100034000080000703000c0400880061403aa0160041d5106a00041c04507100748850f0f0902c4001018161081028072034208030001243d184a81c90802150342031014021440080e0f500340c001d403114242020520805115070304030145008a00c4036200d0013070f000800e103003424021b00000004042d00d041203880c0312903a041d4416800c001c0b929007041c500d141c80e50340ca518002240945004c0c08454203010b0044450000300082030341c02840c05410341c10b403001000c0c3c0d5100d0f02c02915101d0200000c080013000d10042040358081d8000c3c2c13000301d01a080801d00b994403030340c040041130714030515103010805038082400710b41002d1280a00006c10329064880c40000500c0180d56032041c0d840050201941c007956004691042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 578511016 1250 578509766 578509781
    0x100f0c110604032607020604030305010512031c06170102091f02060601270f1509060c060507050d020c0109141914100c08010602160b0904050a0e0d030903032418 71
    0x20044c0c106542841807009446400036a02500002d040900114881c0342c203903c3c01b0a0216030171700452070400200e034050356126041101340041581c0b00d00004200229110750f00e4204141b400040e03903425000c081001b000030010074405507484070b08449a04c66000220170707800c90000d0910034009501a510f5107000400b8416441e01c100344884009200b00405e5138050075900c40c0640070512444900781100c500b405031051400241c56841603d01007095039020703d4003d40d0034a8180d203000710148030355040e0791141c15002100c3e9074030205102840010702d800007241c9484000742c40180d0340703c0c012071200f0840000183c41d0000840c04200601c1c0204009400358030740d00b00c1441b044d040303103d002c0c0c0074000901c10030001d405804115885035001d42004803d603454100310380e0038040101c0a200044c00001c0080505a64484480040d28000c200d854112541079601050f0075000b40f50080c10b48082c0003020403034400c183c1d82031072441701d00b03e9034505848050f010103201080842c810000b030f2130f02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 578512266 1250 578511016 578511077
    0x80c2b0503181c08040b0f0c120d050a0605130b06090a0e040b16050414040e070306020a090e0402090402010e1311070605010e0603100e030408100f0c11060403 70
    0x909245409002c1c041c400d0310b0300100d4103807060061664803d8103c003504880101207402c104000e01c60000c20901070132103c100c400055051041c9041300d035103080503040e1412007c0e40041460307007400c1c2c900c2c020990b0080b590082400707800d107007102054803950f1001900403d43d454100c1d000c80c42c2c40c2c0740d054030b9600718000c0503200110307500e0015204c40041076a054600d00e50090005540000d01c20950700f0241c07042d41c3e540c0c581403410b4101c4c0d040c04032849a00e584940c8807811101c0c05601081440003079402140010780d1a09004005801064990700113101c541c2402d0410001d0780e1440310440c0d00c42c4d0207090400500242c2000140075030f81000545001c1441c5c01500581d440b80e01c0003034001244101010031070360362104a20700260404441e1194150303c100414020b60809402030f415100c98042181d05050311448900c1c00c000410700701804c0b09a462201820a004038081c070a4812014142240c030090301280c00da441e24802040602488004060003e24450102c15848880c81 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 578513516 1250 578512266 578512273
    0x40311011115190513020f0612011a0412060b030615010801091a061b0d031404110102070801020f0c3711060d05090c1c060f0b100203040807080c2b05 66
    0x400300c41c5e10814501d40d0034240c0c080e44451049500a00b0244200d030040701d0034014007881607203888170004250082864480d0324841c00c0c400011003003440c00c80da04405120b0b65021404510200600d89030060052808c0306107010518007030101c0c0d03004040141580c40104002c90b401e4030f059540b00f640d50a00d4440e03500076070001506034910b0031720302c250221000d0030010749011000c0403030202c05946401010b0700400302c0480101c2d000070454421104081c4040c01a02d01e01507451250908a802510380041a02c0c4000f440b508030791403c0c044400411301103400c041801000040103a280c05c0000d80f60304180111048100500a0710444200000720062245540704102401c3d800070705410f0b036030144548209100b661052420b00319264050845901100e0940d2480c3c84800160140c0080b2000607941c80049640719180c0a04901109071140c008540c0d40345040c4049107007401550010059803c03030380090009039180e01c40c0e00c150620807186010103044500c03199040c0100c401e0000c04a11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 578514766 1250 578513516 578513521
    0x100e0f0a1d1015091a04030b0c0304020d0b0117070b03010321030902030d20060402010206160e10090e0f090c0609011b110a050301020405300d050403110111151905 72
    0x9610801c1305054030364030610f40c0036011920041c42d01e58001c50000034030300ca61082c0015800b0802001541c4c0c4140020502a80d05503252195411401c080c0c0040502c0c00340d6080741c40714510100700703010040984c0038005103158950f40341ca0703c020324484046001c4110b40c0301d00341e580314425000404101d4000f42030354101007000744060000701851103100804c034510f070384040c1720000100d1214810f6406070042c0107613036584103100103840c1541072400c0c103001d0f000355a99465140c4032004150700700e0721346400c141030307007050721030303021180c00900032078092035032070200079400c41c002c02c501401900903144144c48900e428010795448610400d1040f20b826511804014001c7c40142c2800040c000d44540007695200c0d800d0600741d200c3c13405003d41103542c5494821b81c1c55003020046110703583c3c003518a40c84c0c03030704640d84908014401d840100000d07404038081c02400100071038100741d40000d00b40080b80c440b03503290085c0c403020741c000c106a0018a400004070520750080805502c04401c220400a92 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 578516016 1250 578514766 578514809
    0x1052e030504030513232403190e010606080609040f08071515090b04140f040611030a05040605070f020a060507210e0606010305131101030209100e0f0a1d10 69
    0x3d0340e46c41401c1946140d42c1001000741c102180c881200390190b40c1420711079039580042c0c2c0100d40c00586007030070350120f0306035400e5684028410700c60039414410012035070707511304000100120703800750030f45206540d0b4109200010f001418508401c0d035000e204241c036441181041c84403101030701c04116146061042c6d5007030041c1c0c0341c6004001d41d0f42c602001c20080421000780300468460501150b01c580e00c11011480705100c4d40b8101d40e0191007000049804501c9031049101c80c0c00641d503850143d500e078400c0c80100020360103400d40c000401d203005007100140080095890342000c901030038160317881c40401c0c1250303c111441d4100303200000140390142c40604080c0000c0469011f203d54a02980010561941c400e001d464012800100781986030041038607200091800d544111b41030550820494090303880300d446000140206031904a294103500007800b054013814020544550070780714040c08603140001920007040c2003107054007000d5032403619000401d406600940ca4244048252000c00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 578517266 1250 578516016 578516039
    0x1b01021b0f06010b18010e060408031903060503060c07061d06010f08011b0903171303030305010e15090c0a170f01170303070507060203040302160306020301052e030504030513 77
    0x300c541c000202c9926a9076000c1c0042e00b0301400c01030040562441428440c0c3e5803243ca08281c0c005802010149003c0c1c1d113440c060b1440d0300030440500c5850503000154541500340c4a010000c1100b5409405203107044611400944a00300d80141081d9650150410b03140c503580c1c3d9034001d0004001140c0965850709074500b1000342ca07104090380c560801403000c641181326104c0c6160844541c48005006007180e17180c0204490100841c80d4407841808250210400c40c030820300114001e440c006800d5060002c022940031f001080804d643d0906030701c0f5010341d1914040305034480d00c000115034a03030031001005c0302c20301409604000d0303803074100c010b200300300c546204110704a480d20100070410002c141000342d2207002c211940e00102e401400400081001034004640c040d1081c03040d507490350701d51003c50051802d10f400988415a0200050003141400c041c564100f1841c0c58810001c6101c41c00b444494501d411000310401d0f0721840030804050199044d1918481c0c0c0c188580c0c03409403624a000107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 578518516 1250 578517266 578517283
    0x8190509040b120a02010806120607120f050907050f0307031401381504081c0e0102030f0d0e1504050a0203060705091f09080f150c0c031b01021b 64
    0x105914080d400e0800c1d02d0103107000340304241d0010251801207045e80040d40c00ca00001c003026004076010000b085841c00c14003665108140f180c9a80c07400045e102000e008544110f81a101142d2903c4180042b1800000c0d22008888080754103840f06507492011a0418003d80e0000746128050b040381c040c03030b03d01900000e040d054403980c20f400050b890036000201a000800d00c641c10381c03000c0300180c05070900100090040664040092519035900314552414060005030f41105109207010000035500070030203130940409200a60415901d04003040c01c520496880403d51562071007842441c21090040f03482010142828081c08c0c9000d06050f070701c070301840320300f280302c1d000d6000080d06813405201a958403900c080d0111070f04560300b04d80444529850a07242080c0601250000b50036482000324084081c0e24502030240420404601d10010b41c02074034911800d60705000040391a074000040d24420f201080201d0340c80089042d14a009208100a070390301414103681c10750540400082109 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 578519766 1250 578518516 578518519
    0x100207081b09091603140102091027050f010c050a02030307030909050a14130c0e13060e0f0312130602120103120e01053103061b090b0a050708190509 66
    0x607056601c490b0f180791964001c000d061980d90b10140c0034030104030343c0e03c0c01a5404800b02e00051902041000250360035104c8440d40001604852014650050004801030307403240c8244800d131100c0c1803100113000f0354840c841190400081d254000300340602001996800c0703030050180c0c2d60301e811500300201809654046c0c00c40180c10278000c03920000c010b00c2038040c50103c840b001d92494503000c690075030a00d41c41e8030603500c0c03032082080403c041103c0807206003c0c54141402c07104070319141c42c24100f40c5080e92540300e107c0d0006c807490159140702004030355800040140f080015507400244444d03a43c00104060a0141702203440c4201c0c2e2000aa4103041e80d002e4441605000054031003103400396250b582d0103001400902206010003541010100d25402c41d140d03494075103d000262050f900071503802a503000d5100d0440c0c511003401400400c040070b5213441c051b0707038081c24600001441c0c03003003900c0c150070048001514014061140203031841c00c0c5942800d200380d9414414000c0c41d07604081e0545 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 578521016 1250 578519766 578519779
    0xb040303170108032a010c0503070e03150103060e0f010905030a14130306020f0405092a0406090b0310081519141501020114010e070905040218100207081b 68
    0x5602000c42074020504869000000314a031404070700345d50781e25501c0e48804400441803d10281d180e01000e00825284a4083e40c40f15101d2078065001041c203404101003d00030b4000343d03900010346c1c542c4002d45064039082040400d08400011205140c4092401c6003002d070751074500d4000c2002408001055812100e564407640f038400403001070094881c030312081c8450705c42c400f010030006601c0e8000d020028040701c845401d20f03036118007085a42208a440c03400310301c1034140501c200c0344217404d5141c51803070354402d0070b044c58240a000760920041d40244807035242d010002912910290145030301030301030481a1100c1c2701d40d002c102e2102210a450002d81c588135003107a04000346442c8260f403e42c4442c888002e00640303604161489a81080c2a490304554072540411038003804c00061500a0481902004603454040401400900c00380c010724170540c0100706028807415148800c2100180442e5480c030b00c2c0c00314100c280c1c82e00b24076911890450040b5580c0d03031620951131320002e00304207081e01c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 578522266 1250 578521016 578521037
    0x20a12080601020303040f020f040906050f100602030703120603140d020706020d02070506090a0e130b1e01030210120c0e040f020403021f0c02030115140102071a0a0201060f0b040303 80
    0xd4915000c100d94050050b40284005800300380040e6180306154000340c500300841103a900800d090345c1800c0c80654169448a05114501c06194500c0e98032814030340059440702e0419500035143e120f0391101404006904110b241c4126950f48000000c1d68485104841203010300440c41e12010482d04003005801080e1001500c0b070700224001310800c0c03003a4081d020345820300701080103c0d007007483c01039007140c05000007060008842c13803468000c040d81c0d810607400805500d0f00051002000f041d00c0c04400aa40804121a0b10740c200306041d26411141c848500070010401c541e182d20300c00f900c0b00c8803410040c0e40d14500b5000401c04902c01c1060b0b42c180114444020894160301c0b9a2200940094880103500500c039481c550321031422030240b5190b01c50450b42e800103030a580c0d600545070b0034040700610400c5140d03e000046603030810280090720b034862030f02c0c484d8842c006d00e4000c030f151100c40c0010005001071007988008007030311040401034017480d221036414130160030600084000ca0081041d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 578523516 1250 578522266 578522303
    0x40b0325230418110d03110d0519020714150702031605010306050312071211070b0406090914040b0705090a0306090308070c1e0c0b1206190b0904020f1603020a 70
    0x519a40c465004240402000e13600400c1c01028196a2070550400c2158045030104110a2114001c174160a90f03429482e00841d00342c10301d181482601481c159440600200480f8485404a40e441c071802c40c2c0c0d50b030303500b9004400c4d8200ca124511000b54180510000311403001d0300d0042c200182ea0003130b43c2c01c118482c0c8400615503900894409160700d51414010040010a440545065562285000d4900000310700066152000603000800510004a424462a944919140000c041c08402400ba451146403140190fa1010348042c0500b49074100080307046000340100c0b80f1144000d007012094594a050003401840740e203d0450015a500d804113070b244ac4181850380103540c01401041c49062490660440d81050b400c040740c44002e00c81c80000c9800d0b01e0805081e4100c52224400a2844c01c1e030104000e00d0089045510708214008080c40212030300307000da4a540f8029a8016030303800c407080f1890b000d805114031440c5102c00a201d90070400d540884c04507617061003102c600d8402e502e000c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 578524766 1250 578523516 578523551
    0x4140c0307060e120705060301030b0106030c030504030f0c0611040e0123033705031305031605041d07030f0b06030c0108071815031a040b03252304 65
    0x11504001960800d201c11151400c10304c1c40c0d480142110803280c40f030755503c000c5189134009038001e88442066070b00421242c1d4050159031303004280d510701000039185c2a076010b4103a08a5000101c2000b10011800f4204800c80d030100092141254042e500c46a90700701785e040c080d10074054048110034205a5100c032000c00180c104402e10000d025004c0c8060320300d0400c0002c140314115000b10b50340c2400c100031001202c811040d440c1d0091000e50b42e914941e80310755003164010780c4650700130350001da040d920050044c450101503c504880c0480d4404074450651151075501b51491030f00d004181001082143c804410748400d803056401840541c0d641007050340f40c0ca1750001041c00710f50008001100780f48200c2030014026810300341c0300d013016294404012030000c00030007400841c1e03031400000d8255452413150780d40024100c07424400034007450007194840c1d02c052032020510790700e904402802d02811182c44041d222040c180110700203070340145454200811740b200c2c00380b803030045030080300941c12 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 578526016 1250 578524766 578524769
    0xf050a060f0b18061608030408031f05010807180306020d090203070f08030418020d0c020601050315012402121c1103060d121b0b16050309070915080604140c0307 71
    0x14030419681c000f0828001d0366031000718503403071032004c40c1d41c01000101004069030250b8010b6030019268644610a10068500351402c502c0100c2000820019607138402c00199001074646840d40040d03607180c1003030340d0050807030304014001800032450b00741070f0f100360740000c40c01c40c003c904540c907055503a03400480b1145d56010703042140c3c104000c14811904044a540209900000300500d09451044554219400400d114006802a00c0100028a8100800c0035a02e1040751003952a524105503010001a00708043e40450300d11080f201c907250081c0000740c0b5050902e113403181c4e540c0700749002510f000c0e84048a107021030701d0704100030403140e006410340f8030a00c400341c0101283e022540b5040444201135042000b000141400c12000c05400b0f1000d90125200740c110004c1c40c108402d03102d56401071111760304c08125051003003050b001000100507045070150240040d500b04030080c00743c0e115485400290b8148243c100380010482d0038600e51100907203840640e00900d20360810143c481c000d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 578527266 1250 578526016 578526037
    0x12030c0c0f030503130f111203090d11180703020a02160312030906020d0609020d1425030603230d020d05040509090309180703151d0a0f050a060f0b 65
    0xc000400010340902c0041d80c0007600814140420710305650f5036286c2c0c1d40a070b0401c6984040b00035411410b400c00809017858081031001450501210401140c5072044070f000c090001c0b19002c1c5030001d035440e0401e181090141c0038000039124545440080c02070340c080b40705040144150144001120701c4040004107580d88166221448020001e08601601c02500183c8116500b0065843d80c030000d0320558004090406015032034081220100c012200c01040003035420b040c00b002c1110504d8165114045a400218681c9810440c9071044004001d03540004003a107100301c06070b84c130100e9451a001144d80740b0074115030303c41040460482c2c80300c0c040301c0c0c50000708034184400d028610380076107400d034455000c40c02c0701e051520400004544414920701202e411191100780101f06a040c007428a200e803002008030340c003d1410403040320400d040e4103541c0015102c407000c81c001000a0b0056500b11044440c00c0c040c50901e8806507000344218070504142000300800090741c0c0d04160281c4004084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 578528516 1250 578527266 578527283
    0x5250e060a1d0402041205010f0603021f03020c341a1b0d03150f06050d050c0d0e16060206010e0606070f1e0c17062403060412030c0c 59
    0x140080c20b5850001c000c41c1d00030260a0b00600c241d40d51140d1024100801841c13100444401d0a0f05000b402c5650040c0c0f000c0300315042000a10168a0b8814200c400404114090a100500d007000310300a00405002d0001400fa4920000303003000780e00ca104149042c0001341008a8500f40c03441002021548154886248813070380000c0d854481d0405461000c207803400311210711504001c800c0c1071107103021801020a40d6024100e50f40c107038150f0200d01810007105000c1c6143d0500c46c0140c03060283c080101d02c810344070000140303094441300a46584071006042030040c0028140e4403500c079820b201d200410b4007505840090064800500e882c1240c20f00c1d044280c9a071920002d100784c5074000c0109030386842020343c20303030001030a8403401c011003510a0741c110a401200e00e0130754a140001c0d8084461007587d4030359604a0003020420320307044480c5d100480b1302510205007042c8800c1c0110b852aa05000b82c1c0e0801050115541a8121030800341c2e41c00c01007100c4c010000d032007915040d6000382a458 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 578529766 1250 578528516 578528527
    0x109022d010e03100504120207050105070b04020906120312010e0a1a0906010c0c060504150504060f030902040608030a03050a051605040314070902040305010207020f0303043605250e06 81
    0x5002e404201c0c5404406000e80c1c85180d81d4a5114056400c15241101c000c02c0701c03443c0300305ea02d82c1844408003410092901620f0f081064a07070031b115000242c40640325a00c0040411019624028060808140c00040d691a01d01c0d01c00210a101400d101341c4984e20550000550040100d00c104002500d060040d42c55801c24a018401c420034000c29142c103201000b800017010810404800c002090503a036410750360740c24249001043c0c500c0e03c05400034060144021b010751038000e400c5c1c1103048001c2c500090071384510f00005014002d251b000b012140000210002110780c1500154400c04142001b4805034503828810310485d42c19141900000e1800e100a00c00504140d9101c0c070f80e81c8220341110070080d240d51182e001caa03ca80d0045403280c0d8009942c42c1141440246111641d10031405103041a01d800309420042d46d211062208004102001042c003080c1707030070f100d10f225011003c10020303403600f600040d000c224001e2510203031f0100d040701d04131070900c2800f030f100855001410850030030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 578531016 1250 578529766 578529769
    0x603020c120304060b2133060d0204060b09090f090304030209090c0306070c1a0601021e01020c060a050615030105012a051c140304080405120a0f050109022d 69
    0xe400240c0f080302c10544940c503940940c0e9816541c00300540d00d46010203907418018044900d041540c1d10b4205c650102d01c0e40002c640b54103110143c00040300d042c14280d1b680d40300c074001a03800203c81e0009500071b10300180401d030a031400000d01400c0ea010f541c000038589646018030000102200e800c22603074002c0105000608040c650240c00400403011a41c80850381c070f0000b403d141c0c040395204005940c50301d110b001e201d110b2095452120088503007882600304080000d4130b464a00f4000400810f21081150503100c1c254100c802c0c0d01c00000030340d01c00341090840303100a041c05542c80c500c00e018040a0400098604040301d040391416155206001501904803604c2c0d0720207554622441c080030441070109600388550003044c001d00d0010691264419030140c881d031001c219005441000f4405c11000030701d601c0440c1c0660b03100312159900030bd0400286441c10f080480024409170075407400704100b0605400c055010b83c401c60792031090107260100034030014001c0d1003000f0021200308201e40b4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 578532266 1250 578531016 578531053
    0x50601091409061903060216030e060c0607180e011712040608070305040606030803040f120212030112061d030703031a0d020405041425120503030a1512050a0303060603020c 76
    0x101841300d01c1c901c841d030b07a501d500b002ca170070402101c801010070490f0081095803148040480e0300c01201c44500348141000301c1995604010001030030320021141100348030340b01808030300040c0f4210540069541e15013800030304401100404030941d1003001096441214940706960999400d5581d0100e6650f542108078041d100140054030091b96803240440421610801903200794020100d0350907001841c0352480d401801c08590320115008001340c0c0c681d48503120b0460341100e0a0242c042c6031028503040813801004c3c241d4071807410f815113060380140d03003801001030725809004c0d03203082100d0140090764042100328980b8140d880031543c060500145001e60205070441d000d5410a80912200c4045600c0d001901440d148940c1d4061120000020701001e000054120107403409441d0300c699a403030b5920300001d005083c2031600c0b040c0c00040c103203140684500a21100c14800200c4119041040c0c40e400000340c281c001909140c0045800b030300134000c9130fa20710083c1e8010b0050420000c0345050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 578533516 1250 578532266 578532289
    0x806071413081b040501060c0204091b1508090c10032d0207050712031725090e0f07020723040504051e0c09070c02130504050105060109140906 63
    0x21000180482280c5603514074000015040300d0b001010f041e9510020301d1103602c00c441c0f400d44524109801440740942c89400c0c030a101d5811398011815035564504904c5603021580d02442903501480000b500e000c2c0c2c141a00c0c540c00c21a01c0b510f00e81e8494200304c1d0749541041185581140f4494034072420148a54089040e205030071694540c2c1e0b5114145003580b040039100c220400075000306030311081c02800c0c00b003003000b000718030b510030303020f00d00c80d176000e41000c09482c00c07070201c1508079001501080d240f00c0910604001c03c0c08000081000c0e81c00500605420301400d80300c80c52605c005000025801201c83c011310464008110261900108000150003900d0b0342400b614452290540b0740c0b0b0320f000300b901540c841d4000c0c01040e400103044264494100005910b20751001c4000c441c980c48880800744c20151900c0c2130149090306001003040c2c1d00c5ea408116071000d1070101000140001940301901a0300260f840d51603460b660040c500486948021041e400280d02c400724099160440d038648 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 578534766 1250 578533516 578533547
    0xf010e0117100501032f030606040b270f030709020307032a0806090705190306051c05010510081b031603030302030a0605090c030a0e0f010c030e0601050109080607 72
    0x41d9000d5000c004082a101500e200310040c082e02801c0c0070325038040c05801042c3c3c8840c552000d07000d8a8a48070641507000340c41c0380c0c102110000114015841c0e1000b00c030040d0002444013551030070728019000300740d00e8004000001a2855015034018038100510702d01c2194020020f1000d2030074100c03c04029030000c1d1402045c156200742d4903c100380e0001310905041102c01d110191160ac1020103084000000c00b06441404103008001e1481c1c7c01505a40401c0000003110b1006010880b00b03034010900794209503030182c00100f12303400e680c031003030040551984614024041922098007100f414402400b40044c07641041c90311450540c03441d0700c2c00e0701c0001c00038110303102c041508840340070954127600f0903000650004100724040010f03005103401000d0607120441d042c9820381e8201e074680401b0b4400c0f10701546515403165420300800001d80e615500c0d000802c00b040c61001d001e0002c2c103d0324981400742c09000300010301036014095100451b054032010f0600c65991070000c6601078031004054 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 578536016 1250 578534766 578534777
    0x809130b0307030302100c050310090c0e0a0e04020a0509070e06130e0103030908010605030a120806040914071805060d022e120e1b0d030c050319080a09020f010e01 72
    0x4860075034041010000950081d00640501050842c9140c1540c0503261841e0920400f001400515200b50048208649440d00005203000040c10f0448504031100b0451350305c084444404111144c1404801d4000ea00c01c80b8034034009a550700601450241c00c8411070f010492402c1180d48901b8400000c011240305c0582c03803400302d615030201100007a802c0c1c200303034001044000207001d008000d101d1030001e000304800808243c2090750b200000c1c002c0b0b60300c240041040c80008110310741c803150050b14006500104260310701142d1101165241410310031110156040e580c8103001c551284100d0b4021080544203c0003a040d035001e200c00380d903400201c4c03d061b54580d0780b032034a107226010790840450700307941c0c8280040d0340844904040e13482c2d40c03400c0c2e100303500101608000200c46d000141c0e03440c081a50910b0150925050507201048050307000380c810b010016034031540c101d14909094940c2d80b60b40b10080300380c0b216040142100e5102100030340000c003660002004e9030080340c4003043c030314052501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 578537266 1250 578536016 578536031
    0x6130305030408010b0111011b0f020c150d0b04181e06090516170a12030e0f061e0c1602061c05010e07030908090f010e0d0809090a09080913 62
    0x1200d266030b000c0d5100d0001a550390320030021941e40600800b020100080091103100909150048903183d5421a80c0030301c0300800c01c0b2400c25009000110034100010048070290810901281d41544545d910707140d03091070601a1445441e02c0e204150458490f040c00b0712104255680d0040070300d43d4030035544080c1220703400c0d41c000031350280a119091441103001d00540b240c1043c43c0482c52000b600700c0c005c103540e440b54803800300d00c000a4940c030340c03908040480c580880b03580080d4010701506404841030300a40303420b040c0700c410020b411809410780008401e1050b0405c002100d21040903500f00010100c00c002001c00c51040d040591005400141003524010741170301441e03d80901c1041d800c0d051915400108000389c0301c2d04c1c50325030000d910b04052201c0d045540c1d5250440c826060031a01c58004800d26490741e9110b0880c4a240682c0034081c02d56039285802c3c0f08001d6044400140d101d45080f100103290034040d401181c060543c84404182440310708010044030302e032862086001165108030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 578538516 1250 578537266 578537273
    0xf0301060506070309030b060108281b031d011e090507051f1d0123040b030c0309070602011b05092b031d0120030d1a01020f060f0105061303 62
    0x20009a840f94403481c000e241b4601c1c0500160302c3c01820346050180c4c090030404032100d11010812441060405282440840d0070a10002e113640c110003490042100c94034103c05030198040301c01640171800a507030880c50918901d0070b8884424206a020604c20400d1321050b00303640103442c0e03c0380f081054504ca02d81710f4020451001c2e0b41d078010031802c0140c1d1604210385801409402c1501c1045a1021451000000290164221048282c0300b40b041c1d021009020901c1c00a075000b03880d01c11441d0f540d0303062012071024290003d4480402c01e001d89140051aa80144503215203d048181c80c0ea8008401200994803604202d00312600419810701e0713402c00301c1205046021030010f4101307446400c029802c005066145c1c501100701c005280008003103560f80c000b00f4090b452004010664130159800b004c160540c01044c4071a1002404c14aa80180400501071103c88041c00c0e405c60310680c500c0d0110300e690791420f59441201015000051009040c980c0c02030104903641c0103181d0285030749130b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 578539766 1250 578538516 578538529
    0x72301120b060307030c081531110901090608010e15060702100504090f05150d080f0406021f052503090c0b0912060f060607060f0c090816060e0f03010605 68
    0x44044c00000da0b511003609034960041003654000040da03c042c408480507c000c43d000d25559480100c0e60041e910360000a00401c50b001c03640d00c0720040c400c0c00065000b4011480030b80010140c14003040d00148007203062445800c03018102e6600c2c0026031829103520110b43c140c48444d81c9544d4009a0420000000d13032070303007035550b0040d41d026964203a44a28104114084a0140d50b8074010542480d06101d00340909001c22800303281c007100c540007001d080d85454045407240700151501c4102c0441c0c001401a004541c4802d20b268982900143e01000003810040307400031281c1150071441c400008801c00108000b9182148070360a0000e660740c0143c941119201391540407084013a0f0014031450036041140507c298000040018125410402084c000c600c0006024500440010441d0000c0c03008a410400c0c551240c40c1c030802c14034240d004024282615805078500e03034031030f10b00000500a2500e0209046803901e548040c2120301003000c001303203180842d00c025415901c0703180104443c2c0d143d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 578541016 1250 578539766 578539771
    0x3011409070c0b041e0f0b16090b09010504050a09060303031112070e0f030703141b0607060b0a05041d0d020706090512010e011104080f070605030604020c07030b18072301120b0603 79
    0x64036a101d1a0f429443c0c004d41f8260014a01032014410840d004106604110f41505980b4944075460310351045c2c07001218075000e07a070300c0300764446040000003403500f2130782c0d020300c0660f406580c1c184004105c05500000c20b10640e0150840303401c403c1c0024a01c54400e0fa0302c1841c85a004105110502c0d1400c0041c2c80d2240c1a041031710104450303800d5507259a8200000c03410485101c6c1642c6040c03004c40c0010b285030107509009850683c68003030800381540c410409001810000b0004c09c443d240348041c1131104d011041d2a058988030354021083d01c140001401f404940c1c8990390303001301d24140801d10400c0788030100000542c4d034948581e403003005800e0082c075444559280000383c80d646441c80052400420888a11240d00301200c144002da03445800c5030b0340b002d0199405641c4680c1351006030700c0c08a280d80064401e440c101300b0310490910342030f02d607829090b03030100300d901c40d5868200468401c56403612204c1d10307829907151017503654010303011181021016540002c42441c08008100c296104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 578542266 1250 578541016 578541023
    0xa17070305030c1b030a050d1107050402070605070f0c0507210203011a01120c090e04020d050a06151707060f02030c01091101031a010c02040b1c0803011409070c0b041e 74
    0x51544c0a110b1380250500e501220000c500078040610742e0340711070b5111540d10703610008000c541c0c0080e240800d400c02c041002000050030440da81c480c0e0b82405002418140d846e400010301081d014000180300707403c02461140c02070050164035160a150920000071030b803551801400e411013140150340c0c01e1084800507500343e414562031b501443d00050111001c1401101402c1c54040241c48070343d4001440810f44200306141484c40d1142e0000031a00f07509980c0041c407603c21303200a036042040c079030843d01e005442c81600344002034403800d600305c656104014404503940044420401940315034201d600c05141c90044d21302c9d010f07103403030420300307450001c1d03020303545041c07040784080c0b003540e140c882c03210110000e940b0000070690420000b000b0030540d000184c4281d4803840c2c04a81075a48038041e1071034030803864404101500e00d203060b410a4009101d600c04000001580703000d9420a200c1c051311641c4580d035000501c01d070380d03581d080c2c40450180050b941950004480841e50fa810540c2c80f059502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 578543516 1250 578542266 578542273
    0x1506051819050301050105060315150c1b090106030b060f0d14011710020c0c0f060c010e07051e01120207111e040501060f140c0309062101080c0a17070305030c 70
    0x10070b018182507510683c00903000d5002007041105d0400c2800035079445a03002c5442c000070010459120a40b8000c0403030f03070612802500d01c810b80c0d002241c8c0341d0a11610040c0c45910300c503a070700c40058040b0381c0041c240c1078110070200321442803040d00100815500307080035000142120001044010440240c01c1403008078503049020540300d0042042205a00780500294548030110300d440303458244035501c00c0c0c007481c0801480c011b0703541d404054400960001008000740c020b820b44041e03440c40079200712070058044d40501c012840541b9100c2d010340106848015024000c503001400a500c0028103456a02845078958055951001c124491200c16a0201490400da1003000201e90040e4030800a021180100214854014142d11011481095000e444038040b40c1224154400e005082c1d170701c810001550704070144051401e0020740909141d07040c0907a20382c420799a4a40c8441c000c140d1200343d003001089a0954032041120601d8400c0c04c1d9075003145d44c1d80d202d0303241d600301507a50a41d540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 578544766 1250 578543516 578543519
    0x40905091011071a100311033c011b0804080d0606030504020103050a0e0c0103150f080607080709140d0813030311010b0103090f060b0109080d030c080a1506051819 72
    0x4e0b410358951254000c8180c5203003541801e980d01d4450701d0852100405011406610b003140c1c1e03600f4090f141c9810203004455607a1840021100c1b8803080051107001e1600c0c5000940701044e90500c6411400851452100d050b040c08100030344017100002c000710f4a0100802560036a00c1060180c00700625003501e000c10581003510000d025108010708140d00f0614004210540781c4c000911140110400e082c00140e144850110700445203030703038110b0341c0030401c01c002c00509000c00089480c440c10301030355290300c191030b4001c00300c07413851080c4581c0700d0036000c1c2440001240f4001580e90f08440c4500f00a5140020300780c2c2c0d0806200d0103030300650100c3c80f81c02c0c99002101c400e0040d148116001d18040083c0c03841982d645250294800700038104558a004040c002e0740039000410242032104c0440e4060065148001c0c040e22846c48034000081052011903810030803404ac882c008070030703940485091030030540200e403190444034440d020900c20301001e0b002ba4861802c01101144460100108207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 578546016 1250 578544766 578544773
    0xa110c0a05060f010506070f1e020603010b030a15140f0414100302130209060d090203010e1b01020106170a121407050708010b100818030f0d0c170c04090509101107 72
    0xf0b20305034040d9024004c100304202c000740c0186102000150b0041300b0740f50304400b2100c00b203040003248500075001200040080b8030a10320034090b505c1840e20101c18840e116141071500c6c0206441d03c22540f5401c3c8900c10a000c030b141c074650070480d0f10006000081d222002001c105001c003815112001040b0000106005600f083c6000403000242801c065251800f00c01c00301c0c02c0d03841a000013140c4d09e6901c1d904a002c40d902034011080d1044108116001c0004000844242001034544c1e18003540c6450b10001d161005408800c8500b0369100c00b9105182c0c803034451541c0300528241c40b408005005000e1403560604002a0000e42d000d44000d060450400c010395007100c03030800d40588611003000b00e5015aa070301c03d84044c0d01180102e401060241c140b49803504c2c50180c2c045507401c118000c00c614403017001316030000070030031166921152030801b600741240104006540400c40200708000501002030203821103600252001c0440342d8021a5000407001c4980c0503110320760b41e2200040a1051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 578547266 1250 578546016 578546041
    0x30d02070f0b180c041104050d201905060a020723010809210d0f0501030b09010b01030e06160c0503041716181802040608100c0c02090a110c0a0506 65
    0x1480700390300003c450103c5031819a0729405980120321036600d584c040c0040c07000000a5600030807015001c066408030341e02c0c0410f88401d104618038030408000c070540605290031655442001d80d40136106074001d0414050010a40c0010444410751003003d00c0060f043e8544940300348050000800524040300e9100010801d41024220807807541c8800303802c082540f200c42c00c40032031500302340c031895030b800c20641c01c01c020f451801311543c5680d207842c00000074440d0342d0f11207a1141c000310000308680f0100700e0065007121054403c8120a07408a00021134580c0d850841441d103c410341001d047d030142c00d6031307403d15552013600b01d06100d9021101400ea40c041c01c01c40210000a0300b04036449850511540325000811118141c02c1180c46100e00c09004600d40c07200d02806070054000d00450751500d0719203560307402401c2c02d6000302c0c0c1341948a9008a00c40c100d20080950300801006690322040d821a025081d515502404c0c00404c104481520300108850301203036200342e0281503c1d142425a1109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 578548516 1250 578547266 578547271
    0x10e010507020312130803040b0a030c18090f0e0f100e0703030e130b1f020607051c021b060709030b07090302010206072a0c1401030b060a0e0102030d02070f0b 70
    0x1881030070300c01c840040c2c1e00440c0300400101c84802c8940c50f803040c031002501c111115032240c80305000010300880c090030300c00c0060620300c0a5440034841030380d06010856080c11140b0701c031701c10140c9564041c13240f101690411900e1001c00d5901084040415850303030304145c102042c04507542c0c01190207445005e52409070364101d4102c88042d0944602d15180a0b0810300640201481682c0340010450202180e90180c10500c4002d00300c1c07903000b4120407085041c1c28000300c804000d4401e103000242c840748150100c0d4503000d14540c19100d5000c409100311301941200742a29041d42c0004401a0b09100401089108402c0b82d540d0240b894a5400c018901110203002d407410007403251810310150741c000610340d80082e014130304017980d8640016000500d06811144030301e000380005e52501400010060700003a24464a240712039120400c0055044800704040c0c00d4200c501440b90f000482e0080e00c0380489014180192407500104101e403200f240d00404086504010303215488003801039004e049903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 578549766 1250 578548516 578548519
    0x30a08041401110706141b0306011b0f02130605030c13020712050d060501050a170a0e0d020708010f02130b0d14040c1503050907120317100611010b1003022115010e 72
    0x20a82003415080d000d01c40b410070100e1070480c0010209000cae074860900b0001317826454810400003200b51802050001d030403001603220300e15020600b0003013891841044125075004000b800c04840b80401c0c085a5401c107083c60491682c00d00010380411000508101a502265101030369100e00c404608226000340d00964100b120510801d40203030342146034504030601c0700320700f281d50781c3e16000143c0140070042072000041c081c5050b10940c0640004170603060f03450210003841004400c5030140d04a00881d00554202d0802c014108a480c0303105000b80404000050b0109440903d41e0303114402c3c02055900300e8419140d4501000340a010003a040040a0940b0b01800507003010000e183c2c2e542c0785805500a01015003200808142c09080400310071062000d104005143c1700c6800051102d0910404020601c50b0422078080c14040c49000c0c08540014000c854955201070103c0094028150b000203410780311007260031042c5d2044007944242041040740b0f100030300d60f41c00100285030700021607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 578551016 1250 578549766 578549801
    0x40302030714041e0c09060201090b040803040c210c060512010b21040c0504110c030403030f0306050409140c06132c01030f0c050111030a08041401110706 68
    0x51005a40104000003214a400c5004110900b14400140145001c02481e01c0e143c51102c40d0040305606038000d00070162854444c062000d40e609004e900380d0394a504014201102e030341c0054000341a003409150098040c901c00c0a00e0354913218101c6500e800c50104019040c0000700c42d208010500786460090030403494946e003000a04004502c81030b8040c003400b20403400114604400c141e803c1c40e5590b51204c41d200741070b12130406040600710301c4114000c880c000c90400302c0d2001165100d004442c4c4540500c401986402d00e075850855403040c260418104058403240b0010b000e0f40d40380146c01c040d82c000c580c8004158040408540340a042003e03030b60042c10103110800080c004000d0000444134208040d00c42d254020105c180140008108100c06011010001c414046180300303000c00705104881c054165a00c1d5401035540000d56000c10078503074802c1040a640c3e600c11102d180c0c0007807081c43d03881311414000b181c031800e5400c1040100301d081408a00c8900717116190041e8582c001c41200032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 578552266 1250 578551016 578551019
    0x617070e03030a03110c030403060203010f12120305041112010c02061006090e06040b0a030f050f0a0b010303030b0a05120f06010b070309150c0b0f06090603010c0206011a041a0306030d030204 84
    0x20070340b240202c05424003819926508043e40505030012030340c40742034290503241e5981d100e02d00400290800c0c090583e4400c40100c5c0800c22107800d0301d0303c2da10680c0002d00410040d207001c0b030880c00380000a004680f141030001010b8226101d0f09207120040408034008190000c003448000e141240003448401c1a101c0e0000130001c07030b0f422041c08070649410b40c3c080da0b060b83e21138001c02e0162038400021a0010344404000003403003005003040d00300f24032034400c0c2c910b90300b1a050f000707603155107090303019010070310801c01000000d02179400381040c040043c0000d840b45a40307a001030b131036980c292010b6016401c21403401c581e002c424881d017030242c60274442c110700304401920000d10b1a15136010f400b001c090703103001044c401805100301c01c50b90341e440880b02c4120700d410243e007440c001c020f4404c540280d091101140d16442c0600500601100c29802090140c0c40d01c424404200203031b5a4056190204005c0032502840784100b80281018008403203a84e820300d0010b240c60580884030800030075205020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 578553516 1250 578552266 578552269
    0x1208071a01031104110f03040311071d15031e060105100813060c090305010609020d180f06051e0907080705090c0412210905150a0909051806010617070e 67
    0x1411054a00540340000c0c13420705e05061030014461540400d171051004001c01c0100f60b800a0740c40a200254019210320ba0b548030201116111b0b8003809560340c440382400a0164032407050b02620040c00101282c1c150020010000c1045524400310760346500214018001428500c030b140104250a2a10b0003032481c240045580010000500828050311070920710101886525400e02554102000704080c644d280140310096020402c503074882420301000340c0c2c4140c4072200d4103042c5508240000d880401d40c0d60b0b80c1c00100720050502c0c9003504016800f1440c04805860075100d03c0c00c400051180600300401281380101035407010b44540e00400c20400e200d0030307640903541225251b10700e0410340030640c0f0f442d40b12950f10070a91002080049100812294009258011140103403907101181f8005100d00c03c681c40380090480100301d8201e010000540c030b550000394004040030442d004150100c41c50b505003d400c0e0302c03100c0010804004604141108039103960004400c2c18403030843d210490 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 578554766 1250 578553516 578553533
    0x30203030a0203040f0c06081906140111012304020307090506060711030a0f061e0e0705060d0f02040f0602120a09050108100905070c1401060b031f1208071a0103 71
    0x92a081c5001c0e008000f04007080401c02040e81620350105441203115146c400007020701200701e6610004110705003c105420149104803819900500d808035031260302c02c001503412044008055000c0c3d940c0d02c0c24425079015071070b54040c6504d000c82c450300490401d2300416103032007010381101625034908800c0c007003180d564104031803600e03620415002c2c21041ca03500180c144581c0c400054050207040c0c10300d5003000141d85c0880c8408004104418040103003601c8241110170700040e41c0010741c055074081c001840c0440c0980b1101d00e0340400414007140c0c9090210a982041e4401c6842107031a4805224483d01440842051102c80f140d0030300702280040020b1150000c1d00c14a41070000140100301c0ba0500703240820701030b0070801824080c1d4200840000c0c40c283c91a8002c0d1a21600b041000f442c0030410b006031800c50318624001410340d01d54008100c000c000e0b008034035200d11741c5030b440000c0304501039411040c0c4a000340703c05074640c6040e04060004014811290021020343e4006100090412 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 578556016 1250 578554766 578554771
    0x1b041e0801140123030a23060403050d110c0a0b010305060703150302040f020c0f07051809101e0603060518030304020d030503090703020d050f0f0f030405040b1f03062103020303 78
    0x1080324068118140b680030104c03107203844150540a2a614031040c001c4980f28102903403480601c41c04003e841c00d00c0b1986403402950b000340082d004000503041e100003600441d2089006044042c9004c2c2141c0c41180307048400c400858502090704010001d0080c2804040d9004520781010300489054104603480c80603a400f000303104a03901c40718449141800c0d03055a20f17140922007150f0003205c0107040c3e42d80c0c800991040d01d100300080c00030b2800b0780315801d11003401011210000e0111250070141100a0402c8e0800d01400c6104142219089012070042d180250b00a4000080070309201d43c140d9540310107550038a0b20340d4000c10503c401030701c4903001c2101d601d03018034042d0703100e0f120400e6441c181130480d4000307588103003220b0101e0107129010581084540d0800210b41b65040d40404c0d094690102c0325000c24140c109000400840c100398101400f0140c0003852540705424030142044040e400c21070400c00aaa61002801103103414200303043c15403a03141e0010181c0d0b003a40c1c3d0003075136031000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 578557266 1250 578556016 578556029
    0x10e04170d0603080c0615040c09050d050a080f0a12060b120c09190518040309060e1906020105090106051e040f1407120c17070302031b041e08011401 66
    0x20362001c0c038844640c086000303150301500d110743d0b9014208880d03076280003e480100c80d80c00d8800b615039072854a03108100e00900f6985603941d8051031301081040c8510700d401d050f501409800d01d0500010444001070110742d803524009629124030480040008190001390b150729450304809219406090080d1181130b0686103458009980c0c605614000d402070021031500100908085450100351040950507690203450f2040c1c800c20850f807505e030086040d41d016012540458081c003484e44140c0103e1241d07880a401d030948541c06461740100241640d00c1200180d54800c144111078200780101c000038002141d02e44031503080d01c0070304101940c02c800030601c242c0d40c0d801e003810b03081402d03000160185041d283c03c01e4030785050480a0803004841020040f00d516050703c007166036000300640140c400d4003c030140e004d559840c109400a43c4080d01c19800b0702c441405440d0780f00340c03260040c4054070595442c64882d0b449141e40c403a4092a94000c0702160b410055080340500b5421203090446aa = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 578558516 1250 578557266 578557313
    0x8041508040b0f100317070614010b09090903070f0c03110d0305090f0103150617010e0103120f03140405030c07060305010e04030c0f0b0c21091209011103041805010e04 74
    0x50744244130055a0341340e03200411001021903035098820516015003030041c010305090000c2c0b04c0c550380081c100d9000740203088103400b052000600b142040092207030300030500d00c02c0307a00d01549501c03499000300b24030008869440c640d003018010803040e6451020f14520031398050407511030a0758060403501489070744a0080346401c102e1040d6038402e401c42c111a624452480485540f1000001c0058804039402c1d01100850800001c2d2a80c1c1d8500780c0c0d048030380100d000d00340414100c400300d03000a05042c00c40e00701a00d658050400700041515503000e00d01c54401103076101000718685007000c005911000c2030514140040082c21620011194013a50506c5c10f486e15101d5407800b0140703d541080050031154145042180780a0341e41d00400d802c191200b60b01d12981e150008189101d00300721829200c941040889041864810340907040840050614178000c1b00001621403554029500007080301c070901500708201291441f402e400360a01040024941c0707032903111148911526103140100341c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 578559766 1250 578558516 578558521
    0x70905130b040f140c13050c070605090d0e061e031305030a0f020c03030a1d0103020f0f07170906070314210f07180605030702030d06152a060906020403020d08041508040b0f 76
    0x123160303000300e444041e4003034020401410001c030495a503041e590300c91000b14200c9400003100b46450410b517034962440076010310340c0001191407010b5982004d040003400c429425845c40010f402030010348910020340e503800404485011001f40351001c1e41000c14041d420400c407600c0490b500403600ca04a000c1040300400d50000000100c0091007800204100d403100800d140320b100030301500600f800c90041e1510503001c80b040d40700750414420f075400c1d00e81c00041008442c0c0003e00800c20100d149886090043c18030400d402004085150441710101f0303131000c6020000580d480c1c0d03480c06d800c0512403904080f0b0303205074038002400101300d01514046c031002200091445108000b01c4150a003440401c0c8440e40c0d80e80811080c452400d0042c01c04560208007030003443c00c420300031441220356608146001c8a041c0c0b5580010160200150f0300c4c1502000b01002585400004c1a0385a03ca0114683c4c1c0f1031900391010210500380c001d0904002806040c000406c2410030380c2500b1000f04a103038032094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 578561016 1250 578559766 578559781
    0xa03080438010504360803010f030204060806010e1b1e0d051608060d030e0405151008060112020904150f0807050f03070905130b040f140c1305 63
    0x101d41e094032000c2426845081c10311810202900c00c1d100058824200c0e1079662038008000680d03c01d010801055890111003070084103142c0c8210312190449101c5420004c1d541d2200e6945602c240c00c40d424280105c0b50420440c2000c0c03003103d00924046014042e25410703e01241190a40038003000da01480250160000c0304402089444401c3c55042c2466100700c001d0f02080b160300000c800f289090720304000155410869600012070080c6503560500035580d4004018a0300c2030703448160200f003a4064a8400b41c1c80d00e10036280102c42d480da19801a4501c10f082002d001303040542b1034100440f603030074402c00743d0b00301119074100c40c900f042c0940c03603010300b2000c50020300200740d0b48405034103c12000100049901007840a58507003c05450401d0344400c10b205140a0011400340c00d544183d00411003440d01d41c3c001c940103129034440d034100c03100c592509105414196816501c4411005da82001c000d1484a11640c10703000802030914204110001a505409030710281509510340c40046d601 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 578562266 1250 578561016 578561033
    0x4050a0b0307050c0109150507110d181d16020d080406110702060304030e040b030f0304030b09071806050108150609041d0d0804110a050303041701090f081201170a030804 75
    0x180480200820028003241052680f008000c7d401e008001c0c500030110f01594800d07000c0c00e40c2c4048144c014904440d19503030491750901031080d0310781821700d201400b042411411404004841403d600d50005040c44c0d0b50103106080d220f0b0801040d9484410851001394019140c0c0d94040e42000c400101500c2c03080709000d00e849030100c000e5000c0304c00002c1004041d0032080740280e407201903c0801c0303005040020b041d9610a00c0543c1c2005920a110800000e01d08085141c0e12101260940e04d886035504600e09003201041d400b04065900c0e040144140d5a01c09000c560210301e46102c1803518000700d010a500c1d101e460b01cac0c240619158550302d8107031310484e555100c0c0c01e031841e400c0350001d0300d005200600c074100540e4200c50180a46000030614503000100c0c60030303200c00502540c942460010160303c8401142c08a15855407102c0c110b00210b0b41c0301160103407445c09026101e955000052002c400c40d40140c01001c1842415941e81e400c00300700041c52001150700d810044200c0e16030b030070100324 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 578563516 1250 578562266 578562277
    0x1509080d140d020c01150504020903100905010e121905091507050705062b1407050c121612020a110105070204020f030c07032606102705030c0604050a0b030705 70
    0x60039000203103048102405600506c2207104141e407101096888500b0401a40b10b41800703260b00d640400e408103401d510a5000301410f0317101e00d00003c3c120103420499401d02080140b284d061110200d1040605103840b004007081444a1404520303018825000641000c0c4030b0300301104c441e00c0458034404000042040c0005042c0081086440d070440d2921382e10f500d2200580510a0340c00b00c480c258443e1940e0081c0300e0320f207240e000c005101e992035283c12200b9800801d41c0301c0c0d65200340c4100008042c282002400549280c501c5581070103450b041000078501480c0c41a030466004a914401041480141d485580380c240791080c0e4940d8540002000790080800480810b440002072202c44000c0740c00500c5451301c00d4841052400d002c1c90032000306001d1030420380d024120500000d10500e00845000d4222a1508203102a100c0301040f12510400030403a41d0491401c6807804c1c006460200404840381c0422514945030038109808501c80900b82c1c41203200c01480032011510990240e010f40c2d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 578564766 1250 578563516 578563537
    0x60703020a080f191407030e0c060f0903070f0321020a0f12030b03070f0510022e06080102030f041b0501140c030c0a050a1104050114150c0d08011509080d14 69
    0x3005e00000208001d02c07080c1503840902180c0307891030600e03803c0400300d2a50b003d2100149620b00301000c10030b1100d0264048100d6603458010712001050160181441001a500401c0c0310140e07800b00445500b1003120002c9000150741c4800e40707a80c00241600da4039140c2a0348100d6102041000520960141c0746041032150715018881d008550700f00016100000ca440c1220002548440c005040e600d81800c6025030074503210100380240d0449042110b84a8100c140382c0000e4140c2c2d03030f29001030898109541d040e946004140074002072140b40d0300d90381e40d101511800b40d0b1506240c1070028007010a40a0361001c446800b0843c1e408942003441580c40503c140400c0e1103c24031a4a401600c500c07079000d00301c2e059001e528084045040c140f0403d41a18500d06440722070740848410000055801c1221181c40380040041d142c03145000d10614440d0911038035500a50350501d400b40d07060100c0d0350104010020b81c100300300041c4a0000d000003166506003030460445802141030200344c861030401e08c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 578566016 1250 578564766 578564771
    0x50d030b0105090411030405060c091005130f060c0c0b0f0d0e0c0909060a110306010f030e160b04081b061213050a2409020306070e0103020408100203040203060703020a080f19 77
    0x1940d03174100c503c000d6200d244100b0585405944100d2205098002c1c03558050300030b503034408145007640c080d400514082081400000c1056030b10f90322a52008219001680064070003210441007140402e512006045080203e6040500221a00c211030007007000d9000c12503200c110030f1900d1002072103100d242c10005401e861591030312803552aa100c80503229290f000e885c1120f00e0f4486002d0700140e0f409400140e443e050010f002d104114042d10400e280d214183c05080601c01c1460f80034080e4a00410f403002c1141d4507545403200f201d0030000d140145081390051015071064076070b1200c01b150070341c90b420b40401c0030039184e08500f041c0721006158010300d64400c0312202c0003404000500f08100b0500100d00700200b41d400f00790b035010755040500c020342551010740801d010b01d008020160040c801032500509142d541c03620180391441e80b452a0041d41c2c0e0010030301c0294141031100079441017003400c013903180c1340d40850b000b407040da4002c0401c50b69407400e8001c07406204640a80003404010240c05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 578567266 1250 578566016 578566031
    0x109082d19140604020307030605040303140405011505060906030402060c1507050d0606020f060a0c0203131203031d0712030c021008060307050a032126010e06060403050d030b01050904 81
    0x200c101071a0400410354180b50600020103440000140c0e0030700c41c1e0790140c00303004403902d0b550341d00004e171801401c110141620707901c08140a00a41e215144034074010310002c42c0c400b40e10001100c9112143c1c03c144e0107100d04010b03001694446c04200d079046541a210550389642000c0c00500b084241c0d100b9101500c0140c05002c000d6070300c40c2c06070004c0440b0140401281d0382e200000d0b6a01d45420155241c0c1c2c0c0c108a00054045c600d036484104044910b0040d0ba1404d1304035003104c10300500b990000c04405502900240a240d45886070f40551400400030441c1807154406259a40c400e91040c0458201081d0340c500405200b84020210150b020b8104648913041e80000f8100e040300700c1d0128040d109441c000151842c2101d41001101e40000e106071484004030b240c0400d400d04065002c00f880988107140e2a16a01c3e43c0a410080d0b0000b14104115410101e0030f40718000040c1c13515100300d1041c0802e0000c94800701d07030040c24006034140001c2e00d08511005a4090080c1d00a07181d006142444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 578568516 1250 578567266 578567293
    0x5030a2613030203060106030507020c190f180609060506070f060f051905070513050906060c0a03200718051f1715090a0f14101a0109082d 61
    0x10403002d40f403080342030724000c1ea03e50f20101c00301c90003141d50100607400b4400007007441c00c0c04080b48000901461402d0314064651401800494540d4022120403c1112040503500707510704c242e1015000c0140140200e034500030000d0002d026001000d0031408014080204010f4554020315840c0d50480e8103120f5498040f115140525105090380710140c107000008100030b00c00c80407109400c0000003200030841c1040d00380038100f08000c0101e07400020410009450031010025100e0b1148aa5540b87c16503400642c00c4502070950301201d13500794080d050901c8180559409d030000e60310402800074265840310a03000b6550f000f2505d8402d06d41f2110004200340300080d881c0c070313410080b442c102ca40328208240008043c20089404034401e42100c43d40e680000e44041c00d0842150040b54041d10451209140c14100b040e501000050300c0e03070741c0300c0e401110306911100c203000400909208042c64940b40b08182c4070002c032032501d40c01041108001500554111504c0c004204e64002c40f003a9841005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 578569766 1250 578568516 578568547
    0x303070228030633090b1503040b0603070b0301050105040b031317130b0414040216120e010e010309230a0c0f0e10060c111f0206011e05030a26 63
    0xe102d00b00529900c80d2030607103650901c130310030011045088082011071500d111600244103031096184d0056143e0821054004000081c6018a0055030079640b141003480c100342c80c3c02d140344e110070399126051004102981e04401920211440054030700d58a40e205c02d402c0c001d0f003130303000f0004ac40d04001c62043c0414080d29000340c4807800340050400607407602c0d202c04034401e004610403a40032000e0041030340820309150300034051a09928041e000c0310040c658600c1c0404654031100c1000680740742c0e044406690003244801c1c804401c0c24200599401e03a00c90311050a49000f98070f020809030003d10110490030495400c440f604a5100205243c40342c400140320102c503c02c00c04090880d00c0402d07503180080c40c40404960043d00d81410201c1a580e03a2501280c0c00720000b9403040d000d150211848030420705103011000a540a404e5940c14030071460700c40280180001290740040300240a103403000a0315810840d00701100249052824081401d0303000ba01c11000009017001ca003034501c800c500b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 578571016 1250 578569766 578569781
    0x7050714030a2d1406100e0702101a12010b030c0118030b0712020318010e01060f03030509030304030c12170310060804050c0301180c0f030203030702280306 69
    0x2184104a40c40d060420035981e008101000b4111820b052404511051002402d29010300001082060301071981c68802075428140400322003a0481d038200300c58040850b094a010b41601000d0381040d0410f1480290784a02d039401054a40782e460701c40740210010800303816040d08005140d0110030100628007070192000f040d105000344104150b040040d03004454041007048040e51403400d962071034071180030321840544040184583c07401034012101c00c070300045115210030140441c00848908aa80c03c568000303c540d103099151130b005101101504840300112505868055140c201d002c1c002410343c40380b54070042c03051403014000680b482b1080016a580f50091405031503115207501a120320344411550b205101611407414820507000300302858000d801031044030256050000402d01f1203a628800100c40901c48903280100128070084401800011985840c00c602c1c55012a0b500e011b070301802480ba01c0001d80300180f0000051885d00b131801d030304075030140d91a81ca003444070040c8000b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 578572266 1250 578571016 578571029
    0x60c09030b011505070305030c040305160e1e01060e01020c031c2c010c03180303230c0a02271f350102070503070803010e1305030a0807090b070507 65
    0x1500c000218804001001c1041d0f90f85921401e01d00941541c00311040c3d44000c1490821000611010012900411003a00e0f40352108a81c0b062642c14001000c0c48420300620314510307040c1c49595240340380742c071030304850440f00a41081c8030f1107100e1200607402c1441d0701c400107400d8820342d081c2c10144100300003000d480380c04a0725100d414050300d2490f0b004203d003610303600011755080c070726541d0a0f52084000d4001ca13802442c0c4224003000021000c05072034015481900052505680048070649601001144030090458035251640707040030a1f456000c0024042d2090b031130310415140e08030f880ca400490407043c00030b4020321482d1107038150604441c0c40b040100100f45989002c00d520403801191510301e9120501000003070348640c42201e5055000c003011040d55021300421002500800240003403901c1a0003440c1c8940c108500d610f070310400140662010142c2d144040003061021080790400d280300c1c505080e840c3d498540c02e40d034031140c0d80c4c0504404000000c1b02c1c0240b040105449094510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 578573516 1250 578572266 578572283
    0x809120313060c11030922020c100c1d2b080a17150f03030f0406050403300804081207050309100c12020c1c0c03090501030c09051c060c0903 62
    0x40088101d564130b4000c002200e0540c4100640c0907a40b500152100e42c10034118a5040c507526090341010598024040101e1142d10422003c4003a89041c01030200114081c0b030000c1c07412108004080e866842001880e0103440c982811500e02c201718403039480c9802c1d440ae002d81090000c6e140407070059204015200c0001e0a44114030920744071881654020410180e090500322512802c21204692401d86c0c00c0d0700d03202c10004210b0908641c3d028100030700c807d4071507a0315149141000103c0f00203000345500c4480c2204981055a2201141c88903100640d00d8411825511440d0040c03c0f07119040182551a000604104400e580710000307501c40c4c0e4a00741911054116028510192580715007130b0400702c5c00309421441c0446240d40940445100344007150403c0700e885c1e1041080200001c01d40d80082c80168880d4103240c0c202d503101004250030301c0d08104070910b10000a2485607103005242c411070503c01406019030714204040b0050703802180c101b024600c41ca0028141300f4091004440086 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 578574766 1250 578573516 578573531
    0x18091719080f072105010909260301061101021309022701021c021c020f0f030306030303060607080c0709020d060812030f0603070305030a030c1205060f01080912031306 74
    0xa01c540312041c0240c8080c210080c054a070000b0580780800e50b0300460380665034010b041e060480300390280030300038041300400203160522070820150f01910f000300b60040c0d881a00503c40808181000c890454486e894103071000000184d055000e4841c2245103204510f20707800116900c86030340d0040480001c1c40c28021014054411502d4030744003258007035030158229044148119403500326080c15107000344155414045091484c1000703544010150300103a00c00000b0201408040001d80803200400700118114603103580040d95910008088500501002c01e08030b0401c200401070702d40d40341c00d05003900c2840d501c51030054000c5d0400e500882d80c0c0c82c106400000d0030080898100c1e100303a41003500e01c0c03940e5a281c09100b4000c102038001900340c1301e142d00001c04136506001801c4146416603002c0f0350707101030381d500030101f0b40351442d000707595407418090001990312117121180340354080c24001103c0da03521011a0a105d242403041e50104000410007401c0503071110280c11440c4203050400600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 578576016 1250 578574766 578574817
    0x2030304140d0605460c0507050604050105040b07090f030305070201031431020d140c0904060c09061d010f1101020d0b04060b03060a0e1510112104180917 68
    0x3a41e211448179015643c2030b21012071178103d40c01c10072981c1043d00f041880d011295071104d10f003002c100c509842695446042c4002c00400242c456001503c500d001c20086007884406401810360380302c000c0c2401340010780241164004e070070509990300c01c014139014518000c0718134840d2107010520003401040201c0c000000c030020100f01480641c0141c4890b0030b00055a0304d41200c516002c801524512901d0103030703c407503a10307286d0319071146100f65008201180383c1800540b071041190000003e0002001e480c055911511030000444502483c1042d000d1045000965110b0098038080040d94000503a00081c1422500200380c40c1100340e90400886550712011401030009480090740326011000c1041000e10300414283c02101c01641100f039030283d10000b952410b2000d18520101c1c4504000340b0040f18203000c0031000c101400f0030319028400c2c892800c00184a1800340c0282c0c0004044c000321801101d0f0700404d65250720031707621802600200361040d40e0f60415129031003594051034415124 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 578577266 1250 578576016 578576101
    0x91406100e070917120f0a030b030303160513230a080303010f230301050109060306140417070501060510020303010f060f020a02060306010c0b0a200702030304140d0605 74
    0x2402c06665010080b0700704400d0701c0400e60601190815072095103109103440300c0910081070416030550103203986001c60000a0280c4004800d105d1203074200f031081040300200844083d0714403a451500c07981e50820030150042034403440d008081450743c0110030b2442c0314240c91600d0284001180c000000d10303502e600284d81c9100034000c494201c10102420032040074002e20340041812800c1030364028080349000310382180d03000da1043c8041d685540c0b0800c24031065100e014000b800c1c001140003240303856220143c898401c0d4000e0550000e002a20000340802075101d80c01902000f8088001040d414a000317503250403c0c050001c611641c04000103555008045801d8240320b15000b419049944d5005c012058000800c3d141c10b010f5180c101c400040d0300c0084840c4950901640010b070300d041c540012580c910450b02004c14400c0c100325070405a03500105070703401c0f550004600700ca55840e80340450610410345400500300b900705014000c0c0b0a207540c00c40805000d039440221400e205502100c2035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 578578516 1250 578577266 578577271
    0x1a0c0d0b0306100506030c12070518040507020a080d110d0911030604331506090b040e060f0609060307030204140a3f0302070302090a050606040e0406091406100e 71
    0x40540f07410000c0042c0e00740700d400742d5030002d0020017103414029450f80c607010651044400000041c400900d4690341110f0b8070a1842e0400155402c00c081d180105010b56601c2949001802924022030a02040c2d030654100c4100100305104d07050311034040703422401c00f4050b111000c0b10a0b407017030070350002d0504001070218400c036080004100c000d680740b649440c010107860765204004690204d4800300d52014010500c00c003900d894070702071007403900100800c40c00464028881e80c64082000b00402c0c41c030f080c0c4a98020608603a81041c0c50004800603c8a2103014401a08104003000b00140f443e007550185c000c464a08030301290000164041003e524000d018131001080803100481c17003a10701540181c0140c0a00300500c00044056007510180352825500710700603448104107208504104400e9031b084501410305000700c3c1480710020340180030310700480400c01a40d0f0001401d001084c2c0010302d07181d0700b011800f0701300948494141e4645004036480c08081415580000751130a440d0380361807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 578579766 1250 578578516 578578531
    0x312040c0801090305120c0a1d040b0405012402010612080903010e191101090e0a0e0c1302040914060307180209060f0307030515032a04020406210e06131a0c0d0b0306 73
    0x100042030b4202e03c14802540c082012b5003146c0d44511000c9181c603a0300c26580070b00046940c00c0303030400940b240005c1400412041074110390519100300485c2040708404484581d01c0174000342c42e1004400443e00400040c400c0038010312500d00180c400c50100052a00325900608101c0c2e010050b1000566407424140304240c0002c52120005942d4141584480244003800c4255141640c01100043d0605440005040e416078000750402c0018410700c40c103140c0490f14422490359140c0400000c0c0c640d0746030721881500d4010500e4681e5003044550403194102001840941c880003d0300c035031840c40d04119038100c0400c0c82e0001169051540c060b0a003d0210010b00a000941c10002e00180d07100340700d1840d54540106020b0840b00b82c0e15800500b010303044540d180d900030b01c492404030300003051600100c20b10510b8483c4242d40c49101041c61503001c03200380f01c07084405119142c0007032810715101d14a6600d078055400d11400c0c40f00c840081400701068282807189c0d1401c00704050300e900f82a0b4150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 578581016 1250 578579766 578579777
    0x1020c031b1018031d0a170114042a08011b080a091110090e04080d0b1801091d030a02010f060906120f0807050a110913050312040c0801090305120c0a 66
    0x2200103417090075050b0610b048510f03910201c1c48100b001c600d00d10365641100d02440b41c5250f5981d030400c824810410052001504440d45045c540c640d00500e2299a049021a052120340a10b0744c0c3e030605c40e075000401d204402040341e45e007155203c5c1805100200c080c0d001131814004034862404a002e1440c429410660404481c1a240100040800781c07005950a1112011000401040c2c460074944514081c091940e030b44d41c1070110002c12148244540c52003000034a04224030440000d01180c155212500c2c006001c00ca180c4600340e48442101c0e2501d0f19200020310316038247e1703043d00008001c40d848641801100e0f20340140c01d0549407240141024500340040c1d110220310690700c01111140501402413500708603490300c0c1e040c80c1c06a20107035213800d1040300040260a01c244100e134004020529000810082e50340c460b01c92249040500184175650041020b0000010000000f440e0f110000c200da10b0951802505541080c0c0203080550014400501012588000c55038500626a82c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 578582266 1250 578581016 578581061
    0x5030601050928030f140102030403051b150c07031e0f0804080d0504231207031107050303190305011a1207050c010510031b03020a051201020c031b10 66
    0x14031061803407418000f2010004102d40120500e5803c02c00070295010b002c0190034900582040703480c00c4e41c2c08040300140d03881041000302190344101500c29031441c03002c080b500f407400703045598030b071400549008400318040380c180000380c01e030400201102c500c03a031141e08404142d0607910203c007000300003203008242c6400020341050711402c440d41d4080c0c403880181c1d0600b40000840c0045035811902101c18845001c1160360a5801104164024400c540104104403004108ac00d00c4d000340d500041c140a46404800c2c85c0304003c0c0440c8010300030140480392145a10809041c0b440f44800695010928100010410340c141e601e000c0100c2c085111039a280503c060608004940c0007065001089030074011401035040070f00456009412011141a81e507013142449100e007018444d00041403203c00c041000140c882d106072108958088403244a202c1924081501a22403110070040e14000028001c103006001e501c034400c0030100c50304682c1100340e102452411a0112401c91030070f044035030325 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 578583516 1250 578582266 578582269
    0x90c01030606050d020f160c03020310113c03060a0506040308040e07020321012102030c01050a0e031608150403080c031302060711120a0321060305060f040b07050306010509 76
    0x20810300b035140e4280c1e480c1ca80d12550fa1f030701a6102c04400c6a00904088042042d4541001f5249003103060325010426412060101c4405110303003100e81400b481c1c0b0011402080d17000d03510100108040410042007891550200c1400d03a20880e101c92140e0f841030300200d1242846820f40d01503e91101506240c41e04208070300580b500010003800c114842004140950b208002000c210021200161000c650400409050700704800755000c822004880301e00c409a6000900707109041804e00700642e0700c202c3c06004860b00e100215800382c00d4071902a0140540d030422280008545464099a41c02d4880c5031182e00080c50135240940000c0c01c410110302c0b40c2803100001c6802c46e066030784446060b0619400301d4525009502d081d0ba6501100d00804a01e00b00200391040741c3c0c1b00392001d07052118281d0f60152599804001600d0700d4100c0001c198003120507a4000300140d40c0180840d403243c0344c50303407a200b203410040301c045407204406404241414003030b070180c1e40207030b40584070b1a0600c0762520 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 578584766 1250 578583516 578583521
    0x31401110304300309170a1209110607141b0904060507090510080711010b06180a0905040b070e100e010503060d0b0a0b0102011b0f110a12030203090c01030606050d 72
    0x12000d40d60f004248401c40003181e040e80ca4050b00500c191004070340315410b0701b40901803101041d80109003035420806000115407145142c039006d04502d00001d2189003500703040700d0b05241012426008440003075440e00340429103001c0070925031004104c0300292190145040310600041282c3c0d0449090350228000a09641000d0703400000742c40c0220049075034000003a00225600d84490201e003819041c00001d40c2e200c00000c24191700d9000a10468141c07502003003c070f03c0780c041d00a03111800440b802040f9503801c44200e0040060220900c56400c00f82480001d851040d181c4c0307004918411099241800c01c4001450381c84200d4071003031000e40d813010055502d54001055036500980704d002010005202c20140b900030340c0e10f01400551003040d600064211680f1064a201c1b01502e122a2440d150707005c12441030260740c501c2d01500920941c66518030301a0410b000800780a0003c01002e02168141d002e94882c192440032070f0203051684005404940303c81c0103c1d00002e1041000d1001441241c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 578586016 1250 578584766 578584793
    0x61e14090406090f03050d050f09061b07140304050102100b030304060302030a0f09050615010c05030306040902030307080c0a0c05040b01020601230a0b0c07060206160e01050f13031401110304 84
    0x8240c003083c079140b5551007580000705818214041030b800705500c1200020b45c031035980d00801103000c410301401c0195000d0354602c0000c000c1d19214405a10b868500700c2d004041c0c43c0f400341c2c80303601140340d003d003035440c0b5841f50001d00031030b801031213015003034030f00082ca034001c406c00208041d0203585080c1c01c0450440295000034031201c07211f17484d08801458940380d0b02c1680400b0f4040c101800300b908120f0394200c0d00340c2440440e0350400c0045100c0f24041000482142e4000400b110f00191201d058404203056001300ca40c082d10384000071610540b05400800c03080c4c3c109204a0b41c44441369122010841140c0c01146682c0c01640594010300104400c641c0ea1080354240012461401c07000c40002205081d5540040c20219408114040c4c0344004101c0d840103021240050500ca2510250b0401c0c001c000c0d4a14008000284015007600c0e409403044425480c4c0c0005400e540760040810fa81c071000e00b42c4011207401840c03030300c540403621061081442e01303143c102620b071071510307503450f08403c1706182c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 578587266 1250 578586016 578586023
    0x30406110d120f1e0c091208190215090102090f0d0506041704051309050607020c03060708130b0a05090f0f0309011112040e0a0c0f09170f0d03061e140904 68
    0x303e40340c41203001c00f40607a00900c221106008182c015480d900286006c0003a800400078292030038000380000c1c0c040c42505c4028040c1c0c0f903421074850303210314202e29104002c81030100c181d18060910035249410b4004001c6014280c4941064100c1001804654400354001071320507003220022a000a80e4001c00361120036080902c681015291000503440010710410392007250f60b50f030b03921810000d0030f00c580355004009001800100072003401003a110320300103200310200540f84000402c00d5101c03100340c0c500e15800299240c8070b868805c00800003810305440c1e481d107d108001c2c0702040f410b40000e1504207146200051820003c12034015500004c19040d10345090003190391591191168001500092603554003090403404c0c4211103408031200d00341c3c1081002066035268240b640c0204140301164090700480396005001c07540300d414283c04800d0b2100f1802880c0c04110a140d06030840c0301039503504621102c1c0b9030000110003920091920621b142541c081d003400d0458500a504194094007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 578588516 1250 578587266 578587271
    0xc062c06010e100e190609020f0a08011e05090c0f030a090201120509030d0c02030912011d01020a020303010b070f200103060f1503020f0c1015080307050a02040e011805030406110d120f 81
    0x8035076140130141e030030000b03103a07583e07a038040ac0240746560f011071f0041c01806400c1005c05580c04851000c0c0303500429001d028044e8503280c000c9072150030100100c800424200b1440707912410080921005810150401da000481807400c1381b030292072621800307004400c003000451800c01d090b040350020708207200001055000078051a981ea4440c4088900041c0170b08000103486049070f01d200c1d540703691000710f03006940e10610042d00c0407030300041200d0654a50030107141d1100d03802d1501300da02e5090060010214031240b10140501d03400390824803070402d02600d05110311b07a110010b044c128a2540b1a040d0a10140c0c440c0c41a40e42c0039600614180744034450041ca003001e204031b101d140c0202c440055401c0355840c00001200d14405008030701412419002d1407822025807030300c0740e945004d010003910a690310304540c040d444c025030010b10780c0105c40720780e0042d01010f170800d44c0d1a40c0045c8903250120300d041044d12200140170944d01603e00082c2c4504e48048001c1000030020000440300c04165076 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 578589766 1250 578588516 578588519
    0x120c040608010b01180605090f0f04020c21091e040e0724050307080604110408070b0c0708150f1b0d09060b0102030405010c062c06010e100e1906 64
    0x8949004400103002440004a2080b2004000412408803009034070301d01034114105001e1158410202c1e01940700c00c4882d4511203510300001001c0340404100154407c0c400544c200c1000008200385403c8502c03001510400340c00c60071850001e1041c108401e61010406184030341821000e041305c0540d550207000006c16840b41c0204619185007900803650790800322104203031400301210013004e01c1000f850030b2400d600b015840584211405401288600c0e10754100d0780044c800e00e8190340c0201115001c481d103080d80c81c60b4844041d40185000e0015000c0c03040081881000010703903130030f90700c0800a0224079a030303843c005c441007140181030400035111403055022a50400005003406d04034105c800141070482d032405001b01e81b8900045030543d0014401045240e81200c5500603440e002900070820200040d1080600f80790310080300c69000031166034000c8403400180741d87c16180d07826603110864895100200840320140318620f48003417500000341560204c909009104400c4880100d03849 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 578591016 1250 578589766 578589769
    0xf130203091203040b041115160311100603060608060f070f1205010b0c0d08070e0607111003020705060a020f090f210f0c010914040b03070b0c1c0f08010302120c 71
    0xd5105982c00e490004490b17040c0300c24020b2400003000131a50848404110491481ca214214002c5060311103074102e4040c90714003414001c0030303448581525002500c101405200d4401c6c000d05690005a8050b85040e2011842841c0020f44c2d40c00b54484a06110507544d403120200c80902c48900303e01d0820040007840e03814400c036802014060304a48468503199041e40642c1d038a016a481c1400b42000900c82c14881b015800a11024900c0c4042d140c055503500309080003801e1818030f10a0b82d4200f990350700c94040c22030f4107901500b030461003034003601c0d041c3c3c6890b0b510324240e0244050110203502d082010454a240082000605120251542195640421109500e02c0d030164070446150440001403007601b0301800f1005c0b81001c01d00302000024241200715000080c0000f999000700c1d541c0342c070308106550401c01c9400404500083c2030f80c600d203201050b600e40d09400c800400f0301c4240040c030b4011b0741c061a028694040c00e5900c02409070318580800038000210301e010f406d075004110200d81c25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 578592266 1250 578591016 578591053
    0x5131214010f0203011505120402330a0201060503070807050105090d0221010506011b121404060207032009060918030d06030b0f0c041403010f020406020a02010e0f13020309 76
    0x404000b80c0d001602d80d0f16003651079000b00010f1943c00d0411000304020b803514050003910503081501983c50b408a242c0402855851140224020650760102d00403003a5100510008240a440683c002d001ca43e46c1d82050540d1185240107116090304000c4013400385500c200054081d20070000d0200038900758030b07000b0692400040f04640d003510152030300d46442d00401d004040d0440c0c02864400d0088080e46000c01800c0c428002c0103215802061b9070006803441100510740d03c40c00c5020140d50b8a84d240c0001c1c3d40e407030651000710345000b500c070850460100342010107410400b02809405280e500ea41c10002c02082c000d000d000644c41c0c4645030103070039100300050905001003400010350780b81503083c5500040c0d0000c003001245401c000400140301ca0200030764044811070829800011190400603015207140049043d041c2d1010800060715036000802e001c0990003a201c29000042d41024003004621014141e60000118241005049140d0f80110b9100340040242c40803280e0f8000001c80c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 578593516 1250 578592266 578592281
    0xc1620010f08130606090f0203041719030203060d0b010e09070803031b090102010603150e010501080102091507031b030503041a06031e0a0c0e04150905100b030309030610060f0513121401 82
    0xb01223501208100410072840422b0b5001d0f00401802814500095080c2d00300480340b02c6180105070300400481c40710f84828854803461036110b01c1d90001986c58010700c10244800726420441841041d0300020303480d07004021a0300a051503908070003503d8054680e01e040d40e0101c0b121034115035a84000101140300d030000f48a003030f10611800700300e141d940c0340c01600350381040c0c000c0203150b4410000c0341915503a107009001d000017952101620b40c60241810744000341c802085081c95280480070100b01940036005622540c4103000a580d10f0f00302090741c1d81841821508580c00d0303032080e0100002220b003040400308556070202100d140107a15690300711492001e62140020780d109005010070050385400801080c2c0000d44c0411403880c143e00c030596201f841d10180c0b540c03d030b501d03070000b801600c00313104a58580101801f1520396040000380503410390402e20900d400100203d000902c0b0b83e10440072117164107a01c020030006d5074101416000442c0380d14508942d4401c18102d010b0036100c080c0603000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 578594766 1250 578593516 578593541
    0x702060d0e0c040c08090615060d1404020406080a0f020915120c180c0d0b0a1203020d020d0509220204030c090e06060f0d0b0c1620010f0813060609 65
    0x5102e940c00000d00c025200d020402a003445103040400c0070104000031615440400c039004095200c0c0c400001c00c1e51440b511400f1154141028403a6100241c8403403c81d01440c82618100b000a80e14510300d6150030000f9001403500d42007800c45c0c409464504607690700541003000081401280d44001004c0f08240704189120380c011458a482d0783c6000340a2512040300701034644020b20f0034412280c114030130060b52020742e6aa4140b0554141c40d8400424060020262040516122420081d640700680c8404000502c03c05050003c0300d441101501c40c110b6010301810300303075242803005001c0411020481d1228940c28040003020801e0f020110b4010101181c0003c0c1c810660090700303041840007009640511604007182c01e80e80c903000741c10100300e03070041607050303241d06d401e109a80184604801d00d020303001c420300c2c8081445940110100700f0003111a0320f080e480078100043d05c6003059500c454010848800006038003840382e90740310507681c0c890400020010340340c0020b00c0c21a41c1c902200d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 578596016 1250 578594766 578594773
    0x10c0201021e06270613030c2a05011e11010e0a080307080703020f0904090c0e15030c04140714130f151107090f09051e06070e0a0302060702060d0e 65
    0xe184c9101030100c524502021812500c10820304055924000a4180f0b62048050207110302410311410038807180300d621500f0404403d02c1070104e5000c55012800050031441800d40c005045e41c001c030908100e40311415000e055003a40000191204006000310f4005035490700e8001a003400140300c1941024424070260b901c1c3d04018070000c060080041070b01081c544100810400840e80e401942c036007007001c80d804110740700145814059005543e1000700808022418055022403035801c0104c501801d40407501840300b400200815110034030558040c801119011a00180c860b40051065200e2000d40914001c0c2e906a14441e04a26500c4805204001b203800d0001c07000f041c0d05412001500c2ca4202036a8010100403a01c07180d9610424444641c6c642c00766082c000b032a040f05001c6904202580c007415490781c0c900010f0019070030403108a005403400100301031b009641188660501402280c1860b0441c0e0a010440c0d2019005030303413042091005c05080c081c1c07401118050b00038000034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 578597122 1106 578596016 578596021
    0x9081e030403060203011e0e0915071e031a1e06160f06020406080c3c1603030b0a03050c130b09070906090501030e030d0f0219091d15010c0201021e06 66
    0x940c2044c00500d4040c80c2420f825520440c06108482e3b007840380f01014008110001c5c070003900058620f1b01441c101030450a00d00007800580c144100400d4204403240c81c0c0541d0710715002400c440b043d0300058103211465020b2011a040418210014104100c2a690504032001000000c00615030364228503603451052840094a03100c140c459079032100f802e04014901e039821581940030a08004135900b03581040d203500411260400c01a1807021500400c01510080741189550740c2c3e603d8420310b0b41e96135600191103000721525102c544400b840d15402610002042c0c0c011414140303044a001800e80001c070440311069018400003880d4117038003640a000f0701400d80e07482c140c040d480440f4480e07950001040800d549658100b0004180c0c1c0344241410100c044800c8c010b9000c990112003e6540500c0340c3d100c09510500503266043c005010346080104095146515540010103 = true := by decide +kernel

theorem cover : BRFrame.Cov 578417266 578597122 := by
  have h0 := BRFrame.cov_init 578417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 578417266 ≤ n) (h2 : n < 578597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
