-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3920
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:52.930017+00:00
-- url     : https://prove2.me/submissions/562a49fb-efb7-459d-8619-74eb48f5066e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 704856115 ≤ n < 705035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 704857365 1250 704856115 704856161
    0x6020d0f0f14040b030a0b100e0901030818041409010f1104060c1407031505090d090302211b0102070b120a050a0605030d0e1009050607140c060d0902090a 68
    0x100c102c034080100c04110301c110b81055110042c1042d1a0001c44404084c20350724202d10a481c501040206005403c5181a50b695900203010a8a00006120003010720002190011141e03181d035010312045500900100020102c0c003031200a110401e462022107546000200c4240407141c0c064280c69191060350f0714580703407903c1d1040b144a00c103400c003550490306d01c0302d50502040c414400d83c0002c601031406582d10420080c014801c81d00c0242034141c8a900564101200c540c100c0a440c0407280c04603800c4481d4070035803851101c150b4000c016030740e0340e00033b100c414100440000890050340d0001c1c0e084a070405e44440c1c001c1e082c2d00c10004800000100040001c5620700b5940180ba8130148a800101e142c9554a0203c3e01e4400c0100d0b03c500820444d007800c580030f090440285001c540103142c1029640d2a103008605144900c800c0545880c1c00008103e040c044100b044520800b00034185995603c2c1d0740390200b00600186004910414060020942c142110300500410845545d15042c001c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 704858615 1250 704857365 704857367
    0x12c0d05070b0a0204170303040b010b04080607030c0e0a090e0c0a0b0304080d181a07030204060c02090408090d05031c1e0e1e280c0302241306020d0f0f 67
    0x704000c00f01c9546540800010903448100956004209010f0000350740f00c0c2020b103456203801005030170540480505010410a050001039499045207150400007000d40c0588806c03141041240051500081c41242c0028040c14561004845510072810b65824541c0ba0041247c0a0100c0c450302c0c80c50401400441c001c104041c00400300303081c0e1140c00050445a0440c1a0740120001906840b100000282c904500880c0d48040790320514629045207407a040020240191032503800c00703802400c550000900300710b0481c040f600c10400043c401e4141c0039180c03800c3ca07666030181419030a41c00018444000420740c90003400ca880c0403a150005c0c40c904980c1e00705004240000001c509445290200d07102c07441c44050300020554460058422524000d0a145603203060140c07680f260030468560902041c2521814003d0f02d5048880e10190341041061040401d0003846103503400d03200041424070019414013000484500c0e40075107000300c0d02214251203201103010101c0101d02c100c0c0350101c40b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 704859865 1250 704858615 704858633
    0x5030712060515030609091c0c05010608190507061809050402011e050c010c02070312050c03071407030c090b091914130302060c0a021005060111012c0d0507 69
    0x20321104000003403400e80c1c61000a4070500c1c0074002540340c200000c10305c215810200020b86e8003804610050192450545411070001f501c10f2240d070800008030510803c0190a41008008040c12011102d5200710f07085060410885160211418420107800040305030282c111142c045a809000566003031400500201812000701304a0400402d070000c0100310744004082c080c8070307540c0e40e0707400c0d201d0801d840c5050031501944004012f542c0055020030000700c1c940b6201001106a1400c542c485a0500a40c0e26501901c4401017250151803e9413580c2c40001030054100d070b0141c610070b0003059803842800c0440380d40c080703055003014482c4001002c901c0c890720080b00240c0c641c0030000c2c0c8074080c07600300e8118240903205070b00140760714180a01130640c100240ea030000c81c101c2110740341140c0c04c0d078081d40c0e032103002021550054a03a070028070340717a00034041d21000380c54000003401000340c0403604402c0580c3c001900000320003441c403c59031800c0e0004152a0f154065110f4601c0c201c10b503241c0d6596 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 704861115 1250 704859865 704859887
    0x603060609061d120615090601300905030a1205161e0909020f121e0114030a2420120c040f030b150607020f060a031401060c0201030b030a03050307 65
    0x110240c01260b1100c1541000010320606403032601940c0d034460601000181031016108c941003102c0160f2503500440f20310101041100c9481201014400c0c04482c070001d40500c19000e4414000891b0302190b07280c01854038080424484000c106954035900340c6020000c4000d40400003980b030300d0031006164400300c50185584d580742172000c441a540c01100040e0ba01c80c00c0c140002c803c000c0b401d1140fa15250744d0709030700300403080035052a0054008400c03102250504c14a09000d6a211420850f03440c24003074040c04c00d41148030404010b1040140c2d007848240c1c22140241c080ca05101c04403c0350b103652101c0010303807000c1d4a0a140c103042e84c1000c100c0d440090a1700084440410000038101540120300005520604813a6418901700034089030811902040a009000421080e0010303540c0302501d07114540e00311042e03511148140c204074001d100d8641000300742c041e120300108409421850051005100343e909120303074412402031548074981000001e010680501c007050300c0d2030050400781b030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 704862365 1250 704861115 704861119
    0x13080a1206270e0c36010b0906030714030a0b0306102301020f0102120f0a02041a030c0c01090308180f030d05130c030804030605060303030f011e120b010603060609061d 74
    0x1140300307207200c0010451746040308494022280b814001491107403040c840c00c1d8080d0000c000d081250b162604103126071040c0c00810f446220000002100c0c940074284800388214180d00c1e45842e403414020741070007865601403162213031048000007281c81881c00751880039101c00141d490b1004041e10700c00704038564013401c1303203055028100400d55005c0b400d00c05000c0c03905200298070f03d541040c81410084400152600c2c18650042109205001c14102e00c0502008258100b0351f6030b5070761038503600403409003c2001070f4950034400110141360384842024000c3c001c0066040307280c0b44401045596221210181050307030000d111030503410005612480c2d00600b4442c4081c086d65850345c41c6a400700c55504119920400410144140451445059400002074008510314200294a4042620144500c02d148000c3d101a500b440c05908034100080c6071420303020202000310300d401000d1140c02d01503100020310300b5100069051080603600c0843c1c0203a11400101c0303100103070080080c1000b49d1019 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 704863615 1250 704862365 704862373
    0x110711060d0902060c0a1b0b090f010302040306050f0406420302061b12071515230f0303160b041b06020c040b0303040f0e13080a1206270e 61
    0x201603241c00005200d001d01d07017005488880200d1410000c0e03a440d40003540450400f0250034440c6000e554101c58090384121000e5011104540040303001e4441c50b000101950b0030f08003030103c0c01031041041c0703005c0c40c4a14400d00030b0032000501440e525040b4140d49021924015034000080f6505100020040c80c0c0c00100e159581c480d000302d013850b80568010044180503c02d80d80b1750001c00e01051001341001c1c1c601c54580042601d6425407001000f03400d91229075194483c0e40701d03044500c41d610060810f82c0c1c0907171220101d4140c2030319181342140d03c2c42c0a030030240d41c2c42c9400c2c43e0200c1107400030900100310000c1d0010b41d45903c49104c10040c4110740c4000c1d400c51400080012003122402002315900910b86c00000c44144011344180302e0300207020747d005200502c20308040051050550f1524007910905503036403008080070308a40c20700503050000005d20b4140ca00d51244400c9003100c2c49040c184880c0359500da1300b400001c401240140303d181b4070b0013100402c0032250401c8008120300e004031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 704864865 1250 704863615 704863631
    0x203011d0a050c01172212050406080a0b09040b092d1501210203030403021003050f010e070903080901032003091506060403080702131e110711060d 65
    0x142400458100100c14560004041c1c0c41003141c10881c0001240007807030501144040c00e056501c8031003000c1c0c880507040300781036070542840308080078501a40d50454400c0607a50242c1c0c501a12940c8540a031400064581001981242c0103005000c440c3c48003505c000520340d40c940f90a69103842c003400385202402a0608a0810007410b0b45645050082c080c0d140790b44203100d0030003403600784101891700c0c42c50300c1c0c00010422010120168002d00c200f0b11603640b0801039a1000034154455900000d5000d80e490381d00d003451542c1a40440d2041c40030004401c510703601c0307000603500c20714100c94610000c4c00350030080c400680f44402420398940c0c18180401c0085c200c1d5916004040700a0702c4409100c004010491000000c1002841d02c20601c6115107190a007800442c03420302c1103000c05040c0c400006280e404540b59400030785c06003091100d0401040000c161150020740d83c8083e20b03d03110b81041205859840307980102e84456500c840c0030130100f61482d044c010950410388004054641c2c032201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 704866115 1250 704864865 704864891
    0xc0703030c02030418060e090a0308010e06060c06010e01054f020c0d1404030512035e02010c06021303030e040e0d090b030907050d03030234020409020301 68
    0x50517040685c02d08085030260400b400c100e041d540042c202e99159010500607400721380c0140c0c00a0540d81e22940c40320581d42c0d4140810303c00d1080b803070303040098030a05000082100d174807403400781a1081191202071282e4418415510f609182c101c1080342256002c0400b101020004003210146419048104001032404001c1c12030f004032040c1142c942104011000351584a4a0010642c1c80c80500e14249801c645a0a0b525148000040300503000000454604150490b41060511602031001c2d8040b891100c000d03094080d6960784c0041003070034040c0001c0a4000c0c0640c01004845400c03084005040340c00460f213011901c01d0030707a68150b003042214543d0b41864030020255002e40c40709809040c90000f07100454030440c43c1c1e140960020802e40c100c2d90707070120b0340608464048192584a4441e51011414002c083d030200d075100300682c041c00b041641580240810391100a2501007843d1060b0307043c840c5140654090300200683c5125400503e0103a201c0d411b100e001a000160042017006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 704867365 1250 704866115 704866139
    0x1501050321180a450f0f09030c0302070801110d0f060503121308060702070302100225060807090807050415050603040b16110c0105031e18010c080c0703030c020304 72
    0x1001121005025413100d00004113800702c18044611040404200110102e5410421301c0c0e01c61240107440d509003081c80c1c05580c0086015040c035440c03c01401c241c03468050400c80546208a0250040c606c0000ba1082c061140214400e880c00c0702514084803515000010481610003603102680c410303010540c1e4404021401c010401d10524566540e00c2c0500c10a61100e25400003007541d000b1800c201200e44d002c0b030300c10101c80e810303900703418814000745099090041000c20b46091407164140721010b81c402d00e8540c4d0480300c0a80314410b1f00d031500c140466610401e4055800941d0042c101006a420260301201a480c2245010040f0701c2e107880024904d94070030346040d5140400721b018048580c548030040c1c0c1c0c00801c0d50030701413100d0040701000f503203a004030580103050000200c00164580e440c0e111b090400e00103150703401d02c18034183c0c014104030150006041415841c000c01c003250140217000d0300340114207044030f850604541b40d80481c0540210300510045000c140700005005039180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 704868615 1250 704867365 704867369
    0x30412050f1506040b0409021e1f03020306090c0a020604290f01242f030c0f010c0c020f0409080418020a03050a050105010c0209180a051501050321180a 67
    0x80703070342c05403030070b02c032040005695031209564425490069900c0c010b988507684a2903031945103803248000003110000400d000005800c81c401d0450b18100e80c40e4255042e8020352040004880309100303030722400d018507014081c24040e10003681c415004140032030380081b151a4840100318080e1010398050320081d4101106440c040c4000100000600208041d003040f80011001d502c502e035000c200c0e03070400500c04a00203240c0b1a15260225031802c0d0450400074114149121504582d80c5000d0340f041e203a5190522a20b048140d443c2c0000348105c240305160101d5101d40081c0404105100310080000034040d03040110740c070907410400080d04030f0400610980c0030008200c01612400e01000190507070f04024803611000d1f1420005000586e086880044c1242d016160256a41d50300c0d000c0500008840c1800c3e005403003502003400810000140008150140982014469a0b240241a0307507584e035400040300783c450a103042072015010009410000c4088401c2c118844040700822000c0300d1623 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 704869865 1250 704868615 704868643
    0x807090f0b0a11100f06050a050909030d0209011e20030313060e010b030a0f05010507080c0a0e040f02040f03021207050306221b1e031515091b091502030412050f 71
    0xe240400031f1b032800c03202401c01408143c413228100e2400180d01526440f6040d0108885a400f003041726003640320f0a40c403034000c4480c0180c601d4841c041070700030780030010391164100b600490080800c180900402628001c070008040c0c1041c41c140d035620390000e80b603654a6158650758070801d0308201e5408000c1e440009004004590000c11582400c6094070402004501880070702428019002d54600448048080500d40000420a10701c005000782040c0400e43c0d10060000c10b001c6490b90309114282d007140e200700d4066402c0c1241c0480039844100d83d01c1141c0d03144c2c00100c000343c0c6840580101000031810b1031a42e42c3d5050715560745105d4490b04a045044203031010200380a5004500140c901e0b00f0000690400040d18543d6051060490501d00c0c95200d901ca8100c480d60100f107248502c013800b101d003010701c890340c082c1812080c001204081075001900340400015149060400b9014081c080c0d80510325090400c04070748000e8892101c01c882510418458010034541480b50f11108105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 704871115 1250 704869865 704869871
    0x70c1a040f120504050a030222060b04050a0602060f06090c0c0609030703080708060f0112020c0307060f0b0a030c12030905030d111b03030d0b040605100807090f0b0a11100f 76
    0x1880c20407412089600754440b080c0710040100f030005940c0c03104140e04503581190404192001d04030314925800d894040d1000d4203003052804110221814081d10542d402903601311a420b942c0c210490380e0304000d41c1d1030701844040f0701c0880c82c0c074100740c1c07080c40d4841925007845250002c4089468a420f5080394014125000422444101036016900300d401c80001d2500000b6070400c04001100c4140300341200c0d042c40314601620788406980d0301941d402c240c0030410b4030746800d01418030340d003e03000005803522401e10304031030701426241903007044080c0e82e04800c621090700e0070060042098803012200707030706000c000500080c1580e0301f00305071420340302d29a03a00d08030b2011151002d0321b040c2030680050718801504d50a9440c50703c000040c0c0c0e000c0007906a000c1200b0383c400d008240280760300c0d002180c2142403051050940c507004841c4600450b080d0f981c4100b081d41d22100700e8062601d40c01104000d4004010b0030f01e81e948140c1508480c04580c070190b44400c406075980c4801c0724222000d0103030303941d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 704872365 1250 704871115 704871143
    0x2d14130e090705100c1b031e02030f07030305031b042603120411030d0318263103020604050f0102010b040e010b36150409030302030916030803070c1a04 67
    0x48406c040681e1451421844081c00c0c2036a40c0c0d804800d01214411301c4403001c984c103120a664040015030940c80c41e00040d6070820781c0300c0c100104140c0c41220b0042140c0a13400c0c81d000b0701001c1c1070494003100e00d414000007010050122681d2046510301241c50309120501c1140d400c2078000d85150f01035440389054510b40342000040c107042c417213405c0d080d01c14580303044000500000c1030707400b0303549841e8094200d140541202994030200d00040c0c844e0303070b0340420100c2c21142e01d481000c04801c100d1660303091422200c10b80104000c019081780402500048103000c1005079041100710349008010500003c038003c00c01c18042000c59801c2000d840290f9100c04091103141082140300c0140b145c0720300000e0b44001075440704099030303402c0b071940341c0112201c0c000070701001c80042c40040301200040045c8840d443ca4200240131350029201100e403402454640c02d1407406450714127003260744c800f0809045903a41d20095507402445c98094031100000300b0b5015081440140b0b03181b00d01c2c42a03401000b910 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 704873615 1250 704872365 704872373
    0x307030603030f2a02061309090c0806010515030a0b030d0207050f0301020f032a07060506040606050306030a0b0c04080316030212040806010909032d14130e090705100c 74
    0xc8aa064101c1840030070046540d5a00c1824401c640c4c0c4250751021408400c464030106940b4031544605201160f071004012407080b204c0d07005041001e006a038100c00454031004400c0d01e0364001e116850b44900182d555500e42d28043c0040d6501c110600000258000002e01203418025410100401600110b50030310040c6844041c03041c000100750000c504244054407801001d10000d481003400c03940c9201071064541e245038014840302c1d81ca14185480e4010751805c00050b1a0130389503a44220b0800c9d0f00410658824000e4a00c5414014000d100d605e2581c0c9400d40107000c00780072000942e904100200b4000410001002e9011940038107242c8107549060081c1084109031180401d0b40c410401006008800a03001d03040d01ca841000103411803444c80d05070758294001c5000140107080c1c84111402100c000010b070034030517070340c0c4440d004101c080740c84900b644290220007600600c51704084c0144ca014800030b030b52240165040310100c40d1110005202c0784002e03410500000c2018030004200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 704874865 1250 704873615 704873627
    0x3140d030c14091e030d05120601050a1b0c0f030b04060f09050330010b0909090d0f110307020a1514160201050706090c08010e0f07032a0b030703060303 67
    0x70850624011404030007000c03401040e0300c5030350390140c400e43c1804000b000d840b2860302c04080c4040c000b400c58465442501e000382c4250400074044c0303107141003140052681d5020300d040314041c01a0b41e4500400500000109071043c514500c10341d900c500120380030898414100300540594061914001586001d2825a05840000b028100c44d40d0400035201c001400000c1925179492044810a0a03045090408a5500300030b064032028000748000000d01035218500903d40b403078040e1007061095a510881c60b0b90f80081ca208800014800c00f00d080d10b061140c0707095403c00400c0b030309881c40e01c00c40d900060010541500080b40394007946d40480100c035081007980e14190540e00d004c40c03e2116040d035914a50100b1180071303040c00000070b2440d040110a41c00141311503403090354a48401d403144030040c0240b20412440d42d4a10800c0941c5840000c001403038001c0300e40c0411041d44d0f0600411f110090480e00c0c040e1960441408640450694520b03005580b0480f060780c0e001540c5840d6060003060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 704876115 1250 704874865 704874881
    0x301060c0b01120c0323030d14090d05090f0d05100e0f060c120a02130305061b0429070c091a090f0105040507090302030102040f300f0c03140d03 64
    0xa61a2603c0b1040000e2454918501181d802081400240403d4084201025000140c0060034000004c0c000c0b15011075a0048078020a03205004d2441e9036001d040d503540b44a00207400b000300c1c030305100d860010320340031048802d0b0b45c402500a8490100c0d80e91601d1400342d13401c6200c1680c0b81c440e800301010b58000c0040700000140c0000410ac9030401070307104001c0d8030a02c2810142d030901180000c5103898950115030b0400300c40c1180004c420340d83d040c080c2c0c0341c3c58150350b101c043c040010302d918460b201000545066503102c034840080300c00c4007912030320f030b40c08440b501c0b554102040c085078020511045014009000060380031484030300c00c43c0d1150316200c0c0c0700011031143c54900f05200040d4140401203064035429034000070711741c43d2403405444045055100a44c198000240400e01e40b00640b001000c41d08140c1d46400d4200c05448411031a1540d110249401920110035002207004041c1110b0011302884280b224151240c4580c04003425419070b00ba404e5105044e1f8000d00350b494420703500c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 704877365 1250 704876115 704876129
    0x14060a060807080406110a030c09140333040812071b060b0118180605040e0a060b221b05090a050105070507082b020606010807080411060301060c0b01 66
    0x251090404030098000781c0d000d0844420000100c0014080140702d5022200055175030042e136813108400319000b00908040f0441c0f1000070344a075030005071392200d802040608000203001e00200300c44070410302103842040315201c2118403c81c0f80ea0300320183d08590603004500411015580d02401500c0c0c50042d4030107099401004240c0071020440614a42480a4240e0040c00810349404020040300c1010054048071211180038034005581c00f45007010b268010380d41c4d50107124850750342c02000120381070b80d414524550002500400000c0860f402151680c1d0000e081015000c1100d96500480c00c062003030340400b41d910745c1c00c0e16503034036001d000e248092944d1400500d045041808100451984e1143d6414860042090301c01c0007001e008080150142a0443c0e0750301d000640c40703c9044842801c1103402c00980e45080c0212880404c00d80d1240c4810707100e0390f03519250f5080880b801c0c0001402581e02c1c6004d590079400340e030b070b415006500a03c2290b5407441d9075440b90030880e85a20042c3d001e00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 704878615 1250 704877365 704877379
    0x11401031b36060b030a020405010908030903032a0d030b030c0f060d2007050109031209080909040303240f12050c04110d09152702041d010f1406 64
    0x141480c0003a2a800100e1800d02e04114526040010020307106a802007030801001004000707035110a07901070720456001b40d80780305c010b03642d602e0810307240d1041e104042e0701340d042000ba40f0314002510a104010290625005000040040c00f550500c4140d0111710002030700c45035900c04a05d400c00c0703e0340b4034110427142034807400710640c002041c910806500c14409034071590240b8214029641c210141c2d0105c115031a03a40d0400c0c0303401c6000f0480d522080700890002c0a0700820a0f0581c03080e03806250384506914940b203504d004101c41c02a0080080b07080517207900c1d04e44203403040c0d42c0440701a05100600750801c233040401814441c0c1c1250080a04a024ac42c440000301d403001824400e01c01042e5070000e45190b55403404a0b09208202d03507910200d0501e1094003c20441c001909044a4107000801252010311a6052850851403640b154088400d043d01c016181607408071103941c140c031035000100d619040c103a80c00e6501c0a40030302c8110356144200c1102c5010040c400c0d90203042200c8807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 704879865 1250 704878615 704878649
    0x5041d090703111801080717060403081b0d0207050c01110307031209020a03020315150916111c020309100203130603020c0307140a020f090c0405090405011401031b 72
    0xd503078560061101400c503d140d00b40704009074950138011444902c240304803c002c1e41c1c4400381c1d0b5a40715041e20404491248581c200f80004001245550086030700d5602c0c0300d010344401407821030a541c2104040e0090f0302c1084070200340b148034401030100ca8030a02c080d21065412400141101064400440c0160002c100c41c0000039070048100d2003020000c0710002d000700309400890111072903504025003511840c0000c0c0d210008000110388940001e10000c0014120a41400719003d810f07103440c03600111807600d0401c0796000d9400c1254022640f41100c901c1180413142c021540c25800e10000135800000f290401030a011403100c900a40500007540b4000d4552000b0080ba001840f540081550100d040f021145090044441e841e4201036540352410303140b82c05030340b5520940b404910070b240c9202c840c800750a06044940c4a2644d400703600703080c1490002403100752000204101e885568504000c404403000b100214040e50003007008401d095405014130340f0000040d0042842c0007095060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 704881115 1250 704879865 704879881
    0x1407290105010c031d030f151e0103020103050406090503180901120506011203020c030d0f030506030106180b0301090c030c06140309060a090305070b0c03150d02060a11160605041d 79
    0x800f01680c1e040c500181c44500710180441813408202c046a418000d02c2d9095826442c0040e021001140410081d036054491490701038500c1910640d02c038981c101400108007640c041d50025910a0290a0204040e030150752001e003158800d079207030280c420104031f10844d90300340406082c2c0505810300389003030b920b030081c2c4a650b41c44005103e6030041e05440c04012003014800e02801801c000058102c0d036021400c4c1d2005030511003041440030000345080300150300c40c41c05020f400d04031484c4403d80b650051020404201a00e09110900e4240d92940e91a80000306a2005000150301400464114600702103004103203810010b2110384001c418400c1c094001000b03c1d415401c40c80380b80c4000341600561606544601404402405031a42c0300108a40324140400a520600710329109054a030301c1d01d000c0090301c0345110b00294003c41d06020b0808500c1c0548003129941a107181106d03d1b0401c0c00503a280c0303485e2142c00010000c1c5010030104030035184188000b02003005140c9402241c505016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 704882365 1250 704881115 704881127
    0x10c0e01110a1106120c250210050918010f090c0203070c050904030c200f060414040506181305330a020405120f0d020613060c140729010501 62
    0x7038050001c0b40703c01c801100c1590380740b0440c2e811805000c441075641c942060340350020340290105010881c840e2030714083d02948021f0013003040d0380c01880c4200034074001c2d00889241c0c1003080ba668004025110a00340414644403950080000e200c2d00c1080900b0401d807142030354a200d0f0940306540c01802800b00088082e00c3c0981501d40a03034084480d42e441b07081c11908051800300c054080c40250302c6c035000001d8904d0b58400c41802c01d03126400d0740b805110074007800e48250701c1082c902c507981c2c144088076843d1541100350400070041606540c24184500c02c0030524042e0750600300b226032407066000704441030219980b908a5402080e102c0c10810621206007400000340e4600a2204800a4401170081c1d054801a2001074401208c101299030625501c5840700d980c06240c0c86210880d101e5184000340207841141a2010005081d10342d07665480906910141c000034000b03598015480c09150388081c1003254007507401c08919007401402c030000410340d000c0d00c04044070303014010320080e40c1185e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 704883615 1250 704882365 704882383
    0x19140312030417030402210606090105300a061b17040209010306050403020703140c120613080c0a06050a020403060f0e03090d1e080a0f0207080d2609010c0e0111 71
    0x403001c00d9076550b6030706c000f5582c078424101c80155002101c03001e000b80342c000128a8460b500c1582d51803000c0c0d07201c0b030410980680b124400c003c900142806240d064000603038034241000764401b103910a124555030001580c04824401100c07840c41102c00c000340354050748002c054001c003d0b016203203040c50b4011900180301400051309064454003c03604141c401c120540c02141c20071486140809510b0301252035440b8000804e11030f00c01100340c084900c0b4003084c568000c0e9072500343d8400e001510f5031031080d190482d00c00c03454240105080e03200801c0c042c0c05400d1185944090042c0d035203086290410445002000a0071482d2070320708038520b0791400004031016194115130002d00100b541c5443c0c1030501148002860f0300e40310301182d10400c862030b8043c052004c2a511615080080003034101e9444821344540001c1d5482040001000fa004080504480400358031030300b640d00e20b4020408000c0c205407030300c0c200360390744071180502e00b58030400182185000b4a849504454a00107456841100c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 704884865 1250 704883615 704883653
    0x5030a0303110c07080723030a110307030614010f090e152a0304060e06090604030f0504050910080c1012020904020405091801051b18191403120304 65
    0x608031407146a1000e801c0c3c40384120920101d0394030903241d04c28251500b410303100d40c01010756490076500c1007494002c003101b9100c801400500714500181c8400001041c1ca00341c054241c0a01c0002001048160203242540d010540306506154505408030b1000c0c10940e000c502101e00c2d050309100f22103408600301404a40da81c2d042da00d140c8901d008125160031039180001d03c41e590003140b40b42c80100700040c6103d640208400c1100000f8011010740f154003c40f050700c5540c00040000f8000b80c0a01c1884941d1002407034002c1c1402d44406c08148420001d489400b42c0c0c610608003007000100c20403000351001000d03162480f00c00c02402001d009408548030b01d811907070700812164129105c0b541520014800280405c40c20704001e58070711144904c50140b01c00b80c2d42407c00144088038950300d02c08525180c120030a14010300084034007855800400c0041e40701c0120b0361108241c0380c3c020303000c4024213509450840c00313608100c1058a400c90002d402b40c528a070500821000c11002c0c4488075202e100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 704886115 1250 704884865 704884871
    0xe0a0920011b0302010921091701090212061603150b090607020405010f23060a0f110303310f080f09061b0d030b090a18080c0303071805030a0303 64
    0x54200140c48141d00344160b01502e8003000099418540d0540000103124001c0c0710700d000312500102160314170441401000041190310a00701b1a084900170076140041d411400010f9103a4668005203233000020310000f03450740002d0600022105007400d0000320511400e042000b40140d104103100d0790010700ca8001104404100048039859031012100501c0e4001c00401c125030b151440c18501c2503140c00b0b40c5600d03507490351484240284c011400c00d0900c4000b0310140c01c1c480c102c002142c2c41c0a1381c1411404000030442140c419a104002450040c4820f01c941c03c0021082c0201f460030610a4208600841220781c6100c040342d0905101e02101c0d400032012071f0344008072140840e8038840d168260703801c4103000411611010551020100c400003d8050b10a2603662110071800d5401c0e1307040c460352000035030000c02d20380f81150b440741d0110304201941c418013301d240c440403c150459540c0900f203400000810141c603034030072003440c04148121000a8402d046c0008a940d94603040801000d00d0f603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 704887365 1250 704886115 704886173
    0x11040b09070c030504260f0303150906041b021b0d151d030a0c020406080c0a090b01020c04140f060a080616051c0b010206060109120230070e0a09 64
    0x48035008550191040c00d1a0086c139042011082c91300b035060321b030b001006005e1b02403428035102c408004c81f0700401d90813a800c943e9081e0700c420044c0404024201a61165540402e01c01c400000c00e282040208a41c01618800c9075a400c494200e812010b480b5109185050840d400510312141d10840c0c03001c048400101c01c085c1d0126007411007120079403401280703c041100c01c90700d607000262070403082c82940c041c404030740e4582d8055540c840403012140e00001301c44040c0400c05c600d5110442c0b1440503c12900c1c5207d104020604484c216404001c1440301c00d003c00c64040710000000d41c100400356640d41659161000c02601c038003018100e84c0070300c42c0d2100c5c0103841500c280150f0700d500c3e00a000030510b111002100d400200405a5003c1c00360052100184c0f880d80529009000c445864241002200780d41d420041a144507803a580c107800044001401007500c0300742c00c81444c441c0c860084c80c1e9142000048044410002c04110707905042c01644000036030080c1d14000854503034040650403a07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 704888615 1250 704887365 704887367
    0x30503030c16050703080a020d0e010804020d060b04020708032d0a0b030c0603360d030905010f090c031a0c120414010203151207080712060908130311040b09070c03 72
    0x85400d20203072807481141004000d200c1e006c4010042e01103030317030200d030302840d442482540c0d40340148607414003007840e220000d0090300300b0000c0040c006220310000102c0c0902080002d040340c100d080140c5a5007004420003600807e84c9400c441241d5440c0020360990314140d0700b462410074000c0842c2c4c003031915210320f2041a2010070070600751500c0246426201d1800c450800c01d04401c002000d64400c221100c82e9000d038010b10140c3c890b0158000c0a003d20079192101a009010b407200100d88a43d46e510030a020301d4100d00c2556a198414100e00c9807152445c02d20704184101884d074002e1011302e00050045c4900740342c045031514a01d41e44031234a543d030345080002d030790100d20381d944d13199500002c01c1003280c41203406c450900e03100c119050022202d8035510940c2c0c3d90101d018044c0e80340c0c8242d0040c00300e80d00707007040504c1252003403d000c10030b1030181d55514900e0300300510b07954214107504403d00030008030141c460700d1614240d40400000b03007220002499800d014103e031003070000b4080302c54241 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 704889865 1250 704888615 704888647
    0x11d032205040c0507120c03051b0f07032a060512041505040605010801060f050a030303021e0a0e040c081005010f03270302061008070506091c1506050307030503030c 73
    0x1410010003c010b41c0a4681000d0600d41c055070f8103ca60310751031040444814000c1820303022142c0c16540301d5080844200200450024420a007412441624a0405968800c1021602a40c8122031501407003800c1490312004c040200051005180280030602010340d01609070350b054800d0701c29000803911281099445a41410b865a056a04110404c420300060790001c5048074542c034000c005443c1d4803950801a1100b6000700703039025202000c20804a40709401501c04001d81c018100c2400c5c0d070403051243e941d8015110b0744007249030106001480d1902d4070500c04003e09505040d0b10b03e1030030608401882186002c4d0a040c420029000d2451f81d2003507203c0c500b080c1e54001d181065644c1c03500d41d4000605050004c40040c0710f0680081d400090341c0d80c0301c00440e458035000b810f00500b4101008038035040010810f402030090a95440018420300000226030f000e0344494121403d405003000656090b070f00901c0c081d90085108000044001044a50260038801103948603c003440d900180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 704891115 1250 704889865 704889869
    0xa022b0303090f120e15090108130501060b04090f060f03020d060f020d14182b0509060304110405061e01030504080c3a0e01110a170c011d0322 63
    0x703200c401d8000200143c10240d0b0010145e070490b11822420b01c42400c140c1503104141909000480960100d00940d42218440e0700d26072068002045181d103900807a51070390070035404120010745031003900a00c0d800d00d1061001410f030300c4145048241c11500811030800d84004000c0119903501e03c03080b0445a1a41030b1081000e0101d000e11240440c950780300a210015560b15544c2000720110120f406800031b061b200560583c00400f00e0b5449241d005000e541c003070004c00e410b1000c2040301032426998400103611942c4140c10b01001080f0400500084403030050020340a00301d8508280070020103191210005202407a000c501070f655883c0c00074607801064400021813040070b403201a001360f20f009a80e11080d094103514211450000c0704488000101c00c504e01140d98480043d5141d40304404180078208a00111400c041d0542d4803141d079500990000c100700d075000b00300b20340803140a00590400308681c002e4030008081000d070540d01c038070540d42070441070b10722500c02a4894001d1009140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 704892365 1250 704891115 704891123
    0x11e09230f040605011e050f030c040e2a1308150402011205061311071406070207092c191a0903190509010302040305010e0a022b0303090f 61
    0x303180c82403865658225150103003188507180703a128109150a061140000b1198141c4d6007610045031000341c41c110084c001c1e80001005410400d030603442a05e0303001140034580c00d9010f241d44900d1700840c4070782840301810502022030000c61418015070410030a01840502101490340e6060301a000da036040d8442d840003109000c2c0d1800408226404840075200e035000b0f8942102841c071310f0071154102c84003164030171761005920311050b42810855020952400c011000d140c078200c241e881c0c0d1000c19442c9115890654020700c1001045e0358188100c0004002c585020701036022500c50201e04d0007001d05101044544c5c50800000d0200c0070031012013003c400c168541c2032071205041045000d0841104600c6044040307000c1048401e000007100d03003002030f030507030f40710480d1040e142143c441c0c2c07041207900c0c101502400084041007082c800d081d003c8494070000e02804280e0301c140b082d6220322030030140c5e400d00d240c420f4002a20707119006d03410302945440d00040104842c0f401c04547c80076030030054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 704893615 1250 704892365 704892389
    0x18070e060310030c090603120908030a0507080d020705010510081f0e1207060e0c150706091113020d140417090105190807200c0f040e1f0c0806011e09 66
    0x40c040003561b0000c0d003600d003e203071803007c1403180360340c1601d550b10300d48a62a03e550080089041281c42000034000742ca21942002d0300e414610f14010701030342c20480050740c0a035940c6090200060a41c15040010031040020308500d00c1201010b0300c640044122140420751910800c44400d4000c1c0940048a80c001110b05e07114102c40c1882d000400207000491100e00c01d69950304014906803007003001a00d0001d4002c0d02c2d1501c65503400c4040e0040f404101c4440148c1a4030070199500c4104602030712903201d00040c0c442142c0300d00c21094410500c8032251110b00081480081030520051201c2c90128100c0103a8074602311004941c584520401c060f09002e005c3c1c4013058a80c0e010031014000c0300b00303907188401d080d020306660741104440d4521162551100755808c2c46814420611440c44100803c00030b403901d51958803a003042c01c1103030040442c01500c454411510100c0c85071316140c50680c030b40b9198030318160700040e20784101212082c25408250701300c02c0c4507034880c01c0e544001d000302084030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 704894865 1250 704893615 704893619
    0xb03060d060c0c140c09150f1c02010e060708030105060313050d0c052e0e100c03050f01080604020906062a0c011101050c090f0102030c0a1118070e060310030c 70
    0x3d1080d03115480072602032a07090b44c842a084000900c003141600000c100143c50b4a4121131813130080f00310b03400c071078010050f01d90303581596a9280c2d0b038410040c06951003806c803a1142c400100710208004966100e144184041404140d011040e00e065501c145c46141e580d8803003415480785130790750641c010803030f203d07102522901715030011540b90f82600c56402c99902c4d0280041040207400500c0412000c0c0c94004c004004d44001d9400c03031484030350503005452010590000701c0040c3c400800300100400c3d203a000740655010f044031031600601042d40500854241b40d8005001c0e15405040d542c0b003160045803914151020b60300c4062034004541e2601c078203214100d0030a464001c13401c03140d40401c00f44e03200200c100e0018002d140c0b0925541014070310f00001c46040288880c0000c1d240c50444c40140282d061402080007070b0400e5500075140c01d40148041d01c20090458961030321080c0118100d028071424641002c0703d42540e83c000c658298881c1d54401c5400e001c2e1400c1c2e400501425082800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 704896115 1250 704894865 704894867
    0x51306050306030a061b03050a0506010804060b0a12231219030e0a05100c0207260a170d0605010906120f15090e07080111030708190e032d040b03060d060c 68
    0x103103030b1004070350310140700594274040c14a003100c00441d541c0d0301184500700010000b4807941c0c42480110b10081c00565802e0b2900207441070402c105004030382482c1c0c44010035110040750f40c046080141c50500a26030143e005e86110224081c0302400485a05d00c42c694140c803d005e50881400b103840b24049030303803188950030410ba6940306410290b810360b00d058100920944007086060582d922222080c030001c1ca80e9510715001e04e003090031100075029003071801d00024807510041404007140158141c4030065045100c0440d070099100a0500101c0942001140e82188400b1a2891040400a000401840703071902800c80700500da0300c10030600801160b013801130745c00802d0f65043d2404030b4002c0b5449001c3d69003220300d050050105407100384001446036108000d8154855078186245000402d002d0701079007a5400205000420b40001c2086108400c40e891940181c5580c03a0700008100c0d0308043c001c500384901c0c051020107410000c00660355444450a4400031303644400c0400c101c050b080b83c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 704897365 1250 704896115 704896151
    0xc0609030201020a0906051e0c03160f210e060d0f020307030207060b04063501050c3006060706110a05040f0e070206070309060b10050415051306050306030a06 70
    0x4c650080b4400110118a1a21400071390b052583c0f940e4000c24542c03030261b0324040c240c20103443d401b201d1000300b0022150122110807005020320640304000c8284840c60030401d980000c0500307180080700c512805007810b074007031040d403442c110948807540d5034a21161044080c1c20344d01c2e015810b450000084c401c005074194010f020660190a00300498961102000180c822901c078200d52900030340340200318031800d22a01c41e04403140c90b02c010301e11041003000900356a401c4a002341060800300c1e0444424000320a81c882c403044881314030701680004c0340d03110103000014143c90700a40c07003c60104200241da900081011501040c019100c0b00d502e40300034101d902074003961020a2400301c00040103008003001c070f030040c041a0094585640c561604074000d01401d00162006034403514602c0fa592540d0110801c0c0140c19070b2000c1e5254142032030700c155424249445006c0040c20085030281490104c1070005031269844c10f00d40e80e4035084006860702c2c1804001801051909036048244a12a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 704898615 1250 704897365 704897377
    0x140a0b01230d0e06072a0210170a090605061c0803090a0c12030912121b1e1b0f0513020c07060507061107021f050d0e0c1816050a0c060903020102 64
    0xa502c040e4442e5410f00c1490310300b04042c2070110203080d051b200324014038090003c1012045280380844000d0403039100c0c2310400f80c5c00d0b40c0c03909101755074004001c140043d50140680c45a000d40b02d850424604204c6044448034611020f800c440001c8040354100d6400d200000529410620b100e41e00381d1591034001d03004007a66821004a00e1000d03001031103500340d0711310309400c030341040c00440e000c195054190782903109103a0b6110442c1302244490000780c480300417400002e00f403115100b06188249400b40307294a0940340174602c501d04080030040c495030030068100341da805540507420454000d0074500640110940a1030303d0165034000b141640d0712401412125015035024450144a82c2c0c40940f94806c00502a400000300304190402001c1000f0742c482440061a0180c0342c100f0240444049504907100c040040d00190070240305031509084c1031404202041c515106810100140007140071035628240c280030f00407414050752801211650340e0740d030300803606000d040c000d072030024000c3d4010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 704899865 1250 704898615 704898617
    0x40209031b040b030106380f09040603020604150908011104030821041230020c0c10171005010f0f0207080a0803070809010507020705150d0f140a0b01230d0e0607 71
    0x107c032110045040081e0b1070410fa14070f4084061601522400c242c4445d44010754041c0c20a485100000058403a54010001403440952040c001405214002c000c00e2899018003140da05064400f0548052002100c086036400b80c2060b07a14900c3d0b00d0015541d030403a04d0410216881282044140041003484044820560f5910500e11042030b48900c1240341c12200d001c00c80c11150392181d00c040715030f4000d044015080080311409040c0c46d00094820701c0b031b10001000207601070080340401304039560740c5400000b545807600415081100003010500044d03013070010000c008034102040d41c000d10150000d4220359054401141150502840c031340d1066510b240000ca003a00080c406550602c5164040d4a05501410060740340c84200f002100345040b184040c0c0004022441404606100b00d5007911089600460000c40001191181c02c1004010440759400e0018010b0782c0c2c0e03480321400112081c0c0c01da201c0c0c4015200c040042d07080c0189280021046e140100c00101c4c420000b602074820101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 704901115 1250 704899865 704899919
    0x11d0a080c03100507090302130f0c02011a0103020c032b05090606010f031503060519020720030d0909110c0610080d020d080423030720040209031b040b030106 70
    0xf421102c40100c943c100c4840c030000e1504c1e20144014506501c8440004214600200e0b072000071041c020300301c40e080d01d501000350b95100c0c6d6110080c40050b03801074880d402403d04504008c07040001589a100780c0c114040c146821400c5600540040380d00e140c1c030038807004000c014a1a2940900341d0707070391003614100c2c046521210600343d0a8842d000b41c6c500da048003c0c101c1d10161030360b0741e0030010b4034016082049602400b920b101c0c100f0034610182200500a039140c118280c0005510804201c80c0c02440b806500251b00c0c10030070325044401d003c00c0311141140001e142c3c50741001c0f02d2060080328401c0c04240124000c2c412420b4010468405684200040c3d42107140601e000381c1c0d844c924122454042040c90000501040820303c15a41c050a0600344120740f2001c05507850560f03100c580100e40b10251010280030003040720320301d013511400c2640e045140042c00000647c0d40c610080358084000810300101c15141c855400c86040b41e10090000d010322a2070701c82140d4000c8119520000d1660 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 704902365 1250 704901115 704901133
    0x11a0f0f071505010b07030309080d0e1005010e13030c050102040509040615210f110d0f0b1b09090601120203012907020f281d090a050c011d0a080c03 66
    0x100e8403ca41c125120304039401d00d084100e580540140c81c0711101036510700030500564503628110300841e851007059202070300415100d009002d086a0040c2c1250a1580402003040b440e48031140107018610b405040152031070020f49006d601900c102d07004240c00840c200103000400c0482d03002441c01d003484110b00300b0150b4441e904030b00c9101030140c81641e24a1950741341c801085440300c0301880240554012100c07641d806d0003141c902d0364403403400c4501040e142540307028484581d5855800000440b250300c6c00c6c0c051880c00e1501070240740e0001e0b101d00c0d94140400d880b6030107a1105950b0740040d00082d51203681d900881c40071007001180d00306240702c040700d8000350034402600319102294020690089084c882c41030080404210721100700d240722055030410082c40203806e8000500301e001038600900e081444561209001a110400f543d100e0700c040800628041500d05181800786000b0070107200906007410003042c0f0903145030f0064580701c07020501407400f0a040020380400c2d022124030716 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 704903615 1250 704902365 704902403
    0xc010f02030a1a0102070618092307020d08010b0c0c09150a0e0105090c130305152401080a0e0a02060c0a0506060108130b0c0d0e0c0108090114011a0f0f07 68
    0x12086503c50058204034400e001c080d011304400041d0701040306082e04055180e512440823140e180b03030000c0c09081e8500d008051481102d480315402940c901c05030000b00103c900c0900f107032006020326840e200300841e4000b0b00a03820031a14a0480004042001508141251a540e0040f11441600a460008001c1004400464098101d076000750055a40d9600c0c4d82c3c0100180e04000c1490805214100d4004003089040022141000d8070803440b04550408000000d904001640044104500c030f510608131681c2244e40d590f40080703a807802003480710148600c10b007458049400254010320116030030008001c0018100c006038456012034003203854040064134407c408544021a0000e0080c41400044002d581d01d40c02180d4140781038180710442c1e1007002524a0b11485d1504d5500c04284580150780c451030b05500071030b6050003001107a00001010b200d100c1d0501643c1c4603400e040348444854a51041191600c8100500070b03511150800201459544210000d94150350040c142c01562 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 704904865 1250 704903615 704903651
    0x810060e010c0609020303070c030b061801060c0b07090f0303080a050f090a1209120602030f0a050c04060804081204080a110c06070221010e0102041d04020307050112020c010f02030a 80
    0x1100161545102c440c0c1036035070b2001428902c2401c9070180400d01c00700000607290444400035501c1030011103064a054010b0001402c040418051004240c000420080c0d410607185e0401035041020100203656240c002e4130b0b0b01e80b1990014403101c0c03400b0b2001041c954401e0000340264010642409240c40310449a461660255860782140e00240350080000d03660b41c00c0d201305002d0701c2c1000c14240d540c82101c0ca503000030301c04040d11927940002c10032000c1004001ba4581c403141c80c01c0200b1150501c1d104c04180e50245004050a000d907a1010400b402800030a5554611380d42002210301e141c00d10b04554150440e16401c0c0c02f0410540c10040310740d9000c02c0c55491040301030411414101540c08003c0c16010316410364030b051442182020111100703004801c1c0b10900a070025a84600e8280e06030148042d40d40144843c80f002070500c801a50089643c4040700d07000d2806062a58040b011900284149460059698680740700020441c40d03070340185114a40c0c2100411030b4000541da040b02d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 704906115 1250 704904865 704904887
    0x608060c03130c0b03310804150207090903091703210a090606091a01140a0e1207120c06020a1a07050409051302040b100905042703081006 61
    0x611014400210032001c045141d40c0307103c0c083c0c3c5103202c4042c0d0310603280805510941e010301200d0300d4050315240552035a0b140100d080700c0d02c0c000000d0b414044e1982065802a401440d005618680083c80c4c2c06108100741c5000d02107003001040064614034020305261503a00ca101d801c03445000b1004542d007004401c0d11021407240d1410407500e081c2c080c00350700c3c440c0c008050b80081d65aa821500225209105807405000c1c42d920009440c0d0000452480041281151604020b4806c25500541d4590301c1660448002c0c1e08050240f4a4004001202515482d0b40766025201d11200042c0105038045e246c070949000301c0d4280d143c80d4035404c080380c4501d0010400b030040c9960600080d40380c481ca02c840744d802030042c0f47c03241c2000e032908646c2c81541c05c00d803000c0501501311010802589405c2c4a80b500c5030743c044441c0e0300c210030003501c06440c005007072181c24422a95140e40244000706c0f05684100c5010600c805694011030303241c09095003d05540c00c2c0740480034500302081380b901034681c0c03943c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 704907365 1250 704906115 704906131
    0xf060f131e080c040203060d121107140a0e0921131706060d0c081e0d030207020307030f030e090702010f0b0406271407111204030b0a020711030619060806 68
    0x203e003600c00418400a540301800c115080700040000742c0209880c40b03046801c1d0011540d8200b40b1400240d020303450084280c008a21030035800da401c84156039540c2c50742c002c072162182c141c2c400760f54248209041c2691019480d480e1515102c0d1009541101d0004008429124a18040154840729150102100fa8108480c154000d20201d4050310b446441040002d20a242e1445801d072030315022400c02150f500c2c102082c80040c08050a40c51090161591201e8180f0f81141840c1031500080d0350381005120150900f213814250900303040c4030b0403000c0f09100d0064003440503401c101e07000a000701003018112449500e842c0c3c40c030311180f405000390011202c41c05600741d0015411400c1100e1036a1540d0301220b2a503481000082c600f100140301440390a0980b6103e07005a94001c8960400180c086402003134001007200703000250016031004d130001d070800d40046e2968203a00d041d01030b00b4051201c49500d480f411041040308000c030b090140c0c4048041a090211541c2ea0308441e541d0501560111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 704908615 1250 704907365 704907373
    0x102f0a030528090203250509010b0717030c07080f07020405150a06361a040b391b0301090206040303211a0405071d0f060f131e08 57
    0x595400c0c2900110b04042c00102950031451040b82c03440c1b25054115118503248003403410800491030003c4040317006200c20300c1c0c294940700e031543c0e52141e29264070100548001010002c9000949950f09544504d41e00c260f855543e011549400b220301d4000084c04c0348a00c0c2440c00041c14809400b0052880e00000b6082456880c2402d200fa510000103800c04048001d14900e581400440d035002c0b44042c20500c0090003415042c6100c0f0408090300c1303016600444410801040311074441c400321a0440c12042c0c0174141188000144841010348200742450070307601800305119502c02240340701140c100c4801c204103a0710700400707041c00d0318050f0201a602c40d100303200c02c1001c43e0240e001d6486100c044c1c40e10080c2c3c03100000380c50084509038191841c82c043c08880d2415182403030720070b441c3c00106905000550741018a2051000d0b501c2c41000d900500e0040c080c1422a10703144156062407854a074007684540d030844014072180c40c0791040a413130130175240c40c401600082601440584107150b000e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 704909865 1250 704908615 704908681
    0xb03010218060c01090b10090501050d080405011404090203070914010306030b0406090303110f0a0e0d20030304180213090c020a030e1f0e04050109050603102f0a0305 73
    0x10101d50010001c0f103946540300c814640000368006481e074881c003a408101800e0b0f80c01c1030000d1013100c0050300640d0080004848d0000850140d00913a021076601b40303440b003c05040f41c100c46086001c6e80e4003900d500c0307002201344502540c1103c1404103440d00d44140b0307840c000c1c0000044082c0c4005102c007806c007440b14130100700801c11941268134a075009040200310060300d0711914504d540050150300c0c58881c00710700c650ba500e9110200ca100342c502100d44811580064980c2e90311406002107207440c0307000a840d900020b440900507500140042da001700801c0080170b01c000069441081c800b08921070702d0340c010034a070105109040d101d44280e03004103603081203070341d0a070b030721618100400d0b0307200305000810f000c0285201c0c410804041070360f4803940c00d84401c1c020304c0243c0702c040c0c000800741d90529040121a44000030a1030002680101c0880e150790341e00c0c5819585030500d40724115840e0342c800420008900000140700084075541c040103a07a58820800b081200840180180340c001030000e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 704911115 1250 704909865 704909869
    0x10509060a0e03160303050301140901140f2101060f05041a1201020f04030c061709030f0d0b03070602030a080a050c03040f020619090512010b090705071a0106080a0b03010218 77
    0x10b051003403015048440d464009070491034214000d500c1280000e40000050000140354401c00401050590710030200354188604401440d00c020002c50050501c52904049a80d079200d444110300411305110010000940005018100c40d0190183c0807060a1002483e1b042c50b10a03074004280080e5800140c80203101008506484511407250b2590244440e08c0c4184031b0f0300062004600c03546071101ea05180c0b0102601400942007200c10a665040c03c1104403a03000c01152202d4001c1c0e0449a03460503001c4901004103043c2c010b4681610800b500070849a030004020801e5060680b110082980cbd40c01c0030300c061301d100310b9250098080500100780090314061100000d40c3c0300500d224180300201010f01040c5280e007918100188400c50300b00694140820500c11811400c4001c0c002c40400f4408202e120602800440030000005540000d00100c0c1e40010032908202d07012280380d50f0746100081800b102134072a08c056a20b4a110405685014805c031801d4094090001d0f15030020682 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 704912365 1250 704911115 704911127
    0xe06070c1202130c0f030b0301150b091207080606031e0703300804031b080f0724020307081003420e06070c03080c0d0f090b0a0b010509060a 62
    0x34089800c80020720b0700e00c601401ea07004880c0854240c1c0c5d0349903040350300d16100800741c91540c81518005d924090070005941e981e024400242c410f11040a80d40d03002c8640801c442c56170b80b03001d40032103010342c94020541c1e203004030300b00e4047d01044045604103201d22100406880e2401e10620b0f10340d120a0080000a44064030001005041e50990740d00c0c00000e0f00340084030b2061402c1c44005060700c02040105504814102c42e07441d0002580e002d0500c4a90762221030f407107600420364510700041001c008125840714031030050165040c440c10030511036103d08007e50800c1d500e20300490380b0800012520a14410140112a0001c040080c000c0441070441d01990148070402050030241111520881c00c0984402d50900c9100740002d0b0b2070ba080308100d00b00007002d041d003000c1103040d030070050206e58007400341600448509c1c800342c4d881d409044042c00030000b003143d0032038107424004100d040c0425519282c1c800c50104030140800301c0b140d0300445507031242e0614580d210405000803401244a01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 704913615 1250 704912365 704912399
    0x50a17030d060e0f18030a03020c1e030406030501051008150d05120c0f07080601170709110909060d05030a030207030908070f0314011808030903070c030b070e06070c 73
    0x19094924080c1d400760707070300700340c4907182c100840303142d410300621400908104000d07a11140c40c04507000b41c0c0308900c42440d00d901c100d4509000309600450141810780b003e02507001104005648080e00141d00d083ca1503c07504544500000301c3d140200000b064101428080640c40d920354330400c0d140d44122904000240044982c0d800001c7c00c0100c40001b0300400a04100c125841e0130203889101c41e424031880c01e02181100c08031f54229401c1040800300004015040d1540c10344418140c0101c1c590300d03072078100f89a1241080b1400e051201d204001620014104588180c0c0e003090955903540138441101102c0d100184550f000f0028216003900c44c3d80a40620b9210380703008130b40c01da500c8502a107002002e400c50004010000820800c00072528140c2c005540850300034007028412800703403600c0e000aaa00500361800000c00110041c505004807000c656000c06030b1401360307840341072a0b240c000c1e084503d1400f240e001c015501c10381c03a29034180d451680d80040d82c1d540950504948030010305441c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 704914865 1250 704913615 704913659
    0xd020d0e0d0b0a1d0f0d0215060f060f040e04030f030506091f030b04110414041a18010c0e0109061d0d06061d040201031d032205030f0f07050109050a 66
    0x3407075841a50200c042808582210f190005d1a808500070140d504001841081100b55880020f8002d40318a580d00e0740e9a00050440d1400582115440400c803944190a21003035a9000010081855040c100005000364081d985810040000e110b0030b4080b00d0041e41c00a80c081355000008000011408811b21181d001414006105969544400003000c05030f804a8540d60001a4503403d0b003800d21030070030340d0709505072054010b05003601ca2511801c1141000042980c8180c0011421f102034a0125140050000200840300b19003800500d4104604025400a40780c00000a4003901c609540b00c00c0b8801542c40d03866501690040001c4170f42c05e490100c4840e9250400052030480c0445441d0050b00f109448103514581440010111011a18840300d41e42c17400510854036900041a03c24220241001c000c4089603501402d51184c1c40c2c0e413001d6410b10070551080300030300000c41c400900750741d09030480e9010741d125001502c0e45125402556041415208104040c1d4180c104030305441d048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 704916115 1250 704914865 704914871
    0x406170402060f1606050610050a03091b0b09090106020102250c08160e0906070804030f020f12040e0c0f120a090204110309060f040c150519020d020d0e0d0b0a 70
    0xa081e122002d600003d003139035160100712582c0030520800d0300620b070b40000308513001b0011003503d440c090241e00a0040c41820155038652490400c44060801e15102690039525900c041c3d8130381c0c0e030307085550042410501427040500002240b50050003902d0080e00003180c00c105100e800301d44410b0404040364240e49811220100148404080c03042c01c00410102c0c018a914604024806000600160004065500080822101c0f592101d015074002d079042c5082500c2c0000032104914001c290041401140540762505d00d0b4469104d00a0084520441d09030782203903210980900103004000c00e43c50007000030003e403424000742c6104c040e4041c03c10032000407074410710f40104048606410340d06800800004c14080040000c20a055014001c46400a40d901d0280d8480071921740b90b218410701d0400300144281350034001d5059807989403001d0303948602d00742904c0000f503481d48002d245074050f0044003414202503128811082604802130501c03044110581c0c5e890b1007090000307020b10110340d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 704917365 1250 704916115 704916127
    0x913032007140a1508040314090f010309300215090309041508010f060501121e0b0409080331030918020405040f0b03060109090b010b0306030313091a010302040617040206 75
    0x4c0746407a00207420074554645107145410318001e40000c5025103281d561403014446c0104542e03aa600322441c0c04020301e00880c0c035000e40c2c03603d480401c501c80c2102146100000c410008949424614024a0f400341d080b41d5111045100041d481c003c1903d00612030f810401c8040f58034281908800071031100307c01e03268116541c90480070300b120101c2910340c805640b9184200b10303540e40804406a047c0900c0c1042181a440d00341c0ca5840d684d411040b031011503241ca80c050b445a645601105860703030401a1560b0303a1400302920005029503015060707001124010b81c040e000c21806040d19007079810388a101c6554245220310007065050510403105617020000410716488074043e0400e0305510010204181c04c13060205801c08005802071b808080c41c0074050030100f1500c0070078904407400c01854540c0c82d21140c0201c0c0c1140f10708203c00342008598100052181403613400403c0108130380c0a109859544000110203900c11071240c4000511440c80d00446880c420645a40003480206180e00d400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 704918615 1250 704917365 704917379
    0xf0b3a021806130612141f09061a09040b0901060308220509060612060a050604030b10061419020f0d02070f1406120a09020913032007140a 61
    0x14000c080c0c10002840c00010700c8001c1c105030f0480103241c0380d044024130506003030503401e080b58000400040c1c02054941501c0403442801e20403101d6140e1401a000c0381d21840d01780300e80c09001500421548e1500c0c02c4602142004854401d000008004100c0400350b01c66440d00e01d000640030300860415540c8000001c0002c3c002c0e4000c0040c040d00c9881e060b1008a00149501c8213841c6501041c010740e08074041200903502d08003101c0224041c581d40d040c01d9107405001c5050681c0903080f29800a2001030084144541d2504881c8034844030920b200c580c0d52160700c00c0340c40d00d0b42520b140c94110030901408048045603021410000c1d403e03c1100c00d0000280d0865250103800c1c032203c03000d60000f880600c12401c1d000451800382400044215050b8511000320b10103200e801c820070100702441020550031840c1da0002c0c4426070b002441d0340c100341010380004804603040b400440c0407800a00d40340c034942c0d500148005404440c1c0010304042c51500c24075002182c02d058185078000000c42001c1000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 704919865 1250 704918615 704918629
    0xd0e040501050d150612030e010305061909020703030209060a0201060515070803010306020a0507060f0b03010b0d0507270e241009180606150908030304120309060615030f0b3a02 78
    0xc5806569090301070383d2050002b604840001d41024050607200303c010030344001c2c91402800322205200016038036500360070210000d01401c88015840741c0001540300105070305400100a689c4c08480f00480b44a5071540c80c00a072040c810001c00c20340043c130040002c0780c541e80c081c118070992811704070b11701419507503a90100c0301184420002a66900011016401c3c00d104402c1c11328819905416001032039101e05680350040d1149000501210b01c0ea1503022a0403075041000c810120802c4c040c038625000d00c2c40d110300c2c3c4003548680ca8040c040c500c5800d00f404004180c055181925000e9140b410400400050000101340c9034041c6a040346000c00200144100802080400e01d110b03580da00701c007001000c1001c2070740400a2544148180401f007511410601203c540d54100024800c035245004809050147c0c41020b4403600c804100e124075425030440f8103141c610207810400cd92000c0e04211910014214061340741151142404a4a94912028500b6881d10a684410003000d500140c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 704921115 1250 704919865 704919899
    0x105130e100f150e06190803030a0903140703050a0809190b01080d141210050a0305010b0405070908070303051b072301020303071e120e0d0e040501050d1506 69
    0x241d00c2d80c1d102e00402c015154801e51665040e075072800d6003003625141c0098404000035201750f1007014000c40303404e818012920004020008502601d0f106c1c644020804003c000e0000c064001c503680c504408000c0c070084048a0106601d52a51800c10708460f4085903144401814190141b0410300221030070030102c04c080205e64401c109144266040610700790604041301400001d111710118070484081c00e120aa80300e0035028068a201340c1d481c0600498180c1c00e6500254002801403000f0081c131506401900d50741d40169404c0c80191503004045406010038451707203016800c00d0303000788000307032045000b072031000c4010b0002c8601c120f001c00c9070b0f403d10740344d82e010191112100e106240318000286041840e003074240080c43c1903207400300c0050f040002d0003440d912081d1781c1d004c41c81c1685008400b2a00010325075403081203121940e289030f599611996403508041229032204440500d8a07004881c140c0d0005000341c0a079003420303600c00c0180c0d400c0ca4510710759691592404580c40140302e11400ea = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 704922365 1250 704921115 704921143
    0x1401060c1b050a0b2b330b0f0702091005120a080a110319050903071d01060509040e0615030c031f0e39091302090628060809030307080105130e 63
    0x1040072071406c03c00305138200b00800b0000c4171180d80e01c400f42d02c89800440011500442112179450740c1e00e098688031480f504000962041c2c460082c04112289000e031501079500c15070b04080281100d4900c195200d1000b600140307802010072403080c106106040300c2c0d015460076030031a03040c41c85100340004000d0140791207400041c008604080d9501d410400c0c04024805a40616484031503c406911030500501034036043c040e0000c0c000c581038a0b40d074855181580214240c13059802d01d880074860f0960b00d400464464424080010418580460103121850000510203012845d00a190000d88034400d907525080c01900e00400b150714040c038607000614503452004010718100030f810030803103800c402800d007e8100c05c010419a40002100400d4481d01259440e080b0b45c1c0d40340010300d0307100503440c400d210b0210101d00760409c0310303244941006941f950f48541000390340d44050941d50380400c6400d540086c0c1400d00400c550f00701400d1281c000045c0000c00700d2160001e00740c3c1450000440c01e544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 704923615 1250 704922365 704922371
    0x2030c19051305070206012103180302090405070305070b0a0207150c150b040c03180b060a0906060806090a05071706150f07050c09060a03151401060c1b050a0b2b 71
    0x1150b032176410320655024101040c44181e05c11008640f4842d00706000e2070007400e10015640c0c0e105802c200b21681001181c1c01400c051081c6060706c3c2003520352880384001c843c1885010350100e080d200000035a2940881a401002181e2400086119208200030403005001382c01c0c00010109078803440e01111001c0581000c14242d040f075062004550100940c4020945040046640380c8078484085030056001078500549849d81000078900c0c0010382d224070300d0b0610300b60380015010b0700200e850f84903003030840f18a112540c5040e03000c401d07a0000c40761100050a044040942221071040762504031030003400d03103500761751880c48400b0309a00400c00c4800404010442c94100282045251200001611803507500d041110102d0003004050000070240284080d00030790790a9a0750008400c2e0f030307899103444110b503503400010302801156102075402d07180644d201460b041e22013403100308a17500a802c003440c41e0b1406441c207001c1c0d0414401c1c2c1480b5420610000e6001c0c019440d9914880700581d000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 704924865 1250 704923615 704923621
    0xa0905060709081902010503040b0712230c03010e060d0311010c0e1c052a0315012405190c02091611071202010309240203010e0c0702030c19051305 65
    0x16034580209092030a10313a00c2555041c00050342e0020580e90842d520240000480d190840259006c8010004d1301a50519200c440040b45250313010034840c8540440c0d0400c0c0b1a00c1d10362064580d44000d02440355800031040c0494107506002000041040c040c0c0b8240521843d0280c040d420740d6040c05180300098503030440304025280c0254a1800d0240d18204100c15811607912640c8421000c400743c0d80c24000d5100c010100800804003044c080d00c002c0a844910f0381d91440c00e82201001c0c082d0590725a107800207548000c8209800611050107602c816042c0350625210002c100441081d0350704100c0c0407e1450016211026041d0082542c1084210398010a0900601c46a11840340c021554071250302004014203605818050300d40a10380465640b040307060980c684000a080103048550024200c9620344555000d94141e402151002d009a103c0c0f40c5a01203601234404040d41c075410210124810345451b5450b2410f58506a03003160200b951000012500d025412504a6480d103031420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 704926115 1250 704924865 704924879
    0x305070510111c18030e011b060e0609030a020303010b09010c1509110303130b030603012405040c0509012f0703081210030309060c0302010609050726130b0a0905060709 74
    0x40c1e4402a000e0300104444002c4054250b60740d0807140c0c0c00b82c107111040f420081c00341d201e402d00045103081c0907080c084208c1146001e00003170425052104140c003e00c00403401e031400c0030088802803191640203604590034041030454070350001680d07505001000281e5800035090010f9050f03a040300b0700000410005d1801d0030482142034000c1c262003500100600c9501100385107c01003641e8203003008545965401c404680140028004240c107075003982029140800e40d042010181c1e00c06031002d2000780307490389081d10f240c041c1400e002e01040d2000e40c2c030040c4414180340442c6c040000d40030f84c1608480c090006080220681054038441000a5061302074500314140700c4c2c00404004046940c5d901c1d50310010441030075802040108103852007041c1c2810b1003504110003524901c44104820304241c4009006c0f9000c88035200644500c0c0c540302000854030318801c83c412413400c00030039000720540d41c488450050080c400d10407544c0d960411004a1030400400e84626165240c1c0300c81a070074824 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 704927365 1250 704926115 704926147
    0x11070f12030204171605151206040207062d02030c0307051813091103280501060305070f0602060f0601090510120203040809150304030c0b0702010b090403051306020a020a03030507051011 82
    0x49002d071640e40c1c5d0103401038840310101c8d00104d8000f80c0440860701c0710300000c0d01070710171140050851030030301070103580108864030b00c0704007035114040c29094103500501d04030903030000301c4000711481e5050000030f15aa0140000300301032080c21200400005099001941c1d040040c0c00325040303160b42310708000401c03482540d18801c683e0704600a05081302c54010011344456550600700c20464044084010818250445400340d903114056540b401e440da2101c1018010a100f100b0045c0b240b000440d01c840420600540500341c1a51810324050500d01480071051020520404010403142d041c51087c60503c060f60285203d074280316664441c030804c002100303e0507010032120343d1080003030200180d000080801441d6102c82408615660200103074010040c00d207a03150050804010030003059400301c0100640f1a0720f5071010b1840740c88140032030fa80c1c1c5081100a402c180da881042c07010901403c00381010a2294080303406c207904160260040d20207452001c1c082800100b80c20fa44481a07031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 704928615 1250 704927365 704927369
    0x60504050a050a0b030606090109030c03030e091608072316060e0d02190807080d0504023a06020c030c030a020715080f0c090607080304020411070f120302041716 71
    0x840c2d0480c20780c04c1070080d042910020f0100f80c4112000034420744240d000b80d5550b0029500301e040400d0082c2c2d04c0c00d003e40856000c1510900c40c04040700002c0348504413000c0d42c88150783c660365a0380d02e5501c07201f040e144000655040b0b94140b074045410303903003401007000074209580c080e64500348078003180c90860150350110040594a0300810104810940c0c002056191040b0b61140c8810120640c1410021845006000740c02040002030ba0000100e554100601a91080c0d03102000180d01080b1160022900d0030f80d01030002c00031ba01d00807480085e4024005140c02100018503041200e2591491980880d0429103950800b0038100010364040c00004001c00c50608030405505802d00e00a050400060082e090000080d01007030321001044151441100003030401d5558003601e0808030f48907001140c0881c400d07030402d05941030b110351346810340d138403190f0001004805500f25920104c05280d42080041015403d100000d80349041690340300b500c4c021080a0070800341001c0d02a4074075031180e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 704929865 1250 704928615 704928619
    0x120f021f060e0f0121080f0307020102030f0c091005030a020415091a0a20070504050709090513080924030414010c02070803040612090f05010605090a052419060504050a05 75
    0x440c010414100d10f106140b01c42040d540400c1c030205e03014035051a01c1d01440211042d102004400c000d8096015401140100591070704800ca554800c07401504902c68140419045042090622181c3d80a100515046841d03414054240740d102c2083e10910740300e80381d5450000c0c1c50b60504100c4600710b07079000d412501c0d45c6d0601519211503001d0250012455a4502000e50302032901192118401d0220070080c21000b04140b110781440305005191142312b00810014500c3e00c400325022814130000601c0441c1e0150312541810030b001d00300016481c07817400303001a45009406102016106000842c840d074480c00001400554003c12a42103954042078901954403104c024460b5100000546040305d000d487c18900702c40912a20102a10040b60002e00c0c008074506024100b140640100041d581c040d034065526550b4442e8140c1555020f841c00842c5002035081100e03696000e1498400404c03000c0c150303400310440c001e4820600e038502d80c00310740000c5001c50180a14034050409400070001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 704931115 1250 704929865 704929891
    0x5070807050403020901030201140706050a0213081f09050f0109150606020a020d12030209060f0d0e0d0c06020307032d050c1e0c070b0a0801030b010e04120f021f060e 73
    0x43d54045039048006010113410310001d11102c03000c105004003140c503000d51041e404d0019041102084001e0f41010711512489120b0320b41c0400d82c41030000d440b5003481244c819085d0303a40780a03124500180074203002903c1c6801078000e8485a08803d008007075000307200c0c803e1402c0d503a03040c0e88071300211100f507007010381103400540d800c2016035a220700d01000d564008451410030a100c1c41e00350001e200b00c0320a640c104001081c80903405043d80c01405080001c00024009031070080b203516121000600c840d0041a040301e042c0c00459001d9020f1503101e01d40f41030004501c00740c4d002c0c03440344541020311180b288000310b402d02c207d203500740501500064400e00244c10a803a5840d4291504810720162072040c5012a5901a40b1402c002e054003d0841c69506507480840c040f0040031940e0901041d44d443e00703101c000082d41500b0303020711441503421145045150720040c1088030310750401d0100e10214810048440e40410081080d0103404e0440100010300c42e24010491400c400002c02781040303440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 704932365 1250 704931115 704931119
    0x250302090604151d0a0501090b0a03030e0a030204051503150c09190f03031101050127020904091502070c0803090109060c0302150c0408010e010605060a0f0509040f050708070504 78
    0x203031140281d800110845012401c0b0810003201c49245289921902052200c2d80380d200034082d01000c0e190041c003405009211707684c5c83c1d21105080c1e0710140040351f0000104682000801d12450b15200040c40007400e111007181e0341e80000f02542c8068941814101000c404000b03903103020449044003810a4091942c1854181094010390049598080c0296144006d0502c005688150f4002800f558246485526100d08006103007440315000c4d0f448540c030f0040007007581c00ba105000812120410080445088195800070203074004030782c020342203034595041400050720148a140b04080c07420340183c540025081c200c1d544c8003160312816064004000b003480c0790b41d11001c0d2209a61982c1844840d0340040d1504a18003c400d0000d101c9000312002401800000e8034010800c5034070240c000e112002c2544071640c2250780601c0b880740d108100300071aa044900440002c40c0207039281c140340b0704040c600341c04101a0358020707102400f83d5648408121000740c0140c2c0711900040f0707524040d070801d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 704933615 1250 704932365 704932369
    0xc14130c050414030f03040306051e010302030a17090a0305101a090408030c07050111030106030615020a110109080a08191b060b0607060207050d090603020c030306060c011805250302 80
    0x200c41c0c0d0107041491200743d030003c0780b0f5032010000354030707440c84000440383d4031030740c03410510300814098682c40882d1100350600c08483c07040901c01416a60000c0c05000e604079a0b50340e400d140d07160100c1c440781d001028006c0010b03a0751900d11050046004038040d011490f10800444115040300c1c03400050303180b506124840301d40340d081c0515403043c0c0c4551000d0b629100c45800e003c0354020782800030078030f42c20b00d03c1c800400b5588102441c102c4005803401c0c401c15880b00294003a880c07405800b94016882071220340003080140c6500d005040b411706080d0107940e103a142d85400c2a0b05100300303540e10a40002c01d460740070701c1000b2040d202d510a1400060320040301c5410650003002d80400781030543c0b80d403824003150340c84200320352181d98003074821991000700e850001e494032081408140441c4c002d03080001d203a03004e07000710f802502c0000069440c7d951354400b00078542c0c0126040c0c543c203640c0c900301715604200b84080c48900c0380c000d50080c004500384005c0b08000f49051a0b48a4851030f041c0c00030001a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 704934865 1250 704933615 704933617
    0x312050406120b0d081c05130201020606040f0e0304090501140102010204030312200711040c0e10110703060203010b040f0812030a02160b0703090326040803130c14130c05 75
    0x220a07540e00100741c151983c00000c0d54107608020190100500050922000911454610500380c0700d51061086680c0d40095051060302003c001c0e000d038210400003140c901e00342d401851035500401c400a80056200e1010303245400a41005041c60b5403a03006001c60760620541100c480c201b44000d51415007540d400410061400c040100125292440d11030b408c16000205003820f203050b290280c481e030306410100001002c006050b1700403460505d482250511400781b0704000540600b41118425000b0011648401200d4104455000e051808030003e1201d00003140201103500004c0d483c0c03070030301490100c1d80c80359502c80806a803050a149402c10905015a88e024074112030040e11280c55180c0440c0d02d8400b10002041004a1001c1180d0315425070300c200b030f80134001e68544581d0544803244203002c60328504070314114103c0800090001d2510707002035903c828041c400900c61585981e444803011066003041c40002c03500b008200d0310b0b08000c0e41d1106a482104400d004100120f00d010f041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 704936115 1250 704934865 704934887
    0x1305010f09120f1103160212071a07020303160308040210050a0915110a0302010f060605040e04080714032a010c08010e101703090f030d05040b071514010312050406 72
    0x10300c202c0303031041c0c24214025000e00740c028455130180c03540c0d00c007069111001020484001c83c0310381142c480c1080c2145d400200c00c4191103c4420941c6c003200074500100058000f03c4040380c0c544010441210004e0040d40b120003010311989076500c6500f4280304200c0700f0080150384a0400101f4000d07072200d44d40c0842c0c0041100c2c0d5020320b03480031601c600411603e10440d402c01d0742907489101c1d100d40426a0543c0040205481c5040070807040f0703202e5604540500c5684104200005003501060200d18000010680544510f0440c44200941ca02d6203080d0b41011044944910804c0755050900744418140d801c10030243d40204043c00118001402d1001d06002d050003c803c50000909210403034881e1402404040001c040c40d030302210111641d0742c0c0311101c00c6000c3c1d402149209032a04000644404942d038503120b10b0304150900c0d03030110945e00202800d179a440f03900d100d1b0000610882c801c9140402800120041c87e40c1181000f1300c1d1110440401410411304010400985a018046480d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 704937365 1250 704936115 704936117
    0x406061e3b0306071103070615051009060917120306041e061d13030c15020f030916030c030809060423010e030303010602070b090a08010c020d0f08040201080408090411031305010f0912 81
    0x52413141c84003414201d027640e90413041e00816030301c64420a0301e406c540100708403010f5542d410207194840c45141c181d00d0501c040212641e1110031140955281d00014550010020304001445040842441d080d035030381c0f00700e1848146d542c0209111040000c01c0a0f440000e203024031600380e0400c1d465002030800142005003c1040e24181c041c100140700c8d0200030314034030b038000554440400d207420385500d9205803564007040c4145035900303402118081280c030440f0340040c0fa0000c4640742d038a545074603a028080d030b1030b4400801c01010901400d0a017017500340c00503807001c440007001d1810014000010034100310348a5403040c03004200b100e50000e904400d903400000d600d502c0d00c011002103280c910103500055415400c068041342465400a564051390720b291360b50008810841800390341614059401a0018001034005070214030010000c064002e0b005e031000030903680043c0f201131640c1003902c110040304400048442481424051006032201120003089500901c0d6103054240d2031001410f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 704938615 1250 704937365 704937371
    0x10b040e0411150d0513080a05030a090f081c09050d0f0c0b0a050412090803090d0503120c09040e0102040b0417071a090406061e3b03060711030706 65
    0x180801010b4540c01006210240491101e2460090f0100898000e00030360a80c140c1360000003203890307404021800e9010b1b00042c200380340580d103c030b040304c0716031004001c1d41c807a54a0303501c0280003482d241d400c68038181c010540316441e640c1e05403d83c02a007640300307200c101036820801010082540406d480280c03135070781c1c240b500300780f016880e0035a40902030540280904031040b00304145010305c0c0e0400c62145110b110f6903d4003482c2c06405894450060003507148a44c414040c2e442c00d0f040c201080c80c44d16000d14100c03400c2c48084944881060700864442145010205140f00e41c0e040c0340c06030000410b81d0000a60609040c841c501c0680d010703074801c03484018180c5000d1600c402c000d0001030060001c90030064403030f9420987c200d80541c0001ea050f4011441c00500044c518410813604c082040c6800340007581050001c8101c802584e00d050901790420f60b0700206805442c100400d45016500700302d80d40c001110b800c205810b142004100c030701489040d032801d09a00c0c0000c411074000070380c048400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 704939865 1250 704938615 704938621
    0x1905010515032d070f0b0306010e060a05070318080f0d08070309020906060d110301030501050906150f0108041514090106091517070902030f061905011b06020c0102040b07030314010b040e 82
    0xf030781c40e000141d8070903a846a2a8000818090181c0c002103204030707003e03210002c2c109034440500010340b0502c4c080d00c00055060081c00d000a11443c40b100589004a1507450380f9512078400e2402c02c103c03084510516031214214404654100c104240d00512031700303080208080700d07000314429220050010b8404d81000034401100000c83e40611440b180548140d5103d6840b0715140740280429103204801e48207920000e0400840035403440c0c40034002410310b1085e40d6000c0015038250302c024100702d8100400d50104030f0307007420b030f88107402c6185e000480380715aa0410600c038500b15400754014400181c00d104032041101c90050008040b11500c04990910500b150310441c28405160009003c040c000014440c00000041e1024000d480c01c880c04d02d50f40101070800003500b42a485003d0104500c0c544440c0d82c0850118070302061401407201501e0b00d00f00f000305e07d08990164100e44030031100410b80c403050540c5481000d03c004001326260301d6550400f080310056000310b1060b200c01c600c001c800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 704941115 1250 704939865 704939953
    0x30a090303030b030f0304030302060103170f07060903030b1003272105130b0403031701050102060a020d150b0a090801021c09030e180105030d021c050c190501051503 73
    0x464445da007210720030380c2c1d01d0f030b5120701c1d0094550b402844181c60800441c1c0742400340d00403110440b601544090703034461902d10f465803140041c040d080303010fa080c141ea980b14040c540d01c507908590301030841ba80e00000c0a0a140200c1400c800c2c1425000108e170009144040011b110300340c80f100200c01c0070306080b80081801d58200c03210300c500d088414190703401a4002842d62a22006407054034032907110a0f50001541d0404070086401340305690061f0300c8140455400f161079802003101003141c1c13a021541001c1201074202503403075a401980c1c100400650a00380b141e102c90003201614140b030095203070001010181e6140031000d043c048000c1c0e40d031251102018058007603401008006031420103000154038407a080e00000b4415180240500300302c201500b4404500c40f803c5c1c0840c0c0b4081c42c42c211103004111403c0c0c204640182c95031089518000800e05c040d82110788292040300041170318500003c10083e2025012201c500951180021003200a42e00300e291700c40100389000d001208443c250 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 704942365 1250 704941115 704941123
    0xc03040b0c1303060203070906030212010e1b0c030a02010507020d020c010e0a03061802010f0536150c010f050915070210020a09050f030a02130507120507020d03060503030a090303030b03 82
    0x10b22000d650039101d0000030800c1a40265115407213a4072070004255850304194140c2c0305a501b445a9400c1e640014010030781414000c9801c061840d1051582c62146652944540d0014001e040982d00100f01d0310392503503090081079030101c2c00744098081c403a8582e1000e90307035165501204e4180010380580d0801a1035000040d4021138005609100d100380a001140c00b07910000c0042c0e0004401c11848481d4074090012140201020301080b100c0418117007454203d10b1490f903104020307440850852240e41d43c5d03089810090040d0750380340d6941c1c990160030f0b20b0840301d840c41034030681420710080100c1c0c01c1c2c01281c00d1400300038983d5401d216a40d100300c201d00748012610044012403002c1030050b03c290740110980203495082c0e4002245849107001c15540c0c0e401403e00039402000340c040801d07203041a4000ba50031094a040c0705020107240c0f48004140d0748111000c01c01030340300d00301199030281d00d40602c030014101607010f07600d0119041c1d8010089040c5000260900d41c680391a50b0194134100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 704943615 1250 704942365 704942377
    0x1103031308120a0b240405040906020d09081b0a110405102301110c09010b0d1b031406040603021c050f0a05030c0708014208060615030c03040b0c 64
    0x146000c6072882c150350440004e001020b18503004002548103030168019004070340030300b1605005290b0801e490201000090300d0218402c45000750203215030000c0540c28000d0066040c41580c2841e100c400031a100800b06c00c0c0f403100b20714a0b0f400340c048039001c03400344c46505030100002e440c041440e84d200340c0c4620020b02d403a4480c21401e400b888a04000b0b401c500b031880908030090303031341e86030500086928a0340c0303000c4520b00c0e60f03002c81a080104440c0000d03070000c1000d9116500c010800b00d00c0800c2508500941c200ea00c0082911503207103151010400c440d0641c060801c580c10020603007140c02007605c3c50346441610b2000244c1100400910001b00501400c02d081a012980c0e4000c044c54840d0700c0c0c3c1c002c0500a4154443e169010075800418002c100340b080c840110180702404002c0403000c503482c003011140a0344460707550321440f602001564170107403505000500e140d00702602441080c070701c0001032412142c81401400359007407800d0308490b00316070440e1035042c041d10780c1c0300001c265101d05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 704944865 1250 704943615 704943637
    0x1a030609071517010b0306180f040c0e040f110a1a0a02010b010f021015150e100507030c0f020105160302070905060913150204081f06061103031308 65
    0x41820428400030004505040d94030002d020710050480039020707030b1030125100340d9040f001d1129006219844440000d143d1100000b0721300d000d0340650401c40042c05400703480201500804a04010034820000c40400007031840000c0c00c41c851070103840e045494aaa010001c1000740c820f8894426517840c0400140644140b581c0c00d444c00e0141c1590000c07583c01420714201550030411221103a40c09126040d040141c10b0300074020030014510400e0040c101045003c510750002030300032540408000940d05640240d4551100064143d800c0141c00f40c26514100c0400c4001c00206000a0744425030640050740030b80022541c050502c0141e801d8000c0d00390746000c4e24110a50349042c580d0014110003100c00d56001003009071504018012044401c561031401403200312004400200403c4c0441150150184d006003000e407182c03111802d00900c032100414489021003c82c40005c41352140b10010511810184071211201d405a81c40740002410001142c1902d44000140921402100c840087c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 704946115 1250 704944865 704944873
    0x70503121206010c26091801051305060109030c080606030106170705061b061003060e07050d030e040e060a06090e030901022104050901090f05070e130c09030f0b091209060301091a03 80
    0x2600512410703401044160b881001118001f007036036940c0002050507110003410100910010072004409400054005410000d0000000000c1210b10329088090000d402c060555418917004240c01e444054010703100e22000b0900b0b402d552000055503504440302a03c0b440c1d00c0d06882245c0c2224100c8269103030009005640801041c1d140010004069902c9410704100300001c50328020740e00d03c0140200e40e086901c4059040c0800d00030032010101d810014404181c0c1c55003407442c142494410754480d80107d403600d0040c40790030340f00e001c0c12440055041c000d600300301d140380c0002d50300d5410389c1d6035030f11020000c00f90b011201000c50440d0042d20001d0803851555070350b0f1100c10018003001010544e2a4074010104038514418030858004110007002c504203c80c91308840d41c0109032030000e440521011a00c000001012040b004c0c20140c041c04820600b0b24081c4265400c0c40c12105032140030000c00c00034903640d99940d406607810744000b07840c0000d070300369031400d1004a60486c0341c200d541441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 704947365 1250 704946115 704946173
    0x1b021302180a061d091503011a0319110607210216060f140c0114090a110a1820130311180f0411090405070503121206010c 54
    0x8607000c4500c62034501981c0d11a80950b46180481e00d184100b0070b800c5040000404400552038240b0426803c0340c8584001861468500c0009085841a20707138000d0794100602c90409910701448251200c58480d001c1c2c0104401c00d690702100307a803264401134400c5001099220501038240e00703948807029500181060b0301201c0801a40e81c1c15019074400c050010b8400209209215088008003030b40b075034a5100551050f0980c88541d078020462104880d941d50814034021200890b0140c01581e40700043d10110f08103081c91190302c050854a0fa00500c000881045030101c40e41003070a903074042810004200440782900e2038007021452482110b0f6030080707005044280c5c41d400010440e031007450740202d0001b81f1410302883e0344086104001000f244000101040c065080d42c5502c644910115030300c4104080010b0007451081c2c905480c994820f00381408541002c02c180701c0e46412810442d42841140311100302c5208000b002a410000490400700c02c01c01e000f80b01c2122041040c8680c00006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 704948615 1250 704947365 704947387
    0x1b0c0609070302091b1801030b0d0606091a090a02032206051801050601092705010b1e0f0712301a01080106140702030106030605011707061b021302 65
    0x18110b0206078415180e100100710070804941d0218241d10300001103034105407030314101070160890852418107064548100b050300c2e9984003005170b480c034401c0200054bc1410890080c003142d0f001d030512941c0f07890050f034038040360756041841640000c00d1030f00940d8982e1214a00105d0a1074450300c8851103220450301c4081041e00c1d006148034500e0440010b1401c264a1661030030383d03500b5901c40d0b0200345111024400040c61071624980940ca01c401141a00150002c0d032044603026442231090003408100300c505440021140b448800910b410a81464403a0070210a1407150041c020101c403605261080f205010f4400007860a00b12000a110042104543d90344c01ea58000d02c0c00001e03162121502c459411048001450314040c2d680600603802d02000303a0f10303170901c16900d03082c0c9481842090016171f400d00842019510402002ca21940351503102104179102c414003102ca508480024007806070301018140c1c1c2d50768101d0101e00031405900106a030203403040501641ca90001421403658 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 704949865 1250 704948615 704948623
    0xc1a12130b0109050702100507091518140306010608040809040507030b0d0311150906010618080f07030320060c180604030501060f0e010e07030b120102030906190605010203031b0c0609 81
    0x80c900d170fa001d035101d400c0c00b88442002c44a04503608404902502c0701485800450070a548000440d42004150b13808074000180c00b500703699020170070303200003032410070f5150800740816401004241000071590802e0381e6036840a0150664003402030780e403980000d541611a80080340c0880b07005d8202c451511480c240204a6014141c1c2d000b80343c0301d00b2640c00c4031818441c081922039030618015092507424200300315a81c44800e501ca00b90101a041c022440074014071141a0f140c090a00600049c2d140d480c0141003903036460803403a0781c90004440d880f40d00d40701143c3c041c2c0c41000000303c545d0328460080306028040000601c3c980001c4045004030803c84154001c8017034070544060b403c201661102c02e07130300c184801d0080059603403550b4041a98980250400c1d8000d210050003204002c4d8091a0503003260011a03031042a0350150050046000d81c4410351354210907400d40500c0340d00c2c14000080d5a178071001d0003c030700100781070301600307803942640d000e58074070180305819140340b410f00c10015503507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 704951115 1250 704949865 704949871
    0xc04091a070c0c08030702090a050414031605070f0b160503040f0b090f030102090105041202030c0d0605070905040e0d120e0f1c0c110603040302160b070c1a12130b010905 75
    0x60a00000045998130780042076460455000f400312241e41e44500741e41001e030030054021541d907410144131304040c50040c00170b000c07403101c0503c1858407a80303141400c51a29041340e20506800c81c031002d0520291089a046800562007006600c880d00f0280c03600d24914819944616000d1108030404600f8250306002009078920071120440003c00c40d0041500700c0c45001816804030700100801c100320350041a2243c000c030300007020b548442c200b00010500c0d028002c8021101d581e91a020401c0700d5400001032009072000381c1e000c1241101400314580d0300d82a490558091000c000c40003121486c0a802039080d00101006071002c2840381245103548a40c00714542000b800a24582800c07940702e0880100c00c140c00240e1318018450b81300910a04e540050000e80441c040c080b0f049200229005100c00109102c0c42d943d9138803501303820603040c42c5e00c0070381000740d119890200b2800352014200950b000b40c08541d5034401c2688030131000303d0511014042c000c10510b034510001490850f02c1d0b0120384 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 704952365 1250 704951115 704951123
    0x1716080f010b1c0f11040504080903010e0c1005090312040b090a090b0907050d0b0306040c1503020309030d05060105040305010906050a11071a090304080105010308030105010207060f020c04091a070c 87
    0x10400b2803020401112260380c1c3c83c030a4400000580000110f4204134041103054002d105003864011901d0104098a00c1198260307500c600002e0316103c0d500f02440703680200c0303002c0d00c0540035500126001548561151070340300d04000740810441c95a42d410b002c0000d201c031450201556455032404010720340d40102548600c1045010f000003104400c40c012640c2c0800020b100c5041560b82c0c60342a10300750800e07003e003e24550b4681a0b5215034504011070750003140a140710b240c1440c50400c0103484008810421001c1500502c24031507421030000c140c2e6411011010041044c1d0350f1840120342e2030180d6403001d8121f600388540d0f807080c407102d580524043c05d075617034081c041c05555000c0038589200d050001414111608001d510000b140c05c170241d08140c995003507d03e0240d5031404103080d04e800303800980740f501c0c00000400c859a0100f204030000c05d01d0b8140802a0030a540019440b05880c08059000304d031182d026004000c0300505c004c00f10707a40d01803044141d041443d0000c100fa6003202c0121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 704953615 1250 704952365 704952371
    0x70e1f06050309070317070b09010623060910110a0b07080705040b191206060e040b01080105090f0a06270c0509150c030f030c0703030b01181716080f01 67
    0x1046141c82501100d01c500150350007041d82514590350302e800508600324540d110002403040500003129140054065140c200c00030400038240000301220752803210001c54a0256440841682c0e00d45500ba5010503008a42c2101c4800e4607400a407000c80032445079045c030b03028a2602c0010465071005060090b01555111071071952104002e0b07415105600500b40e001000f4800c0190349140a00d81c03901641036440c10105c0da801c441c045405031032043d000700c000b08408a8008480381480d12600c040d1010134a064506940340002140346460003524a48102000702c0010b10058034940050000b000c03c0c0891b2440780490516000c3c0c4410002003811441d0b081a1204a025100700309a82500c00000c000000210024001201d141d118a14030b0800e4007040c410040e40d56000c0e000381d071040c00c9404120b80d4a00d514a001002c85e01200c0415040c019050550360303042c44202c00010a81c3c04440c5081d1286048401380d5203014000f101c50800055055400b08155401189101600d00590f00074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 704954865 1250 704953615 704953619
    0x8070c05010f12021606020406090315021303151e0603110a0b030105041a030f0601030b0a0e070302040b03010b041b1808121e0d0207110301180305090102070e1f 71
    0x11140c1c04401c648400014080f114640540d1500c0d034002c0c04c10b2000452206205d03821540c4400581e04142c1c001808100100420001c1c40030005816010724000b09c000c600d800d01d01c907085100140700f4080a000000c690100c0300c03581c21682e1000351600150000c0b951010701c1e503c040ca000e4610750004a0302444090310044842c00c1095010050718020030402e401d507800c02041c800200f190350a20185841ca4460015260300c00740046508003a00c40040d00b47ca41c150f050820703213000054a001e0700f081c035058010420030004590801541c0d4102d502064484520300000d0161030300300072140d40f081ca80120f1080342c3e40c0720b992000c13084009444016071482c1c01c044d440d480d00b6003482260400d80082c12200c0c0031141c0c0000528040724010000440c2941210034202c0e903030004504005026400120b06043c0b041d60b14008c410184101c00a0080d600030b540140c06424440700010700340f14020500c452941e0007403100c00050304034540caa68041c0b51003100c0040e80080c00c0c1382c00007903c50300c80700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 704956115 1250 704954865 704954867
    0x403020a080307051b19080304090e0a080403120e090709080607030e0a022107080d02070e0112261210140a0621050103060b03060105010201060617091908070c0501 72
    0x156042950040050805d03229541080010011802a85540700f001800380c0c20f00e00742c1d20041140580f081d00004c58845040440c100220b1307068030090b40c0c3d075a000e23011500008034450202c80503031394402040800d01b04801c00a560f01e5402e00300d240ea0020080d000c10601da0b40c024140d000711507007441142d0107621420000e500711101d1040c0b00c00707031f604660210300160400700e40c4851189030384107804213814035400541b802c0c1903035504080125005040300401140d81000043c000d0b28103999505819490f011400c0c0216014020051a01c40c40e8043c02003111469500620800a1210b9483c3d0f00c002c10051001c140d04100c030968039001490001043d070034140c0c0c84c0000c040c0400303030504400904000040d00d50403007100360030080c0e5402d5001c0070341c140b855004d03c500031032040da0b0200c0c041c2648000c060902e20144c21060441e0300d4410100201036000144030000705090703d816000707458000905050200c00300318188005510030042c010440c940c030051259500540e1520421625200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 704957365 1250 704956115 704956117
    0x4090e0d020d030b0604062102040e041209060f0827070603060f0f03080c071d16030b0102030306040903030f0c08010f0801020406050d02180a08160819030804030c0602030c0403020a0803 82
    0x1136101d4000c1020300080c003000d400303002001c00510341400c20130880240075943d40281e0b031094003c40e400d901400c091104000c1011501280415a4100841201d042c107000406952084140800b0022004085400302200303030b841d104040e000520b0051511000394a00383d60348004e104c0c0e00006840c10744005050031404514801b41c1d484858118403d070700e1903e400c0f840b600803003a008214040e000000a0440380441901161190071603611154940541954145400e5a610b18189410440340d0703072540c0c0c3d010003102d80c031002c01c0b034001448451504040380241040e00a01036103601e03040c1956003a1f034014500c0b60480305802030b0304889a8581c0a80c600342c2c000c070711810010070030610104109081580141c003004c8043c0b00294086c2030f42c0000180d442c00194004182d9170000c29a481600304198480350203400c10400070400d400c000c641c8030710105941c2901070200440750005c50b01f0148160420a541e5400c54420740d1a420701c00c0d9514000d0f1701c44e10040303210b02c0f4015030009807410084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 704958615 1250 704957365 704957381
    0xa0602160504231e06030a03020c060c1e010e070519060507020609041a010318050618030405150c10050720010f1a041503080a030f0204090e0d020d03 66
    0x1080d002000c929120502003e86001c610382486103610030541070703c22018500c0140705100b0024040b84e20340d0960071107048080007402c101e020360403050240700841d8001a0700700d004041a03441030307642c00e0fa52482c0b9051003480e018840524581d05501440700005421000b0f080c40ea0f14191503c03240d4078000c0002c1e400c044000c4803024044d03338200f001040d0090001d01141c1d030010701607518000910000404444104040b82111444140140100c0d40d151194a0101d010500030502c0c00c8503d40310701d542c41d40001d04403091007403082d2081000460a000b942c00414010703080c0d03448402281e5a00c02aa0002a00d80c0418400e840d880098011240680d90080009485a00444c49110f150880782250380c889a5001d43d00c070b46110407240424800c3c1900783d0074201c00320121510b90350412068070303c01c20780c04034a1105100e0910208000c1e008036141c245044c10002083c04585c2c4051010313000d84d80c0003242c0170b4038049105039000000f18180e20300e008a035090b50100302074030b02c050702110251 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 704959865 1250 704958615 704958643
    0x215090a03020d0c05030f0301090504030809010506030a17071a010914071b020409050303150f031b1c0b0c0703030b01030c090605130320010801080303070206240306010308090a0602 80
    0x8406030301042c0b8012021316207050b0152040d40d20700403180b6000030341c6520030303403041230b0407030780e900030070040c95400354006402005980c000d002c1c1c2d0030010002950b4841c61305000c0c1001e41010009100c411707000c811074140d01e03400442c14000320303030341490080030040910492402c1428105a00710080004520510901c0343e07455107101e5004880c4e03808101300301003508a8000c0c3c0c1d0340901102040c2e040000d1842801c202510003041000241402803860421403240d0090b80181148641d015803e002c00421000a07038443c00030f4240c04400900b424a890800307403196540d00c050045640740c80b402000c0396030194070144482011800110f045071115040304001030003814003400040e01c2000108482d58017509235201054803a02e0b05c0200032900881504440e281d00c218900c10f503001168035004110072005581103140c4054040d454040041000d441001404028100b80c41100b04025071000040c048440302c1da128030300035600390301400a82c2d100352401070b000182c051000600403020409 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 704961115 1250 704959865 704959873
    0x605040e132103020c0115141e09041e050c040c081e070201060905010b0d180f020d06110d0f05010f0f0b09011115041514180c03010603030215090a0302 67
    0x1400b10041180b602d050245001c240d020400c41a4543d000d0007034070349018100040c03201d8180352400c41c2881100011406014003411000410451080700c4450480303601600e88000303503682d0f450b000d240005c9038400da03c8400d0103200d0300000d00000080c0e580c0364240645c2c041040b106c07805d5040d10001e5040f82e010035004451049880c94403030b0031383c810303401c006036000100d14203071a40e03101d40503104241c00c2006008400301e40200004614000e1310300d401c210120228014101e034980c4080841c1d560fa01034000d40020928a0401085074440101c005a4201107078545180c120860094070080f040c9020702070900c40041104405280c03441c2c210740455650621003460050300003101d0f00711400043c180041040e040011800511806e9080a04104103100d107183c2403600d001d80301010810100c19514110041e40301004a801c2990806050b500d590700c0c41c10342c00421850a4000500150103509000c4000700301500000c1842884103504170780780304e503528a40c0c00ca598a00c03807100940103900c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 704962365 1250 704961115 704961143
    0x15050103020f120d2a1109070318110f06041202030601050307150305150a06020a17030c07080d090c1404060509040c05100c3f0f0e06040e010605040e13 67
    0x10050005c03d52404810800d000039450748072040b610000740c03410550b5031940b40481c104e018984803011ba680b0215034181004043c0b800d0342c844161a4003450001c02c516490300d5800b1141e070350301210030305a880040c041d9968644402013680c121943c11000c138000e114040001ca170500d03010804400740d42100c490031030715041503c02103001c1e2401030000d50344604468000e06080d00d44014000180440390024102c005040c94070141803000d200e82441c1e144424010301c90307561814000c0710f070b0503a00807010b10b40300c0c01c2d4440c0c640c0007086001c000405022a02e40b0001c0e00c8080803002c1803072a03100721b5003085034a50700c90611500803400c603001008400c07031440070701941c42e1140008841140902d0b2600600d403242c0c0d6000010b600c000d14220f00d941c0b80a680b09141020441c102d401c0070041c01c4400c040d44201da42c068414085d0700120000d02c1201c06d0304c0209a101d040a5600808d4242600155540c0d10403010300b00340d01a015042c000200311001861080046076844012075012210f810001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 704963615 1250 704962365 704962367
    0x315040f0c051608090303160209010608010308030612030c0105011523030c1c111b16090b060f19180f03060f0f0c030c020c0a060210090f15050103020f120d 69
    0x3d59400400c40c0c803080d0600c204003068030208090310790000e041c0110303003c0701e41a004224540905070312010400101c40700600008007171200780d9400440943c1c0400724070311018031807030540c0a0365041d60743c590310389030001440d540d8407541c0840051440c0c4488924030502c0b414805402e0310003100c40040c010800208040000c004001c083c403a2400300c1c0d10321081d40c1c000d8540f098404122460050220118020020303124203001d600c91f90050f000105007100b01d05030036110140031441440c0103240c0e1052421640d403900301c200e03446404405090342c0d4401e00011801820480c094045000802907240105000310410f030360019616030010b203560061031035466502401440814188040e00c50b0310284481c890750050003d03e61141e10081280001c55000903d08800060100d2160710b44010800041e90042012a01003824035800301e074403e91410517444010041d04010720903450b01c42c106805403001d50006059038070032034102001e01c0420081241201c588541080f854000702012002d02d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 704964865 1250 704963615 704963647
    0x20303060f24030108241501020106080a0309030b0105010c030c0f05160e090105060402210603030c0706050a0206012408100503030a0c0b0a0c02210408030315040f0c05 74
    0x2070100280480c0710003021085001e80100c40801d00c0c5025080400140182e41c4144080107000d0501c2911605103d00d0640c184090706c0301402406400c0f03040740c46018183d200f074101002801d06641183c503440305614005040c90541d200c203030f81e90f00c010400883c1da50701c0380d110a10550780580d11200140034070744072607000c6e00c0120021a00c46c0b081880210003520703209c00d0340c8000c103d4103402412520301001c1e91425150024681c03031044d0301c10442c0381d4130742d0702c0c201001e0b200708541c0c2d00c444250794601002c41d00d948210490580306118020001030815400310084c01e5044180c1d0a03101c250741d840c02940151101d020811492042400300c0701e001520480070a43e1025106c404c0b480300a0b51040400e0455021050ac1c074000740120903414103100c4ca03410704130b82210140008000c0c0300b210714402910b800740556044850000c1a904032044040074041e940549924016280d490410071340b84a00006065010b0b8002c504014141044110b248280308015249851386840c110751543c10313a00d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 704966115 1250 704964865 704964889
    0x1120608030f13081006030b0702010c050f0a120203040c060207150c0b0c0d2a050c0a0204050615120121110402030a060b1225022a1002060a110a02030306 68
    0x4052111100001c41c8201041a0540210000030011b1268118146004260002441d00040d0381c14014101c3c40f040d40321044802c04508903507015114501302008440940c0d0000c6400d800c07600120902090003498107268048642076022900c000da80d4011240c400c201480005001c20f900e40700b100081102885030f02d6209820080240c80d110018007a21f08541c80c00040c00b00c1d05403803a400c140200a007140420030040716003085414141041246603488542900080c0030350f072103101003403040d110f0300c0c0041950442104840e44620046803907100c4500240700d000c141e0200b01210300c030b0000d008111192010b80200900c0074001050023484042e50001c0d10001307a090342c0741000520881c0081c080c107076a803180b0300185118140b21034200e00e24840c0c807a01d40d120b448000c0440e00ca198001030b00000c0300e102e2000c01000088201062026504900c205581102d03a244907c480e036640801c100c3d00c1903448403c10400501244401c9480f80608041c10b4090303030081002c42c0f030720710380506230000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 704967365 1250 704966115 704966137
    0x10020d06080607081504090209100807050a0506190507020909031e09010c061109030a0c0e07090b0403030e15030108010f0c051312150c080a11030c03060103020706060b031501120608030f 82
    0x1f5034040c80307a02242c00b6003001c482881c90044942c0c0144200041441100001c00045445040d49030400300003c12030302c5040300b0f0780341c850707040d64895041c00d020f17000b542c81c416001000c954981c5012401c5a403294400c00c40c0c052620340090b10303c40f03004445000c0d41c000e0038069540c000344031500d40e2104010041c0d101c950011000c00e1002c0c100554040003074440803841452640c11140c174054944c044c100010b090031081c0040c2e00005c1c080b4000c0d040550b4101c81d05468640342c01b90019000c5066241020002d01d002d0400100119860005401004041c0c812800402a2240c00030040b28940103500d0546022420240d08000c01030780380010800c954001c1000549800c189280082141d58800f000781c045034035141080480c0149100346c001e0709071844449441c40c607005400b0180c51200a0000b41410380c0800c200d8240710325540302c0405000b18038001c0d5907a0804400d8200c0705140a00c882e030001e01a4540403c11810901a403000c0340c5900d0000c41c104000616207074010b80028508007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 704968615 1250 704967365 704967371
    0x3021207081608163804061e170115021204060c021009290d0504081e070803040f2a0608011d190e10020d06080607081504 54
    0x22440000c01d000200302422510444100c1c20701d40380030f60307080c0300310424146040f8440b84030811124413a500c4038000c181161808a5030803140e50180484142404514401d07818045004500c20383c001e44288182c56401d46041c070804842902140c117004018085540451904010014510003c6d507100781194180182c031980e01c00030f0446500d80d00290301220002d1040b03001a002d5003010a42e82c07842462a19104803018100307440d6100c4405c9001c40708030641c200780a0f1014488208007520300168168005100d6070425042030782d1300c0c0d08505210907400d40c0d580841203107032400108031030040d40d22404450440e907d903190340d8801e040400060b0307500c00100641c0102401d00010645404c0e200e070507502da01a0510f20b008028403016003000036100030400740180e03e4104100c0c282d9010f01000f445410044580c60b54030301402c4e2803180ca100034490a10341c8003242c409500506240518540200401179a9101c0f903940d5440649071030340030507100030124501c011003000e50070384880054404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 704969865 1250 704968615 704968619
    0x40e0c120c060f07030f02030a0230030432100f0608070303030c1205070c0b27010e0f03070c0b03091c08090705090601050405040213150203071a0c0403021207 70
    0xb00d0440d0f48010a0541e0141d0b000900c0420140c10950f88080f00341d140c8011800e182541e0400395030781c03c08007155400c500e03101d602d802588410445449403c3c60403200c8607200c0c02c0900d41046203100412a5030b00c01c956495540580142e0562903442955507540103240800c91262614010000e2803a2a8520b5880354004200c07041c003041000f0046129030f40000318200404002801d42c100c84007c00c0d2600d051409000c94507034007410855429030801c0d40f114450702e6010400c1141e0f603140b0403400e007290341c203a00d2684440c4107602c00781003000c8010039601c0302c000d0062800d480e0701c03c1d00002040b4030641242030010340c2ca008046c69200c50220704445056034480c4c0b003c0c0500c032032828120b00260041c4100010184140b0a98005020030388100c292814a003001034514000c5001d802d0160b03a0100306411640303080780c070701c1008018181e14914504d2841c00000e40300d900141c03040e80d001c0d01a081c00056003280f5020f149c4a010f01c900e0700d900b0582541d0130030949621060004e10f06100769100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 704971115 1250 704969865 704969869
    0x8190e1525080d0b0a0308030103061d330403020601120f0618140105070e041107020418023f0f0d0513060509090403030506030f1c0e040e0c120c 64
    0x1500741d866004070356098807a0348241c444415504843c0324a40221708068013000041d201c503050720b042d40c4c1e02c00c5021444000f490f04a00d0224408003400d11507216504030301007000140440c100c5411481e100302e02c1c42c0704403000303180e01c0c04005540090060307000c0c4004214200c1a4521710031b900388914852488038036035448150540d1070440d0131545000c400007404040000e035612001c11403070400002e2125281c20700000d800001d0909406000340e458400400000320b810b0200c03509142c0c001e00401015283c20103c02c0c03041035005040b800740d007401000304484802c0c4000b10042303100ca202c100302c5070b40203e210f42110300d4401e1818000b51056882c0102c403c107041c8034603030361400550340303042e115607107207802c07001c170882692009081c410200a490025140e070584c0c6907105406090108268843d900480c0c80c2800e0841b400025010b10000e15112824443d01210800b074030350b4514038840d0844003003004940d07118101d481c0b540d210000c807004900300007091180c000c06241c280c0d0004005000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 704972365 1250 704971115 704971177
    0xd0807080711210604120512010e07020c06030129040e151507020306010306150f03030509100e030d031a0303040314010f0203060a0e10090908190e15 66
    0x2001c455010b41c11070030000504018550300c844098840144aa02c9041d00246403030b0301c800781c009815108404513519085004000b10380300070343c0165002c12190b9580c0e400c4185d04909480c1c0130014001c1c03501c00602171610300d058905852000c0c00d41201804c0340080b85403010f2007030381a502d11a17018040044c001c1603045565205610305c16009001034911320400405071038bc0c00800005110900500c00581c800241040c1501d0744000c0014000c20f000500319450030030755005a030500c2c60003001008242d80140601500001503c8420003908094419206468030025041c1c0690000505c41280f512942240788044104041c0a96090003070340800e04507480b41e001581c100d982d60f42c000003c01c00911991204071000c00c421800c6041220004030450181c2c0709028601d42ca02020454281401144400030141200f0810080d502c7c0d1400540342d070881c030455094480002c0075100114003031844620454001450022410755500d00c45000740c00241003441c42c410704a00d0410703040c043d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 704973615 1250 704972365 704972377
    0xe011709010e0c060f1e0d0219030b0901050607080d061e1a1204080a020f030301032a08191e030306081b03120f0d15140d110d080708 59
    0x40000c42e1000300c0c1000c0364503000910300d80901804041100c0080e400c40402900d00701d0076908050a049020000074080500420002c1c0024a100086000d2500041d10b80b1001841154409114819016081101000d02440307559000203080006400103000ca000405109079541e20005006840302c0803c24401c500440c00d01c0c59401c0c448090111408149500c040100309541c20303454900e1007580540d1f0f606010708020301c055804180703410b040d4002e01c450101c0d000d07030303004598980da580d00707040110301e80c100b50a401400c000c0707661540340307008100d5010640340f01100806000091506000e0005211801034481948041c60584200c4d0211920346107940170340c2e0b02043c82d42c11300c0c03019810311300c102c00710a054003183d180d50301c6c0035180454a1243e8003a04510552241180b000c042080e204d40d8a581c6104c6182080b81700000035030b0842d84081d1074507203041c040b140f500c010070300200040121000d001c2030a0141c4410380f80c034106010015841c45075001070704010f05681c0b0b2901d981c20507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 704974865 1250 704973615 704973631
    0x60121030e0423071202040f03020603100b16061113030b060d0506090313050d03080604050403090b0a0f0f030614090601030e030c0703060b0d0803191b080901050a020c07060e0117 79
    0x3c0140401540d002884d0101c407000d00c103003181342601e006c2d842c0f1029a4148402070113404c0220000c2c0c24052154131007030041c600360207890303501c41c0304108a5a0000e004039044404500c2c1c02601800c42c00400c040d02c100700d201d021516606825510386102031100201015804445411400002a0140b10940c000c00c10340c0d000790744825980c4210040d0381502d0300014010081c1d000943c0c00300340d011320b4090304021700b9500000c0b40d496a04007102c8500207900b04c290201d4000952142165104120f03107041000d0b41c1d91003402c194200f50172000e5a21502c1a40b924922201900070107141548800750001014107000a01e1600c10000030705540101c030041c0c00356086140d00304140310940c050040070756401c9074104010f051715a0f444003240000b8002007020103040007040401c2c01c80d42d0101a1a00e14040f524800c010700704001044540c084907082c0b07240d420b19010500c000004c0c0251003503010340c00c5c007130721000c2e003802c20480d40d10204202c048d0401000c40c5444040b03044902942d07010b0b4402e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 704976115 1250 704974865 704974931
    0xf0d0305010311040b0d170d0603080a02060108011b0311040e0c07050f030901080a15360204030c0b0d0207081809090a020a140102160611060121030e04 67
    0xd1030030841c5aa50190300300780c0c0114200300d2420525541d54903550346c00e07548000ca6252441304020f142c111030041c0c143c0d201486240c01804400d024020003d003404144544c02c5980980c0c0f9295110301342e840c450b00d54046010a00c24a017025802500022001c00441e410241419a1211248000ca00c240c0d4a101c80d488005140070a0000c2800402d0505660304015807500c0410b9000900c6040c00074454503415648114000ca100b101d440b59400a05100011002800c40340c0344c40c1000041c107280e010410030711a503408002c20070500950701181d0300540e404096501e8200ca80c043c2e54008102640d6150b0700b0040c40780002c64a80c0541010000c076200c0b4900010948107120846501400094995100325a8440141d480b041c4510030ba6118201003c078584041d00140d2501d01e21440f6a1450183ea5a011070320551020740c03882440c190030112121641d030f07050396416420700202090f03008801c00c1080300c0403d000d660700204843d805000010004180380343c40c0e22480340c0903001d4a400380 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 704977365 1250 704976115 704976119
    0x305071512151806030c09050a0902030a06050a0e0f070506070503040b0d0f0e0328210507480f120201051f15050918060114042102030f0d030501 64
    0x4404a24994401c90070b04104825800c0d038a4410021107188200e84071941c0b92300c005600f2141d41c1c0c2280000d01da01508030303844c210b260310388080038001c12185180038502d8011000c0c0c140303000103117208841c0c034020050b2808900304814014560301090702602c940c88100310014030b100315030004100d002e030000d100260981e1419640802d0780d0004034901c00d9540244410018100c80000307210420070704450f00c880700256214250344603469042e00e1a0f091038040e40c07404040c02107400c064803560941c1d80b561a13000b000b00d41100720b442c8040070310400e00003c1181009200c4114510145440c0c5a485041009150f603512100040c504000721182d4a901c0501d0706290b03024000d13190802d03e48000c0030394442c842503082c81110850720070508c0c4a0050505a04000d008104030750300164050700700c585020804002482d00902136450780d000031030654000f210350783d406080d02d055a109200c080d0002c40e40d0b155882040c8010341d003e0384d050003034000740c0815110030040040c04e1600707510081410340c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 704978615 1250 704977365 704977379
    0x40e092a040515010203180f03030d14010b04030308070804110904080a081b0702040218060f071a0601080a0507090e0115140c2a0a090203010519030507151215 70
    0x141e024010804801d0f0301c80440c9090ba0300031050b40c03040c00802c2e0b000222070051030b00254513080703640e1900750075000000d50941c118110707401c0072550404032826090365982e0b9000c106214030861001400013a82c00c004a211340703109014036900140500c0d20310001c0076011000400044013610308a44400c000141c1c010901e411104e100d82c4251904100030b111000340c5018501c0348249400280f01e00da0029900c0c41e403a100d00347c0801c040d500942010f8881c1c050303d207100c0c6503900c4540c0a450b450800d0841154529042d90302d0791180c40c069541d00c00756180c040051000d80400b811600a1102160012a4102004007403600034103aa072244841c1040d40d030030280c00190b106141c0c0c8200700d420020f9408407940018002506000300148840702c6200c0010324081402c8103444a5000c2e64200c000620412603030055030589600b00c6420401041c2800641f1181041c0d1200a210f40c05c400f2007004070421a0b408641043e40c1418810141c5072481d03004022a030300038070351550624019800317010032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 704979865 1250 704978615 704978621
    0x150a0909030e1801052704061e05130609080903010903030203070917031801050c1501140402120606030a1805060417040303080c0d090f03030605090a0908040e092a04 73
    0xa0b42655030031058008070241481c041014080c032400781503071550000203000694141170784240b0204807188142028903015003d0014114400c04100c8080e440c081100311074801c543c050052180c2001c0e00c240695182009070480d008260385a4605004140554a0130301a0200c624842c1e640181c4d00d1528100150804280703400c208800110052980001d020002c204c0d00b2600c60020b0848e5030402501c0100e440784501404046940a083c1702c0d029003014070380c4d8980c165001c40303440460804014062000701d015032800d44441c00b02c9280131800f607041280055400130602440800c020840389640c0c0c03030021041030116101c3d44003200704001c0c4010711801c40160303062440d41ca8686440c0d500d0040c506a0058141000c5450010700c113080d010b4503610510710355520a040c103d20396114140a00240031071b20034240102c0030240081c00b8000207116000e00d60394440c42042c00c290811150074961074005245109510a030a481b81e00c0b140134210038003584410b120f440080c2c2d10440c0070300c016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 704981115 1250 704979865 704979887
    0x9140a06060507020303030a0906060503030a1115090c040506040f140103170c07090c020313180c140f0d0902061c0f0504020121091e02040b0906030d08150a090903 72
    0x400c4802c1c8640f0005a41c00300c11650800b0b01210701042100544c1030000050001d81d0200b5414440007812001c141d410040e4841c0503d1464107668000c0d1040c1105511030008480000395a00f2200d00c005e031500c1d165104542020000d000002c1c400c5130301103240210348440c2151001000c880004000300044a141d0050301500340302d0440c14582540080c513640d203450f00441e070241c0c1e00c48001901c064030070416120541c9400101d1034a0940e5190b0000c010701005502007481c0b81407e01202c82c0500961942ca5110000350000b0320302804c10107144265017001504201150f240d04124000da580d41010b4008282d28414019006050b4440d640885410103021144642090100300140c0e800c0311b01141c2c00096000700c140050b0500e0701500003409585070007054040e41415241ca520f2039000c003503607014403c0c1e0b0108034000300501000f40350001180e02a91503841405082d01c1d1505c65003c544c1c020603807202cbc18420351200c000007100710b455900040f00c583e03500c3d0030f0301051660155142e00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 704982365 1250 704981115 704981117
    0x1606090e060d0323091017060904021f0306080319230f0703020a0b16020f06090316080d05150f04051006030e0c030a0c260d1809140a0606 61
    0x105850441e50003408911403020a48101c11104001d03204403090300b0101c4001c52030050000055918552001d0040c2c2412020601c47c140c1c2c02000a000d030034014100c9001c1d9400402440101d401000f402031420180c404038410141c540b01e0010340350720200080e00115a10b01e030008040700c1c22801c000c040a00c62000186103a03880e06d40e042640b82d00c41c003200c50420041000960318901800c090b880e2a42030f41c80141011000804c01000d038012107190141100d00e40e00b91101c0740c100341941aa101c1c01030b00c0d0000b4a8008104190206040c2550500d2031032181112038102184101101c04481c1d044a0440e410b030030801c8020160702e419000342c068050203e504124500f40b0400c0000d680380d4034012542499950198050006003c001c0301182e1303d8001c08980f0a0480380c500404016030703074814004041d40c03000c103c0301c2081d0441940000e0701401c1c002842110807401c0c1c11181c03960141301c08126040c43c0030000c25282c400f03010b0141000702d54a803e950b14101110b00c2d81c12078400b07a1001e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 704983615 1250 704982365 704982379
    0x31801180c05010509040605090a09031b020901090c1403010e0a060f0308180a08070603140a0606081b0d0e030913020a0507151821021605121606090e06 67
    0xa00014070500038141a01c0c070a180107902e85030807102240042015420255101124600304150b8034a02d80094070041d10907a00c01380c201082150390185840040b20095214001800521501805038005110002c00d4900f41500006508005a842d417084e001108010401400c1011004184c000c5400410600090594462454458118a0161710508544c1501c0200c21400541e141e02c05580503001c40c2d001c1d51402556520050010300340420010f000e151030100007101d41c0c009114150803034189481e17070000c03a641c420304840324500c8181500c1d4403603401d206950003c0c0852040c400c0010b20440150b540380003400800c0600301d0007482554040340108004c0141c60340c450141c0e032200e50302ca810400001420320f200c070054440c08505a032100040880c0c0e400740408001402c0100c030707038140e0b070040301840781404030380721800001d9180310112203004c100108d02705100d41118656154050300e00c41c0c03c030010550000641d82d030001300000e2100b8414418528009140b507000403084a01c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 704984865 1250 704983615 704983661
    0x905030712030302031306020c0304050f0411041203032307110d1d030a051606120204030f0311030c060c04091a031b03030705070e040606080619020d06050303031801 73
    0x10304107200701c00e00000c2c105a00840455220b08144080700c50155220300c096403502e20812203240e59806c14032415104403024008003c1d01d051500c0341c00302d80e94020458600e02801d2170080000ca8002c00b000714101507480d18a0b01e0001d1060014020903105080031390124208480001c0100000350481d00701c42c0c10a0040c0c2d03c03115040b800030384080b1100c001034240d21070400002420880d001d10003500342d01400e440c1540f511800c07036003001511400c0d04c1d603035000300f001d0034450101e00607404010070a120312045071001c40d000b02880c070f445145c1001180d10700781c1d501c840c2d07500f006ea05880788031a0f804085000c0c4801115401442050b03032000160342c014140b4000001c0d0740d02000f290000442030f40c110000713003a4a0503c00c0752156a0003508035480180d4520605000b04400c9600303890680c41e010000c04d4900011a041c4d01400710030000c28450281034020200070740c400d010b0500000c4e9688030000e401d031800d0010318450343d0405100c0d10101140ba200d2070969824501c030304620901e4181d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 704986115 1250 704984865 704984879
    0x191b08160504180501112215050f04030f030201050a0b0613030b0a02130f090f0b010e0909100c03051503300f04180e0309060909040f0f050d09050307 66
    0x24040072200211004200d00c00a803c00070400c218400b000f5219500b0010300240b10b41c6018001c1900c50300c40d0072444c25540b010444104001c900d4020740076980c0e2181d41e51108148200080c21002c00700401e0949095600d0361000326034808200c080b0050b075142e074204140351517688211856501d0546e80c0c84d18010001e00e80071680401400b000f0540c40882020640158580c1c2c107a030201840c1c001d01d13402054540030f100c4450301031840744c4410281495020b48011126004140251a040e100d61400030580c40410442c1e8500501e0310b00d90f0703c11102004042e54a5002c1c0010145964400180700d0800c40306d0b4509074251004a80d02942c0942045800115411224900609822151100400178000e40c001c00e200e08007581c016160041000304595101d400103225407181a40b0400c45881d051904075100c3c05004e028550214060048142c10308211040d03a03400343c4070f14030300000e0501966660724aa000d00300c09440039400704007030200c101d802080031809003404030010844180340c200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 704987365 1250 704986115 704986153
    0xd050a0c0b1602040e0f061017031804020c1f0b0a1509121104150501080f1012060207020622090501030f03110a0c0602100b0409080d0509191b08 64
    0xc00a01031907581c482845d402c4001c2c8041c42c40c50003000c1c203640150030064010340c044180d44c024162504072041c40d44030814400001c88020b90340c0703175a00741143c00d40034007000000e401a0800300183d018079200d00c1c4641c0100303907c4031310803d406a00000c0e1341c20f03e40300b44141e00000d50001003188500b091040c2403680c01c60490030403a4002507040703d10410519000503003045451903a90007500301541800c0301c1d101d00b044002626400e82c0e60a01540d40d0400c0c51041103002c0d02d0b410301d6032501c3c081c14004415003845110b40c0a01588015280007403d074042050781c1d02011000008154a01c58a40e018100c03031200001418910300a0006504580b9518410600b03414010240100b09101040d9544140301e0903130110b401006206817207503148006519403c902180c100003030300e0442048040c1ca040c0c403602c502d2503007200c3c089080100d032500000080402804071403a61040b50011305058405480d0320390201e11659040419100765040300d81c0c1001650095403031340c0c002d0f0349900142c4030002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 704988615 1250 704987365 704987407
    0x20d03150e040311010507020c100c0f1203061d07030b0102160501030b0a09020a030507201509070b0c0304090b04090f110105040801020a020a1205030708150f0d050a0c0b 75
    0x80705000e456141c1d481c00341c81407202e40402c0700c56542807404100ba09500800e081c0b82510003075a03800400d00b00142c0899009030070742ea006200b4101c41e01900301241c8803007907862503a1414200014500d482d0301c0c41c2d0b046903205105c1412200d00c2d40c2c08001c0e1304c1d03074140241a0203401c00c2c0003c043d20503010070a090140154040e990400d552181d80c1c80e416a18511454020f103403c1104560320080c0400040103003004641d0031000c00c3c11920b81164450002812050300d20784d08024101c989401010307200300e0380018040359441e00c60b640022905000d204000d08800780c4100c01140e07118540788154055600100c0524882d61411040c01d0100d050480d02411141d44002801e4043c0b9091005980e640a035412040c1107600c04035502842d280c002074240f4450f40103400321101030301c11a030122006d100450700070380017a01c2c0a010401410b400b0a81ca0540400200344003070b9200c40e50085003042100075401d0303410398051080a0107203d07185082030060700000007614030700306600703440e408044109 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 704989865 1250 704988615 704988629
    0x106021509010b041103040b160c02092d10090605010f120603380601020d20030d1416020c01260405030307110c090105040c17090607020d0315 63
    0x54001610160080d0f0001c000854010030800008079501303166900b039001154222400480e82000c42c40c10750b0000003000c01401c02e950303040c091404c3c1d035080c814400070141c5000f895035510306041c3c003041d2a2001044507400c058112030030303905e020a01301008120300d40c04800f0407803030100306004603680304100b1450200d843c10021803d4104030802c9008007850f51018000d068100c0541c0410b207500481c1610005000c00164103103c0d500c021b014680300c068443d0703405a48083c0f03a100e50309001d044460910080c0f6003d60b8411804001c109080d5449004811007155a550040c03403007050204001d904049141c1c80014003144500000c1d45e179135008890b1605100030702d50007000ba4440e0494900044503100504041400c01d4a401c5660b900152074071000f080303042402c07a28075000041c05042040008180303160607440d000600004040c0700c0300130400c100051030451400f9806050450203510300c10000c0500f480c06020090400c14581c880008060400c4104008408852841402e0f0307014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 704991115 1250 704989865 704989903
    0xd03140f04050a0b0702060a0b090c0d050903070b010b120a090c032301110a030b010c03080103060504080c010903020703060e0c0607060e03132702040308030f0603160906031109010602 81
    0x1481c280316141404140340209940050784c10001e84a50101c0c5860013254000350030f0000c80f411b01c04000050100300c990034198081071107119103111450300030781c5e003200c507460650385043d0315a2210700103070f4000d800246102000084d002015600b2204056002034641c00030080c025050b500c1750503120a601c4042c165400c1940c1500c606c0a0102040028041a0b4020041c01c1c030451180c51881d00417020800200b07192000803540c1e940244d01404840341d0590310801315070f08580e070740401480c000d0010380302980306200c0b122050b142445a1b607a080e00a03001004000c2c075524044041c4d845055007600d442e00700801d91a0f80b500c950094444c8103905c0800400c101c000004090300c1c0d0f0181d0b100e203080710800d2100c00150450310f250300c500b80d407911b1208007031010401c01014099120724800206918010400900354049100d900c54105c98028160b400055851280d205040e103d9040381c0e410070707542ca90400400c80444203668211505848100042d85440c0f406500c40d20b401072102c1201034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 704992365 1250 704991115 704991121
    0xb06060a0e0904150606200c030d050708160b19110f091203030c0d0614010c1b0b040b04060201060503010504050606010f0903021306051306051311040504050a0903020d03140f 77
    0x250100361240001c4c200700d0810440355202c0340109015415031080c210032010b4001c1c0b070b480c50400303c4d844444941c00b4004003041f20403030200300c1e0780c1d50003170100382c82d980820b02031105115a00300140101900845400361a82084a8507020741210440300c030004510740884020440c18500c161002c40000080c03058a924464000c50307090220301c18040b0b6540400000c0140a80c00140649001519890100104c0f5120461902c00704c0e94100074a00ac1150584078030700046c5401c020182c1d040704940b000c0c042e16079030403c00607240c00c280c10074107036500081028894264244505801444110700910480c1010f0300e40c0c41e211000900054104004110b11610084c0116500c07401141d0290520501c810500101002407003140110340c81016180d00440e01083e0901500040d00c6c00108200c40b000a031000300f1008024451045107500e1050200040c5035441d03215440c455001804003142d03511051038000d04201d50460a90249441c08020a001840146c0180c1c6d000c0030010794407507039071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 704993615 1250 704992365 704992373
    0xc050d0c0305010513050f0d170c2a1b060301050f0109180c0e0d0c0e0624130f080604030302030a1103070e15280c0b0f040b06060a0e0904 61
    0x3600c5070800b400d03d60a107003d101d11581400c20001200380a01c2c2510f51040325200c2460700c41d0303608075100001070124407030b0f1103c0c0c00d0506036440d0020803a00341d2a14003c410134203181d000a15000b501d0703510b4800c05101816101c244404500d00ca4401d14840e261b00c42100040d08900040c0142030041240b280202d40e85d034024540c540c00b81c60f59a012940c001300e0305038242d000e000c415a442000842e5101c1c0703510b1a003050354aa4000690160302c41c4101d03404d00744001c4810400506040e40321840903c0101c07010503443c5940003400c03120400070350300c0b100950708100740c0c1c8040d4401191910030900c1040304403c00701d40c40d90002c0c3e040c6000341c2d407a101d001d8030b4006425032070044d03c3e000800200f0701088507000285c3c2d485c004001d481c03051a8002401c041400c40c0610325003544a00340303401680010200d00c1d81c100a0791f80207404c00da0300d80300c0c1c29110101200c20440c0d00c6140006000300b884284160580880d40c0541c04a820519004410000800240c1c10720341d081d00440d081c6020034100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 704994865 1250 704993615 704993633
    0x90606032f060a021b0312070f12050c0d0c02040b090a09060c0e0a0e090f0619060f03110906010c060e030a170f3d1508040c050d 57
    0x658000c000900555149aa078644400e444010807004072444900707841e0a0802509a900400c242d4011303080c2c04903d5080756849205400342c4607414025050f030015600016009170050601a0000d054401c0080c0317400010004614010340c18404140214a801d040001e805076500403145040c0400d203001c0c0c408100549511460306912412039000c200c0800c000d03502c42d281450017140180520040440e00b61003d83c8000450b07904000e43d00e00921075101c049020710780080120048a03c1183d08034401030a00c903003a12499404000c1d0b030044c0030914054040c8130302400c0c01c1405820000e25503070798100d090300c20b80c030014040e011410010303440307a003d01d00342030100d50000e00910520008a05864681c0d03c0045d4180c04a01204048088035040312441071007807441c1c02d85c80d0529180c1e03400c0d108811071083c0b04040111000503079501521403140020201a240030511440340b428100d000b85654140c101c0d000c04c1002d100c0400c404075074102000000c8440540382a54480c800742001d41e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 704996115 1250 704994865 704994869
    0x3020f06130e070c030206100f0902090616060905163f0809040609050c0906090d0f0c0e090105070905010e030102070602031003140f060a15050301090302211c090606 73
    0x404900b0803c03054982000192a200d031195083d2a0281c0d60320200c8419a8010b005810600030b0500081c441080682e00500881c100285202d080c41a1060380f5081c1c4603011404a4015490780010f00030010108082c0400200d201c00103074226007091110b0f004070070b001c0240e9010300202402400c00900c0200c1c1d03102ca08071817056083e46600581412006e5900401009008500d800350010b012101d0303200d0769005000c6062001d03c1e103042d4600300032240c2c103d5402075611030410500100010180920003200f24072039450b400ba4286003902039204550000c040d1401641480c0412120a034420148402e070740d42420315103242c200c410042030081c0035114000f01311500c0003040c0300304000e00c011039000300d81c855812210130803404d2120036100c1982d880d0344200b55000e5000f00f0020142600318003080700c103500c40c0122013540c130740009003034540c400020380c01340c0c000c52014100110b40030000d1200036800c11a4a1030101400d02d42e100c1d5045058000350300603500c04c0c800c82002625002140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 704997365 1250 704996115 704996129
    0x50a0b040e1b09310b060105070c0b130e040f111807111914010e0c010203040b03131e0201020c040c1b06060803030108031801030b1507020a051e030f01050103020f0613 74
    0x4400440030351804484c00d10300c4004d03618440a100021038544c403a60403250031a52100130220002e242c46036506258000c100e2094140c403081d07502180038403462254038031440c010303850381046620600703020350001d5022410b20b0003a0720010044205c0010900200e4100303402c0d141402040c2000340000d420b02d040c64074045d40d04100b03024881d00380031408a10384009901500200940020320002669542211001e540560818041006006a03490180d0b50000c80d80801e540c0029890795404403800c00c00e1032400803d041c81c1100d0040d035138104010ba01c21501521f01304203e030402c0402500c0b00750801804419445980d03005801c100980c1c015500600d1280f048035244d584a010540e102d030401381c0030006100100740d01c3c1c1d00540c17080c0141134600101412441d84083d0782c10300351045900c80902681c106240d01c0000607903440b4a881c80c1c04800e202e0007005803981c0b200d801c141c14a00f21101003041c1c5d0781803a005001698801d1002081c0030021503805a5405c49030300440c04103c03050780145 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 704998615 1250 704997365 704997421
    0x50d1a04020409140a030201050606090307060f11120406030b1516060b0d050106031719030203060d050601060509310c0215100510020f0607050c10050a0b040e1b09 72
    0x4c14040070004810b19a05e110750003d01050380c0e01c034180003a030700410340c3d580d88c1a44070f03410400005018007254240400c0f40c0c5060701040392412042487c00d5030100f40140680d400050800546605214440d2001411155864100803595800e00980245c0c4085c55101c01884204010000c0d50340c000c1c1340c10400901240d4101406003403042c02040e140c4001c6d00c0d1550100302c450341d10305940080701c00d6080c02c03200f85c0c900c0c0304403004200d00a4100800c4a50440c3d25444144040340080001074020f145695a40d5a10000c0d02c0c24001e60340d500d0302503600704600041c40300c40d00c0c00341c1c011090403102010200107002c41044408900e4070000e5201103034400710001c240040d808003020301c50180d50081e40d00c0e000c25440b582040b03985114020407862641c00c82e82c00314400c5803044008144501e110b00450b072440b44a900542c08450068486805541e903a200d8109036007414011145080b060002415044203514481200c0600c3c0d80c0d0030621802a600008000c04800122252041d40c108101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 704999865 1250 704998615 704998643
    0x3c0825050d1505030601150813020f04020d0c02010c1103040504111201060e01021b0906190f121205040b0d051e090a0b01150f12020d0c0c0c050d1a04020409 69
    0x1051442c00340c1c05401d02a0242500208449000d010f03000d014480d15074490f0340075500c4505a80112010710030072031340450104000ca82c0359441d80003400709082c80c2c05002071480c8090002900b10303052110103506115003d8840307007401e41d0110070f69003104c6095038081440c4030300324604070300303440303503104908500c00205c0000c21042d90000ca08408030030203800b220708403150039a2003d00e48005c0040158031407104c90001d080ca0614030007041c1c0844051a292804507110011400317401d00c944c100040b01c0e900e06070300d6418012034042184404804c1d050582c0f8045c2840500c01c1c2c40e200780700001e1445516a004101d0f10f8078030555462124861210b541218182030f060b00d6220f100b07808040d600c40d038040001254850004600180038000c0f500c0300d6060070441030742520007820366109180c0c0c2540c01d1120785a81d80281c01040c000b084a540d4605e8010ba02e40760159500039640c0045000f030542a0603807001070340c4803810351680c0f5400b080f8400155142d20004010300648031004208951003484 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 705001115 1250 704999865 704999891
    0xf0102070b1509040f020d1407290301080607110a061401052e030908040e07050a021c0503041e050706030b0f0d0209060906013c0825050d 61
    0x4034003548001c07260040082c80c10007000b10030f00043d180174081e42c1171051590014600341e1305030050b0707500c05c40440103081c040c00142801e05000307602c80c1209a0421045a240030080d0142d54264000c182e100c500b50b50414840c0b50381d412001b0321110900c04070740c68083c843d0b9001c2002c0c000059200400b84800c003840b00541d2401c82d002e218807400745000d412080701402c0d140a9003900a5100400c44080349605581103000c6c0469010684035079104200c04a50341d100745030498400e428540703440d81c0d01c03614140002c0c40d00c071902551665980e0985040a42e45078490102e0340c016400c0720f0304c40c8660721010b06150021442e00703c02003c80c4281400043d8164040d005114201c0e011104c109840c1c400c4018000a00b001c490025030002c0b03440006001e928001040c04e800c40d1043c54001742c3c0e80c642001b50311180c0c1e0b00003140300700c0c1400381000341c20800c101c60480c40002d120746885600c40c105942c01940d810040880c1c0b0401d4900c10300710000c80c0d07110b40b09070b03071505250740000d0144141c40c3c88 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 705002365 1250 705001115 705001133
    0x12090801111614032821050a06080a0606031202061b03070519020a110312070803100e0906060906040c08040201080403020c03030409090b010b030c0d15090c080609070810170f010207 80
    0x194a1085c0f20f44401c038628481c012110340a007510401040510841d0341c049103001810020b00030016640d9400000c43e140404005100015108a0000076440d086082960f001c203080e0402900310b500003000c10100740400c9240c048552081f4000c651203850b010b5054640b405030540c0c04d9204076a0070044101c003580094910070407402400358400a45490092544404c003807480a0700c04081040250001480756004660100c04260708403151512a0001414014191b80a461070b5100c0790601095180030340d4155080201281c0405c19111103c1c006001040020000fa040c08030b01e01c001000d040c02804894000e6000a060fa80d0700c40c1c490f030055008046014040d9145129100040f41508400c4102e9000f0200058500c3c1071844c1074020b40054549580711110182441100048061260003107544050b50750b160324185141503028007a40c0f92009080324104401c1c0e40900c04422130300004202610005514030840803160260a0725203082d8504203150b540c400141d85081c020841 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 705003615 1250 705002365 705002407
    0xd0b040f09110907021f0603060507020619091208070207032a1415070807051912030501030210030f0b06121b04140904050c04091209080111161403 65
    0x101c1808210b0742c1040c4840320700c080f0703400405a0b00500100242c201015113a100810404101159032500c03a5a01401d94006072082d0015900810501101c40302e0858060100340403100c08001c1c2d86100d445039121410300560202c1070040110220b0b041034402d111540103540c100d5207410050b800ca450368848141c015510145d031525509002c64003903540044201d0305030300202040300d18510790700706010301d9200340e40844507001e04000c81d4001a0301841200c00004c0600b02464054105080c90b44d51098100d120b44200f40c41c240c0188010fa848210405060805140014002c02002040c400420344409180d50040010a01000010603009035034400d4010b507054040072050080703248510701503070085210072088548003999500f490112a60b000340030f50101c8103581c5540d00490125415201c0a89211580c90888600c15800c4035000d001020740358000c101c00902d060400700350780140d18512900550324491041070100c04005a100c0d0701e4110287c95580000902502003c400302d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 705004865 1250 705003615 705003623
    0xe0604050c040c0516080a110609030403020a050405040201080a0f11040803090f0102191b090905010605030c0f090103020d02041b11211207020304090e070e18030a050d0b040f09 78
    0x2a0000f501c141301d0402d03580000c0c4071008103140045d680d030310840941c000c50203000410841d0100713515032940c02c1004501070826400919910780c00c50042c440e17151116002039010720300b000140b10040c0d034001074a651040340c13003800044000103080c032040074043c07078404c808032680d0116011440c404040001c10210310115208900d1764020401603885441c40000c01e40b003007070483d40342008100d840b2281c401c030901d200a07400c00c06403111f10710011201e00410a4506039901e00f030600c110b0404000e04150303030000300c030f17894844c1c0c03200000514240c405000080c040d1503103002e0403085441d50b4200c4503100440251500c900840d40100520710700001c45545014410101d00b8a8080c2000424031200c0308045900b625010440300c0700100d09801904807400c41c0f000300000240c800b0103209007000030340c11402a2624901e425240700800c1070180c500c40410130080700c0e659113144d0000803545038880c1c80c10300680b034200c030560804c000c01140b48043c1e005820101590f41219080d40511026481 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 705006115 1250 705004865 705004871
    0x7080a180b011e050a060e04090204051e0a18151404080d0f051b031806010b04030c0506131503060b180102060f0610180b0a03020a020d020a0c03030302030a0e0604050c04 75
    0x103c0c4503256040b18942c410360f0342142c004d140a0250f2803060030070601e03a51001d4030100b140b000f1580440c00700c84e412100c075034014041c8403401b1403070040002c410f50841c200660a005151000748011311030710503424001c001da40419402014040c07582c004400d1004414160b1030703240741c1414840000d03072211800c0240760b031914070420f0902c40284100780c05011380b50107040303000d454126842441c0e0b1000d00b101007881ca062128460310441001501d0107049408020742d2210310314a401c4105000039007045111709801d1020008a08203050400202d805901c00e1f41400e541c1c0b42803d40c01002d043d0041c060382c003c0010007054500d10004d050041020070b90843e41180e84682c001440b1007030640b05240d10a40c13481642c0c130524812800c26003c406550b980c0c0c1c0141c0c2c3c1e6011104c9283e80510812408250003040b285200b41d018400298400c0190003d880044a16540e8600840b080e00005050503400700104032020702c0d55214003801030310034049508a0506040655403000d440d1021881030b42 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 705007365 1250 705006115 705006149
    0x50105031e030405010e1c060b0f0d050331140109060c020d0210120203040b0f0705040e041707050109060e0d09031a0c0708030103030c030801060302070b07080a180b01 74
    0x18180a81c20181c4010001550419041c24011200320045600417640040d080780c080c6903c0a42c07603440b00034244501c00c0028203249020501c05031000440115100d4800540500302040d07010084581c1251070115804004011000010321800307440c05005d0310f42c000303100228189251040d44c00030b0700003d80719104a29524441182e00c1d0211210003508202202540c1c1d0040c10651022050090b1500b050424040b64281d540100d0300f00321015641003080205110500c4482041560052410301d080c2c0c0c07070300741450030702401e28001030070092000b00c806214006400030042590403055200000b0b200015960070510044c020041794880039008070324041c0c03407650041048808682e0301c26007449020400d00300034045503400030034440b1250810401480022800c800860103140b207a201c00d000316485040007880f6100c160440710506104000340b9012030352418402c1d07400401ca180c0a401640c5000c055400b030700030714200715403014014000408010310312054605848140d100d01d40c60321 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 705008615 1250 705007365 705007393
    0x81b030c07030c0203030409140618040302122506020c060609010f0306090203010f06030c0801050604050c1801090306150e0901060e01120602040f06030b09132a0b03070305010503 79
    0x884140c5000004000802a4a0001c2e00910303001206030300040949082641d10038481044e074485000c0340d41c41d000c0032000c014040c9031200c45076840307081000d1030f1401ca00e000d41d406551040010360150200784007107010300214508505c00340b1585c02e81840f02119030340302d1400c074001c1c1d00b00290070040350140310b00040d000d05004040e641250045e84420419501d1501d801c4000c0c22042c0050b60195240c5920a041c00414042e2600031445040c0242409141000c3c207421504007070b024501c500d003050280042496a4810f0f00d2504910001412100c000c02c4016034401e41164402024076042c2044806048143c2c903400c401c40e11800c030140da441e5500c903960f07801c07618140101c0160b220154010300c0b480b0000401c1b0b01c1c4541c0320390401407400e626400710545241c0c05502c04c0c8002074485200540380d00300001d9980d000047d8200c1200d2002141d502d051541e03c01d1903545266100204c050f07416030a801c24400300030088951466543c5c20901402400340000740130740d900900c50742d4a40d076040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 705009865 1250 705008615 705008617
    0x2e090201050a0f020106090504050d180e15031e160e10060f050f0705010c030c08190e0a140a0b010609060203031308070506070201050a060801020a02061305070e07081b 74
    0x49505039512894402404800e4800d0920401844219980c40ca00821000c404d84511070240307016900820002e40d000900901d0f085110144c0000c1d034081210422040d40a608080d4020b803200c0e078150640705200707011902d40609106540b60742280c01c50611002c041c0400d4201083c0442c80c03c1c900e44a40f1205044881041902c400f0302c120b9641d041049135512858111401c8111031500c0c91418815007912143c4c0e421940080d10303e41d54410b503101c1526010b114a0141c04802d050036140751400c80d090360184452441c4041c100f60b15a1803109415200b4003010008640c058071019440b1401d1140c01c0d9502140a02184e50200c1c410010605a00a0303100d14215102940150300e955212046107482c0300b4400411102940c0c04d025240c0010801d000c503600c00c240035400020709203040c0281c0d40584507160301a0b0105e0344108030b048503180d400300c0c2d002d41c0a4018107a54a10292519040b803401005600011f241130203401440503c591224195005904c00b90740c82a424014040145003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 705011115 1250 705009865 705009881
    0x20d0b131b0234260d0815010e012115140307030f080d050a0c0f0f0203124206043b01060c060e07080d050c0f2e 50
    0x8020810103c3c1c00000455550403030401c1d5080d80803e5140d403072040b84100a0f03000003011103080210314206611004201c08003541c0c115140141250502e03500104562002d04415810440b540304181d0203a40107007507003c00d80d0310341c040c0c403008003881e4541c020041c0700c3d104402c135a800c5811000680880c6c81080c980702c0100007400340c0340385071035075171070f00080b20030340c1002c5500090601c406455540309100345482103031507071004503410011034802462050f10f0000ea0741401011031072240384603030000a44103e084201d514092980303600c907298440410392440c0165500d40c00e209403800303c4d8003012034104150b40d40c020b618102104020050540070310300400060010359200e440408070361b098044480c16003040c03800c107510805d00852400072300c04d800980100d8820903081d01000201c0c4200c0e5000f2803030348050708039641070a40caa522001421801400c001003c10359041c1001c0a1041c0d84c00700418404641009141050a421240880000300800701e58048031001d0300c00c80780030b8065 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 705012365 1250 705011115 705011143
    0x150a05030307021f0e03120c06280f0f02040f05190e0705030c070203150117030310060c020604230f1c020402310503010518030409020d0b131b02 64
    0x382c203c0d00c4d03c8824520414a0494030411882c440e0103801501d0900ca10062103956008180c0d9482000344002d20300400503250000c1100c6c884030211007241c07119466030301c2c59119072000ca40080541c0380c4c41b024000343d020000280344001000500405e1200d00c1004654040e076880014010b41415403680050030303c1100f98242091000940980c841da004590103422a0001414490140c000c0791034515400b5002e038002110381c0043c411142d4030940c079500a1003290007149949421f89640000401c588107100034040d002582404654030001614090440c00d6214408546100380100d0034000040c480c0e800f5008104080c4841d050480240401c00000424423030001c08aa00b48002580040c956400000120b07100c0003249a1001c000b084902c802680d1040c101e08000825085a402a003d03141000040510309103807680072003918200c400a0000507103030010400e04e0b0002d0b10b00a112264081107448252103188c0882d8403011114403080503070a0b100d100d403070042c1d95841c00f240740e640f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 705013615 1250 705012365 705012379
    0x30d050405130f0e070e011512180506040b070f03020c0a030f030e030c0109050d0c02030d08060d0b0906040302070e060d021905030604030203180a18020a1403150a0503030702 77
    0x2001504096000d00c010250040c0d0010321290b4000d55a012910b0a81302008950403800c400c00064a24810580c00340a040c000d0a6020102c60030142003255489615088070f80c45a2001c03c501c0030304268651015088001d48909150030703e00440c100c54116101d00125191a03a074a1100e48030740f0070780e0a403128540051041081c80e441c1695101070592683d0101611044160910b140130300c090105114070000200b020070a80c07410354180110403480c14204484000d2000141e9400242d40303c00c1041420000700c00d841b8007012a034000740c90a0040c10340c1c03002d50140401441c002500c00c2c8624066801d44442c0ea45070003108540303000540d101c6a000d10305800c2c02001d0319040c0c1d0381d6851a50b508a4400345241c0e2140480e04000048800340c0150704049003051120710841540803000c00c0803129483d026041014100c0c5602070108140c0c1c80c19404204330000c0340c00352481139039123a5022821a120b140080c0d084030040707a4802e41078040c00400c0800607141c103002055408480c0d0060001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 705014865 1250 705013615 705013619
    0xe0723070305071103010603150207021c08030c0313080301060f1b050c0f01021e01021c0501051003020a110a050f123109061409060f0d0b1003080c01020315030d0504 73
    0x20350034201503404c0e0a641550b8a090000c000b4159014048040c0303000350b00561990214010800106d00c0c01c400140e4645c42444480e00040601b0110b9030f10580801c0b50f6034032600c90602d010400d0741184401068004000004117020741c01c000d0901039840a0768400c80901c0c00344400100003107284000070190750100c00c1c840d0881c03902c02807513144c1c441c043c8121205190f005000b554041071481682105940c002102c0d104600c8101825105009082c414080c0354540008036009180c030381c03011000c065001c1011010a44503854800703580c20203000300c0d603480c9501c6c2495511880480d2800035148030306940c03808160341c508292614071070040406040c92901101a02111125103040f0454030407810002c180f8403040c0c4680005040401d950038101c0a01006010031504054001031064848040070101d03130f0b8034101224821540807980d80c40b507844444082410786c0741e0350001009080c001c920034134070a01c1540503600c02d108001011028089031001d0545401e42185541e00181d403c1000b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 705016115 1250 705014865 705014873
    0x10b010903030f0c0507150f02030f0f0702010507020607060506040b0a03030c080c24010801270215090a1715040209070309030210061d0c250503040e072307030507 72
    0x302e03500f540e003488501e10b036056603540d0a010003500000c9400b1b00740f0344602d980d11350080c00700014048900007545402c03100d0b41c40c0810390150386801c400e8844000380c0102164450401d407a041a805072190f9141d10071807174210050030048804e1405103191010700002850120090001c89415460f440c041950648a00540c0c0d80304680020b0300d03201e424040c4468188440d510400c0c1250400081c24950405410300c1c01d4a03c001c2400340c5024009030030118881d00c51040d000380641c111188000c210112a070b0a03000e000721900f85500288203100040c42808011681141d107040c0429102010001d0709010b031282800c0d10007a4009800b41c0005001500039800541a64000c0c0101c849810b001000c1c3c0081ea407040e00903004039501d001d4061250320000c6070ba00e400480d159400340c00c000c13132440101140d4035109595070075855003881c0c81003881800e1049074094105440406810320b031166015080d51103200a0740300f001089001d0030b070106480743c29100b1007a41982c0301494400d03d41c035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 705017365 1250 705016115 705016127
    0x120703180602090d0516031407031106030414010513061b02250f15171b0702010c0b10081b0108161106070f0e0102030c1002031909081b010b01090303 66
    0x44070f582c1054800c2c08074000b241d01049481055042820060035090441c98008030000880ca02e03220254841102400000c8074020004c040300e80c00c0e0740c51510303a40c1d00d081c201000c40030402409119440e00d4140038103d02d11404107040c0a000e034109001040385140345106011310200000c0040c0c000303860042c109140001000c0c00c6e07001003012000307010f032201048500b26031b5a41c403003106000615140300040380c10980b00d2101f001c00325608042843c01009a1001121510415450b40380002d103074411a030142d0481c1507207580101802e002c2e4940200c3c04191111039000e011040d10500c08107182907802402518500c09042e03654000c2c42e1a06000800f0000e030344003010060000048800c03c0030b15040000324415038080d0344400118a1880b030107001e10b912040180c0c1190001c000200402800040c80c03070408049a100594a5889442d24810302e291410540003850906164505000080d030140c01c4c06c8408103002085015440219400c035030845e0301486c08607a03607200c1040441e0040c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 705018615 1250 705017365 705017377
    0x51c050c041e03030806100c030e040f020309010b040612030c0201030f060314011d0106050607140304050307090b04050f040218040507270516020a0b060a050a0b120703180602 77
    0x10007030a064444041070481d55009400380e444401c5030381e082061660042d04c90b90000400e81e0449500a61b0640080101d0f01d0000301a050106545035001c85850703070b51044c52840508035045480b400d20008890181c03c10014080c80340c0d040c076201182040f80541185007203a41070f12002d0005c0c032a44e0041d4082c100c003056802c0a141d98802c0007000c2032081c043c600909103504000549100c0708002c550074030035000c40d159110303072428409000039120301d0125245250031030980c2090b801900e980601c0c600c203a820441d054051030b9400144032543d60042e00440d45e0460b000c0c440c941d6aa41f0003e28594111800b80d40903440142414002022400315604280181d0585130160349810a812b09030320441d00c840b00301120340751300c807190517030503c5969000081a56280e0840c0c201c003c000707564080641c0041c0007031030402d010070034540e40e4410540080a01409011186544003a1100d0680100700d202e10b40a11550002d01103030300c203109400d00500900510b14200a10307031034a40c025001f85d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 705019865 1250 705018615 705018631
    0x90304060e010c0b010801140a1107080903010204080a0b0108060703050c03060f010e211c1e0207050d082a1902042705150c03011a07020a06030e0706051c05 69
    0x2014059004c03440528005029055803800440c1c0304e00748509082c8000c1c002022840d000780f504101c9149640c0c280e0444100e02d400145650b140c0d01c4010010380248139540c8003842c0c610442c130004e0700b040a003100c198102c075451010755a0a5072104c00c01d4007a070300c044600c1f10002104000003405850309001e04c0d0030082062400100c8640b410002c5844043c007109010300304450f040d05d25034038010030000910798101810b0f50808149642d1805049000311901c40380178030350790582d020806031080018100424004048452003641402c003a40c1c40d500c400c000c1c00c0722502c19004103824018000c8100014a0804d0040040c244c00c3c4800e400401500340080768456141c0e18440d54080503003000704542d690010b00310f00d04114520b0124640310b404000007e9156561040180c01c03108001a40d0455a011440c2104e500900e10600c1c0b0a10030b0b180000d40c02228030402080066141c4e100c1c060030401e00c000c0f940c105440c0d00c0107403243e001d030605662036110920110303641e1001503040240c0040395 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 705021115 1250 705019865 705019877
    0x108130b01180c020a0b0109110d0903030b01030b040506090106032316020c09070827030c070303091d04080d02092205180c0114190e100206090304060e01 68
    0x216514050408000c0e80032030080341c01a411031100c4905031103020100006800180204007440e550306205c1481440350442040e40c8000c0c5a000c004000d0484a080b0f2060710108003101c528600a402400e01004850000b450156400100d060901c10a40034481c010444102c40e03181c11000c13005050401400344c01050003103000b0200503a14110326024150b90107441c107400d8800c0c94020702d485000b10647d441512013005201c40c0c20b81241c2c5641d04049610400440417150561400155004202c00445c42c032000410061817240420604281c9100795102c02b0103995503400040300220036402043d5412540012a0001d540c84c0e000b4080e40118603005030400c2c404000091508001240c4240d1500341d401c621041c0316006c3c841d01c0d0b40a19600e000000282c01c60701e403a99503046c80c0d48098188050058804807503070201080e5059900854031040040e91001c50050038004c2c422882c1e8040c0c502620104445800800c034541304402000c011801e0074a000801c0f24100b096007485818000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705022365 1250 705021115 705021151
    0x150b2b0e0a05030318030f0a05161a060405060405090d03020d140702030307031514010513030606150930030521090c041518060506041502060901060f050108 69
    0x300078069041101d0242002c2c60300d0789130001c048000b01e101c1000c0c10100b5007007001459150b03d181c0050382e03460032907450001d444110f0321109010303403540e0030350250100d81e13800502d55a44400030402c170300c58a0140c0e01031095071924424402507074419262214250040001102541d1080d40a03041485d600030010503070845070040300c0b8540c01c054075002d006810000402142c25054020040d00301a4441c1c070600151030241000746a02020750081e04100002440261201034800f49601030b6801c0881005119a00e5a003c102049844003000128030161400142c6280039070114a16104c0048003007080c0000302e4840c1402010a90114184030083c010b040c800c1c0c5081d070014401d410742d0b0702e082e941400d0840c1c1d5985420400401c1074807132414401908a10810000d400c403c68407c50001f244600450b181c4502420560300001e40106003ca400a0740c4c894a05400c49600041e809035040703503d400380c03c02c0c01e84405000d285440b5190517010007040d48144090b0754002d90080903090003030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 705023615 1250 705022365 705022391
    0x11010605060a03021201060809070501121407030c0212040b03011401020f150f01120507090f200a0e060f04050d020f0904120e010c0b0c0c0c0a0603150b2b 68
    0xc0c00c8050807800107a400f04000245c04e000c1c2598901420031803d010300c4a2074254407950b5600c1450140e5810003852100c0c10750301e250740e900600003000c080c96801443c3d16043c00000c0c001c08102d01e904006214600d6107600c882e9144080341c06846030810035500e1a03081c00640c00324540550081811803140080b458000c0320140004800000312894400c51424400140704041406030806041ea225003400c18000500c000b568104403104c140303000c03c6c05a65406180d00408101c24501c54111a254051034030b4035211008041d00e44c51600d8410010400105001031401100c2c8200e1030728004100038802842d04d04401c1c59001c0c4010701c160016002880807403614041503404440c40c94901c40381743c4007140c102070486070410007842d121240c0c42c516254550743c80005403003010103800c0000c440120300c4060140081031007000e80140c00b400c2c0d139041300800908031000e40d01e0038668402c0303020440d1a83c010407034100302c00c4440070441c4661a40408800302070b02000d14042c0a80d6170035605440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 705024865 1250 705023615 705023617
    0x40905030c071712041d1506070b0a051005061804090602071101020c010e01050405120f01021201080f07030209060402340b0c03010302100c0c09020301090c2006071101060506 77
    0x140c007840450b04407034044a01c800746800842d440c0b28001396018081840700201d101200c00c0e00883c0e485a552060305d03594001401c1548441407503800c03420001b22071052041101c0954062071681008100b259194904a8111400350140c980e0214040020244140191600c40c02a0400500c0022181c540b583e407002268051181214a26811342036814950307010300c81f60901c01130a007850a0181050800200544240c0c002d5a208941140400010102c200502c9052140c2807000710355800401c01c0078040c1100034818445248a0f011f0398100240e00410f59a080f01e44c043c00e07800751030311030744200301c0650403e0480c08900300380010000000ca682c444001c0e00f51309000b990311088400380c10584100480246200c02c40403017080100010b8031041ca000c07490b000503280c2020000042c2c9008842102c40d948001c01441c004400440c103454250b00000e01030586480740b4803c0555205100444d5810181205d82034010400041103c0c3c000d2502450703901c58507000140f9681c40300009411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 705026115 1250 705024865 705024869
    0x80c011503030309060e0c090613022104020a0f030302100b06090d240e190510020a0305270c06090a08070909142b050c060403180f060e040905030c07 66
    0x19071903004c0c200600905110b01c40420f5540c2015006800000000c1810858080d08060103508072030b01c0040101d01d03943c15100e078001d4485040301d095800c001d041480b42c8041e24160b10400720800c0c0000d0119200d030201e0100c079815009800010000030143c002050154400c0b034005000700403411440d40c400c20555261403103801c403034940740300e072604440c054140c680c01d003501c10740350003009008420009600c4452901c00860308003040345501d00386003490140e10300e000a65002003100750a0603011b40155103d0001154000c007217100e03028903015010701c0300c004202c8036001201040720354100390004040c0440054040740301d1b01e07604e00501c0d16212850b405032207180c0c1d59200400821082040c00e22031403110100408600742c1c3e4061111000900c418006007040d088548100080d0040003620b940c40d480b05c0a840d036030318040c14081e102a084120418840011b001d0109064007990f05181c255080c81c0c0e00d4460b40b102d010180401070090303610990307541c030042c001d0341c0c03441000f0094200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 705027365 1250 705026115 705026117
    0x30e10030504031209030203090405040602040e0901020c0d1416020307050d050c0301060504060e0f06011e030c020d02030c0c0d0204110313051b0607020f1318140a0f080c01150303 79
    0x150341d1801c3e040c001c02c0c0b83c0040d0b07041c881d25424802c054020a030b0000036148031501c11203002505403107034500345000344190390003104d85800c0c00c002c220300004190701402240000c0029a01c0101030070398100c58031403041d80034480c03440c130600c000c072000e054405000041a02c050100c4000799102c0700081c0c8580c1940c0c4089401c0d5100d080820b801341000e0145c7c000410040d10241324280c182002801404402468071041014000014885030310500c9442541c4501191340c0406056404005010b8510040001c0c0544901c1e03a40440320b0344001b04036102a1405c5018081540f103200400024400701801079a01980f64405100508603101c01580078191000b95059191024580941003425070040a80704101d04200715041f030f1545021a50f4240d4110f822040d0006054001600c4046020b03414420b0340c41c2144030f106014407600354002480c01425080e010600c45584140d81e802600c04c000d0020304860180700004000303c0c09000c2d4810f00f24008500f00584034244080803040b41d00c250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 705028615 1250 705027365 705027371
    0xd060b01020f0f161a030708070c12050c1908030c070201020c18060310061809060e01050c130b040f090903120903020705150901022e0f0b040501050603090c010507030e1003 76
    0xb0313814403000e071015004101e030004c1c40360085c81400440001c1d000007852503060202210008400d5441403010240883d408104803011085c8400014007640000c141d0300810f10a00c0d01c1c220000700c01490803400740c0c4e80201f4162465035040c0300c40c042c0d81c0081500301c0c113500c00c44505000641c1d5017003245011111344114080c4d02c1c605107040603e050050590250b400c1e02e402410320030501508850781040d20100f40c003040d8403032140b400000406a01052070400c1d464032040c4907034040c0c0b050081500424807128514440e0301e075602500d1921032885100c40d1003080c11010007208919400c0040703040c0c0207081c11420a61001120820303955104000c41c0160002041403105140c000180b00c5409022904182404010400032350781d94200711101141c8006081080282c14034884200d040d101d0a020030301c50010741528290160042d020910f2060b81803a0005c1031f81c0c00c0580560788a0f04a0000501802801c0001900c0a82c40b951059041080c000e60302d07038454507952280d4844460580d400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 705029865 1250 705028615 705028633
    0xa030f0203011502011d0d030b0d02040c0815060a050913061203030501081207050c010e30012f0906090a080d03050106091a0d20071208060d060b01020f0f 68
    0xa0846d00195038482c51801548580e04402100082562400c90a8100040c1c00544080015881001e100c0001d5105042a000400b4503510000d62402482c001400c904206416000c12400d8016290644002001400701281c07a207042c040c1740076840b541207000140c064039034050300c0f01280c0c05001035010a84a600402000c0f00c01c208490264104e4400c650528400c0d030354264455000b20700590404c03011400c030004ca40d40303a010030610a8a0181c1e0b0031034118200410350640c2003440f401c4c11455103005000345640301014440350b4401030728895800e080c60481c07460034290300078503d0036402060902005002e0b40f0703001e0904000d0581e4a006000c90f0380e40d10401015204160404820001003507800c0020349011680b407902e8141070100c1a80343c040c02da0076140100700080044d02c40d030b40a1030b0700d540010580d0000342041401070381004201000303d1406c0e201c500050f214540c010300390407560f101140c02eaa010316400c950520580d450340c4601001c8518000f0a411500c0f1107401455071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 705031115 1250 705029865 705029867
    0xa0807032604030c06030207060b040501151403010b090120121812060a020708070209070513080d09090c0e0a0f050a090b090a271b0b03090c01050a030f02030115 71
    0x80341c100005103148a45014155070340c8614210340c902c43d078001e06801044440c10080a81c1001c540f41d000a4004c000710740e0359100c001c0c0703095100300082d400300e0801043c034001540040220f0381030382c000e40f440600e4121000d004441100c800408102099481d07540c41e40b030580248040a07099074454170f155100c4d03c0d044141e200104050340d0240c42007001000c8030780ca0b808003003140340c0e1001c0081001611b0724100e0030700902030b10640c400294005140010026410b410070b000d810320386c40c07040c41410700540361228030313a0740d40e400c803014800301c0c9500c0400c200c904216002030343d0a01c905d02c0c02c4680309038007002050040b02d2607003018441c0c005030f81051000b410400c800700e004002c094414411510a06c020500490010307118000c10342d22010a603003c1030b000382c2c0c40403440720705481c00d0000c0607050808440d10110011188880e0b100004e0010b02180100240d902030b01d116000340000c18040401520715900800b0000d003850b44500307012a5a680d240701840c000c0445520303080c903031403440c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 705032365 1250 705031115 705031163
    0x50c030106110c0d1b031a0f061c0f030314100501110304050108010b090a0e0108060a060e0601080a090c080a031d01050307090b0a0309141014090a08090a080703 71
    0x300034010380c0041150fa04076038441840c19007568001104500101465440c0540d00805800260403600403200560003081c003440040c1c8031340c564114070740702d9458401c01c11610003000a4103542340d0313095001c6280403401d6188503001c4d00e4401d08000602e1260510b20610100b012260107196516070f1004205650b0007001c00d03518401200d010350310b02070800001802d18072040c028100350b041e01041900d0280c80d000b030607401908030951006101e694640c1c1041d40d0700342c11030300d010b50782d405d002e40043c266403561940b80c000c03803058541c2141650f031098084002c2100b59420b646030030f0f2569000071503400500852441078007075900c007490311070b00031201c180103210848540c1c1000420000c010030203070f010002c4000e450045008540c1ca228040c0c0480180100002c06403c02c160b03603001c00b0b107200d00019011101c030000d10040c004982c10907045425000d00f103580c001c140e0065405d44001800d00300090a042138010301129025844200c65407503c00306810840351000b0b1001c4003012059240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 705033615 1250 705032365 705032387
    0x21090c06080108070e04050f061914040f1401090c061205100b09010f03020c01150305010513120e0a030b1812090d02090604090b040503090a06050c03040302010e1201050c030106 78
    0x20070480d0965140001c1d00c0d41d01c0f00c00e440b031082104215004a020040184507500122500404640b25428210b03103c0c454001c24088210105113007070001341c1110310303110b48a4411074025200c1828901c41e52910341c4100d80f07601e8403c206540c0c0304c0d0741c03000007a1101480e0018058903581c03c0030003400512403104591015140c1040c2c08580d600400058003070310200c401c3c00d082860b0104c1e01d13030a1034600703138040d000b1f003184021755500745120070075440c50b024020801c0741d0240d0000e0003680c43e800c01d1110044032300c4002030300220001484261907070003800219900c2401601c002c0b80d0b150fa035100e2a40038101910300c000d0b06252a018070000d034404010303510701c900b0742d17048861078480c110000980320504864024000e4110400044140e42e55a002c1c481103030308104080c0c01d86c1303020700c0c000c1e88a44c005501b01d480b03003806020104101d403240095591500744a0300443c5407505680040d80c40c501541165070f48001c25540211203c48203001d100d0041d4022401d46450354100600580782407041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 705034865 1250 705033615 705033617
    0x11040c050918040210110f0709020901090e0906071808120d05160203030109200a031508011e0504050a05030a0210060b0c1c020102091e0f0409021e0121090c06 70
    0x140030143c2e4070385c00c0c040f5884c0002d0800026034241e1401040c100030340317076102d00d071a4001e507000043c200b01703e50010148a40c2c01d036503c140c0c603900c44980c007848110507108900710394002000294002e004003249003450343e0b4039150700c41050b900d012151070424025902c40840d0008a0081070310104d1b0300a642d00302d00c1211b0703500b1465032100c800a569000502c1103407076103515440041c0303034101482000301030015211042c81e6079078042e034805070180111001d090529402e1210020340e161043c42001c0d10070000d2947c495600402c0c842004c00f42c50082c0007a04e681c012403a48200041c0100001d01c210507154018000c81646948078601f2100c2580c400c0445410800410115071004903c1d5560003002d030041e42042075500310101e0090069141098102540c1c80c2c80558008000034440d0106208464040060350b0210900060300d01281c0000e40017030100259110180c3c01c00d03121000f205043c07400741009400c0700f8141510306000100e108a99555402a2080c400c80310b0300d05020f0441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 705035971 1106 705034865 705034909
    0x5210d14041a0c0f060106140f0c19060b0405010506030c0c0f030c1e19081804051924090908090303030a0506030706021209040911040c0509 62
    0x400e40c040303d4030b40303e240300c40d9400341000242c0a06807001907490b081421030100070750019402c1100000707181300c1d06108400181000b00101301c00311048003400c0c200c90801e401d100044840051815000340e0500d0700501454541d10100c2e03810600c1424407582d40c036900d03034415041520119a125882c040080c440300046000540f9071310000e11500510303919010709030002da81d000c2107890541c0900300516444082900c4101910303d000a8504c00c03401c03c40e08500150032558100c1e6081d110140e070141c03c01052009100300701c19924640c0c400075070a116280344501d0001e040c4104c0072442c1e1a0b6000d40c1c01c010a82060b1060818090b048a4490600c1c0d540c01e030103050210f407603074004e200b4508001005803000507190b00c044415500c0520b00320740700702071202401000c0c0301a5810034081314048119222446070201c40c10742c43e03446030b0300c2d04084401c0180e4120134412400c0480c2d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 704856115 705035971 := by
  have h0 := BRFrame.cov_init 704856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 704856115 ≤ n) (h2 : n < 705035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
