-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0336
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:17:08.259683+00:00
-- url     : https://prove2.me/submissions/2591846e-db35-463d-810c-bb9d295b0bc1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 60251801 ≤ n < 60431657 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 60253051 1250 60251801 60251819
    0x105040e090a230c01081e090705040603030509040c14030103080703210507030b0103050603070b1608031008010b060f0904200c0f01050f0103020a0b030c0d0204030602040503010e07180b0307 84
    0x208083c80c03c21107400844992003d10100722402c0c10500030310301903640f81881030a10340c000700029841148605c0180c0000d841d4141001107200402c2d0062090004a81d6403c02505550101d41c00c00e01a6051030b181078a00382c0600c03601c0401150f005415840c42e80b81d0b8036108440d8200307100480402c1b03a03030a003a09918282c00c0e80c1d03c04090644c240018a400c2c100c00203000c4070300d245629418941040100155642c0120342d5000b10380c0300740d0034242d86984240b0b00f07100f0728030041c00082c165103001c8140203e05800d06012000ea500d1340d402003201000703030300810480340242c905082440908115000b03860806410812042c42d001281c1c80105450b850705a2207508400c21024407980329844064515000b401803e4104030040151170095066401048445045000381c411401001011070142107014045600610080d04d046407515200d00d003581c042c0d802407240d02c3c4a53300b44038100014050209554040b6054080005143c0643e4001c11020b0014005201c0e45405400e0b800110300c0700c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 60254301 1250 60253051 60253073
    0xa0906020d020a0f0e030706110c10030504020a06020307051209120105070e010e181b130303050702010f021b010f020a1a0f010e0411040b0a03051603060e0a020105040e090a 76
    0xa19000096128050f050000300100b2040065408101541501c140320381c401107000b84c140c85403851314250440e48100c240d840c1000500c2121340000e402c4608070a410b905a103d940204c0c400c42d95200129601c200883c2c0c0c80c01180c0020b052a04130b02d4044611103480380c020b100d0000050f0540804914210003a402c55204071075840c045100d050384480150780c0700c0b292a002d60402c85106810a000c06070203200d10f807005001c15450b145224410b61480c00500583d00b100046421420380305843e890000d009402c64003040380407a449541b0001c0380707400030452041c20b070180941c004c24054260011161000a01e00150543c061b00c2e8100b000310b0200000c0d45a408041d504844007030524140712141600143c0c8040380001c4003505020004011440c034040c513540031140400c1c0b07166580000790920400d50b10045c03081c0b0424040c510781d6041032140e5011a4000c102c20890035600326a410344130005580000c0c000f400c00c0000388400d45869a11f039070002d0500e8101c541002d115542d44070120 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 60255551 1250 60254301 60254317
    0x40f080d0944030a2109030e090703020403080a050c1507020a02310501050f270c130801150801060b0406080a020d0903020708060709030c0302090603010b031e0115080607080a090602 80
    0x400e843c181e080405c00000e1501c42d2078504110400220440351002400369900e24102d91007003402001080b61644030340c0607100916004180e190391921500801340256011a07409a6a070190f280725088000d030a14040f8401c00c203507009051500030941c00c0000084906420320340c1c0b08600b02c1e20002100c25144120b956000400e0000340f55410701040001a0403402d19091049541403e149401007100305c0350005400501d554000c03e84481900c01524020f10124600948141e0030018640d14150054603a000c603828903003994a445001c458280c0e84c2c04d0040018402c000c01081041c04d11800d00d59901a90b00c6d500182000412070384035040da21044c03000c0d0700580c804007040c41580c80620a4a41000341410012070207490343d990024030201c1d5102c0a4411507014002800544007134000700102c00c00101581c0104511116807800a041c640c146038940d864485503001d00102c4090380c4081c1d0b840c0000130030003a610890110343e4107400400e011781081c2c80e49075010010b421400644242 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 60256801 1250 60255551 60255557
    0x30e030a051603030207080706090e0403030e0316111206070f020102070b01080d120203010e0109020703020f070611010606030203040506130f0b070f080603010513110105040f080d0944030a 83
    0x52550130000e2030503455030000e40c03043c0c10a80e002c0049580000c6068101d520382e03008141c2c2a039441c1800c1c0c006055100e1b40c40c140f404006091200b00710000d900c031101d588105001100400f0030380c28844100d280c1c407010b07402544200042181c1500400c080d2180040d1440003610b844500e030b0f60200072413020303800549660301c541400c0c00307071a0b0040400081c400c610340781181190700d030050f074840e0001c0610420742103560000d41d002c00c0c90b100340710304200d03541c1480449036a140e58040003440b04100c1c8a40c00034652904402242161203402141e0140e60000000c0085417111a050040c803070448608640800040c14076000140c400c0b000c04d4070450720750f11800d409210041001c0c10314200103103078a00c00d0345007600300400300803804046a03113190040c40200c2006140e03401641c8034407841c3c103d80e80000c90284000f0741e13410001680f045041140c2c0d51006040d039185402c0c814503901003a005415002d04101c40d0000209024a50481042d425903902034031940a01c035040d80d001500c01400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 60258051 1250 60256801 60256843
    0x4020d0222030b0f090a0807030c081305011803022d0907080907050108040b040f0320100e010c1413050402030f0403080609240303041a03150108060607030e030a05 72
    0x41c0b110030309040e98421300c12850076074a480e11100301c0e078981d0400e4400800aa1001c00e0340d409051042010311102503000d10000d1f41c5040072000329007140f44030b1054900054400c480e248401910203030450440341c0c05000b03410815001c0c44007490b809250039105040005a01d95500250348140c04a405808541c90341d0a403800c1090070703142410700e01d03004141400354140c280300015002e07103100365100e500709121030800303c0e142c50115001643c0c000403200310464134000c02c4801c9808910401c040d0741d14041046040c40c200003d038207a98100500b40003094200c01242d10401c00030b8010103203501c1907106070842c592544005130481c2c000740c030340c0b0b0310840e102c004000c105034000b540c981c1c01c00340c1180d84d421a49006118040c2142d00200d0840900d81507035440c4846840070019600507144006802c0e56100c3e028924240c40c0d04100d0f002c1a1810310b0f0b00c01103107a5400b400a130b500550740a4042e40c648152601d003074034010900004c2079051f1103101e2050000c00c030706000d00e085954030899180d00d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 60259301 1250 60258051 60258053
    0x607080a050c030402090105060306030f071d160f051c14040b09012009010207080a03050304031e020705010507080d050411010207051c030e03031b070611010b09040204020d022203 79
    0x1c50300000c02d0a040305004106200240e55080758060442e07004403103860752a40c0f803c000c0790a001c1c404c040c4540500c112980802c424108442000800301600501611035403400810b4690b5201227101e1004101c650ba0745003505031248000b0018175410720202200000d114132500115446142410344040d580414007080200748404d07140c002d400503009021030079440ba40c0201085004499103040000003034036030b000d0790090210800510221041d10748002c0c0d0350401a00d10b1340200c41c203c1c0010510b0705a40c007408120a1000990010740c1e009001e004d06010041d00c0f158042c103000e445107401400003504451003801091301c40c52050020302c0c05208600f0004e0701d080b100d034000070b110b074a5448511032000b40c0480f02181264051034981d2100d08110046810340c0700c0e802244201e103e072800d00c10902480040c0c20400c5a0081e0f444010111002040c04d00300c42d08040d5a0703a1107070075400400d0240c5403a40152540d2214000c006240c01500307214240c1ca900c00048180e0f2590001400700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 60260551 1250 60259301 60259321
    0x305030c0d091202130b030f01060e0f01150804060c111c02010606030207020f0d06090f0f030f08012301050903030703080f1f09090516030b04050d020d050f1b060708 73
    0x10080803a2860b6510f444100c0d40040d41c103400da00f885400007641c03a522410f131960208443c44c100668200200070340383c0c4031031294603910400c07030703440401e0340340e002c00080c0c52481d5908030400100a88d5441c0426129070381da46001e044090a07070f00400482083d00c0074660f4081c0142c9070000e032a0507040c480c0d144140c00290950340c41e0303803014050500c1804008090303100da102c08003c1e002c0450f44042e00c045117140a000074145c0c1c42010b44890508103620080015092425064030300036102c5111100090004590f208024041e00300040204509820a03c0d000900c510700000c05041090804901d04042451904003540c00c2d4001440345080c4081c0403d91101140c01001c5504403120429060690720848170300c6101c1c1fa18520340e01d01807401803043c10b0210684d08045040d040b11581e070b0302d08101030070500c281da003030322a405a2080b040146000141e00401006030f5240d40e801c003a1002c00c010099001190030042d10b0220039600e22401905016440c0310711016100e00d403003424a00030030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 60261801 1250 60260551 60260567
    0x6020309011d130207061815140412050304020f09092107050a1209050402120603060603010507020c0f180108010507110f0606040f1404050303010501021b0f010e01090305030c0d 78
    0x10510120401d014911036403540581c1c0f04030074020410142e5078102a282810040405144245c4800200039110041203e00e2400c0d40c0c0c20500f075002030000e4913482c054940301e050152001404180c941500110485c024005582d10500061680c158030003c10041044c1c00411941050582c00600c24000038290302c80c1580405400c10000ca030070110255103c680d07440c41400040c046000340e89125101c41d105118210180c80c1c064025921060816103601031081e0580d240740c440d000d0280021080d00301440b44a10075842a4000c020042038002440200070484a08039003040301c0000c5422580c0801d1a418020003022000080c4c07803418050041500150702c503248025000441c44c1c071001280000c066400500413a0001503030504107114000402c03040080720810200741c2d04000138850040055030480300207800340c0f00004404660100d1000c07070010050350000a08a0003d0340394899000c11203c2907041c1040803900703890392622495508103a5031105154042485004100d0303000f000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 60263051 1250 60261801 60261827
    0x603060b010914030706030225051506030610030b060102190804140904083717060d0f0b150a03061e020309100527010203040b010b07051005060a0f0602030901 70
    0x3503440070304201c0005e032103a50921841c000c050b0085212056611102c50402e074084030743c020b60860f48090315200e03443d5000b40b030340c0300b01105e40c0e00c0009039582070120301c0c544124880d05011021500390382c0d80a240d03200c0541407504521500444804600103903e2454125016038261a2210318000340301c800c0341c2c40c0d440d100c3c0c018a0400d041c00006010780d001c3d2900b80c80700040d040c00c28541c41c01c500a132500c0c021a45904070b0202c807079030741d68282c0083c0070896001c03058013003c0c1203503500010f11500e0110044001e14140102d80348601081d00c03c852242c200d0f00074650401c1848138500020b001000a0700142c0340643c0e02c032a15031046525a0000f4400103029009500b10310300300160310f48489202c02c10150140e11400000c07444580c0b000140170b440a04c82c400e01d80c0ca0020801e95000f0b4204480440c1c0c0070881d04004203080300c1050036100340a50150090031200e028403e01c401406014106d260020000040481c0e061070005100b005009035500a6407641e10007000141551030180c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 60264301 1250 60263051 60263069
    0x30c0b0a02030711010315030b1009020306010c030309080405040213080c0d0804090504050c03060a150504090f0201180e0a0b01020d0e030715140a030b1503070f031e0603060b0109 79
    0x410040030707004000e440003071381c002100c030310302c1c44031a001170300540300904810080807001000482003080701c1e00346030b00503841c0001c1d0000030790301c608500040b031100ba40c2c5640420595540c64001034842e8020318070a91040608034101581ca001060a0383c0106045004036003e804080c800b4141c20044a60118402c40b100341c0c0750805900c0300501803259020340c034080390301d0300c0000c2d0074400200041032036424040c08607410344c80c01c04401030040c00700650142c03136488000b0300040d452805002c0d900d0201d42000f0b034050340550a900540d0318007051100001404060000098031502c00b00c440c520400310050003045110301103000a00748921f484048051291b00040d02426403400100b060540d1150105840c490800f44015100200441c1c032000001b54000340314001140e040d00b24094200303007030351001250101d41c015409640170840d8100001040e0680c6008207a1194120020058410400304c0d40c07202c03003130500c07404d58585410a456640c1c0710a08880c04d07580c005500310060600131 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 60265551 1250 60264301 60264307
    0x6080702010606140c0a050d020303010f080703020a060315090e0106090f1418030d020c010615020327040908071115041d15030a050601050a0b090609040c03061d01030c0b 75
    0x900c084d001004010310b8002102c00814401c00d943d0b42000700c00303030b21b0390414212080070078110002545c0c0e910074000c0700e20340042e00b00000f0313585100058403001e49a00910491603181005d03800c400410700c0203407082c0c950704058400210701d03810344100c0c9240d1136500c0000c40c3d46414a100c81042d580c05c000c941500c42c2c5014101c210684110b10440d410003602000d110042f0b0a0340110b0345940124079003100354500c005001d0341c60500541c81403049440034080b81600800c207080603616802084141d403002c40c0786070f083d0f90000116110254620303800500000305040700c0c1c0c0760318229400c403407011200b40b8403c4d21000304514200d050442030303001d80410070f4501802c02038400c0d04100a904400340061406002c28076100c07802811a00410001c0c0840c1d1140100703050107582d440003841040d0182e5203a034004104a0200e03801c50b40300440c0036041a140c8250303002408000c080f10820f5004043c2c4d01c11000c55511030307160310003161400180c08480702d54190f041c0302c40f20352403d40c82248000810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 60266801 1250 60265551 60265559
    0x80106050f0d0f150b0903060711070e04020310020403080a0809071211120303042306041a040302011d0a020a050910060c051c030c0305070201060524040e0c04060807020106 76
    0x1040c1100e0b5480e03203100d40400d051200301c00310380180502e40c00800081885103404504010341d00050b140c241030841c00c960342e58030340c40740c1a100f060284000c80d0058020000520100700026842034100b44050111002500b00382c60813000ca0304103800403900300e08001150780c403007580303d079090b40c208480e41c1c094489039141c114410054640082c00412900200c8402c000daaa075000c1000d01001c002c0d03058a549107401c0c074200c181c180c00026a030510200941d4644009000010658491580000414800600603040b0020710030010001c0301150340b10364150695204c0381d4001c0482003251001007c14000714810461503020603048117028069620803c100202c02000744001c4030303110300b8242e01c2c55015041240c1800310700030802c2041d98407450b0b80300000c0d41c187c0c04143c144030255008c108c0d90321400300c200d00740c070085e202e141d40c002c800700d405604401c404012140801e0308940f0182c43c05035030302d04e0310302c501800320f400c1c20041002003400c1121542105101d81e02c0b22503440200b21072428 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 60268051 1250 60266801 60266827
    0x30b01020f060a0c09080d09050a090501050616020f040924051006050a051b072c06090c07050109050a0303060b03090d0c02372705131203090308010605 67
    0x3403801480c2034413180320500080c00307070400d50301030000742007a9100c4c18001d143c0a410341909214881c020502d008000903001c500f4800c4a0603180700400d0300380340c06145000402e03100564002030b80d00051303070500c2512a503100d2055138000e82c4524090302050000246510721300c0d0005d08401010707410607081010002040854400b81c908a0504d16110824400e04541901450481e54264416030540c030301c0724403001034440308603810481150245041401942d00d201c5141916600404103a404581c1e0786c6049480f0f941d10018045103a400c00d90b1644a45003580c5080c0720070354254011503042010300d5814018100078101242c502c0d031860801454440e0b60f146441c00e4142005180340c1c01e40e0466844520424400078020701801080302c060005900b5982c641d030b46030580001c11900094086a0318100e0031480c401201d61420002204100e2009490020000902e00b40d0305184040041d01c10201c030303c035011080d500000d03410018030300904007040680110081c09414009040582c1c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 60269301 1250 60268051 60268063
    0x1090203070504150b070302010f0c0507020d060b1504170f06010509070c0609080406080a150807050609040f0509031207030b0603010501051b0615010219030e0d0807020d030906030b01020f 83
    0x6000d480004102407030492400d2080d402d41c20176414054005145420315034150802d200001c94691304010300f07100000291402e2084500094000e0920210a004074400340e005400704140680842c1158525801da48050f42c0150003400c06081c0c003021900e54110104004250960090700800081d41041e000800080000380314400f0091507140a90800100b5044400d07416400b440041d02d071611690050708640d421940007a1851400d50040c1101e000400b020048400d0580501443c505180030310920303610800443d504203440321201d4941c0700c11803144510854041d400f441d181c04120000e8181a90058040000c041c1402c100303a491383d0f10bc40071681180c0017400c2c00c90340c54410303030401c0442d40e01c145248007250054604106020f106030089204a0130240d00f91071b078009045c407051001680c524030207000150f07400c402210301d0812104108000e0300410703201e420700c40250b000400030014414124006030110204000d000c0d014003a0411203603090020300104c1454a8485541d65 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 60270551 1250 60269301 60269309
    0x50705070b0405060324450118020c070b0912070b0901032408060a14091c050705070b040509060414190626061f030201051804090b0103140109020307 66
    0x1c0d4a144502007006c01e07440b41c4070702d10880501360030664a5918150080d00c4403599170300103600d07807130000d1849008082c66032409415a505810003241d007130803124035100b076003441c01904041e82009000c494100030030900008080c200ea001d5076503140325080c440d031401e0340c80080d0503d03800110207012032a91401a03a071680028a00010352181314146c05664409446122842018402d0003155000e404612544950384441c000d0206d021035141da82d0381c003a0101c88044203500b04044021204100038028202081e481c0f41042c20040b19171912810a0410340c09902004000107040009040241000d540310804031801c000c0c00880b0180091144ca0041c161402c01d80d8403d48a1031643e03107540700e000074050782c8024041c1980000d0000d84041c01d540b00242180c410341002070b081604145400c401c0c550b00b404100c4455145a0054503960171007081d806900c140e0f00c18001d2640c840d44184815540541490f07001541346041c031550a046d614400300c803a905000300100541c13400134401c0304032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 60271801 1250 60270551 60270571
    0x10b03030406050f1c14060f0f0102070b0a050f0c034b0d020403062306011b0302030d020d15151b08040e0906070f08040210030203070903020a06050705070b04050603 73
    0xc03000b24214140c0b8000803241e81e00900d00c4e042600714003d4a0f042080d01c100380c01d036248c07980b003d009130401c1109508525514016070222005001200040303025003c0807095051041c1454400e2500b00c146402001a402c981e5201103414081c52134a200c07605c00c1d1041e0751300403040705040c0d240350b005007804420ba1740300080c00c00080001c0040c080001c40d02c0203c19103200715203903511791500724040c04e0090320340401ca6140c0000c003080c3d83e22052041d40034810503100c083c103a401d0741d030400d00a03c41520058085d40004d1200207403028150000703103c0e81460100024041ca014081c07251400d000c0d4100304e81e00480502c01540103030b007100c811032090460600400040046140800403031181d07070030441000134031500340f10229000182050048001d07858160822407081c03003c58a5410031580650b000300f04100030200180070707900035074000d082450540d1480c0d45940100758440116803240b130020707500044010a106081c814000a03000350910a80341c01d00d407038001105808090f04101d61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 60273051 1250 60271801 60271807
    0x150203011802030411040509030d0b030c030d08090c04060b03090d09150302090301060312030203040b13050303060103050403110a03080a0f0203100522060e0105011106061f020c0a031103010b03030406050f 90
    0x2e0119081721300d024140e0051051144e450051300302a00d90f0452100c2d04981414006011101c0c6000b09a0115010014001701010a0500b4086614810140c0b040700a4010b0440990141e2114025031015000440318259681080c1480b5498410200d01c0403041101e1210305001d02c401c80c6014020381d00c1d05240240e01d0f402c6940c0000d00610942c0c2c40104803441014050040c107405402840c451406240e490b00c0e556640a210100307680a06402402c41d042003000403a10740c000c2e030003540c1042c06481c0c40c4410780c80c032605032860000c504900b82d000c107414504201c0322103001e02501c0100384080c5019402c42c244602090240b140178000c05100e03580500140020b0350300c100740c419041100d41d406016041c1d4540480c41524002e0090700d00040f0700300d90b00403002c440001c40030f016220103403030b024410101201400111050714100e03000c5002c2c0c040740c0a015502c0c1c0d00035002a41c0100c0e00b001204d03280004150840d0000b44069000c3d80050008114180d0400b0075240c62005042d0b0b115a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 60274301 1250 60273051 60273053
    0x1704050d0e0103020c070f09150609090510120303050f0105030c03070902030903120a0c0801050d02130c03110f1908010807030311030d0614040501090612081606020406020a1502030118020304 84
    0x2e80a810701c80185441b0303c42c000100115560510000c44030118400c0011180301000361114107080d00501003c90701e12030f810840c90160b5440701ea4400f81c00340c0c80f101410b48030b20680c1100c181c4c0701400c1d8000385d1260b06006c1c0300310810455030b004040c120001c05901e0982c4000c281c40360b0f618810345407038035808400181601d905204071205c400d843c1401d48254a0555510001000c03501e100e4000185807500104160400e00350300c548068009219440007081c0900d0403020b8061203524100309a02c80b101c01690188007409080c11010481c002070300c481841e285010950418408002004032420040204650215000058070741500e4440c01038500a40d29a1030344c401e402d000881c0c0d03889d000c2d0010343e0524807210102c2c0103004170b030280420b0342e9400c00f08055400785d0042c070003409007240c110030000744400010656610f04800003d0580855124241260080c3d8019805038100c0800d00381000320078807208000300c41000085045505140c1c03072071404580b90180c0c800080d40040864 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 60275551 1250 60274301 60274307
    0x70f290c0705060913061d07050906030114040b060f0705010e010b0f01120e0a080301030605060f100f020a060e01090b070507030c06180203060702011a040219080c0c0115061704050d0e01 82
    0x2400350103001106000c000c1d0f440f48900001d1f241108001c0e03c0410b2840458080c92059041f5450300000070503003421039007002040115a0340301103031280e000303559111044860320b03860080e100181800c0350b6140c441450f41005030948050480c4280300741d143c0305014031030b0707666130180e41c0c4001000c0ca4462200c078640704441d0001c0c00c004414603114400c40e0171003420045071400440c10399108078424000c0b900c6110500c05012101c010f02a0b00c50882410808114401d140b0300074003281510484400340c58646a500c1280c0750b00c8442c080594450682c0c01c00d0103202c0c586141c1042c0d4519195207003911036140103005a80c41c0d1340041c2519281c112030300b03620052a08981007290010241d0381c007800d0135030010b40200030b64034082c5800009a50400c580745454802d882c0d00903130f003e0440d80d141c444410101d504100042009030182405e2118605108091003003105003445041c00170190f42c103140d0b000c0c00700214540b85c140d072000810100070000e030000c00c0c0d07041100c0340c0381004680300506600503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 60276801 1250 60275551 60275569
    0x30a0f1103030f1611090f04032f01020706051e01030b0c0706180c12080304080903031605030a020c0925020c131b03020a050406050309070f290c07050609 68
    0x250314101004140300c008201c001c0b03412013a0f540300344110345400e00d0480502c000c1d200c00b100d90004c0c0000b00000900801e020b500b8410004c006031100e1203100b070140d070042a169031901c0f007846040c1e42c046061020448a88109034100c04400d60980001407000b41030700600030140802000b04c1c03c8440401c0c1010450004c5c1d8840d25400102404109100342d83c1140c0400d50110580f100f141f0b1980008507014980121031280e034120390240e1959840da1625411640600c41c84e54241c442007005290b0b60726413107054203c062180000d160b60743e000103c001c0c42c110041d00c0300c2d40301d010020103001030b00f90303081ca04e5882214080b10034111191407000c240e0500055000d01c6d50040b02c140b07491800008294041c101310041110803400001c0c0501c0210128040c0e01d445201150741000188505801240596404600c5800702c41c40c1a441d00b00c500d07543c855551100d0503180c0c0c00c0e071240300030703011440d00d05c4051444070b401507003040400c2c80e0050740c1d815503118950081d0b0780050a103c598580c1000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 60278051 1250 60276801 60276817
    0x6060305130f030c02060318161406031510110607020d120e01060e0118060806040b0417040302130501150c020f0f010905030303010602070e0f070804020105090414070f020c030a0f110303 82
    0x841f80c1b00d141c0484113030306070014003980711403601805c888220052590017403d003c1d1107140085c1d005170303449101030200d180d101420001041081c2240c43c0881d036600c0c4210700d0740300320307558440c3c3c4000b41740400d6a1a24901400820030354102d0900c200700c01d40e104030000d15445101d0b9002c00c50380140d2512038010321454002c0428818100c0022031400030301c020800703500070103410400400782c3e07540c1c030b00d622408281ca00030a582842d601081c041262002d406000740505613405280642c7c0358000f42c00080020b440d0040c2c0c60b1104010000c08111801242d407022090909102c00b01c519800108819003101686104000d040281c9049910a8100001920b4041c0807203a42c3c0d40c5401e8080e50300c0c21688100076440b084080000d01707400f5100801c0c0c0c0148890b0f01c81e0700c0140c580364015207094010410301c40d0882e542d00c100b200c0c030000c1800d1441c09104152160203408412402c002d04012101081d18000d0340700020755000666000d030400c000d5a040a003105e0f0820001c0c002034194858500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 60279301 1250 60278051 60278059
    0xb04050103060b12070e04230105160e03030a08011a070f0803040615141e0301051005030705220203100b07061416080402040c022103040606060305130f030c02 70
    0x30040002c6540900c50b40082140c1d03101180380511303000769a411083c00b62490080c899008a000100000740e0074551001c04140c4c101c1058a4604990840e0380844850040610b01011542c0054101044802050058024600d01070781418080c101400c18458a00c24041c2c1282142d94044c559003603a0700c65138841010001016030f0304007020750780c00a840070340e40c1310300e012444075011180c03013025070444520b400000f00b1900c00710308002c5041040148155110200d0003a4125a6428401e583c03081c2110040401c2e02810401814504200d1786c20460080640000c520082c00c90300c0702c41c48807200300500159a80d55940c0c2070a5817800c003030f4071842c0e851202081240422a80e41c00140c07000a100154030705640d5980c1c44260081101103808010402e403030040f50150509401401240e88640111502040398217014401e000c001c04016181c0c1502005210030030201c3c0c094013005011510f002e00441c100020410f045511700390005040e0a2518103038005c05015004400d2082d40080c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 60280551 1250 60279301 60279311
    0x131103010b130608100501050d080c012711010302160f111807021209010c03030207020d020a06031406030d080106110a05030a0306180e07060507020402040b04080a05061b0901050307030b04 83
    0x10b498402900c3c8501440e12907018128560300c04071358602c0b855040702d400034140ca210b07074056121340181d41d10000700743e40c0c03954072070200c000c04c90310b160f42c151810407090a2034a51945a400c04040c04040218038904040c01007011144060256030b841040c80d4001c0301c0350030012604e01d8400f00b0604032142594020a01140340c00b4400c1c541c06039640300c2c594940907950300b010a0217060340184120b07031541d0301040381c074600c81002c248203901a204952000c0c05c81e116130283e0790006800d06146900031800a600c40c032410321500d546451542c0c220310107070300401a000703031304002071700b14881402480100319011000c000180d00402c007a10b5180d80010580b50740304080f440c0280602a0303806454032801034100141d420103400c6c412540300190b01000f420015003820790407a01c42e440790300140d03800764007444040f6070f02d01c614009100404450700280354042443c58070b64209840100341841c3c9942061015030741c03024000c120385083c031091034510b9403641d450314190001c00da03501c2c2040d0414680 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 60281801 1250 60280551 60280579
    0xf020c01140108160503030d0e031b0303011503090809010806030307060c090e070527040605030303010e01030b090609030307030c03060312080405070f080c1003060506121e131103010b 81
    0x800103950580b0f142c14140e1300100591a003201203508035201d40e940503413041004981040480c0d120441c60301001c000d603441c103c1000180c19181d4104031050419800000c0104901d000c80c800e102d8086066080501c1904001c1e20381d113125010b6031240030b040c00020380c00644990303828000c40d00d80ca6405141000603500d2214001d2a0040e6802000400c04c140404240228003641c25500e1050b001d903e01d003560b809012810301000103407090710f50040d490b60310109940d03606101640c00703018403000da2081c81d0716500b855074141030b000d82005a0f9410810500400000c003004403030340150242404220300000f1482100248625840900b40a00038141c42102c281d11071215800b0300c0c0641c046489660306c95101040300c0c0c0c81403141003c51340c40f8640000080c1050f4a40c1c2079020300c1130030005211940c80004c901aa0f01c101c2c5200c0300022010104008401d840b81c50580803e402180140540b4280140f0066200d81c9a00900000410301d007801c26641c0941201c0a00c1101401800a60042c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 60283051 1250 60281801 60281831
    0x4060506030c0702040b010e031c051603080610030b151606020301091a0616170c0d050a0207080a12030509100c051804050405060601120b0613050907020703150f020c01 74
    0x11856013240705d1820400180e20383d6128403120071600d84001c016214915201400f041070000d01300760002413082c24004851008080c007a800701c0303d4040e803620030940c0707858010040c004040030a0350051600d030108584d11900c50b040704074410741c070f03a0380721079512444c800c200c9508a0700c101008144a0000002042082e0350382c2045911100130707651901207100303500400ca114042c46441c0c062610540c04044042110403d0218500c810310104520304004401c2c41800c0c001050704c0d10b40800c800182070028a5410808034004044140c0a425111410350754082c0640c541c0d0750034010542c940340440d100d030b0000e00c180c2c20605000042045078045425025207175422200c07550a07500c42d410b13040313039035401e06019191042d0f6110303002d0411551142e0055518460424049030203507901c268484a689450005041100e0001440c41e03017a45007408100314408002c0c081c40440d004080100005000c1401c10007804104a00110703054807000446002030140d20f0b004101c0350b09040c140003400036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 60284301 1250 60283051 60283057
    0xe070b09010216140402090d0609060506280501030b01030f09060506010e0a030b0c0313050a030806040509030a080106110309040515030c0607081207090b0c0105071b170904060506030c 81
    0xd0280c09495081e004200700e0201d4118511426811518032107042295143c113600070641150010941105140f003511240102d804107007080b02c0403a550024081203140c44018801126004036002070b0790004805a500b52503014400da605254403403214010b00d0703000350802910441c10400410903080c1301d040c150003034417056074003d001c0f0392000c2881540d03007840742c0e2410540750003130b136140c0c51922007840c0141d140e440140485088010402c44400182080c005000001c2c040d40c1c5080c92070400404000880740b000d40480041d81c0304015400c3e459400c8806c1504544c068240b0464022980112508500c10400e5003640301d45480108101100390400d012803002c0280c2c2100c044030355101c06e20034a44100030f00070301114010310211808515494906500407c203207400c03d526942e501d050401ca80110304d4649959440d0800c01c50700c149c1c8010039100f6020302c01e8914251085030349400510080c6c1e1620700040341000a078103803d540303580d0400c2004040181c200747c1c1d02e240130005c01140750 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 60285551 1250 60284301 60284317
    0xf0b090105060906033f16060c030b100f050f0a0908010c030504150213030f12020105060f010504060302071a090f010c02010506060409150302060a0c061506020a080a030e070b 77
    0x40c4820010800174100040e6801030020514182d1204100a4544154612107603c40020400b076403100e0340361100150000e40000101c0c00c1c0390107602d00f100d1034420700342c40c00386621104141c40c080910310309a80d04a01c200c2120b01c00d040204480c0f2420004039018411024440b41c4880001035000c1680c2e400076940f401c440000008002c00881047c044042e55020303a009000d0690b070030b40101e4540500d600410354501304450b545003881d52a42e6042c42050010b070700fa10441ca112400d085040c0c0c0a028041d403003002154502c518640c1d0100182c014001d902800c0205540815003d00300b02c003201001da10020446021145454000c03160350342c8070981c0c0b042c11019402c0480c10b20159005016a6000300b0000306a0340c10a070402e4002001012406074401146c01d0009000015031903080040220782c416035601042c180c01c606020054403000207040030700101c8502c003003010a0307000c10781e2001140c2c0300c0c0c8050341d1800304503c1100a040c00b43d08286241c02000b10010714422040003c100c48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 60286801 1250 60285551 60285559
    0x80a021206040305190c0b040305490b19150212030105010e04090c0306050604060b070b0a02030414030d1d010510091e0510030303060503120702010305040f0b09010506 74
    0x420503a0388503521080103440c0100403e03070511280e4410752210015649140d032610f890380b10000f440c0c544041c0f9800564007a808030390000703501010341480d01d44032182100f40c142e2084c442142414500144402000c516018079070b0500003d0018044d504410000040103100190383c03443e10300c095030368044a114004075224060007500c01580049404114000945d4016055030710f0034005448110170941c40715481030350740c022100024a000004805503008080024841c6890420701c005c4030840c3e0000c80303203540103011070b4000544038400e030b0380e0101080d100540c4940b100d241071034026981010400f5140004150016010007035482a01001c0008a041c4506002120040e003212025a12420075050410007404103842c0307138004403402e00007202140f14100915607040225201503454050b540d0b13100c0303800c100703040d410b005403005018110058410a100307142181074521919100034141611000001c040c040c2d0f64114006094004c0380710905403419443c618003c280850380c20340b00e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 60288051 1250 60286801 60286819
    0xb0102060708130308060a080114010602010e0f1002090f090a15051527030d0c140102030f01090b01090909050607020616020a1b0b07200103090b06062101080a02 71
    0x1640d20401480d8020f0000300b00c3d4448100060f00c084400d05401001c903904a000030f01d00142c650000d102d10030105400da00c50411650403d007009007910044c0407151800d40c8030f100e40d144034800100d55206d60380000c0d2001a6540300b51030108002c0d070404121503500003203402c104080080b95401c030010075020850b00b106039540f200200a100b10780c080040050000612079070707400c026152004101e48a130325030130010290051300080c4c54040002c09140000e03082807031607010456208120a105401e0340001e40c21490240ca000c8829a414820101c0250305d44501e0701280e401066400d010b0541c418051010049074102a5614003041d54802d005104410004403100c000c48000c5050343c00744d5014141c2d0b00c0850b11007078071618104100b508151060b480000e0000e03402c50041c560140700d090b40e410b000320f000986100d00d490308000c65042c0360405c085440015a0031510940c8010300700c65003038032094666404c80e41a20302d070109540040d1500000b041c2c1c2080000c0248003a0702c01c44403540c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 60289301 1250 60288051 60288061
    0x10e06030d0f0e040f1802180f06060a0302041a0c15040816030306081023060310020a0309140714060909070e12071508060303070c03020907120f0b010206 68
    0xea50790300790428000140d280c0d031040720154440d603419004020000c20100c0d80142d400c040c0d2007180c80010803080b455000d0790b5690210300340703ca402c40c1c9400c0c28180c40d0b00d5524212200b040750800042000d4803850b800142898914000d90540340645400b0003200f0707240e0028901148983d102180c1a6194450180c000f031000014008040c4182d034065602070920342d2030348981400c42e0740c0c08001c5003455107030000440c60103000c200101a0041128000c15080002140102840701c0c0c84c4000c502072800c0d4080003840d842c0003c0b20744c10380ea00c101005940e4000706404038010121701e10000e08100c03409040034980500068104207454071013200e508841403000400080340703d643c0140d50081c00c950700041040340034250610007014040c2c4404140d07514000c0003400c0815035000320500007142007810a01c0350b84010350380e5010f1b030258000c52825246803115076404010380720003482031800d0400907004610450100b000d031207541100740481c0c44070f4038400c4007030000042c28500500c01c00340060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 60290551 1250 60289301 60289303
    0x601090503010902030a080f0f0705150f090a031d06030703140a020405010c020d060204030b090f010c110616210b31020304061503060c020c060406090e0406060e07020303010e0603 79
    0x7001c1580e0040042001441c650b487c5596a089440d04405002c8284008043e12210f0b90081a0740d5103c0c4000e4800c2061610718111040d102801360510a00f5000801484040000e0314000d180e0701414071043e242e8601925200da915002d2029400000c00700622100c0358041e040448084000c03110100303030390b580c0c2c442203080340118451540000c00e0042b18030050b040c410400c03408980207070005072400d070300c9440e0420b01c1c05080c2d0704000300d0f50105001568110081c0300e00c0605160a142c0141554080f1f4100c0350703030301000340c4200743e580241d090044180d8060003401c52084c0485c414000181200320401d40104500007101d409810b0682d4000400e544150100c20604083c24511072115005000700c802508002c008441640d40e8040c0e0900c3d0000ea912404010b500c00c41020a650107060002810402e00991480c003c840c140014002d06070804002e10907a4690903045400303a0f1141400740240442c2d42c03040031541c80c44024482c1003540400114140c1c1c0591803206115140e22081c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 60291801 1250 60290551 60290561
    0x190804120509060a051605030a080f010509070507030e01031401060f0206060306041a13170d240501030b031204080d0f0519030506010c0b01170c060405091302130f0203060109050301 80
    0x7559008008104c03240340380e40144050680d0b61420150004a60f40c103594591450344243d20304808104400c0401404540110080e4050102941c4020040c100414094428060840010240086506800c000e41d1182e03000740310f100d010f0101d01e515540c0d1900c019150b82d00d009003600050181c400010140d00f00003481ca0301440e03001d2000141c00842030058000500060040301c00070103030305140340201d10b190680403044403011076400d81d2000b41410f49400c80d8004002001c003201054240c0008a0590b818602100c0f000e08010643c9003203000043c0c00c0011006000380b03115408203000c543d07003500040c0318450206075154000c0c90028101306803880d001c0c01004d40340340388000c0544002c8500c0780e00000c1d00180181010307440740520341d4a0b0701017202c1c01d070050400c00741b00700c4c0f103142055030400c400c204103842074030028038281c101404100b1046e0000c1c2150901589d100d00141103440d5a00466030400c50140c0c100f006194940007000654001d03600c46000684001000c92146018818 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 60293051 1250 60291801 60291817
    0x305060f01030608062a030702030d0614010c0213090219090606020f030f1b011e060b040b03010e041e0c08060f010803030f04050304090603060b0a090b01020a06020702061908041205 80
    0x1742410b0355030a14580c05038400ca000d906100300b5032407891004500e040c1c099405210307240c0141d0344400500343c40ca42294401c0d800180c042800758054103450b40c0061080708002c0c1c040d509008035101000048015103800c0100940241415542c4105480c0406170b00d0142d03041910300b40040d9580c0d800480e92000003140a84040d0010450340314805070102c010304002103801d42c802c91072076010f03c003a82110300c500106200c0c0c039081c541c030400304c0c1903d10511010340740c0e0309103281c1032a0514110b64030f2030005002e4100f00b605040081400e00c86103046440f0309584a0031035481d0901d86182c8400d80341024806d0819a1103004c0104078018403681005050340c0c0701100443c116170f107100411343c3c80f41003c0e00565190104000c0450800c1d110300139400a5030003044d0100e183c01a04043c84a54509a0f001e8911180750200480701681d0100301084042e40021015842e4501400014900d10804400f0860413141d1541680705640003046a84158051555200400181c620544080c402c07459 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 60294301 1250 60293051 60293053
    0x3060302011b02030109080a05070318141c0803040c03030807020118030c0c09060914150d0803070e04020a090801050f040302250e010902031008070b0d0b04020c0a030305060f01030608 81
    0x48030100b102125036060401074001400452516415110b103a1a0f034000f09429000450008180b8280354000880269102100c03030980100380c504468500c2a10610901c030340300381c44617002c0c1e510b54001c3c0402d07042d4203a04981c0013903903410a4a0051a40500d6100442c0031440d0100003500450042c030840e1a04140382c1240340c903070181036600f00c030007c40011003101d1540e5103090104c0c10241500c0b030200506100c140008a1124410001d03a0b03240d00101200702c0703074003c2250509540c81d00e5485a046540c4029040d03240d40b01d82d01c003a0307800e000080d1419002071010032014105135109820608540c1c07014000c0020b40c0790400c4240f00b42070220b0300540941e0000004104403a0400281e28140148418a000c0d090711242440c450032401e0788103d281d25008014044031101c4d095101c4010700010f4000d044e110b280424868641c0245406589469500d2013200c1b6103480c0d54044603042401c5405564041c031551a0280040009980d003901031044154040c00c65402845032509a81c4458 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 60295551 1250 60294301 60294317
    0x180c0412080d0f06181103130212100606020f0c03070308090a090c030f05070315050f06090604080601050f0604060206130204020910021e0d0c02040b03190b040203120a0806040b03031e0909070306030201 89
    0x502d1140c108c00c1004100e812800d081400d0f00541c1c0b0a00500409080c5c40d240811042e03e844402858101343c420000e43d1904010070dc0b60725a540018040100ea40c442c44c0c8a4440400a00003541d42d0a10f61007244064105045c91504a03410b51143c1e80d901c1803940100055140e56030300306c2c201e81c2880c21042001112180500075031030687d00c2100d0303004000b070502e0314092000021a10f690800e5100341c5c940d03400100180b00903d0405000e00a003241581c2140c10646003140c000c1d0303245005019040741402950104080d900c694044900802d40907100201c0c000c61307420000e6480e400c88141804000707800c00c20144000020031802d0f814941a518580d5141c015020003009103ca42d030002d80c18400c030000242c4918040680881c40c0b4003800c00c000041c501401810305184207868000c1e0f985508000c103030580c0303410001694004034256000a50740c500580860300e54814003110385240c051460510184000744401071010b02010740d0340320389584035074405030140c400602009020504c40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 60296801 1250 60295551 60295561
    0x70807020d1104180203010c03020309060a0c0c120503060109060e0f0f0a0e1009050609010609120204060f08031c090317041115030402180c0412080d0f06181103 71
    0x6410180c400324080c103a460030b007546903000102115000710a50b520000703103d85920a51600b8071401198250300d00b0b065196241400281c1c0e1220401800075001d16569400100b15130f10403c9054000c5601c598000306106e0440d8000c0e00315013044501e1030000388154008211a841881d200d0a041c8010702002c042d002254100061245001c0106400031307480c17040020399040d08042d450040c409034031390031300040c2840321000580310700402c03040c02460140010000c05510085440031640c0828003001003504504c0080c1c040c00c2e00d940304805207451443c020170243c0c8040b0040000d0714550152514007139007809000c0c19130b6070380701e0040c0214100e1403440c4c004103242d20f0308581c801d100b010511407100223240020b03055280c6101c00d4614500100801c400c43c2002113119505000301a0070035500d15206144030f00390b200750300460441488108041d82040325000079106203040311030084c045541d668501000501c42803188824008081040d091107440b036120b005069580307091304034a0f560714 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 60298051 1250 60296801 60296809
    0x60c03141605030106110c0d030c0512040506040605070f0c0e10050307030b06010807050409050c03040201110109170d0b090408070209010e01061413120605060306100608040f0c05090c07031407080702 88
    0x45080c1418081d60b02040e50f103070b2350b40348942c00107486621410100c100c142800e520305441e50b00f02d6000b00c1c504000501c9140c0e0388200b40e60442da1039103001d59039101c1902c0c28140c4180200750007001d0342ca800402181c1c0074042c40f4030b20f2160890144245030255200d00b010b541e411180305c00b030b11074851000807c0c81d95100d403d5640d8880d03940d00301645001c0c1d941c01801c0854504490703400460320040300f0700045680c4802c01c0d0b801c10341d4500c002c1c41a612580c6400003076a003488081e022a85000655901c1000350340c02031044400024810003141c41d140c242007440e940f212000300d10035050310001080e440903a101450681d0702959480c05400070901c280035660b07100e1065084002c00324040001e00c0040301884101c242c0c8100c40114240c02e0403004e241ca40640030303105400c00c03102c0d01400e00600d94025003165005030407240703800d4000001d0a180090052941007160012010003c100b26403031014024a0701c280302ea961221148051080403c043c06600c0b8001c0c0302d42d030204142405458 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 60299301 1250 60298051 60298067
    0x606030c0a0302040504110a0303050c1e0d030b01030b030304170c04020c1c02010f0501090c020d0504050d11120601030803040c050307060e040f0b030d03090303111201170a060c03141605030106 85
    0x120444c00c00903d928207c0010300c143c005540220001030700020b40ba815118107000c0c0c0004070900c440300030102c1c68041d101c0703510762507030b2250300080580c1c0d5400700240768420307001341201c2e42010302526a80c644452142c8005000c12799511070920030400701d14190b041510856038803c83c540d015140c0ca42c80c00b040c00e500119505080e004640d2500c4410355000554440c0703a00070702d8041c1001505140341207001c0d0920010400d1617050100621041009845800c0224101c42d4040710078100c03800090005000700000b082401390078460b400000c010096810002c0d030045024007a4000d140740d4510070036a1302c01460040e0000590800e00511240c18036030044540144400300100d004050440030a140100c6003003081c000a844034000424503816114902900c1511000c8616211815450305151030046c420411001132807c134080307489000380306064040c1e038400c20912480c8240032008014018090b64500704d109140c020507490454030310420806030b09902c4203400d50386840b9003a11180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 60300551 1250 60299301 60299303
    0xc03070209070c060203070c030e2b03050408010908031e010302060d1a030a0c0906170a02120f0105010909020901050607031d0a0812070501061509052209060b030606030c0a0302040504 81
    0xc41c09106000000713106002452203501565100c0710032001e1800c00030103c100e081c120038040c06c8140401e005500c0542c01407000c1c0303103a045500e5045e1541d850300b2100e92199601c0f84496500e030028001c20800305d00002d600039846a54516410340d200d40822044038000c0c03100a510400800121540a17281c0d003080b4260702240c0b14507102c620032000464205850780f5800c403410355442c0c605010303000740f510610026144c442d002340c285010407a0300540d00c41c403401c0c02a01c242ca2041220f000314804000e26800100c100c00203220a580d141901005020890300407031094041c40008034103400c0c40c3d4241c1d034000350155034504002d2079001e080040300300e22a40300741d000816900d02080100307041081034030302925000b0355a034840c80d9003405401c51b91540c01185440040c805c401c42c00a5001e9210003e4036807c031811041c03100001c120103015400f00c00000280d606001da40403d0000e607174800b0700264426000e6841c140d48081c20540c03514480c00286a12010440052000d07003020b1b030141d03500c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 60301801 1250 60300551 60300557
    0x201030513080c010b040c03060303020c28080c030d0507030807110115060806030105060406180c030f18110a0518060a05090f0108070609050901171615090b0c0307020907 75
    0x102064560003020f03400340b403004146079160010b981c46810f141c420100981e0f01803404120312811950003d40716070044540a00c2140b58480640340c450305403c1022024500078207002119036510300c50360301d41e141810550300c2400f450500700143c034001d9040742d01450f0b0581c0d90400c1603403a204140c072040e0080e42d4501c110741d070703480e03112100c11032194810010f443c0c10344412580340b400c04105401c2d901c00614a500072410b103a810050394824250041000c00240c030045117204200380110000c181e0a804840c1d0700c0d00300004503c600004250400c9a10300901c0f62000c1c13078020400f8890010081c1c462a0340082a2442072501090080d01d05a00020700911080540740c1c1c43c40041c020400c241c5008c1711103a00280100956001001200010302590401081c0285810001100d44505200f141c410728076021010252040c00c1c0320482064000c0750a28104580b51500c012480f0400400742000c52114400460410710040560714039038810f01c004c5191005640c02c2c4684440301610400274 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 60303051 1250 60301801 60301831
    0x801120507050909070302090c040b041505092709010507050d110708040608060a150f050d0b030709020d0c03020c07030609081204050c010801060c050c1c05060c03070801050a0f0302010305 83
    0x355079206043c050095080200911a00e4254010042416005000d240713000f082004208a24003024040c0c0c0c040392840e080d045002100800d01b902c2a1144001440c0d000c640310140c1c003004d00d80c010140840603440180ca50b2180c5d10341400d0740c00c940c0140e80722408208280b1203900000703503a0304054080d0444507025400e019180d5180d0f26950040c1d008003000c503403110700b0014281840c402d03501c0100280340c409204c528005001600c07a01c40e100444040150008181c052110350750803090100c40080c3c1180c814540d1240c005009402a40782185c0d0b4508040d00303692020310900940319000e4a80f009002d0503407440d9501300c0145400e03481161044001d210a042304100030710624481d901a5018001c5407015100050554005030003400500c0b661001400c0442c800041c50041c01e03005031000e040c0c0d49223003522403c407484030650040c2103105050800225007612006580201081c2c2c880007101d9072107504101940034a4081c8000199048608001542c40b0303030403098008090920001c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 60304301 1250 60303051 60303059
    0xc0b0c0f0601150f0207030c030f060b0d03030e010c1110020a03151712120f0403050409020715050c0f030a200409050403080105060f0d0902040b030304080a0507150801120507 77
    0x30030a0350991203c65040d488070108600103404c001d80c02ca00c510544040c02400342555141d15150529000282c055015407102c102044801d074000c130201c440082c46800850b05c58500100a8018594682280c2d420640d0340b40049000d84050078400d0780c00001b4148042c002d80d02c910094200301d1142040584654000030206810a03040000c3c4c103c4404140ca01d42d11032000a01e05100301000440280c0f040084041440260190b9030308190b8481c50140c06480c1da0400322020300658010103406480054448108801420078400483c851141400070350389045012005e40075110741204800c80c1040024902102640030400c3c582840c9a04582070f00300e800301031015006034100340116540c407801c0c08113164002440034018039081b02d10a1a002307a0842c091044e0180344a900c0d012911401510210340e45c5410001300000060200c903215540c1d140240c3d0345400140f41035550f4007a1a0021440014400521a03840c0d804d0300d4103076641e440c0c00900000210310b803a06441078010303010042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 60305551 1250 60304301 60304303
    0x5010f050d1503050a0c1a0405010509010c050102040603060905060901080a030f1e0906020c0409020f0f040917070b15091b0d050f010510021516090905090303040b060405040c0b0c0f 80
    0x8083c40c06040140219955450174414246094122440900813038455014184c03680c412201510b00a10f84545c64400850042e81d5044420200030f000d075002003800b040c020352540c4098220740b5401c909001300e403110000d020003420203018100c0150088401100402d0194490144030181450004101c030a40c0f18803254604400301090000752070010308002e2f840d81001500544c450403182000303c51031980c00101d4208901d01410300801250b0308405050340c2b542e00c480d10b83c81e040119442981e010301440c000d6940232450031034114400c500851140c00304100e0042c1084805805e0b0303603403911154602d0558886104803000f520300100f003541070554a5000380c41c0142c2c0703021003540e03042d41071400b0080180e0340d902c0c07400110343c881611070740300c000307200b4040d504451100c60083d20742e080d081c01120768005641003600040d0805041c0406003c0020055115030300908031001c0b152501c0042000380e62007903e000c2d0000c110a0801e0110751949801055059074010441c3c2010f20145041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 60306801 1250 60305551 60305591
    0x50d15020c0f012c24070207090e0d020f0a0f02040f06080a05010605010f02030f190e0d1b0608060306041203022109060606040803041403031b0a11030705010f050d 72
    0x60b8071a040003013030060b00c2030410810b00149a9188081e002c200160040811065180100704450300c00d900701040803140280f0080019000c01041404110340032084c1c2d941c0c841459213003200520591602d13007d150b501007040c900c0c05038488540418010301d0b80800000d4103426060403505650768800083c0390b14200020860b192091001250003443c00c000035007250110744100b0b0654108110285039682403004a501300f458a81105c04c1442141c881115525840d0f400c05030011030300c0b0702d44018000000900850300300303069040f2074000e890f2002100c0203001a00c1d60f80d015440480801c2c0085d25030107480109214a02c4c0c01400c24100c495007910b200324a0b054294000340700c00a1140c00b207010f06c070041d44203000780d6078146864a004d104950f03a2089126241e1030241400c070466159900384112240c0c140340404914007a800ca254039600c03a01122400c64081e00c13810a407010905021560808507641610703540d04a9030014002e480a030300030f0f221003110503a02e0044440e140201003003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 60308051 1250 60306801 60306821
    0x7021c110f040501051011120301240201020703050a0c0f0b1602060c030f0103120908060a060602011a2407060e0c090c0903060403051605060a0c09050d15020c0f01 72
    0x940d1000d40102001d00103145018401c49000e82d04040040c059601ea0041c0012845914034281c2e404120341100c86e400c10703045400380d9103152000000000c13903030040d0a00400d20000300100107426070755140c1c207a00703d10401714001d011640a00511862500450754004510702520b60f24002002d1075aa400c2095401c0b41c0d0000c3d41158484021402075042001d95800b4040c5140300f8039504045030b0054102c01d0521004054000340c03850b8004180c854490358009107828002c8400310b040030244000603100f203002d0070006610704441b11510560466903502d1300074001d403100300c03203c0c0b9400080f101c440381d1a140c105000310800950300050020701c580e0518480c0540039012000350b9800300982d026025280e1454642c05011034511640c02107402a08a607149c00c101d0390340d2481101c5003100e20a10100508107000b05d204120741030504d50004480360100d650350402040c1c581c0100301c000103500344007400031000c0040c00a43c081840d8001c0c450104c0c0c2404442010040110140c255010210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 60309301 1250 60308051 60308063
    0x1080c0d060b18010518060c03070f03030902010e0907090605030601020c150706050609010e0c031306050a06140102010e0c0f0d0b070302070b06040b0102030a0305100909050307020306010f05010804060207021c 92
    0x565110110b9200c400300f0b5404024078000d4034041500080420085040300344905c90600068850310300c41081048505c0190700004036400b0105500700900103040c4070b18203134040780045035030300748904d80054114825800e80e100c42d41100d06005044406070401404141940f00e0010300011a07500c0250f5560441d2480030030742c0c0d5400582c64103006403400030703100c28090201c04c00140319091004102c0c0c0c0c3c3c440c030035401d0280c803592185400045c0c40342407003001c1d040030310b440140100310314250065003d4440006040d90b03032401c040012422503022101440daa50002803100f545490480810300b09a04001c08c2058000c046881e504814203040d101034000c02d9001a6281c104081c04110707030b0f40108105c4007044850034110000c0c2d220b01ca803258440030140d507440041c0c0d48040900d00c04c40985107144040008101519009680e5440040c051f4030031722403600000382c00120007480e4400c0c0c42e011b0b990010b807500c4985d1000e001c0e400c405012030384107040d10007c0e88414000c0b6103c070305d5140a00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 60310551 1250 60309301 60309307
    0xb0a0804110303040f17060103240609020d02120705090607110d0203030c16050307030f02040c031103010603090b0a20070302120d0501031101021209011b020616050601060804030e01080c0d060b 85
    0x9100486c0d5021241040700345a00884010008242c19640394941c0da600c42da030031b03102003040100c0c140c010011600501c240510105000e0000805030340a042c100c1c1d041b22018074291120341042c0d8841c0180454203920010821011002508500d5081400100502800303a00c1580d62700080c00c50700940865002070340a00785013294038a07200c01c41e800504058001c0c141e02419625080d040861500703000c0e015a44070300c21610594400d41c4920099600b8210103622542c50f400014007400406070180d54445250003c03403408101481030900c4041c613a8054211440c0d001c40c0f0490a421901e030560541c060b4a0244c030704c0c85000c0d03008041e2000c0d0000009050360561901c42800040380300424115800201d10100e10642481194480e2000b4241054002400200f00b04c034040342c00e900039001503001c6040025261484a5850300034810b50580d07400f0b80c0c9034581210718401c01c4030090000f4883d6100758480354080c4c1701140d00501c0d0b40c0c420526020511091800740c802c4c41e070004960030400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 60311801 1250 60310551 60310559
    0xf0b0a2607090e060307060e010c02030a030e0a050603160e130204060e1c1a15060d150806090303040602090103021b0c0112020405150a0e0307030b0901060603060b0a0804110303040f 80
    0x1000314070251800f100303a02041d08108010070340c1d511040c0100300920580b80d2821419138056103c003aa490b0b80101190b43c91889403600810403403e68180c50300501305014007213514a41882642c0c442e205000c140112800301100440f8500c040d480c4c03440d00040000c546400318240c50008101030055511401d501c1420302041c0241c040200c00b040c7c040701c5500929400040105089041c4c1c6204103004001a072124400c80b0030345c454083c0225400302c0c00051030030b5040d02d10f0700144000c2c11500f644500c61903454140984a1200700d45000e000c1d042040090005410b5a010b8544124107140041c00c0a408105120250b580c0b00c03940852035004185840c43e660b4020340e81c241c0007141807002c3d0b00341881c100100742d01d07095000c2076114901c80840c000000030710510204101d103100500b11200c40d5520f0030032000c9100140c030540324a5003080e1001c01c0250184c002c9038100d0310f01e0308096152000d9503408843c101c40103441100c00c803045480000311950200054005400740400c0240d21b2890 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 60313051 1250 60311801 60311807
    0xa0506191205040f0201030e0c06040e0901050105010e0d06050a02090d061e0b010e0d170a0903030210020403030806042f0a02060901050108070e04080f0714010507090f0b0a2607 78
    0x703090454501c0e6080104020000c0c0081401001d10355082c00d000c00da880c90b1a81060820101446031078005801260000d01081011a294080c4039108020403003a40c8600044030030450090a8075005042c1e0700680000034a81e60203207034005000d21005003042d400c100090fa48603040b12007550f0054440c0a154400c40c0c181561410403c4201410080d4041e5440040c1150319150200b038032403410815500140703c1401044002444081c145540c2c0d088503104c007502c00c0000d8001035005101d0030000d144100d1342c0d0b00c00c48040ea40c142e114004260b9600003044003525036890b40d4010700404243c075201403801c80b112048203454a29034151540d8044400030b1030148020000100c5a05007401005a41400304103c000c0e260030108180301503640742007101e01c922035814448035112000660805210a101406801720440c500038840c2d03450301c078401c171040030850090740c290041c100301c100000b03080343c00200b102c003015080041074505010011410040417205100d422143c5908000c2d10341d41c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 60314301 1250 60313051 60313067
    0xc08060703090203100905030702030316030908030304030504050616051204230609120304030b0f061003050603120c01150906030605010602030a0f05070c03080a09090c03020703021002090a050619 86
    0x10034501004007042c250002540ca5415005207202180da55410a0074405c051044a00c5a60081c003103a0b0380703913484d50340c0a0500304402340c1900010084580410100c00120841c1d0003150990740d514103146c205400c0046a90010402012a5984a0400700044c0040c070141c1c0701d82c0301013092140c0b25031407e11041080c01005200c070881c0001c810781c00103c0e94454054408001064441d9200701002140303151030761180340c201501d0072500d10100010080300a01551103a04d050b204c00010314917080b001d17010f0702c2068514985c160800a00c00c0c10750000d40d005070004c0d80c218070004c103405001d101040b85808040c0c11580ba60303501c5400610612400340905401015548015443c080340c07400024142d40c182180c2004201002840c072003804403440c082d402844c0c10901103507942d002c4c0c00f00a004c0d4501c0717200b44900182007100185480e03000c0e10035558620b0700b54014107214004085180000e5000603078607a80703d440144081039544500b00a000e441050140001004d02c0d00d08021701801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 60315551 1250 60314301 60314311
    0x80105010506090916052a100902031507032408070605120705030903070b1602010c0f050405060c010f1d070509070c060203040c03140706140702101107030204090c0806 74
    0x2c03408200b401801c1e211650f0701c2d9801404d00881300e49140c0700000031201480380840211400d20145280e200e245403038034030818000002001c44042100b26250603081d80c184c060041d41c180c00030018002070240402c002940560103140000b4007240820403044291105511943e1a80d40038505200007281000b0402c0600b8090421342c0c2440c020000c0300b2040f1800800c51000c000c00800400c00d880000c1041d542d010b41d21004100e028540720300111600b440301e0b10146c1c010740c00e05c400300f403049028455950325030b030403640c40c00d00d041c3c101001d01c002a40138210181c0590b581300c545000041c41c9210b185104c0742c1d90000c03035440030100e10701d0900e0403840d0340140c1e08c2001c16500340040c094200c8a40200b082d0b0000707015851b0768880c01e20b0042451325034000b030140030900c0d0001c65906400325000050f52101c1d2540d0040304007032410341c0c1071400346480c001d41150449403640e981c01c1c044c003091083d17904000111250182c07681d010070b0503213510550803208a007506005020020007840016402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 60316801 1250 60315551 60315559
    0xc0209070207141203040506070602040807030807110901060f0513050411090102150106020a030309020d060c1101140118020c0f0d02100c0203070c06081e040803160c05030301211b0801050105 84
    0x9400720041381d516841988640d902c90000020f00c28104100791b01524000d18034042075817402da50701d040820140e44580c0045511042d154a90110f0385840410a4140c40890f9a05422210f00c144140c0b01d41d4403400c9401d4003001038a20001c0c09540c1c038040c10901e90380c4140440d03140d8000000180c40d0031600c44003494081181001445419800218410215010316010503004424000702e00c0060311640050440d900f08039141e2070b1507810003c045682100351008002c1c1a03509018081a40341c01c0c013807400750403040d03801411040704a8000c3d0076000e1000f82690226828000a03d1070003080b007000c1c002580005140d80e40c1c01c803d501c41cce5a87e40c1003c2c0003461800700d095480c0008007589000d2807051003001004164280005841e07900d10313000306064226103003040d081044050700704480b00e204904042440503c920312403043c07102c244e9401001141140d0a08048004001082d00ca542c07107100046a6900030454002c13100c1c034944503100d0220b4007107003458221402c0d00d9058000f46c0c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 60318051 1250 60316801 60316819
    0xa030b030d020d0c06110a0206060102070603110304080c0f030301140103050f0103030f0c030e041d0606010201090c0326030705120117030d0203060d02040c0207090b18160c020907020714 82
    0x34054020070046030f4407072103180c12800c0d000d480c07401c4401008001025a43ca58010135400d4196400180701e41c042c0303001740c08a502242c2e4919048099600c0c0d008c0f00d5920080600120b800501100040c00002403c20181ca0004850803802d030b1440d00241c0c80058518011440840c4958240c8038064000341ca0101c080195811510081c08500ae001011420400b500c1800720500d44120219044120300030700a01c070f4021031811800043d42c1100d0303035800710f001d00d2010847c2c540c014480c400f241540244e01e403c5403461916907008400c842080c1a0039840b003000483c051041c0003005500c20000d80d250385850728248241b540c8101c0d0140c102800c02c081d03400c0c403000e030b0200020656041e020144c00c0541c3c1d980e02c2502041e400305944a00075002410708501000590f008100380080e110440b4041104600500401040d07166242c0d0400c064080000030681c091106406417082621500304902c0e16400c0f40e0205020301000c440940050304010070501001803038840300c0c0e400400c11500003030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 60319301 1250 60318051 60318073
    0x20c0304091107110f01050405010507020f0a15031a030a02100507080708040e1b030c07110a03030206040506070507020f041a09090d090902030f0114032a0a08030c06191508030a030b03 81
    0x1f1540c0b146010302c43c1030200c0490701004540ea401c12042e400d8034082d01d60541180d5403008c1c105101941c45080001c28206081d1032408640811410684900200106508000d036000e120446080d04c86d030030100b1504002080110702454020f0401e0362040e400e141d070701e46c9030000c2c2d40913208018010310f07021f02e0300c01c090b440c1114040042e00e803c00b0840c0c4c1072641d60035481c50322171810801140456000303804800b0010038590089010351081d4001e005a5101341d9500d082201e8a102e41c800096001c204040074250070704103136100321805507600e6070303903034041d5100c00019060110494001540e54030003248800e2642d40151070740001c1030322680940c2182001000341244a00500500c211805440f45442d26035a040140c0c0c0da0317214103901c00802c0c05400003001d0160108088030140509520784001954203400011107040550311030142503141c490004c0003241c20000d0310b00c0509251294108055003030700003d090300920400000b1a550000c900014059840c4140309600c203800001c0114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 60320551 1250 60319301 60319307
    0x20414090a03180e040b0609070c050303010905101e0609050103090305070602070206091806010816020d08092104090b0411040303050c0a140d09050306100504020c0304091107110f01 80
    0x40e01c6a6050804929082441c14441d9400321182e00516100500f4400c0c8814860407003003990250b0015240b010040d0744031031003a104c9800300300c001030003a03004100402c00901b003584099004031200da051802d25941d402c038800b407507090101e1440580c801c00000c000312900107a20344000d08080c2001c3c80510803a0f00c01604600510102804035600050300c201103640724800c6031010324004050092000700120603c1000e041110b02e82e02051310071021803501441c61000c800411019801040c0003031a2341c00440d0003e4028246007820303c01c202c400280760140808103042040c50411450b141c078a0110a402900c2c2c00b00c41d074030301461074504100554003072503044405994040c01c00e40d666032904040c8615064224002503d40c41e141400c00a4079078010500c501c805042e42e544a07100343d15501003544450041d209900340199150f81000b003400d10760080d26074403078108103590410366124854003ea901d03a11501000da2800510b02041000d20000b42d0000c0710241d60428404d0244030000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 60321801 1250 60320551 60320563
    0x2010b06040b0d020d050112140a110111010923061006020a020d03020321240f1c06050f090d02030f040e25030516020c030703030c021906090302041409 67
    0x40c01e100b0000038000c0707021620b90103e8000500e03880d4200a10344c1d6501c25103003407036070000088403004010508400d58203000180c0c0c00b41d0f10703000b84201c030414440704015070300140011456000d95403590102004103c169111145a480d16405e400301c02905039200750410000410b980d51621140c0c9050100356400124000c0582c1d0540340c0d20f1080c032003410705034074500400e07100343c030340b00420292000c6400448040601907006186102d4a4480750725101460859402c41c0a81000c048821408580307800303490648903200071006003c0e41801d64644605540d401c03181a00020b2265003400301202e000c002d4213801d0900340c4041d604004030348100e91030742d10032449040000c41015002c18020302a00300541204014040d580903400c05050f4003a0107004201c0e0f0114000324041c070345800742c50001c43c84450400740200988006810740d901903540c50540481a600180d03a220100c4814a900204c0700141030740d0f407590580c1a1030751041209648a21000250102682c814018004030000e01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 60323051 1250 60321801 60321809
    0x30b0a020304081303051507030b09150d02041b0206060d0c0303030b06041d0601020c0f060f07060b031905070603090b06040b13020418050c040501020303070c03020a020901081c02010b0604 83
    0x1580d00d032a60300f0b00350200c0c0950024101460881000001000b00004500854200d8a8801002a075074600151f080301e00c2d62403200d0b001041e003400140c11030070340200c9800c9050f00500c5251040000e4000c01d04456410700031440100c03d54140084039a0104800782e4048412240d210364140695070b030742d16a080e42d100050a250f1075694034005a030f605415540035111640c10b05c4d05507c1c0c481d43e05180b0324025114140503000d03501801d10f490031724618900b001c1d04040d00c4580740c441d951089041d00d40c403c5c241900c001c1d90320003644409a0301807022140b2250540803600c0107804030f003040c2d03040c501c40d0303130008090615006c80c0708001810320800d50740c000c00480c1e0014241d5440008140140c240340f03419081148002001b0455855001511508000c1440200070356920851000950300c6a0300540380581c0c0144006070047c1e2245103248100781c8030b407054400c1180150f0214080403c2a0000707100c40c1c10117550714600d0507002954001c10885480280601c02062011074441c1c40386000e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 60324301 1250 60323051 60323071
    0x30402040522060e21131a040e04050102090a080601090b0405060d0201030905151602010b12120315060a030b0429150c060c0301080f030f04050105160c0308090316030b 74
    0x30324540d4038209212941c002e0200054007004800603181442d116802001c1100448450101c046503600c10629420b60800e400341f90189803170701340914200380c01d00051003152a59020810f1607090786409000e50018400d05000b0b0140c1d5040420716400c1c3d0390f40c09001c1d8003d501d4401080751070f44c4d448513a0360100d0b80a080c000780700d1741c0310300b0300a0504030851150034000d2400c4086c050740d600281c049048050f1154000c0180e50182402c01074800a0380e840a0b4a41d4040d002113a90007080e080119000418841d0203003681c803311002c603000307400984801000c240d442c102c121890800780541d40e031603112070b101c205850785070b0707040701c1c0c405540300890500900a103e001d020100002044032001001c80301121800e00d03065030031140c107a209000380d4209000e610640c01300c0c880c000080e50070544882540a061500700b40c011911600f0586d500d100d5554009000c0740131034210a00d45024502a00c4519a100c1106c07060629000c40900751403080409a135080021500c8240d102d07405c005404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 60325551 1250 60324301 60324311
    0x50a141509041d060603160b1210080111030411010305060a0e090109050118050d0908030909060f04021903110f18040902030d0206010317090d020409050f0109060203040204052206 79
    0x300800c00a1200100104a51240e0b4842c4143c2820001d01d491088000f102114041c3e840501d018002641c2445440d40c03658040c080500003910802600f40e00c5091541c0280c08240d4989802d429599090f022a5424100205000900400d0701107952500320a0034103000da0b007400301c0494034103107582c465940101e901030082940004e0039040a03541e6500607009200d00c580400d21803003a0742d407a6108580c03d1052a200d0300c0b019000300000021200400c02640c21310420700c1c107100103981c0080105a0024980180d040c0940c2d82e032018140d40c6045c002c0100d08481026409821a580d000c01509103840501004c218444400c040781e29010032041484481801000481c02402c24070741e00a616000340595045543c0d400030308181240d000344184071050b66800000d0040e445000b00c1c00c0e410819182082c4007504064012043c01131240086030082c4030120760243c21a6003c2d981180d4150f000001d04c000d6103803e00070141c1001844140c04110b100148408000c400140401048543c0310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 60326801 1250 60325551 60325567
    0xd0506060d110322120807171602060a0b0a03020f1906020a0b07090f0608060d060515120607020304060809010b090103080d0c080412030e03090a090204050a1415 71
    0xc40140c50010400038018041030100c0808024280c00454582c407124410030a201141c0201d00c82003821984c1010201c103241190311422516480000c01c1c00c010300c99a1003103c03c00c4d1002e900114401d40300c1121400194445210003810100080c01540f45a03080040070070701a5903441420703040b02d40c1215814050344440b0003040c1c014001244a441401801c4800503203d038000c02d05450092040b00909080d1b0f83d44241550414407c1c002e10341d0211480d0070500400d4020420b15030000c5005221006c100095035401040d00c004940e0000304e800280722240140c10480c04642030f10b50103030003070062803400c0c8900070b41c0c0740036170301c249810030010201250b604602940002001500500708403050342c0c5904005281e0741c4812412400b06c1e2800c0240d0711560711a41c0c606000319801a44101c0301c4228100450260082e8022282640810806210303241c1e90b050701000100034580e0051b8a031031601040040c0703000740741d100103d4140090030f08643c581d10072600e00c0b4a0000300c0600f98654020b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 60328051 1250 60326801 60326809
    0x60315010207030f06020a0807050418020f1201170d02340305030c2109011d031603140706020f0a030c03050c0a030306030516030b0a020901020109080706060305060a020f0d0506 78
    0x2c940d20241c2040e030710085031020702c001e9400801840304c40f5244c240c0d0b02c0d100c040c000c40d07841c03096118541d40b0b1049010300b201d00c6119900100021802c4c00c0c82541000c49010301940400d03001e90000c942c8a0401040d04680c00c000d0045440c3e46001c0d00240c0205180040c0c0340040041d520341413103402d50004005090003400079400000780d600001200c3d142c0b08000130031070380c440844c0d40303000c10304c0f00c441d00300031010707001c901110244c400685d1072480c0e454000707080d08102015842c40c0c942c90300410203031482c034848503416800103600031807580103141141d080740d41c01e00c0c240741c0000f02107400c2852914842400000d18155a581c103142002d0010007a0070211403e00641d004182e183c003c442d180001d00d64507400c034105481c0504280e441240301b0741401580000180700c010b0151040c00d00042c3c0501080d40601301418040c000400c0040705565841450b901014040b1081c1d40e2741da8003842030082c1040155403100d2402e1045260181e174000044003030080791a100e4070383c4d890382c000642da034403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 60329301 1250 60328051 60328063
    0x5120a05030d02090316080c010f0306050d0b040204150303020a08030c040b030c030a0b030721050a020a03080a0e040c08040b09010b0312091f08010308070c15090303030c0e0603150102 81
    0x180100507280c80300145281c01000c0e50102500511034400c108107109902c8a0f02a40e2040f036a01c11300814040c1c10100040d42c0e806109883c02c414560b45100000701c80e00c0d03059006c44c1c0d46106030a03200c140e00e480e00c100011104403540b10b400080d8018010300000e9000a054030030340303801c205101d8407917039000940c0c040d47c171558000705a501404814410145022000381d030140d00340c000c0034002011440f0901d039440c0c03114402c031419074003944010500040c0042c24200403601440039290007401c03076000705242d43e410b54000c481017407000900c070b07018550110358203a0601080ba01071203c034018850080606202800240485940e003000c81c14808095006d88440c64000c4c0503100c1c92140c41240c04000d030085203415010383c8031025081d526841410300107118800584507480242d0840d111440e598210000440d1490183ca0001c035910301003501810500e40240c0d105404a0300310b00d0000c040d6103da010030f40900c0068500c1c9980d0355a103a05072680408442c2c99240e07032401e510300407881c141e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 60330551 1250 60329301 60329303
    0x30a020d060e0403080f040b0601030b0609030d05210708010e0c07050a0804090e0c0607030c0c031502040306060501110a020907091e030b0f041101080601030b060d05010305060c0c0705120a 83
    0x40e250070800600102c04804041c4070f9406929064415528a40401400081154002c0003520300713500084071503019610141c584030004d802542800740050109151048d00481d0b00041140459211901403020120741601d4203009105401ca003803030070700642420410700441700814014000207075010b1121050303c4009801904444040d8414101040640d0090083c501054145402d038078451000113030343c3c240e018002c1c007098075100445d1802c0f07407840c0d010402154034400c480d0380000400c8495503095140b140881d07005943e20b1071450290103d0f64164002c5040c4514a0b80d507803040039010503440d880356010b4030403400c070f03640708841101d810001380c220300407810100e0404211100c40812120589100f01041c0c00c1c80d803100d880d09540c0781c8049500400c0b40440c091889120351141c01740d00d40243c810b041c0480e40d000d842000034896004003070300c6100c0030740d240b0040080c0281040b0194004403420078161038405581c00d2107403900e500d4080c4a0003824501c0c0c0d42d110414007004840105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 60331801 1250 60330551 60330577
    0xa02070306091a0a09060b040921020304080607020304060e0d0506070c020609030307081207080c0a14040e01030303140705030c1b07030501050412020c0a050a0e07021609090302070b0304020d08030a02 88
    0x180c0b0b0215480c1006181c44070040d40c20354a001030b102d0719410239100345800a07030410810a40590300c1000c102046601c00340342030840c0001d00001034000002c02949010703c8080c1c010b1a140da0a0103401840c280c02c000c0c10911500038184280082900424005d40100483c82c1001d07092800d400400c00c20b03c5810f180c1501340c4000120b5030b050059850140c260502e0f1300c01e00035020f8649400c00c0328480b400351175a5144c214108098000709000d102148020003200010300c1c202599490381c9080840264010b501098807406d80f81c4080148000c0141d0141c15030402c0c034214100181107003400d0048422148090800300940408900d0400c8160000d5512000030b00192600d443c200c07000542d02d64520016216032050b1040b01d07d0249100320076513401400440c1c40302d2a100c001e40c185000602520b055006240d007070803210081c043c84202415103194003054419030703840c0c000d240554903031103226592414828400180c0d941e48a1494807a0889a465265280c00e03444400070701c241c522403c64 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 60333051 1250 60331801 60331853
    0x504050f18101811040512010e07060f0201140c04060c03090504020301061e0212070b2d0106090501050301030203030409091b030b010303030b060705060a051005040207060209040605060a0207030609 87
    0x5581c40c901c0c003801900d02240400400f80400761001c0c041d907800401829082c00140070a02450800c0307407071090707106a0100003003000034100c1039180c02d00d94190410000036080e0f0110301c040b150240268032111888500a1615141890100c0c0060040b40540d200f0019040c80c0c1c0300c245480345405402821004008550301e5948a0307015059a007980e8510340c520000200804482c0c0c00480c6141e547c3c52401100e5250444640d10507101001c01041c0c0202003064040610200d00401c040610910200390200c2140d410a24040e00e103c50507481103040000420041c40140c50200a507811540b010a005ca081c131607074a455600c4800c2403000740e0440325010800001c0c400660045030490b400f030b840400401d119038052091610a6074000380032580800c006c14849540307644500c0c0c3c00b020068003045200d48400001c0c0507a8004401515155000310301c4a0b0540342610414004180440c1c94500d0b2032458500a034640e080d62001030046039454060700c0a1000c21409401c2c00c840d02840890 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 60334301 1250 60333051 60333061
    0xc0c091e0112110306070905010c020409140606040510052404080307030309030306060302250302031c0f05161403060402070c0303020a03030609151724040b070f0504050f18 76
    0x1c50180100740c243e8000542815070203603800d01040c0a801040940d07504490203044c07400554801450000072604242c0c0d8010002c0814884081d00840003070800c007030103403818203000304010340784041c0018070480c003030f40030410840d0703030b140c007650f42d0104505140c10509911a80340c01d818010f0f640b1100c4075001c001242020907078150b20505841e4484c1c0c82c01c12a0988901040302203008010755010752882c0c000c1e20500b100b80705208000800d100e40304030f9143c880320340c00074400ca0085180c040407150711182240d007840007038022244c0c40381d03115092000b0081c2c2c42c44000e050380030800803118555400404111a5222901100c1c402500308911079451175883c034000b9513078078203024186c00107807500750046440354071400369203804c48810b80104845410910700c0001070400c02c84141c1d2510030074141040362206a085000660802c60a030401171415041c02101070400030304034410402203411510140f50043d0582e0280c43c1c080c1c038149140c41401010a440c1d1a03001f41c40c400402c88941041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 60335551 1250 60334301 60334319
    0x60f110705031504060f020301050d0602071106130815130f0606030f08120708010b091c0b0a1e0c080a0e030702090420010c120302070c030602070b0106140c0c091e01 73
    0x10300962044204000d003a0300101b58004901081c0912507210344604030a101250458020b4034109001b405c00d58000c0c44150005102544064107400d00300c000c4500c00c01000d2018000a50008100c020b04e24040ca04440d00c0401900d0100c401000a034042a8003401d210b01176000c070700a1540320480c1e43c60303400c1509154059400001007081382c03c0d602c500182d0440d02c02c110075070489183c20035083c18941280100710b50030900b424400b90345090040088046201601c646010714039103040042c1c0781031a491016110240c0070305401c04907007070041c03480311b00d030348502e0746507208180200014184420070369180c10351181740c0019505c03e81d00c0040c0420300108584540380000744a9242d1822001c82005681e1046a128050070b5070309a40000440c0c240650018061035100f90000e8140b80d86075540e4104a8210300020344140440300e0050110541000e0b480d25043c0509007034500b4880b0083d5070340d0b46e501000c40002d01400d6942e000c14030340003043c0020154040c58102c640e07850746c1c69207420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 60336801 1250 60335551 60335593
    0x30708040305011401050d020901091d0102040b07052406210307120f0e09010323031b0105010906271803030b030712030807031a0603070503040209060604060f11070503 74
    0x104c103c003440c6000000d002c4c9003518450f601140d000d0440c04031a071a0410103001403640784103e0030401034003080c182348505c080c8000d00c060071840000988901e03443c10402d141c40d40740681111800d01a07951242c8501c40e55040c1341c6c0c032220443d909002100c0c43e00b483c400500c0c803641c5100307641c4400701c1c0c2403003001504421400c880100e9038410f41c2d4401e1301c9004640c1801d003008819041035035000188080f454a520b144074440030080b200407075071640e006031440c642c0070758491651000780384482a41302c0d000380142401016107500030b1089604007000c03840740c0140075404030000c118803182d485444110b504800710207a052140321400a40c1410003401500a0303191951190186880115403c01d40b0500d000f00c4580582d1a410540d6480409a0041c01849011904c0c005203032010482591110001c1d4420201580d5154580c1041c0c8144461840007a003081d102c5d10083c1720034800720350300c41c0e0270340c0382c0c10301502e0b00c00a02a204400c8a0800e0080c0d0480303074140c011042451080e0b00e5012038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 60338051 1250 60336801 60336821
    0x909131104060e0a0e06130204150b03010303050c06010f0311010503071709030409060e0708040212100c0f0e1806060901170a061502010203011d190f050603160b030406050903070804030501 83
    0x20600803a28085e54050f100c2008403038440200300385a40910140c181a4071024420034519200151903459000e40c2030140c1007648201d0008000045440204034240140e500402003650115000e45c2507644103804c5c0d0301d803040f040d1304100b00800000c40c80c0344601d8440c018613a100c5110321545c105100300b5512070b0301c58020184250f003410800160301c0c9a00705064401d1100d0368a041442c0c407583e0030404811100e01c01150b461155005500e06c03802075208140d0800b07401d489818640082c2c800240001c3c480007601e0388580038130881011207859940c800c550141e81280c00542d140a0301d001602d04803040e0906025041c0000c040000000e03055001100b0360700d0042c00b0302c0c40d1002488080b0700340d20090080006c0c08410420000c1c602c03000050b0580c00c49203101200403604090301d100f008481d48034000c44172041c2c0b15028010b46050074022201d40c0400307100c1842045060602128192101030320088c01c0603a20b00010341c140000780709072600550702c4041c00e581c0f55940c2c10712a02a002c0030103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 60339301 1250 60338051 60338071
    0x319050c190213020a091701020a09080c03060109021c0e03040e061210050601111c0908070f05060d02040e010603060e06040209030604060b030705030a0c030b09030909131104060e 79
    0x100d0503001041c14000c600c02690041103100d0358003228210401940105005200b4440615408522003404110070b018460981c000141c859404039801800b41c0d4180d882030341d11790418058a107031a100411058190f80305e03980096510040c100c082518005511f1844801c0c900d0f10800020000300440108122140441024002d03140e40041041000c3c09020b1141c039070b840041c181701c5640d0990405035000030141410420303805007c0055080c04d20b0243c0103608000f00320b5007109001c0d00040c2c804003500310030009002a81c00e085046541400301d0003010b100c0d100101d203407a02c0740c13025012a00506000a01c0d82010759460314058080d0005e406000c5001c404840060f046040500c01c2c0c491100c002801080607850305e841e101e00500309544603035094014540302080a0310104514168144202502c1c080c0358514205105404006081d140c01a0010003d000140c0e990030100c80d0031130340b004c2d00f25900d1032891400c0d0381c142400c4683e00380c04c14100750000440c0c2c0e040711459071062801311 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 60340551 1250 60339301 60339313
    0x18050d0b190b010c0b27010902090106080c0403030806060f120f280c090801021306080a020301050102060f1009050705090f0a050105031512190507151e020319050c 72
    0x2011041070b11269200c05002405062482001ca035254001c01d402ca00c03144134101c8070745c031010f1820140c0e118045007204aa91260024011414020341c064010a16403034a903155060445581940344298030004d0100306858012482540d07401e000ca85d103800016030059a40d141c600c00c483c09000084840d02c6034030540074001080c0d00300700110156600c090460154074aa5a0310301c0320000c01402e02988100305103440007103a9200c2c24401845034020f84911003c166103400002868140000c0031400c00030300610040101ea600018042e400600b8001c1e00ac0d0b00d03558503150006194502e80c4400c507000d0400b018000c50b20303008801040074070810303100090308440300424010302c1c001500c9101d00248042000408182624070790003041c2c44010415202004540602854840802d004d8a40c0500074000c41c02004000c00c812401481c05400945010102c2203018008520698203884080e01a584003440d0520030f0045a4a00c44a440c03443ca50b54000e0308000e0541e003102c6a000c0c1144600c07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 60341801 1250 60340551 60340591
    0xa0201061e15170414011506050418061406030c0d091b15021527010614031b040c05090409030207030501050903040803030c0a180303030e01050609060306040318050d0b 74
    0x20f0b07006007003408001c020b280040c0c0c80d5552460480c0394004400305440d5a60041413149040a4481900410940d540c0760344071801c01807248440020031f0304080c21300c0c1c603100b002c103c0043c0c003c0c0b9482803d40202c81007030f202c1e40c442070207152512801e40c1001d044d900d07001c01c14007007207a561030407500032200c5683d19400f01e89686581226000b1844140c01507842056842d9030b4130703040d1070b1a544c81000d00c40503c1c0c0c422004400d0001120034180e0b00200c40e516610f040c40f65041c40424602846000c83c002e08150b1203500380040640c80c070b0150340d0f0095843d100e2102209000d00110b91003048050010840c01c00103060003921008280030444c0d065080130081400e541d0b0020548055a07055409140303581c03150f40501c503460b0b0180c220f40040c0481c0c210015802180d071244680203502039100803c5605d12039031041d08583c0000c1c500c80c0b003011100c080c03010b01d440000306242c0c016030504010100e950040ca000900514603449103038000010b0140c04108000301d00c2c054010b00321790482034410a81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 60343051 1250 60341801 60341807
    0xf08070e0403020c040c0e03010e150901060b03070c02041401030501050403120204050120070b0a02030c0f0105010e060904060b061c140603330a0204030212060601080109020a0201061e15 82
    0x309440c0035005901c1240c0c02501490a50702041000f0002d04100624018004c0441d0a5490508423040243c100d1007665900c1d102c00030701c2c150b03c42c003103038002c208807401c08540140901010b8040020001241182d4003103480355481440481c0c4551048001c56030340e03180c454041c010031a01100007030455900180d008490b8001e850940d1030585079030590010264410044444601d14801e0030700c0340e0745000078090072440041c10450b000d603024550303a00d610600e03d49081412120b45456a26040c0108889544601c040e0f0b01f004c41180c0080035502c80f03050460180072110480c683c007400c0042d101c00c140161100c02c40c10791a103114244004c041c2d41d42542c445c07a40403680c2980640007003004101c0c01013403108001000113424440440c101c100400506144011211540ca01e90700080c10b2055103042c007881c403500399080c80240960310706903000906520b0188603000d000c035004103010f15100d000b90414805010500c103080084d101d00c952a500a4600d803044030a203203a07a408a440c0244 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 60344301 1250 60343051 60343079
    0x110c0c01111207021305180706021605211c090503010e0d0503060a031205120c0a09090b1c06050109050f130305130503030d0e010c020c150f12010f0807 67
    0x7805080c0d104003041900364141c0c010601241e00040540d40104c0114052007a40e0007000080301000d240c1c0c240009003494201d20b5004407007950b004901404030f94007451450300940310281c038400358030200b181a00c1001c0703034200c0d0520080e0040e559400e80100980000e21650042da90343c910b0303103603628410705080b14a0940039001301e0700107052540c02517011300d00840e08031802610040c405541da031190f540d415009001c54000482c005072100a200300941095040007814441c589130003c0c094010300b02081a204402a581d216144d01c1180da94048850aa2104091030348010854900e04a00240001d001d1011603601e8140400e649695810706d4922031044500700c41309032080394a09540f1504524080b800405024a0100740f41d10140040c0c0821600394a002c6070180003400d009095820400b0700d07070110b5200784190303c07455a0300a42140c10103080030b281940d6059504c1804418842d00c0c40c142c803010742d04400095991807082d0110216028103095a15894603983c004910340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 60345551 1250 60344301 60344327
    0x15061503040611070803010e07082409100b0d06050a080309010f0e030c040204080f01051503120c0c040509030406030b0a06050301090f06031202030a09050a080604080c0c04110c0c01 80
    0x4102840007500166459001e001e90003000700e01c140c20040c8a94502c0c960703900036085101036049a40034012220f800502035504071b54400d00d6914544400700f6112620b203c1221003a00c60400070011503100015400e54002030424844410342d0b418440e50200c01926082c0300741401600c0700030300003a0a0f0000b005480d040d081c1603450800105103502d007156600704403131000b5410300403540006040d0355103200600082c00102d0280203554441072509085030402000d9541030041d50b1054240d03a40d01040c889203400281e501d070754850303500c244243c0c5800084680560031074a400140200d80800001400807142170399400d01c40c403040c0005201c1800c03641c2c0f0940012410500051050b100b980d004451046000c0303200164040c0c0d81e07100d001c2400003e40080c000b607000001c0f1a068070381d02482d054054001940d015040c1d0b460f1907030090707849000400142140c030001c00d112800417001d200100362514020000d1240b000c0c030340e0b40c42e141c582c05250760004d24801c10003095003030350040303008503e04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 60346801 1250 60345551 60345589
    0x90603010606090e040809040911130908040504110409140910020a050f160b010b0d0c0206190903020a0b010e070f0206070f030c23030a0b01020a050303060d02010e030303091506 78
    0x8901c1d20100c0d902056005e002150702200c10700820030182c8541c40303082006401003401c4454079031908280b00d45080c10442c44101c1904014458001c1103901080700c08a075001d540c0016041c81d07080118405000b2a0803290710641080011201e05a80403000741c09032010340e00b074410012614003808104e10901c0711801c08140c041c0039540b50700000c90050710003100704c010042c00e0000b19135290400350b1001d0300400c3e110480801e0101013443d0318400c0955900d41d50001301443d00f44540d00101d9001c12445806c0000d449040c040708140c400d1200c0c60516500c0401c1c1e04142d40c50361110049604219605000220034103a1803003403510001d01540183c034039072902d468516810808a0140100c03095000500c40d182c0c1d0006081c1c900742c1d01c080860205034102e580c1364200506108140d408907444181103621510396030300030903000700c01c8907009482190360382110b0300584010b0751045990304405905000100800502c0c04e00800d18054010340e40c035030240e055540f801008000401c4000403100703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 60348051 1250 60346801 60346817
    0x903120a090e060111010c1e1d0d08070c1d060d020904031125030c0906180903030f05090a020301110f0403110402090613330e121b090603010606 64
    0xd8014900b40582d08007a0615000a2803141e1150440c20b40f0400f04040300010419402c0120b542001848880521494a04207800480031360030402c910085902c042e20911020310070300304200c1c0e0102150001075120070001a46076071001c52041c524005403079140408545070000302c4c0d03458000510040198028101041c903125034404440080056170034a00300e03c6600c10105640112400c020b40700940c11b001d911845013145003418481e0000e6000c0000b0070b0409205004031240160074000e0003541941c00178400045003411030150120384a0f040c00186007806020a416000c1080c4141d14000c0d0001d010300b400e175507180c440034400d03a10688407540c418081400029a41d0542403c1c6d86802031000d4240100d1200041c8254080c1c0c83e0018000110101080444503894041f241110420086202c18817500801802c095012201e8001c100e450b00c00d01c46582d50305030100e003442070b90800b1541170001d4061680d1314107175950a203920070440c220024480f4601400b80a0684010380d80b5020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 60349301 1250 60348051 60348059
    0x60e06040b1902070504050c0702040609050603030715090c030b04021c0206090d060b060d020307111c0e0301140c030601110606030a03030519090302010c031b08041112120903120a09 80
    0x400440c50702002c008500078004005110368444c010303a4010001000c3d442d17602c1c2042e104200c1201e90700d600124615081004024a6940c04410780d00119000a12440781d18074034020704000744944240101000f10240d03000c0180700400988501c81c40c400d4900b031030740e1852511164140f00c01f42c600294048420072151405080c00101c40c0c2585128490209440c2205800034686401c007103010004580d011003001b95147c0e00000f01045d007042030024104100c0510444461003440040c0001403109a090000319030f142540906184128102203501c2401c000700350380c40c581d000740c0380b0500140124042100140700481c1d400e014010040003000750020640d01603002d48001026040706005842c89004007110600400c40c090703200382d00020b03480b50a184064201d80300f041c9000c11720440c1003000e24440745c003c140c80d900150000641c1e100064041c000401f06040d4001d600114010500c2136846546484041d00d8205400c070142e5001e41c0d901c4080744128003c2d102200700044070210700300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 60350551 1250 60349301 60349327
    0x5031203072001022113230f011b092d170a060f020a0909090303020c030c06010e0f060108071404050307030803010f050904080a03180c080a050705030d0f110102070b040c060e06040b 80
    0x1d00c0c8150030603607c01d012000c21145410800c24001e030f56460b0351035a40400040600740c40003c03141d001c0d410213807251400c10820007141200c0700c00d40782000c410341c03d20301400c54038020000000d201400210602d074064a980343c3d191031484c402260118140340e601641c1d1402402507130110a042c1d95400320181c03400c070301b84010b048402c030260180f5508000004040034140010100b4501200c0144425454010b440e120240b00400b9030202415800500a5983e4410301090300940145048500c100082c106242944550340c0718691504c0b48210000c00c019128000c0e41c101c801c1941c480c2c1649030740c0c0c003c1c0031a02808880092007482e0070401d600100703000f0f1340000765030740c000800750700d00c58200d607035041b00242c450304085282e0b4032a2000c20f040050403c14600540411b5029140c1315401060180860451541003014040c5a851096140c0b500754150b4a406800190104d050708080c1004440751032603001d41000a0002141003810341800c0c0100c0d001c075015031080526203c2c1002d10f032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 60351801 1250 60350551 60350573
    0x1030207020a050607031707020102070f0609140d1706060c0705060d020d050f0115031b03110f0403060203010e100506040b0d02070605040606090b010905031203072001022113 77
    0x490b400b61118402141030384a1002034940700b40302c1c0c2c44403111000c40880c81a00c5007402440f800071a801082000000380c50f0103160490f280c2e0014000c202c00a20340790801042064401c1e003040da02c42c400e42074203c80c1e480080380c203444108200074039468580741c060094034070a0b900d9805a40e8030441c0d0420450401c0b00050028a0301040d0050a004184011070241c681c23b0f03840d0621003040c000140241009406c41300485426402c040040602c09103981c9140340c9050480810b1558482412520500a03005c8580e01040d0424003903449449280c207000941080c01101c8008114074001074046070020320880c01d644009000340d042901e007a0030901c0d50760100356200384054003403040c54009002401840c1c02188500404a00141446114000c44540340203860404c050440100515200841c4420300321580f840c42c141e0340e6640c1042514117603025480d0080368480d410400d001502c065002c2e001907440e04c3e043c891108000c01c1d0110f4610020f4a02c0c0d00d44200610851001071404060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 60353051 1250 60351801 60351803
    0x3f200712030807140304120f020109170c150c0d0606080f0c1305060a020616050909040803060102010b0d1a0709080c131b02031305060a020a06020304030c172205010e01030207 77
    0x1055040035081c4c50441010741003510222010112011502c28580c0c10001d1041c02004503c000c1101c8650341d29000130290169a894070a84c13070001c1d010b06000b1040c40b941c1d46455078815044524100303605e0a000561000144502c90341c40c003034001ca200703403290101c0c0b8062030040e01c80c10400e4a078080d940400e40e100250910f400b85001c2c900103110f450f5072001d03107615610f54010302090b141c00c820b9400010307614541c0710100702d020403403048555030b151202c942058021208588981da08801070340140004000140e1150b11200410100a818081d00c200c0c41001000c0008940380d4103002e5403401e103070340500b64242e040f01e0302010003818601c2141c82180c9800401083c0384255143c47e11752162030305005070050b000045e5200d850500390160400401c2c00781d810600d001800c400c001d48442c02c006000b02000c1c1c002003c1001c0c5445600d08251898220320300304aa40c0500001b84610780c0592540c200c0007070140082c201c00b052901e40c0c0b170100d41068440340780300c030981c00045009500c0504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 60354301 1250 60353051 60353057
    0x8070e04091202210306010c141e1605010302030403080a05040c0b040801060f05030703050601050105070f05063102010e011b150c12093f200712030807 67
    0x1100e9408525009198184a0300e25006412506140c0c0ba4044c0c0150048011074019441001400001d980c402048c86a05402840720058140c004444a04003900d0404030210a204940002524600031032401031000115100c4032000755290015026404112401750109541c0d500140125540e83c000702d600030b114002d401503481d214449101e240d0800d8100052a81d074034042802070300180714012016010480040c0f81c1946180d8850366211014042c140c1080300210341c02d010841d4101c90034001c60740c07042c02c1d181a485e05000f18825094401003d0350000091b9100b19810b20f180d4000c1c4c801c03541c06130340d64501d0031140001520101026095008800a1081c85a01107010012132945c41c03482c014011486520b40c1c0f00040840201d9070030044002e00d05a41c110009800d03c269200e41408680d000c1005c1c001d05034140c0d10f043d06c5010080030b003a2103141e1800c0003a8052441d030007140c0d80d0042d90385d0080c004c850709540c0d06e07498000c801c400b007004c00700c13400460b024880302540918146 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 60355551 1250 60354301 60354311
    0x30412110c0d121b03030209120c060307030b0a08070902071a151e030609070512070b030105010309020402090904050c01080901060602030301092a020a0201120c0f120e011104081009020108070e04 86
    0x350030b840701c0751010413080e8002a030100c0d41480c0c603e0f000d2549840541d602c4010b0071141c03006000a1078500c00a03080740309250351040d0034005c41c4c4548080c0700040c050902a507944558442c0900003950010004480350700091000c42014850080010b0040c2010042155011140d205000019120842040b908181254261051781c0e0401909105c0c42d603200190484034030300b50a102d02c1c1c0410014400054020100a00032000b0709016a41100c40919000c00d40c05424008079000780300d4121000c0d041054842000b003440b01c0040d49800e8100280d035a12101ea40e02601e8a088900500942c40160410030040004144a40201401c6184515074188510010070020000c404880300b010250b004020300600790368000b00303e400c4024122006124030400c2010041c43d2088a01c140b82c140590702c441445882c030a0350142c84c903505243c000b040074071301029100032650854031441c4180d00c295069040b02601d1030169082c50f84e81a117400026494460055039998103c0500342d800960320f13 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 60356801 1250 60355551 60355577
    0xb01051b030d0c0206040b0a0b0f041b022104050603040212030307020f010b01031416020a050601170c030f0a0b040503190e03160609050d03020c0303030412110c0d12 73
    0x116a40804003032400c401076907907008079402e03081910158498101590803e008000100e08407012881d4040d200650000703107589036000181805140c1c0c0201c5402a00e8540c0c54681e480c400400c011400d0348a4003119441c1c004c41c02803041f9004185041c04400c030062000b0005400c01034055500701d03100900d42513016421a2030070707185410442d0046c0069000844c21030320030380b0030321a42442c90003e20b0240401902d40500c03002281010b040d515000c1140841200e4051090159001969110040d2045540d50380303804a40d40060910b2445180200d650b800d03014a0002001550807141c4405042540800d8669116820002388152480d0004010400d440e0108480011100403540c580c00313180c06036074040c1881e0907804403200707900d101021b400340f20f000d421003051401c90b103007120303581c03104c05443c0740c12400c1030038a00d249034140c80301001707100410921400c6900048455998454402072050289070343e901c20065041d006428416040042a007001703071210f0039081c604040c40c0e0047c103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 60358051 1250 60356801 60356827
    0x3032109060e011407030e0705060307020c0a0f0807090204080c060a020f100c03180f060f0f150503151605160209070804110102030702060f03060114030a050a0b010306030f060b0105 80
    0x30031482044580d5580c4c11801882c030101001035000b05243c03070100601e05501844a640d140e59015451041002100140525108001c0c122130b0160113000728451f56541c2805d480d00d02d02c01d0080310442e0141d90720100b00300f9224400d46040720b5000c0028144217034080148010f80c1e110b50319401c02c6004001580318042000c004103e50034a07001c0c0001003038190101c0040c121034480d00740e0740c01184140000070202e40e000a0b0070700200c1c4c000200003071a03003651150702c00800038010ba4940c01c504025280302d00f4500c0010340c4088480aa0694421021034011422800f804075400f00c4030000180b90651640d101d40d0141503005900b40a00034040c50f0f980000f07900c012b04032441000941c2560410042018030701d00b00440381c0c42800114140b8245600041690040c8071408d40c00d4440800002c1c800e03846081015036000003515001d50b2070600100c95406406c080350662401c0d410000b18a85a5110748183c104a030742003c04001b41a103181d0302c6501038103031416039504002c0c081c44a02c20283c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 60359301 1250 60358051 60358061
    0x8160305210a05010b070302100c030209040c1205090a0b07050c01060b0c06040212010c020706140403020d12030b0307030209040b1b030a0204050f030a0b04020603090102040b0703090806060306010303210906 91
    0x1c54801000400d1400c00558415200141c200208201c8140094400a900010450710204000b1303401300c2c0007600740780114000c0c000c42c41d045a0050803d0300ba001c0c201d4010031004402d805c0c00750140724942d00c00c840195504500302c0014006a07105000030102481000544030031203000d80040340b090f40d503c800602c0c41d04046449070b041d4011009100c1146008800c5042e4020300c10028400c2d0384500101039121b51840c03040d00240422060228180b110f0030b0101c401440c0d00030203071426034296003002080400029030003c0030038940170541002c1d140008400d0300301d99008040784150795881e56614034404000c3e00080c441001e40f500c0b546028848009544102010040141c6880c0f400e81000f001d056800d0940b40280c024102002c0403e01c0c202c000e55129406030344580e940d45905c000b10b402403241350701021a0700c0021554508041d44042c15800320b0f0110740c11103c058465100f00b60700d844082c070005001c131b500190346071200540001208641a845880081c070100c0c981c0311136065407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 60360551 1250 60359301 60359347
    0xc050d020609150d090b190c0203040506090406031415150616031b0b061306080c190b130e010602010203070f030b0d05031903060608070c08030c1c050106080109020708160305 77
    0x340000807c0450a06160500910400b25406000c442d481da00040d490b44601d0083d030340104c0d0005280741d040d40310b542000000b5a445502c0f079076201001c4480c02c2e2920101c540c0100c08402e80d9001c244650980c14140000c6100100998030b003041064800e00e01c2c0c020020100c080c00340da25611100c43c0380404041d02514054459180c091070060200700b0a803100c1300d4030b40115480c142003405160380c0010360382503c000942d0381c0e018200c15004d40500c1c001031039000b5810a280028003100903411405e01408035244911481d90f00d98881200742d00740d00048900c50002913648031142c0140b4400d0300800b0500c00c001e081001c079841c070398454900b568000015400080394107110f1105881d410721400d0002e000c0341c0341181003414420b000501402d06100041c18040c070110101d10b11907124421100401c010700c1030017500312030512104028003024422403002c5801070000040c01d40c2a80215000d003903010000521700107150f141e8448258000409a00b0000144070303881e00710400e400c1c100208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 60361801 1250 60360551 60360563
    0x9010f0c0b040f05100614060c03070b070509040c090308070f020f04060b0306030709050c070b040c05040c0e03070f0506040513021204050601150203040303120507022104030c050d020609150d09 85
    0x30701c1c030b07600300315241c04217580d0071818545c5007000400c0341004080f901401d41c0c0048850070340d05c82e00601c2d003e1030b5000324100a81004407100501010700c1e0010000d01c80d040c0d0685060028890b1010240d0703815410f8400589500e0040244a0004014440030b955447c4000c0c40800d0b242c9900c1f010408507080d030303045900180300c000700340141031030b080202d070f4010701210400340120314041d0889a401e016810009000c0701700c020205080040d500199805000060010031000600f84001800044118601c2d4001d00582e807002c20108048a030741c03820b4030340140c54946003903d0401031210000d0206100e0148039401c0c050920700d20803c0143c54000d0780610000e18655042c0540003486081c00c10a05003558010001000025049800b128070b18200140000c0c0560b60214142e09101c42c540c80000380700703c1ca4602d010000c0c2040042d00549008441c2d017138070030b070310350b000d01003150b900c100c01a5211400344521907840c9009104040c1c0e50301c1d40d030100c0b820512424441070695151500c2110070b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 60363051 1250 60361801 60361823
    0x4020121091b1d040c081b0103051602060601110c03010c11070801020405090a05060103200307020d08090a060b0303130f17060f0601030b060f030906011410020309010f0c0b04 77
    0x140b001907280e0034a00303100302451603640362a1082002450141d1580d40c00c20160200020f800e00400d0003541006000801c03d442d02002c6030003500312842010444907020924002c04103014024074520051104565001040c041d00c0d04801507410b0385d1010790460b04c1e44200d03050130603039413030a0050520121103a110940035100104102c0c0c28004144c00401c8240e20502080099540c0c503409c05401c46205280001d254441d0360049005d031084440c61506a49032101c0443d440c80b83c240154415840c5038261240e101c1d0124040360361140940d000c1c0c19a0b40315110190200300168081420b0000090480c1c1c54103007026064120b035102c945c071203840d606c03080d0000c020400942c80c16000f1038030004050070580c503140921030780ca00009040e1a04141eaa005c00b004a5101c0308202e4685010700c0940b60303200e242214086a0b520030902031003400800c51900d0b1f103107500b807400c0800c00308241a00690708003807210700112404104008031100b0080644aa44040303805c20b12114000c60040c010450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 60364301 1250 60363051 60363053
    0x30a030606050f030613090605040b24150a030213060504060e01050306011205060303040504110301030614010b03010317130b0901080f090307030302090424031106030c0406080402012109 82
    0x4111103559001005101081000a404004800407242c1c0410101d40b4011406424040300008007a41c0030300501c610f00d010180f1041c0400d40d40030b180b00c0d5400815100440030918142d121100040d01d0ba540c01c82950008964009040300251008003803600d00142005128016004000c6642e40000040f4500060034800e03141d1241d1031002000007070034407901d1400c0c080700007071010402d0038031044400e40da0b401044242d507040c401c403030050500500610100700030780500b90481d80203200840310685003242041c0c540240143d0641200d441c0d4200c241580e2071600c2e454800040f080c2440040b0004008c04000d540e2040021809400e5000320152a001150000f60a012000c0c00001a02c1c5128040090000c400011900b4155140c5009a01d5400c0d0b00301040140c903480355a034000d072a109100c0b401911030103401804982c01003185808903c500b0703003406034611060341d40a90b443c8c420401406900e020384030864001c0d10600d0a4001c04194006944c0d65030100c202c031400b41c4fd1180d400b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 60365551 1250 60364301 60364307
    0x70c0e07030515060906090121060e0f0408030712060503030a030e060708061f0306182702010e090405190506071103040e04020d02060d110304060f15051201060314030a 74
    0x10390184514942100c003d1003100020410301a0600b00c511a80e0006402d20705e5903c5050916600d44030608502e0316428400c0c001c170041d1115000b0441d00390b44441c001482c0c64001d0b00542e010b00d03004110b5514688442008803805040c95403690300403504c458001450780c0f0308100514110040d5580098400e442900d00e0b41030041c09098502007107014010300c01650358160102d201000f007244803c82c00c1074940400d0b000340041d43c1c00840102852150300021100036000ba6014020102000c0c3c907000014a0030040384d444010064005419034003c00308d0745c104401e42036003140c014011680605050054800c0d2a1014507084030b2640106080c8541c064100102080c01002e02c40075605060070001851030700c0c08014006840340c24042099005d5458140866409124410b03091001e004505002001030780f064030221281c03480c01030350701d003000214481d14810310001411880950324050030408521035075842d419055507140d81c00000190000c0084080b4400030003d991140050003001e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 60366801 1250 60365551 60365561
    0x70f0204050115020606040f0b041a030105010806040f1506080a0303060609050a23150f09030705040203040f120201020903010c02070e010906081c05130603020d0509070803040506070206070c0e0703 87
    0x10301200b03946112021540202c5e03265131241d4195000100c5109041c452000760010f81c0714142c200d85000e00b01c101d4451825031000709580b0680080c006079a0300c10704182da07100112000303407140c5401800600020392150406c506a6503d031f0b40858200e03251100c8d94102080341c4011000b103030340d0382010018a50032060b407034000c0c0400c86084107014030f400150030203000124485110712501c5414080725940b40410015030700201805241c0b203109801d9614060b0f8005269a0700c248194540010f080c5894000c0340c2c417580c0e000d40d408d106032005540701703442a05d00090702d005654081c000765031151024810311100f8a40780c1e000308a01440d04a280740c0004041e040340f480c03d82011410300040d40005a01500e00c1c115004150a1010b50007080742c840c040c540708114011200c40300054040e80c580c01504c1300d00c42c810410031145d00d078020196078400491180440c1a0002d00c405c00c12460500301501600740050140c620b040625503401c41c0280a6030440143c2c0da02100505c080140d141c410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 60368051 1250 60366801 60366809
    0x13050c0103060501020c06030a0e030406021e0a0f02040e01140a0207150c05031311060d0f0f06030c12020406081212070c020d0f03050c0601080705031203010f0308070512070f02040501 81
    0xc02c141802c182c0000d440c0e03a000c0300884e00840001010400392105584420381c1c1c040d0170415681c40715203815009448142d0924032400406c200f0480901844010403680d0032a64481480010741c0561340c00e1001510011080440340d540c2e521003031161041d501e800d14807036075040c10016550101443c00800e030440c15a28119110314004114404682000840c0d0b00603041c02c0c0743d00c0080b500c500d40083c01e1940c181e0002d4020002042104001d0520303044010111040311050190080202c0100304603045440702511880c1101c00070408150b00b00c8020800500103480800c58a49034650249810010f0100c1c10203004001348000d410388808001b82e411100c9450030030300d400440e0b0006101000d5441d0701a2031207050010440400d4002c404840d035204580d4207a03400d6680d10f10f8a5500c034a028070542d8024000c9070308090321143c07150101ea0681e4408401c2c0c61403d81503845143c03039500050782c222030b54400c4041c0c162101c20404081d1840c144103102030000c4003600e10501055440c103907c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 60369301 1250 60368051 60368057
    0x90605100206100302060f19030501050f010c050a060203061c050c0906010801081002160209040b01030506011502060a0c020304030206071113050601020c121e03030a05010e06010813080f0313050c01 87
    0xc3c00a880c0e21082100204c0f50111841900c0715804c40c034400c001c0c440e40514040c9506000b001c01c074426050340016040310307012107004052400c528015201c0b00200900141160405c0201e480010020b07805950414000740c040c9010b898038015408000354100303403d07280d0343d200c0000d04016203000603c0d1035111400f881e100917a54035110b07505070b036101e191081140003a0040390800c02c014030040400c00136900140041401c1c141400c00248019080c0010307901c43c0258400415004a0f40186011000b083c4c3c3c002d00b01551004a500028000e03da682d20440c001008000050f983c4c003c00b920015005541d0011148521401c0002e20140203200000781c1d400c00301005484e80c0c002c48c1080035405c0c01e6404005030805011510700b000100b0701038062000081c0c003080703a5a00d001001c0c2d40b2074414420200400d98031000e4104002d10308540003800541141c0005000401900d4504c6000c1c0c484d10718103050003490b21108455070811640301488c020200c0f1807500b44807042064641c0b42800b03007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 60370551 1250 60369301 60369313
    0x5072c0604200705010b0603010e040308010b03100303030506120106060f110712020d02040f020d020d15080c120f03030f0910090c1205100c02010504020a09050705121f0906051002 79
    0x10100c9020750034a8440d00070250710210f4003c1c140482900500c0490707000805440c1d43e5a110000c03003443d0101510103400056036000041400c000b903a04481c041e2254660040c1c0107071460740c1c07c40c00b5100003015a5002500200c00c941a4442409020060b000f562660080c4044515004200c2e600d002d9610b01c1580c048201080a11300c681c0c1200b02003070301901da0013002d5600e400440c0190540d50100c00c4064400a41c00340900032075400f4041c0340201c00303410311201c0c0b503005580290025a0052140c660850030a2626900d024140174450a0562059410b040600c061507400c5400840e4840d442d50a002e0403c6842070341844060a6400d03045010082c1c181c05460354060847d00e4003c400005011a24210a000c1d040040e4080c024035200140032500c40c50030300074082c08054804a000300074401c0c02144c20141d9014a512803000d43d42c409050882c0101401c04030100078154401410211035115451741c240d0000102401c0428008030340b01e407401e001e00108540d10b0855400310b41000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 60371801 1250 60370551 60370571
    0x7020706080103080901030e0d051804020f03010909031205090c0906042a020c0a090204090b0616020607060207050d0906020d02010209011b110303070f0501050709150c05072c0604 79
    0x404962419284c000d80360030307101d450391001078005000c070030140505440b5411001000a074050000d0141030303030070441c8904100c440d209210030f0340122400c42e00c40780c1d42400180014509907102e076030098040d180100080b0b2002d80d002045600c240d860324060342203218044010300b000c0b101e054004405075810003c54905002101404a84c0d1a0079120001002005002d1034400c201031000740f00c000b0070105005a0316108000254002e104005996090100c1000c0c01d26000d820b8604000b0f001106c01c0040100350b080140c1540005411660aa400e001c140040351041043d84034035801a01c484000a080c4803000e0302d04010046a10f00f160b0040280e80700c5039900047e0f2490101d02c2410000e4071032100e1420000781010508615090f02c80490302e10f00380000c603d040807881c0d0058001304019154241c04807054055409080c0705c01d0a21320400a000b4401e03070841400601420507100700782d803560900c128400603545500307134500c08003070b07880070705c02c00207040a810040c00c5030200800d0b809 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 60373051 1250 60371801 60371807
    0xc0c0307060b030c100e0907050a0909091509080703081006020721050102220608011d090f0f010213150801030f0c0807180f050609010b07061803020c0907020706 71
    0x85090082900c2d448240b80c0050b42c03010002d000c40354000a201003901000900000c1200c0341014107544110340140100301c0790390042c021100000140e17503030908564204031034103001d8441143c08484000425565040d094141d200e050443e920a01800d903503403005050090041c540074002c5407481c040c140017045200e40002e040703401c880250a486a2200c0c41e03941e034803201010342178080c0c220f500018100d440e001c0c0190700801c56101041c0c241c02c055444020448200d00b0900581c1c0080c01c00081e09031417110344406181e03001c1442c804480707511100e50383c15801d20000102d400416174002c11803181c048151003080c0c01400080640e024440c0481c08014140300301072001800100707607200c1000500c8820101d14014000302011039810f00d036202000801d144040c00d1050740d46107050050007010049008840c01303803e000700b021003103074244800b0300c1440e8485074048890550300c0d581d500310781c8907000140d1099402074014100888008041c44a540b5006028008540050405114080d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 60374301 1250 60373051 60373057
    0x20c01090e0105011d040603030f0f03020c2805070303080a0b0f03070915030b0c040e07210c05090a0b04090507020a0b04060504021c0b10050307030305041208070c031103060c0c03 79
    0x80300346000c000740180c04a000d071050340001c51700f941140c1001804824580c00c06407074a104920b40da60f100340304c0901e1100301c04901610044100f583c200492158000240300c409507032400450141c90813203540b9507506e5241c040340b070b442100465501002c01c40e0540f054855000100016954010820711070000292980381d03d000701c050681e9184840780d4105203406019004d07561045507880706052110411020743c12911507290b10417807590015001e0f030311440781c0801c20780e0454240c648201e115040e40d00a000d5501070101040028001c0000566940c550100100300c0318070803540d20313410690150280d44c80103001c0810355001b12401e03400140002450799100f50021030010f420340b11840007420071000744000c24640344280d90320905115250707012328041c500a1202d92001c03950350051540f80c1c01c1c1440090003160302070204100e584440c0e040c843c0700e01c0c81101542e180040da690303600e04082c0d40390800d844048540c08048610f045c10040c04c0e410603200d040b441e0814044048882d030300d03c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 60375551 1250 60374301 60374309
    0x50c0307081e03010306050901152102011206060c060b0409120302031e0721060602370f03030c0302070c05060a02010e0d030e060f0f16090801090c06020c01090e01 72
    0xc0c4000031240c2842c40740400312245103001514082d5607581d030342000e4010b8181038900c882130303500c0e04010400398140140c0110480d101c03c002d82a044441c11040e405d0b4000180080c0e042c0490310302005d000542500c1803402524854882200603220b500700380d822900540c90560089241031a0b1030003040070801709a04d18501442d016a9075610384800611403500100d590203c0b480c1001071004480d0811904501800b01030400504101c205101c0010b40343d40f40b00b42c00242c0c108031110060b01c03d00c1c003036206280c0c038035035003c0c904604000520aa081218882075502d0700b00044e0160400d5803600907401c6211040c03600b9070804415444024140099100303061081c0701c00070b030490540c2d001790000b8050f500c42030280c0e07140d400b003002c018002d400140503a00b42e60042c000060180c82001e40c983d401030b0404c1e01c542e40c1d50380c0c2e00e1074580e004901865010041c840b079800c0c0014584402d004501c83d052044054054451500d2400ba281c9107540c81c5007414082c440d0002e01c400346242c03142c14111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 60376801 1250 60375551 60375563
    0x5030f040312290a0b09120307020306040b0414011104050607021305070503090705060c0303070516140a11030c0d02060306010e06130807120506010504091502030f06010906050c0307 80
    0x6034a45103000c0d5101c16010036068042424071100108a41102c84030340c40301c610701c190040d00641c4010030000407000740d01405100103020b01c43c098450415080d007503205c0403020308aa241900c40c0d00043d00d405811036048407040c0f180f07400c1004014036019018405481030009000d10b0030110441c2c070081c01030b40030305c42c0104000700b101c3d015959035090350800445156410809424041e000800e141e10464501070607205039800001e050030440700300c0e629454400080d42c00d60b2900c000c2121a80e02481c062802c40814881c6000480e450034250070712196000300030004043d10386030040500319400c91040c0320350400d000d0503070b141d201d1a00c0300000c641c2c101c40b00c40d40c0740d94650041c1c405c3c1c0c142d07c8440750424800310360003644c49440384006081e50032a40071900515a40c100d40520088400c038002c005410032401000103043c6900415009807080d81b821002c400c0b14a0780300101d8004a9480c20315401480074030032156003046004010740a00c0c81c140c0d14049404024075540e2013025401010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 60378051 1250 60376801 60376831
    0xf0206010e0609040f0b1603110c03030612070312030e0d03140406051803040f080105060d1a040204061d07030605121203100528050a03150f090507090c140304030503 73
    0x4000d103855406410681c0940610110300f01f0345201140d84100c0841000400e19150b40918403c0142065480070881c6200451941d47c0311010b002c03605556a078840130030712034030802100082000c1040c0c01181503940d130004100811404881c80d02d03080001540c1410328006020490070700c03507801140d20a4008401251944400603042c01190340c0c0c41190205010100d8041283d4407005140d000b1a0554402400300e038440078100f000b2140700681c02860081c0405440140c0c241030900107074018001040000c005649650003400d02450000b001c00300c078900d00400c01d91541501c0340e01c0140c03805940c1c080d40c4140c60000342c0d981c1c0c0e1441006040d03459002c40042c00d20220010008090070014000c000c20f02907802c0f003019807100021149614080125010909080244141d0f0490784c004006003c5d0101e030200081c014000300518480d400d8642d814071012030410010341005050034080041c480d9580d010045c65850a08846900b0140810610011961241c103480c0c0100241c801362035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 60379301 1250 60378051 60378053
    0x1030209030f01061d0f0f01260307030c0b0f04050c1c050307060c0f020f0715030b041b0207050607150b190b040e0c0a140f13080d0f0206010e060904 66
    0xc07400195400b09902c039824580c0c0820910250310b00c00030302e0082c0d00c850101546510440c42598042103c40d01784501036540100b24a02222040b182c554640100e07181d402c011075000b07181154808941a00403c0c05024500c082001421980f907202c0b002908460301c9051a03501c807501c03400b0244c0801c1c401c0c0481c2c0203106000d005040126801035002003140d55a0303c00303240c02c0c4090443e103580d14001c60400d558a00941e40041900744081d08503401410081e4107140011840072082c0100c00101591101000d126407520310a0903104410900c103031311a5012071070700a25200c202d03008603024110030700c40e18001401103d800303420407900c10000701e4040035400118440c00c00322006500401c0c092440041d03042c0c1c80c14000c106941d0700301983c1d0b14a6641d0710320307001944160130340400040c0030f0507800b030300c150354038006080e0300e00b03c1064407440d12402d4481c0f01e040b10181d40010f559078024a4125031a1754024841c03101e01e88050002d081d0541c0760201d50800d40b94004c0c29140201c4c9441c001130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 60380551 1250 60379301 60379303
    0x1030c1e03081c090b040212150106050307110123062209050f120705011406010507060e071a0405100e09040602030717040b040327140303090402160b1003020f0103020903 75
    0x3d445444081125841e2410514180d0b001510140d01a8014181c41455040045031045880507204020030099103044002c0700d83c0c5e80010944000c0002d650030059030043c0038014000b1105d060074044440320b40c810400f280d46800946098450f10030711811610010b00601050009680100001202d0360b83c1d0504901300315205000445500031020181d0508148401500c0510f000d50020010003000a941000150b800c0d11446e004c5001804103030300142d016086070a05034100300a6400071556038414484101d5444d01c4181015000f0405111904101402e02c2c40603805140416401c4510004520505030291002d03220f030350000002854240150043e900c1e0340d07401503c038080b524040c10824119142070ba0b04071300003038040b0f0740e031403485420034800014034050324a1070b8102d13840c2805103104a140040d410380c06000034060340d80140e686101824000c400e0b41c000038205001413a0440382190300510206c840a021031061026031900300c1d000c0c060050a0a0050359103202000103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 60381801 1250 60380551 60380587
    0x70201061412070f1e0801020306090a05060103060b03090321131b12080a0e040e0303070c0309031b2103090302010e04020909070e01030f0207110105031e090601030c1e0308 76
    0x205010305403240c130010302907a615135011041500085118070b1180c80c0c208150a230f100c241d80c0254000900e202052000019074030968219805041c000780c80c6a503071b04039000f60740086510070410707000496000c0c2c04540603044e88880c6402d0488070b0a01c0d20344085120006111003030302408200481c10703940c4001d527040c0c04000203840c010050060412103443c10142e00d510840e142c0c00010301c0c090102040381058003c031290422450040d41c05c650724003104550003210940154200800100d00201240303035110707480b410780c2c03075548e00d00d507007a051009402c2010b030100446200300d07107403d400b5401300c0ea0022000b0240e95091070001102c1002c000010068040c0244050703000c8100014440140c2d04581d101d0001d00080c5c03818030a40c040304205e00200d00548d2009007408243d071b8a45a0030750f2140d4000e603408214104244000c004400712401e201508841a40c42e540c0684014010b06c031303405450600802c44160660754120b00c02c03a95080c0e404031840300070100d032000729011054400804903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 60383051 1250 60381801 60381809
    0xc030504080303090a02040606051608030a1d01020301050108100b1c1e0506130207020604050906011e020109030909110904110f1c0b0402030105010c0b1f030f0b07020106141207 78
    0x320b9441c1c1c20f11500700c035102d03803900a003284905c0c504000010454010001c6e25050542010b610340a001c05031500c900c203030f00041c0620181641d030034106c00c1001c82040c20951000303a240c0016160b40c1400c0002d44115000f800090f00303042c0088040101c04110700c01c8910203a40c10a0300a2140030100340200038200d2004101591824034100158090140c4c1c001031080d0700440310300240030b40d54200c0364101d00c905075020f50008401c00c02030281d030900d5102c0c107803c154185024840c00f116410140070041d9540e1003000146d44400c541000d141e4800282c0c1c0152103000c400f00f2440440b000f845071548990b403040341c061038882c5020715004800c2810746402e5052000740540d41c0f01541c100088022a0020b07582486140600c4601941054803d40e070507904103031503060350f002c00b940302e4083d1a0070007412840815140d503401d1240007201036000000314464a0f8102e2502190714148a529000401e06011a03143c21010001c56400740d203194040e03d41a58170a50030800000264140b00061b04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 60384301 1250 60383051 60383053
    0x503071202041d0a260a020105040501060501080108070b0903030d0e0a06050c090a0519090617011104080c060708040510030608010b0d02090c090303040b030f1008070f030201050d02120916080f0604030c03050408 93
    0x1704442061f030190402845a03125000030440c15440e18010f544001c0e080c060071220364041202840b0500041d402032403032140040031a414126004203001c169542c0f441c0c45170860f000030b0200400c2004074012603410074a007000040c00c0124100104154010351300c5441e20406458940d0381d0f9420110506601030581c2810a1003032607250002034004c5402c02c030001c00c407036103054140d401d004920b100762130540c3c0340040603000e42034042e0200041c0e90441d800a4500f003c04020010345660399000c241200c04143d01e0200c1d00c40c4c5000c0c281400c4a01401c00a80103105a03421180141d480480d25a88000000d942c5502c842840700464038601603a006010070450000511410f640030785a0030748165521501600040d840d200580d4540955114440c1b40d1000f4080c2400198025400703040e440c180b840d4010304040b0301100c40070003160103540f614955000440c4912264000c54901c41c05000102d009200305604541d13455500c0718001d10113400c010f242d9100104042c444c41c204e1380100041e02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 60385551 1250 60384301 60384307
    0x703020c0f010203181504110310020409050109060b0c06071d13060302030d0c11040203130204180b0c120412020123010f15050a0f0302040503071202041d0a26 70
    0x301e0803034000e501c00d680d24011116014013101d880c00c0d000a0b0800814041059000d4680b038503035a040261401c04403550f4503018041c1c1115400d0700c2440588010103500354082a9945010148422202c460308941c154180c1080010301c034000001e4860380245042c82c1065030341c0c120055100304200c21074030b056032100f0f6154000c07030703c41c1450704954144c2c1c0c001c40c2994031014040c04142c84039041408018928240711942c00d0462130031741d000d150712910742070368141109046d50000c8c0488100480c40d54510440c10200300500095044696008854110492500076000c0003200341c020300400040002d41c918540c03001c098401c1d00030082c0b030340e901c1820502c000da60302100b011202090041c10010f48004200054086200f940300d10440150741300d540c0742c40090882107a40b000420307049030a040d000c000010713054400b08406001412108480b10b80c00f000b074410007090b10062080c0c80503071003001040c1039410070003040500c0d60705e0b80030b6031485202c001c4896041c00e0300005000007003004404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 60386801 1250 60385551 60385573
    0x70516050312070e1f090306050403030516050901090306020708190809100603030e13060803030702030c07080609032502030109030806210d050f0f040602210301120b0703020c 77
    0x1010300300b41c800c500100011590392843c1100c01a070003440d8551321450414252001e8400c40048500a51003403030296003040c4c136a103840051f00e00a41e81100003a5944040061a011144002424100340d1502900c4c0a000c40300007400c0308a540400740c03605a0009130003042000c45021134440025028041848071555071010b030200303204440d400c9045c0561488071078001003603c10325090f0b9a0641321202501d42035024055108100c640c814202d40c0d030f030040403400000c200081c5208107019401540c3e120300d04c02c841360a2001540c0700721941d610480500c68000c10110955000a54943c0800c3d01d512071401c44160b10183c2c0f4202940551a0680800a0650080c0d1aa12504068410784a00e24441000c00114140c40802240a41100d05403074040c9109100811840d5110401130b0305007600b400c00198598041e07440100903920003489000c904103284c0441581c00344103403c20741035614040b01c0a02c0055a00801401c5260312000980300c540a60705031950801c1c41c0c4202d841280c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 60388051 1250 60386801 60386803
    0xe0a17040e0112021c03020f010615020d091a07030c0803040305030f2a0a020c180105010809070f030303231003110d110603040f02060a1e0c02010f0807051605 70
    0x107000310041010050004036400c140c2a043e809410b50191600351142e50141350310450700003086080301107000303040c3c840380c2d05d01090056102400304c00d840b40760303d0784080d03002070b150580780302d900780a100008000708000c402c122076040582e030b42484000d41c0c034800c5250031100980540b90040c1152008418030040c107600001030b41c810700b69801c00003031a1711042c20340000c01d00c6824600e000c0e44400c4283c0b0824400210240410014600448180b66595000244103200d105d9010b91038180d4800104455a84032041c140c01c1a41e110240801c5414202c0030004002640805018103498030405264202d8400941000e0144100c1d80502401e15944440707026850340f000b901d00009050341c2d500d65142102e4102c50196211280340c0ca0003114000340940f0b40c000a02c2614460300c1443c0200150322102c004080d4109159202600c54100c2075003c01400181c15078003003040b01c030703007002e0005036003001840041036114100035000340e031400e5086441c6c3c07141d0801e21111050b5071851a0070088 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 60389301 1250 60388051 60388057
    0xf12090510030204080303130c0504060801091109040201090b0f040b0a030903020c09010506070204050c07080f030405070f1412070f080a02010908010b010503010b030403020a0203060f010617040210030e0a17 91
    0x104440e40104140c00d020101d00fa07000f0b41c025160903801c10004a060f1880421528038201c1c4a200003038940751780d400001e800c5a280340c3c003405150351941001020014203071417100e03040900b00c607000d14a08060300000c0c412032045c001e0118818002400e407001e24181e00c1518020840030300e0441e81d943c54800010054482110220050b00c208204440540707071000069051302e01c090096401c03d0b00765002c0002808019082c0e80e0790031410040301c0b01080b071401c000d099120501801070340e40e09091502c1450502103600c0003003030100b000800d20a42079030403100b54400508440d0440c140d0352061b07030f441c1409140d5024154842c9c5131440052a01004664121410b000741c84078401a641c4806070307030a0311a08021980051010401030010848a0700a550014060301c1100c0340c0344400e5010034070f0042c0c1a10401d00b2000b06900400405620088000740410b00609021250400f40d02140b00400041e20001c10b15845070901005054204048005c1c01d82003520558440c120401581c0d15038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 60390551 1250 60389301 60389309
    0x51501032a0e0c090a0803040b1b01050103020a0e0402040e0a031101060b0310060c050f0a0803060a12020f1e0d060504030305010812070b0a0f020c061006020c03060a05040f1209 78
    0x11030509012030340c241903200404507102e0004095a6545030f66904946502503801c1300c2d03014040c1399000c5591101080030304007800c1009001030380c402c14100c0c190003c0d0404c5441c203410ba07041400520050b122203000608581101618515070744540c0300107405000349810b2040e20380709000c6100c05156005d1055809048048003c210a603100e00d03584145102c100c030403840c542107c0c40108840c80c8503504c4101c1090044050701c074540308440c10f030f50900382890000c2d03429090220a10480d45132800c103031002040040c188003842181079020661044018991300d1041c018458231401e40103a01e2400b49400d1001003465047e00e00d945040c000800041d50280c0000c0c0c81c1200120746410001050040e00c00621080c0e400d0902907038507580d524130014003000c02d1a4441c261611401341500240104d5144500038020501d004210000d102001c0e5011204642c0300704182c40b17032510045006600700e400d0340f40201d0150f8582c1081c00e041c105909004006074a1038494011081d0b1082c483d000355 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 60391801 1250 60390551 60390593
    0x705040b0c070e0a0b03070e0601020102040f0f0302030c0603041e020f03010204181521060b0405010b0c01050a18081b03190305010b03040c09050612120403030201050c0711090405150103 82
    0x384c0c481400c1001214402c00c021900b50f840490700713105102c0e107150720907401001440054a8252588072609074803130f00c0e9001c00e2203084010010b00452a043c000424901e0003551003d0551425444200803144401c00220f00d414a41182009540b60000c88902c102000b6009555865440070305001c186140344030118806e01d41003803101788002c40080702c002c07560105800d00340c9030034603840b00e055034400740c0040324000ea0380c0509140c0e9031260302070203000704186814580ca0302c88030590360b0f080d03a2000307007405003003854106031951340c00412138801e803505d4000288580b0f45500b0013441d4100c2c010b070032030100f4030b01c808940e24111260b01561340a07040c907a95000d00040e641e65050203040c0c0403ea800030300c01c4120542c2400020300d240c0c810769101100904040450507222500c0e07040035240314004072010302c00202401815024020a50401401050303a440c1060f145c0701c9d0704451100080d000d02c90801c10012400b030020801008081401c00b40300030310b840d40d491500e140f079a500f002582c494 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 60393051 1250 60391801 60391829
    0x150c020c040608070501091823160f120207020a03080412120801080a020f01023a0503150f0310020c07090c051201030b07020f030705030a02060115050f030705040b0c07 74
    0x3e9100c0c00b0504404696040e1600312055042c030310201401140a0030386142c80b5510b003d1409200c000304040084140d601503285010f040480c40888c0c0e0f2a52500030409000714000d0300c03d807160740104c0305000301907402d50058550102d4030004005d03a00c203a10103054940d011034041401d50301c2e006209203003817040000c003250203441c9809070746c810800d101316501074101041c910007508203907007240d0b034101c41481900d00c1001c40c50801244403801803084044442c1810a02d80b041604450121400105003080f9080d40303018079034006861008003c60b80107404041c661441d54a08106449494240030005d548446004441070759618980c41a45109400c0c0031280c0b1031035024008950701c0d04001050004268215140d1603003191000c1d0560f81184202d0400d10f84021081c8003424036a84514051640d502c54842c000f481c0880607041070000c0792640708140782443d040ba0458218107614252140ca039601c0030000c1e20300340150f600c10032889100240b0902448004241c103810b03203221510340c4c2d203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 60394301 1250 60393051 60393059
    0x30c0d0804050601030f0804030b0411100c0c1502160b0a08010906060e040e03090316140105090d0308060a0504020a0e01082208071707051b04020f0f07150c020c0406 73
    0xd100c0c4800e8801400541202e0010300101d0080212401c40c00d0080c8202860702c3e503666240d884034042154242e9a000010716000d00b1803401d144091244040c5280c43d445008a5403a004954100d900c5407a1100011038043c0d440d0900a100082d10038086054100e8190364030658070750369034803202c02b0000094000c800800d04000e2842000d0658410307507100884011910305004c01031540c089031807154841801940b299035001c01440c07904801c4a182c124020703143c600301c0802c1001510250781407260500c154040394580d03000d21802340b40c04d4986510581c44007800729070080a03903000960014000202040c0240c0c1025510400d48000c1c0d131040c003543d441c910800d046035000754228041e414044824804282000c0141404501481e179006c4581d03400161111a6444804100ca00b0f40000c03005010036520641c500c0b0b0040800d071019850504000711140c990f10030003000031040d03100450440305000400111401443c5140d01c100500c00004c04080c2d034540014500030b12540c1000c50202d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 60395551 1250 60394301 60394307
    0x311010e01020412120c080a030609181113140a051e0601020c010509040b120106050306091501060804050307060e0f0106050402071703040201180902030402131802010503060120030c0d 81
    0x182c00c480d805290884014401c4da2000141791100c10300408000c071040b01c104c086040c076002019003c0094500041c818070300703c1c1c4482680c80c002c2608021203209840c80000c2445001785280f039071012101c0c040c002e0010004c29004091403066411240c1221341000003104aa40c0014054400c0b00c0b58220360924a240030840400102d0300130303005822070f24a90320b05501620141002c090001c2c40030a0306001c40010031071428030200c810134243c0d10b40307071300304541d0405110503038002a141c00070f0f000c7c2c080c010b0020480c114045c82a582008007031000207044c40014416940229840030b4103020014541d03203050b40c0c5a06c1160668119460000c00040c03520382842110801940031050300011355250103028016040240160f040c01104003810149020280010b8081d00740c980300140c9a04090041c0140c5040029610303030b81901e0203601c1d50b5013000031801c141090b60b0904e0b10a50344d94402c0c00484005045081d0200348030340ca4401c0201034400480074003060000398003115080c0030110022 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 60396801 1250 60395551 60395557
    0x309062509090218040e0703060e03031e100503150405010b01050a121a0d06091203021204060f1b1d0603010605030a0c031b03020307141c0209040906090311010e0102 73
    0xc40030a000401c1000311580d00d4001c0e003a4031801d444600e0080034602d010609468800c007400d8600e03000351405100700150b03407003545031062120004500b140340442c02407009082420410032500070703000024501034102160000034280180070343e03900035403c0e44002c48a40302502c00316079650074880e03a8a41d86d4428029140541c0c803568992140c510f1100b0004000c003480f01e040600c44078200b001c00b60039203691003603030760142c803401d80003803001c40d907082c0b614140925020b0300081500401c801d8140c0b040740c0c4011500550007200000d11011940a01c0c0020050482201c10544c030300594961400d800054400c90420003c1c03102904e52003000c00c10a0364802401aa40070440620108920100c5684401d4583e2180d0900044503500301c0d5011900000060824001a03000800c01c400f00e80e110b9080380106480405690505800071294001e8500500348032643d44c0c5e000c02d825100d039444c8e0300300700c802d5a00308408005030369582c10b0040036a9540c40c207c480035800c21003d440145014422 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 60398051 1250 60396801 60396871
    0x1701060b07030e0f040e19050a1a04030807020c0607061a09010b090f0402120714040b0f090111150a090303060509010f1a030108070501050c010e01060b130b0408070b130902030906 79
    0xc1d040d02111f41c0d400d20303c0e4055000007039a09108100380702000400e0400800b112504050301184030f46003900c1d0040104000800050464010041500040e2a4601a94400c40c1e01041c0401c1c0c44252000101d002411420a00d9021543d44000501a8101001001ba504058920100d0018410b0500003a4841c00d44c0307998209a00d440003600030351145400000301c204d00358849181236500c0d40b815001d40c104000b440003060f00022505801d60304140055469600c030006060903070510002e01e00c034448010709070710700d850300c83c0b8000c82058465440500503282c01082c0c0d9041e540c40340e40f01e00640d4194010300504446c4034a800307807000000c0b001d4030b0423144058000d000b500d0400b001103405801c02c0b074154107150348031300104014920a008200150080022044d2204042607008032011881c0d0b006400d0b003c0100001c0c0a000d401003154801d90398000700803a99400c0c2850b030b0810000d42c0c2d502c01c4d100340d44040280701103803a0209405000d0120544120004c1c4480c0d2024096580f403091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 60399301 1250 60398051 60398053
    0x10203060a030f020604091a0906010f020d031503050307060c020105010b07080906071103060f090c040c02070504020a02070f0303080718180c030e0a0807140d08011701060b07030e0f040e 82
    0x300400c00550007103c0f091100b4400350081d410a07a0715005481500c7d205041641c80da134603c2c0d0002418182501401d51181091070840d421209010000e5140c0e00e03622040340800d038407161003540f07406000a4000c01107511400f1241d4420031820400001d08070350b4802c8005500304000022012103000594401541020429141481c99400c001c4142c0c00b90000b1901c0780c100094081c059941031009510400d01c0720450365091a1114105042c00000103500341305034a040038a035103181e80082c030402684c0d4107540040e035823010200c085c2d14043d5140d101c01d00c0c0c240d9100723000c010191302088450140302c00b502d136181c0340b40464402440c3c2c020076000c0c0c40c40c100d005ea0030700e8403280080c1e0015010b010300c5040000c1c0442c0001d8000307091505411043c0e41000c8001881c0c01044140809410b98050000241c00441e12484008000c00010320130ba1400d139107102c1c4540720404083d40040000e003002201c00d40e0354800d80c6805040c00e0844d40c5001e10800d4102c14000c01c0741414003900d9007503081c401c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 60400551 1250 60399301 60399319
    0xe010501080703020307060e180c0310050907090306090c0b03041407050402090616030c0507060f0806030105010e1b0c1c0e01180501050c0111030703090b070309030206070c0816111201020306 84
    0x20004c03250300d088c2060040c4e204000054140810f144040107901034844440f40c2c594030718000350b45038900c50a9500640c003603000981000440b80d401103811095031351012001c941d0f50340c58140f504040741c0790303005820f90142c00400d2000700701081007554450000003040c0c90b07003035030380b0300800080b030151002c0c0726003000d010098080c89800c008211002c0c3da00c20700303150103160340c15280c2a180c2a040c0e0424408070701541000303044150848400740c0e101c1300840092140e5030408034010500b070300c050000300c0b070900040c400441c041d80010a64808960000c12076181001e90150b0410420350315181c070011402d01c4e20710b50115403045c0c5168030202c0700300c400505420b00d0440115860f501c014011a510f550350511800e072106800011802a521640d02007030544441c10301002c0403030003038401020b0614000110001a07000306038940e10094500b48045800f005090070030f0b07180b045428200c6e00e18030030701c114001c1003c00004b0086822050340c0d81d400304000002841d00701e20003a00c045038028160 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 60401801 1250 60400551 60400559
    0xf040b1308040303121b030501050102011103091c020a061503020f120c01051e03040b04060b1002070303050a0504032a090b030304090f0e0304060305010510050301120201120617010e010501080703020307 89
    0x2c45082c50300d1170106200146034220320b4550041d40e005800760f80000398842e0010011036909010301e03401e140140c440549142042a0b4255030f075211858034041c052851a10385140600901a08400f80e400820601003d01216007401c645041030004078454400d0091240d00c5081c5a000310402c20311040050070031072226001564140c1150004070385600c01c100d03030441d5141449010b9405684990304140140c1464502202501c288607800c500232001001c11505250380011164110780e0903003002c0e0703a10f4819001c00c843c50700c00c81d003015100c182c6c0045104103c4105002001403c490042c00c1424035845613500026140c3d010b1a003907043c4d205200521000249600800302c081c3d858400060702c4015200c81400c5400603070061021980d500700420490070302d52104404400b261a01c9441c640c10b09041c845118800302d8041d04028814612004505c6a030780810050040700400700210048090507034060008101e2155840d42002d000040c000e00010b00001600d60041c0506045810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 60403051 1250 60401801 60401807
    0x6140708090f0a050d0c090509120703120603060509030702030d03020c0d0e0d0506011205070501030c0f0e03151305070504060302010f110c0406060c0302010c020705010914060c01050f040b1308040303 88
    0x844000e600c0342c03d400000800380e488448008400b03200d20810b1000d03614010200084400044c40700542e03810040071202070001000031110455890300f405d5205103040316009005010b90b41000384040d14190a22034003003030000281c140144200c0c110340c098544c8407421800d90045886880c0640c0c88918410556070040d10403030800b40018040d04044111522903600c0d003802a44001c00c012002c5000205014040c4601c070b020700320030308081c000c020740c42d032004104401c08100c000400100007a16001590240b141912800e83c4109030f86032402c0c00410320542200c0c2d090304861500c14400001002c2c202405400201c3e074050b1580111042c2159054501c0600e14a92005d50300801d00e144441d0741e114410b040180c82d050343d8290022016180190844030201d0091003958003000041003641e91007043c0c00c0964940d000030020024050000c22954019221540e406500746001c00c801c0f4104402c800344a6409411501490340311921030191000e00c03a4001b5005c00b104200520100f40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 60404301 1250 60403051 60403069
    0x6030106030f14070810090204060f05030405010e07180e060c030103060513050a08030117061501120b0303030f0402091003050d0503070917010c0915020304050f03070b130614070809 80
    0xd0050010600b0309500f521040101412541c1ea004681e9803c1481550500e0f40102d030040c0c1031110003186014100b800203002d402101c442d02040020000000d41042070070b40241d02007507500c408132071000d912020452510305440001d5007000780340c4a01c20050b50400500c1c42d008001e1580c2c42d502d5a402c540b10741c006040020704240b0005c5400c500d140c0043c2c400c02c1940b83c0140039074041c680f17950408021540c131486140c1e405500d40c1c4a4000d00514a000005440c102442402c0041d003421b40c0350b00501c090011800c10941c1742c0004403c0003000514140128400c2d8822108454259200502c01000c01c1da68040a4501ea006510320050035000700020b54002e029400c2c03492000e66107076001f840c4600a18201c0b442c90351903110264100750440c001c0c0c0f002e00702503000c070000c107458120001e540c4d004501c10b81d0300c43d06000c060244942c03401e0241d6800351003010542aa20740010f101e49851030050310401000130b070300402100321191843c1c15107042c9070380122514904010402000413810b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 60405551 1250 60404301 60404321
    0x60d0b01090902150c030406030f0c1704051204090f0b0102060106090e0603070f06020f011b050913140106020a03080c070201140a03060b03070c031704020a03080d0902060d020408010f0b0603010603 87
    0x24902070300042c03401d8440c4019040c06000c5000550b6540e050400060513211414076000e492030820340100e1440e90409000048031158441c332404a659904105182103000038108890220008021a60801c144c1100d581c00501010512441e601d04004980c1c98009114020010740c92040511802c690340303403880d810034030007170441c0c0095446480c06039a09080780e2107040503a10042c12210f40580070b0284042d92000a4890102e4104200028140d07125003000c85105035030082e04880031132510352100c040c0c03644182c0c240d02d113584c41d4400659100d0181600b038010941e080002141c40542e10200c501e842e0303060b51030004603502c040500600d908030048001c20315446a8011441e2140c0b28040c41c89421291707100c00b491700e100c0c20047c01d01c5c041080c610103802c680c6010400941c0324499103408030307584030030599554483d00c4c0001c801030260000095102c80d00103044085005a50098030981d1140e0008200c0d5800e5020b5060450351500081900070340c060004200450203030740f11135110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 60406801 1250 60405551 60405559
    0xc0c070305010204090903080604090209070c0519050c01110303010f060c020303070204050a0b1005090d0803041a040c06080603030901020c130908070b0a0b060a0504090507110d0e0405060d0b01090902 88
    0x2980c4a03a1060b00766003194001a0407695108000000e2660000e4059044001074404018200c4c2c40e0700410061240200600107100300510f0480402204000b0098031038841100b2090007452454080d0311041c0726100c0c3c50008920004500c030601010084034126200d6054480c170f240c1c0b4000c4181c1d400310042106036418003051040c0d20240e00c5a02807144584a400302c0041d1031100304081110a07291028002c3c10040c05000360b00c81515a84200c21303416070066050341d200e6940d440d10341c010920f01080404009984402d00c010440e40e1442d460580300e0039110891035656602c107140e600d000c0d00412078010b03800240e4415242c14410010301800b96103000106000d5121303150030882e6401a882280c0b8500b0f00c0e020840d50710402e10400b4107500040726040e143c4070414400600c20f015900406541c0c035500d00115000304e02880c040306000c183c4070255403403d011940050300002041d6046e0740100d00b040001240c07442d02d101c0030180301d03a000e010280664200b8007030000a02c2500c0f4100e800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 60408051 1250 60406801 60406813
    0x705010203070c0510020901120b06040506180117090a0b041e20030604080d0203061f030507030e0c061c0612080414010c02061603120f060509010f0b030c0c 69
    0x1040080c0015445800140c65020200500d8601540340075020707240c20700850b106205001c481c0c0c0e4040e295055000000c0c901203180c1c0407020000741207101e2a8011940310000151140c0020f86100020140745800d80f00c0201c43c05108030124040710084462a105400146203413000803628107d55030000c0c0201c005907030080c01c4c00102c4041103140e10094588a0786e0300505000d0002d4180200d2500d0000c0d0060a194109603403002040c1c0940c401d2201e9494010001940c50b881d101c4444002c40d40d03034410103108421101003d002031005498a03800a41000861400c8074030000755040301d550041c0215240222a41c5910003002c83d50801c540400d0700c0c0d04d07000610601c034281c842c01d01401580384a9070740c1d103040f07102a24201118580c038140100c0704940000360392200242c0d943d4103880740c0d450050061520301140c0b030310310031050500740a2400310700010031300b1175034010f4054803402c0c2e989040a9898910032051820701d4881d0101c018401c0000620b504100c5010b0018550030208441c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 60409301 1250 60408051 60408053
    0x1021201062705490c0f060206060d030c060203070507140726010902060c0616020d120506010c150515060f03040609150504120e040b01020a0204021b011104080c010807170c07 77
    0x20401190700580e042c0b20300c4d02500a00400e081281700403d02c00182e0302500740b40280c069190b03000181000c1c8120940440d140c10305000e14030440456074040b42c02c5517680341210303003d48541c01c2050242c401c11000c03a809115100000350400c161426101954112002000d804091040c03c98140229540303070b03c03205006032581e001510601100001801c40f6150040e000110101c007200074204641c81401d40c021070a400801c0300c5050010414045259582c103001139951b8840c842000b040300658200c05070310001103511140c0509143e2089040c40720b05082003140c2802030182c9101c5440007040801d00080d00383e84841c0c1c5081c03107400b0a8214071a0460144d084a0040f5802d480352520b101e184000f9030b41c001e01078000800201c608020100310131700001e690b8880018000c0c001c3d0790000c1e085241e4005240f0034200400c0e004001d01002a034043c110286810920400c103981c0700e4440c1c002032542c001c030805485a10345603104c940c129020541c0d1a030b808009081c4c0d511150003006814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 60410551 1250 60409301 60409399
    0x903070b040b0f090a2105090907020106060206060130090b040602070b10030515072003040f0501030b090703020d270b07020102030c0d0504020301021201062705 71
    0x380c841c601a030307840c07102c602c1c1802d01e42d404200e0080280340ea40d00110100307030000d03c60403c0c0307440040c50348210b121880c420840554840c0310342d0140e40d5101060200700280141e054000000340d460301e03030075520702c0d440e51001500c034400c00001c00c03251045031581c07100705408010301904c0810011040807520b40c6040d00e40011000701a5010b44480c2e0700012003109004007900301c20b82140702034400d2202245140c80384c54607100d040c1004000e280e0100040760140b403044c0164040742001007502ca21620f0503083c041d07682d40c0980b045a000c4452003400107007641c040e110310361203c0805406981607941d41c801c114000e5000d407000240f1560b0300d50840b680401040d110341c078101002e00c10840c0c0384255040048850718001e00c00421a03004104020089041c04144d808144c404400440c1a449600c002406400703000304002d540d1a1761000041c165900020314024030b20320715607101d0324a00c090320f0400210014010603030044c0e521a403640c108158440390040344c0c1003000c1c003041c950441084103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 60411801 1250 60410551 60410573
    0x120a050d0230180c010f030b0114040b04180506030a1b030606090204050418080a1808060f070f0507050303010315090f05060106120501050a0e0403090306060e011526090307 76
    0x42080408000030055041c888480b184040461240209001144d90000803c0590030000c0b03903080586070024450a640030304021070150105100554031281c413803014000d550450320481c0ca8480d200f06d500408003e8912030b1600410300a00a0300c00341d940c0d600c9507081c01c1c49103002c03000300030742e03030000000498168880c142c00350003200c00160343c40745060304100c1a503246440030b4061125075a05400040c07800703400c40d8444001402d1480c0311110b036100310451040c3c81d0340169124094001000078510060201610a0724542c1703486400101022049031139020703424000704154820001072010810610003010710702901600070945154650302c280c0d075102e4890046940e0f9002e9001841500c2e08100401d41008481000b04002c5d1300d02400959001c0a0303200b02611405500b0202d000c0c14403402002d4041c40e08000d0500020b50b031086807038400c0009104a010180142071030103d124030079000003c0f0140c1c000d81701c1c1100880d401c6803040b1664064a03544c3c040c032040100d100091054414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 60413051 1250 60411801 60411877
    0x30106140c01050a0f060503031c0509011d0d1b1703060409050102160b0606070f1115270103020a02100c110a05030d050604050105010503070804150905060603120a050d02 75
    0x40030a14021641017142030b600d558201903c40c2e0030610000c0c0d0701821641c134003030038406c0440000c80c0980340c421142d401810904403003520358400303007803d540b581000144441d14112942d10610b00c0b182d071002c000981003c040d0021300e6503040c44402d581c40d03504280074580007040108005554891595000e0881c0d001484056184101c1102e00041c4841080501d5000342c1c241c918503d401c86550b1980c20120341184001c0089540700309840c5c041d115804404074141c44a880103a0f200560310040d507030203065843c0c48118040301c0d0080d8240354413070b0082d0742001c622900108110f401c0310103030b400a000f10350741001c10452100c00c0c10070344480030049804101d01a20140d540d4403480c10f42d071001c1da08000c0c0b510340640e00b0200100060390b07102c405c0780e40c04140ca141403582d54a0700c0c40d00d000b00244411440b0b0201d82070204403401e0040215102e4080c1c0402c500b200c01c0705903030304d08010150203241c1c0f5450116105004801101e52150010070301c414580b02031903032500c000080354240c0c150387c60b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 60414301 1250 60413051 60413071
    0x406060509130b0a05070c02040906060915030b0604092012030406050a0311040605070221030f0406030c0c0c0501050c030d0c020d120e060705090402120103050f01060603090503030106140c0105 85
    0x310b46061110044000fa00400c000400b8821481c040d1005801201c41c5440240143d80d110065018812164490005810440300900015001c8001d081c442801da00081c0e44130030751740c0041811761501c1e02c14404d03050362000080294480c1c0c1044020132076260141c464100d24203040d1021410020b0006001a000d01e0702e4a0b51910b8980d07100070201e0322105103107020303c0e03003c000612803071360000103884545504a0b0704141180c242c110f0329a0f040300540c50b0581c036200228901d0003055a8402030b00641da6140d40802c51400103507002c440035000b5440140101c074a10805003c1035104e94018800c0d1026407003102d240000205540c422614500a803800680111801f4444036510942241900c0c0c2c1c1c20030140085039154950644031700d40a8100740900c400081c0d07030000c0e0f44454054038094410b1901502c010b41c0c0d64242591030b51314403010030b01c0c1075103070440115005009102d12480b0a402c440154150303801c0000c155500c106490110340740075014001010303440301c24005c851103005001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 60415551 1250 60414301 60414331
    0xf04050408092d06040509150604080d020307110f150c01150e040c06050703090603020319050a05010e090a0305090f01022b02010c171b091302090a2c0406060509 71
    0x81e03180c02c0261600c100710f511540302000108542d41e00c08150703580214445480c042d28035030b9100040d043e0310503030703002e440c0e24003442a0480d00e01c0c0c6c02001909850303004039440c03031856003c0020080350141034040390798001105c0145642c5000c440d0050045800800c0000504904112140c51185150b5001140c0140c000742040104000c400c2500000c1c07005040160070500b4130b41c2c02518800302c40c0215410190702100060f441101500c1410100441d02020002810588c2209014150074004c1c941d40404207000b00340750100c0041c42520591700340da190381c01c10603001c0c00c05c82c800c50544085411449030003280441c40c110504030854002e52403040030708500e00140d0184c29981c0c101440000c1c05202160681541e0411144903480600300350302d200201c18666140050b03003d01c0c0050f6410881c4901c4400e1644010b600510300c1c0c420460703403a44107a9131038640415041078401e0310126004001200c6140c000045552600248100c1012a031591280046124010116440070302e844100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 60416801 1250 60415551 60415609
    0x612050615180319050d0305060f0a03030314010b0405010905090a0e01060f060315060e0d03031410141905010c0507030f03050a1704110607030e0a1d090303060f0405040809 76
    0x8000003041241216030a0b80c03000f0451700d42c1174844291207034050034103454000054083d80c1b455100040f0300401401c6134000340c0c481c1001002803103080c459600b488540000401c0001141c402c0da8101c03a03050313403000c0790a07040c03e061010040700586461480ca03100c1c141848110400e01583c006040b000014100d06403a00070010150740544260b4424081515020320211f640b26081d80355403d800e0300c8681c030a002e28503045000301302001081603884240000c0c0403109090100603004c8a40d440d080c81401c540260801001c0035404804548a140d04135040080354010001c12039130502801c25182026969210200e521104000440c00a040015410141e03908000740154050a0b8850a807240c43c042e130300c0c0e400480f1040f0007a4403480f0301207014820541300c0c0040511100001d0100b5039095070f0340082980701c4bd03142c43e48030b00e0b0303076003010005401e1207001017030364410580144214200722544041c800140310280c400e482101041140d012207498600f02c00074030000c18100103000d6012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 60418051 1250 60416801 60416803
    0x10022503050a020d03020403021305090c0a080c1305010b091507050a0605060a0914010b18040e07081c020c0f060d050f09011805030304080c0a05061e0106080106120506151803 77
    0x113100720001072510500c070030301c00358845242c141c0861a10490004a607141c402c910b510b40880b10700308036882188090080789940001c1103c0ca20101d0a8a22600000c1405911001d0310000d000762521039500344a12044d81c80c14045150000054501840c5002185e4640c9400c00d10f08060680c1c20030b4540c0c0604ca80c41c1009125000180071488003017040d10006100c81c1c0c542c4006100328600c2c400085480c400455a2800303d11400340c00802c01c02003402e004c0d03480c54032904144200c045c0d80c0904840c1c3d000d200801c0845600d0131a00340c0c040c02850a6080400c070542030901a40c9800030130501210010200e03510405000300c03081c2c00205068540460098295100c0c1110069903200725900c01c000504000b003980c1d00258000603254441c039048003500d15000c50180090725920925003480740310800007a2400d1518414459581d00760b8032144c043c2c4046c4e03000c0c4600030010b501c1c0c0c0c0000b168812036510a64020303c004051508120540800d0800c0390041c210499500d6640d4624000503d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 60419301 1250 60418051 60418063
    0x203071709090c04180216020409061104290703080f100b040b03061905010c0f1104060b0d0f0902060301060c0c05040c030f0501150507020907021203070c110a050310022503050a02 79
    0x18690001394075003107c83c0580601e10900d620000d0180f9158a0114100b004640040c40a1444151a9a111591035000107162aa2443d1103030405034444900719816001404940320b00d03405446490940d100d44140014120004201c6c4410440002d8045650107080d8000c000400005a20b42e44a040400400c4400c10b00c00b8200100200205410402ca0745c12911006030300d9004110401030381214100802590082d0401c50382c8180350410100b445140c48028101c6104071313080401c2140340c8580c0074400c64560b040080e6003c48180700410206208a900b501c080344603025040301260307200085000c1d0780d00c2003809004a03031142103990b1003031240d11649005203641602101b100c00848405051482821400b034081c0c81d050000405d03031402040b80b042c40d0301c081010321b40c0e20b16010000500344280c1000445884c6040151445a407401c2d50b504819150014050550001100c860700025445409007514000000c204135140032005114810018000c0d25095030740c1c4160b0b00c000b4100a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 60420551 1250 60419301 60419339
    0xc0402070309150f090b070302070f0303030603150203090615040f050c04050114031b090a081204050901080f060f0a09051005011d130b0406020d021801030c0201020a0203071709090c04 81
    0x80041c4a40c4c1d880c0d211080d0740843d0303050b0340e8559071081c00307040480c100070441d081074030107d84601d000401c041c0e050780004100d0340258000d80c0780c0510252008103910054507041c00c103600010200710481e40300e01010b907210b00014000514404001110000e4880c00c0f205400400b80c0030800300281e5802124066006400c0e00c00d02d465460030042088104540c40c404840d540000301b00640b464840b603048501608001d401c540701915500c5081c039180d800f9010302401620f54030000541e49000198900b44c1104030b2020308402d80d1411003505610b900100201c945c1070f119151200854400e01510545d8004070034049090740c100650141e241c7c1000192000d800302000c20050300701c549040c072410495015080031204c4d00eaa082000c040c0c012005820003451000401a50042c1030200403a450402a00c0604c004201c16400707070700b01d00071a0382c5800580c00801540d1700141c0203040c80f0305240701d03103000d490800c00c02402082c21030004031241103c9150014090081042810b2000c141d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 60421801 1250 60420551 60420557
    0xf02010605010c080a050c070b0309010b06120601081510020a02030c1c0f0309180c03060501050a1b051509030301030614070c14010f020a02010606031a030607110c040207030915 78
    0x2618100009100f40d140740f4002e0803076800401ca19000c54171400c116640355450b0000c503500d0b151110441d41040c1d1050314091580d61038910700100ca07044c00c0c02612400b12a03081c00019640e02c040040d90605001080800081446800c00d00c003955000045842ca00140d4010484092140b05040c9040300030f90790f40b84102c2c036002030444141800f6100c0e072800c507030003c00d2080a0302c00c0d14041c4c980e00560b401c140900c00411100d00c40c2200b082d4080a0381c140c03142d40030710881c2e0703954006442610403070349004009007035031100240c1d000c054600744d14810320410407a400c9050030360a030404100700341c442c80c6440e0000401002070003142e0280303040c1d26404404400e000c0c1440240948820a410001081c0c600c544201021021080d886065410350042041d565003484e04002402480e0074052080400d26000409085d0719803003001180081024005100544030140c0c1591849202c04890480d44180c110900080e142c600181074040e219455902c64241030220605c21003280520903410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 60423051 1250 60421801 60421811
    0x115090b0c010617030c0705010f050408060103120f03050c0315030c04050a02031801020c0c21060a0e28020103020f0412050a0b0105011b0308060303040801020304050c010206010b190e0f1c02010f0201 88
    0x11b144008204081102d1003400d12081503544507005603500c0c0100c3e446070902d802040000000d200c403241000c0c03800c0040369200f51020021f01026000c0714401d840f10181180184001030b100542400900c1c0328040090031610041703140400102a29011258621a41d4002c4107101754165800881405014448000d5080403180b440041c2e07a00c1e02280a244919031000d460034681030780300d40d061541d030307481d1043e40c2071494412002d03800f0b81101030212420780303d1000703420420355500104080700c03048580080d029400a800440294100c0c98030b001c07120b0000c00000030001480700360745010034410740241c0f24020b80c80c10038040d459416408503040c400888100140072140794180382907276506041590460f10f4081c0800d1540c000e94105030310a62000040c8014010001810020503400340d0845a1580e00c41d86520b48d01d019624990204d240d4905c4904020b5025541c00ea0340c00201514010001608000183c16680b40c089207406007e02d038151601596401207006000c51703018002408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 60424301 1250 60423051 60423067
    0x106031115090d060e01020705010912031e0905010e07080a030815061204030e03030a051e0403030207030602031506040308070c060e13050405030c061006020f060f0115090b0c01061703 81
    0xe01c02d0b0101e5034407401c4610089020130056601c008884207244000f11340399042071070b00d00d00132309401d2400d80d0300740e0381916200035961090250041901c604042e040306c1a40c00b01c10302d0701a22507101d046440d95296491003103190004c01c420b1008207a04c80003020803840d1400c020b401d12a0180103000400f03001c0d130304500300e515507900312014000034002c9448107a4490a0840b410300500712150340c5804009075814070980d004021301185601601142c140242a043c54000c501c140d12006000d83c010801c104003084d625405140c3c002e4107540a000c0504030107000808a502c0340d00119003071740b03012035107000780003140140001500c5039082540403150000e0020f5060680e0900002505440c0c40c00141000300078401d48608031008c3c0b00300d0300c00d414400e20f4480119098041c0710018840d00d0346902c00c1241c00101c6074001d503090100712a699080c418002c0c1580411080030b000d1021b42c050001b03035031404000808680c0a403a000103046414075861040f200a2f901e5021201d42c41482090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 60425551 1250 60424301 60424339
    0x170102030105060414150a05090306010503070e0c0703030605060a0521010b041802070b0c070203100903050d0b01020f160501030b03070302030c040b0a0306060603020703030507020615090703060e0901060311 91
    0x82c02d1781c00b440d101c200d15207868130000e0014140e000c1280503000340401c40340f01f10364001c0c025102804007142a101c190b030b240d02c207040da18021845042c2304014500049007810801e84024056180a4503010800b0340d151408110320f944081c11600003d10002004c02052440c54000c2e002d1411620b061a0194035165040d295802680140020454000441c106503181c5a0444591680c04040a0034900e44145000860303008002c040c0c3c0a40038400c1c12000c1000c80340309099040342e02da2195424200a0f04420008101591119065100741c071642e0030304140821454040301d011304001c1c1c4085042100041c265640000304c507002e035204a505200681d00414126030142090741c3c00284284608002100246a5800500018a041000304001e0b1303254005041013802514148401e0f1038802d402c82c0d403007900711404240030790000c2c18001c45150480e00300c0d03044039403860046415031720713251014403140b41900c0c20905a03640f10000c00070002094a4400c092508841c0030401c2a0940070345 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 60426801 1250 60425551 60425557
    0xe0a030804080f0c0a050703030201060f0b030c0a11100b1002071206050a09021008040201020c0d0209070e060c0d0e0a08071503110706050405010b040b040209130207210917010203010506 82
    0x600d1002d010880c5106140340328142c2d03c0c40b04000044400007a000e08002d82c84060702c0c00300390019400c000001c201e519081104800b00c9a01e542c10031300c4c642c0e441a5040d080c1d0001e034221020030015030440300110900b040300d60a5103105c0d401c0002e418405d14100031200354883c460704150742040c80104040110802004d2105820260200e0f280d507900240c44010024440029800800080d00410340c2e0343c040315561185200fa0200d6107208039040411072079582d00d1500a5000c282000043d54040c410303a243c140c0340c040035001906001c0c020700d0351030501408000f000f00146061a58490514102441c20b0041040c5000390822904042420f00c4140081e2050014907440b0040310001c0d007429400c40d48600c0e001031040200e4205403500902a1603400107881c4110f0a02030390100c1e0349018402c6a40708540108403001d01e13804015600c019401c03810081e680040390118104141814040880349600542c1c0d500701000e040807403440c016030300700c1e81d8030700582c0c814401404561a44011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 60428051 1250 60426801 60426803
    0x1f0509060f040905150f090d090302130e0c060d0e070509070c0f03050f0712030c020c03071e050a0e040314090109120516060810050303130324020315040e0a030804 72
    0x300310303d5200d040071841c0201e401681c4a00ca40310604014410400c407550328001c2c91110280d8407400b446000c202c8902250b4007000e58060f00c4148017a400b030700b40f0790000342c0801000301501c0e001c8803450b000039000d03049010384039000c070b46844040740c0d00d02c410300c0820003070202102e4170141424070460040c45203d01800007030868801d1a486d0b42410700600c16a560304d402a0040c41c0d40d003019250803035580030029080400309007071070342e0b90040300e001142c00549024058004d00c1480c0c50450800100c4081241600404901d200c01160740c0d181c56500e20042e0084450500745400c10b0700d4020b040358074051811540803001e01c4141c40a0380c1c050070700001c660040b4824032003001107080c83c6042151034141000013102d110b01c0003d00301d4102941034880d1900d81b081d06200c0b9030314824140c0300e206180031400b1401c161041807000403c0503000d1155905601c840701c2003800e211041c80101e83c000e8403c3c000301d00d943d48202c1c1d52880c01d40120440782c3d03429000751803508a140d80c09004a040904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 60429301 1250 60428051 60428059
    0xf0b0307121e0201090e0a0f060e1303050d06030203010221010b030114040b0111010504060509160315020f0c03040b1210120303050403111f0606090806010311181f0509060f 76
    0x1d8042d05680c41144018041d107800d248602183c20301210398402070a01c0c101c0c2030020741c02c21400091900318100c541d4450f44071207103091061185640c0807100703948040b00b45000e29642d54400300c00340c3c8003440076141d46049440c1400484404002021442c1030507808102c00c450200300620203e040c44c0d440040d40b500554001c600014000700680c3d903225200740c0c200441d8a800704000c12710039142c015901540d441401d072a1900e80040b00da90f120f66082c040509100c001500303c03400c008542e40184492084075074030f42d08040000203142d0441d8400d6008004034000071582c00c1c07516110340c86880d0040d03030b06090705d13104504d07080d240c151442803000080d047c15a24400142418000c4140303007000d260351026120b00d0071501e401290260341400096000394a4581c0200c2d086008503070072015902c9400044c8082e13031846c0e8500c410b28440202554200151004500003045440c841e280141c0d00d20f075448556402c58000c0b803000032150707030040340720320303501004c0c07000d9910b80304440c80c0e520005513 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 60430551 1250 60429301 60429353
    0x3031202090310180204140c070f0507031406010806070318030503041505090f100b010206040b041b06030203151807030f06030507060203030403080106020c0901050607050c03010f0b030712 83
    0x40064103104440c3d551003502424100c05074400d180d81c070221500d491084804102c1642420310795286920f007104c00400c0322404018002c00304078014a5030394030300d10942c101c4020315203d07074410420f503070903404c160f6140e400311006200c8504140712850f0b12112525040010702280c054001c101c051110000c1d0034003c002000c13605101c2603550807045c10803419001d00407810300c034500a0399280365445c0691640104104802030f03103100e0166450540e0140d0007040c0940342d54450725545d090250080382c09024004907a000e1480c2042c075000104a2901c00585030300d800d14110a442c0141001c451041d11041010300c44c04110b8503035542c1001c00c1d80380c0003404040b2444000024400c1d41c002911900c03611000080f120b50000042d48501c0c4644d4138070425907602e0900366908c0c01c510b03001c00ea1000d4103400500981c24200c000d02002c900840c22a40d410340d070000030a00f111040307426201c1030354680e41c508402e800c08010080c0180224000e21070146015100c100501e000c605406000760440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 60431657 1106 60430551 60430567
    0x402041401080903070605160f05031e131704030c050913080f28020607050903070b0a030605090c070606060309020d020904030219140f0703031202 65
    0x24094441280c20440015100c4450091640c001480203000d060080b400a006103801070b054503c00101c69060454001c1800c0c1b803034040502132080401c14004d0404c0520036aa10121640f03002c02a41d48402e01c08843c0d0034a403000241142c0c0074004819040d40c6248000e00071a8890143c281a0f29610001d00000c85000c440c01c43e42c0c542d40c290f445003c5000c00c0010040340c510500b110340b030580d81c030080c1c8001d41840b2002c1c1c0c05500e400230380042a40c0e01000f5a0f0b41020090074400e050007800c02c00640d8170051401004454200400c0480318240079801210245c200202071150524144948070b1b802d0300701c61016210380b414034500241090003441218411600903024902d00590b5400781b2103140f2010b04210114401c424000b03540c000c00b013130300c035a11501c81c0320445508440101800c1c41c0c02030f154203a490310340054500300000303500014907151038000c04401588603101 = true := by decide +kernel

theorem cover : BRFrame.Cov 60251801 60431657 := by
  have h0 := BRFrame.cov_init 60251801
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 60251801 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 60251801 ≤ n) (h2 : n < 60431657) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
