-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5427
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:50:11.609966+00:00
-- url     : https://prove2.me/submissions/cfca2b6c-58db-48b2-8b7b-7480a76c1f59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 975899280 ≤ n < 976079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 975900530 1250 975899280 975899293
    0xd0308061513030515070801050f06040509040c08010e01110910050c1c020606010f1706030f010204090605120c130906062103081b042310090311060708040b0309 71
    0x20103100700101842c40a04400301101d515605069051030701800f20601803420000810000c40d42c0240b416054a2080310284c8d40b09441c84040384032805140c214940200381102813005018810002200311000f0303000a000130140030301e50300c2c240c0c0e569168428460b0f005200751003c903c1e2031510020014140d02c1d00700d06000511451038030b0862407003401c3c08034080d11079407506125810f20186521410030b0a080c020009000d4004080002d0011038400500340301c00850741c180d4083c40b0b02444d8188200080d510b850302c1c2d144520080410348181481280030119000c01c118001c50303610740101c4003c1400c1c41c8151000c5500c2c020f0884e000c3d08032206550b520010880c142051030701039240903ca4118201c0012918004e42020006085000e41482100b0b00e85035a000000498040d9810209922114410200600304940300c06800550080b4182918450698400c5920040b81e000c0d2441511441d14001400a28460b04801400840003000700f0f1150020035001140c129142c4801c9540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 975901780 1250 975900530 975900559
    0xf12060b120102160c0902030103120c0609060606110c090405031905040b0f09121516030f180c060512180c220b09010803030601110f030a0302040906080c0d030806 72
    0x2242d200130007030119020300d40103a405100100d41000c000d050f00c02411031035941143c6030380c118134202c40494030400020045041c10000c071b0350494111a640700b041482696100c02c0080c083e040c0d98030610000e44039040c0c0d9105146002441140610340080c0510b1030300d6101c140074030940b4284d8581900b07011003000001490f010002c010a5005511300702e6648a400c404100320308100544110704d5aa400000150051f42c00e0301c1c403190b002030420001c0d076030b0b000703010700c040c2c000e03101c00b001d05848507107002d510018070324082c0d40a8000c04c0c8103c0d0030b400e01c00c1d102d460a58840c020305c220703040012405400160307403034100c0007400300307203090901219400316072180010aa103650780000c000307000c2c15011103510754045019a10040100b110050708a6060609080d0740e40030041015042000d414024902a501448016030f04100d48080d40e42d10f10b50864050040d40c400e200384d010041c5844c0000880c40c03408224007041c000010148031541040751001c4404c11400b4140c01c0d44071085829070700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 975903030 1250 975901780 975901783
    0x117150105121510060f0e090a02160605010305010605010f0f2102070b310818040213031113060e0a050a0b0d05163c0b0f0309070f12060b12 62
    0x61290b0f2450303002d0300b000c0307050280041100c140c220206d414004000b4180d4400c0c0ea07004507180e445181c051005071a00c68064040703c50421148000e807903686410008428018190803040940f8400c0e22800a41c502c081011a1060461310140000804401c4d840e031601d900041c102214031604180581040c078a6200c180b1060020342c2c24201c43c03100d42061035480c101c1000844140b1983c015600347c0c0c00c1941d140d04010740b19160484100c41646591100c080d40c455059843c19200408020803694072880c00720407001080700340c14424001100c00c1550443d55020ba10b0a66803c44c00e403500a880700350401c0050b2402400070700030036482d4441d40130303140c69404440c40c240340203c0003031002c0c1c004042c0103000d12441c1e80004010307150605002ea0b003004201a100290200040707480c0c054084944014440c0049410540c0c000c9000900241c000c03c1d10400341d401030314001c01703135450180c1d02d82419800072460301c20f0901c01d00c005030f100008100240d000280000c4041c00a500c0804a542c11a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 975904280 1250 975903030 975903073
    0xb0406021c090c0501050f180a030b09060403030b0906060703050a020c090c0702124c09060c09210212030d050106080903040b0910020c0a080105011715010512 70
    0x341070260340c1d0425001400400000d00d402400213003000d52400d95075440d1100c162046000c038901c11903003100c601e030403502c810000e4001150404030812140c18035516250b04c034042613900340c0c00031341013040c00b15440c0380240074030b030103100007e01507441c1c4030080e07905962582100210074198001c0900200d45c54985a007001c4c4901101501f490b0348404504c108a44403180d210011541d600a600b041031a00b8400032030007000900f2005507510103440841109201c598060004c1c04121005009005c0102c42d04071100f00c1d88685404d00c030581c0781d240c00f11b903180d40750b101c2e801700142c10b9181c14100010003c10010954009844c42c0c080e04e403030148a514550041400d0b00d4140d6a40c0010000f00b42d001c030700b260700400c8510140d460030f450f04c06110a02d008004101344104802810359070158003c0290014001010300320044441d5100b0a0a008003000d22030021b6000f11000e404908860100da00d41e46140030501d594146c0e401c140501409242e1081203400c80c0c0f007403000b040c0700c0180c0350015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 975905530 1250 975904280 975904327
    0x6180e031219050c0a03110705061315020c100b0405071202180303070f02011106190c0e1c02040b1903080c07051302040609050d02060d0c12021309060b03010506070b040602 76
    0xc20f50700c030803201001b82110502c165100e170404061081c08005000170580c41d0300020041c6e41c0d030380e00710010301701000c0c035840503841505280e03c00100b4034442c01000c2045829000c503001c04010030500c5070184400d0368012101000007498a0052080b240c41c681c0c05041c0e0342d5103112254003031481000c00b00e1703d1a401048281c8001c40c544031364004643e13000d120600081000306c060300650410b52072509243c540c82001020349a2601d481c480c0140c496003512403c1ca50050800041809445004419604100c0240d00030703814a41000c80703a00340383ea4103800002c1104000d070015403a5031a580780d980c02104103040c0c0750260000004d4955980c503c070f806e42080f069801030340c440ca00f0a003e02100d4180c1e001c180108414013a41c00581d40b10030a03194880c48000b40441c050050741401c4134000028a83d16407070701e201040300003035000d8440040d0151401007500308103a0751a8042d81c8040d0209128071580000200103140c0020a6a80e02d80e80040c440d074800340c104408100c011490303007000041d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 975906780 1250 975905530 975905551
    0x927081603080a1506020307120e090403051e0306010e0118050402120a0c0c080d05060301110c0102220f03080d02090607060f1a01050412110409050106180e03121905 73
    0x50050040682c0b0a540c206210f208907024a1441d05d070000e92240580d100c090701c10120510b0144180f4000c2c502000040700007001c0c5c0d03460303117014940907015410030b48003207000c5442050301c58980720160084a0295105850300400d0700019801180c3d20000080600b440c660040c03000141c40d01c032400a0000c24031010f403000f10f02d08e042c4400104030784200c4d80043c1000703560000040422400000c0358801021400003061a070b40d85004039000d420109000b0f1918503000841c0780c858031043d8043e080d608040c04042d500d07070014401014419902e0b0080004140012104000089844000302141c402010015084c410031600050321600400d9068940f503449641a0b41d41d801305214080c940c3c030a2000c01d80044c101c0800091135401140038280440b902c0e016040d05014040022032600c01c80140240050441c0d07150070b5010305402e225558040b0060311312121078110900420700c0e5400c2c49001181004038291444003c3d843c064045803402c0d40c880340c059030044107409510300c603510b60b69 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 975908030 1250 975906780 975906797
    0x615020a05100504020d080c01021209031902071a0c150702100e010510052101051e0708130b0c1605151f030b060105090909160927081603 61
    0x2407190428041c84a0508a5480d010400c00181e8a030f80500306502d40041c031640c1c80300c8902c4142402885040386540c5040044010010b880b60004028104600040780c583c080d40340701c00c420790369100e0754086c2c2107030001865902c600c8054014080c08414114900302c0c0c200c42111341c8040052a0705031002c40058000b0a00070800106901654105046000003004940341040805890000701d004041c4203094000701c00c0840300b200498101062a0103000308054113182c0049d00c0c0c507130346201103000b622001c1c000081d0079a01450030244542c038243d110515040641c3e1341c0042e0320800500e14005e520301402003408000184903040b0700c140c0f0480080548100452240407019801001e94204580ca501b00303043c05084022240101d0340e000c00b140d080d6441d51801606d841c020300300c980350400780f64410070032207110004001d82284040d100c280041e5884600c0f0405035050791145a840b5103c0000030508035103482400c001150041c03543e030741060501c0c40400c010240c1b58206400203100603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 975909280 1250 975908030 975908033
    0x803030a0c09080d0e030c1005030a05011217070f080a03050915010b0a21050f0a05071704020d0c05060d020405010305130302070605070309050303040b041418060d02040615020a 78
    0x1d11a00d00d0400560420440309031030165810b42c1c3e1007900000c8020400d2480c032406690b1800c11000d803040c0002040c00324040d8003060000c00c0b44d00100c544440040c100343c00010103004a90b00c40f6081c0d0742101807401c00000e0307030410080507070001004880080104403103d0108440801800d508080c0d07550104450800d652034030302d01f4101150952186150b2001041803828074400c40f01742e142c2c0b50620240c5815161030b04c4071280040c0d0312075100e0a041a0401070f0102c2c0c840314407441a10044c2080013070b61101001180c2c5484e281043d072400202d00004200546410100c1c13840162140f201c4400a81e2154007081954011206010885030045014002983c1500030294010702c52a125007085020b81c9000756903981c0e0f4810031040c080c001074940d003458454200080500720140490341c3d0703650b880051510321350043c421a010003c102d2080426880d20b59410f000c2c07220801d40a524a0f02c4080c100080e41d1203444080f6409982c60b03c1c00115180d42d411808940c143c01e80103042400503a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 975910530 1250 975909280 975909301
    0x405031318050a1b11010b060a0c03120213170a12020133270207030519051215011710060206060111061906030b09100b0a06050d05060f0a080303 64
    0x7910329009107051a044404c0040c404e07560002e40d80e010300d04002d5125886401c0b074018141d0501c075a03001200003490b0410700717420440c802c40030b5100742c0e5031418000b10a41007800301d000341341440d540c407a20302c8010032400c003121880c60780c040c100380107443c562459551100d60500b080d40c41030700940d444004103000d00d20041520300dc0f621651701c0446690400003001e0305080d1540c02001990200300c115412030004800c0820204001120115540d407401e00f005001a00000000d40c1d100c1d8064203c143d95078030490a07100c00146030800c207046501c402c00042c0d20b4013140d4500074100601c08a26084089007100c034140580030302c0c101440c1c01c60416000a04015004200d036040c040780301442d0740c000c50700041c05948404005401c02041e450240100c1c094541d5074400f900618103c4207212030200d0206040c49445a02c40e010000e91541c0800c1c00100b49440c815000441d509000c4840c9820442d0001e99000700010401c07400c1d0a60780001401001e003580107403d140c0d00104c01c10108002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 975911780 1250 975910530 975910541
    0x50906060303071e0609080c01061a04120b15040204030c091b08010905100509090606040c0e030705010c020a080d09030318123005130509130206030405031318 70
    0x401e40156203031424a840b41c005904844480008656201100e60b041c407040360320160410b42d1106032039076070710600344425002c2c0525000c0d02d080700c08401304100000d80c14004850884064501d00c0c6032080440c0c0b28041c00b040001e106689034180561154003540c0d451000304007552182d80360a41c094184004001101c1911304041c100c4a880c60940315559004244d9a04480c80c207032021880b80e464000d00c2841e00915803005030071134241410f1101030307403012075a180b10f618261410044503040140450740c1020402c8040d4054100345c400380b20a52040c60610102800a4603803110107a40744c0d00e4615214000c8260b90000b010082d040c020142d0210703036403405a5580b078070759010324180488100540340c100001040d0115010340091521403490003c00d003d9440030755000005111000a4800e60006600001c1c269848401080515101032228024011410194030f0301c2043e50034440036600140040e10288814002c0700820003200324000d000c1c01c0300c09035082101400307045003010b440c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 975913030 1250 975911780 975911791
    0xa12020409140a020703050f0307090504110903390102011e0c0831020103090204091410022a030d1b081303020c011b0b1510021501050112140a050906 66
    0x4d0041100c1d4010079032206c20340c1c20100c6045161980ca0303d43e14010b40d8040c1e001d0b03018030340003400c0c04101c4c11003500e01c01c040d14403004203070103684600543c210441c6401c100b01c1e2103140d80c0b20040c44843c502d0010fa001203440c07594180000201003200c2199480b4400f02a0013450785075031100305a03015143d00030324a0340c000500031072107034510700c40040c4401d0840101c50321030822400e100541042da80f2a4200200494015008000101040c208182d00056030201d10703541781304510302040c01035000c1c402c840c01c940c0b0011aa41c4180c1c4051484990044110702c8aa403c0c4801e020020100d2014800c1e4103038a140421039104107808042c0c054000130005160a0900c06260b07900f1000c240c002c50031340b132000d00900e031208541c1c0924101800b1141c5204000c0d18101800040009403000000d13403041a000840301d06180400303820049944644880504450110000041003954003c0e91010700c654428203000c1501b0349180030707803546244100c82c841403680d01c45060215000c82804080d8004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 975914280 1250 975913030 975913051
    0x130302010b0d050c060a1b0c06021213140105070c090b0a09140402010f1110090218010f0621110a0905100507021917060f0f10030303020a1202040914 66
    0xb01c2094035155140c820000010f40559000a00002c02500c10b83c0410b804544510603482c80c50380e07a040500341d2003c02d008000c0503210314150145081800019a640e0512034900401e040e030400010300c500c6a14070040c9414403405001c00c000040900c80c0310005441c003188005800c210395801c002640300070307170b01c00c11200d4501000001d120390803850003540203030203081181101104020444801800030710071500e5000306100204858880d802002d031060003140d60900c00300c200c07800030310304000a2064440061011508204e0a8024603000210b44e0071200719805e4441c500d80f446066951441070700000520020f42c41c00c1c025000007121001c1c0c807042d195100c050000000240042c8650310380030380314030480c11452852040c00c24181003d007a0b0702d414211524540c0300c0a80ea28001038825851034042500041c101980141c040d038070808260300c0040c003003807542d00c06600951202c160340d01044103080004100250900081009189000001410060100d200c00d24520060b0030b45404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 975915530 1250 975914280 975914299
    0xd090f110a0b0d0e0c04020c03071b0807050d170307080f0a06030b1524090a0e1603050603160621020c060c0f0d0903090f0506070302250e130302010b 66
    0x8070846050b100281ca0f505000a014419402c5007480d000000f075556600c6400001e001e11003010202c0900041751041040000031000760806241c07080311030040405581c801c613010002484c0c900d011350041400f6a002c1c007564041400d89020391742c81280c20f140454214401c1c0684030309480f0240390301454070030040251130306565520b0f00c1e040000d001c0500541c0e152404054541d50010b407a40143c0250b00384054a040c01d003801364554118110b0b00b44202070038100040c0d10080c403004180324502240300040c1c0e03944002d0b011f1b001824040c082a4051056017080320301c5040d00490381004d0001c0b500c800c4541803028004100c50030100720541e00560040c440e80c1c42c10040014201d406c01d00444c06c294460541008404080c01340d560420045400e0000f60410325801c00c210405a80350514800a02602c03041405818464030388000c00580c88602e41040d01101e0140c0c091051952601c80e5440a0762a102500410410354602c0c03008134182c0c0a0000709502440754450140b01900c4c03d541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 975916780 1250 975915530 975915539
    0xd06080a0c050d12111509060609010605120f0406060806090f0d0314060d05160e0405010606090308030a1a031002030a0b040b0105030a0504171b070603111803030d090f110a 76
    0x404d450440e0143d003d00c100303014000c240400503c411016444010100781b0989460303603000d99250070a40c3d546005d8024140040741c4079100c1c000315080040c00d03008003c2c40e5286c441070120640d2005000345c0d101e41e6110004241c0d66410300002e030003410110020b00c19421007450640c105100c1030f0303141040c11f281500542421001c0c030781d46030f0701c544200d410301c181c0c000300d007842070820542419116400003403d001241c90180040e90034080c034010002084020b03102c1c102514010b1355800003805845051001070f014528a03001f00320146c03c038880300080f800a03240464540b80004140c030754a80e40100801c81c2e0b8000511550f052014200d4003070241d0206c007000600b4500c00070340503c41040c0c6480000d4244809c165600c044102402a22075a450100c1d461100211004031101058080d030f641c000b50fa548203000b00144800c09015280c5402141240c02168114411855400d40400d001c078a02d8550380f48184200e00b80100f01140420039246810b10540000c813003070314071440c4001820700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 975918030 1250 975916780 975916793
    0x60323090a030509130510031403040e01181b0c0b0f010b0406080a0204081203090f01141501090302030a0c05030f15040b0a1803270510140d06080a0c050d 68
    0x107102a405050003680d50100b00c000c20321402c805c1484000183c141024840c4218034607002c0750890b4010f00c80c6c4a0a0008502c1e030588911540c45440b10b05c04407580180300401d04511020311104403040c00003821100082e45156455071558540c010600ca1140034007131101070030f500f40d030160344803c0e03082c1c0d1581000481d0241c0d006e240181401c0010369400035441c07200c1d0754101c0f000b0340441d10481d510143c6507085c0c0380c0e40d5801154280c800b8040e10301c1d07420a0801c14000c040194508840000c80c50f0365004085030049180403031203041107442d02d000005a201440208a40c0340142810740c9954100000c0c145402420071205d4102d0f8001d40920048552955650b508580d01200f81700f066142c281220010309160421072099490f0b40c500b450405802c0715000e00c50900456082c81c0c83c0c00c0f800400001c5086904c581e070b400481c4006004011882074908210505102c0c4c42c080c10300034030481c100c04586154110800340da12100da50014440c4007818800105022100717641915080d98444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 975919280 1250 975918030 975918043
    0x1d0306040b07120902031c0512010e0103060f02030405070b090303040b040e07020706090608150d080a030b0f0102070308041a040f09150906062705030f0129091801110406032309 78
    0x4002c00c015402d0203c0707c0e24458422154105002e82d00800301d5611154010f0400c1800c0c401198013a15000c0700141c3d11045000760b900c00d03034010000d0080f040c513001d9020700c00d500001007a50315020811010600381d88120150000c0c05c4882d070030818501c0c10b440c2c0a46402e6658000400744031200c081041041d5000341e8081d03028030903694091201d0340070004104070070aea111000308216408140307210070380d50551141c149140d0441e52600003100440040e40ca0b00142c2c04003402e16074082109005080901c9145500c40700d1700403040d440c1a035105040503114841e50048048180c559040500600501da0220013420f40540100412450160090300040401c80d9504c1040c038800f0001001c00700c0b10010360020500541900d81c80f03d03a14070a6402083c0c030200d07031003184031502d405134104c000794242c1d0000001c01070300d04102501e031281d1035405007511040d91a011742d00c50060001c50f120071000b034801400c123501c0100b8494040b120101c40321064587d0115130007844410012209800100d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 975920530 1250 975919280 975919303
    0x1103031c0b0913050d0e0d1e200f0603060307090603050303100b2817150a140105160f020a032001030b030304090f090f050705030706020d050a1d0306040b0712090203 73
    0x20606c0c10004e0302c041980e2800081c0d018000502d441c1c2550500c14020805800551042d0f419183c104000003c007501e1100001c0345642000010348c1c0b11140d4240003001350f81103c0001c007241c900664882045041e190682c00848181c0c1011040c0007103252800c50400240007000310103810411000d0400c06403c0c02d1814258181c1c45442c142080d40d801110700c104202c08078181d4580d0307494480c8100c006541d440e800c8034000c64000000040d00207800305040020b40050b0758152401103120001c0a1010408000755000300c20000c14a005a41c2c074803a0800031407044500e201f82c0c40320442d181449400c400906414181003036000c14a95401000721004c3e1600348000040000c14030740000c0040600110041404e52081008014040c0003d2558100c6904400320390f0415122507040341c440c0100410b43d804103070140f090b0300b03502e4001c112003c00000e11200e5010072074a4a00000d2800c10181d40c01e8510710b28185c28402c1c5941e100403041c00701da40390041404031101a0380801d64501c1c12003107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 975921780 1250 975920530 975920537
    0x15021203090d0e04200408190c120c0905040b04060b030a02010915110a2d0b01030f062301030302010c0c0c170f07031101020c0405131103031c0b0913050d 68
    0x34454140e139550b40c0425080b645030304410307081168060b8000700580c00340c05411801d1146044010002c0000e400c0381031285e900c01d070300407542031400a03c200340d880480000c40307441100ca170f0080741c01e0b0318510502c0d2049001c0c1001c1c403418101400c18001326070034000c0d2540285c02400c407003070240c1d800c886a0701c00c070f580700703c0c9212400301d0800c02210a2032000130044a107008069412003444075841850030710300d000002000c0208008801800e00c00f584500091540c549000104080b6001144c2e8014141c0103040201d41c000c8004598071501a21251000100540d240180103041d4240319041d640a507e041200d40807005481f050342c070300708034800c48040c0b4452140c4600f1460091084004c1c040b9410110703901c09480380f03032a4072100103110300c4500512450f0914469032415026660041580d001c1c009110402c0740c6507140c0c080da861034102e403d440100321080c4040550a9030107c201c0d04071074000f66280d9407104008030a200580700c1c2c0628000d12940002103240031a2082c0615150305 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 975923030 1250 975921780 975921797
    0x1080319031512050d0e1c03020a06020403060f0b010f051602040608030c0303151507060b0a0b0c07090b0925020a0203120c1c12090204140115021203090d 68
    0x3500700e0140203112000301000e200c001c80041c10183c0744201c000c81a1003007045d01c0c21700740c0742c1c80115560100c0d184044e5000380181146488194480c4c0c0c0322014074028815070381e0101047d100c00c801d0307030302560080350480d41d10181055681a40e216a00b5090002d00e0440d003100e948800c018424023405419820b800f84800911045680c4e503440400142410010307652500d02100300c42e0307280d820071107070800c3c4808915600303405072070300d0f54001112184a5102e54145a280d0321940002c0166078a0190071144101000c0760f2141d41c9000750010303800c18001042c005050041c841e00781c510b082c440343d02469244c428040d601c424410040c4814091400548031940c2d110310807441c000390042c4c040c1d01409990111a2103260780c5000f49444001c0da400c03a070708481034442c12100074445509000020b441e8907107950030842035820103592140000e0000c14012248980302031000c0e401c0c0c2c0042d2411134944001d046068043c44541605d0340310101403400c61412200d219114807044805004226031039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 975924280 1250 975923030 975923077
    0x105040e03130b130623210a0c090807050f090c07080a08041a0601021e03040512010609051b161e03031e020a020c090403091502060103020a0e010803 66
    0x42007911403889048030350301c0280356100c5000c0d0103548128004d0108244210000c96490b0107424000ca6041c20314060b101e40150342451102650002031800782d04c00c546081000c01c6007040070b00d85000b004410b00014441c1c42c2d084001d0304030031b07040e440840d40390414072040210707580c7d92034046804c4d48141d034aa030351907540300105409485039020007480c0030340118400c48425800301c0454451407140c1800100d8164080d04440303000400c440c4c07203006074002d00346081e0001c1d402d0a0800d002c40254222030909440d00e0004001000108a59940c1d039543e000c00c001c07454040c090b041d00040c5014007083c103060008446c4c8003d1040150262410501e039080d0010449240100e020705001419111010764440c503005001d0003850740d16a10001e83c10714682070320700e004d01c00ca4440100940080007400b030f00d007043c0140d00c10020019002c0c000b003008006110030755100c00040311080c65010f0101981184104070b550f21b0103402c10706611110a0050018a10000440319180d1030b00610722600600c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 975925530 1250 975924280 975924283
    0xf0f05060d020c0a081b010f1802040b04150b0309150403090e040c05060403081201080303090a0605130206041719030c11040b03030d0b0f030607171e1005040c02150105040e 76
    0x2c16600805102000a06c501b114aa8070144101c4070b420900900845016401c05403d41c0c1110f0619031029030030150560051400e0343c443c020542d406040818090702070070f81c0e411880800e03400003000070000000c00041d02d606008d08402256901c602080a0602d51001000d484440c081c40d000804981c0104003400f000c0703180300f00144402000540d4507916840c08004980060319000e9010382d04000208961901005483c4980049002080c96403a561901000740801034040d06c140c8552169150158139003100401c090035440c030221100c0d903640f00300c40785000c98044e1441114821100d03079100082e0301c40c01040ea1a43c00011507004100d031100003070001c2c10350b0740c40150702d4803001488081c5001c8640000c1a1588100c540680300720f00030b403e240d1140c00031604036001448181103030842c05204d8182c990000141000b1070140600180d116900350402d481500000a04240c10005483c0a00454240c00034610184c28518003940c80000c001c081805014819500d400001c920440e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 975926780 1250 975925530 975925543
    0x150c030b030d0203030c2212060c0903111005070807030801050306250807020118121b08091224040b012301030c02030d1a121f0c090314070f0f05060d020c 68
    0x18147d0300503031001c0c1c0d2910f14903e22032442d401218054144a50340464600401142c0d04403600070f54041c00403001c0b030307080140c80c4030101201d04c184032081c0709240100cac05440181040500c40d4484904650504040529081005180045060306c0c0404c3d00c6500d58444480c0ca10482c031030034551315a4503503603020390241115620309a0342c4d0030315543e01018041c96411010320540603443d0000040e80c8070314440d4003504056005000da100801100d54141848102c0820741c260b45400c2c1c0b070841c59492a08841d20300c08581c81c840d013000381002d000501c80500a928010240d19024500724103000d000ca1030b800b92008000c0341450740da2000c206003680207004640445841c03102c20400d044003481b82013601e031044180d99000f155008811b00c080348001800500c809184c1c056a9604180e010042028003051241034080050300c2c0000030024600d0309008020801d090003409425050612483c0108100d07404030507031102c0f0315020446511401c088801c145c0548801680c0c60440d0a0320919150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 975928030 1250 975926780 975926827
    0x10f1b06061a040b0d1542090b090414151c1a0603072c10060203071e12020102030415060501140708130f061205160c050a150c030b030d0203030c 64
    0xc681c1c40b1403e000000e00d40741440140b1407645c91040d240c00301034000c0740c48401407000f40d02040c10704609100c1129000c01512b2032541c020300104121300e10b80c40c8100700001c20b07220160700b1050030b600600b19140c240c0307101c00620700031a14200c40706041c2c0c403102c8004d071404034000304480b004030206010f92414881400a4250341c0500820204c40d660200c050768268984c44042980c05000328960351903542d118011614164019824189540c881e040c0c1e0f5403581c0e14448805072010700840004842c2c030a25150a0500e400058881ca0f25040c800c102841448051841900c0e04200307000a81e00721008400c0c00310854100d94644110b4503106481344648600c16100c090700c0c81002900390601360f0002c00391036640d0b942021081c3c5c00c14658099420a46051400262041100d06101d1041041100550044046850615403a220048400380d140c0b1b24030300d40354403103949098503500360141490076401030740180700e01030602c1c40c0291603000180c0400703a10400020b004c3c1c048000e8081c40c83c1040e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 975929280 1250 975928030 975928049
    0x9010e120705010305011e031529041431020315010512060106020c0424030305130b090f0105030705130620150105010f1b06061a040b0d15 61
    0x600404000958401442c46900c2c0024100700005c211000c048003510300e44c42c00041e80b618102c3c1190b030b4202034202e02c020802c40c07060b658101c0351641c0b621080366080b0010380ca500301420b08000f005000c00d491002502c9501c7d5040700e4144846d403070b901007a800c0d8050050303030205c9514003010b016410044200320042d60501c0f44000510342585050366a80c100e85e401c480c1040d9103080c0310303141900d42c0f40134490f0b400541c200c0300c120480303070410343c0201515420718960007046c0140181d200ea85411540c00980c000791000c64140002210521500050401014054200301d400000034400c034590700010f81c100400800402d2216005105850002e05c0392400d00b9060381d01c454000b0701047c02e4072840705903444828921403c405002c1000005013101d03007030003404c41c0c0c00c1400655a00120040000400208410540d5481c001300c0c1c0c041180341c8200001305801d8a0482510580721441c1d402d180070748030400041040f13010080460b400701e80c000c400810458071140345074003d503400f130740883c146 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 975930530 1250 975929280 975929299
    0x11010f12020c1b010c11241c150302150706060e011737021908010914030c0d0e031014190501060f0c0501020f0708071205030c030103060209010e 64
    0x34404038100c51000807a03200f800282c10707900c0044a5170f0281500183c83c4030b81d2070b8100a80341c1050115200301024540c103200048050582002659020241081e040340141903800c40c030355018040d0b516002c1c001e0b5104008103007160001401d24400341e03040891030500050100802c0b50329000032004040042410f042c66a6a80800d540c030140d0030071504d00d03400340300400060854401d5808100c0154140800d45100000e00c0d424030420440009991010b031031444840500880d030b282d080502041000030850552a1404160050320550890802c2c2c009102119140c000092120807280d11450000b09034180c0402080c288020f09460441050508030103078914109103081034000c4034044085280381d000c50131400f040398000e00548002902c40da14041085108920f007814490080000500d04658010350002c08e511000c4120380e0b00b400414124140110b0341c1e009080554942480d030b103149060300140c0807a11050000a2100e07601090200c1d89074428501d0600303030540a00030144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 975931780 1250 975930530 975930547
    0xd11040e1f0509100612030f050304120c050a050615130911011202390106050f13021b0607080708010e0703021b0607050405190311120a08120f011211010f1202 70
    0x2e0382c0c071b00d010302980410b80c03404050318402c1c0702e002203d110b00d0b080305506a1b406904482122004801303481640c2600c24142000e020482c10304c07000c0d01696410100c1c940b03a42e107100500000c40140e0302440a018036146282011498842500b03030641424a403080301c8560200840d0b00030300641244030010080000c0750282006145092100320400c0700008200e40799a0381a103082c0c44443c060180c0040c16110fa164060030074170943c18134034691000c0075007081c42c460010803e140001c41341d4075090b4058824022803e404c098104c0d001580c0d0b00d082181ca40c1000c0d00002c085102034445800c00d680010b1190b00c5490290088011044203070944905041c003e00082a54103d0b0007414416911201d202c0e200c0140800400b0440f80d02044404207050b04808000040e81880801c5440f4021411104001151003000344280000e01d00c103a4103604140c000804d241e9416000085410710f040a0800810a55941c406420300c09103082c068000c44488101c90072003245207c60040c5001158010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 975933030 1250 975931780 975931799
    0x60f0904210e0109090219140403080c0304051504231f020d0306090b0102100203100302280f03150f110708040e10031e0609020d11040e1f05091006 65
    0x102c4051003640c1d9040c031940c8601058040b84120a00d210481d00f2124a241569002c0c000000340162914400d608055680d02c1d01e140e60781c0440c04901c0103410019060103140b0f045105107040c990240035542c20726080c0303400c03c25007071f08258203008901c0b030401d4182802d0b83c3d04a010724020b80d0000404540f410745e2134001c4d60342d16010611001003403c00a01181010141c8201000850143c2c000c11100025640900c02940080c9c0300c20300700080b00c8008000360b154441c01210400114000b00311081c4106d6002d9091006a000000710b00810041000451260f80c42d151001410200000b0b000d800704c2c043c034004024000002c8200c01001c1b510724184913854010340202e45090081d4862592100058040380040707000041482c60f807120510301c0f0703140082004181e1440340d000010741030010340000300f0314150780100312034031351907003d403202d49043c280a0390100ca90380c00010301614145800f5100154040041c0314030050b55203002515010080040000348107441504020383c544804e01308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 975934280 1250 975933030 975933047
    0x70503040528033e12060c091c120c03090b033d1502010f020910050a020a081c0c0c02030c040923160806040305041701020714030c15060f090421 64
    0x164070903003200301c5482c1017200124500703104403a0544a00d142245400c100080c8032128011188000e0307120341c1181c0082d41c041c1c0c200d42444882e4407484400740c124039004140c0c004541200214071424418840015100c0c00003503080840c40d084504159001ca00207101c584022031248460004100c00207a00f0f0000022565049100d42c0281700042007002004144c0c401c8803211034010945601e4601c55900c40c0e0301601490300d143c4180c4264400580310b809894100460742244800440d4060382456114811040c2a045504041682140e26000a81c0300e500f00d01c10f060140d074441002000300a070543d41d007164040c01000100880210742c0307405030b4580f034000c08003d14400e011400301e048080050043e114960666401e0702d03203420103030400a404140c00c10f0340000c0d9000c0c041d16000a54401055070003084000040d920785200382c0b0290301d003800c860400095041001c050090540340e400c21600b001c94180c0b504407040c0c0f107078a065421002d40401300000d00c0020b07051404082d9100c50b00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 975935530 1250 975934280 975934403
    0x711040c0e041401120212030f0d0b0a080114040201081f0803030708060a0806040303090c05060c25032d120503072604120306080307050304052803 65
    0x80059100c015007032040070f0320a0180d42031412485a1034001494800c030110030111400003076a08005181444450f942c002503070001e0308540b51200c00c501c5080480003c0000c02c5801c00034414003940365040c3c0300070b02000e40064100085070380012a00c8060318042416448101d00c0c1400e070030f6942c0c001c2512504140c03062400500b003100494054604401184241c0f030540000d01419141d5950035802004098400c407034180c0c0241d0005820768941d8054404030701304101404a81140c0117400001c07803012a02c0c000941c014001c00e001085c600340c0402100b40d12109015403840c50b8441d10410400309007001403041c1440c00100710110782c024042c0d030048085443d48918110701c8000c580100200381d0030032000241e84c2c00020b0101d10880001c1080800da8200000c44646403d821801c583c810407080e42c181c1d00c005420843c03404d298180c11500708004d04144070341400403040e6440c69a562001601d900d1010808094002068203038040b0a82c0500c1d0b9005101598007028420860701c015 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 975936780 1250 975935530 975935539
    0xf0906030c0b030903030118140702060712110412020f061c05010b090607110f0a0f030b0a0c1b110904060e01140415090318090b190e0c0711040c0e 65
    0x7070000e91403010300305a9018466000155003160300700030722003104d008202840502c0301d4862259000240183d0b400f1402511360303a0103000c052800c00c0000d403d80200107010042a071078400126841b02084c401e035401d1b1901d5400c019010f0ba200d000083c0c1030305a0304d00c4180d005100240b142c9001031110000e0389d04003444181404160383c0d804a559650003040a00382d04100100480c0c40051400880e000c0b134902c00505040d40b005003400401c040d4140e83d040042c080022042c00e0040c030000a2425a004ca040a0244584529070380700030218260406902c40000454110758104100d00c4109005134038050980455403800d4100b00000d01084080c40d0b041c0c2d40303881c0030114002d02055030a07110b2a00070305006480511801b02070010811032700c042d020000304080d140007841c12540b00c0401414031100115030450030004000a8106003000b1000f031280d0040c0800c80311440a0f900e0764001100c0c45885d8403804541403c411000c12919583c0e031040ca040355003401150001d000000c05041030b076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 975938030 1250 975936780 975936803
    0x1605300d020f22140109050103050c0c010509010b03071e05060307110303041a13171321110a03051203150d150b040603150b0424031b0b160203070f090603 68
    0x1c42c4d41c0c4105040707580b82c900181c9044010f010650203904800e4100000c408454540f00c0202a210b0849d50141d88800c005d9455004400c42c0386410800e4001400d60303003040c1000003011045240080d1400c2c0314140c060380010000550342d50003259075076442c01c81e40f41138954a251528046012408040c403003882c035241c06020441c0c410b542030ba25004240c1c000e0058020300c0c1c0d2400d8405454100251001c10128190004a400e84034a22000301c0700364400400c801c81c00c15031038900a8800028540d50081110311000c1002c00d400040c00c89030102000da40c5580e94545510b45907410240c5070840c0d4000707403200044030410810900c10459501e03c51030030419954040c0030403055401522028040801c11400044a2603190707001c514501030003800080c0318174418080450304460350510104400385c0000410a01141c032090992040d0240d8182983c10300348078103601d460003840340f0303498000d150300d00d140c0440d102000014043d1149041603040960b4840c0c0d48009420b150200302c810745110b2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 975939280 1250 975938030 975938039
    0x30f0106081501030e03090607060b030c220f06051008070206091b0603060a03020405040b04060507080c03370e01061202030a12050f1605300d020f22 66
    0x1c0184038060b400398502c204441c0410070046000e404a1507044000e40401c004c50310040d51408001e1186600c00c0c980414191a660205402c204000ea03985000c0c0182c2409a90003039100254452040d5100d0300000e40d00301055003510042100b03030401a081940c9404403001260041c9103e4400c0d2243e0b801c407101c03036452054403601d8041c000d03c925880d050061403e0b002d407030008095640000c0207455840b18940d2900080c060790b0058500352843c2006805000c14042d0900906906c0485070412440d541048810000c00344002040c0c60356010307544c241d0849480c4600200c60940d03100801204070728401904c94001415450b43c0180690704c0c2240c00140011741d100d856280369002005000002c480d6102c1035242043c80d9118410024100200d02d6041c9000001d000d03e100d8000d5000d402e1021460010725002d50110700100344c41429804803851001c0034031002132a441d44e80d516448403c1c080110011740560f40c4211000c0d03001280e480c030404000d884c03040e4a05045264200c1d03803030b581d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 975940530 1250 975939280 975939287
    0xe07140904181e0b160e04050a0207050d050412020d050102070b0c0c0c12030d020c0f0111120601050327160806090d0f02030306060906070b1003031d2202120705030f0106 75
    0x100c07003000f40758880700b10000b40c2485d0390f100740705001000c90a02d548040060800a01102d004407107a2035582e60100303094062010800040a185030a400e10628081c188020340940c2148154020f2003585405030010820400303406480c541640300c81c1012050518040074070503030308092407084183c481c41004044c43d28080700984005001000079514006103554800081e40c0174581c888581e03c103400180342d4002c0700348207018000000e8983c003601c0b0041e41d03e00850000c0e000c1c20441c1005030901c00e00203640e1b000f445410007062a450f010580240340846241445083c0c88a07814030f0a4005000905140c04903200c0c1c461145602a1480c110320480f0a60300303102c2c0c8892045c0180c0c400d00000e03801d07040c000010190210300500d40340c140382c110b03640d0280164003242e608404100110041081507004016501000102c2c0c41d500540c2c0c4892000c00d01000400845060300c3e4031441c02c49108074000e50440380c5445070f42c9021561454041e10140003640142c52541c9140548000045c81c42d11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 975941780 1250 975940530 975940583
    0x1501030b0603041118090a060609020418092a0815072c040f0e0606061e1602040212041a160c1a070e0112060e0714090418 54
    0x100601c075034255151902c2c3c2070b081081000805030846840c50300040315007002a101840b9006060050481046614040c025541e0703030303444034218900601052042d010324000894158031030900000c2c0f624840d040000092028100c0700d040205190280c074017400e5450a4001500d5264045521801a400d40b0082030740702105c02078002a03c01d5a44003502c4e445060000c00d5041c2c1000b240002e040341c1002030708591f60b150552132042d0b5650701320401104c1c02c0c0040c642c00b070411104c10303003003402c4122000441100d822100900c0c810004402c1d10350b40c0b40303030003020340c807900a40110344a06a51248641c60281914140c0301540e100d80e0081c3e00c06180301002c0d2003100e071030403ca8039940ca042810f48541d00d04610456114003801003c5804484101405118046a540b88441a41401700140906001c0c1d80c0c0080300c607051038000d00c1004589030301503800042e10b20705000800ba1816403010b5a0140c80881c82d803060610003c00c402890350804d0619103400b5079800c22555100000c00c41c134105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 975943030 1250 975941780 975941801
    0x60f09080615100e03010c0e03150118020f19080402011407080a080a0b030a051c02030f040e09160303030b01110c0a090209040204030f0c06090807121211060f150103 73
    0x8842a8200d00d410310806041c440703541d071304040f844205150006400c3d603117142080000950b004280b0281d51804110450907580705400c61059541040d400101e85540c1c0d05801d0766450b000100c0c200c2000340202290717403180124102156034041450024140d05c01590140c0c001a1200ba48180400c101d9003122115580f005c5521700d858200a000d9460400040071480001d03503400081a00f500c00340114840b41d4400d001414000310b0343c100c032a01c03200ba0000d8000442d4414072003a5490050501260150b40e4050314203141c03560f584101d0382c504011010320708a841e8444000208060300b41c0c2010481c040d0981b48c0c081190403100d001683c61a100c184550b21031000d000400000b81d03554000c00c0c600c1000b900c058a09912a03ca0104a40d02d071038003141c0040c580c16041080c0c17940120700318040d00b03100703002e03001d8203144c00784242100001405c05082944500c4c0300b84440c1380a0750284058080d0807040e0389807440c04a40445148000320b070035041000210303a6030300c100d44c4a44208410391 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 975944280 1250 975943030 975943051
    0x12010b0c03090910030f06050a1a010206060f0a0302030d2a0f0303050c16050601030b090616122c07210605040809031c1106040c031202010b0a060f090806 68
    0x90244200010100003138000c10042a500c00040041181d0024580707003607018000c081061304050340360b0300840d14031a815980090543c0c1c000141681d002c06c000c0c0e005181111400b003400f17403500010300045040ea10080d410700c07034405003640709a0040c02344010b002540e4490302e0a04001e8564036120420104014941036007000c0107000a402a030004d500b103001c21540ca400d1140750300c1030110300010201d080d1007035403066004000300001d844107143d00200010280029040c803405070007020400d0307040c540503c1185595000381c403800e603102d151181d0321034590b04929169107607100d211407240b0710045580d002d105008034410b5800404e5003121500c0100802e9000c01c29111400105000350040f0f85101080001c1820b0755030401006000720811040188010705260700941121000fa24070700f00d0350800c10420000c6100c40070390030300f100d4118541c50325500c1624003c900500d104143c0b10f80c040c0c0300b08008101d40303038001313194142181161038801c0c44c15100c02c030315540c0e8403045507144100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 975945530 1250 975944280 975944287
    0x70f1a1603060f06050730020c0a120209061302130906141e010e010e030601090c080115090b28020303091002040e0a0b010909050124080402030c27010b12010b0c03 72
    0x24040401e0000e040d03120b10981d2692011000707071f10135501e00202100d0050b4440c040c00321584c074040c0190f00c014000000611481070195012902c038100090805114800400c0031000102160b0111810301c00c14141314280c140d15803141b40010281070052519202d05480c035500c00d420310b0440c640c0a502c3d103c0c20300c1e0301340c0c00c0c89004550341c00e80c650401e030400400014024081d1401c000060103001e110602041c40050300b680200f49110503848484062803000070091096007008920080d02c811170180e030364603024000504242001c41403040c0401c41c2d14440c00708103690110103103005402c400247c0e1018a2070f80c500100f82c0c01140600442e1a5100c0c3c0810b2900034140d000118000040c10b180389219600c48c0d0840c01c6800c01da000c00d18040c41c05040000440c13081299405090150410281c5400c0074ac01195541b403446190a00506182c0a9800c0b101c2c4440f61342c3d0b0004034010000c400543c1c5810742d0a40e140c200c400d610754828100c000110350b400b48042030303c00d110407906c007c40c01d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 975946780 1250 975945530 975945533
    0x1e0b010914040b09150a020c0c01051602010807170a14071d0f04090507180b150a08100503010204031401150308070318050d050319020111070f1a1603060f060507 71
    0x3c5910001e000303043c25115501e414404401080d43d03035440f5020f040c400607210590615501e0801030078500e0a4101311041007800038403426002580c00c569020301e410b41c216902c084040d118260780014011141e20004200410346115400042c04840300c041207010039125001c0958116078000d07040c2000302501510342d141070814552a25100318001c2001c1001041901d585060001c281c10108100c00a0890080b202459020b0300d80c1c03400d011b80f19810340300805040700da21405511514410081ca2002045c030031901202610040c010040086583d160b6038548000c0210f800000002103508141ea0460ba0300c0e500075200f000c598101810501d0068569000c60341c41c803061080444e20039050201050540791403000c220414403400c01140d56610313900f4480400610818114116814a000a00941d450b84160b80007151f02403160191040c56141c001030310441003488501c0350303d07400201700030610a03041c2d4807030303041c540d840410070b283e1074040358080a0f48600410000c28020400c0300c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 975948030 1250 975946780 975946793
    0x6031707060b19090f0230092413080c160b0403020d031407061d060a0c050a11010b15041a03041205030a1503060e011103090d08070c1e0b01091404 65
    0x140402145c1d00185031400c81c0e404a02614500b150000c0d2211034094108080741740d45403c2604030501800604980200c02485800c0003400001d11544070b0380c2001007100503004680a504207030340702c0455034680002c034240c3c542d0b81803000340c0c4180300b03a480500012201402c10450b401d407a00030781001911085901e099400c4124441d41c40d82500e4100149404103a080c8240d803041341111001800c40306030041c50350b142c56005003150f00a10303d03010751000f1789034010089901c00601ca06050303002c04c040c424254010200c0c5814150091080c100d0451783c0c4030b9680041058a40c1c0c0c40c030316600741c01c60300207070707070341030000301c03402480941c002d0000b00c8541e010300051588550001c0010a820383c102e01001918400340d0f104582d420340b40c409411090303400b80a0070343e000e09504a598254584801c116950340c2c2115110002e0011810100c0c2d8411310405101c1c0045030442d46180e0000b0f6503c0601000d000c0c1c0319400d41e103500d05103001180e610030314000c801e000c1449052282040d2100d0b150b25 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 975949280 1250 975948030 975948041
    0x60c02031c0902181b0a02010f1a030a0b060321131d070309020a150c06051302031c020c09091f0209012106090c0507060c02060106050304080d06031707060b1909 71
    0x30b4443c1c5c481c000c900a10a14440245a03c00a550010503108401c1804500396900402d801d20f04024016500d40307071307032000903e46032003039001010503040d5110341000c07030300304040c1100c030444a40d00301c00c00c508800800001010030f407504020b03a40d099592030548110102c203900f00080304403102c07004500b150740710b600a00082400100801e02c1907560303c0c104e000c446285101000411400c0c01880d00f84039051268030303072255407a035651008021a9000a807985c04c5190a02d00c8105030394a0203280714400c10254503621400340c414001814000e2045907100702c1d0b01d0020225200c02c00c13103e030040090340280c62440406131101e0f020004031140c034950645183d01c96015043d03445a00007169110f42c090885a101592a1190380d801941048c01c00da420440c07200c5c040d580084010030170f00d030b401821258800c3c0c010031107a803254030f6450060090006c42e032002d0084109003000100d1627824000404c80c1c01d10402082103500420028403030f42d00105000481c0e50140300008220800c0c2c0c40c0c022 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 975950530 1250 975949280 975949291
    0xf060105040e09060402090610120e0c0301050708010305100b1f02010e0d2003030f0c07030e03100507021b060a2a080408061f05011407060c02031c090218 68
    0x80c50500da2940030340e10000b6021a00150716074080010302084d8185040324941292082c2e4140b620b5084071000a080c0f80004241d84400955030405964094014002d200c4800c100500038804c9003000b11000703104550a01050f1030a00806956505011661240d100b4101c40a404002c11000700320f15020150b4036540500b0541d503c501c880ba042e80024802020320585d15140c8400030f500301054208212000c054203a01a401002884240c44c1080e4000e6031000726810615a2282d00c0d103402c8450110f510b88583d0148280c1404820000058000700d2283c1200e03421200100b05504030791016202c0c0c0032295801840c1001800505845138102d4003443c0b110a20800c0c481000403000800051000c10a9640c83c0e4041405e00c1965030500c18141c000c1c540101e0218890320032855400d41040f40e00c545814401108080d00609510b20141c0380b8198208030108404185050069102d6119000801094402140c140502c40329840784880300c0784c028081c000e8060641d22030195902c4081c11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 975951780 1250 975950530 975950537
    0xc020918060a0606090b18040e19050c040c020607120e0313080307020f15030126060702150627090109050f0c011713150b0a030c1802030f0f0601 64
    0x601094140811007980682080344001a88600e0b01d44000e0071100f06030010004400100f29600d280101058049946d000440b4006500a00301c149140317006090080102030801c80058082403002c04a00d9610b5000d0540b003c0c40070000c00c4500301e071200320450320301c004155000b08800c02036401ea8821407549445030104ca00d8075012404c13250000180358018829680006002005c40c100200303052050b000a0f1401084035202050303030041c90005004900c1e03030154064402c0d44850001c4200e40c6032455080070780d1510f062103500251100d1426690148404424000c210182482100c401250000c1b400d941c40001400c0501001c401c0d01515284081d0f482e4611840070540521124504400300c01c024072401e01001d00241900c1004440c4101d50700540c803c0001d400b50160002c1034541d441105a0100b605520004000340789541c05540c100250000c0442001100d078001e4040d20b00d034881c00090310740d1024601d0306074801164014070007451400403842e00d142c02c104481c0c00520505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 975953030 1250 975951780 975951811
    0x504180c1211043507051c020a180504170f07022e05041403190f150f0207061a01050403020114090607150f090302030414041812120c0c0209 62
    0x480307070000c00d111518802c1007140f50000c000c003a848501d00001c00001c04000d80517071031801c030005a1184149140c0130300e84480764501c80031950358590040140510118850a20420340b151800900c021501101c1c0d4a18800b0800c0c50381d0500300940d607218140c0f030011854000c150303081c010038140c80502c3e44184441d0f5590b0400c0b1001400b80017410300d40d25a6607984541ca000c82c808001821802000c3c02904480700d030380d16078a0440f480b810040e4010030200e0044040d0701e07001640c1c50410010b10304442c603140034044840360316001002070f28060107040c03020400ca000e15401107c404c04c8000d0129004210410043d4014508002284651182c40d804c203940240450010f46c400382049540c00c1d001c0390300740790a86c414410300400e00c8080c13a08004544082d500a5501d200324020b035841c06107040c0a001d2147c5e51034010700142c403084035900b0301d0001c261500d8400c0f90800040b8001195081004040d0f2075014801c3e0100c00c41107a6481c49a80016000d10442400c0038006844481303140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 975954280 1250 975953030 975953039
    0x90a0506030108151b0d0e030910090f0509130f02011e050307032d02090a05041503050d1b0807082808011d01230a060504180c121104 59
    0x450185000340fa0210261504466003c441d078076245008005020202c12500500380601c04036041c2e40b411051a0800039441a2034040c05140d800742e0b0f5800c0303038082004809082015402210503045450302451220f07410389a004002c9520801c48544000c01c0710721007448045006034001c100300e24018107140442100c1c1d01c1040d0190001c8071480004607100009004900764107100e00703401088201400e4070928003981d0b00c80b1038560721140d907054098021038503c03120340d144100d850041c80300810409c040b0b00c821401400c4c1607042e1000340d03614002c850040804600818086c40c0b1002c03c000c007003184c6002036403044a42c0c3c2150b0415110032909010f50b00840103407115541c21044071b00942641d201b40740720000c01c12070050b04000a4182d0301b00101c4c0c1712155214845054580f800c20111900f11101103180b10303c09103465069201255280001c1d01680000050041d1450510031440310404602d169068469003246140040c91040012502d010075a001e540302e400c02e014001d1516030394 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 975955530 1250 975954280 975954289
    0x18061b0f06092a04060f03081801170f060118030c03120216120303021b06060f1f1103070b010b120603010c210f0204150215010e040210050d0f050415050c0f090a05 72
    0x81d130b04100c40c148c0b00081c40c0d52002c10310800c1c0700d00442c024a041c500540c080c1d0121740c20110090b10304101502c20340b0205416a0184174294a29125256041d0b070f080e81d80c1c10525283d030014031050b61030304110700c0e8003401940b0100e03e421100742418020f5a0182c544028803c0c56440320005804040c3c0c24054000d4a401c940507940380c0300c2d03111004010a00700a410003c001c0b02d1f0070100d510505000000c0050740b03100f64034210480c1e08a0030180c81c00c0a450b82d8150071807007200402004510482d0010461160301d001901c1c03110240e26058903540e0303800c0d09040c2262403820b994000300348958107800090101b1340e60b0b40100c0c03200c00e402052b0b000241c1e182e10241d80054000c19284072038503110440c6a0b078101b2a42403c501d0310908601954580120129042d034040c0c006030007100c2440c0042d2001d8095412200804200f040401804501d0314000c0c0c001c207400da82c12201c093720403d17a040702d00340501a0f0b03809014503600309450030102e01084249039000e40c440a40143e200800000c40c1d0b0359 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 975956780 1250 975955530 975955559
    0x2011b02151e0d0f05090a150e0304090504050d0206132f0a060807022a040507020f0601230d11060d0e07030b100e0c18061b0f06092a0406 61
    0x400d06000c0f030290002c2d0103190a07175000038078285a95224407505004107140140700c00820002d40300000e00280d4003400c950a40c0f0554100c20381c12400d11092104210f00058000d054880b40d600760344060f00c400c2d11216002410340c00240c509002c101507880b440006034101c98000582070720f0200070b0310380c1c600407605803030082c0d200201040a030020846080e80611001481c1140703e1040b1400c4070314543d01030304100713034041caa60141d56900f00180c0214003c02c85e0300d416490b0102101c520b0342e541c440c1c801d2011040001681743c4d806d802414655420f245082c100b600740e100340000c020142c50b4043c01019003145030601085034885804e13601e500810702005026500800c880d035100d1510b900c5010000ba45580004500480042045500712400381074a07070b00360210031264160f01050002504902500c6081310390030301106c400c0740130510700107505100400c0d400c040e01c0181e60780204480c0c5519000c00c1c0c9003840d41102203004951100700c0c07101c035040030004000060103521034005194001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 975958030 1250 975956780 975956797
    0x203221e0618081009031808031c0b0102060708220510050711120d020d020324040e07030809060c12030a060503071a1605011802011b02151e 62
    0x1525044140449607018000c445075000c150b5040644600e401641582c628049030001c40d05940c41e00d0403020548194025050b0500000024502036201c14000740c4030b5101c0b5201c0c11008103000c078045110301d100e000c2e043e01d10b030050300600015558a070045da0034880041c01601034141c2c042030002038081d0305000c0702d0610700480091513070f503c3d851034600803990041d00610602181d00b07903206ca244e4000400708402c89041490036207400c0b000700c012002c1c3c0107952091741c020b400031007044030100d00344620101c0f080c1c40d40c0c804041e4555480900084a15190204085400285d401d0005c1803d4000401d00401c01402040c0b400c022800c13158100040310303030f0745a2070680c0041031044403400e07805200d0107805e08070042d220403803808030250319041858288401243e07001c41c8603410600d0803c1d101c50303040d070444c000b4089200c00102409500c0041101207010a1030000c2a8000114050440001d81d60203401c030550720341c1c0b800d00750140c0d8004800c0941c614820280ba00c1c010700002003d02280c0303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 975959280 1250 975958030 975958079
    0x509010204050909070302060f160804060f180b0301090b0117010909022d01210615140313110a0f030503040906060e01020703060209010e0a0e04140d020322 69
    0xc034101803c011000f44050200b0100e07900685061000d40d6561045807084154074501550b00d64800e4111501d000640d9400762030702e4004180020821740002110150b40000d9941e01c441c518901c0e82118546824022201449020301c010301c1028510f070300004850780305040020017040c0054001075446026048091402e4a680c0100700710b060103040c000ca50b0134241c1403880107040501641c03810008000c8030b18104000c9a410503140440c4c2e0764a9020828000414030209485925480070241303111b03244000111400f030301d48120101c000c240d07402026420030315840b582c02c0380c07a0300c01c40342400d48456520500c0e003800000e104c00203400c0350b07000b1441040a0764640e0f01e003200c6001201e0403603100500b4004000400f6080d0786e404209502500d82c40700005803100705040040300c1032091386049541082d800a03011034284240c502c10380c4143d11451200c280005128400c6032555403245074500564410311100034440c425005800d003035000d100000303030000d558951800010460840b1017410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 975960530 1250 975959280 975959287
    0x40b181801060b030408071101090803070b090618330405070801050709030201021f0204261b0105040608130602192d08040c0b0a0216090902060403060f0f05090102 72
    0x3445003801a94002c0040b890300600b9031030705880c3c1d4450352040007002006011054100c900310303030190031800c024200000449844021074a0720490030001a900b40360240700741000541110a04290031020fa113620015040d80c4c0001e4124a456085c00b404071458444100d1418115a010010f807900c2540100020f0150b503151001a500b101d00184c82241082000c600174000b6036000140c10f5111146543c240d107130074250901c004001e004035000612000400c0481120505070f034a00c2c26000c404200603242c0030701c10002811005610120f810380440d2041c030080152038002d07003130390b42e102141d001e8805c04070001e0f84d5560200d906c442610b0b25049408074002002d560b001140e584108a1100d2002501c3c40c0d03400014241e1a40110040400028100080c100b20b108101140140221100c194492400e81c501a48450b90f11100c00b042c41d1780c0710b00005a8203950b0040e0392220743c0103000d10303141c68195183e0002130004403891030720440d158443e00100b032020b4480d062240e500000016207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 975961780 1250 975960530 975960571
    0x121d0d0903030e040b0a061b12020d020c041b05250c06031b080a0209120f0c120105070905060a031407080907050402030402100e150406020a06060b070f02040b18 71
    0x10409071000c01401203142072020017807a2255071001c4162652030400751040c40420f6540718a07924210402481c86109071500c2c5000e0350000340301012052305030291403a000340f0405210840d52400a080340187c1400c0034132410700e0107480100020a030001100c1420800c04020341000b10040e002154041c46400080204070313410306c0f600450740c8681c4512030025a09010080c141c0130003600c640040c580c0040d0883c046e64030303080d2040c0c8001d80017051741c0300d1400c0c08007034540300c22000703003c80e0054094401c20038031800f040c4907852050001e40c95400c4c0c01401d02e03040c82282c0e0440c01160040c9666211404402c03020380300e0301d038414401507480c155140ba19410340c0707040403401e6001d20301490040c400d1100694034200b511540100518040201c2c0b1040d90003d0400c0240c40305039481100000b6001c104075a010801499040c040d580a20009503101e1101c0d1240c421010084d0001c1300301a2160010300d0036070480c0e4880c1d00000d19009004858465400c440003050b10704003c0201d030f503130381c154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 975963030 1250 975961780 975961787
    0x40504050a0f08120a0905060f19062d060f081e1f050103020f07080711060301031415060f040507030b030106080703050c0108040213090206120405160f06121d0d090303 74
    0xe51250400c0b80600010f0fa140e924203540b1500078000c0030100c2790520000d44c090707050403d162510b285001050002e243d90b80c40d84101005040c168100c804084006100c220703805801c11021504590343d00c003020880c140c0200ea0300c41028044542047c1c84804c2040055040501240a43c52000354507001e110b45406c150304120345684050305050060040d03209001c2c007501500c6100350002c0045a60f46c5552400c00040341552403407550080c0c000c0001b10501941c00051140c0980c100121846840c81e880c1220846008a60a903407104462062001c1340c01c042e0000c5070002200c0c00c011036880b4288000900b556044d4114100c10f5008160402c203020342005502c20f4800282400c0c1300030709194001c0b41110303000301030804185896100800c215154401100c00240f44081da01106081038a08180c441c50f6203c10301b01e0341403820501007028190001c0c9901140c2080d151810035104809511700680314002c000885140d01c00c1501c40040c5003440240c81410240d9503c860450031490080c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 975964280 1250 975963030 975963067
    0x1201081506151e19111c0320031006110c09071121071a010b030403051303021507051606020c1e0603010609240507020f06070f120905010809060105040504050a0f08 72
    0x40110758009005451b00c00015510422940028030b4045015207480c000f90301080c2000c01c05090b009070010420a06030000210701060320004da07a0281c03a649450386869a88603d1520154419000008149000e00640c0a220108a000c0691b0502814400800080c80f00864400f446400c00100103041090b80714240515104bc55441005035043c08100115408010802018410009001100c9080c82009400203541c000e040c41044030202e40520015040310408a80380c0c4103540d040301043c00050810b00503101158020545610300400300a007252400e21040d4005000500312012901c40d5030046000e0011a202c11514900c2c2c00d40e1160303184903d00c010f00080300440c44030300900d90b01104945034560102e50441c8540c0c0c650000a150703100ba90b50003068801c0200d0320408100303250354022083c1c030098841c2026141d40f03200548040d01c0071258049503412440c010b0015140940c080e5400c9405241240d030311a8903a502e8548044c0d40c168141d54000700400c40c2c1424000440c280e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 975965530 1250 975964280 975964307
    0xf061302070b011a07060510090b0409150b060c0f010b100903153b0d05210c0c0a0b0109110c1f111201081506151e19 52
    0x110710700901519142e11000042c0104004030000c2040600114000001c1e0350340d0b10340046042245080140c410b6242e207040d84074402409040c0114101c0900d814483c4465840d0031460075909203140d0f221400040c000020126409107051020501001007000686840799042c1c0c0001021500d4404001c40650010000740c00c1014403841480010015041807401d034500c000081510285103282c0303c246000130441200c0340c10342110340c2c10100c961009251b141b107444001e5800458815008a50030b100b90303465000d90400b00d14206080c40300f01030f2240d40c0002c00404045c2400002020b10341044c1d246c010951b50b49004000500010100c0d11400d112086020801458004c084640c0e944602d181000c030f54075030317003980d80e42e60041301d141d08401c003000083d51034aa9220500030180d44049000e02410510b4801c403941c5526407900d2032007280c081c6100900d040300328400c4030f66200075640101c81c8000181d0b0000305850700e00310700b140035000b2000c1c51f0400762040d415001c40205842481c060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 975966780 1250 975965530 975965569
    0x51801110f010f0207110a0b181f080f01060504060e010e191d0f011518081e01050a020a020712030e0913030e031b010c170c070f08010209220b04050f06 67
    0x102040800702303610458282000244a51108240c1e41000400c0c00c0792071401700c3c0c40c80d1b00c500710785030100d580701c0e200511440e800c54045500ba40c0390407040300c5a0107240540c00102d400e407038058201d503001c0d01401c0300441009140550843c600040c050f01032503554030000e1243e640d00007482c108009941a950700594400000d83d143d0b2500c072019202c010394003200014040300c05103030051440341e21100c1d0f002d1b111040c00c4980050002c2c200712000b600c0650450840c1d4370f088041a40004e19000b101c100360701a60041081c5401c0c00304404d144103007000200c003481201841040da94590f202660701c2991b40c0b20710300b4242d1006081c0941640c45101c08a0710035003000700c0040381c1408d42da803e0401c1071400e11341500042d40d1031500c611040e411007010f0280c1034002c0342081d840d007000a03801c415681021000f0b03944035524410700d400d0703000c0c0206259210448001d002815500d00002460008841102041d01c182c25004a01140d02c2551390101d01020502040ba81d4142180609000c5000c0b40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 975968030 1250 975966780 975966799
    0x16030201021c050d0905030c0604050319210c2c18040b0420060d02040618082e0c0201091112030403020409050c0907080115051801110f010f020711 65
    0x600405034030984607104e4495958808a0041c0141002582e00c42c450801c112036060809041030707540c9400c080d80082c0d54080c819242c40030a0710805074441c144468180c001d55241c2456130a9000d0a01403610004200050b948001034054080303001149040c41c01e4000302c0c1c980349109208003010b000d5601c2220a4100c0103000002d1401c5000c198040c0e08042c03908440d20034844034980005103000459804080400d0454084030075500800498402e501c540103c48271451070002c4010551042518541107000300d5814102c40740346540211558019a1009415a1a4801c00c503500340e0f9443c80180c0d035038116441001104c0180641c1408101c545a20510219818070354901ca0f13400002d01468956407a0fa08010b802c2003500d244205c001d210300518a01200000e114304001d2044511b14451003100c13104040c0a0421500d208000002000220204100540300c3e030043e03600d001241c3c800c6080502c910303002841421600d44540074003581e035200504042d400e1004160a007440707143d100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 975969280 1250 975968030 975968083
    0x40501090b0315040c0516150b0f090c070203070e0112060c0315033c0317040b0a0903110d0203040503251e050604030b010e0a05060913020d051603020102 68
    0xf00852a4403c1c000c58021440c02603144089a13140601c4c140d40040b0038030891150104241304102400b11509204104002c008410070400907062400d45d15811089881c0450384213050400103000a500103001c555419695141101107000260b12900600107100d21036410096140188071444129140601902100307080d88024440315203c0207000c110564024045040c005103030200f5150b4201500e545140d895200c5941072400034422400107040e000680820440c1c002850701480d001807a9585684d20229140004c08004e041607052000caa458121007041c10440f51107543ca4640c003850b1a903191000b41450701103025061a40040301381e00c140f00c0c8022029203c0111881007000d0b4a03048069540c0c1d124490311500a182c21440008000c81801500190a4125180150424110340d140040d40003120710036a00070364085084004102d107008080c0b07801d104140020600b805c0d50b0b07503950740c503403400e81000c105c0c420896041c4410000e41d030301800b03136485184407a02e03a41d0501845 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 975970530 1250 975969280 975969301
    0x617090d0225180603050f0d122705240112060c1e021507110604150e0703210807020705090a060308030f0114120c10020a050d05040501090b03 63
    0x12180031040018a0280b004111041c0d100460061040c109070b28818050100080701034451070000796400d00c1002e10b440e9a18000107a0b89882c180560354100b881003000364108050704213402c1d052007550800e11844a200f07160f0350600e81c410310910080000094101c0100d00001c00114881c07100c515038401003000980300403018904951060000514030b40b690403d0b03588400c0300c2c1c0350b40006d40108840d01151078001440e120b0100351a002208296950101110310340748810b1841500c4c0c00590101d130004440000c104070f502021600461283c0d04041c0c0b1914105031607000381c545010780500d4041445480303001030301c0c80446203820040c03480c1400b0080d56078070ba1481018014034000c5d0011741080781e56401140511751010007260b490401e241c284441c5e50081c011000800c1103a070781902c2c0c03484e010004500752610b08001c0c0002188803010021700c50320b007107140030071f46c042c5c0f0318604001b071000d1001c4880b42c081510350380d4445040c800014004149604484003004c41013080c052040c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 975971780 1250 975970530 975970543
    0x120a200a0516030201090b040b010305061302032a0d1a090303040209040b06030a02060406030f0515010c0803041403040602280c05060307210c030b0901050603040f05070b040617090d02 81
    0x4482c50704501000a1400f203005001a4401401c40000b141c2840f040008110540c3d0480c1c1c028012200c0d184c46064009030301b006942ca0095060707008030b4080d40c00c0b41140307100008000140b0f2003030301c001100d00081005a00c4440003203d091002e1504d02d20481c0c21058015005a590001503045140540c049001301c000500090502c0403a1303800200c09a41c2082488821540507095984540d50f5200180140000ea003800041e035041200082c41c0034002c029113403506505a4500c400390500f500d454000e42c0c0701400585908081d03544c0031540c40010001803000300056401000c1e0034441030082800c443d4504149078030b500500107801e01044c2c0c0e1a03107a0081e00c0c0212176059882d26031010603280c11350080340c0400d8054029140c841d81c281c0c1607204402c0041680c4041c01402501410403040840902800b07a2208041c8007080110743c01c0c0c1d0050010038450000c4441d41910f03120f01c40500c1d04140c0c400d000007000f58502194960a00c9601900301c00c9410051104080d48000a901e926 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 975973030 1250 975971780 975971797
    0x102070905010e31080706050f16030b0a030f080703080c030c0a2006010806010f05030f33150a080c0a0308160b0c19090b0d0c0302120a200a05 63
    0x30190703040f56003628004100c0d4480c0705814644558244154030300003801b07800505003950600c1c5804006031489a030810a98442c9407030996810b40e6060801e0184d005141021246801410008000c800142c4204140134060300607001c0d03c0d220201860010520031004000801d13800050060185005050b010341d00200f6003030038020078699403200008000d10017030900e038140348103220000138541804141c050584040103034400f80a5100c1c0f080c103a8980c182d0941c601c07140c0c88074080804c124240300040c030558540b501d05181060180c4cc16202c460000c2c2c40502c00742c203c1d02c42c4013803540380a00c0041d00429101c1d000c1d10120201d0b50001e00700903400c1c130000e020b80c0c0d400030700e881141d444460440d604551120410455040c0207030001c07840d400035102d584040b00c48809030884280910343c1c11048440c074100b143c1c40c21100700601400340c0440c42c40d813402c3c9030b0280044929200b051000c1c0c0d104029805001500000300c1e01035607040031480e5013441d4884800c01180b20746c164828100e9a640c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 975974280 1250 975973030 975973051
    0x16121106040f1a070b04060b0909010e0601150912050102030f1003020609090a06080a06020702130b1f030603060f0c02070b0301060203090d05190302060906010f060813060f0608010b0102070905010e 87
    0x5044445101d24601c140c810040c000017060741040100240f035072144d004580c0503540e81e949643d0340030600e42221243d110584003540010010440b664a61101121101c03491420a010681c0d65540741c003001701600c011201c2d030350040100615082044401e5621440c2505181451480c54000c45e805210343d270341242c0140c10f07540000f61640d21580001c40109000812545d65108504001001390400c90b8200d205003200d050141e2021458054617680030001460344100b01d2140d050714683c960041c62080902d9110300340003002c05e032213200d2524502070505011440780c0b480340d802400c166003500080c480000500c0103101069002058130107401c0c013a01e00c461540400d0810038940a002c41042c450303040350b05829410950301090840c0680000c008860352640c8907030346001c030000c02d801603500003201c000015110100010900c0d075681c0c020b940006034001d03528283d00c00d1726a50b410128040c4e440c0d40c805050355038104001700040a112408003d1541410180108580050801c0c6140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975975530 1250 975974280 975974309
    0x5070303020c07080d0f08010b03160f12021216030c09060f18080102120903030105090f070e04050106020c180c030403050906040b07063602090916121106040f 70
    0x10580104040743c0501035000c204d6401713a0034030100030041c2280c018800009810b480002400c40703c0384080e0b174041c110281202d03071405022002194003d0074015644100a032004a18018002600c0200b07030b940359101003014289040c1e40740003c0c1c0d41c0ba00360f40380201440c2045420007144d1211040c000e403502c034648032800c44410402100c00154071003215840800408000400d04015402030110600010b2111800c0d5a201001912030000340b04141e0000110700002d003071681c600903883e5115000381000c008040000c80800c04a0303000741c00141c00b507440018000d02524010080c1030058840c64184070b164545451198000e0201603c020140400490503078499614413064502425032102c149443e00101c1c24041d020705841c40c1c061050140b1684560204001000d0108110942030340c209030080d030540c24007415550041085902d4082c0f690490040c0322207a1a0200520100c41442d2031174025081c100241c8050320006c0f84910010081000220306030582c9000300c40e08945039403130 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 975976780 1250 975975530 975975547
    0x17070911040816050301150f1203051204050607031109150904021c09030f1d0d0602040f090212010f0e190204090c030e0c0a260703140703050f030a0507030302 70
    0xd03406550001007103801001d08919065003400184021210114001e00000404a0b03e140302c0d00c0c480e0041140d81d0252a0003440000d040710001a07446100b450420310700080c004a9100040c010b690803111504103009210041e9031600070410140c42e0080c18514240b00300c000203800c0c462130305958440503400300d4440c01c0c40c0e40b0b07581030301c921596221010041d010590401001400100750480c0890046001204210310810400710307a07060103920090f016030400e0401558403082c1204440554007080301084c180551101000200b8441e034000d038941043d4103da16100c5c01c16007124101c803202000030400c207160001c41a401c8004110b22074009007014004070003911030b981000908c40c0c10301c2c8901c40d417985d0542c800c1b82200300d50416944504001030411030101418410803e103c541c44070070a5569504401100030036000d1400c4680055682d900c82032806018140307400707581c000d54410010f000040c070101d82c00c2c01000c40698500100f0900291080c080c40700c2c017804041c0d000ca0100d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 975978030 1250 975976780 975976811
    0x1d0402132705101505040b040e090a06240503010b2101091208010602100b03030901030f090f0b0910061a07110d0507080d0e030c060310030b0f10170709 67
    0x36151074464800b4400d929260000580020a41c0b0071003011003210480594554455025070707043e10940b01c1110b14103480d21003035036000900030b001002c143c0a0000240000780d1544202c0c040b15002c503603041017040d45070340d51a0000c3c000c4d03401503000782d040680c030b0002130b99480c8030502240c1d004050440c9021500030b64030f004000103131008040041c000205800c1d903412250701c604880d00c03a421545490f6070f14580c0400d86214008250705580309012051281d80240c00c20010790009840015a51086807075948100b1543c110546210a9031010f2001d00c54003403041100c141b030f4030702c4288142c610302030700c2e114131854403042d142340c80074085141000c1265000d611039802600400c039220103800d5003801c94542c1990b1140e00b07902d00c02c50042c242d07642e002e01c80b0340d840c000006003d030205180d0002800b10740c0d84000d2540f09440b04c0c081000c00003030342d9616868040c290b4902c80d8141c07032030511540c0115010745e80000c103600c100892180e201220000d5514152403022102244510f01181c803030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 975979280 1250 975978030 975978089
    0x11d010c14010f021803010b090c0d1104090911030303040503030c090d0b15040b030109030c0b070302040f0f030b130b0411040e1b030c0607020a03030305090c04020a1d040213 77
    0x81c01c10750900e215031201c500690060075035410003550700392103054030004050803602402c82c00c5401a0a490008008a100c50040d1080c81142c2001182c012244095801d40c0d83c010b420006806945080100070300030351040e10301481c40f059004524600b401d0304c80b10750741d00000704054040c1e1030004100304244c4952022540c01b580c8813442c80414249041d40110801c0c0100104e4019481d1400d030074a285414007500c0ca45503095141c0c02c0762040b55840c0c15502500040034902415020000000c01c2071010210200a21020300b03144807450442c6003403035540201800364024981d106a2034400305140c542d41a4010b9808181200c002e4600c00c01b08001d0501e4a04414480c0242c5c0202c070180107a20300094540c01c411070642341c20603040410012680108000650041c1c0090024400030307000f544401d800074490400c5502d0f544140300010140d82c0040c22150000d01c5000380c5c4071050050398880b0000c004120f50560808001d42c0c5c0c213102040c8a4810840b94a010300302804240c8048140d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 975980530 1250 975979280 975979313
    0x9080f030322050c060a030c080c030c04030818120a14030a0504050d1511120108030403050d0f09120f030f0201052215060b0a091202031b03030d0e1b011d010c 70
    0x42c2074548058002c041e0023440c8002685000c074840b2030026601490540c222403060030003980084c1001c2c11a1078284040d040303800d035020240c4c040d03100c4101c90b5a84074104000421208001e1111840034070300802d4186c442114565903030300c00d22092072015040f03030585043d41c00503140c11403082c100c0c0c00c0490700c40300078080d080c140743e10340400c141c0c91074a10402042501c8031103d5000b0180d99496160341d803441144400391aa0300309900a2a41c68843c01100c80201001d1602500217a02e8203445c5075111110402102c0640800c0750300020180c00541000050a013030000300010f00d030824151102c440d141e00c804030102c21100c160b01c1049484501c20396504160303e801c21030306403151a60141c962000309904007181c070a4800003407131600169103e82044e4082c000d40746141c19040f09452420700762400c25407602003813040c20382400c0700d07100d8145601ca03c40001c1025040080c490307000c240030f00b00325a040010030105210f0b500c20f100c01130403900b8020310380604212058246240048180c221 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 975981780 1250 975980530 975980539
    0x23160501052a06101d0103030e033a0c0f0b0c041208070c0f06090b0906070516150207030f120e1810060318062a09080f030322050c 58
    0xc407000c800310024402d4801e42c070700d0004d103800c0c580322040c0c0707105001007921103502c510b030304401400081c0c42000c2c0c1850800000d01194800d040c055141d4041c550303484525503007003400e0200c0b02c50130000c6460f1210141502c0c2082034008440b520740304546923049202518404909001ca482034420303004880050050341c070385c08081c82d95860b019159500c450801d4800c5ca1aa40b0041240800b00040508882d0192a03020016140090001c0340741c20050b10305174807001c01e2002001007281804898103554a01014012203420840ca04146130011001003045620406042c80042c6802422840c143c1e0000e0301d0b41c0204102d4401159031a825519940d00008909030200c110000d0341c11140c021111250f94036481511b40c00700310119448141d4100013654040402070206803280c3c48440c0c0385001d10302d00740e100000b41158000c2801d00403c040e002a114000421007801e050044410340c12401020303616504000304d040424010444070b196502195601c1c801c104001002110000d060240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 975983030 1250 975981780 975981847
    0x4140a08040801061e120302030f160212060601020d0c05190b040b0c130506030604200403020901121a220b01051c0312180803042316050105 62
    0x601160300350818452520309608050020070101c103076105504118010303d40c080d40491404010b880c01401341c000503420350004002c0346050591540c000c101310022401d080341144000d20500c0b180680d52100900c094121105205041c1ea0204509040c01202c1c036101c50300b0062428520f0405800c03030000251080481e0b202c100f0801c3e01c2d0001c911490090b00c008060356510448551148242651807050b02c080110a22207440c0400203160003100280c000074480d24804903e054082841c6034500300208045001c02c00c600e0030011050251180d8008040e0404040d910b50184543d4011340c1001c035001500010321055032031030408101200141500107140c0e550a085125030003e01445001d04040e15161007085030b1040307002c2e056a41541e0705107441107046c107494000d1001840100b0340e0030301150003d0115115101540c0501e0003040c103a0b41c1034082d10600d50a001c40d00c50340c0160f40c0c105180c11400c90880081c0070003203610030300b01255100325404010702414079004200008207442e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 975984280 1250 975983030 975983033
    0x708090618010f0e09060108190603050f010f09021503130f0b06010e06030609071d030109050606010f080114150c030304060b010f03090c05040c140408010c08101202010804140a 78
    0xc2040d0111030302a25400d00700e082e440c0045680102c0203184c50742010f0740d18041032507548600013056000c203020900a44018180c0c02e95015140107920503035081e1f0003001c002007059428817a103224100900010460040c00340c1c0031501c90388600c0101c2d11030010102c0010f00d0542001040301410f584240034074004050b0345003521080b60207031074690000f05480088201420018211380c01184014079400013540c071440d084501c118101010302541e84c11b0b246c2d00c0020b80f400d0040c0c54070790f489a0003801083c60010001091042455450410444124010000310703510a9403440307514010786c0c4c16000fa441900e5491120301c039105100256100000800050080e25840450008400d99900c4a124003800c011000c3e03881884004d459600c041c2010422841d05502c140d0b2800304a040c9098070071844a0444c04a4010b0b41c00f541440c1d4644040d5007296501c004440d81c8031400705170364036009007000c15000070000341d8480203050010140c042000e008a0054120045000c00700b03d8140f22541e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 975985530 1250 975984280 975984307
    0x31103010e0a080d230402090405070b0c031c02131202010c0f1202060c0a0e01180f03140606010c031e0c050607020a1b08060403210f1b1d040207080906 67
    0x40780062089182111760900100440700c03101903400051404c1d032071600d407034003008114803010340111002d206031040042c0100c0c110300078110310030405010f50f4482c00701c4110380a83c000b003885005017180c0704000300c81e00d44490850001c1661aa0050310409600e00d10041c2c0754071909850113440300460541e00420414009800388404410741d0940781c8584460002e848140038a21042001c503401c44404641540b10300700050207410045034003801c1c1d42d594418510a5112500305944d45440d0080d54803143c03404100c00394003e0000e280030b100b865015140186401200c9401d01c0000d000282c84900062203814030503541d03504081515081e00705994040d54802d14080100d9065601d25140e1114516405103107048440907009840c0a81e26a80c0031541030071052608500070074050125410b0311042d12804240706203a82c0009044440050758048440c050742c103030340030801d8030f01e01d40d11000010354140010000030b4601680301c1c0b0243c68074040f54050402516006600400c840844010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 975986780 1250 975985530 975985537
    0x1b07151107110406210302010906110408061b0a0e01030e010608010e070b040f060806060c06010801140c03071d030133080d2f0115060306080313031103010e0a08 71
    0x208529001010503a00c05100541d02d052256003010120b480d07800302e17480402841204100d11900c00051442a9a07643e5011a14a40401600210b0200d4240700301c2c00d007048942d410191883e484e502200244c0035041042c841c280a00c0d0030085448443ca030964065002142c0d5600d85500038402140c860004a00820340811a5400c0c0d1141035000226a400a02110144d07107005400000c02401c000040d00c0c3d06201601040c0c0089080001a0000c0420701c90617002e0300150b0000304114081c0c600c01000e0340c0c0081c0048040307400c02c005004000c0d401404082c031070101000c50001700c0c12000700003030042aa43c007403402c80102c8404031203c0c007040b03020341103142c2c4044250405205d0f25030b441d0b65038640c1000032120100d5001c07070110301340d03801400d5030b540e01280a0311140130810b41c00741c0c2c1500391060310082c1d045d500c100440034002d040c0c240c0200130140c10703036000640c1080328000038141070207201d1001401c41400c03040b4803e1240c40030340011550151010881c0d01945061030140c101d40d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 975988030 1250 975986780 975986783
    0x9060a02090604091a130b13050f1501120e0c1002191502070804081c050901020d141918050303040b0a08100e010909030905091b07151107 61
    0x105000208015254400d0368079001c005804107003840d081030880c400800305040c0351004183c2c00c2411441550f1040301c0209a850b0b42080031420140b954140400c424240e06c0c102030b01403c2c441000300350101901d1403540f085280021a00114100005846040b00b800c28440505d040c85507500c1024030000c0e0300720741142e042d1000c0086980c044d10803070300c41d000c0301c0200707555800910a090102e4031140c03180358007600c10360005140c89020b6481c2485a4096840f0a0540d00641c0700c040000148035034000804806d403c149103003040c6100001c0d203400c480f2004009010b901c25080c4083e480c2c80054605100300c0018041d01c8402104c400340c403800781d41130001c00180d2b80301808221400d01105480c00c650101c1c48503400c002002105842c1907200402040c1d034001d040100240405000341064000c01c0e04600c00a1103030355505008004e505c0c0e580020340108002c0040c041e030081d0b124031440840403551202500c602d0030b41b410303a11500030241102901400c00015040c1592100000c2442a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 975989280 1250 975988030 975988033
    0xc0504031709090f070e0303040f080c0a0f0504020a141204020918030a030504050312010303080a0f09050a030e190602151f051021060312020604080f07140a0b09 71
    0x9402148030501c510382c022900481ca14011500b46038010000d15044001400c0c04818103490b0707404240b8540141d80725100f003016a1a04100202c02805410350310744058500c0c0c280743d400c0001c542420011485420f020320b60010310785005500c9010b0f00100300c13025454240c1c0c0c031403003a44055003005080d42c060744540c10a102041d0740207101603002003110f2850010350f0603c051010140c000341402007050300c50340420010035088011410019020314866220010301d4200082c000c411120248880d00c007140c80c01e03100d1004503600141d406041d59240c6040e60003884904042050710703280c20400c00010000c0708020400c41e4000c5031a00201014003201c01055551240d0b01343c000d45004603024444030088404e200a040182e052415076107541000d82d413150815042810441d102911081030302d948071000c1c01001002005007001116620080c8101c2c2056207401c5802d2040021280403c140001c00c00d040240c9100c070481d0b1610791000365118054181010840910200c4000585 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 975990530 1250 975989280 975989303
    0x7031d010c2006160905040227030c0a03110a080a0b01060201110403021804081c0e0705060301050a090f150e0703060801051e0910050717070e06090f040f0c050403 72
    0x5165103891151490212801002e00e6241c000e000340c0b2103104c03014000e08105039030401064944450004280240c40540040300d40822207008045c1d02d21148140f911940210846421640c2c8420840e4150398101141000320041140040c4421a0f81e40c480f414a004013240785040c00390091001d0f040b04c1041d0024002000004d084044c2407090340002980b111000f40b1a05161305050080c0340e0082c86030882610302505650008074503141c0c540c800008507140d40820355074207000d01101c0001c000c19120303d42103504040008a55180342d0250403201d80c1d542030807030305440311a003205042040c4201e21101160711001c403850340700c80884007040441e003440c4c0001a2820140704141c4101c140084128040520b03e00c50000d200c00030300052420f01c5981265514030b1082d10a29006403190f440b07142203907002d01151000390000a00c404c0c140000c0c00501c2d00d890715800120380d50007008807015900c03c5e5030000000c00078500b41351220010fa103412003002c64650020000d109580c080c0b0710780c0d0703803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 975991780 1250 975990530 975990557
    0x4180503270a0b0d151e1523040b030a020406110d0906120e010509030702010809070b031918030302040503070e010b09042a05030f0f041a07031d010c 66
    0x36201c64509940b40c1000c903503a410000c80009501500900b0059100410310301019411001c5016280c3c0112041c0b10564803540180d400d81c00c1c0700f00041009200c00130307000b65025409415418040415040c1c04006041d200c18040d00030111009401700103521030303c81c1005500c0900035000750040e000880c0c404021100e042c100096034082d14400742c1d4600c41000c0c104081118110503640d0300d44045030f01d4250613003103e0400c0c02507501c102d20180085407101214000145105006421400c01d81c01c00320007031001800c0b050490750301922551078826800c8966030243e00800c80b000c0b406150714405800c120030107a040e0014411a0400ca0880f40710315114079400003110401e20035401c02c070300108101011420281c201030204102c0790442060a44604000c1d81d1011904200f000004d10000401c0801101001002e4209070400d241c80c0b84ca191541e10540c00354840002007915880490003d40081e2203034010240b50028a58089660070848070b00038040c16170011450301143c060800318a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 975993030 1250 975991780 975991837
    0x911040b0102030c0c0609150313061b020a1e060c0c1502040f140307080708010504030923041d010c0c05010c0c0b011e051809010c020d0909020904180503 68
    0x102c411041601404d00c0c880030f20100f000b141e01c540283c5800230303840381c0708082e8000c00b40061803103801d01c0f882d00e00b0064000d1500c203003200c442e41014009420702020311103101d03900150074442d4682c0700160031102c0c2c0d5061000d8002112030304008001c2c5003041004800300b0742c0301e20131040c070b98400c4a002c900940e049d02103400f1380c000c500808081d440d40980400c140b54103c03410140640d000b034151141c20b5282c1e0f210500f45049038000b600d00340e468805020030168813261002c002c1c004c40321010701c84402910358070329980aa92240388101c0d02c42408404005070042c1c91151485a80c00070000c04240d214090082e41074202d00791801d51800b9081c81001d40910065241280d200c081c0c0d50b80d9a0800d00d01c4441c1a02003403038070044503090000030501d0388503502c10141244043c4011142403501c41d0f03031182510300b941c00c0b00085412203101c07034003110f80060044c010340e2007000000d6115544c0d03002003001070503c3d0072400b072041000f0755100c00344800030ac001d02c17035214035032006c01c0c24051128401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 975994280 1250 975993030 975993037
    0x150f010b090112090c08061f030b06041a10021029010c0602160f11240c0a1e0b0a0209031c0224100806370911040b010203 54
    0x816058010041041e00b50b10415140d12106491038001560b0b90300c0340c8400c0d0314503650760409451684003809005c1d07210401d03000c400c0c05501c460101c441050550703880e030512410141640d4083c0d84c50340380007240d000881c0c1340103469070009820301c450590b51500c000e41c0c8405001c1e42130f00c0c040c42e00000c2120001c522280c1d5215900d180d03590162450b0110044400d504111003d40e2116402d02803400c0303990106000c1071301036001c1c070150341e450000e03800c0403103014003000e5446124400810081400c014030b48403035480c1c45020304507180c407007039404090703800c000f4000c0b4004c16901180035026840341031f00c000b4044090060004460580c1c1c0d02000d0003c0b40710310791425070b240c2d00c0b056000d0b0384403900201d1a02c03060b941c0d1040c1c900408050514550b00c44500e06024270300d80d918000c1104200c00b404100e40201103400c010007581c105810184190200305a10440542c840c400b81081c50b00c1004800040e6031341d990b0200a400741c0c1c1d04020211004107840300b4456410105040190362000084c3c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 975995530 1250 975994280 975994289
    0x20304050306040305220603020414271812030406051602060a020304031715040f1a0607170f0703080708061305061f0c1218171608150f01 61
    0x925094495132815552500001d0000c03000b178008000746e200010425582d10700401503074a0168641c1c0c02e0800e2881901d0320a901540a403c04010803a5015517845070328a21103000102007006484180310701c0c6401d42c0d0751458034150320170700d01420041e0754968003c600c150b01032402008151200b00101220000d90300040740180e11440100705051134550003150024800d007400d0780c020010498401103c84110380010030210001c00c1c1c1c0181d818140034001410380f004004008a00e00800e01c405455816211540659008a99a01001f11114800b04c1c1c42c2450000d4545602d1010001c3d5019030004030210000744e4451702050940703014404450003424000c000c0050001880000b034001c7c6070040400343d022303001044080c10310b00507440c8400304024954170303241e541c1c40500304100c6141080858004102d018a81038561001c0c1403080400c0d1881149003c0346403681c0c142d42490300d0040144464a5140d560340000c42020001c2c45034042084072842201d1542c8035806208144400d01c40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 975996780 1250 975995530 975995533
    0x2202090a0e03041a03180102090604091d03120121031416080301090e0105010b040614031f120203010b010c261207020328050a0302460203040503 64
    0x104000035040d8100d007800d9000042100d041c00e40d91a031003402020a14a9041801000400d210440050001c40d038540e0003810003c0d0724025208011070780c1442248103244030ba6030382c0c407054810000407903030044951903400704882e10713100380c816460a050f400f841403102504858241003c482c0c00e048524000542545800303c44040d01001c220345507200e0401c5800c20940c803a403140015500c3d070b000e10b0180c00f401030300050500303443c0140c2c0c1c00c4078410f802c104140303581484100b00c2d40382d000400e100c2d1030034450354058aa4807003882442e8440d10303040401201000c500350100f131001d081241003407110300880c024840f5691010040d66510203607100508059140e851402d03240030343d20039000d034115151031000d1500100c0f190020b1003e2042d03130f492005800c0045c3e6021940e50102c00310795024000700500700160800e600c05001840b903080c59006240e004107000205409047c43e026001c080e034000300204446051107200d15401301d40024010110030807078146c42030b10001c02c2d9000d8410150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 975998030 1250 975996780 975996799
    0x15040e190b030c21072607080a021002191118100312020f01020c0105040c150203120a09140d0801060c050304050904050102090d0303150518070c02040b0a0e2202 71
    0x1014800414900064100441a428224904007400300045001420405c402101d12016944043c090300800c41b90814107500c00c0a0a120703101011420401960b412034104038031001102c816414415101103940c0080c20b0000500c00f88181d10303072070f9101642c044444d03000c41d403141500c1003020310003501c90190524015000b0f000141d004c9640e82450985401200c45041360340c1000d60980c0d01004500503140d441d82e0a1000300040d40482401400c0200ba01d45140c20305554000c7d030300e0017000c0010741800e0b83c80f4013041c0e020400398060028280c01c048070b544c411610f1503030591354400c404c02c0310000509000c00010028411402004516484000385213420320f80010002c400c034016000ba201550b080023403104640c3c4150f64180f449209840201c5d00d00c0803031201c2011207805900c458020003840b08001040d2500203c42580a10182440380142c045800481c005107201c6691a4000c4680d00d40801c0b91920055580c1c07141c030b510240760324004002c51902031000030b1191700940088100c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 975999280 1250 975998030 975998053
    0x8040e0f0903370c020f0604060c030f0c0b0115020609010506030d03151e0f0608040206030619050a09020c0f0102040f0302060a210203041103010b031b15040e190b03 73
    0x6525240c0000000c0c8200108036591541180754843d400900408500e503081e410341107081012203546101c00c21180c403070a013840d2200281041c150f400c00101040681083c1d6030119010314008182c00c0d800c005034001c15070710758101e450300c440540e44040161050b400050310700441409080e08c20400580901002600c101041d406002c608404802224400f0404541701900d040c2a044d50001c040f5030b0036015240000460070159290000c3c0c041128a02c20840540c68035011260000000d48810010b6000c0c00c90b4418001d03026000503030311400c125030001ea107444030380141c0310040154040d41d69002540c1d80850807445184901094000d0580003003001d40b424402415001205080c603801212000c0e022008050300324603a6059076a02000340418000e136034504c0085800c064008100102188000032303500c256000d5040e52011204c80b80003031507102c14000040207032018a24076180c40d00c1c1d0600520f940401c4034207000408549000c0008040320340211402e01801802500e01131029 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 976000530 1250 975999280 975999307
    0x40e01060b1b03090303070501151e03020904080c0a0b01050a0b272b0c06050c1c1205010e0f10030c050d03090b070f030e0409030e04230408040e0f0903 67
    0xb05407031814140000d00c281c003460340b0240000d0916900c68000021125580c4d15007001154049d000b4041c0c480d03184050b00035007100301080300207a0303404440f071090556592810309500d11607100b0001150142e00c01c00c4040006120b807c80c11b0b03400c1118104c003400e4032001500302a00405010443d40c064080006101440b00c41030004540e1014004803444c001c030031401291045ca10f00709246480c0c0000c4034206001112142102805441c50944d180500c0c1c81c4005a130303455040b005100c3d842c1d680c40f030040041c2c010b0002c0d13100c1020804041c082c0351703941d0380f0f920000102121b0711003042940b980000c881c002c0e034074200000e41e80d00900c1890110300707110a018003214010001ca0500440c0c03038011070034044480180102a21900d481300822103e0310340203010044148045024034105080100040e81002c9070005000c820750300003507046100b59002c084666442c1d18600c0c11840b03102032009110322200200195105500721132100d4950050902e0506070450301003210703400501c5407000301a00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 976001780 1250 976000530 976000567
    0x61203090f040b0307121211100f061a090f091303030504020105040b04150e040e070306151508150105090927120d0b1f180306020409020702040e01060b 67
    0x400340c000984403075150b0102c1e103400555000004281c003e800070804112111f00302a0410101c0c3c504140c1c910700d4580c525903282c00e0040a1001e564031407000000d007680a40c002070042c00850808446040030b00b0550b129070340300c03004036030007420140d03c0050759051110350903005001e40e11000360808040d842c11001840e028000701e04100041200042e02e4480c40c0180c0040c003818500c07a2020044000090800f0040c41001070003241090b85503c01203901242c0324003141e401800c0803c3c42d4040e0044101d0564580d040340c3d240d00560481240700641c44035999104622114040003089035403401524103019641c7e08a6103c0c58070000950300c0410102c0884800488012500b07107403003040e000e2814007544400c0282490404100040c400180d402400c440110035110350003500b103880b01501510000e088440301b4040311403030907424507866021000c000d41c1c03c170004644441d00c560046019502400003a4030480c1404031b40403c0d80010b118000446148911640c42d0040080f00c1c48062030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 976003030 1250 976001780 976001809
    0x103050c25080702270906010806070e030a12020f101803030b0d0f050606101107050108090307050f060a050c2d04030b090601090e070e01050d1104090f0b06120309 72
    0xb00501c01e090050300c1e100301c242040241e14000f80c0000144801c0d0442da4800185064000e91100004100407080400c00503040707201031500c101c107924410042803034410a0440146640c10060b110036400e43d0200b5035070390008a401c15030311129000038801050b41c1c00080200d8414116031200301c0003a000e0b600c903000504c40a400800300d0000c0b030319a00030a13041500700341c445401803010030210b4980b142c01e89180410303d00301580b60000403000d1569480355402040d05120080b40840c44000b4204195400d441d8844101c03407041685282c5a500c0da08241d809008482c00c000124a4120310a030595003188041100c00c901c2c00070303c0b000c0100c072800407c030301e2900400401010000c1b0300503940c114415400d05c8001c0c9000d526100c0c9280445404a81988858100350360611a50103d01c2c0e0840c11640120784001111006080c8006251018202c0e5607202f0300d021149000c000950300b028a109000300d240b00c1d01a80d603007050020a680006090185030030410180c5064504a41c2012415 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 976004280 1250 976003030 976003043
    0x6030604090602071532060a05060403050d030c11190c1d0f07180b090301020d060e091c0e09040807060608030d05060d020901120302010b030706030b0103050c25 71
    0xd105440d500120381c0940b070192455180988aa080003401c0d00403081c80c0181b015a161303c0c014198046400307040050041240ea2809030040350050ba5500e503614043c002c006e06841e99165640b07800e59071503001c59041c1c40401d080060403000c01d40940140700c0b10310250341c05000181c00c00740c0440d1040c4400703102203a01d80c801040209a080d04400c291180d00301d402d611003114100501103550140d0018510f0303040003100c4040c640c2480c1c2c009415812900c03007910035501d60034840f000a000e4001d0010f440d600f07518003c0002038119034602c290707019449900c151a003903869000700c070508451820341d031400300f6065140421141003a0a00c681e1150048403940e042a00c107550f032034251629544005829840440c0c4206442064403031150490011103608203010100da003c65801d801c144039590b07241480d00042c0041c14007e40107018840c4d0003e090703a10441d01c8040207402803241284031030000e4501000a01911007100c100c6445d004d0180c80e07010407000902036408500b20100044500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 976005530 1250 976004280 976004291
    0x100b03010f0303230c012004050609101101051005010f17160504030c0807050a090501060206071b061515051e070807081c1103040b150a0512060103031b0503040506030604 75
    0x4130032688000d0200c0054000002c2030829050600808445103a919582000000c200c1081244e0700d074000c80c2c0b04100107503940403100d6901d140c2902d103130700e40303841050302c95080c401041621050160b602050300d8007602c61b0f5180814181080320350302c410008090b82c2d004107001040c1c017445801c10608468245140281c9455200d6840b000084010307446002c00da448107005000c43e21b003150040b4080c08800004020301d40c50f00d0402543da880242080003803001d002031381e500015092481c05146a00480d0600104007604100800c2d0271940c0300304071501861940e050505407050089644c3c0045216040c00e0309003c04002c81201c0e032008200311085241006003100040c01900a80800111f0072111200305840521000c142c403400902105e00d400d080040000060f6441100d5401c51051480250500b070108045011691590031090780300200000645100c10000b5405043e41d1199842002040c000c0ad00b1003580c00ca01c207002086508248800c1c4054201007014607801030b0001c002044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 976006780 1250 976005530 976005587
    0x17040302030312060f100507031b0219170d0801030821010803030a0b37090e010b030f06070519050d05011205060718030b090705030f06100b03010f0303 67
    0x615400b141c1c0b420300d4401c4040c204980c178901084410030300d01090718803881c0201c9501c03005281c3e10500d40d00a050122041402e140c0400c407001102560354050500386444038034440341001030309a4800e600342d200381c80c0e082100340c52000c540e04840301c01c2c2c0e440e600307070303e9007507590f00c5030150007907080a00341c46c0c0d088164a010101000e07172a402481144055a603a060141140040c1c40c410a003550092072408150344a84014502c1c2c60003c2c0141d0080000311080b00110000c40e4502da4841780144c0d041130552010884194402c0f0303145541203046885100c031088005032514002c0360303100d010440900c5881c00740781e0000d096104085040c5445444c140e40c5010000480304203030400f030321842a182c0c81e10708015081181ca5001189400c080901c000c0042e08a8040c00840c08001c26400d03150010604960b000c1160b81e000d44001002d0f81c03000c00082500507070712001240da01385001c102c2c03080010350380c4c280800c49042e5820078946268481c1940c070107440c2c40c00c4017065002c8410888040c401c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 976008030 1250 976006780 976006783
    0xe010905011b080a061a0309070305010e010c0e040c08160509100806030d03051501030e030c0d05090913051b01021504260903150c16050102040e09010213031704030203 74
    0x1a51100d030750300504840500c803000f080340d0002004071001504d0f12009200b4003c4021039070050040301c010903503503503840000f0141069443d6100412541c01c00d02c0711250100b040d0040b030609000369a85282c0c0211b190100301c1682d01082d1200003049440340441c81d4008448203c0009078440d0901c02d2902072140f0200e041101001104400070700303544144180c9190510201440c0c0f40c0d41d190900c00d5042c160000206000240c44480c14107130780d80002154803005200f0b03220b00b10348540030b40f800404000320262099000e4940c040c4188031610000c1ca181020704000e021242d000340007060080591402444800c424102060640c4903c0070200030b0110a01e50b82d511451243c0c2e03201d25100d42648081401100201c6c1a4000907011b0181d030102d078800095a081e500003440034003455807990900c0d03030341511036000c102c1c1c070b1341c045100103034180b10b0150001c0c80cc0300c61565034902c0ba981c07010740303040c200e000d00c2a0140103142540c0003000481c0364103603006180400c00c0c6680d8540f917620350009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 976009280 1250 976008030 976008041
    0x9032a0f0105160309051c11060a09090608010c0311071502070206070b16020f0a0b1308040503030a0f090f0e0a1109040f05100509040308041b15031e0e100e01090501 73
    0x45001917160345040c41a405c01c1c2040002c444401014040401150307601c1c901c03c400e4090312a40140d030041003480400340310303528141c010001c03203000b000026101c44901c1d0180c0f44070326001c80031034200051601030101c80012200300c142c008120b00014004c00c821075010394815a02a80e200200784201000f044288031242e010342c0c5183d440d0f490b04240d03a10041c1c144410840b1407100d035007000225401148440c00d207140c0c0320103208101080c0340c1e040e181401140c00386802040e003520001c140244450303000707404070501c4401500e80c0c2d4102a40e442406400a00c1e0f03014070100403602d0300c042199426643c01003040c403000b0000450510180038046030880d071506900c000641c0e00c500500c841c0c6100d036030500001d4407041e241040140360540f80a003144101070001003403c1c0607402d2180380907003014262809030070590407001c0c030b001030008004c000e0070800907121440d201d105405210804503106401c2642d21120117000a6039240c0281d00003031047e48000c10b629504c8106a2000400078410b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 976010530 1250 976009280 976009283
    0x12013b0604020d0606200105150607020402160308040b0901020f25241802211c08042f100507061b0906080606070210022109032a0f010516 61
    0x400c82e01c0d60003559061000b41b05001c104a207030340b40105003c0155005072000101e00c801b5107425685400c14030100d0003e20408480e5880750f09480205020940c0c84045113001b03500600514406031101c070741e03982c01c0b80b06200740f108101c0410049092840b81d903209507510f100c0110003200d2030465540b00c0d19210040100d512480b0300c03500300e00d440b80d400c20b40704004910701204500701c0c00325600d46c08150540000500b00992a03c0400c0d503020101d010000d50150344c04040100400d10021a0040c0c144802034808590081d2602d1201070014002255506c4030b111030010b41c02c035004038800b403180074903891203001c080210821000b404940b50780a603142040c0034489400c1d110201c0080240001d5054003d00100841901440030bc0d5503581d0507034403001e40454121200d1071340d500b4281c0c58507030400003020b05d200c0e548241c2d084500001d006803c03e48400c1d400c0c1ca60410307019154402d20b0000700407241e40320491000c00049418882d4a01100c45811304081c0e1900d2803644100c480110010780 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 976011780 1250 976010530 976010537
    0x120e0607261609093b0307032c1011010f050c0903070f0b250f03090504050903071a220f0201020c0402030c0a030b0f0612013b0604020d0606 62
    0x40208400340d0000b41c00707005008003c020011040078804100040014410a422100c0030080c40c0c0c48850340285050600e0310319000b101d941da051841c0284c59200201d01840e54031241e43e0031201100303c140c940e6080d0f09e000500c61180802c0060b82600c4404414072421034a43d0b841c80d0541141416200b9107020300083e401c0d854845180d0006c061030100745812002070450715050400004205005441446902c07407054003881800c040c98400107001000054035202007404108241600404004182c41d803c1d582840b01d5940c1c02d02240c0e4a04c81d01c13400404485040c10291444a05242855000b00c0ca030b0a00102c20122003200c13408c90101010107448280c0e00340c2c91081191703010803000041c04402d84041d4110b2401301c090031546e0240d4142c03102495108c0848040c00e95a517190f100c03410600030110703503e0702c003104450003e102d424000c10520383c10495402e800e00030fa41d40e00b07024800388034410007100d240a00110004050262205030005d800303018150140b10203000d000c001d08be2558 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 976013030 1250 976011780 976011811
    0x91012060e09101503030e040b151207091a0903070b071203060503060114040213091d071205060615040839010806010c03090503070b0406120e060726 66
    0x20040382462940b4010b204060720348544214034113142c1c2410310440b90103050000c001d051080106014046140701141e02480c00020386107101800005061650200703541010155500c89054841c0811760050042c424520012516112403c400414901c0009000d031030b04103035152000340c8160444601229546d40d075032010358407154507100f202c0040100300c00524880d4901140c1100e4501c800021074000d540005844146900c5041d803240140422001000709460103612080700d901003031111003031401503100000d42280c000c8055040a60014080c00040d101c0b01d042180740403c4400d51101c9180502000401050a008031060010f406188945041c01c2c103508003400c000c0c006d0000070020f180151200141d85c02804558404400c4c20035492902090800744da500060790300041e0f142c03003491720203d0081c03031480141c003c9440d5078030f80112852081d011803007514044a0003a450360f1090f00019050307482a220030141180216034101201480c01d50541444003c5a240c07005100780c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 976014280 1250 976013030 976013041
    0x90b0f120112051504020d2901182306040203040c1d0403081e0a050910090f051203090307030804150906050603071706012606091605040c05091012060e 67
    0x6100b40c007080c40b02500c89013203a00e4958006003c2e0070440714040c0139480c61407420381205694a10050300003004198090b115030352414440e0b10081c2c0004528881420000ea4000c2c00341202010001e521251851340341a50368a02440000c2d0401441501c108440c44000070740c200150703100301665803045090003503a240a09000c1c190f014080c0902a5414454890b0020b66030b44000190708202080c1d00407c403074030703071007611450b100307000f11710000c450301d0721101c802000300c08504004420b00c074005075403500307006d000103140f10700048032008101e0704104105130029101d000c0e480e6200b8860402d189044010b105000200e60385c2c0d88040b245696260140440c0346400c100d40d0004045a505001c0d88004900005458001c10b110b07203d08002c0c2240854102a5211681c6485804690031903010346480c8511942d948441604502c0c81800900085042d08040c0600c602103152512001d01d0001c0c140b007480903c414a4245400300501c5d2030304480d0784034490103124024014071482c0903490504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 976015530 1250 976014280 976014283
    0xf0604090204140d0803150a050a060201060f08030703091424031008060c07060513050a20030705090103031206030b15130c08070c0309030602120421090b0f12011205 73
    0x4014644a408a880c58000042c200400c987d07000313000da01301c0d07055000703000042141c10211340c0003950300c2132840c90040b80b8540d0541c4807604880802590507100c80d5680590b0f6141d124411002e40040c0c501034040c060710318000c20034240d4120290000e58015001c0100e0340c01040d0107444140350000c00000d02140d140c12191410250204601030a818148130303907060558407441c800109007549400c0040c20084065441c92084c540140a444081c500c6103404502c903200d50212900c485ca40742100301c030900f0001442d00603210f014100184c240d0950b1010307110b00100760381c40145203440310000b0002644d43c2c3d42e05406601e000607500e03506400c0c507081082c141c1300c00390110107a501d40b0b45110045079000d5404d503003040f103d003450340f41441ca9040c1254003420340d400150441e400001e40404c41c8043d042c4c01c038400d80c0101c2c0207140c102901420800b44030401a14200012804072080c03044d0000310006000c21103c0302000ca01d030000354490522465026805038114085e5031101e002440700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 976016780 1250 976015530 976015559
    0x10207080418060528091409070e0402030a030e0f0409052404020f100c050708060717040302070b030a020403050708030d0b1009060f052a0d0302090108150f0604090204 74
    0x10b0740d5005021080c2070002007524803543d002c0440100080000103803441101c10107038000341100a00900520307101b03071441030402d0300607504100544100b501c00500054054025405184c0c020083d101e03071442601e0441d01c0c03a09182c1c01c40e901c40e00190304003400c0e540354420100080e1107500685080c6041d520380e2002ca601c804c0e40d8001c803803100010480180d40e5000510b8000c44c045904003180490104100c1e1009407406000b006441840404a550307030000500034828829030b40c5201c4000110040c518401809840c000d0240e030140e0410712884c60105c01841d0300003101c03a001030501d543da0315038074039105d0aa449401c0d103800000e0742142840a50240d9840c903407080d00c1c10700c009411204000c3c483d44c850f00c107540811031030f155240900f500c10300891745484500f14440c400000050070381180d900c2c09221101c654480d2441d07040741d00780a0300968070001016141c050440e41c5415240c1a02d1a4402000d540603000084c0b007400c4d030b40c03120b010f8009400d07000350042e1628145503800c0342c03a88 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 976018030 1250 976016780 976016819
    0xa050702060604061404091716050615010806280609172406010912080a0806010f170606070c0b0705010c0c0b0a0b030705151c0b151b0102070804 64
    0x5040800c00c0c0f059051754081100100410780e00060500c0071402c11600f08805c002e55004250f200044181003052035032401c080d010300030001d0f21003a07240d0600b07501d2031401d0a003c0e50301117a4214002240743c5810246a49000229019030408585000d00303860803003000e410801c08a8058241408058a9041032032010908803006042c1403100348030003010101d003800601e007400201c0740080d03107903449003024900500700c02250781100112460b084895800140c06000083d080030002071566215040210059842da00c805090000d10b525943c48480018400340e0800d0080001400250300303003012000900700898070741d89a20b040d2030450309540d1050440d404020790040b0000c04907403040c18898002d000c01c0e10000b0806002c07030209041141540c400c541c405070902e00034140d01404e20081c09400c2c2d62414801c0c01102e180450f0702100c800002403900007280002c203613802c212010051010102848071020041c02078114a4260703800540119034454000c038080003034466111b5030f48a0b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 976019280 1250 976018030 976018039
    0x9050708030f120c092b0611031501080118020d0e030d090b07080c0319090b0a0501060e0a0326121006032a140c06010314070b07030f0e040b090a0507020606 69
    0x450b140e002803464071000b95181200345060202c820258010250b1401260b401f14052040200618002d0401c0d00200d5040f048100c404000c0d46403503104512143c1650f520341443c3c1d003601c624000500003074000d04454401607950700098505824200040d0410a000510205e07c0c0859840c088490010280008050040c86010b0140184160701529408035031000d00c40000e10f15850b902003d8003810360040c001c04006014000b40c02c1d25600910706807426a110155415103001c1400200c000360b10001d021401840c1c461001506441c1d04042d10840da00a0b035410003081600c8004407000c103558200400340300150401c043c5030035010341d42d02d06152021a4401880044c041840e00a11942010400030400520304240307010703800741d490b458100300445640d0342c0c6a1030419911403021008008034072a00d88006547d0350004101c40c051949691485140014400141c4420000110322640203842c2d00045510392900c0449030b00c80c5841d92000b04207170030300381c202a05121340a41040d014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 976020530 1250 976019280 976019287
    0x110307020a15032703180b0738130303110a080a0f02040305062e08010b03160f0e04020a150503190501121704120f030e2209050708030f120c 62
    0x52501030040203045805050088031702c883c40f03041e01e01c044901d400941048502185803424403541c00e0900380e0200300c641c400544102083c44141842701c0d0811038410780c50040b00090120110004a604032a100c1d06010400c031240e101c441c076854014410101c0040c1daa0003c01604800700d0051050002c03044034118900350858554030b44441d03005015410400ca410641e500c5008103040343d0700c200d002211a01c030840e44403003415000c1e200813642940310b40705100007100b90359110110320080314551104c480c1e00c00e16146d1480c040d10b034004e0044ea84001078500018500004030b24116035088680c1c6d407242d1300d140142d1244070300070280f41c001860910788401031003d040800e081c100b402d600410440002442c4000e0075206106942220080c1d0b80800500c1040100011410394603500c01d4403015405484902400800b850940001c0c0000c0900c542800000303100354448035041d80501d050301e5816860f201c0d81469540400860b089114000654021404c1d10074030507504a0720309202d2915 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 976021780 1250 976020530 976020581
    0x5060909070305090c0406090e07050307080c090907050904031245050a0c050111030901090902070303020d0603030503090d02010905100203100816140301020a0c03110307020a1503 79
    0x52040204010281030f41e8101043c1400700421820203003e01c020418055652100320340c801901c0e48002407501485071020202d0305240102e980c0c8251004c105c020410354154204000040801503c030900c2030080c400007103402e0300c4041700588100d0098960344010004a042e4008981c0a517a00c0c000002204004000340c5c1304503640329144400200700c01e1180000740004100c07004410700010a10305c01c0007109000c0100060301401101d03403d0b26514009a0141d2006481e4403412402600040c7e203d00c0c11b0104d41c4055000d0050b0342c1c02450018100700d8081e0014044420b290001d0b404290b01004111420104011b0b0401c076004901c020701c0000107944c1c1d210380e510340e840050145990080b000646840c000c40c0c601c0e00800000d0700311003000b1203001d40701010207014011b0350000c40002511032043c0c00d05008440340281c443d6100c011004150324200c1d5250480b028001260204001e001d003d0b80d01c9030302c6840070b170500c58403036115030000700000780858841c00101180c405140c6038541 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 976023030 1250 976021780 976021789
    0x6150331110402031f150f09031a1b0c100b04060602060402131e02030709050411070f030917070f05030c1f030f0903031b090b0403060b0d051e010501050609 69
    0x2007203408140c4000d612520344500c10144140c602020100001d02c1103400170300aa000010004c6510994484407184000c101e0125103c4109000c05080d244c01e500c480240c0f10511a03080394412a0912400c40843c283d990f1450b10354400c500c854025407108608088005041c0b0034424180b80c11034040202600d41a0040e40300c1230700400c080d2180c2c038103031103d900001098001c5800386030030060312050310341000d0011001b50170950312000041c0042c000030846007403501c00d400404150f100701d1802c0c80c0042e40c030541c4000c0545012010050300c2000050344d460311240380400c110609020b80748090422039040760082c02c0e588054030a500c028400503581d2501d008844a07154481d01500403205041801c0e03010300b64240480310454584200b0505040d4140d10032005421100b4910364610000c0008a50360381542c040c10075040d00804c000c1000951070303803180b242c02d03802429003003805a140c0c03681da08080301400c1c60b10112611007c1209448020b11034030340540f00466034035040144660100c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 976024280 1250 976023030 976023053
    0xc1710050a1d012904020d0c0210060f050f040e0a1b030b0a0b24070534050907050a020a0c06020f070803070512070501140405030913020304081206150331 68
    0x181031181241c0c40c4c0c5510f8540458105409111040c0800301c2ca980e0025a6010741c01280e0380703030340e150000208600078424100b004403a0f00400c4040d0b402d88690420008159015001c0710703d2080581100c00512819020764156444041080c1b4080c070354200b1400204004000d691140e10f0405142d4040d81c3e00f034a04084005954800601100c414141540503c40d418020300701c1d10cd05640e545c5016141c0000c0d60001c81c075500c03807114103400106096a008698004e10303074024401000141c0d060721620113800d051a19104132140350850f40c8404071400c0b0316802c900c0043e0803901101d100c050040105c21b000f880241c00461a140c126140d180e1225500e0100101c49000000c3ca8001c0c0102500103940020701d000c40c08105017450710b031460303030b9a0140030614011841040c140c10609641d2090340d204d02d0300000f5443c90b0507006095a003008400404150307020080800b04d50300d00c400800034500c03c100d54a03040a8000d04040e5403c40140200755000e902c41c40e0400c0000010f03d212202c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 976025530 1250 976024280 976024331
    0xc020f120c1203131a13110a0317030a15031a0711030a110105060f300303071805061c0e0f011e060504090c1710050a1d01 54
    0xc854a414201d05001e040c6100550102800345000c010310070030301d084120f070000301407007612080e000603c01c42151318030110807580d800d19548650009004641d6281200c0800d910060000200d031741c0304d944021007540c081500c05001580807081081022540c840e1400000100100035400e82c42c603a03540d213909031400c4c840d803590b880304c0300460001400b030302c90105111012400d0f6502d40d00504030080080180310410440d642c2031201098003402d02d15080f04010030068190b1070000045054503419075461020400d41c404841841e0102035000e00146000c3d6400b82c0e6405070101d040304080c9840e2516400c01841031a082006a034a0040e003c140c405004a0384000f04510200c0100c071420000000740710348455003031441c00c0d000c045140e5401c0c2d00250701d01c0d500700704051300d40d0184001ca80b00320f40020425004172409100501907030a10701c40d40e00c0898220b03100070141d9582e56041c1c880544100510584460042c6a280b123000b00801d41d80c02c3c1e0f14000c021040d0781c502090402004483c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 976026780 1250 976025530 976025563
    0x1b0b04090f060f0e0a3e07060501030c03050609011a01230d150e1317070204062303011104050f0a2607060e400209040c020f 55
    0x18091401d20060b00800020080d00940d5250183d0310360070300c201054100c0f0303020722030b40c500203130100c420711918042c69019040500b6134010b00294040003641d58070310518040008410b008280028590780075003406580b11355011720380649540340c9140b6060001e0040501c0c4e034108400510390400c607000c404c0e01c02c282440e10b65101050001180c44c0040c84440d400c0440b1000200c5e1082c0f84070380e40000c1d4420b4a24088503944a59400340650b58510984105039101c0c1100400c1c00070034a2585c500e50b01105841d91030340b40040980c0024101c40481c2d05c40f064010a080203660700d1134040440b4444288141c00900054802c801c1e00410341c401c0d406071901c40d01c050240710300c00da25119400b0024024442802c0502070055451405d4005c1004c0614018450007401148851013480f2449888001810302e00c10030518603003580308141842459a0304210505a11501031111180301400100651006a0391800c003002d02042d034248080003010f46d407017400c500c0301e04a00012092021598800c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 976028030 1250 976026780 976026791
    0x308030408161a06030d0c0b0f04051e0d08070512040b0705041d0405070f03170318011a0910030803040f02010c050d03150f0608071112070503071b0b0409 68
    0x2101d8051400031030000d003030a03100b09503100c00c40d001074807058084c02c4110304984602040e80350031942c03072032000c400038840c00340f8602040d190210313008041c3d007191181081d00c0002c8140c450402070000b44407032011195203e004590140c5411070003440d0010030724034201c4d28000b08100400c941c5180a00000d002082c0180020381b89845001500c01400d054210580c460065426184030584151000c0c2c0d040d000b100c000042c0c02e5042c814100c01c4a42c4684c4030612005041c4030100c01381c000400700c0c840e401e40c609686d8406c58003803050994829402080c0c115400010341803200b04031004006c01c0681c8100a400c0c008607031302c1000c0d264007541c0b000c880c2601520a1004840ba0b80054000629900c42d42c2c0103119441d80540081e4010040c42408421646d070b202b603905a51107c9100e8640440e0040021802c454494001122103070003030400c54204006c1e101140c01c203544a2102554203400c00f14506040006081c004030560300c840506070501420700c02072440c988240d20514088540c0d50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 976029280 1250 976028030 976028047
    0x303040f06021608040806160c060905011107050d0201050f06031509030f0f0309010f0902100e031218040e07063c0305060103051e27121e040308030408 67
    0x54040b58410042c1201d0919143e000f40751001c040c2d000b42c0a961014003d14000400400990300e1298041d482a602e000e4001c006485120003048000001c2c5d9455480760046003090a00394020322007548150000c086483c203c400080c00c46a01900c00b07107042c120201070282e41d41d400a8424502e001542d000704843d00d8541800303155106a85440c050304202040742402c0003850350255200e10641402402030740c072444060b50807240c4a5a000b5132040c0c100790540782d1580300d98480c02c6151009802c550307010303da00b15041c0326500706c0720030b000e0380100071842000181018090004d80031402c0004041640c10300c2c2d00034005514801880d0b21b10301d00303c0310303030305070401c5002402c1091174011a0340d408203038914100802900c4101c2e01980844d0604000c205203c4880d00080e041035804454104552102c02580d44124034050514800d8010724000120101c002d1041030000e0300120403681d038401c20340c0b042d1100c6200d070040b6210842d00031f0004102250b107050840798481d80c031110041d0703654940c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 976030530 1250 976029280 976029293
    0x10f0315090e0d0203030408160f0b090c0a0602030304050d0f020a08041203031409100c0e03070806040c0602030703020c04023109060801021c15051203040608180303040f 75
    0x485488000d10140d010008503150242d01000500140e030069803080b080500c0d060303a8074030055600901d03080e01000840d05c0405281c4050784100d1084509440c1c0d40c15580314010807a6080d1141406504a9188684e4a01c0c200d02c404008280701d001030350440ca46a10380310386600995181d8814172031792610744503400c1d10910443e80e02d80d80c02150907880d035807200d2308080030f03007800035080f00883d24054030800a032034a24082071041c0c1924004294079400260000c0c050800d02c449541445841e403841c070780c107030360a112810162104400810080c949800d14480c0c0d1341e00da40c0038030306642080084101103940800c0011840b4820b031005070740e1340b0103001c4110303102051251940440b42184428541d0f12031901400c01100c00c00300081c8a03903615421440d0803441f41424500303020110801c10350050000d900000b41d22003066280c40710007a40c0b40301260000a22621820040e040054140031094001002507080086242000c0c038540c0200d0b030640c0d5910010340054440e1341c0142003c41005117 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 976031780 1250 976030530 976030541
    0xb030601120837030e06010b0f070f02130f0519020f161a01060e040b01050910080618010f150201090308040b27010204030213050f040f1104051608091506010f03 71
    0x20f00b580000f01c41601d6880c01402440c1001c2040040d000e20400042c0d40602241600c8a59450300c00c160b10303251042c1d0b140a0041c81155081b60890002010b02d22074410621410f401040b4a01c4042603a103860030096804208501d20a49030a2050000c1410403000006481a002601d184600511000d0800b9255549a03110740000f083d015000410400d84c13050b0840001034040c2e42c14007034030a2803801921140100000b440e0004079001807181000e100d401c0c02c9400040141069100c018544400f03148880c00342c0103104400d10450080080c1c4200a4605c022031a40744020403250a459400508134140500301030300030102040815868242c0340f5607144a15407050301e420501c890940614044c3d0060b10007a40305d660300c612220909411801240e10a641c18030b001c5a06a446680c5d03406010444e034001c0c0d407194041c0f6001e15041d00e4a12a4600607049002c0817540240404030060010b11300824801841c0c10000bc1c42201c1404120040e030440d000342007929003200307004011402002d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 976033030 1250 976031780 976031857
    0x90901090f080d0b011e140721090b0906040b070203150f060f1807030c021006090204030c0503210a11120304051c090302040207060b040f0b0306011208 67
    0x1084210304104903081c0000c2c0301c083c001d08800e1203244001001900c44903004401d104a008a13141c441039000d1117100301c440d41807500c250503130500307001d0703190031018103401010f91181c800c00d140704005440c0c100690400a1159804031481c2ca006100414820300441c03050300301c143c0d0003048501c00c658088c804941c0d0200c1e10301c40395860b46400108048203c40646109006107186943c003141030420024140c544d585d40031582100d9200c0300412001420005d0492045001c0c0300910382054280340a00d20040155080c05a207450075420700780c0d00e00c0615070003540700f584071080c400404005180a0560707681032080c010303128007000078181e420010340c0500c0d100a001d140054a20302c401c520142d4090342c06003084800742c645100560074505403415410303000c03c40c102c0003040140740c20340013414200d1040741c010840e001c0140102d815120189110b01a403038031a402c0c20020f0908201d00360040504040303032280c15440352900e406a00c506407003d2a0105850010940c070101c1e404841000d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 976034280 1250 976033030 976033043
    0xa0e01030b1206060a06030e15070c05060a0c020105060a0501170a110c102f0f040306110703170112031803050613060b15030a020a0207091b02010b0604031109090109 73
    0x700b16442c0a940759042100e00340d00c00d490401c0040345651083c1300f803045030403c00300281110038030307001112002e0b400101040b04014424050000103141841464083d0550500c04981d299179480007071300703540b00141114065030a20108014076030340625034605411a20040e00c6507916640d24079005800740510301c0094000000b881341c40310b00001a80400004501720403c0003200d098004507001d40d51080c0325000034200d0022180708000740f030003460107005884181e4a0595240d442d10152450228101d000850206031842855042103000d08000c000c3d121380c2075258101501000d014142200180c01c00205241c0344200110350394911000d140c202088905916043c2c0c4810312540d9140c50403035202c2c1c10310f800c1e00c82601b85150324407600b194142c1c580e4295903841540600a40001200000314401c0500014080c061032003100c81d05d0a0040590506030b82c050350190030f6940c3c0c4035445009150030003041011512510200311410402c07991005162250b058840c054159040c025085 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 976035530 1250 976034280 976034299
    0x6011202030a0f180b010f031109091c0c031101090b01090b060903070806180a0b0403052d03010f08031314030f120318010e0c01050a020a1a040c1a0a0e01030b 70
    0x10b482c0b8134042c010609108952608007a078072914070014441091000400c1074043c20083e00c0070b032800c2ca103030071340c04440380c81100c01c0030700072920040701103d9090070381010541c0c0b00003001c141039108440e4100307100701100900c880c40745e56446020700300c4c05102d50704c40c1d15500d41e2258403e83e50741003100c116600013000c940c81031341c0390301c00c00f80c82e00400c0c0c485aa10605084482d0550341d404a00b045003079401c81c01303400c00c95031151402d4070940c1c800072480c07000300031691146610602490b4070081041c1c401c03080c26283d60400e601c0259924054005030312031380c014840e109607848115040300c00d031015014200c18411030764001c24a04064102e5040031801000aa0f80d0700c3d048000140d0300c10b00b95035025202c82d651142c0361074200e500d81c0e840f240558004e2001c03200703a540140001c02c1d1405107841240e020f40000d4584e110302040291060a4a001040501007030082022110014001c0b0603140d501081d0418110001840f07803c1c240d20038441d080a581c00183e0190740004a0444040c020525 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 976036780 1250 976035530 976035551
    0x40b120709020c0105090a08030f27060a11072a170d030b010e01080a091110120606032a02010b041107061109182505031b0306011202030a0f 62
    0x79400000c243c0c1e55642c40c001c0011500d010000b8509041c0b500030f50003d14580391040c2c40c03010090005c00c180f000300c640b40007010714512500c2d4140c1c2d405401b000580000d040042104060794001d007c80c4c901e160b800d000040104180f5030400c1c407a1641078070440c2040c3e541b45013140d031481043d4003181d100402658072400c1b142c804540946108083d560400190911034010344140c1109072106000540c2c103130025544184a601a04410f070045c03035240c0607082c103000003941e40c0e070503402c070715000800d07920301d42070f80406900916010340b00c1380c14140940ba0018500100544020407012000030755080c1a07020103000303501050075a2406441440900030a6821003504d40c00004116000381c607285000c43c0445004090305e4110300c0c010098442030b800c030310030442c1002e40501801e080b018030300f00030740f084900c0798189107001c0c2c403d4031082e0700c900d458103441c4003043c08000029480b110400411040b44ea000c800785450394000c62006071242c031101036050041080b85100b41705589000202030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 976038030 1250 976036780 976036799
    0x501120905060717070305070f0c020d0c09020a091401020a02060310030f030e01120501060207050f04180b06030d030902030c062206050415022b050f070b062b02040b1207 75
    0x901300a4645900c2c156a102e003c401c0b4115002214500300080e03144038590b07112481045000d11032400102107141c004142d8071a010f147c440c0c0c0c4e01c20a6001d0b0b0010301c401c9840d030000741c0b01000701815800302154101c085d001030744814060200031320600e000070001d00c9188500000d01c02440e04061514071080c41c6240107884000c03231910440c0801e0a5551141500035940103c0b41610866809444034614080c2407142000745100296406a00ca075885200b80181484c014031407405500c903030003d0f041c0641410f0411b650140740800301400d0032040009601c1c0014030401d00303c030a50f00c895840d0702141c0c82610f410784603091000c031601001000076180d41d00001620660308941c090100490800d801039a40700b03400d403013280142c160b00010620665600c540341070070500c1ca0400902d004900014001a944085012240100c1001c140421410020300c502d513a2000080e055019040380c240300b20f01e03000d800d10000c0c0300c1c1b0740394484007481b81c442288420401200c00c0403100c400b5103401015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 976039280 1250 976038030 976038047
    0x80c0c0609030a1706010c030f030207080c0d18062a020d05060910090f1205040510030609150e0a0e07120503031f030803151c0b2e05011209050607 65
    0x1000074504a0b0703844c5198030340701c6001e00a4038140c441b060b0300a411380c1c050312041c0e6104801020b0580c24848800480c1c0b4100c0203003070b0141f01e6809403070100c1c3d0b0503001925a0000c0c090300310707840340c003c002441829000300800c494404902c0050500b02003c1c0810300300c130886050000e4004070940b02c0502003010018041e0b00641d9620240d07110382007c0351800e402c8528a4a01524100b64050f02001040103a55100070844603464940e190985501c041480301d072030140503400080c0e5800003008108024454a5016071600708640c0041d07107040c1342031001e508064814261035540d031800100ba207800b001000f00a1084505004034803e542c1405916508200d51a280f41400000b1200d01b0000d40f204150030350350b000101030701b90707290511500949007841c1c400d07a822840e4404d081007801840c200c41003000c0d100b6040414140341040301e004010042c0d0008510041000c01000c80760f492030420401a10001c1c40c2c0300c0080083c0b054620054180b003840a0420f002d07450900a4156101050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 976040530 1250 976039280 976039297
    0x18100908070c0e1303111014040c060315060f0314190e010b06070308091f0603052515030b0d051c05120f18011b090b1306080c0c060903 60
    0x8007032842d0307541c50a80081e19011280c1e40c0c2c002d648904041d001138051502c0046c0a0700ca401100d2108507042d8258044030701494085100c459038070100010450464411009401a0314007071194005606c01c1e0000c0c44418082c036401c0c01001e0041c0600d0521a521600d83c060b5110720030083ea00b0a100c0861903540d010b4403942c42c2a0620580d64013012050180c4040b401c000f800461405200b6103049900303003005890350849006d001a040e03542c004400701f04801e902185000652030340f840c0340031803a18440300d009200171303400c40ea506101e11400c0c0c2102022180d40c038054403011801000c08030700400d0b200d00001c3d40038035002c01901c14400001841c01a0160f11030281103907850403a8280c881c1c2c0030f83ea003403851844400000568860040a0980d004a1041405025803411440080c01d4407003000701d80303c031003200f5040a400580d001e222300004001c0d058030a80b400c001100c18899190b000d015201c1449015404200385a890000300c90101250307009031426428034031601512036000200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 976041780 1250 976040530 976040543
    0x12120a0f110c0103050c0705010507080a0c110705041a12030a1b110609040e03280908071406040803040605040f050a2103260f01080601030503031810090807 69
    0x2a54a40c0500401c804110100c00750300030300100380a000110017418005040252030401481600c0010b00700b40102800f408980d06c0f100c6c51880c10030303c540100ca0450010404203e40080c880c0f4480401107a80c1c0c0c165071060b10040740480e00000a190216400d06807280c001400c0454810a0306010002d803075052101e5031803019403001211a2842c4485000000d884200d698020403154a0b002c00103000c00d65022380041007050008148038210340108a00407042808842c001c12000007080c400b210701040c0c2d04100c1c0c00c00341880c21195499045014070b0300c0c0c0d4000b145150280d680c50300243d500600001046a50b42c58981800400300d4005104a00c070500c0410000f080501c0d12030303504800c3c3e4414030402289986a22094501c20700e85010076414408000020301094007000c00c00415516240c011a01506104818207c8044141e02502c482d402440c0144002800801100c4d0800c0c00a8211400e0034428001c07981410504851000002d240400800821042501800c0d8543c00b65a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 976043030 1250 976041780 976041797
    0xe10020c28090e1002130f0603051501050c0c012316050f010504030e061804020c010606120203090a0b04051005040309050405060d02010504060311070602031003050f01020405091512120a 82
    0x22140d00942ea403c0943c400d054200b0002d0043d1313a51581e01400d00c0d00e56400c06031040d10341d5080024600740d413581081d00001d45410420540b00d03c05260b4a030079110a02c2c10310b140414041015865140080440341000ba20510412110001e0844095442e4082c005607580e04140002c000700c002511508842c01d0152410920310a6410720840780b045800d5281d0041c000e03611070401c1a00d60000d0060b111200041603404038a86452000d054202054000003070400d042c5a009030070032610285290341d040c01002040300008001c110f01401c0d540c03003a00042143c40d68507089041c1401d400780640110700e00401c210a06600100d0710080340e0040d6030811030358980c49c0070302405640c0490040c0c0450010407041203120300c203500450700c010071005c06504208007507940ca02030b030f071060301c106a05c150411002d03c180001440032030030011a520086141ca0b20f46400310750300d810000c18050303841c042420090025190100c0c415410000003081e1510b54809014031001a0001d841c0d010005284a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 976044280 1250 976043030 976043039
    0x5060f1207020c060708030a020d05090706031128020a080d0f05070c02090f07260a06270b0105090405040f110a0f09020702030114040302151302010e10020c28 70
    0x1040c3c0e11044000501540d151079940d44a00034a0750000d00f00d002da20784c1c20804100e203510148140e40c09014850050a01d403032802d040141a90500c00d201304902c40100003042c07046084c04002c08000d20034001c001c2000505a50a07810b080043d88064044400050907800e05080e07a44140c1c0c1d100280300c41004142c5511204654170151040c0080d0003500c140d01013400382c20742051181e81b00200b85003600081190040314034010a6100070800c400340d00700188048041540240c1c4054a2100345502010680501410220005c44641e03800540d8900f1600c0c0c0c0c90b40324a0440316000c001800502150602d80340040340c007000300c0000c2c0c400d0600051b51504500d0040c2d06013080380d922460a115003400c0819000003988001d000b00ea0641d0b03a11603001c8490008450f40c0d110354080d40242082035000c81d020626131400420601201c21034070b0365500180e800104074010540c041d42c10071485920b201045e4648407040c0d81840c1c0c40b00340400c00c0c030400200c0c11322203c03406d007502d5000050343d81d64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 976045530 1250 976044280 976044283
    0x6040b0c160e0414011b031a0f0d06020d1d030d0c110c1e04060312091d0123060d020a120221070c0c0e091504110103021305060f120702 60
    0x80340120a41c000345140031401007404d442080610742d034010000140040c4c4d950f4550303070091514a1a0300425200c280816040120f0103000c0e0b00048241e4aa9450140242c0040c018007804240200800d0b80841d850802144c2d07a804815102d007500c940c2042c403000711030182c1e541d400003280b411402d81800541164584100026030000d65020001d0454040c0d6104204000032012541c485803103200c059018107548900400b8000c0d0701480110a07600c0085900901400b615001903442d80361005a09002c440b10300801030449005203418030681c2d54440d9100c44002c04200310982c1b050000c5528403443c48668010180f004c4980c807003095180c2240606c006074014210040c0550303030240403110a5a040b0751546074030400c1498902c09582155540000481243d042460b000e800d560030090208420800402840008004420a80303421ba0701d03118406c0c2c4d05c0b400b40341015000318511203c104000c0c04070303002e460010000768440b0441c190300400c1e03411200d1401003d0403074a0202e66000e00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 976046780 1250 976045530 976045573
    0x319050f0a0b010b0d0e011404020a080d050a0f051303030908010c18121b270203270a08070f02090c0a090b130e07120e0708070317040506040b0c 64
    0x41c0070b1841c42c0141c0ca0140500c00d25000158004c070b90f191510700300c00710300001788a0a42004c110a0340c01075242440d0060098420b034907084051142c0c0488411703500d6035045070541d19050f0061510348039500039003404030b941c1e000c0ca0b5107100440104003408020540c00145500507948400000c121002601004440040180800c03003481c0c06001014005a02c400f420801200d000e080303a01510813640d080c03800749a20070341c01202e104400c0c0b8548408031500b00380c2408409500403081d030550412000d0303403520f4440e440c0c410100042a00125007034440601400700c450350000c1c4050784488003410302c0209101200ba00304e214005580024640c41240400c1d02e81d4600b1640d02d03000f08508101c015400f0303a0165801180c20035003014000b440c4205800300078411200e558400d000070b0b4000d81280300399030441010403016006000c0a01003400d00081044c1180c5d00902d064042c80030050700303100c0030310417600704540099000801040c2032508000034940035120b4800c6520f88600030080c11400c04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 976048030 1250 976046780 976046783
    0xd02031309020307031d0c03120702030613020111070b030a0507020a0f200a4a0c0408060c07120801030809210105130c0e13030c03020102090319050f0a 67
    0x9000d400900186400d0381c09150b2001c0c481c01c0019504c40404001c2100310b070000b0441c0070303c0e80b21000700d800703e040a1141042c06c1c13100611441c10604268000703610b548000b8146000c0c02c0111a840c01560700c40c41d42c880c0f05004403000d80740e6260b21050150700c594803c5401011035400d060115190390b10009413660219084006003030740106079034825051a5154800d4041c003c0001c1036100d5a03034076960507000409410350054030141600e4903001c107465680700c2c3c0a1031000c4070b8041c0341c10441c07040700d41d9000c0e4100d4600401030303550700b03009002c0e2405150070200030b51060108018254100c04002d060441c01003c4000c040e00e00c0c03200032902100c00340001031519009102c0281d003030800702c3c219440c0203140c0c81c00b21800241c00c12120b0840310122a0a145100c0010f565814800d000c00e440005e0140c0200ca0707081d0b894404800e80d04038005180c01403c104284a903101854401c2d41a104001e4000703040d42d51050b8442041898a041d000c400c0e50305025a40d80030f0b034480d40002c1e401b540e4030f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 976049280 1250 976048030 976048057
    0x50f0106020304331d0d0203030328020408010b0909072303010f0f1a0d0206030c0c030d06030803060406090b031b0307050306040b090c01050c0a080a09080607030c020d0203 76
    0x50901400d04010410144c240c00da00381c4c040c10341e50f07101c03c4c1d2600342e820b602129500c0003913940c680d19034900e40080c180300060081013408207070710250324080b0440c2ea0040c0c09240b414058001c0200c0d0203000024116807085441c4040380c042510f14041d000000100812551121161200012103403550310b24031400040e006100c041280d003030f4000e4480f0307100c408010000a041c2007a00300032015500001c81400e010303a91101c0202c0e0290b4840321900d600c0a080c0c030407000245030760340810750750b20020344541540c10780850300390141c40c01003040b42c84d4403248030000c4c1f1055559190041c075941013030f101288958200b140c040b44906040c4180344003008018010b000104034000a540c410200380c03d040c0d0103015020011076180c41c2003011031b000c0c0d0300c584c041044070f01c2c2501003242004001c08a203410080f08100342d07040480b0004108206c130350040a1942d885220480c10f4504003a6a0f00280301801030008000300706805030310580904aa41d02a00c682c50f00b2800103d1b102d101d00050900903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 976050530 1250 976049280 976049287
    0x503120307031517100501060203070305040b1b0a081903050402030a14240105180402130209040219030e010e070501050a0809100204121506060e060a0e0907050904050f01060203 78
    0x1240d120b03410009002912010001e901034031141140580000003c03401135690002d2640740d03841e18103204843c010051480030750300304500c90703a00070400d2150b807080c1081c410012a800b45e04000400310f544150010380216140710105107002003181d003142000d01c02d8190103943d801c944ca402402920320447e8001c1c09001000d80683e645001c1c400410028051845401500208c9028456114902400070304048803558900010040e210039040d0f84c070440486203900b0b000058032220410500b21400301800740e00c41000e074010400900440034055030000c161410403500a41692000302008007180007404012185e4203d603945600e244651400110b0401000c44070a00c261345036500603c405055622800308242d8036070a83c1c00640203060950000c0c0d149104100105500700040043c052050110a140a0028202d10a1903400728003510001a000c1c1c4a1071081c645c10f460500d0041640c4c215080120000b4020740040015074040c45c5403502180b40140c0e0b40c00c0d25030403602d40d039000303628 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 976051780 1250 976050530 976050541
    0x315070306090213232d0303070b010b0705150403051804060315090606230a09050702031606090c0905010f0e0105031c0c1202100506091603110d020c100605031203 72
    0x9491104505000c0401840c3e2000a51b58500c421005845d091400c05035174040140f10000ca0200b201e640c4600c40d40c4104500c800140303400c096181140c0194081035101d0405060541c14041071115886140e844501003104150f00840540f803100003042c8054100880b40c0f06001c00ca0b030082c040905000c540c8023139028101507030b030001d16207a441140c001c142c9640d19003481d14010012601804401c3c01f03610440d965043c9186900020500301da0f05000904001e14081c3d1288206007220701c0d21801c4152280502032a5001a0621640640341100065541c922a402440280503140884518180c001051000c090030641a50402801350098050001d00b4005d500140d846142c184070a801c00b202c0415280c40b001441c11026402401070300c907034800d0600464000a040a1007012030f00248540c240f00c0c10342e40d0005100d5424000307291440006403551500840384118051800010705000822002c07940c413070300e2a03681406202c1c6507150010592910a080c004400d0030109000084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 976053030 1250 976051780 976051799
    0x140103060c0908070b12060901061d0d0813050a050f0303032d090f2802010c050304150221090904080d02120a020c0d090b040303110c0315070306090213 67
    0x70603807106800c0884071690744501c410308180301a4403500ba40e8901003590495401c400104540c4803d0403290b104641d814604c02400002c80d83c0e1140140e810300000c6042903403030305c000b15283e00b500b18600d9922503801142608040d00c1501680d4080c4810410000d050f0030011030041d0001d000401850640d40c1e0034800e00c140c20801980c54100e080d900c1100c8104000301090741c2e002d030031400701418130800c50001e1240f4005802600c145c42407401c0d0011622078105642d4401a180d0900c1e04030407916681c01c00900e18040c613040b8902e86020b48488130704003600010540c481d901b81c02010500200d1031048035034903010344c01c096900041c01e2000a4001900308004000d4a10909401404e21325105407203d000c070b00c1254040402a40060039201702c1c0300402c22100c4c42038046c60101211810a650b4a0780c41c0611f21006007400460400d00c4020b400a01c550108050060700702d85a08a200040c0154141c05a5400020031f14151020404c2e200703500859040c1c6010100303900006240c804900c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 976054280 1250 976053030 976053041
    0x50d080c160b19020c0717150c0d1a0d080310150c03020105160f180e04060608011503030f1101060b0708071b1430030a030f02160f08040b0c061914010306 68
    0xc841c0c0a540c1440b9100700c8220031040c0258695002c9d2030b162582548644100d421002c00c00480e11100c40b0100e5082d07a492545000c601d82c018907440d02c1e501c40d0f4640900300e8826411000c0c0c001e0154610302c40456110341c0342c035503903030081d4028091078507411070060550444a08540018141d549250382c00b500540a00c140c08040c200d903c21001c0e82c590700d0703d03406902510708941c015200c0c0d1003003240200c03d0041d980c40ca401210800baa0618680c2c015150360b505003555001c1c02038403e00b040c5d4140707003940032078020031240c44165a103118615060020b83d2292508894501c1040d0401d044003050030800300c140c2c0c214210480000d02008200071451000da0b40c00c00300c4021800e0542d9038a0415504181c1f21007a0310000c2d900c4050340b55025041c0ea092504480200307205000364490f004e11700556840d46038102450301c00a4125050002191017260468902400002450750701000b0001b00c851044e00d0109a220403180070401c0340083e540c0100c81101c460305100014070224041e940072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 976055530 1250 976054280 976054319
    0x11010e0a0803040e18010507021b04060503030711190f18020f181c0822050607050a0b01060804051b01030e0706030501030b01060c050d080c160b19020c07 68
    0x81805540e80d800c50707186541d1254000c2041c00d18640d09000c0700c040800c040e403c100525400a11040c40d110700000c0da145101d60780300c94102d5014a602041e034403079500690140c01c001d02540e5442200e424950000195100300601820305000b0280e4900c0c109144c4005850011140c01144e52a00c0c40c88060704101c85440e04800d5404c2051086c51a4000c00404403800601003100c012a10101000119500a82c3cac442044900130762030000214242c040b2400140b51802c41d44038101c99460480c1150034581109030010740002d40341050103000600c9001a51242c61118800c2c0e03240c1038200d07201601624010710a6009086400041c440d040c2c03169940b200626001030040e600281c000c0c6001c0c8190b00000100f0b585600610034000800d1400c5e0140c403031420511401c0340269109651415007800d80c90410a2001c042912100440201c0b0001401a54081c202c2d1b4011b0a20340b8042000780e4801c14040750001c010545107026000755048840c0c1e0001a1002c2c624003809000607041183d42c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 976056780 1250 976055530 976055539
    0x20a090504090f0506011e061803050601180e030913230c0a0809010902060901051303060f1b0c0206181804240b031c030f0614180411010e 61
    0x10041810748540c490840b8982c01801034641020850620900300001030300445501084020044c8849400d1030701c00c401c03a10545410104a141132200501c006000d40008181c0e00982000091324900c090007005201901c2c1e0041182204101555580c5d200b44100a500700d80014220000480c007644070461814848001849203680f08101e140c20007411a0100b01e02c007404145641c41aa1202405502c0700b540d80080042c1020307900011010300802c00244d04001001400a4445018408101c0110f5014000740310225060788540050420400c40c2c07110302040100380700800703101e100c9035050a030b0050016881e10406001c02404103001d10b0000340c028403001400401c0c8044034070201d22483c003603040761606155409c1c407814142d52090054540d14200010500195030201c0c0200c004071458441e4501078900c0b10301903014150251030f040080349030502c0015040c203503080000d82d180044509400f404c1205042040b160800d0f02d000e09501d2100001803515405800b081c2d10303078000140b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 976058030 1250 976056780 976056797
    0xb04020d0c02010c231e0409050c070b0c030f0f09030405120f0d02160e1005040c0903030e010507080403120203251109070e090c0f0706020306090a140703020a 70
    0x400c0001990440d015040040c1c0d92001031503c202d500070b002a2488036000d0104041121248001526000b0641003900240780b42c3c1500b030f1164200d104030b4000b000000c2c420301c0645008428007040c0e400c03aa0007a02d2106000000038420b00340c18080300d02c00c10311090b203800d04e40c85418004c0100103008060042a2204210104540c0c7d03074602c41103801c42044c2c00034040c3c2c0b5035074060503082440d6856045c0a540c0402001074100c112100c140c01601d00540c0910020341d61250501e4017194160301c0190441c2c0741c080c803892026030142ea11410340740291141041d24008400441e0588034600e07016040007810b020900005400b50103580c502895441128100011001c1c0c401040c050740e50740760504d40c04500300b2000c00203003c0181131010021a0580000e181401001e44002007103039a5521500b41c0d81c000030030300c091400c15204905c09a416040d152201490724030002e504c00c1c2c5d0828401e400c1c11001034101003c601400100007600c00c1c0e0200240c4070298254081d4100c0c00c4980103104400c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 976059280 1250 976058030 976058047
    0x4030b2716271e15090c030204050907080a1b0c110a050102190c0302090c03040606120809040509100e150105030a170315060d050a0c1e0c0212010507090f060201020a09090b0402 78
    0xc0c003510401005110284c0c0840e0300e424459812180401126014140144030401c001c3d5141c0c1034855102484d81041001540d850030458001c1c00680c1c4807021001d18070190240880e40b041c440d9520901c2a0044100c0305500d1701004041101d511820b40186d01c0040956400492241106501c601c500000c10095171203030f0004410741c2e0b080380d0800c0c000344c0c00f008010030712150340200b40c001c00c0e000148143c00c40362912100d02c14468159058010754951010400703a2a040040c0340301e05090701401c000c00385c5054005038503109501003200d0400b0820b070000c00e251401280460205500c505410f56002207a07080c0c024a41005202c1601c14840403010101a115071005009030115a24001141d1600984000440e144000680d040042006001030300c22101c40042c2c0803901c16080c508d0980b001440001c840c0da40c0c80b1000300c070075400c0c8000d00c13982c03d40007080304080d81d40b031152000d021611413004a00701d024492000c0300040c010340007002240f105600c4031081000c0680b000d454940e03003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 976060530 1250 976059280 976059341
    0x120305090a0b070b0f0c07020f01050d0f060614031311010c060c032003040f150b04180507050d080a1412040302060f01050f0604030b271627 62
    0x11030b44442c0038070000250800401001d19280c0e0340c030885025290165041c583c040340c041d4054081c000b4001c4c5ca4100110079268000c0f01035912003a80304501788440c101007000740303020f0000c0d88186170100300c1c00c2e400c030600d035024541070301d02c64405e04503007036691038040d01c40301d6040c041c50181d10305014034030003403c01041e42801074220020307184e00e01250740f500a40d44003c00c09402410361888141c03d009020008144101d0000303459084061082c4a88511803140c00601c0c0d0000e810303030b0007441c000c500c0806460116209101ca80a02c013030b80c1d50350343d0701ca090018480001c40010000f09003084030640c010b00400c0c1039020400e0101c0082c0c1004203141c1814402c0c2000d9400341d001d68406805c2050703040a43c421540940010795001c00000300c21000308006005500001b46143c0c1580c0015402c1c1c065015400c2c0c680d01c81082c4001c91075a030001098441440b602a00e074080c1c621040414820041c000700d152062001c83c41c07042080000c20b85600800742d0584048542503203442c1090b043c04c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 976061780 1250 976060530 976060549
    0x241602100c18090c14070f060504080f070f05100b030604030c05070b0706020d05101203050d1418010e03120118060305100b010908060402010e0613050301090b09010b030f0712030509 80
    0x304000008590302c13400c070050418007580742c0000b02c0010400880300028a06011410001d6001d440418946c6440c0743c6040680600706000000b0f20001c100102800030804450800300d005000741c070342140c94250240192440c0810803905039002502041c0000c1c40b55207481c0805d402042a5000552950200c1410303a0210005545c15500420801014103003031040d2074008412080704c0f10841c0c07910401c140900e43d010400f605111004c10041c4904450741c20000740c203a004521040245442c0d06442c00407000440c04001c598a0302c4101c440701040001181c0c0c0c0302014100a420350781ca80040c1150028107254120542030310340f600000012810458280c040c00e00f10408640d096605000519501c120340c08004c5a0740300c0820b000c0544d8200403258001c036421350700169070743d4141c1540c1c2d03510b81c1c0300d0317106541540ca07101421702444440843c0f54002ca00390b00003070200c032034180101aa04c410000c1400340c2034206060800030a4100040c0c00b506a02c6403d0113420902c0e00400580c800c803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 976063030 1250 976061780 976061789
    0x5060913051f02121f170c0a0303020102250215092d24030a0507090e0a09234b01060602061510030e241602100c18 51
    0x94004c1110341c0608005128a54410010882207282400f01d00c80041c4203042c03803080410304280602c850000020500921443c4403010308801809070740e81c64028000e41c040501207140264254199625440103000440c210303800820001056031181c410180305d0b0702a09032036a11034a85648011210070800c0000c24440f1300103220080380c4281000c5c800302000101840c0126120b440400418100035001d0320341044075840c000480d0340d2511010354101000c0d8010300b840325070507420002c06810703d41115121034428007910010710010781030800048448140c0150030340040080a50410381070707007600302c10700c0c1c1588410004000e020030f07000c40b6071078104c40d0020420000b445461070402406114024145c42c4018a828641944903008001803400214030940b094010124098400e0708611100007580c0700352000c200e60307241884c8420a0a01d400c1c1c1c409500c441c0081c40b0324a90816130242109107801030700d20400d08055581c01003144903c00c109001d12274400072150b00c0521f04000280 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 976064280 1250 976063030 976063093
    0x1050f07020d2105100807060507030206011a070c0806071202190c1b080a0506130309140d210201240e060310111308011e1e0e1b040506091305 63
    0x175410440c400c1d040181d030f6000b84040c00800c00916001a6000604a044032195142074411806030040118030740300d0688050801d2621100c0402c0380000403804030f0040a01d6150030101c824800001c0060340240d42c241d0303144040c0c0103490b00440d8021807043c140c1503c075204940b880040704404400d4000f0603004818a580101000710410200300480741c1c00111058101c02c110503030b075500400b203403120b000d1110704040241c40b203500c07910b0f801c0900029581c00903202e1022880600c5e940440040400414010340c00c1860501200070103000600c5105c0c03e4005d2428403600f061900c480160014056907010b01c104406440c00d1b2a0a100e40b660101c0da410b500366599444510441d41d051403900310250f40d074501000003000c5485840c02100350002444046401c402013414070075042002d5420102043c10b04013071003007282c0003069204d480d040308201898043d442105000494008503502078221410f03602044206010341c00d00ca241350310402c01c44120f81a0680e2551120070500e0010820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 976065530 1250 976064280 976064311
    0x3060b130501030f0e191401290909030d20161a010b030103150e0d020c01030c1106150d12030f0c05070f06241701050f07020d2105 58
    0x182d81e05000c4c10080ca60602001d010100d00300302016219040c00400241c200101c0303082d80200001e00602d2a11340400400800c030300c0c00c840455070b604511612840010f420101d001062910b84001003600540b100c0c0011410207050240c104020b2502c10800407580116181d61040060030400034030f1030b884080706041040480d40340040c11000c1114902d11912005001400160300d81400d40741165003003440c0308622511ba07140301c4e00a102080000d00d69001c3c02c034161340469000103010940c42801c0c2c1c1c00708001e001c09041192490810040c2030101e030800304c0071445080c0700b440074541c00140103210680e070b10b6569a907401240100f0320b1b2000480d460300d003a41c4081402d0320402448200a04040c0e250264695035100200018071004020950305c0c03030700c00d41c40001d81004000000000703188411903519800098000901150211000c0d802c21002540180f02801d046004030465001049544c0b44500295040c0304880c400d941418103440c820141c001c014000c140c000c00d00c507084400c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 976066780 1250 976065530 976065539
    0xe10020f120c0c0a0e04020603060429100c03020a02120102120f090106170607080a060f03050a050d09031a1f090b10260411030d02030a1701060c030f03060b13 70
    0x104884090030900c0703a068103c04020710170038200903e902580c100c5007643d482d80c3d4030000030010b2070034004800c03581900505410302d805400c00078244000e002ca40c1001c1502c0906402c50b80409003420060050304140d1803840103007001a10030b11030304512400541025150086038160440841c0e50710b950307604000c01d0020340710003841544054105044144e00038660f1100c400e07038600000d0101c03000c0000705000205092459807106e40a4560007955240240e80da04100341c6ea0f1602039030548043c054038542a10705802040ca03581120340c0000c08103502c0c607100000381d80585001700300c0c500c107810440c8108441d5500c11420805440400030020341064003005201071410146150420701c10740100c0c1c030100b03003152480c249419000880c1003500350341c3c071f10300350444414644207150984070721104402592b40100181200300171955805d040d007100c5582003104800284514000305881040c00808248208151708822207107081c0800c086580b01c1014090340d00c058018111280104010700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 976068030 1250 976066780 976066783
    0x9210605042901031a070905010c0201030b1c0209060d030e0904050109060615081062010501140108040218070201020a02010c02120405010c0510110304021f0e10020f120c 75
    0x40f6888178240e90210a00c0d050f0300142108400740110360500c40c001505100310381c4250410640101d01400d030117090442c0d03d4250500b1401140304920400000c4000f440340d050025804440075059529002001c05041c01d1100707404010f03006540759501d90a5010200b1018055003000b840440c1111420ac90b4814009010600191412000004402040000e240940ba01010301030500100e40d1030a860741e030219030142e900000819a0101030000c4061030042615800da0305501006003581d400d802595190032540700340158044544041840c5c0543d510441c00c0c0d81d841440680845c0c0401c04a4500792070310a411109040180e40000e24855816420700030100d0409031400101865030340c82e10310303810760b0045001d214100310703102c60500280a0701308030194070b455006408004603c241d501c8142d090f803084800f64003a0055240111502411102623000a034156907a10340044c401030030000643d84010000d0308510070144400c0d400f00e418082006180302c010768032955140103141c903d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 976069280 1250 976068030 976068053
    0xc0c1c0f111008060d0b0601031d030301212a03052b09060c060e03120a3204140f101a090603030a050a2d0921060504290103 55
    0x900c10000c2c2d0400b404945d07112488038107030307031580700700d1010450b95540c0040340184500654000d5804038004941c0d030300c000c044000c505a139041d00307010a040c03a01c401441c90300c10301118010035203403041d02460b50100f1845085403a0159402c0d00d80c03070741ca070790f6203580d880c004184a0711140d010228109459200e02400ca000c42e8032101d04081407004e180840c054600c0d05a0715002e08096142c9008000005d4203104891010760b00c07100007200c0c0c0c201900c4400080c0620004000c403005610048044010180034104440e1080200d000c0c03650381d182d03114030260f801d40da00380c0c4040c8140200d5140ca444180085411901c2c01c20f1b00069031304a0307071018078005200d1100a405007812000344a19070b240030080328209045401d1541d6070700b040c00002c842181d801000709001c0d10a0300e1034000e0042c0442c50720142d0301c00f95030712100166190944c4480010480164004000141e0190800500305420440d401030003a0301409082c1312170712800314080200c6556841d0421114014410421005e551 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 976070530 1250 976069280 976069309
    0xd020a120b01050f0f0717130603140103020111070305070605070b061002121b0a0c1d07051903060b07230c0a0504050c1b0c040c02030c0c1c0f11 64
    0x28451110030000182c098030454032154503c1c1340008180c241d0b108010304685c40070b94041e03081d60310045281070108440d002999100f203038210281c0001203881c4280925101405a01311030030141e442c560041d1104050070400081c140103946000010480c01d000140003800203840c0c8694030740c0c2d14500001409001040c1511900000300002c42c0c1a50010b500d11000a40c1d1000c1642d5400130000c2c4403510482620040780c6118812a0f00d0401543e1407446040300d50300e54400c4d040e41d420710f10260301498129004c04c000744061003412a0b1440480c0a2005081c250070700064440d120540c051190b0310001042e01c04944034900c0e050700742240b0046995441ca03880181106106401c000740c2c0001452140c14442d03901e80000c66000100e50301250520141c03488907140c21200c51143c0c0d500c452121410501c200e2505800304180d41c0040101c03450310300c1e800d003c1c0441d8040c1c9420800024107010340c0801024440c000303200000e041c0412074050a018500038000c20418004100750350054142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 976071780 1250 976070530 976070567
    0x30c03030f0d0509030423090906070e0108150303071b0605030f15040b1e040b030c0603040b07031509020315010507050c010828091203050c0f09030a080d020a 70
    0x71814400c108003907609400c0040d80c080303840d03203401544d1441d40c01190008a806640000700c050310442c1400c22070340c241c0741640e09150940d1150074668541500312191030120721046020049903100300c0803140d00c0783c5c0541c00d58621640040210b0b180d0703080b1120440d0342c24940d019985417811070101c15801001c00d07140030303403a5207004034640320300b040c01a14000c840d45c070707550500100356a641c10245540c40b0251500303040c0002d2000703007111010724045840c0030340d2130118109a10f080102e0f41a5041e00094401c91560b140c1c0d07691222408030003849001050b0303550480d054040301507000c00000380b101304005a120708156038040784007011102ca050502404110040004002258904400c142400c0c4492030366140008580c403040c0c030150100c2e80c80145032020181711600e91104030310303902641c40301140141d0200182c0c02c6032800c4d503074a00f2942e01440418010fa251030003d11103424050240c801e4440503a40e8008140c1141c1c4020703222030740108541c81c1c050b5220704410b480e01c202c42d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 976073030 1250 976071780 976071787
    0xf09150e0303071e03230a050c03130803060307081603030e010801321512010905070507140709050709080f011109040b0103110a05120c0310060c0303090510050105030c0303 76
    0x7400c03c050348019803200b054115130ba040868020f85c44444a0341c0d4004403481140e40b001d440c0f0040700c0c004c65820072914036040118032000540c03800e60f885030100c10301c08484109036458142280c3c00c0140082c2c2c0c18460f004021400b80e10504c101c8400c4210350f003003811498114980a00003141040d1110704208035400100100d03c5010b000c50003802d403102d030080809103d07000b0b80b0042c107d000a22a00210b4204142004110070303001003400500d40707030041c1403503600d40c4081419150241c0342e90000030300500090303021503408040481c0140c1d141044034616595a01030303805460341120440d0209590035403c002d003410900042220400840c0200545d407407190790098035028280801d030003659581500c10f071507406a40030200201420158a4a03980403141c010095401041041e00791005440440d10300c0c000f8006803401910180c161007032050600800f1114880d40280a408160b2101280e401042060003404804001c0b64004034582d07060200b0705240905440c0314502943c802c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 976074280 1250 976073030 976073041
    0x1209240e0d031406090a33140a05060901050c010e010605010f080613020306010e0d080705010b01091208030c07020607061b09060e0f0a17061005151c0f09150e0303 72
    0x5400613907000300116201031454503007100000040844d1200d04080d01d82c1300b8022403c2481303040041807600140d4075402c110548480700c003500140c082d17034290f0b0000000d88090081d03242490141501000601d0201e050814220255080d2028240c1c0e1042c980d642c0c01041c025540e02141e6100030804070304066600b41440c44c00304d20060f118050740c102e10f65000c0082081030b8850301224440110003003007001c1114060400384140e90000404403199071030003441c0095540a100c030601240c02c641c014450102068450b10810f900007400b40c40165800c0004d02d005075103c0014144141c0a04030005d5100b00c1c204003400a03244041c5010240000741400300807440d4802c101785c00c014000e4410300080d14602c008203420b542c1d160016860030741c41c1c2100660101002568a00c01c850012812420035074a205000c1001c006403103076400020b00300b0041c1c10803a811900d044c17030004c00d032000040e440d8841031a4001c640502008446a03018141c1d00e002d60369150099901012100010754510b0a00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 976075530 1250 976074280 976074311
    0xf0c0c280f1d18070303180e131106070204050414060c031012080c01020408030d0c091202100c0b0c09040b0301060e040209040305070c0e041406071209240e0d03 71
    0x2005103400324848400c0019044600000204010356071400483d000c254580c5000380051f80b6980c41650008034103003001406115000314640100e5004038411501201d1361a030801003c0c041d2200d54111004206000041c0c0315841007500c502d000b094a00c2100080386065030070458080c1c2302e003261107030500900651441c241d04036009c40340783c01d403058220a05864010764501800b003503800740303501c082070020385100d0100c0180045e4803a03031410006098122425100c154050141700101d4148400781070040c2040300c82c0c203840030a0790401545801030b680d210360b24620112840d00f034403440403800c0180c6041c039018894461404500138400942000c551156103100200007a1054401c0404541818001e80c1200ea00c21b40101c1039421094a0780500d03041d0b04001c2c3c800b00c1c2c090005c602400801c9102080b201d00800072a514209503008001307002002d0329020341d00703441c01c032402c21200b0003150042401008803c030038040450300022101c3c0490811560b040e417503040c1800c0000c3c0740404100e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 976076780 1250 976075530 976075559
    0x71a090607090b0703090305060a06170703080d0c2714041a0f011701030b19020c3409060e01080a030504060f05160b060306090c03030f0c0c280f 64
    0x2070f81034441d126030b04c600307045804d0401c1d503001816600595090118161241e0040c2c01600e40402c40030f03030005103154a0a80d241d0007840080e140a1091107154140005900000000a06890035461494680e040d80314903559144850300d000320401c40402490f001c501407104102000c84040103070903580341420105c0e0b805807140c03c2c480d0b00d2400c2602e12aa00941154511076039101c103107130315581c69103402c81404505954181038403c50710040c14800003a40220394000715500094140810b28040a1200340c4040d50620f40c0c11038146640c11480c2040d40760040100300860b00456000e18200c401c0d00151410b0700f1010741a00300500a0700440c0d0010b0440c0c04541385481c01010301616200308941d40d009840d1459000403c000d03988081c01002c0c403005000301c004405030340072601d40306002a654050400c1e1107405030402d01100c260240e044000c1d0007030400e100c065941550300f184c001500c956181c03542c10f0342c4032039280000032000904004000548900c00c4071905650034460b50303103680c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 976078030 1250 976076780 976076789
    0xe1207030b0601050c280b01030c0608151e03070902070803010e010f0f0b03070302040b040b070201021621060e0d090f05040c080f040f080c0c011b0201090b0a030e03071a09060709 79
    0x5440118107070000e40c9002086820750800c9030280d248d61a071070a440b10f1000d40c420000001c0820300422101c0881c5103001400b81801000714000c04140c100d241100c540342480240d250042c2c020006103121079000800c9a903124020301c540d2581400c189503074511041e000101103104001041c891078002e4400c0b00c09541000283d55102c0e07803007000c110003074800c60f0050715407150040350026003400f0402c06810440c0c401d80135203180c495001c03503c0e2840103040c481d920025038450718003c7c0d280c07500701c00be0110030300841c0701203501c07034a40c400145030190742000100010800d040402c000160506101d000d400d00329818070107001c500b800104201c01c090f00452010401401180070070040e0004142c2159000c1c0c000394032240e01c81480394642c0391001156020803808040c40240c0d2424001d4020003582c140c45650042d0f083c0349040b00d507034101601010905aa40c0d141d81e40c900070807c05080321503c40c00441a2100103010115001400500b00c000640d006506010030507401c100300e00e0554 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 976079136 1106 976078030 976078063
    0x19110f040b0a17030c070f05100c1203020c0f150106090918030c030221070c14010819111206040b061207050304030e1207030b0601050c 60
    0x444203002101e0788012400d10500c01c10002c030150420000f15a41142c0c1056080c0c550589403060507004450011805a01001103103010108040c4081e03c42ca491149a40c1c03950799040e10300703508810f03078090640100708080d44130810010400001003c0381110110310000c0c1007510005800e000b40c500140d4110f0020a1071840d41c000c580c502c842c00e08001b1000c1c10705450454100142d000d0072000c500680d44000f0308409000000b10b40241c980941d603658211030728181408981c582d015046e828036441e191502680c201035141d41c000c0e15400915610606440200020584a070402c401040c000c01c0c041070488995620620681d41690200021088202044114010416248400c41c45103000540651081c009150000e109041801c8008514000101c6150b0a5206c4440c41e50218204100f4070903080078190308500b086c02c10518202d00a000140c542c01803503501c2081 = true := by decide +kernel

theorem cover : BRFrame.Cov 975899280 976079136 := by
  have h0 := BRFrame.cov_init 975899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 975899280 ≤ n) (h2 : n < 976079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
