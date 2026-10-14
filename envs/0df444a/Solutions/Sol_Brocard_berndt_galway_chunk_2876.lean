-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2876
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:00:39.475832+00:00
-- url     : https://prove2.me/submissions/6bb61610-6932-482e-9106-53bf3252bbc2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 517086330 ≤ n < 517266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 517087580 1250 517086330 517086337
    0x303071109011502120a140f07060b030601050d060e0f0f0708060105060a080c0313060f090204050f0c03040b0403110307060b19030b010902070c05040504060501061115010504020d02121006030e03 86
    0x1c4903001044c21600785200d05d4929040308400da030402c0400c6a003c161804240090001d0740000d0000a458401502d03016003994100c031010f80c0650311510040000b03680b68194200300c1d1b42c00c0400000c03a902101c0b0708500700072003268007450900c00d590100c0404140058041c003100c83c2601540d170540d0f2298108041403241c00809400258614082078080b40120025508400041600c042c0364600e075403102c007a61000c81c560b407074031a9203840380820346c1000e00405a0001500041d001186040c078042c5040b400068030260146042c84001000c00d070241e40341908000103507048903214156407419a01400c60440c400d40500c0f42c405541048211364036207042580d84c03010000741507030b00300b5038140c00941183c402030355410303035107040060305455901c5224025405850b021035190706003480a42440c0c048512140d07680e019040415111a14962282c1565800c540c00b60351464a840120040d0040960648004003a4424840c860110509101c1152a192410f03c410f42c0725516090b101d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 517088830 1250 517087580 517087619
    0x3040515070e01050a20100f06080a0b06030a14030301150516140a141e030c030d0b0103021b0d020d051e0903070f06030b04060e071d0f030307110901 66
    0x4030381d100940450f6000398040d0040003403500d0604800b295107850000c400b43c4821203a905a004a0f4042c80301400a018154890038821014410f9915080506d42d50714a4014060000f100ba0408103190341d40038403074080b96982002c2c03d595060513486c0c002d0386075402885a0301c04c1d142d000c514a00750600a01c1501d9005961a4162461040d030342c0300c02c02000303440a0045101c1c020006000001404d580440c0c00840e2902c004080c418101403c0380710308034080600c01c19a030310500075181c0b07964000003106c07002840d818010403075441400041e0080d000d920020781040d1060800300e00810800120f81490281a81c2252031001004405846d06e100303998070605070780e40c032a907a82251048400208103240010707084895055888904081d482e805401110009458440406441c60b140c02000d001d005400c2400383d10341851180544603020342e440982030410824000e568660b0b40030040652a0303c0038058a50305c042d80d107460840b022482e40d40c1c1d41301da1010070010924120945c4603c1002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 517090080 1250 517088830 517088837
    0xb030c0a0b09090910110d050105150319090c030f02100e0a061b0203250b040b0d09050f01150906080303060603011806150c030809011e0b0105040e010b0304051507 72
    0x2140c0309050041143c0c0003080040244100f09401c2c10400c030604c6004ca2513000540a03c0e201c040541400055440c10b0b07014611030f4902c94140303c40070b2960b00481c0e8102c010034051864150446280c40094212000007410300c05d81c0600000900400d840710000543c801c60780d11048490b4107006540791422500000d4001130410000d00c802030003080c1300700011040070030165104c06158002880c100ca51000d130b45a4059141030075507403c0c540a01003000d0409c680c1180c0c102801e102d4034510f0303405082c1c201400790740c91b140200b0a100c0d081c04064241c4802c2c0303000340110048070407142c0f031160380c92060902080c51b20f80002110080070094074021800208410f245034a0024610480c1d20707100c00382020280e03102000502c031040c003050585103181c90b88032004484001c1c01d001d401c1800003880e984450741411a0030a0041038500e4043c80700c0d4560500040702050030004941c1030245801018049100d800081900010a80590f00c264854070444140368103107040400c0d07184054a041021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 517091330 1250 517090080 517090087
    0xd1116082802120106060f0c03080406050421050307020c030f0d05071703010303020c0f03060403020706260c0711060f030a02090409080a030b243a0b030c0a0b 70
    0x1110a81c40d0340d0880d00c85011200c0d26031038650b0009200c1518040b00540c03980c0d03544008020140e0081c1c251001c1c42c0305800e01403844e000584020344032100060004042c81d40e0ba4001600b0001d22040844841480e0307075800640407000741014101c2d03403095804501504c18100d030010140750015400c1e503042c0d407101c090b0101961301c240988403a00f040380e00722001031031403982a00b000c0c011005035001b140a58024002896154140040c006001c20041e0094000c41e0411001ca0f80004516045441c68a040103040403140c1103c1000d68012a44102801042040c0000c02110001406140d4054851030180c402d8000c100000c610903580700914003041440003034032401e6103601500e000e1401400c0400c001010f942c43d030039079030f11003410100405c2d9541201415030510000008403216284c1a814041040f6213200490703004502d048a920b03144000006c0d940010071208510504020151380d010a0460160340054103c41c40813a001e4401c0b2040040186454018101200c5412030b41a18 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 517092580 1250 517091330 517091353
    0x3061e030b060f1504150903121409030a05060103050c01081e061503010b070b0622020706020d05070c05010c0315090c1103130e01090605090f13050d111608 69
    0x241608002e2045901c031443c0070800b465500c0340031880b65048411600c945c1d449090007180c403125600103042404100b2000400c1c000101440402c442400940c24002460300140d0400c4a00e44030f159100340c2c040c0151032010040040c0004d1392416a0300c40d800741d07800c00084000446824400700c2d5581c84601103034951200300c000307540d0125000500502200102820000e031801c16030300c20380c0415094507001801805010507e04d01c43c1c1c1003c0101c0d40802003000c102c100400110812404080c0305a000920404020702541119241c0344410010302c00381c034154070040e00706050004151019400e29066070040340c0701c0d1140d000c0d50020420003422103070810722844020a50303441c03c24240103400300d0303816120a00b0005446216103060401e1405400c1101c10004c2d072206174040b80c0500c0c1003c0b8148010b030b445045075640a004014441110340e950480b000c03101000b488041c200f8021100d0258030141d00400340c40d00c0558000486140d00c141415040e200030241c8182103054000109010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 517093830 1250 517092580 517092593
    0xc060313020d0507030b010b090f10021f0209040603240b0306180a0c0e180606030a03050708071505060913020f040c231315051204020103060e0a050703061e03 70
    0x94450083e0308841102d81c9982e6402860002a0800040f1420201c1c0310116440e01c680e01782c0d1040c500392210080c80380210b80c00307541d90f4107111280d201482c2110303180c6801d0355907a05944035001c0040007031007103603a207040040c504148811404404480c40380740410762049800b03940002e0101030010b04866650781202c000c043c03036001e10720859014241d0b058001c0307200e4403058405000b07a108683c105080c10200007038507221020109555402035410005d8039907000c5110001e03d60903040003030f40c0c1d05483c64100410700c244400107000000d1100c1180c7e818890b64040d520ac1c2509481240c03050700e850b02c403454551065007001350b01c142c00f90350002c5142490b4001507000764240c10145103240c01c0012210000b4500418032240304408141c81d11010000d04106000300382e40f44155502c4804a4002446881100001001d0410309004181164821342c004401011200100162070138000d04200140c081036503810b0009003455008910b04c2d1030a5003014040d64101044599580b40d0364420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 517095080 1250 517093830 517093849
    0xd030c0509040f060806090d02120a050f120402010305011202210c0a140a09020a02030d0908040e0a091209060e010c0f02061b120a050406030f0b040612050c06031302 73
    0x8040040500c511030076030b00c1d9401202d0200c0d44060001c100300e814910750a180c000024845440790744150310f076000c1d0035001701d000540354092800c01952000609029102d030711034030f0380c01211000300290200704840e03681041400f40380701741d038180603903603842010140c54410104060b611900d1030315212080c9110440041d100c01980d4181e86004240c5000144403244a41c040710b10320b400f66220315218680f01c0e5910028100310b200842c2860001c0d480259a8001d01c108520300540ea41c402d0300074842c0081c01c0d140104440c00a64007640340048098019140005007180c81d04092051520118090b140d40001d50781195a02c0030f80320948c100465000b2110316090316a02c2001a143c40583c031074030700420001c406000595072114881051a107030901e080c4d02990f11120a0004c1900d29510104441c2154094900810f9003407034148018001c1c9070200455900c14030382140081e07541d03101c4542e420303a103008406491100c0c100a0510a0301e02c0304035514088118017200c82d100610300300442 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 517096330 1250 517095080 517095101
    0x50105030a090209011205061806130f050102031014030a110d110402030c0a120c08040b0405011404050106060e01030902060f07080408060708011502031c051b0708040501020610080d03 81
    0x1c030b40c1c0c1d011034000c50003201c400e800ca41d00c240c00c0f591203241400000c00000380c02000002c00c40030011f002004154407000d01034042074440c0d030a032804c0401c3c4a200d050200075a90800003c655a0030010442600501c5070b1203049414464264048241e00e00401c8a045290b00a0814203001d074401c001c21a000c140c1901c1114507402c8201c0c0b0f00c0282d01c551016500c1048107044d101e5413220300302c0000c3c0c055055423120300f1000f8106015800100c0e40031f95110b4015a01c414542210b44441c034040e03026000354180b40b40400039580800c0240441500a281101c04940350142295400b000440039900c80220107500308504002c06085031119500404c802030103200e005007010340300e003102d42c03e00d001136030a800060100f030014022440036002465a1302c0d0240020340c5812402d5015403100c0e18910000f080b000c0d51400060000703061841c1000b20310b040c0120f038079920f003a07070714001c2c42642007070090701c3c01031103030380001352010460114107810395405030014140501401d00460140c4043e499 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 517097580 1250 517096330 517096351
    0x3030a0e1c2103110a0509091510020a15060b040317040e01060801030c1d04121e021509010509031b0a0b0a201617090306041a0a06030c05010503 64
    0x1c5100071550381c01d8805002202842c51428998070000020107030794281e40714580e07095081108143c005c5e0050200c03403051034103039090030b055900c003164503441d40000d460030394015513121001d03007145a011401858203449007007403029020320f220520307007240d480d4000e800b0f58107010441413011032030315000c0f41101501104068034040c0c5490304211414001c1e405440400d5108006000f040340e040d2403a0090542240d80030390354004580c1d000c04640000e0805031031014019205001d040c401c240d40002a42d900e600e13646800040400213590722100b4414210f12520100030411300b9406008203800f8800702c0c4c1c001e50400ba081c8652410101003210040814400c1c102d20390001402d01128501ca00700710f1000103180828180f040c4a400002d101c100044541040204a940c2c4070f0004000c0341a00318140c000c96036039086451140d84540d203804ca51512404080008010517124680501f00c800d501004c3c49889043c414400e96000313000040280302c11510611280d4480c0000d10b5101d2070400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 517098830 1250 517097580 517097629
    0x90a09050d05091c020a08120310091a061b01060b0d05151518220509060f0109020a030e061005150f18011206030501020309160e01030b0402060c161403030a0e 70
    0x162031608e081225514089046004000c124005000e1800c08009152080c0c040c404840c503c0000c502551502d40041d01c00c900129444600704402441c08072a0744041c0001c1140684402d51401150085003d500202d402c00c0c00051104805160b003040c400d40c00b6006140c40c0c11140d400000c07540005e640c9050a45807030780003500030740c1d40501010700f05079a04060344001082c2e142542c15540000c000030200d5200c1414010b0740440c0c40c980d2411195078080042c0c541503181812800b400c0010f0810285109020500044c0e60b203e00c035100c121803044640040b45c42400491200ca40075010030441c4008092000c0c1c43c01104818110b58030000501d810480424502c0c42401100d200c1e07001030300c03c0ea501008100c41040c040020000c503110040d5604000313803074504124075a910500000f012421100003180c21511624281c80d00481c82c001920400d0040d500e010644684900c1400700800c1c18540003403c5007004006c5951841a0783c0d5400c040c0d40701e400034040d1030704c044001e90040700302d0407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 517100080 1250 517098830 517098839
    0x28091104020a0c06050f01060f020d0e011823031c08060d0609050a060c090b0903070524070f0312050c16020a09020d05010e090102091309030e090a09050d05091c020a 73
    0x10710031607220f80c6c0000264030b0700754107191005203069081c002d0b00041d90700000307811455036040b074444920030b05c0900e880061250100c0701c2c640d41e4002a80300c0342300040110040f034000c503481040c030525003509030200e0784141e51300e141c00c82040000384030880110304000c0c0401c0c954207182454000c0c043c019580402d00f4031a51361418501b03c1d83c0c1d2000c0d282e050340c40c2d0100c544d180e0301800301001445002003070303801c00f055000060780b00c0b0410321805115841200b100d0f60340c1d81c0c08401000e00b40654916281d204c1c0780c1c2d81030204151580700c134210000740381c40400c2c2840c0a0a03104880c06045850711541c00d11801503c103580d1400039007416680320020300d00005a00195000804009074202004159945045034003000701d48061b11900700c69005006906076510307480d00c12840d16804580210301c0780b40a0806031114801070301c2040c0c1014295007000001c24203504503c0c2c0651040c001c9603902d8640c00c07401c81d80e44c05031a85007a40800042100b04802c4c824183c07400105000514280c2040d640c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 517101330 1250 517100080 517100093
    0x5031e042102100605040606050909151906030c020105101214010e03120f01030503070305030c070c120323180411070c0326090402030a1428091104020a0c 68
    0x24641d10300050303000c1c5403d49402141030041c50014041501c0900c4000e080c200b000c0c1440c02550100340c080c140010000305042c807104541d10040202030520a41001d62140300c803e13000140c0100404030f0308080c150108944144560340c80740d40d1180a850b8160300f0f0200208001c1d01d0500705845245d010801c21741380d034800380320322070003100000c0080d80d98035689403e028400400500c207a24081982c40100080360b4003208881e04540e06283c06e41e566610420500300c58050034401400191070244045081055800101100f80c040c0d2039040182c544003100b210050006103d80c0d103905400d001c40240242100321894444000500204505807408440390a54100d044c054132098440c03602007003405050f04542c031000490140e20029081d00f545032022520415030803500469002000441c216205d9200b004492014902100c19080c0502a13800b40c2c1038488222102a0507420300d0603500d8980e11070941d050b6841860a0100080780041100a400542da5201400445202c00d0001030300c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 517102580 1250 517101330 517101383
    0x20c0601091a010c050a1b0b0f0d110c100515090a14060303130e06011b11040c0c150203070309210813020d0f051f09060c05031e04 58
    0x485150024840e06298400d21001d5030341115207040c8800321380d12101240010400340e501e6900403005802d9680d40c0c00600d400e8160681c0400d6426201054400040e41308074001c208a815400c0144181101d01d4000c0724540300301303140000650f03c425041050040c1c5508080d07031012918000f91108115903001c03c2132803d0459002400954400800c0c40861001e8401500004103400446c20300c04441040004c1c80f440e8003071841018200300004106078452290042090b4111603c407001d4405071400d8033703005043d508464855030526144000031442000c0b1070706601d07000100c0c100c50010140c1407070f00075403010707049008060f2129205404030381071840582c21340800b18201d05010b000a40c0003001503602411440310b61090404580150381d41c003100324000d41d0840807074900c0603020b00d1302c103260403521056850005140c1502c60a50300c2035600540481e40545020301c0000b00510701118140b00480e8412000710841c1d00c000141c0740c4d03160030341c0d50040c418281c41e80b0314255502c800e0a9580d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 517103830 1250 517102580 517102589
    0xa0c061b0c0501150b0304140a0807030e01020d08090a0809030f0f03070506010506040321200106080c0306010303090b0a03020f0f0a031d060a1109040929070e13020c0601 75
    0xe0401c9018020080248107469080001c4000e10300c2c4241000001a42e500c00580054194454100ca0481614062007145812039004440941d264902d190203003100c50014140c6000d80500b041540280b40100051442122600058000c40c1c3e640d58901c803054000e0401690141700b0b0241c0e0328038100c1d04100250803098404001d645800caa4a04107140c190140c100c2c5000c2d0809020400000d04c951460034150a9442441004000851400c030703203403402290300403955400d014001c2d5400c2819840007083c1d400780001e0354443c14152041c0359585800f844000e0014030341d06030410030010400c001c6c09000c111854058900800b44445900c1ca400040044003020800140d401005401d4030800420003c0d4030400912072311151500d0b6180c450040007080c0350760b107940d94820350081c40022683c886c40c00078010080302c0b502c0e040410001080b1030f445690546000c0c088400c1004000200707110340c6655441d612991001818030401001080344004c1068090206406800d028000305002c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 517105080 1250 517103830 517103837
    0x40b09221403160c0f050a031707020a0b031e0c030703090201180e070806031605100905031203010314060103200a09020307020a0203160b0904020f040308030c070b010512030a0c061b 80
    0xc00d10b0304140d813450706654480e08034140c4810003042903850b543d031440f0407a074101c08036440c00d40500340d1000c918420104025440b1003105400b281c0301f4540720155010b03250b091b03c07109501c0c840307405107280f00c0d0041d54250000b240c1800040c612911a4004002035413040c980914440245400140e11080750f0f0050034a00d5120707420410301d0343d03114807600c0d81310000324018150030692100d041058116400b68034007451a11584050041c020380301e2000501014040301e00611116100c1c15440c0c00c280012942c03d44440c42c90b480402000500a050704e8111218005406520f00380750310030810b00902d40d42250b54240000780800061014501c07411440d0064442d42c100ca204260800700181300740503001c40c0d081d0060120750580026915926002e8900580c0c680300c40029080034011584000e0411070000100221800c80c080508045881070301c00c40000e980b120100b0000281c0c0294031a00c40d4401c0c8000d60029229860304c0600c503001c1c40300011060000c0782e45420240e084446100032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 517106330 1250 517105080 517105117
    0x503150f130f030e01021f0504061a031f09120e0a05010305010b040504050a06150f12050c031528170c0603060d03021515040b09221403 60
    0xd054021420581c4025040d4540c4450641591100302502e54110060f00f08108062920031590007004207810801402d0380c480c0c0e601002c00c40400c042d050031a000ca6510307041000040044200202070041a0401006403000902402148485030050700100c2c54041e01c400d034010106051781e8032041030204a43d11168440c4014085c441c0a800e0b43e44490b04143c80c0c400104010a4030206030350a5480c1201e021030740b500c4254a8a014000c2c6400c400d2100342024461054550440d20360f0380901000e4665200c00110440407000311101103440c4036000c1d03410800208620400d152000403144010407100011011108000d091605801e001044205081043c030210311074080111456a559008042c00150304e000b09010340000b5141c0d40c01396400703000c1001014000c0c040034030903400310b050f02c92052078080704070804a9440758400b40928682886041701d4209003800701d01c92403038485010407a86051007038159129184c03009075806817080d1555043c4442c144001c02c90300310b03801d548006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 517107580 1250 517106330 517106341
    0x41e030b0a2a05041214030f040e0c0c07090902011107090608010f0204050a060c2607020f03010c0206150a0b120a060e040b0a090c050913050607141207030204050315 73
    0x4144800086076000030342a912114965540032080b101130310a81c0d5175480c00900c451601503020700450210100c00e001c0811007185407c5060054011034503a0a44109552281e203070b0f81c1814440e20140c0c804a401c5070009115006041d04410a00e82c8185000e81d50105044840d030f003041d12907040055415112602000604424000e01004a4010004524061820000a2221403241b045100b4000040c038070a041c090421004042414400001c000d80920100c900540354000007040b071040c840c03c0c40c8200541014070610f00c10841c00e80040c050380e2a2074100e06070300050845001c0e48141644001b081041d8403401a0400f400c4900c000c407070a08200600c5420348640360841018180d40000b000082104501c034290083c01300380d00012007200c00d0509454102003070f00500c0e0042036807028031402c810300d02e800340041030207035040e110161501d0310212010440c000c01380558403424082c88288001101c000358200d902414010b16095aa038046800d20070048030981c1340301ca52804102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 517108830 1250 517107580 517107611
    0x101e0504020a0c02013b03010209091e070f1d041107081b0307020604181503030c1b0f0611030405040501121e0807060216140f010e03090105041e030b0a 67
    0x89804110408514030840a01c02034030030301260510010590f103946c001e0010b460a504903101c000015100054030300d004118111384001a000c0c26141c6205040060703280c2b407042c05042100c0d80e03140d4480402d40e03200c2c0040800040d0100840f54019601c0303018048401c616070061400f244240f0445071074000e070f00d0480038180100d800c01e03105504100101c1c0c0050380c42404440070b56002e010940381f103508103841c4200900054200100301c186610010040c150004c085400091140103120b00d560701103042c1c070012411501c141d02e10345400e100148510f80c090031038680205400811641402d6407000001c058460a1344401c0130700c0c101700748000a220080000d08400c6500d0a098080b40da81562041110300c189000a040c0a80c0400d000a001c4230846000c040c0c41c0e003040e20400b02c1d074080008192607000c0812108582d41c41c1c051011304041021042c3c40304028142c4540e410a07182c00000c04405c211140208400c02c42c0358000700004403410310060180c042007100140d890741c003c0490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 517110080 1250 517108830 517108847
    0x81e15030f01060b3f15181501120c0f02120310050904060b031b04060504090c12140f010c171b0c030c060a050717101e0504020a0c0201 60
    0x1809030f41070110030702800c0ca0305400c0f035403042d1140c564101075072100c80c8030741c9001d098a1201c03281c0e18540000c02c1000c10a80e50380e18000c80c4600406907540040c0d9082043c4c0460303105d10030580d9044240016403c41c868101700d80d00e408117043c406003030420003103410300300d640c012003c1011650b041600010710b0fa0401109a4215000d40103610314101042d500c5142c1070144203043c4070300003d000017020401107400c0040c07400406801c9648944000343c200500000780b00109028901c0e2210010f86031410340201442141c2101d05081000c1c1406124259038030046404c0d911802800394959101a08204070440b15000400001740445101c1c00200142d03034400100c03400a41110070b2244007901d240900c0b01800d0141070b0542d480c07072920340c0d460a501403500c001e4903d028031006c000c0c0b0803980c0d401c12881200980d44200307891412211f10403481c6400d64800103030036402c0700d0031b1098518950111050001c040c203400135950355840007070160b902c143c030301000080180040408650300b15209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 517111330 1250 517110080 517110103
    0x70206070908060f0c19030c120b091305070f0f0801051608150111010f0605040e01020301080a083403030b0f01050702040906231803030601050901081e1503 69
    0x84840c940b400c074880e039030b90704080c180042c449102d01c0420b415001304030072206600b11150300101040d1012401070010528990210301041c0c00c04100780b0000c501c0d10505400d80001058401c0c192a041100303103001c06034440403074040c4201c46003c5408910b8100c914010324a0040820007142800c4030305083d500027406550999095008040485400205007644992820f12070700b00c8541410048031050a03a9101030039035444d200d031b20b040510b0150420410b45805031400d2041c91070b2401064200c0c03009216164407500881504030000c1c2c5e103040148100010308580c0c1041c003801e42201c144c5885000b1034a14040c2c030b00d912500405805004512406078101c5408011038a0080043c0c058418104000e128503550b5102004010703440d03025030001c4103072040c039042445515208000b12801070f10364060444103024076a00800c2c4c00401c0720f00c0f48206130344c0e2504022000005441256000d001e80d4606207201a4102d400c040003004144507551144520000d1044002030600f4a8580d401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 517112580 1250 517111330 517111337
    0x10b12093004050a3b070c05011413060b090603030f0c0f010219030b0a08120a02010e070b071a0103080706020702010e10030c030b01050c030708091f0309060c0c0b0a020d090b0f07020607 82
    0xa000d0b041c22495846d400281d6081101045180307190140c0100702c40c80c0781480503000c49081c00749100e42183d400d80d09511950041211050a0b001c0010403441250082e03403580c0100101000000c10401506941c0980000c40c0c07403010f2081504c9081e600b0031110400782c1c60103e4a040003c5915001e101d104100a4440c0b02c140340c101040d02d0340700d0b0020035400c01000030010712100318902c00d6101c40c0d5020401300540700607907201e101401740359010300d00c141c2d000b0394145c80c03d2502800c0440880d040fa54480400c07840c201d400d90f10080a07410020050b418030080d00a2600d15859010109560a0142c0d0300010440d92121b00501100e0b40001030604001c0d060103034030340b000000400c40c0d00342508004015180c030960780005160014a14522800489124101005a803d50003481101d84034181c14003540d502000101c8041071442c070701620b90010f07500803c0b070b050102e500401010309034510204900c0c1d03164807290300048054406282e0a09a031040004180c0e05020203a0004014a03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 517113830 1250 517112580 517112669
    0x1308010b1302130603111201141801120611160f02120102180d050c06040b041d040f0605040804050d0b15180411030c09010b12093004050a 61
    0x1c000f01c60a2409005820a155840d01c200c1400048001070340c046105503035130942250f03164406040d02c5544000414007031440314440041c068122160326050f12106107841c141d82041e81c9405c0d001d0101045094640441000328604501d05000c080640a001e04038003c0e501b07142d03106001d4207560380d80780f910340f50b441070140c2c1410740c1a4a65546000c5000c690002010b40c503814564145501d1041c01a03021740b00090000318041000d015100326500c2113005904000d500700100c3d01c1d0141180c000300881c0340140d0b003400003941c84d88882d401c940a0b02c0d100d81440d0310342c004a103584900c900103595054402d42001f851084008643c0da204106440844480d128900a00d8003860054001045210348820035401070f1020448507085000c001e140070030559640011151a50080c2c1246101c10461000680504e90000311001e80e44a0140b00c18416202c1014110041403040202080900d00300070000d050f0392400441d1001d002403038100f22107040868440c00c205146903486018545419 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 517115080 1250 517113830 517113847
    0x60105010c08030901021204030c050d0e30070602070f151b060b0603070507110904020303040b0d020d0c051c0b0f06091306080d02070614090f01051308010b1302 71
    0x74034001c205a0002c0c1e081e80f40c1d15088165406070090a0301d0b5404c031110b0104000030705034043c0c0820402c0e8014000d40c2d10381c400c0a8030440743e40004460701c0e900480c0b00c108503400a5540940780d0400b1800c059140005200c025100781002c61a503c0070300143d100e1030090281e0039050000e0001807141c284480225030001c074000e03120000040d400764481e8520140340c014402160444030340c2d84001045559030780b030103400160450b00401c1c81529102c0203040090000c5c20040c0d103180c001d5400800030350030300740b9042c4c8051540c0e015000ca118225028403845080080c20702460961860649900f6140c0c2030292507410b00c0c030350000c0505625810024550600d8861244c1c0d4101c0031002d881c80c9941d0072020011904201c3c1c0003130801542450084005955040800c050071445099429a203a40366154011110500c168014440b40041000358600c1c510b4038403660840050181041d500702130001416908070816a4031100c1143d440d1100310155240c042c2d0281030360042444210b0812128 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 517116330 1250 517115080 517115087
    0xc050d0e06061e0a0b0304060516020f15060f0603010906090c140a030207060b130b010906111b03191208060a0e0f06120703050c04050a0903080c031906080607020f06010501 76
    0x18191810f89882c85251001d55621940e001c0005010b000411a036a81010701d001c1d8010501141c5100320440c0c0e8500b242e0782e1a2000c0340c1c824180449c2401011308001c010305901c10280d0103003020741d10007000c80002e00280c035007101444c000c2c55242c0d00040c17502c1c941840901520130140d890420040c10344403a130310844513041516040708040c1b030011385072900b46ca01180100503442c0c5050344031110a40501012400d03412800e5440d00c2a84ca06800315a200c00650f000b644d20043d40c0c416030082005202070031140f024440281d003000b001c5030584112110100d520680021080d035410105020311202c260300035905c0c5400220545030b045080d4034054206c01400030240280741c001c0358101c04150741c0e40d51460b4074000b099514007900d012681e0380c030b440c80d030b5400030403c000d020307a040c840011040001031246949041c1c03d615a10f000343e0340d1441d0407840d540000d15544202480c03008010681c4218030605000d032529100611642c181100c000e0303c1c0c20b022888055060344030500510035641d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 517117580 1250 517116330 517116349
    0x1a061305040c0f090b0f0a05060d05090c040c180503030a050a031a03070b12011d04080c150a1d070602030901140409110307091e060c0302010b03010c050d0e0606 71
    0x4528100041603201c519100503035030070070340c0300320b4841c214800e02140e481000d902a101800041341d22400c807015800501c1002881403046035440750f02844003031559480c81e003000e64800c6c0d992040d147c06a81c0c0c000006c044503001480c180005d810303001c50200c205800c04c085809400704400a41c1007103200c68004055114080c03000c4100b680b100700c088264075002038400c7e850880107080d1049142c440e005042140c02c07900344641c601003403000014155001ca00d0b01103c02c161456400180d035210f031a4402d2950204a40480c00d100f4a44c10181558840c2d10160050a541c240801c004201307128016944443c540e0741001b5400003001040581e400004445944500b030030a440400040210702c160360113036601034011581090802440c55582100862240f000794542c900c010b85c484040703600c40c030b070b458881c1002c0201d12102441002d0080c06440e58081c400d10010800502c0c80c404203094507c0703031a1075170129102040c62088440e1030700660707801540351802440340e031030080d0003d4600030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 517118830 1250 517117580 517117609
    0x21051b040e070e0d020a080f010b0a050303040b0913050a050114061215060409090b01080f0f06060103090f0f050f060a090309050f010c0c080d120903050a1107050307060c1a06 77
    0xf44924110708251648000000403540042c0703045072095440e0a001e44808a0040901c459441c01205010b940b0b04115080309544010b4001c506050a00d001c02c59142d00003038120341c0c1b00903581ca4050b610380050207141d105003185500070a5a500d0141264020135400c0e8441d0300c2800705100ba0140301e5250b440c850b41c40313805418105000303010390002c22075078480d07600b1020a41d401c1080380400c1c898034450a5040380d0701c1d1412618918054a201a103848158020241c0c0d0740050003c2102c1d51f110742c01021509000e10f201c800a00c0450340c5158400d55441d5007110250803a000c50441540140011988940c8501003030110b4081980e001b0443c695070700650b071041010b1014001a40d2103000c40c0c284480e400303048074010740d03100d04440b542c510070001c16800003000c0081c8040042c42c2c078000c071079105900d034441074180385901005540c041c0e000d04110402d407240960020b80c50750104803290060035192900030500c0040d003060a501d141c0c940500700380803203804c180070343d80d10b6882e94030794080e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 517120080 1250 517118830 517118837
    0x103060b0d0b01030b04020d090b070e01021e2a0f011d04020d0e250510090e042a1703161e120e1f080601030c21051b040e07 55
    0x10180e02c4016401032019001031600284040741c0d9203111500c980c0161411800b5142c510020b5a64180465000308c070044201e00503005010404031600840c0e4108100c200d0900a8a407049140d18040701f10040791914801c0c1d4071100c13102d405550400d00c4507890003803001c0c0380c0354048064400040d07000707000d103086141c01950300040009207e181d40c2d102c60980b42d1880107469244c0001d041e00f01418145404400510884d0307040042d0380d28003c0141401c00304180c4503542e8031854064200882c20000f401a0b810349a10441c0c0c1100808004a101d00b1086050150158a003440f41c1a014030407420705000090b4420056801d0585854000f1b40d503895102c0b100c0b0f41c90041058508a072040484001012030102d0304040d0041c41d00100c00e44408503050318640c51010242c140d40c5110102144010f0100c0c51007804036065522a0b08007078860000f90600742205800c240342c0c14520a20010360200f055524800d1003c840700000c0c486071804614042182050304010000f061980d01400b8801031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 517121330 1250 517120080 517120091
    0x270e010b0604211a0f07050a080a051e070809010b010908071203051207120b010c0f080c011e0b1804050712060e100906061a120c040e09010f0b0103060b0d 68
    0x7011885460440320320703880003040400306a280598070b10003000b505ca000e480780c8554001030006100700180d84400c1510395070f124403901d0b000c070490000c24010349001c48802201590011600d4a800d4103401010b042ea078100c91884c058050f20b08503122000000c2c10042881c0f01006400780004480c13043e0b44010f0300320f112003826860103903094030460f4145c0e40d6000000c0100722080340c0044407100a8a019441448400c1c80e40c001190342d40c013602402483c0984045c0d425000c0384441e00a805c0c494481800007500080c0d005000300c0c0324042da681c410504c1c1c4c82310341107242c60030002903160703601c4001a05065541400e5a031280c4403800c1e4041c1c191611105807a29051148980200400080c01c509440194940c2d42d00362020344800701d01980d18a0505d003000800308041c9c0788a100d43c01000c9681d1303041c49012640c0c401142009011070303400c10418003010030742d8808100304600440d591000011b100080c071584805464032001c50905240c80c081d400c0095440c00e40442d106440c3d040000100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 517122580 1250 517121330 517121369
    0xa03031d0a0f060503040303051e0a050606090a090b181b0904021e070b090c010f050f0d050916141f020a2901050d08070318270e010b0604 61
    0x92146070340c1d00000601110100c0081e015070040d000f10f00aa010781d070140415501c401c482c00000300d034940d45031041c04000000940109440d80420f8100300020a41480d000007440060301000301c1d60030485410b0f81c0d5031044a000c0c81c2940c1c07000c0484503e0340e03000c0b520780350100034648000e80d01940d01c1a4072100081010255a0307580c120740c00d5100070001004404644420000b1a8102883c100d0300350740311300089008820300080000ba45030341690b51955050080308200c2e81600503500d142c80781902840980d170340300c540e030041e188a400120300500c0959181c03031945522110380c0c3e10030464015034100140c060b403501c80700e00d40d503280301034107144200620100c124640f0120100c003400010280701d40003864240026080030343c44114006020700d03600c0307504000d109500310400411005042292600082c002d0088100c10034240450740c3c03038166102040c1c16810030300703a400d001c420002080303001d1803031f40d0b84a0500c078001500001c0000c0803070b50002c40d04910130703030180503201c520780d400580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 517123830 1250 517122580 517122589
    0x60e04050c19030b0403050306030f070b0306010c0303060e0a0209030d090e040b060117070e0109091a2b060212010e04330603080d0c020a0c151b0308070e0a03031d 72
    0xc503030140200b1201d1800c6c2c2801131a640060329514460300420000a24240d030008600060300c3d600c19285145882da00010b40b522a240001141855100c0100040304250051350501c518001e60340581d460700384500b014148010555090188080c1c54424000d40c0d0810f07a40c95402076000e012801942c640c1e40050303403040e11a01159441440d030904000303225078800140c0d0716038402a02c607484083d45071044682a07515400d2360790411841c01007808000e20b010030322420071000c0346070207401c80740094480051088883c1c0094681c2c0c2d80000c1e0002130340028042407801071045e13817101c442c2410655107041c0b0f10038200052034a100c2800e07101d601b401d90402d81074019500115020096107542e03190010030382c0c00880f254030710340b0b15003d401e0007031500201e13140741d009601898603102c2c82e0801018082d21280c640500c801c1001c5203844540c0421800e22180d1490b00a0301c54065500d00400018a29122200c0d203c0c0503003a018010030020782c002d5400080110100b40c80d4030780307010080105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 517125080 1250 517123830 517123879
    0x40915030c0b0a05072909070317091801090b010801091e0b0f040e0a050d020d0503130303150611060114030a140111120a110a0c061a0a08010609060e04050c 69
    0x9810304020b42c0e0641c6c805007107900d030380e00703003440c0c002d00300e480c0b81d0300e00c5800c1d5103c10240c4400f0307010310288034680150b00010b9005001c140b100805d0341d0580410801e529140d241d090700504001030b41c82000840d03641c1c00009090061400000500030f0b01c944517803840c1c101c03800c0302640780c0b11a1244032150721070f07480300005040032030068020442484a8902c0541d2100a030900755400e01035810031007126417012404140040890300c030246140c866650748804540d400d80305604140d80d50000341c080721141201c2000504803070f99140025203200d03545901300001a8401c0341c41c806044680800d0341c80c003040800c030241e0440404947ca0241d91541c0b8094004c440d0740a440305000a103110309081d05404d401d0088440f0311042005840ca41498001e61040c41c070000d000c176625010b51000a151508140d1022800c0c0c078415800559000120301d040b60309070440b401a035141c85003072000d48039600c203440040c03001c0b1f02c4a1086092540b6095126000164068007031504080c56580b25000240e40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 517126330 1250 517125080 517125083
    0x60902031209091e01053c0102010b0a0828021305071704020a0e1e09010617160e06061b01140601181502010b1203040915030c0b0a0507 60
    0x241d640481c0022490303815a4040c0d440c1da88a25800c4012032044020540c4e00500c11100d0102814503034205003c00030221500406c101d0400a130390f411407840541451246072043c40d603050f100c000e00c0da030300c000380c2921000c00d110341c080d0403c0c00042280301d000050101360b08180502010340b22110180903500c0038403496020350444c0c00149291140d00c03c80d0f0002c1c0c45080180d880d000c80c61003001c420a44400c0c140c0300a54007828007031090010561044203250010710492415449a61412026182d4101100c1d41c400076507460713504000c0340402c8515007200c01140e201820404d00c0c00d441d40c00d080102d5000d1041e030b480381040081d81c96124181101c000840c0b00045418052114040d640071740031a1b1002079141c5440c00c00b28045500500040e07543c2040340400c010b0150800c1080b02c3d020f103490720041c1c110b6403281400103250303c59013840d0303d40d080a000516503942c2840880340c299201310600240300b0503403a50070400b040d1880b1031181039980c00d103070082d40d4444001e0100e405001d031440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 517127580 1250 517126330 517126333
    0x1005100c06020c03040303030b060a0c03080618092a0a0306020f040302280f0617040501060f03061506020c2110050114010e040e03040512120a02030a020f0a021302030406090203 78
    0xf481401d00f000000900101c030321030394080c0700003080c0800f41b01c0b2034045c0380c0919012038052001100000d000f1105198850005800003032648a440701c0034020790026031f0914100c5c2c102c140c00c00100810892010702d41350700240d05032144031240c00450300403104d071300c400381819a000c14103102403822a4212001035800400c442c99880b802c1e4500e035084817030544650800c0f26400c100084581d0144010012101035442e91a00720101da0f20881104200610868082d503a403180410440000c003160b0018502507600001c10f000000e41140c884d400c15000401558030802d06d0484c15030300c0440b044140b210700c3c1072071040040034510b01c0349440315564079206030a081c140046102d135002d403c8882e070740f03000b40e0780c2d0030a5104242c14001101e901101c07800464004100600690400c885208480c0c01040101c45195404180008003034002014203030050300300103a500f62107a4101329000c500302020010701518029540058042c7e6060303446c0340040c40e000700004090024550000c0c400f59009030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 517128830 1250 517127580 517127587
    0x70e0a0e011128050306060702040b060a0e040e0604230c0a030317340e030d0903051e0601090c120e0709060e15090408131203090e1005100c0602 64
    0x8604015503000038810b402000740b4400f0300c1c4002c0340d4007140020b0b00a4140c80b16403a688a0384140710003903204400980c1c1242e110b00f880e901940f070320070041c1017604080c0d0300ea003844a114801c11056070302840ba00032103680148144000300340350f0400340c13601503007060701941d000c0100000507040102c1510301540c0403016440020506800100c0e0050150920030428810742d140c02d0182801603d141031000700c00f05c02400c00d0407100300080d280300508424285258008015000289400d400102410005042440c2042040020040007035503070020342034010b0703250302d528199075a04014440c02281c21b80721140c52240e00d0041c0b44401520030300340b2041c0541d04c080100c0303c0d0b07642414030819a1a6152080000c2c900c0b2507001298000c000200b070a0b56503407484810030401c000c0281c4169000241000000009008088500000c0c05503115015014009080281000800707505c401d420201030780c20010342e166500403020603500c1c225100e8a041c501d0002c100c48010b003a0390014402032001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 517130080 1250 517128830 517128851
    0x118020f0a0819150f1d15040b091306051605070f02040605060a030e06160c3306051509010c0620121803070f0624140906010201050108070e0a0e01 65
    0x1021340990b040140000c403001d0b520f011001d030244014000d07010740302d200408074404620320500030a41d204002c0c0041103120801000652a800541e08a0742d40d20040c00040100720103070007900d80c00018000c03105003841206201926034070559000501c040c2c0082d40c014110350b155801036014207009002140c50342d00341232014000388501c204040262291100142c0c4000c80e12580119040035592000d8010015964488a590174000402c0c1090710002d8021824950f481d0202e0311102e0044011448600d8441848a00e08550541c5010440b040249021b541d0700314030281b05803076000b00700156203600030107000e141ca0310b014480d038001500050103140303050f4805420350107004583d81803000e500b16083e0440d501e1052006c01050295110040404074150f603020607019000c5c42c0042c03006418000c00c40d41c0c001199040406c1d48149000c0c84682e50074a81e44069000200f80001c010ba94100129190340d82c0c550b105001c800fa031a0303400515070410b250400184400160001d00550165 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 517131330 1250 517130080 517130111
    0xa0b0c0d09080307030516021e01020912160504051509090a0501020a031508070f0b03092d06280e1507020c090f160e010302070507030b0118020f0a0819 67
    0x2135030701c1c400007420840440e2000d0300d00500c40d040464503800074008002a00391800c40b807440c0d8051900301d0756080c020801c01e611544d03500e1ba0300d070503890041e0120360000d02d90030700e00740c03403136040341c0e024600e03000c204107500303408802d0000c900000b107a04025a95511345154a0250b807080f0050a9500120744403400e01d402d6000120600040060900d00680706e5282c203584a40e288102a44801556010080b128110000319004031140042d519149500c01c2c1014807480924140e8051400c41201120481c86c14011035810401456814090340c1c50ba039580c019441c030910103501501d0b03542ca4803200c1c2000c01c0041040103460368545200c107240684c40039440320002c06c83d807070054881000164442e1030468546228890b500241480600c40240494166616002150605900308142c00c003191040200750300451240300709940c46c1d03060100509003560801640e0100310300502101d441c0b0350b001e505443e1200994a484400c6513a070307148030130040d041d014080f54030a00e40000740024600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 517132580 1250 517131330 517131337
    0x10206091231030b1909050c010503060d0b0f040605220303050915010312020d14120414011e150b090d0c1802190801081e100c0c02030d0503090a0b0c0d0908 69
    0xa0000f0028218007210410802d840c46d00500134103a40003400b2034180c540c010b070b016542212025000000c80034241c0c2c1c681d41560760a4403011103841540c41040108601401829441203c01c1d00266861030040c4401c050049281e400805043c0c440000810314042045101302c80c00c0660f488000c1c82d6540d003440e20f0420b50808601c1d0050050446c4015002e003c0c001601c900d034003482d8071514007440302a5106074481c01402c12a11454003040f208a115400d0003505107400032940d8841c0715180b070701e11500440b40c121041c00244292610704000301072041e406d9071405182580d28015404003468084088443e641001e04180381c0300d1102695101960301070401400c12005a082e4203511074802c0c2c50170318091044491f01d600a40745100f062413400e1548216140342c000711507040c030064040d401500c030300c0c681c2c40002841081102081d45403c1002c61541141c3e400c0c014554142908280e032520608a0083d000340c41c544c0216042070118411a5121010001d0421803841d003858510407650 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 517133830 1250 517132580 517132591
    0x91c060501060206010b1207120e01020903060906060307090f091407140405040807060902010201090501180314040303090501050c0a0c09060509310c0f08060105010206091231030b 79
    0x10325040020410900000c1c0060603180c48013103450070003140c68845140b5000082c08801003210140401840c00100d0198501105203800056103500f1a14203051900c43c3c0141203681aa1003030042c4641d9460100e0340c0c00940d40915000b242c4501301041d40c0020b024410b50080c00300140c0c008440ba0140b01003103117001d42d01c042c1201c0908114450811041c1e0307409650150803194104150000915298408490b852060001040d014003a803115800c50b1140440040c043d0124090482015884040c2651852040e02540c1c186070560310000c118401d6030103003d0601c031000601c0900342404104190300c1e160b11021402409840c0c2c840c01000d410300d0b216682c003400b49a804502140e040f06404401c902d40a900070303940182c03040c030080c440001040280c5e4202185640402c07840c40702c590303400c0a040000000c0c0b46951501c0002480c20364010b200b010940c0080e1003103580c81180000b1a640c40400c440c000071050b0190a0079902c0d030006c0c0815101800c03011030008100081444801d1141 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 517135080 1250 517133830 517133843
    0x3030a1806030207150e19061d061006031e060602070f050d02030a060b04180602030412021507051e1315020c030303010306090f1e0209060d02060a030c05091c 70
    0x303594444080d01a802010001810f000030f001420140c0066588035144007044102290400684034542d80c3e580c441c050025100308c0c6e2596056450110415464681000198000e21751880e0110158100c801180184400c060b1201c6030155151154244240e42404106040084079960403000c4c0d030301c4015105950280110751030000e03051500c1e5804250310b540103805082a200d20342d954200a2101910b40360780a95a12420041550340603800304005100d0107006a903401c1a042c80503110113101603400440d44a845804942800c7d210990740246c110304001d07072185a1351072248980201382c184041006030101e443c1400c48848420042100c0341e82050400041d0180d500326101e0310070000007030300341c1c0c001c200400c001078059000c01c0131107000c2c0c640d92644206a96a080b41c0d80c030361643d15081d40c0c40c00314403013080d0b20b41040030030381000c4100e91150304189643c2c04201340340945090241815916051464500c1c054800c5401c580402042c5240c503154001c00b2256020340d030001590703031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 517136330 1250 517135080 517135127
    0x3091005070b01120201050a211d1603020604030321020309011a01050408030f0708070f03020607030608010605180603100e030703390606091109100309021c0303060503030a 76
    0x20740d01e002c1d0b2800d175010f07034420780340001854003900c0c0c0101c0030158040026015812114460135446460404c00810384441c510079a20041180b070020913400c0415840041901000103076a640200c030112130381420708516091518115201c110b1031021400340d891f0002040182c12481944884084401000c403000070442d510011100b500440c0203074010b0760b0081044c2c56015030104e000c0c240181c401c0d000189400843d965801d1800c18a00048000d6404034043c4031000d43c16000c0c40b00a084558000c100891030003000070b45802c1d050050a00d2803110401041064406101402c0f94880500042c0440004519031964a5101900903400581440407070304d00000d40c040e03040310342c00141c5c000b480501c03007a540410110700f44c1c000403514255511000642d14050340940b980041720041c0d143d4403510102d05106607400310400d41d2040500e0a4920300040e601c0e007005401c8407041d01218485600d65280660081c0380c0c2c3e4000700c1e032610000c501005129405000c0d150f01c070001a051400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 517137580 1250 517136330 517136339
    0x2060712020609010908041412101d010c0203160602120c030a0b090103020d0201110a1401020304060b0d20030705040608100605010f020303280507090504050601091d0903091005070b01 81
    0x1c840030b1032001000700104210400007230b03410740c0c4118050a8000d01007100c000300510080e10b0001d0280075441c050340c9aa11198541403040f08252400030804000e00001d210880c00071b440384140082a00400050907401080c13042c541d064480065800804d01214204580f064000b40c00407200c46013014204480402d0600341100414103c80d406407586609010942c019222503000c5900e001c0e05108210b03040001c200c8160894114191000006a8a00342805d02c5000d0702c0307414035506d0141c04e410b950f45002070043c1140100221320500c2d044a0034051900207424036445134480c0ea4000d0606802180c01c031408a040d2250000c0850f0422074584c1c1c90005581c501001042071015800a000043c03007800002a188100e0340d448140c1c0a80c90444010303002250350a8419200240081c4402e01c000c2c1024462180c10500c01d003130650119141428400340c2000e804400c213401c01200d40460384000c2c041060b00c0405600410203c0002c4012000401c142c02c450300c244d038100703c01e030000207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 517138830 1250 517137580 517137583
    0x30501060504150e0c090a031208060612070c03110a08030f01050d031b0309030605070f0908300405041409070f03080d0b0d05070605180906180c0702060712020609 72
    0x643c054114400308035401d1420a44000b0200000e01d10020b04408020b5440147c4d01c59030107a0295108030041c02c1c03e001010b03030052526a000300b00b030740034210400907a140d080005c0e00442d40f00405252441001d4068542141c0700b8032901c00e044014847c0391241c004212056015511409504014864582e030701c10801c0040300c4007100150218900d44010411170b0001d6511405480c02170601150703041d07680c0c2c7d0f044119003045903c000000c01042c03001d81e040e81c0c40140c80c001005680002c00150741041c298561034544e1800081840c80c4800e101c0700c0c2c110f04203050b1001040000c1003002038014681580c110b0034801c0b101404d26001c0c0c2840428180b503800d14001c141c0b50001421400c0c0a910aa698000c003941004598050b42d8500309a0001d20f003081500007130040740c2c1d2505c1c0c807290b115510a40c800d4940c00d030a8407580c1e44000f00849601c51880100403044070508490560320b490400d000709224981c00070350400e0001985005010400d00440c040d1074140e801c40e00c0a40c0c585103080e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 517140080 1250 517138830 517138841
    0x5100603050c04050d17070b0a02041707030b06011b1209030213050123030c040e01021903050f0406050417030709060923120f0a0b0907050d05070e0a0b1801030501060504 75
    0x15070020412500790085000821b80c0301c000040d038182c542c034040c0552100140c2c0301089036054900782e00020240a00e1210903003180c000740c44000100398260859880100210005000504002412139401e513a82131b0500f40d1880c4503000481c580400400c040014640d800500080c0c2c050446840003845400d12442154100c84e00d440c0c0400c1c0340c0499204508450a00c1d0f02c0055151003000300a82c40340d55580720f45141e803042c902c001031743c801c150111a21190070368a44c00061510380300401c12585c1d0341418007030f4801c2d171007000042c0b150344520700040000341c0008a40d0940d8004410403040c9074200032004103442103500c1d9043c00607511044031032160f0a0804031100d0045242c080609820208030305855100290701b5108030410307441c440c1e86020707513600e0281c81e2415688140200c180c8103120600c080c01c01940c501100d0340c07541d15003540d02c080d24171880340c8035042c410000f15028034a50000c403044100a11641d0f940f03003403018402d6008003c1c042543c0715440c0c40c00c0055a850700d8440c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 517141330 1250 517140080 517140089
    0x60306060e0705120708150907170108010207020906191203090e0f15040c0311120f0603070e070c050c0d031805040c0c02240c0601090609020a0914030a020405100603050c04 76
    0x821000e42d48041e01100d8103200138003100f05c60350b03162840d0511036648444581c070400c41c68ac1da6200b541ca110f04882225441a03002100b582d104120400241c0c5030381404540c04503080c0e821030a02200c801c210764026515601440b0f01c0d0740300003105030070190720900c0001102c54450101341c21b615880b05490f407001e82030b144204802c5225030f1007903207420550081c000e181032074200082da000058803019016440380388140000c4482e18200312022000c128160340003401038004007040c9081c514005040d413400b601e81003e0140c1208040c0c2000302c08c00a0000c01c40024081003800d8050b0324003c2c001c40c0105801c2503403040c1c2e40501280d030b0f080c00c0c8030765002003819540e030300002c1c641ca40070700122000104902e150345094610751070031191801c0040401020840062200d5854100c10908a07451904010607103401001110003880d031103038500050310304e003068261005001000080c070344800d80303c7c004d401a04110403c2030080003020028110340140d01c1c113000135079030050200035900ca0f6014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 517142580 1250 517141330 517141357
    0x10228020907080f0a02041419090c0908190c0605070c0b19031404020121060f030804050909010c1418030105070f0e09061f0c0f0501050103020f190509090a0204060306060e0705 78
    0x86941c22352404900b0341003034400c0d414001305900d80310502c02003a24003440301c990104200030380400c60042e040000c0c411085205102007004032041c1c0d94002280031500ca51030800101080354400c1c086c919080100600345100c21540d01c854040c0c0044940e01406c00110200740380c04002c46081c091011041d10440d8140e49140b03204d40365580c40a601c2025052400b01c1c40d94501c0c001c1500d8483c0c00b07040d4007030341c000c84c3c00c00e03140d81c94081046002c0340002e080c0042641009136804d0480e030410200c81c1800c1d400102c00c0d840b22170000381a5484403014018036855803d1905110310389800c101c2c12201c503140303aa01c1031043c13200d490a128400500b43c582030f801004000710501060880060900814698649102252010b0b2a05204001205015039060759210010003c526042d142050b820806072b990382030b0040000174150034040c0c01c0c8a1203006003541d600241e00c8403810b01c441520140d0007401040304076140d050150081006004441c580c03003081e80440c1c4058092803e81d40500e982e903c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 517143830 1250 517142580 517142609
    0x6030f070f1817250603090215030718140303090f04062d05040902061c020d060b040f050f0a090b061e0c070b09010228020907080f0a0204 61
    0x1000c0300d001080103421030400c0044402c02c120b400c2d00c26500780003000007003c05090342481c0001d403420030341301642040300c0f80542900007000a0403409900100d6540d0700303001035044014008280c110352030400d0f00042c032000200b04190940c20894051150b1a090700b020515515400f00c5a84000030302c03101341c1e1560052250313000c24604041320078040c0d0750141000c10220754401060500704501882d00c3c3c3c0742d41c50700c034036202401e8541c1210001072030708035003e20a056a640100300c240c818400d100c07a03440000284e4140e0507543e0b4048801c05508081d00b0080c80340d5583c05031006406c28080e054111100c40c2d0006441e14041800701881d10340101003410300f5252800120082c0402c114407a00200e0500c0a040103014101407074158003400041c4580e2103980b00880e0381801141e4015000000041c080c0d00c100d640d00043c00d1409100080740324500c948884082c1d4260981c03032600030750000800040050f903030b40c40104039001d20182110381950fa280d82101100303a001c3c0d03000f403c0250003610b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 517145080 1250 517143830 517143841
    0xe0303040b030a271101021f020a021615030524090901140a0b120d05041505190e090f01051806010e030105070e13050411091906080d030b06030f 64
    0x403000b1900000d24400024506240e022410303010706100113050100c103400d03803003e0140b04803a0807640390407609201030046440102a4105100809041d44402641c003103244101c80d07008208200c5050614100c17894171541d140c61401c2d88080105050000900300b00c04140b804600c4c03c441888020014542e41c840da42d840c040c407011b0403009000d40000c3d900c4e500b0918400f44121622400380c0b103d41c170041903094031342060018800342200703800c0c05d5900034180d00150726130010039601a603c1180c40d15038010440c1b0b404460b1801400c11040344076081c401140001358001c05e14a07402c038000d035456901684c030891300c61840c01003403092030b800001403000f001c0504c4030007030559030041c4141031100c540c40402020a0031900120340503400304078003010b1141d0b00e01d01042c4030010740c0da44040601151034130b0707907d0f40212040345c403042c2d0050304c03031070081a020242e4034074117218222048001c12001350b4840d0b100d585e03600700d104a1004a481d007107115405040c01c5003168820940e6a09529070794444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 517146330 1250 517145080 517145099
    0x103060e060a150c080a0c0c06020303040201140a110f0a0302010b121207081219060b09061209030708030a06050f1c030c06020405190801181a0406110d0f0c0e030304 73
    0x841103068104014111034000113245c4030098403503004960390302a40c1c3e070164074145a0451080e000316040d90700c14001c0000503070b403110703044a4038854440441e841b00030034082540c407200900106d05840c01010001c03c2003e02c00038894010601130360081c03042c0381512051140040030394092040c55041521a0705100c1c4080b4000d04406100da00550701d4070060700318480407040d05680c2910242d00790320718800d80070030380c0c05041d001d8050709501d03928101045002504c50b10036503411150710301000d000a000600180240c0b034501d900114643d943e881c0c0034014400030243d038003e40d4411a00180d041c9664105228804040710012400303c040f050188c81c01c2d540101c8061044880b030380c0820011413192142c078000740708590030041112790309050600c2242591404004605401c2d201c01d000b4005c03440451260300404152001102d80744c5950425030003410000d0b4005a1140740080c000242c0940d40c1e2200082c407500803002c0044450100f000c560704240100c1d540c2d80f590040c081400364080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 517147580 1250 517146330 517146359
    0x519020a1407050102210c0915160506090d0e01170a060f090b011d0d1511030709170706090b0901020a05060a06050a15050409021c0510050103060e060a 67
    0x2901e050400d0600c0c81828900c1d150352195074200e07a6030750007061135410b4141c100c071603401e0003c0811040c901071030030b002c0c102014000c104085200e00210390206a1900c0c00d14210340e030080c500324000111403880d09159948000130f460550701c81c070076962310b1400741d40b25050003513904405a41e00708202115400041000300c0280c54807100c0c0755030f10800103c82c11520740e24402000b0314600403800300c103140d0001d800140304459541c4104d581020011156584003115410168808844101030b04514000c03c02080c1e00e04503e011904004180250690042d048500319000c0103c6a51488002c1c18142d458140f10b2040c9004203103030b484240200380285000d4086050180304540d05208a070312100d00c1c24109881d1900826034a06080c4043c2c280020b002024102d1041c440e50307289400355004103584128424220700d540e0100d800210152501103140312500d0b01841801a070401d0011040c512190f8440c150220307103029400a10888410500343c46510002c240490562400003107010040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 517148830 1250 517147580 517147597
    0x30a06090212160f080c10080907090204080a11042c0309060d050f0c0a020c010807030e0105071e0905030a12030608030c0a0303060611060411190303050319051902 72
    0x8008a00510800f040f950300455440c202000d00f030fa14142c11252612802c1d00701040c0e580024048016035291404030760858201d600c1d06502c107a44215540d030406032650044220340b800001c00207104c0100090f4103003910700820480c3e1040300e5100400046850080b00080c02e82040c103082c103910320300d21490460300340d03c01c81034911300b1014500040302e0360b00803e150700c249684c80b0148620b481e070b00c60156a100d46043d12083c80c0580c6e4110195507490300c0d6241c136041000380310028811078403d42040e01000e001200a1003e4200300328050141802c01c541404240402000301200601ca5100d400407100b02501411840c4000d480b100300c188040c00c40d03030301450b495601c0000c0e004401c000a004114402010307140709803c0e07140c01800e0700c1305948a4400c2082e4151066927503c00454100d0700107602164020300c0380441d401003504000040022441e0103110340c000001c7c15040b000071403040c8403000c0001100f10310880500f04440d0169642289241602c8602805c04910388c003d00049 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 517150080 1250 517148830 517148839
    0x20f03030c0307080c011506080c091f020a0201020d1409060f09060304052b05040b070c030206030c07061503050307030c0f0204050412180806070f0c1502120702010b030a060902 78
    0x30240394401c6140d54485001200d080c0000111040444800e00c203030035200002c049520301140c070300f500003000707500040d1203d1a10311001403500d0140d501c59108140020940a6120f41c0103d041d002035215003c4035400d0340980210569800f046201e001d02d4918048451866800c240f00d0000307112254104042c400c805280420280d50581d45410146104500c0b5100500101d080d40900c2034105110400c03252001100c040e004400c0c5800c4415542500c4062040640302c0c100b0342480340040409500280d0084c1001044c0401d20030720343c1c01845064041c11082c45102520300c50050200d040e40700240c080d41040c4010f000091007050b4400200f405090f461000f80e1841d00000c1c100d800c1a034080f12032140301005004425000501410240002154100643e2070f00c0295515040d00421140c1000400c1d9212000b080c000d0140103505a040b400c0c5105420300140030400940c4195a47c01080360ad440c001040d0503c1402a0f959100002d005003031803030f0131543c41c000078042801089030301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 517151330 1250 517150080 517150087
    0xc0f120221010e011805040b06100e0406030c0501110a1a100f060509040507030b03071a04090630030f1808010e0105160c0c1e180b030114060d020f0303 67
    0x4110302030101e4080c010b2a4203003c0d0300c0d4940b103082038034083c14083c01080b5034100010030000c10107207542203500043c01d441c3c40110400c0c1000031501c04c14001c0e8421b500c503103042004001e000b16505207400395002a04c540c141540400c19459407001c07080001408106a05415104071505000a40d0002c218001c8400407580312081020711b58000d4000d440010301c00305281455140501a00390020b030b081c00c041100101c120082030311b560380360113034801001da5103205080c1900d944044030b00809042c0820401309031501300501800c40c110f007840f1006d040030b07a090030108a130949502d00c071591607114003800ca488808150340ca500c110742480084c00383c1c0c0c0342c000b03815002800f80891034554900001500e1420400c4101e0300012840e0400030042006c90603400540e0001c0c1038030550701056403203569084540f0031010040d4040e040014846a4543c041604603880d41120005e00350480007403209000c0342102c11501c8104460041d400b48102c41100c01505290710903050081018003a81c3c81c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 517152580 1250 517151330 517151377
    0x1103190903080c01050a050708040506180319030b0f06040803311203031103090a15020403021c0c150c030f120614030c0604080a0206181c060c0f1202 66
    0x211038003c42c8034840c1e580d45620402050341010710489902440c2400c016034203041c50b40741e031b43d40d0b404020710b190405100c002d10b441d0201400c1003079807401280c3c0b241180c0401d103407a0000b806410140e6482e03000340203e1119680c2e41c9403900650302603031001d100941c200b980807000042441403c04480d90303121004080546864000759404014003103d8202c000b03504a03910b0000c0490300f0001281c602800180144002d174000812180805500310040e07050326a0290081f00003445598402948001500c0880e4001350703c50100c100300781d004070003040059681e65010300a41c03020403141000115024910000030780140c5800b034000c105490007841c41302000f000c20080ba02150046203016031105010100c3e85003c00c6000c01d60441a11141c8c00c0c98500402c1c41d68850200744000d2003007034007280d03001c41000666880008510000c1024041076400840d06608813100c09054406905000004c20380a01802c1401010349090350760010424201d4131a40083d00070740301079409001811444030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 517153830 1250 517152580 517152593
    0x319050c1e0c0a0b030a1505090108010518071203121b0201021c09080304170f041503060e040213050735010522020307050903060f0402040605011103190903 69
    0x404180d5070403074102280311140c401d89804040485030348070740034100051003000e402e54145c0350440c0203e41b01103003800c1c140c1000408003080b90400c60700283c03a08000100340d0015000300340168419010704030079010f022031464442c045401080b0140c80750f41c100400080c4580106440c45a118000189d2403c4012151072040c903084882e070010b0303402007809902d440d0501141c607801e240a1004100544050340d0b104071a0000a101600c0d100301824500000718588046540d40c0c00c181280c1e503690350b01c92101c00e0300e00340b80384005000a880d12601086134254a0001405180c0041819000040940d4442c0240030001c07d20001c0020038510100d1000b9000e0111190184043c03800181400754801d51b140c08505a1042d880381d0414100541d00404c0c0003500c550310300c064080503030b0325a07071a070042c0c1e03061144141c020f4240c40707000200010a000640b10f50f018502c00c80d414444117940714011942514828040601908100b0a81241080c24404003140b28405d01f01680c5059598407000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 517155080 1250 517153830 517153843
    0x2060f070501150b07031202071b031209090227011b0c09050f0708070e1f0c050d05090f0402090f0603040302060a0501060f0c0b19050a0213080a050319050c 69
    0x440d103503034543c2d0320400340b4948002080081e202c854607040c2469115103005120401c0103c40740d46160b400181c0606001103289411025101c008482c80c2e52603032864480f6084021281c1d540016200070300100d09000e440c001ca40003c03050004920010080304185c40d81c8400041841d03043c8914660b107604401c100510400089000e42074030020b040c9440c885030103584008000010154540c1f04010700240c1100c003d6401001510f001d1884e82881c10114407040da210001d100441203403091000403030b600c20b000100c804d125000ba290b488130500c0080d2214011110f55a52102c0f178681e609417903042c258003402040400a00100d04240b80e9008502c06600594054006802500801c00341c03010034025180101042c3c075102c441e010b00d8510007031010700e030048020026034000300810741500d541d945e64540303a10030440401c80c0c0e0411201c218001d6010703221b80081c1e080d4195002418000105401c0500c035001000f0f18074004441a0792000b8028400c480000c0c0201880020310281c1c0030880c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 517156330 1250 517155080 517155083
    0x41122090f02180409020d1b08100903020c0906010503060d0501180605180c0f0d0302010f06090b0f0f090c09150a020c01090519090e010603171e0315060702060f07 72
    0x1640c0b82440080e02c0f0091030700c01e01c1d09010f581014090401070f1a02407405000030341148103002080109010402960709961007401035103d02e1006c0c2d030b910300650307009150a0303200340c08440301c0d035140c030044c010107400440e01c40740890401e0000601e2030500c4d0020101d02807050000040949038900c0041d04152400da00f9030310700350b445081043d1500240800c00703020054400402c1218036031070000b42449940b051340c501490700d1103840300c2010b0003504048000701c49400148580d5840d0440c45004041c040b124900c144400c56610f246c0c0d040008185031b081c2400380201c4c160b5030301c03410100e03455802420042e420403c5081c40036000c00c2400c01a000405081c2e014290308c4283c2d42c0010202201d5400a61045072040c10110a07184000303041e00c2268000d0002054031480100d900340103019640c0042c000300880407100112844040040144032600c84e04d10b0300d15040c10161500c0d500040728515410905402c10007001c1c9405400381000600c0101070301e1416a08129003211500001c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 517157580 1250 517156330 517156361
    0x109080f04051215010b09041404050c0301061d0103120509090406050f0705030c0324030d05070b01141c02040b06040e09010606021f0e0c0904081804112209 69
    0x10144250f28118100c030840190071001450b528921603144500301c3c4062040b02e11203c1c00140c0c113000303620b41d9000120351040c8000030b12901d14184c14060b071508405000c140c030952070160041411812000845928100300070a24102d0b802d56a904005040c2c24030400c00b4802c0600052060755115040c061141b8414040440e07542000948041c03c3c440290419082c000180200024540300c1c40c02e0ba58451805100c240c03040c0d84100410b950400350900b02e9030940a1010003c10490700070b00200051440707400403208680c0d8480c65403c0d440b400c10440c503400660f04405407000031000c0c022512040c0011b00005490b90010001460b55000d03900101c0f00d40041c40030000407803420300c00e0200811075030014018024000403013009500300c0c002841803856413583d603651464030400c03044c90302c28000b0b800014181004c0c14000d0641d041089072070205445d100c044000744c18203009900700c160b907036024281002520602f55580d0400e00030210450801e95000140d201a14050861088240321 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 517158830 1250 517157580 517157587
    0x220c080106060909062135071e030905060d0209130e10140a020d0f0e010b09070f080f062d040b1206010608091006090c0e041514030109080f 62
    0x130305003020381d0f807183c0c420802104a24440d1901061940441206540c400c15034040c2c0307a0100100030358603a5034551540b00303103d940c8068110318100b1004206880c0a0b80c2c0744000381003010f24000405c0e502e42c4000300050b203c1c020810450414a0190010307001c844005820b1003c4040410010a81d10002d801000c0d1501020140b90348148003270054410020820f00c5122028034000d0245c0c08050140720800754001038031840582554040c503104071642409000c010100b07401e0902030952025400d03c550070150100c2c2c0001d0041c041034031442070075264448155151201520b120300014400c41d0485040915510f140c00700c1c242d40d01d101014020f0a01004201e0005e1004491001801a004801e041400840b0081c0004c106046803a58904031450b507484a01960034501004080d2800d141800808034070100b01c1c0d0422101400507a44030b8151020481c10001903442d51505034106600303600d410f012030a940090202c0000000d000400c400c851a90307404041d601c8441d00340030344e16012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 517160080 1250 517158830 517158839
    0x3020f091003140a060507020c031c0e030102160b0c0414010516020910030501201204051203090a02010e0108131202120c100b0103020a050f3604050609220c0801060609 74
    0x144031b040c0c2c001341a4402008400707248004682d840144200342440c2f410340c03c11214030244155101c1d201c07400064000d640f142030300240c801c1890094142201c0c103185000004a00c1c40980082d68122007011038030703141c400b100b400159003e902402094007440201e51000700561108801640a030b1548120003024502d5428402d007151005030b42c820106060140400c81d42603c40241d03003a030004040360070102d85451a10510b048100c81d20000720100120401441c000040345e0304030500e00030780320080503070214001152200d0044404011a1720b915200c400411007511890700040c1c403038011916000008058030325030350810741c21440d10341d0112000c0c00d0510400d00507260703504030031709041d4141140007101401d980107140280141d800040740f02c0d60107440050390905c8007410780a61160540300d01200c3c0707020000095080e805642810007140302c03810080f480034032410868900803004101c1c1000ca9021100ca26003c0d05c910794129000b0900c0d100a1140400a102e5a05d0b11424140fa1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 517161330 1250 517160080 517160093
    0x1031b05040c02152a040f051903060c0201060320030c0f03120307140a08060102060f090c060a0c0803090f1905150a02071416090603020f091003140a 66
    0xa80c1069006034180300d040d6400540002d865449030340b00d0f4038800003658030300e00700c84910044e0003a56901c440d9444d02010007561100c006000b600c14881c001c142c0346807518140b100042d0341103402c4030f0418117154100049045640005000e003072903c000b01c0d04944e01d40304c80c1c0f080e080700c100383c801404164280170304a180401410744154015900d1090741400803000036264241846001e0440c0d10010005800b00e10a02c211550450440202034135840c146c00000c154100460f401409449141d010602c8604048120b42c40380c4c0a2400410008112206001c10380e000041c0f030800340107860301701100140e843d5010f5486454040010010751841078400382c80c02d03c0108101d041d040c40030726500007050000c5120107078100d03912100c1015884058004000344203071480544804446901d01c2d607409004600d500c07003881124111450240c45445000450b86148002035125030034055021440c10049006940008070461500d8041d82d170703494242181079804014100e0b60400950101080803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 517162580 1250 517161330 517161383
    0x1203050108210a0309020a0f03150e0c22140f09060c1305040c0e03011406030f0304050a1809020d060209010f1b170c0d030615020a0804090207050102120103 69
    0xc0a0707030045564200d07810700ba04500c20079296904144e1104008410f40d00c0d01208040107000500c072001c2d06607540d041000c0c0711030501070000080c905100c0c60304151400011031901403240140075111600c2d00d51840c4180c48002c100c0c2d10103243d240c2160340c81d44100d200644d4810321120f111041315161141d1001e0030407100500b0a040c4800612682141c84100e081d041d040c0c5100b920b0000303c8402045058503c0d0a0303140d03e8951541c281042d4006256002c03983c02e0041e41c0c1034013100d01080c0502d2110381c8038003c034001d207904840a0002002034007040808001c0c04036100030001461a041c0d004106a00c1c00c8040603221241c00203602c0e107145d40e103d400d080c00b6003120b01e400004124107541801c11101040400f42075225058007041c0c00700424411100200080c104444084420007005000b0700424801c8070030701810816140006070010400000845e80a20210304c0e140c10f000c8908000d401c555816610b545d030a0209071004021582e0480c00703036014058002c55803604414800303d040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 517163830 1250 517162580 517162603
    0x1020c010e0a240204090905030904060b0313030315090e06070f03480c0b09030301142110141e0c0c1006031b09020a05030a0908071203050108 63
    0x60084807204080381c8106100720b10010306a4049410300503100702600a0f0181d0340150100754a082060003c01c080000180ac140c1c3d4261401c0c851b1654440b04205a80022a4003c040040c00703038510002174802e40c8402031036003e50001011464840c40c10000312190800036060f10b038001000c0c414102e030000f10b2044040c500e80303010700410b4407203140510700a81c0d00c00746000f0508100b40104049003120480c1400c60001041515098a0800020414140e81500391941c1c40c06c4000325400000100480e4181e402d1502e100300e55005000c1170081d905a071001c09040046200f4600d048500f00780400075644207000d501052800c0400b060300510308000d8103031a91456210703046030440390305050580d0f00015450382c194455010b07034901802e203603a4500e441c007100d01d0304d000403041000d50010500016500a1074400064079120102c08038402c680344040030900500c001800380240760400c0400702e100b0701c200b030b090155695506044181d920080c101003500c0f0b400511040004200503215007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 517165080 1250 517163830 517163833
    0x3080f091002060f065803020706110114091011070b16050f13050a12031d192405040305061501030207060507021e0304030804050603060a030b0a0902180105010516031e0201020c010e 80
    0x120710350347e00690369180520a04090010708400307001c49450031760182c0225500c0840320703110307864407290081d02c580030f24505014951030600e01c20100030500003500c0d4540e030f000c1c0038540380e52035603189994241001c2c0610820004108908544000342c04090103880c851a418030050307604100c204121189543c02030700420102d42c980d40b011079070101025200c2028041c00d03001011070000840ea190324020103008100301c5810000582d040c108403040c4404e5042c045224462482520031141c80c8034a10000e030890b800b22000c200701c50030301c0c1d05001c00703d6070505005161582c295540c4082d50002c840b280d0140c0c0210014054a0b9640c0b4188286c13425040302035461b10341140d580103624080ca01400e401420007000044568541c1e079000030283d500011205c5007498460501d501908030074904a0040c10f070400c042004040d500c041c141601c605846060a00c41901c6c980381c4c070200c03020710a40820000d100e86c00340240c605a07106401ca05103500140c6d4410f412181c19082d0fa40c7c83d007454605 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 517166330 1250 517165080 517165249
    0xc181e0f1d0a03080a1b0c41030d090f1b0b0d02090f03010e101404020d020103020703180609030b15060a11030403080f091002060f06 59
    0x7072100c08164090096418201142e6507290110284010445000548800c40c202030380b8960803038004254140ca1481200c2203042050703121140c1c1c424030220740254030183e4121913607500404503005180015450b18041f43c2c200a4629918002c0d01c0c070140382510302d2420003545d9020b008000344207880c08080c00101070002c62030191504050701c581d035182000b040d070100365403409543d0500c0c0c00d180d40760020b0007480b180da1017074841610f0740c0c28a040e0900007031801b0500c0b00381e002c0500b1403e2050350004d2030050604050740064000c0e42c0100400c5040046004501e0981c2c3d0490551704040c0000c0c2d0355140714135045180c03920701c0200c054281804000284440c1e083e5503a2101211030041e41c0d0b14200e441c042460703074068554065074000411403100450300311140c1c10a80064034010700c0c02c64400104100700002070383c9802c8155601003d69050f900050514201030303111040b5070a00e1542d102a105042401e40da128400e1800407140e203950b00311038070301d6a000b00c2100c40b22400d010510344c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 517167580 1250 517166330 517166381
    0x309170a030b0118141c03090f120b011206020c060c0a030e0604020f0f1203370c02010e0d0215120709060504150504080618060c04030c181e0f 63
    0x130f00e0745a101e00043d0b45000c080e104016200e94a84c4100d40d0514503441004500518000e00445014051090a102c500100142c00100204402e0003260070681c842003607400c010592613000e45952003901d26540812124068440400049108034181f4100c00d898141c1c12600809698030b03666210400c2d803040c01840090707a40c0a02c6501440400c50b81303407813019a5000811791100104000300307810301021446c8000b40e02c02000da183c1e4048004652142117a402c4924070200340c2510724000010b41a00180b0010750140420115405000340907030303c400b00580c00100d205100b0b1078554039103000030845202c2120a002059048003035410b1000d002070405600500c40d000702d10501540d224200e5450080e40d0055049801525071802580d40d41d250280303010700c1184015500d07031300c00e208400000c1c5039645404280c501b642c1d8025810b481a51401031600f0000318021070340114250b031f41e040b281864131056540400b010a80750b0200710380b20040805000c4640d560101300503d00d40600070340707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 517168830 1250 517167580 517167617
    0x20903241806060405130209071d0409080a1821171608090103021e0903070603060f17071d0901050a06060c150b030709060801180809100309170a030b01 67
    0x294024810b4400041c103564034846c007060010f6014005e504441e1501c24000210f600143c04e210750300080726140c690382010b10a001c12215a0300c03010f060400d040c40004030703091242d241e000c48400324015403e920381d02da03000e1650340704011005018511260059404202c0030510b540f100c8407904840505000301040610307600036840500900e200000504048141e0180d81965400b64510310900c0c2d00e2079404610000b40da0154038928468840c0c00c0300002c0140c0319020340401e450110081101c40380c1342c001c08030031b5000018907048843c02810004508004e07100b18030f64460503c9190003895044c0101d27241d0031540060b10581d4040d08000040c010b1503005010403001030b5200080100e80707010026541d009003c43d11301240d0500651000040080c0c590b0029002d4070204070013006400d2108103040881a10b01400a04030f030401c4c0304c10b1005251108030b09084415600300400d00c03d2095480401c109103200c01d01d12a094003068807030400350b1611a8040f2503c00382030804194032003000c00b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 517170080 1250 517168830 517168843
    0xc06020d0b1219030f050418061e061409010504180c11010902060403020913050703030e01020712020a030f150608010204061103090d12140c030304020118060f120209032418 76
    0x1c4e042c041e446a620110b41d2003003089600410103092426650320f019001e1401400f1316104030800d21503801c04075164030802d111501e0444501d5141c003e150169452125910b410034680785061000610000a1812940700c0d64030021030603440008444488050103040c009010100702096858550341000503120b10048034207407901210341ca0783c2680c40389610000b28690380e0380148a40110a000400c054000c030850b82c20f80c00980076900c119880320030f1180803104450019502c200000702c1000800c0000f109040b5081c02074071813845062a42c1298000d07508180d1044855079400241002100c0e40032145016148014010754941001c14000880d14000f080c400781c0b400303c40600c1c0c00c062502880101114810010b0f00c29210302804d00c440e1780702e81045605038082410143c40c801d80203074400b0807400740c56a64980740e000c4080a88201d614840c008040c11503e40e08101c01c1005940400022000d2030b0220942c004c40c40ca180040e510b4000d000e0075840682080c001c10504048011640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 517171330 1250 517170080 517170083
    0x1f031113063b13020a0804140c0102030306040c0c02030d0e0a0e01062304050315010f1413090f150c031103070509061804050f09010507050a0504060c030c06020d0b1219 74
    0x98080d414205000039403e9820041c0b401c05a0b4400203603201c0c0c90383c00490142c0b0581c004c80720901c0100c480640d007031b1150215039032103005030420000103185140c1503000e201305180d00d00e0881c0d045111a40481d01c2c045025805002107420b41c00070501e81d1a200800402800c480801c400f0715501d031140141500740c501010711426140d41c66081078015207d03054400a1100800b11031004408140700c6008800c00c2c090901c2d40444107c01103410f403c0c4d50540c0c2507140c0064420000d500360b040701036006102034801103420010942110340440d07085c01e28692005031100e000210b074010281c2c0034040320501e00d041ca2079520180200f00d900d50704031050310b903825401d4450607518143c407100100640f001c860004e40c002d151030144283d00540000300c0f4030a10300000200300039110864240c2c2c00d03004507912000041d00c1003105000349880341800d06d04d0305109041030502c0e0a459a21401a40c02c00d501480042c5da44103500c01341407070045081e18001d42c60102a02400f01c4060742d480740319015010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 517172580 1250 517171330 517171427
    0x6030b0c0309160906090612050a03260411120105060102100f110403060b030d03060b040b0a050d0e032a03030103060e19060204030c0509061f03111306 67
    0x5105410103100072110001003c0b40185410b071590070b8203008103200d01950095902d403050115507040c01c2e60341000d001c4d420a0041107906010b0340c0441c1d420780c00202c1004049244540b00b0b03000c007a031020040c05944100b6000d42001014024000100e003400d00a12445c0c6c140740501c08980d80104913804040110200410b800c2100629000504940e070b46041c444100000e0000a1200540c000030072000210160780f0791144160b405c500343c1d44203006443c5100000c02c010003040f90880700807c21100301d820901c2c10700b54030020142c11680701d52803550051b00005a10005035051040300c61403800321003603071800071514040c2d4680d80e02050000900d50350f034860340c68040c4682007160381e11600440c030341505103034903600d0031001035041480200c46c043c03d012004600c41c030f02600010305c1410701404461140444902000c01d8145402d151010302d50398070441d2000e100c1c800010000800d0301c00000030b46500e02070004104a11401000c1c035080d49428004402c21404201a110390b2900007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 517173830 1250 517172580 517172587
    0x409030e1504081209191a0714030d0603020901270f0b090403091d09031804020f07061b020105040f140c1e010e010504050f1327051006030b0c 63
    0x200c080d5540c2c072894000400f6403240310000c0e030702d054801000304500034003504c6480c414000c1a0a030325200b026401802401102c0c140c25003003184031343e4041e00400c1e0240502c1c1c1c141196070280030f41158018410740c5451925410b05005504003401014010140303211030a2040117007400c0b46030128181c40141900c20740303c0c40c840d1403200c0c07a03030072032624641e00804040c254203052030090b04207421840341e81000d01d002c509060855000043c5188201900c2010b1850075030756203404140c4440702c50356580e106a090001001c5203050b640a08640e51081e6000203a5100c40f4100c640c0c40f81c1918411070841e0304000802c0005a100c840c0d0300603a030352140e4200d4003500500342d0b00342000300d801e001c0b507001000120411003010480140703c1c1a1070003a2900d4404007040300c0115494840c0d8000c0d0782e00001c00030104096030411001d808265442c900001503640c1d801c8074500b0990710400620b0340b00a140140403030a200042c018603551107001d1404105091455a41c0d802c40c2c580104551b024440c00b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 517175080 1250 517173830 517173859
    0x1e0e0a14030a0203030f190306050a120501140a0c1209030c170f0f2203050601260f0f0d08060f0f1903050106150908030f130b0d02070605060409030e 66
    0x402c4200240d0364018150b03600d62601d070b80700e80f01d10303041400c0c144008007410345100748690091284106640000d825048041d061641c0070100004444088403903669880c4040000b50355103c031180241c0a01c40e000ca040034400f000240688081c2200c20100f034a00103069001035000040046041c1d48480e412160740001c00f602003441c00f40e502c00038100c03400099100d044610180041400c03110211b026901d203100103842c0303000e4003c03500000706140c1c405001405142c600c6250101403408407000c00c00004485800581090210510303414154410b559080c0306240502a100c2c0460003460303e11154a0228001070301085012501030099900d05d148000c80c1d1180104640ba04104950701e250700e641d00e01d80310380204624420b102030418801c107503042c032902c1421054200c0710010015418a480c0080c2c54085d40e1003021000c2c40186143c02c00242501640c1c003504010701c40b1039005845a24a091002c2940d80c010400d61150389007c0405001a401c4a0010b4032420f0035141d1138240400b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 517176330 1250 517175080 517175083
    0x11040c050c0f03031311180406020306040e03030714160503040f090e0a0804060c0c17060103120c02010804110a030b0702100c0e030604110a0b1303020f0904020d03080a0204090501061e0e0a1403 85
    0x7e28000b031060784480e40812017800b94507001140100d6050350300f0000d60354082c80380c03500e90000f07a03441c400094800000e039094401c200c2c09403420040030300551094105a81d6a5499076010b0b900c804003020384113808006c0403c5074851080b40355450800b801c030041450340c03032410a100c0c41c020801449401500d100c10301c018010100082c144683c5460541c174920081c265841030709210881d9036080008015460354400d2465810f1258180c44070784154566540f00c41307401c0d110208203074000194270000000f140b080c11240303020f84140d0300078108000e5183c0c171980a403603602c0c20301c0082c070921250280b020348000034151f40c0641c10485015003044000c0c0020700e6000c1e150710a15000c800424662102a10381d9140001c90340308a030399a15160101090003a802c000700d40103548052181c00f28004607005d04c800590241208100500d4176880e40092002c459003a001603001507201d00b042040c0c0d6010b40e81801407603240b41025009004078400040d030744d550901400c14071250031041242c00351030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 517177580 1250 517176330 517176349
    0xc12090510020f1011120901090b040f030306050901030c14030a0203011e1d0d11162402060405030d0f020c060703020a090f0605070f11040c050c0f03031311 69
    0x10108010a5607040700207603540b41d90200c04030a40071301d4040c040300316283c2c0b29031807400f09610885414455080f03004418080020300c807802d0780d501d0f000c815000903540640766109900c9052041010754031810020112240fa400040c0034076003101c01803000c503104002d503504a03228100c0c403105242a07540441d04182500b9002505503080081c034810a0164018540400206d0070040110042028001080414428060900390000a50345000a100b5041c0a0300c1002585c200c80820a40180c0d01c5c2d011031380d91340047c51110115840d00c40d0000b4084a80100e10003902c02899182015143e542e128802c05040d031242640c1c440c07000d47e88008a4040d50722140c0b4000958120740752541001c6c0c00381d40300c000d099000a4200101050803280c22281c3c0060340c03004e90390b050400f6101d6955002002e1814800d0321680404215054a66920301a803182d850203a81e605880e4040600500c2c039013858000e0100c00798009004018002d4440780006a015400034120b414281988020440c50701 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 517178830 1250 517177580 517177589
    0x160e060d18030809010b060f0703050a14040311271501020c060d0c0212070b0105040507090b07140d09031a0717130302160e0703050a020c07080a06050a09030c1209 72
    0xc011900d207809041d00514424411402c0074001e00000e0088410080207100d41928107403916814025040800d100e1400b0b88080c15081c00d1503025042280b1301c60400d60400d5000729554200d58800c0991400c00c001c52a90088600014441f0903501d404c96002e90030b4018524043c0c205003c000103847d031300c01c20801280720740c0502199501c0441e561024003a0030902c04050140c0f140b41000313003060710362900f181d07203142c6c0190315940113909140400010305009010b00c400c1090f5500003081c0621200d00409140d485801817103c18659a03a00e18140311000004038184002c844041000c0341003420b4614514062003000c04166030360780380544000c010300342594224206c000c1048040700b18401031182407402602224090905200144003e10080c0105080500100042003125000c1e4200f50f401100441c400750810b010410310900d800e82c1d540c480201c650101c0544000d21121740300d565040a10140f007403107420302c50b45020740030350036400c4004e044020350340c0700100c8c06200301c10a50241 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 517180080 1250 517178830 517178861
    0x9090702011d010f0c02061e072d08010515040501080a0207082b02030c0901050a0e100909200403020105131a040509162a1b0e160e060d 60
    0xe400b115040c034000c01034002003c800510b04170b003000003070780000341061003003100032000445050660100b1400002c0a4442c809207e10301400700c4504d40d03181c0d2400241e006103050b02c403543c0407a990040910038181c2c00750340564801d196070400b01d40b94408032400e450b000e09041103140c9903405450000c0c41400d8015128a40200c3d01c1c1034100c200a000c100b040341800005100e203003207031180008a1000343e0b20f500c01c00d8410000401994018005404000500d0426403808803001c3d000c20b0000b01c00c1085200020310410341802040c4052003000000092401d0340700782c40045600601c454426408064180303d0049406c095020b03c104100d4058059010f12a107026041c40b20050150082c0c019144a0440080041c0e010120a03000207500708080c1d85000e03040c1500180000050202415906001c842c011010701048801d8840c4011040c4501c04070740d918582010541c0000c400b518141d94602010416401d05920000c5008d072075204842a50b5640b15881c80b40005022011152100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 517181330 1250 517180080 517180121
    0x2205090307030816080402040b030f010c0f09122a081b01120e06070513030602180103060602070e0c160f061506021501150306050a03140d090b0909070201 68
    0x1152004406410524403a80328000c158451880350600030700300d0f011103800900c10034002000361906410503903245074040e00350b507101040d0a600300d0944080808850100300e402e50894406640982d00340020100003070755000c0000159580088202d0300703100d85c1198542c81d0050384405d80b00c1c41c2081c1c010130f941c000320360141100528100e01c3c1d20062180301d0210301040100202c42031280034017450068010007424103035540800a0b10f682d00403515007816098036039408000a9118401011460301d0301141c28003000c0210001070940e020b6810210840d001500c040145500c1c0311400d40d006900720588544500039620002000050840d001d090644110380701d60178400641d200842d84c035819074603075039080d03200c4c401a40d0390803c3c0105023080d4107204004010500d48120281c03403081062802013041d941d25000130350340c00c209030001d4594241000070000210000c00a00794426036074240451414544040003a46010720000c00e40103c61400000e54031501c00c3d07020b1000c6a2310400812032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 517182580 1250 517181330 517181341
    0x304080f16030f0207050405040f02210102160203210313021f03020a09140a050609040b031c030f0605010509100e04051f050409022b1e12030504050c2205 68
    0xf031a44000b40c002e000d400340c3c1801040340d0415008207803041c0c1e0002c0840c401101d450342409400d20500032204454030007000070800703225003800104014034a4805101c0e40c4031003070040605003c03801c0d00c42641c0c5a082d030500c038004030090043e603a00c040000000588846a800482d048026185010b01c0101001c03c8851f0510341650190420481c00c1e0b60f40d040c901e880c0c000c3c003c0825407104070640d2081c42035408011510b00a0002d29100c00050700114006840d01c0211b880e03d055048403415410710442401745140d030501c00d0038030b0f412003400284610303444c1c400041c0540c402c110036103000e941c0800000c0b8069015218000303401030b000d4020450746c9854003100e04428018688000070a0072204001424a400e0042500c8150000c3c60320304100988501c03200d800907030540c2c1d001e852200d8207401000c5511101d0010074800320f1242240e50f5680c51800745c4031440584400c0b418546000d00348030114000003002c0007000c03020313110030941d14020a044003d2000b06050180d419050204002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 517183830 1250 517182580 517182587
    0x1208040b0703200714190819050f03030609070507051f06060201060522021e0408030d1404050604080f09040f020a080906130b06060904180203070b07080304080f1603 73
    0xc505003004140c1c10f03100b18240c000507032184424070404c0041c00400e10311521915180000e030888050781202512419541c219031800c00c001d8a80c0c1e0b089848031320104100b840424842a81c2030300801d000b56186252034400545030440281a4400308400441c01c5402c02c8420400050038038650307101100c0c26024074000501a05190052034015420300000095030300304040e10084843d4032800d01441d03c1601c4074040002e4000c110701e121940c842e09c034402201308016006001a01a01c4091590340450300040019074900c1004007071894600700800000c1007000c102290400d0344100065500cac5010f44d0700c15558000c001105a0061078030003103204140c003c1d070090000303d805485200e202e54561584640b6070504903071405008101c2403c20f0001204e542c0115071007400180103a041a500d44d0101d42100c4a440c09036010641c0c10004005510f4100706403801000491407451414209644445882c00058001042c2e42c2000c14042c40034030046043d280b007007024880448034400d0605005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 517185080 1250 517183830 517183847
    0x120804030522241418060309030a1409090a0e160f090c02010b0303030406091a0f0609060603240d02190e09240601141603030e010c091208040b0703 65
    0x2000c41d0780200031003452680d58405100790501d516061941421003030100c6541c0d1004821151722850781e8030840c696541c60000d075000350100001940c46860260300900440322103240480070450500421403140d0f42d4042403035002102c00f4010170909100040310786005024414000322409440c004104010910b00b290200d0380a10014080708041e60f43c2a822a44540b05507500343e0410400107012503002d4002460807032158803000c04a4050718411a5114002c1d9440a042d41e00101404454078207000d0268010070b044a51601d5810031260310b10003540c40e110b100c0d546c5080c10743d607281c0302da0310001041c03c01c50b001380c1740311990322880b0050603000c0e0007401000c0404044038080356a01000003000d05100d403040404411800f40c10307108800b100c00c010183c50400004800c204400038030b41d80905800091580405100501842d019040d251081c0d1030050700c0e03151544907a04130340d01aa41008540303a0b664443c12290140c1800c130040d1080d500103908003030001605108140e8031050380f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 517186330 1250 517185080 517185089
    0x60504061508181c050d0609090219060207050f060c0304080c09070e010f031a122406062b020f070209060d03080408090a0f090609060605030103120804030522 70
    0x2400103580d5403074146603d00c441d040198600d54018031a0180b0f15040900c0c20750319214900b45903090428266a42060300c0c002d401c080c00940d01c0f4025003003181084a80c44d01c54002002c00786400e03508250000b90303542c0c040d101d00e502c40c1640071380951a58558404960005482d80183d030780d00c81c2c48040607607403051903404035030240c281c50001446041c0309100300e036880c1505940383d40d00b9440100e401c0b8081c12051000c84403030541d410465000e82d5900ca480409103880e18050840420030480400e4802e42c0c1500d140030881005c010852203a80c0d0008489001c0d04006d01c1540400d010190f0400d5014406482c03501c140c400104c0000b82541d5801400d500d80c0300720340c2900103503120828042c1c0051440c00003004502400049000507244038007511a03140040d000c00010359840c508070002040507440180301590f20907083c403074000755001d290042c00c0c0d141045441c40d45169240c8000c07030082e40312001000b0701c0502040c2054403603c1200d0308240b00445034141e0701c10194104040000b903124 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 517187580 1250 517186330 517186337
    0x80c0f040e01050114030c030403080a14070c0b0c1305190b07030c0501060f08100b0f151201120f080a05040b1b06010603050c120907080d02100b0312070807060605040615 75
    0x1a80007030b070304617040b01d00ca4080401c2503415901c0d40d07078040d140c032a0702800c246202910343c980c6060011107004200d120701c1c0c140d900c41c00310080901f065015441c02800c600d442000800c040010385034829085000c60310300381d9803010401110390f0101b0442a440d004240c204c030300095070800b8158441c6041e20424001d1000300049660740c1288100707100c0c2889080c0c0c064101e02003400c2285603540c400c141c2c01d20041c00f0030703d10407104800520643c0601c080007031017610209030a108201d80f0304002d405800c4010b0703c07200c1c0c40e03990344803810f0001c5100700c0280414000220407800e140710b24180d0300240302401a13281c465091100b00c20340c007010030090301010303c81c04c800090003a06c00c1c010240100c07030314a00d80c1e00e4501c002406a00e00b0700d00420100d068070550f240055903080401810081d502e640d8050485420000b1a450a482414070b041c2c0c401e610400b010415400d0800841c0d01040c0d202c400b05941c0d10440c030707104016110344c0c4d100651052038090300090782d01c403500e01b44c060384001e541c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 517188830 1250 517187580 517187597
    0xb0d0b030601210516120c17190c05040f0c08091515030304031401020301080d0c080415022a01021203010311040207050a0506271507080c0f040e010501 67
    0x1400c0c9540c407442486800d0096244a0354190b48100070162000c0c014000c005032013500807030040b1030500450f158058015100c400c18003005110703881c601a005000010161401d02205000d0280d0340d034405076000000b1903c0e0401c0008200c02c080924000f448090800e102841c035070818a002401002e01540203d8aa6400a202080041030000351841c4045004a03107448589442c60045444400781e509403100300700201c00b25610240c40035011346110005a0b896040010171407c044409101c1800d04c8500350503640041d5030101600c0035625891914034500021810880c40c1c401c0b001c1d0040c09881c0c0080040925500031001005405000c2c0c00710307110a00e503800c206140d803209110140261032100240d800c140b615400800c0510302580840e02c0b00e1049807a00c40c1802401d4818006505580540b200030070101041440d1201001c8050108c07100804038010802c240181174404000c0c40708006400d4004c0441915801c010040f041c50f1581c0d03c0c1c100e1030003007010030b02500f408246501d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 517190080 1250 517188830 517188851
    0x6240b030403140c0607210f0515150909071b0302061f030312090302010603140102030103050c060901050703080402060c03040602070e10030309060c150c02030703030b09090712060212010b0d 84
    0x11000c032135030941804020001903440101c201c400b6010074464042c82c0004804036881c01c0650300501c51018030007000010541032403240c19500404101c04076010b00303102d03d450b034200c0180b001600c68a140c01d032038811940ea11100d080740da180c680d2400d6960070714020b07007070818103a0010300d25120f030850044100d2203440c059042c2582100314031001f8006a15168038040411081d04610219403090001090058036562144124540106080c50740e1317501000400a2203030810084c012542c2c141d401910b000c20010000b4150300c0b0f01d80004e42445001004207007151190000c8902e0201c202003030313075116034644000a48480030b41c450114541c101d040883d000340880801201201c0d899110406514580001610126040034082c2e0301010200b0302c0d00e42d1341070580100c5884580a0740650f98030001c500d0054107c6618440031070090300a40101315100d1400910785003a242d00c008032003581420740c604100030307104050365140c141c03968a00000c3d00360011809041c06441c2c40c0d8081c81141002d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 517191330 1250 517190080 517190117
    0x110d0b09150709080d030e0f071701230103020f033306030c22060803040e04060513120302070203030712020f060c0f03011701020903010903090f0801110706240b030403 74
    0x204d02410a45812114511181c1d600035030102003101d06180550301c2c03481981c407030381d400c04e0000d50020306114104a1383c60803042c000e00c41c0034800c040358a81811003141c116643c4400041c140802800344c00054503072021607030100204039a20403210b0031000f02d1311203504a0b26801214074030b078150402c401c1c00442d0300b03480c000c80c60003a0140c010b4000441040000310358240c000c45c006a902a86030394460200e44014103000074400fa0480c014071040030309251400380c0841308000c2040300300c3c00c62030107400001406046079640889003481c0258171020140002411071040340c2c0d0040c40302d52a05056000f260300800e001d400903070400c0c20ba5607207994041c800f030043d202da002d0445c920030080006011210000c84407040c444a44400142050090004642190750b4a6015804138114100c2004140f07c002220f10181041100911030071540742d07071020640c0920714008100ca40c980c204140300e181041c0c51500302407020318050103281c0d40c0751072585543d44283c034150b0000c5c0840d040c0701c102c10b50707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 517192580 1250 517191330 517191347
    0x310050105060f16140303071b0c15020102090406081528051e10140307030f020f040902031c030b1806010e030322180b060304110d0b091507 62
    0xa000b03189496611000304032154858083c00300051114141d1002259095400400382d902070001507540c0c1c107240303401800b140c5180114181209076036180300009111220748008031200e03012407840c1820450000d9003e40250804a5005860103c001400b075000107404030700d102c5400543d20f1a03071100441c2c99134505c5004a40384140d401d64400b166143c64650103990b01450010011483c02d59404003050140000d0b16220311740f00050f138047c49802100c408024900c90202c0007050038500c0c5503a903080e00440084068401c02c1d400721412503d8030796030020807003240e0003025280c4404a820500315510f10420b40300c8006468101000550b0030150f000002c1c3c8012131051000c0b90b901c3c88011680307410514000343e0035000c10b10203410012803011000d00c0420751404485515801c0c07242b82c0360070105442e880020941400002d21054842d2403c40307403c07940052241da8031400c3c00012504244041d40700505982820080000001c404541d591044810080444890700d40d084200c56042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 517193830 1250 517192580 517192589
    0x20a0605120f070504090c0201050a0e06100303080a0906020c030703090501140301051c080406030e060a060e01060804080f040306020927070c030c02030a080c0706020102032503090b0a0b03100501 86
    0x41d030200c0402c0c0c0c046501c04940b5800185450401d181a48a035076207400c0e56035140344900941e4540307091003900150360244000c00c44070180100460b1030007045084400e4042d120142c00c3c089100302040c41010389030454030520341c00034400d541e41c2c040c481c0040d40d00d5004820940000f00800300104140d8468402c10003040c503081400f6046034200b10070000c962823550010420040e55803601e20000390800c1c0a040282083d03200000c1c03600740c4a20050529038010404d076602442c0c02c00520250704610400e50549803d0315219843c3c5d50b071450302c082c55120303800c0120080c14010600000304240358000344016081600c07142d0700c0980c540300b248810580000401c1c14103140e8000120460300c2020b89451050091500c002524100c0e000300e420103d0301101a103a85000042c00311080740e0403c0104002d24580c8021480e516004101610301c055114101c003c01c090428a54803287c440c2d007000c90400d422a0004d1143e0071301000d65002001c03841c08950081c00b0300c0031a03440c802c0080c0f1a00d030489 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 517195080 1250 517193830 517193857
    0x150a08090d140702040506190305070f08060609070315031506050f03010c0c030e0f06071401140907180f02030a1d0a0f08210405060a0f1b11100e010603020a0605 71
    0x9807158200805040024899500500740019a03c230f070310426821540110300602c040c1400b107050000514045280d9000141103030311600c28400303d52070741c40300703103600801520700042c40c0f40c08085d0007085150f071030340064401540040303140340426055018600320340c0b0071240141490501c3c4203050070380d00100300340c102007000c58580c100424016842d50503052002401c1ca240a10340c14009907540e00b100741c0a0702c80d0040c43c040f0b5003017500700740300d0400082120a6408841d19040d04500d07599400c60040d0302030105c0c0c14040108028981e000340031880d080ca0310075500d920741b91182c00b00400b1449000100f1640202100780e21003004100120401d03002002d4500348551501c03403110f02c1c2e001038034043ca4102030001001c0c030b00c0d030382701003650041e480360000d02072a04218110340c080d581c98544072180706181c0780000001c280300c4407046011400c9030400340d40d200581a5200c1c00d10001001c4014003e00f8032045450482c819802007055038401c4401c6190241c441c20102d40c5401803000e003040c0c5c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 517196330 1250 517195080 517195087
    0x2090a051e0f0708070909020c0102090316050607060b010509040203010e090d0f02030f070804080a0f1a070c0f02030c09100f0806090303010501050d0902100305091005090318150a08090d14 83
    0x41c02d211300003156200c50b0b941800d02c1e0340c41d601d9158604a83c0188158102654041044122403605200c20460441940302d54176105041c980003030254401d15400510559641e045020070380d009806a40840900520440d00c1e580d6440c86402003400488180300c0b60301544824036005405620284118880c139802581000b1900342c240c00355521060050fa0408418840002c1c1c021080010207906881008814400c01e590300e4201c00042a12100e5481c00000d07908002029900c921011004c507042179078034030140f03281c0c00801d04000c0f807511200d4001004404100705215080c08800441e01ca2080c8012451b80da80d5031940c94103015200000c20b42c2081004000d650b100d50301800124144510001e58031105500180050810860510101391a03404001c04854140062802c5162184091003e40f5089a10f552240f00303034580c81403040c1012541000c40d8440202e4191200308035140181e4070360140c03c001e410150103c41003007030740c8a54900c03220940c0c46062041c6c828846208542c0c02d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 517197580 1250 517196330 517196341
    0x150c2d0e0303040503030d02130902070f0303021c092a0e01050906031203010e1605070b0c0d0213080f0c011704020d0812071106010f05061b010902090a051e0f 70
    0xa038810001462981840240404038080c0e500780004c00382c801c0c204c1001030f42c0740f68107001d80d0000000360b4800c203410b0744180200701c003003285443c5071401c0701d605150044c0c1da469920300105920821041014401e4030340101710080015010386d040302034215128280164507030020f0f0211a5009000c0c40100c1c0860300010880c50802000386908104024240c1d0100002081061540c3d0802d034401c1c1c4014110303400f4007601d070010074440c000d00d009900d0024135003a80f50700d61020303403000540400580b0300c000072040382580250303056800c6814040d6900c164240c0da00c21296651091004000650080b0740050b1000e42c001c0e20a038004130f000710a000490b594039020000100c0c0ca114050b51420010002d6a08045003584064815242d5880e04d5090b00303000c0301e001d0314000b03050304405c0108506050a01c8144d480c8416180d40d050542050b4042d0005886064090500c94400039000f40340c09040c410b0108060300420311450b02040e50a0750500c058258035150b100a0b030300705042e184a240400c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 517198830 1250 517197580 517197587
    0x306060923090c0c1912080c030f0601020309040903030603211209060612030230070f0f0210120f050402060f09040608160f08071a16150c2d 62
    0xd60090f5043e01282c01c108140314020b04091490001c680c0c0050f110404404101201101c0030f40e0b426980b0301200700746800c000f084201c0c840503000302c6201801100240880c4c0c800c1040b85d01e004800303001071002150a280150103010540030440d5a03401d840186100082080072404014001d80d89180b210b0004454280c0244410305042c0c5540e51103078004600040701000c0001e905100764010581582d18014140300c5c048c90b2162031000301c1141c81e0398800c0e03500040c26220b4164202c10402e001c8201403800a80400a02900075040140060f4892103981c120300780001d41c4225110500015040f00c14002c211502224025030082050104150841600700a4400b141018000003000c035140c071400d03440d060800070355082c0140d064a00380161600c0b812442c0c020120fa0004003846030808036901e00c400080c100318038840c0c03000714480c2e80019543e00302210090b0070200c0300300d40c0e41c1c00c202440040c0c1031603100100070801808041c01d4110402c803032011503600b140c1090702c04404110045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 517200080 1250 517198830 517198849
    0x60b0705030a080c04080303070e1305060a14030a0606080a0c0e010f0306020d0f0509010509070501090b09103b0616060c0c1a070e0102060103211e0306060923 70
    0x4240380005000c04289a00d08000549c021070345030300c0b06001c43d4960300c104640c01e031601111803642400c090501195888007503980d0242c800070308000c8641c1181c14007080c40c2c40031400c000f60200d428041e00042c0084007040001c466400f60400f085929250042001c0042081c861407403000d40a0b9400c10200c0c1d6640e016114048000002065000c1405020000d481c001e1f155400c60365550001d100700c0b1034007000060001d210070308000401e24580807810415028a081c0c60380250103400c0950002403046206010714824803000031200c07178010400d003030a4003184004950148200300c4458035031410784266521040030300305441c983c4d28a5076410000d08080e0140c5824001d104410b036000640d110340308084540314601c98180ea14107418000c04003c0c40d88040f030705540103280188041003400000203403c4d00000060104081050030880f414504660a010040d211014030442103615130001400c4910035643e110782c15855109001414014071035091256035560240c004500701501c2c003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 517201330 1250 517200080 517200091
    0x10302031b0d0c1b08041815152a060908160305091503010b070602091f03020703020601050a061205090106090e070e310f120210060b0705030a08 64
    0x2401040c40440301c41d42a402100660035203980f207003510314800d40d01005a5041c510b0f11104504070540e1500d800640d41b08070300608800d41030002440324600f0b0550014400082c0b00840403403503560302c024480b502d60011a9141c0001d46904221001d052401586010201c1031160700300d603030003035644003c0103150030341040f0fa40c200c00b803043d403084a000c2e40043c0074041c003e444d55591b41a11404024400010700c0f901d00714048148018400e41301c1000030707920070315401480180e960840900088110000c038a48400c001710100e08909926410f401800c18513120f42c080f10000d1340c03501c0030440300070080c4c02000001520501d00c0070a9201c141c01031a00900f140c80001081d40e21049200181c403d03800c6400b00603070142d601081042c10b05140d440c0e100b0b01c0d49030500706015920302584e8406000031030b0b10003c0502c424040b0180903094200484080d40700d69800c1c0d1049485e1806500e84240003d0180540c1c0f9100c070014000c030f05c0038103d601c0254402c016500d010b116000645074007501500c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 517202580 1250 517201330 517201351
    0x120f06050109021b0d20010b030a060903030c031b1809050a060609270207060b030a06050604110702033a030504020a060513051002010b180603070e01080c01030203 72
    0x4044081601849101c1c0600030702c0002581e500e07980c0d141006050800c2c4010041644012400080c16600514441054114040c000d025031200300c10503007d040a1450b81da4035004400b8078900b0004c0743e80c00016040e109480500c5118180c52041d001c440c07509080001044a5112690035107100306203110907240a42494548240c480c000c040c21100115845003145580d14024001030750800240402040c064540030803011843c4400050f82c03182d0f03480c0038003550700072400900f00019a084000000030107011901d501d40340e420010003601b019205e0314000c51800420362008032404081364606a00a0020300e202c0054203591500d80c800c4899501c2e14600c881140460700505410061074401156800310700f60900340100040120390b41d0243c4180001044042014040b0101da00100d90003102c1c0c04d880b421070140241c3c0034219110348554024016843e1b00584c2d401840e540c0e00803401a4101d0300c400b521513019010102d0280070b1a152603120409080301503109070011030b40f000d42d109 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 517203830 1250 517202580 517202603
    0xa0201120209011b0803010e011502030702040f02072004110a0206060907020a050d0f0206070e130c14040b04080d11061b0d0e0f0607030209010c0b040f08040e0f0609040c12 76
    0x1440c4c910300d18105082150041e200100402c48085c00b01079050141a80d42d100584600c58010017940d688500d40009014a4941140194000322541034840c43c94102c45d9927180b04030800002a001d10300c5402d014421841c216035400504106000c0d2821000705800500864482500f0848403031801065982184142121440052024456405c5010894884550f80a2801406402d054004000030100142076250300c1c0e569072104621441c40b6142100091481c02510707003141c10400e441c094902d0350400003000900300c480d041c020400c90341a02c09449016403030410444007107002c1003901c00140d0051f00070a12041030000e09015141441c0483c6140030b0044042030f0540d002e1010341c46468200201e0302e000e000e01407040304e51107212443d046180003423a10019103c0030b01242d02030b104404072230004042010340f01d10f59490640200c202501d41e0358986980d01c40c618111078840b4040d2000300407400600341904014001d03a40240b4106106051030344031034805910790400c0c1c510403400d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 517205080 1250 517203830 517203857
    0xb040504051504060e0f0105030c090604200301060c02040e06011d070210140103030f020a26040504060f08100509030f07050a020d0c0f050a14041d0d0206010302010806030a020112020901 82
    0x1384213510080190301000300c07044c0ba20a42c5400c010384141d00880c06074000040d6056659102040558081c03011a0000b92490a90345482c1c80c0c07107180048150003550010002c160580c000c1d407001d01d000c1c0308850900585038a01219a2910028485c0e0f044407107401e401600d24800e051402603208820744101d5043c40a010010b0054441e010b0706001d01214650051081c50f51000605d030100c0c00c2400107001942060707481e20446500c2c103606400340403256811903c0035040700c084070000d0000800900c403040d00c0e400070008e0107100c2c0c41590300e41c0c2303c2d0130f5161955a1060240b10721403a8010041c5051080d000894044c1c0d81c800c0108580c1405070101301c0340113a954110182145004008002089003009184911405240c2000d41b0880c0d910340200603080e04100726026a43d0203640200c1c00f03842c036904035a1030031428014007080303010740c64092600a40c0007545504a074000d9a5544403500c81805240d140e42411074042e00258100240b641148216002805100780602d002c50442c0c3e1407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 517206330 1250 517205080 517205089
    0xf09010e1311030402040b03030c0616110601091407090f030f0f06020310080105070215061207030c270605011e0516140d02013c05190c090b0405040515 67
    0x2445040d180c0204048140f1013981003500c141f200c904401e400446c0740a4007034070516038590008108103020350400a0034003600c2e10443c4540040d01100b801c44126507107613a07080014290000b00c0016241c1c1c480c000a500d544a0f0300c140d000c482e060b10703401c61080d055894030110656101d00c2611800c900e00000000201c2c5403008620441c0c0c10304070307840300b40c0c14050f540d0f003903504c0070b0250400c550046100350b4801031201e0300c6540010b4116100c564400a101e800d60900070b1036800a443c070061007100181a03591084803c440c12052503d10490282110041c011212580505400280440300d000c40d00c0f003100062051400301800e01c80d003049105154040541e08211080b114102c0e403054101d4242000c205031054a0440d000900c42d1000741044100a00c81d100003150800001001c0400d0030000705145001a2102c0c0034213200903e03001d4982d50b0030702031407007001c02d0745450600078004091041c1c01ca10196407542d2102490981b42a04010150001419822000d102c418111810b80d54 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 517207580 1250 517206330 517206341
    0x17070e090a0c15050f16080a0512060d0b0a0b01350a050405030f030a0e07030b0f0f2503060509041209080a1e03020312010602030c0708030f09010e13 66
    0x2100000300040711103854221035074034260f486030900c03c02603410400090780040a58149032115044142c58440d5005c1c20303140c01c4814a805043d02070000780d8404581d901100030314400118001402c0300c0c1c0c03150001d101488980440c00703043c0c001d811011400140040d044041c020384d0515048496074004848100580024803d0011010708892105144605c40b00c5080c0e104001c940c0800c828907168450580700d1184807034505144c040000000d668454607446820503901d140100c0300415228a410408404c0503a001c05517982200c00240c0034440e20078000c1d04c608a9083c00190006c403030403d0040c0140188401c0041c103481d200c01040c50b841d03202c601445107000701d4101da82c101003c0405000070760140c0242c442070304074a00d048007280c1480850040a10b035020030880c60461424200d086019400c000c004047e48000001070f41030f070000107062050305000598002e43d81c2c42260590701e110f1841a01c4240205109903022507009140080c10180003400200310f500c20000e4a10841c0c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 517208830 1250 517207580 517207591
    0xc21010b0a020d030605241b2803120b03030702130c03290d02040609020706051816150507150f0b0906090414010b04060e15030a02010917070e 63
    0x250040361082140c1d50401600f19a10901d0030200104c1d4141400f15000161308009080d03943c0400c0070100307841903400c00f00c0d0080d41001103800240000c0001c1e40d900c56142c003407003203100b07504000c0000da2510782250040d0300c10750549485c0c810032511004000a0003030b401ca15640742c00240582005610390112004011203203020004011840c1a0050202d8083c002c46c001006d43c0204c45441801018000c40204041103942d445035a0607403002502404650300940989070001c641041000072507000980606d0100c4207c08203c802000041d0342e4850400c1c0c8080c4408032904100164069414807404a000d580f43c118a09000d9840314114a000560045030555881c0c13074444800703d031761081542c002011a22008582000070000b1528400a000500703000d080080c04010394000b5849082c54801c0a8020300c05240d443c1c1102404030348c00ca07040d54205010b01001a100d16001c00c6030101d0940c16110322080d0350070401034140c1e003651400652101d1007140b9010a040c0801c076501d51185 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 517210080 1250 517208830 517208849
    0x20406051012050a020906070308060a0e06060d0f15030f06050109020f0a050d090507150f020303040b0619030b091f02030903040b07060621140c060414010e060301060e09090d02060c2101 82
    0x32f081a40c28401c0c0d50410b40e0091032460012001c1c000f49640340030443d06170106259001c41d0310ba03402e0b41110300130304003c001c0000766010701d8000000c00c100b01c401c01000500586081166a036100d01c0b80069224001c251604031b44100303c030700300c2f01740200050030401e000c5050000700103196070b0f540c500d860640c0c0c00c103c211494044014111651080960f034500e00c4a01c051811400c0c05d9030f1f511700c4241c000e8545842070714080b840c01da40300804000c1c0002036411040d200c43d10f0030003546403a21100a00c0140865040e9480d540071a0001390085900031220800290301c0e09103031500b014526041010101c81a94480e00001502484052985a500540d104100a84206242ca40300350014607580016a41000821540f15030f11541540c0480300300c072201054188017240102d4103041641d0701660300940100c00810583c0c0d020811541851081d603036420292160f44001e95141d207102c26130340043e4000f034006101d03d520000600310b0124101c3c044031103031420b9000e025280d00240c0184081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 517211330 1250 517210080 517210097
    0x120c0302060714060106031407030b12070605360f010504080102040608190e12031b030c031b04321e010e0418061d0a03020703020406051012050a0209060703 69
    0x208401840154010210303400e0400c6422070080f01c2c0048c1e408001c007003105050b90b0b84218030240c0c851041003940401124141d82915403201c00180031608100d01707120481203494004500d42c04c1451f05588d560182d0044070030103c1d00501001030041d0035013901ca040000c103010000700e02009001800240003141c03214589072515401c81e400c0000d0040240a0711801c01d816020300540202d080a00a540c408001d552561518065100380c0c803c07180320034041ca0000104003001080c00042c5002d440c0b141c616103500c0071120046d4025000e54050241d051000180301c01c081e00307450b0032058071a520070702c0522175164030000158201c29900800c200031450881c3c4228250303402030714464140011102007224070703405a03a003e006510b10400400e220340d1500e0000604d1040003c0d1980141c0e40400c075822203403280390003521394619110433400742d4207200300071480d407030001440e1412039442d940f005803a00080003814040c202c0030301100c04455003041080c007a0344660004000032402030311407105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 517212580 1250 517211330 517211363
    0x140606090604050408030f250e130c0f0c060f050a0902040b030f0a02010e03030714070303030f0204050607060f09120c0b0c0307080c0c0705030a060f0c02010605010504120c03020607 80
    0x14154010001d5101e50b242008100000c3c0e102015281c0103400704010140c10b07901c07440c8580600c2c4151100e802e08003014601c0c5600d0580c00018501c0650382900c5d1480180010070740d12003a01c45910400005c50000030103264064030540c800e6848038060303140403c41c41d2001c40020100d84013920f407130220325126040542941014000c1c0c0071141403e4000386444131110146a0322481680d60090411102400300c0c1ca83e0741e820400d07a20a260040098103094042c41c00550740d0701d07110b10040f80400c1c101111101003101c07520907071b130441d140680014642610340c0c0d0788170010078044c2880100c0f55560b46480f400728184940b00101e800303a9480302111000942041c01c041d403801410562550f10400400ca241e41d401945143c10000900d4042e40343e803102c1510030b040c0b6281c0d822840d090321a44c0340e00c0c0240900c82e00829207030050303400c0821080345036490481c240d03006405801d000c6101000104007207515090f503d900c281c0615003078a4280e44030390025030164406c81007540d040000e40000c64 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 517213830 1250 517212580 517212589
    0x20d150510090c0c080d020a030b0a06050316030911130f050f01140402190e061207180501080403020d110f0f0304060e0d0b0115030e06043503010e0a0603140606 71
    0x540b03e20940c10040c20142c4030740e81d64209440f904a0240c0800e802164990109000f0340081c601c0940041c65441d00d1a03c4010062403900215100344180c440347d010060614004e05c0f4030500075030400ea644980c0c85117030f4284556003082e209464104d6507a400998003009042c85000d000e1800140b00346283c3d4905801d07050700140d01c0c510144200c2c41003006510308102030007500880045424101400204d884c002150707405100229003030030b90110f0130000802da00903000b035049512115a0701c0d2264494004450388441100c00402591000f990030810a00604041d452014400304440501c003008840740d0a0a110301054030a07a88080b07403c0c8a20b88d000b080c60030700b149065034030f440521410389407507840350300c10b12401900700f02810200c01300d24401c0d0040c0c0b144d60218412181e190901c0d00d00041d100500401a20010a403024015000c0303030400030302c0c0841000410000d04590030f1680030881c4c442d0144c410f11810b0b946610000004201900c024040c00f0100050b003102d223010310600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 517215080 1250 517213830 517213841
    0x81b150708060a06051b0a08070305030a0f09051f27051506010504061b1a0a1103130201121508030a091e030305070201140d0e120705030304020d15051009 68
    0xb51242200b25000d005480d488401d42c1d2080036100018400c3c8a01c6081c1c2da82000c01c0c408000c0d042000001e00c14086c1500b0a0040d4001d601088040141c4081100c00310201d603600704001780103400244094040c0204040310440303483c0c5101001488003000162800c0c0d2160b503106070240002000701d07001c00d002d0180066514411604118600c42c505140002c0161065024100601c025640d000c403040c01c00103220644c8903440784c241c02200170350003410551420121404600c290502640d10760f171403503000c196402640c01001a00700354246a00540725000d400f44e107000129603c61504107d5401c09a80b800102000005555145002c5000401d18542c80e001040103292221408031543c80321000002200e80601d49252142005d20040b54428132302c5405074004100401d00360b02d0072b40b03103078040f680e8001001d00316824805004542140c6008100001d403a80d001440000c003d400d0222214022a10501ca080c0d802c0300700e00c00d500e08881c01510019200d1451907018050004e00344520f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 517216330 1250 517215080 517215091
    0x6010513181d013b031206040e0c010e0f030a0b01030b180a030c14012c0d261306051927030e03070801020c060a1512081b150708 57
    0x130b11080004060f0240900300041d40748000ca011012101482481d1551030428030031940e055907541d041109020095810607070b03202e88240c0c60000805510107000990781e0040710180c43c0d0981030b24081d0108a16501d81881890309401000341c0000062669045d490103144584080485428980451100c0c2d102c407103028207281d1310003110b10b03000c00c3e0868075807445164001140003101000c40085405452006140e440d104003000b601c00f402c60548503c250840750f00c000b294880c00146800316900c08902207ca0042004014250301e07000f0795000403076000340c001103040c1040a840c3d83da04207c40d411122580d1003120711801140f401c880d402014070300040d662801c3c06d030342c0e0b0341e0440c071695401c030b244001c05000b07030002c44250588051000d1001008108021929180c42030440da0312818129016912a840c003882034048141c1e90b15184182c803098030300c07400d5003020b076585e040341035100c2c2a0031040c030741c00300020468441c010000804074110081c600d400c58100301d80040e214410250a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 517217580 1250 517216330 517216333
    0x1060f0803071407120206093d0f0516110a0b19030c021e011508010f0501060203040f03080f0909010b0d0b012115030203010219021009020906010513181d 68
    0x104030440300c175074102c00c0c1d0f01e030100c0d0001d540303e00160005002c03c2015400c41d01d00b08404803c1144e402c4144007000140740e140900c1160100080750032102288465544404508180425000488000440c0380254031035200b8003081e03089c400c00070301481c00960141c4020f420001e0f82c490140040c00340d5035003c61150a0500c40d4000009010792101c40c3c0b40d482412010250a59000c841d03001d403c001c905502c1110000049612000200d000e054161990040301d41040c0c0001113a030300c0001140c00300c41000340b04c0740005065684901e49a808548440001a820b1015185e00d83d500346c03c6900814105540701d0383d48107460318400075141501412030502600040e01101c52a50078200800b00a01d0440003550951390f810384e692548460b00065007541c1302188101c007007003000d00200c07144185034085a9850780c415001c2d0003aa11a860f0007500240e1007404540c09502920240680402122002c02c80540390741202e0320041400307428001603a142e80303408001c0e104580d0702d0420b0304040c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 517218830 1250 517217580 517217593
    0x503011401090506030a15020c061006020307030c15050c0403020f041401150201110d05091507021b0d020409110a23090405120d060e0711061801060f08030714 70
    0x41030303200030a50500c1100b52075a118000a0030665092050704803959002088041c203800004000340250003805040317903540b01d003402262015103e1450001240c0f11a8021403414040307540441c2c500309010401c0301c3d20400c000f001504035031240259449084407202c500d449034903500402080f10300603181d0724002c911f00820703804060091700226054414000c2030182010031800c04030300400b562035103000d11b04404035440b0460385890b000140108000012601009001280502c3c8180160780c1140964400c02c800442d50303456440c9400309000040c0480c0c126070458000c1400d580c800d488c12901d030320202d2030550301407a02c14a49005003008541c0301101c0011604180c50b03110b0000781075845003034180300040070080704110312445500791310070340303038440885905500240189000c0ca84401e4074a80004582c42c2c0301d08130300e05d5880c1074800209221b1725081600111556042d40380c1085548900002c104d900c00f0007842e000801c9444000d5580320020b040c2015680d00d02445240c00e40c00c5131 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 517220080 1250 517218830 517218851
    0x5130b0c0a02060c0709060f050405060117040b041a04390e0408040308180102011109032a04020705100606090302100f0318080306040b0306060a0e04020406031703070306050301 78
    0xd12000000d5040e540d02d661022000d00d04c515001e419441480550304019000c5a0341c0d4400301e9010884200795828026174680a0054407800c091455a1811480c1c1e240080c0200b0200070b04282c22501071107803045e00100142494000030001c8034141d4210b00c0d0500317814041d000f6825044181c50154100014212914242c449800150b02c01c1c0200d1483c440c0101d810b110800d0102e500035580001210398800316220301e0051140c0504007d030240d440c155904801c9020316086a040c410010007400031959240c00ca000c00080440c80d0340030800a11b101c81a0070340341c52000b0039065014500a000701041c84803280240d55440e08400200401d0180810041c5c070385240c100f15032141e50400980070320342d140d000c800500c505071079680321001c1003ca040a02001400941c05460291420b00c00c0d840c400040c15501c00041c0c0e0709540003c0030400c100001c603a655003140c2c20500c003c2021a5459903030720b510041200301d401c036804c00d440000a01c00d03460317018030900c8000c04058000348a040d090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 517221330 1250 517220080 517220083
    0x30b04021201081c0807051b070803160506010e010b1207111614030f03041a07021e0108060f0609061602120c011b080d0f020904240b040b04060c0302070801090305130b0c 75
    0xc4c0c43d22310b10b91661403030a01c044000700b440b0260140004c8000c60f038031004844212580c145940409455900520002081c80120f80c0f01860580d031030442c2070340c03800d0310b4007503014407804005194008015204900e980b0001e02448141007882004e192244100d0500c2183c10ba4141900c100758030a9120004190100e800403080d45c04541c03640c51890301c4141d45104150b194420184001d60100c8909001c00c807880016249481050b4280c0c1e41c901d01d5510703a01800f5050400c0084a50700400a10031051a4580b44004080c1301d07424100249181c0e82e2035011070244441401280c03036035044000c00560551f80310b00c0c96110141071080303068115005417144207452142c26074103900c441e02c40f021a40c1907941a0110784141c08058401c02c884c0c81c0c019a1440c1120042c04059680c11040000099080c003140503a0140c4602280403440e00349801303030903030b50040c07402d408500754040c0100005000a081c852401d44a002e0345801ea900d6075400b08507410200907402c01200743e20240507441100b1340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 517222580 1250 517221330 517221337
    0x50405120616081f0e040b010b03451c0518010c080405120705120f070b0d0905070e040209070c030e121e0c030c0d02060a030b04021201081c080705 65
    0x240d03402c042d0129104c0d5800069a001256a020441c58441e18000794200f201004c4901c5140102c0040b80c299894101d018007a01c0140e42091102e03000c00c8035a02c002c5980d50400c130b2020491030101480402c6a07039034005103140c0c5262220340d604016401c1040558170521300c0c2c02143c50f841d05520b4691000d00801c01080409005810006006200004c10401c3c204842c0948001400300405640c5c41260f182d84400768040c2c03500410403040a0030803000005500182c1e03524000180c6030090400b2002030745500701c1e4111054251300c42a40e03002103101807220902800c1d914142180901c1c250041c0500c6c200046d01d030074204141900441d02103648484003078901c0b502200c1030092500c902c8209450904845001c1240d803007171000d41c40520600050b0038220810a078142e0342c06880c0f000030440e6407041c00d880030f500645c04000d41c015a80c860340c0b004800d00f0b4001e0006050014079043e003003001000340c011805682c0548524800b90038640407590300049a4542500c1078503098100426600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 517223830 1250 517222580 517222621
    0x9060112050901020904090605070905012303060d14030403050706090f060e011e17060607081b010906020f030406050604060503030d1a1522050d020105090105090d030504051206 78
    0x40e81e800c081102c840080d01100c0600d08001c0c402e002c42401824590700801c01a00d070b5a0102e13070b010f500043c40c4d5010722880c54260242d00485200300411403841d152070307400141801d07440030707074408281c3c00505003400c0001010341000085071140d0031490807030b1816415070400024080a09004c00840020480388400d44540307151045d442a41d810040c3c4840500ba804022458401c1060702001039014982c885c0003541c0d0b4241100726151002400380a200b039144c09081185c01300101c4842000d07000c0d821495010000000030362100540301d0604036088100701c001039810001c00e000501101d8018140c114004031001c1180c2e62070440020354903c5000120200c0b280caa8403001d00a21000032500c004080140c074000b01002c0740d10000c01d040c0c2c013070051313007904000182c45c00f00d0041d125100b1506a80000e0417402d4190019001500c0c5500045809410130004200e40002c6840c1c0d00e83c0c142450b07100f0348580380c8460900c0c0c10403181c1c5000d0200103043c0d81c030410030852511000c551880707005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 517225080 1250 517223830 517223867
    0x3070210031508010b1c0b220c0303050d0e031216090504050c0301051011250b0c0f10140c0c12070503031501140a030e01021c1406090601 61
    0x3021004080d009001d142c640404080010100080e0070301c0190420100b80034101d550b8540400001c08900002ca1901c4019040c91114030024624039000d00801c3d00150400300c00c20100c0e1074039603898181040f03031307002100000c2012800741e4201505c0e00900b8a4940c5003c041d6050003202c0010810b140c20050011504d0007100c03000f020181d00800c0d03004041c000c003400c00e01a0345814200403026074070030301c0340600403a003001d440c840c442e00c52840c00c090190200050490150101c1708030010844100f2542c005406a82d0009100781c80803004201c0c14000d540a03100d00c1803c08000b5042c810014444940a8280021552540905074006901681c100c962540350018400503a180a0a07840380d00304a84000680c08148603002010314171954100b585400004098030045610340380c401203220790704009000340c41c0c40500a070040940296104001410100d0020180300100840c0c1c03194001300740e0b61000b45214804103800070b039114034141c9000c0064204200000d0007012100040a0035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 517226330 1250 517225080 517225099
    0x50907080411010e060d020301050f0405040206040303030b19030f0b0c0f1e07050f0a110a030c0905041a1302030709021303082104080c0f07060e19030b0403180603090203030702 78
    0x903a028444c13074901e56401601190b102c200b03030302006000f54400e0089511407224030094140302d207418040c003032107198060021410103103156001e80c0a400d80b07040e51a8800c3c0843c480351040c0030342880b828021401680b074414203884a080401d02000b01900030170074984100000c83d03244c0da12404507180361519425504207207450103801d0a041c01040c0c4001c00ca402134486103261030000040907102d590092480d003140240320005c00040c291248402001040089810000310425500459225001c0d9840c00c4130054400503503981d90b0030844078280d0101c000d6040209508040041802400060104601d02022050f800c00c00c441107100052aaa6002403220318203c1c4245500b6a002c0d00180e00070b0443c10a40780180c001c0d0469141000d0b144104008201c00e039000248410448140d40c89040d021003400e03050281c0e4112800c4040d0711000c01000c000b001030b9444c90607921540c06a95a448203810f541401c0c501c1c0c0a181e81b00b1000c260910810a01581d40803044031f088541c1210750951 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 517227580 1250 517226330 517226363
    0x6070e060f03010b030118060608060405061f0225031e03020f010510090b01030507080103140106050d05060f16090501030504060e011508070b0a0903080f160303090209010509070804 80
    0x10314410300c92001600000440009084102000954161050908002c0d21424201c04040484116108580014928801242d52414183e000980014002d400c40e12501424282414480b403282a11f20060f40146e01016107a21000426100e01503070307031051100546152140049400c0c1a94604011500003921000f09802000101c0782025490024480d503d45040c40510300c100e1403155240e014140924551250b1081c400c0910801c0c15482d1401c1070313402c1d52901c01c4c4040104008000f20340d602c02d004a425940c80305084040c500c950018105441c051703001c82c1c14003502803c840c10310003039681800380160f003218408040e10400c0c640040d840e41c4c0c6080c21009013000120342c020552070109020404180031040500707480080013256400c560f95000d20465216890b8407000150080d4030610024000c40d00510161181149032410710608078250b01244960407812000309079203024207030842c20042c4801d401801d0888030300b00207140c40c04c4040c144a400400003411000d04410011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 517228830 1250 517227580 517227589
    0x60a05032d060106020109020a0e2e05030318191d060d0c080312240d0f02030712120c03052523010e0c010212030403020c1504030b06011106070e 64
    0x8000d03401030441e0b03101c0d41c0d2440040d000700101c0b102607010782c620040101d2281c5aa103881070044c85030b031583e44c001000301810031181ca215020100f44000c03c8440000b1381e9a003c00c081c0c40095084242044140c8003134003041201e030000710304211403420f41c560802525819064000d0074001c8171480107010354070840012111008400000c0051519144c00b04422800001500e40d078010044140025110086007507a680140001015411b0f03038403016804c5418100c594900e82d07442240c0c0c50f281c040d0b9650000341810b0f20303508103030346400c3c0015001080c0100d007041240c407a40d0504045001400a84004000744500002501514541204884504900d401205006070030004155030fa510703001509013010030340540f8032042e60030595a0780d541c04000c00e0a000b41401600200001d4900c010241402e410040065055000d002542c1c0220f03141c03000112030011001c0d6613280c1d82c500f540788c415112540603105c01c0c10030001110300d01c0c03c1580007803200c1e04400f4504050040b00144c0c00010f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 517230080 1250 517228830 517228903
    0x501080c0405091003061805070b0a030f020301090509250b03150301060b03090d1701050d080c070303090e150d020405090a060f09030905030d2307060c0f08060a0503 73
    0x45400c8010340f0104121401180785040c140c038072620b000d003c604610005000c0203854110080c005802c100010032881d106100141080b00460501103000c00c043c5e005e04040f40c02c241d105c00d0703900ea00d070010481030940502904e4040c60301c9000b442180d052980009d00005128000c001c85640004040303091060071005130130005034010000e00202d900c038aa95001da80bc00d0b070701030390940f00b00d00110400e58001d484118034403020000101da5a80307017608010540070501c0041d42e071044100b0880405003030512040d4003550290701e840d920b003440d2040780c141d0000300910b440600b21a1a11a031383c65500c4034601400c40d601103d01045030340700e40c0c04150419481000060605c3c4c07601034002c105a00681005218900a49945164603940e03c14540c81c0d22405516900180001c800d0880d002c0d0fa6003140e844c5800c100c0042c60821800e81e4030b1a04440b00446241c020802d8460446012039104100582c40401590f0341031134a86003802290341d82c442d0303020501c2001480b110085150700e0038040c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 517231330 1250 517230080 517230089
    0x612020a1a19110a061e0c020c04090303020c0d050720010c060c020331060c05060f0a090f030507060e030903070b0c0a020d0c0801050a050f1303090902040b0a03180c0501080c04 78
    0x2510341040c4c4a140c550014104481100302c010018604020242030610800f11102010b80280000d6010202000010440a0011014541c0c01e100300304031500208005002d081a6440307841d920200d82c01c020a001c103242d112a6010705002d040051280d0388080490340e10750340002c021400d1001944140d0860085482801a80b01000310906440c5a0f900b0030f08041141b100350b500e000d9440701002c840402c5e041e900500140d001d01e000c07540602107020003507800342505030006010200d607a07681c4080c0c007520400f980000d80c0482c41c0024002d070380c4954103940400d600150f28190420000c2038840001e403040005240010420810405041c0308295151354014035018200b41280740904c1e160f115406921aa50300e000c0000c0d41517891407044601508807034004484550750205418181c0380802011020000003c1c000594101d050015101a101d0b100b84a0b8803500301070760003421640301c0f5024400b004a20118503000c60329100400013651428031b44503950b5078031b01e0681e18403803040307510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 517232580 1250 517231330 517231333
    0x20a031202120d0204061211030601080a020f0703030207050c0a060e1002070906031a0c03010506090609010e0904140c01021203010e060111030a0801030c0b031005040f0905010612020a1a1911 84
    0x1c02e103e0b4a80603900600559030103450742c540448a0f4141c41c000c440752204a41c910341020008124658050365205510030000c02c005480c08a02e100750f0303c0550468407086010a4000c1800010010144088200d03c042038500800181c07400600424443c100c04820f405402c1d28040300034250700c21710203003003d80083c2d001804095524a00f54000c0400b11070341c078101c215000f002c104e51031042000c1f01e04a580090885041480c20700030411664003e0280f103060000740c03500121035884d2001720303038440e0b8001c82401144280e1060348070b040040a000c1a4119001403184031030070704c00301c000c3d40e064641000303900b4443d5562000581d00c040c0000f2543c5164813000c500c9040a9034045e580b1416240300f54542c0b04501d980d420b811055004c1640d5081c0700207050001403060341000ea00c100c3e0840952200412079944a4440500b1124150408089010510503290070b506000d04450000d040f0b1349000a01c0d4117010ba85210a405060440e0156094241004404510a00980340340c03028000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 517233830 1250 517232580 517232587
    0x3020403020d0c0317040b1801110109060e06130201080423100c090b0306100810050613050a05030609070603050408120a020a0e04061401051336020403020a03120212 73
    0x804031081c3c0801e00c01203032800c80701000d0b003d002a544060b1002c0380c00501195083c10103204030324006110f003150a07410850b000745076080068090107025072290107075400107080351072109410304100c40100101e9025101101050050b40e100900c158000e800c401241e0440c0a500c00c910300c045668460080f6502c200000804d01d00400e0340010b0011180c0d8581c4d00b0b11a64aa582048500080b201c0310b61007182c1e010040140b03802407a1095001d100d440002c0ba4244d1110300142041d0040340c450781d600b142508041c022070400d00d000d180548400c44c000c16142c507002c1701a540da02c1090040b04101503c9401280c20424010141d4113032002c500c0940c1024506181804002d40142c6d1400000643c030038a10409424688180e0301500ca1100c140908211801c0040d19113a02000090b60741403165440001d00740d01590b89041c503101210740d0304860740c101154151882c0401c1c00840c800c00d1040000308016078444008408407a4482c2c4100d0101c04018404e9041c031101c040c00c000c4002000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 517235080 1250 517233830 517233833
    0x10c0c080319020127060e0c040609020901110109260903060a021918140307030204020c0d120b06090d1e03200313092c010b2803060b0103020403020d 66
    0x203154418800d0b50350003008a070803040c1c8550007460001d600d01140001c40c02e40d46000c5803558011075034004804040340c00100700c00010a04545041c1e001c405025800700b2042815030b4403010764481304600d14001c0c07241c030741641c442e400750000d4180311240e40c0603003140481c00b0307000c0281641c0c91800300500b030701d045d49450142c500103036001070040c0030305416211035580300e180180038221200d60032601020713944d0700f0050120000c40c0e004411aa251060340710000050307823640010050680c80c5000340c07800c3c1c00c0041e000f030070080141c1c3e694112117044c10040002502e40c40d00f510703005a8115044c00c1c08016078101034040c201c0a4565195209804c4880030900d44c208102d0008039440c3c880340700c0b001107000c5180d0340303e0081c40007401044459450810081c4180d03003014880d0810101c070f503000e40114001801640010000030a10359450f084a4030a41c6007c950030080c0700d40800a4055080d948805c038064550356000c0180300301e558800d547e80d680d100303906039401b4580c060705005140c1500d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 517236330 1250 517235080 517235107
    0x28020f07060b01030221130b0a0603051915110702091e070c08070209040c1203090603060b072a1206050912040807030b041a160f03050105060405010c0c0803 69
    0x340c04191011070402c6020240c0e94824401c0340d012242c0603000c80a0701c0c0c040524205c0d00c0c10040d1036030015602c180c000f2404240000000c1d4080c08405400040c4685149003490829841c04405072004601003800740c08550560340c0440105e0402c20300260000340e8402c03284903400f4200c0080e4108468400b04203508000303040b88024240003500840c842c1da10800210b50001f411480107145400910603540141030600034107800c9480ba6110001154542c0100d20392552043c00039800150515020400580c15109880242845010b4149842401d80b62207410300b004880544c0805140396a01d42800d018001d5203003c0d011080350400d00c9881c90030700c030001d030100b5a07000e03c15026502c4042d1440c559241210b04503200c01020307003005461b54441000c0420010002d032054001020080b02c0e0200c0b2540c00d610800800d0042110007280e20001042c1c00c03c09500c00040c1440c4c04014010740c0d81c0d80080d90102e8800b4648288501170900e040074032001613500002c01807002203854401080c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 517237580 1250 517236330 517236337
    0x10b0a17010315050c090d0206090301061d01060f0503060d1113020406050a03150e01030f080708040f060e030706082202030a051e01090c0509090c10111b0928020f 72
    0x40100080c8100c0c1c41e8064099003900c1680c6c0003d074400b00040000b0b0050800c41d0150168000003000080c40603600c20125911540802006a075205040c00501087c0c0c3c00602d40541402d0502e0142c0c214030741031010139032144086201a00d00c00d202454100aa52080c1030b2400b541c44c85803040d9140c5644200160158001d910004042403c0c451888d0365403c104d01074500706d4540c071072171000300c2c5d1840d00c0b1100034603513400301a80d00321001c02c0741c170012607040001040100501d0022541d0b051034808020401454018524880e4121a208001d401e5000b01000e4200d242001400c50100e11000d00004280381000000d4048c001c2c04404014032501050100c0c0100d1800c5090040b4400c4000c1207003207640b064001064200c414000348403d0412481d2a45e200700c0302c0003210130440d003a0000580000040e4290070000300c0200e04003100c08814004240d042030342440591131420300c07a000901c00c01000700f5143d114401c00301006c1d48400c404103048610b002c526411907460a0011285085a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 517238830 1250 517237580 517237613
    0xf120402041d100e01090c09090c1a0304170a02060a0506060d091101090b04080318042408120a0e090a091401020405042315031e010f050a060806010b0a170103 70
    0x915010130f00500d00d0f0103000761440e02e940300c8502c550050422000c2e0008160402d402c0e6060040c0180c046071503d00600d045100e0352120300c550b0340743d01d418a4500c20860140c040426030840c24000d07549011740002d820f582100f600ca10100e2182d8a8001003461406161614a940f42c2451803030410310441e21040b41c13661100b070366030000a507240d010100030f500c16840745048680c1308010f20346440c46901c030001807200e80100080b9070b210804000301c0340d14041c2241240320034042001040681c004001c9030400403103014a90342012081e00300503002c140816422405105032000042c0310030b10725400702c9181940f007040085900c10f1000c0d41030007900b045c0240d0340070b94541004c000904002c110703d01d802e070f1801c0b1206840c0d5500c602c00300314924a22a00f2a405200351039410001c0180b61800320f9001d0944400054110502c50551042d608080c1250701003038036040017408003000c04514581991000b03840180e88074102d09080302d08072814901e00742c48861110000c400c002c1356591084441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 517240080 1250 517238830 517238863
    0x3020403050f07030c0311042309010b0a0506180310060312090f0e06060d0f0203070302130f05150304050c040c081f0605031302030f0a1b0b0f120402041d 68
    0x10901d0209682c0e6103d24000500103440d0488100300244440c0d0307a078590403001070000315a05003265400d48450411008144c2410a100208002c4401c240704035109800704580e5004004d142a011414521a000004030707003680030304000d00316031020041c0030401c040d02c11003082041d5582c103044400c4500e1008503000582e0350000019000c40c05041c0e070062710900300303015495860302c0e420400c031a0b007c042c8215469840780845211030002e8800303588581c04944000d070355440351410a00880707032141c114903002c5d1400101800b80751078000c1c0c4c50340902004005681d880c0c5460405915000d102d651050f80b0604041006100550000141e80141110428503103031483d40c00c02c0700441d00a5024040c000340e001d1000540202c074a001d1400d80310300140660300c0e44104d42608074101136445005550403505c654210050001d40040c0c0002000d1010300c0c0c2c5d0501e0041c0102000c240b040c07810140c1b0355803140d408181507584507070000e00741c038a0340c0fa40010165101c1030700544a61101100600b46e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 517241330 1250 517240080 517240093
    0x13030b04060c020d0e0a2309090c010e030f07050103110d050106030603060c0e030a02090c041d101d0703111c0903030f0b0609150f0a030605100309080304120e040c0302040305 77
    0x12401001c0105022000034194100c16082410380800703004494011000003401f0401a001d41e10361141d100e004000e82e002030900c4c103000314005060460000f280a000b40d010521004800d400461000241c0d00c0928020950084215010000740192101c1c86201d5242030b000081003134048e03100c00c040300e00c6040e00380a802c0b907814041c3e40e0781d00d00410710380c1c02d0340005845c0720051401c40b80081c1c3c00f8841034422400e041d22803525050541c04407009001441040082c800356620f8143c07940d0041c1801c4000001e580035803d01404954400707414031381850345404500000d805103c0648000034000f06081442c0010ba400c00d00c0500f40c07818054003c0fa03c0e160341303850f05a0081c0141c2c0c41740e00003d03000c3d5140003140300c02d2018a142c5020541000101403096441d00d1684c10001e08020010381c3d80892068140401c000744140c08c11400414146402e0301e017400103102c101903039409a0008200d01096007004802e80b062800d80882c2039005280c1a02c9041d00c6800d94050401d6034020f80440300c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 517242580 1250 517241330 517241353
    0x1404090c090507030f020702033703090f08030408121e071a16020d0c02180408190504050913032a060b030d02062205150f280213030b04060c02 63
    0x483c0305421f00031707400d0703044880c401110340450841007038090041007289841e0909080c0c48011281c10100c11000506c103c2002c001c142143c0200c800a444402c02843c900740c5801d8200381e40d410418020040c25002081042d81a586200e100b42e001030004580c1c0d90b54080d074a00b41400d210300c52408a9506907420102d0441c01108186120103e050340042408420403801a07034511a4241c0072039100e2003040d200d002d000c0d03200240b64041e074440c0030016120250110b10700788042807021503004001050004000d030340e4903904070720780000b084203094004210a082c120380341c0c202c40340e8980402603004180c1c0d0b080032800c0707061480340d030240104000c3c1100308400c15031034660b0040c25400680c48007000c02c4c080c0b9208155248000005240502c02e2410750f942c20b810040714120440038001c0031020050300c400c1c050000b9602c85541078024008409a070410300d1021078103001108280e501080c07440f441c0d00000403c0001d15082040d5117840d18141c9021030203010b4045810005001303007400b1710b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517243830 1250 517242580 517242611
    0x131a01110f0106091d01110d02090f10090806130320032214030c030706030518150403080a05040203060f09010617031905070c050f061b10060b0a08011404090c09050703 74
    0x114000d44041145881c0c851480031000cac4d00598919035010301170ba04c02448640d618000006102c4040d11404585803401d462581840f00003000403c09020384551000040e030300c0baa000300e107140000c02104000d4016890949140901031141d00d04016441c44100100414605101102e21044007a00346150030750038541c845030032042c0d2507050341c442c40d07040c0405402500030f035600c400c0580ca03201c420070701c0c0f1204516000103900f141c81d160b124003040c4001c0c16401072001da8400100ca80500050800c0c1d40402da44020041400b02039122010118010020a404c028028080c0103550982c2001da00c9559840381e02110011402d2500c81824281103401082501c05007504110445481c40c5010b0501485100019101e603203c00104011400c030003031240704525110307680004208003061781c1002c0007100c0051b0005c01030110240141d11800780d0200003141562589104030350105140d03c007240141503200f03c0203086128544021a805201f0352010380b02d0300b4169001e012107100d030000e0f0b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 517245080 1250 517243830 517243841
    0x102071406010602010218101103041202150418240602150f06030a03030b061911012a1214040f0b0f1003080901020a0818131a01110f0106091d01 64
    0x8130860100a1035151f44c5002c080e2585031495504001a14003012004142941c0c4650084c01c800d00607a21a00b0940c14110500b05e411241c8800700d81c5028140f01d510940340d405070803444030303558544460079000c1d070b08101c80c0f0b0031040010680d500c0c03041d124140607459140310400c0820789200e007000901010b10000e5498041c0c00050041c01c030004054908801804100e55000c1c0c20400400405161108250b0000f90f19102035942000304c2d0102d038070550a440001e0303030602c2d840d00c84d06049000d00034071480c2c058060040703085c407140c040340c0c501d605806080c1300284e400e81060903034200800d110b42c0c40d90b1290b032140b050251800554a2640400081205039107035041702600740b5050000032a9030004080c4688140100d40030318800e952186100d610881c20310070303420b604074603031006070510000c801d24410045c542070100c00300c2001e440c80540c00d000042810031018140701040100103025080c1404030766002408034507280d909240140c501e50300203d0500c89080c405910400040c40744 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 517246330 1250 517245080 517245097
    0x30f0c09010b1b07060302180103050f19060504062d060203040522060323070b0910050714030703080105091b1b0102120106020606060310031e0501020714060106020102 74
    0x4100d0581d0034000d880b0074a400003074051203815410503018070714003400c010388030003000c1c103075805aa2082030368280e1130100b88800c0110b0506080105020040d80d00c452126031000f090700052081d03401050f04074010f00100e610064005140c42ca020400030f43c00200074407031462400902d10182246e405110300c0320070501c01c0c0340043e0000e10060080d85000b01c0324100c00c0b220070000ca802c4a00c05461002102c1d071075401120502e440c03103581a465150f01507403809280320034002d007c0180c80d00004c2080e40c403030503006901c94120146103054690182c0c00f0b581e12250414041c082110103510540e6996215501c00e40c0407030f0700c004c00041c9524160042030310840003080c0a1082130344955215145401907442d212410303500c000e00492101c001d101810750035a07400c0c0c2d0040c1651410700041d0a050300038100f00d000d00c00410400c2a2507580c16201001c495000050080c81449050503548480d86000010100d500000c0c801c0c00380103d00409030756084800d020303190942d0381d40909074200c0c85030000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 517247580 1250 517246330 517246339
    0x301120b0615040b070309080d080105010906090e0a020c1504060605030606040204050d03230f040e090f120c030f071b050301050712200a1e050406080c16021e030f0c 73
    0x21300c6001e4500740685292807003401c0401a00c2d460b2403204d401c103075180320404001014800104180c0d0390201720000104550306004000742d050111807001400020100ea10380c47c1c0020b40c403c0c0740d03241004070700c0c124410541100c1203420185042c0c8050151449090700c0b911500c0049412031800740f08850448e0301c0103100f000003500555058030400400e0b020402c1504442040d208905d1a0500030911100c0c10164541c2d942d041103d00c86040802038280d000755841a00d005641c1a1f001440343d003078844039444182c030789903099041441c62003401c16130a0880008113001d002c11041003407941e08101c00071006194152a502030500300c2d40708a0b1014009214821507820a100ba07a0004c03130a600c200c074080c0d40c0ca80e414080941c49502086100002904449140340d03d1402001c0e41d60907003910b840d00a02d4685002030041c902900a0300c40c40c1c6000d030028284407080c2444485d001c03603550103002342c60350380c40003880c4003c0403030a417400b01d000b40501d0180c1d00c004c000200340300c000018000e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 517248830 1250 517247580 517247587
    0xc0f1e0c2103031a130f05010f050f01080c1306050910080f0c0708070807120f0c081911010f050a2d0b010210050a270b0703021e0301120b0615 63
    0x2c034114050010410242d2002c1078088980c0030507107420b04000f84840340e000d808030342c0450002c000011240140d01507480601a140c1c14041599010000c2541403024030748065070340ca0f880701c8508148204c030070300407141000482c0058695045000703030290a4044800c01c0a86540d0402642d0b4044115011034208005000103440b20040320094101c8034010780c03010741030089642c0c034010b56600c1483c003030300c40d14090f104c3c0d44213150744480507509082081c40c2c081c04180081c2e5500303081c6d00410207075946024000c0004401d903882060803410000c04203000f404020000c020380c0f03000300416241e0008442c04d088200740d8070352100600c20039041c004501c12800c01000c5250b20f0052803001e03c224110b00640304103070440d03450390290030300603a1402000103401216401010030b080c9544048a03190b05005a41c10106195842c3c1d00d9101c142d50601581e1750050a110498200510420030030000e80400040340d41e24217060b03181e0380c2b544a0280d10425407203043c20000c0c485200d215a850942c2c040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 517250080 1250 517248830 517248833
    0x12d18020415050301051e0714070803070c02030a120e030102090f040207020d0b0108030d0f05060f3c030c030106080a1b05130c030b01050306030d0c0f1e0c21 70
    0x5034003100a107010b04401c0c0b420240c451000a095070300541e42d105c4256800c1a40110048402c88034a0f04041c8d6410509810000070414000a000303505e406008000044001814680220400078407940d008041c0c0c0d05072025841c3c035519030f036042e01c491000600c803010442c480d400c05100301d450310f0000500c441040101c0c001040041d40c0900803c070b8016005e9944030700010042c0300310038083e1000e00041e649488400c80c00c801203584210b1411081d42c201020711101d40c4403040c040e010080c0544007021503040c402c14404007040d0118070020b45070507509004c2c82c114018010020350550440507100d00300381d99002c042c01d862403802010320310380249600100088041c42602d18000f0624034091010350313a10b0004603a0804189080030198a440c040b0341c03143d030305100d0110408800d007415811400d210f0082507031890124074102c10300124a5150302030100422107150140c0c0e000b490065000005821892070155807007003150001c0b8850000328114118170300c080b2a180c4803070400ba4640d80113 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 517251330 1250 517250080 517250089
    0x4180615020c0405090f01091a0f19380111030304210e0316081e0c0607080f39030d022208010c0e030c0303070303020f0408012d1802 59
    0x10381711088611070410707940c002020a0094035000340c0a03c8156119210391080940c03c40c200401001e0040d04c000c00700030803070107078800c0c000d00100c188030001401114013600048045c0095030040f0f500781803a040c049c85841d1106038182d540420f07a00c112450042441055076804140c0300140030000015407c041d102031030414080f400121310309a107400d081440885c0c1081441d11102c500280450010b000050040010104000241c4024140c1800302d81c52544c440a10760b15003482404002412414414402c0560f02e281c9a0090025a6120400540e810320301400b8100b83c4101403c04010003810381510030190f03a954038001940c6880b80f1020000c0c02503121003160700701c0742e034001d4003510107801c00c2e40d070703500641110000000d100c4807480028240000b485e884a2003a0300a1801c1d240540700030058442640d414100075841c0c0d02c036509194010b01454101c030038158607018071408160024050310224246403680200355070b2405001754107036150200c80b0440c40000301c107100c006040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 517252580 1250 517251330 517251341
    0xa06051801301a070305150f011d120a020103060b071a040309090905070e060613031106040503030d050103110603240406150503040c050105040612020f04090204180615020c04 77
    0x218244002d011040b940d03049505400209840da0040345038003000b00a60701841410303003210503010202c186d00b40c000300140618001105413810401068100781d076940b4071080380c4e11305400041050b90610b84400c4442ea031703400c008500341d0020b8240400001c00b41100d4040720a040c1d0403140301c070060b500340c8142e4140024094421002c00900200015410400307205001c03c807071181c809000c0407490b111400c81c1141001e4a6503210b141c08000000b0700c1e000c0301340b0700c03401c8962107880c40d0300388000308001a00c14000c070b51182d90180000140c003005000581d2004e81070320300c140711290b109911030007030100e140412520221446a40d800d07052a541850101e01b81c00c5d94001c201140305511008450607142e40d19541101250b0048203100030051030b0f04d038103009040c0c01e20380a400c007403600000910a00c41c0740000b80c01e003540004c529580008100480d00a001c20380c0c5d05540d265a06d0501010045182c200040002e2902d00042003c11b60260307801c4903405281e00070b01d0881050700804c401001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 517253830 1250 517252580 517252649
    0x120203060307090911040c0908031c0f0e16140906060d1d0c01081303021f0e030403030c02040e060f0105120c100c020a0e0f0c0705150a06051801 64
    0x10410b400002c400c41079000d0300b40c0c294031480120402c112500306110a030b4181d40e401c0c07424046002828407141100200f0b40d003400e06008410307101e2200c41000c070350080181a451020071420300090b610040f000044800d40d290490700c8181f041130741c44842c01c007240700200b19035901480020110300c0300d2030b014026001d0029a8000043d000c24a0002c8081001a582282d40d40b0303045407450980f00c0d80c1107108541d0104011400c0c00d450400c66500940b00c40c0340030020010340840c1c49504001882d59400400b0884105003203d0780d85480781030280080c2e0840800300c0c8070390705068003188081404640300b0301521610500c5c4181764209010080545030784a2103040d54451443c0130fa1003a0340344510ba010030074490701e518290490a0060180864154006158041040091102c800301c04001c050388008400d008542f20000b500e0f100381805803154038240442106400c0c489080c1442e8822003c54200b22002d4480508c405040880900241b2444401c0315034008220606441c003400e015007072 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 517255080 1250 517253830 517253833
    0x4060c080913090c0501020d08250507050304030318080102072d0206040b0a0e090405060403080c0c16082401030609020315090307061d1f02040803040303030b0a0909031202030603 79
    0x41071059800040b00c2080e0f0041d140008007500402c4113503018860100291060701d012481840e040201103010300c1c5c00c844402e9400440441015207a2140064800c8180e0190503255126079038100100302208001080001c080c041380c00003580ea20508c2220041d540c80540c8903d03041c44820711140c5c41c000c0c0e80700ba80070b40030326148910040c1d0f2620028005841c01000c8580c0318440e040700101849400c1e81014040c1160300d06200c00300703000090880c0c0c81945490110b00642c0c5690643c04140203000044125104130701001440d20003c40f8810241d420000407112132458210100100da02c8001208810203159130041c00859010381140c0401800903040700c84410b02c4111202541e04c04403000100382d0000b1441504014540c02024074004c034080b0a01d41c10505001442e4461021881c0d2008a15420b07040d1041000c098042d50010030000056030f451325a01d080190190424802040c400e001e40d090224640426125034200b150700b40c1e990000c810841c4226000940c000790806605 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 517256330 1250 517255080 517255099
    0xc030b0402070f060b1c080f090603010e04050c1009050f0609120a03030e1209060d0f05090d0801081c1b380c0a0f09031502040f060504060c0809 64
    0x9803181e00041c002284143c03080d0102c1c101d541441c4c022250007500c103602c81c10a018445404180990000c2940c6400850003999121107901c500da1500c508034140750800b0327021000040501141102502c1203020300d05492200d20f62008029488148127046008070348040014000d50800c01040b50000a02400d01898050440002028484410b10810035640412101c404060b030600034048000b090b400203150814030f080014103203001d13026a40e03015400100c4c40f0101c2c3c100c0b41d0481e6038040b41c040010000b40c03d001132038940365110a50309901050000300001180b03100006c03944a1501403171841100c90a601c0800c850141c0400e800001c000c42c00c11200d0003042a0306240281d04c086e01511b58007040301c803840280b45810150017201102030080400c542d4140210071a001c1c24820b1505c1102070b81010810b64071650190005082d8042c1c80d180d105035484964001c009480744170601c8486555201d80843e040c6c4541e0140b42c0003e8494901303400014481000b0741006100104001c90323 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 517257580 1250 517256330 517256351
    0x506030f0a390b09010912021807030207020a0f080d230c07080709060504060e0f012c090606010e191503020c030c0703060c050f1b0a23010b090402030607030c03 71
    0x800d03403190300085404030700010008429030300440244010301c1f006100c10070007641500040d00442103800d00e5418a520180020a1284203a0481742d01c140e004246110441c2c9070b9106151040c42070003144098460202204080b41c041c5040b400400c0a107000e100400315070030381141454000c0709601c066840782da1400b00d080c890900501010b4a074031240001c1162800e0100b1003594416031002d0358081950040c081000b61000c0014150351400c28130044444000c03e008000e80340b030b0788915403c90301100500c1541c03440803c0715405900d00744d9591030900d2002d01007103001d000704441c111407458045820098441d1050602504241d00c0c07e00600b017420a140407415a0301c02c04400c901504005001e03c04c11080b48280f20326840980b40250806405246441491040915042c1d0030310040c1071000c080f0f80c0800c2000191903010b280d641c3c60080209400444100c440c41d20740300c0c1d508200400b041410405621446550004c2c020314071070311800d005400404880300c103902015220340f4182c1c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 517258830 1250 517257580 517257683
    0x3030f07030e101e030c0e0d060f05091603170d0504080304030915090303111603080c01050106050703080c1315050403060e0307030225050d060506030f0a 68
    0xd40103000392250a03803010140308002a04061a03440020300038a00481d2641030032410881254407254100021000c07a855815585c44104c0d1000591104110720101c00300242c60300022011040c036501406207480301c41030350751640480b0302072110501d100748041001c20002c440b680012103203012250300d4241c28014020545204480a4401002c00010b1008240e8800031813002000349c403580604002080d0b400034031300040c40c40040c0c2084000f00f0700e001400000d1041310754141c4400241d9080c5035803441d21086c40e0300302c0318100070154640000024038601500071540140c0c0d1681d01e01e951640c0b082d000003460303040450038550224640c000820f030b90a0410308842d40541d60788403551076624524151050318109481251550000d006183c00a900018050450484405c0d03a1404140505881e540750000742d2185910071162800d0106109995001c0c83c09828154141e4507416030682c403640d900c0c00c10903c000d01c8500d0310f168403488104000148825888600300a4441c48961062903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 517260080 1250 517258830 517258837
    0x40602040306020711031009051209012c01180303140c0a1406331225090b0402090a05060d0f020c07050103050f010803030114120d0903060606050c0601030f0203030f 73
    0x2100c80050710880500b0031301c2d01f000b60904c048136000061002a41c65039540b51180e6070050306101081000c610020240c6c000c25441c0004a00f00b160781e00300e03003050141c0501310401182d0311404122507400c020b59403581d900207030301a20340544880391284220002c41e55241e100512001c01405442c00300c10016400f18810701c9041002001405141416458020b007940c05c480200d040040c5078203d00010100c8454603400075030101e64280b0303550601e003001070a10781c6020080101c80c08407581c01800340303842890b0b0720079108820404c00000000c4418071003240b1815102540c070881c0481c08006038505080200301920070b50502085640c08031010b00c050341c101c407502c240c042e005501d007072050b0f5a1522610364003404813082c62070342d5454203c015031244810f004211005080005543d1130781c4881840340c800f440070608503514218603080040c40b2890501003101c000742000303400a00284100309544008101001a1145034615a50680e0b0310808910882e054041030203110440304018015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 517261330 1250 517260080 517260083
    0xb0307031a04020c061504090506090f0d090b0d1a04020d09060b010806010503160c150c02010c02120405090411091f060804200a0306020d020c100c020c090406020403060207 76
    0x310303180c2060003048085034503001d40329014a10601c44d0b9100c1490025010350440902c1803c410085015400304e800b4164150014050b40320710001e0007014440040c0038251000d00b0015180c0014841c0c40450f0486940c1c0700c0d40303c4040c003e00080290148541c0500f03e00d20f201d20f1009007079910714011030144c4e0421514070034605d0f5605480c4c5d043c040b035400761100d80442440d18000510303100c0e0002e8901d01015083c51260006e42c4a915410b50060f10a409a26000a07002c4000c44442c8403e4001d00040d02c0c0070001542016015000780d03000080c80c000800001d1200703400c01d420300c000e000520348020b0090718215600103002d8880d0300c03032a11190107141c1e01400b40e0b6401502030b07180104003050b075000c0000c0044850810000c212612555207640000b00c1d10a90781c0082540042c041300455080500001d20001d81442c01c1c60080e8028000007045405440d41e440d10300c6034000494030500c0d281c0c0c015070800500c00c019481d01c0d40105a03c24440c81c00142020b03225122403089800c038100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 517262580 1250 517261330 517261337
    0x60f03030e220b1c020a1211031207110d0c060c0c0513090308090c011d04020d0e030a0216051305130f060203040b2a0a111b180f0c030408040b0307 65
    0xe550303299042800d40c00510380043c5401840c4c110007175011690420a9101b501d02511814407900b0030040418014164600018200c5d03440c17000c0006582020381c04050101c800303c10000742000141000c540c03600711303030b034100151000003460202c0a64030302082c03600440f0061501c21000c41c055031008031031030340e04282940010340c3d1a004e01c2e002e40803000150050740d041c0e108005503161a030b8020079032420030400500d2018200e034010003003000703406844980d012441c01d015100718200d03c00000742442d07401c2e607400c84954003400e40012142092a0003000e4115140d1584003030101016001260041811080c00e042044151a809211050444111907054000041c0410301411081494001d40c4601e80800d021694810480c0c1e480d6880c00f40003c11540070448440503805403941d240c52104030420740b03d040d58041880140c0d4007400640520414002c03c01204450181c08114800d200014034441030342c03500e50b290103d03608010000c50306884100004510100c0c0c08010f54041c480688 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 517263830 1250 517262580 517262591
    0x70e0a030c090e0f1011040306091a0c0702060318070803040f03030906140a180915080d030908030103061e09110f010302130504090f080417010f060f03030e22 70
    0x410340e0540d0908603039a8107651041c40344c41c403d400080b52144d424041540001404211542444451b0180f82d002400d484c0c40d1006080034040a41104407055601c2e010f0095103584042480b00c05001c2c480303010307410070800c2c400581d181d070105034220b0580580b802164505551045014516482500800064074445400304101074100e1881e0028150360b0070042000e021015440001d805426020020410f08844d5101c01d020307c40b0b0360b107000c1d14903640c05108003040f036210000c81c0401c0b4400c2d05500d200d080c20a0440521a00c074160710303654400d01040c41d50b465501e601019200365815810703120800b100841d1a039603540b00e2030400c680b0510314940c4000e000300810600304103240c4030074103040c0100b00114180c08005401416964103ea00040d00704ca603007426040c1d004000b50040600d240094042552407240402064110648000f4404111940d580d20f0940d086031259003c4084160003e1000900848200c0901180540740c40082a845404948404a901001a00c15503603d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 517265080 1250 517263830 517263839
    0x20906090a03050a120807080402240a03091103070303090e0702030f07200906090a241409010f050906010c0609020d030819060305070b03060d080a031505030606010c0b070e0a030c 79
    0x517074070140c0301003824120a40d1070054409403007514001d000030710804490300303c2c80302c1460305050301d5000c0040101c216100c0044550140c020150000180d136440f80300329a0401914000503c681580d40c55540d090a9515158144c14032038801b030b1081d010350205002c3c6d900c1e031482a102a290300d9004518640411081d034101042d81500c2c603c1c40d0740507110000412406440c3c1c034580701d4110744400d60001d42c0c07041401c1820311203507040221842244903640001844020b0003010f1009407400c0751107c2060340d13100c2042c0031030748052041d680c00100306000258698007605000c00c0c1ca90043c08085003c2c1030a0f030028440720712445080f00401ca07400c0c20b1000c3c0e10107000341291019002a400c0043d0783c00c50720340d640c2d038401e03a104540007010000300040c0d2039110394102c0a04540d0180c46c2940725805258060081c0c58504d96203000751103803c600040ca4503000900758090007041c3c54154910030b01c2d4562030600c1000804580070b02c002c422403a2030780d40f02c203c281c400450080500040030b03803c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 517266187 1107 517265080 517265093
    0x30e0312030f04050c060703120207020114030f04050f0f032a030403080301050f01050a080a0b1215150619050c010906020c0105090f01050702030904020906090a03050a 74
    0x404424400b4141491410500540c416410340343c0220281081c410f0390b0041d80800341c000760703046031205909007569008220141c01031605a400080020f200000d55005640d10150841048200002d1003000d00050315a4405000508032400d844054103a59004a50620611460000d48800c10004138400e1003000d004d0b4000380d0351510758078140944260024862180525244050412158400c504803541c4440320f440f00349003510703600c3c60034000344414003a60f40c10814542c0b60030381c8040c00300120119120321030300c84805494040110550550755140107405600c050040c0303034070f042480601074500111450419103070800d000a903405030012400c09032903079100156000041c501074008a1041c0350300c008450300c6104846000b802c99104603951390050f001881001050b01d4203400400c0015030080450703090a040328000342d001403455008407010391100044070200541c = true := by decide +kernel

theorem cover : BRFrame.Cov 517086330 517266187 := by
  have h0 := BRFrame.cov_init 517086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 517086330 ≤ n) (h2 : n < 517266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
