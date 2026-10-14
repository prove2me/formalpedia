-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1291
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:12:12.583633+00:00
-- url     : https://prove2.me/submissions/e23f1b76-392f-4b17-aae4-feb987c0e116

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 232014388 ≤ n < 232194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 232015638 1250 232014388 232014407
    0x302071e08060a0906180213110c070b04030c0905040818040b06180406170307110607021c020906010519140706060305070303020d170c09210703030e0a050102120307 73
    0xa405000d20410001c50703a03d00c0d40030198260160609100e00c900b10410003590020140c402544007007540d0301c030403070808030740c1c402500c030703216800c099141c400c2c181e0003149018210340c485450b01c3c000141c24400c00c05100c035401c0c0145a0a101480a41043c0d030303d80c1c80d82d004035080f5441001c22400302801a5a840d0815002d0a0024050b1560b49050b01c09440305000c03000c001d980038900784040014141110b058040407016810045d50410166544402a440003103900319070103c0c007070102c0d0000d0f9580c401500034640104420081c00c03410380c411720194000c0203011505200d8240300c800c10550340f010120048518a2400e01c050200c03070b0041800c24050104040c00551800f080032042080014800041e03e01035021a1142034000d08111111400011342c40c0c0f02b00003500c0400c0304d0401200151000101c01854042c68800212054003804131072216040c0c60ba00080c0102300741754020b2440b514000c4161004000b46090000103540c400c028000708401180000c00a51524810a01031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 232016888 1250 232015638 232015649
    0x16020f0d0c0b0904060b070f03050a0207031b0303030f06030309050d02131805060906130b0c1903060f050f0603130c0f06020c040c0305090c1026100806040302071e 72
    0x11528a40742c1041903000d4001d00080780c0503502d4840046803150662095842c202d50207542104200303100e0350101d0701d035003003041c4001c2540b18407500400040c04156007210060b41749200155641e01d182001815640c08540c418035283c5000f5040c000720358031100c000d050f2a429a030400c1e04a5031031002ca405400c0d4807017450000d92a041c2c02e00310210240d06500c40844c094401c9811303e80701c44031490380380d0340c040c0c0300d070780e5840308100610002480d45001c46520250390540f15080c00d1258440042000d00341e8000b00000e59515414480143c11280340005041c00747c50080d0340003a07800c04280607100c05050302c0c400d10424032001042000c1100c086000e03268501c1040c00103562008043d40d00c20091402500c1241000400d1450610a220302423041e003004006003404500c41e03052040e880000e00c084810031202507c1c14080d803002d00b1016200c289000e449100a2604c0310794040041581d802031885a041107082c040420360015040050322580c00580244a2041e50310031170101d6542d018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 232018138 1250 232016888 232016903
    0x100902030a090209160813030306121b1a1213140115090e060412021c1e030c1d21010c03151505070501060503010603080c0d02010216020f0d 62
    0x1006071142064100c0328249100ba90506240d449000700d500620a484c40c02c1c50000f040302c0001045a200c60072811951402400d0001c0e915881c0d80e058007640180d402d05071030f10b03200c03050020512103540c060300c0d00800d0f06111180d814403208480306640d2080c0c00e0150807070a004000300b102c05600b03021081c9203a901100f8100c08115904d650b03070180106104405200300780d04030000300f00301d15004440b04024003401801c419503c0782e42e020100400c41584c40218821035800c000c41e41d81201928885034a5915041110405841e01e606a10046040c120405003403c11030707407440f03400020101520343d042110300b0078250500080303525881381e4024509941c0e05089040300910b411b5210010015403654107200c07020100301c440b0081e0748036208030780c5026016100101c500e8850000b41c14150720480010429a82d0f54000a0a441054105807210540080c2030440b01c2d01c100241806070300b040c00254141041e107a8100141d078040100603000d1416030698803225030b03840b100c0b401c070540d01580 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 232019388 1250 232018138 232018141
    0x6070f020a1508040c06020c010c0204020309010627051609260102030109060e0901060b0a12091208090d0309030f0f0215090304090b010212040302040207050a06050c030a1a0d0b10090203 82
    0x30002e00f9802e0660301500c8030b4242c144041400c3d0720100d407030342910806841d07400403180c8036420300c0020343c80100721003055540d42501207111300704c5015101c00700620507030b2590030615a8200b00c00711580903100c2c00001036490b000c07000700340d00540041c044401c16a64228038075025450050000c41d02e400c1c1900d00c0d480000041030304280c0f0360100060390084000325600d0750301e50040f1400c0311214003890a503d8020301c0516a00f910030116a444034050600110300441150380c0c003400c15030768100d1480410317600300400c0b03421901000501c282040078034044c1b001201700c1d00c004c0d09802c04074a60004100030358003c2418107000b0010060040c00650500d030503403600050704c984a03001030258a00290801c40c2000241d0320000e02018400410006103141a00d103070708102c02548203402c00c0320030303000c1e5841e00804100305100b0b90384115211205150780c1d1400031120b1013281c0280b8101100c03802d11052200c600d40f00c0b00051407216070300c174400d41e49a0710b40410040e880380040c3e1104064a00000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 232020638 1250 232019388 232019429
    0x30f05060a050601020f101104030c080a030311030115030209060c0d030606090b0703080a05040204091202010606171621090c090606030e1c0509181e0606070f020a 72
    0x61114400c001e00c010400803a150381004a842e050030909210f481d41c0304040307000304100664010580d050f20400b8082c54155281e99189200c082e591080c2c0c40c5c2e41014218405142e01401040440742c201d510745031466060008441c000c031326600d008420141e020410b906c0302e0702d42c001200c8910b41d943c0201c40081042e403000401400ca80e006001c0050011100015100700c80000e40701001e92580380c20000d99540c001540003014000d00c180d901684809280001c01d442c0059040c03109015800400d1460400001609044005d2002d6600211500030010364003e044e0449803048802e141401c030a40141900d00003007901070400d025600c4c5489032020400c40d4003243c40e4203d07100814284240341d50340c20b0540c2129540740c0a1424ed0b003044501d150031034203450300000d4500c2c0c14100035052821240100d030b14840c000c0d01200442c03002c1c1007401503110082c80c21003001e1030107007007001c0640342c0384000c03a007a8029040001c101c1400a0700c10030071503840903041009040c000c803460581b000d056 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 232021888 1250 232020638 232020643
    0x71707230706030b1806030a08371b0204060810020d110403050d0521070908010e0c06040611070b0d020316030c02150a022827090203040309030f05 65
    0x10550368181e104600300091440d003c0c1c050042044401822800030134040c004040e60100000d01640d454001c00901400080c5140054800400d416030340540f101000e143c00c0f62822000705607144100c01c92000200c07d41c0e801401c1d0040c42010b218041d40e0380802d880494082d25041d00001624003940b030000c1c1c44048140e01410400c411010140010419020510a5842a400007500325005500c1803689140158000e110325840301480d030804419900c951031859000703a550710002815104100103410090086140b485c0e46000503022206540c40000c0c2c0502c00c2d4460301085c040706801e80009070700b0500140004218808030b150f564814030100000070341c81290b080445034690200f0400c1548248139030070781c0d030400303130000c1440e004144003684d10000c0040030292400d408101041c0e47c000c3c80424440e044914418440f8404801140500303031113203221900070b41c00300001090210015128414007240c00c10b0400503a00e4030b450034216011350a6030400b410341707540c4070404402c00000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 232023138 1250 232021888 232021943
    0x2070f0b070306060c05060606090d0b04061a010f092303030c07030201080c040807092a080109050912030103060b01031b050706112701020f1f0c0e06071707 69
    0x15039504120700fa40750390050704c4d03007070045c880a0016844040062070301d0030b003203009211000004010040148482d51ba070506c100c02140c086641e60786480280c0e02503200088910340c49002402c0c411290018540003c0000809101d21445110050302ca80151280004c076807040e00c0740607068965a28548900944d902407074401240060403800000b8102d203804e0045d43c0c10380d081e001c090401c583c0341085d0b69028181c081e82c5041114000c5468514004030206180615160350705c640341907614241042c011500b00030100e080d0394000654002024100d1011281501d0f8001400110740c4050b00041300141003030700301d041100402c020a0744400b50000090400144100303020b201c40091115401c040740034000c5d654420304160383c0d120440d22242204e60500e030b0410b10407514481c1c41c0c01684c81c036180c2100280e48041ca0303414003180080d141c40c0517551400115003865500f000107600031400c503216251024010051441051680ca0182070407600c0d01ea030480c100002d408283c484140b01000c4c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 232024388 1250 232023138 232023151
    0xf040c02010b03100b09190f09030c0b0c091c1b0b13050402090f0f0d0510090309050904080702090903040506030403091d042006070803070201060e0708010b0a1202070f0b 75
    0x95441c0d13070207840b801c0d0151040c0c0c0c24001e0102c4000386c6031250000308030040c2114900720161500d01c42c094003946407198800b26802981d400741d01080c0781c01e10740c0f82d041000e4800d0f06448802c000150541c1c0750030010710710030b074020518622855402d0038007407500031480c2c0c40c0000c081d18803000020011b0000d40600040444241d070180c1807036903401000200e10074110b405810069000c144600c40c40d08080012a417213001c2d0400d445004160754203800c0c2050fa00103400407e83d1559180103141c0c0c420b8100300602401d5940410504203504c44a03118020500b00a200303c01040008400078030520a0310020079011700501d032a801e02e80360103480165207018040320b080c01c1c6444029120b2003005034500454000c2072800f200d96091400c0216102d1070b01106401c03040800a00e2f0005200d07500551007003055074000240c060510360a001c011001915603c1040000001401144c55480868aa100c501c1c180808501999081003020b40a503800107440c4804085108050100724240d5520440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 232025638 1250 232024388 232024393
    0x16030e030d0302070c05090a020702040f050a0b0303040302090103300e120d0f030c17013314070204091b080d230a2d090b0a02030d09020f040c02010b03 67
    0x1c1500504604a009000020b40701024201003040641040c003203258222840c03283c05807406c407841c0c0105058810481c102000b15546100b080210342c1c26201d1122020800c40c080c6150514540005050801c10300000d070229000d50f00a0908e2104200c0e0003a220841b141030004019048070301a160514000c0f02c3d6010b072405c2c0600003081d00020604d5241c4800c503499070303800000c4d0703c1802ca008100300e105960902502c0041c0d403510300e04200d43c0354000d01c56050416940784a2504400c90411040c40e0418011106e1303200140d0305410009000c00d0076054080303242c503032105000140103440404005080c0741d0845460300f008245400401c003c0e0b4500030111000300040300021103074a2032079251208143c074907403012000380b9403000080004020505c0c1280802d008040c5d4020480d1b0300d0041c20030f0150b070748249900e500d41c00044400c02805040502c0d8145145c4900294681c41986d20310701555955a024404542c1c8400c0b481d000350801801c201f282050000000e4002c0c8000f101052291 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 232026888 1250 232025638 232025653
    0x305030d0507050a020a1502041e17010903020a080913050f0703050106020c031905070f0b041a030f0604050a0e01050705130e040f17070f0b0402040f0908040b090616030e03 76
    0x107002d081107584408465001b0041d0441d15101c28440032844c100103100550200700c00034011143c203c002d011045e80c00700c03040d0154542883c24289840e2120400d115904062005001c07c0d0045810a070b0140c01c8040d155940c03c03620000340410700f0751021007801c513190409105a140b009455144680200d0303d041045989480d03090765900090302c04079915600080c1d110f000a124811540780062203502201d103c66100d102102d071800c11600420070704440424100520841928404910411070380c1c010b1660511040c2581581001403290b80140d1712100407428001c1070307500c2282c40c1050072000300250300703014000802c40d500c0003031513441c95050180c01251052907070210302c0c050390703000808084194880d03071800d00c50308160b100e40003900d000703114030b001107015207036071004aa12581000040b0311701441000111040107101c0c0440b94034104445001500310012281a41c0c0c00c0108251210b280c0070014600344031319002c241c928900c0b8407640081540004500408000440544014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 232028138 1250 232026888 232026901
    0x50402210a09081804020403020a030503130608010501020705010c0302190c0f06080c2d120103030305090109051b03010605061207080906040503091e040203090d110102040305070b130503070305030d05 88
    0x582d00c4401d40a0820700082000c00c60150014140d40c507940700c05000541042d5a90300010f07039000e119801603450340c000152070103014855140c400c000d0016810410100d5042a000035078490b05405114140301c00c030000784083c5402084955900e10328081c4a4400c17104503c0d00c10519903807072040c442608043c400110700a4090801036100c2c0402c00c001c542000c0c1d5400c14140c149900700c11007001d1001c0300e02e4540000e0082001407190307512140042c0da40394510318000f0110750006050804030b915005410000a0001c106080810740070031400800d9101d11001030700404c1079600440d4850f10008014410f4480c0b1485a845800c1b26150700c041580c4030b100c0c42c4c2c1c40700c408560040040d08100101d030f043c0d14040c05925032400600d05c040410044402c00b241c102da000795003203652a4420103101f002c065205207807500c007a110300d0080d42882d245075241551000a8010070700006030100f00225000300c1040d2031001004020100c41381581da81c100702e520f82d0b010512100e6100e0420000841 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 232029388 1250 232028138 232028141
    0x703020f0d06090e0111070f0807020d050c010e040504050604060e120403050c030105010b09090a02030a0f0504110306010f080304030b2208070c050406240c3206010e010506030907050402210a 84
    0x51b06c4050542c0700d45014041d5442008802d042c03002214041d0040c8100009615298134640303000d8466002841003540c50300000d807a101000640c94031481c284002c01002450201e540f54200780c0c401c9001c940050760313030005810318a420510b20510380d00840c3c00070510400007507898264005400800542c2d032a0080c02d40107119840d030080e0403400d040007207404035040354011680704190000004107280030106240030385405803010344403904280452082071030240180d50040003c0c4000d006076519240c0400d441e4040c504c006041d614000f0005100d100065444900c29104101d0f28100710f1010315101141750880041540c0c00300c00b4000101d03d40c2090b2007014140e0b08015800c0f0030024002c0c81e5150f00c109000e1441e000c102c4201c214000189001d10549040c00e004280c0c90001071a4008008410014503000305155110200410604119041b080d0540b8410b0743c0c032640d01d64404039114901505d82d40807030307001880018940c48040c0c0c0c0b0143c1782c84080020540c80d40780e4a600b80030f8070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 232030638 1250 232029388 232029401
    0x120f1a2704150608060106051b39030d08040302070e0712020a0e0409080408010c1d0409051203070203030601090b09012c19090e07120206030703020f0d06090e01 71
    0xd10282221001c00d001c2000c001001c80100040900400c8868440007a24204103080e070100001c0344c00424814012a00c410030040014044c00080034191a0f8140409240c0100110700070f42c44820b40100d146000c0230203420340c607080041c04407402d00410581c01820320000311415001800703607050200f800d8090f40c04040c0905501c0c0d4030114040c0c400d0000310020740c0409a0501031000c200300302550390b1218025200320501031014561282e140103121800e45400030181400c20a174070701c003010080850311241000b40c0c03040d50009075604103850841d103880358000300c40d16081000b0003000001ca074000004c62041900ba600c002e03005507280c1d10400070b030141043c100c3c0410b840107400c3d03840d407104078907150482900480350f02281c0f00940115107081001c00e46c1724280028000700340048a11400780c50715520603074009110301841c00c0c02c003c0342d6808491000303108607800400301d0030180c801d80681d035089200480544d51252000b050303800621480c031500e005c5604164103289103035018407421 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 232031888 1250 232030638 232030699
    0x80f0c071e0e180105040303200702060d023105210d120f0c02032208030a0503060402092709070b090111120a050706060b07030c03120f1a 61
    0x128a007402d2901ca0751449078001c1c0110f80626980900e161041003d002d128041c2d802a1000100b100c0c000d4050748400e01c10480300d4032140c008026000042c1c9515088070b061105401c1d0040c0c91707204803200a64012042441c80d4078002c0307070050140e4034032850041750080b0303030f000c030355641072480103000d41200366041c81c90450181e000090580308650141c0d20000035640345040000700e00c03000150000840c2c105002800040e80b0129240e800070800016080c054100810102d05284c540b800c240d540f0720130b5008107000c00101201041d4540c94503010b90700702d003030000d01c00c454040c1d000750307001041450345800414180610300851810080130507020155054844000d141c034040d200191410045000c100b010342c440c203485070307002514200142084400380d9450710b503a410b2906000040d22000d41004107680f0080100034002504602c590300d4160f41030902c80024011220f4980040404000f24000315040000400070200015107075600f000d01110604000c4142c03011244400380c0c5000031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 232033138 1250 232031888 232031939
    0x1d100810050f01080402040c0320040303020705040504050705010507080d0f0504030f030506030304050f030c04090c080f030a080601030b040f060305030a27060e0303040819110f0a06050d020403080f0c07 89
    0x5c20301606168201d41c50101c03450402242c00c00010a4410400325035400c04103d41c04003007400d1003010f40c18044d003001407030100c07002c2c05a400c0030707110107448032002d104d00d81c18040d0003c0e08104200701c180650320032114101c410840080324404c190081c080c102c8007100041c4010700c0d6080c81134000d210b05401a13001030f00850a2600301030610004e50454884554948114900340940d079440d40100311026105808c4d10041c94a0008a60705d845e61094040e031868005000100704140e0005159620500920300401c1d605020740c0480d008043c1d55001d0320311076003404070100910030700000030a8480d00542e074443c000c088007c1c121502d659007040720480b502c0014400c004480c81044d2400304424002c05407494103a66a003401e00d0410518072215581c0a1701c2c070b43e0400d203d8540321548110303105842440c400c1c004800060070000c1c09001d108148000070410f011b00703c000781e066801071a0b004e040203a844440c00c0c40c513402070304207600003500c910070300700042440c4a075000550540c2420410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 232034388 1250 232033138 232033141
    0xf030c0608131202010608030d0608010c021912110102071a100b07170c031801080601030225080418050109050a060501140306010201180308060405090303070f1d100810050f0108 78
    0x4811046a140f420301800319034a45001103003c001c184003c140461106c0300c0010014600502d85080d100d07080700c682c00b9904071358200080354084904141406a00002d88c0d03650027a0703010107a4100c2540a0110071561010a0350020030148090482850500a402046540e41d0440056020b155030281d403803428410711000000030152180d050295100c685031600b080001e0350070624503000348a045842100d044540380701541c00c1007500f41c1010003841c05524028058001c12100e0585031100c0400c4d050b0440c10b0424040050b042c3c3d0003078004804044121600d81c1c0d88003028101c06e01601021502d0100492402d6200b0f1248004441d410b84800030340510714032140070039800040040d0f0665403543c194031100f02c00d02c2d400f085514825114481c180c01c1c464141701c1181e10091401c0c4450744200b0511030019009908007a5044040c54518103c0b55404900140b0150340c0b50450b8110000d0780c0285034007a00b04840910a10300c40903004085540d510030080400f10a05489000c03603010350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 232035638 1250 232034388 232034393
    0x7030305150a1401051e2107032a1e020c0a05040e06040b04080d05010b0d0b0a03030219060906060b0702120303061e030c0a0905180f030f0a090b040f030c060813 71
    0x2405064100084005141b40c4000507000340c44541c840300c0b415502c100300b4a0f03c13058802d0301840441d040f008a19041080b15108035004d40c000308007039072a52001000f040150307200d610903030b501c864403221600c209180008020010355546040001c1521a18400902054508080c86090700c1c4e546881c0003800a07841d5a154100341010181095501c2d0808101c5400740050034054a40202217042485076038a1074999403204507210000501e10030b103d02c91040011035400103142c1d0b21700b03000c0c0b0210040340e4254600f50005082c01c1100070316075402e10b000014680b842a0280200c24000e661008141c010300c4c0c0c10329202e03c030413212540c0c4030309011000c502c2e100c1401d0480c42110005070440355001d1030500090599011503000b18040d585030f02c2000460385801a141441002c444010610f0307000301c0520740c0e2240141c0815a017085804191254014840d4a1620080540050a69466486896030b070002c0b07405000507a0510510000000e00b1881040164414940c15405041800199 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 232036888 1250 232035638 232035647
    0x60306010303140f07030203300a020c010b0409060c0e010f120902130f05150402161407030b010609081b030604140f01020d06030507080a02090708071407030305150a1401 75
    0x564803e5100c0c2d81032000e42c030110032610060900c0c600a40081d038450025148180d40c00c201011407110042e4240b80c41b140050941c4083d540200d458000503071034803005c81c03607d0300402400d41c0c003960042c1004542e50502180e540060030b040303840d07960408203181d070100650f2000c10f0703100d2440004068031030300d003401006940906880d80c0b00404c1200c207401c000030340f43c050301c24115070094a1030707650043c09800d0724800c05105500e02c003684d09504184148510090890341031b071014000d4824034600303103400e11007405144050340d4480e90080c11035855180080c6644400d0207604070340e00c01c00034050001e064440001401c100000d00400700e03540d46594581c0d401c41001d110811511a419180390f01410038006000702804034000058410f1850800b01e180c030549900c1490160441e1001d00050b03161261364a90000c42801c0601c00e03612180c90468070590030b80c1490f40503400102c2ca5400701585034103d04d01031700e00b028640380c80701400302c1044003580300381c49520f01038548900e1421003940034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 232038138 1250 232036888 232036907
    0xc090212042006120906100f030213061a031902091e0301150801020a0905060a0225050607060506180906180705060a030605032802041a030f0f15060306010303 70
    0x610500005100d4442c000c10000d40104200d003e4124611041104181d0104007090340308404145149400e0300d018005100b90a5070700000e8014441c1c1d10710500a00b1160308108024500c0d1034580c12860900003d040c035a40003510b0302d180c0c1c4101d800710408170500e64000d50340381a400900c402c00010503842000600711410640d20f41554981c100b4280c01c401021400700200646000507a0b0741104400082154045810480c411041800b03030034030032607000503101d1216080f85010745010400301e100010410507075003d10741c005400102c00c0f00b0444141c00c86070103200140c0d111141e11000488004440400312000c040c2d5500c40c3c0e0004403000498007040140c0d01c004010744004507241c00101c2c0301c43d40300c030484e007011940b1440e0410086c241000007a02c0041054907403180400900181015a41d0f00794004c1e106640703070140ca07240c42c0b5080da80d0246000000782240d4240e6030342e241c040d4503210080c030b030081c0e80e0152801901c0072441e18568035114800007000342c1403580c21a60140c41610030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 232039388 1250 232038138 232038173
    0x9060a020d0b03010f230f071103190f090b070f03050a030b03010e0303040b010602030406050d1e0218030f011a190305071205010b120a060b0301150f030c09021204 72
    0x700ca9200500c2c980302031003900603a92003c840410400404183e584404100c1b88220100d101c1140800070802e400702d5040c0d03004400c80c540607040318007030a04d40d0319502030408000340310034004000e504d2132900010401e406600035110686055a540b0000c100d500800101410100c0e03001c4c04807000a1240004005810040c20700080c41d0424501003401c403184030001b00b0f083d030700c00800c3c0001c1c806035446840c01085144015031805007082c0c0d008080d4000d035510080e0150700d0f006010034217117030060358495000c8030301c1c4115101c10744051000500f0100e1042240039000b6402e03145010803044c011482d14110030b0451154480b880801c2c09044420340101c00d060088501010000480601c154001488100681038491215042c01802c61380d100000c0c0c2c0c4500b94088000c4070f040408540c002545421180002e851501da03000729026050b1143c0d40d040d420040030001c6041c800354041c94060385d000302c164003803a030386a010313900480c1321b100c6040134020042d9000400044050211401c0e040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 232040638 1250 232039388 232039391
    0x3090201050d05040303060f0306050411100215040303020d0c0201021b0601060f05070606080f0a0b0105091005060c0f06070914040204261c050a030b0a0308030118181109070809060a020d 82
    0x10341c1e90240d0000d48d00340790012030b8242d40750030900c07051020640b03140681d0701c070440d4980ba00703075000034019503101d0000034214130070700e4444001020f26001c0d40c151118400103040500c50b400655100034001d620040007035090444100d02940d40300d00000750300e8141c0d401a02e4543c1884c80c40e10b029519030f0000481141e0710341c0c40e8200400e44070000d201c500000301c0304900600c8618803515164000c1d00301604928000c3c040c1e5010802c010a40050040c22660180c5845a0300c12945003850b003880740c502140740c0107100e404140003540b940454000111510030b52106081c1c0301000800c01644254400e0000d94282084459021681400105a10602801107903260400f03c103042c0c80c0b550421044502060300850044003642d05070050f5400e0050072640607141a05607a82c0740034500040c080e1000300e10f402d40c0345800d901101d80c406017102c211140c101106040302e191129075020b129040c1c500800d0048040391071140106805c60040704458054140c9654040c1020000d400c81c0d8203000109 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 232041888 1250 232040638 232040651
    0x309190807030b06090108032b09120504060f0201020315040c11010507030b0a0504090506150a0806010306090339020103060e10140102030f070b060f09070905010206010603090201050d05040303 85
    0x4003010404007006601c2243d0300c19951415a04101c1c00c114164070405168004010b034250400107201030088034480062101001c096550524000301112680209051ba54041f0340ca240c5400401500c1120040d54807850302e0072014504a00380e000070750301d82d4161442404168031500e020b4000c1e0100500c07514040c084600e00c0c10310b03503085d03038401c1d644680402c3d65503001d1201c40c1409549140940801d407024480000b03a561003c0d039450008148102c02c6101000d03404040d554800a40001c1000c4000c4424558481c1082e0b8000c20755000b046000c10f00190b11883d100c80810b0304062458180000384c010030744502c400d150540030440c8101e04050740d942012450700969100240035003112500f5020380350921440c01049200c481c03280341035600510100c038941d21000101e48a4940c0a04100b181c2d840d40400b10301c040d02582c40903980101440108058150b000000c101115003d0f1300322610360340c3e13906042d02190312000000e0300040f8200940035418226800a64101d4803e03c0c1c00a0710 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 232043138 1250 232041888 232041899
    0x8060603090102120f0916030302061302041b0e0a050904050a1709090115120203060d08071a07023f180307062c0a172401081905030919 60
    0x2400c122501e000502c4504180009800d013005103402c1041f24190128001741183c4010350788031402403040e15190160001c650031500c507a0403101d642e80c0e8650b60780f0a00c2051400180c2401360310043d0b58000e079000d09000809240001c2c2e40c1d406183c01c68060000400c0b04d403181047d0007141d500003450203c04206c42005034541a10f01070003440100d034903d085d01c20700700340100644012851251402e00500a010081c1d44000b10f0024007584009001c3c4d5502c21780c0344c0303181e00252030f000011311640308400304042580c0200e000c3c0072409807080d40320040c0b03c0e1806080382d604003182030001c41c0314401014100c0d01032500d00809a066000d080141d8180041d40024078145042e00000c4c0001c10140000300780071044420740400c1c01141c0000d039040148000408c0f1501403c0c40fa08440940ba0003066000000a0044054103a8816180b0841d4052800c40c0c40d0713182e200380f1440c640c52251a45c4100c5c00a10365150407072807940a4040c61518240c11b0820280000361090701051b600c08500019070b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 232044388 1250 232043138 232043167
    0x512070c0c140111062205071a090910080a0201050d0b0904030f030e070b0904050403050d02070606052b031d030f010e12070b04020d0c030b090c0906030d08060603090102 75
    0x618103007450340400702080b400140413000968518a41c1c2d4001e00900008034041c03078101c841e60816071b0500a041d03241d81481440d001d0941d02ca03070b1151000c1e00b06101601320480c02070004005c140e510440075200d500b000280d003650313880360b400c580d000749691000545c4140010800c91140840105070103950b6000542054019101140480c5030341891401090b054042c90380040d022a016040840ca00b46200ca200d103c1c10b803000d4401c0380d4520004d410140100309032007244811a808548030402458080000c240034040c1c1d51007107880b59914202000e011a46400415034003100360b01151046e50f05481c580f218540300402d543c00314400d41d06a8400300031807125010344100205d0884401107140307060069021081e080046e003008480042020f904882e9000382c2c2c117440c0c0f05085001801e00c804030840075040100042001000d00130000d50000d141030420000b2a191280358a072030701019518000300560300c000c18100d00001e00c8074030f4040d0266500101d180000361400c1d134075000702030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 232045638 1250 232044388 232044413
    0x50915032a01021902040c02030c0604060218040c0c0f02010504150203030a060f0807060e0103230f01090203090d0e0409020301150e0106090b1902070503030c0c120a030512070c 78
    0x64000300004888034603055407040c4a44842000e0001d0202041060b480f0711441c000d06001070701598440b005814000d1080044030541641d10007030342c409041902d0a4000f95001c580c90946030107517811000420b107041e210341011340c2c0c0c0039200d0b0b00c01111540e6545550405082003a030500409110006441e5668034406c2401d00d880da014681ea490b101842700101c4100e90000c11031f095107080c06005005002540d00203031010790405014000c41100103d01410000d600850b030000c003d0050521940445c80403400b802d66050483d026a885a00303040403808102d900755110b5004000c8404010300071039010441d410040c0c03003c00c0302e188580110307080d12a5480c90150b0354191000c1045240c0200700101c0c05400d07a498241c8129107002200700f214011920341810f00c000f6032a844064a008005090050601400352134440c4d0942c0c101f02c1c0c80764030b266001400b5951070f1600444009010454200e03042e49500c4031800c0a5803a407041000d100c0003800b01c0c05100c0c01c115010003060301c501021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 232046888 1250 232045638 232045663
    0xb0703110a0b0117010e0706141605030706050f060f012c150408060f10060f0c0f03020c040f0b0a1509030f050d031b0801050616080301180605010804080405091503 72
    0xd944001c4c0c24a545084695400c2e600c1a82d41009900b80007696001d1018609002c1980a490b02d6103100c411807101c01d440390000405034030001484004218075030708128130500040a21100c1551050107000e214004e800d51140060610801008588015405d0b01d14600401810001100c20380e800b0640f10850581440350030b030300100d4101b1540008112540e400303210106807120a003003625a013403040f00b450068105101d0729002c04a201c52154500c82281900001030380b00c02d5003d401d0203034590341403007812400345061498540b207200d01070181c2c010740940500110106450186201a80364801c44104204140310034004046450005002e0303400340904007030b09900c034010001508840d841c200120300e884040307241500d986c1e004a1124110303141951aa540e8190414043c3c4000c413240c0740c01030422030048004201100e84600d050202910440100101a2904015117200d00100c400812421003040309102c0350a01c3c4080136003101ca034042001410321040c0000e802c107100d82229 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 232048138 1250 232046888 232046909
    0x1260a060528271806020316020106060903030918150f050a1d041211070303031d030304080a030209030102040302060406120b10020a0204091110050403030f0305010b0703110a0b01 79
    0x2100100e40b0b05840303141c014403240e4a0300082610316659011500d900c0c01c20401640e0352280810013240c00202000340c41540b2500840d5a40343c04410f0102d0b1350183d0054200541c608800881e03a00d0066804030160380d015120b01102e140f504440740c00d91400e440010310000d0f1981d046070380980c810310008000d400002c1d000b8200740e0804007448000038440d400198501d405185040400c4150442c007500107401003191a516141000e0980c0d0340307840b18081000c2e6202d410300000c14507526031b000c4042c00600c2d41892020301021103101c1d951740025500941310800801c0309141c800d00990046c8254240070b0005418a540c81e000100190407075407201c0c012420460107461459540e1040452105007101c50310303500c058a0000075a0313016400310003401903030b448035010240145a46d1202c10900000d00d80c640f0311403407440081c299042844100e0110741d000d00300d01b01a038003d000d058161690100040c4c2000ca8035103049a000c0119410001140110028134010541b2261034a003e441a80c49 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 232049388 1250 232048138 232048189
    0x609211110090810090c0e04051218130236030115090513051c03150909050f07050d11010507050105091608030f1206060c0703031d01260a0605 63
    0x4001e09003a8900030b5042c1041c0303000c40001c00500391b50681000d8407181141c50344140c0d01d80c40c2207071400d40c0b1124001c900002c0440c40e12111101e4030750b81303441c2c91b00a54038020500000e800120a9008414003203a207a95101012450000103031300007541c1e0442040004011071280000c217003101e03901c0c50066914415040d05104a0099024003504200c80118003001c800490315881c8e1a0b40b1a41d880740058400c110701021002c0c0710341c0044002c9030519541c0e1000b00d9480705e021000300202141110075016000540e088070710042006021900058030701d60084905941e140248840d0184480c180001840014003298007481018031802100c4c00618104000707150104800c2d01e2503000d0101c030f6008100c1c1c0e01d0b03c51000c00c103035411500148105800341d00c41d4000562030b402002c001040034030904900100340340d0711601c68510050b10300308503c4030317030485401111001074660a040004410090424103280c4440041da4841d815480000d440340c0c88800044003035031100d00c02408010a180c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 232050638 1250 232049388 232049399
    0x403060c02011b02030a020a03120f06121e0b06090a0f020d05180706050d0b0307120303060e1302012010090305040503100203010608150102161e060921111009 70
    0x5040b1190800c3d140003c0d4241140d405000350385980e1000010108407c10040e0786804600750860340801d00c14082c00d12407182c41e548003402e100e10342c650035104c03c02d0386041042840c0302d00610304001604030b0074014003982c80d082441714029000d8041003016a0750403122448005038805011482c00c458400700b544e081c000500f8080200360b04950f99035812200e4100303c116044400c50300151802c00021410003e0b4500103802c01c0c2056104200c40d6005445c4c15003090f034182d101702e040d1920040441403980310900c5000102545c00002070101d21400b01810241e007001e8540741c049010b59007191040c0300c0100344c5800741d4080c280c2c12004100003290505c1286800e0142c41c500d941c100908608540c0341200c001d12486000d01000c0b517040740c501e200c80c4079900c01c4c0000545510100c039080e82e804c1da1900b0700040b400040c240041c1141100a01207052489046c0034800c030f4540340381011100740e076800080c40c921010305013222000e186440308540c0d80c941001404110b50142c17a081559490070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 232051888 1250 232050638 232050671
    0x9050609030a1706061207021c020d080406090620040e090303090706050703050c03040f050f0a03022d040501081509012c030c0f0309031002040b0706020f0403060c0201 74
    0x29040816a07002401400011a40000c07906814201e18040400c26202c80020860501c10300799403448001c0c10300100700758260009421140020612081210000c580500301c0c2c45620f82120703000090687c0b00800d0110314140c100d41d10a5005000c00610200407044410b07a5041c00004035200708408a0200030350b080c0c0d20170156106051101a51552070b03c5404251162860b020fa0014050042a180b042c0342c4a00c003501c80680d000030403250380d1a1202c001c00401011482072501c01d001815094005003082c805400031640d001d031220044a400440a641d2911550140321300c0f9121405403100039655802003134020040d0b00b010340480308a680b6800402c81e002880249180c4c101a031203004034514500f070a520700f41c29424185255042000c0e030f81144610f034a049a588a600d070b080718181000320040040020403004c0f2201c14000382400d0050b8080c0d4480c1c000d81d0001844654017262058000701040e413a00e04045213001c2d1641d031120b048840040c990790050303541d41c02e003074004002c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 232053138 1250 232051888 232051891
    0x303051b010f050901140f06062110030c0b070b06150c0312010f08030415050a0e030f0705040509010c120e010e120d0c090510030906060812031509040203030f07020a0315090506 78
    0xb000c00e108035507e0703c003541c001091005061070340078480004200160019807120906003038803c49a0405e10705101c0810780440f1858001641c4c1901100030004002c15400112440254484000174441d6074001c00c100884111882c0c07060340e02c1d802c10044001030818401040355029003a0700c41c4455050981c5004009401d800c050310b03a46c0104070500880070404a108495601c529104c2d41e12243d1020448030020207154260b0103210f04243c01e102c00e2000309910341580ca0275502046150340702d0050500740c5a44e01c4d0b503030010902c880e012880c0714070301f504042c400c1c2c800e40001188102e0800c0c0c1c0ca03444d0034090707400c0c54400c0034040b440c40011541800b42001400161410107100b50410001402100c2c108800300103056885039503004203c0c0d0364005100418410050702d1010f80444445910350f441100c090401a100c56a5031240d03240413100c07a8000c54000c1c00031801d0132256204140b99600c01d0780241d0b402602c440d000000a0200e05840119901200020624800034902185030000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 232054388 1250 232053138 232053161
    0xc110609070315111902010203041a0126011b120b040615051c05090a020112180209040c0b0d020d0510031e0204020910031d0c0a0303051b010f050901 66
    0x70681040003c070703c00c00704040343d00702c0354a40000c801011501c1820244141500d880c000046005500301c400d8040d8046d51080380102d0300c1c805080022035151024103000d002c0c554030740004070318181c00380d00075412a1944045040c00040c1001d9a8914000c1120303883c210f03800020906c402c21180e0003450f00421729000320070b440c1880050309200e102d212002c00b8400074010441c02103500d0401001101d40c0c1e112940111008000b2070138028405504d40100003000da0100d0407127800001c7c220294401c0310348801096a091045610541c20400c109001070002d58450051142c08146405c484c00141070201c440300d00160b0b20049125040c040e20070050a90b80b20365145d49007040407920102c111700e0b410b045052540143c000c0b03880020020300841204981090381982d00b502515010ba00c08000507080c0030b92440300c1b80108000e180e0b20050341c410f03103811960010040002a0140307015010741c00010000a480030700d0840312500711000015104c4107140c03540f062110311002032203000d0704c259 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 232055638 1250 232054388 232054393
    0x606060f02150f07180609090e0f063408060108010e07080a0b3f120a2604200102070807150e0603040c03051203190e030d0c110609 58
    0x10b4045208020002d402001c0c142e04840c030000180c8494410b01c950f4100440303003074215440d65103a16004040400d5402407810040c034100600b2100d960000d0300a44940403d002002c9139a14240c851409806490030b15800c6510780c803a100c1d50f8051a084106446001c0e03035011903a01d0094001070222506030721401c02e140c0600d061106e150b5022180c00d13400010782c540810854503100c04a203030302201200b586a103045643d00d42c1031b0f80c50400c1d480c1c81024803004510b041c09040d00c04d030ba901c0b5600d4042500b07007002c04100340042540204a40b4641084a240303c550103040c4640000c0c0c560030480301114008540290080d150001e4103100b04024001c0c8002d00c0038074140403403140c2d11100c03401038520302918544102001c0388154007a06d4404c1c00078040540300c4c10a460300762580c01850000721103500a040001d4200080013003aa4810002107908030811400c1d200203031300500440c0100e80145c0410084181c0c90101030140c290721440b560703108800b26001464841c01d00c44050030070501d0384c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 232056888 1250 232055638 232055653
    0x201050f060d0b0601231b010e07090b04060306060b030402010f09180e032b0e0d08060d0c050301020c0c150a02071806090606031410030c210803040606060f02 70
    0x10707200c004002d014a07070701c00b041d881c464940c2001070390701c0301e00c40c240c0c8500904d181420078012550000509a24105907140c0340e186541da0030380d107098618946c45407419074440d12080000e9070454011410706034019000054094030b944a14040d07402580107002d0703840001003071100315640404c090540780054500384c1d1115040c14000000f070303a80390319000c0c07006032a0410340140c10401d000700c804012900c041075000d00f00400c014480c0800c00210204d42c54a0a640b414801c00d0104110026080580d44d503440c40d0380f050b040084002e4420010b981001d001d80c000b0861751000d2000707040242001c0f00414401841d5410050018048125251303400d0090005240c2103400003181300958846031840850444000040340007400d56a0200200d181407400015540781c06500044401c03a032800004110307a02c80e01170210080c0944070051070100c40340c2c020000d0070046c130311810020b16403029800d0013103840e450342c12a50304107650655074140d4650003040101d802207800d031809040d82c0040c02c0781 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 232058138 1250 232056888 232056901
    0x60c0e030606090c0d0b100c021008190905190809040c031a06160f0813080f0d1407061b020d1e2618010b040209030703060c030e06160201050f 63
    0x4103d005007a0b0071603654003043d045078224481d04001c03001c00300a010190242c1030020000c0c805908080141d00903802c3d0404c0144452045007280c0c8540114803203100a681012a03034001482c0d1108183d400e4040e50001903014903c0d249242c2f000c0f0302900780c0c0c07611414240b080004580e1080c0c00002810f2800d0907103482d0f0f0f0001c1d45d4258401000b15146a06d941050b04042d170346004000b0010010b4400103800410000c070540035011041155907440003150700c940e030a9070703548445e80f00300710390f64040d1116084240c4240d11b0358810640c840e290307904244a0781e45110075164441d200300540500d4a410b02c40307550f4100729442501105103040b50740e4240c1c5170038500c003810b5644803002c100010349040e6150b401c403400100152105807112180945084682980b0359851136844e90450b5003000040c1070145040e0003502c40d1181c00601408280d8a160380d10401051903a141001f81500c41008461402007448007070f00c50b031503400f0058005a4003060007821220b001b000252181204000e1106 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 232059388 1250 232058138 232058149
    0xd030207020d0b060402040302030d08040b01050a03020619021903030b12070f121707060518030306031b03190c030b1b04090507200106030309080703050c1005070b04060c0e030606 79
    0x505030b40002d20f84800d80c0ba1038000c28080e1180b500045d4061091014a10089a0040d40103200383c0c025034241410b641c0741d0b0104500a25203120280d849070302448007040d4500b45442d5404c01c009140115141004000085840c01c40d07580401d80109543c1c00400449060690103400418200c0014151944c2000d0704014007902c1c502a15120126810701c4e4010001803d030302c5050f01e4046004907844100d5884c00e40050002200e06020310103442a013440040400000d03640101c0000300648403540d030b18103280d044c0e0704496100503814810601508403880b461000c124019004081d1010400e05508040312100000b40070340454254445411040030b02c80c4d82030710242d42d481070000c03d03262184d4908440c1200c02428a0091a29150f000e100540d0154071180c00c072440303a2107103410f8641c1d40b000ca0340c132011503100c042c206070001035068180b444d01c014040c80030030b014280b9a0400d41151940c80355010125011541070782c0c1c0c2e8514020b22034000010241048084000784500d1a2043c0480c1c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 232060638 1250 232059388 232059409
    0x20a170405151806030a2a0806010c020d15050709060903020d0209040809041407020f0f151308030c0405010801080a02031f1d010911030304080d12020f03180d03020702 74
    0x241ca4040110f0b2510b02803407407940d40a560040100801c0d1a405e116030742030000e1014104460010300c038503034481e0003051055030040c1c811000d5120b03d00d150755030400548041030903c80480c0d02005803816800080c90311183c1441145941d0000542403505850162104060381c1000042c0010044c0400c0183d446491a08041b541516000c40546980c41e001c0d005000c0c03568400c1e0b00c9070400111000c50741075040280d100d810213500301c45003103100343c00950722400c00c070421041d0fa400c02d42260b040000c0513041181c10600a000c00c90320700c4c80648075100e05410641d1a00845580081c042103150b178484506405041741a010f480c50900ca0750001e0f50303459030700d410380d0000194801040740325405944000400032960b440c00443d081003103c690300a100e030402c101c8070142c00d900c00c0c3c005801c0c008155020307684000010280503d66040a0b5810486a00f41d0b81d8915000c209001e02e9018040203580190104a0100c2c03502402240b154181b0800500308010144144180b2015135500080c05c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 232061888 1250 232060638 232060669
    0xc0618180e1c09050d170a051603080105210a06050606040f0b1e0309150c0d0207060c0e1e011101150303020d0e040902100509010905030607020a170405 67
    0xa0100e504802849014010440031420389001d5a04000692007950704149a0040c2da996010a01902c03807041001624602102422002444400080041480c1c0081030400c61a040031820702051021002045881540c2240081c1040c0b00402041c00c1c080d0080c415060030307100c80140200c195a18941d181040074010b0007254942c4041801ca0310347c5c1d802c0b06c0c0a000b020340c082d5210b68841c0402c1905911200050702c0c207044440d1088100208001030303c4c0600010006090561906060f15800c01c102810110bc0c82d40d04106000708044244010301400c0d21030f043c042800400c480c0c026160700542e00c42c440c001e40350090003005070012070181c1365000d070007400d02490300d002036001da900404070b10b0107203620000740000c08400c4c1500060b000700900101d0795281c81050402040c0300a07504c0c5404025007002074414806c3c216070141002e41045032040c907214540a41c1c510000703142800a13074500000d40c01101585040c0b181ca40107811052102c0301100f0319161500012500202c64807080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 232063138 1250 232061888 232061909
    0x20906040c0e090109020403031e0e011409060d0e010f0b03210909010602070806100f03031d0306250518010e060c01050c0406030605011826010908070c0618 69
    0xc0405140981d01d42c4214200243c040079040d81c42e450a04001c1d0320500003900410800100da448060241c500c180820105655020108810000664182c2003003007800c03c01c04010321520200c0d44650026180c401f030681d80114107400c86890003421104c0900102c0406418491103030000d07180003076a00c20742c84801501b40c0b52483c0041030b03003006001d245000795111001d00b00000d04a13500141c03000680b4519003c0d1345540e00c07001c08008202020f4800d04ca659035820380c9c00c0010a002e81d40c5100300702450000d502e150403200e800681401021100e20b0361081184400e1742c031581d00744017950540b074a0fa0a2040c6405903030303c420f244201701100d03d5810445251421007891f1034403815584466511030080c80b050800c1c0300c0c0c0c0c0100750014011403000070300d00140058190b00c18440d580e05c8031a4851002400d40c1010b0036400105d40010003054644492051160010307400d108181f00303103005000180d150030040c5850b40500340306511220400c0514401602c94044010000d01104c0100301d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 232064388 1250 232063138 232063151
    0x1090c0e0603010209130f060501080709030602180d0b070206072318060307020a03021203040b1902091806040f05010806181e0a0501051012060b04140c121302090604 73
    0x380c0a417161180e001c2c0c01c88507810300c0d6809000c0075041509002070396a000d10030f0f203480310011510b80804503803040000e0407120003000031a403941c2c020301c030030040491028038402000300482d0030302c0843e0300200c0b2400c0c445010009181ea040c40425005401d40c9080414107411100195121588001c0c103905034100060051102c038a00202d51005440940080d807a072602c1540a926002c0c4c0d20130a80c05400780e1450643e40c00c10b03003802c40b840780e9400400c0900300e0329801d8014503c4250400031100f225801c00c010800c0d03556030740030104803001c0b03460810a035107020000e01003910088881e0700600d5040c00700500040c40c010940e65841502001c812a4080807813080301d00d82100460707800485001004840641c00380407980b0030700c1c40d014900900c503070780310b035007034480001154401c11030b49980c41011200054955009078180c2c14005002140300150300340f00314080b020030780b09103d28034400100c03600c5001003008040d40c03052040a07401d81142d20f64012540f0008020120f40c4596501c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 232065638 1250 232064388 232064401
    0xc0105090d050708031009140702010506010c020a0e090a05061008070f0e0106080403090302060d02070b1e1602030d0609060303120b0105070602071a15031905030a14041a04050906010201090c0e 85
    0x6200040040c451f040c0201144c821252214400c2078842e08010750801780040c200d94001e4613819402d640c0a03180b00c0d18603141034030550050402501c91103440c022485000040385c410408607004840c4000601545c1e45040510f80c50403201c5c4c2c1c00344421204000c0c04006543c078802400e41110264104216240e4071841c088900d04c18a1b04001d40c0510045007504103030345c0729400340c805944242c1a05c1c086499452080c000300030b40c411203c8590071081d0004100b0b6042c0f1150002c45c1003140100c9081c100c0c0200070384182e40043c0c116044c4203030765032010018507900856214a4038a807013002c001e440d01480000b841440f401e00c000c1e002e681c000035064100100c10900c00b00720940c4c0105103051f03041c84000d01d40c0d8500c0000c011482441003101c00078008001840134a035030743e40200103524088103480103603104440146070025461051000145c0740e40ba030207000e00540003010310342c0da60f241400c0800048440c0a80307842e045a04d0189000e000a18511440096a6a00150030319a07522031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232066888 1250 232065638 232065661
    0x90a11011818050f100303030e010b030f06150111030316090302090a061a04050306060405040602040f15030f1404030e0301061d060f040e10151a0c0105090d05070803 73
    0x1074807400910445800c005030303089103160a42003103003240340140110313211441191300381c040540f4405e5841e917480a081001074003039880000c4001241c400450040008400030303081110085200c0c80c99000102041060091526a08001d8409090410f80055114401c554901004025404041c0825501d001007806211942e00855004142c40610314151283c58080d0017184a030401e51218510001c0381c0d01010401c4c0c0c2c003078520280003002c01d40da07032004000142401410a80c0c140d80d08210220b003030444000f00340007603d80c0c40c041c070745550a15070005044861140903000100e10706080b504000d10036132030301908240c2625119210b148501c0010f401862560301480c01041e0441061002184600280e48100c00403901c54603105200f40c24001584c501c4484462260008202c049040400b5403082184d44001c40200c40c845031900900807004940c9036821200c020f02080306400c07000240240790b4081145400750032842c084080c01350440c09040f03c0200039420200005401c070188 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 232068138 1250 232066888 232066907
    0x171e0d081503191a06010f0c06091104050702070311010c0201080103260a021f02030705040b0717030112140a0803010b0f12010f05120601050612070e0d08040617090a1101 75
    0x1212107141072103c41c0d2070202d842c3d043c19054281e603c0d002500290166020f04403a07040041c2c0d43d190b031030b080c1c0e5060f80d841d801040c81000803202c02029000b030700030a45581c882c880c0301c0c080c1c0750002c007409410b50a02ea110713030249407905410001d44000c1040180d0348191410304580c1c0c01890495026403050030006100501003840e145004045820000584c3c00075541c9200f4242c03004035020641d803d1981c8003a03200c1116050042201000200002c1c0540c0000302146800f4410800c081c04c11803c4a002582c020390010b46e100c4040c0e000b00d41070100c0d000d994142e00925030002d040050b03640c0d94071703055800148190030b0241c4000c035040d404103040c8001c40324800c00307031924150a507840d5148181c2d500742501a26000b240000c40d00f404000b800103400341a604001c0c419810101044a249a0004014407407002c0002a000061080d1202c40030194250310450360552a941400002000c4003038501e110303001c401525007403004040c0301280506840b50040b243c20032500c8030300010f07682c5140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 232069388 1250 232068138 232068163
    0x307050f03010b040c20010603080a0e03030409060602060f0c0327031308030403031403071b080f0d06050306100e04020409110a17010516120510171e0d081503 70
    0x410140745e9081341e100b8080703815440c40702c0c4480169008850541d0880d422030100a000b59070070001c81c02c0c15401074120003410700d401012646400e40b90024a42540c44503071118015a104800f80103140c1c203001c0089511400c8a81c03544d0551070080701e01c24100c8240d400050110094107110490400244200c80031008441291411280e6034a000b0765658020300c42540000c2402000ca044100300c0800c690088080b6a22160f242d404000068200003940c4d004550086040142001c0a480c0c50041c020086c10100d00040c620b15100505040ca0801400410000c006c581c0c140165a5801d0040d900a0f4065500044140c00c0d031803c4224194400141c0b42e100000100c0010714110281085040015941c001e100a848620b005500d909107075407400080703100401400458003a40d0320080d0710509a29402694558850f400c0000c0d00b000c2c994014039070403a446200c1d00c1c01802496440001d06103006020302a540480240612000b500000c84e87c24200c5244465a804100f900e80240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 232070638 1250 232069388 232069391
    0x30a18020f21150402040507080405060705030c071e17041203050c010207051c020705031203060108040c15180506070b01120807080a050702010e09100b1b0f0c0a0e060307050f03010b04 81
    0x50b0603c400d401407030110741c200c0c840c5003400b001070500ca100d50500d03805240e12000500094031080c00c01c0d030381900001d24981201038207020760004103480301503410703031400c0d040380c04404c500f01814000352040188102188040c410442000000b086400c0c0744043c58145c074219440303049a00b5034070b01900c03d510000c2c105220306002441d0f080800007551b01400d001da02105c0300c1e141d45000340341e11050207a1040c0300110081c0700040c45940127515031640b0901c0b4a801402603a201d406e0068008030a80a810000d2924100c901044c0149111440a0881280c0c25400d00c070041e0b41d840010401406290103c80c0d011400c18100700c0c0400684000303561040f44c2a499030b6508000414275003151100f68005051044000e016083c803400f01800782e2034140c8807806640c2010040c011541c4072082d0703005410b181c0035a90350002420b100c400e44045c0403a028148081da070f5002c00030702d080f20740c02c4005601600410301c804d540d800070f040303411194241e62802c2c0b42961200064010603074841416040fa = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 232071888 1250 232070638 232070653
    0x2070609080a021e0703050304030b0c0c0d05091e150a050c07060c0b0105040203130b1008100c020607090605091c0b0a0507030c0201022d1905030a18020f21 69
    0x116000700d50f55800382005a4040c1300881020015540c03110980b0000e042a0004c0000740045048a8581540451800b030594904080000300d1803800300c603d142d000001d0301c0440d000140c2d1401c90142e10605407491004918000d0500024901001c3c0180300707090b44400040c2c500784c241c001d10a55248401200955806079a5002e028202030702107681100d008089600100e03a5180c03070300c2901c0c02410581250381c0414050341d0343c00100540a00301e11100280c0502c0040d604204114042040002c07820126402c450301002034507155018200c102032210b07100c0c0510109911105580000c0d100315080480c0024070048094680400a005040c100340c6500b080070803145071304120300880c481c1e07170304010b00d6031103402c103d00f00e010b040d00741141640700d15030181035600344a14000740b03110a510f005207040f5103e910860703005014800c880110b000401000010700480c0f140c6101a00c45410030301c208000e40c2d0000795201a40481c06120307480406100444000085074860040c03c0841103c0d940b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 232073138 1250 232071888 232071907
    0x801152601060215070507110609040606051803060c0717090a090c0206010e10030609080f0c0f0106050307030b010611100f14060d080405120c1c0212120307030207060908 75
    0x89003000d01441d0301510441480403c40100d0082e101d03c101d99a940740c608124a42c0d55400c1c20070103100341c1c0ca070700002c01d00401031a41d0b0740b031084100910301500c07059640d07602403546860750b0701403540340352103030708030b0010400258207800488141a50220859090f4480c1c1d1208240d0750098005c0729420081085000c00e080010fa0700c2134030307424116001c64045aa944103650f1000d082200c5003561510000030400024100e60801d680048c841d015240c20180c030070070000c2164100d1039520129038440c1c06410031040c428420380300582800e501415681d811038454000c5800e061181400f0009000d01d0796448200c14464030001e151502014401512001090805000070604100f001410500840c1a62401c4c19640450581c0803004605081c5400c080103003d400c03400802d0f515001d0f180142d130107039070381c0e0554082c44002c0d0680401101c985005011001d440f00c2c0b80118281d00100c180301c1082e0b00d91064a5000503c2e19003d0794a0180703280081c00351201440086c200341012a40040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 232074388 1250 232073138 232073207
    0x6030a020d092a0503030901030e071a070212030a050f0c010e06041b050105030411060901020a060e0304090c020a0b01090b01050c030f310603021806070c15030c080115 74
    0x164041c0100c007040140c0e43d14110b000c42c0041c07a20840c0e40c558010885511694082c0d0004089030707510320165000181e4414110403c54980940e6991800c00040c4103811803501242883c904000b44000303508010f1f08640c050300710710406514452070744002c82d50390800b40c801d400020048501105850090a0a00d061041604050500c024000d980034000c6225446038040e01d10981d04048403020710080101404a56800010b1080c1140a101c0450001c100c1c50301800b501c052840f0000d690711032501ea400e0342150b40300c0c0100340842d0401c512000c04101c0e480c04441c1914030a02000981a8502d40180c60741d208058200703015000208045010117030800107096003a104d0980010f03401110044458240c10503000080c400c5000d5801b800301d14440d502506100e41c20390700f1000c0c214504c80025686d80c024410031590030560440611101c9140e40d0202e00e54106428188101050808003412583c0c05000d01d100c03244610070b608100300e1060040c00b03100c800403440c805011000c24115030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 232075638 1250 232074388 232074413
    0x190c030f17010e04060b150408060105300304081516090501020a0311010216050102070203010c0305090304050904060213081516050f090a030b01091416020c06030a020d09 75
    0x140030903020440c81804a0280740c200340103400c0018119041c2c0c0c00c015000d03501d844003900c161784190703550380078442940300c500b00508005110b0400f161a68601100b10385000b5050300124006c6070810720130128041c1101c00401582016401c81101d440c2c803c9485140d4000c5034482c00451064419404840114003040c0b40221507810842c01c0d400081c40d070540e0615614428140141e101d00c0d0100042481442c40c09418544c0d2000546407085000840316601c4031011f050f221a5070000c0c48104514003441203411004041c11b041c001c1e440c2c19801103803039019520803039004850b0100002d0411420780d0496020794152688520140d4071045815680c03081c024081c4003a401d80c00c0818200c0d5420b0081e0080c0d100e0a0790382c01c0c42c00b0111300044101fa0000c000043d088411004003100091b142c0c02c1e0540600301c0030b440010041c110560b071002c01080600104468854a0480c080607940400e500d08000e10a5400940e0b0340c4484144c100244502e1141d820000d182c48110410070280d8031710903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 232076888 1250 232075638 232075643
    0xc0509030c03030a0c0305070c03020a06030501090c1107120201030b09010e06120a02030c120c12030307090506120109200d0507120c3f1d030403030801030215190c 72
    0x1a210780101e001459075a101c1c04a10901050781041d010000903c980001c0c034040d80301e00c1d0001c913082d40d20303800305080040540001c0c1c0800d4882c070050100541c18032070461201203a1030f00c44c51031b116400d00f80d80c81b41030740d00940307000c11485203850041da4001d41100d481c80001a000c440551f0390b400d418108100182c8655201704000a11446d0028001030820314447d00140a400c0114030303082004103101201c2e41030181c5000e58140c9240c69502c0b0a000080402410040e642c2c0e460444d00c000d103a0060740d085540304071001e2000d500d20b415886506410340e01c42c1d26000600007070000d103810f041c84d4000d000001c4c012001070702c0e88400d2555017046024422580700c0c074000b611281c3d4000152903241c2c54500020f02d4402c02c0ad011504442080c05001501c0c900c641480d601040301c014028459006402c4819201c0c02000125081a503103110a2101c9102031070801c1c1c256540181400c5044c4000f912951310141006600c5041d88101c1d000c411201c40d030105049140880604496001d0009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 232078138 1250 232076888 232076893
    0x30605091f0602070b09090a141009061215020d06030507060c12090305032a070e0613090512070510061203090b030c071e05060c030406050a0b06090f040e010c050903 73
    0x1e03050f40001607150a540311440401c2c106038040d005e001010301c00a240110082e16081940c80b06d8080b070f070015004211340400120b20030304020006051302c10652200d200024042c5040d0003146149075030801440302e08034027681c0d03000c00070421009003843e604003805500604500062058010704804000740c0300c0d003003080e00c000f218082955040345a02c0080c2107601304001c0340045415240c295111944015036006802c005444948e240003103d420210359003c0032000e001040c40c1c510f60308910300000541c01e1060048907915581c50314520f0079920b1001d0404603444003009414071520303808003840344003009130036610604844010f8803088140c0110300304007404076030010190104d0f845080b41c4007400b46050810380e901c050f01e142d200310441c8a90105240c200000e00248100c43c01005c400c091251a07041500b0501d0407240050516040d03e440d04003034038029101c400c20344800490850b22160100011000301e4090150107010100e50351805611000c4260000e0280c4603140b07040d001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 232079388 1250 232078138 232078201
    0x30d17060301020f090d0516180b090402030a0b04080f0d0204140a060212130801060902120a06050117131505011d040203060606030612100c08071e0f03060509 70
    0x81c18200e218608181071400d10030003c511450400505c5402002d100b00704440c00b4a0003c004405210100d8001c075665500410208501c18011b00a000c0c1d00d01c8200c0d5008004c0c10144d0000781c0d54010158010008151000080d040c06680015104a07045400b01a540d0302110820100250310901542030090001e61000403141030040002c2c05440c9140c008000000c0b4030300c02c2c0070381600b042d002842d10825116002c01c02c803000780a01402800f6900d809038461441c2e03810840340303ca0061004d101076141120401c910ba9010711541d88a00c42099842e29507103032090851400c1c2070b41d440c0a01105c521300d03c9440126120f078480341c100c0d03d80100b50306d40124081060740000100740e03406941a401900803550391b1410900540d00203030000d100d1403401d00340c0d80b4070f0760400c6000588900c0444d51100410710458025000305c0d8007001c10b00d0400e41c200d1000da2181c560b91b804c003184030b04214829030140e00850083d8480c002038040200b094449160804210aa0418040044410300355814 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 232080638 1250 232079388 232079401
    0xb0a0c05090a09110d1806051b04090c031b0e03060a1112130f0605010f1a070b040525050301140112030c050c0a0b0d050610120f0b030d17 61
    0xc103448030004010441044a40360062040181c1406440003451113000c01c00469501c40724071400c28082540b191006550989082c2401103510041c1000b0340250303000e2803a2100c181c1c200c115000e441217082c000a00b40000182100182211017420510603820f400484d06035400c84160b2140440440031602d642d543c0b00341e400103440024480d011a000188511000d000d94000c0303150b4485482c0818407001e2010303032036010880440074400c0c0c5001c6d41e0740c0018051520503919200140c07100c200c110020103000c400e00c2030584034a42001d003104030180701040402c44140b003007001c103070451401442e41d070183c0340b20b0703451000c4644516072003586420184403441620240d458101d8201c6150711800082a44090391440c003110001c4805005181032003115695401a080192541100071910b0b20500385255048076000740405108981000d14501d80662000700d801c403041454001188016a0400301e502511101000c41c0e40b40c000e1001c00180d203030784503084243c820700c01f4191903059180d19 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 232081888 1250 232080638 232080647
    0x30c062910050a0f0809100c080f011406220302120f010e061005090a15060906110601080d050c030f0408011509140601270609080c010e09040b0415090b0a0c 69
    0x803900c3c001044c42d4010f09400e007409124907907400304414040e25051400164071004440d900100355020039080000c0c400ea1141d881d06050140c00001d25090500c81440002103240c064140024a0030b804403d0485070401a00204c1004550240c01900c2d00084da01c00c16498115902c2e01030134540c0790071010038281400140003406800e06c5120014154280700910401c000c000300041c00c882e80707840034848070206528a42006140d56900d150103a4141000204107379412100b900240e030001c00144050400810f000b0751400d10342c2001d503601c81d4900c14650540c0100611101b070624007081c0020980f8064102c20b54002c402803882e000642ca5490700022911198410340340c00513480c0009040f540540c0c0054500401010201c9501d054482c13400c14107030f16600407200203250400308102020082114084000c401d0078502c052280310740100307515180080c0003170000c800100200f8140015100b40f4420035044150078008a00c150030880020002900c07690404c51801401c1d40296124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 232083138 1250 232081888 232081897
    0xf020901260f1b04060c110303030411060a0905041401032f0118030f051e0106060e0f060f0703050c1506030c0409020411040e0109060510020a030c06291005 69
    0x140303105005803244942d90968120041042d505003490b41c240f0207114620b400504001c0900d175581990701720700c620704541d00401c0410440d0182d8400d00912000502c0329942c44507455042d12501d0700e94603092811034810615511151f081303480c0803c000c16001100d084141039038026014101d01d40c03101c80803045100714640704030030303080c540c021a0340d5070703620480c00c400003800444026102117489442d0541d841c6103408003200c03940d20091003211000c80d5141c4d58001540054000c001c01850044060400880301c014144101e6800500411700c0d904d650035507406405040b080c136228403451030017420341e50051780b03030349050301c5401114000c211100d1305661160384003901915000d0783c010305200140c01e100000301e078040d448107203141803107050034043c100802c4040340050b81d6500d85001c0604031400da030495809030241104480c0e849400003007140c8400d034989013480441e07401d801c1c402c0c028000712a040d2800702688850208507500001c072030b181c4050032108400301803101e0b40c080d6402c2c880c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 232084388 1250 232083138 232083197
    0x90c0f0207231201090302010e031305060d0204080f0d14040b0406030203060a0302091f05030a0f120e0301060902070b1014150c030a0c0c080303130602030601020a060f020901 77
    0x324900340214400d141c2c118003825442001c04030507a0080307000881851103000680b40c507a54898800c02411303424020142c05c2007081c0081c515101007950803000b002980d000b241c2c0543c40020710f048072900254119402071040005460300c43c03180b15071954a84820202c550000b8500302c1d04480d414689000721401c8400c4408858900b81c5400001d402940004007000d40c401c12407074001001d616142007042c03084084a402d00c046a07000c82901c860180c8a420140c0694400d000c98800580f14050319242c0542060400c40045c840c0c440840c2ea1911401d2403075003550a0004c00104500342d6005405440c0c466000c00b0180d40d02e05074049070303804d41fa1113500507012501d0301034201401c09903c038000010b000240185000c21004070030f80b03140d0102220310000341d10004c0d5002400100c070246d80c007410b0200d015600d18185000f800030030651100029021a6000000c03403810b07070081001c40340040c4e0008040c01429510038980000307401a00761540410700d5070b2101c100464007486141075100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 232085638 1250 232084388 232084393
    0x8060115020c0906040207050d020106090e0304081e0703050a03180b090108010b16020603040b100b0c030307030c090e04120210110706050402041e060501140a0806010309020604090f0501090c0f02 86
    0x4401c0d0b4108114620080c000b140c1040e0300304514000324a040c0a440c040c1d840640010075014940441101103410b05210740710180c0040c00280600040410100d048950450321400c0b00300c06010800d04144a41d0710081c514410f07641d0361010150494580c1710108100443c1c41d00310b55984000c001c04d803080c1d1204c540090203210051100075400d40c05048041134848800001201d1540880c045500590302a00c1a03010071081080d0030012900f4400500b548006850801c18001c140a81d0303400b02522050626443d560b2900200d031061140e01c00520f09a0b10100c81810a81801040b0043d810f0218005001c0d02c0c0b0031400411312070040c1d11141e488a0901c6142a07195250b810081c03202074002c0303074001d440c0d03024070581c4002c000e002c84d0307101203151002901d2890400050400da85100403c02c0c000e006001582e10541c1207902c00764840700038200407030706031140c0c40042da5612030f079040030f00103a00e030482003c00c100d82c55002074140c85480d40104079a190180d42a00c0031420001d4640069 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 232086888 1250 232085638 232085653
    0x8103303020315070e09091002040801060f080a020a090203090c0a0e0411090709030204090804080a051005150109030204050a27030e240c120f09090a0603080405040903050c010212010806011502 85
    0x241402080c0703070f1f03100074070340c1c1902c0d110003840e075402069030b01ca54800e0160369111001404000c4405140000034a08500109200c1c041ca80c0829901840c0748180c140160f0b002c0006810b240c021320488840d100010441520f661710703215190f147d000291800e40300001c13581d2200740301c4c3c10852103160040d0304c00e07140c1e00082480d41e0b0801002d40402d80c8100d0b0107603c24000055036940c100070b0012628856005011401608001d0a049481c020034403a00402c0e0f050f201812641c02c4850321055940544002c10307143d032903d100300058412004034030314181703442150355518184429170110340c0b442960351318840d102c00010049802542c50526408003a100c0c48080c0721154800205006400342c1c090702c8415040808002c0d16400400c40c04202c100001010003052800e103807802d1303000c0c1c088803040103414110f0700c0d0102c030340c0205d0107401d00407540c0342d40c54400e05000300d0a0310b15090041009560710300540100b203417450400e05c21040544103070400480d0f4402c1100310307542568030560080000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 232088138 1250 232086888 232086917
    0xe1225020a1406070c120b090d2c0907090515030603061501140a09030c0602011506080a090b01030c05031207050604030f0507080307080601180810330302031507 71
    0x4500c61038030003907101070200050340000d81c0105c0d019004001c21010b070400810741d070400d0301c241c07440103080c3c00340303504090b10070880c1c1c90300000807461030140c0c044504c50b070020901041403500d1b4041c2c00309500c01c0c42001081502c40e40001c0000640f1001d0f640740070500c2028800900f01e01090f100241d040d002040007032714a20b094074a100017032805242041b500700c807926001080354042068480011030410080c410301c6640300802008090b2480200f00e0b04030310b6a00003581c001c06010700000c100746100801e00c589119000003144035040700c10b030b5489595a01e0701040340d410318400c4502038001d030400c6000c10310403c01a0790703045030080060082c036503680e030b412500300d607a82030040203020081c060840498861405544512140e0b104c03c85a07041c4480050401d000c0c4100450490254402c180301404010441c0c1601c140005030204150501d4901e444009401407410888044084011003c284105540e0400c5900035001d03110b01e40d645100c8041034174001c541c2000890b140c044010318 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 232089388 1250 232088138 232088159
    0xc020a060905072d1406191e03140a051308090301110706050405071703041e051c060f02030f01050603090a05071e0504020a08190e1225020a 62
    0x41c8510403415655101e445410b19000c0202c400002500301200713440c403105980306445500007030040386911041c08401c6034000390240c410003180e46075110140d4850410070340600300703c103440041441070540c040c0000074010010400243e4070700360f035600040490020f18403846058001c0c024006120b0380a001d030344401500e503000d11080ea4242d0741e101c0c003c04507d004080070b00b82e1180308240c007050900701800d007a0f1502d05141c000c4000c0e01400b6a08600402c0c00000312411a148000d04010b29030321070f1440c0c14403072900e52181740c10000502300d0303040740d440141c60760302d04601c5440d040143c4c040c00c2c10701108078001214800822102c8000500103840c02c200a15030201d02e11044440050403a50b5440c2400060341c007040e1840c548407640a4502c41ca4103403c2e02400c030640f011401d100000b80d00411040c00645070381c1d80c0c3c503800040518240c11503000610b5405444007112070541004424a01c190702010b9a29512103000001030013a00d00354141c10102038000b011101c4441c00e0800d00003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 232090638 1250 232089388 232089401
    0x150c0703180e01090504110102060105011e1e020307050f0601030c03200d050f010c110c010f1704030816030b01020d14040f030803010e060117010b090a081b130c020a06 74
    0x1c0025044110004a0610601455001c2c1043c058007203040d00b040d02c1c2c002014580060f0550541d0000d0006000c82d0340d100400b035400310000300600c1c00c3e00444210980d80340d03a4203404541074404451180c50b100d13030004001d10760700e0710a00c1201e24240c1c0f005089501c5210038000280a40b100c4441040421822410111102c20160060080141e000002144523290042c1140ca40e00070610000c180d1340f0070700c01e80011907402d0038001c4021090700401d070744802442c81c456050000001420301680c0c801c428280e1000f00d03c00489150303007000e08018111070021107070b000d584141082e110304424400e0040895607001a0010842e096042405a94800044543c2c2d892170b0410b205c0014484c031401d185d80025401084400c2d581d5040c4070a00c080b800b00140384030b0500941c0c920407004069020074080c11984080040c546440d103c100080198900e54011101485078488040b070074203203031400d000340510444002c0f4101080c81c031044141c072042c2d801200980c001c88101000f180c1e0f00c1e04042d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 232091888 1250 232090638 232090667
    0x31912030f0b030619060501020a0f0204200a020a060506010c0201050a030c02030903190b010504021c020703050d0c0e03060906011d09150108070603050105090c0a0c05210c150c0703 80
    0x1240c980300b000c001c6803400404640300c10b000c004484848032403102502c03419002e403100388003a1210b1070050710303403003c0180e1502000340210380e00d031906401c07014402d8030100e80c040a103604560b505030889009590700300c4404159401072400c2c001c10410344c010804003d83e168180c59050503c1c0d0310344019802040c0000445095010402540185681c148441c0d616a0500600507020b0520341c2001140c190050b080301e40130720302c1002204000007920030614010840c81e040941d58002d030346400c55440c022a824510342d40d090440e800303007680d0010841549040c0c01c0d411108a90303035500c91a540d0742030a2040d0725060750300a19202082800c007640550000c0104c0885243c100746030b901c5e488040e4240e00c1144103820450061050340c3e40b50140358018481240c0101ca54101203c1c0e0900f148140f16603141482001022102000018048103406c1800f05040e8604ca90040389180502c3d404400d401e4810b014400007280c503112100a03850180000c51041030500f055507500f0782c1c540c4172a4059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 232093138 1250 232091888 232091891
    0x4050117090a0804091e060b16030311030f0103060c0c03080a1d0318120a02060f031807080105090d02011401271b0f1706040f02090a0803030402031912030f 69
    0x30401003181c0d0310044c401001c60301d000050443c1c1501d002c483c0090048100309015050180821091440b1300590748400c0c1d13460f002030617142192070113400420258070b180c10580720100410040700070310410030781220701803c400d011905550304d04803002114600010045254600456041c20680c0d00c00549000314802c070102d4003040b001c0f2685550005203415410002c5a240c5540f18182000e560300300c000881c006000e8020103500148060003141070303040c0ba02e503003c000074142090040380381a0780464402a20101034030f9001c0d150181400b291001d0640c490305001c460400c5c81441200b040070244000106140d003462054030031050030450764401c82580c82d04102d46030303c191080d021400c41c00c0310380c1402e590500034058074400303003c20f44509001e404e43d01585201c154014043c0d000e14100c500144d01540f0503501d400a016080c2c1064020111a0000c030b00b02d0b40010040d03010700e00840860f100b9940c00781c1e0303941007502848401040c504180d0b1588050318001c0d0042c2e004240034200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 232094388 1250 232093138 232093153
    0x1505060d0b190b030607051c1d07050307050f0306010b03071403130203070b07030e04050405190c0e010e01082e1b0f020633040203010308030108060703020405011709 73
    0x3034441d04030009458007044010182c41068084041c1c1c4104804160254040c0a00c1c2c940084041e000b4000c44440320303a00741030745c0f90703001010400c2e90203200002d414007202d075100e05080322050340e40c0c180ca02407140280f28528010441785005000350b085404020000e103a039a0822501400c650000340c401d0b424050780d04241c01d11000b10a01961044051072085001c40c012401018a04ed00d5607000c921032070000c00071080030990000d120a601c0c40c05942c0483c09888900d072140c90300480c00d03404100715460704203074410172000c400341b4401c84100c54455001c69880c1d030641c428107c800e10075440c1690000058010758400c08040b42001c10003040f03040c25032400105040141c81140c0136031000e800052029002058002544050340c00b0340f88000c00036031614000e541403803200790741d4801080d414150350682d4400280703040114030b03a0250042d91256980d140195058100b8011440039010340400555144d200b8400c0c0c40c201e40d016940c4107821201c0c0106d40369600000750100c0b403540110310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 232095638 1250 232094388 232094393
    0xa0603180204090f03120c200717011d01020c07050d080405031e01050a0603050c010e0d1a100e04080403030e120d0e0a0501110d0302030903190903110306041505060d 73
    0xc280c3c4962801010201e0320a13680749002003100065515003000c1038a84401603190541c00381c4608800e20f82c600721241840c0c20b00d9205450600d050b400b0000e030316810f2090322401c54064011604940e480c030042060303000c0f442c4c561030903405030104215803580400000c01c0586403a4550f903100d41d0142c0c100e58607264603400820300b41740001c00c0c04e01c42d05840ca001404076840901c1a21380c40880084d04200090866580d143c0b90404911864101b0200010f903254541c0c0d0758910a001075402801003298403140c001c20214000100c0f0294190f20400307a0006d0703014000ca110302d20540c1d004441c00d1a160441d40e050b21508111300d903090300b04862140c0030352042001c00510b49182c0c2540c9035030008000c0300e010402a5085508128100300c031000c009441644006890014800c45050258036a075070304101d10320f18055181c44c4200315549441c1d0003880c982000d00d030b01c150ba016008400c0000050000d1542c0c6000a54004000d810010842d4141c085d165103c03940200000701a101f03a4540341c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 232096888 1250 232095638 232095641
    0xd111603020319030902090f0c0c0708070e1303020303070516020909010b0a0f08030306090705090a031202060a1a0d05010f0212090c120312150603040f03090609050a0603180204 78
    0x654110050b07400081c44108054aa542c0d1551040c068a070070701804c8400e502003604050064100624205030002040c007518440d426079543d170251a0884503907650303070081c1960344ca04501c60020f0402c00200801e486501590036400c2d90303034160700150300e981c03105401100c89501004143d0412580c3c0500100103941d080e0b0442e0141c154040041011900c100801940302c4499114072055008407a042060100200949a02c0401222102d0030755035001c006890b280316050405500a1181101008000708810401c1601c6603a0b4203c52031070303a4000c8680126080b0410b1425241d24800300301e1320614180d004c485135148a0300000c180308169030103100913600100381d011740c01c100a07420410620710401c42528508400c440004400c51071502040c0c50340704888595000341045000280e074901180d1040321480c9019203000d940c2d2601d4103000710000c008a50440000d100c0440000320700780304041c0c840540e80000c0036564a1460148154001c00d680f000008400700041507032805640ca6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 232098138 1250 232096888 232096927
    0x40b0403030e152502040e0312040308070e1e0411040f0321230c100b0315040309060c1104060b0a08010e0f13050c040c030e0c150d11 59
    0x1d407650b0803158000c200f008107450503401d80961002050140d400140c45028405180d09103012110313044480900204003c0c00c481c01603009640700c0054510410004041a184240d010b9650400a600d0b420411290750700070b510040c0c1c0c08032250b030000400e03150360008041c1c0010020b000090407040a4521503035074100d94048401c180010b0800c005112222084400d4500c0f1071050741030110840344054a003209441c44622a0704840421503c010003d000300d03450040f5010440d4441407994586002030030141c0e0085020f40115030b0344121200a441407640903e0741030311800d5406041200458902c0803000c000d07210315405901c5401d00b0f849902c03405c000f5240340b680480e912440c2c0300d0064442141a0301c0340001c3c2c04182c0400001085902039a46c00c10a5203245015a00c103078241a0f1505e80e40402141e406890710302080e40180c0c05074000d10001301e418041e940c02448510030442710158900400300840c000b080485202c0c2810341c40345075140c0e0b0008100307040006401c1710740c169192 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 232099388 1250 232098138 232098143
    0x60328021908100509030a030c091a03060f0414180c0d05101b08010308070c050414010807050604030201051207020f0d0207061205190b220603140d050406080606040b0403 75
    0x30084103000b01a001e1001c1c2403859068407042c0841d08041a0702c0c0e69a110701c0104001b0140e41e501e50b039420600c42c3d00e0810052001461030f000c41c99252402d082c20364004d1350020700c900704040008409090cc7c3c013401820200003800001035a032031150129110780c1707100f40300d0201e00a0780e11018140c0c0d20214000c0d6001d019400402003084c180002c2c4045035005013407516081c443c4640445455400404036064a511694240d1280c2d468034060b01140480d03042154028104540c24094108100e03c1c3c80c121132075402100d4001d680c0f0000c0c01001c2c0b0039800060300040003017100041b0b007126600080c0e0811911710482d0320360f4600e0001c0790300307082095459400503009501c0810801d07620410406480110040410041c09c1c29401d100c0d0f03547d0700719501d00c001c9803502202ca6031a5280d40500260f401443c00e150126001e10300a00c0007415a4081140c01400c0400354401d01100081d051001c2c51003500c0380743c94241004000c2d02d59040041040d0342c0184104030210310b000301000500011031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 232100638 1250 232099388 232099429
    0x20a1a03160305040b071404030b090a02010210020a0e010e0a080d0c0506011e0611100204060e1518060c010b03011b1b030206180f070308091806032802 67
    0x105240d00c000d886611036071000415080c503051102040d100c1d182da07508168241011001456014640802030046a00141c401c01000c42000990040400d02000181c800d074255202c0084d4118011704902a6201d048002140300e01c11108950080c000c0e207089200051007d01c0d8983e9440942d1300d442103010b00c507000141d0b01003208041003420001c643c058a07054040d41d4034140d01007074109802ca058400c5208101c85c118181040440070f1200c4d18444282140030342d52507440d0b0300301400728004040044c4c061104001400301c0400300380b00ba50180180c260041401740c1c20302c01000320b9a00200184811558dc91804075081d1ba024400d000080b4800d0f040da5200b04001070000d454040307044141440d448002c42c0780000281d02144aa90004041c01003042e5151080402e9140191a0081407142d104510012041c0f0141d2806400301c204101c81202c080142811000030407201070360030b960181d00003604a20310b20b420f100e800030420080100c841c1e124100c0d0f00000d2001562814400d40e54 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 232101888 1250 232100638 232100641
    0x41811011d0d05120c2b020a03200703113c030313060306182d060e0a02031b0703020a03030b010c080d140105040c05190207170706030506010309030f0804020a1a03 72
    0x41d0310b4000071746c413111001c0707082da415002e82c81801f03500c6580040c00101080f1807984001c200f400f8070303400c00054400080484401548034604501c18665880e08180328030864041394801035042d1081040404007035008110b034014103d040b0110b001280b11195040c00180603900d0f42005540c5680014150b0b6640802d00310324111030100601c500e603010300805420b2440c2c0e100341140c500b02e04a070481011010240200141072000c0080c12260009120300c4c0640d814030500c1407054000d11300a000c410069903200700079501c402194410108001c0242c1c001c072001c0c1c80030901981c17020014520604080c001c1104542d14104a030744480850381401d0b45d01c0f480391081c000c0c198000c0c1d02400c429a07042000b2140c8610107081d44c0117403d11582e411030944d0f601480c40c0e01c2405102c00801c120f20300c400940d94944805a2070300300306e00810303000920706800108150310a018054000350140c03507a4600050564084426000007801030303070440148540000e0010b0310a22200564049403003040e183d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 232103138 1250 232101888 232101913
    0xb030c0a0e0d020d110f150c010f05041703190501060221040506090f040b04020c10050907031203020a0201200703080c0c060105090403030b041811011d0d05120c 71
    0x45001c0e010050140051800420058440000c45003803250000a2103502c2c02514001924101482c0c25407074018102600302d103916015080503081048940000707002e0000031b41009400c50714120360290a01c03090340c41d03100c4044140c034004c54129107070807007500511180484c40b0301071360804e03484076005030300035036081c06540d0400200700312a0100221140c98980f0344000074030703076010700880180b150340006070b4800c10340e81d0390740700e4005914043c000b075495801d005078403600c8004600d54920f01506000000e13170900c0010406000362a400480400c0c600d200c1d0500300c00075003018510384150b65030b96a50420410b80c032144008940c071829082580d810311807074003c103015800750407800300c801c00b40428000030201248050541d0000e4508118595460070704070050080c220140d900285081182111b495820515007011802a80c0c042e0840400c0c40044403c003ca80c03035020031041600c02d410005e490f055101f903504c0e134003a1081700c0101c5524016900a0352040c10f1030440d40d40f068105514 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 232104388 1250 232103138 232103147
    0x607050708122d09011b0204090303090b090a080304060e15010f08070602030f0714030708030c0714061e07020a02030708100b0d03022503080a0201050a0509010207200a0b030c0a 78
    0x200703070615203a000d019100c0f25141010380030780c4d00c0b1181408141e049100410700e050044811039074004000380b1860603542000390007030628035000c0d20301c0c46200b000660503c20000764000307010b0340541d0645ca150345541300e40c0c0c010321034241d0b540c809000d032100041c80b4220484070a8007800c00c66564002c040e01e0000c0213460000c0c20750251080d900305204020140c0d810b6025150ba203504407042d481401d004840e654210311499000034820b0002200744800145a000a08052445010707500c0b4106100301204d40d032100c04071034620704441404000c8032910003003e2404d03000082070045450442256002134208001ca07040b0f528103511450070a0306603000c5020350a410001520311400c0c078045900e00039201c0e00c00760809218240590f001d0100044019510001540c00104c0b0944448164500030f001c0c10041d01c185501e903003401c0102e4581c00701071003241d200c1a0310020010b032040d032000b05520513122003420301d5031120b448030000900d1078051008602ca0400c001c1d0340c50756404401d10162 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 232105638 1250 232104388 232104427
    0x61903050a121b020d0204050403020c060403050115050a05090a0c02010b0303070b0907060c030c060e0a0c0b0a03050a0e0a02011409040501030c1a130b181c021503070806060705070812 81
    0x11100c403c2007240c0b001603203580b0300781900030ba0181c80204580c1d4550070140c2c0340c0b0032012012078024400180020070b008042d07200e03040d00c2c41d82d50281c10709699201c0800c11610000d00856600c06803d03008103410710880c0e40062400d26640c000800d51040a00019046410a072802d03201d240406040200031441800340790054001406e090000c0d4140c7e803002000c202034414010076096488003021441203080113124043c540c021160100740c1c1c0c445000544035080410761501090500d004900656040c1c000c420300550b2100c0203025008040e001140d00c071000340c0580540f98020400307840d540d15907000e101e010710300840485056074902884840c2c60141140d90f005c82120903c044c0f0700104050307200764200c0d07902c5026140c48981c00b1411103034000190381401c1d445043c41505019880d00481404a1140200c4104c2201000061440c60601c011155000007a944900050191400801503c4401e01660032540103d032076048541c500403d14100c100042008109090080303164041007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 232106888 1250 232105638 232105667
    0x150e070302090a230a12080a1107150522060e0f0f0a0806011701020c0607030c18080601080d1b0b0c070f050a060c0516030f020f1504170f03061903050a12 68
    0x1c0100c002c40352207c151501524448400b003001803941035500c1c5804014040281030308100304447d441c541d85001c0d00c0ca230f2003100307048290700504c04800000c01420720307203c04480d02034450682d8410b00e6810058980e030780300c010031740c090038008200c0d8103074507940303440c00103080010010400c44d41003020300090810003280301681a0300411000031034203408124076401903910b0a0100c0c007d10300348011365641c8030f80004040305402d220000030710070900160081c12078802d00b003616914040c81404030303aa41c42451030040c468185040a40002d0060700c40c0581c0003c03004034250030b041b100d6940007140048200e0544c2c00e503129134005024441c60741b041400104040c109245442c01c0240304800101c21903002909100e500031000303144c14000d00c0342c141d541e201202950b40042043e81c6595044500303842c00e8a4401c01a408520740180881c219001800b0104643d401c2d940d034102049140e0000403245510041e409100100043c170803c00300c7e25043c40f40ba0b030240d58110a090040c818080410f60 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 232108138 1250 232106888 232106909
    0x20909070303050d02030a020d0903081015080408030907120602070213050402091305030d0e150105010201111e070b04060506010e221107170301030501150e070302090a230a 76
    0x82002036040822580304c1d103400381c0b01686a0741d540741880300038003500c07022a4840d420081c03003404050740f0003011403040b000e08a0a0420302d4480c001d04028029100c148404500000046800f140c3c20310301a50344030701e5501c11180d80c240c440b80021041c1410309400c03151650042481c06c02c41c0f074024814190150150403c00103450281c000070030104000c0c03c00d613514240b02c41040b0612000b881250440c0005460a00031240d070b101e2095030303a0511650800d51010b507140042669881070086281540c01024600d0410308001407400c3d0b641c42d001000080740000304555400074100ca6001c612460182100192900d8408000351079103141c0d80c2c216102c0d00c84a00b00c0e528407406480600743c50849480001081540f948118401c0c0c4901c10014100000403810321a07416001c0000310305a078400c00080c00100078001425022849500410040295210000c1c51a40c071039030103440f01400043c8902d400641d507100d1181d101c0c02c0031200f2001c9000391a103000c1d0500b0000b10f14001803054558 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 232109388 1250 232108138 232108153
    0x190b24030a0f050402010f0c020f1f0210050603031207021f0606030b0301060612020d02090604031101120209010e060a0c060c0302030604060b0301031707230303070e180c0c030c0a0807020909 84
    0xb000d41f641000e80d40e00b030122903120241552038101404c020400041c0950090140c1c0c1e41c00b48413500f00032548100184074a10424101c0d41440c0925405640003900440c1070002c91140b00c200c4c01002040002103220b40000c03805100ca4000d40325011520a1400242580c00c10000500f40c1e2141014a80261b05002c0c08101c101d40c48104800000100100181c880d40c00c900d00d00c0207449000c842541c0020081070100501610f90b8041c1400c8400b41c80f60080400704003580b10a0f030291400d61800315003120200c100300c1c200640202607041007882c1c1403600c18100e0f6103000460321400402d0000940c08000c010550070300e1f2107944003a11030070000e01d04661456a40b0b007040303807101d400f00404000100d684030800c403120b61a180000d11f0842112030724400c4080c81a43da4000321142130006075008044c960f14144083d001c81d0b00d82c40400d1454407661055600d5205902c218079081c10351100b000010242581030008115081c807440d42a07540c0e040d540100300000b0405070001e14250004403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 232110638 1250 232109388 232109393
    0xf0317211b070c0b03061909050a0510030507050d0f0501020309060f01060908070b0a11070605090112051608070e0d0516090b0916090905040b1e190b24030a0f0504 72
    0x1125441200c2d414044c540e0b690366690003040d090000003036600c000b40240b910104020301c090b00b2062188403015010000c91b503030450b941d4100326a41c800601150058107080c413031418540c032b80384503c44c0038284807080200180c0e1b80500f203900843d458001600083c2c1800b00103400b1141050041015240107000141490100303600da6490344601d40d01803000150441d417050003240f0008800d141c0d58169102c0c00d5850402600903800300d003900380040e20009040c9034240c0c0303030310a650081c03d8180310201d0016024109946040f0080c00b020180b10b11a200ca04440e541c21110155981c8070707001404540c0139926a41c0d41042c0c0c542c01c500056801e040710100540c0360182a02e50000d1200038106168034940d40c00d6071008840c1d000f441089050008020070300100103a060b0041ca00d00e41030302c4080c0c1c40b08503c824502001d83e00e038001481210240c0155400c7c1d070308030741c022100040513403030800300c1940c0051302501441c0c400507200d032001c02040503d08440c81800c00f02e6203503060500c681e24095 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 232111888 1250 232110638 232110653
    0xe07090602030316031a0a0b04060912080a0e1f020a03080f041a0c12070309120905100509032d0f0a02061c02130801150503070f0317211b07 62
    0x21040d003410142d841c06e5100300038115191a450480e8050300d01c0543c9074403a6103d0003550300c04e0041001140c03448800265040484100149540e00001d00c0ca06040c2c00e281f0403100b55444001c02a8000e0695242180c850207010880d0720f00381458009081c048540d103005409950014500c010904140d404c1101160b085011442e211138880a0f151b065601e06200c07110038022180c1c0b03008040140010800b00b1905503102c090345c1d9000d60314035103404841c1c0c0e400304c40054541c0107064010500f0061403114601640103040d403c80024256424031848501c510305402c40340140c81c40b84120304200c041e00840c2804480351004160300905507507070030b540100d42c29202c0c10f170145031920103c00801c800d1500d190f0540301c843d010081c620321060796400751240600040f15888014030302e00c0b200010b00e4680050100200c1c0c10003915081542e255440324420010401c65044004104221070380c0142e900b48200340452a5481e0701e8800d50030540070400e00030000310603102001600700b040707401180c840c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 232113138 1250 232111888 232111921
    0x109050a0b0c0f0607090e0108060403020d0e0604120501020403020909062a040e040c170d140a0201020f04030b010e15090a0f1820010905130b15040e070906020303 72
    0x149181d940c0e40c1c01d0b58084031864002c1d16410403803140a11414072030f480d544000b08200315040007001c90f2031641c07601d004c00d4592070280e03002405a0320800041596a00880303429020550061580341442d03175549200e0488030b200c0008443c2a58006414000c5140c41c01001d45c1107400c16004141601e405008205281d09003200c5c00f030100e08842c4500c40751040b040c201c03000ba000342e13019004203081c02c2c600245054001d0041990000c1403400d0790703021100008a00070040d05a9855440c01201c1c3c2c030701050703e46c0c844045d00d42155000c12615441c0600c00004000552140c10340c44442c1d80f50074500d0403241c3c0c0103892100b060065840c91083c55540c495001c0e01700c0d210f2827000604414440810009046405c1145081d02094200c402485281d00d81940300d5440c00107503c2d41c5519200045603002080d000f07141d0300030100c018082c400f0302541d00c110b4800d800a441107460035600001c0501c1038209070b000d00744080800c010803005c1580a459000201240d000840c110b091002100941c0d118 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 232114388 1250 232113138 232113149
    0x3031602040b060705060a0b061603050904060b0301081606020c09010311130c03090203060f040b01030f060f18110a0e0105040f061703040510080106020d0e0301230601030b0109050a 80
    0xa05451540965456078854610701e0401059942d032041c40d4682142c45c0c81c000c071900da03610791601252030107074108001121040c49c5c1004620b00300906566041d02c03250041e158068010342d0b00d500120300d26000e03200550190900e01d0080000049181d0384003910382541d0056030464206e43c099949640720303180500c2c1920340c0b08940b40035500d100300110b4814107031110041d040c5401e10180c00b041c11b425a00c0140424000d9060710b01e00d6440d91403403c010501a1b60082102c0700c7e0340c00400104841043c2000c4d104e101c2c40000c504004800d40d02015180007004030300880c2a21700c4030104004010300030041704101a42c080d02d180d0301e07103000c181d525a41481440d0040751556001e100d10405503110030060300504c22105148464940c446589400034041c00d4012500700040c02262400381602e40d040704e003994010b242c240e007800ba040f5050300b40100c00c5605503490b507010a040c0321044148400800480c19104072502d001030004042d120354035441414400d0b000024001521050303108001d468 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 232115638 1250 232114388 232114417
    0x9050904110306010308040906120c0306020f1308031c1406040b0a030218010302040605090c03160c0209090d030f0c0203072a090603050d03020f0a11100e010e1b0303 73
    0x1900c9080901c4000c82030020303160301d4010880040200075488016006640305484100002500c60300d842d10500090710000e04450841c160401c006100754006041189610030740d84d00b407202c1c0105c4200c00c4441c1c1d0700040e00d00d070008a144c43c204420101c4955041c55550f009000100310140c2401d54545c006c0c0001c0d000d16103e4140f4081911585030072001158098000349802c1d00d1000b45580740c40c1c1c00c0c0000c034807075803e0074000900c51070121806400344040c500c100785980c494524402d0704607000c3c40b000040c002030458880259483c0b0211610a2511401400c403680800030300504464984004940481c80d0411994003164000140d40c0340560204400c0d00807078120b20200c10903045050355650b03100e80414085510b5500b50006806c0324454003c031400b040351150290143c0c007409410a0b90240188440000da5100303107c54142648510b003038440940318009840c00390b50349890161020b80d141c40c0c29210b2a2341c01c200c2c60440201c41800444c944404800194903442120024040039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 232116888 1250 232115638 232115641
    0xc02040b04052e08030f1b0606010f03090606090c03020310060809071e12140d26060f130b1905101d0303191b050c06070f050d03060e09010606090509 66
    0x40c005400c501c0041c101000481c1d0301c58181d0790b1308018546c01f41e02490948642c282c1075605030540040d80600404c416101c02e041a04560011802000c2810058070303a00d440c2c85000440101911610031047c1c596540543e403841c107050003161954a40c0d20840c03c212529007046090400450b0b140e0589860754802d0308240081703401000c90b03103240e41004030b54001c1d0450410420903040e48164150b00d02100b0b035120203620340c03030589503850341d05c843c841491001c43d01c403036a0700d80040126a025000900c00d91089180001140403803002140001d044c65480c81c5400091802c0d100c1102541e4200648004c045d0800c008952451b40c030340d03140c2080c01034052440020401000c01d20882d10000b41c1140c0c0ca0f021015103a1564003005030402c0c010500c010b46000da21701d0003002800d06550010003d160801580060141c180c0c80301b8800c0d50034040303144a4710b000034428001d40945c24401c0d50040b46030350401846002d8400050604000c0b0780c5004020043d260300880c014003160011039050800c2d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 232118138 1250 232116888 232116961
    0xa0506040b0f04080d270e06040b040e1e01061a0a0e0109080f0303180307020109051315080d0905030a0f1101090801090c0f06050906120709080a030c02040b0405 71
    0x68012a000130030035024148403207803415407040d00002c010169403021210500f4964440310205080c0c003802a100d040e001c0000e485090503042210b14000107040007943c4405a0009070521014108602642400807100c80714504240950710150000222000c65031080b079094001600c680502765040c000224080b00301a03029020050083c0b115005507158544803280312512a0f02c02c813940b400202001d60140384144001042c1d44d51664180c4440c100c19041c0003c109510940342c0490305540d440d00f0720b0021080290301c0500040180c08020903444081c29000341ca040c8998108074000d0b4031592240011803900d4410072040d0390440401d80340c0100050040310803038030360b0300301803252341c20300340e07031400b00154172500c8001c9604010030000e0803901d0301c100b240c081c410003507001d034050000e002e00490840f0b40301d01540c00c40003030b040c60464a42e40d42c0c4440d0815002c10b00c25404601110141c41c00c4d81024044d1541a07081110104407614000c40d00d0148003001c8040146404007c0400600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 232119388 1250 232118138 232118167
    0x60f070e010e0109030204050a0b060a050c070e010b0d0f0204051003020417060714030a1404030f03050603070f063501090b010c120509190f05130207050705010819020708180a0506040b 81
    0x80d2072b107001c0c00700c0303503a408040406811a030145214282c3c900c0795190002e08440700142d42c605030703410705880a01d4200312250303030006452000c0740b88907034950805c0000b60f40d94030410b601800c80c000351805030300c50346050b68000103442442c04183c9242c00520402c9101d5901034015907488a2214280381c50380c8030f11050100030608800c80c24181d164800503c030500d9003011013500038600baa58140101c5e40c598042c55154906c51155400b85414900709000007801441c603560f0140000416049500c1c0d00020004000c000c014241c03d0704243c0300041c0041d582c58001d1010124080c245002108141d580c0e42c0401c079240044d0104001001c550f0003c10380d03c0000c000e081c441c00c000a21240c685074003030369644141c1032203079521812a1811600400034140261003095801c8005060124030317110040d00c181000400c07030703c2d116040640c40c000380e001502c080c1c0036182c01485040e840750101c08559141d2985000e685101d00036131903080109545580456081d50480c10b811034a8250441407a803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 232120638 1250 232119388 232119401
    0x130609020301030c1514090f01020c03030f0a090b040503030417010906050c0309010608190b070c05060f10050d020d060b0411071401051006020a0b060d05060f070e010e0109030204050a 81
    0x41460340004000800d004114101d0f00c103448128902c0755407611070100071350b000800042881640182030181d036245c0c1c81e140c0700d441031001060041d01d1511001c0000203044d43d01c06003031b8a03007040020840b04000d541c0070301c0d100c0160840500403407400e0b05060000c0c0e6a07020394852a11094015410401090000e4000c00d290b81d03407201c014450b50030030110100c01500110340d051169031070010002208907001800c1d4507c1140b800b0320495409a41c1c84a2840400c02050700e41800f8902e80383c4c80c0001d0003046224890500350580380c1590800f207404811103d100d80c8028410101c01ca0b8500250351500c21120601c0c1c0d00c560001072007100318003c40c025003945140350309010380108038a0b083c859039107056818800704030020816640d442c4520200103c180c003a80c801a4480c68034100040c01131500e8a4004800404562450010b07660726071034294100d50520100a040003446522038101700860ba02c2c45c02400c064100381c1d2480c000811000c02e620010744070300d45500c041505900550f2140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 232121888 1250 232120638 232120649
    0x1d0a0b040e0c10050414040c0c0f0803150f0306190e01020c0102030f0f1902180907031b02010606050a080613020a081b03070c020f0f09150102070b0906091306 70
    0x1d0000400c00280e0780d89510402001034040c40a5250118003148942c086a09076020000c180b03595440010902006000d0000160301b07220300c442140003c101c07040081d00506100e210020750b81e00d4200c1d0f036690015a5440c11501820b41c005211000350b4020850340e5006d4040340d000c03400e2840b4142c268025003000f1000c24059440040e1644c20004107400852154000c000e100f0341640b65101071503038140048407209000100c00e945545003103c80c1d0018800141346032800d49120450750b0015907891416103c0380c01183e941c0307003c40907600001030003030340a0000740020030025180400141c11480307040443c00400c002580019001e542d4020081c6d21000001421500d9010007a03000d0250300d8140c982031010b02c20100a6420320780024100c03449020320361b0b00e40703500071440d5003070010780c03405880036941c0f201500000d980c0399121032030180c2c400d5281034600c0ca2404a80400642450065000000603900401c800301ca1740c1c4400c400c41301c0445003900e401603d900188000300c004c2841d42c014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 232123138 1250 232121888 232121891
    0x51005031b043206070f06020906130302030d08070f260405011401150c02010e0d1b050f0a1202100c060c03020a090e090606011110060312181d0a0b04 66
    0x120f2401d141c03944102c03d01c8980454a1006010703400c8480d20000311020255010340208a40e00c0003c201c00b066000082c41890050b05005026002400c541c10100c4408148441c00b40104254a41001071603d071310864140641c0c1c0303062240c802400040c451045070140081401891288042101420305412400e2400015070030b0520740640030b020300c04800040800c520300045441501c5401c0c4940a1880307440d9404400c8143d40151f0701000040c0e80b6940c030802e0a902000130800c2d02c880d050f94071801e11a48210710707040c01c0402100c1c2c000354080341e01602107180103218502e03040220b9030103a90126000018020300600840792583c051a0003800d04c0d00701002c4042080e0150050031003010355882c1c404140303480f5599003241290496620003660300c181c002c20b10320b500406046604410110545d0000c19050b9140402c1d10041d40c01110b0b050030300160b1a1f161544800d030003115002e401c8800031030341e107004c12030441101d0456000d42e40c072050002181e81d82032103602901480202a00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 232124388 1250 232123138 232123147
    0x20907090302060711040c05040806011a041d0901050c04050f1c02060705071404020309060a0b040f240f08030418140f0618010b04030f0c05030a0f120504051005031b 73
    0x2414081120802c0b51704d40150b04145446046501030340646059030b01d0301c8002c0c01c0507071802100d000d40c440352401190301c20204000100c4c0039880c01c01a120651001c188007003c90400070500c90031036500070106c010011041c0414403413a41c0351000c1c412000c00c1143c0e44491a02444059507000c002c5841c000e52003040002d00f4030410a01181c80301c00c0301c64000019010505d80400d01050f48001c036540c0650341c10410004458405c1e0380e00c0303804501c2e0054400151035100311078030011206100d109001001d8000d4044080070b0b44d802100c2c002e0312400c8a03001075140781a12240c2e8a00440c000c01042031212071141c2c0400c0c4003175103c40c101c03009681c030342e5550f401d05c980711403070140e019502c40b8000ea40001150091184c00e45026048070044c2959170b1902d450741d01c42071090301585408a80e040e803120000101903404000740ca080c0c2c0e0113100680060a100d14221107040040001c0707106201c401d00c0308000381c3d0746105842c004404181489a074941c1e0b410400d80f0300320110001282e950b4804074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 232125638 1250 232124388 232124393
    0x315010e0109050903071505091c0e030c0a080d05030703020c0a0606060f180b130305030301270504030207260f01020d060e041e0c0b07050109060c0503130209070903020607 76
    0x44440741260100070003004241c0b1410034242d03e03840f8541020740070060aa000f900110000e500c5a603004508030107a8042a00c4c120b0311030304510364030411074006001309144400502e400c0c440c2026001003211005121840d141d00113031038101c800380040034000040005281c0d203000ea0100c40385d9082c6001561440c8402d4a0100010211030180400051a04070341e6030a0b01d001c0c02c1e0f907035061000210751100f607514100d404500342e806a4101c2c552041c442000100050040015501820004607510702010950745401c0400c158098113a95032810303e0180b01c0880d8001ca078803000d844c244240485603081100142005481900c03501c1401d12402034901200380044d800b07802800c900341000c0c8141c07030303880511816555040c0d40241110140c20000310704903040c00c2d915207032540f10790034543e40d9a0b600c5214090f550045c0c8400d560076510307010b000c800c00c00c035445541e8410016041290440c20410b1014000c60800310000f070042c1c0b444000300740503034004d050400055500803e0070f0f5a8003030a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 232126888 1250 232125638 232125659
    0x90303090c09020c06220813030209070f050901030c0e1e0103050901090503090d020103061d0907060503070f0e1f0c02040605090606030a0506011e170f09030d0209031501 75
    0x240980e103007141c0c41000305580d00c0b070f402181c040d4030641d0001d01ca1074480300b4483c401200100c29000e41001c10003d00d00002d022200901110800d9085040e2141c2ca14014018601001007440003000650804906440c0d041015241184400c1c6400503c000d0040d4051b1f0701002d00c4c4d0780b0554000c000c038000140300c9001d005100c0c400002070740c0a001503241c82c081c150a990700008001c02ca40c1003031012110350f0030008a606c109078014500403580c181d4800440c01c11b5080c0540410044901c01c04000c2101c404021440080105142051030352074145402000d15507001418401c100600300c000140b81e4900310034085088a02c030340e4070303900c070f261800180c000d50340e45004030b0040c0c2c24070000088078907124041038031525001d800382c1c2c95a60350401d800020a002407140381402561000130074140080a1500c448011903210600c11603070300500c01030b43c140c008090308000b445040070030034a501d0200c103540b082d1602c07480142c0c0f1040c07540002418806040070054000300290000100c01626 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 232128138 1250 232126888 232126901
    0x15031b01120f0b0411180d0f020d080318070302090705030406060e070c050f010606050703080c0705030304060c0e0f010207050d14030a020a03110114160e0910060f02190308070210090303 82
    0x1220200f1170a4000204410703107000d160001c184221640120103400c0c20248420b0100c1c521441c030503119203095900150944030980b4083d20b442101000b0010b0aa43c0011100e4184101c6401001054516030004502070030040c002c10030004003001003010448181c0024001c1c0415480c1c5112510385620700500c02c45031450192400c0c070845510000303801e018400d000683d46150344840c034200c11a2000da4014002030110300c80404200443c402050b8180003940c0198401c00d808912024410300045c02c803c4074824192041300007d0142c0c201c2d0b0380018282044541c1550004040da4203030030044034034a0502c0780d8103801e000003e904415540e020803000c2a9500c030f515160080c0d5565041c4901b201e445550500881e04040302040030041403008c3c014000155251000102011002185441c10166101200349808a0052001070380099461456882d030344000c0442081029211008108100c030140c240070a800c00300b2207443c400e0282d47c58600d044c1c0014800e2007103c0c940107005040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 232129388 1250 232128138 232128161
    0x3030d0f0e2a060a050412060204090e0d08040b09030403020a1202120708060411220624050304111207060210050c0403080d05090304050a140915031b01120f 69
    0x4000350164410402c0245420070a0b42c2049071507a48410801e00540394003201d014018418144400035000b441000782d050b501788107200c00f580f200e1800400780203075415000300030b0554000280528800e80c0c4101a1580300b1f0b0403c1c04404640c40d0404070078114882d6070406504808400004102044008a20b9038058401d446807640880c44006041d00d8400ca4050001141c0185000c1404640c4013860f00d0b24101e0020084a448031101d01240407500000d14243d61990f03c614040181705000700c0b5900032055004082e099420a28900414921004100511000c1c018105160f83d88480c54041c00d1616014112002d40d611003401a41d1003090700c51401d4031900b000001001080002c0c1650104d941c8a03103158145500640207401078003004010a00d00e1000b400300103010760364140a40000c03c55241c3d12281140454207202c14400c000740014a10b60b0a0106203407503440c00106002541d05912840000301b9007080100c7c0d21f42d01c28140200000e0a01c182483c4400031503000801550 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 232130638 1250 232129388 232129393
    0x200a1101030b030d0807031103191a060a050c030c07030b0a0513020d02040f0f0c030209030f01060b070b04050c15030a050709030507060e01020319110712021c0203030d0f0e 76
    0x18156004600b910441c1200710f81640003510f138204240c4c0150302c0c06410200c54200402c1c00e4060300130501a80d003048034810004008041541c1c1c9140e9640b04031b0325a241b01d1900540c50110581c00301c3c62070311524600808004000480e48101d02d0184140c8402540c0901907525180d66801e01c248288401d4840e0f0400da46003001040901000b400e04524403a405054000f8044c0650208030040040803241456076071200700f072280c007000c18411900100a0760310b00503100e9071076400385441c03c50003d110a80581c50408140300f4400d4010503aa455588003262861981da185442420400703080f903026000300600c50130b1203c140c0d00b0000f40d442200e010808128070307903440304104d81c004950720016105410114052003400c1c40f9082c04081c00b181801121300e02201a1100f40081c4000c06002001480c0e01003c4180108148210001000344141549201c00c0c2a000107030a951919070410380442a0719080341151820710650304980360740b00c0304101e07030144000d1071005004849103414460 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 232131888 1250 232130638 232130663
    0x9080a09061205090714030a050715020d030e0a061d01050a0605130c1709010e030726041401030207061e0605011b0506130c051002030d39200a 63
    0x707a61910a00e4898002103008000c17081c43e04c18007030201414010039681500451900d02e0124508000e000000c1000d10f0010a2035242c4840003820001c1100b842d1003014101040841010700007d0300c03440c0c15070012000681e001009000c200300d203842000119655003003004100d0316003d82ea100d001120800d440c61243d2100042c2881c04841c440d00e12070340070402e40c81c2d0036131466010340000c0e43d00020310000010480040404107240d03030001e501c11510401d9001034010790350b981d120101d200412154034542003e0400c01002694075800000504056000c00d04000f8001142c10640f005020f400184001050400346000500310034040c15010515001103854070001411400c400260418094071454982c042240c2c2000b130308601c16649041e4920000c1801d685105902280c3d1665400442d501e032000303800c070401e0f80d003448420150208003043c00340c20a07004c0b40080324142a0380304000301c401480d130401e4408070050342a0701d201c800f4444100c00040b4000a41ca0a0315010f0b0b41510400b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 232133138 1250 232131888 232131917
    0x15050603010501080f040c05150726030a0c05040504050406020706050903031e061503160f0207030c060f0903080f0705060a0b0a0b0304050f0a0605161403150409080a0906 75
    0x2510080c0319190004000b8000100958000f040854000d4803e00c1030174200c80e034500000324903458251032000c0080d40007603034a08100348c04500901c001d00300140e44590781118690820b85020043c01c1041d41511605c40c1164244244d0485d0090b040003001040f2a06150030520001e4014031400c43e011860000818005400007042e07a00c1103000c8140000c00c3c120090f021b89180c01e018060b5500824a54215088002c521026600c103101000c02e200c005149090002d004034104c40d0f07048255003010900340045580d440e9081d003540c40034142b010070f0118183e8115520320040c0d0010b86940408694581c4c405440e000406035036002e241180c1181d1500c0404a044036508801503502010111041100300c0d840c074051a440380c0144261071140f000d01307403d5030402c14800380495826a032902002040750354149024829450381c03608551031940c117900780441d440003815009a10710900302e0f070100342d81d4a800034200c89070300c00040380e101c01c41e030072018bc83d00c1d102e40a000081410080903800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 232134388 1250 232133138 232133149
    0x1b060f010e0709081e100203071728050411090405030a0e06040b070b060109030f05010f0515010207030b100b0417010509030a0e060a200601060201180b01050628031505 74
    0x103a8132804080e28588101421102002580c1010164503004903840403491059502c003551140d030064840c18981549000d440f002c90500070281d1404140503e40b95041448003005401c0c0152801000079140d2102e0500f554440394400032654455500410041085004006002a860280c0369005240070000c10460780f80903d00641f95031031000c0c040c800210b8114883e481c0c001606040a80c004c070344a46035805030b00003441081d60169101c90507889208494821a0340c400740d000c05d0144c0000c210300000791910524800075207150b81400100700c03180303003000e5810700401d01b80703880565071a91641e000f0b0080c84580c800c40d459520b400000303101050040201c44806030746581d449e45545045c0208083c9410507490402000350707980c44640b501c11810303240300d04c001d02040200300139854503000a0940351804180401800c850034494001011400314505484084072840d1311514040c5e107829010013100c10b014001c5615004042c455601940001865800f400c220031300e594682e400c4c0007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 232135638 1250 232134388 232134407
    0x303131203090812041109150109090b01080f0907052e020c031c120e060603010b2205150a060f090602070b0f130803031905010801090c03081b060f010e07 68
    0x3c000b42400c00c605a0b2607000c4d1410281d00c00c3c8a5406036202d10801408182200000c5804122080042070740c0810b0703681000040c0e000f4080d00000b402122034140000b400c6900c0a41100203200c0804003003507003000c0612644010341030180540c2c00d0780031003000d0200e08040d801c03c4900110304c2d014010044501c003041c0c0075840d00018004100307007800900b17a0341600019044030010481074800c1c0c081416500c3c002d400410560200800403410050105070844401c400800d1040791602e41d641001d000111000b0f8000c001d03400006600d035514a044070310410b03281c58081d80f0045001c0c0203d070b01c0d40c000045042ca0045030b41e840607201d0f107840c23003039981d034002d130042d20401e0000b4404043c005060f00000c0c00e0b4910042c020b040c0c5140e0b5000c01510b580c0007980d0124250850001712540b048192007410700410442c0300a00400d9410f45402c5440b0300d1a000140400c40d001401800881000180c903164a08860413245903203444801d0b4442c24400f80240e290a42c04400400c1c04948500b2940 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 232136888 1250 232135638 232135643
    0x306050f060f24030703060e150a1e0504140f0f07020303180c0405010e072303150607150903032f0a1404080606010905030706080103020d02060903030313120309 71
    0x3466116142c400308041c56140114145076110301c810103c280c030100501850040c0c00f240c40215586090140ea1102403034003c1014842c1c00301440d19014540e20403181a08499518a0903040fa0944000b820b801402c1600070980060600c1c0911041d200e2200e1074603c101e40488020301aa1600585281090416200d50740140d1060001c5440300c2412040c2c20003406160046820103001070000c5030546100b43d10500001441d04108011a6004581e44100a03508a04009150070304400101c041c08041c15005400c01514a89441d07500d40108031000c882d0400f8081d40d1aa0000c0200b10290240a608070002400c00d01a0402400c410b40000780b000200c5100e074a0210404282106031342007030744a0804c00c0710700b4000d004110318000c0108044c14100c0c020f081c0358681607002400354809075000d01c2c040da0021008105256205451905584c0e0460742211060b00342d00010344180101c01c0d07a0360b854040081441440440d81e00e642d10420703c1011102d8030110424000c0c1c085512800c0007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 232138138 1250 232136888 232136899
    0x210f010b0904020409150602070b09010206010e0a180803060102011d0309040e01240e01060906140304030302090a060f09090b010c0311070f15081b0f0c07080d090306050f06 76
    0x180000c42400300501151038000d000103040c1665440200c05603031110040c10b00000c0d54000a012440d8148480e002074002507203202e20313054022000030342e108014071a12030500120340c007081c40009940c2118030b90300604400008407845500740700c02d80382c0c0240d482901642c40c0411220000643c1030411405580e03100195040ca842001844050320760b2a8654100d550385d400300820501000240310702c0b038001c40401c0a0308a04040c040060312406030000c8084c055840c108000183c0d1000b900c4040c03000c10b43d000c54584d1910b00e030076000b0f400340d07901c00c5502c10040540824216840b007011000380303040d907a170a0020380e520181802103c03221039519001540c0c07030f402e50000c01e0003145d840c221040241304582c0c5040d501d15115500b062550800040103441c0f19035007050503841840c640e04420b403510b8006442005603c054042c2c403521648050070b03200866032800303186e01130002d900109002c5064400507821148010210340361800112403651500001c103003450300404400b0701ca140702525 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 232139388 1250 232138138 232138141
    0x70909060b07060e0705211e0705120307021509090a06241b080306010f0203120f060103230a0c090506040b03091606020606040e0a0f02040c02030904020f210f 70
    0x841c20080c00c4c00d916a41c0203441403004c00550f0307032910b0284000e43c0301548092081d91054011441c1019602581d205182480c01200038602c00d02040c0340080311b0302291400d5140c142c0000450030b60041c440040d5001c0155992806640d800c0c0e80204038064040715000c01564071201104102c0b24540500c1580b09403001e1103c98000385403000300a04642d506080d10400f080d4542c0070442c41c100001100d0072140031052088951b003143d41703c03512803250300203542030502e98140c03840354800003003981c00404400780124a050740203511151007140c0c0c44d40b4041203c820808441e401080559445030300d1403601c4450048540b0600100c4203440c030052401e460300740317010f44404a030b4002501a08103402034105690940711810080d00c02019650081c0038686002c504100840e0704d0324a01381c503503410001d0181d0024400101c1380e240e0320f9048400241d1000400401c03132a6001c0d107155260050f200240e00022400b00c0b90181c101c00745294640400c041c807010410700d002c0b4082e40c0e2030654a44500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 232140638 1250 232139388 232139393
    0x5010c150b04020d150812030f040201050304020d050a05010e07090908040915050307030609031e05160305090a080303041506180f02070609061a0604150e042003070909060b07 77
    0x40090700d0000c030041c80941400f2400380070f4422500d036400054000030f2605001c003c1701100b03101102c0000d003409a50350440c5400a01c8191031480188024108000000094110350f2043e06400c00a034110085521980c0300d480c00318000e000289011700240f04081c07000400301d003640101001c05a000e05841e040c6858070781c0e1180074002e8003040c0c8a03115120840420305031802c00004009502480e008140f4080350b0a000d0101c0701c14111800c407090001d80f0208155030400202e59100c407801c0b850f0300960580341003c035182d0040c0c4018503070003004050700080e003007400000303540039500032550041c41e0010140d125048801911440340300c03002090fa4031078210003036403107070341c114072000d1000d490184c1c150750711011a580c4410072620250f5a02e41c007400220300301c01d044040b2109461142c0740a06001c0d4199540c0c001c015004c0401c0700c200c01c072003200c0d200c9400422402e0482c0c0b900500801d902600304103103030001c50341980011031900000030441c13240e000c0c0c1c0701110601c41809150130b80c5034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 232141888 1250 232140638 232140641
    0xa0e0906030a02040b03070902070c1505040b0a0c1b08030c0f150f040525140108040b130c080d03090203100c0507030309050c030d0201290603150a080307080702040605010c15 77
    0x717140da0f605000314003000980303620a0004003d6544600401c00c103c0782070003221030042d5407000800d410008140702c2808210403190468000d08503a007003180300c080742c07407420f000202c480d0504004940302500c0000389549000014103600000d01d015140841e00d80900705544040c12a0707808800f207007601c04070320701c031845031202030300907018a0503185075446504000b04650300c03d1403410302907607180d0001c00a42c4a500241c140c80d0000346400b516500b010740b68081741d444003400401504442036481c04c100704907002004020084042a03a84151240340003030020403000304182d0217401103603004540c1e803c86108603044070030162181d90602c5181d8604030300408018400310349610034403c80920340d40c3c00b001048545100341d0b0002c00d80005000907011300960b6000000701c2e800d2120040300191782c80c1415a54010150000c0e5400102d1401c0090030032181640f02d4000c80c0030000f103003002e209a1800800f00c079402554184007142d0b441c0d00444242e8001540a42041c5510381c0c089501d2045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 232143138 1250 232141888 232141901
    0xc08030601050a0c210801061d0105090f150918012103030207020933030304150201090b180d0f120c1e0804110a06021005090307060e030a0e0906030a0204 68
    0xc0c6080d40302a00195106194400c03030617202241060021005810700b03911181a43c090003142c81c108040040d990240200e00240c20007490501c480410102507546921f0104402c0070001400008003107200341c02568a9844160800c0c0140203034a40703000f500442d8000d080c100d5002c2140030742c115200c00b071080c07210310b20b1020031820140c08001030409a0f44201011340592131144a90246078403903800000320954240045c100ca807a04e0305509220794003c005e84085801c90b110300307034440c490a0002ca00400184200601e0f0407090028011110307842c0c032400d03650b21441c400b02c50360a41c0080055407154041021540003814124400940a0b680d4001903403c2c481c074180010008a0a4040888685d8000510380010b408104010501407030411509d000c0c801a08c02c10b019600307003a0000d440f81f0200c4a04d030304907074660000c90410707141001240d44071034000c1e104014030054420782d642c5aa22101d00100001e2401c260a4401c1c40d03d10403050050f00d0013001000d01e000c07070741e0a000c0074114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 232144388 1250 232143138 232143157
    0x70c03090306050109050a0b030106082d19110a0e01060323070507031e0c08030c0c0304060e03011401180b010509120d0f09080604030503090c150c0d0c0803060105 72
    0xe04034000000201d05001d003502900c000c4502240c58a808601e9500302e94103c480700d8801e80c1890780401174040302040a591a0151300b988900010111282203503244201400c404d072440713144d1031401d001030a080405c100a116200080e46c0444060400551035003500407064050424001004642e000b075004140410507040e0810032611660780b000c145001c111070300c102194001400008059002405d0300801c1815580744a4043c50f04000814030b500d4000014408040040810440f400c40019101c411795580c08803a601c0d0b840b035000600e410a6034a130b03540207600344501b43ca0000d94420149040c0c400110264406080c3c805284014151141c003960501004000070800c54417071841c2c0d1890a0000c0c0014607440071080001001010507104000411944490911a80c81c011032000d1f0003a8052411130384980f2090340103800c0400707040000360301c488103a842c48203803d001009070205a009205a40c5089001d86041e0380060802031b0080c5a9582000041c65640c0148090703d000302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 232145638 1250 232144388 232144397
    0x12010b100903110d1e05030306120a0803060906010c0c140907020c011e0905090a0522051015150306080c030c0a18020f040909020f04020901080403033b0708030909070c03 75
    0x81141410b5910f01e1741c20b84251110f4000008101060070580c0501c0254244070004001442079a00d070780c8620700000c0c1c0200e1152006101041c141e070701c00c807800101250821424440b03e9039903445440600b0803100c01030f00400303481c00054046170010030040c24000060b103800341c044801442691480280400c03400610814540110f200c0c2ca910580c1c9110b4611490001940d04254101c1900f00500b41000b0548550b80c03007542c1c0004001040c814459030a100010500300b4072021100030590301900200e07030310032492400c04103c981c16001001140da51809541210624070181034441140500c00e0360019410b000801958100305041c01c2c0c107c5200000500380b0300381601190135139200340d106150f01515803c00d02d00794030b400c1c0c06d4a0262141100c04618089620b000a400c100005101801f89039890311080000805044046142614443c0f49050410817101d40d80610b80220100c8140e845540c90200345003400208640344007200801080d51941d0700c0b6001c4640c0b1a62200480801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 232146888 1250 232145638 232145663
    0x30c09041704090501050301110f04030305030603010207060203070c1a060a17030c0f1c030501182a1709060903040b031518040501140118090f0212010b100903110d 72
    0x641c0007a10241480800114840d49024101425074089410080080748200000e4000800a404031030071694141080303500e03955000700090080c0a012406441d86000204001761240c2c408580b041c0a4451400d0342795107403500c0e0069118031411a01c1541090300102d05110155820000039185034052080324030780461005290b040a00c0001034121039402400e41041410031034490f80c4041c0605d00d400c103d150b1404600c007250f10340019561940d5940c948612036680145105200115214000c1e1019160080d40040c42c0e0b868101081e0101008c0d03d0105070038080104989004404c640010b50800d03040454140c00d0b6403025100c1c1e6591140400700c88040d4503a055048490058083e946403c0e1401d4207246082d43c0305841e0001580f080480140000d034840300320003400c0618088005644229031170554101401a04040c2d4441c18061030300b410300c036054000303500948013a45d0180b5031822003401668800068003009155a01141104100d41403002d8060a4203009800720a0380d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 232148138 1250 232146888 232146923
    0x1306020415170108010225030201090f0b1005010507020f0f030708120a03060602030304030f030b061b0a061107080301120c050d031812050703020906190b03070206060f030c0904 78
    0x807080081000c00d0124040c0c40428511007481801824804025803509119958030142102e00140013241544001d0080c01490301c01d500c03140580c0e5000340305580801c01418800919903007140d01a510f16020400411903501ca0806c0d40e10b0141e010780350143c4080e500003081581c0109080064040c4a904070014102d0380c10042240441d425600c10f0ba507a02038018000c041d1100768020400f55803040081c032000a40c80088007507800d0980c41c0020f0b0280c54040021524030403501034103424510410303800b62a0308007045160034503224010400410a4441d2000c925024507a40901140030600041000c01e9858a800141070320496000540a40b5003000810781654220150000345006040c80042101101e428020b0710554188000c0700c00c09554070b541c0d9443e00d00009002d1701890000c41c903143c40d030181010549610004c0c1f0019507840340e1060100d0380049586a0051082002007040c0d804c1185403084a001e000d005041d056145e039040c42460000078208a440c00960b000e00b118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 232149388 1250 232148138 232148159
    0x30a08070f0807110a050a03030e040509070503010204170706030c05190203041802031f15180819060f0b0d060504030c02091305070e161b020405010b0a030e0c060313060204 76
    0xe03011301c20611010404c0d01c074810300800c0703259900002c0c01182050b400348007180c0c110640c80e42500044401160340d560b903100d25800c00d10140d20541c0c2640c0003143c045060308200b90562007200b034000c11620183d90703588041b0207841c80c6c2c62104010030420031a10843c04042c507808050071408e4011240b03440c1e0341d4403440b0f030701c0903104820401d216800710500c4a2681e00580c03400d4401034686001280509010840342d01c00d4004400809010b00c1c42500010b8038880700d4144000e006810a403196010100c0882070780d02058981194a140f401c1e5032281450310b00d114401c0341000140070b64111003000c3c1d4031403009040c050002e03820701c565440c00c01e00599840c50802d100d00c1d00000b481c460104180303412480c0480c00c0c0c018031788090601e01044403500310704000b00d01904880c90040074030354220f445000389040c140d074040d4005040200120b020580400204400d4008d030f07804009036002441e0b503507100c6903000c5110b03522600400124082444c0d140d000b55880740606801803a1541c0c03510403d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 232150638 1250 232149388 232149397
    0x1507141e0910020601050f120a02061201060f090605071403120a0c0f02060618060d0807241815060801020d05060103050708100303121b020c0f0f030a08070f08 70
    0x4590440004441800342042c000041c0b07410440d00040c40103504280000d6105800181028000d0705801d4680181c40c00c108a41c0c0115900540000d0342c41150706901210384109000b0280031031000d0241c400c640303110740d880e08110754281c0c0c0c695050070740c01e9440c0450400d0031000f0311083e110a014243c42d501480c0340083c040d107804200000d0003050020058071200c030017580d40c02950860350810005803036410010105482406203000345560704070000b4075a50500c0000740c800c503804990201000360811002404603920082e0300d010700c101e0902e1005480d2030103001104003006030303407140000d90440100c02c10300782c2d106404581c0c161078403125030890b0040030001c2c80f00c2d40c0751418402c184d601403044a1704a099407402c0340c02071030035508030b40d1210700510006042142001103502c0ca40e08a40c05480d800d0800aa015413074448140020754620280030000d02c2401c01305c1000c100c07860221421044840081c003d00036440c410f0b100e101c0641c0007000e00b030700c40717450212285001070180401070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 232151888 1250 232150638 232150687
    0x405030d02010e0d050a090b0f120403020106030c120210031d0a20010302070c030b040615090902031203090c0d080d15060809010c200c0a14010809150714 68
    0x80b400900b0500f246009204440780c01449410004030068940c0018140203542200075070301d50316440e60a02700c20620800c50a0808440e456040c0420542d06411031000c0b02d025400120440e80c80300011102d4030009600254000700c00714100b0543c501941001c020b21108030340109500760903008180c144829020f0880f40c180d51282041c045072000349481029101c02e01c1c0440c00c05620303a031000020382e000e000142c40c640301000001c08002294010003590824141110349555644c515080a4032182c2c800300d119000d10b40403200c440c8111400d0341e1149012000030900e01c003070b0205000c000030054a017681e1800c0c08000101d4040050f028402d82001a20403070f00f44140340c4100100109800f17409019030b6418001b000e145a540104c490b45244040b00c00103c1c00030300907c1140c0390804001c9000c5c0c2081c0724000c00500440840ca00c0c4040e61400e8aa40a1581d03884075069150400302d40c00b810041da9000219986074455500220403041c42007440f40741c585402c3d2580302c0c4c0200070810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 232153138 1250 232151888 232151891
    0x11030703150e040f0803100504020d05010521030318100203010b0306030d030903050304080d09050a0c090f1b18030501140103110402180906060d05090607020105060a0e0a050703020405030d0201 85
    0x151034030701c1941c48000340203084a1500702c0076400c00c0d03910704000c41d40012000d45001c10220110303400c1c42400d40048000d100040c000c46d641e0955460321030140c042446510310510a10009400c1154030b418140098450076009d5442c50f078071a01c078079014442189928600e8454202400081e0790184021344c0a0090304100644900d0a101010305d000704440d142420581031031845800a03030808166600203500c481c4440c0c4800c168076010004040680002d80340d845001080b00c00c3c01070812030b0f801661041c26040c08014640703031500064440f4a2070103064014601040d2021521989184c03a640f40045449010560b81e030b00c4141c2982c0d0844c4080f9995503000004208000c403a420070341d010b96040d90254201484d4100003813028485c10301c80d0707010b0b6882c40c000410540d10102150b440b921941420440782c00c142203110384c0d411048a92102641c41d0001240c00d51600c40321000c115440504802c9496580780c1100d0003803c00075141d0002d05409001c0400d00e55414400245542e0540d0300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 232154388 1250 232153138 232153151
    0xb15130902030d1e050901110a0605040b0601051201170c0d050105010807061d10090801020705031c0e0303070c06180807020306100f1a070203012a08060d020d020411030703 76
    0x41504180c10042983d00b80030030f460400c0c88a1503031518002c000f61303450600381d4031001420b0040c0c4039180f0342c800121300c41c000c0584441c200090b079031225020700c0c080e80051003a03035a1500151070030300c141c014500c001c00e80700b0b004200c49100230b038084601c02c00c1081914014003806002c40c00e80d0024010480b40c2c5d035182c82c01444000030070072907507004003c0e1745800413001588104003050648041c102d43d0003030480d6041d60032210300400e0710700000c1641c200219540c4c240350a140c0e4607a0080a64402e1841e800c24803242030359507d0203804131a08844019615544440c202500c40c0c5010380c40c112030711a200c8204035019103410881800d1280207500003640c602d03c0d8810541803801c0284205000740b04441c05000c4103030300b000c0d50310035a00c0d102c0c20303140b04602031f00180c8598012240c2c001e40c190b08044043c090f03107603030418401104e0b0034a8042c407000c420640094502c21030071600a50070042da211244098940500c2c00c2c0717040c03400580001401090b000300380000c1e41c0201c400d10003007a01ca1382c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 232155638 1250 232154388 232154393
    0x30405190e0703110a0c050c0909010f050a1506051305060403060c030c0c1e0201020708120c1c0f030f02160b090c0117010303140c0105010807090509060709030b151309 74
    0x1c81d80300080d4074003000038156600408144e80202c0c0da820082164401250040040412000c180c0c0403008012041c10710342200c895010307205040150340c68a0411002c00c0407840c80f030181d00c4e006d4202c940d0000c1d045081010444160300328080e244200008410000341d0f5445405c0100701450088030301090042c8410300c041c043c1d80c010304580c001c0103400143e0301c1c01316251310340d5155a1503103819a64901c4195000403442c02d0019004242c1d14010156203040c18040d074001095506003100076551000301035a40c0e4210100e0007605200400c1c000600d46e1166842a40510080c0d080080014102034030008440d501019a08088170003c8050742031005861003041502c441e00024641741007203510b401146490440103100003000c2c4800d00b2008108000c01009440001401d070008000d03d6039210407542ea100814895a80610b00c0c2c80c01040059401140091081280c2e445402803103103983d03550142c01c4030042c440070309428603900400c980c5d03895940081140d80c0151004c182e00b6001d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 232156888 1250 232155638 232155659
    0x306060905060405180a02060a11100507020708060f0a020304030504080d030c1407020a05130e06040c0e010b0a08060f03030c01061202090c0324010e060c011a010912021203040519 79
    0xa03050256506500c00f402c51041c1780026441e0b6002c0e810341c1c2403078031101740341000d641202c4060036803010350007041c410b03a2800c80d030b540c4444d2203101c040d800c5480c02d9036658440380c2c540360103582d56500180800005401c21045400858109110b031410a140a176140d9805007000da0508540380025110f05081d01c0c00380c0d1007050b03408100070f20321229180440c55800900031a0042c0b052500520700c15400300d484a40643c00300352801000416103a151405140034842000301740107003090130303040f41c0010800e6850001914400300441d02c99582d00e8035154100281c000da2015039941c10710080012078120082030046100404c0c4008410284031494410021890780081841d02107090502c10040040300000c1c10020000544048080b96142c40004032800b500c034144007a0007400004030102070401c158400440c240010203042c030f00c2410400119405162445519144151190900c1c05403500c1000e13441c03865181d608076442c096882d004500c1000941065070204030001e0010011003140303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 232158138 1250 232156888 232156891
    0xb13020d052b0c03030522030801080d080106140702030a06110405041a0d172b0f15170115030507050108010e010f090c0c1703100509090618070306060905060405 71
    0x8010041189103003030302c002002c07464504806010161a20b0120f103240d00010001c4419200c0f80026000381c01c110304018040e00028465a5207034840d11041c03012081c81154468142c0700710f5580d40c0c003a0b10b19425265140d0300144021703039040c002c40d84124001001c5100d80c00d034114044000c540ca0314640020841121620903030405034115094003400240e94540301c01407a2580b00e04103041d138105642112816014640e60000000140b01d000c00030480134107604003500b40c80c1c2c20244100e51810820b80b00340c0d440141035866542600138144040084000039080c9075891900001e68825202d400c542858026401510b41c0c0d006444c0500030381d40d0150081e405482000c0500115500d4001100c421010078071800e034546540305c1c0d2880310b45118104642d0070980007444d02040c1d000312908044203610990b404104070651030400122801c0c00007405201d50f541d14080c10065891143d0b44261034107011012815008544020000034624482c4101800c0c0c801c0001034249040424402110300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 232159388 1250 232158138 232158193
    0xc063c01170307080904151a18030f0c091306150f08060c0307030b04020909070801051f050708160b070302250f060c050405040f0b030105070e010801030b13020d05 72
    0x42220350301084c2c01a003200c030052000d540000344a401c101417511040e01329001301007880900f0b094050700c0c0d102c400c098410070b28155102d848003240d007000c1683d40d00d24404020160703048240640003915121802950004025000c0108000705948810858240340502c00c88050501c1b014022028502c0d543d101622802c401403005080c240601c0a040c01300801103c201a183d040509258583c1d070183c6000300000303417880c103071410105800380262209001c2c59002d900f0320042d0019541c514a440d001c0f042d103030f031140b602e410700c9511219201d91002c00c801052490509482c4c00041c4608071141c401c20040c2c1d03006072074060846500412042c0504003039a5202c00585a0000ca0044d10006040e5a03020800003000c243e9014203850764001ca5001c142d0280c03410390184036401480e003103d00700c020214001c00082e0717a210001e6072000300d03411482d400070301b10000600000e10501d041c0380d00100c5907440d007040c03007d0640c0024110f01140e40101d4054000400700b515843d0791340c14490981c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 232160638 1250 232159388 232159393
    0x7030b010c0813090c050c010c0807050a050d0b030a0803070810060504180609240e0705040e042a0510020d05030a0b040e010207060b09010b0c063c0117 67
    0x4444000248000750010740900158400601c080c1c8866410340c1038801448041d0701405405080c1c580034015401c00f80310300c4403550070300211300b000398400c00b10140304000c0e94403400c1c100202e0000407076050b00100c00700519113554021250150b81c08102e541c5117113100e0071565030380f07182c20a801444140301a10348021445a01c0092102d1904a403c3d1001d940c5c100090520b980c82d441c080c0c0000d410964840060300e803901c1d8540004295240e903000380e258150145050300c0340d035090792850701641103a1a800113241808280400711240d079000d50885e0003840103180c6441d041c64000075541d0710018541d040f01c0700100420250038030000d4214600018006041700c81104100606503101c0142284080b640d280d000c0ba680782c3d140e51150320180c0c90ba500031500d07008249080002011032000062290319140c00000d99450300c00e003116101da11020103007407147c0305c07a0018806c07601c000c00b42d038114a450410410b010032a18001d03e41400c0300e10200100e5524204010701c0301e00c80c4594065a83c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 232161888 1250 232160638 232160651
    0x604030c330305151e0a241107030501021315030504050c10022b02060f161209021906030501120c03110114030709050906120607030902040e0708150703 67
    0x84841c80344107501000141404030f640d50790014080306941c0828106540145900340903141d0004d1919052181c040503101c00740090344842c80101002d003110b840c40e51030204a05c0854909204a2003000c90101d802c0c1119099034982d658282039170040e40729510782c54803504082221000780740c44070031035150170f0034208140e08060300ea40e0744914050749880e00400c5c0d0405600080b40c0b0811071409072a0710b500c003c41081d407034022400303c00c1c8605071224005110340710210302c007582280c038031394043d54094138800c0c0d40d045104000d0350003040f100703861151144e0320501240980c80b94515001140fa40030f541705001c80c00c0031000742c22904107030003d418100040380c510b4009003c100ca200180d039000380c40c0051340309420004882014540c941c03070050407804000e1040d000d40049041098440c22100c91860380e442d81c0920503a100c2d04440c00001d5440b1402180c4164041d61141036410300144c0045030f80c4143c141c060b440e0480961000341141c3c007803800524644961460b003a000001441c00b407119 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 232163138 1250 232161888 232161959
    0x1180308030a1e0606030f0b030114041205040b0715150b041e0312050403050c030c01051c060f06020a0b0a020313080a05120a051e07090605180604030c 67
    0x254080140b040b0310141d5106429002d504610070312010145240c2d8007404040e8441d08010b0203400c0d54010268000d0070600c0e400010f10741030107580381009111620607a959a507803640442c50713a103801c0020078044208004030f1200a510000c0090303500900f52032401c2c2c1c59008001c422100c001026400e800f02c4044113011500754142240c084642000d28900390003800310111886400c0c2d41d00003001d0341c402d210f514101e07540243c0604102c84c0204155aa0400ba80d0140354448802c2004907000582c100f00e504070030b00f50804c0007240e00d5890040010aa0340f0b9031200c20040c0115080140983c0c0080302d83d00801030082c07250de41c0b00641035415401c0d800c2092401d045900010002809540c02045444c2403610850039141050b0702e108410105041c8200404020b180986865650b80d1980d1444404011110899809400c05507200d004040c030b410000c5405402c0704020f14444041160411041d682c1c09010340003560051034103140744c0d0301c0c042240740d007035890910100003d00745800d803525 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 232164388 1250 232163138 232163153
    0x140f07090f0603020a03020405040f05011e0305030f03090109050a03020609010e03090d0b1e0f040c0501080907090b0607140c030705181b0706021201030303050703090b04290109020702011803 84
    0x7207448505000d80c03107000d13210045d4040d005a270003403034100d443d02c40804240c05207500250b040b20001c14013050714003888004e40d4001e01d00350102600d47c7d0300410461002005501c000d590080c2c0c4140009010051980c85505001c0040000c3d00164029001d02030b19540a110740424500e030b4000841c50802c100005c101c000322f076540b014081561000001c0c2c0f080b9103242564034000c005a40013181841c1800784546803040546055a080a0015000c41c05501506020780a21084c00c0200300b41c62900c0d0800010f003001160441d0462030602c56940000e103694042da201024420180c024890f4001c145403401e141c0f644040c0c4030b04510200b40062414808036540c100c03110549820074580511051a411b1043d59002030883c1c5c40000c81c2a41c886c0c01403115030599119a5040c025900c030804128281c50003044043d010b42503d0010400080d0084034203407510114500c410703d002c80c0c60100b800c840c0426170104210b00e4000604208560b4000124180030300c0042c151000742d42180c440e0728 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 232165638 1250 232164388 232164419
    0x4061815090618030504060815011b060e01021819051e15160507090509072105070e0f090a030905040207020f040c030b15070807080a050d140f0709 65
    0x10362030341d900d4085105202140d08090080c0500d210201c42040142c50001c0c20b82e4040d00c10000040c2c08840840d496400696010f042140c0582d6030400300549003081c4286104441e0084030000e680d45504508003500f0700240a5000103c82c950140c843c00e0403d200c64030b80c060071000170000010070244078a030b6516402e0058414680200031100c501e00c3c0108610b40241c01c42d2604460b0081022403148003c0d01441100500c40d0095420160380e505614042d240145d40c200042c1d0012401880a854034058541c0c00030308042602d1081d25560300d80a0610540d9003040180070039403410401c0036201001c0d61500100128001c000c214038a0f1001040105140a0148201d07000540300065540300c09a6460180000303100300441510603c0c05801440d203441c04038011002c0c1e242040c02101100151030025030421f00d080c3ca0705107250358600055004e840d011051001c144158080e01c1c185201d400d10100c40018007003184e0a0043c5a40c1455200811140030001c181c0024403600c804041c0c0305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 232166888 1250 232165638 232165673
    0x330105030303160216030f060e01050114060c030906120f070e010509151903050a0b0109030b0601030504140d03020a0e090601140912190c06050a0e19080a030305040618 74
    0x3c1210054482c001c0b400c0c050155003034285140c04090100a1100c1d01c0209500300b44640010885c0c03820403840d80d8240e4400348690050002c0c4880c0b90802400c0c03000040c4a01404101541d00c2c00000340001b035413541084000030850321460007000710700c00704e0b407038259000500b50500f0310395840d011000800a2080c2c80c06203003d8141c0d503900e04204120b85040e00c11301c10000741e00e110400e089080003001490b0454901490b01d0600c41008803a500640b426000c2d603410108a03462591142c0c0190701130000904103c4500901c110310300c18040080c48400c0304254255800b40c0d54600308003008081143c90252a88113003620340902210703030f801070b440c07c1c081244110015102c880800002c2e407408601381001131340340211030328103012810510005207840e2283c18042d102c81d4032140304496a000b4140d915000c08c01109000f869807600301c00b06160a4000719480c4203041d10703101d10301d0800307000580480102c1e80b14002c2c001000018001c5402d144942c0402d80e004030041d4898850181300a03d0a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 232168138 1250 232166888 232166911
    0x90e0a0c090b040e102901050f0906070c030506100b040e06010e06091e090a020301080303071d0d0b040309150210091e080a14030105090703020a020a05330105030303 73
    0x309400d503c0740d0304800d410320201d9050300c0b004500d1103061400f401800c0c4141000c0c0900fa90052052811004442103290040e51158201110039520f200944e101404941d4082030a1241c900051704003511100074600c103c01800c1d2908006442d50382084154010400c09241804180101419180d03c291321540910300142162035800100e0406c1c8a1a0380c01a000804800d2070680460035000b0348000c00c0040c1c800d540319030740b102c0c0100c00300e000038081c1c18015002080811101445142030000340480c40300b0300e812210202000820005281000329001c2001108010905812030140c200424007002d210900d0074005e00e00030340b200c296030060f601290741c60180300c0a02051035101c49101d000000031000320081e50038000003e41203442da580c0054003101e04078160b19100016a41220300190245980303454091054020350809813100046100308036890000c14002c00280990040c0744035884c1501810003ca8404c90008421945400a483e001001151400001c8075800208980c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 232169388 1250 232168138 232168151
    0x81005060607021c0f061d0c0303030624090a14190302031207030c02120a02030f030703090605070201021615030b03060415090c030c06020c131a06031f0f090e0a0c09 73
    0x9080c1c0780c1d54582c2d100031b8400b41c6480084040807420680c0040c1880a160480d852502c8140806a07203100850315181c101041c49a00117104c0b030300110309514400402903044c00d0840b10400f2540e00d81850388000308114003000750003c42d0070890250040302c80b46c010310900107030031740e0040381d902c400c4155500217004000030008245071003803a031500000e900400d0840d000800119141c3e99040c452010f034468080c50142c8421554000300b01e50425602d071311505a02c62404074162080d4200480c264154001c0c0b500d81640d80e00210700510143c441c584000e00f030540910720080840e41e001500034040e40c450703c10701000c00c00c207040b400040160018017140b822003501c0c141000e50711a90009100720b01403c00450000e4011804030a40101030795100080b8101c84450002d4604207207500014200c1580c9a80541c10400d0066034040d035480304080c1900c3d80085050307047c4c040c070380c080c0c24a07481c45001800758004500482c80e0000f84c0780d00514030194241c441641d0000d0342d10600c0d001c0c503134070714 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 232170638 1250 232169388 232169393
    0x10f0f05030a02040807080c0a061d01050a032403150608073b0a150e040b040303061505071709090a020702030712240204060512130c081005060607021c 67
    0x3c0446000d0b00388502070f180415a50410301e5682ca900c2c00c02c4912074841110041100c0d0f100b50f84000c040000b040030381d40380100700c40066a0300c0c1c4c0000105400c260b00c401c104004c5900e128074007403641400b01205600350717103141032100718103030040c005030031b61424000c040080410021301c120584100032480c0c1400c1a4500c03001c682d8035800320300b03840500c4543d0016003044001150942c801c81100f101880450400842840030044900bc0c81c85080742c24404200483c2d020304440340c4c024441c3c14006012034407095005001c682d200060360004100044a41c10400d178680c0d0001001018041d96003440a54400070700000002040d141d81aa80480d0203000e646d001c1203150014001e0488038802e42c101c81c104000140000301c0302d1407074010307103480c40e201e4031107203108450803184682d441170b081809482031088503450150019906241418148001c03544121908000345040c60042c98070403a007080103000da4500500452060400b400040096241c0006055800c841040e82411860749071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 232171888 1250 232170638 232170641
    0x6070201031e050702160602161811040b0a1b050a1410062c060609040f060b040e220507030f031106011401111f05042a14010f0f05030a 60
    0x141e603400b24981c00c02051085a58001c190441903150b6001540140d0307440c1c0300140ea40301c01c00300701e504503003541e03070700030040300541c11070310f640e0700b00d1456020465030f032000b501700e4141e00701e40c10109490302d002440701055074100d11040b2040b4409040798071a22042d0302c1e442c2e00c41c50407010140030601080c08404200f04144903070741000c00e410b102007155540301d452001c1840030a09080c1d4200c0841014503200644020042e44240d40041c080c610301015142440082c106844e4a04100364a0300d0011400c00c0301d50b00680081d02e001c40481f182c524140c50446140c8441d503588a204250025001002c180b001c11403e0642e034010a00780c03640056464100c274a503864824003003082c000c5c2030005c10304035a20202c01084074400d0781c13400000d1045403200c80c2c54000c03116000b54150441020722564039250303003140e54402c3c000c1d6080040540402d004141840355446506800c08c5a800e050002a007103c41c0d03903140100a01c0c0001d01d0201c80071000d043c54075400d0b401d4051240c08000250410000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 232173138 1250 232171888 232171931
    0xf0e04050f0303070e0f01081b09010c0215030a1508030403020f12010914011d0c0409030c05060c0301030c1a0702010c05120c070305060601140d020f0d060e0610020303060607020103 80
    0x407001202d07640d1614480003866032a42040c0c1e584140c410080e210310562049400c40e01850b10b16142c02c680c404203000c202180c0c1d1000d2110790601c0200800400940c0d101d1030704100c40c000c1d902400f41d40b80f03040c981d200b003201c1d490030f003c02076449104000c3c055000f00000351810b9983c15200e0050000302d1500061546605c0b80d00d00ca425803d22424808000b00344a55810300101d001c024000e010102e040f00b07001000d0844000c3d0315500c9220745030031501d40b80d0009240039029082c80380c10f004580c0c6034242020012650a80c6c054400030040040100440b5104002c000c000c0c0a0801c04072590300d159418810b2500c00b1b41007118034000d140501c40240940c05400ca0725089042d07403100c0614646848661903c401d0342c01d4000c680011300694015004240170904211340c403403606d0401c0b01c0000c001d40019014a1b8070100600284400d0b000f10b104040290619100782cbc0c4191812004000d42d208103468042e046400505c1400010b8881d98140d8224960908010510034040c400c5840740080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 232174388 1250 232173138 232173163
    0x20403060207061a0a05030c09100801020f030103050c0306060127050a080a111c083405011b05090d020402070503030f010e091203010306021b010e0106050103150f0e0405 75
    0x400211542040903a5124940041e113250300801003002c410300708001d2144921509401d42c10080b2010031615000e807129501c95481308000381045d03181e004c0c450882c1c2180300c405908500000044c000e01404009400c003980d000c500500c035034508900000d00b4848900605040c041e40351940207000e45404540b8030281c00c010b8000540c481c0d43d820000da8640b613004056490100e800c11303546203400c1804030101b1f0304c0e8140704032040c3e00700380d50344450702765101d6001000c81c118500ea03000d4083d40c00814103031403018003c241c02140289814560308451542c00b80540b05c08540c52100000ca030000142e603070500b401c0b03d64104110346400407402911904200a10ba40400004c000d43ea40504132801c3c181d8075a4a24030700f00b0783d9500e5401f6954403400260302c60450b020b03c0108009002c540041c0200714802c0d0f04280c007a50100341e40c50a42d6405280145183d44800c000d000d5541e061042d1041622004000340d8130900d4514260030072100f50260768400d1400000040038840b0070015000f5590 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 232175638 1250 232174388 232174391
    0x804050a0b0c1e0906041205160e0402010807020f0c1002240f060a0b0708090103140f0a0b100c02040b010905090a0509070905040b0f060102120c0f01110a17070302040306 75
    0x6007103000600c0c0d60340840352124840030164843c0d03400ca41a58151644224082c280925040c1404004086400d001604a440e8894110010605405054004010301078084003401c54109440050031104006200b202154003c162408215400045905100c2d02c181d900425055020b04103d04004513040d0020390b504281c141c85a812030300c00a514412101d03d980e005e00c0c0c2d11500104000510303d481049000c070f02c03d00200000c24404c900800031346c101410002040200f845c041d01d540c00b07045070740c48400c0c40c0383e004002040301240500044000120b6035480d80030014ee002415900307100790040d00866135035202c503401e039015544180c05804000c05103c030510340010100044d0000311403494580c083c0e0b42c0c2c000340e092603c0c05154091948500300c080f180e41d84408101d00008014100b40c118800d983c0c0d00712014070404010045012408041c1103203000078000542034400400d040c40030200100300d035241041d48225485107a0410541c40c0d981911020b0302100640950382000d03003142d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 232176888 1250 232175638 232175641
    0x5040b181e0f10020903070303030e010b0a0e09070602010506031002030a06081204080f010603020604090510050603092506021216021302030a2003060103020a03090c1401230a0804050a0b 82
    0x1801c0000e0661201c025800888020341ca126200c501a0701800c540c0a4042d07001c1241400003d0284d000086120828400040c00000c1e0300c00152904020368000c07c0058075682c240000101d0a104850252500d40001d01003810003002095840003420b902c0004030703a0110105541c6602ca0f0000d00007416002c0442c2c5a8071411403e541c09648980308003615442880c2302041e00b481c060007002c04031b0b07070000d00090605240c060400c018182c02409031307100c680404000700e8a692410091405041400d0080c10100d4076810035056110f5440500401004c0c00c01c0b04002d0103a0000314145108006a55582c90f01004540082540985500250311440306100e00308802c155a000c0d51240399501c005000c024004030492601c40b00107418518511400c10004e299540603800801302920f5624000039500c0f502d4950034003100b1190051040a1000c404000352503a002d18000105040760340300c4074215141c103001ca909440b60781024400c2c070920100240500c581031000c502c3d0385402585d1035505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 232178138 1250 232176888 232176943
    0x1003020f01121d030a09060207050f041109090414011103090c04020a020a081611100c020111070e040f0c05060307020303040615030812011806230a080d050901030f05040b18 76
    0x4036040380c240341c5c00045407503600144040c0b00045610413604041c0c01090072038424414000600744c0081c2e05010302404200200072615600c40c1144564041c010440400040410306801e5130b90750440f510301c0640c00d00038013051100202d42c083e014401124016540c0d95201c806031708180c1c425901804441c40401c90389401c042c0c040b6000400b51080b030242c00303d65241e4080102d00c8914807042400600001038800055000b0b1a10040105035241219250ba50f1003071442d00620003100c045402c2c0d5890400081041010384850010b08402c076015419840d200d54029aa0f0100030300c0a4035054544043c0f0064040030200303140507542042d4aa43c0d030346005000d040a0b00f0f020700c03461b00100c0440030a0110154248030700010765002c0031452804588462884c203003c5040351a8690100f03181e040014840c00400000a2100d0f10b80c6850361200000c02c0090116070040c812480064101410000003610b00786107640d01c21b808040182460b07a0341c4000c03034540078100154113100200071010858 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 232179388 1250 232178138 232178143
    0x109120512070f030305180d080405070807030f02030105060d020607150b060f13140d0611040b070f0c0617060603040f0506010f050a0f060f0809010f1a091003020f01121d 75
    0x8443e030103a1428065926101420b00840080180c1e01540340c00c110000c0000622500d075581e00b250040b82151604d907290000c82d41081d18076482124444146194181142002e001d0360340c0c00081100c8940c0030000760780200d180c520030040000c00110401e41d002e030340208294480c0c0b2003110b0140c05140c03240c0f880c45489881d54044654410588510400040c1c0b8640415890900c80b0003e40b0100b54080b00c2da4840002c0c0c294030980c07088265040c040800e034002d041e4050032a140c001c20703100303489c006903051110f1070070501e800000c00c0100015030301c450000c00000d2075802c100b041c1c0b83d85a07a9902c0d4103103c1c000c966249170003030041c09010000a4406c261000c010142d0384201e40740030000d40d98550b60005010a031207180f01044040b420910b82c140a07405d240e600918a01c00071592800e020348407800c0740c9810f1800030200081d0401e19516081480845510103400c0a00c040c45505640000d24a4001d101c09981004034284072405401300700d4009168002c1400045010507102c42100b54 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 232180638 1250 232179388 232179413
    0x160c05030c03120a0507020f0d05010903080c2a0a02220b03010b0a060e0307120605160f1d060c1203070206070203030f01120f1e050c0d02010912051207 67
    0x512a1080075070712001480c010514101220107100c00c07514140844600b550b05130010031060782d002c8555420801c40d62565682c40000d98400c0d000001c9451a42c40c0280134140054002e203810031045c00b454001c180035200403060140b4181a61b03103903034000000303146401c00c8401700030740183c0f0701c40e10030300281d14620311b00c2e650382c04100b41401204684800d05003219160380d4000c1e4450302400e020440d19000360f180c0c1014541c05400e4403105520713000c2d84032035590105400c0300d0541c1c1d508204418403140350a5100c6145d03852603c00309000d080c0304000c00b1a2904100e41c51810100540c00f005652940300311400d50200d0015101201825159040c0c0b507041100c181025005e20700c001410184080300f1248982c0810041d54601e909180101c0400781c52a9005c50381c8024010303211001c56885160103040000141c1e40710318401d0340e4600b05050905100086020b900040b00e10380040c1c0c1c006c1d50705800e40c1c60108414030480e140d8140766103440350b1f14051103014600003510506000344000d108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 232181888 1250 232180638 232180649
    0xe191113020c03360108060f180712050f0606030a050703020c0106060207080d0903170307050f07051e0106180f023603031c0b030a050105130302060a0510120305160c 73
    0x1038056054100d07954005482c2c801c03813074001400c1d800000c4941c50040400c1c1038801c0042d004c01e00302800312012600a8070207654680c041001414105c0162005004a03a48600c2481a8002e80c0c1440004114540401703418803901c9074403070707000074400e51090b41a603000802c0d0340300038003c40d9a52070000e51560400d000300e58280c01613001c5444018051602281201d501603038071842d000c2070340310308802c0e0f410142455042210800151f03030b003980044d000c0c1c0801c9004a000c3c010503102c12420032140e00110691860701e905040c0c0030800000884a444603419480d4004180700c0903c800d013030001d00c134846d6002c8c041950305501074494000034000b88042d10080a850004122a40802d0796901464414a10203c0040b4201c0c2813134859401010050300b02804448000a160380d80070b00756001140c00c002d03a410075810b41014998100444c5401c14510300b02082941000d0310080500c4000d4001c5060b40050102000c0401d0b2052040302c101102d151051403025103689460b010200481c8903c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 232183138 1250 232181888 232181947
    0x203060a0c1821030203070204060b0a1e0e0d0507090c081603090506072a0b0a150302032d06010e01052d150c0109060e191113020c03 59
    0x803500c00510400c0a1401d4030240005034030070840003102d00f04543ca420300220114003050143c0c41c0180c0740ca0044c030020348a08008241c0310300c00000020401c11042d001c40d0760f60403506208214040c0c12001c00503201100303503615079101100e818094a0039015601c90340302c1301e2808407008101c039440302035503001c0d00135450300340103460140f20101e00703480350010080c10a401913004a40114010000c0442680d6044440c1d0401040c041c468030502c0c2c8804410f40300c9000f05010030500c0d00300f0380f082844000e04900010310250030f60f00482d030b9400901082450044e900019100185000080b40b00e111503034030304a681541e11050743e003250120a2080381e01840c1e4172245086000000c0702c6070717510032851080c01c20500c03550100304500050042d41e00107000b50b04000e02e609241c400e00804140300d014100100d607140e600c1000c1b61402584003030301c2e506010354400c041c0009078103a101105456003110b080c01d20601000000340248641104c0402d24880013400c20f501d081d601e00310614141c83c0304078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 232184388 1250 232183138 232183157
    0x905030f070312022a0d050a060507081806060907020f071d1b0a08060402090a06090e091203010e0402130912020f0c010f0c080c01021201030b090304030314030a090203060a0c 77
    0x400ba6901c05a000310800817041182c2000300000d61482c1d00500048014041914503503d52951400c0084101003914290b07218001c1003581904611a90f4021035401c8201d100c80e448500c0036030302c80102511031403089c1210004200307080d100304091298522090300741c0741081d54840005950b03464107404e08580101003000940c1c6411030030100300e0b6107100130f440e49140513401c00c8119403214005150962090f82405010f070540c03215038a68002c3e00d9240c64030024a800c0031401d1411540c000c141c440d843d40140300e0f10f130446604900b900e04642c10400c81030040c0c0c4861000030b110340102d03d540c21029181c4401d00042c409802d4103a4a601700e203809417003941720040c01080d20741158002450114442044016240d480b0340c0100078000e0003001441c0c2450410650b95003a644405041d4640b8000500144113000020840381e411001500055191528655003e40034540088800030100da02100140007079100c0c1d08001030480c0c0c01029036405145c4207040c100108020040340001450550 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 232185638 1250 232184388 232184423
    0xc1a071104090309050d0201140307020c030601090b0f060a03060b07032105090601120303020f0406050a110c1003180209070f020106170307061d07090603150506010806100905030f0703 81
    0x1080b088120b415603030b1240001e040009000f0340301e2000030104e04022180824003a0850588080c0d0700500c8580d018080184d450300c1014a00070060700b08400c8246488228881f036903504c00a9101580140c0300709031580340002040d00100030560018034100000580b8008059020352801c180300b0400b05210940000071050b10100c0d1000c40c0d0314211507200d000180640a43d0403240c51a040c8640b03005450661010803040d02504241e200e0030103e4400701d201140250000361070550304010038001c05a042469000588454103044000141039a03035a500c090161005002e80500350081d20341089401c001400a103a68440e080450055190080124038001c4407070007202c90241036030003142000002d0b01c84100030201c07541042010b841203017160b04040028005e1200900c064840091100c3ca141001981c8030440e4241441c143e05e00020011140c0c1c10102c41078100b02c3c251500c180e441c0b1410b005842080130f0307070001d80d41489102c0c2101401e01c40000c004050b01c2c81103485680340c91105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 232186888 1250 232185638 232185641
    0x409020409091a060d08091c06050106080609280f090c0302120f03090f06040e070f0f0305070203070f05070f1e060c030c0b130c08060925060302070c1a071104 70
    0x259101365000b03400a200c3d801080c07201c4003030901c07850010110941c140c1c50601400e044481003804960041c2c0300d10041200c550001901c6500c8041501c101c206d9141268140b5030b035140301701c0442c03110444095540680e0340594842c1c80381c1c2e02c4020040154580700d00381400062100d120403480382e103070040704580380a000f0a03c18400303900b0000075814a501c038801c01412406035200c0b244c000106000c0015080400941c0d00d00454a9858040a184114400400f00b1031040910b9003814105030074030003126400011a042103400080341c030303110010f900d0254181041a03010046610b40810046a83c03003141820080d00c0300d050b60301d00340290b5200380a50714040038200240110b5410114000401c4031504419404001070010601b800095500e0301d44088581c1c00c03480c4a40d001904000319190100f00d004601009801480301c0345942020003d00070555000c6c5508058022400004001c810072513070010781445c00d0b01610410b048414141150002c030000d0398000760707840250145007050b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 232188138 1250 232186888 232186891
    0x1a0a0e0705010203040b071b17010b030601030308361605040506030309010503460509102d09030807050f0702040c020f10052a1209030409020409091a 66
    0x60f0080c60030981313440e18061094001d002c080d2422030002c0700443c0c0c4621030040c800c002d40303141181141580b40250013942113400980c1018080d9100303000500c04650008840c95001c107101c40c61481a01c40c0021454070090382d0144510398118914010b411100003049602c03d030f0303900c0d5041c0e001440d038a10402c13050300d6040e0740058240d002000b050045501c604002c42d44081c0c1c0c1c1c60703608800d45c80c0c070040c20b00400302c0401224107900605e0b00418100208080c601c05801144428800c41c00c11083c40c907114440c0d008517030211035a07076841c81410503460f5851540400307500780012940401d00b2140c0c018004040c002c4002030540800114668001d000399003030211410360307803030a0508035800d0100412a000703402003948540c40d00f0315116101000900c0c8070b940d0030000414541400a5000707000100032003070b60112141441070400c0c2406480a41c1c00018900011883e19101c00c0581806c500c130b00d0704070702c010714000540030a442d0100e4004010852107001e0b0514401098440ca40341c00c0e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 232189388 1250 232188138 232188149
    0xa050c1914060915040b030f06040b0102150712050118060e0108030304030513092309070501021b0a050907030e100912030504030302042c070c02090a09030c1a0a0e07 73
    0x1c0080341501c0070b003090b501074080c1070800f8245046203442d580c204403450f0402d5001070300c40719000042158040c6090216500b0060070348060101c8006580003039129001c03c5103d810514103100000c01c3c86102c2e400700310038000c003500204025611440c05454001040000c0352241f414407000007440154250f0190491b40c1e03441c05541503446070350301241c1c6503200c0030014840ca03164100108500409102d44000907142668008104a0811441f40341250051080d500d80e000141c0800c440e903008191200e00024000f03000d0708207480e000000741414180d42101c1c2d0800c1d2501c1c2000800c640541c00501c6001280c0c00300d40030380c60703010010416500420301c010700f0442c07800f0650580e50300942200c2d4000b4401e0801601b840e864a1b0004400410f02c00b40041d03100001a10903000190045056000441c61038203d42031003603500841c984c482c021f0703e401801c554411220050510440c0e2008000e40d2242111450714a0f1414152041500391816110540f400d091355690004c00180c01c401c481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 232190638 1250 232189388 232189409
    0xf06070c030311070e070c0c0f0515090d05011e0e070b090409060605030d0207060324051c020414040212160b0c19050609070b090a03060c020f0a050c19 67
    0x242140d40c125010603001c080c65403140b1503184c0202c0c407001004901d40c0325110581d5185449080390030240c40f444000d906c1071850b145108000d100c262255148020b140c1c0c02c80424503500c03640180459407090022102602c103500c1d0042c02059104114042c0d0002d010456003030014800d040d4a42d51101428420a07407840790411805400b420036030082c0c0c4115000c1d000009619603107078042410041107840340001a00071510a02c07035203416120388110311111004000920004008008945150740280c0780709500390340940c030042c8040304440f40c0c000d034041c0c002c1c032110700b282240351120b1100740d408074820111081c204000d0b031030000b01250030b8005000c3c0c0510b82d40c81c06070011080c0d44150354100302809403101c1e101c1c0390389507403a01c40d036400c0c421002002d00340b40c15401103092100b03035013010000f03142c100700c2c0c1b02c6160f03500785101042e241c10003000258007000744d605a10b005981c2800c25080d0007101340306020700501051000b92030b9070995110300d5103564098440520b507954010501c051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 232191888 1250 232190638 232190663
    0x60f1e0a050618011e0e151513120b0903030601020c010e0d0503120106080c030408190302070209090f1002090603010306110c0f16061706090a0b060403060b0f0607 72
    0x2980c454001540040e8080c1555005084003003880341000300036000504007003003000e806400d0610300d041c04801080d0101800605040c038003513600c80c481100c13080d54840c00f1040c4421003d00300d204100c07010588001d01c0c20702031130382e41c40d95280b802074480020345914066500007110740001004903403103414140d0241c100003010700700545121183c1010a5001151220074000148040008142141110380c902d829589000070042c000c0ca4014440d0090410030b10a03c0001020103007514020408142d80c042c086441e424101e009014850010b503200703956005002c004003020a4030342d2018441c0c2c05499000e041c0380d0200e020380c801c208030180c10000401c01000403a00c030f54000401c40f0100091180b40041d000000c1d8a00524000d9069076a0450318840700c01218030310480004040301c0c14610003101c25140c99801121004100300c0c080c110020000b402d4610640c04050002c0c4002c007499100c0b13881e820110020842c078807090780221550005040c031841c111003600d540c5640119540c81c42e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 232193138 1250 232191888 232191901
    0x1202090f0118080a030507021009030b0c030408120c0705120f180303041a0a0f0f0f1b081b190b04021c05060a0c12150605070515010602060f1e 63
    0x100c409501d9090010b00040c0340102d141c000600840040034020703a13a00b0385594641c01000403401f0f907003054a044c40f18400003080050300c000718803030b808184124015101d0369142042c14192103030554401c60014030034100000414403030007420006000e18202c8141000e040810b209170b00c80c6909610345020140b2000303407668041030410103c404040c0560b82020394840b00044114012107400c0c1000d180404e00c081e01503484906112150b0362440c2800f071103030706150b000c0c0c4170440700700e0780104201640351585070000e43d184440400690010009541e21641c80c0364501c040301910ba012224056070070202b00064083c0101c0c0c14042d0131070141310f01a151a4200070396a16440e0208942c00300301c0807031384040350051049030711841d186000441c070000004401404c508070565219180362130080051340b01e0074000c400800340c0c0e04505100b13980e020b0f5400c00510380481e0013010780340221201d00101d0041d03808500c848c0206204855122691112482c0c21110545101005107140400c0c000910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 232194244 1106 232193138 232193147
    0x90902120415110a030b030c21010c080603120a0c0c03080304030e0415061b08070606060306120b040201053006090c07031407020a0b0c0d1202090f01 66
    0x9002e01c4466410698092003013a00c003099034691051429460800200004400003040d002d00c80066481d90b104020b5100c4543c2803c0d400c1040c0403c0c41e40c00b8108203405014024040d000303130828200222020740000801c5010400c7c1e0b1205031b00860901d030085800381d07000716041c0341d592610741000f074411001030b02c1c83c40c003851074006400c4603a9000c10301c1c84190f421a00c0d20f14411103061592804290742c0d00806001914005158403c100d400c1d44444100c40d43c0c1e443c284003a40c0d03241c280001c502700d8203601806032010380d0f00080056200384000c00d0720002c1a0201400464428008030300401e4032080079806284420611a0b545018501c1e02d60051184406c18a00815580c004104c0718800e41c030305001200c00300c0e918085548504110025100100c043c580702d07070082c00090b59810b04858030201051441800c0714903021280200c404421000c0e1a21404c2c50201c0011a07 = true := by decide +kernel

theorem cover : BRFrame.Cov 232014388 232194244 := by
  have h0 := BRFrame.cov_init 232014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 232014388 ≤ n) (h2 : n < 232194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
