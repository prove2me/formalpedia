-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0561
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:27:01.979736+00:00
-- url     : https://prove2.me/submissions/a1fb98e7-934c-47ae-adbe-d3189c45346d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 100719424 ≤ n < 100899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 100720674 1250 100719424 100719427
    0x1206080d030606180509040b0702100e030301050301060906050603041713260d0206042a0b1201050312070b0a02090d050c13020f03010504180210021612021023 70
    0xd492008014090350b01ca0b01c404141c0c5131215402c149a14044842a1a40905801e01c5500c482e590140c0d0314100030407030003c500540c409104440b032603004150030260031b080196100d5062504060840e8a541c1c4450702d1030b468800200031548401040e82c0e4803075084805110f0342950111a171096209521115643d0055010040f6486800825810f1009100d0504980e0b1800ea24071250b80e80f405050154056441800040c5c009081022003c40030010480304401110a004410315141c145401c06040c101c0046405003850f801d00c09050300510044008116070040c0c0c0000e81c1c0280700b4800040c000704a201e0024900f00e04540440b00600c001030000c1200050b04d04103c1e4480303004000f902c2c42507400d181c0c1400701e00900d00a8030115a094254586540d1801c000c100040c8400c41c50403401951559541c2c1c0580d4609903104030703010f60b86d005403d48541e503e2130303a1004540d58000220150040342044050b84806603140d013100454140405441c01031101040c10b0180c441c00304107140c2c0d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 100721924 1250 100720674 100720693
    0xb0406200a03060b16060e01110409050f100302010f0302030c0909070201020d06290c0703081201060f0207030b04030e030f070f03020112050402180c07080a170a0905030901120608 79
    0x4850041010700c281c0d0b501044559102c031801c003900e12601a032150407040c10f0800302c011a050340d10149900907a40000682503203c5401c038080c6070096408040b030320390340300c00304500d007054100b4180c0d11107258084402e605040d60b0000e482050f0000300c05003010360100c0001c4c15180d0800894103803c000601c01046840d00a070028041d601800034811194103002d0005400c050729081e022902c002c49501e0098117201a10083d280e03040031700513040c648a0300748000040b42d5610024100201680644440d9605000c0050a02c8040035a0942158050303441000801c3c00750401039041641481c002d040e5100100c00240341c0644019038100da40945140003a80c024100c80d5581164402c0e02e0710441e0b04e0044024400325402154081d42007000c0902152071442c401d060a90301031800200c0505040090f00c4071403c40e00a07080c030b078001c16841c010000c0e4000c03101000c154060264841400170200c02d94825449026066541d814000340079a885076250300c94101c0b00c0600941001c580c100301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 100723174 1250 100721924 100721981
    0x50705042309131208070806010e040908040b030f092b03090203120c07080102090d0f020303070602120406060801180b09120d0f0b03030a0807180509161202070506040b0406 76
    0x3000fa00031941400305920302d40c400c9000300c03001c1e482410651590319290b038880c0015a00c1014041026a0140d80e880c1c4440014240e00c0c0500050485499125128a000304005041140c081c0050859078025910000f00306042c00d00c1001d910345903104804003c01e0240203030302406107090029454000c4d69040980e5905a0740a400141c10b8403007220005030380c6a032164200e1054025864000e04d102c41040f001c00d804200c4100242c0c40507040301d2616803281c84030380882c0c02001c2c0c0c00034110502e90900003032100c0c0d80240d04c081d0010300001c200c8170f03911003100301c2144c04440005200020350000038031007400c107000c1580034101400300c0b195110f2080c0311140003890401c84010245161408400c0f02d4180001500c0800c0c2407a190b101d100d84a1050546207034a040701c040500c80060640441d15880300015580200d94030041c0031030840704024080c2c60180300d004c000f0700c00ca105000c51400f184001481c079400c51b41141401c51103459a0500101600c2408580440000c0c0d83c41038204c20f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 100724424 1250 100723174 100723201
    0xd1404050909010f0f060806040b071419020c0913020d020102101a1801030228120302150a02030c1b010b090f0709050102060114040b01030609240504050705042309 72
    0x60304c01d59000c0200e62407500e039090480d03105014960881d0b000d0b000240016035085103041c0c0180c0c032400c0c0802c007203801d03682c0990103070302c5440a181a840d541030100c400c241c04002d08944090110b46640d414600301c901451502c29565010b44103440d0049031006690090256841d001a02941800b024a40d100b030501f0018071128664021403410390f005201011008486040c0c0f50b009018034031900085441301c108404881c2d80382d02c40008d02000043e51141c41c1c1042043d10710a4000e01108010b10008100300a0000c0550310710900400030024001c61002c06c81e401c074680c00b42c43c1b541003000c241a050040c00343d1441c19401015040c00d000c0c841103540c1005101e4101a910480725030307250401261101c0082c480c40c6440c3d02c103802c80d00c0191906800c82802c5801c18500050041d0f41c80922030166560443d0b01000c40310b1010303034846180d221054480c0a0042550705010b54144450300074024400c0c1e10484030540b4096400748120081000328521400000f00a03505c1400c1c0445280001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 100725674 1250 100724424 100724441
    0x30f160c03021e15071205031503060a0c030c0905010e060a050904060815090a0f140a0203010908130503010204031104050415090c06030b030a0302060103030f090816091d0d140405090901 82
    0x15000c111224a1104d10a000c807403815900007070300302d41c550b000001610990006400300d184d485066a041031141c03410003405110714810f0401044c14120020b001e022561790803a600d080202d102018482c59070424551490382600baa401d42d0b4880400c0c0e01140c0b280261010940e0003414200009191500044c0301108542c2014000085441d10001580c1e20407603000f00811043c54461400e01140c0040000081e0301c08640aa0311451010b41c0024210b400501080303440000204503250103801a500f03642c081c28081e00218509402c50301c40c1020b103054035950610580d12180010b00b088403080c0c0d824101604040c0c1409944c101340340000c448142e5000711000a0b103011007407591031800142c0c2200007501078000d04a645d003182c80c1160302083c0311101070700b40105940e0004081d0010041070240310310002d42c8081007400c00b40480c0c141e0301d00056900b00311a41504121885c100410b0301d8840c44000d0030540c6406501c04d050105500417036100a40c0001040c04000c0e41c8001174219405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 100726924 1250 100725674 100725679
    0xb01090e0c0c062403030a0e040f020705160608061002100e0703020612010312170703090201140d0e070801050c041e0504050705071406090d0c0206040302040516030509030f160c03021e 81
    0x249242d080085c9a564000c44200170001411381c031000840f4101075000c0301d00340507100b50261400e5541c1c1c95a13807030454100710884656107966010410603078000300312070b08800e0464541142e452034050096039040781040b04803550f99034070b804403042d54041008000030b5034054180351703c48036003108400012809200598840e2480110f40054078072610440701d003104049031421054591300c13800c07030062031110300403410b000c001c42c24280c540380e002c0e01400c460140020003051141062025901303000c015400610070303a0500c0c091005800b0321000b82c3c4c003603411501c412085203058a00700360031195150702c0903030407510300b6050000380e81d800b00060079014014142d05120315850080d10365511030813280e0200d60b40000e2411072545e0700c034251404003540010305039410661640c00103004c0741c034142d46002424140c010482002130301800b419a1100714003004e9814440e4200c07201c45c0911401d6100703075107400d503045a4003c20903026484c0000d5038028000c91001054481c1041c3c11b189458046803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 100728174 1250 100726924 100726981
    0xc09130b0a0501120b06040f150302120102092107030605010e0105010e010908030409020906040803040611150103020d0f0503071209180b1507020d0b09010b040f0b01090e0c0c06 78
    0x40d0785550500910b81214009503180500342c550f5140c000c2d035803402501050b88143c0381c0c407800710010460301900104110340120700d00308924620420a1081c21400c0c800980e0340148100d111960f80d800c21800c2040c2d241039007150041e0007801044c203080d01504010700c864070300800465010700d91a03546060359002e032102041d110702e0b080107440998240c070580030300354070820080c001d0043c41d401801207840042e04490515494281050554000f6000f080026524907004089a50208041e010000f5143c46010283d41140c01240700114081c071702400200c0028400b1040000401c104e46200707400000c94420705514440003806204a88101030492920100c0b8903000640c9120307080c86003500400080420f0b20b00380c034030034054001c50000d9038041c6403056034901140d1300d40c160382e1050140d500000349105111080008a59141448040d030910300b000315811030741c0000050382070b28034003202c41c0e0555540807150081c80c426006020b00500034074040c06020581d1301940310107400c402c0d1211 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 100729424 1250 100728174 100728181
    0x1309090305091503130305090105070c031202071d041e020907110601090e03040504051f0b0d1109010c0215090a0602032d070f02030304050604120b07030e100203090c09130b 76
    0x1a100d02043d698000f0b03030960203405e200080d01030320040800c1101030604038108400d039105c000c0d04202590081d1303580120a02d41e184119414015078010304505403000c98642092425240004d0f8010001000009004081203960710306105501d0b80b07590080081000c0e1400c218000c1010449907240d030340b40d1080ca40045484040c038040d07208950046030003141810301d402d00700006050068a481c2400d46690b0710005200e42c0010810007410701984031680c0ca90648a0880444010a9000d40b4051051101e14400c0c1ea0001502405540480310300d0b01120f9428010309403403040c66403140e4020120800014072a40201c09060300d0040403134000112103600d00414822070361154810780e1010b04210407400640080ca40c01390881c005405c40e0706041e120008103100350f206420400b410000014290100503170b840201e80d100b10640703014840c13400000314880e910881d003444c00c40ca03550044001a140c207010400b4011080004105050038101294148026090400b00740e5600070905c000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 100730674 1250 100729424 100729459
    0x80a240e0411041a0a051210090c15050301060e030109021309030e0a0f05130204080607050705070801050c0d0b030a02031209060d02040b1309090803040f05010b0405040c08071a0f130909030509 85
    0x5050007d80001d0103040c9880c003900c013000c0200750340c04040328080301c84c16020884034010241d500d106070071030706c45940c3e0754141030021b03162800311401740e4440e038100106000180c8903101b40d411403940e102004256688240380685442c1c0d420340200e41c211448403000265004500012001c9034001c5e500c60301c02c00708880a80d02684205d014285407640004003003032401d07110350020101980141c0655442300c2e2102c100a0030349400750342003c0880070224610702900d40d28403038581141c008900804c03200010758042504d50b200700609290300d1070045039494094030b8030412206940c1100608658641e180d6401912641145002d2009a000075801041c0c03c0c1c3c80f4850b8101080d08824920700390ba03030310794502040322403604045419548804e5440300a48883c0991800b540c400c624900666040c5a07006140180c560f1051000100034188916180201c104072007880d01c1010006503500d894003103240150314550f010780441840c4c503d6100a25501501400c2400011104030800b982618107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 100731924 1250 100730674 100730689
    0x80306040c2c06120a0507171006080c16050a0605090307080f0a1205070801060f0e0d0f06060b0f04030507090209010503070e1c03080a240e0411041a0a05 68
    0x4400da01d40c18103001c0c00e03080e80c4888500400b80b402002285490b500258140400a040c0c034440c4500b51210280b20406411600510b03074103100050070034080c070f07001c541e410300c80e0401c0c4100310034007a0a4001c510090441d004541e8207040040559214a0b414600103030b44080c2c0600994890f860000464024003001c005c0300c101540202205040240d9071404403070359488410601c00340031540c403120391401c1540c02010310688454442e0841589484005400c03c03503801d00c50420800510240c030403030790382c0d41d41100000c0e400410b01e42162840d443c00200030b000a801c2000d030302c800442c0100405521800038001d4a200c0d80550703c440d66504100c0041e40600c00191b070124200b880000d0706039115030561844154001e01c180c481b0200880340021150a850055001500f40d1003000684002070013940c03c0ba081810400b0300103180e04454440c0311107a8001c484400003480081400e014040360030400e0340c400100200803039045172103180104225541018010620980005042c1c54070300c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 100733174 1250 100731924 100731947
    0x3030118060f09051905160807020309100e042301090e1609150302091e060a05030d050a0207080d0504091503030806040b06070b07020a05150c07032a080306040c 71
    0xe80c0800c90500f0680c00314040e00780100404044400d40d60200103100490042600500003e540b0085c40d034001500200640b10041144c002d5600800040e400340d00d550524124100d401d01d803207800503d0380c03800540600030418070b01a2a00155403004031082603881c0590403a0100c05040048180c01040e6540321ba031010a2400c1201c00c120040100d0001500115104094100f0240410782c403940050329509041d1010401c89501561104440c86030360066508040129048230f40789180c900001c2d5900c81c115050001c0000c041110950b40b4002c12803040a0000320040c7d8404001041c401040380e0010700c11081c3c00380c100013100000700c24500d40001500e0b0960b840d414960707160424040944103043c2a00c0c0c014900b0440c1034085190342491900666640e4060b000d49a2242080c1e441d2550881040b050745100005106030304540c54121004c030b41e07140c24500300d00c500c010b8050000103000c5403002a050511001a010089505d00a40c41103100b190104100354005a0884982401a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 100734424 1250 100733174 100733189
    0x6020604082502040f020a0e062502060409051312050c100c050408030f03040b10060e01121103090d0305090a11150403170a030501050108040f170f0c0303011806 71
    0x1040000d542801440c0084403500b00109640b050460366808101103e09065034030a1a9602154001000d039001103180700041e802c40d11075041020111400c030980001c0303901481c0c80e031031b040c224004545561040d20010000e52800300401d01c0c1c46860010340b203e10704803c60b10182c0d10586000018001c0003a45c003102c0000c8010000e0b60320001c0106c00034101c0c00344103420b2040512002580400410080c44480c030416482521790509241510320004090319080c1c038504807031428020780354010184581c5078000d10341042200b0000301420014154a4265402d4a10000802c220700600080d000311000341c030781d070410580d0344007070100b80c85003a0604020100142e440301440585010404800e90f4043c00603002e29055403640c56107244411000d0551441d13001041c00d551458040c8a000d006047c00e003480c54030740c940341e030340e02100e0000210300174041000c0d41072081d6418444402d503100313810000a0f59a80d00c48520540d0358a0b007092280c4002d25081070000307e0310545c02e0040300112a1704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 100735674 1250 100734424 100734427
    0x618020a0c03110726070602120f070807060513210504030f0c05040504051f02040b120a0906050705040503070f030c15020307060f1418060106030b0d050303040b100602060408 77
    0x56a904031050403d03182e40f110a480340c0e1002003001d122442c802c10301a40c813860492a0744188070314035424008680c0c000010340d0008045001c4400d5040216640010041d01650b070714405483d040312180504040544114586001c101c41d080f20303080040c001074050818206000319019850386a010764042c28000103a06102c20030010300c050309400d101d18407602c1000d104a0326031001c41c0c1140c108a60503191036000d242010f000b0000d9218034000400f01d039806520b4541800c4500311240306100000ca21602420005809103505602c04101c0310f038007100500613030500b01402052608240150391203030003074860020b190118099058126036104c0204a040c80c6012081c481c3d01e801c5540101c00e50100b001154009080c92046030001410f0140016408080c1c00a0b1075000c540101145400703c2c445403546034020340080c4150444640e0714010901456840104031500760008005205200210610081061401c480d1744290a100c040c9a80181c1d140c1d800c90740e4131020341c2c1c0500861030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 100736924 1250 100735674 100735697
    0x2030406030c0e030a0308040209010e010b0702060a0c0b0a06080706020c0d0303360b06010c170306030a02150405030613081602060412060605040b0d020a180e060702010618020a 78
    0x30340110b074401c00e603814000c0c0b5001005020900b00036125000300c00181e0700380200800c40c0340068003240509010600c4d1180c0b58107019007221248900d42019101e400c01003603680c4814072811001601303643c002c070683c0c0c0d181814225500600414026070b001d90043d040003103a01480000d00c00207155004204c540c40c03d5144d05e0030b5004143c4c15200b10000640c0307009031080b09402e940e115440d840c580e40800680085403d1403107802002a01039410402085074a0001c5080b035500c51920b81e0310303886116900d03200c0a0000f0b180c062188030003034001540502207010046030b600500704442c410f5040e1001d59550420b0000b081c000480001c24062040c064489261106540c0701159031000d41040d1401da151000b4854000722000211085600c500e021700140c2007a00418000100a403010780405013907500060b0040c40c140180d11414000011800c0500e81d103400124210760b81e0800e60740d09040845009000e080380d40035881e1031040010100d000150781e842220a41040e5680e606034044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 100738174 1250 100736924 100736927
    0xc0f0708070b0a080c090613031101020d17070807090504061410021504060504020d0212010507110f120f0904110a0f0819021606062c0403090512010f2903060702030406 74
    0x1001101921f40048013409240030f1010900b00e884050b602900d5841c0c0404082c000080c03034145c48600400806c490f03d4410f00e410202c2d012801e4029072181051803107580d03020300840c0c001210340d00c01584282020800038101812040034051800166400310181880714000eaa07201c40590400610824540005001c10346a602175604244000c090f4040c14440b81c00058120041c0400e14000e41d56800604c50b100743c00a0122001c68054006032200d402e80f468565195101c640354450403007800110995241d0043c0103e5000c02401041000030b60f820401141d1142c119840581c041101049800001d900405500388900c44080b0301d005142486000f4101075084142c003c2c1c6012008006040022505c0c041c0d00d0250255420300e0505400c5207943c413841010100c0d4007019841240180f0020035480fa0036041a95800e480c144050a14401903500504044845a080b5858150300f02d158100081d809045080c401040304c141d030186070109a281c1006581403005613004200400005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 100739424 1250 100738174 100738177
    0x712061a01020613050c04060f05120d0f0c05010914160603051009020c150f0912030f01090b06160b070e0f0f090a020705010207080a080f0403020604170c0f0708070b0a080c 76
    0x3135102d42c003078441c0c05600c0c0300401c080d02d8003608090124004180f003400303282092440020020307824070041030200410b034005805180240103800401003510100400c0c44825003011041540c4030081002550400d0407598440b0060316019a28610301b80e0002541442030044900030903c80041d9140180307002225002940051844406401403482552a0034400d0207900e205000c450020300040c50074800c420f0408203000d03080e040012043c400d101031440c1382c611071410b44010702000070b00e854800001404600078200c080002210076140c080800800c1403815000e26025120340c1440042041040304021011180e5a044810619000101c0c034101c07203607030303003145414800520382480b6445a600b6640088010340380c1e60400108107501541c40b449007a40428030300910085800d06680003900c6c3c0002401c082d01c48441c602100e4480c0030900c00b103800081501d022140700714125240d0507144c20b190305c540409070154031400a012107001084a81c3c55117190b80302a2603a81d80116003038503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 100740674 1250 100739424 100739461
    0xf020706092c07110c0d0c09110408030a05070501050609040b04151104030302030c10060e160509060d0e0c03010e03090603100b030708191b0c03020f0712061a010206 73
    0x3007690682c0d2155500c440742c0c0d1841c0202c03190350b500c0144c00f0003650350034500030000d50128000ca000240c550041000072070464280d0744801000b03c0d1545044000791505d0040350071002132030000184006d0000d4000004141e120320a100a01003680c07140104281c152088030054446207031000014001070100e545549075624004001481031a401c00000b19031b08141c1044002da400041c200c03084d11030030801064213401c0e46030103100c407604080054081c000302500503400300441c803003420007542c021403c0d50381115028003540c2d110440c1c5400f1a014080d407038030303d081600640c0e10200543c14103014102036140072000071891302100209101131680001c064501e100c040003408118074031850020740c0640c0d80c99642da005030070104440030b150081f40e4410a24580340c03444480020000c114003840404142c100402052401e04040c3d0411140001c141c3e0240a10340004c03da03182e02c10425940103000c1c4000b00010714041b00640c4070041109001805a403140d40010b80c000daa40407800b05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 100741924 1250 100740674 100740719
    0xb0403050304020d05070920070503070201050d060306110307111204060f0c0b0708060a12030914130e031803030306032104080102031003031202070b04060e030906040305030a0f02070609 82
    0x4501c2d0301c4d41c0f2090300701155078208401c00d50322000c44c1000104621459045034821100c01c519200740d1b40c0d1951347c1c80c40b5949000f414400086507a01e5200d000307a01010086402160502441249002030700b400d0303108585440209000d82c05503200502d000620003801c8248401080c581800c00c1810380e081d446070480d8008010b9005412030011305d00410581c01225a51184003240c10094200718160003682c21250040b10f00e405803001007944448554122003141000d2a10b10301c884001c6010316403c110010301003400c04906500d0520000014001e11107943e014500e00742c004000c064807488141c94655055004c8490011f910000710555249402c2e00e640c1c2c0d52420f070b5074110607801c2e60021600420114a001d00800a2580040710305510f1400c0c4141145010450b558206004d4030280024001642e9a00c0b01040c115040017281e5606200400c003544581c0e4030701c2c00030b55a60000d1080310000d030030344101012031400020180151011511140b580e281021100740c0d401c4e161216590 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 100743174 1250 100741924 100741939
    0x10f0e1e0a270c0507030f05030601030e031803070902040f0b0903030c0706030c02120712140d090602041d040201080a1e050103030c060509030903070311040609150e01080105040b040305030402 85
    0x60040c16041004601940c001e0072425031188100364181181c60f1029114280202044150000390384031403210303400441400c017541c0300e44039140124000d00b047c070200006880b000a0000d1003410707202524001401c110207c442d00c545921020b000d034041c0744207030745811861000901c0036401000142041d801e000e41103034200912116601e1a040c466400341020a5440b00341c008840c1c0d040c00041003a1541c00085407500400755a03491815102c44481001c0004100346800081001d608139151062149000d000c01c4140b42000070003940540300b501d403801450039021242100030000288102e805031180c55580d641c4070700400c05422651401880c000d000c600c0240d024030f1b6441101e02079170003a502c017003800c8620319040c1d08645000e8001d01d90341d482484100708a42d4001411025264800d030016450074012000c50054081501302341e40c4103080000e282000c0c04103030400c1c021a44c485044c01c83d5a6a81c0d070b0024202c680036200a0b00740e0440e0307000500428003401c0159003182c40030b0b0652 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 100744424 1250 100743174 100743179
    0x120b09010b0d2628020c09071b0209190b1005071b0510200730050601150212040602030307030e0c09010602160501020613020d0510110405010f0e1e0a 66
    0x445298010710ba484500510040c109400581c4c6503091007401d1140d0000705416002e00002480c2e020300100701000f0400b800b0350074140995000c000c08042503001d000310f109170520101c03001040c54040f800c003070458605130601c0c189142c08204011104c0c401d03250030303203051540c2e00e40358120903403100c40305d0b500340e136040d000500394070740101c00000f244041c2e072039420b011751300901008a0041403201407001c0d84403480a102c0c9022613081102c1c012006840400440c0302d01048810011404201404500810b000014188443d8100f040c1b610102d501303a1b80c08000300e00c4000d6503030050f4010500160300c2480050360f120f004c1c0c1c2c0480124404c0b901202c03070307400c03c410010715000400d070009001038002e8012504101e1400c80b182001d8403090000c1d20301890104080701c152011035401a06c11814405500d05026040c0a004803200900005001101c546c82e15010b1990140c820f0a00240b0312080030b85ca040d205076848407106800a05600404861a0110203c000d00c41010380d80050407a000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 100745674 1250 100744424 100744493
    0xc020a05070b0310090e100e16120c05010503070503070f030b0d050106180209090402060d0608070303020a021905130903030f15050a050901080d0302030a110301120b09010b0d 77
    0x1800a01c03401010a07a2858500e00013421200c555100500c00f41c20010010219036011414449a03074441500240c0100700422143c81c000700348030503840500700e6410105101604c4200440ad43e80502d0901000b2581e8000440b20391000700c50b05800250140085544180b00310851034159065140114462449000141010040a00442e8281c2d507c0e10200489103550b030310034030b051a88080c11804e04500501041d00e030a8010802803045a0008140d6040d200543c08100a440c090040300c0c0f07070a49a10700a903650110140c164490788400c60500032020080d4880c2c0c0a40d0780c041e00c82244000d10b0380e50040949440207003201410b0300c618010200b01168070030b0b4151070f600404201455480c103820702c0103400d0386801c01c6000c0c0007104018030401c13800242c040c3c8185c1c900d150046c0d0329562144050001c0000c0140c1a40b100000800000d5070f440c100000c1d90382a00494151083d9229510710600700c0d42c80041040c0c1202100c2c0185000c14224443c0310460780c0002150040014229070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 100746924 1250 100745674 100745683
    0xc0f021e070b0f0306010807020c03070b0f0c0703080307021911060a14030a090204180305071b0f060c0203060a050114060c0c030a030201020703140702010504030f1a0f0601020f0c0907030c020a05 86
    0xa00c01c43e44007021080000c1580e01420b0705800c500c060000c0c00c006100c0340c012030303181c83c2640555100844000381300e081c102c540c0f02c21a0440c0d1080420b407440c4640341c1c0342120590340305890201c01445168070515200e2a080c80010700c042e44801c0d40b4008a1405051102a030803c0c2c5c00c0c0700070301410711980110644840700945c80386101c03c0c0002074288040c0b0410046550b000d501d241303002001c220310000a60003408131615a504955044410b60415400c0c000d2040f894101c0034809414078000600903811060401c07000744214266001940c0307040050048407801d115003a0004107103454140075040a1004007038481c107840c1513440c0d407181e100102c0c0c070704004d15004900603940055240149503111802000701e01582c0c121a20300f51645d00001c02c10700a030700018184c0a010312085c010040b02c040e40c0000c005c1030004110161514454282104504813006800740c0a40f00220503001004500c0d0402c03844000c1c80e203100ca072074940003107000303006003e44031065116403919800403407010031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 100748174 1250 100746924 100746937
    0x102090a1d190b0a0f0f080f0d08090708070801060509010503010507020a02040b0102151801110301080a06110403020405180d05040b31090207030906030b030d0c0302010b120609010c0f021e070b 85
    0x41c2407031920300d0002460f80b0381c031b0190302c0805560840204090b55500200b518a10031500f442c01e0381d0151a414043c0e401c4c1b14041c0c5c0100383e0b0f8896032000081e405030642101e0308482d8210781d0124180e03a40c80a25007a0b03941207131054010303000150020014a0554010030b00702d0010300c100d1340c441403041c0d4035290024050b622629007050085800c400380c502400b034140070f0301042e0b150038115454424400e5542e02070310001005d03191600d80780000384900320150f0b401960010814445401d082c0340444040b008800b60704413034001c68081070800760203002140d04464085140c0380c07a105c101e014000c40310b01d03255262a40f54400303030407072601680c034001400043d051881d40160f84820921303024042d4845a4400820f15052842c0c1107501d99000c44d071811013807174600342184449240d00d07040f40141401c0165540c000750100720b210310013800280c481c0c42480c00100070440b4800e1090300361480944540018010384c400c0d880303480301f481c080c02d0750301038040114201d40ba980d40366140705100d500700c603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 100749424 1250 100748174 100748189
    0x180f042103021b01092315010909031e05040b0306031005040311010f06030305041203021203010f1805040b0402060a0c02060f0909100317090a080f0102090a1d190b0a 73
    0x400c1c05102c00c402c5040028444049000801c01d0841700d5586160005884500b041880702c40c60f0192101c1e2014099000a41a6040340d01400e6031100c043c030005201a010680000e54010307c44403006180c1c2407540c070403d400f41c0b1003e041030700d44110419240c4c80207003002d8040c041c5200d5400c0821050241c2c41c0628880c0d125900e0040314541c3d841d003114201e50440c0310035400c010082000c250410112800d5405110800c032040e141404c0c10b924156254956113201c4c08000b00004407a5104076000068407030080491030382040c11030300c4606464064402805d482d500c00c0100700149030a034002c14088601c1d041c440405c4540b0f400240b042d8008000c20b41041c1000685645146002d0078034951041e111700302261110700b9a10789071342c01000483c205240380c10016400e543c40d55580e04070070007068100c04a402101921000c81c0c040d400c042c80090242c509500046142e10520445842c1d0b2a8480340c0c030810780e1784402d1158070050b40f200070821a590f69491882040d15420307100005001e06 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 100750674 1250 100749424 100749427
    0xa03030206011d0402010e0f0402070c0303051903020309030d02070312090303060302040506031b01030c02010b09090f070e04080a0f120911010f03090c03020d03020304080a0606050906180f04210302 87
    0x140b4030740e4092010484488000c03c003011041000603a0441d4500c0f60000c0309a035515459041900810020301c1090005441028024000002c05030b00070000d001035560303c140000d26003070901003901a804241c0e08585c1d1030300184440f0082c0c481c01e40c0901140f50191601074200c10005520004490070141c0a400280d15241d090003542030501529411034401c0e801096012402d206145480c013456400706c1c10075868030b40c1c21402601c01d4000b000305101c0100000c02d50b09100c1401030f80c070051800c0c000754030301808900080307aa40e000300302441941c01c0240079203003030a0b07464115402c045c551a00f6040c002c5031442e91210f071000d40b1484030444d100344903808464280700000740501c2d10740b00302c1c1c004142c107046841c80010301d0324040d40c080b2a0305880140c403600c2c181c5416410341c010340d0080510703807044841318018410690010000c90b00155100f41c0b4a8417040c051180c0e40d01c58540342c80c84060a90081040b51000c04c0f10503030310600915841c17400c0a4486c11398054000542031a800081c1c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 100751924 1250 100750674 100750679
    0x5060306150f0309010c0c0809090907080f0a060b09090a0602031902030901200906090409060209030d02060411030c0a03110d05031c0f050f01030807030507080a0c12110303010b16020a0303020601 86
    0x348101d4075484814203090110b640b1f25900c010f0319125601d00c0a0082c071103a000306141d20b108200c0f020140006000359844130181c20401c03541c88000f45000d80340d9900384891007455080104405000d02c80b803802034a4012b1440d11540041d43c0b01400f01074601100103041c0e09009030610186014628034030001ca02c10002c0d1040580081901e5501d40c09030307a08000d0318034a03544180444030f2201007607801007240001402c008000740181540d5036054018240a0100c2c01d0340490501d1140d4400c50b05600014500014950381b0754904110340e4203d9000031060000c0348800d505021080c0703004102058146081d5904c1d42950007070300355024051079400300c03c40d80d18100d006410001d00322031000c01951a0124004000910621024114100004100c42414031480840b940030b90000510740d23541e00c51800c01017040f8410041941c40400c046070554038944600010f00060a1203001503045074203102124803241e0020354084051010000201c006072030711111175000b180203070080d204562 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 100753174 1250 100751924 100751941
    0x1050106050406110d0509011d0d060207020a09060302010c020906040e070f060f03090c030609031b0807060f0b0f121e0102040e010617130c0506070b09010e0106030c05060306150f03 80
    0x46440001a5031a01714001710031200c1c0d070003400e444040d030303007460b2032104900c00c3c45407180c0085101d0b540c650004c000c03129280606c20346800034146980b007030345c02c01d50b0981d4520003035084411a00000f40000c0300211458050706d0501700c080c0d00840010000200107102050f040d151440d103510241c49628204c030100003050f04100d038040b4401da2414103100c001c420b6911100f54400b90700000b400c0c0380d07641020340f051500c01d03002011845c002d201410401e200b1400c0a12142d0455441107a09a0900040c4400e019050150100d2180301074510510a04a4400c100f003040b5076104a240b10310030103d04080c0c07408511081c140c40d034111000142e40300e050000748040746105802500130301c40784040e46080b00b07868810507948106104002032400c0828035050030600d44a51085501442c00715000040c42144070750540505030120007049140c501c0300207039098803034910000d010089580001c026070704045000310391125000340300e1409650a80b07128823141c0c0040c1c44460510102204000c042c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 100754424 1250 100753174 100753187
    0x1415030c030c03030d111b0a060506041107110622091107080d02030c04090c02010b18090d030203041b08070806100e010b09040912020a0b060603010e06011b020301050106050406 78
    0x108000d6002d01030844100c40807075900c2c460020f90040d0580d0b258a403050108400c0180c0340c80c4410754036090001045402004d50b50480414190361451414021a000e032900c1d2194404160407103d149060a0f8140c9960f0780c0401c240c1c20075034225504200030780c42c00034000300b10356441000c402d0154070703182842046d40c211803484c0c500381244d00e0108949400301c2c03400015075030029010306001d6a60b50364801080224026a409503500c14204489521013503019002049000801d07500c407880411158142500301c2000c0c3d800d0205a00121194040c551194000b95400742c010b40c0740030044000c6a08021061846074001c9855400100c000d0181203024040150003000b00c2c80c11540c03070350520302542d80c0c3c0201849000d180c3d000014403041140c8035500441a620f0700035464501d00481c54001a4070340301107400498404030030b44c0000d080780c035000d803d580c147c40e0701502000441c1d407144d0064410500e03003051903080ca80c94022900040e9070901038540601459075030b171a1228909034014019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 100755674 1250 100754424 100754443
    0x3030418180302060606180d0602030711070614070303060e090a0203072301260a020301140114030402010f0c05010c09090b01050a02060f1306240b071e0204141503 72
    0x4100c807054041d004240c0c00030f401500440d08541c01661050703034641b411074210140c54042e03000f81007440031006002d00c5501840c0320f012981c43d02d49954810744190340e00c0d9940e5000c1c09020402624410602d81c513610080c1080038400d00380050040d48a0540440045003262001c0311940000701250840c201803000d01c00a003010088108401086400d142916614400580c10052100c440880024404054200e126118800c03a0150f00f0084451406580240510121a2842c007c1c41c0070a51084030100740310204001d4050440d01e665004441800514810703208004c003001401000c18402e214042000c0007d44030200018903080f0b01000359619038012078140001404201401900400c1840d48250404402c0c001541c070138003081c1c901450b109002e0440c2d482c0681d0382010205503d01964241f80035014144910ba072014044858810800c000b0400054004a6480c1560b10011b07101c0ca40d10040002c6406100c1010180445d00102c80c04000c180c8003101c1c0b541607003403c1c05983e13031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 100756924 1250 100755674 100755701
    0x6050603010b091c0209101707030b1b1308060105090c0711090601140d090c050301060320041e1e05070c080f090307030b0118061406090301060503030418 68
    0xd40d071411441241c80d01400c200705024500c2240343c0745100c00414a03207844554004c204201c54141266420004041801880ca001d81e007403200e20b0301040d00144000c2282d900104000c010f540300b80c0c00500c0200416000362100320240f1500507000c0c106402a00a400b03003034000c01e42c5615200410620700070280100f11201010040b14020a501c0c55020070b5160068400386e4054480700c00403a89552080e44445403542d000c103a20340c03601c6254102c1c10196000b40d900c08140e44d103800070103007200ca5a11004041400b82c080f1094402540b1039840000c4400800010b208090300d0300c1d0801014110100710859076076082200c0511200c00718080c9045100d22003001645030140c405000b801000c14003178402040884ca00079011154406c450301004c0182c00e43c3c21960ba2403405040b407442c02c1c042c5002e60090b8462032444002207105001c120f13601d20a01a0542d01d0030010f00005601c52860944c240d529104040f40948080004000901018441c1c0e288010f15140c45011548400300942 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 100758174 1250 100756924 100756927
    0xb0406031101030207020315010902070204050a1b08070c0803070f08280b040b040204141002010b1c050f010606050c0705010c2d060507020313050f15030910020705070801060506 78
    0x80410708003281140c0300300d8207082c010707580d050340d0001034604005000008100c100500000c60341030070b40d0b006020528802d81d4140942e4a0368014070068030817080640c0020301122004c2c0100900c01c0c2c00741500f1040c5401c0241c984c1d0b040d91a030100c183c1c4201c2d075020114480801402030145d010b030080785d00200f21024600401484070320311900098200d00381001c070b61241544440c1d650746a005400912009004550702c0c1d59442c0d0f180e00c9900e110b0030321840f804524020b4104e03240180502000d650700281030a054003d5400840d00940180d0b800f690144646051a120780200741b0424010f0304103a00d40b07603111200034466900d052103980002c5d0410503584000f600107a4800311010300b20041100b51038100300c450841810001c0d03903d4003e05100e00304000d02c58000e0b0040014440d0314450b0820f40801e9461b1818401c0d0a4401c94034281c0140c040c40c454003141400c280519004200c1c0001c0d90fa1007502a4905070681c1c110038400c3c0c8403500306c18070801401d0002d01c1820000c04003a40c485 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 100759424 1250 100758174 100758179
    0x28031b0614120103030807090506041e050109080c10030f050a0b030c040e061801181101030b060301050303180f04140f1e01090c05130603020c0f0c03032221060b0406 73
    0x2c2c94040113100c02400d014000c008140b440e805501c41303c001d02405000c4607180c42d580c0d4114103008152400c0d10616a000b100c010800754032495404007991070502c01400c0c80c030240b0b028880740b8000640210304265031035094003181e5101e809424040c94420b5004204000c044007003500b484540b8403502c0c4038916121034402d00b00700115210f0380c0450070b1020284158401c03000e171405000000e2202a810902002c210100107030004190f031402d401ba82c007000300c162110207101003848280100c0303905500134040c5020341c2c4040f00110100790005044030310681d04580203c1d00361484201d1009200c1d40401c100804034645d19540ca0340440e0789450140c03461a2400f0160748464107008440202e500c0f9500740c941a40a401114010500ca209003d00b11341c0c2c1e00c00c010000d4000c20120742c0320b40907100002c9049403000407861180745005000d549412140d500040c01c0d032110390300c0e240c04040100b00c00220b21185840d0446050904011141000700b00c0c54050b04952810360311520541ca441000e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 100760674 1250 100759424 100759447
    0x20702010327061a1f030501080102040b0304120c060c0c060b03060f1b04031b06030c090b0f0c07090e0604050d0f0c02060d0e0105091f06030228031b0614 68
    0x91144080e044940007400009041c2c0c241080034011302c6154104101010b240642242d41c0c141c1c0243c1d43c07035a502002184d0300c90306210300782e00c6288a1100805000d2002c6004149807161100e1406828184554004e03140d80e20081034826042c0140041405055001c1c20700801d8011b030010064100c1c083c2c0708602d0443d03810640322501800c503a8500003400c9030391803000196002c460107036410000d000da000c00c03076041900d042d49580c02003000190a250002c0c04030780c01110302c81c00b0340c1c01000595041102c0c040c081040c0e81c100d00b900404500c110400090f0802d11031244041244c000f201030b2000d881c10342849445e1080d43c034034000800c0359050b502e0b590150f108449000103030781240e2059960400001c00307006001c03042d40c224895441c1409003d800c400003e00c0c400001e0034076803418901c001c2000500704455075440f002c0d4114980c3c80d040c0c8901ca40c005511498218000c03020002c15840e5120410446401e01000c0c4112401003420300501d0f0300a0600302080b103542400600d403840d00c2c2a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 100761924 1250 100760674 100760741
    0x9010c0c0c03170c0a230a151512060903032a0810171006060f0507080a030e030301060c051203010311090604060503030f071202030c0d0c020607060905010207020103 73
    0x34004030360180301d0791088210070040b2000613003040116000442c4604010800c0d90030070725005071210000c425543c04800c040303800000281c2260706290302008108645001e046805038003140c0ba22039590200b0350300708902d00c081d1014055900003d4402c900d2402a04440c40c5441d1100070040c1c441c1401c100101a1a840610300a0307845c0003e0b031034403850030080c4a01001d42120a94004200b00758010300b100141c0e03000c0340085132400f8400c040e5910000d807001c01a2140302c42c00507000700102c0c40404c0342c4100416015065103400600074101158050442d0800e800c003c00184001c42c1131814880c00700801d2032070101c4c0da50001e203154076568443c804410b15400082c0644c00c4600040c05a603516400a00100030150a0ba5910710303a21402074546e90141c0c108443c014192200160844d100200b51400301003036000030f140110400c2c0381070304c0009420307100f02c2c0e211b40c08100b61700c00078031a030054500700361050001580b9009184005410740e02c07034241c0c03000d04000e6115060000343d170906 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 100763174 1250 100761924 100761929
    0xc08121204061a040207120f0305011421031204050f030406050306130608010219110703021011010b030d0e010f0311270301090503030403140702090c0903010b120609010c0c0c 77
    0x10340009410032100360030701d0f121604100069002e1310102c4c1d08800d1120020110080714680c0d034400404807003001c0d090382110002e000c4c10f6185840007030b40704020b0030810310740c02440030004280b0300c2c04080e0100c498a10340c000c0041000b01414038081c00f080010410440ca51704512201179402c00d410f20380d00070154040105118072410940050700303034486040d4000809000e075000299a01d501c0d8850030546403a6000306a40042ca030342c00070100000c808141c84081c1c2e41d008100011014080d9400c0302c40101103524003405550703e0400058607542001305a49501140e207500804440100c0090072503502450300f8401e00d401c128240e11b03091888400c481008403002003210080c04444e03800e003594240f80f119035805610b4283c08106000c800030141d8440c900c0781d0384c2d40f0585045da6501e0410390180c3c03c2c00a4021807c00c01007440c0b1403020010b030103074000c06000098403142801c00240c3c00010701c026100e40d5080602484140c0c0d000303015040041c145400d0252400f001a55111650704851 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 100764424 1250 100763174 100763183
    0xc06130204020c010e010506130b0d03030203060616030207030b01350304080601231e0103051b030708160306060e060f13151d0d060b0312070c08121204 67
    0x25811504641c0c0380d41c160760300c0d00c4408000f0019400415440d034000c140a6910600c2485212403580000f41603001d800001940608200200b99003950260040c0d00040c1050342d110703406200c40145040c001d10b01d0300b02580260f0050600d680b460411501001040c1c01200b204507001441c4013010f4100b0440341d0070112800701045005040350040d0342940101d41118406010307840000616588080d0b121046080d4a207100c404005640200300c20300d11001503a4001202500160400d58025070249510844420f2400100d000e190f10f0308a03207901c11202c0b24081480d03281030001800d8444680014802d031070408101460411001034680204c0701040c1d8411007000603141c041c200d03000241c40c00642c4030718403016072984554505904406003030303c002c00540c1c0a010004c0031249030341040030440000c0e040c4102c8444503103c1e10050080018210b41600c40d0782401c80c00780b00040020541c03907014140e2031001600f0f181c06036007000c008140d00c1300f90f10400d0200400024080c3c00294002d83e21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 100765674 1250 100764424 100764451
    0x50f0a0207110f0301060b04090203010f060c020307170705090703050702012409050a181208070e0a0e091c0f020601080303060108070f0c050109030306090c03060f150201140405160b0c06 82
    0xf88000901400403034101030b061100202c6c0028040c0840d8010b076058908035152507510769110324040f60b10350301001c4040c0d4035512410003008032980b80d0652014008101d41940c3d14940c44101250321a242518200300103940e0b9000c01a49590a01c04c8140041c80c0c0d00700140ba21640b000c85a103201000e000d9411815a41c2e0302080b000f00c2e065000ba1140030002c55031703016141c11410710a56036403040108001050b90381001aa00501c00e03c452a00018000c03c00c0c00c4040c00c107842084003900040c038580b150b10030702d0013483c542c81d42200703c0f80d00c82200b5503c000340d211912600904148040e401240c1aa106100f848440da80080c90503502c18040d2900ca2409001480100c8084425240c094515403900505105055143c0c1040c0c0c04e80317a442d4000d2242c825410f2080307040300c1003440340c0e10200d08880c20512412003040d114560f204e030144000b1039200804c201191480300207541c122041d030f0200307101c0400c040051442000400ea201c2c17207036050074032217203815464100c02042200030750325 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 100766924 1250 100765674 100765699
    0x10207090e0f160f0f0602030d0b010e04060311130605090619030f151b09140a03080d0e0c0904030813080f0c06010602120a020a120e13050f0a020711 66
    0x181008104a80400b2074100c414200c0d08100e180700e0240b00d4058220003101070440841c101842c40108003c80d14560b00441c42c0104254508004250031a1603c0c10020000900e0303505a030f07140101c4010394000c0400b58464003040041050500b6007609034683c1c2030501c50100680e949000c0600e034402c806075440c4002c5540c0d011410040880c0b170700001c1002c40c00310500c000f446224a040300106a401e1001c1160000480644110320740e803107d0180000d100c0324050240300c00d444150301c4040c802a00700340321651295201d0740e85030801740075801003a60303442d842110340d00d04000910f140c5000b0b846d0a00d050500d80c500138000c17500180000303113503418584c041040000002c2100e2090810ac6145910350550b070000c503440309401c0c03090f0310062054002c039600080e01d200841e00c0182c0d03950010022a4a565600114501c20910043c20300c02020b815000686034000d116801082e100c400007841d2a15a82c1e07480840d2005d028202514414459640002e903014802c0e242484100c481518001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 100768174 1250 100766924 100766951
    0xb0105070212120403060c08010e1302010f110307080c0709052a04030f030f0e01081311030f0d020304090513020f010c02040b04020a0e030f0f030a050c0a0b1617010501020709 77
    0x403e08042c3c501c1070758000400000b80886640407006001d800da603110001c0c0d0f650180c5003608070003a82c886005000364524000158000c0c689031050462506101c0c08a07800308141a040d40c002402c10307224500002002e0044910a00a10000d0045400100814100343c0342c0312410b129602c0341e111116122480343c26100c840001030781d0080d580106400059444c1d031038001d24900a540744100030412840790004e196000b800218810001051000314100554640c08081002199a55014001c01c400071804034418840c2e60b07101c3c80d00d07400844d511071401d510203044400082114018501e200000710043c0d40320707400d500a004091034400305140890000034002e0520150260384213100003484100306801c0f00054010a0044040d10803151000881940720480b0386900c514640007042441c540b1406500606148682041100d080d2182e6907a4102c41c52001d81d0000799003021441503106540e408051a00040c001000740500b41d450540080d46d1002c140c002ca9000c5a20388042070140f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 100769424 1250 100768174 100768183
    0x60a03090b04061407030506091611030a020f1606050d0504240c0906020102120a05180303010321030b03120d1814010b010503040b041b03050105070306080708010b0105070212 77
    0x69044441c11180307040c030340380850050940e207480a6800c004480014800f41c06803040d10b01c40c0720094954140c41e13868522014000056012010034040400c4401c040064108007501c4043c620790001c04a00400518043c50403148406020181ca11640e09101e9640c0c8403043d0f8170707290a014000306180d140c0b0300e00a64404481c95000540b04202542e0800141c0c0782d4109001400864940680c1d0329101da008038203030312580d0514032a4040c40000700300342d6050381d40081d0380f003200800058407814010b0000746c2580d00a0703205442510070785001d900e0700c0c001404030901e0104a41010020310786100d000c6900c80303200c43c2000007204004905104241d40700d41021034105140c0010041501d41c43c50b002d81c1342010780b08201c00384c3d8a440d28400300e42d400f51040300e003d039412148481e640e079100c1e51806803c41400a440051880c0303800000005142402001e0003158261400304406040c986a00d00c6e042055000c140c540c0e06001304800982d811200300c0d800280c056440e040c20600081005251 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 100770674 1250 100769424 100769441
    0x151e03060902181e0d23100614120a0b091204030311011404050316020316090b0f031b06070204110a0f0315060503060d0c03020a080a03020f01020a020606060a03 71
    0x11600008410743e100308030030b24298544800710f41140001000c0e0f400c903809144461022608140001c1c40c1001003a940f8028a0407603241c815000e80c4100d038400200e081004048142d5403c2c1d80707510701408500076004130501c2d00403040e112400d100070700215259540380000030207000081c2e41c4011400c03542d0203002c1c2d031103c505000d103d541d980d1382d20714004010400f0032401050651a004031844003071400d0900310300444d000002141800003060100d00001410380040b641880341600c218400c2c17070440109030003001d900f0400101050000c05000104521080f402d129410101401c10300410718443c03408001d03400e0b0741054807010705101140003444442106100180c01050b2450600d40c0444080e03052005540c080c0300001e4800c50700c014a00d2580659004607005000280450600a07030803c45a405001e0355241c032a6283c010882e19041c5801c923650b02d0f0080c0c1265014513404003c4900c005001200851400c848248025114030300074011510844000801c244040e2090300016034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 100771924 1250 100770674 100770689
    0x1101110703080a0908010509031305060d06050d060c020f1516020c0d08030907150815130c0203180a12020105030702070312030902011704020a03020105090d0b0c0c0601151e0306 78
    0x255008001c0c030107042e81e0921701c03801595600b4000003860a0f1801b005445500a440b10008011820682009580d40007021a109003a60754800024907548400b42d04c185240121000506e250030940000e0400c80b00340c15200311381c0d209045405c0d91904000101e940300e00041c44030959008241012410302000c0c0c1d006d194004c02c00341c0d002d410b010805004600031070320f0030211560310f03540d0061030013103c841806800200d140000002c0505d1040b00660b9080c14000304981074443c0691007013000c417640381524000680c0049415111514004417900c0304070f0381161030003010391800a40c485e40c103200800080c104000030000c944124004c10011003e1907100644020903000715800070020000c1540580c0001c04074101e001100c000b0762681030150740c01804524640b03082d03030015120741d8060100281c1100690b5006000f06111003c141d00420100c0311140d44d4801c8810390614191040e0400710b01400d000c072403124034980111200d1342961541200301d10041031201c040e0300416041c1d00440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 100773174 1250 100771924 100771927
    0x31512151006020c010804050d1209050a0c0e0705040506070f0501020715140106030c050a0c0804050d050a15020301050604120f17120a0c1d040b181012110111070308 73
    0x86a059840300310025100e00760f080710385030818403004540b08030b0141c501900c90b8210306441c40480344105194111120044008103003012240d03526454074481c1c0d0b07020b07900348280d00c4041c00a0040401d0b8250004414500305007401c1c2400001540d9110b07048004100804200305c0f8000c00c50300f901030b140240e070001c082d1505e030002c2040c428081c0c0f180f40c0000400d64201d0001064160080c03140300c0100d071a59588500b0942d5600c02910500d00c0c0180030b0712070910500000903580c0da20545805224481c5029003106100392034515071300500d00803005000341c010300050000741c8a01003034800b114009600110340398186e041c0030328400b400700c4001d0110903103509400c00080c540001400c59124009000f46540c5c1d4000080c0c080314000c0030b81c800081c5240c07102800100412861083c1480000c000040701d070343c1d42c8001448082c55090407407584500d80100003c02c240102c29400034182d420b40140c1560165403400c05c4400200d08182c148074814664590540c0104601000381d50b01c042c1c1306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 100774424 1250 100773174 100773181
    0x6060306021201080609010c0f0e0109081b090a0902030316110a0603060e06100e010c0303020c07170d02010207020f01051602090901050a06080708030910300c0503151215 75
    0x242c00c2c0024021a56540300750404074144210501c81e080c0c0804250f0384208902d40b0041c4200c0311001c041e90428100140d4520110700c64030b0600124a400c2480780404044900d02801d108022100603d00e095aa18080d003100c0541c0300807007111558200c50300f91300c5140c2d441746840b1505568280d0000c0d00904851000b01c0d00c6038240e80050152086100c464a44e65100300400004001888000000031a0240440101e500413005a07401501c682409418090140c20345882c00f0380703950240e40103c0d009642c802890f10140080c880ca000244029032500d481c036000310704030401000740581001400603000d10568000c964501c070941d8014000d10b62410070403d9507000c0c10060740d80720f90252412800140c10600080d2260803242c20f88061801d0041071420800380340c801c0c1c010359050090003001c02c0e41c2d080d15207650044110b507840e041c5480201000703c0600b00c0324904904418084c0400074480d07401c910400c0c054020b1802ca41c002d0440b0f1074102054105140c1030a003519541001003031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 100775674 1250 100774424 100774447
    0x503100b0a15031a040e0715020f0313030b0c130b0702120105090a060b0f010e06030402120f030304051002040b07060e2a040c05120414160e0f090309030c010c0606030602 75
    0x94081080304c180c0144008651000c010443e00c0801101a45503c0000c0c1080300c494900020192400d41e4016980b0000e0540021070859000d010000c140c400b6270303034042c406c002d00c03294119000b5990105032420700355100301c030411004042c010040c8150010801800315a503050881c45a00300c1100244458107000c81c0c02070351a0703481e4400702d03034150401c3c041030b2640c2442e000d400b18004050391815508070141c802d001240d44003820030b81e00b04011560420805108020f10300f425100800110795a00c0d184c18103074186400c11140d02300b600c0c01048200f091402c01b900756400715801c50f07130000f50144090117517803030828200b040034480c1038440a80c108448604115484854081e1000c2c004009112130403102c602c903542d403443c1403201e40008038020861300540710340d0a8420348102c4444038400303d50482c001c4c4059001225640e031240c204000c80140d02005034010110400450404082000094a8440304c0030418100070680088400f80b12042e0410f100554001208540d07440c020b901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 100776924 1250 100775674 100775681
    0x1120c0b071101121104050d06021303050d030e01410a1a121908070204061203020f0d02060a0908040509090c09101a0304020d0512040512070503100b0a1503 69
    0x50b050100d451802218103100f45405110b00d064a68942185020304000801c11419442d20b0140d4005a0030f110422803611072280e180b018500910060105000400380102914041c0039840ca560341030480341d15198400c1443c20b01d0304000311020300c1c4a00c8c15007514543c060f10761001e41d4004084641845062101940881c500400300005a181c1c1041c8100740031803c120407110f80120f41c440205d0b80b0f45816445410301ea114490f51281d8901100e94002405880b01a001390030700b043c06c80d0316001055010040d140c9801400009420000d81d5018040e45811000304507821980e1125049001c1200100866011740300003440205641030044840e5620011060014000e01240003c0303402c07185407060700c408503140207003114483c5047d040032941d25040503104903004103002c12044001181070112000640381c000304907895a180508007c04245031955401d1250040001400a030301e0100b116043d0062509002c2080690000419420351302a401010310405103480090b02c03950540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 100778174 1250 100776924 100776953
    0x70f110604061a0405010806060f15070303060e13020a032406030803060a061809021e030a050f0604060302060d1a15030f0a2307030f0603060203100603020306010801120c0b07 77
    0x3e01d80b4240b6000030f4240000c540c1d080c000e11705030f0313448900040c0151400941072017100317101a0040900e1a8660021501d03500b148008a01086d1182c106001c06070400300c0d12540003110300b81658502d65560003080702c10900d0b00015140c2150018070545462030840d00791141080101c04102140da0b03810142c070280c000396440f51040c44000340c00070b0183d1084650011040040400c2c01c0c09602d060305607c002e46c80840f400c00710381610300003003141201c101d001d148a6041284042a90310382040b21100c110f0004109511030341c80d02c88240056121041a117100901d1003030000b88c0100440342c0c2c088100710590900d588191494001d4a07450303004405140509035480c0e00465a49500b81d040c405d07580031485115003024050350000580b0000134125030410f5081c1000101d0403950418001034070044d4000b651203940000502400c040704070388510045c101842d045043d401c2510008002c80018410060101b0310f45c00c140d4240507240d44c4202c02041140005a561a5a45410b46c142c0c0c2844 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 100779424 1250 100778174 100778201
    0x5100510030911030f06010b030a060b0d0f0e1f050a0b030a080a0207060c080703180e07020a030207080303070804021003020904020d060e06030a03080c0a020309030a06060e0709030803070f11060406 87
    0x552281007804c0010b06410b28030703200360283c0007a17800c00b0b00d4140e0070340000b024055a5921078800003244a003210040092929000c0d000c541046202401e03030540e9022104e00d51030380d000041650a4032818508849810951318010035079803941403184d0042c040c20413910382e041c083c0707041c0c940800030500001e09401c074030307034003034500040d0b03200401e4034940540f40024024002c204919000288104403101d2a020301c100340c0e40c503d50b1107090181890404492403405030344590350750300170300d81c0400c85507000b0507030f10b0000e52461608a10050103944040c1009000b2040c1c10620707500180a9015243ca0300f0018001b15286c0c1c412489841c00b410140c81200000c1c0c2250010074030070309001c100e400c0780c10b41546441d005d549803076250211740d84c00174a000045010500444c180c0350340600031540502c4c05000080340a6041c801502e11046c0b010f005141400380300c260401c00a43c502042d00c0c5c1c482140e0501c1c0d19181c2440d40250340d0224220310511072801103804100c10401c4990101c6140d000c103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 100780674 1250 100779424 100779443
    0x506070f080f01050609090c07050d090612020405060d020a020f03030f04020a090c170a11030903030a05090601032001030b040216060b060c07090e0c060307020606090601051804051005100309 84
    0x303070518600b00d0303842800b6550300882c041003003032070504100500d2500644103080c094a040307035503201c2c0d6040420144040000850405081200c1907000700400d85d008148102140380c90f10b010001040352141c0040c04a6054020a440310254000c2c424402c0703c0c41c03043e090f00e80c0c0b0302e455094800c1202d0120b6080780f007244424804290058548039115a01c070a43c5c03110b0b259211103816001c0f604200400da00c2d0f43c140c0b10380c0003100484110000d540640e81c640011900d90904060b00c00644400030042240b07540714000401c089841d4000c00141408510000000c2e402006c0c0100c001c0e206440c3c0c056001400002c00304c08894132204110242c5004500410070a8001802c0200c640325030580001107521180051042c2c0a036607010380d460030f4452044036000442d0b030010500b20b030000c45c0c0306c1d40541c114404003d1b290a00c81086940102d003403070100d00d49584128007141c0501000101c1c0d02a96a890003e6900414501070390042c0c40f00030030030720880c2c0007030030001d0190002d00e00c211541100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 100781924 1250 100780674 100780681
    0x406020a03140703080a0902120a050c030d080417130e0103050309040f021305060c01090b071713080f0903010b060d2f03041e0605100e160203090d030c0506070f08 72
    0x80c944140c82a00b94584d580441c2600d1b03080c108006400200c0e0241c0c0d00c403106481c404002801000785105136803040025040d104201801c05051031031690441050200a01c20040020028101210b644110414282c0c881c1a0640040b07840c40c4544c20818809070014008414080000b02501141001312001e0007840c1e0301504802c02c0c1d000d40300c000c0c507011054000a102500c0c00700d020b4510741003e100005408503a80c2c03a00701e000c840581e20b0711301044004a42c180101c40000c2516071222441d0b85000c0074004594850031103104902c40c0c650850000710742000555029000480945802170143e1b0b140c49020020f003008120030b1030002445601d44906d20000b805010005484800003400142165038a84501090754944141c2c0d0342c04402d0070448900003100c5201e0725002e42001c01c1c0d2101da84c2e003401c03824081d0807405400a03124501e003041c003240c2075500004442080c1803d450b6041062001d1800f0b84010a03601001015405001c04200d00705900411900d88031035155100c1c0281e48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 100783174 1250 100781924 100781957
    0x8091509190510030207050a0213141612050601200618060606070b0709030602040902030f0f060d02040e070506031602011d06070309030e060a080106030b030705240408030406020a03 80
    0x120902c14036400001c3c10304a03441e214002e0b40502003507030045080e100303045c00790346c00075040c031180503208101e581d0340c0d51003002009400b060720f0390701200c81d40e64203107541d406050240004080d40588000c0e242c40b0800181164402c40484c03071306170440e2421420002c48001c5541e100d84040b00d00c040c901400490191680000090310341c015900903040d1450041141c603040b500e040005c0074001806070900001001500307501c0140b0003003411200042e20790405c01d0b0300603c08000646401c8484028070180300c45540c6406001e811340e541160002002d0710007030349450401105a012943c017400100410030b0014006000050440c2544e000b0491a030049041080070007031001407020b540d00502c002010f40d4000d50004100e00e00a0802c1800b00c0c03900f000081c0168031400c60b03000010800c81c0100443e40e014041c0e0348035040110301428040b030511010540c42000d0b03903120491010081c0e2101610302d40780044501038401740b01582d0380c0d00e03100c2c0c4019542e0410b200b0214000740b41000d410000070f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 100784424 1250 100783174 100783219
    0x2202180603010e19080a021c030b01090608070e0d0c1d0405011407051909090204120501050c0c03071707050105040c1403120d02090f0307121e0507050d08091509 71
    0x80e5600713001e00c01030084944a000c11600720064140562040d00c4040d14152050342c0c0b804820070300d039a80480d244a001000420329540c0350301c01c805102415050110454004100b403040303ca040d039011490100da801d00c41c551203201ea01c0b078000f0300c03a0004940004003547d02e0b15071046000304004e102e038100c409903200301c208040f00c8810020324140100f2616200e901d404500c40708107031620803515910b0b1038180040342e00c99800340d000201c5400280003000b2081c02020b60055114a245041060b42281d03552240300d0311000804481000c4003103030107002c2c0282910601c5400c20000c102c10f2500d49001418400c1a003c0e158413202e0541c4801d0151800044003002004009003603401c0c00b802c561408080c0d0007964100350320000141c2e400c140c5440c1000f94400520400b440108044454100710301c061011000240c110340844050001248000800307404580042d20050604201c034100744045d4001c0849642d84040d50344d07002000c248030400a01031409080701d041090100007a04103401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 100785674 1250 100784424 100784443
    0x10e33180607030207050a090603050c030f03040504150e15180610030e1e030a090b070507030305090a0f06050403020108070809060708070302310f0803032202180603010e 75
    0x104185490200c05003441c0c0d024090083c8a40103c8078000e8036003000558a04041d000720078480d82c0d0342c2007001400304c02c0003118844801580942441e980d4680302c146c4074030990140b50300a584070420030110b91004108100107216a4851412031308240340c90f00309020301c0107980d5110341203100461100390b20324404240524001403401250301d81c22082980900b004540c1c8000c28002c010105410003a030442d06824941d01c08081c503552490061b010740070f4551034200300c0c2c400005001c0400000d000085040a81c0d4040c1000c84d00c2d080322a00055066406400101030700e903140c02c0c0042c1e40c0c2d420501174420f5a20036240d501190b62648021035003c41d0840f0ae601c0e180e031002011030f04440c0500c1546410500ca4500945020900b880b400c1c200c181c1c1c183c01c07000380400741c0170100c21461060001009040c282d80f140c50b8051802030b016541c4d010203040e00884d42e500b100681c240009820304403c1c05039001e488203004101400da03080104504854040c042d50800001c4031001d0b4000c5642501d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 100786924 1250 100785674 100785697
    0x1051303020607091d0712020c1606090b120a02070804060f0f0e13090204020903150f0109021c0209060d090b240d0f05031e071a0f04030e010e33 64
    0x1c10701395917031a01d002c81d1009813000701800381c40e6400c800040b85600040503984081c000030301c3c00240316040f000a1381e140342d11100410441031000d00000c04072000315031108018120780003040d00d407900c0f000c000b8420008000c09015001400003012504101e1304045454070340c0741c11003022002d810664401e0709140c811980b105480700c908034624070340d44c0043d2807c0d001800043c1880b0071100481c0c43c1072213070742002c40190303a01000c002c8203048003041303a030142201c40e00c00d504000c0c10311000400d0446d402c00401003540c0204418060b61150000d448600600c071000344001001070500c00303076854050b035541d08040d0b07000c3e100300e01452103c0c60780400d0400c0a0040c2501202c540c13281252070707011090449243c002004079407240d4080302d61030040c004c540b00480b60f4408042c600007144000c20b408441c01c03140514200000305001211f460341c403a0701030400c00303000100400101d441c1542d007a4400c0e4420207120300e5415000c1d60b00750340f00c2041c0c2d12201d10a00032084c0751388000540546001c140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 100788174 1250 100786924 100786949
    0x1005090d0512031906080a1109090f07090209030c03010b061c0b1201060519050a0626090601080d09050303031b07140a21080601030c020f0105130302060709 69
    0x201428000c0c02810035900503000d481c4044102049481c0c42d52042c0d4200c084212842c0090719403400611510340100301d0070300100b1000610b0b82d540802c5c1203202c8076492003070b02c180001a0b2085014005500031954080c1500c003030586072803003031009400c8151040c1c002d2103680030303005441c141481195180c000003030415041c00c0c0050703803412000d01035054203181d454448003298060384a50705490a21a032032070011807040d0030302c0280b0481160902259100c280708180411442d2114a55282614002e28196050080746184000d4bd8203c0180881d031514144003000a05c8401288140c1650810030646040f2902c560303080344e4040d000d0080950540041000c560482d000185442c840c40e2040142428a15151100b08190084046505642d0070170650036003044000d80500612649007a1682c0007400c4200300101940c1004001e00e040c140d0b01c1110543e03143c000c0000281c44d90020000b80034500d0440f2007038440c0055410120054813903007022514050060640d0703010740d000313400c038070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 100789424 1250 100788174 100788187
    0x1d221a0c091f031509021e04030803040209130210091502071802090a031e02010806100c030309050c0d030c02043c1401060c0507050306010b090405061203040816051005 74
    0x2481d00c0078182d480380505135541e00d41d400000e4454070300c200915480d4001600c4490170060440046c45a0740c0c04481c94104110030b00019140400b41e903046501070310101c106550b2206078941e054142d1300d0217544501034032000c00195130700108030300130380702003c01d0440302c20380502003aa030340c02450280304482259024050003910345980604480c1c4001410408045e55944a00031241e50484040700c9898906030746009550704404400e170803c4081d070b48a49504d0341c0da2802811865032003001000c061312903d940041c0a0204030320380c080741e001800b85100e0402460054400c03011502d00724012070a18020036560010702e41d0b030700080b205600094001d400705010000c1d034410b500c425254010303a5180300340222011450014042c00040c2c8480c0b4900000741003007440d19900e58003c0d482a400760303005001d880300800989080d4202524081aa80c545600140121090030a012100c0c400460001149400003c0501d100014890388000198440c0d040c05240e5810b655801c0101d80d00700081c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 100790674 1250 100789424 100789459
    0x102090127090606020d0206010503030a0f21020a0e0102010b04020c060714040305010501090b03010b09060105160203120313031106040b0c071b03081c0203011d221a0c09 75
    0x4058002030400d403030401e900c9108210898070b8a40003000182e00030240c01d03222580400031240500310480040d41084183c130b0780100780c80101c0f810841001540008650920741000c1454100a860a42036440380310074203001389480080140c050040d800d03e642d0800608141c42240c000d40b503400054229075842040558036650f6032410310310510400c0000002046003886507170301a03c0c00000106114a05c2001c15080d0340d50380b14100c3c480c40c80802440380300d070380100c210340b904400e015407007003900b81e40e000203410000c0c408081c280d0448000b00300b26100400c240c0102d640c0d8425114015043c048020482e40c851080f0303401000c18540d00c0116101c038456a01034002540720b82c00030b4226501d075080c0d20b04841d49079401150265808158407020681b40301842c660081c806100310700319890644800a288203208046060103410004155808100a100f0a1822003500281c01c03084051038200c01021005003417803806507100303001c0348400c0d42200c02ca80c01410010510018040b04018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 100791924 1250 100790674 100790717
    0x120b040228030501091a070e090c040305031305120a030c0f0609050d02101a1f05090603010612060506040b090909070519150509010c1212110310050301020901 70
    0x500d94808000108400710001008203031018520882c008107842d452841c2440a074010002c0c0031142d50b22240c10050301d6a400b410403111070b030084410740070540345c0742d50300b1b941881030381c201420a00001450209c1244100000c2e0103c1d41c0030740f482c01c501510303401e1407510b4a8130590300030000741c800c80003040803d098090020010f4000c6400094501e030360380e03406141c141704240301c10140c0c110f5040241030603200c1c8918081c0c000c0b81102da0740c82076803010020b840c1d9504210f000a151101c1e4a503854901d20505c00d40d001080c02030030032560380d6156200a0040a000082c9550280c00c000020446050400c01d60f0100c41c06005200d0808540c03404005aa440c020b1420140e407191520000c0d29942c3c0c1145c031f00b409448680380c24881420b00b40700e10718154003243c2020034440100000440e5990000c600300d1400e82041e510803294031316071022540880d620a10035161410306494450a0326481c00940c014009038105051003a42c450615080c2d0141509090106030848101e0f02071316000356 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 100793174 1250 100791924 100791949
    0x20102040f0603020d060b0a0309021206150d0f050706050409060b04050a0612110d09030e09040f031103040f030c0602010c02010b1302070204020f0307090e100803070303020c010213140a120b0402 86
    0x117804259292222840c0b034080d00005101c40001e074032030088800b9410300d9a00c08030312030130f120054070061030700a201c1e01c045004007504502070102044480e052200009008210650290585100a50340c100c02005030304903005040c0d5546c5030850001d2021802800c03202224406840c484680b841d203941030b03640030a1000c000c0400741e01c80c40c5440c9400c440398014141107806900001e10894a42001003280c8001045207006000351020721010601c1d2605400005505103001e00b2003213003450710b6900310f00655012034004d1003228000b00405c1355008804040d204140e00070041420b102e003049099504400c030298000c040c9122140381c1c91219001040c8880c0054405443c2c000c4914540f00385e1340c022a030050006103516814030941c00f45000c0d02d504855814a02d42029080565540c1c40384107580c1e000303050581c0014100706801c401c0d0181c44441e041c200352942c0c03213669629040002c03c0c41e07548861180810503000f2070880c0013130000341e41040d08040380d60001eaa65a09200f41d540546 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 100794424 1250 100793174 100793197
    0x50a02010b030723060304020a12020a032111010c120c09080619050123010507140d02251d070207050a0f060f030902011e05090a1e0501020102040f060302 68
    0x10708040300540c504020030801014142e0407448250031a0310326000103650403207414400d04081087c803000d81d950032803500c20b070344014405e0719800110344001400c4034090303070004102007202c030206010700c0328038800d04040d000036848858589440061482c01ca039219102e10703010442c40034400c2860071003a4041210341c42142040f194103500d030b4070158507281045410104c01c0039021850040143e580c040d01e80144094a100c4c0711082c10000021000010240240e04026022035802c007403008080c0480020307148001900c0f500d07082290020749444030f80014070800c0704007211001e5040c100000240c11102d030942e1048601c00545400148184090000e80c1180300b84100882c040d55403c2e00c9000801011140c00c4035940b409401804401508012500703161500c0394010260f608109178106511019005c5000203400d08000c0d40c0c00c0c02042c02c56030304120a00404151340f44001806031104000e59202141103595400480c280d2045018a10a100448108104590103600a0040445c82e03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 100795674 1250 100794424 100794431
    0x1f0305010501080610030201231309090212160e0a0b060406170f060112021e0a11010606020c0d08130801020a020f06060a060203040e0c0d0903050a030b041505120f010218030613030807050a0201 85
    0x12812b0b2201d40b0f5068008041d21030b82e0340144400c5240c58000c3ea02c1105240014000e2103500f07a25003981c00724144109541d1000c0d8100040741a649942308082c5420014181511907403954001020407940c420000540c2c0c205401140c203010400072564440c040595651b08002c484411490107500a10180b5010b00d0928881400080415000d040b03280e400e0781e24000c2d0301e40c118841c1d9096070750310b074081010341d0013a101b0385080c5d45450100c201000d822401c41a69900040280d9600d00c15541c4100e1241d4404180c19032041d901003903400701e070b004110485940751261410405648920300c04e07000075a100304000c100d83c801c07110086a010342c5208605007004100702c0000d098810300d070400c138006400003030500380311038051080b581d0380311081c0e504104414a070480702491a980b409458810310b1000c20403050340a04010b8143c511451a00964031107021081c41400164800b03041846401014001500403061401104216800d40d50301c128986416034103940035401040f14100319500c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 100796924 1250 100795674 100795687
    0x405030105130506150303180111060a050a0606170610021c0507062d0e010204030204020d0f060509162f0717070b040308031f030501050108061003020123 68
    0x80a1240900ca58a929240007850009241090134490000c01c2109050f082410fa045592000002d0310a00c40710080c0011200c180c141c01681c8584030005d0151003803050300708202c007000c0e6030340003a8022008207400b0311070541c8594081c1c804c032841150311283c1700c028000040c06c80c541560310b014244142e0058070040c0303040e220003072407150b41c1d8031900d004281d001801c0020060b081c0f09017840c0c0b880850319810b0b1150144281c4011521500000180b075440c3c0c1810101c1007029030465000b991300900c215038540500a880e001b0b403203607a0724104401e1070b0000000d664101881001d205080c207800c1e503c401c20069506582c0800c00e540c1e011541d1044000102c0c030391455001c003c05210b00308008100861804156944142c0d1082000032030f600f2a0204101c928107000690303007680d501c0007a60b6140d0f9951491a9211100c2462011441620030300020a016065002c5e80c1a10011029a84155158030800c2c4180e103103031000034002008102030076404100388001315070082095034090725011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 100798174 1250 100796924 100796929
    0x1002070f020d0b060f0d08070201030905010605040f0f110304081e1e0d0c090f03112403101a0409050a1d16091b0c030512070f0813020f060f0405 64
    0x1054001100d0f050b410809220052600d440c503411210411a800742400085544840450080071802418183c49021a07020400203403c40f1000d0200500100260103002002c0c1c0b0182601d0004222410304d401b6004020f840114200ca00c40e43d0041c0c1120716000c04e0403c0400740a001c058000302e03044050084c4480719500e07030000ea200d15018100c0e0382c1c4031490441f070001140c00119000044c0003180508210101c2d40851540499402c4031225034461050307004a040150f900c42c0041c43c0346541e40d070030441100035001030350041d18007480c0a0701ea15201d80601d807001041d0b15090702419010f2104000d41a040c0d08007c0e1302400484010424440c540783c0c0d0410901c2c800d6002410360440780a01401c01014600b11008240d00c003018810100740d14840d109000c0b80100304410000c4200c0300d04240343c0250100c52501440d80281c074850300e003640004003a020a0700340c01d000545810f003c40e020765181c0c1f00c42072070550001d040101c01c85915042020590182010f90040741041c0070028459 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 100799424 1250 100798174 100798189
    0x1e02040203010b2502010807030f0e0a0b0403120c0c0b22080d0f020310090b030a08030114120307020a0e0703150305030a0212032202060c0d09090b0a03051002070f02 73
    0x742441c8040f240c50f1403952400c0c3e40b5000640c44801c80c01c440140c2c030030000d41c0c2c0c032100c0755800c0851400d00203240940242190701818466140348028492429040204601e0196052181d40030b55500c0307006100d100c40c0c0d20250741d40d2001d44d8000070b00c0c2d44441004140e8000300306402c11981028012000148101c0340868990700d04240d4120390042075032050000c460003421040c1a42c44021882d514003809681c1c1c3c48001070140d240000d9860f82c0e0070619032010050205200e070071010b460746075a500c00b9504960381ca43c40450380501c8008500d60044500041640c4440e98010003080c0280c2c100042c0720242200142420109a102c0c1d82404840f11030000d00c4d005580078074040c44da184800c080181c134040e00c1074142825124200200300c802c0e21440c035101d0645207003404c980107003601c900000700980504026481280500c1c1ca11035040b603000301c0104111004103a050040ba6448020400407440521014016030011010100750000350b50003010311a218540ea01201030143d004118070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 100800674 1250 100799424 100799429
    0x3040303201009021c0c17010e0a06020706140108031e130f09050601110d0c1a07020c120d050405010c0609080c030d0b06071104020a0c02041e1401050306041e0204020301 75
    0x51681d528074001941800c0f400d12803003240413006880d42c0085c0755a2003000c07003100d22600c00503d041c078440c441c0304d1303001b0b400454404281c5021203c00c0000360900d100290300400341111007a2400c0107142d1252100d0200c54100c5852002850a05929403091000e03902015040c5000030400c000c0c3c69500013210745000301501080f480448407030f00b8682881c0c11540050050f50600c04640400d805010700002c55540103e01c51070103102031400c42c40c2030300300c0d03120030018554500345500070007081640c0015020301c2004103e0704046500841081661100c80c48098900080e03000c1100307002d55400f506060902600c12100010800b403541c80e460303d5a040904e0b80f01c5d6a400c0003c20044083d1b403405826030103075044804916110981e5956100740c0c0f40d14031a50301850f0003090b200f0006000302e100c0c0c03070131580160043c4007005800011151200031924a0313003841c0c3c90080c1c00c601d001d4540103286d05952010b4007d280ca40c560761142d0244400c01c0d400c0004e20f40305604000c0c0140c84a0021b50300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 100801924 1250 100800674 100800703
    0x2060706060b22090e030f13050409080d050a0b01020c010f0215010b030f090f0c010c020d0233070b010302150d0f0b0a06050c0a020402030903070819080609090304030320 75
    0x14400a41e030101c2e100d00311a801403102900b405c07030322051600c000c1700319101105000d200306d54640502c0000c0c1c00d0045140c0c801c5034002d10b00350a01c801c1c048450000c0400490402c82002242c1c3c90b010010100c0c0e0b9500801ca0060b0302c0560518902d5004070182141c0c2602e07401203a41a01c05020b504407201c900360450b42c421800031041c4405038081c9412035030001020009005020200540d0742d50380e116030503500381005041c0c04d0080039900c403000c9404c0b5041c0c0140100b4049040300040030408080521035500140701b00010b80b4001c103440c0700f6621020350009111074641d203550200031020485500c9440466006c0000c1d42c0b60545038800c4512400c499000810454864410820741100a07407020060000c2003241c0310700d202d400b08584401c02e6045500680b00d440d84002140f850040c050010400c0d9000a80313100d410702000c80211842130280d84151707903951008240f2400c0c1c04142d40f101c05950080c0402c0c400a40505400c41c031840d848006803a0b175103400d00d4001e2518042d41d000c0d0380f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 100803174 1250 100801924 100801957
    0x62409010228030513090e0a021e130506120a03081f06121517060a0605040605030d0806131a090f010f0b070c0b031f0f0308030402060706060b 63
    0x41555806000c0d8803403048400c05440e0b074a0120300080c5580c400b102c00010b0410500045030448078940640304c0d03000d00500e610030410340c071800c41d009585051a04090348600948410880100c0c00d00f900242141ca000d44a900c0f03885510190401910020b002180d1000da0b0025a8103070a200300304047e40180259201c0e121410030210030703800c4c00d070244000b0000c068840c1d020700c544c42c0c02c880c1c600411031040c10001256503001308404c0c808032898001800e08005d041a0303180c40c90000a2b081d00803c24204100981d980e42c42c03c200888400b0300c2501d8054000402e0403c2203401424161752101000e8100c00c02508182510030444004460010482c000d40003203041501b855059554018200052007540c2c0d41070000e0881082c0480c41502c9880000003098010400f500e49034800034440001003603100d092110603e00c91805104508019032520300e0005501d64050b2540d00880780c1100c0c10902d1503c854003030100c240e02501b23050391296100c900008006c2803620040c9581e246611108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 100804424 1250 100803174 100803187
    0x909070e01082b020a0c090c020105090f190f06020706060603050f091902060408010608013806031f08010b0112060b030604020c0f01060603090308061008010b030624 73
    0x1000c4400d81030708101801d43c8840c182a030600c070559040340e1100d000f08090100c0a100600482c82c00d60400801014030442410010340c1e06075913040fa09106000790024001a60b41408455440d04031120b2924654800e40d510050b9040c4002d040400b94000e81d8200c40fa40c60a8031400c050b0b03405081c0403070f01281d654a081128541c1071040c19005040d8142c040c0b02804c2240c0c032070341d1724102454402100384056210008542d03e12040b900100001002840030300e90f2042114001d200c500d00440b102c0c5100c3d55200980e40000c40b02107800240840401c003440320010500009820042441240711580c5c80024580307500380d045d042c011b107038800000c60707a07802c0e0000044c043c00e4031241e800c0745642440e03401d10660007d01d0944c0d901c40c2e420348006032941440c4040ca454400e601d20042029480c100020440c1985500304500d01800703030f100e5644c0ca85886050042003a10191014001080c2c2d00c014441404424021038204000503d82002c01e5112490141303442c0480000105038180028030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 100805674 1250 100804424 100804439
    0x6030e0613231c030606030e070e07030b0d0f03020f0f060109020310090e0d0306080c090c0d022203021509010507060e0708160e07020a020d0f0519080a09090e07060503040c05090907 80
    0x80c480038120504e0306015008c6070350305160f520010390080c603c0e480050000600313058802d5101c00c5190794020302044c8079002505001030250420002a8010301030488044648900015103400646150008204e660700c1c0c84003600094101030310b03030f030705c1d078050742c0d5002800440354080c0101c281c14660103421314040a00d000b504813210f580c0000036a4200960035121503440d20000c5501207591010769990b240300b0252403000f80309020b94a1141c400184155014070702491001d01603d20079140c81050302e42c1040414100d0050102150000c0e0013042a0030005210760081e1400070b00281c101d5240c5911900d00b50300b84440601448200010000c1c01c1040801c4400400d400020900207000c25036820b401143c1c004a41030300180c5171850311200d9808010040001d249141c503044805c04000e2203926240e00903921404400000032000000420342400354801c1e610198041401084110314050b03095506800040050340e00800c00000080e5503104e40183c248504c0314800134140e0507080c42d04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 100806924 1250 100805674 100805681
    0x20703020318010f020a0201050f04030b010803120f060904111906030b041b0c03081803040603090b060a0b1909050a090207170901081306230106030e0613231c03 71
    0x941005040107044d080720781c010405030065074080c40c0140d62070f16883c0d080d1566102c0c95000400040001000040048001c4040c01100700b0b2054000304540340c00070701003090442030310281e03401840303000401c1c0020418800d5440c00c48010f000301030250000c1c1e000394141d8005502800109031030340240f4075145014807c4819164914541e186082560f0800070524000c10341c0c020300f80008580444c1403004890380c1c0e1082e2031948400c4903038440c0ca840005000e484500001c50303e600d00d0801007401441e0070050380e402d40e00d200f009d6606048040c4c07605540102880c10341d0040c040040342c00b0800d41c480723103603d10183c0342007400940d0310b000700d00e0482c036140f50702c5148a103000001d000c40b40c11a80d06c00314160b0081034120180048106c3d60030164014040140b48185007200f12419003981104011040d040300c04989003005482caa1312030107900e0f00c00448140304065000740310500050100b901110f80406140781d14480184400302031443c16803400006088a40e403011042c281c20b60502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 100808174 1250 100806924 100806967
    0xd1205010308090105030903121906050603071d0d02030601030b04051e07062d080402100e011718060118060b07050a0209040302010f151a0901090e060109090207030203 74
    0x10108469851612000e469029415549040000c0000410b21a82c0f0400554040f801c0c01610154a07040c140401000481d00b0541c00e4031290406d140094035107000350a480c498502501d0b0742490484154425071036011589205a005484241e51700168a04100e0503001e54443c0c501e44466080c94240149024001c1916400401201d0680c2d14145070104041048641908043ca01008031606006804a44018146040b001600712400d29940200c020380228021742e2400c081070302c549800c490215000190b1404107007041203c00705101c120800581c030a04444031026551148000075017402c80a91043e013040e2651201c0018413002c0c0d114000041c0303204956075240c11a0b07507464640741d82c04c0f4800a40b04d01204000901814000e410140f44200c0d40c42b02001050708001210380849528001c8001000c3d8a410924182440e0f2044888c501c80c142c40d0181513500e06141d0064454000b0620b90400550a00006a00c0386600103021124030030b40144d03441f000c49008078000e82c500712 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 100809424 1250 100808174 100808207
    0x12020403050f1b1c0609060f09061b052505070303051b0c1005030a0f0c170c0909040f05150c090f10080106030f1d01060f0e04050309010c060902040507020d 69
    0x41d07a40142e5036040e0042e5031169004e80c1e1080384e0400c608042c00101540c000251106080c441074100303d6403140c0c80442c1d0345200301000c0200007032102c80c14504400c4010060003080d01003010081c4550302104540c065000a0030101e0704410079a14142860311507441140410300210701ca8085040801080381c03014408002012100c818000280c03a800d03800701e540f401e0010000200d0031844154004070540d102c020424080622100c000801405128040d0650440a10b020a181103902c500316085008001d1160406845a450b000c07025044440d00300d0780340c8603820000b404076600140051140110a1005440311031b03440911044a081441c401d00c90b40104110041103604401c2150542c0e5003442e0018860b4562051403008090a540e007100c00c07054450a02080c00701500114182d0300620000320505540d0120646d81000a40303000789141c10500986038554414001e00d10101d01985002c14041c00940102e01140c0c1c00340c81d01401038120170340030880c1c1c1d60800c404040c0060710 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 100810674 1250 100809424 100809463
    0xc031e120117030d0603110a21020103020a020f1005010302041409060c03100b03091018030518061b0604110d0309120c03080a0216060306030b1612020403050f 70
    0x480e1400501805000c0e0032290300400380e1100b107501c010802e8554204541c141009410303201e0510455004c10350088a108501d100c5000c42c1d400840320908a8803000782c5196080c842d0325a0055000c0e400c605819811481081204640207200b004680060340c8000c0b030000f210b50460042c003080d5400c6220001521100d141409000c4000081030f0b076111000000883c0c40381c031081e61022a0341c1541d071140000e50000b00500502d400c000c11501017003c2002000c101104081c0068050704071640ca015012900c18081e000c00642420340349030444000030030703007803034a00c1414108402da404020b121031540e0081040108101a90042c031b03440301000c42c3c2c1019852020b9400405a103041d002d034101310703428030041204100ad1619040c0c051030b48403072031645030b0418400080d0341d0609248060301600c0d27200e0000a1143c0280300310b00a40750000503606055076001c030303080011300d01c07201c004040000800c0d00c41520051440944044d510840c054035102c5142c0326081e207401c001148605102c0304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 100811924 1250 100810674 100810687
    0xb01050a020a0201080c04090e0f0d0e03070611030409090f03030e03090a140a05030f0a030905010503040201080a020a020a0204020a030614040b0a0501120e0a030c030807090e0601050d020d020c031e 87
    0x1c0018140c0e180c1542403910034a00d07502c2800c007500c540266031002501900300400c0315601a07020507c00c09810012044400c182d442200c221910042009040c1d01500041000d21025218039000001c0380803070801c42c0e2420796a8080f8a080750030f1280e09039103403842d405200c3d0070154580100b0b03034103104110003181000d0040c4001030f4551003600c502112a400132090500c19105c00141c24000c100050543c0c01d504600310049031183d05804040340004c0b84290046a15802982070303034010b54069617646c01d165203000c00c0744001d6101e007843c5021340c401c0340b5540006980740d0009100c8148550b401080301460415800340408901407028441d900f09482503000c2d4480c0b800c0c00c000c841013403a145220040742e154200c0142a00d0140c00c00c5401508100c0d07040c103802c034010b002614441d544240c1c455940000c102c0f02100240580d045c80d50100006c0380702588502c01030031601c1c4982d02c0051070800f0750000344040740d0014500c2655074001084007905500c01814150258902c2e0481074139098 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 100813174 1250 100811924 100811927
    0x8040e130f0f2a14040603050304090b1008150f040914100b01020f0318011404030b0709060302030601020c040e03040e01080706030b0102120904050c1b0106230f060f07120306090b01050a 82
    0xc3c039000740d01e5030381d40f10340061841d56210b402400041d80c1240c19a42e8a68441200801a01c0070100a0340905940340210014034400c503003262280c0b44060701d00d41024410802c00c50200d41d150742c92a4081d481e05800400f04142034801c03581040c0300d4001b460000300c00350444080c0c80700011181d06641203d150161814004001c9400c0c0c80c11081e00c17071040e2a510700043c1d891184c454030b405040348020070301108010002c81c03070703600075501501c03144651980c0c1c080440591000703d40250061300103802145140c00c00d80c00ca00280404001520300742030b00c0e90350390010040300360b01c10701255002002c01c00c0801c1d0140f0400342544000c4c809060504691143d00c1d44c60f03c62841031500441c3d41e40c0001d284c03941041d0a98500583c010307001380d40414030304481c43c0070303142a014034402c2c1424102c81d21544644400340c00c40090010f4005620641e141082101917040305040031200c9008015282c0003a40c0e0321003401a0803030b19207000440314104802c0707800311940842442d05000007000040d8589 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 100814424 1250 100813174 100813253
    0x1e0607020d0903170f0318070515071202030903100609063203100e0a0201030b04020c0d0507060207060c0c140a030503011e0305031615060308040e130f0f 68
    0x80340c0100500b80680e1344182040070764464030a00c60711555002c401d0110a040484820415810403002c80303182503114010400c0c09600d02404002c20f000420000f4005042d15940303206c05102401580d0800040c2c1011a003031203100600442801c0d6204414825000148180c01c081c2c4074031200800b1000140e103031028a40000706880200c0c222600320103545c1d41c0e04020304010169001014000d003820303105141d03541c1d011070804901103410880744400506042c425542406800c0008012200a00d44159010741c0500c0b0240c50707180d0204030b0280800c081b80100e40e039541c159a40c04442060600700507484030360720f0a110031b890300151000c101280e03000d81624151031244051450080b00144032018a0b10140d100424500000c070b00a101e101c0c40122910301c0034000e40f10304400c810705101c3d903000c41e8a240001411940c0c00d20041c006800c00782c4841e980b040c502d403840340d08078046840b4501c491a400b0001c44006001c440414108005d4101030386d038000c00d00820000f040703a45558000803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 100815674 1250 100814424 100814429
    0xa090c0c0305220609030506062209020604030b0c070311030c030901030506011701030501020c0f070b071112030711011209020d12020a06110703020c010903050a02090a0605031e0607020d09 83
    0x2001804560140c100802c850684061080800090041a034444c0e0141c0018000d00c0282d465009040c0001e840b0300f4905c050b100402c448240802c0840c0c00002140020051000f0036600444240004400600c100410b64000d103001d69000747c5806003031800804c000c10603c0f4110880d0004d01c0310803d090f000000350740303c01000f4200400c031551468012030f5440e038503001010301c00b04080c0c00082401019802400701d070140000b5151120b0003901c480e980c0c0c0490340715a0082030020444200426175004414490710b800801020640a00900c1c40340b841c0c000d51303030550b00100f03010202c006d20f44c2c0141d5002d04510340c920051112014940008040351241c07200500481005000345010030b03c24004002a140d0140080101c004071610340925070304281411009807081ea0031b0652103600070300846e01260f5200d001800844010390030f0000c401c9001d0280014980c0300c03040840e065400b40310300c2d1280821441c03404031701940c0440c042c1c680040500340e8010764210144c0321010301e5104030040705 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 100816924 1250 100815674 100815677
    0x2150105090406090203010f0e0d050c0a0b06031c0305061e1807030b0a080606100801030818010905040f0902041407050a140706050103050303100e0f16030902040612020a090c0c03 79
    0x80c0e40d48600307042c005000380c130b800258103500c0c0c004203180562690b405290224072000407603807502407010041e941c5109000c16000d007a480b0202000020746146c0701564450ba01805a4914140c8c0100080c070036548a440380300465103030800c001c20b030309101200915032000172903100448113810011400100492420444095500e0001041c0a010390040020040058a15103869548138000c40e240c03a000d46c6d206218401c2544047c6030740e4401c003401410381c1d4100801c90f04d00303034180040790010411a42806d0500c00c241400042d240da0f14420312401c500000c0d000328070001c5a10400c41104d80340468111602024000d10819582c41415038a4441c010304103050441000000c102c11130249900052451341050004420030401001071344c09a5000e220070a14079883d203044080200341101c1c1448101141d034001003960f40580742c045641d01c420b0600060200703454003c94241c0d0901e400450004c4d1100340500118145045200000c000e0b60b08200120701074104020f00004042c0d402a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 100818174 1250 100816924 100816939
    0xc010b0103022503180803043f0302160b120604090b0106050a031d01021c0c020a111210020405030d0509060f0702060417060414162c100e010602150105 67
    0xc105401148010030500035210f0b140c2c5c605682d1440c080c1d580d031050095562100c10200c890b5a044a060304103003021004091038400000d019010620411419400b50214458541010202d0134060403020141c070450443d955203860540d8040c2101307801030161402645080541c0e408030350000381090640f115490f010340d441510b05001c4005d4040340d020021600390501004101d000150f004107050143c014101c40d01d0484018000100e40032000c140000d80c20803108400001d42c200e81d280e000d0303000106001d2404590862052500480c0780003a81c00c198006400d105901d0100403001c0124268a00b0501d0005005d002c2850f502400c0b000017600000461000210b555840503600030781080c090a0141c0d141c000f02c40d85c0c0e9a10107941c103550301801c0c0107843c102200003180494881980c1c42e0442034481c030b401c1c04850446c078816101d11000f00c00ca65003102c01d19111041c0303070207030010103481003002e418486802c04440041c2e0005081d90301c00405900300700342c468030072070445000f01d4014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100819424 1250 100818174 100818247
    0x304020d080a051b03070308010506030903030a18080d060611030f04050d020301060302060703020706030f0501031101080402040e0706020c180108100902030c0a06080a0509010b0f090612120c010b010302 89
    0x191030707600403076407200e643c075040c000003410740e00c40080981b04840c0a039561141907680c560034003800d84420384945406800800020f1412800d03900440160740c1f2036202c80b01c80c00c83c0b87e118000c107604141c0301d4607a255100e00701001a19404481160665002406545082608080d25126110b24860103000382540d49804096603000c4d80500015900074140950710116803030029110090780c091107010a00e081820807031002d0503c01c441c10b8a0b4001441c0c00104002001500c064000070000c036031040d19492003030742801c002c0c400c141c020029030300180a1016400b08115052140440107010790203203100412801c20001902c85420110090018521030680042824051501c250a40141d588000040c40c81e0380242114410007803000200129100c1c501d486003aa010320301460b500003002c00c4210a14600700d01c1c02074002d44c00601d4020a0000d01701ca20f414003003000020110b0080201340111014428022240b43c60400d207030461402c4135613481d820f003031000086494142085100d41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 100820674 1250 100819424 100819427
    0x20c041a01140f03040b010e010602010908070b280e01050f090a030503070c0b0f090d022d0a06050103030305090706020f0703170903060408090307080303190c0516030e150304020d080a 81
    0x2c83d4019116844a150359280904180003003000c01e1081c90f80ca076800a0000902a01c1807140651055120306400e203006956145c00300e502c0406031002d2501c602c5007640208800400e020f9400d249224a404141d0601081c10301d0f013101c20040c007000c0d0002204c0204001c00c04042010911240d16040c05501c0703484800040310049280d06000b070030801c2c3c0800740000349583c03d03480c910840050382222001c0114000407030303e030302d80204055510f850700100060424140c0445d00c1d80c6e1070b00981214055030040d11400d059039420ba205402095861040c40340442c1d09000b010050308007130008003198420f210100e5600c5100388005003420028a0a00040d0044801180c0d0000c070010300721074060919041105582d407060781014845e2003107400004080c0c1012040c0c0c0d10800c910351601400300f004c105003c018050854108041140030071a00000d4030055408001c510b0003135031404111075904040c07000e141c03960304220090b1003040c0200001a036641b540c0c83c41d80741d402095141c070b48540790070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 100821924 1250 100820674 100820677
    0x80a020f03040f0e0a09050c010e04020f0304060606110d090603020d0e06041505160813060204051c0203070902360a030302150601030908073e01020c041a0114 70
    0x589012034003000800081e1005a440883c0035200000003c41041d11580e507800c00300c45a42900514a8000d00c0b1058850340c01000410340d006400f0b0706c00751800c20699020143c0750f100700d03000c41d0201e07507801c1c09110b050350020503802c0ea5400c1400505810380398440c00307480c403440c0d0300c14002015000510f0549480042d04403064400e0103e003201c2050410b4075081041d0142ca200542e07809241000003514602103c40080c04042c858460490549070f81d11807441b420f41d44841034a08076000c000c001801e480303808074110700001e00743d15020000302c1c6204050a0480560186407a02d0060000d4040314441e0800503580c0c900d15010498003322003403689500b800140041c592150071040000240b60700402c2c1149030414059029440b5541c010040d402c4900702c03030014101550920104c0e00094070345030580ba4202d00c01880e02000ca0001d25a484070410041c290b010f0503c20084802c000d5804004201512401b1501030264486c0e00107a030a80840c0300341e40a0410400f80c080000d111a01c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 100823174 1250 100821924 100821943
    0x105030a0c03110f210112080c0f030c0303010306151802070215031303021513022b0c140108012d0503011104050a080c0303120603030c160801060e0f04080a02 70
    0x10b0609032074030401008025160010f1742041e03440c804400810070b8210184840c01e050b20107014108007840e80c070f03440d045d01c1c1e0b4205820b416528400d40c080e1004e107840c00c00281c40d003032041c1d500540c0c0e41d60640c6880c03002d44a052103c10b03600c01b90a00203203c1e82c1d101c654400528a42040700580300c494a0001030100c1c1d03403a44000c03c004d40004103000d800c0e9560012400040e000c0d400300e030641d0803690346020403800c045032908440105010f1240061030800c1c169079003403040340c3e141040c8032002a140d8220000012089480d9411903908010780c24188511000100090900c01415890860311030031900145075441644c0900b0684d8099202040c60040040c00019008200c0b80945403c126216406800380a105212517000010003d000240048640d90090081e5052081060030100c0040c1c2c082e01a07a4140010721001103003910420a003050701c60f401c625403046900e480d007040d00311400c47d04503c010044210400441350010b00c1810b40040c1e00c4040d9550343c0402c2401242829100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 100824424 1250 100823174 100823201
    0xa03050d18170a14090a060f12060803030f0a0b010206041104111201030b060a06020c010509210601150c020f090601020c0904120212030717061c1506050f0105030a0c03 74
    0x122240c41c0b80807030420207002e43d44032a4648070030405104200003164000c1c1003845030b01c01c0b007103034050141e54802da03c145440d00c07031802c103d16003e400c0301d0341001340d44550300b14040310380c004000c1240c15120540d0080e0440311032081041210a100c0c0002e4480340001d00c090300780100e010480213591555800361480301e0b103078490903456411201014000640c00c1c44165051200c01c00854070724901780707040ca801c82c2e015800a1010248203401500c0d150410350b030940c1d100c048403560700080aa4891788a051041d100c000d011190304200045502d9003640d41e0020070046081c2e144e1005071104411040350364000c9501a006a0f034020041340303004d50000e0280c2d0030500a4090004000c0c111500b01103a5405d030b000d4400e4585182c0c514803603408101d506900150041c1e003c2c0c001c014602070040e030030a1002d050540c605101c1c2d1380124641b6000030046030854040c4242564040ba10b2264001611089405000c800b40c001e000a240340405840e04049585d15000c04890034001d5000c80324480c1407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 100825674 1250 100824424 100824443
    0x70f142407030c020d2d090302030d020d091206061d04060c020705010512040503042103030507050a0e04090201030e0115080c030601062309030706051804050907060c1104050f16020a03050d18 84
    0x106c1c0004002405500c4228040e10410706103048184c000b003400c0c08100b0540d503802448510701541464556944081a00d01651303072400071038080308003801c1807044160640003480b282094504a405c440030344400c41c003150845e003030038004ca03a40401241c110ba10040e403120056200c0e030403c07078150700c1203a0216401100e1481035520000c0a0301c0d10041b038a0082e1002c0000b603480800a89240c1b08000e4440c0000301089440e0300c1c10b00c3c180c1d00403115031340185400038910304445000390840340340c100780e9a0032100f050f8081204e600d04019045042c58168054609940340c0b00e0040d0809094400c41496180d40c00d0500e9050710b0181d0a880c0741400040440d10030315650f01001c2c2690740030030800b000c02074415000c1a15400e01d401540e00a043c00d0000303200d0351b40f5180046450003103425045590861040100c1c9996807213005250280c40d84004913055070424001c000181e48d80b078144481550130036800840482d40200685060340709070400442d00b016118904c44080b814240300400ca80700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 100826924 1250 100825674 100825757
    0x260609340207050112020a020706030e0f0105010f090b0303090f09070212040306060f0b03060a0302150d1b0201061706040f0804030b0a05070e06040b070f142407030c020d 75
    0x10700040490485900381c80c0d4590350a00d070800030302030b40304054038003000d64081241003018500c00d9000710000501c0d50103561403030188001007425a0030130f92014040d0b546424050042140c0380c4a00782d03198404600a40c5803040400200e000c0041c0a6201031182c8000d1000685060082c0550351b940d82141d111a1380d2543c580c54200d0040c010f9018842c1c0b8100d03400c1010030881c81000440340500f0009003103840140c5160308210008090700560844040c040c08105103a8141d806026400c00380c43c0e000c41e90313507052428001d084611079032081e040c1031464410249000d00200b0002c0d04141c015120342a0840f0904151b00fa920441e880100054620000c1103134109280c1c0c0080e001c1c00440c0c0c0da82c00d10342d00040c00c02503940a18014110044000c201540000d03040203440040303580315941401c990f10741f8a0070507007041d520780c1d1405c45c0e4a101d1852a601a441390811507030061507070404000070308810030000d603035810300e0b0542d000703121100c10601e0341080540004411220441c00c07420342d010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 100828174 1250 100826924 100826927
    0x20c07170303090d0c0b2410030906050709060503010b0c0307080307020102130608010b120603010b18041a0c090105090d0203010e250b120406060e010626060934 71
    0x380101c1e000060b07805049003502004d4172039201c122220350450782072007464940705490300c0c0d5100f2039006002e19100b420b4140c1510786030b81c00b9070b0003440070944000031202d0302402d103041500e0f0024210801c011a042c07040c0143d51b08041034038192000c0b41d640716103901d40da10707000e80b540c821680c028102ccd020110800108941c150000d2001c0d108502d11a214a5904d0f0fa0a0780c0180b001c1c05240ea941c001031202910107405805100e03030002c0d00078008141e0000a401103070b207500e1501250000780455070104000e020f501c0104601c4608141782c0300b00b06191506603081c2a001d03500c045410800e00041410190f929402120907183e0020f00070813103203246044680c0d42e9001e84214000c030905140c18030a80384144001c0c00700329807908004514245d4040c1403e0401040200708884455680b400840d03801c403541d903111b01170407164940c2d5400141d04001210607007170b40300c0e2442c3c01071245d008202654a81c0d24284d500b1105540b40c0c9081d10550326040e0090b902e00b105080000030800e240c1b02a0103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 100829424 1250 100828174 100828177
    0x70807061a031006150e0d0c03050d080702030f0d05090c0405011e1a0405010e0a0b040b090f031f050a0b060d2406141605030a021b031906020c071703 66
    0x11103048044407654608100ca183c140d401c0e51003000320080b144901175003080c0c041c070708401480c00000c1481e080400d10741ea802c8028206500152001da00c02da0341352043c59045480700b030300114240001c504105642401a045101c0c0c62000100142c686001c103003404402c209401d81044000d100744040d40c4c45418941000c03140b070040b040340900e04500010440300e544c0030703600001500c40c0d5039031500b030800005403501c0c4025100e2035000f00041e80c00044039402c10010b40090b242c8112415641d08903031082000702c04c08402c070180310b50041605040100300a0032400100d84000b00040b0b8035a550280d00d50040c480000c0c042e404c07160004120517100d01c15800888045124605008401e0116030030360b480910394060040813898401070410032603188006400c040541150210300014503a440e142550420181407000d64014032540c007913100008a40243c80c0305c29001022403ea42070a1400d081039030100150507581d0000d507005a410b07042c020300010384424140384044030540310341c1584c1c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 100830674 1250 100829424 100829471
    0x91a0102011506080c0f0903100507143109060b030a050f0610030b0d0f0f031e0219020a090c050403030306090b010903020405060f0312090a0801020c030f07080706 72
    0x5510b070000030300e103502c4840d00d0b00b41554003c3d603d0150941d01c0d84990300d06075005007048560802d052288802c00c3c0d904202450000b541d40f0700114050a040002600c1903c4009107030002c1c00701440400791803844142d489100a001d03241d5100002d03548004500c191886800820076142001c4011400a402030019402202e004404001941d101c22044442002c10340c0c5843c0e0120358120380c000032910036000038101d004000c1180d140d030849590307400c4407120304181c1100c1c42615200d03c01c0915401c0144c43c588041c0303c1c99114030b04061a01c0094442c003600a018080d03a024a820700c0654a40340d242c0d03070117409000c0701042491260321019200b50864802200043c2c109200412a507000c0c1c00b03505511750040e12080b01c05401c5a00704405000000d2034190003e020f00c8917030000c0d071703030070044902d40215550034913030b441c401082485941c2c0c1303090300224020b0780104400c9a9120000084402e60240002c5850301d8401e14604000144603450011345098100161002001c5c01581480c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 100831924 1250 100830674 100830677
    0x6180207030e0402030717040305040f030b150306070203092e0905090c09060409020901030e0105010609140f03150702070e0c09040c03050906010501050306040e1203060108011d040318091a01 84
    0x2c182190104010603807000700c0300c80700011480401a008104410100c58200381b01741072003828543c40d8010002828280c0c0e0045d180c010703294084c0003442034000d400501003501034003d03000c54a0600ca019560b4400d081e242402007000002c2c118082e000107403c0c0d415800084404107489416000c010400003548c01400e1040c5442c901141601c40c540d401c5407003100019020506140c500780405009400401000741413649480100c003c0308021702c1000c2c003034004d0340c0740c021059043c904d80e004d842c001c484401d40a141000c03070010b81960005441710344409040c40c407074030540e2025022814000c030781c1d001281c0d0316030707030824040340300814070240c080c0c0f49068800300b204800a02040381500d00179200c00c06d49400480062000f0b5100d5002942e00880240001c0b60982c1202811441c0c800c00200180007401e021091045030b40c1e11014880c01041108403e8003107041102c0e9410701842c0180c4000c0c10720424200080640048040c940000c01103443c007044400100c15544041030b00c10800c190 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 100833174 1250 100831924 100831937
    0x11e030e150906092407050706020c01062d030807080c0601170c0d1e08090a06090509090a05030a03090516030506090d090807051203090402030106050c0609010903050306090a0618020703 82
    0x1071300c01c4800120fa07402e407121440c05054020410340603c0810101400001c100041041602d0118000e0300041c50681c004100004000e0315007132000814550b421307010541071840600444c45204040c00c00c00c1a00e410418590752100c0510b40a510b911034000346a2060080100004900d4140f91500e0b4000909000b55814200d0740b03020030a42c5004184000d04080e84c0c8500340020303c0c640e41c4070714017503446451342c0b51a107050080000e8050065074840d400045629100344228245061300582080e41c00005280c60f022958480d81c50b80603102025081542c0c800140e001c1c0b20040106420303c2401c40c2403000c41e151242031035512008119242c3c070440c81008a81d4210512803030004040340c004102802c9481d06000410400689030b40700d1403043d20081c00181d980340c1c1c45200a60080c80b05071201981da8080719801d90038501d0003044c130034442e403400c0d0302030020076000030489510040483e0080e107a035555904820090010360406501e24000b601c040440c8240c46d03008080b010300944560 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 100834424 1250 100833174 100833181
    0x306110301080f031303030f172e0303050403080310090606030e010e0708190510050115021014060f040905060a0518160603020f0f161103010b011e030e150906 70
    0x1180d1301e00c910141621046030009081010a10038130700f14001803998070309424400b000500c0d40180301029100321040100c00f92044060f00560b170010341113a01022600441a4030355100503116003d180f00103006140f0000c001a0107040c3d4601080151070103400c200101900c524004009142c640f240048540c41c2c03d040380076408002920404480d80800217000e00718100081010411941600b1101ca00c1480131003484902107005550103070641e400035100307185104c0c0e0003e00e000050442c080389c81d4a00400094518012210307590f00a500395950340f0240701245c041001401641c601070000c1c05600180322108206030031440c00341520140b142aa40003016039291100c0001c070700307114011880386c2d040001d24040c2d005410440c0c080c0341c256003404400c4130010002e0384000303030000c5002d6102c80c02904100610071040d04420054008100700010100003800740003850144962400c1162710b50711642d031180e08a54482c0310203805070b0b14604171655070520101d0060720102842d00841000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 100835674 1250 100834424 100834453
    0x1223031303032309150c0c1c0302160e0f04020a15030507110c010e0904050102040302190602100605060304020111120703110705090903030c030403020106030c0b1305010504051e030106030611030108 87
    0x7030b104841002445d00040e08402882c010b0241e000c2c080c080e6841c050714001c40803694400055010301e400200045034110068a4000d0802030380d00f03812070b0046c001c0d00b014405105141405030b80711141c0041144c0f1600c4500015803010303950391180e0500c20714071034040e1030303503034550071003400b50541e500c0340307083ea02d0010740361f6459254003400701f0300046400603054807920704180f66035041030060700014a400d843c6d030080703a8100c03d41d580078098000c94400800000394108101103401485240401006003440300140092001400103410000503100003042c154080c000400003640d0300d40e00c0ca41d41e00951402400f4211040c40001c92402241d400140398100900541d00ca141c14501031032a590396100d0001d001e80006d002902151759659001c030000740d905c0000740c090901e0304d02c0d06407258141281910744d002550882410400d09000821068441c03040510611101000c03241034001c5940109006085941c405415141481810383c0d01840320002503050324512010341750001c038500f03039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 100836924 1250 100835674 100835677
    0xc0807031a0f0a0803030705040e06011d0d0201020f19020406080606010212070602070203060406140601020a020306011a122e05060702060304031e0f02010612230313030323 76
    0x228a81c0003959000211051900031901c0a49480c02841159001e4941d0300f4240f81d0b80040340c41e400400c1d80002c0500003201607104081c0d00280074a4450b101715068292a030039a503012002c94007070401e948411085a00030321500101e05082c90840d800051a0701c0c40b04055284001c050740a50720703080c0c001c201c03041c0c042101846008103070020140f403800f0014520803940a60400d0f81c1a950901405006903000d1080038000c40c0102404100d1844100b0b000d20b11120203801c41d4103552102c011540103840120f00541110821414603074088407056104915104803440c6404038441401040b507980300480c8080e10f00002c405154078800e004149480e4944442d018080c0c1c0104184440001454048001d40c0d21600c41d241a20114048a0300240160207010220000c20500300c25031444c540d091041c01d00034691440c000502d401c003522030081642001c2d0300c0c4000c80020000c1c0303084000c4108100c90426012802c521b684030390b2420011b20150203410b05594071807018800c00180b400e400f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 100838174 1250 100836924 100836941
    0x5070f06200705120304050703050709050708090c100f2d02010c021501120f0602030f1b04140907020c0904120e0103020c19030216081507020d0915020705060d0c080703 74
    0x40504c19900038001e00b00d6080103200b04c407548140480400020303000d11064008140c2e500c404540d40c2400351026181c07140003000f0030803d0340142c0c05150340740e0f16002a0110b4051038185611404284141111001d15032144d2550044000e081103050554a1040fa00003030f4190703000b084441a454401c98451941d14403920540c0c0c1020300611844010b80c040704425441550188a20340142d038848042e600102c41004054542004114a800200b00d0b540c21440d440c2904c10304d02070400d50b100c1c8000201003a158080d032140c00000d0040e500800c41d00d040d440008100d9107243c68030f031510140140502c0908400030f03030440040707611940203009641020b540300300030f400000c56049040b17100d000b02540a400714881e81c030a850082034502a91005040c211000d01907006c0f0a06442c0c81c1c50501500c600c003150b010030031001040b0b61008410064541e58a01700032000940c1e1030403454045079410040e072200000036815680d1003103a0000410590130f40310001c45558a0a06804451901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 100839424 1250 100838174 100838183
    0x40b19030f0611040e04030819060605030703060b0a1d060918071121072d030201050f04080915190905011b02130e0708100519060f03080a05070f062007 67
    0x11008031b00000e0051020a500691180341103400103040b00c40303074080ea540c6502c0f400200e9800014440b1240d45805200040c12191076868582580b5420042c07040140401044140000740d614027100d5407a44100c0b407401200070840d240418012845020009083e1010700110340c595110764824403006c030309107000300d100c04c0070180081030340c0641c0d48003039201031000c0780c0c0301d0b1070712200d07410606103c0d4140d096001b400340407029000301032030040c0c00c40c0c90160200281c4510a41000001107010080b5500300d001a6500c0050310400d01004141d4041c00c04115080d07007141040f100d2080e813000003e022190241c1e0782c400c1001d05035107040581001e5010103500b041c450f9007031501680450b048090302070340c90002c80c2d00d140e5580008a0600704a22880382800c1e441d5414400b5500c481009180c0c240701c0074a0402c2094601308602400c01c40a2000401c1c0070301c00f00d02540d105010b6010b40303071303202d8010b0310403607044040e450701000914030508101c5604482c3d14841350a01000c1081e1100345910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 100840674 1250 100839424 100839449
    0x10c0914010219031106010b130b0c03160807050321070c050d0503060102070e100602010b010f0c0b0402011403041208010801020a080f04020319030905040524040b19030f061104 78
    0x8900612520042204254180000b0003e005017070308080000c00d000b8075451880d1901e44107040301c0344580340b5090303203d82c1844d0020300075003120043c040704403001c100407850003100d0852145130100841c0696800179000c1e00021408425441007002050160078400c25040341542e2000410303100c032005100050901d6102c502060031b028000c00007076070044014011540642e40e948190101898200d5075154880c006000070004036409000f485286202403d02c4c86059a50581c01400420481000f40c50000444081010b590207550545c081e41912204a40e03030b460b00e820400403500c607000d040c1000651000000403507810610035516810b400e561aa003c83c2c5689481440b4450090030a99050203402450718600001c0d4400c0458641700b0349428440510381420031007100c900511600d030352600c00404140240015408030041031080f240002d860b01800003207940c0c4119141d0f114031000c0050404414401d0501d081c6002a11440301031003e14403414058006000e14452808070000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 100841924 1250 100840674 100840693
    0x302030714010209040905100606030b0105030c07060f0501080c031203010f1205010f02070f05070803040303092312030c070902040302090c03090c1801050f0d2003010b0d05010c09140102 82
    0x7800040c122210740d9000003608206040c00003404940550308200c805600c81940610b01103054007030080202a5418100084020342d000a0043d100042001031b100c0400144001044510b50041c04180c41825041080c0d68440c0e2860b5039408803004003510900c02c0750702d0305079010401070440e41603174181c0781c010424910f0418102d10304441d00c0c030300302e620755211034550518036101d10141002c00c0c000ca40850000d205820700301e0074240c03d03401c10010343d04200000d00100350080c20b46000c03039000710001c107100d0b1051000c800070000000381e040d030700c1011000c00d6103035414000f024018a070408402c0d80d45107030703036411400304a1083d480000d40002c080300000f68200b68007005903502c00c030300b00142d07401528003c0001e070001e1501e084120f1241304140040c0304034180071004070141d4005540070b0041c084c0d2070311524205264004640340103040011103800b5610290410a04988060182c5103000078034500039010b440019640d4000074110b0368001440c18401001211035401a0041c245211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 100843174 1250 100841924 100841933
    0x50a0b070c0806040f1403160818030d030e010b060301030c0b0f04090e0303070e010f021b030c120312060109030b0a090204180f02280e060118090204080c09010303020307 75
    0x411002003078400840400340051026001d00403184070300d10a0030750f0900403542e8500540d800e2000f0b089081154410301c0340040342e0359142407405245800401c0141c40710040d00d1710600c0c0d6038158825136014003500170b400d40080d41603006851000401d40003409052800340a00c01140003d110140c14208280020403022040100074484040d10f6568070b80703001e0301c0b14051804d5910080c8450030a9100008200095910042d4a200b02c0001d2a2100c2240c04000000b580e0303100c180c0c041c81c40e084801070702c40b80c00d030b5080000c00d20440300070308082100002050321030340725040040c130040c0c10203041e400038a40758403680d9100181c1e03900940c100502e451f0100c04000038441a1012030300680d942d480b00c080025000108100c0c1c1e8400d004110344146140305021090801c004070a034805144040c110004c0c4141e65a0702c180d84084105002655136070004940c00c1a603014000b80a003c4501c0204d04016036400400030740d28a2b00403079088100d51000c1c01038802d024480035005800c10b100304070005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 100844424 1250 100843174 100843177
    0x4050406060812090103060504020702130f060812070506060f010c0b09070b1602190f031410020a0c0c0f06050f030a2703031b0509011407050d0f1107050a0b 69
    0x5004040c0052550346441c4a41d28061400e6030a0b08440404a100c030300540e498081c120191a0035982542008015408111032805480c02c00c06055220480c074542c15115a00c464014000c4070120340c01d0400d1810440341230fa120309425511401140005443c0342030840103c2030f0020706a40d031103100d030300585409180100203010b6901900649000040031000c0101a180c05251000d1541c420540361040211090403003041c0030035862600d00c2009100d088101080c01c5980010104a242003402d5000b410803801c42c1c0444d41245c40230034044400355110901000251040d10f10300e00d110703100c8194145040051051600107802000003904004041c4047c54100314408404186c80070014074001c910b40d03032401c4a8200c2c0d42d28803035110074154107000380140c6a400c000009025054814010140c0c41004911814081400030000d440c030402003c0b24900c68000065440e09610220024203060300010322400081d101454040080408590714040712001801f0345045883c051495415 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 100845674 1250 100844424 100844431
    0x60509270402131113081504150b030a0b010905090709090b01060e060705060705130906030206040506071401020706050f0718030b1306021317060f011208090301020a0e011d030c0405 80
    0x50744401d20302131405100701c050104400220b82c1c0e4079681d8203104a152901d2528010901c1c1a0414018880802d83d205040603440d421b00d0008210136001b500031078a0240f0b1000b000304003034039500002442d2081948160702609840c01511000756481d82c602060307aa640c83c020f40040419001041222702803d01c180c050000540398906103c0c19444150808608440b03c0c0d0114100044122140303522450390800340c03450000401806003190086049400f0364001c05004101c0010160309000724100042e000383c14110080d903a481d028504540500f10540d0030703000c203070310400c08129154050243c02c080400ca0f10300030f004492031621044444040030340801e004280f040e00008c0812880c0c00100b0041403585001300341685404a5078400e586076821603201078100f44e00744003511001c15100f90466a07600c1d01c0d00b100981c903060400440c8079409841c1e50640c400182e09501d00e801425444000f034007600c902c100c803070301c00500a5854a507600e5055060308a136038041035903d0164403a640 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 100846924 1250 100845674 100845709
    0x312040b03180a030e0301050c0f1207110304060504050a0f080c09063f01020a080c0304080904020a080618010f0b07050f010914060a0c0807030b040b0a060509270402 73
    0x7a401c000701e020b941000b1200034240e00203048410390340402d0409015154000c200b206d0703028982442c0401028441c061180d41119580c0d0310300101c1c0080d4492903a00c140c1030b00f40c3d025213513126941c034805000d50f4030601c80c0500490a172440050400c1e41030300e2050032100c620f809070407039030701c420100480c80314002c005584c04800321085400d00310900c0e8001c4042c07810f541c11410050102916640001c04078421819142e0041201c1001164000a840d4021000d10070031902c83e107a5290400007409909009a0058808102891900d42c4402c5c0b10703008680941d4a84140c07000c028509203210300c24005c202595078102c0080291405403001460000d008109650150a0303280d90a400c7d00c1c9002000c0e6509034004203410000041840141e802440c542800c1064008240010b04003c00040c004418150340d210304440c15200c41d04606a00540240102a2a6143c1c0303c060301540241111030702076100b014954819518400454030702c1404241e005c240343d5160f0342008250040c3c00740080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 100848174 1250 100846924 100846951
    0x26070308040f0602060105030606060a261006180303020d0c030e060a0c1203020405030d0f120e0601150216170f0109060c08150d060c020304050a030c05030c0312040b03 74
    0x8101100d01800c090300c80b10440c004200d1a020707000b80350400680200b842078200c02d05000d40d0350741d075204840f1041d01a051400143e81000511400c0818105418428ac0140002c0101154150b00c82c0c90568582e80c030341082d2000e50707100b0355504072660b00008026a011a03652105140a8004142141d1280c0b81030074402001a01140c9160007071807941c008111401c075a4020030070790b80b1f0b880702d0501892074110304042c40c0c500000c0c0d490003c0c0c07003144280b00c41d00303082e50351140c49130955105104000070184282c182001030140e450700d0902c81c914680e0228026140c0841c40800c84141807110040600c1982d07041c80c081c0d41d02c049c208413003c5003500c107403402c006034a8420300448020a000c0c2000041c1070036070350380182050318005c1201749498010601d9240560b198031494030006c0e0031060003d1841d0840e03106034a9072107541c1205900c241c0c0c0480000c00c01c0b000d5002d220948100b42c0c142c0b031180d450f1805059a444242032402c07048807080c0400e0082e440000050f5a1040f6038400d183c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 100849424 1250 100848174 100848179
    0x606041802040302010305060d0b01050108060619020a0212012f0415021501090e0d082223012a0c060504030507020a061d0402070c050604080607090b042607 69
    0x54048a8084903140005074000c0360800c1590f0300751081603403105c0d041e10b0440c04422540e84aa600031380501809050082410200300d254440109445d24801424030031845c013100220042c3d500c505086049100b001243c02284400f42c040c081d09510b00c5013201511098a030b806440c015102d10030a034110050000c6c080056404600080701d1b1020701d240d00640a0720406d40e600d0440e802c0160090040d06090181c640100500000d805100c4800d903e88403203580c846c00b4030700c03d0940070000c034107440d2410f1001c00d105210780103c514550000e10031110f8511000c504201e4280e03000c0a0b0201598680203c89042a00192107210749400c03503840e2a040c404015980c401c01c07541c090fa42580040c80110b216421400e103042c944010b0006814610b41d03800400d41b054900700d181071841c42c025500440d4581c01c000014009401402008250740e0325203844099055881900303c03030080020705a1813000407110348044c100c40c150b8100c000e4191003900d0200c8010003100203400440c24900c98001d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 100850674 1250 100849424 100849439
    0x60910080c0c1c020f030f0304020607020a180c0809010605010e090a1103010909230d05180604091401120c0510050d06031202010605010314060907050c060a050105040c020a0c060305060604 83
    0x40b6044426040440079024441c103c001d02d02000092884541d5008110854585a400c0c0960307502590444145135280142d2020402c081c20780e034410360340001411000c031004840e581100d90380c40c0a55988941300c1d070740c181210303081c0e50040c030950f40425101180d4000500b0901c584507441840c078000462208c64201c640942036000f640b2912101c0c1e5207090b1b820400030304803000120001840342001948520a09145d01c90b82d0303000c403240511800049d0101f284a00401c018a080e0004185c580c4031a560f00491024009022111031103007035a000104106600e07840c03088410340c000c1d21021883c0c0c00c260a01c9410358142208409000c420f000400c101c0300c40e400744c04099031103200d40301388035a080e08019080d1095904082d0525003030410300d61554001e02c0347c80380e109100700e82a500703030303100d421080c2c50520400b450091107010300d504000e07510340c051308034038106c0f00305460401c5034004660301282c407080c43c604c004008042d400800c1011740c0c440d4200d07d4000c2c80080105103480e40e50342c1c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 100851924 1250 100850674 100850683
    0x1701080a0c0501020312070f0314010b03060405130807061517150702030c1908070203061305190203030d0b040b0d03020109110105090d0807050c0915040506060910080c0c 75
    0x2041245a100090403030800c01d01e2040c035002084280015403c00b003205011000d282e800608550070007000c0c01c888015076100303410600300c02c185180e00112958465070030074295402118031078095030038040810300170708461121070074076034008402504117145541c90100cc7c02014180415608400c000841ea042c521610240c0c00340c1e80360028001c16a105419000c000300003800081550030600030300f90900000320f40b0700710100d104002c16003490618a801411707801a10340194040c070412080042314520441d815072024064401c81c0c841c03040c803000040102c542d0460007034058105100c040f1043d801c2d80c000c9035440c140100007041448180000c02c0b06c0d640f07002c10130740c01030b9142c10312031060150074180c50031007040a1030401d242c0704600001ca0211440300e00e0082c01c3c4c8000240800a00c201409500c4200b2401080d000140c00c1800c400c0c42203940251005120f80c1c50a001700710b05180c08400c5a042c241d01400031032140d942e246041e180004002c18024489000300003502c4880803d10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 100853174 1250 100851924 100851929
    0x615060d1103090c1c150f0c0c050f0307021003050612030f07030e0913030f030e010c0c020f09070e04090f080f04060807020303010e15010e03010c021c030b060f0a1701 74
    0x4040503103d14110f07030560326001d0201c0586005000f610002c09801d80340b210102c50031030700128074040404d03103000c201004100786900340011078076100512059039070150b008034019004400302c603403211030700d010503899128800c0000e6028940480d0b010170369001e034201035032000c8024040f8045511890f5010b081d036100200c400c001d20400103c0c0d00825401c00c100c001ca500041c1c0f286010b51034400b2140c1300b0301c4100d01d07001d020700040c060280c00c2d0900c40e40100c00801c050300024403c851000c8005000b418802100305d2085a8501c02c03400582061900240b0515981d5150320101c5590000d02006080741901600c1c140c005450240206541100410f000026150150386d07807840c0c0b5000901c02c84029005a0840d00208010400d403400245001c0c0c220140c500d00104131340d00b0b0360043e5010211002c40c182c06500b40013011500715000300d06000c60000b440026000c90850043c100c0846a41d0001260300c800c080c821400002007030006080f0007400f50410400804140c180001c1055090b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 100854424 1250 100853174 100853201
    0x3070b040911030105030d18030c0303090e0901020c06040305090d06020301030b0a1103010b0702131d0d020106060507030912022101090312050717150d1a010f0303020615060d 77
    0x1410007441d14140b0500c2034203001c8404890455050400080d01c03a0b000480d104100856400c0600e65140c8071080700c4011940800c2c1502e4441c1d6038034001d00040c5a03841078001a411f4000010039801041c000c40b01304031344200140040d5030301ca9400790740507002519019000000d40014000080c02480103601950062200c9200c0f407a00c20000400e8030540b0a03402039605050004100f4542c45405450340d40c0c3c3c0c121a640070b0058422409001486030200000458110018002074100c0c04a54a88281d81d1903009000d419200d60017552944103404000307001900340b80e0704018144080c0080c00740c03584001c20441010000313140b01143c40001e0660400c15075500c0307a80d5401c040c0c100e400d9494000b40c515050055140118000d4911400580002c044030511000a58910000c0d0140c0301c03242c00042100c40c1d60300b15810320303183c40c00d5080c807201500042a0004503410004207030404c2142d034113600a1443e9910b400c100034860f480e90031040d4001c1350074407000c0c040030341c41c3c0107070050f100c0ea1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 100855674 1250 100854424 100854427
    0x110d0201020c0f031617090a0608040318060210020d060b040f06030b01020607050f07020d050313090b0a0509010b0a020120030411040902030606040e120c0d0f2109080903070b 77
    0x40e44840d90030641c3e80d81115619074000c21040010a03490300b140003006803c003108100e0318044090041c40c0f44a80c1d0f1640c0da205a1020010070f000340c000801900960003540d4049000d00d1071400c223900342c1c24a011b0400564400c0f60302400c10380003600240b1388812036150106120355034000e66803854000341c021001c1c2c44080328040c850743e9070500c5000030303142d0300344003c20390750401000c042e04130700c50148a40301040300003981c9029034903440b200400099000044036615030810041860700c000c240503181400d41064415007851030302e641500140d170f01c01021042164a07000a03040680d00c264214415035481f0080005142c0007040560046880315500d0340d43c030300d00340c580071f4a030f01d082e486010701c514070f440300c000c0150701c001410759444403003a207002415a40d1444031900c4e00c203011812a1a200740001c4a06080d100810301402e420030700e1310f45c40c614445000b01690080c142c107040c900c0013200170fa0f4660741d203545034120940c09409200c0d840d10708410800071034180100d175000007005010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 100856924 1250 100855674 100855687
    0x6030d05340b0f0702061501031d0d03021b0307080d05040f0804080303040c08010e0d26130c060206040809010f09030204050a06051c150c090e01030b01090f14060907110d020102 78
    0x20f00203e0142c0c0681c0901c0681100e01c0c11203440c0c40346c4071035082668105a541c6003580b100840c60200b28603d070611a088580b045070ba0100100690f010f03040c105141c0d00001340607090368600000751a1502d6005462600b4555140b2052006003c02002914480001c8400d034000c500000d008002400c403400c091340e03907031515041210503184194000030341607140c10240410000d01150656500c255882c004603200792050050701c4000c850500c5113110440345062110707083e1941c41d0100c041d84a4480994406d643d0340c0b05036100d090860380039021500400000610350710131001400500650b0400d08051901e031380100c1e049900864642c0c0c02c0302c1e901c040502081c58160310040e44c0300380380501d6001504003662041b014040e203a269204107510307100343c2c4201034012451000a0500c16884104640c0d403400d014401d0701013840f41c20012840e0400c2d841d908030280c040c2e01c60030252602d5848098442c00e040c041c0b6010b0080115040095198000f002c005081c0314001c6c800d815a8005a210f44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 100858174 1250 100856924 100856941
    0x80c0105010609050603160203040f2601050705030a022503020109020306090c1e06071205030a050f130201110c0402180307080318090411030105040b0a0506030d05340b 74
    0x300c06030858810300118000411455442c07004895102000c1d40f4080c1ca515001030042e440c1d03005503003001800701c40618000c10314030015090076000100c14034403140040540c3c3c032503a0880c0d00c141c03a0100001d400308001043c0c610341c0c1d0024080103600380d0f110b5105105d600006d0400f0554804201c0c0142d4581d22940c042d481c080000f01d4000c040e500c017401a024900300000c42c40003000e215403ca241b00c0452480c2d07682e5415090b01c0b07401382c100614100c0310101c00c60061a692088500c245032070b1074071011a40004075130340310328454102031a15000c0da0ba290303001540c020b562003901e85503910131488100c0280d2594000313004030a9409000e008661850010541007505d941c02c0380030300354420700502c0a903480d100301e10380301280305403814103031a11a41043d1315426226281c80342c242d800c000c244404c0007181502c1510131664113408021030740300c800401d44c46105000c10b9500150080c807400c20841640c00c460880c0d000b441c003d595200341e481c040f612074061100416500260820100440c0c43e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 100859424 1250 100858174 100858181
    0x1412011d0703270201090e0103080703140301030f08030a092f010e060a08041401090b01050a060c0210080703020d06030b0103020f060c1207150e0d14090d0204050c1204080c01 77
    0x300c56041c28060f40c20580060101240000140c2c1900c541030003081d010f40e4010761040000d0206024020031540e1242810b10647e849240110700052704030a9000d5107007200401e46e8140da520a20103105070b40c864a5501c8160800b5011468165aa9101200140036200305010042c015890154204c15003e942c10358006500412030500c404400e000c910366036840101e03107180005082c090310a88440c20f0109042e2074181c1700c1c0765150320b000004401d110348079640074101c4400f01c071341c800720701c0c1c50f031100710b4421340003c0c0300940010307804940e44c5c81c03a8003071220990700c400540340041c14405000d09007801e0b40d01981c002e440e1a45103800600950412061980c601401605e00f80e01d040803c4559030354940c18611200301065000c6029410003000200b408c6c2c0d0751010203005d00403140d401c110241c440c070105180d0700209010600040c4e02e010890180d90813050028400e01d8100030b190240005444000c01050f000c07a0f003000800071941084055a0045016003c001e85031300c80503964030b084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 100860674 1250 100859424 100859431
    0x3020c0303070f0204200f180d080d2d0905060c040f03060e0102090402030906070905010f020d050d0212040503030106090509010308040612060e070e03060a06050f011412011d 77
    0x2a0002c010907030105500c00945041e450307060b01c00080100402c0c8880e1080e60f107175403040344164070001b402e00d02c03007403410068000000302c1440d0104501d030510170030401459020006040d820180245100d21341541e006060106d14400c2c0c1000903440d46800ca4452410340d140001419680e980e940c01340402045180da005203010300c0a032402d82444480c0c07002402a20000340202d0300c500c0ea03002880400e405591003120042c1040d500d0b0300300384030066221881118144001101315000040035032042e00b034020b01e030348160064101410030103011a91340d8800f400b040344032030f020820700600000c501203551049000c0c1c1c02550b00e95041c40c1000700909070f940e206610450300072b00144081490002100e080320320a040c0001d45900705860600603110952003920b850042c581009040c0390020648400e1400031020348103541d07100700c106c10071200780780101500300e20fa21720ba40c1c0303103540154601c00ca401031240d43c640c01c3ca045000e090300d291101741c01c10030304c090784604488101241c40c000c0582 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 100861924 1250 100860674 100860679
    0x30a090303170603030715140406020405030120091507050a0501060501020f010b10030b0415150f031b080c0403050624030c150306120123010806040c030201030f02090907090303020c 80
    0x100c2d410107500007035582c010060b010300052801403502c3c02c01210b55100d2104041c00801d5038031189410f04010b0000e40107417041c00d01039400d041a01080b00a04d135081c03140d180a4280603420316100d40280040f84961031b410901d00380f000c002c1400401c804210b40500342d441342001180d030074245000203042802400f030031415a8104003203550309507a0700103d170b1401072a901c0c00159001000000a010301038100807014404070f200e5020600e1045044860b0b10400d042e00d91801403e8802002c80454680c41d26500a108202d440f103000325120341c640c00d400003466044541000e890b030300c683c0d081400130303618100044c00614010380600d103580d0710141000c038200c002d4014042c1e81c01c00311303403070b0074801944000003240000007880c95038500406088400c0f0102c000c0100c0c0003100d200025406414070b072035000400032400002d40c0080000d049105980c0419081089407547c3e005601800c90049a80340300c9800740710403019502e0320410544150941d556a00718030740b840c01c0103401c19120f03208550 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 100863174 1250 100861924 100861967
    0x30303040f05191a060d0f0b1f08030306060a0c05030c1605090c030a0c0908071202040605190e090102071a060a08010e0a02011d0d0f0605060105120c0c0f030a090303 73
    0x2008184030309056800c070384d0201c0311004030b42d54400020b121143c04090080c61401030b002d000c01805900005c03684101c00e00907104404440401d00b45c0c440c40c1007446110500c0d8020400541d203810890003900c1d502741a4245084080519179405041d03410203060345032a07070301540784400c2107004012004000d013803c0d120350819003440c040140940c44001e0121400c141c813580740c0c049141c4a1070a4600078500f0005950303c0d242c450f1104501c40e12505426482030b801e01d5000700350b40c9040b900d800645110401e042546c1882c2400030804040c0c001c0003005a954240302c11404685a020509102406255980c600d0301d031110820904007216001100315a00d04564440340c0b42000565600844c2c09017410703a0108a6005114041c1e030b480b10746640c0040003906071404000e6206000d000c46440b0b140d05101e04d42c0d900f401141c00740140c03d008600140c00301c012a040e032180b11f0080c55400c2d00fa000380c490481c0e03e83c00040c038643c045180c000025103188030030414140d011200028130391400d071905 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 100864424 1250 100863174 100863223
    0x5070804030c0204090f05030307031401050307051c03050702031501060206090f0606370521070317090a0806091615052503022a090f0c09030303040f05 67
    0xc05009680b20000d00460341c50403214103000c903907400c0a6034070b640312044903901d1501e094001c8c081e24840d441da1009031042000820036180105690f0140c400c041e02ca66004500e210352400980c10600c81681441020001000980c40c144641240c200c2c1c01041c2c0c0600e540f40c184000c0c0ba01c0002480980e06400c54000c2c80113064002c6071180d00000f046440020300c00c03110003000c003010746190f80e140d400e211642c859440510080c01c0c405c21902c040312914105882c0000d07150105084118800d40754201c40804d0000810920316014000f40c280c400c0f5052884140c0890102d880c550000340c0c496008000f0014903000c20440c21803102c45003d0303412205072820241a6a2758146500141400340101d420441001c0c001e081c031080380c102d0004c010b0f030760240e4107004c1d44a11045030051003450f000c0800c030600c0700c50005c00311801354029000a1130b582d1007a811080c1d290028240c1e482d0154208500d020030f40e41040a98080c60041052284016085c907201d1b242c038084c614549040ea4110821 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 100865674 1250 100864424 100864427
    0x1060e150402070b01090209130501080f0d02060702060601121118041d1b06070512070b0106050415030f0b101e020a03080a0b03070b040909120201060f05120c220507080403 76
    0x450741155140d06c03026803600024400154098020350054200900c5c100000801c1040040c1c800740110601e02074840810b80098200e89500080314030501507409140407401551056080300384054155100040410001800c0b080c6075104c04100810010544420b000511b0503128460445242c1101080c951004400e400d845d10101510412088083c4210805980750f641c100c0e185a580041a81c41c1c41012400098954008160503a004d0050381c0c00803034900e00417002c032001d440c00c0c000281841038150314114082c280011501600701c0e180c14040c069519412046155074005840e5005600d415412030601d08040c0c1485a04541c8400c000e607021942042c941504011455400b290342900500801e16000783d6501c917684070302d00020b000896140c03662104114500c52204022600300b841812426641a409014600420b83d1030402c02071510400d9650382c07841c232001352441107000500003a540060102c1c1014400041414009043c4052080c1c9034400020f04100c085424642c03130 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 100866924 1250 100865674 100865693
    0x40803060a210204090618030504180204050a031202010608060c0a02151b030a091208091c020601151b0c051003060b031303020c0d05030c01140402032d01060e15040207 74
    0x4080d00840d03861004105000c40c580041f8011121004480e95030000380c5002004c03640144203014103581000d00c00c0308141a50300032501114002810104d1650441e00c03400480a060509102559607844001400c80002c2c805540b1800410000f40e840760603108010b810000e4101ca001d0f840314540d010020407503d00d0380042c0d504401e5048860b100e0b82c2d2104a000142a031f584058000303543c20b6401034505501c407400d03c2c45622540281c480500b08201110500300c094041140580c20a400510000a0392002e00d0f4100401d443c0c940c4c1b031203114100881d50081309a9054401203100d06041c890b40c1401034400e03030740c542d0740e00c1c1c104840c600d8a0040c0c500fa002c09020341010741c940155100c20302d4800c004032100c40d10002d00304165400d0601e80a0358035404049206030399401c04807910a80303400404024130468001e03000e041000c2105140d1036000c0302c14014031000c20b149810a03a00d4070002d210b08c001500380d03080205401e0400c103911040909050494074440ea00402070b54000520054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 100868174 1250 100866924 100866989
    0x106030c090c02070b18040e06130303050910050108030705010e061b072a0e06010f020a02060a18030b0411040902011b020604090906021914032805040803060a 70
    0x1072050780b200400c900b08103007540301840c580404104403d400d42a920300070001c46040b80d040103851006040c0503203526040340c829080154003d00e85001c2070081c0c0105074000005010b907000703020a81e031340104844003a007280305564804250380007005000d22542c070b0301a0701d0400502c03c502d80381c501c10840031540c40350940d0f800f40229801f0104400b040021003220b40c020000e0700a0851040c1d0194062024842c40c21600c10090100c3d60b65400303a035425403e0b40540d40a00900011381c0c0900406900041c105400c10081ca91004800c2016404000242d4460100000b55003080c2c00c09120103007060403200d00c40e900d0f2000820040c0e810000b0005c0c82c01d1074010203a03801b4000d0000513a40d0085034030142075142030030f04081c1000f060350300038180c4013800ca400c00d140000011088079500d02c40c0744450928841080400c43d880700c480c99501d012804411816081c02e1000d403014156001aa801c40720b0100200520050f4604001020003820a03000d00104200c03914240d0315940032801c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 100869424 1250 100868174 100868189
    0x8040501150819050a0b1303030c03020405030d0e0310060e04030306050312030103021320090a0b0304170304080904091103011a1012110a0c02010801060c020a030b1e0109060f06020106030c 83
    0x44001e00100f20040c400369070216002046c0e03014500d0068654030305d1194032070044001034a4410450400ca0180c801c2e2406d5074409001002081a254429185040b00b412425803600ca240085000f100084c0940d5011f0090b11506200b981010325005c2c054486940040e4440d4102c1044918200905400e40c0d0440760120307028150358040c01210b0000300104221f8101403071030540801000c502c1c90006141009087e295008000d0ba5001520f8440c00f00b9500140001d48008007008005403c0002e940c01038042c4409034a80700500000500b00c48505a044039840851034480f030b0549000c1c4100348802240c03021901103900358000061034400c0c014020400d008a401102a105e55181c1c01402000d40c00b207161592181e00d0040900b0b8180c0b0114101d00084525001040e501c1c402d14082c0c1e09140d0151545640d541903640c0d88000cc6001003000250551424090301e0148404071154001d02c0c003401c7c001000c40c1000a80041008560003800070740e130605504000003004d0050240c1200c190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 100870674 1250 100869424 100869463
    0x307060209040f0e1e060105150703050d06030c050414040f08030907050306010315051006020304120215120a050105040c0210091a0a0c030605010e0105120703110a080405011508 78
    0x800000b030010107102c0d402111040c81e211100c481c25200041032040c078540c403a0800203594091900641d1054240a4960414143c4407041c40740d41d001000b400c1d01c6846410301c0380c10302102c019107404640071584195010f0010003020403040c1060300c0740c10302c014010824003515241c580c540020500a4441c0101040c80000009445803c10310050b0050300e00181940d01a580d41e007050115903124120359644203142801091210341045250000c0300c8032a0051800c01d03203031403e045106111031609903000b28032040b40c03000f010420001014a4505d03248000c44500307140c10310304101c5505800c41409580341c0b608040c00c407500008c4a007802100c106010607100098038140350014256544c0b6804002c40c1800c3c002000901d80150150b0300c40c642c1d0422a5a40d01e8004407072248650380311a0100b001001000001d4038443c0c10301c0c0d4414164240400c82035041000050380e81e0042030791000182690081c441045020b00850708825075150b9042d0b4501c0c10030340115203422404802e014000d10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 100871924 1250 100870674 100870687
    0x171c08040f020904020f0d1a071b0318050604120b16091a0f120103060b0f090a0f0605030d050408070e0906010e180601030b0105100212030a02090307030602030a0603210203070602 79
    0xe503003000000340c4201500441201c1c0140c5848a0402314802031184c501d010040007441440c420040b00103c406074910030407440207151010ba8400350082109501144c020001280c541c80300f07802031005102c80074a00402c4002406c2c02e225080020f0031890110f40e12480c0403583e40d510030200015600c1c0d0380e04a1005035001c088005840c0b04030810402088008aa008030100241c481d01d41200c0c0600c1050141d01529020411000e001d000303c1584201c481d00030501800c00c640c081d20241c8a00100010b0080e1520002894030300d0700880040090000076041c40b0003441030092100901c0d0005500b8200c1c1003841c1d000e0303201e240c1401809528490100040c400c82d0b0301e41481904c24512000303035419540c40342080d420782c01c0c007401003c2c000c403285c1c080343e40020306c00606401c0d407111030300c280c0e402d58441c401040060b41c4480c00c0c1c180d25100b00c403404000b007081440290301900c41d902000807070900e5440c00050380c28003009048220304241c82e0340c107886500441100e00442d442140141c1d80c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 100873174 1250 100871924 100871929
    0x601050c0c100c260a2006090327030c1c14030711010503040309030b071112040e011707092a020703060b120a0809030304171c08040f02090402 63
    0x54948001684501034019001001c3d8001421034080790160b40511002000c10f80360b80c49100000b00e00404442c03082110710f42552240c020140104144070a107036032002c0e20360a252401d00151402c0d943da400c00074403900580e43d0602c0502d108540c01440b025070720b40000019844a4600c082030f03014a05000400e02540703005056882c000d603001150385d01200110407400c4e80c94021000450b2000c8012448540d80e40c02241541c0c8107907131580d10b01e2039150540d03840c81c0545001034051001d000c170900340d090a14100b0310020078031a001045058a692401049024650040e23002c4070440451203400c02031030601150510a4900320074000c9004818007003d09000803c1104041d4500b020016030342c046c50303002c10880d0480b4000e240034450030500c0e10410501404400003003440340d106d1031102c40041c60500c01780140c498001c0c262810155200c503160b082e65900500346415411404007809041d1507103a0741c1580015502c1c241c1c1091405941c1c0f01d003541c180000182c0b003015620000380856 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 100874424 1250 100873174 100873183
    0x50f0f0f0a030b030d0c0b06100207150309120e06040608090703060603050109020906040216020d17070b010e011d0c03040609080406030b0a0b0307091e0905191a090601050c 76
    0x100000c22429660120800e005000b007444100301803190003400c6825002a120b2403001c603400340c0004001010792140c500b044400e541d014003010030340c040d07002c0008400c00d224084c241107003101d440100d8035a1aa24081400a40b10780620b8148001c2060100d10740d2a49020303030b407c1d0782842c100742d001030f141c0d0001c0703501c0c0c0a09035000408036401c0002c08070800c4819080076203201d109503407003207040c2c81e0327542040180d00071310314010004a15031822001518040c000c1140090140c000000ca6024692081c0348640c0814000e4802ca0b803001c0040103420f40c800d420500500c840b210001c1c0014002559880e1004003419030a40b04070088046028021658440c56805901c004056070b65541c410000e80500284082d05120307015411000801a900004807449403c42d90b80300c840f010b05290407030700240600940b40301040900403010840303d505100b650b0185640c214030016480714801d00905444a0440d540c2d10300c00b00c500030500a403101c441980d0421030909059445046016009141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 100875674 1250 100874424 100874437
    0x40b07030c110306180d0804080904180f0b040b090f0a02010f120507020d1103040509130311030a02010504021e0901030305161e02010e010c030503040602160501140603060a0c050f0f 80
    0x5400f944e03041c00f070305000001c004001c0c1c0c40c00c5815a41680365002003920a50001c44014080f070108110b6440c0a00d8282d04c501c0300e07402c44c0b0381d07014a207502c0d80d25503064480116104460286100c810f01050124003c2d045610030f046a0007002c120150848180c0c17615207407072001f4140004815501e000034000c5000b0b1400e404420010000303803070704c1c245c0251341d03498a040369030108074031744c2a01092940101c01c95080e0345000e03210035001d8a0740c90081180e107005143c103800300101e0502031002c3d10024401011424200d81c004102c80c1442d00420941804441034100100400801982c00d601c41400250440b0380500388251074007030b0841c1c4894540c2a21000519106498880d030f4150850b482100d41954001c0c2d8035081500c0b42600151401401070070040e01091042c0001400a9020340080441010000c0780002c0d1401c0b580d0703210b080d100042ca521802c100b0320420003050381010013110343e01440a1500b80700001a40f01c0c0a40f8130f00c07400b461a010b0210000b04005001700003011202c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 100876924 1250 100875674 100875679
    0xc020d11060705010b0f010f0203030c0d29030c06030108060601030c181e09020a12180c08030a11120702190e070207030506100b0a0c02040f0c05040f0902040b07030c11 74
    0xb51980145451030003889492005807150075141454595944034401c100c510f54080d030002e40ca1a258000440300e1504070310701307403c1225110413201098201621960780c8000800c810010343c000741408143c10311802d5501c0b14007031102440100011000014080d81000c02800e001640d10305103c4100c0d04102d0550000c442034242c0d0800044890403030360160880c4000401e080e500b9600c880c2e4240980c40342c1d250303403000241c02411105004071158050201d0745a01d080001e0120044e64441e480c0588942c04002943c001142e80c00d90a5003000d02c00b60304120640252503080000080c0407094058102c019000e054954400ca203412840079206010300a82c031209006483c000304000e65403c00c03800210340a008000c045070a901c0801000000e58a0030100c1904005140004072081491301400ba6481512138200381d01d11003117440307030a00c02041c1c3d680d0144e6940c10f181080a41400c682e010101492042004210202d02041036416959051400c180207280504246002000310040035a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 100878174 1250 100876924 100876927
    0xf030305070e041802040e06070207030308130605010e01060e1012020a030204090609020306010f020a0c0302060307050d14060a2405030402060d1a040c0e0109051002010609060801020d1401060c020d1106 89
    0x19800344c2c20010202e0964800c41c2d060219094098401d611641c0030b84000c0b0141e400043d0520000340104407099025003104145404604662500c205541c0280c0c032469102c00594018030409603c020500d02a810135115156542030341c0d00700034046841d0440804400d94041400b2020b90710940495005100c00d00040c050540c40e960544001d62003907911901241c1c0000d183c0c802103001042d00d41e0003d8114003407a07040d034916002d218482d840100b0160420400300040700400145108405841c50700c000e500c0d11a18081c0d0501500c29170300c2d04070441d801d84805400c402c41074042c10350b0440106500d003c330f032251076610104226002c0d083d200803010b0300344071481c0e03021906036a090164810440d41480705029161054a400154065040c0080c0c00a0014003850410b080400640f180071702c000941b40b50303110486421500b003500841040d9400060190302198280681c07400c0003039403400107081d94900403004c0c004d803900d148000d0040b48031003440d009000c0c0c0340811140204002c1c1105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 100879424 1250 100878174 100878191
    0x230307020d051b150a0503040f0b04030207060818030d090201020a050a0305130905071b0302070801090305132103030902031204170111030c09060d1104080f060a02070f030305070e04 80
    0x2d685419584a1110f4201010007803080c0740d207820100c02a44080c0403484c00e10345813144000703d0b0242e0005005840c0540180503180020351410010341c481d5000f0340c00303091158180701c1c008100da030016005070140103201c1c1480c511000040300300c5609102182000801000c540300507030400c10390041c00780940c02a03440301414182c0000c0240320446822f0410003802d510b40c82c002c01100c0c0c0959024001130b5030500c2001440098210407042c050090040701c03050340da101042c40c2554803050f4114000345012580b030040482c03603080c0c00003800962100f40724001c602d5503002c20105500b10050b0425440d92224000e6440a004402c0c2c40e03200144c51595840c1c80e00c050001c06900000009459031901419455000c2d0308415a409403103004000352500700d8050030001e40360082d4022040c5c0c284c0c1d4405481900c2101d000402c020884480a80340b808031081d6041d0900d8401410036a07442c0c010414400050b1801c1d20b80c0c904194582000545915254000c541e007000c1c140301143c10a2404005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 100880674 1250 100879424 100879433
    0x31e0703080a0f030605060406050301030f0f0816020f03030406140a030204150801030212280c050a09090311010e0d3f0b15030112080f03040c0306060e04230307020d 73
    0x20054081030b2603c00740412a03860080c007ca61280c2d10800000400c14401800007445c1e40302082d01260154030040c1143c4400d44484809078030003d0049061007034011000d0440c1400b654901c101003088002d07508142c54030002030300c64940d501b22003941d50800960f0300c0481e40268103550281c9403051810302102850b0074007a0111b20280000d9204a4030101040f442c03100010f00c01c5021880340d0005520001115484101c002040804840070840b070307500447c05407500c042c0800100700900700401c000046060143c000c074a03410f41c0401d6039041a0f0203c413078800015000101e61007038a0041c0501040782c2e031a0084c489070340b2880002c235071100c90011540742c101f18a40c2e040c240140c0d04208504014040220741211806150626503051004014103a903800d80c4403407a80c02114450f04d4801040000c03403030755004a4040342e28141e5a80c0c02e00a1064a01c00da00290510500c518203038101600d03a01004442920300d42e010083d041c0029881140034000c0e122038640c0584145143d0390b140c40d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 100881924 1250 100880674 100880687
    0x100f06050a08060411040c02190503070212030c0307020d15180b0106110a15180b010f140f0405041407030302030c0c01030504020d03050a020a020d061506030b031e0703080a 76
    0x62038490100c072200410600c4010403401d010f00c2d071001308902400d10a40c1840040c04514103240f082d030280703611105a940a42001c202406d106102443e5128003a20403c400b034840001900c01035403090040b5052110008100c82e44103804850404a01d8450b151040e64074000c0681c04280d5401d001421001001407556400e0007441604242056a2288022983c6a203110b954400e20b900034006100450b07201d240c0c0c0203001106100101d0380802030701e038a12548282c120110303007100518004020f6041d00e41c1c042c00240644207410895002c1410003d5103542d8034054807845103075510085805c11443d403090104405042c41600c2503581c0c0c1e418069243c0d0009103100101d0302a001903010f10758420310590f8410f6038014041c980320002034400711100e030000e02c454425449141e01c0303800540c3d076011188000510460000c03828410021411060314526441071007030501700108990039540120300c907078103d281610f01d420b0b045c0f40360f8089460300c003040c0e0020306a014001401c00410740c0c07090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 100883174 1250 100881924 100881929
    0x20f0304031d061606050c160201050306040e0303191b080c090d120e030c040c080118020c03041401020f06010623091201021905030f0103030516120305060103150e01090509100f06 79
    0x700070000c1f540c440442110351b125000c2c80f1690b103000020450700540c010406181c002d4805040061500c0344070790594034661050300c41c3c1c00c1011000300394156403400d038002d008084000f06d03100f00f0000403441014189940c042c040b01e41500e40840c1c022855280c01504401440c0c1001005c40104941c00c0301400c051040f0441d14028050800000700e2410309000307005e284171140d40c03955401e81c603000110040d0099100600034040e000c0040c060504002c102600161000c83c8402100549603400a454003841c140c2441c416003013140104001c070b0700216000c01c40c4000c5c92504807000703400a003c1d0031522880801c998440420301300c03002c0c0c4540542c0038040d944d0002402d0700f100214280152120300080b03d40001c00402d0400610010f441100613100c41218502e62050601250390386400506640385128006030b50384c2c0c100046907074540140840ba4100c10070301c0350402d00300088111709800c14001c8580440d00c0d0350100320241020004440c2021300480c003080b07010400b0745200e000c0e14051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 100884424 1250 100883174 100883183
    0x207020411031801050108030708160506070503061206150f06090306010b070246030b090d081006020a08030424050613180201030c090b2b020f0304031d0616 69
    0x2200d07410f00c4000501c15141665031200046080c10401d94410700381e07a001c04940d00061805038010390004d0401c00009004031126100e0316120301d0124144170520400d00020802c95100405000071149108680e805a0105590700304020030a580403408510404000a400d031040c20300000365990710001030031807240708507042544901c0c591300245e514400c0d0319000d59100203e031003e501e065410f0b01d209030280442c0016480c116903d403a00c00503014102c070084103130703006600d250700e02640c080b41a0381d001610034080c0c0d003040e0400340000d548211072603004001c1d440001c0802c1c01d00189029000c5480310340b501c1074280840c4401400094103003a121607001c0d2a000e020484141e0160050803403200c0d50444d18200560690011400f0701003250170082400000e80011400c03030401d50007018a0bc0d040d0040000801c8100722482c00b0000240d5480d000c64410302c44005014403050440307405c544c140c41d180c080e5821740e242e407210f2911a00c1242b0391040340020941d440b410006c4c1010b0115018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 100885674 1250 100884424 100884451
    0x120103060605040b0a0b030415020a050c01051b0f030405030408060108150a090809060d1b0302071e0b0c1b0a0b01081626010902060304050a05100903020304150201020702041103 78
    0x950301880140ca4139031402d264001d16029081c400d10030104040c0d54460f0040c0b071000e240030041c10b102400c076408841100006000021074825101c400d02851341c10420000c29159000c101030012601ca0043c211051100c00000000c9000d000040098401610b54075080ea03000e542c0d030350001e50340e400b0000c0e52400200000400940c55040c0f078400c005586401140c95482e00ca808000c000941c0d0000c004036215076500d00300305002d038418600c040501945500c00680d0360929007003030061260500c2e0010361400b5407034001d000080c5140d80385904100c40e03c0e003c41d1146005000314603a81000c40d00002c444c0304020614081c007540c0d0f05005d04035002c84040d2075583d8600d483d03a8090b540799024001030110ce40c08482c01c00c1c9030400c2641c00300311142000050b170554540c00100680c0c03050b1000d0316141e2000c901403040c000b0511000d299008180d41c1000340d845a598040e449004622074840010b182d04960703002d0324002e404071096198000d0040040c040c2d6030201c00d44d15082a55040c003800311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 100886924 1250 100885674 100885679
    0xc0902120106030903021903030204180e03090d02010c290906060d110402040b0d0b040c020d020706030b1302070c1e21020a15020f0105100e16141201030606 69
    0x544211412144040120181a03003880000da0240000703110440840c4250180000012608203800040314444d6601681c0c4510300401c051016040e0080719000501c0c060040c044100000200c40c0284001d8030041401c46080c001030300ca1518920000d4200c50060b5062103a519003600c0c890b5034008814802e5a05403a00c0038080c3e56100d048503c10f41061804800304c012030203400700c40d121a60300400142c82c050700c80d421407001e80c1058a644c1049174450000d040c2500d054080c00003403860910003414030b02103020300207603140840c0c801c41081c03598481c03004500c0d40340d40e81c1c008103030f4800130004d55650050303142c1210100203e102c0e101d68040e0f0104196180741c1c2c400e40c600104c8403001820349003203d000400e2034984000b1352003240d10610480d03001a640310240c00544030074030a50090005020b00c680d4071800e66000403c111040d451031070702800000307a40c081d8260040030b03558004507244003059003035810f50070034651300000750f9001c40c41c801070070644490b481c1642d106242c1131001a9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 100888174 1250 100886924 100886939
    0x3030c0506010f0b0307030e0106050301020a030f06080a0b150102010f0504050d020d0216030b100f0303020601080c01031104060503191506021009050d05070510090b07080603070b030a0e0a05070b03040c 89
    0x303d50058904c0c9507000c00c08119168401c0d004030009103290740000416070f80d00d4000900326813007040e0090110381c84103a40c08a401c82d5100e014001c200303903800741045140950b25100c542e00d00070002e800001140481d200c442c0d2003540200107004051070200300074140b80c14029510a170096208d40180703e0b20700000f0031a403000c10009069032a251408860b00e0440c0d55002c081030f40107241d44100c1080700b0700010300b82c5010031201e0045000f9005807001d03505211045080c039002050080c18903007450100840c0c41c0e40e000032030341281d201d4604035450380c54001042c01c0d50500e980400c0821800c04c400e80241507010240d06003142ea83d5000c4601c550346244030071050f5010f022021b00141c1009001c0c042c2e9502440081c48094450001c0e1207012680b0241c102c102c43e02140c02380c86c841da1410420400075004101203402041c00c43c010641e0b1842c0020130340040c8802070040d20519220314001402c01c0007007091010301030340801903031103050312240a025542c108031030548441002650004046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 100889424 1250 100888174 100888199
    0x303020c06090a21020c03060f040b011e05040509010f060306020c070806041101081008060106020304140102010e07030206090402070c14040c18031e1a0402012703020d0809090103030c050601 84
    0xe6440481d8803c3c0c2c0b21054003901840c1c0321580c0351340c15800340018003000e5030b40610a03030f0300c50240350181c0046410541000c2008100507005115099002291460756111844000c412604120f4010410707503206400580945801110600b03141c0c18040003008010740c1e42c0142642c2072060048034062031780c4054259440c4c10969015110680e440e0009207154462281d40b6400384808908000d42951204100d00d0b00000764000c0c1e0042e0800702d028041e0a0401040103080b110034402030000c00c00035010b0035100c9400340300081c810040046e075441503460304c1e01500e074510f070880195262555206c440b1b201d81042100f09901c5189008001c40381c081c001c03ca030b002038040181c4116400c43c10750b82c8540c524468050f0440d62650200a050001340341303101c0319030010f01a00410182400c0c5840098a04081b0610051800f8011038501d1101e005920f520000c0300d0701210752802d41503080c20480a2842030700b141c19044010480007000380340e0401d00003400503118034201c4419030b036540e110f400076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 100890674 1250 100889424 100889443
    0xa14070c020904080c010e060c070b0c030105011205090708030721080103051b1c03030b010e060a05120c04030c0f06080c0f0d1a091e0c09010207120c0803070303020c0609 75
    0x10650400103d0041000720002e07000c034402c9100002101d8040440040c500f140440345201641ca0000b010700401009038803c80e0412003080c140b508650600c40003806840122408540c8141d8510004001c0c5004201010042c800e0034240c0b961942c1504160700580170301b02403000c20704101122015590f2003450014100c2e038101d030103440a88070b05000c014001a0f40c2500581c441070301f085401c004914040403907241c0303110f40c60020f8203841210001d4401a49103020b60f2180d20240800910690030100311651250540c00141c5165641c1203041c00c140526000605159010b40c00421501c2100c1c218609a59082d1036944c03040c1d6911902001a104507101002010814011104a140583c0040801e5403514101c0112903e1030000708202d40c50888003038036204415902c24002190701701805800248007000203280201840011b580c501c40f611881001214080407802844040282400034180a5050b60b41c0c1c0c216030709004020f900314510103d0b02d0300500703011801c40040014075445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 100891924 1250 100890674 100890679
    0x2070e070216080a11090901090206120402100f021b030a0507030602030118090503120711010e100b01032a0909110406090806060f010302030a0207060504050d17070203070605100e0a14070c02 84
    0x701c410600107202c0d0310701d0003401f802e00715921390240d480103030740c3c81c0c01501c856204c88442200602d1b06004010f000089600c098052000c0c0b481ca40c1041070380070410041000d244c68400d5008103240c004a894400008406409405180c6011042045540056040300c0c1400201001d00000658031821120500307401485903104100200040445240f216802607142c00c0ca0118159000906800c2d40d03174102440c3c600342c22003408031000d81d01d00d1240c1d40c2030740c4083c40d0400c421900070108044003d0040c00e0340e070a060b00c81c44440f00c2c09100e02403c401800011800b40025607280746c0030764954004d8041c490100d2000000803030944c2d00007460520a000040240d115011200c0042d0000d600c084c11010165170200041000300b901401200d0007244120b00400c0c11841c0144001e000300000910002440f540005001425500100f921a4160806000283c5468551000008614540c40742c207006000100300045006540d1261024024103002000d465071000e004a454a00c601402503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 100893174 1250 100891924 100891943
    0x60608060a061d0406120b0708070c0215070f05030c0105040302120703050d051009060617010b0301030503030f1f180c0305011a0c030421061109060a0f02070e070216080a 75
    0x1402c0080c0c84039007909901c000c4c00008003a521040b103440300d0445118203484400342a42444640350b0b01c1007805600151a240811241c0da040e070000b0440540c5135640c58901034042052010b01001d0581990f620380e2190071a96619007030021079010340001ca0f001d801500409165440038501e4000722114142e01da42c41c24a0000c00143e050000c0c100035000c17174040d00c0110408035844090b031207041e0152200751200c002440d01c0e0380c41422401d00c141c00c0916014010300c01080010f8002050f02e4102c21504801c01c2c2690b1804440300100006c081c04102845862130001100f6a102d401e1844a510b0002c3c140104010707c2015410ba0f2020b209130f00c0c40410701004031100c8643d00014000c0140060292494241e440f45141d031403541c104069409040c815441100b080041e10651401c50082d48049003080c00c0800064000d02441106d1414403c2440071038480d28400c0c8090710140004000003000c3e4200348030b0003541c0345550a440e00c4252441e001c041500c075400240043c00075030003c1980c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 100894424 1250 100893174 100893197
    0x2060c030f130203010609060e09150403050f09040c030614030a0b1b0d020a27050f01030f0e010c020c130b060a0f090b041203031419180213060608060a06 68
    0x50441d0014440c4903004002c8401d107006036028040c0b080100014200450a2814a07445189118019124903603992000b04806822200804e003254410f0309410702c07544540030040501c0551240444442d4003610744084101a240c01d0307070104081c0e03402a0100380b40b00f140081410b5484e0030a00000d004c102c01000020880c0c00c259071703980078450b00314a07420b082130014144481640c100c54101c001088802440800c0d101030405502415549813a0340310300c451030b04000c201c0300000e001c04c1a04060321403214080c1d048140d0041d00d00f12038150300800181c24100c0000707403507540c440c020500c10340e110280311144900501030740e500890700503c150726010b00b0100176540c65001240782c0041c8998001c00044492669028000401c100d001201c0300b00e2a518004003110940005200c12411510034843c14400c003001c0d403000d584031008001041e00d40d100d404650501e505400079409460086c001400e4038082d00700300100c94041c0c6403d840342e04c43d03200300300510000d0701030035000520b0203c61 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 100895674 1250 100894424 100894441
    0x6030b0105180f0102100603050604020f19060305060f03030a12110403171605060c030f3d050301181101090503060c07170c0109050c09090c06220f08060702060c03 72
    0x30f480154805004440c0120300010010040d108194070650341134012030b08110560400e03552031045064100c3d01c1850f4019010400300c0170306060700550040540d9000040d5164a07215035041c2e0f840e8000341100e4541c3c07403080c4014114090502c001d1110390030b2500c07d2410038408400d9409995003c10f000305455540310311906550040d0b0440010386020074241008180217104c0c0d14000e0b03803115040c40d5a0315007170089422140c80030300b0007506100414603003000200e455070440003003032040c003801045e070341840241d0700c00d04460b401080d415481d02c100c109040c0740084202c50b0880c071911640070040a18401910010301c2e0384111070b050341000c1c00043c5044002402040341030700c2004507540c0c0d000b419078419a0740d00318045070b501c180c1d036030361404003402420020000300f107004859420451421240490b200d24034070000314011100424180c210040b1460860b0395411144202e50b51565580503000065056115051060240802213181c40f0310100710b03103119140482c00545140c45540c2c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 100896924 1250 100895674 100895689
    0x40302060d020d05100e060a030201090506030a0e010c0914030601050f0d080c0109030822020a0501032f1308010213050f030309031605011107030b0f1b04080706030b010518 76
    0x7401c0da2025820010104201c0d002c0c4243d0f40190070110300c0e0a07025040444007400701c45c010700914400d1000d0402040142c0c0d10081540540744181c1da84c0340c032521482d8800f0f015001010740c802c0603500700a5a40040b07688400541d04558202c03002c0802d03400c0d030009064581100b0b01a864002400c0300026080e414060940d006440c030900100b40b4100d941c0c9089400c44001074070817000103880c2d81c01d02000e10201100e419200c1034090003198010700a500142c0030340a103104090625441c1c0b1282d030314000ca40a02807118040d40e0a4450340c401c043c54100400364401c2c001071491314030038000440c02ca2030502c251101e400c00c8000310303d0b0240c20f2004118803490404129079140c8000c000c1c0ea03107140ca0038401c6000c3c000300c1c411440c600c14100800582016180707540c50a07aa40a4130040011542400c2901d402c044200b00d02e00098640002100300c40460b40c501940d0840d0000f03001a2102c0001250350031540141d40812449c003100004640d03c0c4124601d801103031300508000d904500e403a05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 100898174 1250 100896924 100896937
    0x306030c06050a0207030c0605041403010e10050606040f1e1a03010302190b0d0e010608031c050402010c080307080a0614061902160906050a060e1c0201020a020a03120e01050f04030206 81
    0x11601000d544eaa0f03008a00720340d623040b04000500121f8108121009105c1d0030110100031002400a008901c030460341c2c413203020f580080203640300d1000c240700e51104000c81d4050070000590740d03107075500e80000c3c036940c0c040c0d03120085050b00a110f0001d00d900c0005010001e0846145031145181d00c3c6400f00040b4800500d44040d060303080c4640007440a20800007000100b130000c1000c0349050304030856600b150160b41c8540f0a5800030003d854014140840089081440e5400007440e40c0b100c0c0012030f48542c00c1c0c50010302d00500001405400c5800c40191032140b0f000344003d0101644880107046c0d00c1d000104465003000d0207100c040390f89a003862000079100080e204441081241c94541b00c0807030010b502204243d65260302c1801942010b00000d0f01602c1c507802c040780d8035011080818039020349003c0c000030645c60f0410090840e81b00303003c000b540c150000c001c000c155860341001c3c121808400b00c818081040301c0040c180550041c4150f50703071a002480103038180351640c4c090109661020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 100899280 1106 100898174 100898177
    0x30f0106060203040b030a020d0606020303041b060906110f010c090315270c0302030618010c0e060301140d0807030f020706030510090c03020c0d08160306030c06050a 73
    0x2c44d0115010b061a041c1c1d02d94030030344520000d01504212a44060a107100003960650010180d4000c034003aa22404a250701403c0030070251248d8400d060215650003001c0200f00e0141e070944100b003040506450402c2d80d08051345003164501440d61000c02c50684040c41400001c28a00f409031405007010003c01820300c0030b40043c4094540240031480e41441d812040026104030304005590260444031a82041480071f41008542c0310100c41561030283c016181501c28076138000100c102604140c5147d00301641006400c8120407420380101c1280e05c003100103038007100144111806551540e4060541c05002810700301554800e10405007001c080c4150300e00100100821108402c4000605104198003030700680034081c4846424003d6440442001e5003000281e485214000440c61031000640e0f82038081720740c1804090042d0036420014445180103100401104c07849 = true := by decide +kernel

theorem cover : BRFrame.Cov 100719424 100899280 := by
  have h0 := BRFrame.cov_init 100719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 100719424 ≤ n) (h2 : n < 100899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
