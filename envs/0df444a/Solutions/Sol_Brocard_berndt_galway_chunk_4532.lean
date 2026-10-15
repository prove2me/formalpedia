-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4532
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:10.971565+00:00
-- url     : https://prove2.me/submissions/982687db-30bf-4397-be0d-318ae50f6846

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 814928057 ≤ n < 815107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 814929307 1250 814928057 814928077
    0x301060f0315060b031b070201020106030203030d091a090a1514070908060a0c050412111206060306071106070f26010609050604030b070f091502010c030f020a0225081020 75
    0x10075507240010205c04001f0b0840e00c2c010710012135595100d40100e8655031010030404400c980d1200300c0e906106401c03018620b0310901c0c0301c1c0501642040248580e86a06998015014500310140303154121070661020900c0c9100c01610442c034984024042d29410603032242030071501400c4001455010b16108242c0e444900b42c030703918100360400280c081e0040c40d9040445290030a600600c0e604e95840d0540711410104400400c00d80c50700409240c2401405425042440300d10880d6844000021541d20b40c0701949260030880c82ca40c2c408120396086120181c000716680040b40300b4852941c44010794140c0da42c6880d40f03449c1e5903994044c40858422840082d198242c0640494140d51160990040004451400036042c607103840d0200d1500744c1010100c80540e40d1128105500394050144181c203140358803007141480003144010b92a070b030a0340d4564070381502410801c1155010141d0100142100701d088986e0700741c142d42d640004000d5580700c180c5440e0a124040b01c012802c40445500c801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 814930557 1250 814929307 814929331
    0x150804020a0632040b030115180b030c0d06120b18030c03030c0306031f06090b04020c0c10030e0d02060103150507050a0f090e040b1803040506090d020301060f0315060b03 75
    0x2140b50440700280090000310300e20400f0800000440d50580c00107140078202540c5086419800420050f1180445d1090000041106101040340460a0095a60142084e20010391300d164038100c0300001c0025411900151a00002880c10b02a0031001d1038031410700c039610a20b1030f007184c045159030703409000501c4039694000c00c00240c1001505000e190040c070040c0455206003a005c0940e10b42c41c3d140400c495400c0d54031001004810042d0141c6440b03108144c400718030b0000301189450306d07040c0481125000d01e203101400001988240e01c100e10248003c0d0a0342c1700d1002c80c80c0020340751082840103176400c03030740580e4041240701103101c2d4500a02c1280c6406151140529041c0d803449080d43e001f005002440c070002034074101d036555092099202d4492300c4040d00d0482d103000c80c41003151216007042e90041c07105120a0700d84d2001c0b500002c0c01280c5210340e0481c02c2c400a4050301090b00140d9050a844c000003080000034048c0f181c801d038484406014142d2201e000307170500e000c02c0302c0c50f0071840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 814931807 1250 814930557 814930607
    0x8040204050a200c2103040302060a020f04090b220207060515100f05070605360d03200412051b013509061f030503030718150804020a06 60
    0x4840744006001804042095a0b50b019003c5c1c0103002c803000e4040c05c003020001c000100020035505205d99070744866400300850402100f5200c00d1294006c0740940040030380e840c08800340c81c2d0741e041170220387d4802d1606001c2040c24155443c40180d0041141224241c0c1008045a440e035000302e548181c2c41c0300981805001e40c41400116070420b884400e01040c0f0034104101c00c041183c60040d248103861500301165400d40d911403140b103841c02180800e00803c88003102e04809103004c18045407006191030040b0700190a11107482d04001902d000d5103100c103000900041018400901d0440d17203000300113030381e107903d02d1410103c80312804070040d900140c1000091605404007074081040e101d581400c0840002d10b140310f501440c001034415521503801201084191140300403200d5a100101e8a8500403a19590300e46640f03000c00340c0380380240090ba0340101340040031409c41d1001010800d941b4140440340700070282c12050f0960701a80520b1140030046152406407034841c0c1c40d04c00b4003000c03c884d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 814933057 1250 814931807 814931861
    0xd02160e0f0c0c121905030f040b101d010501030605010518040c0c0b24060a140a1110050a1b0807030c0219081b1906180602040608040204050a 63
    0xc10402422010700701814440ca041c04001003001301890001c4031804e680e69049403082d0500c0d4070700342a4110400ca4108108258000d184020640080d0b104062650326100e40502118100c001d4101c2d090303a08030708402502c41c411402c0454102c0e002031300c00b000103a803103100449461040702d46c1c6940c03044081e10000c5031820700b54040d105041c03040c0303008409440380da5100b6184078000d5a640c5185100814400724004510520070400d0380100c4100e45460841e101c090051041d000004030004400300301d8020340d6005161780c0b0012001003045e19161055651810003c08040e540190214900101e48184022002240581031200e440380c070142c2d501d691044000c0c0004603580c000b1806a8006550303510300c040180c1590a10813182c80c0e4482210039514a02c24520003c0081241c0c080d250f0b00000c204035002980415801c0b5401050080300120219072003210240e00900241c0b0028000980c0366021407458080d43c800c540600117900d440b4886401c0d6012400041501c00c1d02400c50508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 814934307 1250 814933057 814933081
    0x3051b0a030f0203040809101d150403050102070302071403010c0e060a0c0c120215090d080d0e07121a06090a1808030916060306120303091a090d02160e 67
    0x904161481d0118080d00c41c1401c0308203030380065904072401c0d0804600c8031024035007a04984d99000307251a2144141042c6240014803c004510240c0500380c900054a83e2441d242e084401658115000759914900ba01d002075503111948109403071000f441c0740310700141c581802600c000303020580c0c5218109042e1410014558451502c640c180182c0c080881c0c0040d425071080740c0240b140110707004500c00c40b8018002c141d11881045400e00c2010415000a541d41003801103c4640140f0103980310301d11042610010311a10381440c840d4414940c0004800c140d000c1c25580c40da2142c241c8684030407602c0d07144205900c081d900d00d035000803032400040d0319020a6202c034030000c072034640e031400d5054503480c0d0070401d5100380c0f65503419810028444814500300000c000042141d45800c0014918051080c101190400c100904054031000000280400c01104400c1100070910300b05c01e5040020320a07540303100f03480c0608090b0080c1c92030300554424100100040f10101040400c07241e071b42901380c41e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 814935557 1250 814934307 814934317
    0x8010b0d0e0a050c0301180b010603050603031201080c10050705070501050c0312040c0f05030d050409231e090c0f0d06021e0c1006051c031e0203130603051b 69
    0x80290351021403400d541d10400c685040700d40510090100390700d44800b4582964820040c0c0c0304441600c4206c0c0c0c0c00210200125030440300c140c81c1c0081e2941301c1c24006400c62080c2203030058910540000421000c60104000f801e91108a45000b98040c0e040002d0700d10303014a22001e0010740100f0000c0280c0c1d4080e000070b02d4240c0c2840280c83c50036240d0031808100e108284d80a6902100c6400d082c031210003034410600180208038000c101f415100c0000801030303c214010007450300e445c0d408a48035030940c286003100c03031090203005070020b1600d50015480030391540c03200490f00b58503901080300001d020980b00300c1850003505915021024109000381105e0b64030044808960070049094014000c441480d204d902d5000d040c0e650303540d044116403502c107908150810440c45c010f000c020b55a1644081414000640071044043c0018101500c4121602d004103012240040c40e211109501000502000300801c03a00814561a0300d402c5080300e1086401c074034400c44c24446039900c0070540002d40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 814936807 1250 814935557 814935577
    0x40506030f0a03050c0c0307080a06090201050d05040809030d0323061513031412030103020f0a0e0a0b1e0a05060d060b040603060504180c0b0d09170a1e08010b 70
    0x440101c11080154075110700b0400503000144040f6000340901c1e024000b200540c0800c4005205840c1800045611100f04c040018041c5e0341d110b03180d204590140090700c3c0c1103c4800003c00051610341480540c0e5402025100c5c0b180c000e484e00d07010010f0113440346100e0b082200050324a2815101641c901d101c401400c0c2c7d551151400d17241c0103980000000030603030216000d8120005920718030b030508603802e10a51403501d0390000c0c901c040005054030243e0b4112b03074044648046c1d0220241c04154031b660703150084442007680c0c0b07080044034400340e0004001d000b070680b1160024046901d64450700e14102c00d1440c0d000100010800c49854010041c015020b0351603000101295690034241050303000703034040d4021a032641e07804c00a030b24242c41009502c01002c20050ba5025050340c40b400448414002d0808a91002c03415034000300c09a880810030030380c040c480b031030352401040342d41125070850094503000942c001240307010701c40c25225106240c0c0b05901c41441c4d80c0d003000d40c00c0e14543c0181d4001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 814938057 1250 814936807 814936813
    0x50c030606070f080d0b030601080601031a0a0e0106090c0e030604080d0903050c010c0f030e0318060a12021605010b100f1b05060a0911010309150e031201080d0e011106040204050603 80
    0x25401144c2808001c0c900d000c803090000500c80c0c101401c0c181442d00c1640700342d070180c00c40c10040010420015182203080110305001405036504a0020000c4c410b0b400c0d01e608035841d09501060000c02607025000d52409a102d400d1700b4aa8842015a83c60003190010402c047c02e01004164401b03640045607500c0c807c0c105942400c1ca145025421601c1000704c10000a5107640500700080c0c00d8850801c0c8d0910f12005581b80810802107240700c10000c0038464010540041e050316034600c6280003284c407070614503003550b0790040c01d0040c0c1c460f401c42c1c6100361a1546071070860304091400d144507040d000c9950319000210034000000717075000a004510001400400040100001c40500400d841914105d80019929915091008001c40501912410300d450007503ca004030760f200034400b401501e10f01f001308000b00c3c14a841030450060705600c03102c21002e60300104035180d002c640420700280756a1000c030104081401140c8812484410700541c0d0402d202080141c209a009580e01c610084c0c11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 814939307 1250 814938057 814938083
    0x60506061905121501170c0f1303020f0901030c1a120a02030a0e07060207090908040e0c0406080702190219032a0e060306071815120f050c03060607 65
    0xc00720086080c96a00340002d01d000401000c103611000c003150300941c12409660003000080300181603400c40e00d120080292118000a40700c81c0114100e548200b40e84000716100c0350360031400e00400d4100c1c0412445002c1040b0146d003d400c120a000e412a40c00840d0003075a80d2501c1c18101c4014a00906109414410441026000226110386001e8004103d006a40e07190210449003220b0810b602e10140c2e0704910810050369900090000540d85000310002d00c088403444e0401080c425903200032070400f090307020400f003020514007800899005c0d0311140032542d5080c40403a2034003802c0c590b11250f41c0705400c1e80f00c054101003140c0f00020241100d50740300151a034581c400303544200e002000a88134a02d01c5611414004045000242407a01d5210703c58100720000039140c14004014100b0400415294002c4000c2c81106100800200d508542561031002c0020904041d18110202940c03c0a9102a9a40c0d1501c03d4030320580d4030045840c21503c4010030030016034000241a03c41e0507035590 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 814940557 1250 814939307 814939327
    0x9022b140118051302062b09030801050a080105010b0712020f0618010609051b090a030b0703090b07180608090c0a0f05030c0d0809010806060c010c081f030c0306050606 74
    0xc00140079040303150035420a240696034400548400420032001d82c5101248000181c1b02c039020344404030301800006009072040b0f1509101400e1100c01002000d08003004c12092641280381d1905880d000d070f445030300550301c42c51a94281d90302031140e403d44803c00c0000201051013248075959050f0240305641c00b96407555070503458035405440410100c1c02e00001c0421030102441100300130604801c0c14070141c9024200342070354041000001401c0ca400240c040b103981d131030b080500f01840d4020588400c90929447c02001000c55000454032500500c0c0859030035402a141100c05c0710503c03058004090a10008490401c0050540d0000b40b05d406c035010390340d5449403c000041c050050104a1703151802e01010701d0308180d88030301409034000c1154040810b90203000c681c40c0d1502030030003078950740b03494020400e42d01c106c80d80060254a046201414a0f92081c1c00c2d601584801002030407480303a00c1c1c5000359610840c40300404001080f48200005001508a9035011900405190510b10000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 814941807 1250 814940557 814940591
    0xc0b090a0b0c01050115140f0706020f0d0f1805030912010f020406020f011b050403061e0203090c0f01210e0a12020703050706081b071104020c0c010909022b 69
    0x32070300b01a41c0d44a0300103010340c810100d0801240012840e0520001031840c0c0280e24501c50503484d80c02c50003002810f0800d0200d281c04841c1f40745a040f10fa659144a00107054009020402081c50352038100304d0302c0391081d0b5180d45c26418164119028500d01103016040104820401c00030010039525803841d5515640701d8800b0b480146072540240c41c0c0004152840c900311001a503a41015451002205026a9120003600c003500e0740301c2c3e0001100c4c00420100b0191901084003001038500000410680100100b03046510002c00d176106d042040c00c034001921016200314800e008032070b0032a01e02010210a4000d5501e8003010010b452340392030315454400d08074482d42e1015000d40d100c6441002080400c00118008102e40e1400c01170900f40303102140880642e045800000c4003001c5060018452102d1071151500c90041046603904c1c0009807190301d41c00489130060201d412844009012085402140d10721241000722402088090021000b1f200080c180305c1c1c001c1d6074910704401d40181e80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 814943057 1250 814941807 814941817
    0x15181d0a0f1a1f020a0f330e151f03021005070309060801120201031e0e071805090a02150d02030a0f0605120c090604110403061a0a030c0b090a0b 64
    0x110400070105980003070094041c003c01e003007a440d140080c903008015601082d07008089611400c0d00041d203010b4241a02c8400002d20503c140304489a81e03500c4034500641e05900c03c00304203409100010f00f400d5180c0d221507040507012041c040901c005000c1d0f41241003020309440b02d0a418003001c589940200c1c000507103212601c004500b000400328103140d0400e50050080000386409091507041075084852a12085402411b250700c1e01c0d9246500081c0a2506000d407258880130007122100306d512540e514160720400204140c100d04507040103042d0f0090314031600d52000102140001c5a0900030314000c06a401480000e05000f4861005c103207000460040c03c0e0a00301040e0020001140c00895001d507011511401e401810340701d40c06008284203200d9402128183c040c2d0791020045006012010485d80b002040044c011080003a2580003403031518100f0750080044d130030380c03051004034103581c0400b9240d560014410000030b00030100901c421a0058041024686d9a0042d00019041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 814944307 1250 814943057 814943081
    0x60307170102090117090304050118080f010c030516090e04020d020315070207140306070320041806060302120c160b070c02030c041104050d0c0308030115181d0a0f 72
    0x24030b44000d40e807001044107401c00e00c1d910154207061a25045503680708d10301c50300d0f0502a2110111034248540c552080c0240303800c0c0f05851428502c078052600070000003240b04086880d1101042c40b555104490b41910007054680c2c0311041e003403842c0490300b02c400034401c0341c0c0b1030544401c4c200140c400b030100c5400c03540e0604000710f00717040c0064068105041030304880002a9180c0e1100b07015900040e099400c150307181800200911f95510744c03c08403210700810310b24070000003000204484e400f0f40c01135102c05141420403640740c407800220168400d80c2050302050596402042e0000c0c2d10130300920403d00c404103214998100c96a412054030030858440010480403914042541002c1c850000408000c44081214505a40e40354a05015501980e0b028942e2102c02c1010802a091a40090740d04402099165a90307100c0421143e4209803000c0001044992000002d450035070020301507804100c43c040141d0502c1008000c0003100030040c40d2007a85445020100206900c200b06903159 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 814945557 1250 814944307 814944311
    0xc01060317070b06030a080a030b0a1e0f0504020301050a0b13030f080c0d0f08011710091b080f1b04150602010219021b010c0f12081e040314030603071701 68
    0x1c0281000200d041c402010346001b908012100000540c0d00e500b203807a407003050b0a000611150b05e9011444c001b00c2c94010340102c1140a1a02d40b0404a10308044103c0350028030305a400364442050105900080c032500b600007003400418000040c014010f8070140e4903003c1d40002c0c081c0c4d20703158140d402c44044e406440000c1c000503042c0040306c05100c00100002641420090010344681c0204208014421103421014000060b081304100f03002c580500130f00c59000788007001450811210030740846038008004030743c02c840061151000304130520361900481c00351851030303a491000c40c42d080351a4402a805540d41400c803490004130b005400117002c040d4001615600e83ca4000d40e00683c01c00e0050040d03600c0100440303c65407902c85404100d1500f86407400c3c00000038a0800c41003410003100a12181004013a085615881442503204010750701903800c1d0f01c106685c1121504030241c034080e001410b0321090147c4401e0f50340c025500000080c0031100c80950720300c105080c05514500c040b140da5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 814946807 1250 814945557 814945567
    0x80405040605030c0109230607050606010809060f0f0604020c0f06070e0a0b03040f0813080a030806010503012d051206040204050a02161403130e091b060403080c01060317 75
    0x41898850354000d0842038006001e219506800600907100c541f04090034514190340c601c1f012891401c449140c00c038080d00543d01e0b583e86140268841e0011281d807800200440700096a065000070b100e402050300c40308440c010b0712140c04022200314000c0c0005c2c0c0041e020058004004c0e410041c10001c2c03503004001e01564100800014000800b10107a1403158400b01c2041c0914030a0904490b0000d60008401d03001166a182070101c0c2e00803540c02da00751009880740002c143c4000310b41c42005c24481c0d941c0c42031503034400c001540d060000b801110126a00d554041d865580d48004941280582e60510340c070700c0d580c0791b0024003c840900644125504030a0510046081c03e001d07081c1c0241c0b42600540c20280303440d180c0c3c9918010780e036019000305803101142000c02028811202c1041004410382c0050303031a0b802011004c00d041d503500d00340b407040c43c0f130f0b407080b032843ca02c040d801030381e0020084c500c1c04c2d1840c0c8800407140c019617103e000c55541d4420000c0000c0f46082030a058041a40e0003035260 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 814948057 1250 814946807 814946809
    0xb1207090501030218040213031e17030705030103030c0f1506090b120319030227090a05010f0605070812130c0801020306010c0f110a181d0a0f03050c0109080405 71
    0x180c041540708606040c018000e043d500242000580340c0310005807030041e2542c0f00000000301020300c40d400a80311800b15102030310b840c40020f008421050140e00c0d1400400e54040e01024184401c0700d00e1800980103100600010703110340c05200b0084e0054804001c0480c1d1a1145500006811540850359580d00400c11604085000d207d100c110212000d416454404c0521030322442001860300d5142c00d681c54218009000380d054540e100202d040d00785501c00c502640071031070060661401e00c201203010005003036a61034000c0b05c3c10303034902240b0701c0340891a200003982d154002e880c003101c1340c00b414059811101c004c900780f1849510143d000c54244c2506050944454441c0d40000590f640100304105540c1d8014842c0b0020584c00a06402e030080304e824201c030004006e1404950042c48a000010309820080d14000000400401005a5185c0d83d00991001d0421510701e442a040246a0000308560062507100c8a000341445494900c40a80042c215070300c1190844065a01060074051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 814949307 1250 814948057 814948067
    0x60507030606024309020c03090108010e04050a080309010f02030f040c060f02060613020706090309170c090c071b0e0a0c090819080903010609091a07050f0706060b1207 74
    0x5031a001c0c403442d41c18190544800c0542d8141e103800300c01e08149480302d98248803150340701000304171078003045489081151100761030b54084000c160000b200340d00086120000083c420b03004550200045c04050100c0d070b21100340360001003880115550b940046124200c160000b94803c0c10444441c14543c90207241240c81e0031419040101001078110b902031181d0f40015007250803140c100d692100713008440711040e01034400c040300144054203262041c004c140c1c02c101000309480c20031079850300a201d40505247c1ea01c800c12021a88841d524004c1101c03401c84000038025180200c484103012010420f080580700c4580d401000310820000401c203982d1034501c118010380000e0300e00140207501d03005401d40d40c1e8004044442c145c041d80034a2404111103a0700f00e40c2018406402071204503030385d002800090040d680c0540d00344d9040680c200030280c401c04518407500c0c6603101d03241000781848640c9420b0b084007104070f5020382e50f4240070400003003010181001e090b808003507000d14a011003000308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 814950557 1250 814949307 814949323
    0x6170c0a08010506091506040302060a030b0103060501140a0c06060b0301081b01090e0105010f170a0f06090b010f1d04140703290402370215010b03060f04020706050703060602 77
    0x1d03080c0d1402d4107002c402d40c1c401c40141d4205044940d0311380540c00f2507000981d10311443e44025445540003810200c03054150b0001511742c030382600c040001d640e9600040d02e0b00718804a024080e600c04000d2000c80c2c03401010601030582c0a4031000843d02d803540c0004180d6031003a044015154051640088a02c480110309c003950242032078031406540c90201c2041603000e06006460510104070701121003944684030b100c00f2480c000d24200382c3c40c100005a1802030105003020b4407140d04040000c10b5542841c0070b00090f07420180c0da00141c0c0881d22000700e48000000c010083d09000350480c07100c5650755401000720038000482414100c1c10400d0004d0201c52210100c4110035880d9900034194685079107860072802c1c0140c03030241c1d546492a00d641196004e40240010000d05214074401c005e0a07800c070810b20071000c2d001c50f0b100990000c001e002d000700912850450030310400004465041400c445005983c1c0a032016040c9161551240c06407241102c090000135a9000d0401646904100c524 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 814951807 1250 814950557 814950569
    0x4080105010812040509010e1f0311010f0c050309090702160305062e060e0303040911130b04080304030f02040207080307031407050c2a030d020109121b03030504050106170c0a 77
    0xd45058030348004070300c010300c0501c034502300c502c2400c0019410700310b880c034000c42d4440c0c2d01c3c0c2c0e03050b0b145440e49400410252903005450010304488114030110b8051041d45090301e07000b800641c00d148100c4104000700200a0681045008042c0041c501100c64403d120180d4820001340c0000d1130062255592003615001d91300064a001ca4074640704810f01c681113096540c0d0746071683c0484a0700c00031034510f20407503100c170390454a0880d070030391805e140b58080d01d20b0245841882d201ca40da5200501c1841c001da005842c400e030402c000c2040020720708150031000c83d101400250070001c0ca52661802500122030050200e600c585503030b20591592101194000c500f0708001d802c000b04c0d5540541c4d15100384004058024050b42c400c020300c031032200402a0440c0080403034a0780458194000e002e090b030700340210b4104441f6404091218085d080e101482ca038090000c0d00764610704e44044000d0312002c0c0c4191001c2d50307101c2c008540c0c0070443c075072400e4006181c002080d0f000350b0b50040c1700c800300a0b94041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 814953057 1250 814951807 814951843
    0xe1519110403020105160816050703060b120619060320130c0c0615030f030c1b0e0423010e010606110106030305040b1c020706090201020d02060f0a110f040801050108 73
    0xa01c0181e80100642d40f001b4540003401007a000b107468454600d1003000c10140180590050078001c001c1c0000d06030f030540740b103010700348800c551920030711150440c80e030445021500180001001c14602142d034411031521107901042d10b41d80c07501da6140c000e03070086003000c02c040103c4001d03e4501306042e01080d074000e80d9004111503901e607000200305079008c00f8010011500e40c484128442c02da640c070034025541105225031140046d02c2c000c0c160343c42480b000c4030311220180983e500c924200000c1002c59200e00054070701a6a10740c2ca0a03a458501d1803840f000c4000a14402e0a0403800d115000b02000c3c0a0300003c0c1302c40c00e280d070252022038000c84c0240260304100d020b02c0026805030580317044621059980da00c80c0c5082103000440b03202a0119241a8400b0030315a003800050742110603114000e0b000d88440640c9a40300300c0e02d58104951410b09100c2c20000308030800b681d80e0121007803c2c040e514080c2011000c03094001664801d51000c040c6a450310018081501c01380800d10710801e1000c1c1e5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 814954307 1250 814953057 814953059
    0xa0b100905101e030c03020f04081e0105090c010f020f010c090503070e06030d050a050f07150506010c1a060d0203060906041b0f060c0816152d0e15191104 68
    0x103201030b0820f02c0348a0810580c407001c22002d030380d000750141e410585071984a9502ea0341c0f1850065501c0659090403d581a083c0046152091040c8110b034001c2c000c08001d0b20244a00500645410100a22a004612440e00d107210941c00c01c1c801d403d882e250f51360f0703201050745ca070404051900105400460a240c54841401190ba800103040d000800d010b041c0140c4a40b41c100e400e50340c2e4001c6000000c241c2000181c040104100c0f9000e85100301c241e84800c01060300d0320001151003031005000103000c2181c1d151003100708002c181c2c041e68440300080c2899841c400356030201e400c01c24152001d111951015041c0020020400c0080c508075240040c0000d48510b07200d100000c418180c41808107114104110000744046101141c0d22040f22a00c116840030440c0740050b400210194110080d070302c1c01110041c0d1600307003d285c0c07446040c00614103072100d01c1120b6010041c81c45000130600e510401440040d518108401c062046000800803002820100340c03802c15121900d16640c0780c0441080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 814955557 1250 814954307 814954337
    0xa06050306060918070603020c1902090a1104120f050c0d02030604030c080d02041514031324111e090109180b03030c03040f0f080a03080a0b10090510 66
    0x1022640300b0012140c007029030300c40400400c803480103281201d805000388140458003c1d0550000c120120f5414111411030400c041424103041460f50003e5111b20315a010a4100c11150807204414400c1d200507490142d80310696030580c005031804980c0300c0c2c00b8001010521200788111a59070300107450907088070386c02e5800280c81d0200148010700380550801902d0500c42080240d40c1d42c0c5d40614001c541d96500ca8812040d4403401c01d10a20019000342034a00e08500111300303803170065032003400c003000c5c0307003181d80e21b178480071100d10a1240c1c1c6c500c020a6030b408260050280c0c200300c030443d4680c02e0380e5200c050310009c020303111a10664030350041002214120799000c00680100c41000f1170301d00d400c078000791000c0b01800c00c44840c680d1610021072441d40f03040020000300116144c0a5448014035a64640d85101c02c00901c900707102904507140b1440402e00803000c039903000c001c0000014440300a180002d8400d1100300a400000300301104c140001c1c10300540d01c142604450410b11a4000481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 814956807 1250 814955557 814955563
    0x304060f030b0418080c0309040c0503061216090e1f09021e0d0b130507030602130512030d0e03040b0301030804030b0105011d0f06070204050a021e04030c1e0b0304050a05060a060503 80
    0x1c1e0300600004000a1221417001b041c416100c01030750080092201c010080001442500300341c80041c426002d020f0000444540000c1011211250803501800540307032a00000050003402c0340800701c0d01410207501640ca900440090810240e014001101e000740d00501c8074003900620b03890990038505840c0d400d9650b441c1d018158440d40b280d19054296520040501d201c43d28540052284c0b10300c20000c403c20040d034000d40010078990700001e8001c2d0b59441040781034981043c150643c0e4000700324071800348149410080c4d203005104202e918103a41e5841100344c50f4001da100395001070300442d0a02c1003203d44805035004150901c1c04181c0805502240ba244101c440c40d03640c456081d0f46920440b607111700d4140c81130340d600144200f20a183c80040d1001941c051074504004102d085145407242d5941400d883c1070340c0e003240d00540712501340300c5003840d50900e0b803480316001031802d040001c0c4107008000541c4540d100d01e0241030403261134900203161250107007039070041a080070420312140d1000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 814958057 1250 814956807 814956851
    0x10b12031c0b09190f0c051b011107032a020603280207030306090e030309030a0305060109260c01091409044205010609050d060e0304060f030b04 64
    0x74800d280c000c1c504944840000d00c1026a81a0040048810400c0c07406080c00002d00718016860103011103020490b0070000c44513881040c90100748140408440030255081041400b0040380001402e04d03014105402c564011440440002ea02004042e40e082054100e5a54031a1901d0301403403c590181d0015950b404001c00d44201a407601460b8402801044549081069035160466907a4103a040c028058280744c01503407607990410044211241c000012a441400800c018504040100b5012406848003410702c50410480010101d52101c0642c0070160b4405a419400b040c038034050403150401c01d4820499040c041403000400c00ea0001e554400b0780008120b42c0044180d5507880c9c2204940d0345954010940002010007454610060300f00e111507400001c22070144a5050507040b060760b40901403040001d01655081049041100c0c20170011440b4900c0442c042c52298001440c641155100400159a03020300841694251040402c200d070b007541d05004603c03c080484000e034803a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 814959307 1250 814958057 814958077
    0xa02030a080a1e08070e04291207030f0206160206040909060b030105010f17010213030b07200a02210a0c150203070f020f06040308040603050f09060601270b120405010b1203 76
    0x7100c043c0c42442e076030360344500d80c0480c99021440251030098460400744008c40c0515000340b0302503000400c144c400096403000c403940800c5c1080345410315420301c00181c20403d0b40d9a03038041903049181c01a40d409001e08050841c4240024405505081c0f0307806654a40000c0c42c0240d00d482c0040c012804510b0101d0140c1d0146914188410210503200740244a1840c109040122910b00402001099102e05000f00095640c0d0030040010306040c0c0c80789034a84401c0c0344c50354819240c0c43c1c0141080e59803e1858084042c80600040480840c14100030b43c2e400104d4008000c03810074007010481c03810105000c40b481c8011410106699182034102c1c80c07003403010f0320510044214480c0ba0351003a080b140a158054041c0351101e9650401401808098980b04502140d1100046105000250041c4501340580d80c240070310440000d005c000e070404043c00e2080d400c1e025000b03c0d1012111004104c6200c03009010f2a4a24043c10072a003107440e42502c0d58070804c4a403401d60070764030b4004140d51076012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 814960557 1250 814959307 814959317
    0x10b1e090403030c050c0106090b030f12160201270302040510030206072a0609090b011e140d0c0809060a050405030d05060301090605090c040f15170a02030a080a1e0807 74
    0x89118015a024012407041e40c1b07075907088c8400458040c4158001c0f0001d0101501140d002a00342c0d1407007030700d40c51034480d00b0986100034440b40078800f80d4501881036450041c1800f101164004010f89044103d9010000292054034410000c60805106141e030108541c601410090308590004010344106200500074000c211107800031024074554901c0d00f20184c60840003030954641c405000c0044901c100e00031945896580d0207994002c16800d6521400c805000c090000446070550302107a4011040c80402030500c40125080c2e003c1c416001450794545078000213107050241c0c107240280c001c2004041508080600001490000c260340200c1c44004c00841e443d035625000c640100800040509641d0504041c042a80008a014035001c40213031401e000c824142c01103002030355035088046036400c40e060030400131140c40d4000c0d0140030203020b05071140c0b4120b41e00000c6c500041c08009456076100003802c40300c81900840c1b201490f0818055490605540c1503000d03145101c02820902480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 814961807 1250 814960557 814960571
    0x4051203150f040e03070c0e06010e0f10201e0d051b1204180f0b010e060a1103030a05090d030603030207060c081207020705030d02031201051c050708010b1e09040303 73
    0x150f1160049080c0300452411a84c98171180d04120081401c1d038030540c5441d00745800442c10750752094500c0100e440010302022500402101446100c01c0350000c0001080700ca44820140244903443c4c88042005003801807191814100700002c21028544c440f51469120710140554160072a050360103192074050280c455003a144011030038505034000404c980100094042841c06004800101e0400101810000c6009101c1000200c8401380c60325030201c4e8000e55952094034041008000c142660300e080e00310365681075107003451600243c80740168030361078070708000c0307810420003110150402500e01400150311750785001c3c0d1245d4842c005c900c20489d40c0d100180038449d034142107810444441340440024584040c00940f01d54440c092644203000b80c40700f820003e440041503505c0e400101c66041d41c164030b0102008030b101c507542019148400031111420108005124020044c0705410000c16204010302c1000070382e00c600d6885010500c1031081090168890303010850340b09070325050018842c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 814963057 1250 814961807 814961809
    0x5070e1e1302090a030f03030f0c080403090e073c1409040515090a0b0a0504020c070e090703050f0c0a050a0303021c05130f1d090316021305070804051203150f 70
    0x4000e885c0c0003c0d280b83c801c20a1401010b6159000071040700401e8810801e9030040142190003041c15900a030001300034074401d000300e21070007541603000241c038100902c17005915840720500501601442030800041c0703890314034800400c1c1840c84602144e15203d102c54101c4020222640111031072140207903500d00004120007041c100c070210b8090020891885454010205406081d500703440d140905400103001800c5c1c10a40250764001e14002d001d03007040d605140e00212900e90082802c8901d01c00c0380d8001003c03030000e00009507504103d00c05400340c041d10a00341322a2a41a501941c05420303c49030400119601003501e4000304041d04041513001d60140c002c80701d81c01405020240381b020800001400e6400c544000308443c60035454111702d5141040b080514541216080d0041d00700704405075103440c2072590856810310040c0b07103062010b100900e440464008550101c08103404c5821300040c84010840d403030b14034105614040c514580b416010350700b40e0711821114000c581c0d4000710303070007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 814964307 1250 814963057 814963069
    0x30709060509010e060c0f120f040303032022291303060528020909070804151d0c0a05210f0d050909070201090c2705070e1e130209 58
    0xf204000c0c200b50322086c41145940e141c24010000102c10b00c901c0407110407002816080c0c4d84640c10941039903050502d552403d0700a055a090050005584412104101000c200140a540403e140900761440c100c1842c0f180c20708050308101d13600e01c00b203900090440480c042d404140040c003428030ba10307a292401641001c10303068100600781e03410041000034030450295400345542300d4103005040941102c4095040b03110f4130404030707085081040041d4400f030043d11904e4216110f4070f12903100341071050a000465184540007404c00c000c48203550907403041003180014414044980d408100d181c007000914070b120340740b90810f10aa407031036103081c1000c0074000e001e01400b500059803441d0141440041050f841461002e101c0e440300700c04110840e20500ca232005140e80040d505030100d04140e81c103021000a640b5102c0c400070103260400b459485030182c540600c0d42d075202e220b410748840c4e0420007400e00b80700322040301c0c0c440c05021030005d0391031132200d00700c194241e9001030b5154801808910 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 814965557 1250 814964307 814964327
    0xf080412120e07080d020c0904050a02100c12031508011a0918060c21010e04080d02070f030807110d0903020d050f030708030603011802010c1b1517070503070906050901 74
    0x2030034054208002011302003c04c6407002c4001903401d90b0503005544007004101042500d0141960744450382590060803d90036207a03640d51a410072206402090743d840e6030b96410324000c10006030700d620003200304414002c080c0005d400400001d0140e020f801d600e4502050600b40802d00c9030481101051404505552262150315968152800c0e8649080c0030300040d80000f101c08502840160100c01040401c00c0703542c10388001900a4109407102d4880904603007041c0751107006e29a003000300000056801070168812482511580c100b850a04005022108985102c3c00550041e13180a81410b030300c01388a0081c1d0341e04550060080425040c1b0514090b081e00e984c200c1488000b400e40103001b825000356102c0c40b8110004c0c40940382e03c00585480300f525502c0207001c80c2e40c10741500001410480400483c04554100386882e5550310114094200000e2001c40032401425050124550703030303a802544244542019845c1d030070059001045c1c2902e5104080800c4000304100b102680b155207220 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 814966807 1250 814965557 814965581
    0xd061d01020c030415110304030b041110030e1506030d230a020f21030a180b011404060e040b0c0304030219080904050901090305091002150f0105010f08041212 70
    0x1500c0702100e41420380c0d03a6100340900b0307040c41080645084602d2082840c900030041b0380c07024500301461552600c00e80c3c078000e0130480740322a50320f50400c0145c0b5410700c0f14459400c20341c0c010031001d0000001c6070070700c50344141083c514605002000444d4500091483d02170318075250142811b0a50718500e030760700050501e880c0402400051118419900040c84881c1c0c100403400c1d9150000d001040010b0503104041116440006200007464000b16511501f0b160400c80b0301e0001141c0ca40e5500c5400001c00d0304040c80a05106a10b00f203242498482c140c06000900402c00c95420705841c0e249262000914500780c9130030002c00501018401e02c600c10100064100c0c0190092031807a01150a4000c10b85007802645498000fa009809c14060010602d81544800349002c07640020322500d4680d001c03400c0154418040c0019850140300c084c1480344059080381c03041035041500043c41c080f01c0300344000030000c0803010700c03020800c40c5400921180300782c1411549000d0b852034010141c04012484 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 814968057 1250 814966807 814966811
    0xf050f04080a020306010806041106030408070b0435040b0c1e0607080c1e090a030c090209030606090c220308030403020604111009030b0c0f0c030405090a09020d061d01 74
    0x9070308100003480c1041038030803800d9aa17241c3c1ca62000035540c440895010702091140300c01030351075082141c002c58000340118045454150749032506d505025003620100c1d4000103c00145400300118000d0031250141c3c00880303000c1d0310701901703946060700481c054509242d03c00a09150444802c01c004550400c40d6200d04480083d40309c030083d11600220b0326a404541d4a2000030282c43c0d0031021a01120007130003107650000e26140100403150460500729030040000030740800070076943c41c5140010180550096590300000045c5800e00801501e50390260b6070701c1090000c200001c00c15503132004a82c600c4410300c03103200100d241208000d580f029003145d0b800800c3c0020f055011603014420707030103111150100704124041c8070405640311001c20008028030800d0000030a00c400041e00700510204850400349403d00040300c607440162a0b020035400020200301c1410044000c55011612150030410200d0640200c0d10701c88841000074001d555401010500904010990600b0350320503000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 814969307 1250 814968057 814968059
    0x90d0b0420010306083f040914060a29122422021e18030102040e0c07020a0b130303030605030a030203040b0f090d0f110409050309010f050f04 63
    0x1c5500740341c40400c40c0d95406601076041d8841c0354081c0c020b407401c84800742d006103000c280507620303158003a525035207006411038001c280c5554040785000c498201c0b202650350507036a0341b801c3c010000322940050440c50840c941001c118685d070b40c002d807030811602203c0010002035040312a05000c2100341032020109107004c80c2e40c00e100020310000c81c2c440d00e01d0350b8400c4080c610203450449030320a154446a400709940c400300e01085081424030b2008038500d2000350400524000c104629011084d030b00130300b100042070059824008010041c00c25209900840c034060400b50340381d003d4803005143c0c0100701800160b034000c54544c0644400200b14000034581c90f00f00c800220214169a8803060303000034105035010072986004110240615455001186481d240c0401d880c1c21f90041c1e00a8490404240300302c00c8a5210590b0601002d80724040144801d40c2c0c0b850141020800e04481902440c035050391800012000012108036460900700b0207144000030300201c61612941045000300071011038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 814970557 1250 814969307 814969313
    0x18050312041a0c15152b0510140610031a120a0c03080c1203090a110a210c270b1504080f010c1701060315030b0f0901150605070206090d0b04 62
    0x1029034000c0c958034110807200002c200410215403d180f4a100c003c0030790b0300b0103400c002c40300c0740d000100c584110306441d851000d1a10340000c644103100c007127415204510410150340303868820386004007a9030404100622090f551111010001c03054a4055603c1200114080d0400c102240030140c1c0064030300318032612450700b16020b030002c0102100a206840d03844000089520640e4401d030340c813800030018030440751101e0b0151480440f041e9000481d0640100300c42c52009403440ca40f2a000032517500c041a0b62511001380b0030180d0020841c2020060f05489040d075500440e516580c002d4000f08801c44503000051401d85004510643d00800050000e4640340206030440d03842d040c1c80013005445000300042e28440b5007804005a010030580040c0200360207a0301200d140d01c174828480d868240c072591052038a00080e80c050f40002d50800c104a01034030240184084440c40035400120145000b10150480c080e14900034810071003c18024847c0d00da1242c0d14030496000481480c050800b82 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 814971807 1250 814970557 814970593
    0xf0c09062215030603020d0605040615031a01061706120f071e051c0605040c090e01020912031914130f090c0306230d021018050312041a0c 61
    0x1209408086410311000d20b4542d002c1c0c80f9550490760050013003903c0d000e4594461009110041048032507030790310721a04c00481a42403000340070710301c6044180700502d0f0303144801c0401c1405038803000401a011007400c2c02d84041c801c840b50420825295a890550001119428440300605009d5144125200001c00b80c10041810500d080c0e40c000c007200e82600d171402c1c00b080d056207100080048800c2c00310040041c1031580102d51207400782c8205c030026a00d450449068403002c40c010500daa4000c03d8014186ca0004691031410103890f0045140425080300080400305140c404400d128aa00d030410b00d201400b030860740360300c6a400703c2c0d20342642c8504203254403070458014448468a44400f01481d280607109078810741d1203801f10000240000da18403d010600342001130b401c41400301d4100010380320460710200c4107403a91503440c104440c80c0e4100315103191941c0000c0c400e034000d895846003900160219820348a071a10100402480c01001002e40d12940100c03004520035100111910300e245 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 814973057 1250 814971807 814971809
    0x9050702150a1107030c2d0b0702070302030c1009170105070233070219290c070b040201020a050a031d0303120c090f0a12060c05030f0c090622 63
    0x1e0141c00390640c0301d2003840c10071541e40c0c29407400301a80410032000468040c0321044a81c07440f0710803444c48403100f100740d00442c0058104150468071030b60442d204001c00c0541d443c1c2c1c4000c891005051251940d00001e94411303880d88000d0103601910443d0011078820207110014000301a00c03e19954444c226442c000c1c4070849240d00140034080004007800340014020910240f91000c081264500c1902040a40c0000c0c26079401d5120b0120a070f6010b22911045d0f918a81c080d00c101c1a140d5080c0500300c00382c1503e496080f1002c00180b0822451070000415602c1c0290040d44041a90340c903440180c5c54400c04420107446440b442080000f01756000c0140644160a40120610050310b80705040d943e029000e96480e000c811800040d8a119981020703009150000303000c40341240a00012405911a582000c160702000705500810712255016035003030f24000b89015032a6183c90210307a03a8101c00589055000740300040c00303200c2660b40d24150b035000041d210804000c40d00d9071082110307401c05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 814974307 1250 814973057 814973083
    0x50406120308011d0412120e0f07050102010c0c1403070b0c090a0501050c0a03120204120b0912090a0b0a0216090504050c01231c0c120608030a05090904050709050702 73
    0x102d440089081c0c0c0c80302401d0b60000c4160070203c4130380d444a81e01c000c0022558402c120800c5840c60f9040c841d070404c1d0084a0300c400f0507101509481700a4440c490030120142c129605681c1400361040b940360744080070008082d04003090345080619455101e04500c80d982c000340c11480e6420901240c0e800940c02810001422038402154584c3c400066550340500300c003628280d0407005a280107e4061040d003031506104130001854075894940304400d00f942c04200b502d00c2003041d400c000031540c0030405008502d00d40117106040040b0900000c80b0b000030360064001a003000700d032182659008201c60f1801410324400315010301d440d83da12078010f003000c440649040c0708650780920154001d1040c0c101c90b035105044061244065041c05120384c1c07061654031074900c10b0800c10f1030400b5542c440c2000030181ca60341c40314503162800e2040300350b40c995000392100d0f810801a501075a03801000f1a02441405da8040c181961242429420884580e100514480c141020094501d5002c40c22000c2840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 814975557 1250 814974307 814974317
    0xb010e0a0c020c1e0102070e160806030105060a06050d06050a0923042f15090a150f1b0510050105330c0f070807060f0309050d03050903040504061203 66
    0x1004010490f40d031014500e41e16041500401c1608604030052204014010f06004481d0201d50b01c441e216052401101c040c14052016004000400d500400d0503030401070407002889281808070006058008a115000501400040082c80291150800001050010300300011251f0f105225005410707070969105140d14241c0d00300c1c100a00c004181d0340030f13641102d443c41503001c149241480b50340401c140c564210001d0444800301d56070380344130100842c1b2000440ea40f250b990030244410003181e034101c0c2c10394240e4895070700d5440e41e02c00f5043d068452142303003101500b0100120700c40030084080020386203014502030007040c60100c0e04080d049907000c0d40c3e00030700c004882c214042110604400c1050803404820b884e0035096041c0081c0900800040c1924210607602c1085482c290071a0f01142c4243c200394800c11000c2d4101c1c1003648001b141e41424003010015030384141c0c60701c1c03e040d10305042c1035564001c614910001c105032000b03400064010440e072501d449041d0304181e600c5e141100015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 814976807 1250 814975557 814975571
    0x14190e100f051e04050a06091b02010501060203030f0c131e151106011520150105180714041a0306040617030406052101170d03020313080c0304030b010e0a 68
    0x41402615004401c3c2e03d00c41d00c0881e0541c060410028117000381c80d84048a44805011032980007610a03c088484461440801002c4000c0040d0a42c0c90591203034043d5041801081012001280d0041e80698180d1105954a1071a0041d401c004040c0c2c02810214104003881a2a858002c1007282500c0c402c00314040022109002161b5610703142c00548400cac1c2121004010307058a0000c08400c1440c2c034140b0031844402e241442104a400c1e0320200420707800303141200c01c40d50004078a180034080a0301d030002d16a48510004060810107000b1500300304a801800684e1a518420385010703251541101583d060041c0d81c007130494000361030052141b07103807940029001061104404403001d810015508043c82d10509507100e0300422400d1110424040c44010400c0c10240150701030009036490014240d046100103241540d09040342003030503c10418840700009040d05003900c02da002c1d6850760303102600d0b80440d045001c3d03a84001c219101030300000c37440300d01c1700400c241b140da81c0402c10441d203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 814978057 1250 814976807 814976809
    0x603010204060507030503100308030c1b0109030c0b090a0606081b030d0807080a140a06080c09010f1202040e010c02060912040b04210b0a020c150114190e100f05 71
    0x38810382c480d020124900b0420800040d010317101466200802c0314103440c2c020754035201d02800b9801201c1f42c18011100140381c00700c00b800300122604140d25040208025a03860f030740901407000d004030180c6802103000000300c0302d04041240c0d0010780c1c1e03c08020701142c0d43d2452800c2e6249020300413060500b45105d5040400d040c0040c2c41030069810703644103200360b16180d4003507a8142c0b020f085070100f40e443d14100f1130080c004415060161180550004095103000030a178140751403d45114440c45007100104051040350b03040c0000e40d61980c60a0507902441e20000d40106420004280b003542417006141d5929004540c05104207a060b05071403d014012001c810984124003424200603c280030900100000d0f44044070791181c3d400a0000464070b030346990340a40801c43e203950003180c0010b0208110b140610a030303540580c1c601c0f00100390303504005c05001e0520503c0c070058020181203440740440e1070041d142500170504040d10001506160440c14040750060140c020003030390b99500003880d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 814979307 1250 814978057 814978061
    0x2130503120d0e0f1c0f1805090901090b160f0801080d03050612010905010621030905040216021008040615051f0e0303130503010522030507031b05060f060301 70
    0xa00414841140e1034407400300606402000303c44030300c0c80e01c0c4c820703454810000f2000b0008080c0c108144942c0504c9900b242100030089201c0e640000200078091100032900403036044003000780c95044648018aa941c40d119500405c0709071006032030300d41c0c40400c2c480425402c00c0469010a100d603503900c0e800202c2c801c181c0700c155080c4502821944000200c0306481d1182c4e102d1a00014018a40c410984a0030880f900b9180c0c2e012041d01c0c071365500c0400700419030b00358200c10100d80080126074280d20705914050007015191181d9801170350005500c0880c82d507140800400d8950040c20118030020341e080052074a0811981143c15a180c401907c80340910940c0e0101100d038001c00480120441901040e41040c0f00900c0d4000d02142d00d2902c08983c0d000c1c809030410500500807030544a1801701003500351000584054108010900034903d4590420b0f1690b80658160601c0c954518607450101d6606241030f414410b4012003080c048100040402c6140c00b4040c0c0ba0810300a5881e14020182 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 814980557 1250 814979307 814979323
    0x80c060901050907140604030602030103030e041b020d051c06060c1b03020d030f021011181905190506030f0a0e070501050a110c0d0819020102071106031503010e0102130503 76
    0x36254400d000400c07002c218010b4174503130480c02070304090415a8a9441d2002d07078000307030811004a00780030b40c0076400b401c06d803145840c442440602d0400c6c1811040010b5211104d160303d20040010000700304101c1c1080c402c003c0034810a42c0310070046160b48080041500041407012a40074124560a005c8018210b1090040d0781c0c00034602d0600452598041d500500c100d0040700a50150080306907190070280316000001e10225040d035551444443c1039068505d004080912442e048092030381f41036620380083c8151103082e60240042c24019440d102172404035400f113131b03000100108002071020401840b038001c108200c024008010440c01d4139482c0e40d907034010a400524284180b8a20b2440f840580203100380d840151403c49408002040600ea000c2d40d0568074800d00162400340c161180c1c40c0302c0c6180f4481d03c021070600e00c49645079440380c1c049454040c411030005c0085813100c4484107502940d000014001c2060944c401d1405010750845400c00c2441c03042c0e10340000b66410007162401c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 814981807 1250 814980557 814980571
    0x2090c03091b030c100f02100501031703281401170a11061b0304031406090307060f1107060506031606050706050a060807031b0f03031b020319080c06090105 69
    0x201c1030314030a80384000302e86181609540e00d807141d40200d0b881500c17040e09403001d980c82036640b408840001c420103841d0000700410800045e2901d4010404a0800317030b4101c00344104010426642d4440d0649603010000ba20031701d1750358941d03000000b00e0b681060f0384050003255611840001a82e641c0f20004150f03113111007016040d8121000c14000151071040c000c1c03441c01d00a01d883e003000c100c003080300c414411a042a044a030700005040c41480780f80e1083c81040b00e40c1000402007031a059880c10340364041d00100500d03072a01c600101200095a41086940c0041d03c4003980c1c6031010390410760060041aa0203901074052940c0d02d03146101c505011800740e0706039443c1c403440c0420030342c1d545008100040180c0000c5a0311800802c44100601c034240080d4012405c1580485182e25082c40604095100040b200100c40c0b080000a0700502500c601000c0b02c0c41c200101110303800070a0400050154015a05000700103031401c01070440d005d0b03c52040c1040c200d0720641d031051891800c0310742c140e54403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 814983057 1250 814981807 814981813
    0x2100b1003050a0e1009060b19030f050a140c100305070e0105030405070b120907050415030f060b0402030712180f14150403030203040605061008071d0d0c0302090c0309 74
    0x4030090080d0096070300079010440000c1c400c00103910301d0b401d10700100c4081103a40d032640ea02c4000c1c00300d0390141d40300640c0c00300e40d40b85c12003007014150f94030070400c4c1c80010404100c9014034002d00000b4402600f000d074002021885503020004500d4403903210142484c4030310742c84c000341000180702c2c0c41034611034407083d2034407006806600700655483c0c200030310440340c0341f18801007c5420660007000d80f0b540e1840d401020214104841400c0c1440900e400440c0100d1034581a5407508902e42420003c40c0d070020010301c21083e4038107060b0084d0400c030308802c0d0880d000001703105075207501020702481c3c822503020800913540c07005249100942421000303000110032014141c081046481c0f00e6176644614011a1651190414030914003001100c080d00030960210800c828451180200c079406001103d04481802e5642d00151828102600b070038108819030190229514542407950000b80c0001c06200058042d0b20b440031000c0c450f80401c030b00032a089404114044074140540b4014140f08000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 814984307 1250 814983057 814983079
    0xc12081e10140a0815191a0607030e221406150a1704150c0e10050c07031b091d0c011805040e06180307020a09110f180102100b 56
    0x1515442c9074071038014580c8031030542d0f40094088001c006039020b074404a505407100b49401440040500c01d088480943c20b800d0440d0000d8010340c1200002030f4400480c1c24684070b1449090480d41121014100c0d0340000080c1d00202d066a840c80313011000c030a00c00420301c41200c481d2106101c0c484160361460f0028140d003034041e001351019024010a1146150000204c0e145066051140409803003d8804841001e05000b41036181d010b200030a044608210710f056a18502080200e400e4001a00070401c0200300d28a003140c05003c4a80150303008900107600d0001d078034500200ca03085124090740c4d10320701aa4690000c040c51718a100816180004d068156480e10056500510742070001c0d010202a0001040b1640c4d80c2c842c0100b002e4101004006600c1c0104188030340d003c50010a50f050361090000c100107a41d0600303520159400b5000124042098490058050042800b0300080303110104031281102c545070030b251000042642155611070115021038100e6006407400e5030001c8211364 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 814985557 1250 814984307 814984319
    0x1b03030f1f1a0c0111040905070905010c200307091d100c2c060c03070b07050f180604080105070807080f010e0f07090f1403120309070e070c12081e10 66
    0x40640b050504120000c541c01711060b0b40d103d15580584c1010010300d90366410b00810943c08179483d0058442800d00c98000c01c07803511007140901c0030070700f201c09400300450b5a40b099101803080d4002055072081c1445000c5401b14802c098a001d542500014803562502c2038410503c0c0c000c10551500e20b40383c0c00d00484202140c010817009020030b810100450f105681b5072034590b10010880c0c0c400040c05542c86a030b69190090b50f43c00d02800b034804110060059050116000b01191041c2200300b11070701d58001440e01140c16801594849203a075403a040403c02140d812150240c0304448907a648040d6585280c01c007484910280214130f0b0311901540024450690340307000f00e07041340143c201a080303196100103410b00042e180e00490f51000002c0c2030040c01c1e0404211103c23901d240c100e400c0e030542c60903d814075690441d40c842e1684d07000c080c40106200c5805501100c0046030407070140c50341c0d0140014041d2100905903407548080000c0c40320010b042088049060040c0c110030552409146400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 814986807 1250 814985557 814985609
    0x1a040c121a070f0f090e220803011d070314161709070609050f030a0f0314220b130e0910021332061b03030f1f 49
    0x3600480307240421800c44140e00d03030001892845600695518440300f42e800b0802011000f22a20440501440200074488134601c007801651140e80d1402d102d1031184481212400d0303055002c00035140c02c000000104040312140b4016280b014024500105506d0f5004101c0c111540d062a000c8018001d802141142e2582491821041903900e0035180b03041506800602656080d9074072101d80c2d10184080140075003010103000241411504549440c08440101c0c1c4c4503120000020b01c0e41c00c0000504003014000c4800600078200b41c10210748030001510445c51401c040c0e402440c2116218100152100f220411211100b001031b4440701390501d414007030390340c0100c06411412980644c2020025810092001d0300c0403d8501c2d04980340d0030702d04001006c2c45c2c0640480784125250a84240f09400c0e6160b040c202c0211040c0e070f40d82e41d01d40042007503140f41c042a0043ca03030325000000902241c3c080c0249114011600400181003100009480b8880c0c80e03c2449002d0403850942a071482c000112 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 814988057 1250 814986807 814986839
    0x120403030f120b04020d05060301050a14161b030f08010b071a0a0f02070b040c081c050d0b0d030e0102010b06181c020405010e0103140109110d020f060c01091a040c 72
    0x402e81c04100216003800140070307a04401d00a08005698908008040c40e0900496402454804082000014950b80c0010841c0010040500740b0310302c841e5038103414402d18154451000e6184400d06030651454002c108110121030031002854410000c100b41c8061007c4070900360f0304c403020288601e01100881c2e4803520082803080d2041d80c03a2103c4802c07500900040200c9480303100b01c074415242a00d04010321008070b420140c566030200c292144102c20152104001c00e41c107081c500e8884d13010303584002c0508850b014060b000160040517004164210340100490b00c0c1c01d0b0028004200184c0600ca80c03402801400ca00d000000703c0d034500d2a0510b00320841e402d070444a4084003a905640106060343c0081e0b0140100c1c4002c00010400d0041c03424100350100103070b0b0020b100c4946e0079110406c2034101d04120301d12031414050244110b5846148400c8945c002030702068480420749012802426004800c1e10001c15201c4c0e40d034a100760000e20300384a01d92250702d580342c4904044c81c2c030a24100f8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 814989307 1250 814988057 814988087
    0x150403020610060f0e011e090f0b0406080705131a071104110901030e03041706010302120d0215090a15020912150a02160f0807030e09040b011512021803120403030f 72
    0x2c020b2500107800d10101c030001d0095648d102e4005c0c50707190040d541c1c50740e940da034010303441c030130050100b400095030100c2c0044d0444c416207025611442000b5030480d02c511158880188401501e582d0001c1c0c0d0804805802042c4c095018181b0b110540c20900c015170b100a0402c402d812800c100503c0658040e40c0109074071403401741100e02701034890107114002003201c13000c21101da10480c0100214a0105940b2842d01c0c0088e001d0081040ca8540107980c6203510388000105400c1c20000804c0018104111000160800ca0602451240e1085c05000f50f2080d11680d02514614501c1c640d00c00001591480c00441503a96002d06e03540c0b10000b1000b5003186428103144881908024003090480d400314503028021080780381c1d1014180307006004c010808880901450800d8204030101d0340341030307296044840344054000c90401c510130440310941c040110401071480403540914a159000c810483c419007901195800303d0000203441403409180320040c00a00c01c001c40c0046144a01003c59034075030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 814990557 1250 814989307 814989317
    0x1d0d021c030626061b04090f0207061401080610180e0304180c030605011e0e1f03090215070c0b0a050909010e0601030b10050703051308150403020610060f0e01 70
    0x280310f501082980c0d545039418000c4420780998030b0826481800030541280701c01c5840c1814401001404095000c0c80c811801c0302691034151b10500f180e00e404907034510b54403840400200c48940710354040300c0400c3c0180c1400744030f4600090100300d0035034640401d40b01040c000c2000d4a0010048074090a0f03640300b640181c0c0000c0c400040c0709035005508a0010030344500110703158004120080450307050340d10881c104031240450303080300c6602070704442a00c0e80a19099003a00c0584012a9400040e220b02c0071074400650b0040000c00c3e8198002d03480300d4801c6558252a0600c041821610f00684c0d1015100c0d980d020340401210b02c140c00241194000c80c06c215003480d5201c40050006031099004184013110304040080303541c0c0c1441940e0140b4400c49039075040043d00003005000e0b02031000000d0070f000f80001d040c9a040810010900104484800c0700e60b40b40b08407232070b20f45003030060f20f04401502c036081c045504500250341c4e1505a039459500d0950800d50113104441102119040038140b007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 814991807 1250 814990557 814990559
    0x13050a090507080a05160302060d0b010320040504050c191b0506040303020c160b1606140a020c100c0e0d21020c031b09070c051e011d0d021c0306 64
    0x20710520150700203200000c05001038260340d0510909000c0c15034454501501d1214060005a030ba20082e122400e01d69640001d010318100010780003010180c11078444000c16180350145821600001c009550064405224a84030050491501e025000120000380782da9014907610074880c43d40400c0486203160f20711200c4809856144c2002820f90b001d0740000d40008018030390719000c005072410003182d036240c40e203e80e10304400b04540c0d00034041e603c80031042c20394005041c4449500240c2c0010b1203500100b5403800c141d40d14900075801000c80d42d1070750161018680c030341d500c41e00c2000c00e0b941480e224070420200f90001c005a00000c92070441c0e0a80d901e82d1801d02c190381c0c8154100413180e8580040c1200c1b010030b0308047c5000565201aa546880340c21140f5503603e42d0120182c1200705400c080c045c070202d9191040c2000e01d00d020b02e01140744440d600c0040c11805401151107140e003100c004840d100c94820207911030114400c0b120242c0d10040040c41c2c60354000009540340100303450009801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 814993057 1250 814991807 814991813
    0x1120f021f0e18060102070303030f021308100501050a0b0301090b04020d0f0e07090e1903020f060c09150723070f0b04090f0204080703060e031207051308060613050a09 74
    0x40c41d1640e4480e0300242d10860502950700705080b018030822812014580c0310b14281d40000d541741c8a50000808254a80101800040441d0151003c0420300880c509205407240ca03040d9461098543c102e500500341000003600303051081c0c60300181c0718890b02e614a160700703152100d40500345143c0b0403500640d08110380090350f6401d12810002c0d901482c070110384000703042c80007480c0c502d01360403010314146446018003003040700081d80c0d0105504140f405d10503044030f080c01e9042c13900306101d401003401070300d042100484e142801019080c8085407040325510b01101c1561041c041c890008101c014160f206070900c1c10b00d0340100413034400d003c1c01c0b144e4081c4c9506d50a0384000340d661124802d000d0206040c024400d07140281c00c2440f40c0c03205c00b1030800c2d240280031651000c0c01c0c070018148669604c0c0000700311505008840d403607850f214442a0b00c1c2071840c80282240c1c010500381240c482031000200f0321880c0417a000d4005e50700100040454154030300d0381d00013080090710502060799112018800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 814994307 1250 814993057 814993099
    0x3100e0a02150a0906020c01021011040b0a02030a090603020a051210053303101802131401030c030501150302090a03050604050a230a060c050c0615010e010801120f02 73
    0x10114072054079a100c10f0404405030550f4001e8015800f950042e5003072400599000030902800c20303503903070302058449103295080102d200350b4001e07004100000484808040c0c00000078000340075141d4802d1581d680ea010308404a01851b079502e400a141006001400e0b0f10460f105a008051703801c0070240d40ea598800140b40c0131078030140f00b400302c000c9110200e808038080c05a4040c030700740045c544d140d46404040490304051500881420300204200c03803403070b01003a13415102c1c106049107125404c0c0342c445941101089208012600003411b02002c11001842070140038101c1c1e600a008484864592900b54082d400840e61143c001c1c0b40104004041031041203403900690081303010b095031640070f0620500003101c80400c44640d01054100c01005d0100207002000306801c00390006540c50800000c0f03034944245152090b0500c02d41e070901c005294080d50409602509807640c1c100c0381000801580c02a03000d10a4078101d183c2c13910500d0200307d1108080d611b0610041807808903204010030044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 814995557 1250 814994307 814994329
    0xa0f0b03011526060102190b0f07210510231302070510020301170609030a0e0406050d03020d08011d130f080708040518012607050a0e160c0203100e0a02 67
    0x50f2041e06a0500c6845e50701400204040c2150f18040d40c020583d03502c2d0f086c000c02010b00b201c0520041c91001a07646440355546842c1090713003281030300c490b0f504481c44001030071068480111030204804009101174a241d0030142c0070020340d60001c4000d42150400103130400b004c0100ea01e550f020410389000a80c207100f20100301a50001c016200e50502c0038504503280051015540760b8000414404109000030683e0020311036481d040d41030108040101d40030304000c0e88402d82081c00285800100760700455040020b0405a40700720b09070f0703a0f85291004000381001003910000c030110101c0e0004203001c9a01d5140360103219004202d1005503a800c515a21084007a03e2200011805000b10b01d8104401e541e202070f105603105855050141003014920280e103246803410750801c400e00c0ac50b4003400360034020315004020405559650004003e0303005d0443d56110f902502e200c0841145005910307404c1c00380c1c1c010f00208154412002540700419030080404034a03c9044d548000582d1980082c503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 814996807 1250 814995557 814995617
    0x120c110a0b010e010816090213090903120c0f0903020607061407050c070803031e1f0602010b18010e0105010c0516120b0a05071d0604031401020403020a0f0b030115 72
    0x16001d0740c54810700100b4214180c101e650240c0082c4203060391055070760350a2007602d07000b070300050b542c49440b54144c20303888140d480fa942403800c01c0c07054018903401202840381403002090034000d4841c0840304035508074803000394201107181d800040c0054180040a0410b5074800c2100044420700055001c429080483c0c07040000713140066404245c1301c05004980c0100303c0080210f06504086c0441505081e07404104074130220588001800701c100001407428410842c02e5820086840d200700902a000034251580140c40001c0c011600f904e09a000504031500550842c440b43d0800004407103a5070310140c240d0f5140f054072401c1d24000f005c5038075007004040b00340551490003010701c3d0002e02004000c0080641070302c0c28007089601c0d42c1140301452000e014074004128901c0c13080008485020380d810140c0001c0a9607540d18884905500a0007624000c5503203075440b03540d44140c54990101800392a03400b440c18001000025543d4241c51400000c9082100406030503403941740503201400e56030f0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 814998057 1250 814996807 814996823
    0x102070c0f03030f03091a060f0a091a0a080d03180501050f0f070201020a080402010e06120406092d0308060d0212011b090f18060e0a0507020c0402030601120c110a 72
    0x1041011340100c131929480d0158101804090241d480310242d10528102c00c40c07108180304001041a5214201d024203e0402840600b41640f541e403020028680c00c090742103100c3c0020310b106410300e0210000702c110340e10840204012105444103c0107011031640311150300ca40403022070009007081c020544964000c000b1800d03149000642400121005040041564810824881d400d07070701841581d0310030340a00b004042c05076004085a881e100c1c40e0b0f0903035a44110001404200002900b148032410f00034201c90911240d209542160b903000c18a18071030207071001c03001d00f000034040e0710883c4e40028000c1081c2091007854000c100e00d191900c0c07035030301e05965910300e060a031520a40503124420a501c0d004001d1030500002c100003400b94021000101c070407045e41000c0706296048031014150204048000381008283d6030041e2500740d6000026000304e1800c0001401d16209032885003505940e60880628504041002007020000d5001001a5950800c01c00c5070104100300c2143c0c451801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 814999307 1250 814998057 814998059
    0x2113140102010c0e0f090702030f2a06060303070f06090210020a06050a051501110c1009170a021f0905060c0a021507020307030803070e030715020d110607030e0102070c0f 75
    0x9085500f0304000c5800d00003800c0104003e500e60441c1d80b141d041c8161041015512100000d03031031070003080141a10b03404001001c83c8002441d0a402c161a810075040c0e810014140361003a407188411950550594014000781001c1201a4002e8040070300dc1c060000307000e0000c0c1c0200c1c45101e50809544050f91090194070700700308443c81210340c0031000386010002c606090a44940d081d1420740c803541000104040705c20741c034400348610200468000c10076400c4401c46180500b80038036034465500904200740086d4a1880081441d020303256005040040c040c0490141d0003200040c8c0908404204e8483e40106240d00d46400a00d008451000200450101841003043c50820349900107005601801f0035801030318001445010b4031380c420f24164a941d101c00f070407030701c051100000582c14030a01740001203580001071444070380c602c26800c1d12203440d01440103440403100d8a03075109841e40000b00250569201e5404070031404031210002d0314000080c0c039203081c51081c54000c006a138a00b800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 815000557 1250 814999307 814999309
    0xc031f0b041401120e061506040e150a060908030412080d05010b04050a050d1205092b030905040c0c0b0a0915020a0f1106070813050f0c0f010c05211314 67
    0x4001c10689400000501503d1174074195180c0712480640a42040e80e011803c500641d95101c056030050400880d066519260414503070200e0545402042d028454030240803410320302c41d03d0400203581400d40150320f810310308900d11207040c00440040e02c03101002d01148414131600d0146074020700e1300030007450b191402c0c02c0c00c000c12082103600051107010b00345000380008031405000ba41400711340c1803640d1950542c2000c5481c029800d490300d90b210603625045101e08228800d40c0e24480d002c2e44d5181109501d48003070004072400f88201d4000b04500004c81c00c001039401741c00b1903000341503a0000c079500c944c41e501c268200c50300c100c60a14198001c038840103126805070106825101c02c3c6407180e050010703100312a8840c08042c01d00f038100000800000d04460040041d101615402003c0350144003020718099110200b200d1024441c020031142e0006540c4502003840c60180c118001c4e002807040544110702d90503190814010018051109001d501480b07080303500201469112011a641404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 815001807 1250 815000557 815000567
    0x908120d0617100f021806130807030b19110715020c03040924060522050909061006020c1806041d1b06030103110f4002030c031f0b041401 61
    0x41c1c40e407130b124814000042c1070b0503a4192042030401c01d80300ca80d0740d400d120f242200380e6442c40e044500c007882149400010068250481c82c41400135950160070310700c152404030280c81004040031464041030050300081982c2c0c42c01c500d000714070480c0040c9018480e00f175407403c2d50002d81c040954285ea0700307513048400001c0000320480203104920b0309540c40c246807000e0464004c04602c040d02507007200b07085e0005a40503940c1c43c05400f0003044490b40d490301c6154640c0c0d0b40411100415042c1040303200141035400080c0c1254094001001d80a24541202c0c0300804507400824140d44152204001c4084075003002d0b07841800000310300a49060a0a0103070b4411035502240d020340a0f00d400c00040011841425000d2144602190440003003880400090003901100c4541507203503d11450415928095548040560060206e095003609000440c82c0c12800120f401000d01c103c01c20001d00c445400ba09500c501c101c95908096129480e440c0c0401141c105406c04803d1400070901c0c0714071982c02c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 815003057 1250 815001807 815001821
    0x10f0501080c0a02030a110c0d06020c010f0c0f030c02011b2705030c060d02130b03160305040c03140a0602040b0306040e0a0f290c090f010908120d061710 68
    0x90711282d01e03003d0b034a03c00035524803420300c03200304102c030145200681c100d09000d80c90b4014002030144c1d4034100c1505000d030080d40300e0360200d9825840d080c66001a10503a0081c0740c1c2c1d0341b015844032002c0e1040c0301d8040d005002410210011035507268901402024211602a004d050540d00c02042c0e1040d402c1841055000106420715101030110810156030002540401d09605032100c5880d0650703265203902902510f402140340580e400c1c1d000c102080640c0c0035600c079000c01072813000d210480510980440e101510040c250f03004942c4203001145640541038612011030b03044a01115103a2604030403038100f42c00040e001d0b0300010a10441d03140c40c0c042c40710341c40040000352580041a070b5900f50040300345030700100f10600c00d0020304480e80c0c990080180b503000800da100c0881c81d0440c18502680d20208400b445290400a02403031544116101c10607982500020841d144100040c80c50580003449018106a00c81202041c0384000e580c02c200713141c0b2118014885240250251004c1d6a24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 815004307 1250 815003057 815003071
    0x3010314071706011e0509090f01060b1c0b06040b271f1d04020c0c030d05040302220b040603110109090c09060503040c0305011e050109150905070e09010f050108 71
    0x600c90442c071800201040a904450700101e1000c1d07480703000c0b40c250740d01da9003941c403917640501400d040100b0f168002c1155848101c0c400e0080040139202e14682040c0c1c0661640c0c410101102819608202a40c0d800318000e064002c120f80d003095070b12040d8524691085170b0700c01c0042c01780c0d001d0400140070b90341404404001141c802201c614251500d014402280710500c0c200404d299003112405411000c0c200720f240082e206558524010201c203030b85410074030505021f40b00704050140303854860410b45003600e900170814508889500000012102003c3d443c6143ca5600d03280544c180d40c8910070613000350321842d01c00400183c0030002400e202d81c40c0e8421070b5034508116070341002540c08041c0c1d1080d615075081c81c60b00c1c0c0d155414154000242500700038010340c0f81c0301507182c030341748144590b0003501d00c030200510490381c0701c046e1002542c1e10032050b5200300c1c5e1902024024010b164028692020151400405001c07015001401c100c130283e0107078003100500c0c3d5080c003540d688420520b41c4036003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 815005557 1250 815004307 815004329
    0x3020604230307031a18030309030a1b11060d02120126010509060a0e071a091011070b0a111e010e010b1e060c12030105040e06040b0a200301031407 65
    0x3143d6140c07200100526000b80e1703c0d880301603000944010100034400d510b0a24181202e403a403404d210510340e02e920803540c0c10042804640c0780c0488a9050216100c01544129101c5050a04505005154001d1603040000707540a025603107629154007040d900a00541200580c0f0400c15461180750b0034101c0459000c9034100000c00c100c103a00054080e07081744540c24000b5014480703805032801e001c15600105c6100c50f900b000c1920701520480500b0340d84000f100d000241c00522041599080a00e41d490592500301c054108002d4407814090700d0030040d0707410a0030400101400442c10f2540407015040302c041c407181040d001550900c104000c81003000300030050703a04404000f414813018003c0c80d82c91501003580304042900c0d81c800b902e03a00f5103030034100d4824000344041864141c20034018180202c0c80d05481174241c0c0d000103000ca005903080715141510351035101c100340142161071039002c2401402103220703200e1980c0740000c0d0300941c054078803240700c030f021030a15030f061400070f0f484245442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 815006807 1250 815005557 815005559
    0x1c0e030a0905043b0111030f060901060906051305061606050105010c020a0e07050714010902030d1403070c051c030b04060b040b0f030613050c09030d02033103020604230307 76
    0x1c488a02c0f640382c18188140c18105042d001d804804910744a100b10304d03440d400d14031002d41c4035240700f000e140200035145104174a559440c060080140c4c0900c0349400140301401e080151500820040c0ba98031070210b2605141174544022036011741c41004a052408000e9000d4424008a4411580500001d1800d0b00410300e41e034000a07180c61046c02a0038200e1151400720301202e00039012604040c0d480462a240070b08203010940c002d21391020140d000303004a43c0080800c900c5440d51807002d801881d0781c2c82c115151401d08580065112500b191a07105000c20508843c44c00c408103103095440c3d035004500c54101d44103200564480b82d1058511500510061208401c04801d0ba01101d401c68106600c2c2d80c0d4030b0000506482d83d00701216192898002800b0621a150000f00f0a01000313800b150301004a0001c204d94a00c2000b01c50064404000c0040c107008480d0109a4100400c85089241e216140c4d0001100c50b8403d0780310110314052a0001c0b06100c1c1c0d1821000311000d000c501810fa61 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 815008057 1250 815006807 815006831
    0xb04060503030a030209180408070501050618040b07090b0d0b03120a0f05030403090f0e09010b010905010917070e090609070f030b0106080603101410091b051c0e030a090504 76
    0x3e000c2c2402c100e05054004c0307110b010300d4445401c0c0f203103081020404800030381800d041c504603030b60142606803185c2d400c000009045080503405440c0d000700002c0141c1c00e507682d64449500f1104080e080004104030244001208648c41c0007401c14000f880c00005800d400b45410103281000c102c100e40d061100170b011218606410901140d066401800e14aa0760b544d9407800300d401c1c3c0c540e0303000410601803c60b004035070174000e0050203204041d840000c0000705200001907504240707038441d050020301403142c28031185121b4150105081021012510050344031160301c03c04500031520141903500907010011401c9041084d10014070345401601402825a00e844c10850390502541050200e25808915280c404200c0908242016841005081d5018038546040304040d60118451b030f06142000c268a10207200f005d07400c0481080d450345000503180d094846030450f40009004140c2032034441100740d41c80c041d5110380c1200002031135440b0384005c40a080d20000d904410701440c507040520000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 815009307 1250 815008057 815008063
    0xa020f060c0307210e01020711040e0c0f2106061801060206011e210605060319020409030e1503060907110a0f06020c03120115110303040b041a04030507060b04060503 73
    0x310381071920381c1300851008a40c00c03298a0240c014001d90f4645a102d00034048194054001f035407065100c45410f0130801c0070401a02c21811500c0101c3e00141c0341c0781ca8929002100d24114130001d001886000360a03082200030a503681c00b2103c10390450400c1242c1071500e01003507007080d0f2007850214161350412400a546103c1405401c83c141a884c1000c90341d56440c0902c80024094541515400600c140c0240701c15116a00300311031040c20940401e000f8500031401c040d20b90382e029400c1100340075030380030040605441c0d0400c1c3d05002048580c0c000a0f114198018030031102e4003601652400d1117000d000c0e01c100000c00d0082000303000d14001e030304490b0120310107aa258009640300c03807501e11130420788000e103c1c40d000c0213442e100000d44000d4070240c900d4000e04a9210b201400d2103d0943c103419281c0e00085050100243c0040002900003000007444581007070013410075a500c24081820306561510030796040c0d0204201096003800c0240d28000c02e01141001c1c1c42c14042140f4003c0404d603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 815010557 1250 815009307 815009311
    0xf330c06061507120807051b160927020609040c020604050d030b010804111302160314070b06191a070b15030706031d0a0c1d010303050403020f130e01020a020f060c03 73
    0x204121001020511113440340341500c1e1230703007011030103c0c901c0755083c02c000760ba59a200c0d1200301840092400010007030202e21816a030840d0080040d40c90030450728481818480c1044101c2c2d110105228108140d242d0b44031f40040007107150010207031030509040151411b2103182d4940109030500030f40d0780d09070b6404016560003c0d07016951101d00310480300020307041d2546100c0981c2e42440811403820124410200401090103510b510b031151000c0181d02c0d180d03211f044400340c40000f13007101140301400c0950351940060140d08040f1b00032510340301c0c0a0a4511015042c038160200801c102c02130103c020310b0541c0040d4400d1440c001c0714a0b400229448804500c107007424141d4844040030a100700604103043c0060000607107021011f5450420300900c5213004070b018800c40390803120b0000180c0c40141d410b0300c0c0c2580b20142010308d5a801c105040d1003d01c0401c0c0c02c4500c0741582800c0c1c61040c00760a0f800384051001503154030f08403500034500b00120801d15050f91241c0c0c1030222404951046079 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 815011807 1250 815010557 815010593
    0x8010b03092a090403031e270206040e01090c030506030c0901060f051612140a0c080f0c0a0b06100f0e04051005030303010303020d0206060f330c06061507 68
    0x4076000b103510360b2222005151041143d04034605204000816030316601c500034544485180000e0542d00e0307003020707044481c3e01c4200c03016000c140400200c0c103400c4c0f03080d01084500c02000c00e071400361205082a803107442a4131801007a61202001c041e1650540030300b940c0548141c0c0200b1914480c0000140d03035032010b1003010140140c3e0309034008414820003c881e000300c486640c0c003000e10002d1418401c4011104556000102034600000c1030310302400403a0b120040c50390303408260039003c0d180e080260784124015022080b040041401c240006d1003200c000742d00034000d20010f0f2610805021004004600c1d4900700800449209601c0341c200410101c0190b0565000600b40d03602022440d5056094101c0c40e0f161001000000070181c1c00213004030b0a07205c036406e40c0c1031600c031401408540340c01d0146160b48805044100e00e1b0083e6860821381c2c508003100c003155074104840c54404e04a41c450144400c00380c1184041105a05244410080a8060080040c40c1842d01c0e22140e9042c0d011802030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 815013057 1250 815011807 815011843
    0x10504061d13110409081e070f03180e0106210605030a060207080c030705030c0d0309170a12020f1e0406050712050d0f0204031b050a18200a08010b0309 67
    0x1000c24070852895240c11018003500401008030581040f0351650403161f052100d8042c82e4516070403550101040c0d03500e05502460029000d061550141c071200d016000c1180410042030300025181d0201c2c10700d038000d210b2519507030080780c1981c00d0400540b14415000301003605052007004607840c00101c0f4124150172001c010b03254111460221102c4c4a248040303c02c9200220300c40302802030100041c0308030640401214402c074000203054056070503400340070f085ca05400e07504900c2540840011b25007a12240381c0b5640c800f4800e00b40a049810140e4101c00329035001c191825204c42403e08040803001d40300c0000c1c2403038a400da0040061064403002420b99001100c10344170280180280e6102d007624000a02a4074414105a0005d40081c80f094070482c43c0780d85a01d101882d50050780d000c0e108040d0800706064100200c0003114800c00f0030400c611a0303240c1e101254030580207100f03a904d40f03c0d42c0b00385a842071203000040c140c403411b0f0460340030a5010002e11058510006989500180c140c000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 815014307 1250 815013057 815013091
    0xe030a09080f0a11060d1d01150e04021806030a020406030503090a0803030f040305091f080613180305180a03050f0d18030620031f06141e0408070e010504061d 70
    0x241c002400b140c086c1c1c09030182080d9087c20750841c064009260038900d05001b199515520900c4018006041c0d40107504010310b144c1000e06646c1250546074009e01c003800b1603c0d040090740c0401d0440f0070301d0b88151516000810b400728249810126100181041070045066042009407036800203009030008052140000b03000020b030301c0701c0401d540f502030300c0c0300003100c00d151442c40540f86480c1220014030850f540c0d55680b40a07900c1c0e1058184804280500c540c50451a9800b50340c03585c031a0318010100d610716101000346035a2000460080d5100c0d101500900342c40f8405d4505c1e220001480d82c00340800e040c0d004110101195409007180e400c44008903501108406a106a00418040350f00e01d0200104000f82d02503046011210351400b001d003134881c0e41e40c640c02181e4030069078064500507039040000e08149003040c00c04041d82c0b00e50200051034160303900c0103949400c0e007590041c0d414401c090010485490644a060b00030010f100c0d280000f0100ca03940d024482d240140660701e22070717140c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 815015557 1250 815014307 815014327
    0x61002010c2a1b0609120803070c0c1205031902070317070c090c0309110f0a0b1e1303031704080a0f030e07180f020f0f0d0e030a09080f0a1106 63
    0x700c4200b070783d410605003081c0841e0120481408101d5000b4400030440d4504000355040c89000343c640295041590a420f43d110aa8103c8110852900c180e0300820424408540c01841400031600144183c0040d5076800c2e030030303071201700d954400100b09055400c0040c0c10000304406000d03c9200030b5500b08095601d561900e802200c0110f2904045400d51503d0101c04025030580c0c81801c145018400b0303c2d9a880c0007104100d072002c1c0101d02e007504a6076800d000c00c03041d48800040c0007181045890118007920b03500400c43d1542048082e980030042c1c60b0010424180c02940d14100c070111140442c5070380c54140c0700d6903414803c008004040241e40813401c0c07009840f80d403140c60740050b20015560700c9039076603c1e80e01e002c410900460041e50702d0180d0f03074a031a04841c400c0714500b50101c6146400e00c85819103090040d040401030071074464030b8400020310030f0424002824100d0407510303000169420404030601d0008d03500031003211743c1d01c0141240045002c08204034000780d011110f9a68804601e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 815016807 1250 815015557 815015627
    0xc0602071208090115050a090c050c010c180e0103120809011b0f0e0d150b0a0308040f0f0b0a02101e05090c090603030a0c030c020a051305061002010c 66
    0x12026041d840300e210581c070740c0c6500118090142c3c82400091001c4040014214002e04c40c40c400c082d0b01a0b4030210170412400550800030484070141844c038200061a1000c5080d1101201c1c4400000c2600d141c40c040000038000c5100509205012030042d50304540d41c1d03158540718070320b1003010301c411800010724a070000d420103036030740182d500c5810004a907144090108000e504034007020660300b115481e01e0781070001c40700d4902e90300a818114503126442d000c40051513009071041e00310014090200200c2d4800000b40010040c003030300102d961f4900642c00c650300500d034011401c0d000d001c016603842c040d03002070420209010300c01d00051103003114100314090840c466203000701c2c5007400108002d00601081b40c038090201564000d040b56201020951203229064140000c10480c08800001c03070f100c2e10701d0b51003080c8058080006540c440001583c280c0e1107001400e04962188101712103420510b040b20711041c854002030041c41c081460261200c0b01ca5519589041c0301400e4031408204a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 815018057 1250 815016807 815016817
    0x9112a21190c02013c0201110307020a060f0218040f0617010b0f03160603020c0a020a0b030a0b1f08040f1b141005030609090f0d03090b0114010e010c0602 68
    0x503046030141059441d01500100405006a000c2010090f011109200c80c40000803080d100030606030f88001150141028142078016010442d981c68010711144401c5000460150071a500241680c4030585406001d0394241030303602442a0050208289542d804000044c1e100300894000c1000e55900007410014211548440b21071002a07012003d2a4810340c00941410b0094440d00d03032041c00041416039410041600c40344510f01d4a07800c1020511a0b400341060196400540b5a15112600003072a41900740d00803048540000060100c2e090f45032090801010041d580b041c2c2d400548078a00c0030059204405506100d24500001c040111281704118000c2d4800300303002510301c101170508400c6101e4004c110728070341c0710b184e5415146000000c100b02c90303055070b548a00c0e50b614941070020545010f402500c191180c00b1064405040520902061900c0ca03500014000e0701c60502d01203442043e0701207808046580099441ca9a1084202400c1413003828111215001441c20f138009101da = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 815019307 1250 815018057 815018077
    0xb0901121806050112020f030703020d0f2105220308090d060212040c0312020c0901140105070b0103060c09060e0a0303081b0703090e090c0f091009112a21 68
    0xa0301c0f0010440c0030040d410410700900030340e1901c000038104010b1507500c02080c003010703601c0000f100b800e500207100e4070a01504c0503c0752501e45443da0146007208600244210b0003404240081606550207000b50900c10000d10b00c0f103105a18036107140c6a0a20904c140b003501c0e80101c8250f0100003d024180e0101c590300d507803084818149152500b040b00da21401400121415009640500503191000074070b5401c250f0000c00c0d681c1941d2a00360001003842c4100ba003141401070900050011030400813909000f14010074010440007514400180184040e4210704140462102000260703151288947c0c16603906041446082c1c8580b00303140c54602060318690307130b030603400035810302010340c84182c02c2c08607051036608081540f10b540e082a119400803541c00d07040240c0964524151401c0007509402003000c0450590541e203030350450040e079582c03000c80c3d030301e115001a05842c02e16205d2152071081030010007150b103001d03c0c1e9040759180c00000400c4410002d5100d500024518020100c0d404466 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 815020557 1250 815019307 815019311
    0x51315080c0f0118051e03060a0603170a080a0b011808032109030a1d03010c0e0a09020a0816140d1508071d1009091b0b0901121806 58
    0x340d59203419581e2000000898028518080800483d500030002d043c4003580c281088030f94a402c3c8010700852000030201e980008042915100340c5480502c80b00c1c1c010030421402180c3c6070f003181094600e65644000f02001d0308000c000e8040d0703155110f040380b9003000c8400c02c0400c2800e40403004903500c450540781c40340382140000340020420000401003803d8045110f11240c1c00e840312240350f003428411540c02e8003075003013048590901446110085000456400540511240c010100e82107503456040100400c4032500c9034101c629007825510024600d08100b5403922040303880003070071050090302e03800741d0f07a6522140c0042030307008110503c2c19001c6c0410700d5484002504990002d00740411320300e0300d62402c1881c0450741510204a00054912241621400b1a0b44078080c3c842c00c180140116a0b400008802244c185680e02030810018091019240c00980041e81a000d911483d4040300c1424070800081d01280d8002e84405a582560b400018010b003001d02804598500300400a1102e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 815021807 1250 815020557 815020559
    0x1b050d110706030606321c050f090d200604060f0e0d051614030a0203030103051c0e1c05010e06010815010509011e0b16110316051315 59
    0x95802410205211020800c4415855841100350304035030085c002d40b00081c0d8030380c01140881440451480d40c0b00d0030001c00840000101c0101551500000c8064510030000b81031014401079034080e1a420884503501c5200d141040101699a254695006c00a0001040e416a400d11008404061401e510010345000f4030781803038a103004000f07a154021006107081440302032008005061040e500a41d01d44502d00680c8044101400369a100100c62005816100c0c01c04d0304001e20241410302d0320381e002503881e94114540541000740320f85a440b00f91900b5540000141e42c07020310301c068550700750744180003000c0039090141c40d28440c03040508207600b0700941c0c401c0300000044c1750b8100c520308000e8640c80c076941c006e152000300080c0320b090b501803010340c014015a800380829000000105e002c0d103208664806140c0d40c690010b40003a0040c0941d41000030601c070010300301045503d012000f1f08400a00c000382644603844500880d80135007070801103504007004542c0424102c2e4000c1c44020512 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 815023057 1250 815021807 815021833
    0xb0612090a05010911010828180c0b0d0b0603090712030c082d0711090703061505070b0606040308070615092a020c01050a030b01021c0809010b03030a020d1b05 70
    0x221751050700050006421000040d0000f02d06403204205010f108024210141c450500344003a15120f2a41390310800d0548009000801d00650340c0c00400304121059156400c608821088841d030a03402405008200204411b001c40820f8400984001d4032403070300350a0317540c03c04641d4036280750b50040148200148210800c459240310862107840c14002561074203403070781894424041d1010061403542c1c084041940307072409501c41c0f54000c596241c00541c00c0c1e40c03003001e2200300c0e410b9008000484c000142c1c490500c03400000050340720006441d003d140525681e251103c0c2e12600501a0405544203d80c221808100040c40010800039030b0030301008100030b1010803890a00d00705844011105200034014900100d030b0403101640584a450401c03d882c401900a8044840c0450440c0a18100c01d07030503001c08690611400b0103a5030b10401c80c542100e00700c0c00c5540340020301d40702c3c0d80188250141c095001800440400203450002600e80015200f050a416034880c0103100f40500c4017207442e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815024307 1250 815023057 815023073
    0x21040f030f05010b010302090a1413060e0f06190902090f060417100e070303140c031801030c0305040507050d0c05030f0312100305101e0623040b0612090a050109 71
    0x12240510001c000403141300005500700c0c8036921076290021401c501c00c005c4204d031461078007544c0401911121341001c10301c021703000301d1b801da4121940c002b81c0c0c1400c0c01400700c20590030582c02501590180e51241d00e6041c0107001c05039a1144840c0b20f0b40004008010b038580d00b0a004a50350301038090398540d0344a824a100107202196500e0080c0310b1200944031b05500d901954002c01c0144000e80840350840d20100d4400c8015251900742d030008110700358010400b04002c08821040c0c007100140c4480d071000043c107844006800710b0406007480c05100104402181c001c007151001ca03a082240302040c030b0000d426542541c8415030501905060101c00e06001c001070a403000300ca14681c41c3c40da103a000720020b143e118040640f403039020700403218455845034400d491201034082110b1000d000380d088901516641d4218440c0024040100d1041c071000300b0a814014104803401e003e00c080d21008502240203a2044921038412840400d407905820302c03800030003c0d0404000d210780b00c141e060000f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 815025557 1250 815024307 815024333
    0xd23090d150e01180b0408160b10030c15021b01030b0a0801090606081b0603250e01021c080606090411040e0907060302040305030d05180f07180501030521040f03 71
    0x700c2e5500701140c01c1d8081c480c00241c080410781c456100600354640740c841c09aa07030410206007020000c0075075201e01050043c11594420b196542d40b44111a0951401c03400400e01c652258641800c18540c242034980c01180200c2c019144041c140c07041201c14004a0140001c200701e284c00483c2050003150016042d04042c4109004400c14402c50f642c419601340d5902051000881d16201c000c221203241c5021070007940c100c211285140c840720180c514002042c03001c40f0403000801c400c812a4203041d40c050041c8400702c200c581d4050250241c24001501003100100403e10403407000075207d40a0751181e0052440d95121545551504d464030320f0305407105025182c0038071ba403150020024002d4468021102a82c0e4410055801c0c50340c003842240140c0f40c050409a14682c0321624200f00721420420f0140c840b440c0401409024a0500300240203a8100303110000107081000600c0400d0002900000001d01c18045401804028800c3c01c818003e80e0031145003608a11400000e10160180e200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 815026807 1250 815025557 815025581
    0x30207050a05030d0f0f0e0405072615090a020c0313030309050a050f060904140a2306010e010f0504090c030b181b09060d021b0d23090d15 61
    0xd5507603110b200300755841c4070f5098940c00291a0100241107070380b00744240c40034807850382014036000d00c10304000f0b8241ca4085400c0c100041c0d00150441d545075030020081c08042c80303012071900c14200507640d81f060035105c410030307400b8160400108010130f61541c12181c04044010903a0340b141c000d0103d110792640c40740310980000d5424030b400700f50342c6422042c0302d0441303500800d201404500e90007400190f4004450441d8090b54600615010800c000d64451040c003280000051800d40c16120900c1e03030004030740b0b0502401c600d030100300e43c50340c00004160604209080107091000f882070100c5091055400ca5040715041c0145001d4458145d0880300a600e001c880c8a0015441c2d9008100106000c48000c3c0d1000d280d0020501d540b481200140750015015003200e00d4030034211906416640400c0745148050189020072401d108107100c0c000c1307400220b00d01644194403240070701c0b07500c0c4081c1141c504072400004141d0391503660740114810199000149402c00460340200d000201040040301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 815028057 1250 815026807 815026819
    0x210030905060a0c0219020310110a261b071403031006031503021e031b030c0a060509131b0206100b0703050f0702030703020904211b020d081603020705 67
    0x1142c100c0140e809a0040001545e000307104108030003180c6085aa40442c060307030580078603d507601c8a100780c0c3c0100382c0c02d02031030168507544450151b4002d1550001d42c2d40c66030b40e4400c1e00c1c000351035860b81150300c0d504002c001d42001400c0144954100e050311520400600c104100f9002036004940407001d54031405441d15401019a51150240d00361100c0841a4850038030f013a1007400140741501e030f00c0340b60141c11030560151882c00c1005c42d1038020f1220349500c100c0098882da06c8189030030018090040008d42c1c402588510303006002e01940180c0500354443d2041c42500030b8800070a5014140c0381005040d4410f265583d00c030302075103821013550200c180010410b004200030501e48200c4152941c1692514a1310001601c44810b5401541080340d141c0a0540300201607581d40f0419400741c0e0040303202d04245a0000c03c0c103440c9520454001080c07050b10000b482d1a01c120510500725160107403880d030720300030355441c1407040c0e03102c0c1145c1c00360141e49002d078100a241e8001018019980305640c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 815029307 1250 815028057 815028061
    0x60a051003090b1008061314070f03020a0b0f03010306020c19030f030605090702070603020c030408010603081305011d040506010201110a050a1803022407050307060b100c12030b030307021003090506 87
    0x24502084d103402180d1080d07100501040d040c1c1f00c50b4003948441400f6070320b100190280e0b046034034100320403907102450340d166604052007980360107c1034034010004130064031700c1c0c032031902d50359100f0b030105100c044d0266501045140e911001405041d0801c0040317402c4440e2420246000391500d61070b0428640040c1c940301001c1890708150180398041d800302d40040200d5413030140b04501941c4018481040e0b40401d2000003868075007401510041e40c07140c001541c5440b4551984003020485900007810400143e00c030324507007000e00f21006c42d5190b06070390100d1140d4403074005134050f0000e00ea404034071030300002745074180710351101c05018540c045503241d20050803000341c8811007254900002e9440f580030300110b004690000e10202d03061054200702c0b4105802612080e04680042c642607032429150f1150440c0e42c0b60400820844c440e081c01d15250b20300c4180c0b24444603802c1e4000c000d09141da168680d14175a41c0c00c0055917002a4010309090049452513002030144c00c4058080740d4600c11070700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 815030557 1250 815029307 815029321
    0x120e030a030f36140d050306100201020f0301090e01020c061f17060a0b03190c1502010203070e120109020405011205010c0c0809010f0c0b040606210b0f060a051003090b 74
    0x1011011030a00015070f1408000302a991050304801011985030810a004811415080c0300c4010314103690740318543c0740c2c80e0000c10300c420030b0880345507002103902c10051031000c1031060056070306403028100700003011052440355600901c114042d224152140d10200f01007140014119600ad099294007080362035591a5218840c5200c01a400c98580090001400072102ea40c03211710528001411107a04900d520003080102d82c440e0420307501c8051009060202c040710442d59400c507941c0d48021031031850b241100800341301e0094601e6128812803181c0c0d071611a801d4005a61082e00140108001c2d42d40c0c0802558010f035040c130444180d402c0001009016014010b140e00c5190440710f0b0514184003000115940d10400008106200c0c11040c9507021602d08001a4031441c45100c000640ba410b203801c0080ca40005060001c0300110342800400151110765030a4106100380901441d036190700000507101c090681005400c90356114500b12405c0c1c2c160040114140500d1001da0b0a4075004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 815031807 1250 815030557 815030591
    0x1204241e11270a03020d05032503050a1215090902090106050708180a0312050318061b0d0912051305060711010c150c17011205060601120e030a030f 65
    0x2074151144040c0910014444502008070040c82c0c0342c005004030f205540782d0740040c4880b8810780d010b6869a1002c1000038041d4102a082006215140c0650051500c5990000c00300d20a07080d210b020440116040004e070051a00b210105030f5000a04600c050740b01c0040300010605484242d10480300d0303400002d2020300030401ca41040f6044440c2520313080c9214107044061710041c05181e00020807010005c0032600002182d103404031580d54050383d905088680421a0701100042c07001c41c2c00c08030a219250a078240303107002282e45c45200c55103034806030801c6001043c50745005494031500c04a014841c076070001c02003000e00c40703458201140c00c1d120380510450b80180100140040004400d0000c9903004641100c587c6100344a40785908031440310800c1502c4c002c85201e40891042c4191b00d011540b0700d28128050201840754031000c072079a490b25546c0d0390014140c0f505100d034800d10600301000c25000000305800c0070003229030f600751020004004007082008040000c1c40c01504c485800160 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 815033057 1250 815031807 815031817
    0x30711060103112133090c0121050411100f051b12040e0f0a1104090b040921090501020102090d03080711010c080114011b03080606070f080d0e031204241e11 69
    0x46c00078202d601110005440d40d103160b8503070340b22024a11552030001c20f40350091234802d40c490140712042d040d950003802034809030024100240000301d01104035041d4860f003600c0c04000c0e000d1800002c445000d8110b410040400e4415406500c0010f003c50031021015441c1e00440c0c10b101c01c0340b040d644243e00482180d0000c420094861000c00c420005543c450b0084031007008d00402c0068001c49568a54000c0064000c0c0d800040304440f01e15444180c000c5074480c010321080c0001e40c0352048250009015001102c40202804401d502081a251080c910001a421b201000f04a044107003403010304002000d00c102d680c0000d0170f8032452031552242d0031151400020300462201700144c1d60f4283e82024000b003503103402442c140f1400001c2000c000701240c80c01d00a4039101c6d40d50071030100c1d100a8480081410340b035a4001c00100030302005801c0c50301e62058110451690a0a140c1c515003c00034010185540c281d081c0b078507100c8004444408035602c00014038080198884403840706e01d00d070080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 815034307 1250 815033057 815033071
    0x103060c020f07030f0206031009020a0c03030e0c090a0c0e0909060103020a1a120910090c150c050a0b091204030b07120c05091e060f030711060103112133 68
    0x1040d40004014100b1901858010541d20001080c02c3d2b03d41001d04126002407010000045d450a03020044c55014400c210a2807241005414142030003008034203c03640180102281c540d07119503101d6682d00c990000300c0070150041954000d82080121103580c2c000a0100f07030f01c04c00e6010384c005489058201e200c1c1c0507009000702c0609210094511552038440281341c1030080c05003d0301044240410b219440c0c0709840f0f04810048c880c103103500364250080d030b2280e02c014007454545900c0484c80000d40d00b50300344c2e84880d801c02659682190309080219104601003810f001040101c01c020303444100710300c80e204a81d12408441c8000d045142510b07000d80c02c51010500800c033710455800d040740510200c0c20680d401c02c0344a00c260010030003c1c1c0c44681c007005c0840c0c0210a010896500089a5008100d40c0004110035415500d41c08140301005191501c20041d039003503801d41c00f0307200849840681340d5074141d072144000504c5542c0e90040b20301c82d95001000c040090354410003407800e15801108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 815035557 1250 815034307 815034323
    0x807230601060e091f090c03060807260a0f06022d0301051203040509011d01060e221b09061b1e08070c1e170a0303020f09090103060c020f0703 63
    0x15201080c042c084c18094907580c03101c2c0800e06003d04040c4c0c0c0e00c040b040104a2100002054032440000074201d60190f000013003544c000ba5002c1040301107000261110b900f42c401440d07450715915108929040b55a50300030710901c1141c03d00424084071303901501200c021440803d44002404d0703405a610441c0010184c1c18031000c0c0018411400c14080e401c1d448144130088038502901c0700d0006841c842d007640a01403500068110a10320b03a01030071228010245424448002c40256000507400c0d0b44490505060412880f900c00e500d03144c64110f80290300018581c240c0c107038810540101031451f02e0041001041c29441501034044410204200c5035800c1360f00c0b040c3c048a1400f41c00d412981608041e03030303000002c1c0910808a544103458400038010680b0700c0703010007159019020b04980980c052484d40325468490a0780310270104000c080180d00d40340040c1d0720f680d00814600d1602682200c00d4100a1180c0040100703c62584081c00420040d02160401549046007550303403c0719004c0100482d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 815036807 1250 815035557 815035577
    0x270c03142206050c0406090501140d020a140a09050306180709090201030e030406030b01080601030e03031807080307060902180702071203030f0c120c110a0f0609080723060106 77
    0x4010a000c484040107810000100c4a119100e803000d581c0d05868842da22000003804002c0c050300b00c40404003e1000b030810b101c21000e4203070340d0b00c07050089170800301c441c80e00000d544a0252003107615039146101c8018254541d01142d6000704911003034081c09020740b0650003c503001e500c051424001e41c000a4008100003800c0244540240c10000c100720b0502d40c4030744410180314011f0010700090107090340c00007420283d142c0014078000000e02901d05052070241c19108a9102004a07907000e2815500385403180d82001c0058544540c6512034a42d90002080e0305041200390340122040383d000300d0702c031850b0640c400f445d034403562819a1100003591026a08003c44480b1007030100141307000f0b090015800d00000c071030074145c0b1820070403140051494524041111410301c290a00340c9404c0c64100c1841c070720009055564245403101800015600580e50b0030450f56801030489298172030741960f00d50300c6c41e01d000203680b0154110340d62100300800316110150303400a0198100c0b0301d90b0780c038001c503a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 815038057 1250 815036807 815036821
    0x11220060d090602070602030c0a0206070302030c0315150a03150f05061903090804030b061002070501021e0a080c0d021203090c06030a0e010603051f05010b031f270c0314 75
    0x28101e820341202c40c3d80d000d000000c0400c0340d91018500c5140e120390200e640d00b4203450000d04210001300900700f4584103000b401041d41d03071141a658403048851101c00304d00c04980002d6000d00040c4c11200d6901800103900c0c100650540000e1440e00100301502c40094580002c00c144c8095070203019004001889140240c2c200e000c81d640103401c507810b00081000380740c0c40c1c8940c039902a0f0802d54101d10550240815410000004000c3c03071000c2c40588055424800003e40f52410056602d40c03032415682c03c0e8421200611070041c200340c1c0100d2103507852210840560711107403015031500240c013664081c0380d0441c02c0c51080300d1082244c0070103441214101020000b5a42000d0b201f2409603646a0301015002800d04c944000746009800a1020fa02a500010030940340701d0b0840503c82d00b0500104140cc00d0782041e0b03604019610501c0514065011a01c129074036568080d0310040c5120350031500340c0000380c440e05000f0001d09070900452010302d00a90540d0700495448840e11043c1000440d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 815039307 1250 815038057 815038061
    0x60d0e07091112070f0c1703060a05090f19110d0911031606182102040b0f09060d06140c090901060509030c01031d07032f0d0f06090b011220060d 64
    0x182103003904121006c050542c0b0703110301c070000040b000e0a66400010a04c00706262902100c0010041201c540640d0300d86901c5c0094080170240030110511408480150a01d0381078004038203c05100c070002c0d460300301c5044c0b482c02802c20400c042c0d403c010070140c03401d2141000b05092160211001c0c082c46078170b02d001070441300c0f6101020507900c02d0389144e8001c0340c114241c01040d410b0000a036092848400d00d0b0041108482a040d03080348104150340c0c50b01500c3e250300141a9000c24200d4007d00030600c54100440509002070201c011425454200403001d094000688a600c1d801e071002c10080c0e17242c4600303070307020311880710441e605d540800b114036100d40c4280c01100d103000f08074007050070001e0303503034146803600500f45c0045513009100001032001200740b10950a1f01100321522910050754500420740c1c1000a440140c1060000c04850b400d200054000480d00c9501191030001581c2d280080d0f03404159141c3c04032202000102c0700e90a211201001c440011001400585004580121400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 815040557 1250 815039307 815039327
    0x60c0304120e10030c0801090b0d02010e0d02100f0206130c15200a0201020f01051006140f070b070807020a0809190801110a0f0c03050d0b060d0e0709111207 69
    0x100304429014501c15070f03103408403800522000380d1004940c4841d0b45601508401c4141c1181004920b0905c035441c032a910202441155902030900f80f00d070082c0b01011503c1e049800e200607400407480d05400c14400e52000440440c40007590a44450351039046606084000c11040034194914058090024840000720304030a4003050a04501c21000c0c056241e003008115512002030340c004212034015940c050000c0e0210103000c0d00200443d192040520902600e0344c058081080006200c54070811200021203841850340b00381306890f02c805181100c003414044801400154000d0081031440303000003409014182d000d01c0c002c0c00e010811040c0080c07a059140403d01c80c1c1b21090700060515070a00c02c3d85110101802c4443d40c40f1008000940003110f1140c08070100031440c09011301081c1d111042e82c200f00341040d0b011521400c06800030b52036018502000a41902c2c10380c16480300307540021410121054244180705c508000e9580c2c4040d4011414000000b4800f0000030780107a00c1594400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 815041807 1250 815040557 815040593
    0x3080601020102090a03031809050420031204080606040f020c150a060f080f120a08060402090127030507080d1205040609082205091623070c090608060c0304 69
    0x44c20401901d0004250746116803060300800e003084440030300b402003100400007030b118110042c06a0300305943c803e00842054a002081001c12850004159600780004da650650006070652146d84a81100703480b150305035811403013141b41507034008801000c0d0003500e10702007000018104600e804c40341700b0f0590303c1c014188002c007507a6040102d0084c1c204004e0703001070021000101001101003600c0c038501070240c0c10074031710710304140400342d15254840300043d03000d001501e0240e140d0007907400607280010152200810021200008100f8590a6103a001100e0140c4201c51040eaa40c8810036102c10091301440000740740501501c00388102e507044980c01a02c41ea800040702240d580b0341d410513801500d9601c15980c081c075600c50440d5003501d00c0030040c0c4011200c2c82c400c3d091003450043e92001d030000f14418014141102c10010300d1009445000100304164566078884a1805c10341306141e40c0100c5141030326000340419503034000103078548144101e80b1000d181da04c440d211107080c1506007070a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 815043057 1250 815041807 815041811
    0xc0f0e0103050a180506090609070f03080c030f0c03070203100c09050f190b0d050604064e06240b0706111207030c0c05030a050a05041d0702060109060b07030806010201 74
    0x24410340c091381c207008060314013403000f901c41d030704041032440d040c03807400b80130304503264030100003031103505068009541100d92044103156501c69402d0400d007940511102d468031741c00040740b0f022164001000524140703108506850a6074901c00340030044950210300d500c00111101d80500a07805d0003c5203501c0e20100500e00045180304400b025540d0303513035030808907180c800450850b65141d0f250040b981c114004072410701002c2e00f0300800d03d003488004400c0160001d601409010410068408510381085034070205800c0c86505241c64080304000c182182c0480c509040400000e920300d160010221511005081c010f02e09400e05446c8d411010044c1c5100d0b65400d00c68000c0e0740f000c0010001c0920b15142071a05142c00d41c00501110b1a0388407120511032611120320020b4004000c841c01c5840f103040c05900c858581d50102c91a0144d9000081562258064071a01404001c05584550110f5080702c2e100d0303880f208144140c84161103a1190a0700a2189100180c02180080e51041040c400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 815044307 1250 815043057 815043071
    0x1009050303030a240302030a0f230304062d030902010215040f021e030c010315080a0f0b1f06050904091a0f06060f22050306040b07030c0f0e0103050a 66
    0x80d003594015582c41d048580e41c2e845596a401881104011070750030244c09400a91542c1c02207a00c2e01001d510003001c10540c1d81c255402c000d00d0280e1100d44e110101d12020700c080071101030360ba0300c0e400303805000046410074170b0030145114500c0140c2040740455814004016510320194060b00131040c080307056000e04102e04040c00c16820308988580c3c0900390301103c2d1580c0c3c2c0140100c00386400c016107070360b1101c0d51082c0c1c1d860320300041861180034207207400a03001d103190f02036940240c1680c000704818019086081c0900c889000803044c103a000301508002038079015040152070a042d01d03d4504544a21000c00c8040d0251000d004021b90142c404a061000e50340c1c0c108103180c455810040f0300b5042014449034902885050f903010300300751001483c1500b0105469414000c02442d0781c11442d03030301100b4082d0811440304030001c04000c0d0841d0580d04041c81c040c10b0303881c0216400000039182480150310503229240b108105d903200c0c1c448044205880004501800c002440c103c0c246441b404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 815045557 1250 815044307 815044309
    0x20a0903020f1c0b07020102071203091e031b060b040c031b08010315020d060e0106050c01060e1e10032306060105030c04030b07140f04061b05150405100c091d01060e100905 76
    0x22b0340d10180609540c000780c0c1e16440c0c17500e0030454001d000e00b40e0340b00700343eaa20040040c0d00300010310304020303020040b81c00306500d51a04a0160226920a070380090030b2040a0390615007540000040300151112450150092101102c640070244005400301060045880003011290300900540300c1e0441f01040083c0c0f2417142c010000801c0c0d200c08001400010803017482e40e03080c4104000307000110030a1855052180311500148445003011140c48880070125104810003501c5500030b541c00140480c442004811002c2056010111060103000c0c00001410369031141c01102d101e8046a65058201400c40d211042d42500081648007408601c0811101851980c00074224648045551540d12400e00e40b0003080130701290868909601154100030014001107030301e00c444012607400300401c2d0765500b481e510f000d080c90442c031581403401031a40415907003e241c13070094a001d40049115a12403401003c4001024444c42e4001280101c915180b0310300300d16880c82d0742c046841c01f03030300c3c440e10380c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 815046807 1250 815045557 815045573
    0x3180a020a170f0d0f0e01170406052502100207060902120102030106030f06030c03020d0224070b06031f0e0705040615080705070b04030c02040f020a0903020f1c0b0702010207 77
    0x28000c100d54400b445415004180c04110800c2429003000260620400e000c40c09042d0288038005c110078007811008220705c5900c00e150081c05d00143d0100c80040d801c043c100140104820307909002c5040340319402a0000d03184140210358849551700038003012000c100d40000940000104455540e1900502c001585c2c0e5500710102040e443c00006907254500384014084580c02c01c41000c45070705054040000c104c41054071011207405540b60046620b141c0f0000d54441030129408080b44503025242d92420810400b600b0454850440f40240da200d110400d5510032000803006020300544039890f42c4140141c10032172112820b101105c101702c1c4c81f0030010b416201c1030b4008800194030070803000f904075800810140c02422034203280f031428200d034031080700c0654006e0001d001d001101c0708100464540c0d521210310104401c80440d150480c1c1680107060710340a1000364800e40c2400c4020341ca03850914010a00e401e052025414841c40130780c0c407100900c074000c0c800d07025035500b801144089a400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 815048057 1250 815046807 815046809
    0x103030f0c081b100b1c081b032106012a110310020706061d010e090a1e020a0611191e0335010b16140c130b010503180a020a 55
    0x28005840c400325034104134022941c101040910034000380708144805401e9510f0061040d0f00806c255a42c0e0205241070000d081b0041415450fa2100261801c0d510080c1004a98040410a40440151505001100d9211511780e0818440700000f0149004030000c0c00780c056480e06c1402001110910b80d00060705060301000d544070f0254001400100f04140c500c02c1300301030030981540044c50030005c507640e08002814080d1840030020440480c002c05005c1005144281d44090f649000102e500042e850204543c00220b0203240072410200e182c5006075482420802d465008014008034203502c0c1141d05a00e9109485c10340724004044042d510300150303185c00310700070344a50b80c2d4000c280b040e610320b10200d48040c00008805005031043c112007008035504490403066055181c201140030342040e0800f20200a1044406e50b0794244402c001141140c80e21034212562040c80c03060020700e40030f40e042148007a0004908000156541e004080580b5140201008842d8499240d9011648032150b07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 815049307 1250 815048057 815048107
    0x19030f06090f060e010f0b09120724020c0f1e0d0204050c0c0706050309060402040e10090c05030d0c08030f071e1223152707030e060103030f0c08 64
    0x25000c00b88400c600e14038404d030060446851041c001450003900075541d001d494011440b5a100658800c4010010000700c000f600d0058000070b0300c0407a040d0703225020002040d02e01b001d4010603201880314502000c051004100103041e2814190500c0d1503060b1404441c1505540401407000c1e03140581c4030ba101e4544240c1009080c540c0d10300c0b4810486180c10780c2035110000300300c005c0003002160300001c102c45030000c2e0b0590f030104451306102c035064104001005028101d52403d011002031110f01e003024822110150160b40c09000a000100d1781030090310800740400104202040c1c3e0307404200c0132a90b0100562800c41000d1441d8410104026002e200d48000070751029250350b43c420b524440c10914014a100c0888030640b14802c80006020007011828030201c1d10086807c40c3d00c030084c100c4a5844000b40c10000c2d909160302d031040301030043d940000001c2c68503d10620800d0000340c07450507240c050b00ca040305411403850032200d030380403084121491407041c0500341c203000403060300100c4410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 815050557 1250 815049307 815049311
    0x2121003020a1505090603130b040c09270b0703060f08060a14060d020f03100f0608070f031a0403020304050402120f0a020a050717090a120b09010219030f06090f 71
    0x11540c010482c03549126001403400300580d480c079540454021049130703215502542c0311501e030364a0050080840e684417001900b444c02000810041040d03558120b4241d4600e50010400744030b003401f400001402803200c281040c010014207030f010a00e0068625444810303440c3c0850195216080050b49901e680d116040d02d80c80002405102c200c0c078001e03581030501c840940d0703407545402d9000640f252000f60b40a40581c650000c0c3c001191001d010071510300f004d4203010b1100c1044860703458001c0c4505d10518803e80510ae001103807440e02880707804112034201c81c00020121855112080580300034004034254030041000007059202c0c1c0c000340c82c03468003a21070125103190281b07008502d40401406e80c01000d01c100264040f9540010958000c0382e0064281d60340c01d52801c00140592240040c42c42d800756001c8800200c1d010590401c24055100c2e026441042c2c43d4100c00609034051005289100340d40c10780041c4c6d4851180c4d120b407010144a081c0031030525503410040d402c90b000c01c610a86407503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 815051807 1250 815050557 815050559
    0xa15200307020c0105030402010504121b080708010e0309181e0c091002070807140d02030609010504050d090303090302010f120c0509010f050910030e1006090c030507021618021210 79
    0x2d8060240303042d40d000a0803d646107141a500003000b900c52401040c0f0720320071060b0300d503041c4460300544040c641c00c4955442440341c0c96000782a80c3d50240c0c03044c0081076081c010074460144000c029038034000c0e80a4010414480c801660070b07150307200200540c050400c280040d40100d04112491400b4148803e480c2c0da840060201380500f55469602c190f095500c010000c1102c001e00140c080d044843c0050002040c075400c4001030100c1044100295061248500380641c1e402c065002c14001da10400454924120032801500c00b855240f0010300462241d6004101650180c584000480c80c14a003406074520b07070001640072200e1030860b4000040011508070000e50b00000e43c58015138240c14001d04113110400040d41c101050942803042580340c1c41c50040034181000b01c1c15011b1101c040a0200c2529101c49200034241c440030035001904141c0440c0c440f5002241074016003034084001d84125050400c03060004060314101c1460740e80c200102405649a00e500034001ca801d003c2c2c00c5401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 815053057 1250 815051807 815051821
    0x411122a090709090e10090605100609080d0503071e02060712110d0207021c03030b040b0d2613061107060206071d0a090207060207050f010e0a152003 66
    0x10504000085004640c1c9809104010390004104011102c90f4600811007000703d0701304900340180421410f110340d080249803810000c4030f400080c450601070b0034520100b5034503501114040003620031448590000c4a0740103205e4410b80065500440500740011900c0000310a00c0c16201c00c0d910360401600000140310302c10358050702e03542c070b50109500240b010740080110b64440c0d00c103030811000019400a0f44008540b80c01c2d0303c0e0b6404c090160781d0804280c200781406005040f012034076502c92403901c1003080c90380c603000c0f5401d81c0294200d4200c480100500c4c030408d010b080824280d0029030020311181c0101412840300740083c0449607a00c98801184844a0f8070344100c942200066400c480c081000a5900403102980c94040d08084050701010002141c810bc1c000d41009a0141c00014810280404c94004202242c41a02220310760010502e00b2822a08140465011600141281404140c0c00509542400890038000031808103462982c1030000701ca220320a1307810008400c00100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 815054307 1250 815053057 815053123
    0x2040e040609023615030d08090106050d1101080a0b1903140a030e010507060f050f090d0e0310020906090a09090506090c0d02150d0e070f080304030b041112 69
    0x1000c1032501c1c4074000c203414007000301035203520084e4810300c48880360000b41e41004554000143d6080140a807142c2c504080c1009104000444050010750700b001c000080c1804e000d0030800304245c200c0010046070360442c0044803c220094144264241c440303528181581c1c8504180d1090000e500102030268554501018414002000e0b0145034011600000109400c5042c420806609181165882c08a868a00c0c010500d080c0c00703940342c1d450841048010f581c000d25880c09142c82c001101d6a6140d0b0704011507045c00794400980c0c00d0b800c441c2e40004c0d140801e80191080d5100280300909066148000c95240703512980b2441d152a224601c60041c003c00340710b410740003503440d0050300c2c0720307142301c80891104520400028000d0031444d03070f0b4200d07e83e01c1000350356071010500020310000c0707891080300342c1d120864001d00e0103004003900f0002e1284400002c40d000ca90380038032a02850360b299140d070190361308213199032034120b150300d50101401c00e024004203454168508031001000080442508 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 815055557 1250 815054307 815054329
    0x3030a0518040f20031009050415291909051e13060509070e0f040c1d040c060207051509060f16110402030c090f011e0504170111040303050c0102040e04060902 70
    0x41c011304005000d01031400c03880100941300c1d03034440030a007525240340982e12074146444090000e850704003ca0466884080035940214059040a0b0400c0107102000200740542c3e038221840f2100b5801040f9206040e0080ca0380b018120098520080c800884982103602c02c8a10000c0755098400388420404607104040e08950003500610040c0c0c140741104500202c098041c0304111030620025040003142c0103180090328220070088075100030301d03082c280c01c030382c080d00e08403200003030414040b45140c800610304046070802172221030103428a5207407080644c011100b060704850100056894800440014440d01ca031008424003028a0760500300900443c00c600c4d1482280100240641c0c92147c00540e45c01d650204c40c00380c01c00c2c45170001a40e15480e402c91b08040425035070007400c0410707080000f50003210100b204001016003411a003a080760742c2c10120382207058040c04240003086c8508050444100c440d4001480e2540390128501f65080894040f070700b090315290340008605200d02514 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 815056807 1250 815055557 815055611
    0x818030a030f0f27020a2301110c01020c0607020d06022b0605100522090c0e0405090307030c0804080604080c16050f060a02120705071a0903030a0518040f 68
    0x225031101c03401c82141e115907004010301c00143c4c40e00c000c0195941c618082000308054598031100542c56400030644590002c003040c003240000c90382c100e441d0b9012408484240059029041c850004020000303141c0014034141e8200000720100c1000400307904c01015002c2040d401c00c09140c5110240e0405880c1c40f02204818034101081040251500c40704d80c40d203141141030154681502c58100703955466058003031460b1203912140024200020750101c1016500d81d940c00c1c400c07c1d281020701050300c406a541016540c804c000380f01c0428070880d605207800344110103852409548541c0c0501c1c00606a900742c07020364000900604c00c0300f04002d2800703100c1c003510106441c5490500010405180300b04540d006e41e600095001100c3d100f4020581c00049480f0310035261480783c2055a41c034070440c024525844440c0690130716054400c1c00b55082200020f00842c035104800ca8201c1c3e0b66045016184104da09568154005503070303c0c0990b081c505039100e400240e044003000500c0001a00708410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 815058057 1250 815056807 815056811
    0x7030516080c04020315040606050405040b152a0f060610030e100c121508160b0f130b030703090c1e0b0c03070803010e061807050304030818030a030f0f 67
    0x8000c078100115005050030030480b001038584c0e562041c40744848607483c980652041c50000c0201d001030300400504252001942c04000c82409041401000d040000c0d000303280f21070501001c0c128480035442c814580000080c03440c0044105120b00d4641542080380003c0d540140c01040660305002c4001201c0701c174503140c01d10001e8100fa0300039031142085520400e8641d10381d06064140d5024510705074156000210401c10301018112a068240c10741c0100c84150181102900b0320300c4180076400140c03a1141e010602d00b00c00505603108540c00040031080484524500086511500c400740d40b280e4010745022420307110514006100b0503158000034640040d00c1d110100031340d8403000e41029624903040701c542d10030072041507500d54010040000c0070300100100100b06021030f405024050079050382e40481d0303950504c109006405040704c00f500010414800100482c4c8520106500400501100200700440a4050782147c0c40f481a00010a0720351002c00c0f0b5021080c420b00392650300183c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 815059307 1250 815058057 815058059
    0xf0501060e131109060a1508150103050f280603051b0114040b0309100e0a0303060e010303050304150e01020f120f040203032727130b0106260907030516 67
    0x81ca5022400385401d03d4000d02e089030000784141c03508800c400280200c0380364602c01d80f1519400400303040088038605600c2c91000b43c000d459501034064130f80039000d5102d04184940c0e60b4003001c0c040303624662a01801300400c0213000b69254043c030403440610302940240420a98809070ba00e41c0000000d8070904000c540981031501016030400d0780c09490b40c0c4080290359460f03000800b440c1044000b07010341090701d0545904c0d81c0b4040090000c003514403903241400311a9030703480c101500c21403d01c070140c04100c0400001d80001c3c400d550241030003140e0600001c9640110103003d0881c1c001040882c0e500000248040032480f0303085c40300f80c5c004124851840c01c0c1c9032983c0400e403a40034682c2106d90029540c420300318044980000850800c0e0050304010040e110030204c2201c1028580350b001c0b4250315040480e41c0110100140f0500d26004090f2207100e9203000c804541400b0b82d00107500380c2816904007003c4004111501c240504000002084103d0030f60806c2414900d03644c1c1040d0741d06ea81800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 815060557 1250 815059307 815059313
    0xa0b0a060813030306051801150302040602280609060b040b2d0a031b0611011808220e180616081504020a02010501150507032a0f0501060e13 62
    0x700301d544101003101019907030707080e4901a000340030113812940c0d1000f5045c2140c9070900c244040203048441425200310020041c00c02581203200c0c40c041e200040e000300002101c094000d40354245a00250140460960071030b88940003110382440041398126240c18070028545014040d5018142049403025070180704800c170041e04000d48482903035071045000710305410b503403a21003110085410954001d001c90022080c0317032a41040740104800702c1c4030b000b24180340c240705205500603240108900030003d40c0303680301c81c603a0313400036842e28560f86400100e05e6a040d103c1480300c0d0080258030b0981c0c40a0400640c0c81d100140300030310031140da0f0b01040822881d09100f819a440e064400c1c201451103854010b01d84d180100c5035050a80c016000045111501d40d0541c46a8100c07a401700d045400901c200070115502d1003602c2018002490200c50405068944c280031142d00040d00c210007a000140d0f907a554074808042420789859555407003c0003d401c01da502954015140c10000b030421441e0340d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 815061807 1250 815060557 815060567
    0x140f0706050f120a14040b040c0f0302210c0301092906060304060b0109171b0105191d0a0b030103060614100806030c04050a060f0b030106080c0304050312010e0a0b0a06 74
    0x14209480c448551010461400c03003580170b0701d84010204000040ca1400d4205040340110544048840c440440000a182580d85000e00280c030f0b0300802e0780e00b24a02045201c40306170314551622041c0e008910f105042594244030300346906116034018081d1040a1010001c046d000c1010034802010050400c825a52a6012240c0c800e134480030015500c51b130b0400484408401d070b00803542000c0c5415482040410014562550703080352150030003030407103480044515001d01c8552a005240c044d924445190240d440820804100303000c40d030302803d101d40001d184141030307401403801040000040c0300b400180e0160038050712840400c4640c07910003101149816840355010020015034802180075594180f00307000c40d0040007403050041e410f14102c000c008103260f10601460700c1401c5400a03400d003200098034100d410940781c680ca6583c40200414886d80020411541070004104000c490f0141e000320700c5c0a0314907034600007130b1071a000c0400d004030b850001c651f034030800c1c0f141c1041206903880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 815063057 1250 815061807 815061817
    0x60510050604051021060806130203030a0507060e06160809060721090b0f10080c030601060f170c04050a0603140703020d02120f07031404200d140f0706050f 69
    0x80d84c00303c9110300c410004484000d02d0030030602410215003901070494905400007020b456150307080d54016114600d03e4006800b01c0b03034001390581c1040c01015807960007030029081c868010540480d20f1840b8001b03550400b542150f10030180404100c28920440e4403240040d44039a10034001e0245040c4018060306120420710000d10624034480e200c02d9414ac103800000c1625846140c0e10041d00b0318190341c2504100031902e03140860464040010b500000103007001d44421f01802610700b69080401c2203403a4038000708040b0600c032400200311541c4991442c0c07070380b268080b800f80549035402c02040156007841a44064109424416000d020303428504c0c0e1503030051814100140d4039194156100041c3c021814100314012160080084503800503400903c10000c4d0350782000703500f0f0b041b0102d5000c0032041c1c41c081d01c449848000c1d81000c011a045040003200c0042c00740308480c2c0700748c1d034060034052081c0706000c050300401c0c0c038024080401c00041000d00302604040cdc0c10179190701c00103d258010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 815064307 1250 815063057 815063059
    0x307080a17040f020411120a0603200109030b06010e12030a080c03040302251a070210081003151401080a14030f250f2015030c03102106051005060405 66
    0x1658031000380c0c100201c6d00300c030301d400b052503211281c901d000503108004001900c01600d401900840c00ca050322921041300c440f034101610ba2442c02821034903036112035030380181700300e0503c0010800c0000d243d440000131b550400703108000315074070704c0c00d00002410802e001d0700843c5081c81c01e10502000913004900c4140407502e600000100d02031a1403500030803c12030344800003c0d080c12100409039010200108601402581c9159900c0268401100c1d2a1030803190708051840001e402d02c0002c0804043d8021001e03a602c000c03400204d900401d8000240c20f03801440664001c00101080160010344444080c0310a40610304010343c0300b078a01c080340304100d10442c0110140c0803410400c0c9182c0003400c007503038000861244044041c90b14410850200000f114080c407461003000541c41c109038501c54910b4140071072410f64136405469003c9400191011100c1d40d410b03880480c100e140d005000440441028000f82c010721a824204100e400c0544404459015924181b10071340f6494212821150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 815065557 1250 815064307 815064311
    0x305070303020915030106020123040f1205091906031406090106030c0908011d12090102030d0c1b060f0b0d020d021203071e0c0501020a030c02090c04080307080a17040f0204 76
    0x580c10001130f49400344c030414088030440200000c80c0540c2d055102c01242c01d1034400c0036a07510044020b160074810704460080180024890b240d001801c4508003143c0d09060f820300d28100b4500174001111401c40ad90050329071025098204981075050280511404201c041020f087c1040404140074000c140030302421315889a035000e039410301c9000c101d0010007804000f04451110002d2175901c0b410018404016481078200f00280100690f040301c04000058001354682605124264060702c0000841028072641c0d210880c1c9400b0080c0404240900c1120000707410b14010f078030300c800c0315250031046014185866020006071651045030004a40488500c4011000c0543e064514072905000a01c100782c06500c00c2c0d0b22190031440c200d00d0b1407090140844070354442c0012030b629002004d003d03000070710400c045400760034208a600c2d00700011401d000c3c90180c607a10031510390b42c09164100c84040c00010340007000e95001d880c000180310b41941c241d02500b80360b10350f42522680007001902c00c0d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 815066807 1250 815065557 815065567
    0x13060f0c1704080109060219090e01150507050a030e130b0d080d090210030b13050903030f070908030c0a1401050402030d120f1103061908250b040f09110304030507030302 75
    0x240d0007002c0e10010314407800248003014192400ca000303900010300c54900d000041a10b81c03040350180c80000103640400c02400b015070329103014100d055078604618000c0c005d003004480301292050021004040c043d46601300781d10003003810311100b21404c440c1c03888140c0c60628000e105030b0350080e000345890b8000003c5601c1d03030b24552454006194182c2e000f9400f1003e244e2070070041c1e816820501403036004030380211940390180242c80540300110340c004100d0300104005040b8002ca00c0340640c200800785001c01025480e040c505103150700100d13070b0340807580c40400200104150407900101d12164140280005d05003980400d50350700300c402c0c54106104500c0341143c02c4141c03a90004410440254040c460309013441c2c00e151069109951450007100c00e48106004181c803100728208407100d680043c20382454031504a812003901c0c2d52030880c0c1412171300000442c41040c01c05030000d009040c0d40d80c9001403508041108031016194412009501881040040380c1c000054500c0c1c80d405040c056960 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 815068057 1250 815066807 815066843
    0x50a0207030f0516150815090402121501080c091e1303030b030d0e040c0201050417090105120f090d03090305030c0c1608010203060301180807080a0909050a0213060f0c 74
    0x80a186032204088548070010786640742c8001c0b0001d40d145c1e520355112646074203a00002c50084071380d405030400780a0010034010304040d00640300205034130382540c69103a40c1501400840c1400e0344100229840101c800c42c0501d0002c00442e008043d24203928550018110f200140341c0000380350b4652031800b0714030318082c107000f03421800c0e04090003816101e2400b100d00c80a08a4411030385514000d502d0304000500543c014428540920b1700100e031005843c00d282c0703650086505c20302019042000c107010306480d03d940c04000078010f200e420080c0c007003481c0c0490a18a40402c81562000701410592010086078200307080b00e400031000403000703540383c4074134001d01e203440480c281040f21440c0101c00007c0c0030310103601a40c0030f81e0084000b40500b1442c1100d5600d105014a000780811b44100314003000192000010480400c1c2410001c890582d034218400841c0c00c212030034070b0925000101407a00c1c0c0760303108088003d42a1410501c141d0743d0706000051a141000a004202c6140d0340401245 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 815069307 1250 815068057 815068063
    0x1e030403050d110331060516060b01140310060f170f0717090601060905040e07090b040e0d05041e0612090305130f1703030f190b0603040f12050a0207030f05 69
    0x1001d0817120326a01d010036151603100d044101c0b8030804482e28000c408902c2c18410412119203580d5403000300701c0e200d0303507843e08002492610741c50f03814020300f102d002400c505103401039403084603e542010b1200d86051400390032124140380c4002000340350494841d42c14070b03c5041c181c02c00e00038000c080c40e5542d140400e50304062a800d1401c0c25441440800400140000d0518107944059403840c0d0a81d03500e00900c419511f5001100c00d41d60883c00d424020802c56030f016002c100c3d00240007041c50800c000c825130410300c880d615000003510004051242c0c0325224840c541c1c08407018402c00b110f601d041c0c00144000ae05d001501101602c44400314141849203003552007400c009242059001d540e14500360b0020403a11403c03640c0000c41a9104040c100802504d10807890340640c05070f42c0d80c400c040c0c106103a561441524025507650b00740d04994490710080c5100318401ca100740f021410030700b84040404209508139081060402c031200055601094520440e5070291440030900c07524501079007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 815070557 1250 815069307 815069317
    0x1302013006081608071505030a11071a0c0405090c070302120310091a030a08071b06031a030604050c061b0a0825030e0907020309121e030403050d1103 66
    0x25141c24a00701180c90400801c4045001c6288456240680d036505180350300c0700c1c00c038402d858282041c003114100c814014801550b1184020078000303a0b483c41c130245074155030080042030320814854007a01c41c560010041442e000300c4111142e42c180b03464200090081200140000c1d92020040303401010980204908041d04012010b01c584900d44104042021107961280c140319500300341c03800c005401c000d0050150300e0006400743c0090a0651614981c9500ca5002203440d011125103a11054401d1a0600b0251543c0d95000c5003c0702c0c2c83c469501100d0940c115140702c2d8003d8020300001a40c0064100e144403800d9a01d241c464010200c5031841c0101d0003a02e8a46006d5042820b0401c0510001800d0360700c00c04c00d28420402c00c01d01d464520384560000140420186107540629251036445958085520700c1101d00e0421803070045150516100b04541c0039602a00b04410f0441a0700c01c030120b8401d249006505040c510340b1560f0303883c1400041901413100150301c00c1c880307000c2401213070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 815071807 1250 815070557 815070647
    0x1b06040b0a0e090a0e07061812021c0503070611031006030513060501140a0b0414040f06030f03120b010c031d011b080309061003150e0709060914130201 67
    0x90610321309050740d03c001e008402030b10201d60060001c0400c03824003e051803042d0384034a03404620315600b41068803010315925001641d10402c0c4002160010201e1072015012030721034000780d5103a015510709003084c2c504400c0804004401401001002c8440a18000031104c46103070200d21a1291490700080b500109000782c0698104000810240c1d40140050708002046d41c41ca10b2a95844260000c0360103580905040d0510302444c5c0c444903c2c16800c41c1181030f4081100003030282e40c9a03540344410060300b038100d011072030f1580c00074078000c10351280c841c65603001e003416090b898160f41c0050080381d081080c102124101c41c0d050450b6440f030142420340d407081c50b2030110440e503d8240301300c140d01700300e55086003031040c3c40c00281c0189481001400703c95115a04071f0340002505800c40141180100c00d41c0b1714482c584000442c04014000c20005043d120b400041581844c000b01c0c01421b401440288101c2e22030080d000142d0784020460030701a64480e1030031030a003e0380c103504a2420305c03070502 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 815073057 1250 815071807 815071819
    0x3070b04140a1d10081b13020c1207020301110309010b1503011203050705100e0a1101020c01052a010c0f0909060e04080304050309030d0906030c09080615030c03030d0504051b06040b0a0e 82
    0x10f4107500204406c0e0280071142154007103a00e1900c4082c010a9115274142d40742c01c2d4204d1103020f4a00365041004d01209031000f4004102030301203100710303481608215149089a0345030700e03c100305d50602e5401c2540c021a2703035034081d24541c142101a0440918000000d0403c400041e19806220f002d10a0b00750464844400703014005103002102e6030758100e842c00742c4080104200b14900366000041e211049170040c0c40e030b1801c0000d0480e5407002d22403181440079205d07502c0030548612032000e2003444200207050b250090600040c0790005e180a6194000d0900c0b240f030648103211070070b03c4540007580560b01c280495a03958507403508030b0450007400c102a802d8807030348010b241c2c55500a682801951000d0f60100b159911410048941072041e00c10486a50080404982950f100706d404407901a405400c42d10000b43c0903020178a941d00500c903410130b81396664140010010140245075280e542c030407002c0f0078a400b40c0005032951045229a2558080000d4243d00701030090718860407480c002820 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 815074307 1250 815073057 815073073
    0x6020f0c0a02130e0607030c03150609060f0306081b060d11030f0c03270a0f05150f040317070903060f05180a050c0d0206070203070b04140a1d1008 65
    0x310358410290000300c0c4200c003d085114000051441103003140c42840b0028000b41e2901c0c0c1081d002080c43c0084c4400305921000b20002781003e03041c0040003800544c1e5100704061401d08010000d4000d600010205030605800f0020a10006400d0a00003240011005440403080000d08a03100c0c01c007164092604200c01400d007400c40001031807043c0810b1561084903510258107103002d120032107014620911031460407905105500c44d120358070720309504480b2102c210383c44503103070800410401c07142c1d075000380f20b4040140c1c104015590803485c05038810520341015540030b00210500800001e503840080d00160384907104e540411f0065400c40030421444074400301c0e100c0503060481e440550410300c049007a40ca9840020000c21440c0c011001e8100b5500010030001035440c4103c060780e1103c800d000304070140c0d400b0300100c0000c1c01c01540740baa8551910a04e10358604214007580e120703d0000380104021a007500d807802c201e03580001c21f000c950351441010004460650400d01c014404c0c140c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 815075557 1250 815074307 815074327
    0x70b06190b03090a022115280e15130f020312040b0d060503010603120302070323130623090d0512030106020c030a0b0114220b030606120307170d0f0c08060102010c09050d06020f 78
    0x201c02c81502005109456138100c4100105102d201c0545215501041d0801c106000c9216033310009000d030700c020259190054044241140c941068100c49480440001d01c0402d01c83c503846007000a2038242c0080c0001e03440d684030091040c4a40001e5418140c001484008162203a02d030310600412240d40018280d8004078034000030f401029174610003080c000000705405010b4985045c0703613070306441100002841c1240080c91500460002038010020035050b10000708284078040d848402c1d030310303c1c1d5101c0d031503c1e4009203403d6040290a003c2e4106210800200c2c04c90038030541500c16811401c51001d24070004244c2c0302881c0304401c000071008415442c0300100301d1300088440a4201c04542450711288108656203804a051440c01d5008010100c0040c40507000d16a04c0c001401c01c450410402503221810340e500c1c0c0c0e030720210648d81c039442142c005400501640e0050001e1000304065141c0b500054400000d078042c1900c10584500c0207000c000727003070b0101d900c1c1c0361070301400b60784a0306801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 815076807 1250 815075557 815075561
    0x9120f0a022209080d39051e27090411010e180712020c1c050f0d1d0c0109060e03030c01020706061a070b06190b03090a02211528 57
    0x41482016070030008680c84c90700c43c034101d003070112500080c100c6e04542c4180f503002d0005c840c6090300c0c0501500b070200b41f8041c005602042d8000082504140e0f590503503075203140c11400074903000c04001c503401007110315a03201e28600c168455031051040400f0b54556005880c00c03040d103250b2640c000041c1024000c07640c0c6080324a0b00034600d54441c0d00602e0b00110440c0241c0c000d0f500654880c3d840f1240115910851001a80b001d1940f81809481c180000f0110801607001e1040040b40306d0301c55500a82d0100d00990782140c100c4410060324005107844002816004135200e000108607010000c54240e9030140119040120b8410086546c2d641c0c9103800c0700942142d104480c162900e58450f094021000c00c200c4910580c0900e0315445a0b035400100072403543d40c0c501109601c540e03940e001c102171400c00003d41c020950b2000425800c0c48603c108012112011414100400b0102110b25000310000d4031b403040c2001c1282103240b130b0747c0300c000e41640369610309640200d411011072a211032458507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 815078057 1250 815076807 815076817
    0x30e010509011112100e01030602070203101a0f011b0308040b0603060403090306020d09020406030b0415060815060f0a06090e0112031e020f060c09120f0a02220908 72
    0x110009100941e00c0c0000182290202101100d01c41d40c2003100c1803103001e1036804550b10809040ba64001e0f95180c99a100302d004c000d1700202c1d1041d60000c2d001044d442e04200d00d00d03440380360b81010300c034182d90042200c10b07134417281400501524294103026413aa0242c4111070f409110000c4412140c0c640317045c0148088404c1d0b5059403546c3c40000810030f903003404104030f4403a54264541480e81032071503640390300a6010020700b0301400e40c0e41c83e00c036006a40741d00908000307500614955501c5e04180c20041050000c0700e00380d2000b00d1602d1410031528002041e1241c92101e40680d00103590341d203a001c1500401307006005640610840004034080b034001040c01c080d90401002041d81381c0e21614941c800200c80c0b0005004143c1c920443c5450800d044054104130000788195030010300d4542401c1e2030428203441031281c4030004a541c81d41c90030f180011a02d2044280000e000004503140e22035118180182c0203809090715030220102c1808a80958280841a00d000c12450600f800d040d0746d03030b400c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 815079307 1250 815078057 815078081
    0x1213030b01050f01051207020f0d030504060b032d03070b0a05010e01060e0a0e0612060a0222030c091d030d050105090f0402010e10180e041103030f040e1503060703 72
    0x1060001c142d81c10803039800c103150a01a1141490142000d0210400003c014040390444c8500c0203402d40f010300a11204000c40001e48011409040524120054406004145000342c4c050f20a00080e0b10021800c41070308a00481c40a44040360649542c2c154491404050080503600060005882d6150305c014104e4046014516180c0d1702e4200c100c420b0000901007543c0700326007800511021400d08081500900c009149030000c2d841e18808a00b4030008550304042c40d5404030301e02c107a04042508d2100d83d070f144501c05d18400d86c2144d079a4038440360319000b0020101d0340c441c07d41c2d120071040302c50b8145134507008044948503500c08080c3c8000d041c00b400b5003030080b10f1090100c1d0024000f00484e500031a0305031219040d8070882420320421030a80500300e820030a46c032404201d00c01c49507044102a02010700c0c020780302e15080c00d1142c620b83d00121040d000c2c0e0300800011144942580a44041d142c03507100c0144641c41d10040019050b80840c1c1190b854022035051207040c1d5003642c000e810000c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 815080557 1250 815079307 815079323
    0x31023090c03010605070b0c0702100305010f0b0726070f14010c080c16031809201e180a06051c0b01050403020118080d080a0e03090a05040b03121303 66
    0x52980c640007a140001c0c4110004145c083c0107400001e0540e0301c0d550740c0640702e0840e10341040c1560b00020b44505482c1510320200b9560001844050744128080b8080d28000d900305182054964404110191074021200d01085080709000b020070040110b84034145c1003500840ea004c80350500b5500e0703020342d84884a10f903103010031154107c0c0c012030b2403502c64021095144d0903c043c444c6846213041d00d50004404205035409030014518a501e18480a041101d1000a00190301c4c42461006840f00311082c4208000b804040f40c01c00740c0c074a080702484c10100b681900d80c171500741074807288690a044c041d4016203580d0b0100d291a40503014002c0d510b10380c0d40c1d20b03901400006080007140d8489030b4160018400304070034800346d40201562100489000030b140020b9688040090034486e00d0f5007580009010741051007901751603401340d074a02c09841e001031458051800001140300e9014030800f8040c580710ba2440a07196002d00040e0112080c3c0140c0c1555020380d80425440c81c0668082160030107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 815081807 1250 815080557 815080561
    0x904020307030c0e0708011a0a050703020703203f0a020402030f150117010603180f030504031b05010206010315020c011121060303071b0b071a01090e0a0803102309 72
    0x4181c0d000b40043c4c0d0088c24210528000c890f0100701d605910051082d0300354400d5040020000c0d0a0446501d0568200b4101e018507030380240c00c008000003101c10003a510208010200c454661040c03000c41c0e01503030404500340e5900030750b54140c104042040003070340c407601c08420040c025940c580281d202d1082540e402180019600c01074400814028001005d1351418006000690007507000240d40c0c00580d0010440002a695020501241ca9812400180003040401c1013000c0034603112604079200b09515249414080000d5030350405200180c01801a50903a041c4601a98110f4411402c9400240254010102820115071000140400c000d104072a400642c0d02055000e41c0030300c4008000c0c61400610740c4804c2644140e14001c012503955001001642280860080201500c14110052220813040403641c000740144e22401c050b038100740c012042004003082440c1110f510004c070703a8403074461403002e911204603600030503502030002aa00c400b0403042042c1c00404141110104129 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 815083057 1250 815081807 815081819
    0x7081002030a1112180f01020c0c0f011e12020702060c0106031e08160501240513110702040f0e0a110312042103020a230106080712020904020307030c0e070801 70
    0x51080c900646070407400311000c500315465405c441d051102954045075030340c1c0c02c49030000342240e0201e02c02c0c0c20b20f64800d10a40405003011035210208003000d0901c04501c00b40700199100c5202103115a000308001d036000a40b01c4000707581501c11090300030f42920f403030340c41d610102c40c0208898042a00d0a8800c0c00c02c1c4500421800c46103140d05a201c070000381811000c140c85002041150021102d03552543c001c0510080038a40c007200030400b540c40115818542000c1c01180b100c4680d403041100d040c54440e541d040c908201322520f00764143c0700002d800d803440c2d07290340082c40c000c0e0341031040c0d0091306c14030804c1c0403030421445451030049054502c4c0407800e51418140d4030451045140c800060241d4081042402c40e83e000d0b402e01a0064424204080c0d0f41d0604945854155000200e006221f0744d4a00909107d11000f0304016401003810600b0300c600001030300c0b43d52070300a00c680c42110000302151424030682d0300a5500400822400ba194220896004801c0301d020700051443d100004034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 815084307 1250 815083057 815083091
    0x171c030213081e24040f120522030c0e070903060c0c03020f030724060801021204050d030504050c13180809100e01090513021309020d11072307081002030a 68
    0x941001e4a40100b98220040c410010034004000f075584e140440d040d0706c0800c60300792201c040450301e42d07545551240c8030845d02100701d240051000da815415a01880090486075104041d40c02000000180b0364a08604442080703898100070401c1e800e11145844194000c100c80e040ea40c4070780c0030b0780d440190000e4855a680240c001c0a003008500c0f2004221a001d05040720024801e13006000c0359543d100e6482c1c40c05da910100c035045c0c882c01c440c0304000c03c4c04801d0000188030403603407505020a05280d110240c0e6298216a0301e4401c654510b10228846a254407405000d0003800d41c9180c0903100e402c0c4002903811901805004005071203044404505c120107503c0680c005031a40812642854180300801c10355070b440c5d2004e00d6082103101c101c1e804400c034001c0105035071000983d507184164074502c02e50b4140c18154001e08130a0002000282d41d031001e03500690741480d41910b01800701c0308942e00d0062964400b07640c501428040c441c9905054001790700c030380b058090500000726003809000d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 815085557 1250 815084307 815084323
    0xe130f020309280210140a090e130b0106180509010e0f060616080904091b03170a050319091203090209070804020f0d020127030c171c030213081e 64
    0x2d4400803243c0b0b11801031528901107840c41c0b0042c80e2030110220260442951039000c02c0c0840042620100d040069800303c41e0343c140e100046288030400c1c40c2a583e185d544031001030107280d0603c41003050301c46140007800e10701e400400c002041c135030841d41d460440040303808003030312601030005000d0001202c0341400c50403907035075403400958403e40820a0301d44030b440ea0071807515254032645810300c860100300007200c4640d501c22015202c035011482d40c541145e80000304103003d40c120109000c0002c0c600d0304102529400790150b0007022100740052040710003405030300380c001c00c0a0070301d801a40409606a21814085200f50356011460302c9116041d1032440d000c4400075170151703c103030b0340303503540c0c14400c185a9295206041034090341200b444050800000e00070540c2644d10803880c1001400f0f04c1c0b0014400410003607032103242ca00701099025072100d140c0360703048101100c13903040f28410511a504076106117101e01324142d00143c40c0c0c50700607101d161849004488003010240030710010381c0483c2c1c0e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 815086807 1250 815085557 815085613
    0xc0616050a03150504021801020105100f0303120e01050712060603050c0a0c050c090a0b0307051804030c051011040305010b0406210303021c05090609031303030e130f020309 76
    0x141c185180610304401070505900034003420a16003200085645407170000c0e012403d40c0da1206032400c0303141000207017120001041c0d0224408800c2081081a181c038170b00d1400d43c1c0c1c0600d405070244606014080207400d1820004032250318181c01c00c0030443e0300010041d41d000c21040180a0030340d030b0b01c001f1015284240c1d140c4500c04420000160388038010812910443c2c8143c041d83c03482c040720380000d444107100b25400b940054490780d0341d02c88c1d46024403d17040644000c5400d40d202c8144880c8003218440c0040c40241800501922281030040810080305030f5614824244a4070450590103000f607003092004544943c20035010116503c1c00e4050441528005d140192009413108a4401d14412111094090690030071002d0f01001403468003900700c2d01c00c190040380904103800d40c1840c240d0000e0140340c858209100000c21020450300c0700c0d04903605850140280e40701a40015104200c5c265001126490026020700c64281ca401031480b030308900f015154610b41d401c0300300344484510441c031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 815088057 1250 815086807 815086817
    0x50a09110d0c020f0109080a09080a050715021513060501080607021f09061505180714030a0b0619030b030c150a05070c09021216051806130603020c0616 67
    0x1c40d407031400e034441c240c01c114503c126210250420441400c4809152040e40c04000005681107400d801c101e81500503c0614001c0070b0041054554039100c82e0301e0b001328034003800320781443c0200600c00c101d41400d48040c0c880107420b908018445846a11500d01c04441c906d00703110001480840100749030380300d20301a401a101000069072501c6944030031060404072150342c0c41d0140c010460b1486a40c0c0e02502c07480354500c456060604000c1c084100a00b181c41440203a01009844e540c041d00340420642000581030b1292540180b680c050500042c0300c0307402c0300b0040346010401858031049405884c1c0b070348003049903030107100506498a4415085a8108101c15040350611000d2801005180424a405818201569030302d20740301400f5070120b50750f1030300840c440703010180b1445142c0e000307408118a940090b00d041c001074428020740c0301e5114224421822211607884180499980e01e50384d440d840300790380c2c0303032000a00250800d0883e48400e02c03c43d40041c0c5d0340c00c08440700390703929400d640761 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 815089307 1250 815088057 815088067
    0x10602071a12041203021c0524101107030204020f0a12050c160c12120f0c020901050d2d050601211211010204090c0210200c01020c1501050a0911 64
    0x2800340e05046080d130346401c00d50308000340030f6118401080c650309038182c103101089500306401d0740c3c104210405801d13080c9103500f00030410f2a50751702000c2a20b1441c0c0341000b402c4030321220351140c00c2c20845d61000e500a400001d40f84030000c0d03108002d00700e404c200d4850705001070203070f400c440454070101c550807031200042040c95000d00c09425041d0350a0f10a91454170310580310032207030151004c2140300302c44081500c07200400d010f4114404141c10b403a103142c00440c3c14601d4001414420040c4038490081d80408101c00510a03040d08510914507900301c454003618241550790f1245600010076200d5015010001c0f030079460542410714100e460542240d50748645441c0c1c018141000f8081c0800d011448500e0b405140c1d080c000f4000801c80e0302400a030b543c00c074500c0603050103d10344410300c0152411403403da640c4068081c83c3c14400f8483e4010b901c0f5103030400b02900901c2210250042c1d8841c2401c03200c1d0040440030014180c1d2016288407000a40d01e01041056820080c1425104081801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 815090557 1250 815089307 815089313
    0x20607030902061e120f0c0702040e0a0506042102071a0a1116030c050306070c08130308040f0312020307030c110f0d1109220206090402040509010602071a1204 70
    0x1040a07042d00061a143c0780c402c2100075400c002000480d040740c5a20082401c83c880c212842907917502c140e040d0b8100c1c0813460040301c3c05070680300e07a40e0024030440da15030080d00c000700100036070390b01d0079030100488145046c83d081c10905601c91f0080c00d0400b218103a03c0d00d1885202295041c11101d080e130500700120a400c600c0b00b4590461541e10f0100421811190720701081006404110890340160091103400c40c14840c941c156a0307000140a40c0c020001d00c090264415600c0c1d0b400d43e00155803030b4079213101c20841601c510090740040d155100108012403401d04050240c070071a4440c0484d0001c070000590142d84034040c0c2d05014001ca0004140c41010584056807170710941c80041036180c5456014000900001604a055608040c000007841040c1000b1403d03a4002c022400441c0050310040ca00e03541201e00c5c840b000f130140f10041480c0c94540c8894051b01e002d040020b0010100d50b0312424000d548248520640340c0e20907000004807151003d1100300c5407214143e0b10700c0b0413103070b84e151 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 815091807 1250 815090557 815090561
    0xc040605090606091f1e1d0d0c05060a0e030105010e1e04050a080712080615180604030618060b040203150108180d020d0e060a200102040b07060b190602060703 70
    0x30540c19008501707000e0f001c0d03941d00211507402d0b00c4c400e20384844c2e41111546194842419500d03600383d0900026280702015000c2c4511140350003c01121f40c900d0705100e529003114805000d5024681011001c1000001d103a00103a002c1c0400300103400810490703a80f4090549a80029281c4844042402c100c6480035440315034501d23031050045084464814a50b95003d1990784640b0051f20108800f06611041650015056400c52000c4130380100e910b0708c2d500b11503002d00ca95800004010b402e40d02d541d900c1c3c0c0321002a6001141c000c001040607d500039411080c1c074284400031110795191605100c0d00d450309109590141e8407020200700c604040c0001950075400140118800e8500700743c5211a00c43d082100c89008000b640c082d00c0f10040414010382685180e80702141304000031700c16054015403011100d00169401c50800342040401404180248a2a0001134040c03070001031481c180f1180350010084420b050350010a41d03d03011850700c40b28011400396000503003107500400d58941c465 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 815093057 1250 815091807 815091817
    0x303021b0d08070c08060a06081b030d0507060e03130e010e10030b040201121d070801022d04230111010b0d150612060e0c0307081c050408100e0c040605090606 70
    0x150b0400802c4c282c940c903400d89404402c40d8030f41c00c6252907540600c40392034240400e0282e203c0540f82108481c0c48100000d03200e00d58030310b42804200000c128401840f14030f420907010141c1e04010b40b9a00c1c00e2885041841d03094038054110032480541c0001810f8014055041c8220050640309628504590b1609141003015009030b040112081c0c05640d000c45501c1001c40110383c01c1021038104091815075814800140d1004c021a4414018081c1c1c03014100c80c3c150710307a5046429004040c18a644401c1c41e0300a0340c20081010003071000701040030310f096424000c01c0009032203641070303004500c01040c02d0b40c2070a1481034102e43c015400e000004c09101d800085071030304031008107129171111440c3c024030006a80035201640c640360103000e540014011000c1400043d006400d4203410114011303a141c158000081805803180c000300c80a82c410390a55002e419801e044d1003a01d5510400440900710f070b1b003a0490140507501640d001498644104811240003500c04421660740104008131a000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 815094307 1250 815093057 815093063
    0x22103040c050613031e02060304060b01020f0d030504110d02031c0203091206060f010801030507030305031b03180d1e030509010213120b0901020304020d02040207020102150106090303021b0d0807 86
    0x41c2040c041072580d100009000310240f10242d02e0409031039418102e00c0340c0600c08421802503182402d10380582c071010704407640641c1000001c29041c0541c40100d03d13020b055100d591040c05800480181c0580c9500010300980c0a1032a40e10480001801c02421060f1024000c0d1716a20141c0000e40d29001010032700985505401035034285860307400410307401c0505511400e4240c104808001e594074144110503004402864802d10560444da01d0b1581c0e109140405018400003000151080b07013400010554545101c0529481c0d052602490104906402d041300903802071407007841c0f401c0d20034061a403041104280e0503400098648040d00100720150655003995000c20080402d400c12000d00b6005103804104005001000e00f012201000d010340300c80100e1340100b0600000d81e48450078121003e40450340140d60714410301c0141d15105e0002e1640c0c814003c2c0300300010743c0fa0f4200c4204c00c2268000c0c0c0a441010b14904a02c0221604090710281d12103160307007203107010520b514003500d40d1502c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 815095557 1250 815094307 815094323
    0xf06051e18040b120607020114090106080304030305030a020904020720041b030b180c030f01090c090e060d02040c1e050717072301021e070c06030f2a0306050102210304 74
    0x2001482c135040034403c82c0e040c0d015070b45550292503a0440a15501e80c0b01c2c1940d4001c0107050f0412049030745a2003544001390400c0004000702e20380b0f0140c0d034100c45403000000c000310f64a000e40d24040440c40c1e0400c0480e9440c640801d00c001e224203040c001e92000941d034804030000032424032025030080c50320302c00860300000510b403850100d07044040241e0040042860b070baa16417900b0a10080b0304841600240c10f400d081081c4601210380201081e070580f244004120956a21500421105440401c010798030904105000030340c282c00131131104400c5644003c680d940326068200b9146440790100050100ba0611881110048644007904400e4401c060480b124041c0008410144c118003c80e411503950000e12004844e850040003011545901162414030b582c503106d51100078407610600040c952aa4000c002c078500c690b01001070346447c409001502c1410700d541c0d0030f02d20603401040003c245090000710741c945c000100c003c2d01c00c280e001110014001d00a401449400c050000c4508072 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 815096807 1250 815095557 815095579
    0x60c060e010c090504180204020d020304021c0507090c05160b0a27021c0503071a01090507081504291201110d0e0304030f0f0b10051003020906040f06051e18040b 71
    0x2c0e5503800100344131011070200bda02d80c101030042241e011030524225400e28070b40e1810800003500410044101d4103a0507000541644041e41035071980b107001030218444c100c2421080804c0480804540503500340d0b441002401280d80817403050491500f100f04d9040d9152450000600d080d01241110000703030441660000030320303902c2a2445d084503408440787e005c0082c40c86038811410716104e00620604d50248660b040504014103180c4026101090648500325120480d88503504403944041010544040984045c0141c01c24813035041c0d20548150500c0c0021064190140600310500c41060b054030310307004100350148010144544581c042d404140400004110428216038a0502400a10885851601c0c00c503110300c50007000510f10440b810800e00c00e070b0b01da00440c1c50131800242001a600c00b651000641e89000f5035102d0000c500e8050008030300954081c018003200a0807000c4440701d0b910580561100c2c0c0210381c0509006903412800b815249071503000051284405400d8207219 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 815098057 1250 815096807 815096809
    0x405010f1208040e0c070b132003120309030a0e0625140d1205090610150215180d0504030803060904080c0d0201020c1e0a06150e01060c060e010c0905041802 69
    0x22132045550f80c43c481c2000c00c0f040d003440043e44100368484031000407400e8501e07455840001c081c0c0640c0d0101e040e00c01001003012140c4040002081480c090603c1c0c60300c03442c18092180d81ca030701c0740200200141c07a00c400d50209051003003d0f191510b003a9543d1000f45401d102c4d0080c4140325552065801e54081819228200f400b4002c50325138400b10b60b1032020220000c5c899805482003d442d03100268030050030456800343c071480490550f50800964100d0306040d5200703c0c50608462880c80b140000344052140320380c001499078210030f81040a40300d44c240e0a640036a4180201c0c072028007044010400076001b442d10251455000e07200d251002c0c217000364100031070705c0c00307013103c03d000003603035000030140b10f9031200700602820700c02c2d20720199135403841d2030422a0303e4072040000180850380781c0360011040c132031620b038413000383c00d403288140540e41c1d40d41c00040c0410040503040e201cac14600620944100c40600540358900307082e8450101ca01d240105200090081840f01c004107070b81c10301c200d401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 815099307 1250 815098057 815098079
    0xc040f030b060411090907052a0604020910060909180f03080105090a091a040f05061f0e0114010c0215070b04170a0c15150305030c0c0405010f120804 66
    0x14500580040301c5600e40201031004440c03007031400c02100c03901400304c0e0825549400602d40c1c8104941342c0651100e100103000540c40603095800340b00d0300040c4c01101001c40d0001140c0348030303a0080340d20403001d07140c2e12290300b000c20080c0203103000182201018000580b45030000c000c506841001030036200b1842d00c482504400128003100044c0500b40100800e280c00345c116500900c441e5020001180507a40e40100030201d0104800c510000d000018140700118140a01c6150840e00361950381c40c250310307200104042404504129000c41202154003d0940c2c403950503102203180e0032101894840064078507040c803080403030307104d00340010090f0080181400786c06081c0c460000c01c005814580781140c00302d40b85840700c1c10115824060100d003503074840e9a0901140d00006104480c404c001c404402400300009038041310a0030321400410400004000e280c0d02d41d2010a41d400504220100320a9030402e102e5200c020740316000500c900c2c0340d5501c4081207144150340d003c0ca059507403010614 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 815100557 1250 815099307 815099309
    0x907031403270f01050a2c03011b0f080402010e1201150b0901031410060804141207050c0301051b0a090503010615020601061403010b18030f030405011706030d080c040f 74
    0x110b00c031124040b072015007481d2500c003c2201003401c0c07079401c140300180003c047c00c080030540c10480180350790b00d50444080303c882e4918044003400a205c018802c070458044c0c1e219010740d1000207000c10403005140740c032824035240200e074169100f002d450500c4080084030380301100180d40070355951845d154400300c801480001001000c062a440c0c903028030000d402c45a012140c4c0b41e1003500d0004200c0300007260b004050075600141000b40f00380e20f40b0b0802d00110002c4480d089650300c071310754441e01060a0040580301982c45841180d8100980105150a03100d0a4503581040c2d203024903503856100461000d84920880b41c0760101000e0303a40c000190a40b040e5074010300c031211a404100b000554184917442c050145410840e188094151104403148014890907038440400306144564042200c8a00c045204c0202100c3d1004203c8111645a920910903d404540301e696500031404c0b150382c42610810004018010740b020201041d030b50180c0082c00d41d8503940040002040e07076034017031010f17034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 815101807 1250 815100557 815100607
    0x6040c0e041a0a0501050c07260708060f01080109030c021c050a1a0c040806190f0507091401020a02011205060d12081006090b07030f12110d0c080907031403 69
    0x444060410700c14071443c141c840c0c00080c10080c1c10043c40600d10f500103500310840c2c098080c021054070002600c02c0c0741040000680f213050090300b03000942030071300168481c0602d101c0d04000c83d0b20f0b41e90390201c90882c8d03014032009020411035406c82025107450590003400043d98103c0c900342c014250b5501e070420510602c11102001036441d030362405004500e40951251001e40c50f40c2c5440d041074a40c1e982d442c030040c00d420600902c1c2010f4400c0d1419504003003508480c1900500040c04c040782c0160001c403140c0503080305540c082e88281115031001407084d46064041c2c42c1c9407020307003400301414080d18005141c1c0d6041034221070343c040001e40b4410305981c140707881e030740f142c0325400e10b41d407405103022866219908022600358180947d0a4071401c4860695141c01c0030406a4070714141940e20740c1e288410f01c1e140c6407038080c151840c42c00300d100602c03244030444403c03c00b0170b94585040c0e4816000b6a001911580300c140f051001944000205c0551160042103a00302190810f240c1d002a054210300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 815103057 1250 815101807 815101841
    0x5040201050c0f030c100902011403130b070e031605010c02150c0d05130503060412030f0b03030a0207090b0402070305041203030612211103030c091224100e06040c0e04 74
    0x417143c042480303800c5205010f400d09200740c40c800d80009083c400304401080481d0400000b0800e005140490240d41d5980100511403c0c68009409011100380c8a011b50003405031404421780e203000302c1c0142e0152603050312022a210900c2e000d1060a0308040c40410040e01c0400c41440704200c100944070860440d0365505036190342226070105802500c0d44030078041d50001c8140030000d000f0030301d001e01a8170300c2d2900243d94204076200001500003d441107401d800000341c1011450360100b019402d440101005100030104941032004a10074540e019000400a000501420350000c0c000b0308024000d150208a8684130754150034085034050040724902c03400d0804131003071291412081d0790b0342641d007040780c141c20001d00c015403280301c002c2c00502225000924584c2c02d9950030041c950075040c0e003007282c50a400d0300c1075180d10781050340f00e41180e05054400240b0300042014110b41501d107584140c10f06034403064213010141c0b843d080c040052044040d0010031a032903030700c285440b0600501c80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 815104307 1250 815103057 815103067
    0x9060d230a140d14090a0b07111e0a14100c080d05131e0f03030e0f16030c050d0302120906160c1703130302120a2001030f0c021005040201050c0f03 65
    0x160000c00503813454046107505000b000c400380c1c0c99039000700c211010882c04580c0c035042403401c000c980d201481c0a941c442411250000350782660000c696540780709940d1142c42030f48405511087c0b580d90404071780d100c07010355070750040c0038071030603040d04041e02c228050743c246141c900303c520564000700c03000c50400a103810098140240100c0310b600d410358912203e190713078540d5240e1918290800b1005000d058982a44070044074080044000008459064882d58880032120354800707161440251410300403902c02003020701d048003400d08520b034160010f018903905002c101c40d05400c103001e500c1e80410203004440052645800f50700304a80314000c1c1407040c6007080541112920740b452885450f60050140100081000c610711080d170341c0485100c611100c2d00e5003010f18000610000030581c18802514500ca03650742d84018402840c2600c040c01602d450060b0a42180c04a80035400180d00c80b45008001c000c481d4810761b085801898558948002450880d06c2c3c00c484814040c070503440010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 815105557 1250 815104307 815104333
    0x50303190b0607050a022e110d02010509030a18050a0b0a0201060b04051e0a030501151d0709060e151306141227150609060d230a14 58
    0x41800441c40007190100d050500e03c0d100c140c1d88842000c80207018508038070030015005403030491000800d40541440b04a00500c0b040103000c194141500600c602c0f440040031f02c0d030f03801805001d03c0b81807032038020740c2000036152084501400742090b00242e42d00f80c034400f0400340c0340c003281c0e04050300810861603540c254080c8000e085901d0355005801410041c003040c80146e6520394480888025a10442c610322846800a084085503500062480d03103401524004401e090210707000300c480d242028100c41c100252040420b44c4201d500b44001900900240038a500410b5014440f24000d004151103120490405005034001c183c02c040752541d20350200a8680d11003007910001e101d051500e1700f001d00c45244a070700b10401a0000800141e002784008559910f4403405e52041104800c40e2150702d00059281d480203801d941860041d0001000140c50703041030680c04600c0795000649140340043c0701c142d0086507410b80b48100c858020400a1000f0a02084000d081a10303e20060300188084035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 815106807 1250 815105557 815105561
    0x5040906030b09160b0904021b0706030902031204180f090c0b0316020a021302030702151032090603030f03010807090c0c03051207030b12012027040905030319 70
    0x5130030070381c030203108003010b00699100800b55480700d001514003613100c103901450709010001c003890190342407068000010f051035154010303220442c02a8151402d4800d1401610b51510440c022184107061440c170040000055601403944007a20842c00106e00c549a40d80c0305071a01c042c2c0c00000301060100c00d00c52481000c80c803400240c10240000d1110f290540e010444444082e9450740f0b5a903401700c0043c2c8510b009000004040700d030740c100b0130401c1c5000080c648558289000b501c0c0368006c40e2802d008000d10304d200c003d050050404c00c604c0503003041c074100044800c00512080d01030200f07000704940b07100304101860103800010050700c9a1420003585800f110002900007040084030007103000803a80290844100d07030742b00c1c450044e081d50b13501420380c042d01c610340d03140b038108481c2004910340d0700044d071140f900469801105420344500804805003070141000041040c45a0f0103001c224541c0307100c0303210f02050050b0000c90307600c0b00d6031200e0b429900102d6805c58624107000360794003d40114 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 815107913 1106 815106807 815106823
    0x20a02070807121104021218010615020f010e0c1f140403060c02010f0b18061203030f04141b010c06150b09011d0d0b040305040906030b09 61
    0x85107900715681c141001610715001041411034580703014022640071f5078035400d1095142e12000c1c0c010b18050031404c9038000347d65a5002c0001d0036034120728410082605031b00604541c4941407207aa094603800008070070b003508900c0c03400c45a9aa4803a443d44089264003140740d50700c0f03a0407c1600c20701542035a1102000300802d0000c204403a64120074281b0314298020711804001015034020f4038490540d80303034004101c2503001c01c5042c60201c3c841d40540e0060500114022480070f40341103600555488a0407441c2004000c00c0c0710031181c00300d40b009001c6008140090620110350402c0615250090411046141c4101401050341100000d1030507041d145041766518101907019500815680c3d0200740c402e08044038405040154030f41d009806000f40e0641c1146a68503200580b00034400c90034480d091002050300000f500c1108040d5102c2c01e01d0842604045035140d10b40445 = true := by decide +kernel

theorem cover : BRFrame.Cov 814928057 815107913 := by
  have h0 := BRFrame.cov_init 814928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 814928057 ≤ n) (h2 : n < 815107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
