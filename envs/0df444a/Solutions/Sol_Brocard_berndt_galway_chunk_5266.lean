-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5266
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:17:41.821662+00:00
-- url     : https://prove2.me/submissions/aff84662-d4c6-461a-acab-489c573cebf8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 946942446 ≤ n < 947122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 946943696 1250 946942446 946942471
    0x4031712041a0921030603011103011d0f0105180a09080c0a02091b040e070210051005041b02071a0d0c1e020a05070302060d0e070806160206040206090f0d0b0702011a0108 75
    0x100c2c071004109005d0f6030425009030012602d110f00700c0d20506240c100360011101c4141c9011200d55081000c0c082d039411000072404004103506000100d4050b0038070030501042450a40d01090700d510340c0754440301b15507402201043c1c840340c40c5080c00e0b4891410590a074418500b180200c0c40c444212000b407c09140a004510316051400340060440c3c880180300406501035074038200800706160081a01c1103400c010341c031201c1d80c100700402040f6006040e0b28003500d40301a91800040360002003120a441029440714800000c601e840c41da54420301c10100c81c81c07800c141030144050f03040a0700041c03000800750240c51001000c030049a9a80d100704001e051940b01440810160810400600340c84d880190086900a100510b0a180c0004d680c00301840394840010005251b03004c13601c1c403100f20343c07610140140d820242c00203566030007181282441101c411000241e0f99595030010518a58040202030440c503015401900070b041035003244800300b802e46e501011a6102c0c0d05214800c03001c50001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 946944946 1250 946943696 946943743
    0xc0114040b03040f0c090513140c031b0303041701020c06010b030417090409050105040f05070f2601181506170607270e1b040b04031712041a09 63
    0x143d9803044c00c0800151072544402d0340c04a5001401d01a443c0b196107100d089000c0a50645098a00c01d4840e010802180c3c21401c4008402e98000c15148407440c007031030b10120010030300f4000904500c0303558040701d41c4880102203e21290019000f5045c898404400c0d524940c0c0e85101c5420319200407200100110700d1889101c1060a5078406000d8041c00a000018500c800ba9103540c2141c20039101070340c10000d02e00d00b0800700101001840042c068038030b0301c03c0b4000c0c030b4100204680b148c0d19004c00040643d40000329940507096019200900c80e0208900708180c0b2410044c03c0f40c40c401400320016800c0c64004a00746000300065074550040f00d000b03048a0395113240031a1103e140d125a200c80c00d0121203e014020705010821028041596421030b01d4103241c0c000c1c14407054541d180d21010502444204408420401035400700c0e070f04200790343c2c03908444191080d603070700c00c00752841211016001030009010840c882c400507255a506038100c2c60311040c0100340e807885040140d8049143d000344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 946946196 1250 946944946 946944953
    0x30d05091e0a080304060603060911040b0f0a0e04021302040b0301170307021e010306080d03020a0305160212130e0709051908071712030c030f072a1109090c0114040b0304 75
    0x455005006c0c2e0000141292240c2d01d92098408106007507e03040c0300c0903110542403a15109801003c00103d45e0f40c03400d12112400b2510405151180165024a5000041c01c1d9214800c6842a0b040c0341101156103035100d040743d00d40c0ba00b01b8003981d0301b000c0030708a003452915000801c49000300d4000f4210707001240921105140441c4142603181015258040001c02400030410b40d2140c0c2d15903107001d078407201c400380b00038120f8034000c1800100b4810324920140868001c252030322000380101066648040c0b000c011864030003542d120280e0303940d0b0304080141c400d034060004000e036901154203881c0300c91113112401402c496405010b00a40203280c08001d001c503482c03d44d861b090700d02c80c2941d1140c0302031410780e03101d0b8000712850405082c0010401aa490404141651100260502194100030003038560307818403c580c00c01200c010111510014800301165004000000818104d058506461800e448207030714075500f800714100c8244c001e40f00d001c40c0240c6040d21491801d00c1c2c19a55683c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 946947446 1250 946946196 946946213
    0xc0f0604020d080a0513090209040b011b030806061213021302130605130f0305060103030311181509090421110a021311040308180f010804061508030d05091e0a 70
    0x11131641c24031800300b003030360000c000c10a0104000d01488a00689450030402440300b9143c410402d14100402003282c9101401c80683e501e428070f40619226500c9d0341c0e02c002045440c4242e100403417080c0d8422003040b43d000c1024010385044c41c8251076080c4102c8503035080000780c0c0113091980c0074070306030030105005852150700500310340343d40740c0701c0000c00b00d031b0352906811829100e400c1035540341c00400040c400c1c1a054024180004501340d07607107140c00070001d41000008410200b00344200c041b041c0425020801905481c0c103d54010030780b05071401c0a00c0c01d00301034801616450041c0e4030725030781d8048150007904003000f65100d02001e42242002a4200190020404992101c90303075204443d00ca910b000c1400340000e03601c07a250311030352280301009541e0742c10b8135030040034842e50a0075540103190341e01442c080d42096100d800800c07040035144080c0064892504644000e204c0450a08842d21030b64010354041c000c054141e4900c081448501c001c04000c02c1c003580e40740d071301070750841002a4101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 946948696 1250 946947446 946947457
    0x150302420405100c030e0f031f141005091b070b010b0c0607030e0a020112110c03180303040b09041e020c030a030e0712030503040c051c1202060f060402210c0c0f0604020d08 76
    0x5007a698005003a015510b03101c2e406409c1e0022180c1d54440d004041c03130320101d015030401540c0c0d0a00e0800303858140041c500c058010034207005040550180c2c094180103e00ba2019540e1103079010f9529a11840d0f101c1c0b45030003045840302c45101e00c20100e005180284505515000c4990140100c2d440b5030300192001015040f81300c40321a90341d81c0c2403061b045641c0240810000c90006196a21030042a90f100131b104414a41c2c1719130804c0208102c4505100110384178040c081e100494901c03c2880c0051100030036012100c100383c0009030341d0079024030200090031480d0103900c00b00196074060310392a40d204a41d00812051032002a00307030010034050030242d54400d1040074250852500e9002043c80d4920303840c001e21603428000e00a0041044004900b10060010f00c01800c2d0b500e0a40c205910301000034000c54040c1ea0300040c40448071450511810b1380700c040d001c0b080300da414511041c401c203a00c50007100c1000c1c0240214920300c580c001c20214000c1d90001d1007458550030b00c1e1103510142d0b110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 946949946 1250 946948696 946948699
    0x50303030c0a050d14060108010f081009031701030305211e090709140105011706090103020f0102010e031815030c0904050709081c0201150302420405100c030e0f 71
    0x14010291000d0485c0104000c5890381c20041c106801c108001400005040e0048588550800c0080c050f9800000d9480c0c1c03e800b407504041001000c6040a44d9024540c25480c0d000d04c0310304002000341508030004040520050703804a500d025000000742c6100000d4401d00701e40141c0700d42010744500035103009500701c0c418005a400c402c3c0c0d42c40d8180110b8000325041c1d502c41c18804010031007980c005813043d80203c00080402c03c0c2e4a03266000680c03148050000034440e8514114103d03540e4400d500c80c0b00c00b40c001e001141c2da83c2244e607260502c07241e03810b25174a00c9032305104109031414840905903405511211001810711800a04000140c48000e14400c10800c1c5130b0000034000d0020000c40c103c044e18005292040c1885200003400d55914010742500d0201c090000c10042e00c8200050001041e0030b481d54030f907500b05680414081e85407903001020505165400c00b2080302000c020802c54034210340940c54610011800d6601d03902484000e0041440c00076400c4039800c109100c410101c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 946951196 1250 946949946 946949957
    0x2070e07090806010320120a0201200f010501050f1f03111e030a0506100c080714070b0a020c09070801170a02100e04050c03090a03050c1204030f1209050303030c0a 72
    0x2c41d400e1240c034000003640300b5034090b04000141080181120350025207040283c40140d0400c2c01121141d580b80d46083c2c0c020b04102180e03000403d101885c91410040d00001001d440301d1003900001c45011b00340a0045a11400c052040d6007920710303080c0d00008442852008907017943ca03072584240c000b44501944c04980700c008110700c07410701d031000024003402046070719016142c0c2007594505040761001880d50380542c40d044400b02e625030308502c0d00b070350095020a00b250746106e10f1a0030304006a0113400031407244980200410405100c402401201303400c2c0d4229103141c006501048002181541d804001c9410070005101c2c100710041c0d800300745001c0c6021980e40551035800702e030184034641011000900c9a507041b00c618030f818003616401910500c4420b0440c2001d890036900e41161440c02030030b11600056a205c0d0a1052265164103903a800d462901c50342d40c2c0c01d045162045080f8110380124034001c00343c3d60f190284241109481028000754115a21001c0b0014294001d000c032806005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 946952446 1250 946951196 946951199
    0x221032211060427090b24090c040509071407020f010e031f0b0a03020f0d2103090b06041e05150406080304080114090a11060714010b030d0201090302070e0709 70
    0x202c5038801840104201d04504a402c07502000583e0044002c800700c418a9042c40a0440800e031540212508442c0c15003580307003000c007040e0900030302001d80000550411244804c10003c0c541040c0904100c580668004c0e2241d550b5090807249550000000078100e04103001d201c0250410b40390b424000c00b810705007190305400b04000280b50988140208103207090841c84070704004514002d03003400351030030340e84020400e00390750029503074072100d9041070f0148814601000500408506045550807032403d007907000000d56800074050300e1810810b503001e000702c0c0c02190150810340300300d96503158007071083d080a10802c696640607081c050013a0640e010350030342804103a0303164071482d4014108440150313540c0d460290017509640c02282000400c00140080001c42000421005902c5a00c01c1440c002c102030035000500a02429402501c894100d48104050b400d055103d103d004908070200d030031000e4210412400da0310240030060050300642010031818101038040e03604400c8a042c042c1046 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 946953696 1250 946952446 946952449
    0x60c0c1f091a0403030605030a15111902010213050a030206090d050c030d0c02100f12050402180403120608030a020d051e0c060a060504060e0f04110901060221032211 73
    0x14444480e2102c01402d010180810140c0621550300101015800707041042c180f516040c500e40e20b0004005240c0d915140f0400880c070780030080303800e854803040910280100030304000b4003c2d00220b024000c0904220004616880c0c81c960f5442141e034010003c03844d20341004184074814130701c01c0f411981407203401944106540d050208401c60440f603901c001c2581d5050042101d50700c0f0070521601840001c3c04d12115055000e40c107811542c034001404140307a01d07107101280240d607450046250101411050008255025001c440491a56031085c850641c445103415180c1c81012114000b40c3e21441c0b034000c0007406940075004160542c0c4400b800301119088d178541d00e03800040c144416800036810007200c00342902c1420040c0c001614200f1140782001c40f00c0b01035103809015002d480d4280d000280401000b0850b040800501800c80003440d6900e4001030355030140c4131340c0311446144004c0f00d00940c2c12410152032048480300c8a10310030036080c42101c01c42000d100f006540c9584220402c8806 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 946954946 1250 946953696 946953713
    0x605091c030209031c022b020729070c0905060a08030a0c170403030305040c0806160e040906110c010b060906031b070609051e01020c251a0c060c0c1f09 67
    0x40d110036009440e947c030006906180345070400032003022040f9500700c499001c540c001201d4007511000090502d02840c420010825100c2c0003c1405207590b002034800f0812280d002c4074400c45030302210500c09601d84804000310b4145130b015401d2103501c1400300c88905031040c245504850b000d800b03003101c88804800c6803c840e6026400030703008243c540c02400200410398074101c00070030031722000e81521304190750b51020b41c40a201450080001100c2c241c4240d075a00c3d80705a0300da03039008c1420861024810100101500304480c0360103903502e0480150f800303080c210112583d501d0003c1600c0c0c83c3d5a1090003241c1d802c81e112041c84440c280501080000521520940300628058002826041140e4030f140024062030a40204649d006002d030104c82c0d50002055420300e0182502c070390143c82d8911524070142c040e42d101c0d00c2450031064464035205100e41c000d0040704158002c2c1d5520340d80e46581c0c82031034450705418034a80e40c4615298408040c4030001103c1e52450f812002c03a40145a4842c01c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 946956196 1250 946954946 946954993
    0x512270f09130609080a0f090b091324030c12020d060e03040b1303020f0d051e010e460f0501020d090501050709090e0705010804020307050303160605091c03020903 72
    0x445d00e07070002d10034002681003020104031001d0b51400c074460500b0404000740d10f02076400d403507000710105488558580301c160484420074452a844101440740c000e20301ca000c075001d100584010700150300c08a14001c900904501c459005804102c00e420180d442c140180a460346008031408240b001040c0031301444024035094515100a4a07607905500401031406a8995454410300007203a0540008402048120801e1035800c40010030550b00c080007030140403600d00303204140c05041204c548102000c44500140c9400e00d03100d05409003a240b680c0c0c282c141e85036840c254664252170141c001440c00060701400b80c401d80015040c203901c0441c540640d6034000d0300315482d0b51501c0801000c0d079400700168000f42092041803200036242c50613152606002d01600b41040309c03020010b0155282048882c000300809003c0760344d5400c059060340c2c3d4012401500700c1b0030a0526000c51000d4030009035142c100e90941c03407401e82e0b13540150401d41c003d51160f40010f40501942c542201c2c0405500c00004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 946957446 1250 946956196 946956203
    0x10060c141501080114071202071a01260f0309060d020d021303030f0c0803060f0117041a0c0703120b12060702060a180c170a0512270f09130609 63
    0x1001d550400c4a05030030740740d0907000040e000d1251030410503078070307801074080c00f03040c08001c401030361462a401c00c2030380302000d04e55250011104100001e03044103800c80030400e001e0524280f1042d000c0702e0300e0750307034079800310202c0440154010b105000c01403506000815480d61085401481d00041c1d40405081e40c00c0300c12400c41040e10303e0310400038545c00c48111034030b1255a1500c5801c8001e00c1ea03e1000c0d900000c0d001c1402107040c82415000350f401070b25103071000c4104225015076841d2628110001c607600b00107200c0c11080c460041103060413100b00b640c1039180c1c180c60b65244041e03003008040084c400040e4503036000c220000a500d03c03d40c20300200f80600744035070180c071440c90010060f03c02c1e42c0c04460500100d508481e107500110340e4542c6810260781c10002c0b80c0d88010410340c00d561a0400781c00018109004d4010f080e00c40903003000003083c1440300ca00d804a000350120b4102050700250b00c81c490340020142a42c03082514100e0003070351740b007a061030010b09000e40c1901e4000440d01282002c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 946958696 1250 946957446 946957483
    0x60901180801050c041a09091503010e1903091505030411130f0902010801060903050304030605060619080906060901081c0311040b030f0c04060f0c031209080909090610060c14 77
    0x1801010000031000700b1800d50311b000035241c48644404250340c0e034030080c0811540f44600b42038064503603081d00021280342c0601c0c02c48250b40c0c50140c0c0d04011100100c4224046550303130320005018118400c2c40e20b480048da07100e070b50841d619600c034400c10702c2100e0051a80211b400c90f89840c03030301d8140320720000c200342c054000414643d10b00c0050700d4404107812100c10f00078400003c10002d4400006c032016254011030200c0c180e124140403030031900131414550083c14010094555065000704d5452107800b85070304403807441d2078038414801540b4007802000419001a0540b0002c90341d40b0f0074005c0420090b00c5d0001e040c5204540c1d42e00242c1298220208403a000018064150141c46450b604003e145112515142c40d100024106000300c00340ba1050084070628141450300400f500610044a24024408800c0d2484e02c042c4a902000340d45101d00e40f10008110348803000540140318001c14841500300500340707003080d50500c25810080311940b11003d1315116016050100303402120541040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 946959946 1250 946958696 946958699
    0xf04032d090609120215040e010806041a040803071b0b07090609140108060d030302120a0b1807020d050f0d020a0c14060402031e010902040515180105060901180801050c04 75
    0x40400340c26a00c036504003e075000c428800da506503100c0300949070b070440d0413003021010015140c8407070045da440f04040c0c101c2200000745540001c200f441c880d80c452600b0904510940500c0c1e280d00c2000d960151904c1802e0000580082c082e1000c84404111a000044400300a0744c038488201000c80d002000074090b400c2c100700480d045184100a080c649051a010344c0d507440000f416208010042c070310401c00c14040009150199040700d200c071019000c451428640b550341c0e10040c0c10000e1105014031503074411740c0c12003c04840703413034000c00c6103070301038070f1048403151041303649030410001100402000c01014032065580d1000780820002034483d07a20791303801400c0141e80380140c191100a207410039810440165008030b1301880065000300d0054014031048241801848180c500030340052421060090703c2c40c0001100082520844915000d0440d100d601c04500c6002c4c4605a0403000501c0300c083c0b9036001e2180400012000903030502c43c0d0b55a603075031b242903c2098a00c3c2a000c200001c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 946961196 1250 946959946 946960037
    0x102070605030903180a030507080d08070e0a0501120b0901120209010602072409080a0b15041812111b0a06030b1c020f031f050a0902090f0403 63
    0x1120010103840c00c1003030540c58841c122039203a10402c510000b403040a4990032580e9500c0d03c60810165812000319403400703071105030159460040002d0f90300400e000c035000621082c400d050b205414500035012480c001d24200040d2600309081c0140c1e0708098075130a413840ba9441e18a092070080c0600028140c0c001c00600621150703507010380202c811900b2001e0240207401000011947c40f80d020501c411108041c00c1003291010780d00c0e04405254001c0b0f1501006004001543d64001c0780812501c401d07a04805040204032510308000d144140d1240b5890004104000c0c1d503d40241d0349070074552803100d04080c1450501c4810b64524840b4030003484030f0700c450300b801560540a0006420100480c80d18400042c1d1007080320002c0d14580e0328500030250841d103640e0804100314902501310b9030610416041003280144140e42d0a40316890071002610540c00d902070103034240d401030718080d55920b07040c0401d00c00d850010425405d10030710624071440241d18581040301d42c02c0d0403400300c1c1600442c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 946962446 1250 946961196 946961203
    0xf150f28050306090708150619021c020709050a06032301050a05040f0b090a05031b0f0a021011070b040902070b070c0b0106051b01090c0509130804030f1e050102090102 74
    0xc40040800c081030040000c2e03900c0e8904113039004845800d100780307580e684130a84203003c40c00c108102e42000000c07518040004100d90f0b0250b170704c5400c0d02078508403080036078030a540320100f031001e0b40180d00850042006030401d0b4000341c0c000d864a00c010401c40c0c0c49854400840300e20030f014401d00f1602100b60540c4500a20805030801d1001d0014003c50038a500c81441d0001080409402c400300c040105256040400a0115803980041542e85440743d09205403001d04015003480042d00403500720111040001c500180c04c035600803d04003030f003401c0450031500d003020701248007143c0c4944000402c1c0c100c00d0034042c1c4018182c403840503035030300011314104030001000703008041030011580e00000081c180f451214152171031031900c1ca4079000203000c1d00400159440e00e034402d40d440c040c0440144a45010004103454058030388a009840e1002c4d9001100d000c1600a072800809201c00d000003002500341d201018056100030300c0d50a00c202c1e20401c2e0f406405401c8625a5001030311800c1540c051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 946963696 1250 946962446 946962517
    0x71d01080607030605030312420102012306010521060109090203100501081e0405060a0608030424171306110702030303180a12050a03140103020f150f 66
    0x20310f001d0042601e01004070b80d0303d010741e43c1120107581400000442c6a0317044c80c99120801500014160140b1810313128410341c005040c0c000c9200084488080340f10b5005002d4420503951000001c00303030819403c180d5254100c050109410401e0402501150404c0f05c03d01c000b021409122a040c40e040190024188804a600c0300908a0062080201440380c01c10703071400b124820300700350b403981e501c2841201c0d92540510880120341c0916080c8000d0040019100384110f41d030600c1001059140e507000341d41e07070003680301d110449003001031164641d42e54140c0301d95248000d030800c10304009040e001c40894140442e44610900c2603069101d040c00f644c0d014001d0b20040c612055460b042654001c00d480b4803005009418040c00c813404030919000400140e40142d400415549407460700c20030040c07840d0701c150074680001e4100341200c0a0004601101e41c1203990040400c40d21254120601898080010f4a10b544100902c042403448800320b0040c0103e5072421440345c0c07400c00259a030203580d00c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 946964946 1250 946963696 946963711
    0x6041e0f03080a06090b220605060c0c0f060c12161203050a11040f0509041104050c0a0207050a050a05040e1005100602190305030402371401080702120c071d010806 72
    0x406c0314540d065143c451004614100c07151600c001100000380e00d1002d002c03298417898000d080041e5004a42c13402081d03140701000110b410128010b400802c002043c0145880340b01075420810040850782c3c000801450901c4c240d4003414040080c17900c03000320221445032102e021030b0b01e0340b0400a05081034403402c600500340400050401c3d040ca40d000c020380ca131358054ac90080e801a0041014400d800401c50024000103000740298607110380841c40c1a0030503602440544200740c0045041e00d050410303503050f50780142c05012654600750400002d0104400c1d1120b41e4010190035151441c29030044620681c60180701000c110f240c940024a440401c240040c0e0040011441c0800641d01c00200d82d08103070103e401c45003174164054001d84500c0d0b264016036410b00449843c400d050341d04840401140d01c07802c1040c003a146180c005590305007084911600580011504050902190010300203440341101201c25150301c4068881c4491580e254044ca400b20a400400c0154400c012080d4040302c0e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 946966196 1250 946964946 946964951
    0x711060609070813151b090b0304050613080d090c17010608190302030c030409050109060b0a17090a0f06091103030a0c0210140316030c0f0206041e0f03080a0609 71
    0xd00110007003148034081c081c6a034058011001c138040c40704040d500c20842e90141c40c01c1000041d1503028010090034400340d103011403080c8000103070b4000e08000f600c0c0325039048400780c85d165a40e8044403070b01c88404601100d0541041c030044102624500c2036036011403080c6411a00c81e800c140025840080ca0361201900da81090700900c004100410480b0100c01a00c036841440501854141d0071070240c6500d035081031002090024405099400460495041e01c004101464940ea90a0000c2c401c0b180a0000f24403246180038406d0320b8140b669038001c8900060f14070380003c503911001c821028150940b440368490420f40c0c1807105101001e0400c1200718000c1d843c0440e0406c0180040b480484e004c1d108900c81c0003810b001d81d01850305005100310800c0b0f000d0f5245010810000b4600d101c2441d1000a0310b01540169424051410a400d800340c580003801c5903034407039844034502c510480000803640700340200c0e040018410a25110841e1180d101e60743da03450034000150443c0c00d15402103014a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 946967446 1250 946966196 946966201
    0x20d150320180405210a030c080103031b02030c031902030601082e060b0a0c06200f160203010e0303090c0901181d0304270b0f060a020a0501050711060609 68
    0xb5070700c1524407605070826103240e0180ea11814140d0802410300c410080c055480c6042c003581c41101d400900780c1c01450740381000159042403007111041702c01d010003404260160280388407813403604940c031042c82c4001c080303920712644500481d0400844446400001c000f0403070190851400340310380c50251540000030f01c0c42d42e110703905101020005504100c0620003411a489440005801000250421503501a614482d4010051040ba00b605003640d03050b01c1c10710b20b04000c800051518a11004240c40141040c1c1180c20382545a402200c1c544450030700d040075680180c03002e01500c0340051058006c0c1d5145d15080d0346107800c08011000c0a4410756081d00103105104030340c0001e020b0304501c1280068001f000800000d180000b0b030000300a2403001240014072484101c04514002105c82c10300c0c1008194180f5a13400d59021041441d4042d000f401405001e003007800c06051008504d104503070300c148444e2a9542110000c1c0c800400042500c840070320070b62001c1042d59000003050b9110340c00c40c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 946968696 1250 946967446 946967449
    0x70b0d060e090c09010510110601030803190605060306041e0f02040317070317060f0a180c03361707021f0207171f020c2104090c03020d150320 63
    0xb620140a00c5100361003c08007d034400b84644400350110815804a034840d507128208040c69400072110f107802204002300c07070940c0104034080c4404883d8054a003074119120802000043c25072142500c0ca0481c1c0c10600100d6202e9030301402c404024845030050782d81d401c49c10802d400d000d0310454400c81003010490301001030b0f8001d0f440070442005245d0740c8029112100081c210038040c0303003440d61129400c28081703100002c225900300c0b04185460104031000b0300c00f9040d816220101c600003082e07a26005952001e000d6003907500c04010440030704c40c1c0d640541c2c1c0e480d001d00c40c0a10b50010262800400c45400b1030620f0b0419604071000044603200081080900039501c810324002e40070301008615010404810401c2545000540a0312400501c0d00a1b1a00c600070f41221944801c01d100b10700d007000014007250014507118030b40381c40c000e14290402000001070004280c4001c1095420801c0603807482035886000c070100c42c02d501d4800e5051950500c4810030010032243c24100304a0751984406 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 946969946 1250 946968696 946968709
    0x9040c0f0e0d020a090212071206030c090903050f070602070b13150c020c0d0501090b1609140a180b040f2318031911030315060903070b0d060e090c 65
    0x101e0404640c0028160b00c03901c0450066146680000003141c0081815420f800c83c0c03504503417040f13142e0350751101c1c801c01c40c4150070141c41076031001501d00701204906000d90085a00a811902c1c002d007000c528180160b10440d00c0c542c44140181d9407503602040100422603140c2010303030440603141c0d048003140501d031501042ca000901407446419541d06014040c01d00a01410110807402000c40c41d103610750303007440e50183c1080b1000b1103071140f500000904001011a03150b564503826a01c2c0004039050100241c1d046441015060340403020450008910003984e20240705403548440106812402c10140026240c41000c944481401c105203148040d04140e400710b1030021003410303211552a550b001a481449100e005506070200040310f1110a8180c500740a00e414541c1e62042d51140000c00075132030380002c0d10321561071001020405158640348000e0402010001c00f5a60790a907940038000b0654058a90603450341d40340c0c84100410b85050800c0d5502502ca50040d08512030b514001501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 946971196 1250 946969946 946969967
    0xa1401051309080a111002031b030a0b0613080d020a05121305060c0312070c0302060621010c030b0f01030b13091e0803010911070302120307050d060b09040c0f 70
    0x40e07445900100c0390154503000a18940c0d0004529a594440450004e20b0010070024910580c45101c00c03420b1940700d54800c032842150019400302102506144c01d4100d90710180515400310b0f240c0c071451603e6a202d6000f0320940e001140480003a51500c0401400c00d11078404040540d00004250004504003095003407403e06e625002c0c0d40d031840041c081960312600303600802e4220301d004c41c100c2c1c14214000000c0c000d003030b1242c1e4600712507980d5134000c44003000704400060040e0418004154581000c881c1d40307000303038011250140c5900b890350109003110359001312600060b807681200780e29401c016804841450080c03038240542425000070580350303c1d41304100d21085590340b07500028802403032040c01907402e011945140c00078045c28203480c645c0083c082c40794001e20300050b41d900000d8071021a001c6680c90b4001d84950ba0f00295034110a810040c040c80a0210070030036650341e41d109104020103400e06e940119154134080c02844112aa41c0064034184204401c410b80101e402c41031085 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 946972446 1250 946971196 946971199
    0x10206041a071101050115080f150603040204020d0c0905010912080418150902030601080c390d02010e060c030c030c0f09120d030f0b2101320a140105 66
    0x344645807108116a030350030b0f16540d00c041e5441c0070700200e01046420440184500e1075a80c282e0161109007005420b03400c266440c403041c5030b40e01d564101c1810107801950b40640018401070500032210200020b581c070040c25140040d410078414402513030000900d0010744440040c0701005103040d0303208a91072185005401d41c14460310000514040d0304c0c2c00086900180381000010155918a004040c0d002034401901042503800050702c65100a025614418144010840010848500012010001031800020b0034260a4041c14054104120a042080355000040c0010079242c0541094400b030164400c2034420002d00c2190003a56081d2034100020061300c41d940c00301005940c0c414443c80c0d803a6a0032826040300c220b0361540c00b16440c1c408500c261024816a0102c450480858200048403a0300c40907941c206a0029500707154a48805038050002841504203148420503035081030200300c0a001c2100c0603c0420024665541c0005511409008109000c0422001310310305000e0603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 946973696 1250 946972446 946972493
    0x11060903250f0c030c0e070507030507080c16080a030e060a020703140c1302090130270f02031b09160507150e0106170303010e18120a0e01020604 64
    0xd0003800b0b1121040351185510809070161035035286800c0100701e4581c480c0d00060780301500011b0055000300112042c1c0c0d981540e42c1341c03802c1d80a540382d9500f500103410440b000d2160500f110407040385001041d0240000c43c0040082c0c001924004244501600485006607030500000080e030317400090303840c1600d0b40200012240c0c40301c906180d2505542d88005644440302c0c1c240342400e46110780c01041d0304402a070700c01540b10780d619a80f034000d1840f20980300c1300f2000b2803084202c400290740501801110b00c0b818100c0544101c4d01044d56017441d544c1690034420303910ba00d0045180402a40b498011842c040000b160417200c009460034400801c00803841c54407010a030300c09446041102c81150b0f012030b07072441482541481d1001005035004511240d0300c8c0940c042400241840924401201c84009501e1682030699015802c14083c01c000e00710400b18540103003041050000000d601c014014041d15401002001000e0755030004481c2e055410140500c404500411108040c0e081e1710b0019 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 946974946 1250 946973696 946973767
    0xf09150302060a050706050a14090a02030703080f070206071a0718030f020103020d020d1b0201060f14030a20130603020117060613030c1502010b03031e1911060903 72
    0xb0b4070b0311710602000505075854030080004490072a44240e46500c941c4070301030080e94845034419900c43c841e40c0040e505070301107401040000c80240042615010f107940240c02e01c9030603404101070b5000030004036045003020305802c40035078801161301e500c03c41520b40031980f41c0c05103c201c0d00488141c0030250560050a4218040d64000e0301111504100d0040031913443d11020f500c48024030003c0c801d40d10610740e002101d00b0f01c500c14000c3c102601d240c81c0794103903e43e1400c111984402030b01074080e43c0502a080184000c200c0f02c592644d5803039070b081e100207001c1e1354005c100701c0814081290307506410302e8070b1030034000350741c0c0304855040741ca041c4082d04c8165203900001410034010124411021482d4403000300400502e20b1540303048402c801400b6040b80b030070b80c1c010707403e0394101001ca5415600c1489102400d240d520907070070080384402c000628101e05105c0c200902218000104041440001e100102110420242e6400b4094002860501d51392000c41c586006520203802c0020358000710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 946976196 1250 946974946 946974967
    0x10903060207061413060605030f0d030527280309030f0614091f0605090f1033020d02032215031b020601060e090c160c0f0915030206 59
    0x51404c201c1002c10030f01c898a007407036101e54002c0f81c440c3e00705c804500b0104000350508002402c0000400da4101400c82001000011401000d0007405120007240000740d0150a0490324001c06221258401601c58091207514550341d0203542019050040f441c9502080070940c03012114054a45c802c0b04160282007d0508001034001034803a40c0e50803168009022074a01c001900c8114a0701d4080104410100c1d074400340101d40d85441f03100d802c41c403110002a011a411102d0a600008280084031602d844022142d801d80c07146490455040c00343d1002c0400010030b00030740c00f081e210f80c0300408189206801c000d4880c0030f0b0b1806019050700c410712034081c0d1614645043c4c0a03090040346c4200d00d03001c0031002000f809140313146080c08007500345038018045c0302041c080c0c10fa03022501d070307203400e600e440c018000e001c10010440c201030001881920b045032a40400e20500030700071f064842030300d402c100c00c80c1e5004210b507106030315580c5080d00c00101c002001d4042d4044980403200c0307503200c120700d05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 946977446 1250 946976196 946976201
    0x5030d05031605161a060f0609060306060a1b060902011103280509030114100e04080a0804020a0305190b07030b030718090c2403022104020a0b04030308091b01090306020706 76
    0x1000184017400da00040c10300e45101d220a0b91150808480700100d8043d4401130280c54400e212801c0e801c91420800140f450078414024031910140e480c014000200018a0b21200d95140d401114100e8035800c44205541e0310110204001d2000c1001d185080004084060459021400c401d848040c508032410100d010b0825229904c1010b8003e200215001c810342d030495070102d40522404842d80307c0070405160101d13107144a664401ea030725151510440c0b040d200450014802c030790081c0d2070382c0301000241c0309005460304813210010542801d0704600e040108498010180400c01d844d04000130f0b41c580d0001a00e60481321311000388841111480950710181c00841c40c054403250003040e000600c0007403c86900141440d150021540405059040b000c0c0c0c441c2c21985540003010141c284c1c1003810302411b04c1d801520040c0400c0c0c1d46555051250f040d80c00c075520070703004100080100300f10203009111003a0484d8030000c800a034035840000207801c0780024000680625404035444003009001d9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 946978696 1250 946977446 946977487
    0xf070e060409140a050c0f07151127030607090b0904090512071b03020d031b21030516080f040507090906020d1b09051c02040c080105030d05031605 65
    0x282d40074850540d40d04103240151105443c0e05003114a4900000d440b02c1841c000d45203d4a030182020b890000b094540a092800129001141c269101c84551140300305034003e0448601d07054014906544141017030081c1d50644403110300a40202041102044c2d20214010076103404030160364450612a010034004c02c0c000030001c107284907054540d92220382080250200c241304001000581d40d240a0009880005101c004d401880711160000002d001b4681e81001d900300c81c02c00d0306844a103443c2c0c41c080b01c408a06a1000e41d144a4064820729031500404c2d1388003401004500e60b03295440b40003007151070000d01b5090740c24960030115007008000d0007054010f000c0b0360300c10300c099040c908105c3d00039480f100c00316841034901601c900b1009094040707100c242c50242c8885412501d014140300d00d90210084c0c0d45c80b01c401100105c0c00582c0d4074800c91924004560368078855605002c107240c031708160060500c0920000303100300840a402c004040d410411145845625000808551090006203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 946979946 1250 946978696 946978709
    0xb1318050a0f0b01120c0e0705090a0e0105012d0507051c0e010306060f080601140904021305032a1903020d06050907060507200d02190311090f070e0604 67
    0x401c00c1c080d051242402401c07040900a07091520240da861040c91000702d1401402032a4480300c9200300200306078001c030554403103140d040c101e240c0171044c40000c40b0b503122500100000201e20b801400303a035901c0400501d0601049403828041c180d41c00038180703401e00c00f11008040000000b191410098144031600201c8419542c8910002c5a90340180201d48202070150020b40b40010004a09105501c01d030049000c0303450310030050f2116001141c005401002c4038000801c100000e01d02505c86200074500c8000d000c020b00785081c00c3c101090f0900550f5041c5007078004007c80314105034444104c1c01c1d009002c0440d02d070401e13502d17001c0c00080b01042550000c1d501001c002100c109200c6250002031040700d0101c19900c03403a885000565850140b000060701d500c80c01088882d80c00d0064800e90b039591001001107a001203640e0018400c2c0103504c50214600780040c02c10000c008032069030490a84045030310603018a00584d050341d0303000c0000e040a00b04001040c1034034407500d403038080b01c018181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 946981196 1250 946979946 946979953
    0x180204080a0f0215090913141e0d0504180506030703020a08061f081023070507030f0c02061219020310140d080307050c031c0e060a0b131805 62
    0x10941014140b03051200d4003a80950382c00d01105400b401e541c4101d070040f290060114103192603440c00c0806001076407904480292003803042c686152070400628440340c0c0400418024802ca4114081c00c10f44040355190500805010500080c0820780081c841240c1e4024002415903034000064605440d9031710103900109181008100c2800c04a805417198418511000b00c00c3c0300b11103104940705031486501c076250031848100b840d07400c054204280301e4020303180c41c01403010a450340305d045034000da901c0000308000148680070140c1009042c62250b0180c1003a2002d10f0440e008a2070a110703801c0c189040304c0107c0d001403060703001d03146298844091910f046450340750501c121010307011540200c0070444042c014143d2b1078039212102481441c2d020050608584400c1b0003904d954010620203040360000f4059001046650300f0414103034040300b070021482198110569060280c0504141d2121f41004030507800342c2c03134101c06071a48015080000401440403e008640c00aa09600526502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 946982446 1250 946981196 946981213
    0xc0c0a0e0612070513090510050709030c0609080a230601260c0d020420133209060402070b0103080d06060804050a031803140609010b0d02090118020408 67
    0xa60100d46184142400c2e1441041100d401118a58425140c840e66501280c0d603d03a00e600c0315004c0c1c200080d179074030036000ca4130861390240480c0242c81c000c45401c030005000c024100288064031050000800c0d282c01d2010f00a070504002c2900d50503c80380240404201c880c02180000f509145082105182d030250b890380d584030300d0840c08040d0510348810f0b2481c8420700341e0f001d198012610b0500d034480108604880784003642800050f1074410070000d0318205c406400f54400b107101006100d0200c8001291304a0390400a5441d43c2d1983e040c40c01e40307402c441450b40740c08250341407541409000c040792580003070381c0c03500c0004020f13100741c1034002c00140d040000042000b180304080c0c445480788103800d01240391105421203519104640c0034225900034890a004030b80501982c00b0000481d002c49507245840340c541c880308208041c546d10081d8409010025031100c28031400500083c201c0b04000c00a030343c1d40000c1c40c1e08406002e41040100d0080d10401c0321482641181c0c000c240c07000950301ca04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 946983696 1250 946982446 946982459
    0x10801351c0f05250602120f060406090908090108101e0503010608121219021c140106020a030813020a12060f061a0304060b03010609060f1a0901050c0c0a 68
    0x40d0410390301801040880424180d41401403084c0c4030002c15078051001c0c40d840c03414402a030590901c80035030784e0a50801c211a4170401c0c411a443c4650003848054040e410010180000c40e40300c0d0380890421450103207500d001450940c00c450340380200b4600a01c0540700c0c00b13070310003951445500c00a0a010500e04816500644000c020110b0780218000c2020681d00c480c01c07510360100050a1015100070060360350300300640c15105801c06006207078103515030100303030b42e410490b23002c00e030441215091908201d038001360501072000c800701007403e06081540341c00f2020307586a1443c00c0003024020f9100008200140200000302c20031307002040c402003150769115050360032032a00c3c0165219400c0c00e260a940b40c02c640517010855191a1810f43c404403d40c2d911060b540000e0400c0f250b55403035000180c0c199500b4050a0090800944000f0b805031070080c151250800703507803007140404007040b4142418022a000ea030121721081c00d01c40d0f038600f46410f00508107070072454842c0e1301800002c0d010505 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 946984946 1250 946983696 946983733
    0xa03020f01031506110f06071407110303040e0402120f0607110109050d05120c03070e0105031905090607110f0703020d02060d020c010212181f180809040b01080135 72
    0x1c904407682941d80c0221b61009442c0c440b04101e410002241d01101c502a80388000401003034000d001d14441e846144030000000e095500603030084410701241010b000c19403401640c201e480c400340e04000c042030701d082c072503503a00d4400081c080c81c18010007400c60a0440b40c20341101c0307101d66101095038040264440d0191840d0080b059a40b9403194040004030080c1c58602200d0152071a0b454060498804c84011070f46940001c040c5d0501c100080440e200b0b10b0424003c160091400c600030745150315010400614541450721185055403101c18071041c111400315034241034035010381341101c101440d4004a1064403c5d0044078000610026900280070f8066024001181410045007495190b041100101c80b10952054805400200301c4185603000c03a80428a01d022000c000f15000400302c12400c0c071003801ea907003a1003003000010301ca0074900e091b10650064410908099916504100302608407404d000c0341c103802c16800c0c55a44100100490031440d0240c404030440d0649152901403600b07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 946986196 1250 946984946 946984967
    0x109050312070905100248010206070e130e0a15060f0f08100e07090c0315060305010b0d0c140c0f2109011d04091b080c0a03020f01031506 61
    0x18807203510201c0d5500d0400d0500c1c0100e00a17900810100c0c411441c1f030941c07800d04210a80010702240380814090240c2e440d011014000f981208551800440c006130414000824810803c2a4a006070f00350743c0c0c851074540040440c14000082003032203046100d03e0325040200103482d050405544900c402d044d500b0040c00e64600c16010780d01e46545010325403c2c1c0c0c100340280c0540c6d40180d500c1f2901520311340e11140c000054042220b051907070361f040134012119108032950010b1703140c2e44991a51580f07040d1500007041d20380390801441d03142000d80394036070107400901560b40e51281d82506466110744101401e105000c1207165985220400c19960354041c8100341c4813501072100390101e03240000240d840380300102c5900b40d2130300039410011a02b0800e40d00c90030802414858441e00303543c0703441c0b10f2440d9107481508c02c0e04104500c0405091501c0d202e0b40b0041d80356002c940040c0c15504c884840004481e030580b942c10b110303416240182c0150402243e030188400001d000024801e41c041c000e9803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 946987446 1250 946986196 946986211
    0x1d010612021806030c130218061905210a0f0e011514030312070e01270303050702012d1103030f0115120c030504030e03010513020405090109050312 65
    0x84126500c86a05145144941020b9441100300380014496080c521065502480007015a501005405d000035085005003450802490703000c100609800d4143d510446400822078105041c910401001120200700103a207104000000c50031500740306902c8014a031000132100382000a1606001c014000c0c000c000c0441803080c104420141205010b00c0b80c83d00b1304a140210b400c4090908642e50014014a0720b42605032101b0052020f042038841021409144142c0d02d001019041d8800140700e030b070807074884d01d203107140e1001d0701009240039042c0703141225030504189841d00030600060752620012621164102d00c0d60100d20740d0004104000c0111340c0301c40d10b407007600300b4004020582d1390004136000300c42440c40d08014800b11080d140c4804004c0480d18000700110703606030b5030350160750f203c5200c100803a13150014070042503003007020555000c80a400822a42c5001039018415402101004e4040d66880d80441c4c1c100c0029007000314500d4000e42120b0b6205176188400c4403050080ba0b012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 946988696 1250 946987446 946987451
    0x6090321020915090f060a0c150c020105090d1e03020408031201081b03070513020c030c070608131101030f0b280806010b031603060e0705030f010b1306120e011d01 72
    0x4140f41d02190103031010003901525021800002809102032903102243c0d410a0100514481c4002400ca541c1070398007050620012518982c21540a8290b42e80600b0410350ba800c000032481d21150b204a000c0c1040000c0000c0304c0c61001760440640092149030001c00c09070000240c010030200d561074405040720312400c203c520034140400342c10036010030000b40a0b41a040342030104042d1600d54001c00c07041c210014014541910030581519550211000f01d5058000c540100100b0f07801c00400ea0780049030700c20320105010035607103420800d41c0c0152060305250351040d000040311115809040302c10b8000e072000040000070004072694440b43e180c00030325220058000708400e500429118122a008031445045490740202800d4542c0a25178900800d44c1d50070b40000e17852400650b080c020015074a442c0c0d6a4201460324001d4140c05030008545500100004100805400040e6048503110710704618030b8200460081d014044400c118000b640c2011500650048010741070800070003150000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946989946 1250 946988696 946988719
    0x200615060a0e090c2101080d181e080115080c0a030b31030522151110020a02070f150903021302070b0103050105160e03030304060903210209 62
    0x40100d50300c00d03141c81500003401410510715504100c9003a603001880308071010f04003001c600207a04012403c0600f18a40c58402004000003482400640520740583c6072904140c03c040c0d0405007800c46500c507901d400d07891080c1c17100001d0071520703601019001640c0244003100040d01c0d1902c009116004105440c01070504140403823400c40320240450398089610b00b03a40da034981c00c4040300030607500100c092010102070711070101008540c04082600c03d840d01601c8440c00c07164850a00090400710a0055230385009001074844119081a040c219250528000704c1c000a02402d100010b41c003112224000f00d2840b0300345402161640644e078400b07141c6c03102c90b65551904545030f5440c802c44000300300310141c14005424080611080441225405882e144240e82c1d110b4024800760301c2501d10340d40d101c0038842d1859200e040440c0044252402c00318280140000980340d00c000740008104d5696001410b0806001e4040d103411040e0000c160f840d40503110120f000694800400d052040c00100807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 946991196 1250 946989946 946989949
    0xf0e0115060503040b0103030f090305030a02031918170309090a09020f01212c010c03230609070c0c0608062e3603020f09060d08070201200615 63
    0x10b91380304580000708164142d10315101660202c00311344940007000140e0a012000c26001c000410342c0d0b0f03200f43c1c010340d681d0035482c00003030902040b080c8850030024000481425010100d40319020b90b42950081c441c466842c06100c0c0c9948240207205400200c041e08001003542e02d5800190f800d0300031f60b40c100200c2000401128040391003c8503c1040603c4101420780020305d0340300051800303642c50914202e21022000aa6023003030600c940019030744403484504c480341d00d0702036000004492803100e284810080e52140181d440200854000e140d84000501041d114541607101035401c0240c40b0521a155074006103400021544140600000c41c0c0708c2d01e10ba111000800800041ca0b00c1c001204030081038100c881c07140c82018001c0d645013409486071440b10b01000c0f4011070710002c400d41a143d203107106000740381101051007031141e10b10801f0400740d92210342e00e848070283c3c484110b5076203c0c1144016900d003c68040c04116000c2d03000303c0301d030a043c0c000032102e0041c61a00c0f00304103090002c80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 946992446 1250 946991196 946991207
    0xe060406050f22020307170f0d090501020a1b0f030f031106010e2208040f170c01080106230a0c031701030203030913060b0d150807230102010f0e011506 67
    0x12243d0303210360f00740461042e0032a240c0c202800b0a500c020b0640d003000703a5030480c0361480c007001142011070381c00001c070100142d00c042001002c0c030120b50515104103071501c03001070b440b50f660742800381884040c858003120000301d0300c0c44c4402a00c0341d00034411180d81c41c0d09011002c0d4150401c214007184240c810101031000004003035040751000b4145c4103280da9100c0c118040320800803004c050f103000320b034a84000a6682d00c060b101911060220100c598a410105442c60054005c121b111b500b00800313182d045d1b680203010340c4c159111420054400c105154489540603850039180c1c0c041d1002084550866510485421f071960090342c2d4001c0110050084030380b11102803000130341c168010000100282012544040d076030020100c001100c075a21540c1209981c043c1401e55056541c8482411070355000c1102c0c3e001609640c2d0040900c3c07800e007205803414036248104e01840000f03641c02810280e01c01d404c00c07000c06e2154081440000360b0401018040d0903030450103a101e950303001c000304940e807045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 946993696 1250 946992446 946992451
    0x9040b1e1c120507080705060103061a060304150e070801020f040501080c030f011512060308040e090312040f0f0204020a080f15010c060c03090b0c1909030201050d0c02030d0e060406050f 82
    0x345150446089101c0a48142e1302803101140e400800b0b000507008240140813550085025400120303850561070881d00d11070300122400d612451044c801d2201050710103031085035211502c0000150b180346030125074504181544207403090341c00024005481042c030b501074001c440782030301d44801c40e0326000f600003124001100c1c0510301200a4004110504e400400500b10542c02c0c280f07807049883e251419000c0e2038054005640720345000504205400c05c01c9805984102688051030410a032950110340074000a440580143c14007281c3c1d60502412800740d44209600420440d0b0b90191098041c1642c03074120b4103d44415801c80c002007036071001c3d8507542501c61050750380c4003160885503185001070901800c11000c06649443c001c00003002c909446c0d00903812905c00c40e40301c10058400b200c24000c822480800c01898900c1040181d8000040d1030721303190280e0300404c81c10400380c0224510302030362008401c05414108442000000403500c0382c0503a00841c01445035958644003a629040203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 946994946 1250 946993696 946993703
    0x114090709080a02190f0e010305060601050a0206010608191b02010b090903040504020309390a05090a0c020f061003050105060402070215070c0e15030d090602100209040b1e1c 77
    0x544401c0041c075003031410401e005c20085441c0038030380c0c56107035200c4160481d41128548441440041c41403000400c402da500001c2480c003103141c11a41d40e4020f45855040c89200d051102c481c01140c0c90000d121750303c0700f0840d1541010132034541102400c1095240c034240c40d0015510340941e2078010304180f000c2d60310590800000354501850102030000030743c070040040940307000c1c0c41410030003036003000c00000b0b50005401e4101c0c14a10894072566809000c2c07030f96980f1400b142c5604211039150f840003150f001c600c00400103103800a0010503404c24140350807403200c0303000702d03004c00c0045603000c1c5210b02a40d002d60000c100790380e00c4d030702804100d00c15120065032001c5c0800004100c2a224070084c10350754070801804101941c0c440c1082002a002e4908002c042807407030f05e0b072942d405d0400c824596100189441070080b0324181000e501d950b030200321510500d40020b505041511103411800e98410094504504c2d1507611021043c1860140c201e1072103254041100d01f4010091402882016007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 946996196 1250 946994946 946994953
    0x3070c2a180b04060b120a05040308070309050316081c020313020d050f0307030c120804200a0302180106111209101b0c03060e010c05120601021203011409070908 71
    0x4100000d00c0714030300ca001007604107031070303901c0e050554850340100320081c40700780e003041e40b80c1e9809a02400300200c01000381003028600010000442d40c040d043c0c5401100e9810300150b0403513182041415072240580850018100300030601c100454a0014041546505103051420100d00ca180c0f007644401e8512180d0340784090414070261a0400d5580d1449107d68226484035002000306829600800f20580c0418010164070040c4281e5400b60b22188016240c6401c0f1403406a0b0345220b080c5281032100b603003ca000c103040560b1744520030030001079600140344102d40d0340c0b1500103501000c0309003d00c400143c0e0242074040c2c1980c00041d003103807103c94400d84504000102d01801b01da80080c0c03038007208101c9013408662420b00c070700c9801c00085010f0121070000c076045007000c07010703070340703000d501d040c0581c5401c0580000550010030744039803d0081450301c189840307400c0100d1074100e08015a141c840b40020001490030810a0a141707000015601080c80b42e4911105940c01e0815108580c60342c1c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 946997446 1250 946996196 946996199
    0x61303021c090806010609062a060f020d020c0c130510060f0e120109050d0503010f0306050c0d180605070513170a0606060e01030b04150302150c0303070c2a 69
    0x31610a607072000000c152428442c260b580e205110b00d40714082e8802070109100c0102449007aa101103000c090008100188121000419070b10881303607413040700640001d0f61003904180c1c054140d0121034140c500d04006640b24031580034580d44480380252054410b00303c00403004000e81c660b018080c8114254060340080c1498054251070710242400b0716001c00c204604134810b15503800301042008030903400000381402e090b2610503c1d100180603078009210051004000c60190304e6604029a41c1c010300c04100c9480314180f0211038041c2c504920401c1d402c2012402c4101144d80c1c00080b190b0046406200075203071588152824442c400d12110140c0c0608001d000c00c0e00c003c4108042d80d540c0000b16041c0e000291994030464145030800310000c0c0000c40e1a0103035681c94011aa4610812103040040645041306c4030140c00030b0f07100081c01002c4c0310b136003002841c91b0082a5040d40309100c01303a175541d151203440100310121505045428840080c40403a94000c403400b41580300140b00700219106 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 946998696 1250 946997446 946997473
    0x60315031a070302040e040b041b0e06040b060f0a0305191a0405060f120304080c150a180b07120f020f100e0c06040905060f1c020103090204020403051e06130302 71
    0x6038000c1000301810303000c000006d1003030b61081107644034070b028418140c66420a072030010180d40c038210340c20980c0a41040148181c80ea003030819034009100b00c5001035000d80700340105141d4004c02a4002c100440494005070240c0c00d500b00c00d00c07030900c0e4030038251440640725040301180c1100f04a1100c0c602c07038400500c45420660f00194110078020301c01c1e40c1c1d10342d9100005d4a81d604490003600789400c0807808020341c460800540184c00001c84000450078030050080b4841d004480c2c0f090100316849002000b450001a60034026004600c10595144901d080100502018041c1c0f64001111f40c01c0701c109040c40452410101c02206014040307a802051604000d084c0e55001d07a100c501801c03046813051f030f40781d0004100501910b40d011516142a408008040c0f265801080c02521001d00415480601d88401ca024980c2401c00181c980818004100240101e8000078110b11804100b03840c5041400c1010380658005012602e21303a54500102c8046000200c004015030700841d00616032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 946999946 1250 946998696 946998743
    0x603030f092702071e02010801142206080610051e0f0919020d0b0907140a230c0109020a0501181a070503041e061d060307180f06031503 60
    0x20400c42d8000f60420f03600b138a680f4005a0b4800210403240385510001c4210751704403091600401c40b11092220102c240e1010034030309180d407a1244182c01600e014803000c46210f62081020f0030010089501070700d041f94108200b0312180c040c1c10f110381c806450f0f400d20115a401c4120200001900d14003500c1c034000c00380100040084c010181d031803a0f00b070320300c0b0640c0800c0c406041904c10192011a00030b46103003d00003c01000f41c0040b00300614814452280e190324012614101d1b000e20b810903a19286114425101e0b003a00c09100220f00002100c4a281105400c03028070300b030088407090f0605507680015241d1040f00a513a4a00c00354207401049031617041085200003144a5810b40e00e45901d50386c81074210b0b800f81d0800c420501d5210390448810f54180c003040c024003614100303898510382c40c800003045842c10400087c442d000c000f0000d41010300c9584040701c03281c003a0005a034403907180c60580c500b0754804e00501000078504018482d040b104c2c1102c00c0102c0303410903c0d070040380111040e803940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 947001196 1250 946999946 947000009
    0x6110f1b1005190501090b3006180105090c01020c04200f04030312091e02130f0b040c18050d020d050a03080f16140306130f0603030f09 60
    0x21500420061079003070310481c01094030a005403c48502d103103100c200c88000700c0b00b06801c03440c1900e1038100703214965140c12030702003070078000203808041c1c00c2c0311300b00d5a83c0c114003400c00024040c050340c0c0074480c658413080264040402c1c2400248030507034442e1007031a664403040071154016070040462028900700307a4407030500d954801c00c0f20088000404680300c2280c0c8940d092442d60440010b0810516511103512226410409018407454842d51290400c1b90b0b4090240280c201d4280b040c8011586c8041e00d049050f0b010280910510755640c0b0b12900401010700010300072420b01c000880180d124071000040582c0311030008011501388000e001940c1250a42240c102c510005240003045003044141056846a600e5100521340301031719805405000d48581c156115030700b4807074092908200070044801d003000807907460350344003400a1b020a9512004900d11840d28a1130068002d01d03401c51000c0e240a61115410054036a1084805580701e1040507406850340741c078202d0381d06014204d0507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 947002446 1250 947001196 947001247
    0xf03110d02030103081806040612050a090f0c060e060c0703260f0a090b030405150a0b0d030306050f030601030c0e0603010b091306054f050a06110f 65
    0xe04110820110404a902c03e80003034910200105000001c10040304800060302030075101503013000c5c94070101900900141504281d0b43d901c92000441c103001d00c1d48501c00c910380084003d815081c1e030741050fa204242c04d0080303100240d094000703d025418401f044906d5a5000380041190514503224044001c1c00b18074250495908051807182040f60200a460003100c1090016540c108602c8064400340065220000f01c110600800000c21400701d40d800f00784501e40320b00d1201c0d03521000314800610064034640d90080980040d0f0b4145641a4800001d41d5801e590181401c65042c0416658040074400141501d10808050122140d802c030116009400034001044110344000001c4481e03074212034851910550030116400d00003980075040c1c002844080a8002e0f0031a076015000c083c0a150803504404148420801c610781a4080110b0b80000a8801e2103108200c0c5030042d00c8102218047d140282400c00c90034602820000b2200550701138412a450031944150400e9003521314a03085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 947003696 1250 947002446 947002481
    0x71202161202030a270302010f020a0c08030c06090f03031605070f11030d14040b070807061a12010c09140d050607020120030402091308041703030a0c0f0f03 69
    0x80300190910000d80140d1403940c01868407641050401060201ca4010210041c250100f9030a80c51100078008000e51342c080ca00301c2c0e1280c40040e4240d2411030f004100405c001140000014403460210252a420800c0810b4480c0c41e10396500709552071030b04a0002c00e0a800c1000030030032548042604041d65415420420f007001416200e43d03c88100208099503003102c061001c032001e01e428090102d43e14114140340d8508011901000d000e40a03d000d1405907940003d564024800c0030f4056030074541d0300000900a03120410310340c040e00801812150301400301d540702c11009020600403d800b0034500d6417240711081c40d11500d508490800794070141c0011030440c015011039810b0000b40e07c64901a000415604d009000005618112841c1d0400d001d10a00030b20005a0301c82d82c045810815404211b82540d05900701002c06109560003010071800c441c8074003074032040200145100f954040c0080041d84c010b41d80c16504112000e07800300006590350f00c40b456003400703a441f0f041e102e210310040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 947004946 1250 947003696 947003737
    0xa090b280908030c01140906070c03030209130204170601050a0315022802010902090903040e012d080a020109051804060e010617030d060611060103060905190809040c0503071202 78
    0xba06542c4602c4a29840365101c2d40f07500c9500c0310b074629651700420031038014041d610b0040380080c40a070711a4802001c1540011700840d00d55a40d5003904000109110115965541c40212850014802e040000307540a4a000001c091401d00180c004031782d000b480c02c201448140c0c1080c8000c3d07100340101006030304201c80e10421114403100d40e00d00e40b4410b800004507500180104280007030010b003031003025400bc100510210103000811411204000c003011240340c0d4a840451a654400391101c0d0507621300c01d000100440c0002d80241840e000f07032224241c60781c6403010300040da0541c0100b10280d50402c0086400920b040c1c1c03081031400080d0000142c02d40d103403aa544810138443e6030304070003030344042031000d01e00e0802c0c4190001404107041560228201c503170081d40341e000511019183c20381c0d541e50101400401d0140f4070040c10742403d000c040200c20315100000780c201e0390f040c030300541c9402c10b03800000780901c0c11a0b0080c001b607100c0c070402d200800c403030300b02960124050401c0c1d41d803031112 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 947006196 1250 947004946 947004959
    0x306010c150207151b030513050619060b040617060406170c1e010912050703050d0801060f0e2b020909060f0a090b01150302090904080a090b2809 64
    0x1100c1c0794000000d40d9803042c81c1000c0030804001881079030400d280c00480c400300d82d05103a680114110504002c125a13407261418418440e5106014280e805850104608014594400000204910810800c07603803200c255441034007a500800020404800705441c4001c00c400440b94071110090020444985a501d980f0700c509044024800c1c0d64403240d001c00c114506180405142c44080c0c01ca560602c0040340000c052020328800c866441400000c00e50501ca03040c441b5002440c1c1020484c1c160b030031080d00043c00c00c1400d106010020b1041000281d20710711a4400a076100801480c1002d81c0803030181030f2422001081060300d040c00312520710740041c1c940d18016480303002060050004c0d46003036080030381402c4008041c0016a4508840c260028a1035014141980c140c1c43d00b9460881c4c0310302080c0c00901c181f07006154410020410032080102a10080520b03440c140c1c0e4000c0400e544440854040c01404000a00e100c40781030003001401c02504214400c1031245410038445a640343c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 947007446 1250 947006196 947006213
    0x80c09150306030c0d02060a0507050a080a0e0913030f0503060307090e061005030f03041a0c0619110a120902010203070b180622120e03030d020d0c02030c030f0306010c 74
    0x28254001802004200c510724040c40285002a130544041c0200381580d400034604c1e10900d17400600388940410454180b0804100348405d03680d20030100e540e501002d4101034400c00034000b03030600c40c105400000c3c541000c0803a000c4542c552644491404401000c82616142c02c014041c540611441000240c1d844242c0034641804c0c2d207640240000741060306880c880084c46411070390090380054807c180c2c4003000005c60341100c000210040d00103a1501450790b552042981050142c0300c0c01003405660700e81200a65501c0c0c4180381e040142c000d02d844100c03030b02d00880c40c654001c83c901200700c0e1041c00f503581046601510501c140c0f441c3c000d003582e030440b0f0b03000c0a6407030411244411910520101040004e1600140e0351458041030100540d201d0380b961084510041040f005007441c818468000c440512224500400741c03600d607421200008029080b4080100000381008000001e190020003250480701c65000a94074129860355000b600d503201030043e6041003004c41c40c86004c1740200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 947008696 1250 947007446 947007469
    0xd1218031b0b0901050d0f02120405240709120515010b030714040506070201230c0109060b0901030317071e0c03170124020111130e010b0408060106080c09 68
    0x24000c403101400c682200c001c84903919001070603a107104004500c101da07000f400743c42844840300d50205480c00d0450407030019000da03420180c1c0351000c0390140010040042030240300e4104a645220f00300301302c0080000c11001c2aa00480811804203091004681c0a403145c0b48550180741101c191803101456035001c1c1400340e00c03041d02c022020090090555100d10380340b4012046070303851030420782420001585ca11502c04003e05002810189095541d0484907203c0c030a070f00c2c800b000d81c91303c5086d1450b134040c1034106801c071046460204070850300c4c0390800d8214160790b0143c1c0c402200004819034180360481c0039218000340040540d40420b03000c10151200504809039482c0100c044103480d01418958886000000549601c4014402c840802880c65000500b150104d000c18405800590040c00385001c0c00c02c02ca2000210004040f1440059071b0460350340c00001b1100e81c0e603426800381240228004c018050b04070400400001d441540007541040c01c1c2c0803207038a03000400e030006a080740700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 947009946 1250 947008696 947008703
    0x1e04120c031b1a0c12060f01110d020c210712050f12040e07020309010212210a0501030c080f0a03051803030328020903070306180b09030c070902090d121803 69
    0x401c24800e003503041c3d444810b0b00445000740443c01c10444905000c148a00188814042c1171410600f0103181e2084140945d02c800b44416603540140c650030094840d58807004150180c40e403900a940e0500e42002c040844c0c0442c6005000d00d40d0601005901084030501c00350313101d100e00300050b2440642031007250420f00d031003040c007540c0310b02d441951000c01e90020034500564109100c01300c41641c011400d03401c40400202665a03e41400310403100345920306c201502000508000c10985180e168041c1d0305980c002c400d1290342d556500a49076035403480c82ca1485180d0002d00da0400001c1c0528043d102006c038201d1048000079114012a1071600201d54410080c41141003840301f0841d40700c1944581a402d800039454040b100000c1317a61840300d44401003d0315550008880d003007a0b901c940d4036015a21451415441c01d040a01c41e03038a03001a59085960300a108000a40391402d108662200a01030300300101a6050748a40c20b86854820001050007409000c6d184091303002d0b80d4030000b5610 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 947011196 1250 947009946 947009963
    0xd1506030c0b120f07020c090402011806031e02030702070b09030709020a03050a0e0f030f1b01020f041508042001020c040513111008010323030f031e04120c031b 71
    0x840b10000c0c1505006009001540003c20174007201ea41d0214104802c004141d900300d819440d1032004844e00a9800c140d1804440182ca011541e154540c00c2489040e1082400c55001060b8424007000c07403201395107540169009481c200090801307107015140c0d44a0080c152803816903112001d03816a48212248000a0303564010400081e41910a10300180b141d100100000c2c1880e55500fa900d228041c0a5201d4610100e595500800300e040200050744036030b8020340d110180e00080b1522a00580100c015a038500961030325028414100f0314411600700389422005403420b1458400744600181907130440c0100191140541c46900580c2d0060f103a003081000041044d041421034028138960301d0788100b96908440c040305a00c0311046041d6038022007040e05042e42c501881440d1440038540000c180030108040312041007510143d849000c071300340c0e4a4420000007890440603203045400511151880c10580c03101031183c1c00b580c80961290404075940313a00c0420a03803c040115900322081003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 947012446 1250 947011196 947011207
    0xb0a020d1404080405010c0503070c06090e0f090618030c07142704030e0316090213081f05090102160c0303111c0f0c0212101a0d1506030c0b 62
    0x842500c1810301da00824481000103040c159a603900c54459482268100302554180c2c1d402d004040c0304179070b00140d200b0600e240c216075492000d0311280b1f65114110100020000144000e51030b908001d10886c0e03108054049a588c14000151042000d01c480e600740c8000d002c03910341204204507500113028000754516a018075041045034490b2651415094220708600714038040c0c0c561281f080d005685410840305100040000c83d141071000d180706000480785c9e5400080c03c0c0003560042803510008204403006079104c0e42666a102c4000300103c0514032010b0502c0301c15140d96001d5a0002c881c00d001601c0c0c480902c20414060a280d00259003960780650f00300105a0004800004007504c000079000f0101c0b004049002c91a5040c0d446040c04008401549500e01c80d045a102290b8024400740490082d01c2031103a40f510090040346100b0314140c20070320346081440caa131806000050000d05404079690750301402c00940b000ca074240a40342c080100004400001903800381141191882d10750 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 947013696 1250 947012446 947012467
    0x180f4501060f1a0309010b130c02010605040c080f04031b051b0a03080d09050c04180c08120a1b0507030807121701140111060901141b0306090a0204030b0a02 69
    0x5031001d80c000380004592500800403c4004007940f0880c44241e006240c03640d60758660315000d00320511701c0079441007205000404500040d0710218049020340d008210107901c50040c00101e0700d148501c2c0d00414111000540c46c034800316442c69225100346800d1032401d080b281e0b87c0c21210b0781d0001c22621a0408140f20b0580100002e4403050711b034013111340104151840d00d03a44914842c104851040c83c1c0c0f5141c104003400401c2001d55918140a4410050441100301e03071140b101c02000110340030032003440b0019402c080040c0300c0381c4070b001c0c170000c0b10324150f01d0050a43e443d414151100345441d01e490603c2c0f010800602c00c0c480118094480341c1d0766001c1c5494005c6160181c41280420300140c42d500c050340c41989202203040d5508404030360f110300c1c20040141c502e401d006001041d00e12983c4100030005806410003072a46018200759513003611521014502d0126550158140342001c0c000104645420000560401c841d40401440c00303840351588178040d603045030454203c0d44c0028500492 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 947014946 1250 947013696 947013701
    0x15030605090d050915090d0f1203050705031302010c1203060e090f0a03030b0d020409060b01200307020f01090b03091c030903090e2e0302180f4501 65
    0x20203000d4014200402c098000506070340aa428400c3c0100c40b48490340e00c445860b00120b8213100c100401d80318100f0018a00401100880740c81181c41c900114480071256000780200782c06203050361292402d694526408407490858a241a41000020383e40d29000c10500140a00c07190a42d50b400300c1e40a0a0002c0543c10f43c00242c58141e0542c0002c5071448a40c0c004126102590ba2514001c1740a01c144d038000f8401190804020307500c2071408111000300800392f44a1030110900383c0b15400e640b031034a4408403c40a000403502119081084444010310b00544041c60782c501c141440d00086446540151881e0000c4415068580c4114407140e5131211921300748081e070003546818448150560760061952800f449004003201640d00407501c8410403141705490040100c92242c142d100d03e500802120000348016401209110b0503101c40c0040003400c42c0c42055004100c2c035050b100c10082c2d240c4884010482880c0c4000840c01c1e650440302020000114000003111508540c0018502800c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 947016196 1250 947014946 947014951
    0x2090108010c0807080702030403240510090c0518040e0f0a0510050c0306010c12270f060c0209010314011104090b13200c030904020307090e0606030106090e15030115030605 76
    0x1172100700c070b040180303203540042202d068035442a20041001c80c0c0d0311421166007400090114550b041400304200c00840e810228200c83c00648280440142c40a0a80d40c52080a2004800b012000302d440601e0410703400450705c008040c4100d6203102c2e82405414241558101c0440310780e003141d04030180120143c05000c2d0091840c8902a141d802e0040c00601a403081580c000c02a40044a8880c040c6004050550440c0e1462610154424641040e4241180c0398041c84250800b51140814800d01c529040140039070f0181000d801a400d5849012010804002d041003030740d264420752031164600000b410003032440c0c0f600401d45003007820400505000f00141e00f802c003454000400500c0c0c20240703482d0b900d1030065402c80e507200b1142c0240ba013103100f00000143c00c640000300303206510340c0c851007440889120705251070b01600c9001c10400548000c0c800c80d80003a20048040c40746142c0031803840d030000102c0000110340088240401d00b5500f005503d050080000c4608000b8844d0358040c059 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 947017446 1250 947016196 947016211
    0x4110d110c071d040605040309051005040602120304020a0b18041811010215060f0604170f0f150604020d0f06230a05090f0709030b010806061e0907120902090108010c08 74
    0x46483c4020381c00340307907100e4008001509580d16070011074249402000701401038000501841005440010041c1c503d900074442c490042c030806425469100c1000140c90080741d00802d65400d8914020890559810480840c11001241e0504145135903e40c85520032900c03901c00d2042c40d8038003e007886220f00c000c03400c4a5040d5007000c5c10040314206001c0704582c2c0003904a48800b50764159001040c4070b80a41c1e005000780d80004400c0c01700c030441c00900c07a20060500c0045841c484080c121141d01c582844c20420388038841c80c1c0c0451000d1416030064003c4440311440006c000585198407401c0e25041d6000f51064240c944440b0740034603034a4482c400d4540103031103e030390382403500c0c020036a450707001440001000141804150041e1081380c2d03240040d0340010310500d25507102c403911031312020251180c5110715880290600c032003044503c404e00303815005100d46002d541c0d204c402ea650044040c22030362141d40e100c00580041e80c450240d903019106031400000c40c100007440103000d00c0030140c840d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 947018696 1250 947017446 947017469
    0x1d06090601080c0d0e01090b0414030703050414060702100801050102012403020f0f0907091e0303050d050a02041d040c080102040f0b0c0703211205070e04110d110c07 73
    0x21080c1e0341c20090b15a0425800300310b0316591481c44401c10300405010350b0340555075003070035030402c00d00c8130400106000358020801807085071212140c55a8a200d00300004022860034002040301d40841441941407140280c4043e1600340254000b500740ca110401c0e40c40882c034024018070003940d0921800001c99101c2c2092241c282c0c10007642c4001c07010500c0000d1040c1f128010960a030b03120310804a4086001904105050511080240401d685030044d1500140b5a03031604400c0024062950b04813505074440070300e04001185c020029003001040d1100030f540070040061190495a075200448501c5170a1054905042c9054a0304030059880800560300512007481001d0354020480d080b60302c0c10350031613a51b29071804500e0403c40c1981c0b000e060980801d881e21500407002090900c46822550f0742c00192a002c41c01400301e400980d041000282c04c54580d00b007034103190303100b0103205d89413901050501100712481002d4480e007140d80d03030342e01802013100c843c80d0800308071403000b03801c808218 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 947019946 1250 947018696 947018701
    0x150606020d020c0d02040f060e010311010804020f04090311030309100e030705070510112a011e1103040f08070303020712050d050f070203100e0c1c120215011d0609 72
    0x2552029140c0d0320510501d813400740c0e0401c55a450f84002c0c2050300301d020030300c0b0003650350381c20311640700e800d10044e60082c445071140c081c6903106103480342c0f060703500500c00c0c1c031040390301c0381440000c005400c011018000300c50241009940100040e502c90100c0b900245a007a0000303d5000c140c03205440c103e801c2d68410301000000400102d001000d42d801076401c00f1802c03200700d80460305030400000824460003949d600e51820585441c0e00c090185445401c41412960540116884090040540c06c0300c1f000940114810303200300e640e114030b03004801c00c42e41842e0329105d40a90203250365003c4c405d04d50000900f041010307010f001800040c4180c42e01600d240f0901d48489444050344000b40d400c0020000740711070b43d44060001c0d9907603030f60090200e0302d5642d00450010000e245081c1016018070828003c04103d06e80400e0010105851a414060443c02555500004ca05043c0039006500800b03194008040c58030360f0940c003d1503c0407030000c0403031a901c030f0300d00d900c0e00c09058180901407070002c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 947021196 1250 947019946 947019973
    0x7110705090703020f0f0a0207090b0d02090105010e121b01021204030506010501120e0a0b06041a03070b16020d05060a0c030b012c03030a090f05030303060913020d0b010315060602 79
    0x44076501c41400d05000d070b40c03869810700d444410300c030b840b810014111002c0b5801e25103a43c0020014151074613080104a8000d0003020454650100b00b40258440c890000501695214907a41c44807500c0181100360808404085141084100403100307621101c0160030080070344e810810074000c01b030b0007003810b45054110b4860700d80300e07603050042070b043c400101c030400c0c907143c907a9002c0054842c0352003da40f4990340c6072078822004001510307241d216508100c50040d069400803040c105440c0e0003001464417a10b40009804240c001e20740c040b40c41c5030a4100701003d40c881c0940c21102030b1055000c3e0003645011000306013101c001c0700440d810146007101030a40380c0d070800240304403c00c1da0f00160043e450442419400d14198a4278150140000b04000d0f5515811904081c1900d03900408a2a01074582d07040c076559000482c0e0340e41d417104000d4041601c00243c1100c007241e40c0d0000c0c0c1184119052031b00c0700000803100317038000ca8841d042c00240803001003c038412007001d80603910180298203460702 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 947022446 1250 947021196 947021209
    0x1b0b0304030516031202030f100b0a0e0d060b030d090305010f050402090103030e0a030602040f0303030b031204381902070e01050103020c0313061e0201110706230a020307110705 78
    0x100d005022404000fa40060601030071900c40145a22034095540c4d1411100400c4d05100642d08440380c00303000754000c54104000015541000000d03030301e480101c01d0580411000030040d003410341e0070507662014800c8a841c14091109115010780301c1900384e0b881d6103041402c460307960031600c603007a19090600c4010b960741344266045982524041c202a506400099084d20007a400200200c0c0300140016404090550403012640684c50400c003400a01061503241d648945407107a500c3c10410007842400100803240180ba004a0103424511481e28488002410544200c000e95440415103218180480b03c90007560381540c4060054140f6040360080d8842041c0201e40c1455000303e00c016003842e0800c1510542d5a4030710503050070b19510342015041201320314a42c114401303d5805000500e0050095041c1004034403001ca24040d03258031a00020a41e081c07108550343c02050152081521000ca654040c6844100059407410041000b07040050b0000d10480d5a07088040100130b940d40f0f55 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 947023696 1250 947022446 947022457
    0x4030210030b060331050105011703070c060507080409020301061d1815042a02010606050c070b0901140a11070602010c02030d0c0306030b1e0a0207051f020f071b0b03040305 76
    0x100c60640808105d03564806101c22040302c1c000149840d81d03280014041c1c15000141207490b40010301048450001d0460784910401c0400f403d03807076640340c040122522a000a0091a0117110080e043c180c07209410020781e07100780e00c8100051403071019030741c00c9451003d800a401400f298000f41d22074400d03222244040004059403500200000c4104584d00ca0340c05c041c81d0704003d401580448000500380f050355036480b0005000542c85c101c00464007070f0240c0b0481d1100c0d501d02d40181101880c0c4048c9600e15408a43c456040080200c00350310414801c0c009000c04a0903078031803460304607847c5405480d049965001d582103a0504110880007500801240d1001e10204400714003070703407007042c20303400b818407540700502980100003001201c1c800100390010003080e40000e204251901c40454043c1d001e01d40020f8005d030084000303118840b42c0c500070340000420b0510094100611b00d80c041886410818060715100c030340345c61441000845103001c01c01313024403425441c11030600d902d0050144c0640c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 947024946 1250 947023696 947023711
    0x1090518060907050d020703090e090601081b0402120a0504050c0f060f070c0e01060f1d01200f1002090f0d0804050d060204030605040809030d0905101b0206040b04030210030b0603 79
    0x341d4011501044c8580c080b5400c14255480556440d14240b03402442024203100324000c2c041c1c04404113801a802085440c1210481d034001c0c001d6024100062100b040e040720728961055003000b0000001c02d103105c0e80703172140f01a180000703141e1401e402d00b1400d24003140f001c07e2144e05a9041d920080d43c5007411359104400e080b224685401c000c0c03521a10640d4650040c6c400c8211000000844035808440e04440148581e503a03c1695a8250101140e0405000b40d80c00f0914441c401d001d5001c0c018005983d802c081d2007201d18580d5001e1541d800c10489590005c807031900082d440642e4141900865007004043c0e4854005403801c0e241c3c803075136000d180222403140340f40800000c05d01003250140d4000d160812010000c40c100f0b407030040f20903440104058000d00401d4180c1c18914021451070045400207000d0310221541a902100c80381100c444224910212424080140e00e0b5200a00064418150082d9689040d40100a0510104a0f603601003604220782c0000c0c5840300c60950350407006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 947026196 1250 947024946 947024959
    0x509060711011103040605100f0b070809010203120f090106080c090c0f0705070e191e0e0109150c0e030d0c06020310050913060b0f010c11030c09040602090109051806 73
    0x12000c000ca40942400f6660715184200030043c8010300c0b82c113600240c006c2c2d404800e0140300f26070341d5255084c440c10b6445000749181040c40400042517200d0003c00f62840144180c902d4502d04030300c9209003540030350341c5225034440301c0204010f0080912441010745900002000c003080c441e000074603109801405240459001304070310550140c100d041c0c0e00c034554000309550760141c50f41c11301400d5001c101e501150700080014802c0801949226000d280003040d102c0441c110030404116002d007840d14819a1507658524810000c01c00f0780901c0800000c071b80381c1c0803603080741303015008003142144001544030390402003075016015045158042d81540c05400540c0300c0d0307566000420310160f143e000c02d4102941904220f8040000b9482074940ca108070010400c0002e410280942d21030100c00840c003103030040130307100c01007015044070000090307005040325502c0c203c031000b06400140503039041300c0342600415131416a60704006000007508041d1040300ba400c042d2003403100c080101408140c000d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 947027446 1250 947026196 947026217
    0x105131214030c03030603010b0a0b16050c040218090609090304150905040f15060e0a050f060903030a080703180c030308070e1f033c09051b030d0305090607 69
    0x20707010022880d40c521542907a403200c01c0480b032680c0365401120f02038403e518000f0317042d003d0715025207403809035880d01e00118188070a080d05c80404042e00d0070262028030a0745511f001503036a42c0000d0200e00380e04000c1c200030040700018440e070f40d08041c1c24184218286000c20284800c00030a0320102c519043d81089001607841056450038150b4205c0e5810071f082400c1420803507003907004020208a1402c110081569030202101c048541a02950707020174a00c1040007945005c1301000078044004010a280207031003000a0320710b50055142b640171032001010001182c3e0542b240303c2120040b5011100c3c000d007640d0715102c122429002c01410310090001081c01140b0801410f00041e0f400f40c18003c22818560147c02d00303402c442c11010001b811b20f40541003022043c1c0601c603818150300c03848800502e8021501c00c21802c1100030041460b03a070104080032888c104032018622188030800d41000140c403003410f0600c440c141c2001c00b45420403007485400600011481d51146035440c0440114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 947028696 1250 947027446 947027453
    0x4062307020913030f0e091501030f2a03060302011e0314091f021603030e120409140c030403080114150c340315091b05030c01051312 59
    0x1401600d4029400c00503860801100000e407110a0303079454025211220001c50905003285d1811074880728a0700594084045000d04480c1c1d0450001807905050104205800d2241101202d41c4107400541041c244203502c20b4009100500d0003850f00b981c60180559400d540020303000c070a04400c000303c0900d4040a0b007240a10a0b8006106451900e60701c54141c1022840569035003a400e0140c0c19101c00500c0425062920340300f1218508403012101803000320985058000700510300039501907010702c08018558000100042018114070000001c4000e00100340c01d140907001070014030284000c006104c042038200d85440c1c11204c0380e41981e42d020001e5400304200104e082d8056010020100740611a00710120b05d500b0001101041c820740758070803540d0380005010011001c407002d00e070b5001c1400487e00c20031420702c0360b022405012440441c136a80305081c011086115000700c54040d8001c1c00341e443c060100c16115102480d2243c02c0440384001c14400b0040340c85400500124640c3e034901300f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 947029946 1250 947028696 947028767
    0x901030c2a0618030804050d1803140708030d061a180909030c12031608070c060b011818050a020f0d021803010e0a03093312050a06090e030406 63
    0x43d0344242c0d0007500c280392443c001e011175405550444860041c01e030102003040c403480001d0742c0d500c00405280710041c5135464800700c40e130798450112540d003d81d0002207900c200410081980c00388040c0c00094030b41c940b810040004e4540401203a058a0801003a2036002d031380403400d2a002022240801c45071560f458251852081d0340c403409540c0558202c00f5182c1c85580301451081e90145050f50340004481d4045039581e000b281d0b04404030340d00d65499808a80d90b5803100f4002c0006040c4041038000709403403030700403040b15446001e10044507051240b00134254090345d83c02c80421074003542845ca800c1d4107800716008982c242041d0640c049440d281f0380701c814100190302c0d80040c00800c901e00300e986015840e142e034500164046244c845c0001404030034545180c1088410076000001d0302d04070107000d000700204006c00f0781004507280044001070240c0c803c850260724000c000240c018940024001960701880309108260020b0108200b115040759604802d42070b00d010100d01c40414502941d070f03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 947031196 1250 947029946 947029961
    0xb0a05150f0109050910080c040c0516050a05070315150612020c03040b0409091e08090409050a120305071805090a0914030f0307030f0b03070b0913110901030c2a06 72
    0x5c0c41030084051101204244070721005444100c0b050310b0301c41c5c02c8a0244010780344031010a0000038010451803072000144000112903d20070000d4840100c1c0d9074603a24505104c90b0001c0d0b8002d400c00d8040e9400703460b180304489241c02e104d401b4040b06460400c7c050225a03210700340007440c80d0006401d0111180c144101c401801c071101c8090f84a980380c0f455140103000000c01290301000318210281e10309501c02d00c11095660040385540741613900000d200c06805921022a014881c2070340110018502c98440782c4012a03954000903649810f44004040d584079145050780c02c24005828801071b01c6031031400ea0300144226003c14021501c0c40d21030301c040d0785046c884c00c03d400003265038090812501e00860050005903001d0100601c00d0107860119050000400d82c15486580c1c10441c0c0c40e03401e409450254401041c80c44400b4403040282c1c1680c10000021800c1c40000030011350640e0988226040002e41d868009002c02c0618401051900c420303104030110300c40d42c1102810040309800c03804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 947032446 1250 947031196 947031199
    0x80a150b0c190f020102160f030825030e03190f08031b0f0a0806040b0609011d040c090302090a1407140412060c110102090d020f0d1403070b0a05150f010905 69
    0x1c659420b60304002c0320440040b48103d0041c021903400c03072020507000c954a415a407048103078020043c916612003403240c1c0203046c051200008400319043c624000e4880c2410f60b070080d102c00c0600080c00301094200034040c482000081010200750011a4510a104683e60350181000f41e40e602d034550341842d0000405690340c054140004d5183d42d104e2954090581c412140d19a9501c1e03860310020007056501c40c1c200b568004005114061a9601c15001c0b802051015000c0020011030304000ca0107030340c051070300340d4080b41d4482c1d01001181810b500d03040d808021018200005028902240d0542101801c0c503810055038151904003502c11034101d8000b40f5080d1104000c202041c5002d01c00780c40507c0071701c1c000c60503038105107001b90410300840d080307000000e001c43c581d00c41c560300b00403003008981c01158100d4840a9400009014070110210350030108000755141e40c03003441c1c440140c600003040050114100700134424140d40c40781d01000c0310001183e0b0304c8852004280100e4102036140d000c207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 947033696 1250 947032446 947032483
    0x20d06060b1308060603071206020310030b010f0602100507081602032b0b0d0302120d02040909030806090c0c1b01032004091503170f28080a150b0c 65
    0x22880e038804085860807a0000004d0311040c0e81d8910400d611058244100d032644050240d80c1ea0008840d6401035030b105401c40744020250b6201c3d00c50508104090700b040e24100c500803802c5c00a5501008008040c00c0c81c690144154034248100425510000e000c0f000920072402c11440300c10300a00136200c03940c0000121b4140500725440a4104101280d8100c0342c841ca004184082030414001003a002a0150000c040082c0811400d60556010144201030a035085c8400300d0039003480d000e8940a02d020340c1d02c107030840c1005000c01240e081c0203003a40809580401010182142c045502000d00d035203c0f1039000320400b8200145c002e4051507121407540880c80004a80e40307880600500141c0d4540042084800c100390030f11234003940c0340e01001e00040001d0000c0345004c401e89005050000040421500b000786405030608071500b183c804500f01c0c450751140c0d0b00c0c0f041e406800c1903440300ca800e0050200c000411065107040c242409040034221b00001c0742800c07880c00704010919500a208107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 947034946 1250 947033696 947033707
    0x126032a150703020702360c0f161106040f0b03130204090f12090e0f06040e1606120b010e0f0307080f06040606141011010603060c080915090a020d06060b 68
    0x100294172040049202d560019992a03074900248004104041c103580a15241c0c800380c1110450410010504003202e481000348601c0004000043c0050340e114961100c46000140351025200e10003050060040b40c040c4003c014900c044161300003200c03610404c49540c3c1d01e400018180205012034060f4100703050003080c000700308801c40d20078440d5001c1d0b8130120701201c0d00c1e80c00700c1340c8062034450701c100d004030713000401d044128401e03055411120003000081d40007905540303181800c071003000d0070405807c07081e020000b96411040e10710401c0b1004004000001027540040c0c000f0100c1a81640180c2d489201e1b4490340d1401c21090300504803030400ca40071070211040541d540c84003150102c9406003441000243d0b8110340c00a185200e100030600c9004041c0c21008075900b54900141c0240ca40d211000080451140c1c450812407013640da0f075600280c5418051030345498140b0a07100d45004c0e81c84c040050b503440105007151115811a8410584000c6081900180c6000d41158071000c000150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 947036196 1250 947034946 947034961
    0x10605040614090105010f022a030106030302030d0b040b0901060e1504090207170c06010e0714030c0a170f01051306080105090f19030c030302030c0d050126032a15 72
    0x70b8210802c804880d1038250b40c1e01d034801101e80500030000e4402591142e12a82001010f500c0080c0710200780e4039080d80058070740c500003402c0d00c40981c030543c01746e0800a160100d1101c00d0241000d114002c1d10280820400c00c0049000f403c01445128204030b4403003401802036a03020041110303050a4111241c5a40c1c03501d50704802036002d000101c80d03031181d6034401010501d5440c10f994180d110000600804d0f882c000c070400008000a00e0b4400300200c8450303468000c1203c9018500a083c689403440d00e601d40100082c00e8801503841c0b400e107a064003800c00088402c40c0c0441410f58170262028500c03030001d00a140b000d8011600728113425400c10041001c0080c000544800e0188084200c801803035034811043c00403000b00c08003030001107050210701d01182c0640c00030f54102500d2200a8038000307056030460221502a08000ca21000b61080111510351404101c912000310402071071a19901420700c3c00501e4000160704080c191064010542c181700340304036120000c400c2c0415030715141020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 947037446 1250 947036196 947036219
    0x501091101020c010801080601060f02100c231314010314041a06090c04150e030a0f05060a15090b060903031b0d0c020102102c0a0c05300106050406 65
    0x5244500510500c0c0f00e0302c406610a01c0030301e040f1044a00901000d90901300d046601c0300704001280c09622604848054088483c0b06018803840241c3d6400344034010000c200c105024010086c1241080030300c5000440303080007900d0400c556122040da0018000080182c02505030341c6020600440a141004180400c030480c000713820f60500040c042c1603490030100400303001e065030860400842400140300114904040b0144c200c1a801c0202819031800d000034580000800b049038008404916a410014200105038000b031400300c0038000d1f0a00088020f060b10713002d10403200c140c0d481e1010500ba50301d0b4041100c00d42000541581e0365414020f520240320640c070044140d103803107020701210b0414424080020155070581c090481c0d40c0030084150f0180c91160017580410180c0c042c01182049a0300054882600c00381c0545001c0260341855100f07000380d41e20481c09105950b210349891581c0301c1c43c041b0381040c5200307010001451042d40b07078010301543c0c219a400c94500440420245404c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 947038696 1250 947037446 947037473
    0x3050606090903120403050307031103040501020c120405010c0b0c19090f091b0804060f0e0a110901051f120603081c0c0e06070819050a0216180b030a050109 69
    0x1d075400d5440c0e40318190415524416a1040c0b002105003c002c40d000911030801990030110600e4082941c80140180c01001e07803060f00c0807103560707500060700c1400e500244030482d00803c03280c5000d41001c1c176080000c0c10352805110001c0c900100d05000a008200070340076202142e21b801d02032010840c00c5003001d05242a140a20760b0310000360080058a2902401800d1031402c8503801c011181025030070960f45880c001d44100c511a44444401000036250711404082402d8480280031500b1182419411620544480c41c09845040e0041c4510b4442d4020b00c41c0011200c9a6140c1c03219600600f224007180c1c81111000c042d08141000061211081c00380c4001800038042000d4240910509002c982c010445003012031412002d00305a4130740140686202030240380f580b0301e07100110711402c003142d142038940c0c0c2c045100414040500c6030f04018000c000b440304010040340506149084400002540401010903181d502c2814262810b011400502c0e9206001380b003080c4061510f41c1489211 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 947039946 1250 947038696 947038699
    0x10902030f0d09060309060912050306120f0c060a021c0e01080705160204020c010b06040f08010c0c0515071b06060810060311060306060708040f1a271903050606 71
    0x41e100060540c03180410800100d00d0315882d851003d6140800a034083c16088400341c520304c1d517078080c103004626540c1c120091420a03940d03040c0d592603c8020028200c4508401c5149a40308185008500000041c0940303003081c00c455541d241c00d44410105e244c5001c034215511001350126402d2400c035004410103400e15001d0f00c80807000d42c1c076544125034a0292400c2d281c0758100c0c01e40550050308003580100410380742c280001c10000204170100d880703580a94812a0116031050381000511000e116440e2000b20301c1c030340280040c0154881c01c0c0d5a075030f400c2e802071001c0001404120040d0107404204c8508a040b0f0480ca0500000d040c91070046c0414031402807a0300801c110034504c0d400d01d1080b602aa680000c05242c1c5104103410321000340c10003015036800001c02c0110340c3c042045c040141c8010001289112501d9003040c0003910301c40d440e8010744000c048188900e42003a070f50101804641c20141c0700503141c408459001034003c82c030380b61004041503600c0c031021003441004200144038071130 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 947041196 1250 947039946 947039953
    0x30307110f1503090c2d06210603120304150f06090e03070b0a0b0a1a0919063207050705100e040509210a051e0c060f040c050120030c01090203 63
    0x801c81e0910614600741e400c186141900502c6d00d1464003042500c15400c6a006004281003050310302010311004290400510413003020010480d80385030407c440303843d543e0080d0519046050a51f140170f11040094900c038003150300e032a03492881074402ea0101005051041c03041c032400240c2e01c9165101e502604094a40280480000b000a041030050280c428009482411510701c1c014241503040c00e600300071a2240700c10005441c1c50395900c0b4210006c20205018924450b1134208064840004106a04104a8106075404c4540500310b80c03e02c0b4000030103c181d45d951060702c1d08608050643e088281d0000040842401c483e5200c41e80c801d00340829241000603440300712080307507248100d8090000c02114401c45000300d850000c050054840da504000713003880403d281e0b000440ca0300c0c0ca150061040041403c0c03840040410075550082000d02e40305140b4145520380e01e8003003020380192810b12110304583c410380a80800c001032100d54203410b81b51580d08035000a80600340e042c030306034828407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 947042446 1250 947041196 947041213
    0x10e130213022a0303190207060c091d06030304050d050a0515060310020306031c090e0c0d0b040e0c060a0909020403050f0c01210b06090409060501090c0e030307110f150309 76
    0x340d89440b46041e210f00a4000c500f142c0c0c03510b554a1190b181042e148204680034000140003034454040e000511040d9200e0741e854609001c100e9061900d1a820792040880243c144661610080200c60070780c2c00a607020181c4103d541007076032404200d0b602c018150311030249041a489c0d80945060f020321811400c6c0c03510a8010003401c000e9000a940c2c26a0581006002503c505c26041418842c4995401c195149a941d03100600041d4070844451342c09200000d0300710004811840340d410011800c03a42041082024000159900c49d00c600903030080200180e4080a54011a641401811280c2c01035650365282e00d071040e143c1501200c0c207203551281c02c0780503005600035400308254400d00e00c210302d60600403e0a12001e81130200c011904180100241c41c101d403900e014911480703025000100b125494116828201c82102c03900008010005000d442d0030351740071080310b00d12908900750702d5144966500080c4c80e041c0d8010325540c0801c404030010200040400074504c28801103080d5600a03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 947043696 1250 947042446 947042497
    0x612070f091401090e04111315050a0b0702042f070c06030908030408092407021504060903081806040303080108010506151b01090b0112210503010e13021302 69
    0x308101c02d55020410344c02050141400325601c1c0380d070207070041c0e0b20300b1940d40414001c01c0075006090401c801140d1900f001500300108645003000401090350007240c910b20700480382c0040c0c001c5a60003881107841d0b8907408240c41082503100c00101450409500d44540b1004403a0f403648007120441d002e0794096000112180a8450800881d40200705c00d03295079035698542c1c0165011b6884186e021604e0400c000e8600c0d400b041641c90718035451074466036042140100328610038004e034483c845503000c0009110256000c0306850440c1d41c0109540e0701d0b25880c070040a801c040c0591802c0d00040041400010b00d980325207a07504a80d0340f20000c00c80e94842074203202a22000c410040b9025104101d5005081d440018004d06090f00c00c00020704940c0540c3c0e00315400d00c0c217074841030084032000e9003007041c005103042c00c240389080c0304a81842c1d010303100e50180c0f0318001441007a403146004400506405007484841380030f50f5000b0040ca0015020500c0c02000307400c40001e036240b8031050001000c12 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 947044946 1250 947043696 947043719
    0x80105060a030312021e031e040203031606060305030f13060504030c12230c040b0924031507200c0f040203180115050f0306160e0612070f09 62
    0x54440900702200007400e50701d0903225154088203a000c8181d0802801e8551046003030302c140da42140d50034103a540c4c140029040f241d4003c010300000c0380c8082c101404016030b000011100034a08204a031040003849040910052440e94001f8145000000d03400c0d03646c901e8000142140c80c29808840c000b1034803448120348900070741c08028a680230801052041204c61001840024802c400c0624814085607003a050441041031003545640b00d048800c24602e032a00840130201000e807a0f440d511300d85400c0d00c01c3c403080fa51485001908042c40200c1c46514140b00d04625900c6c0c1c90021456420130301d100030241200c9100789a0044d0440b081c810b000500481c80700301030500240b40c01802c404520070800258805010001c08200000c998200c0403001c4c058024075401140e0044540c3e403402c2c040c000001402401540300c1c0d0010402c00041145040c400380141c5014034110181811410200c0c01d140304a160407170207070a40204105d07425034000c1c24928000d102d6a14086001e03a1a8406c2e43c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 947046196 1250 947044946 947044951
    0x15031406160f082802070302010b1f05030a0b0d050307030504080106060f021e0705030d02030c0706030e191a18070e16030203090c090702061e04020105090d1104180309080105 77
    0x5000703001144c512012100881101c1e6003900d101c00114088164240c100d80c042402200943d44910212106141c0007402c1d81081d001c1541001c100300c41224020518800280500c02c5076503204804040fa48403229500c442980c40401c0769038690702410050319507005403085003415070a044012403110b03c81c21001390f4106036500109410a40f10901c64140000190040030314841c8a00001e0242c0d003c00c48c107400ca100f20f4001c1d6940708002c402850803e01701c1e4100f103050604083c21507150900001d2800b60310b004004111883c8101031800051454003541c4014030802d00b4003d00200e50554442d0f003400e580880c0440f514075a4441c001c4110403400c07650084a03210704020000407900a03001158029400005d0310502d5010400241c901001900c80c0d0740140d0040f000c004003a409000080000011560b56001c1890f00d64002001c03840740142840c041d5810649039420400c04000c1080054401002801528016940c126400c69400c070250001851000002500c074010300ca890f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 947047446 1250 947046196 947046227
    0x503150132061b16061b02010c0305030411090f060405090a08180f040609050603061b0a0e010c060501170115140118210309080c0a0501031503140616 66
    0x1080032010700204480354002c418aa410703090f6201c92150100d400340546026801480200e030505810130303a0081402070ba48045000c0840d850500342c3c0940c3e000750810f030000c0d0303142c900240e4a6407240b4119200b00002c0840c160001c160805200d01a024622294402e2100355020402c40d69440e000a41c2c07a418007402034405881000b100028044030307800e00328840ca024050070100d000c44070210b4210350041e407100e014550380f08107006107031400303004054018001100a81c00c1e28442400250f04d13208486000c02840a00c0c1031640481c2d000b0b5a0000c040794114104002c9907960303031a6240c0300420f282d1085195440c0003820010303060342e50003c00a89107100d15442c0d050070904010b480c110030300c0c1c403c60310840c42c0840c001184c0c82e84d051011124a100098944404101c4c603000d030680e01503811425241d00006507150443c0c840030b6801007110402d2802060f40341c040c4050801c56603090f0006451035284407590a099403002501c1c0e40582c03800c100002040b020780c41c048a600c10f8049541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 947048696 1250 947047446 947047529
    0x40902280f080604020306010509060d0203010f12051f0603052a010504030b060d03030209030f0a0b0f0f060427050c0a05090910240e061f05040501051305031501 71
    0x10f9090901d540507580c000c006062240c82d007807203034000443c5904070410900c1c0c1310b500003005000d41e420904a1400519032182d0448a107040c5940e00e58680d01e16000000d062420203845111402c00d42e0001002941c00c0002d946801941c9441c1c2c14051520740b8007906e40201c4108a003645510980807101241e4004010200c1038940f10108420141d0380c08003582099002d2041d4070803a9403d004880c0031144100041c8410382c52451700080d10f4800401e100c01c1802c51030100441801e03540074a031352015003201d00041110040000d000396421007002c4000c1000702135554400c0100018008040310412038190340d4140e90750081003070b01c0e0705c103c517040a0740d004040524451980c1c1e4100004007406510382140807441c0c084603035600540c0740d1000200d4041c007410720842d0b0800c8a00314038100300900c1040c100350b100b07440c00f6040c0c0c802e80c820141008400603419071661955148440a004000c054079013801109028845800342802222500602012041c2d80102c040d440e00c03110f0071011500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 947049946 1250 947048696 947048701
    0x8070905061c0b03011d030310080d090909170a030e0c0a03051515030d030b0103050a050f0c07020a080601080a052802060f0c0607080a14100b030705040902280f08 72
    0x10b0601a2000151043e01503484003240d400d110b003003c07015517040b103015004544910300b102d02c18a410b5600d501404294000a0048565070317401220030058480404007c28503040518202c07101c03906d15071020000704400f045080c80a5895004501124a200c0854070b0420445082089502140c44020010340c0004c80508840f00c0603512251f00610001c0d13682118090800801c0c04c000c8008401c82c0040c0d0baa210581c413030760b0140301e80d5800804031041008149040700c0000d08400000d000b05c0403070b000201c0d0b64000c5582c0e400681c40030307298000039140785582d079006860b40c6032840074045455020f09649607111a8902c1401907006210800e00d9290440ba502400401c1d0311450100340d03600c10410441c107a486040140500820b0280d4600d150707450007151203c115002045800c01380c0d40704d01d0610500000e240c0d80035090f5180003a0080d0f694503800003c0c3c1e034602c115444a5451070002c50b003050440c902000c101030350005040205400340780c800048854110710f841c00f40128900902 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 947051196 1250 947049946 947049997
    0xf06020c061207050d060b070c09090c230307030506060a050d030210180204022a0d0509040b010504051f03060b030f13050705040f091703011a071a04030807090506 72
    0x9409400000701e0030090710341720700040c0c4042501d48541042c0080390002419070100804000782400a08115404210085043d030358400e1864240c89500d02c03140c8580c01e01e054101c612004240704c40d50040881d03440306d95a1030141d40341c0c3f90072601d00d88624800c040005403402d0803041c041e281a41f690260402440211180005003414001d6080703c0c0702400c3e0402c0180c0f203a00c01016820001803848803640680030002d42a070302e80222240113500004041500305402006403000c60004a8012484040b20741c0100c5160007a503000c01e902103241d1400042c0318101c2119002e040d03c4540d170510074203441e00f0361806284030035104010441300480010790b02840c0d0189604406210b2420b4900195440000400303032200c1045110206a440240c0c0003042046c00300107141c1d25104544a04544c5481c000c00304100d4800000750401c40300041410030815000c0042c12942c12003181c01c5440d08280c10020001c3c941221150045590000080b1b00d40c0f41c0b140546801d039001c11904000740d0240c0c2d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 947052446 1250 947051196 947051227
    0xc050f03031903091e051006091b03180206030f01060806060301032a03081b0c0a060c020904052b0e04060f050d11120307020315010b040e06010e1206010f06020c06 72
    0x13000d403600c4114040c030080500c001d81e26940398500840c000c00ca0b183da04d00801d0704035051a030010411a20f050940746803034110910b010681b0010f400d0021b0088485c1c00300742c04a01d0f071058000d501210000c00c200410a4440c0300505aa183d9507031301000c0c0e55028140050b621003800050b1803091180c5641043c0e45a04603101d20711541c40f000b1440803542c0760750300706054206c0305d003004401807040480d8500030001c1140420083c03080760f1075060f45140c504042d100d010101c0c2d004c0d010340e0006c1c001806000040002d0780b80824503102502d1800380482101d07166020b000001d4000808003081c40d980740c034060040c082a100c0c00709016950130710342000c00040c1114020101c5211100508140140d562654903080c41d42c09600035503920030140c03040500b460720b01401400d41c00c80c2c9600501c403032050785c01501e056440205600500f40c89090050b0740e058641003045501000321910401817040100340103040300d20000d40060f40f5130310b032442030742ca82c0d45208000f40c008006200c1289481c03240b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 947053696 1250 947052446 947052461
    0x302030636010c0f0c0b0117030f12060120060c090d020901030503030a1b08310c050a0b0f0313030c08030f07090e2208160c050f03031903 61
    0x10400c0e40850321070701c01000562062001401c40741d643e015a10116600b05003e00b50701c1089150601d12414130b40e80e07030700b8450018041c04040840401004d40060010002c4804c0c0030040100e01e52103106841102d002084216401da0005c0c60701d0092020f4006200200300c0c0c00072101010f41a1990303101c0d00c0003007079089202d021354080800883d04016032240079400d400b9501030000346989190025110b015951140d545e41680200c680383c01041c15402507040350882804105001001891801510182d0003201103400c3c00e00c00780d100602f08090700341c2420440350140c3d040040740b40d41d424000160300410208042e40303201000040c0d250541c09140704c40c0301e40b00e030414010f902055110004103400807110114002280b40a00c045d0980000400004000c410030701b0300c42d45003902e460a00f01080da080c05900302d40c100512010819140c0940f1200d540c604058289080942810350000300c080c840c039405407040300e410400a00b004030842c1c3d801c500402001e0a0703440001421001003105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 947054946 1250 947053696 947053741
    0x6150f0c0b06011e030603050607180e06040920010e0901080a060e030d05090f061312030c020f16061211040506130306090b060315090601090c02210301031a0103020306 74
    0x14040b41440d40041107440c0110a450340e900044c20b142140b4000f2702c3c0000181402040c00000306180044850310500c000030f45180c40341940c125120940403c014108060300101140a020480d14140d041807001452420090780c400621645400074825548028003030030041e50014044900481c1590700004048001c1c10112407411800c04141b00860b80180c070308400d140c2001d00400c3d400c0104105240d0040181110f0b240320498903034945a030072000c0b06200e018152580b0844c04d1480c028800c400d1100d40d4002030300e0f8407501079008070ba5000031a010311804101d1032410a01030020f9172258036401540c07c80803910345410701e800c005d156004850260480b8030915030100003c1d41500444100318404c40c981849424107030201820070000000324030f415941582000000c1400258990441c0c0940400250002030f41200b203041c008034658442405800c02c0c1d2044010429500646c1200d0081c5280400c210382c144000b5095402884041e5044d03121102003025040c0030003017050309041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 947056196 1250 947054946 947054957
    0x10030b060d0f0f0503070312050114300f0f071202010e15040306050105040c0512070f0e03160305070f0308040e100e1501030e0f06040609030516050106150f0c0b0601 73
    0x101c0743c0d03070000d81041c094000c0381c1c1604081406410140c100e14880c0310f1101100091101c0c1d8104200e000e664145070071400c0c400c0d41c4c103050700805441009140000e50700d40755041042c54809c0585595200000c06081e6028416880340d03013910080403074840f0a07076500d924041c1a4035140d4004582101e1405030344c1c0da100103003010081c036425081000b040194407444000c1215850321f0104000c84c1d01640707144051010070050920b5125240700c1c07042d4412501d04240e0701d1a81c940504807072805c881c698060301441156600301221052070b0000c0c04492089040707580d1940c8602900c01103004510006086550500062041640455034a584815090320500d1150350312980c480b0b0100c020348244a41d4030b00342040121950341130060a0381c20510300c1c008c0182440c001d0605d541e41c60020000707004103a0b540004003c0601c9a81110480300c034600e4546207a1031581402c038001c01d83c40c490145225450b80c03900c18160300403031090702c03241c0980d00e515803805456100d4003000c40005280f64108103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 947057446 1250 947056196 947056223
    0xd0e1320031806010603060503010b040b0306040323070303020d0b0a030302060412120c0e10031a040525022401030b04080d1e0b01091d0612100f0507020610030b060d 73
    0x4040183c20300820459074046401d5260406040c00c4440248610b40180d0800040c02081c0c2c40000740150080c0d4140ba14001103080e1035020301d4864241d4400d101144400111401450f5142e005071a99030384000080020001c00700403c246180144002405a000040060302140f020031085030143e80c182000c44600d03042050741e0048841074044200814084e00d000c0106003020140750826025504041141001c0c0b01c6070702427000a4622507620868032140010507200051a40d10320720f03400703030050b14600040380d08040d440c0c80f410001c0c2000c00802e020100440e169551540c0e04803900500c0d682c02540b82d50720361907030381d034084040b41110380d4941c0d1540e8601c1519004a2804a0090b00000394004e50840010911038183c2e222040e00ca4000008034018200c04c40383c03941212048521408504103184441c2c01c25407880c05071824030345800080d5440c0b40994002510494540e400e560041c0d452030088001c41c0150302000d00840c00f11400254141401c419004645000d00127502102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 947058696 1250 947057446 947057491
    0xd02090d0c06110c2808030706050412020312040605070e030d030c090e2403070b030901090c0b130303030b01050c010e030c0610030f0b04030e030d0e132003 69
    0x825048000311801c601540e4200304196000c3c4080080c40f600030060100002c19038001032040500400b224000c440c1308031a84260310200105000030001d40c010340383c41e01241d051100041c18121000d03151901d890f03040613000c900c0401121a11084041c190019482d5521904024080140030782c041c01048100360a503503604202034003e8400b141e902265500d0b1803400102000401c1c7d2216100000180511903640c1c2e00460078110303485600010420321b000030340002d10f486202c0d40510300c5008000240031011106400c18901301b4000c1e00070060b00f580c1c03200c0b069954803900c0b1030044c0d144103804050000a00c2138125511440c0d0500d001406e024481c280a0b08480921811403419880041c0c80d560301d04040c17244960161030f01c01c1041c456855601c801000d0007000070001e0240318000005020140505100c1c40b4221002e012116000488117000c0c0c1075004030584a4481c071080070221020010740d0140740d403841d00b1a00382c2d0410384c46110212889810107030180004000001c202c80d02d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 947059946 1250 947058696 947058709
    0x31603053402040f090201120504031809020d060e07120c030b030312180a02180709170102070b0a0509100b15130e060a030803060d0201090b1809010f0f05060d0209 72
    0x41ca0301d0700480c045110142c810081100c0c098602c19494608180e00140540e80010000000d1040510080307550b0b5907620301192501c0c07081005000c6202da8a80110340c540295002d055085043c01c0c0400110b6150200d10480103001c95104000604c000c82200428045401039914208541004651b200480300001e065800440034074000c0a50f00081040340c480c2c02000100307001440000c1c0600b0746050f00410014605000046000d20410b0085103100b0300c1800f4840007000302c0800d0006841160342d5903401303540904000d40d00f0380500004070b0101d41c0c1a100c0e19000d50345030401844007040c0c135450400640f0460240300d5115414041c0005000018001082400000c42d00703d08000d06004003214601d80c09004140210f45000e03043c000102c1180499030003483c21a604103001645200403a1419055000503000300703408500800703c66010103e0039650902280c02c0000b584c3c0340c0d4200c10403400035114690b81101c6201003044181044c1004110b0f440c0040000f62901d240003010910 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 947061196 1250 947059946 947060017
    0x605061801123207023a0906021005092107020a030f0c090c08041403070501090804080708010b060909060d0605040803040b060105130308160c0806100803160305 71
    0xc5070b4000301c165600fa01003403410841c5410030004540410b04181000030b5032025000c00000c2102003602441100481403c244a903034040c1a404000752802e0f800f00800e02403071449000c0261061841141c04209203025483c454003090009203c01c580c441c0a02c0d00da1210144101071800d01080218056241c10280101450141084d00c5200c8030354a8003c003003030f45552112016920304503010350219130040c110350f0895003094080e0f200c4000c00c03900f0b605520171148018503941ca030280101c01c018190010707000302ca10400940d1000b03955080d00c0742c282c0b2110340d41c01d68006d070304008075552468442100c45d040200a020301d40004800d584800440d00152400c0d00c00ca4008401c1108024545681d5644010280b070715908000150880420820741400018100f42d0040342c0c116240100c0b1413109a11500305040d0022a81e44100c210384a10341600c08940164040304082407014001040ba0300005014045001503070954904448036041840c821030440d840d540e00203d403900c034065505 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 947062446 1250 947061196 947061221
    0x24060f070302150c07022b0f052104031401090f030e030c01110606090604020c010603031d030a170903030d02040617090d0e0f0321040315060506180112 67
    0x340d85100908010f4600024803207407099082c80b000070049002a442e058545142d81503032440748030448054002c5083d0380b00e225040c12828444804000c0c000800720450780240100141c0d038100c80403076035103214151000c60800050703404002c00c00000300c00390313028980030a10000008440740940e80e106560010240260001010030501c44004c0ca0300f4400150713442800d0800c28012010740001c2c940724030000349428407a44014000902d10b843d030b6011601080301c040c0003001003d4403441d000e800c0000700211106406680b14002d51b260500088104207103400149410354203c182c140d9a5041d40714400b4a501800180049180f01e0114000b62019020f1901c2d0528049a42d164000130600000c1c0040302c1da6102c1c50403080c030250010494800c215084e102e100c40c041c03048000c01d280c0500c102c146030801159403c2004c3c101d00c454050b005480c828030f00c00a20180100e12201507070700c0b50140b2907100000304642022640040007154070500181010460341ca07544c1c56180840314041c4802c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 947063696 1250 947062446 947062477
    0x8040f0f030504150201020313020105130e1f1418040f050303010b091c1e0f0b070203190f0e010c020409200a0902072607141c02010903082406 63
    0x148402107030303200800c113001c0070f41c8021170071841c01000001c4804003002002c1d06001c40050004080c900400301c141c050105c4041800d42800c00c038a403054583c0c0f15400030000310100301004035030321456000400305408002c2051290451248001030500c10140003200c00034068910b04000a43c10301c0070314000d09812000544860540d4180310342c1d0701c41d4040c4074000550042031384000403040140200340f24105440c00001240d5494000d9500fa40000d0160001100070100505158000000d1140c10540c0900d21038414200700c1c05c1d41c1041c01d000700200452811546480254440c614035649140001c1021986000584600000054500200817074440320003c941c0141414010b40300244410a002c5140c00390a0303d035a0100001450103100006040441c14006c07200e6000381e80d1135541102411601c11a02000e482d035881c804404120200c1f140079100251600620542402940607101c420142d903401c4402000344c0c230710801c05216030b0300c0c001b520812a154007001d451440e0220215 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 947064946 1250 947063696 947063699
    0x92102150913152c011401051b030a031d030301050f0d0f0f0b06030708060604150e090102071b1503050a0f0c051309111b07180f0b0109050f0108040f0f030504 70
    0x201c104d42c2d8540500e444003490842440712031010500106045494181d14100c05500c0c50700122400c0c0b00f07001c004800480d0391106001401740c044000e0143d45030070b0b241003005443c20b808420325202d44591002050b00148010001414200b885200c1c00c08003c0c201e4204526540d5603c038041c28901e030584a400c68509640f040000800e610798024104030300512180b89024101961207200610450060f5210451604190700c3c52102001900b500c601d40c9546140c0034031054001d4000300e00039211030382c1c10002182c2c562140304030b00040c0c47d46525280b015a040c07210a4003d000c000d411042490347e5205000c202e40345510681010320059903515941e000d644a0b401c490100320b130040c400c481e141512410582c3d0440084420980c0980d5940c0c2604a42000e4242866080c1d40b25503488010304d40b180c103d11000703a01400c5140b03058201000f15540e01c038011a0204006e00447d0780110640e21018015802103070342b158041c0c450307100281c5030001540c4103001c000c0c9d074802c200d0205402040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 947066196 1250 947064946 947064959
    0x2151c050c1b03090d032a140d0318080310030c0803040603050603010509060118020f040f06030f0e0d14040801060603020c070602280302150709210215091315 70
    0xb0241d15020061005504080300240015041520130300014240000c2004008801e058540c1590070001d14000c200041449400c0c00da0505400c0c94203102140266900b030b00c0541c0c007a105554003d00080d4000b10400c07056a601c51066002030002e04003004000e80c004001200c0718001006010840091511249010740c00740a484010703011a200380d04010801c05035207800680c69044500c0c1064205111114111400c000d2050052850113030100040204150b03c11041000480d070b120782d4100072288a9400c84002c4406140d010007203500140c1340009405d129070001440d041414038414600342d9910180e60031035801c2c3d4003501c0403e40215207950081824841a40200203500142c0120f10720301720304290b0306450030204000911801107078014113108204410f01d85a2566000c986da051010b00602080035900c91342000c085041a5100c0c0b0447c501900075405e030b8050f0420808014440749100e9542000031031a8101d03d22401c54100c081041c004d00d0007120401d06503082060601c00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 947067446 1250 947066196 947066227
    0x7021f06260a06050403050f12160816050a0e120a031803080f0706020c0d02070510031517030c03040f08060c070206181c06050a050f0402151c050c 65
    0x201600781c074072868005a4456202091410103194440400503080d5540c1c641940c0c213020f2440400c00c2084046112400325090103911800b91581440d510401002e1820481e000f21040315203082407200e184a0f62400d0740900054141e142450504070f2200780c240011950440101181c42c4460740000d400c0400e044e009501894003200717403140c0404060540c2c650603103502c180342080100c0000040d00500f40724640d410749684500081c292800c400351203030000d5a07111940542e81c412002583e90140d0302d40a0b11401c00c080721711142c0f41c1c0b0070900e0190240170369000b11024580301e0101300488542181d00303000820181c582266203008683c1043c0b01c80d0b14101c4000c2c2000c801c090b007081082c3c0580c1d92141540c00342805c60740a05804000c030004604100821101e59000e5400000103104021650b04810f00c10845000308104942c0c1d000c81c1e2912110098030080d401c0000c031345c20010f48411a0004000c40e1106441085456031402212822600201c2d6120a00301009c00d030f20340b0310b10100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 947068696 1250 947067446 947067479
    0x1020703090f060c0f030806040207020a08030c120918040c03050708100b011b2003011d1b0d02010c2406090506010f081501121802181e07021f06 64
    0x30700c0c0c403695404545e40c50400c9149020400f500344041c0d540000c44680c0c83e50126110f6550160588200b19078900040350782e40c100541d00021401380e007513141d004541d010280d0b001c054005001500150785071760b04040284d8054015100000d8414022001c1001044818014481c11006050b8422150356200881d80c80c54422410001032052500d07050009501c59680b01d900002c400c18030364105a070b2271003103030080d0912076019400c1c40c03081d940f94014003205403145112441a40da05805c00c00001e14500100880b1542c049945a82c280141d407144243c8061580b02d4420388191100701c0494501020000581c0902c0d01d0f00c9400612804105014858204a0a0802c551041c8562030042c16800d8008d04202c0700f200c04240b00720b206c0e03219240c21300285000a00412041d204650355406114031900e041c0d0090f2242020307040c1980460606034401d9086145504034205c0c01401c801594501400303240031885060000c0826204041c1c48510180d1010b00002d030352489e00001000308040f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 947069946 1250 947068696 947068709
    0x30f0e0d170f1611070f140a0b0d0504021314010512010216110406050604030f0204050f0910020a091701050a0b0f031236150f070b150301020703090f 66
    0x448240891080b1000c1810381245500d002410380049030403080384c200e83d07000c00302d40c05480b403008005420840b004a61007680c180355110206c24600d4400d00a05040900c110030116400300320005540000e6840315030414402000142d402c241e1241c003500782c0d00068603400400d4034400040000d880c00c8141070105106440003503041040c560360000e510840d83c0c201501007000501107921650f00c651021010317100060540d5280d9883c2d042c0450000014041280502d20381804945130300000c056491094181c80001c0242a02200380e50010350020104042404107528001ca6075650740d42e901c0c0710943e280000000c09107007202010b8251101204d885004981d138200c0003510b0348011800703002d019007a1544a0350b5901c010700003500d210340c1e09401075250150410014400d69020202c0c014200c00b10b92003506019480d40c1584d49118000b4220780c810410002040044c4442180c90380c0b0404101c1d40851007482da60200b400d80e880884124006502840c081c01900070307458011014050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 947071196 1250 947069946 947069987
    0x1171b280e0f09060111030d0f051006090e01030f230102190305060a062703050f0609010204060503040b071e111c050319060306020f040306230c0a030f0e0d 69
    0x1640800f00d182c0c4100640164108081040c2c600308285042080300c08520030400100042e8168a013424001d00c0182d502004507084401e0000b00c02c0d01c1401103c2c10345400c01e0b030110241e4a035030388006042c1c04840040f1403480c40992000d8202010840e8800900d240d64000360b40c1e40c840320f1030b1405402c1007011500901d46868140052501d5001661045c0d8580e802d06001a088001c06141103410302c52b200602d030717200180040304100011400051580421045503826150b6225044c242e000b80c0c0071758000140103000041c003240640c00d540360064490706096010b8080307007046207000500045403001041c0940240100780c90f0400c482c0503c08800c0801800384403000344010a00d00c4064000e5150510000b444045010940e10800003103600c1340c002c65484249281c007044c560017610040d14240e103040d09581002c6240088190450b03507034028140e40d903491401c0200d00d504580600f4040690341d1804020038455481030f2082021240c000707001006080000900200161078040b85d05c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 947072446 1250 947071196 947071219
    0x50c030111030601200d0c0203150115090608011202042301060e03070f0518040203120d090c081b09070203090a03050a06180b060d0f1211070501171b280e 68
    0x1000700e006906c8145a160005004c00702d400000d1030856007140980924214070000102000c01d20460240c0000588801c14647ea585100740d402c02824450044038400705110b4800600d015400380c43d5407008001c90b202503040031a0f9000c04c08400360407150105d0f044500800c542d00d400c10030b510061000844a50314181000007146120b0000000f9507818854440842c045540620680f044c0e00e040030035450b03c81107502c0303035280600b00c0c003802503841603086d4078003080400d030224404014860415800850354042000d02c00e41d0280282001d04501080c0b080043d1035403107000082c01140141c2c0181200b1f10541400c008580303001641c400c0c1c0c0b0b02c2e0f118100000030381415415520040880b03641d42c8003547ca0614088401c120040100012642c8143c05d40103904521050725042c2034004840d0030075206c0340191000c0211381c1c2c00310249103a100000f003a075a14030042090004400b0542400c000c9010b220058020703a441e10201642c40c41d00390020441e60081c0d410501003c2101c080c1101c0b07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 947073696 1250 947072446 947072507
    0x106030f09021e0a0305030c0c041a0319050f03042402060720030f030403031406091902181c060f02030c0301030f0f05030315011419050304050c030111030601 70
    0x3c14800e4640160080700c044031a0b582c0100142c011500501640d40c1c0c1c08600040356140c009034201e041c8107624200050b50389a003d201c1d040280e040103401000510707c6540e0001560001d400102c850f4420b0000e0b040e0502420b00140005020480e8201000c1d00b01c000d47c0c0b1402040c2c2e0140c2c4046601000411407466807003000b044c3e0700d50980484100f50720300351004030308611400c0749450740b40000000b40000c140c0d050b88103d440842214020056403140030401118801c1039a0200c40680256882495414198002c0c04103000351079a13403c070042c800c0d01195000c2d0351041510460034030540f03540d0600c18540186696074038a2001140385240034080d982031800107000203017000f2500601030040040107401a415640c00204036622894141c03009815148d035048810b0002c0d61290a2602042d400b509440d65410358a0710750882006696003103944d50001042511180700d400110510368800f0b101d400c0070340b0800d0840c0c95880c42c2641c00034190070388010111440300e407408914a40c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 947074946 1250 947073696 947073709
    0x30403300f030207120c02090601020a020102030a0f03140702070e1003080a0302070602070606080105010f060224040c0306050405031306020d0207090f0603020301050901020307020d0f020c09040f0b0f0106030f0902 94
    0x46400d00d0501c4803901c4032000d400c070000c0c0940000184089905008420280d4004002955251080b0b9a081e90b03030381c07040012030b160641c001c4005c0c056881400951229805a9003015809005140c00514101c01040c24540030400744d07614400b40c0c01031402488400c00b0402c03a65032282244080d0b40c00c551079a40c0c2c0c28101d1080782006c20401d039002c40e40008125141d0102c0d0421034120f4028000c0c29240c0300c0c0e15008110070300c11600c401120302d100080480c000b1a10034481c645400000c400000404801f0590b140001d00458205003100b00210004103d4420180198003c200550b15203001520040e020313011a0000015503024510f1008401d41c002400401d4441241c004a6030741810310035040900b210340c20096040d402d01d020071222040540c041c42c810020359003103c0250007001001d540360f02e241d20303a0320016004a620741c00a07080c203c45058002d48a400c01800400c0291108458010261040c4031140042401040616407501030502d0840342e4810400c01c000055000440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 947076196 1250 947074946 947075033
    0x30204020307050d0c09050306090109170304051203100503010b01051603030b0102010f09060203150a120b04111c1103030f04061803060501080d080a0501030b0408030621030403 78
    0x20940d00003000440e0288a00180c442c107400488003486060510038001d0059100c40c001c0da03000b03214010000d85c203108140543c00c85203030003611800c0e600c0e00c1d00c1001c00b0140c1c0003c006036030910592650b0034207c80130200441c80341d41c1e034918003000c883c2054105429505256203460400c00c0c240507040c1001d4080105d040c001c1c0d8142400200c000074000103034090008110850813681c60482c0460502c64590001c6104283d00b10721106946215010001d003080d080c05902661040d42c080e0100048401c0582d94100d8000d00405a4a80407100040e40b10400000b0354015883c0a05101040040c204210308180764100c0c05036040007000e4525048900440c4202020022000920010106003c1c981c00141d42c024038284620742e1540d0030240d940904a0f14a00062034103400038134512180c0c4201c9059030360007124900d00c2e4959486100c00c80d0009001c0135888140300350418411500d1510b807405e600d44040155031503d08d50f00700448440d840c42315004464401542c826003007070200d80c8120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 947077446 1250 947076196 947076199
    0x506090906010f020a08040605040602070e010308190905040f02071e030806240a02010e0f24061f0e030127020d05120d29030d110c13330302 62
    0x3c000f05268000c80c6010500000900400c00010707000c07404561003c01042502c1d0543c080f6101a40e80340300160540c042480040c100000a01c00040312540c1100e05005074003040c030300035403082c1d00c03030780040c0c11650aa5100c40e100d9900192040c2080903510416030101410308041502035110b441c00341101070010440b07440703401c0c0c800d0402d001c0c581540d148020340a0354920161224090310000c0e0003403600010207040d5210f81c83d0381030f80110b0001113410707021004070340e0400100482901528048005084194000c100340f41e403401101c0311005140000c3c00303640d00c440020700100c0c189421a0403800c440300c0e03500c13040b1031500c17800d00c01400407118007035060300c5441c03000030b140c00d01c141000d00703401550001c42000582c4941180e01c0e03402c4405081240014518000d01c040c074036618503042001a44c0c1c240d0445c0400d91580341c09144072180d0b142e550801c0d11000d688900009811101c402c2c1c003200381c0342d56007201802c0301015408203080d5140450071011844e400c28813a0080e03000e5448020f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 947078696 1250 947077446 947077457
    0x90210030504150e0703080304060c030518032529070e03120702031216170c1f0f0903051e0307020a1514010303080906071b0204020f0f070318050609090601 69
    0x130030301003104200c50b400454000c1c0181c3d40f682003a1620340040d00d0488000d00009043c403021481d2501b49a442603c076490b00d070015441c0402d51400c03a00e1045840968244140b0f0800d8000007080b0f142c4c031100d200c1d403145041c0d04a10400c501c00344003503000c050b008100b0400d19051520082d2400182429914990a005502d40080344002071500801002e141d01d0018040391100312400d0b92940300c00c48038070070510040802c0005c0e07003540c0700d0b000c0d80c0d040f00c2c101c2d071149183d8580070700ea4440e81d000303804c640f040200c0c0c0c0e42901d20242098482d01d0004074001903000400701542c0b000c40c84890360981820803010b14505002c1e40003503032108503000c00762000200240c0005041c40c140d03c200c800e2030103801070886640c1c1d2420040c1165408480156403401444006600c0c45c0c8101618503218003550800d0710341d2010713070f000c1c40000d400400501c88400010808041c101210802400788944280e54640380415a0300b4020001c8d07940d6804940108014000c0101503511700040581c000b00a01c0c0c42c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 947079946 1250 947078696 947078711
    0x100b0d11090a03150b03010203060109050409142d030406020d050f19050408010b030604020a0b0a050708030a0e0715050702010c1b0b090f030a0803040206070516060309021003050415 80
    0xc040184250007105a01200401d030010130000c00c0f10070070a289042250130455291100d040c5800c2c1d01c001c40e06540091105901402285810f60103450340da40500d550402903519145054900414415017031044c40d280c03c95051070440d80015407441e40c010802850070189040c41c003959030580c400025003842804100038115058080c107a4000840d48d0381812400c0580780400741c410703030003402042039039400d00610720300d01c0c10002200303030141d0f0780a800904280d140149420991301312404800401504001c150042950b85000c2e50040300c45d901e002821442641c0003034917001c0c0c1a48000c00080b103455500706915042010f079226a0340a0900541414441c070304100141c05900d054010b10a03000c20200300001e902e0081c09a03901c081d5a8800d015590404166480080b608010031100c070810024006090070005004000c4c82102198149901c1c4041c4114407007054004e07600196940b111384040d0b140440041c04201c035a82020070490070709441c0c40e100e0040f61041403000c0c0b034a540f070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 947081196 1250 947079946 947079971
    0xa0c14060c19060b0405150103110d02281e0503060409060203040f02090903070c120c1703030907171011091003090b010504231510030c08100b0d 64
    0x2241e40010009060b03030241884420002000740342d024043e62490301d0083c1500040c20540301d654001c0d01c181042c4c000300003000c0c0045001d4a15595424031013032091040304010311441c0040c0004105600c0103032201045841d4001c410030000400e2401c00200d0f96600002c0140c04040107024041442d00943d2503403004007040103800d00c000000d008510000803c414803143c0c0c10a0100548219284460768171241510341d500d0040f5000940a80800501003119071440743c0f0500302e0521a001034071949a4480070440c0350031520515070f030700760000000c205002806000400145c03c0340e02c01683d15842103089140c1c2d41d00e804001028041d070340c3c10510000d29048003035070901c0c0c3d0300074400b0b800d2014031200280a003818003070403a03039103906100100745c5241c18003408200102203c0140160424240032035400c030b50291800d2404291450740c01341d01d4840c0c8010162100f084d890120308131460031401450407500402d808402c6925403801d0140c8010f110071652103500c030340004a14843d5984 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 947082446 1250 947081196 947081209
    0x40b070903140318030d020706260c07060e01020a08010b0307121508070e0403050702010c08070501110c0c0a14130605032e022a15180d020a0c14 64
    0x3000608a40e154040032180c04000200400d203003005142e000322502c20610901d546d5450310401c4a001d6003080800307006140c420488900c4948a02c06c1000c1d4494031b1444840c030300d10054504416000002802038140007041c0140c05050105000031490650280d2009090710300600401060030300002c045051140328801000094a1300034040207032074000001c96040c1001341c89040c40070300804100089028a90311401c0c4119050b07141c003071401c1880c1e4011140344c0045c1404480c603002c103000601c0420700910030700c4007940c4991a0241c0e902c400300320305881c20347c60051701c0f0311a0080030001e02c8031204035040c030072101500390313103040c9000060900200581442e8000c0794151080c50140e403100c4c40c1005040314074895491803a104100b400300e15900340c3c812482d022200100408400e0b00a842e00942150000a03680c1550381c02c181c0307540b40c94151981511400070101c8580c2d000281e4200601902075051118001020529015501da8450f00782520401500365000501d15145442e8036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 947083696 1250 947082446 947082449
    0x340347040b18010516230a0309050313030c0e090a0f080901110616030e07210606090f0b0906030f06040807170703111005010b180a0909050604110d0b040b0709 70
    0x4600a012500d010548842005000740e1448001102d5504040c90098110105a090105800841c7c5011a0700500764050002e40c50101c1d40781c4410000011280c1d0380300389a0000c1c5119030b103404101490700344078010f8603101030040c691b20b070046842440011508240d4260195204034200c1d01c80400d00016206414032011103081d5028110030803400010309030447d40c003002903072410800303216900d0801d030f07542c0b480f03008168510742040c1001c25110603070382800345c803d8400c41d000306803142c460042c01d041e82e0030324240ba0441c0e07813200040450f41c80c0c00d481c13040e4080c1080d001400480b214000499641c030025002907d10038002034074406100d41d9030b600d0707021620329000e0342d070380c40c03000f0720780103200c000c19850405030382c011040b11b2a04500a8000c29040f10801c81e1048e003005502c0a19243d60010300b440b140e40142d000800141c81000e03402041ca80c14040c0026001625003810300024140545129030701c503800d50141680020381d2050101d070442d030880b11421180d5101d481c140c4142a03107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 947084946 1250 947083696 947083741
    0xa120b03060403120b062b020a1b0204110d0f0c0509060405040207050115031b06020c13050a1508030a090f030803180312160f02340347040b 62
    0x8002040c00740c80044034241c1d00303c40180d228214547c000b902d0403400b03494001d000081d114010040301624603030308070f070b0b89074001040043c1c11440107201d2061075000380c0b4800d07c3d45407602c40d40780039800544900f616014140c2482490440c44d00300194145c800d0340148c0e4411980440c0c0c4a003401030075804025001d040e50700c00e200894507810260088034600c8801072034181040d401040462000c01c10b020440806010004c0c02c0003600100400b510008044107201943c402c0e0301003266a0940c0304c10010304c116070207503686018181c0000d00703002c1180c007c441e010710050350400000d8100412130b50300504152170142c9851400707440b40d05610a9004d070f1992480801d09200c0031103160b5400e0401e900c0300d0b403144405450a4102640c594000d0711005004062078030b02000390040b8440b1031003010700a9600c2d1780f8240c0d243c4d6140140c2d4281c8144c4058101c104006804600c0c003060500046c9650721001c828148042c01c114003035084008200400328040680070480c0c502d0805400001401d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 947086196 1250 947084946 947084959
    0x5041505100c0c170a140c0d03050a02010c03020909150307091401050a05030c09042d050114070c0f17160605060306011e0e07050403050709020a120b03060403120b 72
    0x301d58001004a8000103040c0c80b044519440050994600ca43d000340c1c4000b500058a221151038652000e424005d40c03481d04640071340e5005400c2c0b0360359540000e0b109403103034a5294a801183c2d60081c04c585401583c2814944104609806640c410b8010340c0d004001c80c02640790110400082801c0034903a40c0300040d041d00740307a480e22182c15454003180c1610410f48030403c00c141c1d00e9040555440c3c0c64002e1580190000b8080f030040b0b003103481040c42c070704905200d040245045012906210031505010344003a55540c950b00000c114004646810440031f00c0c01510b40c80c0e840e2030341d02e0074580c101030003405aa904142914a0385402d0300703807541d05039080784149040740c40381024009850101c0e04684603001d00400891405c0c1840ac0c3c41c5070601440240b464045c1c1014994000e20030090b0180b81030010a210010002d002001450090304213100d0160712013184400152070800c0301d26400c0e0926003003c650401603140020313402e07406900341c07401410480110f80f1450060401c400d489401c503d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 947087446 1250 947086196 947086219
    0x50307030b091c030605180c070f0c151d0405070f0305150907020f011b050702060d0209060310090515100f09090f0603051e06010302090714070b07110a0c05041505 72
    0x60b055402282112010303980456440020044174950400032030320101440d00c103114001c04229502840788516205400c0400c41f5601d0b03c0700e1040e05940100c5001c0021041064238201c1040082c413000c0054dc2070f40c00384483d0428600c040c200c24203072100d070030805aa400010302c40c107080d40c00301d030001e51016010506604040e00025159040302d402c0c980d4541c04c04030082e655014401d90542000e410365102410a44103a00b04020f030744c402c10071805429002d0000640702d5413a01c0046004408401411035618a00781004040d2000100b0a40101d200002a200c00b52114100810702c1c0c0140d06d000541210600c2c010b030f50320351154020140b0107141074039080400003150301090030f0305c0c040e0040f10089600c410342407807a40300d2078103000b00f25000703040104014200392000581001e150308089010445141101c649038100303980907280c4d100d641040c40656900040758158a01210018040e080b00c6600c07049100451881020702540d80c07682c810040c100000000ea001d4000105005080c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 947088696 1250 947087446 947087503
    0x911010c0f060c08070f0e0604150e03010f021c140c0d0e10050a060911090111100e030702010e040216022701090606030b030f06040f0201050c06101806050307030b09 73
    0x4002220960046407028480d44846c50181403003c1e940140202403501c6c080c140b608040a02d40c0c40c02860007402005080c4209a940a01032845034044460005803660034001c1094510302d0211141c0c810f4502d040c5a1a50720a110003605a0017914070320025500c5c1010440e1500030505d0018442c49802881e08e0001d0841c2c203074200500030240e8200900505440300301e40340c100c4051b0008190020801c000220302383d401007410100409000081c3c03a00c0007403001060f01541c4100c04101c14070740002030700c0c1d0110b60f000380144a00c100c0a94045003008009603012902d00203125000c1c0c49511b00c0034054003030040ca01c280003064000340001d80c2e000d503541c4a00c0c80281c0500c1c0142d40c0800d0801041d0000c50400041201105a081004090756219500c1e07110090315181d01c181c0c1045070411000c1402041086014000c1490700c0101310b40f1843e04481c0c05034000d80c000e60202d0b06c3d00b49002040180d81c00030f44441940e80003440d0204a4032856816460420441c404d419071074034007078003400394 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 947089946 1250 947088696 947088707
    0x4030309020406090b010c0b220c030213020f07020f03030408010c03060e2d0c0d090b0a060b0903031e12070903030e150d09020f03010e0304180911010c0f060c 70
    0x40d074825a400d01c4007039203c800c070500740d500c2e01c41e59900140d4420080c04c04100c04814268100b4001241c100300c0d20400301a0781c640c0900f5400a0704c1c0501c511000b00110300303214400880480d6070190840c10801041080c00c054456428060b100c0d41c980c88880302d0310350303051040b54002d00640c3d0080003050310140010700607010a20400b000c0406500010f04110880700076200340c5c800d102c5035540107a0116007100900e0a02600441442c00188100311440f0f11610800d04254002c04007042ea52500f0b184100544209400c80301300a901409090b110342c500000b030301ca24110350810007010000d001d4a0940030b002c0c403881c00b000c41c080301042c4403815070002c80b0039050364082e50700d0310500409c101c240030315610a0001d82016580800542e0803192050340304c4000f0720307c001c000000c5c01090b00c0000b802e48020010380c50303072030b000004c0c00c014003e50040c0154218819000c2070000d0100b43e1900303540341c0004049039041c041d200c0c11500c100060303c00164821544200200200c0c3d40c02c4a00400c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 947091196 1250 947089946 947089961
    0x8190c1812060605040b0603071b150614120309010c06291809030a1b141f0e0a1115031312080402030a080906040b03090303100b12060423040303 64
    0x80403441c043c07003c1154141400750304951800503101901e50b4841071422a00d5450210241303001a81003078980000030004084a90782402002020038407030f0404103240000d00140c464184104101c1c00d605844001c04001d84040e22001d082107150603116003030000180c03410480b80c1005015212190a6046003940e01c0c00076024191462040302044600c904007000c015038900314103900501c8030850452180103100d10f034001088121000703065990b076042000030b80340445940c135080120f411008507084040300c40c2110038424180100707410240320715220ec501c0c100c06400c003148084400e03119110001e4940f6112070f0140c50990f03c1ca0089038171a00030400c800f080361130034051100c000300648100100313801b558004020f449491840d6484420f1984a0b1401941145082c00300007030351100031014622616280029581d00d10b0030340c07066900c144442d044048030407000d0140084003000020000c1d800501540e0001f03014100302c2000c24090300c3c03502c800825807034a000300020554190003954 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 947092446 1250 947091196 947091203
    0x9030408030c0102072603010b0a1e020d230f0c160b12130203060f2221020706080112110d080904051b09090a0e12041508190c1812 58
    0x12080106c2c00b07a049402007003c0c6500258520600c010320a0000f4003000704805280d40c1010300d2401c0321a20400d1340c0752801080200540c12490f00c805090340c004c4406402223444c0350b01d141c510b2032004034100560180b580783c0a0f0005001c40c05042e1017404020b62501d040c0b0b41200e12510941d560340c2c1e10001e0780f00c144d000c070800740700d200460740220500c00a10710440e401005085559145071300704494180007024189071006007030041e04003003060024840e515000d295601001c41c184168145a400440d07154011907020320710400c0815840081141910032241e1200020341d11070515040c00821242e22550124000728030701c0030400c50400800100f4000d40341840550f8640340e00d60000c40038400c0c01d0b81d4455003000f80c89200d01c0e01c0310742943d20040401d00000c40401142c0f82d2480d01c04405100035003003a001a040c4902c1401e021400f80c411110325002c1c2481c81c00003d108070451a0008010034152102090912035005010038140910642035070302c85560f5900441c1601c0d500307410150f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 947093696 1250 947092446 947092463
    0xc0f0e04030e06090a0e040215131706060d0201080c0d0c0e0f0a0b0d1d0105090c03100e0a1401200d0c0311040501141605060f092409030408030c010207 67
    0x110b819003019401c1c0c4060b041e0003081c1000c1e0514155940c1d41e04030008004a0b8013080c043d076440340c5000c5410140c5040c115500d200551141045004002100340440920007039020b00f042080c0750381c0321b0103c0c6006641c20b1801c5c2240b5110200c24501c41c0c09440c2542d25100d00307141140034010361081440060345e0f012540c0c2400320100400f48200044075001d54138484204104207804102c0f190401426031140555044501e8110b500305401c42d075042e2001245034100032954482494200a1041c540c00380e01010086021031410a546d0f039506000300400043c0701568010398001c082d0310040044561140c6810080d8004400e02907076403040e08840101032070000c260480728443c0c070807883c003503e420360010300d00750a020041d50000c00b0070349420071029041000c10000c030880a50306009074403d1004101c1810280e0001c9a40080105100c0882e805008200785100030121540303800c0e4000072001081d900d54103040e5003035218a40000e58540b00006071841c4100c0705600820b503a60154854 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 947094946 1250 947093696 947093717
    0x703080606131403070306021b160807050112020918090f01090809060705120a09090501170a0f02121605040e01020a020307080d061a0c060105060301150305040c0f0e0403 75
    0x104542402504988401c1e00c94040c024000190f4480148103161002011120b49550303903581c040a0749d104041c190300c2e40c6a944800c0060440400044070b4008011aa0724600f50500303503a1130ba5440103224003030400440e240048848036107035044803054000940408114030000724039940141c0f065860006a12440f0200c600e484810700c2400429540100d18528100119040103451741224000356440c0c0114a10b4070100a4100c00034002d44001d81c5448158603e4240841c04459059002680f51869a480d0082054000c104c0295040d13005240443d958028000302d03d02503100351101c000361180040c1c2d600c4850031040f049003240d101320340074040090006c01d054280d020700107603180903910611220b40000c559501404140a4503840090f8031a41c81402c0380c4400d040070090f69404000007200c011071041031001c6400744c44280c0b8580d2540d4544850003840710703a600c120004040d601c40118041010041400c0001c2049450301001283c80d99180d40e10013206580c22408075901c0e400d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 947096196 1250 947094946 947094949
    0x330c03040c0e070c032d1d011707200105100e09010b010206040b09100f1e063f110319170a02030909070e04060501030501051509210307030806 63
    0x40300d481001075a8030885002d4117136030306036090a04d02c03904002843c1c0d0500041d48800741d40c00224404c005541c0d5040001c1c0100c201d840d0a494001042030400203d0031080448a01401c910340e0080c0640c038013144520404a50002200034038103030004c1d254208800e02480c0c01c5100a002d00762800e00104101c5920b0f0407440318200c030b031040d502d607026030451320000d40850a0500784a901200302c40607641000d191441030002c465038511951a0f031583d50121a0301e080c44840310402030510660208107150a01040016041031444600c1c00710140c203202c450258440300c92030504030050041d10030512414606501340704500c80e10705009124020240388618802083e80316810303004111680340b00c09107001041c0c00d40c4031070400000d620040000000c0340d115140c0c1d00d4803d0f070240da81d8158591034001040140c507a554003440c10542090010f001552758080042940b4a0600c980c99441501c0000b041c1002d02c581d070b0031400303c41d00e00e038a580e21020110041489600c00d55690803d80d50380030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 947097446 1250 947096196 947096219
    0xb0a180303110d0804050712030203220e0f100e130609080901110303040b011e05031902040606230a09030b04030504030506250305100f0b04030501060603060305330c03040c 76
    0x11401b03005907000309410030a000480040c8c6d640d82d40207206480c03429020003100a18070140340e0b00f690007202d103000c04100c04541c0b4061240c010035544855605801d2070f4540151541c8903014815854500300e0110709680c0414007087c58070390303200303500b031007000c0003400c5c02c0e4243d41015070782501180101000c6500c40b01e022088a200d184d110542d80300a034204402d107404840040c0380030780c200740c0c0724001191944d42000101034031514103038000d0b0031020f20b2040c03005480c0f056001c1814006102840904481c00f00300d47e10322201e101401c551503601c04502241d010400d0351000d407148114070b00b44014580d0140040c000d82c2d014078221481c982380d0f401c3c039560940340001c0b485c05507080e48103ca00300780d00c41c1e004039400c4007030000321024294446941c040c09400c543e00c60a00c000e0001010000c0003003c1c00b400300285002e040c1013003920714603247d803900e402030400c008132400040d114600c0d809245900310b4030b07141c248020031a954588901d8052140d030040d5010b462481560000141211991 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 947098696 1250 947097446 947097451
    0x80a18080f060f0a110d05100f09050a0b010e0a03020d0f080301060c0302010c0804200d0210050703030b0a080a080307170408070b0f06060f0a021504030f110a08040b0a180303110d08 80
    0x21786407400b00f01d1200030000b403102911560428600a00c0011611410103140c0b002d00040100001c460a1510a51040b901807089444c14009142e240c0c0400e07948482d1680c00300c0303406036071110031000032740b602c030254400322840145001c50100000c205150310134003d00c19603100f50002c01c1402100b0f5416515105c0071234005048006450030b40501164024804070001000703800e60f500107049a0020f550903014420304800541c002c22203005042d418021050101d00545626070402d0400108071b0f01c46802980140c0707601d00020206030002e100d2413894515808c03c541c0c800c00c60a142c0303002c00040d84070203025030780d480130000070032000703007005510501420006102d00e1600c48604031000c00c03030700400c03040c9042d406502c5040d03601d10030745c071800c5110340e201c0e645030030003901201009005842800b958940c03d40c00750711050005105002107905690400d046940c660042120803200c981640400c100018441c1c0000010141c02c0011007459a4181060760010900300a0444050340304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 947099946 1250 947098696 947098721
    0x40f05160f031a04110d05010b090f18040308061f050405100e0330181017070c0609121d040e0c150f0f090102011404080a18080f060f0a 60
    0x440000600e01d0a98013080441781d1441d04030b81464949401101200c4d400d90000382801000510007500c4d1408104461400b1021100c80200703548880404c6283c200c000c200400b40003894022825507038510035031851540402e1400d1803101000d4200a02c190030070b1149038002c9411391000c80c01c26000d10500d201001c0c02400400001c505051981c00c01c10a290032100c0c154440c0804100ca035200b10028801c1c0c860802c05030100700404003c0c866112500c00c0501d007007201c0f8002c48003901c910300c4030b480d0f009051031500c0000c401240c1018001000e00c501c0c020141d20007040641c8041e6048085400400304a154842e00c41c42054140815160124421921034101c07060039141e5181c0141c03c50342d0300883c0720400d41001d060350300f480a6a408015200500400421164031a41e424096401c110003140f216400b2410a035030740c18081e004000c000402c0c0101d86005140d410444a01400201281c03c11200313410344865a00b1b44641c001d0780c5400017640c0c110300281c0145020700074201c1381c0c2e04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 947101196 1250 947099946 947099981
    0x15180605271512101a03010204030201300207120e120d032301120501050a11030406050601120f090b090304030305031b09030d0e01020c090114040b040f05160f03 71
    0x48400b40809110a03039040c103903002688120311a40d2030020050100e059009030b10008104040c412013075a040d20016500303100e68010441480146da0204900e030814005140a90841d0015006c020401051a420b1000b9620204201c1d09004100c0089800e0705155151905040010400d02c00308e590800040c0d9038a03400700182c0e400c81c911a07485038007480500c03400219004590030410390071080a9105180c1b000441d8407080c2800000e2240310b0708114140010003284103080806581c0313001c0100043c240d41e5a88000810507400b034481304030002014481000380c110b803151740070001d02c449030b0241c40d01c0a00c0d10001e02100d81c00030460301580e8068903081e08650f103c10031014140800300700b9202600c000d200210f80c9441c00c0110380c4400e281a10b5414600743c03000002460440270201c0030348204074000c01000a51888207207854050340079074000c10b640b08c2c0100418058140c0114100180b4030b0b180412101c1048440c04081e411040e55a0110200740702030201e0580e583c00030403003030726032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 947102446 1250 947101196 947101201
    0x1d030309060c0106030203060103050a0c1512020c030706060b03160905030a060902030a08030a0606031b090504230c032a030609060f040207060e0d09060804061518060527 75
    0x180c0070010304541280440045240c3c0d4a940c0401d041440030b0388200d45551150702228100074664481c007020300003440c8110348100f40503c000b450801035840304001d460380040d5000c0c15204c01e00403111029005482401620741c0c070000110160b1080f00c90540c0341c1c5e038800c52a05498458400b060489000800520841d082611200010000b040d0200d9261090805910000d5442c00156104c0d041034200080c00358079201014040e11039146100c48a101c40c02841081070b074220304090140e46003910001003059690070242e030390740301039215019030038500c4040009202c1341c2c8004601c80c20300d03552226884800b04003c8107030400c1d0030004043c600014030010788503040034003000e907019100900c03238110312090ba000b040499001c66401d40c0c0658544411508506040260100240706031400d4940306150240c001c20050003e4402812180c40c0c10741c2400802103405240060300d003c510200c2c44070708c1e01c0500d00040c9114840c0c0d6006908000111160b2403c21a8100407901e110f001c01c003c95 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 947103696 1250 947102446 947102449
    0x120b060705280f0302010203101406220f0915050102070e0c0c0a06020a02010f060e0601140309030d020c0312011a072a080c031e1218091003031d030309 67
    0x32500301e6100c048100d800b401030002c0740c454004452818000e80006940381009c0c3c2034400d400c1940d41064075040444950f1030307801c1e140c0070111551199200c4031424061203c20700085c130903801368001c45034000078500102e1001000da20495000302da089080e01c44a98038001641c0300d6400e40304031542200b030322000030304159203100145502100e0340c2c150340344803030113654140490f0408604040140c1d512004490382020030f110307600142407481e117142054a04000001c0030125444112a9070900106c08075401d608100709666100019084c2551620a044036aaa481e00444507003d50884c241000007140b03134450303a0344102c1420003c00d1600e41003668645503100406aa6242d8608002c100f02903e5000c09a07803070005421490041d18411800c0d8040500e02041c0b00001c2c01e00c90107448800c0071811001943c0c0c015410580310007070711186074001070b05078007003a20003c503040b16088040000064a07209590242e0b8407944031001480c4803111000c0c001c804180e40c0540543c4200040c5001d07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 947104946 1250 947103696 947103733
    0x703050a020309030304062a0b0606090f091f0909020f010c0230010b01020f070e0603030d06030305130803090f040b1210060e0f070903030806060d0c120b060705 71
    0x800035240101c0b46440c09150110341385a205502010001d03900400b0740701036111003101c00500c51114082c20b8000070382e0f5101c6210411014098611801000820040301c0d20381141020503520014007001123442c02000c494882140a122910050040ca10120b0307400841e03c41c0c1c02120f40c02401440300d94604800649802034000401d9a0008100f0309410924a14101106100c62140701016480c00c1c190307401c609442c3d00108003415504400b4910205040005c4c8a200b1204580c09156090300c800c00440e04500c030341c0042e0145c0307600708038003c4103042c0c2000040007084a5416140007540d40d807004240c407401540182a840403c40340b111005c3c1c60150803500d000c1c01700818515100b2849400140380004011013000e08544940c020480311a10074007a9a000541c65200e00091810f00c02c01010034406000042c1070058440215078140c81d00e00070b07641c7c4410780b40010020400441c5020b00491002d5000300409818006409581c0c24050300751a100ca0b80715000f400c0c02c4070050200d011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 947106196 1250 947104946 947104957
    0x9080f060a02180925090e060405040c0510020610120203030a0305090304080304271404060c050d14180115170c04050712110301050a031e0b090c090912070305 70
    0x1034075030402580031680c1e6a840c000d0003010b1081c00401c4480f0040c05c034014104542e42e420f01401082c5004002c640412002c0d198052001c660024690717603680b4242040d214250481a0080c00d8240c0000050b6000160140134400009800301180d90310394030456078a01c00c01001307400d90030601010b0560360182d0480c3e50820441b105480c2050785900580d495a0000c0d803000c0302d2003500b80c80300d14844046803081594202c084009002024442007021140d04010303000910842d95190102400c6208405480c0300c40c115080c2401012140144040e00c1642a96000c11003c007030b07240c000d1070200c14411540d07002264200701003514903003406185a1040383e01040d0803809159180d082e203035503c2c0704080c81303074a183d101d600c160f043d900e8041040f501030307812a0781e658004200501003030f90781100e0001201e900801119460551031440001030450302002400b150b580707014040321a42c0400c440a0600050342c03140c2c0d0b030703070b88020042d40d541c0103481d03003000ca10030200b020701c0129124900400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 947107446 1250 947106196 947106217
    0x5090105071e110f012c0a0308040c030611030106020f0a11121009080c0f07140d1401060f140628050f13150804032a050111070309080f060a02 63
    0x40e02c1d8000da00c03e43c2051209040070070f07207965910741710420060b044118000b1002034404811101c940340c030104d5881c650440060140320b11140020100182c032031105014607800f8805000030b00c0b40840c0c050340c1d90028092030025020380041059541c0e400a60240400c0d041203520301d2660800041c0b2030b01e40100e400c51400340c0500404104803171580d0003090751140c41281c82c1c5a550161080701810030080514a902c16040080d08001a021400d05240840f000b21a07044000c030752850141c2c1e001c40140184007040d403d022000408601c1105e04100722490b0194150040280c030b4104440d921404100d0001074581101107841a421100351102400c0542030507841c10080310051403072900424a40c2c03240720403100081c840841c845030400003003040c81c10700c4100380c10955006030808014031000312506ea1001c0c041c04049103503403111103a0340c1d0003000030040a100344041c1400741e4484d0034294045850300200080340c600008132030380c46c402c54401400c000d8072410041d0010b54414170011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 947108696 1250 947107446 947107457
    0x50a0531060e0405070501080708010b040b0d1e0504031d031209031f1b050f090103050405010f0c05040302191d151005090a0e27010207051f05090105071e 68
    0x8904039000b128501d00480c012402003400c103142100052949000500c1c0c2070407c60300c3c000404c1080d68001c199026142c25a51450301d940340d8074501401040d9541d60314180051214244208a0007507001c140154040d03a01c03c0528110010754002008440b030030350350140e100d01050100120f810015000300030005050f500c8490000d84014610300426510000503561038550b82c000a5078000301e000da0710130303074140702c0c0c2401c2060850020320700070800620305068a410004040100c01c1d8440c00310401c0e400d408101c0750742ca620300103002c0e8009010490040e0117946030350f1070b42a800b10542c0c0481e00c10840b02c0c610403080304103072000414050900c07041c0030016150003502c0d6440400100c04446190391b107545400016082000e4064260300905101900308103014a1110402030a0203500ca4088091805200c0100480c0244584540a0100d0149080744a0b210200203110100c000b032800d0140840d4494403640e82c2210002d80c1e5000c00b00300c94170315820030404c0c00c8a21280103652410f05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 947109946 1250 947108696 947108699
    0xf1008010513151119020606010c150b0d05030c03090109140f100519050a080709050f06070503120a29012f0f010f06090e06010911190207050a053106 66
    0x2030b95403604854403c0c01c400704090490201c0c0c5d40e0401c0050f601030b400b4a031085060f989900c1d40e25450800984d80021561900107043d9070b9140d40340700c02400f03070344101200d5650425100e002e807a50402d4402c2800036014210000e0b1000200040c0b2005000091000c9100c07240c3c041001100702a40f80800140041444981c14440441c4507040402140c0d0729096500c030380c007030b200800442000b4050028005110001c3c40141c40300e100514884506540f4207540300030506110713241d801640c0c08074520b4070160007080301001c0b180e0844402543c1c1c000d410304403004130041c4100142100c8041e42e0000c1c0300200c420544006405c810a607200402c5a03292a0940c040d000301e0800301d221840208607074680780300080c1d110203403003a54010094018104405a00b20281c5a03c0d20310602c1035651041e16241b22507041c14443e0304032030518040a0305131220621048010b515200c0034410303d4494010714800060700d0808010001000ca01070441c08803841e5841a101248060713040c0f03500c280c5586100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 947111196 1250 947109946 947109971
    0xb180a080a020606040b0d050a030503310201020c01020303010614030a0b0607030314060a080a08030604060807030b06190605070215090d06060f12080d0b030a0b0f100801051315 78
    0x7400d00401d40d902070a40340c50220144015a00c02c19601400b8541070100400424000308440e802c00d5130600c1d02c95034a8540c00081009001b0403a000e10315030354501d0b908100c1620b070100301004039100303030240c401804c0d0f2080103a889c0d01091088201113507032419500c4070701c1800c100942c0e102c1ca104400103003507078000001c5500c5400409003140402d540e00e101e88001d201d18406e02c0c0d4018011240100c0e200e04127003020391510721600004004101c0800072620350f0703440b50005006005880d0449941e2a9030741080048034009075180e6025200002c03c0c801401d184410395020f079502902c456250030201d40c2840281c400c00c2d0310204400c182440000360550b210340344200c06601580f8003003200d0341001118201c1ca0110f038007038114a03070141c01e030500280c002c20070782d00c40001c54140055130b912a03401180c1408080440100070035105020011300345041441103000d400c500e0307072022500c1d4613440014201d50041c2c9007518481086042c81002503800440ca641c1090100d034081029041c012 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 947112446 1250 947111196 947111213
    0x7020a060e1015050a0905100909120f0206010501081306061509080f0102031006080a09020402030a020a020613030915030b090a0b15040f053001060f0b070b180a 71
    0x881d8214035800601d289000d8041078000d420341100d80180c40d185103440d1200107103076210750307214510020380c4132000222444108000c040080414042c10310040700580341c0801064003400c4154042203824039141d92580c40000c6d52416984181c4a24100d900d43c040101d07912803001d001220707c19142c03000811419001004400302603455240d900c0424144015242403280b04625a070040e03205000b0000703481007620030349040342e545003800031054440c581600082c1981c00310281d0064000000e02c2011241a8000c1c4080d4007154240c0e100c0342c4510168680104180c00d020f00015640403080c00001042d0b00d04405c07400203410002074480404004c1006001e00f180e401d43e80035903865040c112400d28614222544401c4040c2c036250a0500c1c0d941100c03e030a0740074403030143d242d81c107000300c12134500c600800b80b808554607030010380d410b551610343c081e150b40d005189911485520020b104001082603034261130340020710002031f590381c5500308020b00d9002c0000c0a43c0c85040b24100204881c031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 947113696 1250 947112446 947112461
    0x60703080a090c080c0117100b0307110703200418020402030712090b0a150806130f0b0f01050f0d051902041d01050f060d08180f06040e040b0f09100507020a06 70
    0x40d02138040303000304100140442601f0000e0400102c00c85c0100540b110070303a001d010aa45803030114981369183c1074000c5440ca4603544a8170307644c2c030540d40044180312000001d5083c0e00c009a0031b015141c0511000d100680d600d8101c4955082c0038040c40310f0044c03826401856000f2400d14000710507980001c44101034545040c0700b9107003018404140402c803082d42c0180702c01440161000140940317030505050f99110028041c14154606011030b5080106100c0c0799054a5000a2040b0707450401c1c200118004a0070b20820b449540c4860415541c0d0401307040f0440c0e0541c115000c0e12400e5060140488006000301e800ca0303005030707640c0421010214850500d21306e01205400020301d484d121b202046081000752269204411101c0c1000004100f2400c50b09016101c0d21101e0045048102054807950410b00740b0741e2015003c180401d44036101048a03101e240580305030300ca140ca80790341e000780701c09040e500c461403034200480740307642e40c54203400098102085104036181e506854903000c0851303086 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 947114946 1250 947113696 947113709
    0xb150a0c140d08011403031e0d06150f030b0a12050d02060f0423010f0c0507290402150f0307050405031b10031a03030c15010603020702060703080a090c 67
    0x98400041c4401120000d89040c0e50400508840d034240101600c0c148052044200444600020344002d031400d105440c0c45004044040d100154005c41029083d0828000014900d18184001603a11540604402034819a0300c4540b100d03814028100e003d840c5000d030380b0350482d00e403500c0000d201d0110304c1d80c190118040d4018041d4034826150080c203102e030150060f40464005428000403800c3c1c40d0242c10500c040709082e10072401020802c1d405040044040f50b142854440b08104c195005002013035a07912464200c00c45c00d5455260b0707800c0009051450141414400004c3d005081088089001d6080c01170f603a4100a50f01e841850543c1c1704031650000614041010400d505041290440c2000c0c000e10310b5580c000000041035200101982c00000c261310342d28504101c480c07006420352160806420750b0750b6600c0101406540700d10390983c0552030142d0800000b1a14803a2007a1001154014800391401c5000d46003140c0f103c5000c2c0800c1140e6036103001d401d002888080e8040000d128 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 947116196 1250 947114946 947114957
    0xf090b0901150803030c0301060305090a0506040b070f091401030b120601030f0c060e1e04110313030f050316120216110351071d011b02040b150a 64
    0x500c0120001c5040c0c10703030701800b2075900a106001e031030f2100b042070341c8c1920701600d00091907070f90b0381e02c50900e098401c0502610902400040c0810300081c01e0040e4171480a40e1540300300c825034200f04440b902e585200f50701c0c01d880c00e04001070241d071113908040c01c118801080c105080200c4000a401c2113400c0c1e100304d9809460322020010007031070180c22002080141040e1440d00d04080105400b00302440481140491440c16800305981c0d9510401c5490a11100c0649a00c1c0a03400c0308442d011954041c0d02140c1e5046055260074851801ca80c41f402164070717803070f034490900a01501c410465040c2c01e2a9281c0030310828018943c040c0c1070b06090f41c02002488001c04070002810b0502d1001d50062303200b0908003070111401d20302240c0c54020044107107048451382013429021160031402e00d06d1907990300d0b9500280f0000715408400c0d004a8980844203103407030749800c030054800038603050a01040785080e9092102500c0c00e0303400786038000307400740c0041c001c41c60365841d074101540000441c102195 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 947117446 1250 947116196 947116211
    0xf02280f050f1b100807081503030409140f0a050903070f110d030302180306010528080a050a0303061409010605030a0605150a02061e130f02032b0306180f090b0901 72
    0x180901040d141c150301410f141289041000b00240341c00001000c03500f50628003a862328a680b010011103004112800e02040750b420fa907400c0446441094804008002c450000310307a01c8880c500c121401803805d400203600c0c0c0001075550322400720700014191500380f2881c1002e00991070740061049050312990300141c4e1590403110041d0200842c0303030403a0007a40b010740140300c191595030200d0b5078040300c90b010388100083c1006036050380480340c0044005000c6d02c0b0141c000c2103400520300300518842d0b01c007070280d16103680d00410380b00100000250b00000361401003090500681c002d6400180010000c200c06840d030300030400240c2006803090300c0200016401c0c40c215418401240c000724207079030820b00311450a098520b0010003424070406540702d5080c410400c41c40c0c001741003209501405480303988200203814003101d150741482d080742001c04004160740c07902c81d106402c152070045480c0c0600406803e800801801c0da0307194611f5043e9901e50002c042a4019a07151140941e900049103d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 947118696 1250 947117446 947117449
    0x903160801141504020903030d02210901021614010902030703050304080d020307052e0f06090b09070c060e0705130b1005180616060207030f02280f050f1b 68
    0x4811524844048501c280b0038440e003150310118550020303400710382c0581c07076095441c00a81076205403120240c0c5240b0000381000381c0b040034200c00341804e00000c4031040c1a84c41501040c00d1740300e1034174680c15000504510000240c0b10312510400d0300b4071940002103400159002c030340341800c1904141c40325400800d003009061400c1000b89041e0001d44060b504000c0c09580f07084d642d40040068900340c125590a94078040480c12680620280d0002c0603c65000314000f40c2000340040d010302504142069440c0d00309050170f1007094004d5429179190b007080100703a119000105204141001d0314012100001001d650701c207a401151003070858002038101da050104401034a20040290500c18103207c1c000710100c1840d1514072002c02582c2183e5588000440342c2c1e140d007201070000f009980701217400424590f011184030540d0700720b5000c40c0c039440010b0440c500404c005040d4098040340c90000c020004510f55180d0038450b1107801110030112601502506145c1d001e0341d040306c2000440f0941019 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 947119946 1250 947118696 947118701
    0x18140114060a05060306041112100602061e0a0e030d0905030d06120f140a0c080307030e0109050604090b0d05061e13080d0203150406090204050a0b0f040611030903160801 75
    0x107048808180c1a8a88404540c90b800000c00c2035200702c0c1d944212130400f01d5900201e80750041c40808034040b03403900f0300382c01c44115458054500180301c0c60002400c01c105a01d10440c044201c200786541aa0701c1c404410058042c00341280c206010a01101d01c1c2480d84d8002da0200c40d2140c0c0c081e580307a007851001c02c8222420380d4441b103121a00e101101c00400d5010103c2446203402040910400041c4a00f1611f0801e072000300501d043d22820002540c1f04020001e0a0f041e0b100c0d0351600c1c8064215001151480321034040c40394802800c0004121100031507202c0320050001402d5820042c0c0740361142401c0401c110781e002c60000928844a04150410079940d6000b8280310401220001c80e407500030f02801003044404607250f00002191704071410031811010300100400c140183c2da1201003040281d0400d118040c010040c0d440b02042000300041524490083d5036a040d09151620b402180c0e4080e141c6038541041c0001c01001c4c0c80da40301440580444590084825112440c02002608 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 947121196 1250 947119946 947119951
    0x21c050705070224030c070309080d08010810090c09090213060e070909020a020d08130f21090308030a02030601111009022d151314030f0712020418140114 68
    0x9036111100c000103401e4104415241c100d218130400544401c0c148c0750640d101815a04a42c42c10301c1085c4412800d1744e40900d14034180c0703002100b5258130142510407981507075402c0c10020540c03003400344140400c4503181c3c0300351324030350008000c0344042c01085e110000312003907508405010114a01048009a005011000103203100201180360240c0580002d40b60083c0503030090801c8602804240280d0741111075014068000c1003185141c4020b2401c1d281400c2c0740303c0f4070200041c1c004d288401b11400740480e03800b03e03500405100e240d0f41da100700ca80000d60000b420281448010425007c40b040204803181500c4240c0e01d0004806555004003e0300b000d0000300c01e444805100e000401e030030b41d008001c0c41c40440a4a041001c1c0c00c111890702c0c1d190140e0302840d82a0100c2c28400a80070b155842490010482136007034600d4180600d80040d1520250300400407000c10b942008001403d00d80d00c048810300c043d01a44c1e000450030b07610004404101ca00074640c50303442e019442c5045840003401034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 947122302 1106 947121196 947121229
    0x60f020a0206070e2409031c05041a0f09041a04020a0e0901050d031709070e0f04030e0f1302070f170a0908011e021c0507050702 57
    0xa50341c2200301c403c5000600b503881c1d00c00803800c202e50014052058000000040c0d150032003030303089507402070407880d070581f103103188000109405079100c0d49802e00a0b502c03107550f246403880d0603440303400c2c5aa120300716920800c074401221101d6400c6815201080e240890440a800b40098400c1651940107420a000091031450164030840750352880b007044400b0b400070398941042c007095010805000700490200220038240202d03004da8150b200b0411000c0b00d00d01b0740c81d01d601543c0c42e0f000360354050041c1d840e01c0520040581101311111812426100854208042c800192500714206404c031307c2c0315400500881031003065000c40310520f41003924003d020605112000d02c0346c0c000b42194001804200001c680784006020701e185048241e240f01c10381443c128123040003544a1122000907800394450054000d017a4010541304400c291507560b00d400c107a0041c491544801c94910 = true := by decide +kernel

theorem cover : BRFrame.Cov 946942446 947122302 := by
  have h0 := BRFrame.cov_init 946942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 946942446 ≤ n) (h2 : n < 947122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
