-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5393
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:43:16.008057+00:00
-- url     : https://prove2.me/submissions/3ed3df96-470c-4b3b-b395-44777e78155f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 969784172 ≤ n < 969964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 969785422 1250 969784172 969784177
    0x30f0206061f0e03011509022a30071407090e0a0807020607060207031d0604051810090c05090f0f0901030f080c010903030506010215010f06050c030904020a0f090902 73
    0x140c028a14103001c20100740c03203c0c089003842d19090365969202007400c1244210260003081d0000005039074001c86140101070340c0c0668071890380d005a40c00e0354594104009070748010207003900001d44401c002d421107100c0940c8221011a84250046030103420f000c00d000c00003030044495011160041d9a07410300405079400c030058020140c101c04207a0000c40c4903040109403040c802416280341801c00e41d5207108a0300644425000520445624201c80034000803032604520b04a85190405140c01c0008d20b520700b00f01140740715400707007401040c40010506e542d500038040800c024010b850075060003c0c100e40050b00041d100b80c80040b10011242052260901c603408081e044005507800d5480e5810003103001d120480385040c04210482d1841801e1043d4500d561003a5804031740e600303121000a14041c103070f4a6000c143c00d40103004100b0b51000c52038034803c0382c4187c20000c0d240d02e112141642140034287d2103642050001850742d00031948006a04005802ca80341c2d08901502d0f181c0e84000c07070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 969786672 1250 969785422 969785449
    0xb0f07021204150e10020c09070309020603040602070819110c12030f0325020706030518061602010906091a0f100303050d0b10030504051b03100c0c0807030f020606 72
    0x1c00c02c100600c046805400c49662104050506403428000c42004ca00710392960480c1c2d0006030000d007483c0501d80360170300504c2e802008510701400404d1058000554130b101c041c0c001440503500041190030000303007005680b5403104820450b2004848640302500c420525007134642c42c1c2c05115264000c0740342024903005c4920740302d4000c42c1000341040044000d80d0000d0300718601c0902a12142c4104102d00840034400e1240744d015140251a141028050741c4001c0d01e551680081d0a400340341400001420a9120f01403440c201c8540442980030303030042840240c0500000e003001c81c52814031501c243c103140c1449101703142d401540d445030040382c1460300c10341d11084a1a00790078200b012903c0340d009002920354030b44000900d103804030001102400c54450b0200442c0d12a03040000340032040c0321014950400e42140b4440c444a00000313a103034640c00c00800000c9a46607454640303103200381c1801c460580c1c030009199580c411418044e12040080040200500c644400034000c0e050044001215 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 969787922 1250 969786672 969786703
    0x1121a010e06120402151306021606050712201e06060409122d11070605160303021608030f150a03030917010b10170c340503070b0f0702 60
    0x3da00d843c0c0c00c015000c2810308180058131001c0c003118100c2d99101c80780000801c880d4004008024048080c01c1c04145903501030401e200c403e119a03c00b183c035609603d036140301b81385403510b040081c2c4100070b20404160343c0482081d10800c100c0c141312181690101300e03c00303444822100d980d41d5442c20041900c000a00040c0100300718a40c40d801c56004404a84a02071840c103250944080f0264010440d011911800000b8a598040e0700c0541401c2c8004e4001c2e00c0f880c078040d4034222410f203130030b89071f410101d500a08140c1e00080401d142101605152030580d0300801e1250b603420700e501842d20700300007a621003459410f80080c00c121854040c02c0c07101200e030300da00d9440c141458a0030100e4200f104103206046952900100c801c0c035034503640f2490305038000c0d0301c95810380c1c1000e8a040121940080103092444400c0129102c02c1210400c04508075000c54814000304880c07034107141c505818114000c05130b00c00400d84200704082d00b860309108450b400380c00e003800c5d07582c01022a0b41d021000c2c107082a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 969789172 1250 969787922 969787957
    0x6031b1e050f0d050f010203041110110304060f030227011e021525021c080f13210c1505162307060e011b0210020901121a010e06 57
    0x402d00384140b200382214004e0090b81c01201c036600f0a01e0a907403081318100c400d500301c1503000d002c0746400880e911030b00010785040e05103200301da45400e80d2481a40982c009104501003900c0c07401b44650121081280388240038441c807550112a00304d8440c500c113899000c07803c003199904101040380034031071090000d80d00402071410a51401942c4c3c050281030895480104507024031001507000f840c44d0220840c2d40204444408841401d40a000354004030341008041002d114810111061031a040a100c030200880500a8a030909014031600344c41080c0585400c000d522a580120714444260b020389140c0d0400c4901c1c00002c82110822100120404400e4005280e030ba0301c203180c00240500f0201d6540c02c40f805000d014101c1c0d80010b5001c50300070703488503401c5080d60300078002d88060060000c0c03040c80c41d092511000e51034004200300c144030306034003007014021a8403030703407100d00c46c036000344400c120300140d03420000105160301086034041403c441c0914220701703101c000c40d20740c40080385c00b094 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 969790422 1250 969789172 969789199
    0x10b070b07230a0801090c020a0b06102127081e1b010e2e0c02010f0603140c09131407090513030e01050405060d02090406031b1e05 58
    0xc0c1d02c0e01505020403440303a4141c2d01140328502003001043c00c0302e003544800b00d0300d42c900107800081d901e80000c86021074225038245400150311410040d00400219181c1041d100c001008a0f0300d000c50b40c01c011210500e10342140242d1085504c0800390030844003a041445800515290400120050007840c3e100100600c0b01c048450120703070038900d025040024603044c4030003d1b054043d0041c1c11040ca42381d64461440b02416810848480c414403007050f4042201c1101c03c405c0c0551030030450000b807164440b580015800c1c801c0d80003003c00e0401d00c3c000c00061b0b0f12410300d07070480001e10030910124494078414109910308005c0180c411a03051a1030f090070400c42d0344003680706d00b803044001e0040c82030045c0410140342c68002c25102e49410801c090414029007001064550155980340c1800300400c814000c6451312011102220010350700565526803581c04100109144d50001d884444030480303509001c428080d021040b031f80704103900b0400da01c42c450703420314010f910710401da0f02142d11103051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 969791672 1250 969790422 969790427
    0x9110415171b062a01060f33030b040c080711061605090607020a0b0309060c040e0c0c1c0f02010609060b1b1014190513030311161a010b070b07 63
    0x1c001950841c21380f4621800041c0d64014428600025062540d460340d109008081c890444030307000340210032a10350042d040380306c1c14001da41c0c07804038101c0e01c2c0c140b6540a07200c2c902a4100c0d40400c480034000304440020004000e095040640300040000c940d042c194101b0303400016040d004c0c841542e20908101802e8005a402c1e07803020560a40101049c4a140d015a8070880010000c041c20b0b4002640d0f03180c070500b410705002004100400f82a000d02c8144403c1e0310f10701480c0c3d80300c0c80c82c41c669540e0f1200500a50300c0c0004008201014044408401e078070301da801041c84650b110550000e01c410354032a03402e282603d08900441002a0040c03040440003008824556841d44041d41a1086901018032001c10f0300c0050500c14821000c0c0d400380000b2152189240040046440042101e81400e10070514022039280c0060704050302c6801005410800c0c030111210303440400540030b482c424520b0314200d01d1111410100c9038481103000041c000040000303c5181d55805924015299242c031000e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 969792922 1250 969791672 969791677
    0xa03080604090c0b0904062418060c0609140a0302010b090702010b030c040c032007021e1e0f12150f060a03170910120b04020c0a0609110415171b06 65
    0xb80fa6000e81c0300c40c00021500c0300d2681010f403148d90144041e03c04018100c000e04124000172120300d030303220006003c014a03a400054a00d003a40e001401007440780c50303400c00c281c1800092070402082d001d819920002c040d01540025400c400a64041c1800c0c0e441d07560503030807915000302c0030390142c00503d00d08805140c5548810b200c000e0a003030002c1c0e0b0082c004000300240f0319501100750810300c0004c03d6015441c0401d1080340610041180441198505021401b41d0000640c41074046070091001300540d43c3c0e5000d000d00c0d070100a046101501142074003d50744640742c03100860303901d554001003030507221640c040368416036014101c0d501c2c1d68510b95501905240140c00c80101c0c440c140469000c1e40d40d0507040500d44a0741d565106a621021410201110f006990070342c450751042241207844100800c0300c06c8116003000740000d201d40b003802c0c02200303c2090880315034002d00d00f90080e10303100141106001030f10640480241000144000c1e02d540f40ca0808841980b01100c0202e400c06140c510700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 969794172 1250 969792922 969792937
    0x10c02010318060c080901270f020a0305010c17221e0210030c0e0102011e0c1202040806090d08040b0a0e0f0601061d2b170304050a03080604090c0b 65
    0x120319907815010380310b00044076403845004c00041c101400b80007104809006644400c80303000c0b040f0a203010b000f00c21300c401001030b40b40240348005038900d000c03d5541c0c0050010007190080028000240103d10060441410004040b242940071020074141c7c040a248064001c10480ca08140c4100903114010450000c0c0c600f8812006002c4a41c00142c54100c48603e14425584000c00d4101e1b4a50340604006144c151540c1160315101200300c1c0d07a00c0320900c00050002e24003002403c4001104112514686107016a4020713000240c0010f01500000d07455201d00d09040980303421a0540008840f40c0009a80c05440300d12900c020072040900c90b4020a4034809080454002d285607200c01c0781414002d0340882d02041860861f0000a500e9444680a4000031034910141d50165460206d0702d841207440c618840c600a1f112400300408000100051204440740d0340c0c6901d010710b0859980e4607010411030020b41e04c40302052003420a0b0269140850b442440c3e45031241c2000807102041d0811b06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 969795422 1250 969794172 969794201
    0x702060414130e1e0607300213030b1b043006060501030b150403060c02030c120403060c0302030c071401021b070e012c061504080303040b0a0506010c020103 69
    0x70141800b2061031040d2000500e03140c002c0d004000d041c850b110659000d900701c078002a0849010030000a600600320240120381c210503000045442001003055a0800e040d501450320000c2c2000d054040c01e808030381240d00c05e0b100c040842e99a40d20080401410f5800807140601c240001d210380750504c2d5282c02c400c108007a01252140c01c00c00c030120040c0b00d0035030603230f40e9a80d1224240901c0d40d06002c0e00440d4802542c003482c40c082d02c0c03801449184070310f100290245030703298645c0030a04d01c20710854524400d8141295500010101c10781c00b0782d880707840300310783c024601011000c64034024000d9070300c100100181c19062685603202c0c1d204000c05001000000e550070004118006421140e50a050002c8030060a08a05108100c44e0f9004103030000b0205117207a8943c916080b040c032a0400c4400c0a082810a040e120a07001c00c04031800d01c5102c6076003000105d4041410980040078610136130081e885001343c1d444e68040c0500700c0d101a01e08a000600002d21180903500a070001e90101d40001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 969796672 1250 969795422 969795439
    0x20a050d0f1b020102090d030509180c041e051c050a020402030c040801060b070f0323271212090d050613050f0d0801050d0f0506190608030702060414 66
    0x10595002201c544141010340566240300140315280c80b01c09007940407055000031440c0c140d0701000500002d510300c074000c0403c42c00098151241d01c440411008142060280c1005c9080c100c81080315600726001d95208450308083c29210194030440400c106d5801505040c80700c0c8612076040e6000301400420740c0e207440790819034001a00c03244000e41c41101c8c0402a41d4640d07042ca18032a003511159806082035280500044000c01c240c40900d030138455050a10300b2a10716010482d41142e00320000ba520b15680c041100d40e070700f044a030000c0280c6d070610b6030b00f0041c7c03400010400ca00018200c0b035641842d8460340c8594000c5c01c4040040110040080201c5107110a50351071500d090030407180680301428078450782080100030041c10b01c0184001003c0c01c0151052900201101c0052150300c2c40380c801402c5c00402d00c1003040050407040c5e04481900c1c02490582d415a003500f000103043c04146150500c005410280401513840443d401000d00f80f40ca0f01e00050a6130b4145511101a0b00c80883d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 969797922 1250 969796672 969796687
    0x40203010305031c110f0d2415080c040b2b061d092503050f1011070b0402011b05030307030b011115010b07030306080607020619020a0f0f1b080316030618020a05 71
    0xf9603410241c000312845016008e6040065030311020282402c124140b009444c00e10182c840301000ba142904d074884076550306d440da030220300380c02024000300d0b03061a003116240396842040d882e0400000e179560115240886400c010002c0181101180e0103841074100c0800404800c0001c801d40200b10215003507508030f151240c659600309084001041e43c580c1c0714006800c510581030161041504c030b51350f0740c1820071031300741ca484440e07a000804c003d040113401112070090004650240da40d40d5040f4003102e4a901d400903002e402010052200c60214114200700f0030070000c00264041c40700402141426540d1900f10a40d91607000941c0480c2499241e642c0403410703100c02c00055125103502c2d0300800150802a00d41e410078540311248603d4103004000d40d00c00300d5084413484001c007000d031400b11400c0d01e00740307001c9601d604801000c0c20000c032103980440601c010040514082d491021440c11000d44a83d025070450f101c1c0e219035041d4021011140c0a4046240d0140c0110100341c101145480e55 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 969799172 1250 969797922 969797951
    0x160e040b04150f0e060d0c030308090312011806151205090f0a0c180603030e01051b030c0c01030e0f06071107030506070f0e15090f0f040203010305031c110f0d 70
    0x4071500f02d41030000804104003c080120862203410407000e40e80d503401100c031600d80c550451114000a414040c031140841c0440e40d040080311110088040200001e585604090004da01401c000340d52440c1422400b080060f03019200070f8048030315440c0c0300b550450444014015100040a803100c40c050401c162000910621007130000798850b0014030b00050402e4225507510707001588503800d544ca00780f400d10000390840180200350070300742426070b2680840b0004c0106902c5050344201f039804040303410400a01c0c00102040d0200c000d803018040191440c00c11903403000c02024244443d07024101003000320307015250100302c201001095818407502c90300d0f9a071804000750707803010000300c02074040f580d00c030391041003006414402c841449440780e400c50144004d004003200c040c41045000603001d80d640e01c1e00c2c3d0642003294050310942d22507940e8201582ca980000c040c0c1741c0c41d80302c01002e4404045240c89901985c6a10b09941d604048031010300c40c225820050700b89800c0f640d140c422821910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 969800422 1250 969799172 969799211
    0x6051309050c0409030c1e200d0c0b03011409060f1002031209070315050f15040204050d06090303150b040303031e090f0203010c05040e160c0f03080f160e040b04 71
    0x1401782e05e40c5041c2c48054580510392210f110035007006013060b01e001000040507602c0703201c5d05000d45d005152003105c0c0403000a800c042c8528000300b11500409001401040ca80082d60403200c4118100c000d59100d042880409602124140e40c01b0082c04011401e51900c4a00428129100d1044030306080b906d131151a00204141c07903e14440d4132070a401c10400c00350440125807607040e0281441a82840c08030541d41000c080c010640c4006211152186500c46038141d9005140050100ca808e59107070420350300814507442c0c103400003030038105c1100c0c2074030340c4a1404080300c0d0360101306444c103807860720118010903088201080d00e01c002c1140315003019080c01071501103130195a00d803083d14440c0c810582181c11a182004c00d101062108203e0741e41011042680006030143c01a25046c90010031600301c0322031400101004080e03070445045c9030b80811282e04c51842c07200242041c0c1c903001390119207604110100400240c4c4042e078010740341040d4010b00e4071203202030004212880806240e801e0134 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 969801672 1250 969800422 969800441
    0x3171312060b03101415011809050f06010f08070c02040f0501090b030c010e0f130e030a052104020d0f0c0305070803090a05040e0c060f0c0307030914010306051309050c04 75
    0x3912101450824601445000c81200b98108200445c10b40003040280e2000018040e840380e8900444124041c0d025501704044c101c080b5100c030410a444000c00c8005040545401140301149000070b4055405615100c400e0f00c100d4030f502e4450b41d81c46500301da8413a44852304907080354407141c0079a522842405094082c00c42400d0104101c98150141481d08281c0c44082d8100040d0726881c20315a00c03100701003202d200c0c0c240d43ca45501000c00c1800d01c041d001000300c01025110010701820700951080207401003010004035002007203070340d1080003207c0b24241c0c0e0195003e020a034044000a40d01204500030718407a48034000b090ba42c98450701d0130f16500d035000c6040c6800c0003800a0388c501e01070209102400b000c444c04c02c990100340c08240d5440300c0c2503c040c0e00502002840f4505101a01d0540714a08544812680c2d22841490020254402c51040082155010241036070960090080ca015114040c201c45010700700c181c01c0c40090250304a0035241c50081441e00342c91074840d80242403e2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 969802922 1250 969801672 969801683
    0x1051c0e10061401031b12090b0f01060809010606200114070201020a090f03050c04021b16030b0f061e0a031e0b1308090904020a08190b070903171312 66
    0x80c9480c00c0390b050340c0034500b81950f074101480d04051072240000700741c1c0c0c4964141203103003282c141c1240e000010014202e070003015144203905020050302104610100f0b05807000707a41d40071425280e07140041e0aa80707460240001054030480d440700f0038610300e118482400e0b401e00011401d141c1d441501c50180d50207881180c010303500003500700c900c980c000c5041c4c0d00405000c9421003101d841c58a4064581060803c0715104640005260041102c046030941c0c00c2d1800109903941c0180342d0040c003080c000d6a1000f1150f4800940002e83e408a40e0105148100b50180c0080b001c200707030b0340482480c58111003005901c4907213170340e02102181080d007003003140741c01d258031f9040750380c1d40c600340945c1b00c060041c5410341c03a80903480c4020000322140c1c2076880c01541640e62300042e4846100080500c00c460300050442e03c01c03a5010b0484504604c17048440303a01400c000e0305961038012084481192500020305041e0714400c1e040340c0300d0020780040403020304034840d081007da103407112f40c90f003001d01d4038040e80e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 969804172 1250 969802922 969802931
    0x5040909060617031309020706110307230c0613060f0216021c020a06030f0b1302070309060f09050904080408120c070e01030b0406050702010e010c0201021e0901051c0e10 75
    0x1106045403581001c050f0340320015410301c203c00800410600550061001d0300703401040b01c5041180a13000303c1c00c0c109081e000d840d2645012070000f030802a01800454065174540101c84030102110112011540d2140c040c04c0c56035941c440d040a01048164100c410550f609140c6052560920107040e0404500c0b00d030b4900401180104503100f0f55190f890799403010100c402200503500e441e10030086a4aa050104808481c016404020064408101d40022903250381080c444001d900034400d2900c40d03283c60003030715100c0700102c2e020441014a0400300d030b10f40c1400d0080e031030092078450340980b00c3c1d40034a26103030b141c0d030003103042000c0700c038941c04c8020020908000e0b2440502c41240504100c050740402c5624585a01c0e28918002d0302c00b50030305a68002103810740d1700c01c3d0442e03c94003003400000d219034201504024000d52040d44c0b1041c0d140c014148031042e11841030101c480d5050140c0d00c0e14140380300c650031a00000703051080f8880d4181e43c0c0d42031040002c010700c10003148031907500e00040e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 969805422 1250 969804172 969804179
    0x15050a090515070e15160305032e142b0c1502060a020c01020d05010608150108090c0f19060203040609061b0305030a0908220b121501050409090606 65
    0x145030610581d042c01d0501c8602e010400b00541c813041c8074140a000710307510204211081401110381c411544081000002d0a01c00070a040d0408001c50061345280021911007036210251a00405407107864841d0856011007041640d10030075403816401070082003041003450741180f071925042079044d200d030f11800c14286001403080c24041c40c402092400000640b010380b1703d0001b9200c81c8010b2140105c141d0115402a569000758199074684007401d208102d02c0d40c50b86406041c04100715040842400601c0340d50205511074120240100a0107004150054501c030401c40000b50346180e050300f082c260203e84500217100c0c002c031001000c56170003a50f40e9a0034401c00400540440e04500c2c18400c2009400d0a081b04e525031000d129038041c5400b0b45c030b9450310701c10100a0300c80c3d044060403590b004141c40740744150942c2c4498442c01849070308400c0c2d03643c500003803400d401101c405641c80c40c0c0742000100c142605940d01c4080e0101450000d10b05620b41c8043c204a9a205805071011580c40200b807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 969806672 1250 969805422 969805433
    0xe15040f051002032d1b010e070b090d0609060b0303040b03160c05100e0c0a03110405060a24140f03092b030b1c1a060d0b04030c15050a09 61
    0x70184220188082c45c40c00d10b40c19a0401401110002da01100e02079855500c0052040c10590380a0115801c00b140200d80709a603542c003070a220000c2440e18007900b100010300581250403158500340c0074204c401e14001c50307102c07031000700100d1005880c4c054031500c4c900c1903940d0600090001e401145c42061300ca04040501d82c49991080155400717002080c582200480c0340090f941c1050720603c00c02046000c4102101030622030407a4081d50040308220011007085440c10200030003080640e0104002d035545802c12402080510801c1003119401c10302c5510b84110300480c80504440d414440f4001c03065908508442c2d001508072415503c02005201c0c0d030b5082844041e909076400e20070116039041c0605900003403034081030001c0c1890f0b41c03a03021721815151100c40c0015860022503002c0c20801d507081420142c0100385190384070085181c0010101c1c076040001140381d680065030400c1d19621550281c0d940003190000b41c4e0f0b103a0103150b42010b0300d0018020b16200740801000482d20b4050351501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 969807922 1250 969806672 969806689
    0xa0305070c080313030b070e0a120302151b3f16080c0c010e0708150c03070f0e0409020a0f0f060206040203250e07030c0f0315060e15040f05 62
    0x2c082a0300100003144480c6602007210007501d4100440d040e281c0c86601c0305807010003000d601700740c20940c803c1000440d034502540c00100030b8040e800317491052030b00310f1010181d024115020303404185444241e10300300c40c803a8080c281030703400c803c00350082e10301188084c0e1250303402800c06e8403800c1402e20208500181481160b4202e40e9111a40300002c5000b13401511f019001401c4458410300401e0015501301d0940110388200c4d030510540d000c0359101c2040c0d03521441c08840d440c07001c2035140007040c008101581100d02c541c80c155942c2c13010f2424114122900380b40e001d9100e900035110250300d40941d40b10701c00c08004000b91501c0700d2045d440c020a103070003205554000415504480304104c00b40c0c070003003582c0301c00d47d80c0c8909050b00e009100e0b500c0c05520031190000107038609070701c080000a1303806900401000d5016164180c01c0d4910740c1013202aa0072408807440e0701440c2c04010014075000740d690954900004002080c4138030307240302410305500113504c8002c101010032410403203810503466 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 969809172 1250 969807922 969807929
    0x5010f050613060e0a090e0303040302160e010b0d1419050604020a14282606030a031119030903060605010305040c140d150527070b0c0c030a0305070c 66
    0x1070340c1d424000040c011400111083c4100d070248141c00c07452202d1543c84402680141140490400403500841c1c542030750b0790421141100540315074000c40c100c1c0081c0014501c11110120342c01a041da0130008030380650303088003100e0b11169441e00d8a0107941c1d105c0d407040070320801d00c0140c4000c0c0c10351410613410540b0b1003d00f03454001e501c1044000400d035440780740d80d07000042001074161348481c0440c1044035103206020b01c0038601e10f1070b050814660f078003002d10200c0c5c1e0034079000d400141400c138803080b12002c070a40300194140d1001031003100107801801500300034402e84042c0d4603c0b0780c0840203c200c0800c610812000910241c1080c410881144500700141c6800c0c42d0030000c0303140c2680c0d5642c0041050080d2910600c45000c1c0e45501e50302c0654882502d0740c0011119502c00e041d00400f8003038402500c041c0402d00348003d148020000031180c44480c442450001c040b00b601d05082540145d00030401c0740c0480c0034403804003151351010080501464403903983d5a984515034203114411200e10740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 969810422 1250 969809172 969809179
    0x3050901140c031803030702040203071206090c0f080406060509090a05060a0c0929040b070203061f05011103090301151e050306060f01050d0501150314010509010e04020d0c0905010f05 81
    0x14074000b040000700391101c1c4101e58078034206060008000034030b0b40c06260340096009000000300b111250b801800320100302d010007800c0c441181c8131210f1500b650030000b021800100072035078016207680724000b0b15401900450740020a00d84443c080366000c0d004683c2d5070190b0381708103030441c104203041158661000c41c0d10002c020f007529102c002441c80e00c1d0351258109001c2aa0000c4a50400025142d5100280c0b500420303903c03a40c030484541039030410b40050b03209005c0c0c00006804070032918542d031a80d4001a4a00403890308020040d113901220818030380587c80240069107407a2400d102e404551f5140c0c1e8109045545040080c4503c440e0780711552406641150741001103441c005000f640003901110035002280002004139002e0050720400064a8180300001540700c0121815102d0f00c1c1c0541c0d42480070030710507180c2c001e04040070700c00d084e040500e040041112801201141c3d07001403000705501340c01e041a03160001c10b001d50f900000001e40d500c01c0104140d00d10445030b0f20003040180d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 969811672 1250 969810422 969810427
    0x130e0103021f1103030411040507021f0c03021608090f1008070f0c02030114011503020f03060d050111031501090e04110409111306031a0609010618120305090114 71
    0x15804110350710405410341002031000e0160380a001e0003042800c01c200510000c407502c5c0c0c5032909202d50285051070404d030003640b0340804200d01034404143c11312401a0500300c3e0035281400e04180c00201920b407a21030401d80e00307003c000da4414903041499101800b0741c0c02c00703403a4030809082120544200325003612900c1645010b0b02500c0c0c00c00b0010b9480002410015989825100181e880c034908400c029030651810515a00c42102d00300000d06941c45240c941c00a0700c800e110550491050000c6e01c107031240184001003d80ca01b80204088080c485d00000c40c5070902c1402c3e1010700d40068a00820902808040340e1481d68018002401001c085201e50502d082c0380d110703440f0840c0c2c904d403854041c0352191303c0300c010300540d80a5000ca0721005004944454132441081d8000c006602048400400f4500c4180782c510881c040e0a0141340d0040000c9440d0b46021000d0341c1c42002641c41c00040c054008000400f00703001150803560318065120a40d5841c8c52000040c045060110a4880003506 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 969812922 1250 969811672 969811679
    0x11220e060d060e01060b04121109102102180108010507020105161d060d020d050604020a0f0810030b010b04140904050607051308030c0304031509020609041d0a08130e01 74
    0x19045075021081d00514001481c1d610705800e40d0241c8081d8100e921908000100002c7d040b5080c3c8042e41494003915200040200c0c0c20204a10710300c058892400e51500032005019140480003500c91180c100c110000145c0300b6540411302d120041c0d80e4600c9155003540c01002801003e000d019805441c5100800807071610384114015581c0d09161001004038a588030a6000729422000b0401c0b4002040c15441d4000c0020000281d8014080820703c40e0910001c01c0f120704060003503803044001034899501201c6030b201c0446403810b0080100150811400000010680171211140030b84545a51240c2d030b5800d0004501000b400c01e00c0050003506042d0800c0042407001c030301d003608401d4070703c0c010303581e0391210f80403050030791254219011a001c00110f0480d10240003004008803481140100303007004c000784a22044a0000c04d0103504410100003600b294a841c2d8410840703101c0b1400707000710400d40707002c0192904800e6070742298940e0000a0002e0002c421008a0009050442107200550306 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 969814172 1250 969812922 969812929
    0xc030d0e0f24150607150b1009081216062a230306010c051b091807060806010c080d05010608060a080a0605041109040804030627030f0311220e06 64
    0x50140034488083c0030702411035683c0000b19003405820a000c1580f2101c24401107000300350080c8058410140c800750280d040d8001c914101c03c6070a0100584284414101113a00f81d80c07043c1400000074044031103460000f0744d5071256108041902c03c0802c611650b96006c009001c0f82c41c002902840b1000700c00000401189802c110744280100c0e49a8582e15504010307101c80204140c000c2160140e0341d07000b560f61000303451040020808441e8490540c645131403039000c90003491a0488181c04c605000d00040b405404c2c15a00064185009031151a807502c8120154001c420031410030b64680380104115944450301c1c80c0c1110044503d10115880e050b043e1380e03600a0f41c00003c142548901c0060240100a4011341d403500028103c0e880c02c0c50980380000d810f504c08c1c041212840d140400c105c1103103242c8460f5520007514100b00c0702c44140b994800351480800224a84200f40d151400e911000341450f010305041018100c098034086a44000e03152591803d1b0804a40d8448000070805c9554 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 969815422 1250 969814172 969814243
    0x40803070c0227060a0503100e070906080303100902090d031b0b07110c06040f031113050421020105150d060f020c072102030a080d0b0306011d1e07050c030d0e0f 71
    0x201c0403600158001d622091352b1f003040b016078841d010141c0b6001d0001448100400194410065078260504194650140600b280101140c0c3c1342c101000500040000e030240d414000702c41d505a43c4a00081110341e07d14014100c21182c40c0b00250510015a820100030861100f100004940140c10b160401c9074801c1e400016100103403a95503e0703040079903151074a81034007117010400301044c480380c40c20b800c0800c05243e961001180c003244a000c0c8000d214818070a050007000c803002103516004041c0100805141030b400d09580701641c0c0c1c080800015420b00c0100041000d44000c0d160040c07520354082000d18017a004102d6500e580d0801c880142e81c049508411944e00c0780000e9103821035071002000400f804c0851982500c038443c00403c0401e0112030080c0c2e0606030712034021240d5152040213002540b03880d10840c00b01c1d800c0009c6030810b802100905407c4685204590800602c000680c095400f503008250840e00b0085a40300c0c1c810003404803a0703011000c00705403080d1884260340c8400302c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 969816672 1250 969815422 969815443
    0xb2b06091a03060622020d180303061a07020d02010e03250503070501030603080a0c0c1a04170a02011d1c0c080d020d05090f01110a0c0e010f050108040803070c0227060a0503 76
    0x5550004a94000014692110a14908c803084110281415240140c0200458041c03900303400025948034074840c0515049034540d03580a03142ca096100f29500540c0d120709c484c0310050b0301d40189440450b0001c00c0216003c3c40000d07010400702843d05d071a0915040903c103800290404d810114140041080c801c1119580412864a01c009507054101541c00e01226081000303030011540d14964003e60020190055a02ca0445015102e03446400155107955190f0024082031401c504444a1a54501c4040e40d0740c0000c2c00e10007a26010710381c62079911680140c225507000a604044c0b0944008010200c1d001e503c5000401001008a401406074007402c01d000c0d101d5403a40b01000c0c0240d100d050313030303c05a50410701294402e080f24a0030010322085c5019019407814008000901804614000000c5610603110142a42c03555220402d1552000709030354284441104103c0c01601c41e061784525915901500d08081a221160400010400f17010030744a00e0105006210f960790205040d00300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 969817922 1250 969816672 969816739
    0x18010903020601050f21030d0b06040326040504141501020a020a0e040213020307031a060f160f14060a0608011a01080414010f0c090b2b06091a030606 66
    0x2e8094940c0011100300220350070010100746e0710041c0c1421000000944941901c1da1024082040d440040c44041d00483c400504907560004411010600042180e41081d01803c1c2e580d00c1e003a122004101aa044410154007403980c803c1000442c0c60703241701b00c20320540700b440a040c9100c000e0b000510b00002d02c3c01000302d000c068101140442d541c50351400311521b01b42c030342591030707140605000e8002c2107400e080c14000c60000c00d05c002185003000c101ca1110106010b5523040c1054049408100903404804a0f000441421844040b1f00000d1500d889052140014011841d1042c50130064618a40c48003507541e042601c2003020940e031000c80c05c0801028604581250384909001d00ba804032121199495441c0c101c1004046005402032540071a0a0303c80003d144e684012231810707845481840208480070608510011a070548400311445048001161854460b0151011110040151a81218114140302e0301d414148155580024201c130200341c5440d2079580e0b22a03400028292125 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 969819172 1250 969817922 969817939
    0x504020906060c24040210030e030d0b0a0902570c04060308090a0b0309030d020a050c03030a0b1201020702090c1e04121a0103030c0213021b061801090302060105 71
    0x4241c4100448209804141503d4180301c0b0900e6050902c81010ba605034000e1040361f81d90302c01726019005003000080c4000c002c528200310701c11001c00524441401943c840717044400000e20142030b001401c42d400f000480024203011010700010000e100c140040d00740903443c1d03070301c030004c1940b0b08018020305101602030001311240c800c840d04001c200415154840d203820720101c00c1c005004081c155800090769100e100d251111384203c064001203401c607801c0d5208019426154070680c000d42066040b904000e400c0100b111030060840e0030444407084143c1c0d072001c5403400c0b85440030f002a10610321500031480d0a90039004120410001404040048800100c281c026441840d0f0400c050000021880d201c82d201d0000c0389036842501e000341e441c0d0080c10041345110390b0001c1c400b4126035041c0c03280c50140d0203030340c24880c0c244c101c9956a42d01d90707401d0000c00c004d080b01da08140001ca0a0b100645024a031410300c43e0703600e0511b400080010f03894030210100190300003910b281911f40c1211a00b4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 969820422 1250 969819172 969819187
    0x11010c0201050c0d03140903090922050d0203030a0f0b010e0d1b0306020310080d0203071218060224060607110402160507030605070507031d0d0611070c09050402090606 74
    0xc550b48604140b611852240145007021300b81d1592102101361080d000300305141d102c1080943c2d5078080d2213842036026180e440401c40034050241c034000c513002010800c4c0310051850301d840d42002c2d0803c10040245c1c100108102a02100348680b106183d02d95008101c0d100300040000e00030480140700c240201c2c1c40210801c01d1090310011003000900400c1c21728400e44d03d07403505502940050b03445a51a2800030008640d104020a0700c8100e066180e0046040450903190f088602c0c2001d1034147c103002c42e4030a02d4002c0f00300c1c0704512003c0c007019001030001200f6003023404000341c2c0e002c000c959030301b47c00024021550389100440d0320036500040d05a0707051201000050082c031841c8414094511201d80030810040d0104290003242d00409041140d651100401d90700e900c078062008002031600d216108044000204680702800d001d01100181c2d1081d989042c200c0b0049401e03071114900204404040017444c3c5a07034006030403c4c140600090600350702043d5202030103044180300300008683c50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 969821672 1250 969820422 969820427
    0x1608012d0603020319020f060a020a151401063501050d1403030f10090b030d080a092f2b082205121501030b0c040315020a021911010c0201 61
    0x1038015540040554508482a50401141c621707240c0f401ca0181d05c0d0328500024520b8a00c0035541007542035006004503002c3c44c0d455281001444001e00d00d25a990101c1303542501100d40711b507003e00081e450b08103040798141c2000b41d141243c0490303101c64041609019441488007242a41100c400341d0b90b001c4030603824a0400c1c40d218054070180024800441002910320310b602d05207014104900740c4140e441d44450702c446c199960700380344940550203005a01c1c082403051101950103d20400001209691662845014bd0b4107061118250054441e8004505035039062890182d1007264041c1d00c180348110141060700500f805011500000c280000521200a00703c0c0d806006204141e1215070f019407407004c8140f6503008075806452001e17403003601d000c000103246803601140c06204c03007030307a1031039a4140d41c0724030040600b0300c050000c0c04004001902461400441c181d019805a2a180310f014001c1c03420310b882c000408140304407805200031520390805081200020b1030400300d00038607400107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 969822922 1250 969821672 969821681
    0x1a13032a0b18161d01080a032003180f01260405150106170a02040e06120f120702120619050a0209060a1d010809030901050d18051608012d 61
    0x42d030080c000d048040b82460401418a010303102e0070425801c4013580300300200b4aa4409002d498800e038083c900640219000e4855160245101c0c2700e8401320880307080c2c03a10701b10b0304440c8020a40291781e00d0b598042c0d281819002c2c0b9481400c1c078281d462a40040002d04494107003405540d00400c40b4004101440800d02854000d4000442d0300107540d607440800a08030b036000e07158000c0000303851010031880300080c02200d040324424826921030340c071030800b046919540c80c081c80c541c03071184c101010041c040c240802c10292640b0400c081d198000c5005201c10039451508800c0301c1d8006508000701d42f401201a1912002c509000117104d50300d04507041d000784510b15032140d008401051014042d5800072030440c042c01100320160140805d04019202080c0945490403140c0040c000c0c18415481032020f80440f003c00c030ba0110300c007086d6003442c1c4d904044501c401e40701a004213881c2e80c01c10704809642c0004114010003000749000c1008603400c466011580302081c04000f035090803a03010300780c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 969824172 1250 969822922 969822961
    0xd05070c0338220f060c11012702011107090507170c25110319150902010906030f06090f021b030f04140607021f0201150506161a13032a0b 61
    0x4080004d141018000b42011b801f00c1078082042d170030007481c0709900100e4035000f0301d200003400006085c4405940192980e402d080e41604032842020070010385055680100c501810300754580802600c04040080000e034402840e803202c0220800940c0344245030507101025000a1510014055800e40303001d44200c444800c015a0504c901c8007018a00100001d081c00e02ca4820805200c500d9440503281c015205500d0f0041d0100c1c191100c10802c1d240070703030030070141844110b40c0092031946070141d590887e801c0e0900c0202c074943c0810070780024600710719610350f4000003d005504041405010090903c56405005000c40c1014040543c1c0e807101015a01850783c0100501d250150070034809241c60388a008030030040d802c15280c10038016500e240c204c25140b002d8112b5181030888901801d113001200c00881e64000191b905070340241c00c00580038058241d00c03031403c0c1c8212141c1001050302c0c0c1d2520341d2400c1001102aa44010051703500c108245540c01600c44015a0b00c0344118014040300c9603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 969825422 1250 969824172 969824183
    0x50408041706070f020f0606060f041a0d0c050f0d1d011b03060b0a1d0d051203040201030f021206040906020d021b0f0304080d05070c0338220f 63
    0x585400c980540890b080e881000343c1c1d070300c2c1e960300d02e080003040780d9800f203100c034848168001d0004107901e03080100003480d4410310314003628038080c1d4031000e000d0240b41e200d480c00d9440801040007400e10a640c0500c1117100d2803403410742c0c2003903540000315015200d4000d0300d83e802e0759a104a80c4110b002890300c0669040c02e00020442c20b4049007810004007088000440041d1401c00c02043c050310044c00d1f07504480c1300369200e03110011010700f0340c4070400c0b604032402c0d403040d00041540300046c01002040242d40c001c603002c0f5200e0803e4800501500c00c482c02c010001401408400c0c01e503660181c00743d42c041c504650104101c141820072000900c201c44034082da03980001018035004003603a00b155039154225003110440d000107414180c5902071400384440e15005000344100c3c1c14850409804c6103405044039004c110703036907543c401e2148003216003880018562229000c440d03852800c1c0007456103440e40310080750b2030310501c0802510f0280b20442c04c20390301d8640b030005205600d2031061609030b011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 969826672 1250 969825422 969825449
    0xc0415052b2f01020d0e121903051902071406030613050a09150b01080f09030f0a0801051201090c1e0317030f0a02090a0515120f090d02120d05040804 66
    0x300082c542c1c0001284011519494400c40306542e5407001405403004d0710580ea880e85041481d100b0041e50300794a00c0c00058074032500c000d81c40180706000121850b9840303034680c1e070358510700f08461080c90407840b12480b0542d0081201080500c0144520200380107007140c1003552075a54200164200703040b000d0b40001e10385018100030100b4107903400707a10104e000b211901100e55035002d88409980101e511240003075100004203514104042040e81c100b00b05200356800d05c034105000300300702d400400c08040041c038104010482418011038280042070780340f000740009000341d204d0004811051103508494040d0500200104254030101000ba65005c40e80090301200c423030018403150825111042c240c007800c3d0104030320b810329200b101c100d5807000d0580780e001c914203410000c40d0f0001c80c1640d036420381c00300700c80452048050060761044024000c840d14a050840311903142a40001d007142c03c0d503200751070342c224080c8640c050318001c21108034080340030742d61840c00840c1802150300844407040c90 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 969827922 1250 969826672 969826703
    0x1f050f0103120215040c0f0503031e1b030a0509090c0307020d0509010e030109080a020705120601230d060e07150531060201091a01030b0609100f03050c0415052b 71
    0xc104080c03044940d10007241680940711070809d0741324450282c0520007000540c0300b1800b0700350f000d00600b10800c04002025100001440c409041d94000200741c070004200150002013440e2240e0b00355046142c40d510343d415803a01da0b10203981c81c80b26038440410700c6400b098014180c0e200e603040310b442c600043c00a2041100304d14050072250414038001c4013500503550046200d04109240e80d46050710180100340591a000d07180402c9444001540401046010101e25540b02c844018042c00e21900c030004011201880050501001e40c101403400124150072480c0c1690207400d4910070000c00747c0002303241d85101c14019503601c254103070310f030380080300c600000710181c0662100101c140144007075400c000000d00c1c8004404424000200a0b0303204102158207418584049c6070b00060b51035105800ca5119020b0f01000a95a881114168082c03152400315007458084c3d0003a01c1c0076100b01d144524106000168007207105581084907209022000e4909895036118240d00c980040a000703940c0c59 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 969829172 1250 969827922 969827933
    0x90a0e070e180c01021c03060306021803070504020306010c02010305100e190b060702130f0609290604060206010e04050109080a0302030103051501051e030a05030a021f050f010312021504 82
    0x1002c07a4001c10080340e03012070001d0303458082154003800005a018016030b0401c140c40c824542c3e2100030300310806135510408000101c462000b17040000107050710600303c0c2c444404043c50402c040d00f000707014600500c1070080591700840285800d550900740420190b40301d00c05400c6071a40d81d401840380200030018043c250124449e040d408003800b11050000c0351001092100030701c00c000c0003c0d0044840e4000215440721640100340d803988901000c20711940c0c840500054a0403030002200704242900c070a050a142d464076040d130b054042c3d078054102850180040d458800500c00c1c1c0804a4680000a08220083d40900d0250b9403112449403240100c48008000350801d0004540d18400d800d0180d4031b080b14141081d0480b240140500401d50402c04580003c118028046805104901d0b111002503003c0c0060702e040780e1280d00610703c0c0104c1907400b011480200d00714041103489d01e0300703002010219007035181c15a07400452801102c0c851000c08c928210144810040d10071610090104200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 969830422 1250 969829172 969829199
    0x30c0d0f081e0403080c0912010203090106061409040b01050f0a2109050c060c070801020f031e0c22081615182c040803160f020309090a0e07 62
    0x40d03150707501032480d95045202d40d8520010010100030460040000d070001e44241015984042205030107414421810f0216044105903000004170b0794000c001c00c003500009114001c020082c03407900c11131001d401c45c44841e65201e20101d007801242c46010b0180d20341d0003036040390390050004c4031250707441000d0701d401801003240d202005040d035404002d00d05440080e0003162841a001409003e0010691003040420740c40301100420030300800ca400079400d0780070301c05003482803020b01e0b90940d0391034009041c40500101d2248000861850b000344580508543c0545025500c4079a1103a0004003901111108000701e0780710040920070740144c076212480317508002d021110016104041515180000e0300c1c0072503040c00c291580c5100310810400010400c122405091004044407500356400b0b280ea40c6c840b07000c980c1581d1231640001804141039081001d1f0242120314502107940700c5210f40000c2d240d02c40c0d005001d04c102c00481c00306201c25400d600c16130704020740108480b015540d0b20703100300c44803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 969831672 1250 969830422 969830447
    0x26061801080718111b120c0106090e0d02070603020a0e13020a03052a0306061201170c0a3204050702010b011b1e06150303030f0f090c0512030c0d 64
    0x9000e40300d000841000c6802086010b0100f400c15034180b220041502180c44a400e8101170103100c0c100c030b403c086900c2d4000a1406c10598030010a00d40d0821202500f620420600c80d5001d50214405001c80c56010400f0402d40b40c0916000d692000f480720700710350300440c500540e503004540e00a030b0044550141d0051944005681b42400709a50b803640c84000340102a4001210300c003c01d48681402d1440002164849002060b00d810100700e400d01112162090300f05201510501c1a440c61070741080052803840e810454268410a003412071030460204900c1c2c1d601c1c010700c000c030300080100040f42200420801c0250041000f8580303048003d0107882560002d0b4040b46000703803010044869240180c0300142c02c13640040821180000d8002c07030080e44502510855991401c1d054001c058000e800011800780d500425407810900c0d510045074110440d42c1e0300703a86816110400981c58041441c01c0b9101184e03200c4414448600d510b0551260085100f214040e410f1031400e00d541116240450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 969832922 1250 969831672 969831689
    0xf01060809120f030a1404080f0d0f02030117070b131802072103060803072303070c12020a14030a110303090406180e0a0302030711120a050a0b07260618010807 70
    0x8021450180c03004211042da0040c08c0f0400800c00b03811490807220003401340d041204000a900b040e04500070301241c00a80045200031048040c0b560346900820a56000c0c21849200d140f824060220505819100b442111144225012125011301140e410f44003160b03008460b0f407034001041100f20360700140c03c03d8020003091800001042d500c01c000241e40089600c604135a80d1070545241c400c046605102c0594a035120130410302d4009403603001c0c20002000c801c254000440c4a520400c40030700440d80048010803042c07517080c0d08a5400290249140380c0048502c5030b41c1c480200840c2c15031250150340b942240c2014000181d80e03501307400d0120a07560000b81080320000d8110711340e403184524403024005a04c144804008580c3c01d9003010024000185000e10400c065008207003042d010f204250340c15002051141c0503c529840403a6014040d840d11802c0303001c0400c0070071800302040e50300214102c0708034000364658841c1c111580d098080c07820b40c6206503a40c2d440550342c80085002e40d408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 969834172 1250 969832922 969832931
    0xf0613090f0c0e28080d0f050a020d0806130204060e0a08030733050108060f09010c0c06090507170709180b011221020c04060e0f01060809120f030a 65
    0x41c000014454031607916120b80d036140b00b211028081083c0161180c000d030a80380b0f16480d807507503601c1c0c0700c4003600d00401400006d00001e0b0385004001e880701040121f41c0701031083c104800342c84198082204200d03d461410004942e4480801140e00c1d90100100c00d07103003a1000130f0114005800180802c0702c10b50440c0d41c440090b0312a480b032901ca0040c0c240043c0680c0b8084680c0d1840c80ca0070074440070003469109005480c0c0990a1643d0a5800a038000c02d01c6400100a002c0460035421500f0351003240311000b4085020742d83c4008050820300d4801809243c2e5440c011020440148944001040c1d003501c0ea116502d04000170a840c1c0b50f040c41400c101614143d5000b400254040c0200e02a641000015403076a01e00a101e0410461040c000c07074200340425144943c40e0f07015801e010007031801d603004150384107100003444121015500845407806186041004461480c00709a064500030b2402c060a512002102c07458100001c0000c00c1f1060013240f085580c200d850702540c400c4000388420300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 969835422 1250 969834172 969834191
    0x31003151a01050a0e0307120201030b04060e01120201032901090e09030702210111180f10200607051809100306111b010902010806090c07030c020f061309 68
    0x30807030701c4005003090900c0c020254407901d58019406441071440a0a06040c0d500c0602d0000b0700f001c60319000049803806400c0301500750359040c45500721400782a1400c11202d03043c081c01e03000c41230051140c0c1c0c07281e040d205081307070031a44650004442d0401c0250305d070742d240c402190f03403000201d080883c50740050b01014002661404590009002d41035000140d4a0a056602403201041c1c10030804084510342a25400004c502445101110900d040c0301c2038451100264500003624612602c44c0f00f03101c40703500d042e52542c83c60014000c050280c00c00360480100103418119907100702c1c90052403406003100304442c09030048000c103139070850b0030565003130342c0b00d848100408500c0682d18444850400b150600000d049035106078500da080c42200c0b070070000042c940d004611050101d84179140d440b06034120845d6041600c140c1c1020044078080020300d0001c3c0010701501813488003800300400c10f071240c4151b45414030900110301d0301808a0355034001c0c0c1c82c0c600e4503401c0c03d0311496440520308500382 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 969836672 1250 969835422 969835463
    0x507090b0118031a072309151207030b0105040f050402130f09090c090603121d0a080c04060f1206200d0507081f03170918100f03020f0103051902031003 67
    0xc281b0b1003204d00c907010903021008581c11840c3c0110300c0c901e4010059901c01103040000e1005081e030301c240040b18104030710700098000d050714001010039040c42402e20050007844105010401500c40903980184c9420605101c49084807440c2e1210050300003c480202c0c8034103154000416545c05401c0001059a031168054101d401510006d490000351000440e0179520810102d6070f1902045040c0d0411007854000450501d0142c0c40440a50b014840c01001810035000e40002807041c0c00940f080645046400c2541101c40b00005222607a2110100032581c80301180c0c40d10b00c101c00294039107480620600710000c05054812001041c00c2c0b0f40082c40c0140b80e01d00d008824541c0c038000914061665450b40d0400002d003d070b0f2520f9410a100d020f8954861040c01800b10714508007020090400800c1c044d520f03442c1c2d40040d041ca41944034144056180c83c031000640c424286400580c40e51012505081010306146014a0500000a00c01c2c40c010310000c000c2540e0103050100344032102e508a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 969837922 1250 969836672 969836687
    0x6040b06100801030807020103060302120a0203011d070b0c15040f150c0e010c0f140102041e05010215090312040615270504020a090c1d0d0507090b0118031a07 70
    0x180054142d00c014400101164003500b4820f1060502040c4591240c7c0012905003d0003981900c03940245c00940c01e510f024001c40041941c204010740c1c08500c03880c01940c4804990090440d4108009104070000c0710400c0720384044100c4841030501c6080601d008020200c5101040d2070009171110300508200700f0307100740c18010b28562118184081030704015120b00108600c1910041502066000071914044c0c0c01e80c5420129000140d4450810b03541410a00c17403424101d03d03118000005001c10390300007940100c0b5140700b01102c2860740d01c2070070507845c2d0301c2814108041c1544440601c03080002c41e4118002d000728942440200585034020405c080e40345401c0010726603100c1c15410081c0d045640a00d0704180003805109040b900d0758011021b44451071000c07000035007001500911000741034498014104210b4095111024a48516035640e034103000318142c1c1592a100d0041c0c81e0700450007108142903016045103015035038244018005408101000e08113201c4001503001441000d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 969839172 1250 969837922 969837949
    0x11b0201140f0c04091b08010f1208030a060504020a0c0b060609090103060c021e0c0901060c03080a1a15040305010c090b0a142701020d09060212031b040806040b06 72
    0x210344049a032440c858298411010f06014000d00c0d04000c0490050854003900c5480b2113135030740780da002d60b070841c00060040030141e000307840310000b0780e0092100031444603110902c180c00104598a9880e284030400003031805912155005200160041041d03800000c25040280200ba000c41140d4801041c40054480c2c1c15034a0303031112080c401400001c4083d803000b0010005403040301d48000c00140e808000e00004601d1000710b40c0030804c0d8940e0341c944000203602401051500001126195502030326000000e40003000b4551950030310001c0c58100c3d001d00e1000b8000030544009404c070340001c01500d43c000d000c151629420f1100301e8001e903000e4030020b811540c20113020740ca070462002c03003254001030106014013a040104003201c043c04c2d0200141039075400e100420220a46000006454000900d02030000d000d80070208005c801d80206094414240e01c040f007564944c0c540ca400350f10b20312008840e100d01c030008203010030180b000140700303481a0711400c0c03031040c2c0c0c0d105c0d0410003c3c0c190304ea41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 969840422 1250 969839172 969839201
    0x10609051302060d020702040507050c0d0e010807050a11070603090b180307020d1b0b2505060714070f05031e040810180b09101503021011030c010c02011b0201 70
    0x700c41e1001428540010300d0b02440c420001800c108132a030000d8103403081079134070000040000c41da012034080e0901c03c0158075034803418020701e01d0003102c001a040210040c10007040c8840450680300f02c46c0620f0045111000386810781e40300075110314000d40100135603003042d207895a1190026064030900c5500200c4004520001c60030700c2c0c1182e081120100e20901c0480301c1d01c1007001c141e140700c3c01c0350391001c020b070415420803510b4100317141c0305100005040c0c050b4044a039582682201044012a410340c0001c642c0c03414080c10910001d502c031683c410140300604030b050020b80c100a0006c040043d0081101501090300c40350225074605e0740b140a80d004000303264000e0000d80c041030b5882e60084c01000010001c4160345406610b0380110720340c04903800c558079040041d100e140307035025114100302e00e54001124080c990664010419030300c02091504207022600301c140d4600c1100700142d480e8940703000b00900515060442c001d0290400009090300e4030b1028041166007030060041c1c40080c0100b6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 969841672 1250 969840422 969840451
    0x1e03250f050a0b22330c153305090c030a0209010909090f0201120608100506211b01090305030d200a0903110405010e040807020a1d0901060905 63
    0x8081d541c180e118800711000c01303818030212084000341096100040c030f0411059814111003030502089034001250803143c030059218203640303442c3c104211003292900700d5845042c0d2980c10103144010300c41c00701c012407003410301001c0c00043c0340702d04585070a9141d002c6012224aa80e0010f010041d00203454098100ca03007070000034500080e07940600340b42c14052500300704041e510f80e00c0d0300841e0100d000580300108400c0884040d560031000b1140b5807819402c0402203035103000c40352511a83c03003c0c03207400300b00c2d01c41c00400d0f00b5a8a01203c1417a40c074400d011541084506140c032940c43c20b01074645032003d07160303c2008031158043e1142d003003100c0e0032002441c60f09960714000c100505214103004104100c481414070180144005010402160703100e180e40c4a00391309000402c4148140b945100301d0500005011540c1d4030030303200f038000d58801d048544545444c4000350254405412000740503042e80c2e40c09558000741c0b5940d900a0455800030400e5130340740e01c24102500d031b0840f070f40140079814 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 969842922 1250 969841672 969841679
    0xd0f06020702040930080105030718091703010e0106030b0a1e031203020c01050a1b0f0c021804061b080601050d11040e07180807051e03250f050a 64
    0xa03001045142c1c801040092948032503038440e039805e0f412070540e00410001c080740070104000316600e000d04550f00e0412103200c1d850000080e90760120340c00350031054500c40f00180800445030f0410300100c0e0b803151030210001082107050415030024402c034086062040b0000803080e000e4418400b220310041e2420704c0407410540f0006110441e0700c0c241080ca03054600001c0420390100210031002c00f15900075a4601680003140d094440c0a8056120640b401d140200c10240b03400004043c84c5c03850801034111400d0304000d0310259003e440194214043c1d40e2803112440c0e05002c45403185115130020810f911000a58500c06e880059808010038107880202c1c00640c040c0010b80308019031001c001c038409210206555564105601004503007501d1400d114105070040706002203d0313050240720300410724044000b9581c418501c030301d600420910041c0c2000a460116404141401074126845400000c0c07000c503800100c90049440f20601010202e2000003618a01048500c01404008104d08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 969844172 1250 969842922 969842933
    0xf2f0d0e0d0f03020a1203020904060b0c0303070e030f0102040308031b07020a0e190935040e060607020306040b04031b020105030a020c0703051506040507030b240405060708180d0f 79
    0x840003542540718070b100180020310001c000b0304460b5007d540150b02c8044c00740c01d01095880702d8118055402c000e02c0150000c0c107002041d03035031000d01494001c429101ca180401d0800521b030b012070f090348d400040c020080c03201c00b0300154050060544c04880c088100010807a07180200c200003940215410010407112344001613454211801e6520030680e003040030f03e4081200c0504404030b808642164075640122890824180203038140130341c81d44240c481c1085c00182740704030f0040400d501040c40110700c01e44c40706000e41c1c121a5002c0c00b110b840c1d0030142050f104202080b102200008c402d244e80c00c500e00c510205460016906854842c21900c54800c5e00c1e01a41024020402c0c5105581c1c0010101d00c00704209455600c20b86840740603070920000f84415244010a100c0030705051000950f1151188509085903180c2141213520b110220030216002c1c0c459507102d56449031003c9903013400d00801500904818119540700300018910100323006902d222468050700352880280603101050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 969845422 1250 969844172 969844193
    0x7081609030f0b1005060c071502031603110316051b030106050f04020711040c0807021005100501080601090f06051b0a0c0b03041b031208090703050606010f2f0d0e0d 73
    0x110300c800300d01e220756250008198142c00c0141c81401c0380e40000b000f0410000624100444c0071052b1001d1454914112441002c1c1c1c40341c82001002c0002e840c901d07150700481402a551410205612429540c915007043e076529501078601d007048081d0032804032401c1c601407107a003003124406003007076015000c41000c02c0025081a603042c3c0d11410341c090490840e50783c0d4880e2a082c1001a00c6078030b2141041c1b90300a20f8400300d500000e103168a0031050002c040c0e8210b890030200c80007483d01080b19956100122400c04c07082c0c0c4410110780c64400c000ca016904400540003120303801c26900160564146402d582e030305c3c24600580b04000601c2c0034012040700c500210f90050084100031140d6400c45611003c42829a000fa03a5551381904000c0c26254454800e0741c1041c030141c002c108040c1903888040d280d110280c201c5061295202000d88a180600410f04440e2094252505041c1c045035003a0030f0064040450354880c0505000c0c100c09034022800c1a252a0010307140055803022591602d036003a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 969846672 1250 969845422 969845431
    0x6070807120902060d0c140909010b07140607091a04030c050411070506091005091506010e010e040e0304031b120f0809060a09090b040209031b01090e07081609030f0b 73
    0x1a103811070b0303002686807103009021100c10b013100002c40842035180200041100c040c040c508000812480b0000d581300c200c4030b810359145219050707498040e4034200005075002c42c4880400c1c0640c4081050b0190070114440480301032500c22600040041c050900078881c1d4000106a40041142440035082030380c01790030340a2091400a00c0c0825a0b102c1519140d42280c007812180d0001400040510300c0340961504001140020b10f04c90214105c2c1e00e15104004054504103d50340201d001541c1c0305a103d00803102c005003042100e05040c400c007544a51181c00262007a1051001e5150003161400500c000c450302d000912407110080d60703c41280ca100907401f0749507201c044c0054101075640b04018661900d081d210b102c1002d1404c0f440000f43d8050809040c030035403050100c0700d80c039180480e01c1c2d4410b40202c5105e040070700c5008016150503410782c0140c920b010030300d0100000d068114803498000e030740b000d6041064034041242115505218040102000103c00156000510410002c0d810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 969847922 1250 969846672 969846707
    0x50109080c0d141f2909040f0c120c030b180a03080a1401080d2d0e040905010905030d14070905060a0306170703110a0e0112140d05190206070807 64
    0x43d040201441c0d4916071914400031001590744405488250075007171611440e405501640340038105200004540c0f01d0000c1003d41010004146030080004244101007c1d120f04400b910790144141418030001d90301740021280108103201245102c200380c41d84c0040d5880070301c002c2408808968080b1292040030340900f854984403000079800d00c086140d558003a2080c40d004000d240f2800000070100364521241c440102134901085410402107101042d0010076400d000c84540b07052004500100050003000d41254a0b00d42d429041040100c000c0090019120050110f030110b1a12491440f00c1a20320f1004140d05590400c0503080c6200500784503800c40c2800202d00c5e0356078501c800a00300c0d1218010068018100030304c01c201c025605017401460503964004c515060944c07540c02008103000d40039920301180d0079002000f0009100c0c070088404042550024160307020041c040381c10140600130070880041d4100002d46c40054094407403040c80d80d4030080d9444841c01a0341240c000c0405112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 969849172 1250 969847922 969847933
    0xa0903030e0d02091315020324091603020c0c03030c070f0e010609090902040f0603080309012d020f070c0906140103020a0804060c091d01080c150f13050d0c050109080c0d14 76
    0x341c3c2071b070500c00340d8803e02c085108090048013071b400c00e0000b01c440f0f04a50348205111010301c01102c4854400580c100008c1c2001640c0b12024000103140c00c1d54081e10380c3e490b11000407051803070040405c0c10002c40b0703812011100140d4030340c8100c0d861b0300c10074011840011707007004003001044425040400e031030b8000b400002d04035170604800e1054508640094a0140d00041400300c0c0010034490114540503001070303900d0507441c0c0d0b0858480452425014141a6004181c0b0300e01962154200c070304032a80001650462030b6a038a4010150001c0d00c601ca0b12094030080c01a400d50082c000c46607051079a61369001c060b900d654a50004107564000e02040055050010a88914082c8001c110358440d440a40e00d42d0301d4881e41903e04000c18880c680240b503d200e080004410311025542e0218000d0003030b5072141007002030001c0452241d4000c0394420104200482403004010510041d50400e03a184105030b511541400d80e81c1c1c24507040a9000f0f0064100309010650400359240d0482540041d900c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 969850422 1250 969849172 969849203
    0x2402030d020a091d19090b150604170607170603061308040b0d020c370503191d01080c040b090303040b0a120b0a060c14070b0a0903030e0d020913 64
    0x1a60801900985038200e00c01c40103014450000c06400c0d84017080030f100a004030680c0d0740d00c01c54603050251a050003142e110100b0110382d590761054502402590032241610505402c1c101d035101401d0312148049200407000c03065802520103298881c0101900500081d22042ea000c40c181da44038100386d41d8690207110110b00c00c84594010041c22000c000051b8903000c2c0c0300001c40c00c2421444081e81454200307141214041384000218800c005000039001190110b404c20fa810b602c2014021307003034404ca00100c4030005030072510a444c116a42129504c12003515801907a98a4060b51f456001c200c080c48100400740e0f45000912020030b020301540d062554507544140d0715001228a0f1011400308130129a01c0c00140c402c11508100480310a180a4035210025001a025007800f070840c44060548090a42080000800400100800d90350703880d00f400f8020052a4280812070004180d80314488603441c22030601c00d401070f00101404040d03203d05910528180c07415200b26164201c800088 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 969851672 1250 969850422 969850439
    0xe040f05090129030a020105030702030c071706160203160305070c0608091006050609010c0311060a1b0302030121020315010803090a05060a0c06180501020c072402030d020a09 77
    0x45000714284000881c46141202c1c02c045610300103040c448640010310b0700c20f00d042c1d60018043c2201034080c07d0a41d0342e621554802c0f41540f10704500e2010f50302c035482e00041d81769203002c00b010560400c4400d4680645840c803440b09544250b140d0b00005a000340700000e2000300300d10003400310340d01c40d00b4002d19052003507640030540b1354194451004a01c2c65000c00c4031206041c40b86000f4044504010800242450002901806849855410810010302ca80b08260007a8460301178001210b084444c030303107061150000580520070309054042082c58028001900900959040c2c85640325400c4d0400540323020718403c1c907036030740d410ba901d881111413158040000750799050281a0000182d5610a6448140300420900e41d0095001e50010000340410b158000c0b038065819a0000707000c0707031600d03000c031124030380f255074a802802e117520000d0007030040307080014420100d0300d1302d00000c101a8014818a466840d98507000b0015800c1007014402c0500150700030051040c41e03083c1490540c0e00c40002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 969852922 1250 969851672 969851681
    0x1703090a151715041808030c0d02040b12070e0102010b01051207030b060c070608071b060c0509040c181a1e070609050d0201052a07081b070e0c0a09060e040f 69
    0x12540544401d4100703070903040c1070180f840b81054805d00013065144556410701d0034440105900b140c000081400304001085404450040c9000d509141e282c0e001c03e0112120002c1c20f40300c240209640e4200b40f1038550041c0070b035190b00e43d0142c41e41030601550051341d000c85030300180b01d50209540d4100301c55481d40c8002c094081f06041c00000c200e824140900a04046800b401c0c601c18031203c45a080114080c298080d00c0d903540c8580e020031a0002d04406990900540b40079a40c400c0c20815124802130b84030f070300d00710b0380e4598400101d0542c0e0f903010040c0c90340c080c0d0805100c00709001c01c00d40801e501290500900490941c2c030551520300c00d0b440313201c203d0356503210031201c0d5000b812107451080e40c24021150000034090012a905030901d00c48000030804510000e2590004070761a018844100161201c240500c1104900e001c0710800d029140d10590040b0510007401401280900401c0c1c41540c107002405d4481c4000300c0d0a000b025100b090900000302c2d449600c42c402c070055001203014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 969854172 1250 969852922 969852931
    0xf130806091c032c0709050106050903150c0a1b29070906020d0f02100f0606020d030207080301090504050c030d050d0e031c090f0f03091703090a1517 66
    0x10303124210125111103030b0310b40e9201c80c0c082018240004049080314950341d1aa100d8010340c040480c000b1040e540b1800e003d090b50080082c00d181200000b03035190040002c010110b422800d44006480e02e4500445c01ca0050700d020804031020301007032a582d80684070203141d56072588001003190340c041d5601a002d1001001c007141c1484c10781c8204028080459050303070004480c0c24154070540c03c21a00946e6108000c0707075402000100898a40c0d024000d000740300c2240111107003844140c0300c500e50140500201d02c030341d80c014440c1301c012458840c070034426a8800c2c4e40c004015407441c0d00e0003114002418028106840d64000c0d4042a003407a5410452880c1c1e02031184c80306500c03001d1030000b1008136400420500b9281d00b040140031400000551803000c511a01100082c0c912003c4c240801c00441c1c4507401007850403580740c45000d054100c42d8080c1154200c15400e024210308548283c2c81e80102090590071004400040c08200b1100c210001103030090b24001041010003107100442210a44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 969855422 1250 969854172 969854191
    0x17040b011707360905060a0f1409332a0c060106180501080a0510050303130f05060f160303150e190608030307081b070503030a0b0f060f130806 63
    0x7100c0c0c0803d0103202c06030380c01c50100302c40100800c02040c2c840701c0d11244024244c18285030303184001603846016900501c8807980180c0b074034450b4a0304c0307100955500c13a07015078941d410300c10154020902c00c03514050b144e00b4030320072120843d98440390b510701c03005054001003440900120000c10b9580e0b407020013524811488000400f40b65141c4500a000312500c04015101c4420014040c849644c018a03021340101854100041c2c41d40c450004404030780e16a04000c0d80b60100050340c41e802c0c040640c0420a65201030b980481c02983e84080142034031a05003281da0754a000d11031001e401c200600030b801c8050207410040740306205c04082d54520245500034840c00701c0a04248183c2c1c0c00e021016448001c20002c0800520b400c01d40481d40c2c81c04010b12050801c110400001c9560142d0300ca8801c6076800307900c41c00e03100c03403003881c00b01d0b00c0b80c000301d42c0045010300d840481c0c4064078203042c00418001c4080c05051410015800540c0c45178444001d00c0501c0c1c901c014000742d030050070003481c2c0c81141c0c080d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 969856672 1250 969855422 969855479
    0xc0a0b13060c030203010b070803131a150105090d06050910110409110a05070f05120a05271e010e09010b0a1b02100503060103200a17040b011707 64
    0x1d1502108a03074102c036038001018410300c010300c40c0c012010203ca10440c0c0140046842c0d83d1504100c00f041c0d0b11662008040440c150340084c070402c0102c84886c06608400c1192001440140046403240031b60042d80b5400310901c81000d02040070b682c03205411250500940d8040c10340140d08005480c004c00da00c00710036a0008080144000601c1500c80028441161a140c90718424004046004a0314050400b01c844001c1030100312003080152462040d150b4842e4403602d03c0e59002d0300c00d8204040280000d0003904001c282c40301c0481000013001002814007034500900e40341d41d0200728072008010b040c00318000030410036036610500c5500901154106035030320300c0c00d120300411552900d9000c00184550440700401070b074501441c1c0c40a18442e02c2c041e070700d1703540d801c00480190940c00c0380404030700c6119000000e505005c10043c1401440d40c3c8a808003260460061104000b0441e00548000d50000040c407440003942c2c01c0301c068226010071524002e441e03042640b2075984079110041c0d82c0e24103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 969857922 1250 969856672 969856711
    0x1b05030901030f0501030f1101050705060a0614010825050c030c06011401050f120411060c0615120613030908030d020a03111204020409031101180b01090e120c0a0b 72
    0x14040e107888050200401d10031395146540f020b150100c0454020b2149030351082807200399214000303440c001038102081320b5840c01c021380384070b0080100d03004401460a8810102c61030703501421980d4000c4061452000041c46504c2401900c952034104840400c00200900076404800b01b005d030084405400141105524051803082002c113511401c07070600c20140810f454141c1810155080e00c20341004407401ca0351146012542640e8146446600000109101c00c80030000250036102e00310600400f041d0031100d00412000319400b140304001039000c0000180342c01c0541d610000002c0c0301c0e081405800d43c031610132500b542c1200b50311044040d80810074000090b40742c000c503614045d02400d05450b0640e100711001c040c0100a001a00580c4c48414610806100d208451509500c00e802080401181e901491704624482c1741500c1c032034200c2c0300200d070000742c922400400d208281d0080c184009004810251038109400ca00304034001c8000d40d20100d000400c0c450711030920380c01c80400300080c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 969859172 1250 969857922 969857927
    0x20609010b010906050a080c040f0e060f040516110a08041503050c090d1e0c27050601080f0709030b07031b14090f0409061a01020f0105060607121b05030901 69
    0x58181d1000c0c10812040740401441c3c0d003017000c03915441c50b586072406260341e8040c0e542c00c4c90701c240da10044d180d9095040000e810007072a4100d07802002c040343c92150700c030541c1c1c040006555040e82c48210980600941d5071480d80506000b41e901003481017a01c03000309141e00c4545580c4c11607071050036050049242d14441c5541031003400c3e400340400d24200e042114a10108043c0b47e4661340003400240040c0841494040503030811600e203901ca804070003425182c104085100360400d850b00400c00e907a0013001107c9601c0c1c0034151054006944004065680d81d1211003001c40c00740030b40f003c0c00a4841d0100c0820032074066544100c00d1610f01180509004400341d0140710360b41501d500b042210046400e410112008030340c41c1407022585c406490000200240041011800c020301203450181d401c1200030080c07504a860100c07d030280e407119001c080202d1f0a8610440d2303d40d0780700304204140300004061080c00d001c81d114500c0d291040322456001c100c0c10f121480c40030b4a07198804200b440783d13980d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 969860422 1250 969859172 969859181
    0x303060e0112050a0b06040b0a060908150f13020d080a0c1703040b0c090411030a0f1107050705010c0602160b01030506012304020906071e05190201080a0c03150602060901 75
    0x2e40418030401070b0302c031070700d90548a0750303092002001d1461040c04078003142d8940e0004089458000c200c41a160341d501c1003c3d0010040b40304501c5c1c03038081c3c4d031000d100b00396207104101c5c0304000444c407030640c50380c4501d80407030000c0306008102d034003075103210084001c28400800b901c0d800d0aa501e8440042c20309040031501ca2140c0c4500c6c010f0792008204120014410080440e0070104c0e2002843e140c015040000d405009080201040104040f00f080803a800713940108070140403c003010820004402012600c603ca4148050200d82c0001c1041104d135115810590741e00b0b0040300010700380038026010fa06000c0705200c003590754501c60401841403002c2405640c1c0140520030b04810040814100b07104070b41c40705a1058441c6a010070710420f00e0300c0c5c403c201c48605520800c0700701078207034000d4040466580d21105440034030034960a0441c100a0180c200042a016140c403600c03a034550710500060003100303180c20704050700d58075121210007d1020403406081c4c643c024210500d0920740d91400c64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 969861672 1250 969860422 969860429
    0x50f04090b0a0204180e0a23010e1c0203120118020d02030109020325140f040b0a09080c0102011808030912031e0a060509010513060803030c1207140405101b0303060e01 74
    0x106c1c540b085541401400040e000221a0f11054440185010501c00741d4240c1c020484041e065081004001d940c1401040f600425405100c3d1003043c480c0f0010102c3c3d585c0216007941369002180b07001404442c3c5003ca100300d5800a4440c050b1400182d16419416a0000e0744000c0010b40c0200c00d00680709490b1024041c051410100815444c521400c000c24000302c80022400c850f0000501c80a0251030341d0496024000380000c3c103036200b182e10b90040080540e84200c0d9014000d9031008a107540c4180200401c0d14150044024080010344032400749510107040a0314601c107030603081e180c504940000c0c42c03080003500041102015410051a94400d009029104107490107074103002d6691801ca2040c1501c0741519004100b40c4420a0f0030020311050304889079901c00482003141514400e00103240d100c2486040130400d881d00001500e05044040d100481040280f0051000b4140403200c0002081285801c052424440240b000283e120700340541c0043e44400050003c04004080c0c540103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 969862922 1250 969861672 969861719
    0x102303030f0c2a040908090a06020d0f020604110405060d0204060303200102070506010e0408040f0e010611150411010c0602040b0c0c0108013002120109061b09050f04090b0a0204 78
    0xc8048152529503500d8524000f00d21030381d55004a802440b644c02c056808080b005010b5403103036030711240041d644110702d41c003400004501c0c0c0701c409040d40c808a041d074001c9502c1014003c0318000101000b01514004080c950071a03c0841c80d61b02580d43c2d805030130000e50003921f5804071113545e4407443d02014403050444075030340e004101500c00210009642c0d411204408401f40d19500d5a00e040219441264480355090b0b0704a10301058615a4101c0d081c102c0e1401d44a0b009a14140f200c001d8486010340c5c0280d036440c14250005010503103140d0340e802503034014500202483d000da030b19441260440d070007842d07801d500800e407480513000030031005948020908000340e0b19890810000301e03080b4030040e0800014030805180102c0c0040d10525408294002c2003a02c0d641085c14019000704020341003981c009003400e1043c00c5014941d403805200d101240d449207445801e02c0d090042100d18414a9174115a0386c0c4503140c040f81100214601501d101c541c0580c4c0c40c3c0c580424501d15519150440b440e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 969864172 1250 969862922 969862963
    0x8010902090330070501050609101215060b0a020c0f090f070c06090c060e041a030a030513091b0305011e0e070905090705070b0f102303030f0c 63
    0x2110b80e8005070015522055078400c08603181c0b445180444020010110b100490011404208100043d0801c80c414102a2940040d503540e1800340c01076010343d8803505601ca03040168100c08540c2aa0402035050101100407510a9031403403001050f80c0072204050060700f10b143c0005143c03811a004034600e00b002ca500046604080c0c10050a401018120320140301e808280f50003008440d4001081d15a040309000d4406541c940001e004458001d113507a10a80c40c000c4171004075180b00400e03a03c150000b8005018403a108ea40c241c1c1c071a17014143c800400e52001a00044882d00c0d030140142d04515210120300c03140b800d04014090b94010380000e212030008512a504600c400135582084a00348402441c6c613803503806040d1202c5110340c220541000e10b842c1080901c43c0c201000b401d00e1031184034035000e666105140300822043c1995040c07068020f20108104c0c2e0403101c540504501501328940c5440364041d000645190b2240e640c150180318003082d100c02c0d2110a001c04018400286540d20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 969865422 1250 969864172 969864187
    0xf1605090a0c0e13090f080406030513050705060a1101050108160801050108190201030e011514061c0e1c02070e06040519020d090215040510020307050d031d06070f08010902 76
    0x100503d0041c901c0a0003010742508490710490350b07030080078041c0e400c4071544200440354104080144d20a0280901180c10302c804107048600b18030420b001e098010000c5c00c606420f05040043e1980480c141004001c11040070b034030b1245081c4203950003403804034020028210900700c0c5d0180421641d00515041e4544001009556408513296030340702e0080222400725840d40c4016001001d01d40b076440d90a40c600306000d101411041c01d61410b45045400c41d005c0525440108801031284010084058020b1b800b16451001140c00031100f107145581628141800040340541c2420b0301150040182c2c0011020003444222040c07850300240306803005c2c0b08500e4220860900f1611205060710301d2580011182c02d5004580d0104100f650300801c0302403a254030300000e031556009402000c2c85a1100840701c008240008200d82c841640300d0090560340d0b144400c20b90050503440010400f600c620000541e0301391081c800c1030311a200684845004a207440d00c000c151503c141c001c804042e204101d401c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 969866672 1250 969865422 969865427
    0x100c020c0a032001050c0607020601090e010207080913060b0f130e04081912062d06140306030a0602030421090602120912071d0a06050612090f1605090a0c 68
    0x30705050100403840e01c0307403c1d030600100c8141c0714000240c0800e001d60002d0052455011548504a60040b482800441c140c43c4141e401c0380b1580d0710042101c0f00420140c0f00c0b03410004203582080c0c4410b64001102603a0309505d02c1c0c140e0107a2818045440d0004104800941c04400170f0080c062130f03807002e0410b10300b5a807054524421542e0030680c10a200c04811407040c42008000c5056510920074094135607242c000b010310400b011902d400c1c036802c4050400c01000703c1d641c40f0089500e580c0d14004052600e80d100c43c103a500c060310154042c01a904c0940102c3c0841c00103601403403180e00350b0f450600f00590200c42c40c8004219a01c2040400601000020b0340002d00c81c8078808000c02d6680d90b010304500040c0c0000b07e0030015000d42c022803100081c02e20201c0008000f01020700c030740034055500d08803072008a504070702406512030012700c1180e0307043c910f40751419400164001101e4400e110141802c2c41c027075403924410760410083c1414802c2781441c058242d04606803040a00c0000c8480a01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 969867922 1250 969866672 969866693
    0x307080108070b07080721180812160c09150e0702011109040b0a05152d19020307020d0605060f0303130303030b1302070c05212d100c020c0a03 63
    0x640a00d8000c20f189052019013170f206034047c000c1c81407420030909020350280040d046040400d0107000c04210000c1c00701400f169021840c50120740702442c00c62842c0c810300e84424035020540300000e601c4008184d003280f038810124500514443c11989620f0070f03190351090f280080000c0116414192040005004001a503070000c0e000c49002c105c160140b0301042040041e40d00407640f014a5032200c644c0c0200560013803615030422181ca01c9802c1d8030040700b0000c901c81d800300d80744c2168108450100d00288024244642800f881601d14000003a00000c500c0c84442c4401e407681c6580f00300f400941e142c210b03600320b41040142c02031418040b07010704200d401915032202905264481c420b10303804c1c5d82c1c0c640e211508406069011501c812190a0a030343c21415030091074040d40c100360704210011b11403140420705040a90084c01001c80310100ba40450402242c03d5880ca001c210300e510390440240100d40301040390440000351801c030140e00038988002d05540758003030684e0b0300080c07010035101c402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 969869172 1250 969867922 969867937
    0xa0209010501140f370210021e0c151003020d1b081e010c09180c050d02120613050f0c070f02040c211b031e0608030307080108070b 58
    0x2e00070241407101c0d00050310b911900302e008241d02c07000210000118281e50044070100030381030b1110105c8010700505983c0e20f144485001c05a8040c401003610603030141c0061191071110b002da070140e981070146d000802d40094040030348a070413204c090380300032031aa0394003580094000768003610689950003041c8400800320000d0103091480305c0080c8a0302c0080b076454010000300045a11204004003441901001c603c0124019401e120a0b881c503944a8070346c1405484908442403ca1841d0700110001040da07800f950060010910541c510b180c060300c06000344009602150100f40303000020000640b4004a405208510340402e202c02c0000d554000c55202c01d540c0c2c42e2641d1010682000908080c202038029803007820080311224581e400b45d034890010840150940f1603e0000d80460240c0c2ca504501ea141c48540b1041840400e1082c0c0100c100180740003e04040410b52941070300136a000ca4124204582c000014491a20380c4415001c0c0180030213005040114240b00702c01c0307a00e20400d036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 969870422 1250 969869172 969869177
    0xb07080a0c09030611040b120103051b1003020a02011d10320403050d020d0902031005090613030908012a02030403020a030215120103060c0f05070c0b0307050c0d180501020a0209010501 81
    0x3699400b85c109104840260207070900c078079290b141d10041c81400c0031013400700700c8007401010155628091021001c02003010010804100030804c914120000c2d0001d00700b40b82150b4076216000680800201001010034581c0d02404810104440b898240e039820150a0200702c0d68210702c1d0607101507109000c000300180030741c4031440e407505d0404490314058075000b9508140f00140a2000445030307881400d64500c20740545482c0441c0c5401681220800c4981e0002034201d03400048072407040000c040d410903c682403040403e07441d000b00034212454580034640650080e619103c000384c1d04c50800b0849003040c0700640ca40390465000c214803000c24880203000700041c4411002d200c0c1710900f40c82188048c19000207581d070356800c6c6007001c0c00040705e5100109200e45203102078980724608580610341c1040d400e000c140c0ca031124614143c3e0009218400b005024440101900c1040c04500394007500745d55034040c05144080314480c1105a0391205044d980f05164400040e12400e040c241116000d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 969871672 1250 969870422 969870431
    0x9030c0d050607080c1c0c0305090c090604152114070815220510060506130e090a21120507021504020609060418230a05071701030b07080a0c090306 65
    0x2c01c20141a801801c4070341c0500401b8000e540c110242d030f9800303401e4402c80c66a046c003180d1154001d803911440005040f580010142000900e40c1c01e21b5000f07016604c020040c0c0c2d5503160703501c8507036440c9000e4100e0740d4a001e000440584081c001d0a0307c40d5074409064402070107602e4640760b2010b50314070b01c030181c81c085000c46000043c08241107814040b04207651160890448000d458455100c4010f41d480c0c051441c5040d0010030385043c080190381c0d001c0c40e5241d040107002e09141311000f41040041210302c1318071442146100242e440d040350f100205039010000312015240d00050700c400300c80d900380c003041868001009545030340080d90054065480d07090014984850001c03511903c500a10207801141c0058002100b84180c0607055140c0c1d11228104a1100d003001400c0b849080c116090084a06070303400f003290300000f0b074407160300a443c07410182d41036030341004c1001401e0826401076490708015820001401e822000e6154410301c4403404201002c0440d6018000304800d000240c08036585 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 969872922 1250 969871672 969871681
    0x50901120e0109140a0c061404210807050a150203040b04061817041701020a09060810030f0b07120c08131505090a1a061003020d0212090309030c0d05060708 69
    0x80d8404042c85802210018004c11070030031660740c070b07500c80c2c1084541961148000031900d1081c2285400351044115180c80c0c1441d00c3c242d13006440d005100c960045401800c0c010006204a0041c6205c0d8800d0700903107140d919906041103825215800817944034010010000010301c00c1a501e50f105a22a900042023109a078859404405207036005004054000d00100581030001c06070044864009201c01040c9005011509078043c400c43c68000c100d04200030700c909e50090030900c1c0d104d40c405002d403d05683d80c0d155820341d1265030034107807401c000c04400d011b41e4640c048422804119440c1e4144450342c6900750042c04404000e205081008090680070204100b00448102010039940c05000908140030342e00d807600b41034401100c6412240448190042c3c940b1001d9114000060100d1990003803018250081c0d881190002ca02c1c0750b0800500750010425180e80c0d010b0643c850045482d02c40e031805051405e0b0b00920760320711882c40d0281000002e10000380f116440340c0545000c10f5a5103d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 969874172 1250 969872922 969872951
    0xc0f21070f020d050a150204050a06090b1209190606060f0507050c0f12060a050609101409061507031d03010908030604090206090d0b0406150509060d170a0804050c0105090112 77
    0x84c03410003c102d500f06c0a207a41c0400070a401810644104664014980b950740b581a036523503007148161508414180300181c042c0d0300200181d9031000110080c0d82d001d61102c03415540480740804d003250345596035030b000d00ca0240c0c02884814002d01604104d440c0c12400e46a84c0d6a070f8180401c5036100c4c0c0860300504000d619a44401f40d051140b810480314103003032648140c0d010300030445805002d21504000910100110380b41d48045072103000c0b0039800200e0043c14001d01482c01040707207401c0300302805c415062040c00001000d003a4020347c1d81020100c4403210b620070340c0a103030071245c0c0300741c0c18030080c000170800340e404036074022303400322400101c00442c1d00c0856403600070700300384a60002034410070b80c040c405041e08282c841c52050800300644c4041403a22848040c85010b065081a60400040c1130f5042602c04402d0035406501c0c4c1c0350010341405a01c51140c4e001e41050000528840c003480204002000721400040007401c0445c1003164540009049800307498000e00101d442e04030304a507490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 969875422 1250 969874172 969874183
    0x240306090e0606090601020d081807180218040c090501051305031501031101020d20070b0a0f02070503063c040f0330110c0f21070f020d05 61
    0x401403a0a101d021401d00c0410785800044a41c01d00600d45480010340b1588003248003a05801c1544078080640c90301d41d01e400d65481c90002501c0c280c0f06003135012803101d0700304419900c41858100056694511200706110700c450446174240681e0600c560f42d210903411041c0c03801655020b2900903121107400d0514110765405078840c3d601402a0000d500e50540030403092810382e0b0190b10801601c5074848c00481c4c0d2000c86092844c001040241003070a02c00c80042040600c4640d4012a040c1c1074031103103044115804070404070301040002c0b44191440d82c0500202c002054100c02a1509107426668616030302c10801d443c00300300c1daa820503a45c1500c40e4074004010031010340f1a1a64526180c5006148841c42603000e5021402d00202209240d0404100c400340c1200b4480d400742c65a103513518000589185c003c0429402028000580c24483c00c0100445550052009003841c0a51000c441d4220304420100300c10003070f0800503074010540c41c08441d03607030640c1925213038008074031801c3c148d0030007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 969876672 1250 969875422 969875429
    0x1120e0109211b0807240f0e0c190603150317030a050105091e0910050c09040e06011202010f0e21010b01032007020103060e01080307051006240306 65
    0x9400c140803030414040100d008280c000c100e03445a42d00c00c0c90980c3c43c6072001d4082c400082203c501045000002032480e88600c51292039920210100d29803038000740d0070707501d21180700c01c3c2c500d580f522003d0400d0700c100110fa00c014402e80d40c1e02c644000b502941d000300c1303020f40182814952500010042c00400a44201c02103800540b800000c0d680c44290f41410f900a98804c030105041000115041c07401503141d50090880c0d0540640d848030090446110150081100c0510f02900040030240c21540c0126485075014040b1180d54040705400c00048446d040b120203c01d80c8041c00501201d911800c1d011109902400c0a040c19880008202c070303007828199a486d00b00b440c44035500314400c040050b402c119201c0c00b00138891140322000440450340101c081c040b540350f0f0119152800c070b1010004041840c01072401080640d1140b400c840550020703070080280360b0000500b0800e215003030085070030280005005000c082d20740706094020001d40502d0140203210b540c8503000150290f40108000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 969877922 1250 969876672 969876683
    0x60a1502060105090105040c0e190906090f0c091a0d060906080105041110020a060b040b04050f0f09060106080a020309100e0d0e09010608010b0711030604060e16030201120e0109 78
    0x80055020000e445140a20500b40522a00400414145040c1c0103109500da581d0740c0d80c1c11107003203c400b00601c4030801402200c101034500d00c081000003003400354034087e054100d000704e12000010f2092040740c1508175507504002c40c141083c400c81d21601103c0320500301d0000700507101c8401e40413030380041089504c40c140844c41e014002620400641005128a00410344030140303e8048017032100c440021540c2100681203006107000080d10b0754048210200d003e80700041440448022400729101038500a40842182c001c101c1804903210150303500004100250200d03502d0600301909000d00a002c0f01c1615401200090400000304100307900110905c1003408800508801c0c6502c51551000850004041c4040081141808a0014125110307a590744a40d0784c80d100310500b02c2d4001c1c0e40220f4031540da81c0c001082e555010068580124050040040c006022403c028509480216020b440031203002082000d0303038200c60910800f290050000c1000600405000d00404d28003000800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 969879172 1250 969877922 969877949
    0x21605061806062b030e030c0109030c06050703050c03070c030b01080a0302030f1803013215010c140d050d0e1b100c05100203040c0503031603050d0902120a03030c1412060a 76
    0x501d80c0c0040001b6040710198151102c4161600044422803440d0201401d15042030f001000400d109070003d0032154000d00d0030904150a8410090850380004030595080344510310610a00103003802c101d004000c144000d010215807640c020303441e4082c034121005071a001080c0d20015041380403404006441c000c2c02048032010441e500d04d048031400c0c9a9803021082e4440c100d820220345e04000b80038904003100503a119102c0d1004440c1e5140860085030b84804030485900504402c1190340001c000030307112a5154010075001d5411140050041301c0198071024840c20822500c04810800d11415201030740f00d89000081604c4090b0f4103100108548988554450f0380c802075400b07940194400c0810b00070003503580040564902500c00a140c6e5401d2030005c25001902803002050341c62604072003c24070030842d80000301d1245004076070101d0b45c0c109116030800c160303151080c80d48800441c2026140710a010603404070798040c1041c00445182d010b000300c0e06656900400e1402440012140344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 969880422 1250 969879172 969879259
    0x903040f09270b0708090304050a050d29010503010f0c230f0f0310050411031f0905040305070506070525140105041a01080607050f090a03050102160506180606 70
    0x40b03103848215544130010b024180826410000031044408803000180501502424001000440c21000e10210345641c1980c00f071a800c040120440a4820082c6401d1101507240000741800c0d11a003801001e03401e8030704040b4220342074018103807001d420341c3c11091070f843c113050a45404480c440c2250800601c800418040564030b0404001c0d032058441040d004022951801070006440c0000459180d8042c01e100041000c40b00c00012480c0d00422074107a85e1340ca13a83e131817040480300f042c1d4082c0c000440020780c81050200411441350030032810b19045107004a14014a10640380b46000201c0d5580a01120810710910250384141c4020100007000542003620302100e00f0b0129041080c104661900000f039030f8003010410318400d40d007613150030b0711f00200095440c1e019800544003a40c89500d1181c0070010904c04d101030310010000e1800469600010b040480c41d100005243c016000e0040050884082c03003c256180c0001003914411040b52203035400420141c0d104009030710300140e280500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 969881672 1250 969880422 969880433
    0x200a12050118200a050c161202030d0807050a030e030c0709090c060f0c060b180108010507020106140a211a01030218060109151808030a080903040f0927 67
    0x542c08040881082050448049101d03164040d1248800c0c0640024000e020303d541c014002008552100c00a882c51001032000e000380c044042d400c610b030051100c00080007141801c10030000c84c038070142000d640c1c030300d80030030010007612441c03c100081544035a07462000d8801007050b50a980d005405507201541c8450f008030040a078050140c0d026550300b040014110300541c0a4145500301d6512882000165242e400241008a483c04d400c62104403550100e2158904902c0c040c2251071300200e00c5042251009095850b2038210654400c0d40b2034404459a0310f4001c4502243e002c0d414282818200285d61405001c0c1c44801401d100400419000108018100c45041c0c03442211007440390940c0000704640c40c40100c0c0d260380810202d1900f031010142548010642c101c1a1800c130803000c00704048140d04941a6002401c00e902c0803460f07644298019500a0340074808000841c100307442d0903021400d0420301d02c40e081610307a0300c1324081c10500526242130078030320041401d05220812880c06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 969882922 1250 969881672 969881699
    0x702150a03450b150604090e010f1d0619022704050f0f0420030f0105180303040c0b091f021f06080a0308060303070b090a031101200a120501 62
    0x80c2940807007558000654280100c140e52455a040f072600901642c0d004469003c0e5080384581c2d0307030b01c040c3c1400300140f0701c00d450207800040e10703a480011880503008a9000251960000c98140c1910010292965840c0001d04181c0c8074016080100240c010290884020b2284990282a80744070710b01c805000c0385103485880c540542510b00308159698464a4056000203403056554500181e0104020030810340f000c005041242640580070301480002070318200782140c0b0946036035112804c016071049003504c0c102687c0d40f9000514614070b069900d07941101c0d078500520034241800708020589403921030307008480080311181d01040170413052010f503440c01c083c0500e00b003242d120209903000d101d550180908548841000304082000c03580c0a45044100514954240c4030a00c480e2000c50b5000c8004c90040064602816a52a1500300100302d0081401025816070500340c10b14202d440e0000d0019680c0280c219861703d841020f0022110070740104003c0c804d20f400e210000c100d580c194100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 969884172 1250 969882922 969883001
    0x10b0901170a0228090b0f0a0315050a0f09050901050108030702060d110403030519020c030309060a140f0306010206091b04090320071e08060f130b010e0a050c0702150a03 75
    0x5c50b68203007540c42d0300c1e045480c8910f0b1810303010000244400d200701c40c0a40c108800c1c003040c811082c0c0e041500d0f0000f0a446110710303404071f07014401c0014200110b101c21b214961b00072007220028401503042410041d80c80c414048001d008140000d132062585070180c0c0f002d10407a64000003941d9071541ca06000741960030040101203031560000000000c1c500028803801444405405142011981d0040080c10380001020509002c0d21141240304003510ba802400104e04440c0555203909080300028608600244480c3c0180c1c00601003030412268104040c030160300881d00814031a041c0c2c6404c40c1c407981070300d085084103c041802c40e410064013003a041305950104032075411951480e05142c0c0000154805d81c1c0c01e0f0317084400450f008500d242c0e0756540c030241c0501c5a00c080c0d100d40d910301030308080982c007078011103003032006008040c8010301460b074102c00501c119600742016600050b05200e030000c507a2380108000170344940458065040b01281044034850313002c14806482038840710102400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 969885422 1250 969884172 969884177
    0x30309150408060f31150b0d1b0609120b04020a0503030a0f1112040b090d02060a0504090c05030105100320071a100305070e0705090d0614010b0901170a0228 69
    0x6002414201c003000b0b54107031705a0009006034250201e880d410b01407850b002e01070483c3c17616034581c41c0583d1545132803540c5145c840d0b600b404a880b00c140082050304101e402c018100314100748200111940040701421140d00000414819151440055000851369200e9a058003000c9610fa44240d08a0a240300303824558503802e01c506402c05440d030302c90100c0d420105890304c0c140000d02c201c10724140504010080a090300c0051803080e00041c00d40e4001154620024100117400d01201c1d0050062002614180c2061401c55051500140c402180e4900c1041015580d1081824055100e44026040e5141916103669106039003407403141c0c400c051100d40c0300c2004c0140400d004041c15402802129002409458a070f800d16031160741d0180d01410b01c00412005018490302e40c3e0f15071031800c49a6100f00b0300050901e00c031584804c1d4024050707201c4000710405001c2100716036017100ca8888448c80e000c090958580d0782d00c1c040c00c02400341d10011404000409600809001c99900d0302c1e40e00f9420780c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 969886672 1250 969885422 969885451
    0x403081315233f04150b03010510090216080c03040501090e041121030a05040e060a0503060601030915062702070c1a07150623030309150408060f 64
    0x8490300c551207030b40e880242d0000080c860f40601003081601c01181040894840c0d4a2081c4085030850f9440c184d40544020f0002c82d507030043d2882500c1b400c101e84800f50024000351406000c20916240a4810b0001c05a000100d9290303000720340b0b400d0441654407648150715103e1044d1041c1c2d90f6003103130103050b0100e04074000c08941031140f04090b61155504c030300c030100040070349030a00c1601d014001c1e41101903064a1115050b1080920141c01c0b0351034241d82d0380303031074616140000c18040c601408180c02000365034030911454401180a950022007070030085030080a518114209038450001c10700640c0c9080c07004192068801c1c06606040421265610b10201d005540c00880c40390020050258020b201d081000582d5513024600340c419240d01c0a00b0700e06142c40340e41180d0100c0381d040000955459050105000124100550169801c10440101c038901c0119580303200c4d44180d1403107140105042034035105aa011a000f038102d10095592500b042124100a00011b903a0904e068112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 969887922 1250 969886672 969886727
    0x411041a0307090b06030c1e070837080709050a090c030c05030f1308070f05010b030f0714090c190509010905040c0f0c03110a0309030b01140102030403081315 70
    0x20b0103604c0311a200104094559198021a044180d04c1104e51080354490101d5420401a0500290a5030381c0600c41c182e0f80c810280040c1e0071a6a0407801030070038440090b10710000c064050890030044003441c10305005545410005940c03500e5164400b40d8030038070075000490005002e0304000210f0809482c1801001d51618042d40c9078003007111200490466800080c2403600480380b5494003d004070401d074500300003a102c0c1d00402082c4901542e6680d1210f0b079003110360400308248254034081f00301502d609400d0802010f0b07111424088544241c2003980403541404501044036106101c07000c4400100301030040150050b085814024045401880c0010341e030708047c0142c82140d1503c0e030380c4600080c80d018040d5000455800b0075030422071014900707440b02c6010808055100c5c082c7d211040075074a0340c500b5000e40c0c0070503005003190304c050000030300080e6000001d40b420f890b07202020325204c400c01603003203903e86d1071507020002c42d425481102010300d800c103208507004a4400141050500c1c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 969889172 1250 969887922 969887939
    0xc030409050601210b0f090c071101020c0a051912050f010b0a061403040609080a0e040506240705120f2107140c070503100e1b0a0e0411041a0307 64
    0x200201c284c0c103601414040e07a01c042c89a0700119000b00004c242840c190a524007103201c16070100c0b2800e101020015040301400b62084510003019000d10040c02c01d07540d09004942150176901c6864064580910181c207841428040140580901d00243c80f50300340e1400d1450b95120f07100c0c0c4a00c8030303510340303012080c41d8104000b060081d00c4854a0b420361081680040d03000c50340c0000c0056524996500803c000200c03400000c007001c0da030959909134801c880c141003004a400c080c0c019441380c25580c0542d030002050611230344080b4031141c482c03910303032030700e0308145080010a006001d4003800018a04200039001800f51500d23043c0001c81e0001841818a0b40d44044d000790303510004200c0003070078500a8000800140510382001c400e03561b0701561030380800d180c8000103400303801958031400d81940d41d81040081a9111040301e04106060a43c4008600007900b18000d0a020000010008051210304201c200190310083d10800080241d10340b280502004900c02501c03074000c02400140307009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 969890422 1250 969889172 969889187
    0x310020a02071517010b18030a062306102102032401020a030e1903021503011a030424060e100306061401020c1903020a12021c0503090f01030608030c030409050601 72
    0xd0401680113564205a240015500100c211102c00c824404041c045034509015202c0e0789032090381c01041c200c0304240f03408410031603a816048080000f0040010320f035610b1801042c0d47c200c0d820810002499007254002c22003c0005400803d40008180b0040c0c10f06d04840c080c08082c04030300881803283c2e94004a07184c070300008001d00064109140700c062860085500421408004a080000c5a9a0b130205030305030351410110b9a4a580800100030801c075030060f14150540c80d9a4042c510b28150b80d5501ca2a0000b046504540e582c0c3c500000c242c41e86540104054210300700c807e58bd0340703000300440130b281da0700b0302080310418104180000c144c03007814181a00040142c010b44060390008081c04020703031401100c0c0e11a84008070300007001d42c90b543c1c0c1110241202c2041e440c41210140180005c00807500c4280004102c80710320400030840c00303c280ca400c80411079a090100b00d11100407030160480341c00a442d20f02000030a0b200c0003e001005000b19181d14200f071205569150043d12900d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 969891672 1250 969890422 969890447
    0x1050f07080402012001151a090d060504112e03061a030907090e0a1a010302090c28020a03081501020c0112060909030906020c09070e040b0310020a020715 68
    0x41076440481c00643c003500d5038401c000c040300700c01800c1700714420385c060a50784a0f100da000045520202400a00d03101c9854000140e01c200240b441c0c6480980843c5040a00f818060503056945000c07a04100340c0c01030f0440140c000030201c0605860341100b030f08004400b000c0c00b0480c030748610000c1c04200d009009402c11100103501d14400c100640c00255003d50000b0b0100700903005512010400510394815a190b41a80b0801090030301011b181003a400c4100c680c0054506144c1401000143c3d00c0b615003d40c085141c92083da21400899051050301c544880000b0300b034010307242401c043c294006600c0c044103000e0b43e540c524507241e07860207c89807c84490450b0045e040300c110300166500550001c00a850003060000f1025650414142150244002100000d020074010403409904100904d0000f20848128215040c66003029100c01985d0480b00d01407601c1d01904c00e0507527003c2c4a01e0303041c80003e00003555100e800d00740003034a850707540c00303050701602c520307001c03251850b01c10500903040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 969892922 1250 969891672 969891677
    0x503010f021c11032212020a050d1e0e0105190e010e0603010f092f04060906020d02060403030f0204180b100203030c03040803182d1204121a0408030103020301050f07 73
    0x31a00e51682540880d8982c40118030617129001403080065000304010801d68007c0d8064890070b00c0034686142031100052003e020029201c0303980e802c040362840c4c0d490107029a07080c07002c0c400d1204401600d071400740b421008015401c19040394480e6800c208400141e15003640c5141d403482d400c1d0100305040c0028003d00f00e0151016400340914003141d8001d503001d00c00d9449041103803000e8000c90440c3c4820214101c000c4101040800c0580d0300480315a02034091070016204908005030025515140100003030101626150521200c2c66641c1c11180a080b20800d00e40100c0710f0b480c9008081d140c0d0106090144071503011004800e8404030a4901601d49080d12030300e151210744034480181c10107040c904900345144035008441e0f4041001062606000551241d500303014403050410040788074a00e202504101c50b6614121840000c84041d1509010282000c20041c10405458401050350310300d000261414842407050180186049074400c038001e20290380ca000c401e42e6110010b8130b00700702 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 969894172 1250 969892922 969892927
    0x50709060c111309230c010908060402010e060f0c031e0c07030b0a1506020a110a0501050d0f0b090403230405010e060a022e06050604060c12090503010f021c11 70
    0xd45000c070b0b6030f000810400b090220b4009510344401c04030350a005142600e0b00e64000d08080481001e0040b910b601e0000d08003809258644081d00d0b0701ca000003803001381080301c0103280342000d9039004140c5840c0c07088651110b48440e81700c4043c0b9900d60119940207200d106400c51424000403540c1101c00c102e070840c006e800502e207141c2d55511103207005448079440646507203800d11000000b03a600310040160741d00a160300c04180c10a88401142222124041d50380107505000d00c1e6005411111402040d10f0300154505404144000030507001c1c0403150301050300c5c4280000d0652169200104101c414104480b14a10b44c9440120b8030580c42110b0201b280c801c030990407450a00003500d0030b600d1600545820b8504e08440341d0701089150308840c010820560103243c1c000c00761085901510040c0c1e600da10342030504201800582d100302d0020500d0703414074210303c4910b10a11885008202c0500244a0032074000e001e54003070340003c032500b403603c40005014400c6da0b00360b00440e2007130a40c004001d403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 969895422 1250 969894172 969894203
    0x2d0b1003050706080a0b04050a02070201110a0b18190f0c09050601140a0c05010f0e07060306180b120f01060330140f03010312030b01020d020601050928050709060c 72
    0x1343c3c0400e00802c1c425141d5a6010030101e81e0300c5602926100d0075900b03000581e518414130002d07014a000c808500e04591000720201c0c0001c02d6a0b40050300808a201700c254400c0c040d180c880d10f040040c950540e142e490710100f8504020b10b547d03c2100301d900c240790341452182c480000700c0444004448150010368294030a0039040d001d8402011000c0311490440300b500c0ca551200c1d0b0035584404c90a40740c140d5200c1016022600600005014240918060200d5458074610102c1160b00144222105546d13110840705940c80c07411062002c003401090307558050012913000e0081c4254801601e0b41042d001e4002503411710300061082e0050300341c00454129607a0f01d004c40e103004d90490785480810042000700e49042410703000e14000c5208864038100648003140040039550000286030541d88440c250021180d000700e4502d055410581f0400070707680d40c541200707034905203030111100c03a885c4207021014400c1e0542c001a02c526000e441e550b408a945117012150b9400d0b00d507014110108003c07090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 969896672 1250 969895422 969895427
    0x230091510030b09060411060a080402060f0c070801020a200d0c0c050301110904150b1801020309060a0201090203151006030f060b12040c0b030c030103020108042d0b1003050706 78
    0x141d8000d030404501604107900c03a41c481d02c5100007030351a80102c1c0e00500400c01042890303903520207140015540682401415440601183c00c0900000d202d4900801d65003c44000481a1411003c1c0c1c40215802b00b581c551081e4003d52282040d4400104a180c11500e0903016920540107140080001d10301c2d0b0344039100072036a0244c0304504840441400381c000403940d800340a0500c21140e4195029900d07000d0030100400c0368864400c400308140111070400c10000041c059910108408074094180180d802c0100d0442c401d515400398071a60206401da0116815440340b03940500c01d40c103c0c4c560300190090070002203421140301c004902103950600101e440380d040021100c00c40c41c40070070200d40300d00c00c0001903008030f4900605140c010080006100c0c0204068008055822100b0300d0341c1841000041726120500000c2d043c040000d010030708103c211806100044850002419107070f400c0c5584c00d0302c1d50305241055800d803415401262000c200d141041040301d43c40001080c8151410b20b09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 969897922 1250 969896672 969896713
    0x308010906060e010e401a01050a0909090606030b0f010311191d1e090703080901120501080d14090609090601050408031306030f140721023009 63
    0x903608428444020200042042024001d003051100d56003885074110701c8411107842440c040e16080e0b130504120584141c00c0b47c9041c07506610070300c0d005c0d80d83c0c1c1901e542603428818981c0704c807044030318190811042c03149541c416420390788680c03244507841c0c44035640e040f44100207003c0600f616000301e10344203a504d040c1c508525840c2c2800b040c1a81c003543e5604003a95204100340d0324804c0d8201c00c042040b800b1681005100026000c500c1c0c603010b0420907031541d03841c1840c1c00300a140d0140065400141d0380502c80c031140100200006101a68440000503140d01c409014a008a00904006503800c8000c0e000c0e5540b121014090368200307500d1800700201441c0c05440385040c820708010119840780e0503c001c001301841045080400f42c07501100600301c038100a8000713001e030719001600601c003c0032000c19410021070310b4400016100303155201007088030003840840c95440043d1030740e89280749a4441d41c1c3d0008100a40424140c201013540c0c81c0501221016040d400114000845101c0c0011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 969899172 1250 969897922 969897947
    0xa02060c0c0a0605010b090f0d1109180616081e0c0d0b090c07110d21031d01270b01030b041e050c0f1905090901021201120308010906060e01 62
    0x12542e01e541d640d282c8408a0b003080c2c11a08000380d0008910065050101070001c8500c426600343e40741e88169181c034580188030012103031041040f480880d2900d58a016141060700031882902e05504020480c414641c042d00320802c0070424900000e40d1300c041191459000210092500f903055a800e03402c83c19680c4051084805296a1f518403405515044441da1150000e1090159030b1180c5081402d01c400d80b41035280e110303481c81e030401300c0092085044403840904102c400c0240d41033410040c0c0140803070300a8410750790a4410a40c141c090305400c41c82e50341c4114000321020105507440318071002800c41c1c0c042c01c04440813004000041070090003aa00c540128101480821118807403c101b9541174400c1d103803507102c0d880e041c0481c83d0800c808000300d001110b940c04c03c0103241d20b510f03440754080d1146a1181300309034001108080c082d0102c658000d80c04801860759a162011151045d59441c001d6000601c0c001c00400d4420316485400140d44403515201b035041c0c148001140c0049070740c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 969900422 1250 969899172 969899197
    0x260f0102031b0c1c091a1c0b010e092712270a090c02060a0e0d0f09090c0306080706020307050303010306230c0919120f05070e090c0112020a02060c 65
    0x1130720700c02c3c075089984404120346460351150f036602c0c94000c504d0412100042c118040200c10800080d501d1000e00148a41c4a81c0180106249450500507920588004c01540e001103400003080a060f00068a400054050030014051032861851080c0e5945103185141c6440000700403001110324683c8040da800f009004c40e106080b0410008070f450085990310084030182c842c41c0e16540503406000c80ca07804420846c0c204410485409403d565400c010010400c1c08014011640038622039200c02d00600b1a11205201c06c039020000100141064828500355003c0d03003202240c0340b407001c0215a0800e0300000210306503400d540b80c401c01402c0c0d04000700e120401041e400354100c607420491910803180500a1a00d45000704241700c000151200304440d030300c0e0718040c140f00c003590358403820399601d030421030b00c009840341032402d1850540c0c0c9821070050008910104034800300006800341c000c040a0b0f0310304070240c20845400c0e00341d02411010402580152001a901e00380e604081d003443c10603034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 969901672 1250 969900422 969900433
    0xe06090a03052802010f0509010c09050f0301020403060e07140d08120703020705011e15050d080901050c06090c03070609060f0804021c0807060b1014030a0204260f0102031b0c 77
    0x10583c0e9240c01c040c01c08000940d45840d16203203980700c507110b26540070301e03aa4024001400385000c01814a2280c2c080d45115030382c1010040602d032000d40c1524061540200c08124101810104698605280c42034070340f81480c80701c00c00d11074181105240d810302d80c407189131814842c0c00e02c0f43da410894001c115100b09176081c415080814024028031044d81c51408a6403450444002e06406648441100540010380781d0000c01c1076403106140c1d0480300f50004605e64441500c400100c519214800c200b00241c85075000303000c0708010101b115101407600700c003181c5140350b5504050350307a84403620454021070070078150603a01d00e00944501d648a403005100540000008070040c180303403021441035540410208401c400c2258900ca40c40ca05803049806261340400d1300f8000380b100c920889400a80e04000c004600c00ca141038042d140540a10724092108060340c03c0e421202c007103011105c503418803580491001028040c4203c82c000e0b20040d0001d8034031200042d07000c0803035000280b00c0e2041c0c0f042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 969902922 1250 969901672 969901717
    0x1a010503040f290405060603011e09020409290106140405012f011d0309150f09060a030c0206060a0509010b0c0f01110304020a0e0c0318160314010e06090a0305 70
    0x500184103c5840c031007210350054209030801d14a0841c0c000e01c0c241c040ea25100c000a428801e1025040c85090b0910340070803401814404140540420407004140003052103c2040e1024801c01c41c0081c040c80580048103030383c4e50a82201c241003040a980200703d0200401e000a5100381005c010910341c1700600102825080d5400c030004402034850b510907507503a40126026001c0600508051110310025401c3c4a410300028645074000116404203140005e141c0b404145c150741507442c504002007010341c4440190201038042d040f111041001070103408005071b031501e003030040c1905540f4050b00308002a802c1c04800c84056205500c903594900c02d626040441c203009000d961030b00782c140428141c51341818414000840c0c03243e0450070040d100c27002000403240d103400c16681e01c40c601d0f4100380ea040300815441800d001000f4500010b00910041c00300901001010310686084248001c0180d10943c40d5125101c00c0142c51a000342e4000102c03101c04a44514050030744010840c0103942c29420 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 969904172 1250 969902922 969902963
    0xc1a1e040305030108190213050702070312080402010e040e06040809030322050a06020d080a0903140a0822030c0b070905031c02010501140f10121a041a010503040f 72
    0x4045030300310005000000140454601404003000410303911240c0741c81083d0590000d500d1005144084001603550000030b00c545c2e10030400b1000554200b015007194104400c001003000a040321f080c2e0100d17512042c1380342c07135050a01c95a090684c140380900240d4540d41c1d1040000d5229003186641407205021040c80d44000b07a606960300c034003014070540705525060078401c035030165500020564100e21300c10004250041000c9038019000c8000091748805850143c0f1820401803025001002c00b1070311110058005000a002c4c010381c641c0b80034000c600d5400d5522465a01c00010300140d481800d0074001100341c41d071181c020b9460304101c1b12503038460000c070b85445003400790b0b04003110500a0f42800e4079028802c041c0541840e0790305a403045140c502244280100d955624000d0040c1c52080c7c800078072641780144001c0c3d141030705100642c1488446c0c0040c609a03045c0610941c6020303140180030031030011103c105081a11141d056982da6142c420b000590705000f56118140071514425415 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 969905422 1250 969904172 969904231
    0xf020309010e03100e011e0c170907030b0a0e010b0a06120b0a0b16200901050f010909020c030702041404020f1504090606210e0309060a02120703050909070c1a 70
    0x6174000f000040d142e016140d80c608400700c190040496034035100f0300580d42540b01450440c00992041c0745003150701c45155061070703d200340c0e001408aa240c1800d20101000700d8000a81d01030410000788040d2101c0b00030040c403103429101d958042100a404220751588540000e2843c4400403c02c1c0f81480d0f4400b4044040d40c0041650b04542c0b800c5640c200802408000400b039094045014100221201001c07402c0c0c8034046c000d440c401d01d56600d078241e42c2c0e886104904094042100c0641d12070110a14143d49c82d00720b00c00482c820350030844c600307541c514455000c40c86a03030000c0101203506d17500b0082c0041c40380c03190404002802d0801010032044590b00502c00240b406da620203400b01c54000c5142c40142840c03d0840c907150502c4d00b0f25841c4036000040d10500d900488220fa80c2d980c104506a1034610002502c54140b040030641c0c00030302d9000f0b0080d03c245201030355031080e940e542000c02c0320001516140103101e125040400843c00358075400150384514141104144d41429030040b0302c81c45d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 969906672 1250 969905422 969905441
    0xf0609031e042c0f090604060504062a0f1e030c021912110f07030b0618090303010303020105070801210f060212091c140a09210b0105010f020309010e0310 68
    0x44981800c0480f181d81100c40d2164030200d011a4080a03080030329000351518800360000e402a510342001c2002c0c880240d10814254a4015051200c2030300c500c0c44840948020030600045800c2061002946008000041a070102003140e2a80c1741d451072400d500902e8903035140000c500c17551716801d0310318404c0310311244001d026072a103030180340401c2c0300140b050451140500f1603800c0041d02840e42e96000031804142c0b9400104030a007552164046010035400060305098050b1250900c2810203011005605890080c1e000f80f0066640c8001500c5000c000e20900304070b10f0a06088113400c081d44d4450054a510808640c540780180d500e40f10240e0b0030040b10b204cc0aa03028060046000d01000085035078070100001080c25450600c0180c003000001c40504104000028600ea007d0310500e00035020b01090300d62150300c0001f107106802545a200022180b0f100054000310b11b80d8080d054401000c640c1c1d90040d80b502c07208000441d041150580704607010704c6402400c5810300454040d004c0318 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 969907922 1250 969906672 969906719
    0x80607050924070f060b0d0807050c03010212011a0706020307020303060102010e010c05070204020d0e010203012402010911060a0207051f0e041401050d260406020f0609031e04 77
    0x403046900c08010b0142c1a0400241c480e0001802020344410703041c003968062074000f0303101c0304006400c1c00c02d0000f0b040d50b01d000940c048189280c50303041004c101c01410a0500840440301c4003c83c00c01810700b01d1040360100030110036900010403041010714610250000403c45540c1415026601e940c140d801c01e50710100540c001104000725568240710340c500340c1520600902c001000c0385d10141003441600780280c0100e0700001c0000e4966140d0300412040700e1641e0085541e5a9640f0300140c40300b0310920107a1601d0301c0c0240010015105004594509400000141e420310240f07040042c56403202c8507160540c0500c1000041c1c60741c03603400260384451440c180001030440f510000306103207012980c0301d00c40c41c64024003c0301301507031034090750554006564001a9501500b030203580107602401c3d85881403480860b11520080c504090001c0740e040d074003140c1104002c500e28648a07881100c0d03d4540e6841409a082e0220310581c1900da4103400d448030514060b01c0c1e21403202119001d9003903c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 969909172 1250 969907922 969907927
    0x2061201080606011e0309020105070507030602030118060e191d030301060212120604020a05120408091c0f022b0804140105130e100527070e0a030b1008060705 70
    0x3240d006208090f4880b10919001e81904406001c41c1c1421441000310740c10190348000050469002e81d04484030250450700700c8034002c0d524641000690302c00d0007640c028500f50071108058038071602401c3c054825172106042150b48078030360348000340b80301c3e58500111364445c00d040340810110300c0c01b11410b01c19030003c0c6550358100403005c1e141c0440a20318004c010010020207418a03814440d2a0304128125409070342c98002007000c4800b40101c400c11054138a0350380500040020100041205a0090b2114481500d400c0c06c01154145100740140c107024001720b01800500e4609001d102690941081c003407026a02d55141c0d00076803c20800712040240002c0500c031440e10800300781141e803824a00913141c58030f20500f0540006044c46070310841074444010a614200e2015454040c0002801d55a441e04401b0022400c607440d03104410413501d11040810909403040d0074010103081c000e40b011006510f5a6542054140b00501904034071181a0307011885680502002d030041d42103070b49aa4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 969910422 1250 969909172 969909179
    0x50405090309090c1b0601080c01030614030d03090501020f210906160c08040905041b09230c04091509150302100f0c050316110901030f080a030902061201 68
    0x444502900e005038690060242d4041a0f0314401d400380e2014000c80500e440700080c081c40c2c42c00d500702180c0c0145074010790002141d803041c00140c0445484d000d903414008a5038511071a40e0844026443c190142c00416180d20b5242c080c0e000310308d0f2184500c00041c034000344080001c6003600480045c94060b42035516111500e01c00781c04458000c04075102801160034100303941031010703200005032000e1248114a510078841c202d81510f0081207600414400ba00e400d14000001134048510412485110200880c4e86041e5200d1028141480b8102d42c18140400b0070194120b003008191076a506400c0101242540d0280640c0710700d1040e44801c03200240c102440c040594080b49022100285101d8041015076120101c0b51341c0c134401d80c10300c032a01c00400002161043d5040c90040d1042c40001171213a00b641600c140f8000290203503191008140c80d907410006401c900b844080c010003003040d8180c01158203c0c1c003c040209542c00c00044090003039022440c2030b0082858484032407403040040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 969911672 1250 969910422 969910429
    0x304090228020607081801140a0c11071a090a0b0c07121509050a05060702160902030105061806120108060f060609012c090c0c07080d020c090a110c0705 67
    0x4284119001e040840821800c0700c001c2d0360302c400810701c808000055002c1081c0c9001c000c240081d01034040028844020542c40c4401a4102a0b03041d05032107207803810726034800d07201390780c0041142003a8016192451800c4030254031101c90500718020b2440400071b80c10556502c802c40401070076440f105a84550b00c0a61040c01c0003110390144d000401e142111100280014440c0c0603482144d0310005400015421710a2410b440000002c00f58424130090110341500010340301a5202c0842d4044080c0c0d495522050a900080c1b0419421040c280000c00022547c5070064810410141c004d40c1417107001081c580e0114400e0b8030215290b00244203001049000c850141c1d131090f416500039103018841f80008000c90402d84903140445041001d41a00314043c10180e82c00020061017201e19081241d960003880e4401c0700d144485c0d1040c1003001800c03003004613084200700f0994001d4000888070000b0305c00b100c480100041d049540e160020b4082c0501c180c0a85900310782d20006025060412092 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 969912922 1250 969911672 969911707
    0x61e060912030c06071e0c1b03060e060901050109060303020a020405090f0d0c1a010b030615190e1c02030703260424090f23030f21033603040902 64
    0x2240600e1b40c0862000748150802c68030a5000d034000e4001c000b1303c440102c14150b68926400041445050071184803125000244a9000d00c0c000c200070442c50740c0c1c40c12000100c42d40717480000d0142c0c0040c0034000c090f2902e64000d95022291030f040e6206165110400c1d41441c4003d51031034040781e1006401420b0140d03c1f0812207908049100c111703029418290301c0c240500000b051640b00c2c95200391740a08051031402611403c0c1502c4118006480040c03c002c0c00c18080c12001c1e500886a90745100184d241d600804007820f134002e005005101e00310b44038009c61001d012b6110704a490a841ca801443c00325000500013030205103c2c4448454130811a0aa10403500c04400e040080c1c071203041c007400000084040840f039000b16515004080300914211050659106c564180196080ea01d1000e10200c0c00040000c8401924099031000b418509454001580c0f420503000c407090200f03002303440204800b040032034030ba00e03d09060000c80107504e1a50703009130001045160040b402c0c612100b08401c4c0b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 969914172 1250 969912922 969912947
    0x20a0f06060510050319140a09030207080d170906041e05010b0a030f060b01231e18130e0705011b0203060a24031106070213090602040608061e060912030c0607 70
    0x1d0901010300c480c40541c0314040088d000c2512140c3e1281c5101c1090b000700305a0000b48070403400d803205401b0020f0090310100e400005000c10a115100044e11403101040301031203141d01100c03030303032542521921485101854400844041d0344c2c0e021085003d503500c003610b0004500c15040714110180d0b504e084002c0c0d81102002505012022081010006c91420301c40d104c0101d015000d40c0f0307200c4082d18560310104042ca00d00b029500000c0a41d00c002c640307a034130300444c070b000c0e181d40301662600c3c1c26040446410081c5a00c4640003504d092207103620445076510f003030403050040404170b07505400080c200682517a400b1a60b0740d88902007540440444042d1480860140250f01803602d1a01c98110651071032000511444001501c001107694040b0032020340300540780c0801641601e85060300080d0301c940135420200d62180c0001d0baa03841c2c4541c5001d001c8103180c4100821070003120501845800061030561b010003980c103083c219040410190684c441240014412420545006003c0c00c0d040ea6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 969915422 1250 969914172 969914221
    0xa0c080601021203070215100806010605040308090d020111060f060406080a0b0f130f03030203010816140d1e23030a0f0e030c040f0903080115020a0f060605100503 72
    0x20100030180e07802007021034440c1000f03981280d5a54500608908000404c40d484c10343c40c0b110000e002c0c540000c140c0540c2075800c0c2e03604941950f41c0b40d45003036a46d40110301c0b000b40420010801d00c1230b9820046505103a15206041c1b40f008603806902140c18020304545043c440000102000210301c0d050280c80000d001c0d1002510045082d0f0b10f420300d400380018020201c100740900170503000c144103510495081d4000303402054000540c58002c001c0d510a00c12640b0504c00d051407101c1c008550080201141c000c1780d41300041320164418020621445802a035030102c1e081042c0888848103c0070041c185c3c490303040c0076010031401192030340b101550400e11240c5d038014400c890000313410041e0030030a44a80d04150340a170f4100800249031842083c2030030780203810614047e0001c81c483e04000c00c0d80c0c0c82900c9182c1940e0700e5480c540142c986070701009005a000c22441c1c400324200e00821a0324034000c0717070003040194883c1c021402c92a9103401220002d9400000c0041c03050200300890000c0e02e514 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 969916672 1250 969915422 969915437
    0x15060908120304050a050706090306050a0606090504052e240906110f01060314060702280c0b04060c051905060c090415080c0a060c0503030f040c030507080102030a0c 73
    0x1418140d4074503036030a080181620000c085011311501704003000c003c030b80c00411101c10f1501d5400c018a0301280d480110b5a05081501244402d4501e010f4041a121550754201e8a5854242000003a00002e4001c40094242d440790300114512043e1030074410400a20b1800c0c080c1c504144046d181840c2c0c07075400a00c4040b80c1d10140c400c2d0b0b0000d50f03601118224a0700c5a501100d05140b1410840e403001410030395840c01c0d000104020080d0212622800064241c0303c0c4ca07a90b1034001e0b2780f0f03007415140951402d544d8000002c00c094507420840d850f58010031050b4403450b1202a0441c2ca507029030441c001003001c0c070401b03104118040101e107404502400a07000b43c0e07200c603512035075202c901506140a142011514802c262901c2d40443c01e034007c40c1c98100909559503100c00c2e10344a0f990300003406040703034950224015026500c03001016510100940c51692805000010f200d8050000c48400c1401400003000c18030800148014200c1c99000584e0b07400c00c645881c0854101710f10003018070001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 969917922 1250 969916672 969916679
    0x30703050d02132706180c0915080411060a02150a0e0a060207020306010501140a051602031b0102121e0f040e07020d17070203090f01021606090314070b0a0c020102010f020d150609 79
    0x2250880c4498031b02c10000f1428150504043d1244034031a00644c1c030a240c2c038144030f0b49880c1d100d020280103d0242440103030320510401400300c188908082100560301600c4000004c0088601c4168080c1e400440024540c8040c242c0740c0c100b41a486041e20200d4000c514281545002d101c60b9006010074203104401411050501c01a406894182d0b800c3c848040751403940c0410107114041500d5004080d1081071005100e11a00816a1818940144246074004046510329002c03203c3c1101c24814000404204e0305042c42c3c0356020660340c8048103c28000050b04000c0d10880760f001e410150003920b070003c03141d440100114006411403225200305018494100d801008440c1c0c141019a426614220900700507441d0440410000c1851500034071300140c0c40d07a000080005880c407400c6460752044156a006a54206078014140305030f4040050784c0190780036640081580740706000200750042e1400120080340c20009141010981b650200e1b062280030340c9040002e00300f18144118403604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 969919172 1250 969917922 969917939
    0xc020d080c04090f0f05010b25050304030501110c1908030609041121010e030301050306010e130519060e0f030a050c0712030507150e030703050d02132706 68
    0x9444196028403200c500032034200407040307049802a0009a030244082c01c4c514980a008158020a40d8602071030f207000030442c0a5070030300302d90040075558801c10f1200001e0304460100c0c19005c03011100752204200000005000b8054120f082803026251515000301112507410040307403012003a4400310030704c003140005c1ca1403c10751790481e4042d114074802d50744525007205040d0a429086500c00d58540e80907600080710060b01c601000350b400244100d280329002c49650b80400e00a660741030b0410401402100e012112443e800701c0d03000c146501011043d101c130b41c203105140000088072003000c0354a0b0140704250203540c2c00d0030303802030007000b854105000071034480c01801c01010400000203440c020a42041040001900780c5001001c247c8495180151442c1d100c011700300d8401025205c80450141c10348504450401c0c032101443c0703048c00030341c2d04075800c3d40109201800385a092156104401c010b012840140004c022800c100e2413001900c2407071428280e020a1006e03007030040c2804101c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 969920422 1250 969919172 969919183
    0x90f01060c11040b030106080d18030506280c080f090d141303050106090204050909120910050d0c0905120d0219020f0907170c0909070e030106080a050115090c02 71
    0x2904111448001c95002c00003401a00031100c900c1d90643c00d003076010500030b02c00301d2410682e00c03107600d40d0740300000071400343c1740716042c54030000e400d82d0040c0002840b5440810342c114000001640c901c40c2100b40703800d2100c122162054801c001800c09e00c108100419102c03489078103c0f0350311005256540c1200c4006007005100340800c600f2100114241e214020b0405044000e9a8448001d0041c580c035040c0c100000c2d00103109280c03141ca10711010540850300410345080c50120341600e180b0344101c000601c07038940c0c082465041000800c0200c50400c1c816441380010030310b4036543d44c2903503501d00340c10051420350a481800403a0014030b80d200c102a000601e4841581d80c2000f8040380c4085400010010716941c40380d1a080203040c800c00c05a82d42c010411038880707480340c11115241e10307000100c7d5014000c2441d1150041c61070800b1441c1140502e00380c3d62001002000800c0642c1c584103040d0512000c85412075150b916400c03044002c04407105400042e1103a0304080200c0c10310b607000250340d072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 969921672 1250 969920422 969920447
    0x50d080910020c03030403081201050609060a14121303080f090a0308090106030506091e03070804030308270c0145081b0315040c090c051204080405090f0106 69
    0xc400d05182160003a00034041c01ea03c0440c01020fa9454655900341100c89a0103513920b801c108142c1d000100f045c0c80c0600070b8440325480600b10340d04102d50030006481040c01841661000d0b2800d000c200c00040070800064414940c28000c40c0942e0f07428540584a554080c0000c54285404810840842000218040403940501d002d40c4152142c401e00c3e03004000540014000d80114002c000302d4220004880303c07062990700703030040300b45983c42044d91031b401030b600000d0510308100010000702c1e100e425040c0e041030f4040c803201c410140184428860700b440103400f24590f080180285125a0003110038403c400c8884031901c48041c441045201c011450103d00c42440351004901d0342105166072000013414045040f2102c0d04144459a060006801321040c42032040b10381c00324620203c491540e0189a2041d0042c180303600f070112540c0540403000c9908100070b800c2c40700d9034100034640c07500d0340104e000b4511647e82d5414001403100c1110024001d000d00103049004001a43c0d105c5050501c070b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 969922922 1250 969921672 969921679
    0x6020703121a040b0112021305010909090c05010305150d1b0902030c0d0518060708100b090906010f02190f0507120b0c090a0302060a03051f031509030507170307020106050d0809 78
    0x801c001c1c0e0005980303014428213440300c0188041500c01c07040025040c1c2c0809d5800980740e952005d030340c44080c00151140c1610060a4045641007000254000d0f0041a00010b807031400f520784030740b0394000c02c580003c50711341078420781d07200029004040e854642e42800790403407210640c5545800000400c6501c501b108008407a0340c0e40740011402e00d158442c40328102e20b0030b82500e0981c01c01d030000415926041c3c0b0903042161102000080c00d102c940b04030707040c140001c0c082400940c4e800e80151803124540007083c0550040d017550404045202c00c510300304a00c00c02c09466a00440e040940c5004a02d130001906841540e080e0800b0520840d9525440300490b20100d07a559200d00120380c3e0030b00c090b80001c2d0411070202d000b6071250b425802c070510440b2104051400418001294000b4500e0f910000e4440400050307003014107550f07a000600294042c0c28001e1400ba03076943c4542c1020105540300403a81000300500c060703543c0c28040d200041c402181d14404034245c50f00c40460511428082c0c620 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 969924172 1250 969922922 969922931
    0x5090d0f1a070c02040f0903022d102705070b0c010b090a020307030f0510050d110a03030f03140c090906210c0f0a082109040906020703121a04 63
    0x80088203101c0c0340c007003410010710788101c1c14802c502800190b40d0220403840749080850100000440b4810b03c0d51554040d8020602004040d1700c9503003c54140c2d0415125440129410300d08007410401d048010054007000119a50318820041114500310b11400c0f000801b040c9043c0800c2d030000b030340800e4988c1640195a6522405145801841200c044581181c0d60100704204805503501441c418100c9807001d001d12145135041c4021110704850007074039a11407102c240140d0070011101806070788a582c0d0100d004107080000381e400105035000b2400950610b240c2428540c3c103001d00c120140340006600706034240f0742d9800e800c502030624120f02409210002901c0b0703a80300c00482d200c0c0040548074415813a8204070650b110719481c80664000c072002c400c0c40c18182814803034001264008000703808001481c0030352218003403050007600d0400c141446030101c3d0b07545078415504054070034400107950301040e20740a020121040c1c913842c084c62500e00d00076100c1580002034070865104845c00035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 969925422 1250 969924172 969924203
    0x170106021e120a05131d01140906010815060405030a0c0303110303090714030c0415090b1525080c06071b020310051003060e0f060108161a0403210e0105090d 69
    0x220700d0001e40d0101c162400c0303000c075100380a06e14904403416282140f2501c0300d111415414401d64182c2640c20b80d0004051800140c046800c4100007030405900a107064036103940d81000a00c0c000035904180d80c410052101002019000141c500c1c4d58210342c0040d60941c60400130a83c0c8860300c0740b2900c08621a00e0221820580d81400002c4030f07a08000c0003081944949160310303803800058092484010b00d0103000d01014030f80135903100460042c101541c1c4c5044601e200d0a2004540a10030400d048040c001d0580000c8031080944461845240103098500c0d10460007008280d400b121030756800c0321044100056140410203a261070f007209000701d00c45c0c079250302209100940da8400703041185410480d0703021103000304104442003451381c225651a40c1350b0348070540354880352500c4010011401c100700141d81c06131540c40030100d510700006041a5894881c40d04807a0103142c07100c101100350940c040b50580003440010b00020a280550078900c411000c18050244c0460140803020b03d0300350350 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 969926672 1250 969925422 969925447
    0x6031c020a0803041a09070302030c04060e010302040f0207080a0305060118211110020c0a0b13030f020a1814071b0813170a05010b15040e07170106021e120a05 70
    0x1c42884a03c2a000303869450030105044e110f80c11f601040f4881d01035100c0c00c0515280500511041e01c2e1401540c4e15141d207550708001c02000030448080417a0340a21113400411a06400b80c4003090f00c5480108551511034001401c42141e03500072203040f91354103024000e5003c0f01075141d0143c2e0541c10380100c000320340d041c5880d074859030400d540d030b20042403000030552681c0407401250003401643c4400c100d980300c000c042980d010720a0410031b06203d0307030030410209003d84041100c05001600d2805220b4071011074421083c0e503240f40034480c90b101c01704800c68a941c04807980d44003030540b83ca03a1140b40400311545003d04180000b810b0b440300070074510304043e18610048024108003c1708000648180415916500a02c43c00e039100e500c2d01001d4800b6090614210301c201ea4142100342c501421300d01500007001001d0030103010012905502c107882030221940364040c10702ca80040044003414100002d01d0494a00b042d1034035081034800c0981900c0b00426510703248228200701e900c442104012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 969927922 1250 969926672 969926693
    0x3030b0d05060118050109050f04020d1104020a0c1a06010e040c0e03030d270f1401150806060f221e061e1d04020f060904050a0506031c020a080304 65
    0x160890240348000905800700360842c00b0500c0810710248986d80c0d03107071180000c50b1821209000c1d12036144000800600c0c2c03001c0d020103a40e202d15904040007010001042c100e0304908450703c080344030b444801050046080d008540191502a03a291a16101c0002840040e40601c002d014070b496a0f0380180150180520348030b4500c000d8102c1c1d4071810f0b85076520000d801c03440e180c214421034607511020580c4c02c000d1803207201c3d60820f0b074400c1013110555074409416080103984071103550300d00302034241c2187d44003060700a14180d8020605410b109041000f0595107801c51440360085040f0418150b03424800e1400032540984000b03100300300320700307410b103520340140030100480d1900c20081203d07005041460841c41d5809420307280503441e01400092540c1c021200c545010f00100000c0043c545140b2a20034400080c0c90b081c05c0684a0012406940007503411a5846480300e00b0820a4102080b032100514400d802c042e094040c00c0402a4860341503d202500b240717400030010b414010702c2040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 969929172 1250 969927922 969927949
    0xb03070302062b091a0903040506210702070807050301061a0d0914060403030605010c0302101e150918020a170a080d2c100207050c0916111903030b 65
    0x10f6003804100000882d400a2030100700468007280148540e600c0310007080c2c112480b46d151800110302c0c1900706010455250002c84042c1105142d1a4140d600c28100305503080c000d12413a00101486c4d1705180240d4140100d580003940242e140800400200c104043ca42c41c1004041400c2681c5400c40104c02014200030b0344080c011205840f6601284030303000500c0740c400c5000365010003043e03440b14011a00d202080d0005001030348600040c1c0ba44c0c0040354050a000394480380740301c21121000d4540029101404950300f22a1003041040005000c5170003050303a04d2a10840100140102d0f60024605100500424202e00901c1442140544080040002550700001c80b56156405040d01102501c9441d003503a034a00d000d1f140058446080003048a02c240c0300c40e025204030400b49039202c1c025007180a003a41c1c1841040840007440d2582100315010300c80d65081410303140c0103280080e085100105181c18107070b11461014040302e0000c071140510301d516113404184800c0250008190aa5110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 969930422 1250 969929172 969929227
    0x5030702030421060c0c1407052815020d12020903030403140709050115110c0319080405060a0228030203070201200d0509031005010515090a030c14040f0b0307030206 73
    0x2042d04006e42001c0c040220700e104050030501d032902c2c41c0070a5243c00d510b02c541074211400c0409940b02c0c807468003032448240c5410b820112116681e554061901d8680145240580c00942d41483c032181e110098000700b140c21503041d80b6200c21308000c0303680da1060f0310010344040019000e50706600014406e4500400c00d41105101550312201e501100d500a000c50a011a02102c001420280d001c0388050305168014050550310b1f02c07a8500003c60300030781c0c500300d40101003000b010445607128000391101654035401041c1c0c0400000200403112110b2040241c040c002c503959500296001085890084d4280b9140c0d080950150550103810b0701c0e082010aa401010740d04103000394440c0161030788150807021a00e401c41d000d07044404454080c06466003004018425000404d0b0610007480c480340f014045000d100d5a82e2034019102e007585c0c00c00303502514580c4282c895482e180c010100440501d402c1001030707540c4600000e90760304051100038007032030f03001c560b26030018920b01c0c1c090702c50b44400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 969931672 1250 969930422 969930431
    0x1b1112030406020406030e0d120507030e0618240a0c1b1a0612120f0c15150604150e01030e010c050913020405010903031215240503070203042106 64
    0x7071030080b019420a0003020002850a503041001070740006035005079601c81c0e02c624400030a0300d40c00101520300200490b041c180c81d64160710f480e54040101900c81e028110700d00d106401c00301d0311b8504003900044502c5403050103a200586661151284c140c001e0b440c00000103445203664426150840c01c100280400a1030020720014041e11400f558030407118000383d02641d549060420407012220810311015521405883c0e68002c1408001c100325044810001c0c1032042007810149800350078058101406110010f10440249007400481c50301000c980090074a41000121f081c0c400d04295100c00304207001000c8007131640254450418071310751700c0c001c3c0302d044090100a8525440443c6103402444c03019822103240c451442582c00b43e46050b0350700d1140c0d510b562012264440c8003140041c0e61503403103000703484c1140c1800c0200b0051a00d110b05004801120803249210441f1458907c1071000070010840015030120444040e05c04540740940d01c01d6200c0003102c0040c0280400520041c0340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 969932922 1250 969931672 969931681
    0x18030318080303072a480b130e040c1a0910180b040b120a020a0e0d0c080307210903120c060f050a05011a0c060106030e0307020907050306010e041b111203 68
    0xc120303543d02c1a422030300c0e555046800c0e071505521b001c6810f070100c2c16400e40303400003841016002002824880b0020f14000c0203151143c480790b9030300c081604e0888101000550070000300c402000008880750010100500344000c0c10040340c0165486a051020815100680072025400c00440e40240c802c40076a80d403282d44034850202d403a8003802c0003802510396080000d00303241c03840c02180c1c402c101c2a079550054038a41c000b4049e00d81d000500403110a440103101082e040c0c0208041c0c49494011010350300440c101c1149115180c01e000110003c000c554941030000c0303029840b9100b01c1c2030803403921440120640c04c107000140200100c0401c045e00704410702c070f0101296088141039403002d102c02c103601821130403400401d10544400c01d445070007400040103607601981c80030703c1000340d400c103482c6400582c0d400254680d004030380b05404030f200441400040d580c4070181141e921010b480410001c440c006165240701c0701d15040c40d0410450280e41c40300f1940070701c00b89110800104249449007070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 969934172 1250 969932922 969932963
    0x9060a031d10060506042303071a030a0b010e03060c0c150108060f06061908071106131b050f091302030d081b030c0d0c18030318080303072a 62
    0x65140b1000005401c0c0440411580380c000101c8088541e44048840c2d00404000c02850310240c41c0340d61135050140540c0061040080041841e5144001c80c00343da503880c103501c41e84101c1d11007118450400c003c1400f40ea0703050310b001450681160460001035101c01c0000c0c0b0071485d1a0321420212001001e440000030b44170000120540916040d840001c1c4a50310181405814001c00300f9840040c20410304041c03c0c00c0c06545025080802c51a0070002a200d90010bc0d1030500705503117060444140b2707031414042c49401c54507400600b0304042d840e40c6452074000007421409040c03821911800040c00400c1c510010402c03003038055940034080d2000402c0c1011301400400d021102e01d181e000c04448161100c1c000e00c03044900c507004144050b410304220003411030007850880744010074042d0b2700c8040500c408640242c0b0700114420350380e42c100031b03d04030700b14040100d807a449000d2580c82070045c00b031800d421040030708001490b030b108055000310f5002030030f034107021091010b403401b000d4030042c0b8520300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 969935422 1250 969934172 969934183
    0xc0c060908041a270a060f0c0818010f02010e0312100e090d020c010806150a030e160609080133050406060c03020f0a030206070c15060b04030b0903030c09060a031d 72
    0x191130240481d5100000c0c1c4d0701500040151004560100750401c050000d280030b074100c00b403481200d10b0002030786407460b85c4491761039004c40c10031031903100702e1b8217002a80e690144030a00038414510003404072140315000503544e4050360b00c250741e200c13548000180d841e2641c001c00078020010700c8929141c0b41040b00107036441d800d135610b1050041c0a600c0c01e0084550140d0a224090f07107000d80844004a8901c400c00401c2c0c02414100e8205a2074001c652802c40b0200300428800c652105084289450708a02514000d401da00c10340f016410034401c509815041e044c0d140704900c1ea1460301d50003541c0000c0c1e00d2510001c642203650311924144010030000d9110a001d503005200f902120550901c06003141da407850700c1c540007001a400303c2c1c0099002d174030941c90f045184c3d1103001d4a014940d0610000f1040d241c0a400210607500082002c01c24400c071004400d4200b070420300618558104000c600c45248600c0509034020030001522400da14800e90001e0700c00c200d43e20040300001080598240c460 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 969936672 1250 969935422 969935437
    0x3601020d05121302010c0605040308061903050309060a0c080d20070507150504120f0506071b08070f060207300c12090b030a1401090c0c060908041a 65
    0x1803042800d0124214012800c0b200c03150003040c00c0d06143d0352116031008610070460b40403410401a051030b480000c0350780c09880d0140c2d1007911000214686a8140400244400c0e81040f8a840031602003002c40d80c044212000710200350785961b95175844420645070300351041b80c01414620b002900002c034070b42c264405842c220200c022070702407087c2ea0748102c00238052410050200e40106808100005202401c07100044841c10a54206555003003400300318080020140c4e00355035001d00700300800509101846e440141424040d8010106e1280c0c1c02ca808040c000041007020000380000902c110700441000042d07010105540e80e00765464440540700754000c1d0200840030170015500541d5566401c0c0d55020202d035a0141c1c404c4d126280d000c09101c401700c045007400040c110204d4000f005400441c4070320004c09012440c403005060b40e040c0540305a21018110f0710b01b940c0c0703e680c290304c640e503106c10680188006c240305003203041c5900715100395407000c0b64522006c0441680c11842c403000c0e0150 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 969937922 1250 969936672 969936677
    0x5150703270206090f0411041214030a02061302010c1211010b0109060203090105030c07060e06041110051207030f0203010f082a09040809030a0b09303601 68
    0x901d21104080311910200c900a52003103003405003007010700b403500300c1121483e802000440e680424195406d01903100e904075035001d00202a005040c0f04040003071200c80380000b0004c6152070f0324100000c5d1521400b400e034283d4410400901c80542e8400d40810300c0064100d445000500148107000d0100c480c226020300301542011489403182d80580d64010449540340c010354a019500401140d0980c4000d216402041041c0241004591248a4143c005010700020102030800781080141400071403803151182c01d442030305c60001da5009041c0d6a05103004080a9450b8031003a4059001e06910704121006034404000080c00c9500095000c044070b0b4004140c1e0034503035041120450548041e442c16903076003920034410003181402042c5592103801440c88070304121607a00000e00b03114481c4000c0c2c841110380d1052114040060100301e442038020341d001c0395940d103e5000c00d050315038146081d0600403000329400105500324840c04551480881c00c060300c1a02c000402c4250310354440300d4900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 969939172 1250 969937922 969937961
    0x10f0203070b010e1f140d1a09150a050112060e19081c020f0a140f0d0605040608030a2c030a08070605010b04080a0213020405060c06040605091f050405150703 70
    0x40318240d5070b181081c0d82c0a003148917100c90240e81886441d94a4500466041580b0408444230700d4960801e6801580420042c00300c1c14100c989803555402d0281641c441c1501d0030004000001c180710003014038944c040ca02250138404a084d090034041c1c840c241803807011098105134100f1800000509101d581201c80c4081400c1c00108030049005081c00000003d4082016001d028001d0a0a400b000443c08031546030a00c0740340780c01042d070080c0d12440084c0b521102c060041d8039181c01035801401008004508000c07a81c0306c0203180381c41e51000444060300c14811010710014080c5414001075002c3d080758018041407400602d5540045400d440051902c2d00201f0158106412541100c450000400049210f6001c0145a18504800c0040960308200004003902c920002d024a0851400a00b4a078900b60a00d0300c1900d40007809404103400015804a13440b0880042d50541c00c00c10340002030726034461422a1400803070240564007803105004001c1007592541003601d03c4404140c4000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 969940422 1250 969939172 969939211
    0xc060207050d020a170a020a0807060207050706030203060a06080f1f0f120c05010306080307080a170115020714210705030102070b01082e182a1211010f0203070b010e 73
    0xa45900030765a42400503041015488d02041101010701240c0e03000b40c400600e0002d00b651940c3c0ba14180342c0c061030101e0b40200421183d450902090300080400c0d007408140c910380b0b00540700700003000400ba00581d14401201c0788a002c0c83d0700c5501c000e40b03009501002000c1e100e04081c0d4200a141500304d441507205480425154403a000d02d10031a2403120007075090007400c0c1d4032180940c00210900e01002400e04009284a5050300441c1c028400d544545007400601c250003400d00c80d16401c55420305084044415840e00c429400740c1c40c0c21200060b000346000303580309090500b181c0380c0c8010ba02d5800031894a050061019200f812070b02c00c03200f1910f40ca6010b401480112a408801243d03806001443d0312400f543e98001106001000d03001c414403c0701c95552084211b00e0074001186062020242c45051100e003180c81c000c1d2109038140c108000c500e0380c400c4884002074011070b04210400b0584450b00d4020420740d60341d80d078441303000701407980c50300355144010000b00c403807060814000b1801e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 969941672 1250 969940422 969940463
    0x30e12040b07020a0b18060307030e1509100506150f090301060306061508041a090f1f1404050a2a0b0702010e0103140406050615030405010c022a010c060207050d020a 73
    0x39074a5900581d1140c46c490b003250100100c0c0d420080c0030310309041e111540d84808403420b0000301e00700116241d54440c1c40c24001c00e5280303801003802c06080081d1400341400042c0da103100200000daa000c1044a5031034030a421081894010300303004079015030a10b00003008105858000c0c00943c0d8090841640298401c28200c40219041d00c0240c800c3d4404540710a00b004010002c1e035004811004480583c801340800910b0403501000c107443c241c100000160341801c0d58007a0411403600341043e81c2071820607448844d1548503400300209940500700f0040c00c94210031b004a680b001c44c0304211108030b6941c45030146c20383c0c41550124000341c044120070342250301a2013444003510120a001c4800d9035580d035043d0043c0310191180360b0103280700c0d02d9102e44103646001144180e03c284000301c1c0002c132040000c2e02d000c01c804000d0004050f003d80b00005503c1014141e1031641007468604240c1505081a030001d118011024015000342200e983d00760b50002500349400340b180d80740403640503078010003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 969942922 1250 969941672 969941677
    0x601030c02030a0906030f0608030c010911100819060b0a0203040905070813060c02100c170f01060c12030209060712020d030b030d050702040b0901060c0c0e16030e12040b07020a0b 79
    0x1040c000c01c12800c4c4c1485101d00c00d5221400d640b086100000c1d0003070704e030201c2900e143c203d00c0c4815026034540c2605420407110402d0b80ca1440c03015900070450320350355440644400001008060245905040028295025003085000b8245600c0c0ca555480d00c40000170340700e03403041c040d4031421810314000c0b8411a2007000400c0c8101c04068500c62825200d5030f4940286c4980e410910852040240a95546100e8814070580581988078844d154402c040400c07420f10340104000c0c1d190200200400405800040580b5140d60216100e01c40d0041c580b4190024001c1c3d419941d013151010402d02d00f080a040c3c000502c1c8070399602110340614200b14102c0903280c6502d64a074040d0064002d4059250060028202d400d100400205911b035024010840e103c4003640038130009005c010900f010b004050903664098a44001001075034503104183d0f4200101108180d4201559a0007140e1903d00c00e01c8104c060940054440760340b596540c011800d07541000c0416441102e41c42c5c030000704078558104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 969944172 1250 969942922 969942937
    0x71a0f090d0c03030e0f06130519030206040b04170715180c1403011d010c08090c013c090602100605030601061809110307080901020711150d140601030c0203 69
    0x5890b50303003080e82c0e03800700c003c1c00210390003480c0b5124200d05420300310000c7c040e152207900c0d1140703140e505440301d0801c1490314958040400203030300030310f40d4080420360214440d40d006810698010041e1201d15084199114600005505400204a0740304008204a41c81c4262030140c6050000030a01c00105000da04000401131130b19014160801c1000e50410100c16074880c01400010b142103000e0a104030502e0b007802c08249650740d83c07001010140c110a140742c12240c01c0008000da00c001c1e0700080c0c0f19841c034000400406020102ca104940d1520180103940141c00d80d00d40480e4444500242051240b4050b00e409406103815403441c00c1002d01c101c50840e04001c0042c0300503482c00005030342e41c05882d44da02d001004490f8002c12441d85501900a00c1a001e5841a40e02c1c903040c03500400c0c0540250206016900410008011a0303001414810841c400c68501c400c521420f9203800052140d1400301c403105051010b503007643c0c0a00000b00d4460314080e2014803518000140032038881c4241e48 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 969945422 1250 969944172 969944177
    0x2901050103150510210b01020d020d0c1112031c05011a07060f11070b06150f070222181208010e0f0603011103161d010905090c071a0f090d 61
    0x182c20059032a041c0c0440340c1000480c142205c85917001d0000c07854a291201600d0015a11003015064959042103260303041c000520241510214024005140710020b580c05000480c440c1000710041da103529524640c40c14400032282e4541000040301312115010700740c5d88020703142c03800000e00f1117090701d840b919019606181070b107069074660b200d2009189508225034422344e20b2200c0041d0300b801d0346c01000003901074020b8810b549000020890079403030364408000108010300c002e036402d240e001d040d6040164100c95030204146006500011410b007101d5007410141000b2600c01d05c2d4401011400301c05005e10310181d014010450252780c204001e2040c0c1e40d50b6028000014034240100400d150002c40090000c90114201c01c040a582d400688910188040340b2130031031103454000520034140400d00180c0c4005502c504001380220529202d01405140c400000816040400084503007040c7e20543c0d400300b480354030340c2c682d0070401d0448074607940c43c4240011803110719001483d03030110300996 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 969946672 1250 969945422 969945461
    0x14060f0307150c05190516050102190204090f0b0c040906090504110d08040e15131505060d0e06010f0303080f01230d150e1e03070f0f2901050103 64
    0xb0300c2124040740c40705064a0074007131341d00c0d0407006907034094001020300c1c00b4000612600d80078030340070f0304541c00d180d001c281550322003d0300080c0c401700c075800190356540440700059990395508000035004400e4800401d250288000c001c40000218081d00c1a600041401c0100a881c0c2200b00111041030703d002d003088164442441c458507080900340340c510301c9125800d061a82d18001d003002000c00307440c160211103044000013820b06044407130446503600c6000511110100845c000503000c194000d541c041c29000071541420800c81c0c000f50003901224040751031039030b0341e580d8241d100b14141c007040f030001c0d030100c0110784003200c400c031081c0c1640c40c224012103560194464488181e5440390107903800c900c040e048071003c42d03070304291310300f051601140204541504408860134902030010b01480103e0308000704040303400020945451036031101d015058000b060a10405414030130b9002808805080e40c4103008ad030540714400f4150380601700360a400e036203440056003950342c040440c000c1750004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 969947922 1250 969946672 969946709
    0x8130320041509020a0507050a0c0311091003080c010e0a14070614120403030f0c030b03060703020703090b0313150c0e180f040c05031b0a0815012714060f0307 70
    0x143c2c010704c006140d1b81005864a00ca40e500d0a0a00b0203500080d228465059403c10a200c1c00c1074002c115114200c901c5400c82c0f9041c00400c0f0507400501010b0300c00d0902003659035800301c00754410841c201802003101d0b5100020b00e0000b0401907801c1c89031103507004585000840078080c072243e090b14040d600c80c40c1d033040d81130064403943ea0303001042a000c15031103d10300c1c00f00b01424402e01c207400758141d0b40482c02070f940d40181450b20070090710213000c244c030410134000401d9021070350209940c000c4280c1503403500c558000401140030a140500144090950031580f20350320b9000100d0102e241c0c990316424484041040b4050044000b0042003141550000e11018142404070760701500c590380c0ca400044e00c0e0808680b400403070b10041120b03082080c42c461a903190050305400104540b10043c044008100340c654104041807048228030f9480700c5c000c10340300c8201e1035480c1000c03032400740c100300101c08105801d10b90801070702c00602030b469108070701e040e0707040c04a404070590b039050700e404425100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 969949172 1250 969947922 969947939
    0x509030a0c020d06110c010c050a1d060f040f06180608060d2604140d020d0212071509030614220203030d090b07080709150c081303200415 61
    0x20501c00499100408007030349800503503948260a5070380c840051058984030031615450071196124110b0041c00002c0c480310b490540d20205850702603070003801c1c017041044d401000c15101e0043c905034901c088404078010074012070340121070007180c5541c0ea680c40580b00a000c000c46900081c02400001060384002a4a500704403801a515510401c1070070701c0000d504001451200a07281814559017001908000403c540c011101044c5c0d0b0403128035512440960000d00300008450000b400380850143c1254040b40c03e0101c1c40003850b120403645035048400100600d010311500045428038a0142c1100342e00080540403442500034a05800440a035144414030124188400f241d0511080003590141c140601900320b410b44075202c0e92a2500302190080c0031208000c0c0000200300b250719040003102500c5500403400740e01c50070140c1c00c001890030420703554401d00c40030000d242c00303420000041000320300000400211840d0141020290001040295425614040325011080b581440400d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 969950422 1250 969949172 969949187
    0x131a040e071209150605040212070f111506010807021c050d020705010608101b0c02010806040612150e070807051905130204231e040e0a05010608100509030a 69
    0x4050401030291803030b0400903015145822412250465070442c12090b0703070341d039014180180208440030b44c00c007106020301c1c1c140558001e00308000c0144504440032018024081ca0391004440411303504800d1103800e520700050029100c180c00544820300080754a0700c0861030075072422001900300c2582035109001ca80c590012406015036540c00c108403c0001e009104840003002c001015120300c0b40000500c2e4221040080c1c41c22216000c1106200704e030b507028003210074880e03090900302c803191904804100148215040340121480e144d0700c0e4801d00120300d10242654030400400e10501e001c05040b151181d20302d20800c643c5074420300040c0700901d072004801103c0c0400c0420180e407680c0d0b5400080703e02040034040c3e16881c0d400107003440b100d1001ca1425180d24170140d10450041600b001144207103c00340200c0014800c17a510000c165525030b0003010010450404595041c0c0b2a402c02c2c9000b44107510134007a00744100040c041c4e011905c0e000b0b0920900a01d800b17542880e0005506840f41c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 969951672 1250 969950422 969950431
    0x60e1e1e0c0a09140a090302070303030f18030c1506060903031110022212020a0603090218010605090306010812090907021009030302120601021f0207020d06050903131a040e 76
    0x9004a501110240d1030b01e280310001040c44120101d42e80428280502003104041d11394003189041c1440a40401d80000e841d500303c0e42c0c14903001070707544014810f000003008480c000c2d038070441007414035000741540450101080d5000340c60502c01c0c034114040600845d8024030a83c00820f602503402c00120707010760301c646d9200705804161501e880305000190102d80c44841c5241c0d902007009156617040c103107803074014060104170060f5a0700858a40014000803c42d201d21420141c075403102804548596200c1b58508245202c4050039503101c40d00500150481c1c1380d00d5000303104640000a11140001b030115514035031040140c90a001e481c01e00012400050443c0198420046051a102c0c070328030030390180a029680040c0ca0300f003c0b02900050a10142c076a60441d0b004841082e01261a4080304441c058086030040e075510681c808a07410305c2100c0c2c00509050b00e4a42044151a408402011f4038200d054107203001c140c83d600102c07142c0300d009010302d00e42d40c030512083c400300f060141840d400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 969952922 1250 969951672 969951733
    0x30c0e0609192c010c021c02030f07050f0a08040614160303020a1107030f021806031c0e0607081e040303082a07030c060f0c1d1804060e1e 61
    0x460221a1a4400d051062010303c05070f0341d542212841d040d4188400909005054000d0854030b0404c0c400070350320701503c21490f442038800941c0c501000030401000a49181140c190b4800025604050183e500103104200100c1d1380718000181140d240c00031142c1d034007100092000a03ca464030201c0c000d401032080b52040c0a5601a2454031000400038080190301c194103000d030244162041c030641011806c04503219210380d00c1400069540855049000c14a00d4084050885641400c0320580b011843c11900580005298000d20100d580145865045400c00420244c0b0041c103402040c801c0384000350025541c140880d034800071079400309900c80403280520506d404c1d4103a2544041c0d001360801c9000c00d40700c00c58071080103100d0180310383d0203940580401000300782c03981c0640011f04000e2047c0701500c06011540060307071074444240341a550458150b5940c40c02d8a4039000409c100c3d50854200d118545400b80c0c4001c00003040109804400e004c0d021084402144440b41c0d00b1401c411002e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 969954172 1250 969952922 969952961
    0x305070908070803040e15150309010b01052a240405010c0c030503040602130f1e05010f0e060c0f01020417060f060d061a0301020a020c0909070e18070f030c0e060919 73
    0x201980c4055840d0288234024900e0390740c80c14051002400c59004180d2141845000d203c004a0141c060000fa00303841c04101c90440c0e8950b600c500e4904081d080c070500010b0f040c45050f030301204d85004042c0d81c0b046205000821820b0104002540c014400c036800500080c001c0000a00298698015080b01c0110200e2a10507640b40c5601700140283d0307801800d0140c0581500c2e501140c160061400101420300707100352425902c8000500381004801e050f8014400094228070f01c060410020b900130013102c008540711f40c0c50720201848031004801c4000399200e10f401068040c20201051800b80c1401000241541c055a1b110805082d04c070b592048400200300c802102c0340c03400e000404190102e035010f0095114a0030030003503800c0703003e02440d050340d1004506115280a200d88103402c07603d800f1020503121018241c0342d15255998010040080d0700b07540000422030024104401d64406902c10300e080d588400500080e450111141e0354404010b0350f59520000c1c07290310601c00d401030404000b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 969955422 1250 969954172 969954211
    0x1d0c040614040305011a01120603150e030405150a020f030c03180301090f24061202010c26071101050c07060525050724080106200a030305070908070803040e 69
    0x608440031b03295828040d100c1440810b00c150381c85000e1000900c000300f01000410f0031034868469410192070031404082c1c2c0e82c00500c0c7c18401c1001075400800c4010300b80416844481c1403100d181d00100414009840307480c074001d40050001c0240c0f9a000c0000c0011410301c003031900e403504441e14080c0340c0f40d01550796800c0b41011643c0051181c05041c0a20101c140c5c0901803001d2107003c10b42110520640c5183c04130034420100440c000c600e0003902480c0903e5000c1c20340c00e100d01d00d01100310020141c00e1001e0100140400290080c211700780c0918102010700388680300540b098458403041070910381000505000c803d0045010b8605010442110380c14a03004071221600e42100c82021764480e4415281000407242202084400180d81c1460400245100342c0c003030003100040c0524030920010002420a80100c429481d01c40203086c021070341d00b060941405402460103072a83c0b000102c0100c40450308030700000f401e004542203940110320700b600e8821306140444018010350214610321002c407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 969956672 1250 969955422 969955433
    0x270b190203090d02070f0501140706020f070f11090f0a1523151e0705030d090f0303050606041203050f0705070e09010f0501030b010909111002071d0c0406140403 71
    0x310b1058071504020862944910400317490102594410700342c5417102e02c0144004e9034004a004030304482c0c6d0030361603142c100301e1801d14081e00440e840000c0c9400003103901030030f01020b07003030091055004554241c0345103407090074403040c03030002c44481c0400200d00c4082015000e280c0c0c4404909044611031400e00d0380c03980828514204070140c4014061006031701e400b264601a805a03101c0e80264014600d03022500c5031710211500e24101d90720f040800030409000740f0400b88201c818042c250601006018802c3c602804460003414040d000603240c400098aa400c2590441d420749180707040014440d511541d085030103a0241103d80340b10300c1c0034000000091310030403140c400381140329504202803401c10515421242407c4c0060b8840e81080300400216142072440781c10356548030780204900641e8105140c10313000c1480b0301c0c0d8202942c1d9490000982d408207040782924800380c900440c00d840020100c10304281603543e445a1001044204207aa0042ca03212001c0214029942d041c560340e62a03a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 969957922 1250 969956672 969956677
    0x71508100302090705070302060a0b09130c050405010330021903091a120c031306020c0a0b10091d100b011103040b030a05091504060f09021f03270b1902 67
    0x20b131022807404114081015018405154803600f200410060050403800140000001810034000c1c481f5810b058014800001c2c030b1803014000280c424040e0356034910b441242511042d41c00501d400c241040c626410b82c0b2514055240012a03000700f1b800d1441d00b086508180700118202c050101801d400a1021032682017800075124a040f2a034441d80d0200d02c05100400c010801c01c0100300c204100189000300b44004040030360451001038403070361100001c5141901024000c0c000300365480400540341122a0039106842031036100f40010491108840d090502000c44610182c00003507076080d0a00daa80d00c80c03104098149000507460b45131001140c11a40f180d001410402c00c0041040810800342c029190003543c441c0040c4000750103c4089107800a01400c010906070300c0d1140f1348445481504041d204980040030f41e0403d0201241d600c40348201d01051402090070000302e06040c02c8240758030010081150000102c4940c240d8a0880d403c1c4020800e0300b000b000034802484040d402d102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 969959172 1250 969957922 969957931
    0x3110c100903080610020d20060a090213060b03060904080918041e080a031e06170c090103150e01140702241006110309030d02060109060807150810030209 68
    0x9041c009070800400c3e040008101da4001d204a10a21344640d6001504c05605110780c0703082d418000f542240261303000301c800a0b0048500c91901402064483d0b640480c07407152080f20701140c600d007807110b07030000d8420500c80ca1401101c140001400c908000d0251540b05201d100c003a450600c48500041320513054110444030f4050407401c0008000741c001c0c14426074141484001c04400780390b83c81344a548a6079650408060f01c50725540740003030243c15443d0550201107030900249459900240c510700341e441c0c0084031441949040059401e10311300150507650004104a100f07075900c0d580002400c4090a003000720742daa0120100001703104004a40100055405800400000c040e440d8030701c0b0b56440060019a14041405100e83c00740f0001411100b4034140058148003100c00a820741c00307103035000e03900f60180f07040c41d42e0850707404034085040e520001800c004240d1500c0000d0341e20007650003185100228400d40103005401040c00070761090000145a0780700b03443e070740414034400c411768 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 969960422 1250 969959172 969959203
    0xa121803080f01050114090f040b031e01060b040f2c190506040b0603130f06060306020301050a083c011b030c020a1110050d020c06060a080a1203110c 66
    0x50101ca040b8120865004040900c0c00322a4100f00e00171582c01e920031005494031490741800e00300115265900300710183c800040568a5440301c401c1d082101650701132800d2103651a2000c0860401c0942c020703107050750b100c25509205607007130261603030315100785450084410800b208507100740f170030380c0f8101446a00303d0810010349034818000401a100060542c03445182000c0300d401181c1c90300320036a0303408110003407070700f100344014100000000740c9070501600b1642810380100600c1596001141251000c1c0c2d5090710071a0355194060f25603440c0d0a1010002c0d007800302c8100c8d811061150a001a01184002500c49101e1902542164480c00d00d001c0d13016025008010029007521600140b10f8460025020906580c5d440b045840c5101e600c0718440e0480c16003010415200c0c106503280800320550131540d40303a0701c0c5032140d6186800c41d4240c2c4602c1c0891000f00b50030801061001c4180c0d0302192000d00c40c181c411040d4090100c40c0d96480402c0300a01c0700fa40103840401c2041c00c600c2100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 969961672 1250 969960422 969960437
    0x20403060b0103050901181b0509180c0907020a1101090909050601091a0a0e04143403080a0804060b0a0905041712180106032102150c0a121803 63
    0x301c005000d0720720003000540641d1400a80080e0800460f100c101d6040c0c2c042035a101440d03050120031a42034030760304070030340050040e001c008c503030400364161184040c0000115032801c0341c4141000081482268244010b0700a0009000000c40552590f440e9400505007501c0c05d580b02c0c08194201d5119200035160b59004d000100070f404241d00c00d10a4889210000120314030113680400c0d1401d07190300c15500b1904900002800b44000d800c804281440698150b50300603500d5003980031044a4206107101c07805030240303043e04044211502c40c04481c0c2c8101d80074141101c008065803010300c02001680c0c82521280800c805945401c00c6401505403090002907501b800d08245e4481140520340740301410307080010003080f0180142d0594400001d01040050a40059459004d40815440105850380000c0c2002035a8800c0c408014100d0444d4210740c10103181c5000c440c8421401c7d5400c880844c410010409002e101d0600795220300c55000010560f030300c1c0e10810030701640314841c040d00080c0f0758 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 969962922 1250 969961672 969961691
    0x1c03050334080a09020406080d0809030a17100305010f020d0506060c060f04080f0313060f0911010522060309030f0c020604050d050a05010e01050a0b010c080f0a090902040306 77
    0x1101c5044040c11a1201c0c0101c54003021480c0d0300e0108625020714148001e240010742e059990b80c00610f031103680a03105020b0595a11801941c0c1c0c0e4030040d002002c21b070300720005940500b0000643d24000c11558079500140b10b41c604062003841c01604203120500c0700c51001c0040f5000740102c8a504280100c01030f84c1e8491031018400b201d03006403860344122410020009400c030b0000d0403680000c540b001404a580365440c3c42c000c240f10b21841c0308a402008010003204a11203800c1d040081c1c012034090001020301e0b101e40b8102c4000c240700074009407110780200d8840d440f41000d0804100819000b40d07800c40c000201d4004640f441d03002c07a000a850340b008204143e40035100c0030040311a03003020030b200d160b80d900140d02d5000314000c46010b0130000001034140001001803503032341c5170480d0003002001140c00e211806014200d59600c001d5042900010302540308201504510b038100464038140030508950750300d29880703951a0b0302086418400814524554030017840114810a00040e80d54907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 969964028 1106 969962922 969962941
    0x60b060d0f1e090f031b020405011e050603090714180702070515071a0414060c030103030f05030606070212030408070909020910180b1c030503 63
    0x400c10380c00c080e1007040d4416105082c81c034085103903442860310240300750703415840c00801500c3e1605108001c64820207a1392501c082000c02120700f1413076074000805440c0281c1180f682000d5021a40c101d410002c0d0100c00204030640b062030030351500c40356840d1555030320b215081d07284000103c1c5500d540d0f6000e0f01501400300519111805042001000399103d0007805001c1c05240c1d103400505008001e413080d20070891f441000e0b4801c040303000c245514160000f400c00c4950600c690451030f01d41c28144000c5104042c03030540552650724505000b00400b65556416003404010000c1c00300c50340313070300c0304680e445030301139a200c1d40b046007a0b12103610b90f10071544070004501907103401040380381050f0418000540201d81c50b40040e00c4030070360450302c00c0c03042c490405800d400100c640d041c0302464200c140c201000034249101c980d1810036214070301e00c0054040b00018000410821151f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 969784172 969964028 := by
  have h0 := BRFrame.cov_init 969784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 969784172 ≤ n) (h2 : n < 969964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
