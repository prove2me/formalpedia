-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4761
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:38:49.859374+00:00
-- url     : https://prove2.me/submissions/d116cbee-f11f-4f96-931d-25041c4bd43a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 856115107 ≤ n < 856294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 856116357 1250 856115107 856115123
    0x20105150a0e040606052d01081009230c0301080609030705210c010e0f0f0f19052503061407080703020313050f0607200a032d200703020d 61
    0x10f42d81044002001107800594114800c2c1d60010520413407900f00703000803c2c0801705083d001c2c1c0350070b0044030340304005c0c3c90004041703040e81000d001ca90790940191081071510b40015032101900d5124001003074041d00c03206400040040180f026035010f1210341d5204400400943c80c20040d0343d5140e941d5940c0c20001140400840c811022040500c4100e4a00034500300080c00400f2502d01c5045e00c5d184180503200f15840740162042c007400e400b00740549a0003206010b8441c10510070089051940c0103002101d45000b03c0700d40403a4502c0541500c0b42100f6031050031244a81107140c80317422226102403080200d4419410824103030341c01038201e40c0c0700d0402d14025032030741c035100ba21b8040440781d400d005140d4001c5044035100210001003940c45550181e40ea005d010407200d8404400c0b800e64110412140c00c01c40149021900034026681c5802c901c0c81404144208406041d012296207480c500004000100040303407804a54114480c0d2907060020305101807a5500240c28004900030080000e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 856117607 1250 856116357 856116361
    0x60503091002031306021b070906140603070c020a1e060314130203030408030c031804050601090303050f120f0f0702010b010903110a0815010306060602010203240a051f020105150a0e 80
    0x41c803811504e6240320f07400ba4003035498000340540c00c2e1031814444070780e55842c0304440000440f001c00e4050001114002119041c0e1925480705011f082d6000525450510440740311010041e01c981e1a10030080c00c000013859540112582080038804a5500100c1018244624840307025910f112064000100c0d100407030002c1c54034400301c2d0660180340d100340705501006c90001502d01c0003000410075820b001400c890403a07400c804100c1290740603144140080c11007581400020b000d0001840c1c48500315030071909000e42890303e0440c99504850500c610390005082c412803050300000d4030f0304150240028082c1e0b413800400280100600e00c030151108440701c030140042e0f2201d8501c1c0000d4032490050764103ca0022819040100c828401190304601d400f03030020b034043c4184281c9004004540058540c00060816000c1c0140880650755210023a030301c000803240d45801103888a6005950760340610098a8006400c490000b410faa4095443d1042486103035100c4082c6426101c001642400603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 856118857 1250 856117607 856117621
    0x9061b1504080a08130b0a0b0909030f1c0906060f030312140601050a1808071d070206040201050702030f07061805041a060715090c090f02091f030e03070b09010606050309100203 78
    0x71780f40c24101800b02c5916800b03110300c0c2c81458100c440103132001d96440e4240d49a06c6400c540d00e2180d0710381c0b000502418402c0c141c01e0480e06032039100715180c0f00008500101e6640310320302251340d07503030120450f009a91820410140c2003640040c0b402c3c54110108000710074841e0030818004021f22860400400040c00710065000700400f42c0d031041c0407001168102e440d0b0100e980d507101e007070145800d0350320b00c0c1d44880e2840708004401d80c03007030f150355015003100d880719030055550f50004042241d040c09020790210902008020b0745004107120750345d20180207000c401d140359402c103581003032b03003d01d062641c80a44c0190504005400c0d0400359941a41c0d43c4050600003440c0010341c015070031182c01c02c15071340c00344010aa6000d013070318060706040020300c0008050804034070810007010f0b084842e04001c00c030040d20750b10101070302e0842401c000c580c13209040046030560380569011034020503440c044c020041c1003445800041c09403800c02c02e14604200c5a4595074285061148034080d400200203620 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 856120107 1250 856118857 856118881
    0x19051002011805011a12070b0d0b0904050a060e030a0804020f0105270a15020a2607080408160e0a02090f1002010903020f0705012309061b1504080a08 66
    0x6849100422560b680c0200c0c500b240c041c1c424080380d00ea5481c1010294800744c80c1102c00260300c0d06c0d100300240406481d103402d44501c2d0b0007090f00706044030713030721304040a0780e807549442544201d1040015100b14010791400c07408550114181c00ca441d8820b02c0031103a42a0019a016040b540454151206070902801203e075489030384441d4418241403d4506c100000d41c4c6410b0340141001c841c0c1043d00354403500c4590400e1340401500380181e0102c2d8004001c14400455a52400c2d00e8403220030407010308000910413540a500304a0700d02038009820005501d05129140c50340c00c44005c18400f080c83e240103045683c10240040c00403a6000a00040a544145c800030050f03601601d400110441c0c2840603009041203c0d00b40e015000d602c1d06c1515400c0041707104d90941b40140c540c803003000300b0b01c030310300b81c140440d40c1000b09103400402c141495540c0752005420290f500c0705108070580015060681030000303004400301b04030b0440060200044040080e07440c215441d1034030b00180e9641000790f02c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 856121357 1250 856120107 856120121
    0x315150c1704030b09010b030313030803070915050901090906050f12010b04050f0a1b0210020f0c03072315160c02040e01020a0219080406030c0c150b09061905100201 73
    0x1d0055400200001000701a590031449003140300001c01c0224070840915440c0d101b006001240030000000a0000174031840156412984c2440d1000780c1d42c1c1c9031030201c1440c100340d034803a00105802180d03036000c1e5a4000c0000c001703044454014000c03035181101080e400c03604000310701d200d000b0618104004150941c001c0c501c0c02001401400710b0f04001841c4001d0800644080000c14141000303402d40c648001003c2c6440c1885900400513090704003c564000d42103503469020752142080380100000007000a041c000d4014100704440e0103409180c090941c000030b1101a49410141d00c40f4481524030280b6580314031889508141c0c008400022190b1601b05007000b5805446c00000001c2a0700c154007504c40c2c5c018540032500c5185290580c07400009401500401c1d04400b008144142c5110340c100291310b8895080400d9041d8150303581c2e20300b400c494444405450703600c41840c0d2031490203100700d03130300304da02511070507250007100540b140740f0031840c0109405520300082256441b4801d5200d00c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 856122607 1250 856121357 856121393
    0x1f1b031107080a0e0108090604030905040203060343080322090c08010f0812070219080d0305040b060f032e15030210080907030b06010504050d030806010315150c 71
    0x1d07a0710b104110f80030300624102108680051030701d41c00a0126840000c41c0350003560180c560114440c80c1c03100b0400a540010316550f0503001d000000b22214082d2122040525a8080d17001d164109400481f20074040e0144100307484e110380e031010820300101008a0300300d00c20b10040e402035102c840c4245040000c403a442040d4162402400c1c40d40d0383c0d400003000d03041e103008585180720765a44221056903060a143c0d01102180308000803001464818079a482c5074002210008626640d01c0120342010004603940002c207882d1820401004503a010b00d070f600000031518010508021008241d448032420307021884142c1c500c040601a0075003a00e084159402e001c81400206204030022000c015180700c200c0c0505100c0a0004916009084043c45034542200070024185035850700c0401c2d1001030300140c1403090805c004103580d02e9a11784030303182d5400b03070701d40c01140c0c20324800041c02c4440190100141405440e800c1c0074000109039007a0b183c2d141880c000514040794103084610503000894a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 856123857 1250 856122607 856122623
    0xc0b0408070803160225090f091e0b06180a0905010b060c0a020103050c0f030613020c1603110a060f050d1104080c0307060503040506061509121f1b031107 68
    0x103a101c0810a40f40140c041039083e2003a1003106da11080c504481d12540d42c0b8555490b4400f03010054450380040f42e0b040b455000070510f00302585403845000114a49000c0d070a100e2014042449200400300750008001c0c2d800700c907180b85000055902e503034094910400305449201c12010f101094010422018000f080c1036640c11644000d59500c400c0568100e000c04e003010300195101d5145000e60304203000130b500d5145103a4a0004104410f086004400f40c1c0329400d2040d141500c9042001200f192800e81c0c64a40ca90f041d810001c502c4c0400480c480d10500480d201440040d030b10140000ca01005c1e420801d0322801d82d480d1140240925008000a031078000c2000116100300040f444540502501925502034841031308a54601c001c6401030820744c8002d0104145051800901d90100c038610682c81c03d14001d8000620070880300c188080055100b01442060074011070251504071201c42030400090305101c0c00c00550380c08010885050654035540498100c4948040342c201907405242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 856125107 1250 856123857 856123861
    0xb0105090901140102150603190c0e04290601020c04050612030d0203070906050a090b0706020403140c1f020c0f0a08250f03150906060b0c2406010c0b0408070803 71
    0x30f107410890000100d81e00522a10403800c03600300301d03000c2050040d980940034001c2003000c4044008040f0041500721112350441d040010032101016640c1e004900c15004224041003607135010714504078251a443c1003050600c00d000c020307a0002203140c500d10b8140d802048030341e500c20000e100c40056201109407070100261540003101181d00440c82154503071906050142c807101c080301c5d6400340ba000740c030104100c6801071140c41ca1003405000355910036170000d840c040e201c4d17407940d07100c15040c0f51035080c0b68415965407a0324507001d1880c24000307a02c1aa03918003200103440080d607402080407258004d2003401a43c1c9819117a17000350354051b04030201210030344031158461010241c09541c0c0454010084007001ca042440f41c000c81d0700b01da41000c40f00b0035280840d01c1203070081c2100354048a0700c0b6505d000009503034100f20007500c10001e05202500c010044080c11041280151088048644280e0100a03a41c3e03000360068a06039003100f50755040c0e035924034150080e1301c10310102074094000032003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 856126357 1250 856125107 856125119
    0x1080606042c0610120f06020d150b0c01061a0d021b0a080406020d0512340c0302010506040603020303070b0942090d1211070602091810090b0105090901 67
    0x2c1c00c44d01840704880440c0d0140d9139517600e0380359510200d10007010041c0c48111600882c0c0726402130301d00841400d0001400d0000380726002d6134020070707a02c070810640011800344442e040070b00c2008020f144540001c5c0c0090180d548144c036511501c030795490502d5011450440d00d0028080400c0307905801170848141c20128280f03803405030443d2113814010300c00c030740c050310b4414498410f4900d01b4011310411412602c9105540460307403d1262500940d014000001500d134140b1a4051408007150312840f04001050034000d003901e40003041c960085042003401c10050303e001086607001383d08103a48601c2500e074485540d0034801c4148025094000134103903030729420708a0304910081c21200e42000d00c0903000440c0301656150490319090190404105840394a0041e44801071300d900b61035000512003080c117580905504940740540b1002d82c08105416203042810810064550440340c844081c6403203006894090340d0b03406a8a00340e515210300d8600ca90192050790010b6200a203a00c0c0550b031184 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 856127607 1250 856126357 856126363
    0x91a0a061502010c0e0108040609020907090f050d0503041a07082a0d020607030506010537020f0703030c0204060504050403080f060d03270f2c01080606042c 69
    0x7014058181c0a40e168031501c40e40144a02e0304040207903201d1074601c03070503040103681120b0014802d0782c00d15240c0c408000180c0d44d000761148a1039071510303840601414001e803020f1001603a0003203400b0f0341e40c0c1222500404e50010a64080740c1d05100318900d140d9481c400091940100d8100404209010661810442c3c0402c2c1044030100c01014820948401c499080c1c0d80c3d0024802085c0560400f50126198030302c640c10060b48014181019490450243c088501c8050f01c094004406544d041411303058464842140041e8546403009240c4100b465442a0b110002ca200003014860b00c007020710119211900860000d000c000c008200501d003a0a001e004040300301c0707002c40030b507020b5000a00c40e444c10416410155400d6501e00b042034501f00c202096001e0048041c0d0250400c40b140002d00314140021080a00090020040e10444030f80303d86049c0140c044011441400210041c00709040000d00c0c0b5503c20030884001c14800b001d400c884407021300702d000c0511540300603424200506000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 856128857 1250 856127607 856127609
    0x912120b0a0510030b060f1c0207080706271b0f0302010512060a180e0d05041a0f09120a11010201020f09221109010e09040201051204060212190c030605030709091a0a06 74
    0x190851041442840023400100e2082d040c3c0200040014050000030803400c1c0d01c48030903981c0e96541c106440001e00c09012003010340c1e1030700b101c0c0b2032240c0e1030400040880c4500748e0020254105204d1a060441e4006026030151410007400d20010000060b00c81c1e603621079800040608060500b45c20030481c4081c00030341403801c0003107407500c0f4404e28010814032031812030f400c890021814506e01e140c41040000302c0c0d481080c044221400610400c4071340c0d81d511082c0380c0d0490796903008001c0ca070b21600e41a158104406034503419640f0511414800981c83c0f400c9484000086842d03100c00e03c040f40f8182c00029080c00301d4078406182107221891402d03004018261071400341c03666126503408200300703c00c0c00401c580088c001401401000d0310042a262900d4115100340000350401c40b1800038900102c40403074250f02c0d54103840750340c065003441c5445406210843c0389400d000e01400c0c1800f00303581d140d443c440e403090181e468000c03000b40000300c1404101451480f40c0350600b4109030400801800389 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 856130107 1250 856128857 856128877
    0x13120311070807051e0c060a0e090a06081203070f0e030307050d120b2202030c0d0c02060a0e0312190906060b130b0415210912120b0a0510030b060f 65
    0x6450f0030358500b80b42d85e2022001810320745000308414900582485100d4004c00340c0001070016140f141101682c0f0710101911078414820000303295403500e00c83c1c0d45008460744031800310b5401081446401680302c00404926996420300001000003030000c00d145220b40704028109015040c040b15400741c1c8040f401c003546081680c14084031002c1001c00803441c624404c012100b0150200100203e1021340145d81d001c01610151030030111102a030009480080c04200c00603084031003005080c0c04507216015400d40000020350428030b48400c404e8454101414050300d11242070350442d000c08050f04140c013440c0c0c0c4024103221f442d50341c8200e180b09400c12200032140d84607000340403540e408440143d40c21a01d800d03400000460185400f85c500020000c02c04401d5804500d51031201e08d202e000e0140320030720905441d07803040000d4070000e042c2d1030300c030680319041c030309100c8021220340e628580f032415500201c465420300c41140303d0a81c000c00b414010107402500100300390101c041000094400004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 856131357 1250 856130107 856130113
    0x2709030e2d010504050a090b0f061908010e04050307140102300603010203091b0a090606050d0f0203161202041d1e0f070c03020a0b010906080f061312031107080705 72
    0x1060010360f403d00940c0a40ea8110360300703503070030080c0c2e0340f182d0800c00312440c1c040d15880d02d078080c0c80040703409603209403202800c98050b02d950041c299400400c1341c1c01003403c9004006a0f092940e5059240e2007488000382400403040c03001081c000c420750480b03c8500803001d40310840c0c1300c0d01c0344000c40310208180a012a03440b9100041d482c0c2410300840744030b004010003034440c51410003800c80c032172070782d290a040e00444906400709064400d0721400014020703c0d01d820b910307840d1070044a4142e4401601100d0f04500510610a084019000c00042e104150a000c8403941040701020001c2c000c56000c6910104a418203084084031000c0300740c05400d0034007461400006c90400002c51280c181c2d406e43c0c1d00c0c60340e9000a021103200c2c829038030800340f01c1d1068510452845d1070b0100201c0083c0c020001d41030b6168810403207840200700344140d20243c02c015001034a405c0c075114111900c000805400e00918032440c0c02201d1195101c0340d00494161880b030340f1501c0314248024990003541084401d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 856132607 1250 856131357 856131439
    0x15080a020a12080a0807020c040914100b0f010302090d0b010b0901080a1401270e010b03070e15063a1d06063a03092709030e 55
    0x804a00c42d100b6080707401406951504182060844182100070305000441c044c50840801a580354001d00c902d07079006032806810008801c00050424126540004103289000c1200c9000d80380c0d180003910707899003401c0041e01d07031140d9400300d01c02080110707005100038401800440e9030110301c0041c15455100b80da45460035521114440c0460707a030600d1102c00054454010040c1040701e0603030742c0c40b02ca0910081a40700f400302e9010416244400c3e01015980d44940c03003c4800d05042150b8001002c41c1c0e0400303e0942403415150b02a0051102c07014080c031070004070160070040003000c800b440c144a2a0300c8140507202548440004201d542c50b0620b02e040c81c00621035990301403082c40c1a074007644003070b01c0c00d51103071402c01c00a00910f404001c1c0503010700b002281141c41180c0b056400509101e00d15003070343e10f2450300605d00c0081c0d82005030740540c0c060502403030700049044131103101844440015040c0765800d003a948004c01e10710441c0d1044030072902036005005d8051011490750300407240c40f81c00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 856133857 1250 856132607 856132619
    0xa08060d0f0b06060c0a0b010512030a0e040c050c070305010204060905041e3b0f030a120e100504060f0e03091507020f0913050f011b0f0315080a020a 66
    0xc80c40044001c0d01c0d4441d45a0240c000c0340c418251180c01c07640080c54240341204580718a42482c940310700684441003180c0041101d410300000306901250382c04055880c12410b108040c0c000104003841c64010b5a0380c46044040c14082c0e01203d10408600703049503500c030f940345003d80c040d50050041b940010f01d40e5400044508090240302d41c0c2a42c81c0081c43c51402c02441840021300c2c4010107105201e480da00203090b00c4a1028100d407501e5640001d5400460426420502d00803081c100c080103a4010449581c805600185107083c0007008000854041000710050746041d01c0080c0b8101100e01e4034080c04104209540404078401075014140100c4c3c408582e502d03140e01505c00c816401c240744400c2500400e400c0801015618401013500e480d002014000ca15944411650300798a85c000a401c001070090410290071060031640090003400c0402c1c0303880b140d01d40c0400321a414844401d2502200c07a000e034115044050500307141c2c001540e610520685d440000701c0c82a400792901e1030003c260 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 856135107 1250 856133857 856133869
    0x130f030201171b04120201081f12142e050601020d0e040906020a0201050906131104050414100f240e07020718060306110310030b090c150a0806 63
    0x1100d4058445038901d4503402d01c010095000101200321603030442041e045401140750180c4080c0075070000d1122281080d100142940310007400f05010b4043c940c4070ba0528804058481040d185800c515002d1a4907070329016030a018188140000c0e8011110b01c2030002d04c254541c0f49007200c0d45888a40c801c0444003aa4007110010780742d150058006d180c000048502443d4103500c04000604000740c06007098a50300d0490700320000006c0140d4440f000e00c031012101b00b0042e0b8003c60903052300c520030149556040b04079854144498012522040080d0a00c070089000c4110045580c06440c0e0b51595144003038020006800b4a040a6180090b0194102904002c001c002120021107507141c50078000764180c2000020092030842c41020b5001c00c00b9000c00b92003a80c1904c8000011600e00e0a520b00361041d26803009400300c80c01000d0040040b5444210158021242c000329075030b0058403035020701400c01c91030440c0e007604030041d42a000c42c00541b8100074080c3e0202d503500e90710180c4a080420807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 856136357 1250 856135107 856135109
    0xa0b0109120b060910080f0a020906180a0504020a080109030c050601140603311506060e060714240a060906060c061505120a020a1a220515130f 63
    0x82c6815010000b401da080c0744013075580000042d0400046a982d8983d02c034900300700b80c00c1c0041d064100401a80450030f0910300550030240c111913064072400c6041426000010080c040c40d01151248085000e540f074500880c400303452100c0003403102da13a035030401400e03c40c2c2c40d00d800c0f10b280c442e910000500c0c4204035504c3e000050000c25103465174079021401180d8ac40b0800352459540700d1100c0040301142c10882005c44c2078403600300c021110403034850320402c69807194031900c207015080700d4040407035544008807019658000d0348540a05254601140341c9900c2c01e43c480b1060421101035507200180f0f51289104000c0e081c02449070030b80380d030070141c1920000e02c1154089034825050070000b58171600021416840b40801d102610b50780c200043da04c00c106a4000201d4101e072183c641981810f1031a00301400c5c07030440320384440d60524009113452064140c10b0448400c824942c4002001c0c1000340700041034001d296945072224078402d42040d602c03489601200b080c09020024514000c0e401c508 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 856137607 1250 856136357 856136363
    0x20a0201080a05060a0b0705070b1201080d18090f06090507180f0609030308150a0909060b0f1c0c0b1206030f0d050d020f16061b0810121a0a0b010912 66
    0x12400c0b51501b0b0509070b16800c0380b00211024011003602040401c0000043c01d4078441060003005107501d00280103003080d030070690080400c44088070501010942d100540200e4016200014246242c001036100411094101d66140ca0130711052080c510b91141078204001e55803821800c090390341d44400e00145078280702d1003011a1900304104003180c080e18039030f940400c418030200c0c00075807800e00003800c0400c00c2d04407008440d50317440c80d542808803621940844000940c2e59007840f801d1400040d01c60901d001d40ca1a0220f4441410020003c0c00010400100000d0382d1443d201c07061808081c49035030b4206c6003903009100380d0414024280000482000252503515285e00c1c01d002602c41c44c01070b611005019485100800009000c01c4d5015a01302403d170007030500080c0799144030f1035100c050842d100b171081001100c40900c85180e1494001070200d800401c1401710f241c92625164114050550408400c1000c15040003078102090b0066006800c090343d503421420b40720340c0415114400c42d100a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 856138857 1250 856137607 856137619
    0xf140603040c061103040e010b040f0e190c02010905030d1a030d05160f05100e07081212100b0c03090f1c02041a10030204051e030a060507090b0406020a0201080a0506 73
    0x20400b542c041c0207280a00313241e80c02a24030300307038440010088500c000e0780071124410000404022001e0000409070140c8034080e140003450034008001d03c1d0707000380e455050403869500d1002c3c055060003540441c812640c42400e481e110300f1160180e02c010115804d5040b000100100c0c1802246408600720403010f507940c035107904103010500d000d221a0540b090440f440ca01d08403100340030076010407515200c05400000410a0300ba001c401c40d0030000a90701c0100070b680304d8005219401c00700c4068031100300003900c0e040c007507a907480341640302e0340c0e103550041e10080d0002842266402c03000c8014080380300d05a45150808101c1030074070841544881a0041004042003200018586600801c0300302d215060001120482500082c20790880041d002011a500050822181c10110740d200d5205445a80d890707500c800c03800101e511078002c8080209103e40c0c950020303180c240545124000362440c404480e80307441c0c039843c0c040d5642001c40d030180d0100382140d002030f00c001d07007500442e0710503d03014283c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 856140107 1250 856138857 856138859
    0xa023406030e0f01060e130501020702041b0e01020f030409050c121303110705011b1a100e010e070903030807020a050d0509130506060a0c02030f010c0c0c090501030b1306090c0f140603040c 83
    0x1100e0f0707c20200421039055400300560809603446006004c0c03440b801c0ba203025205540786401500b0b02000c520524155002440e8004204d240841601c0807902c0020000c607070380c0e40d50b4444440328402c96030012202c4c04880c003846070b04001180b607030409601c00c2e02c1c0c2c03c543d15142c00030a5510380382c510402d800509401e0329090700c108004d51700f41449204010540e04007020340c0310140c4102003100c40036035070340c82d10800304000003d45030280c0c010000062a030700c2604007010014a24440d9002c090280140749006c0b070050340c4204074600c440c0d0340110540d204e81c0b501c40802030155120b092200e00c20b05a03a901d145e198a91071140d14040c40c0300511072894512695419900b403002000140c1c0c0c54000c100500c142c00e613081c0209042d6500b030317968801065046140c1060000815040b120740c1c9440c0400500019000c8003480e44c10080034407100d0552000e40c0780c44405082c0c81c40b80104945940800000d07002c4654032000c05581018400b210403510722014403c00d0300049070007909585039640 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 856141357 1250 856140107 856140121
    0x6180e1003120c0c1710020f0f1b030703031a040c020c01120204050402070c0323100b151803010e031204020904080405030a08040513020a023406030e0f01060e 70
    0x400c2c0c40b50304025003402080c0203000c1d140e036a540d05040c1c0c081701c240f04850101c503240350024061481c0c0c0004141c0110705041050031246d0140c002c228045403041c0c4009280300d0040c80c0c200c43c2c4c840074440c2d8401c60303070356024518004000c1c100100c080b21401c02107030900c212520b040c0c051211206c025a000705031020b0b11781c00458090211001c418002c560800000c100b580720780c00148006070145c0001c009041c03441c50100401a0420085072640458a40440c0f030203101007008050700c0e02021012650101031000070f0401000c0e082689011000060b070070025814101e480405204100d000b0042852103051198882c031030350b034006001c5c24a000000b801441c120300d4080e042805000c0f000d04060700c031001319180c407241d200c00b540c5e902000b0500b003144c0e01c0d0600f00405008030040d402e5051802ca0640a0340e20000840350070381da4144c0300e0350264400a14040c00413250311042001d01d09554072040a4010441c048407542c990007100d4000d80c0d50503050042908445180f100c0d0b10b2035585080d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 856142607 1250 856141357 856141373
    0x402040e0f1018032f030a021e01090b13050705040e0a1703011203030e01022104060c05120406020904090b2e300b040803010504050f010807090905030403060606180e1003 75
    0x100112035640001740c0b85a0781d11000700041d0108608540041803020310080402042e2011401c000c00203078100490680052640c035149604416086216440040301e0700d041400d140c3d1941100e500325243ca4078024111740001307585220f183c007401c5207480c41c600c2d588070346001c0d202c240503130030900c10b01228010000c1e1281e40a8000c42e6040b0000506091000b0300320101140180d640c2d11aa5286100340002d100c5a485642d420031072500f40345242611040c140100800020300240c11542c0c080f800c40070790703219504020b5880c0d90211203d52103192402c4503043d0400c1c030700c0101d051203508404005c0d981a081c844002664070381125140703800321407200d0340c01c0f0504420b0700308604a082c0c01d5a50000304186d000500440c0b14016082d125810a03040c00b0844d10f00410041001960a00411840c0004100700007a50820840882d40c00c0c1c950030314501e103200300e0780002e06407407606a001481c0d59005e0103582000d40030403001c0c050250740350403605400d0011345440c0780500d07004200f003000034401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 856143857 1250 856142607 856142657
    0x20303180f10061a03070f03180f08190516021c0b04030806090a14010b090a1715060d050d0e0406090c0906090f1a030402040e0f101803 60
    0xc0421544401c06420450307092129030840120007a444682c140100581608008441c5145110441c2113140945c001481008020450f405140c0c0d50380300740e2000c0507003090030000641c21110081c0c070840f00d031034103607103070741c8019090b40382c40809102401215101d03c0441d02a40500c4e9280c0d8040720720354080144204a0505095245206100741800200ca252086110b81e019407584845882c0480500012040007401c20001529051800803901070590405065540030f42c0307059140d070b5021001c504104010303000b51001407041003103c0200b480001d81d11604203501080d210880d00c98030107000c0d8510300302070001c0580d00100030500c402c5100744090000e000008001090099590101c0d10844803040da2910015400a4007400441e800c180207000a02180300310384880c9241240e08000d400c0042c001c460f80700000400320701903581c1c1e50001d0f4000903c681c141d80181600d00c00d42c2e0b603110840c10b2184507050411701d04080041c010140b004203c2d40580354045c030f01c2c8030300c0c82c02da42540751 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 856145107 1250 856143857 856143901
    0x3060203091c0f1707020303071413080a02100e090a2a1115091510170a0b01081f0b03010e0105130201080f0c190c02180414010c020303 60
    0x8080e007281c6420741500850b075440c031198860f81c0164103103030402403a0115850480ca040c0d2110018840c002d580007080301c2e8050250703d0015103004012180c0c3c9164452511801a41544050041401540801c070600700074803ca45c81d1084994854003a141607032400c803e9030340720300d4220000b150040d0340d41003850500c1c045a1a44400080400c10100300d46e200c0b103441000405c03a0020400e400010000f000000082000c41c1c0c0320380c5013485015a030ba00f00d050203a4840c1c41004042060000800e07110005030030f40541e04080300744210080c5070750301c050500941c0e0000340d40c070000419500104001640c5802c0b04801988504c0f803448000103458107004141c3c0540d625505285240c2083c0310b0305000301c56054130300d42e0a490034000101a4031014015684ca029080184400c14002c07808a424080c04507001ca58045d06140301500c18101008010750042044081c0006a0140000143c447c601c1052000c40304601d406c011800c0f0b0b0004503a15026178010004034a1000703c0368020340e84150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 856146357 1250 856145107 856145113
    0x81507020a0b0a02121302030316020609040c05220513021c1a040b0a14280803091305090a15020c0106080d0306050d260c03071110180306020309 64
    0x40d242c1da031001542d10880320303e40d0716980480c142c0b03900c0014209898100c0400781c40c1c0c648035980c54000032340b00e10501c4110042d110301e81c2103800454035a8810b03034406d494003c10800c803e4840c05009031180d44a007241070840350008a501c91502c07180000703103007568000741910100040440c120b0300294880000090b004c40140c1c40d2b058140302600036000850104080a840701c0c09440074030060398a0318038441e00c690210041442003038020100480040000c440034070104000c600c601d0000c03c2540f401586402029001103408031001005003448401a01c0c0a140b504440560034200c0d1030a8031440c00036040722a14001003450103e001103441105c100c010318100c42c644805007160042d6000c034081341c108803501c981158051060500409041d508148042040e80d1656525898500c6110361321142000355489600c00d6025030703903c0000304045030b90703450740e40c203091040042d008a00e51142c140041c601514070302c2112241c4100001c40c00d203520792400c1d40e4461001e500300820391a2944 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 856147607 1250 856146357 856146373
    0x1f0b18010e18010912090f030b04081b06011205060c0f0a0c11060412020405100303080c13031e050d0207062f070f14010801240c020307080f01051008150702 69
    0x200078414a06024071a0300d0041055040100180c1600c890340e0203041f40041c4801c04001080e103542c09944c0c060740c8424030300c0c1d691568000d40012500c074516040c21038414800080303010003007250210002406002100e0b2959101040d0003200e1155140340003101e441848003828042c02000c2c4000014403030719403000005010317130210361180c002d030380107210020815142c041941441d1240b95000400e03081c000d600d03d420358a0142050b1005809101101c10025071412040ea0210300000138540c40329400e103401d0031941d8100a15907000b9400c0d5800c1c0900304545900c103000040c40000c031080e54544154040d84502100604403018902038002c10b20000e0030714442c1028459800a80465903156400b0340c00e20610800c5100c1a80d525814400c03c0401489000900b680b458504200d44a6148440c180c24100321000c80b030703003440207405103c0d115001ca046440031800b041d0000d9401c000b000142d541d81110507040c82640329142150700103086288119403192640740d840604c0f801160066 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 856148857 1250 856147607 856147651
    0x9160e150d06060e06070f081b010501030303021207020c101101020c190309120221150403080a0b09060f01050a0203040819031137051f0b18010e 64
    0x550146500c8101d41e03940704070a000d204c0d0000303e011a8100182c400c03605000880d0b0b12581e224003100c4000d4403010000c220010540a02104410b5010b0341400034002c5594038507015000c1e403c07210301c1d0400b0803201000698014400541d44504000042162011042c0b440c2d09403140c410009980040795001c00504135030140030840301021001c408100e0103807101e40d08008140002c0303500403081450b07690803641c015079609505580011901000a039000c021000950300d812000b0100703181600130f80303040100341600501154825211000248520f001b06020012003a90071643c269100103c4001d12143d9482080503201c0c0340e2050044a1030180c403008010316001400c4618050714959940800804d54401441c144265000c0010081001420800070300100114011105401c050b802052503110b03040d04035070120340100c1a110254800c2d100c4681040303004000b0740c0c4007030902ca0244068100410110300281d070407102e4140750303400c28000c032005c000b01405d800b120151101c0e000030701c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 856150107 1250 856148857 856148899
    0x8030912132c010b0d0603060507170a0e0714191502010f02250302010b060a180602150c0702010c082703010e030f0715151409160e 58
    0x1400a5801107204900d15000c022030b50002001d901c110026901040c040140b5030b00c001c540c1c195910100c000b9201e003480a990381c001c01040e40060300c9a804e110500c00100c0c0c01c640c20542c0b801328180900708954070f869880d0281c4511003400f10007540001d804001807030910007025007d0600818002056003111401784003515203401880e40c0b43d5450100b00c1c9020740912400d060074104a00550401c0c2450507a0540c1d00c20300040e1111500a62410f041018800e60148550f010010082c0f0744610032101c0061000c0e000541024070201d401101050090000071a00071900e000301c08060250780d11450442240c001071001c034180702e40b0090300c100103070400d00500280500c9115030145503c1c1d8200c04409004146a503500907450304107040703403d000100031070781c0040c01100c09550394015407a115014190301e945003100e07a0702d0000b501211030240c1442004079103188a01c01016040102009040501036902810901c02030145098140c012707003400d06403040c01880c18504102f00c1d00444a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 856151357 1250 856150107 856150117
    0x1a1b0a0c090e0c0a03020d020111010c090611062710050403030b011704051e0c130e0609030f0702040c051b06070f0e030303041b08030c01050a0c0c05070308030912 72
    0x91500c0300440d0601440340c480c031544241e000803400030010701200303a002c504116902e01020303001c0c901941203036083d6402030700d04480045240340204020020b2560007041c5071810701500c1c0001c3c00c0c6060340310110b000010400d01500000079080c45211010302d00c161064081e03d55010240212445004a826988a120302c11802a10081090407107100010042400b6920f0001c4000b030582c10300012481c00904400091101050505401800c00400349022503402c451903100404200d000c1e01c164240d0061801014810100c400700c0d200c0c403103040c3d128060881e0010001c00709000c0e2101615264010041003a0541803c030300d02482118510410790900d04038019681c4400140014a98803400e01100c422036850036100c120f5903280025141d100240c0003914a070401d074600e0b451401e140e00418001c082c99400c40f0751f00d02040c8078003401f03460200e981c0780360a8500038a040d001402207081c2d11216074001c024051a90550f42c84510f00d4001074a00f8000c1d00c50035001c00341400004000301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 856152607 1250 856151357 856151363
    0x141e010e0d061419290301090b0c0c211c09021c020a0602151518070305041203051504240b0706050a18060504050c0402030a051f1a1b0a 60
    0x108107031404280200e41d081404e4403424401d8503210480e501e0500054800d04406008000800c18607040b00000e4050141c00c4000342c10200c0d450140b100e224003c50003801ca6403c440140d880111030760b40d02043c20000c2d00c0d01c450759440c08124039004071002e241c100301e0502414400040c07811103600840c1a000c07021618940f0790140d08a05003d40c604100e0b2003004014920081550b102d483c0c0e03a031318099030098010350754506110707940d000750356400300a1036031000002103482c82481c0111f4014040c010070790b400d45900742c0300b10903003c4880c0321f406268411300e090000004440a564180401880c5049002c02d111490011100301c5100e20022940240701c103208454a400a40c18204c0407581c01030491f0381e0252500e2200d01000ca20f80345252803940c4c100c1c0c00010140e0742d80c01c000381410025800503034054400410400d011400e640032900810000e07070000b21080005040840c81d041d18020124681d8a1785d428034400807940c0c00070445800f1001e0041c83e802046030a2600c0c05454160071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 856153857 1250 856152607 856152641
    0x1050907450b03060d0f0807170325080112060f0e010f0e15130c08060f090d080405100e030708130303080a0506150a1710141e010e0d06 60
    0x810750040c12a801d401c0500300707540c20a0b01c0c3d810800d0011701e52220110000b00000f54603510350040c0004c200c00d85d10001d400200b00071003100300340c1104440354011164803c0080986e0f16040070400c1c242101884504a40c07140e541e40c1c1d080c07048000601145035811a2455220307980610110b4880c02040b4416010030008503804401c0c000d50016601c2403a40507085600440d0303504822006c0d4040701d60021524186005c01c0360b041e00302200010441e4100d00b06510440303052099241c052100741e031213070102c0070030369201c0350a42da400c40341108252009089036101e184041020341030399001c4c1d80c9040f541c50489260140350fa60720303404d03a08035202e251044c010542c03007002415041030105d03034030098a1804008a20307040001581210b11904c03000e014040218559181501a0015088180e22089a00750914001200d407440101d0313402000040c0350101021120b9083c0100480e80c26904081400b00e0350012500440d80240017018040c0d07c00080701a040100d902c9200d200007410b560030784 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 856155107 1250 856153857 856153967
    0x613110405012c151905092751010807020d0e0d140703111c022806050c010b1203121008070807170601050907 49
    0x3d405184518a902210001424030a5884480c01c080000c140c034201d410454084090300220300d43d01403c4401c0007410118081d5094850f00140a09490401244d6002c600101e06058422041d003107511070084241801c0070130456850045084e9600c0020303607650703a00742047e20f801c645002600f21001d510303900c854501c80f050011405c580000010a080403155410540d00007541c0703144002a80c0c0800c42011000840d6944080c8100a00c9801c184a07059039026402c072580c89030507911045131813a0f0100468100f0781401c0084c201c04904548011000b6440d54083c04030550841c041a0030651241c0f00890f0b0840303030000c07213801510b06546c445480d43d4240c249035085802408c0700310720400140300747c8030300701100004807081d480350b00b42c1c000c0c455116420b40c5006000650429a110b005401c004280081c000681030100c8031000003a00305511a101555100c10003030080f2600070514400041e0054041c28246000452000c80d0700218070400000160100ca002c50101141d00c4080c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 856156357 1250 856155107 856155109
    0x10f0902040b0301060305030f0a02070f0b0a08060405070e0d0f0b0c0406080c090607030e04110412020f1f0813020a0f17120405010f02010e070f030209010b070f020402030613110405 80
    0x1107807420200b070a400030014039040d902c03515a00d005a1403203101e50f000002d00300950520070321003038004007001c561203845541c503a00d86004503080800c802c0005003c020014a5a1400313018070780c000e59183e00c1c1e400030800e0113814400028800e08080d01d420400d901c0c0140050782c0b6010852040d08072240182e00c49090800051101c0700280101040b010140301c69404c0d41d680e4801c031a01264181814465814500046800b07400c400703202c4282800042000201c007075069001e90003081c422188541c0484881040200d205440c910030000203801454032480c2c0c500901038250455a024040c25040d0301590003d00017107225084403200000090081003c0d506181d4030031001b0a281d00030704882590330210074401e0007981710f1107040040591381c140c8064000e42c080d01090030003100340c2d10082e03190300020450301700601c01207004010701000007403094950400c0e5410b45522060082c5075403030b55020400039401c003420055103e01c09005801d040f102610954a0484c100318005841c2c0d4a054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 856157607 1250 856156357 856156361
    0x1801060503190c17090c0d141501120807051207060b1509010f3c02062a1b1006090c03150b070c0b03132003060f0604020c010f090204 59
    0x207400c514024100b051000c0400d0700260344c4074290302054184501a0340e200c1c051440c040180f04c40715002482c00740d00d0002e00200f580c61040c050300307290482d803c19074007000c0380905c03820921030110703202c1003e0851000211500d000b4a82e45001c0c40445d07400300850b4900c803450b540004001c40d1919515010030f031003030501520b184424407250020609049980001070855035000315098104030501030010101c044800c02e6004550b609020010100081c040c0f050301c1e5442c880c0f90308050300c50200052540140700268061440800d87d580d43c081c840030b030f0002410303001070680100d0022103030014001a1001c00c18400031300516070000c0b6900f407500341c1c150101c55480160400301403c04038404403042c16800341c1d0382210342c1800d40658070f45150501d0003911103160801144a000082403150003e900e0034407000c030f40d00034040704540b82c14a02c01810102403405416400d9007003d80050182c06e503040ca0302d580848090f2000d881d1040a11501c1d0854500b00510882250790360080405d500b854 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 856158857 1250 856157607 856157641
    0xc0e150102120304030c240212150306040f03030509030d0c021020160f08040329160f0e030105070c1104050121060f0504141b060307030b1801060503 66
    0x10740d0202d0729505154400400c2101180030151603079060124003040b60301c0c2c2c1540f4041040a0b203108640390b91100464800b41c03c07040c1d800612501c03204041940a1a0200307040780907036880f00030000b0441c1030b0b030343c15005004014401c0c00b071070000b80072818804515024200071585254050f142c2c142d03811090104036480424020310071909654900340703845540b011a0010380500061f00805082450300320390742d02005800409842010a0010070020305003006465017410410440c80c50b01010000002000200c031030001403140e403040c10942030f001c0e0081c08010340861410351201d203925000309080d2041035501300d00288080c480e090500402240c401d0761810110350034840395141050011481909015500184080116031820484554000700d080603c0304000e00180c03a107800d0040840301804503401040c00390f0740c04c14150b0140100c0c43d135008280105540e0464841c0d18084ac001c054900740117070000107441003690f155013001103082c000c02160b0307117a550f42d15240b4921074540e028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 856160107 1250 856158857 856158883
    0xf2615070f0f030b220204030c0b0909070f050403030c080910090602190803010501030b13090f03110a02030d0807110613020103060803040b03242706030a0f0f0c0e150102 75
    0x9840100100341d0f0303803410303003856014171246562420f0500c000c0c0c001c001d00c5503a00007011882140e41c00908170060ba0094006004115984686030387c0c0c8002c1500d0b5501800d00c00070005404000c00d00010380030f0a00c0e8107090307026600380d90034500c450000c5500d00c03525075112004150b041d8400c11100e6030400610300f0b0041c40c840e1000e0198082d542c1e1035828081806503d0506448800202060b1509101c0340180801c0120520018070036041c0f0050096449809800180d21448801603a00c00040c050741c60765805030082040446440c0c01b1510460046d00583c200202d42c4607403441200308005450060001050b05014410b140c070014040b200356900942881c2c00900040028003112130980b98003c08410650040c0880d6050041c00c888151503c9a030000100b4210800c5040b42c05000154681c500d51101d22030719120105a1f80722181d49004040780c01c15119080024180b200d4015254800c80742841c0b040d4071001051500c4030221000742c114080c410701c5965640e4100011041c171a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 856161357 1250 856160107 856160111
    0xa03050a0c050c120f070f0c030c170615030c130b1c200f100f0305150a03020d060914060708100f1e050a1206060f2615070f0f03 57
    0xf0041031151104000601d030703204000c02060016603070070045e045a01e8142e002090060009003450b20034070300f2503280401d0302d43e2a12000e01207040401d0010b4a0864091040105030503566180d140e078100a58008864060203801030840341e0f91600d00f50600300071702500d008110241d1039024041103003041c600240d9900700002c0000003191641d00803400c031b458400440d58148102c1404160b070441044c403082e41104d81344403520703922980501c0350b140701c0800b0741c0c1c00d11454503425581c0a400f00080c1506501c2220980100010700d0201403072039009106003004500f011054960890440103595958200e030004401c00c041a64007960742948000010615010f82c0d0410a80f5403020300103002e6806440d0109461070a0205c443e40484010200200801c0d00e00b52150f9050484030600ca008440341c1341401c6e8040b54003020211344200741d174803000f861564009410140c50b800c1130840c1084115018054a1254001c3c4000cbc80030720650250325120806800d02e24000c3c54000040d00841c2054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 856162607 1250 856161357 856161367
    0x3080d0f0506041104170c2d030d0f0f1101150e07020d090e07050712050417011e0506121002120703050403140a05270906010207060c15020f0a03050a0c05 68
    0x40c0c085007618140e604002070041c0c800d1040403032600c1d084005503010b40c031140281850b00000f60b0354080038070064923685102c041c06110301c00e043c0e484140c00103034004640001c4402d8486c0d0b210b0901810310171224904034070b250003021940750845a00c1c2352114018049444c080c8000c11060681580010051004124030503400500420505640c041d05c4a094116400310742810b1044080d03035040b64100340c040701c0055580d074024001d42d02c04e100d032140d0021900d4130b4191000041c402c3d00c01040e8200d000c614225440d40140e40280302c014079a503403103070046803c600c40c075070b040140d410111035074980140e07501d20150f003280180c40000c1950040505020030007000940c810b8088450102d00e006003a02c520342c0140c1640c09004240242e010f005a80e00240e90302030010803800030500041c0c0d00764005803a904012611106d8a0103028081001803101000041c40c0d08510b20414400d090014184040c4405400781da601c40f5500d0380c0080e07154010b0000542c00e0f842912580c16040c18000d140c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 856163857 1250 856162607 856162631
    0x7050c0603090706080415020a0e0a061403310506150604052409120703060c02032b0204090203070309060c1b0f0507120c08010b0301050106090b030a0603080d0f050604 74
    0x83d9403500850b001c2000010201d81000101c94010b062141300c1c3c0e000b9903e40030010001803110300035100c864444c01d45040700140c400d0051443c4441c040c941c50000b0300d1030741c03002c1c0c0010006501181d45100307005150800900901e0000c0b8103402180704ac0d002c0c2030f081c2425035851025403056168136210300c400300801c000c50364034400120300300008401a030950014903110240c65004c2c01c130205800409500b103410041d00085400c6c0305803071181c2c5c0200b00340e41000b542240c0d213025040e03180204c0010001413480d200c000d10001d0501e9003403058054580380e200c18000317069070000d65541000c05c1d11460b030401000320a00035128035800d1854501018074807024200c0c1020101080a00701c403142c00300a0f818000305200c04000742151004e0207000e5070281c40c008802c6207036407250300c4055103826000041c3c1e02c2c040c016a03040342c0c0315907202138080307052491203104c560010b4801c010980c0c1d075005c000001041100034250407030390380c00300040d44c0b24440700300401c3d280001d0540784100d241c00c2007010700d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 856165107 1250 856163857 856163863
    0x30510050a0905060a03080a050702031209091803040b2a0604111302070803070e030706080f0402060309340f230310050a020901030b0d0c09020d060b0f07050c060309 73
    0x2c4580c00180859641c56400124000700e05503080500306000c005803c1d00c8845c2c001c8010100340c1d100b1b030212400c01c0256060b1404500034811803691008540c40400d040d02d03c0c1040c0c2d0406e050030754041c1c074a42580c501c94440194003007000c415180c40300303549003000f00c0080c04c1111060b056210280880c0d1915680300c180042c1042003944c4680c80200100c08042c0281d410b803802140c0c82802d00d5500e042c1341d000a00309411aa5540b80700303102d03086001c80d155104004040c0124104075452000340c84075130810445400082c5144014400e003101d4404060300d8400302c0c040d810b00c111060281d003814021401c070038034240e0001120390841040800c13086035030100301c80c40003109880c0c45456003c03090000b820404402248400d05007008103000c4d54100c40c0e802401d100000b40c8040180b8a002800d015040f80c0340000a0300ba00700700e0f40b007040b010202d9002071070501c61041c0e0002d215900e540d1001d58a81001070204c241c0d03440450380400b0030904210862503004200e4110f42507103000300815039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 856166357 1250 856165107 856165109
    0x50a110105190809010b0a0801050a06080a0308060d0f0b040c0807061b1104110d0203101401080a1d0f070305010608010605060d1509020f0a020106051c0219031a07030510050a 77
    0xc2082545030024040388130a500840001c2e600030010416160354071a524040c240c20740340080d08500d0200002076a05001450034541541501c070404240d60380f0041026044503e8070507509200074070a07450002d4111114148501d105820078231380e00f403c14503e24680301c40d642112007404034016608603040c070414416844031f07900c034850b80a071141c80130101c0e02400000e22559540a0007107070001e401d00c4242c02442c03249528000025400d0b0343c54801c80f00c131150310b807049800b18403058007154183c1c030706030481d07941481c01400c07040302c4aa600400c41c1c500304544a03a000280c009071010b200b0403e003030007503c0052002c80b0082c071407682041c001507a40e114030903081303049558869618110004000c000b00040c4112001103481c0c0514a040d03100e250700c0001c0240c019441c005010a252800071040c42204203032a02c4880c01078000d80c28800c800d8501c08201103070720b418041c0000000d2001340841814032810001401c02c0c206540301070150342001d08941402c080742c0304c051045440c0c040c4060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 856167607 1250 856166357 856166407
    0xf120f020d0219020d05030c06191a04021308030c0a0b0a090203030a0f022b1707140a0309062a0206070c230a20041811031603050a110105 61
    0x202083c2d8980b0010b245c401050200a0440c08042000c3c00d00075000725440e031160388114260b003409441003503408115250781410400c00c40088242007800d0425601620f4211101e45507884869140e16000789590003203c03001c1c019034072400411007086040d5007155003040040c181800440520340c0084c0d100d010308144201080148007400700c03858420010790542c4206005141d000d44030400c80108034407400340c24140455544684091140e01c2c80402510500055940a422101d4186083e405910110620b0101500e07202c0c04e0020605500c41c4000141d069000d1030721100e0907400340051038080c07401d41d4065420880c00c2122940d0095201c4910580c80300b042130a030303510010700d041d02003405910103215214120700f403000c000304001d105084408091a00f011080030208010548240c18460a41c481d40e0070032440c0003032800010b860f0b0f07800707000342928a08080844920480c18050b88181d40541c0464075171024000c1030000e0000c00d010a00e000c1d0b00c2d222501c100d800030010f01000034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 856168857 1250 856167607 856167643
    0x3080d020715060602061b12070e0d0206041410050a0509040b01170f01060206010801200304020d0b0c09090f060d1211030406440a090f120f020d02 65
    0x40c0c00b04000c91000c000d02076001c41c402c01030ba075203035480299607280c111403207c0c462451074040f00c1000e000c84203481d0f41c0003c485507a20246d66014003142d52407100003400b0741281a8109d41070042e51128090009005211075498200b20190200b01040307943e5a152401c0c00801c00044841a071310400b154110102a10b01003080440300c4012240d4403030305648010754503032041c00d1144941c00826103a040341c003d07500b2200e8590b00c40d1503d500303c070200607440d81e500701c200c01102c009511000145600c83c2c00142205c01180340ea440b035601058044801c0c51007030b000054a00e85a15003046080c0d00101c03030f24003c80c0146400c0340407441401c09968060801d01020407100d441c01e11440156030040340190070b890304c60f552410054800c54106a071410422520400c013030300c05505040f02c2c4210101603840300d030400e41d07201200306e040f0340140020810075202c2d204140401d9514641c2c143c00c51180d0350104601518210003400c40c00b01d164000d045400103280305004990001d80c05550702201d81038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 856170107 1250 856168857 856168867
    0x2060a0c080d110a02010609050105100c050114070207060306060804030c0813032003250e0a020405030d111b0a05011119030c150207420501090b03030403080d02 71
    0x101c441e001d50010080307001d00f0700441d500d15400e00e0000d800201e005800034032025884044010640b2001d024a64020704d1440d10301c0c7d5000c1c8220700100b1074a000d4000061040c40d0019040306000c3d0072a41500560701000c2c040054903030600c2542d00400551a040c1c20030b05044c1d0780102008500c4030301410048022487c407007401903007010500216803006000e1a9070902581000010498200181c824002d02e160345080c0e0303144c03400c210400f242c0021141071003030400344c003480c090002600c0790301141d609000205c0c483e03c00301f2510030350f40001d8444915014200e54042e290000328000540701032803d014007202074544203502c40c150355007420640390100f41002e1441c6032022011030046007000001060b4203140d0000d000c008020701800880312243d15985211040e486070180c01021120a400800d01c020b4219001c00b4544040e4401141211000307846500740d00003800f0b0a100050740e0301c004110131a400d2194039a481e00c03d9002e182045d03d15202c83c081801008811200b0b5600014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 856171357 1250 856170107 856170113
    0x50301050d080c1614030d0e0303030408031f062a05100c02120310030203060c03091b0112020d1401050d02010e040f021c060303020c0105180111011e0e0111040302060a0c 75
    0x8000c54441412465070905a56103520000c05d44043c1030410740a4020355600085441c131402c1281010240076005500c0c43d120b580e180031240d8801060a54a00f00900d441c040b070010a03680c04000385003541d20000c840c450700c0c03000c659134a0100f1010700c80c80503210040c3c0000e4804624101782d95000040000c174040e810f0002c0e42008011090400240000070410100c8421076903404e00340c0c1e0007501240d60135a42d184200307031544410f940107110380d440303080d10420021040c000b00c00300382d00606d8200c3c120030280001c02c00784e800194031311869980383c004100541950700002d90041900303c03000d58081101d030300080e0641c01224200e40c09a0f840ba010400c0e01040c0b501210100c22001140c8021089001d05080090200c1d02040f001401400c0c10200b80f50f1045054404001d4a0848a000203112400640b24509421608010f954880c44007a003040105903014030810019900400c5640e582201c2070701b103401007024001007440502060003d61181d80648124141c0382c1010540d12078282 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 856172607 1250 856171357 856171363
    0x3080a11041e0905010b131403030409091a0c1903150f0806070306052e1e030c0e03010c050a05030c22091a220b0a030b16050301050d080c 61
    0x5044800508900e1900c01020304040442d9412115441c0d010049031362240c0040100748034000340182946500941845801c8200040244044005084a20b89640c0d4400001920221402a50107441340c061215042e182210810740c84040d51420910785104030f0b21003a002800e000d0203004150780e900b0131014403803414034a080580100140100c1403952400340aa96003030486210b00000d0502c503000500b402c25a000d66007081d00c2000f00b4126030540c4600380c081070940e802290810840c07100540134240d181c003002200c2d007507a990104280c204110007030925034114003058080da1411040183c0c4940c0402600c016900a183c616529100c0051001060180d502040c00c402d0040160621022100e5611002c883c07000c0c4080c4030a10942052150703441c500b8840640050b000707a403940d60458181c883c0c59904105034000144583c0c80c00100e01000c8941c0c0048a110f802c0c4818403403902c400d80040240040c05103041c2c0e10355070508012600e031842c8242e0050000002140008020b00d080c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 856173857 1250 856172607 856172609
    0xc0201020a050312041b030203030405010c06090b0115110c0303043b0a0507030b011403070311030109020702040506030a030c081c0c020a17041a09210d1b03080a1104 73
    0x403000301c2c0e46400e00692604514a0301755800c5809012540601c800f4000804110048a80003030145052515080042d2142c400005e01221166682e40381c00000490380c0c0100c074007904501402d40001410070344080e143d071060301c00c5450540d000220b00c0c2802e0340c00104440c00d44248250241c00b6400100c0314041d810304c1486424440030196803540b40e031651010f201440ba03014110148110b0f240d0381c50944c11a00300ba58900d00103a228107110710620030030b600454000d8101d00d00000e89403483c0d0040c48c8590001e821480b0702503000915107045d403a0500844d500818110042c203010340b10356601034801c0b246084003c144a00111742d070f1400c50071207000c041c150824000c09100800350220000c0d00d038620714804072545546400744510001010050b41c040d038007504201d40c000d00c50355030a8210f0350031546c41741742c2c040401d150b0740c101880702422400c0040300000042115460910004d0314040d0851109032100c1c0085989d180400d070b00950244d00260404000601c145500440d41f07054451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 856175107 1250 856173857 856173863
    0x106030b09010b0a030e1507030c0e0306040b0709050d03020a060b04022805160605040507090218041d161802070305120402280e0f09062706010e1806160c0201020a 72
    0x140c0c80220106c0710b0004441480b070581c654042049d2b150345001520008606841c0e1605540101c0c00540011151801d031604065941001c007041583c5400068820211403404c034011b8101000c02002c1290302c0c01420140e8804680541c1482c03102c24120510007210014076000902c580b00c808021805a030407100c080003400700d04520384211f0f0519101410081e04d00700c6041c450000006142103a0b40b09881507404100242055034000c2000c01015108800b0300d10304149080419840d100d0007002400c45c03441d22545590052450030524118030314024a160804500400030f20380083e42c0442103401030310b030042d042c01c0c89413960b00114001d100c4000c5c110451035010400e001c19a1000311540007102c0c40b0018981c800d64810000f40c5e85100c0aa400e0000d540c001c001041c4640b06441950034a028a050000005520707612440d180c070001303030b0044802c0052035040c813565046041d600102145460010500c07403c1030fa030720102000400700c81d1801c10802107555011a842407104490f0250 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 856176357 1250 856175107 856175113
    0xf0936180b06030f1623040e06060a1a070b0c1923070b040b06030a082205010c0b150607080c0d1b03020705131415090106030b09010b0a030e 62
    0x1046141100d039281e030603030b80d0903c0b074403925108140400c4002602d81500718034000181000f481e00c900b00d030301c0720381d152620f030b407040c01414401c00b0036200c0b4070800034040034071402000b00d81040c0044c0f14250005411010b940300300d03031403602c105620380c000700d82001c5e0340588054003c2c0e5405d541210305000300c00c10401000d841034100005250b03c01d0514460106451081e030259040e076150304506d01c100c900c002c0500c1003450004012907210b03254142c0c0f200740039050341c0703800303c0b159078420b0140d1009445071081e52000a0a400070690740e490440546002e003820800c440d60351f21054101e05009001d00c801031006000030f082904d421041e40d00300c40d8040f50880e11600b2016000307480380c170b41080d41c038002060b036141c1d104282000d008400b416505034000e0500182844140451107642c2c04001c402d0a840380d40d1440b0881c01c102401c1c3c4280101580461019501c20805c003000300d069011f04c00701400e101c5003d41c155500100d060445222030b00d06507403102002d2003a80a40b240d4452200f50b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 856177607 1250 856176357 856176401
    0x801020a0804030906030212040609170a030c090501051c0b010e060414120606060304060b06040302090103050a1505071b020301061d150409030c12140a0f0936 70
    0x140c01212042c0114030035264010300d280c54800c100d08a001d050001c640040d8604049000701c0c03071aa0041580600404c0c180b0148041c801305141503034002c024000007c0d64400c1480950303513000c0d15000261500346070030740c907180076030500b00040e00ca14400c03101c00035031b58406000a40c0c05591000941c040190495032259600c0c040c4608800c45060300f1401101088102800d560000c10800d11a80e40189002e0558445440b40b1b40284680004990400d4042101001580d610f022036402103100d42c004180403e0146407842520340500c40700e400701d038204021b026819411050880d54000090300e100203a40c221700029016000990004114203107420606580c3c400c07002c500d034840d10740c0320401a4072915040a01c0300311401d1120242c0002c039010b903204001002d8080d412442c040503d0190020b10f0515441181603000b0380c00c05000c0b41004d4882040a41c0064400c00100501e60f41c000320100d610255051404414190300841c4903440070001c002c40c02c0740d20001300d01c0c81041882e0b00030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 856178857 1250 856177607 856177627
    0xe0106020c18151f050904150b0a0c0f06090c090e0601030309140109090606020f0d141602180a021b0a0203071a0c010527010b0d060c020f010f0207060c1103190306080102 75
    0x10386d02001e0f8140c00765013401d604001c1c1040c09544241241c60700b4040c41d107081407129003250054100d40040703d04181107802c40f0045480c600443c082d80707000e00018031030f00d8980107200040700c03280306a50407113030085001080465004011742c001c40ba0020711600c0c2e0089030000403201c00041e03030050511720349040000b00e2055400a400019648400d013101c0d00c280c2d981d40190707200c05212880c91410756040000ca804102c00006207089188041c080c0c4000d02c0088043c4c80d0343d28421198110f02d503501150f42e00619072200811191440c1c10006080f921900340c01098071180f00b4003c4050114a10a07420510b400a00c201c0e0203c54a03a0000c10a500f4086000190070784900803000c1102210301c025081c80c031041c8280144800300070810f074100031841d0345820141c03507040160b40c04d5000d904071054103d94280240309511360700c1000140e46036160701d4804120b0b13011181d0a82084001e081c3d0061a5100204079101c0706000c48030010a468a00342c220040d002c0c54000ca810355001140c0c0c1c1081e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 856180107 1250 856178857 856178867
    0xb031e1009060b1c0c06051e1620010509040203060307150f091502061b09030d0302030a1a03030f03040c050a090509071a0d1e05010e0106020c18151f 66
    0xa109040300d03080410b188418220b200180454800f4008a105c048104011070040f8000c0007800e108554600151a00b8010003101d80c010005500d40000415404030400c4a40c0103103c04618486c64200104410480003d08034090302400900460740007011600b41d5604208200081400c140c400080d03800758440103186228160300400444d0090308041041200c0ca040001102010b41c028040c954418903464480300482d1041d070170501003000501001c2e2800d100c06400c000c6981c40140e40e0f802c2542c402e07070491300402c603070001d40c001442c00307510156004009c0311034030b1400c0341c8003c1d1241c84604100c281c250456110a9008801c03c40018242c04540c000621842010080d55445d0760341d00d00c444a442c8029440b00203140c2c040288522403603c0b940704144954003600d540c0b600c442a0a5280b00300e03074003a085400ca0702c0040004100240c0e04021144074400240ca071031400000c000c5500d002d1100240028001c4181142c000e02c540e03e4100702e040f00c200305540040c544800b90500505 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 856181357 1250 856180107 856180121
    0x1c111c05060103022503030f02030c07050708120a180e04030309140703151a09010306090b0a0b09040605040821070f0509032d010603060b10030b031e100906 69
    0x401a04210014075598060710a640fa14a951251104400d0b410100c5e034450900c0389400301c09040e55140801c0303001c034a62001c0c40c03003004c204282c0c82d942d1949081c040e16181c0780b58480141c80d80041100505ca400364002d07148200f0660921000010601c981c0c81c40b10000c68000b4450030104c84100400d040e40341d040070380278a00440c640302c80d0401c0c0c460b54a488103101d020103000000c0c80e141c2481421620341c040514003000f456001c0000081c1c5001490060702030b4000d541d500d80f5640800107001d15195055040340e002c204c20801d80607400081001c011b8000c01c0906907a54a100150511520000303c1c2e54040d1500d02d000e0303110540740c60003005940c040d02d1160009080304030081180340544200c90700340c07000600a009005400f40580c1c0d0b00c0c02c0210100c01400c5015150905051003402113001030751013614046450050740e0240540000b0007420101050300300401c80302240c4009c107415401d041d607210a0b5002c0402c1c201001e1070301142945007544189030511010601030030f50712100d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 856182607 1250 856181357 856181407
    0x81b0a0203091c020f010f1b0b040614010812070c08012f0a02060c070c120b090c01031a040c03110d0203010305010b0d02060d181a06040c02030f1c11 66
    0x80310b0101c0c85160303c02c541e001d10000d420505510324658558090b4480c1c009414480c80c0c01e2a0b42d50309643c10500c0400060001c841d084050300c00c1c0020425140201403140260484c1c00700b20b50324201c0e10700d940351200184485c2c400c60002c1c0ea4018401403900b4140588a03403c02404109011b0b0626034078030340c2e107415042c4000c0e000c04140e000325a00d0002c40e092825958000c1c429600c0351119403499070300c000c45c122229019280700040b030001c034071182c0410a01030740c0c03821400d00c0c007015541d0034000842e01660416241c0900890407892100c058603103480306840020700d00c255244150010720b075121001545500114403030a0394581ea130003c5050320f02c02e1009000c43c040110500c180801400d03c000c2d842002402200c0d03500b070042d80842d40800070f944043c1003101c501c1e1203070350340c1900030658420034900c50010000760742018050b5180c000c80a00c000c2d460a0001c55154480340511000450103180c50850410800c4040d0070006640e400242c00990b0b42416440c8102c4031201c002c07240d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 856183857 1250 856182607 856182619
    0x61e07180e070f211e09032705090708090c060f040302120601030c0b0d0b13020a030509070305071a040302030f0606090f01030f02040e010f0e0106060e0a031101081b0a020309 77
    0x590582441640c01c4100b00070121140e4101040113000c040207000d07840e01c40c03941a891031344a25000030050184810150013525028070180d104046e0000c02c4602010f98242c0861840d0b040289895140d581a400080c1d40b03802c18458980200c1741d810f2400354076030300e40d1003c00442c075040d03c00c07074060082044a108407610300c1c513060650006030321050b003484054400c1c900ca0030200100c01044006101b5641d903c140010120b00b00c40008080c4018a283d81070303083ea0214490400725010701c10381e074100d00380324010b18410380345a071007540e0743c030721800361501b10210485005042c8070b4500548010b141d004041d2a003902c60742404943c0d510080b2035041c2f20300780c02400b18004c0c4082030b107164180c94000605031303280c0c5120f40900c009442641401051990f84455500910032940b09007070051f680c200011034403034030b0100010101c4002100c2e03944070343c0b010070080001411585032032202d03010a0030455013a680c1e15000182c0340540e502c070744141240c00038850400310b901000500a016044803a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 856185107 1250 856183857 856183877
    0x1503150e19140c0a02030d141b031b090f090a09050c100c06051005060d0e212d07080c0618060a050621010e0c03061e07180e07 56
    0x51002da03200071000c4040066100007264a0303031032200051003040f0450049038a80243e0382c089400315441c407034800c0c00401c0c40005001c0c0010305805110100c500110000f0b041d41843c07600402c1c405094032015503140300c0001c03101c0c1c0759116601c900c0419032008106040034a81b6500ca072000d0308000100b1a0f045c0100000043d00e4680079000c50000000382c0e0742c441220440b0b80d60038000745000741050341802583c46000440342d0b104030090401400b0110302045c00d808491843d8034003002d0481041c0d0b0f007800b4024110107132042c0d0080d10003440101094034003100080314006690741d86043c2882184d5400030360f403002c1c0321404000b045400d14000840381503503107a0555403d807010b800e0281c1d0b0075810903004104160440c1d0021508000014101e82d585422503042009040402d850001642d441d8100c515070f081e42448800141e2500f54040d00062602c003003006500300d180d003551826030b5080400308100340c0c0f042001029900d81e030f040f11a107554a8641e00220041e040b5202030000c2d0340d01031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 856186357 1250 856185107 856185151
    0x12180f030706140d060b07030c03020f0712060506040603050f0f0c100c060f1e060501122c19200d11060a0c0204110912060708011503150e 61
    0x244103422101c03140d4860403801c00e0206001d100758000f18000c802291500350101d101241d41b0018030425200b512030303c40c00d482c0d44c50040d04040c0b018102110703e8018038410400362024082004215a0203140083d041e42e644002500414540d0406030180c8030b00034440a4243c0006000001e40075400d00b100c1c0c00c40c0300002040000b40042410000203035503400d10350009202501320b5a4410030829020910810022a2408041410382415865500c3d100e00304841d50b00310b241000c03110b42c0c050b4140646102020104083c8440180d00407421402e10008a001202442a1816040305100980003042c0c20306004581190800c0001c01e01402202d110300c10b071410900d000c01d050ba02290702e4111210140401105401812418003485110005640183c0c0e6a20031140e680c4060542e05480c2c850310702c1403149900070b580341c02406034003680074081c810340c2001c0d03824111043c94076100c814003107403202140680700344660706141e5814000b0125a800c0b00c000d1700352203401c82055070741b030303aa028007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 856187607 1250 856186357 856186363
    0x6030e060108010e0c0108061c080406030c0e15131205070e010b070b0f060607020919060f03080304020609060904020a030c1e09120f05120306030c060a0e040e12180f03 74
    0x1c4d628241d0048104032241e5002d155845d038451382c005c0040301100201c01440c004a02d0a031030860b48000002810711800d9094840c8138440d040a1400680241506001c650030741e120034510703260b001000c01c400308031244004d20341c0082c0035120000054803e840c40c0c501d642d14024000d00701081803050001c18810b00d0307501903915280c2c0108404200d91140206600c0d04000030b824560040400c00030388015032034030190940150040803035074400044011902c0101c03809030b0040c000ea1000f8950410100d401601980d07081a0125201641c0e0301401e8001031507882485002500240003041071aa0f0390303055881848100c800c0d03103400040c0c4450a642103001c0407085803440215030b002105209050b1900c3c13110440c00d2150101c0e004544041e1121440e0031070001922a40401c004204401420103009101225200307691140c103205400102400d425885080c0500499403030004094204040107014000e501e4204042c0e41c0300c9402041c100c00351100d208840c011018070355601c0682c2400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 856188857 1250 856187607 856187621
    0x60f1810150522090303180302030408010b010f02060c030c07020406090b090a0e1b1912110607030f0806010905100e09010803190804140d0f0f0306080d03090609050706030e06010801 80
    0x2843c0c40030407114241c0c00490051040880c16410160759240309680202003440c9001c0050003a0025601e582c86c210381c02c3d0030b560104c0c0d030080c100702c1004010800385400169207a000908030500e00e49a07a6941403c0600d0300400b80040d40c4241030500020b1028820b40c00074801c964196030300350060741d070324807420191920041c2003410b40d48a10800d0b41101c0450000c0c0100c0c80d0b0060401004100d003071141c2c02c0321010703508814201074011540c08100103005e01c400c080000140c5440c0d0810100c1d0301d015103800d203140240f400340040c2000140081c3e01c41c16104024000c0201100000f40810000904010003885901e0048450b2400418412800420383c2e151154114400f20b080c6682d240032911004049d100302c91039008807400822044e014442c1c094a0303203195032921085482d5147c000c10803200c840e207141c1810310703140e0107118212000c140325030f00480c41e0401250803203103880d02200a15400c0c0d0007500e0340c017600c403000c0b450702d5040e0450040807203c0e074101c0b40f0faa600d40c45102c1c222104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 856190107 1250 856188857 856188889
    0x40e04021e0d144606020c070602071a071202150711100902030304030f080d0c0503161b08220b0406030e070806070e0a0312080402090703060602060f18101505 70
    0x24280d111480f8418402c42e2808446401100404c0351581d0b035652170507a003110031b8242c0160404d160901481380d040144100500c3c0da03e620000e481080d4a140800d0b100c4ea52002d0200c44101c0c0c00c03040c50314000c0086000e042c180061440b154904000d0003400340340001c1c91510b0302e01407000d0602c0303480c0080c011480c030640c004000d0352800b0310790380e50b040d25900750841c00c03209c055040c0703c84103082c1650f2249070142d0420703440b08ad0b074a10305900001ca0035072100540f041408a01b48a034034541202d11101c030700c51580300e0303002903075140c1c001c02d0720003218003829844060000140002c95442c0d410405002161032540341071012503660214943c0700e030040d00401056a1010000407411440384070b0304402e01c9005402c03210255181c1c3c542c92910707100721001d1804210080107000850a0a40050754444481e1404000c11818000002d44644002e006c40400700400c501240201d10030450181420300001d00b107032050619105441c01401000d50000b001c02c1043c4400103003800c102c20107499032a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 856191357 1250 856190107 856190173
    0x1091a060d0b042d0216020a080705040c0c050a0b04111c1506150c0317040f0b180705060309030d0c020703140d0c1b090606030f11040e04021e0d14 65
    0x1a04c0e0b51500a410500031400c2032400c0240d064050307100c8040a0000c1d09900300a42441414a024842511a18807404080081c1d1207000d0011440114804541562000d801112519203041c0a00080300540806910081d0f100300c0002e230528000d02440080d00c10000b66000c444003005e04000c07075800d44280d00b41014490707000410f151081c007200c14071a00c2420005200e40004201050451044508a54030080c00000c0f000303001183c074415501880107006420000c1c0000d8400d91250010701c9454002c103030100200e11480c00910a44207000b121000401800143c0c2c0d1009641d05460300c01075412116540f002c03008070303070007081d550502c960076140c0045400c19540c80048461401c90301045600700300102090222041c00303118014440b6a41c0841c54580312241d400c00c551818204400c4980304000c10440b4000130b45241c1c2e030050301196080c05010303a120a0390785a030515241c40d41c0c0203032280020340030803003c800040307a14414441150040046649000d02c0c1c0c00c030034204032050751 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 856192607 1250 856191357 856191431
    0x20703080c071110050706020d020d0f0605060409020a050c0a0515090102041a0705010212010b03070e010e0901030323030a050414160e180a0f02040e06010b0301091a060d0b04 77
    0x4100380d40d0044c88a000c61030401d250240b030361150340c22030700000240d80c1764940000d000c6200c03080034043d00bc480841d40e042000b400b807030a40081c0701c0d441507108003c01c0300c0e00030a8418006000c2c40c180c5408608100030f03201c40c0100c5140640e101d0029402d140040d20f4200e000c82c41c525014401d1310103903a4040901c80000360103842d202c0b00b503001540100c60541d0200032a02d100804071061134000c1144062050716401c0203480900300081c000500f50402244041c128400c1c1d82da150462b0440743c141c00e20021121200100817148003040945040000c000401c2c0440100c0c103912851080740035003c90a01004200315080c1c4510190901e08040c802000b01030010103400c0180079001141d03000010f818902080303a0385c0c140722b06040160f82c9580300180030815800d0500036000e0100d202c0026251540c14000c448609e800180a050b02c0c0702c0e1b0391540100004014503c01080080040900f51560141200000500350340b08809001d00d0610703000b00c40f0040c071004807944c08d2141d112409169 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 856193857 1250 856192607 856192609
    0x603151409040f150b24041418040c0302010e060f0318010e070b120717010b070f020406094a150103080c01110405010e010e0f090a020703080c0711 65
    0x1000054000c0e07074071024500c80040065114130721038a5882c0d070503a01040f80340104c000c200041c440c1d501e84040c00000004000486030401c0700b1a4242d07074400da03c440c1d4003003a90000c03420356042002c1e80100c041d088010300c0b00b4003c1e4805d0180c104c038800d03a2244d5800100d0024401140501d0003020200281400070aa51800760101c100c01940f00c10000260100d1034820a4130b030948580c44480f2059000501940071810460b402e94801d02d141411103422285a800d003507984414851500c080034085903070801c00500c51a003001194000b08103021098485c40c1800081c22181c64001e040d18801c480c065800c2c03a015810751441000541ca24881042a040c2a55940c07100d00a07031030901038800c001c1500b0403407148041c06107005042086e11405030311070700c50840303d40004500c0405810700082002e41e0f44288981c141503030038a08091440141c8000c00d040e01c54440c0301c543c0c40281c0204220b5840f4585e4050301d4210b0081c1d645107910307101d4035a401032501c90024041d2003521221075454035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 856195107 1250 856193857 856193869
    0x908030a02211602062a0337200a12020903150405190c180b0306090d02280f02060f0d0221100e06011407080406031514 53
    0x20b81901c8040002c51881c1410740984681c1d401c0b158a82c010302407103032200e007203a4100083c6900411002d030304441c10b40403002200d0800071141114910b010004005000300e40b074003a03004030003100080304012101007030754056044101c88404600803490001442e509290024100b02050641188030b45841402c1c0700860f00120040300c1040c0c3c0c580c08101d4100c442d201007009206240105044001038145480d03e01c0c240030a0802082c1164441081040495140d0003d041103654440505010030160344055019040f0115501e515000701802c0094a56010030110300070011542035844a804600b000746104164481008403050641c0c10301000440210a07003c2403400140b030b0340c1c00c00d12200c203016429402051040040c1790007059003240e01c40d0000b8100c4100c90100d0600c803d9181c4487c2c900d010403100e1242070400321103040805c010b6401010441d44991117680c106589103180d081c4800690b000b07100345130000e0725110ba4400d00310510700204007030343c04004468049418090070008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 856196357 1250 856195107 856195117
    0xf06010e0a03020904050c010905100e100e030a050c030115060504090905031603090e0117190212071d01050105030c04120515010810061401020304050d0507050d03210908030a02 78
    0x500100340907008000350f03460201c01803081b40300b94004d1400f20290000104081026030029001c2c050094030460f005400c08500d031386a01c8103945c41e410340c64005004584014030807090035054000c1c1c0110100380400450403006a1070705800a00c0b01620344182c00c04011154440c0c074000500903c070500c40c20319141c0140034060700550890303040034000b040c10340000d0500d40045011481c40c00e01041a4040038015074010030344070b00d0304254540b200040f20b80f500685d50710341c103d2801040940c0b0441d616811a030b004111007400f220410307178031559814a01201c500b0b181c0d400020703102c00050558030601c1105d00c201280208181090301e04041d9000000c2200c0046481e8042c03000521051840c0303200450080c0718240040400c41480160107003150320725000243c02c2e101c064458040c41c1d0700002100e04940c020b0750120300512903820729500344222500210f5001200b44e10b05006d259100122110004c18007042c1030510000035100c50840d1415107004120220501c001010080503a015007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 856197607 1250 856196357 856196359
    0x907090e06060c03040e0702010e0303040f06090c090c0e01031b0207030213020f19030c0903031d0a030b04230c10050a051303050105150402030f060f01120c090612050f06010e 77
    0x150030044403c1450b815904a07400045176a8005400c22001c0d036424043d500e09264004061417a50070b06e5102e020541c207507888060729058480d51103808200c20b0a00d524014080008104900b03408001d00a0150640070742c2140004c0c00d201401c1200f006808020a61009079001080c00d0352459080c4080c800380c0d04480c4203156401d000345078260366201d00411000704210061009001c040c1000740c2160401e403034040030000d003020140700182d003040c2c0d92410042584000c96010140900094800e291500010701c0c2d110480240001c00c000d003510751078000c4540d80c00400001c5050841591201b040191541c00444008c030380240e907000e08020001c48072185815803600a440925000380301180d44101c03172580d5210b08003c0d0303114600c02c40c200c2d480700072901546982008484024900301c0580942c0c4074514104084a04d80e0003080300c212580c085c030300c050101c010200c102074032000710391242c10701245003110041d8104c001c510511384030b000c0c00e500340340c010b0300e0340401100c2d1009901e05c06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 856198857 1250 856197607 856197619
    0x1409040201022a0405090105091e0307050115300308070309080a0809010c020d1d010c0f06020301061704022409060c1606021c0509040b060313020f0907090e06 70
    0x903000c1403030100d01c0803d031089954005850398036003000e0000300c620050050f01c40f46d00d02001d01806460110310030b020a4280b01901905e00041d4510900750720074400014815846c21022030614071000401d81d045a40880a000f40c05854107180500710f01c00d010504c20041c509142500024018400b03190420340314500000d903907000c1d50f9950382d02d900c6060210049981c2c24200020200d09006222104a4920140800c01002e10000d011480c54844140b44c0e09441a040800d69200c0e9107503040c42c90b0403044000c042495414807000030b600a0241e00c0000301340302c0d107007032161240218050140c0c0d0301802c4a1284005032402c201e50654a901c0500304001c01c03c51081160b50f80c0700940300d02103142c0060320f200d0301841903200d9103a803981d114000790b4004d03c0c800d03400c00b40407010190250185041981e034620210001500402c00c040f0380c65441000072050040c800680c0e400e481c07485100390703284143c14040c08100003000101310343d180006055110107000740e001c40c40155030010300180071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 856200107 1250 856198857 856198873
    0x60302040c02011d0c0a050d1b031a070509011704020d0b09100e06060604060f030b0303070b01050405060909031e0c0a12080c041a07030e040c050d15140904020102 72
    0x581a40c141205031030042c4c0d101c0c01401d42d8040104c3c07a03400781c900800002c00344102e03100041007540029200d0b051084a50110140603c034202400c046011b540c18072143c41c0e0f070340781e10302043c014502202c900c401c8000315001881090103402110a0b1190507144d544c11000042c1104442460040080b40c10a10084500c00002c518600d024012444800581040400c0102e102d048944d51010365880d83c2c04242480a0b171780b50b80e4111800d0324103628056000040784030081e4044c2c01650480d94051100045043c180200a110103041e02c6007100d0030303c0355854510030056250307400e5440c0d5409403c00c00c181c00c0e0024005141d203001030000710b01c0ca4101200c080c162030030888a26410fa862020140d07aa4810690220034540c0c0300e00c0b6440c000f030803c3d080125000311500023040341c040c440c01c001034090505000c0c0c8032050450030010300c1842162031045000f0b140c1d800211080d941c7d1400c180e000100c0c00c8180c0f03040c0c5d00b600d44070440440c110007200304204591710b001d081641540101c1031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 856201357 1250 856200107 856200109
    0x4060207022202030a1404200a0305121e0a1e0c0213060302041103090c012f100c030e0a170c0304030503040501021504051903090b1c0f020c030406030906060302 71
    0x5007100c5400d0107000b0044c1c60f460015820000e59141d0102d880765800118204030000d00344c0b00d01400c0030b091092480d02012040c5010520040803604094102d02c2a050f80c14950007050005000d640b6a110300c600c000702c2d01da07001042a0081441440202e1201c080d49041880380c80414511007107070f850032130b90618803a004601030050120660404039103452090007503007410300410380b0030100c1c40d0001d4a5031070440041b1780c0b141c802d0b04195040080f5401008070ba80d00300c0d0b61222a00f103d811045004042455500ba910650001e200c10640d00305290540491301078418208141e1080002e07100c20394041d80c0b484111003100d0840c47d000c2000348100140380364200b0203400070750b2087c0015651a401c2000180c9015003801109148042c118100b20000c2d002280d11108605c500c100e000300c40d072641c41c042c1d9114030590880d002d643c00214108031003145503d825120f8080440041168500c084107880a901c10007a00e1041c0d64000c000801c64580b195102d40b000300e006030070015910703850364 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 856202607 1250 856201357 856201399
    0x60806011d040f0911151e040e090615030313060e04090c03050d090f0f03260327010203070e0d05070513090b06040c1b03091a0406090b03010e0406020702 68
    0x8254000444d41e1902d132001002000c042080c00c80000300c4082c02191035034610180b1511034480704100e41d034000f5800c1100a0b07608020b40b030180003c0308600c02c40d0315141c4003190750b40004450a80494407044103031401824003108031095902d50b0744242210b60b060032030540300a82800e1810307801c907541d42e40e041c0201c3c104a4518001e0b40c0300710094610b65503038034002014800c241d0403d2421640c991400c0007021310740740c506400c40c0d510807522940c0c18184401350f40900100c42004049440002c2081f180750500c0140365202c21010b10074810b1580c021101d0390803400100d41d0080411604508010305150068200d40b41c81d10800c12a00e0a948400110320348000500c008680c0d680c4034403141041081c4c1c0700031340b94400000d0302d04020941001d4030042180315030241c20603801d00010245014584200f411074060076543c600010644903080c07048007282d00c54801c290000700d8142010503088100d208a0703049a45101201e4410740700e58880100a40c40003030126840416982e810045203014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 856203857 1250 856202607 856202621
    0xc02011d0d020d05240c1b0109021e030d030e030901110a0606061d1801090203130503070804090b190501050f211906180f0b28090501060806011d04 65
    0x3c00140030540c4170a8100c0c00c64049049110003a46020000c00800a00d094290352035158400304402000c90310030015030040c2007021020350011010103090380c002800d20750100c01540d00740c0894100b0550704004a0442d03802030601e0105400803c1024420742c0705088072003116002000303981c8440080e60300e402c211003941e84a2000f203841300e003501600304a800311070040303504260f035000480381444030121002e400500400401d50741c040045400c440200f4130b654422030b13000044980d0344955003040007154000d4420810058100810403407541048a001010540200d00c0106801d05100040d901600300303075842090500c1c00e000042404191007812000c0303102d80e10b084042801c081b20182c0100300c80c0031041400a061100400c8000c02404015601c25a142000208050040507071806803000e8903106a129451080c482001c4038a0130b1090440750f0480394011003c4d44d68040c0d441078031424882c0360701045606e80055515401401d80c0c5a00c91014400a8030b1000d00308001822240a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 856205107 1250 856203857 856203863
    0x170705250506070509030a03140904090b01030204050c0720010527131b030203130506071713080d05062404080601090608031e120408070209070c02011d0d020d 70
    0x140e0121105000e4140600d541120b0b01c1e1400350702c0d06118102195440d5141c1000078100000070000352030036078414089d078032102c00c0100305100030300003801c081c8404442800140c0c895441e050114003042886030440388455440448400c44014100e2002e00c072001d54804241070000030000020304441507240c17141c000004005034a00707641d0304810310151010b0002013420b1180303003461404204101d5003101072034551515001d03940e95100c2001062107821108020401e12900c030501030495001048200001481b60001072142e5507106001c40901030198040c07d1680200461003450025400440e0f0205001e8500d0b52138000e21104014034200780c202020480c140881d040c4242c0209010840c0101400a0140020380c00c00411903144d1007507140c54842484658041c1160040c0442507400300383d406682c4502919003424526481d50146074121f10440600c00010b140c41d0140c58020f00454042c1c0d00c803c049103110344409041c1c1c021b41000755018100c034040d10300603520f955031620781503c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 856206357 1250 856205107 856205167
    0x3040515031f18140903031b1207020d02240604051503060f0106030c020304050901060c0f080c07051005130b030a112101080d02030304060c0509040c0e1203040303170705 75
    0x19425400404a84c12005420324601c030800911001c8940081502d82042200280511030040080080c0d42d9204501d0102c000c10984c4003082102038021400311944a469000e5825813800a801512074220790105240a40e0295000c614242020390120368031034241202c098188101c500001c0c5840d908544100d100d100400062011903414001c511418441d40000c42c140ba040000003801284140500c6c07003003041301200a8140a00300f8000d00d0101e400c88011a641d140000301107441c1c00d040e01a0314080e001e40001040030a104a040f80d580c1880c04c0c40540044d07042c08014a030035480a00400141a00c0303d100c460700d02c080c03070000c140c01500081d0780d0303545551141d145e140742c1c00f0585c004501c036040441405a6140c002c8212544660b100f035002408100c1020706882e94000c1014076178002c0d151502e41440c40c0e4021a260303040040c211002810350700c10380e10841d540d02ca2800004c2c0014103c03245104000d00b159040c5400840b41d0030b000e4107001c01a50000d003c660b45030301ca910910 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 856207607 1250 856206357 856206389
    0x10f030b0a1e090c230f0409050115031a060109151409030708010b090a06050603010b0307020109120e0a0e0912070f0b0c03040c0e040b0c07030903020303040f1703040515031f 77
    0x41d81c136801074110000c2404620700c0c500180d0000d1024046034480d1b44c003c6480e01303008010003a0139400f1403035140141024140e507580360f00340a290f0110850007498214002c9020074860760050582d0000c4400c0030f05190105206400d08072040003c0b943e084200000034010030800d59024481c00740902803000000401c6211007040190103040906141d81c183d140c2001440799485035000c907410741d5440302400e41d07a603d800204900409899a0103880d03e6841d04a0180d21503000c01104540300d0300b1100444e207a41c8030300c400174030b908003a80d8a040c0c03944200404012020001c024010660250303035080c1c07800714076880380c4500d46001c6a0b000d007a014000200030030001141c40b540040c000d0f1448050b03051800f030340c44034041c00000c0c026246819002c16100e003058840e01c082c070301a43c4c3c003500b600d071165a1043e120582d042c09024125401200b12815084110004243e50403100001c01e2a11017000c1c017000004950700240550706c1c82c18828003645c41c103003a43d04076600140301060481d2058 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 856208857 1250 856207607 856207619
    0xe011211090a23150c06070504030b06120616170a0e070e040804050103020c010b12032515020c030d0e0a020f040203041106031018060e010f030b0a1e090c 68
    0x5500c25030009500d030320340610318186244032140c41143c10102652400d40d144094102c0c0f655a004001d4502e40c140724080c100070f15568024064000c03039200d00030110064a404040100790009007030704e035000b907102100142c0b400002081800840140d400c1c00e42110341d0508c000701c03104000701c4480d000151105400c0840c1c0b0410040c08004001c0e145d4810f48d181010344d260180c0c0d00c240d02c01c4504040e0081611502c0e85c400b075120503030382e11000301040300c2d86020b8604c1c0c1d6126008601d140080a1003001a541540c5101c01c180754441c2e0302522040248903540e60180c001e4000140314010b41c8014480390200b403409115100f15080450014411681d191042200c2c001d80009414040d174010300c103000004104028110f15014200c4105440390703500d001c1d2481d00811907100c9421001002d040c4030200081781d00260903100c42803113000d040da8132039a00c50a00340a9101c0180782c012a40005044104140e200402840307842400c50070007051100c4c10800e468800380c0580f02003500312030070000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 856210107 1250 856208857 856208869
    0x180218070f0c030806040506120102190e0604080618011b0206010e0109140a4a010e100b03010b061902060601030b0a0b0706090f14100b060a0e01121109 67
    0x1025070545008a01c0e035015580003004c90002820302406952a0004a40c071540e0f410031042d4130680d000001c5460300c21140002d240c800c554244100860b10401c13403042d41b410301c103040b0b805442110340140425143c60842031340800018111030780c1e55503100d184044070010860f4900c1100c2d01a8000c00095040c22000c50181c00c06901041a4524069041c050407128812956201d0712040d07001503d098042d040c805001520350030800c034600c2c0340300c494003070503200728044d0340b13280071540160000403410a4180c22180c2168100c00c140d400001d400100d1449900000792900e0090008241041040c0110354642c01c00300c1004611488407240d016015810042d40303500c440d091906001c48840d42c40455182489030003180423902001a40006100a6810040c03d0b560b1141550302c0b4000a0f04091481c00c14080e845501d41c00344901506070a040e900a003c4800c2c40207044e640f91000303e00c0c041c7d6907003d425540605001c1c0719a55150506114410303403090040081a4a0361450038104000b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 856211357 1250 856210107 856210127
    0x24080c0f071712040f1101021c05030a1512110f060403022202030a090b070e13020a090b0408030a0f02030a0512040f0510020d14042001050d09060c030b01080f060418021807 76
    0x30455210006204c03414409d1454010840030300d00741640da030f03100c0034403410140c03088220244014040040008228044101101005009000c240e400900c80d50030400c1ca00c1ca20850f00b50300180a0000b8009440e04c90070b00325501074286603c098491030030380ea902c2a6002102c501e03903d155035000250603c801c40700c80c01d5002d0b5192500d281803072000000241c544044008849110f80c2c04185148154045d00c00d15003e8440d2001d016119940c4541d02a0b586c1c1c000c094000000700c1d821890004180000161b41c40307a4040e8440e181000280c00c200c8082c0400244181c880340390307500c01d020100780c01307000b200c240503060107025944504000400040d1a002540300f00810032403020080411340385c00c3c0141c180e000c0c00e0b049407006a4002c00480d401d00400c04242d00b803d02d0480004100613007070b4000300b2038400c0c1d0380742070040321007075401520140300407640e45040201100004609103010303404150030002e5100c044144070581e0b000b241000071041312a07601049620300f40514190481e076015 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 856212607 1250 856211357 856211359
    0x60c1605130203040201080109051503120c0d0809100b22050405010b1806040c181205070b0901050a14040906032405190e0724080c0f071712040f11 65
    0x1d803444c04c10390b00080c00000305100701000c280e51000030484a84070011202201c0200808070344001040400c48a0b5952100c4800982c42c400c0c1ca0120300d800d0b025505083c4200130b40000b0340704004016120790080c0540301c2000b80e222548802141100c0d200c10750fa89034a007000c802c001285c0c6060f10380f090071641c40c0305615118401c0d83e03104500703090b041c04036031340e0041054401141c00c2c583c4000c2520300050200c11030190369240000801c00d0710441841441180c02441210456651041d5600c1c0074414001c00c5da002030010401c00400c0350142d0020005442c521005603d46941d46603d44203e98168000b1594884000540850140c44042c20201801e8006041006041011840d186001c031100c05000e11600c50654400305081409030380000e0044e0441000c800d46100c40004104c807042c0040d0300440c01180109100320686003d072400c0e07030a40e410442c603058168545130028042c164007041c25640c10082207000e2004100e000d07015512a042c42c0840608500c0c0046442030051491 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 856213857 1250 856212607 856212611
    0x90e061912060609152303120a26060103020a270306110412140106030204020a09090c0905030d030f0b04091202060a0506031504020303190e010e12100b060c160513 72
    0x281520110700071303950807500134003038440e6860a001d46c1810f07402d5800b40403550500901c0390b50761480601c44018041c00300140d0391040c4003e4241c0c2c4603d108040742c05c1003224400107e00080d03155001e9070050600c060f4a00b04a0010420500d030820380d140c000054848210402e01c081003000254040d0b01c84120140640c14185800c0c1040300340302c504141000b40c00301415403440911807800303610440240d600504103558801180001810911080c417560702c081d4034003415500010321500c0c1e2813003501e03001009803181c1007460034101c0103000c500803003030303200c0381c1d82d07031a542441d0b40f0307403040f01ca025201e04907000c0d602181d00c00290034400010040a1001e06040c00c10003155004503040390032208a02c401075854407180040380c610700039080320344110f19031503154034130343c0f44c002000b0074500c0fa09030f80d8840388034111018000034140b00c6245007d1a40710351500d10a807541a0000c40c00c04002800f020304006030204d9440c5410b52502c80c42c04988000c050900080c00c0040f01510281c40c90281 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 856215107 1250 856213857 856213871
    0x50c21010c030e0634031a041407050309070b04030c06080f0411013506030c060a0e0f150d1e060e16090503010204080f0f0c01090e061912060609 64
    0xc25110f91004180481c5040c0038440c000319880c1e40c080c5040c5c0c0044040501d0194a0304190180050031340220318544c168540c02e40d15854541805000110207000340398000503103c101d400d8a0030b81011703042036441e0140342c00100300703421084041c00013103020b140031204203860202c000e000c034040a06030005e220320b81030800005c02d41d2280c15a100882c06c0ca00300100301442c0c2201113030116a00c2c060081803142c03180c0c0d2100070041c880040d010300811401d890a91b1400410440b41d032190588000104491901e100310f1864602c01c07110183d070000c0e006144107600050f602c0426840318108410b560b58890001000c4017426040c0f080d2105000c1c800c0055500b410092030003800028003c001c1c040000e000403150034410038114004200c081d0088d500c0b252581d00310781e10b44d515080301992034850303c3c02000d0118400119204260010b0310f814014070f0074002440c440550046c0080d8011280082c1c5251840035103071150028141c1c05003801e4000c40518050f002c1d2901e50384a55400e41c1003000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 856216357 1250 856215107 856215131
    0xc1002070c14011403070e090a1a0f0a211a10140604090f1d01061a090931030905120601211104020a09050108160f0c050c21010c03 58
    0xc0000b80300513500041d165030302d422048a5040d4403031045900000b040d0b0600c94440016003017805042c0c8400c07003040c0700790010b1041c800e080401c0d20700258089401f00c020072030005854100503112807186203d04c3d450703079552107a1221001d051460b40300514003204000c2414036000d6200003400d805065180c2d98400440011224041c134041c2c0303540c480c1d941040400185503a40084000c06259181d4001c1020000c80d090080619101d003204480040510700d082009035412030b100000c006007000301c0354581c10a03801d510007410140505010f14003480050800c605050a10450311990b074404402d401d10042c8980c07200b403111030421540c0100c00500c00040900007441d100801c955181d00c0501e00c5080011214001c4c020403908144009000030b0141d51062640d0241c4000fa29240d40f070340c84104c01d80000c2c213142d0880c0340000c0c0240040342c40c400e1049259424080c001d5007151007901c10301c0c000031a038011021042014107038060040148000038040c0c5c40294030030303083c00c00000728002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 856217607 1250 856216357 856216367
    0x501060c0803060103090c0602030a182927100206040201080a0c020304030803010f050103060503030406140901140c0703050c0f242802010b09190906020c1002070c1401 74
    0xa00c0080c03680c0400310010b11241d22075882401110b0300201c0c1201c2c01c81d60703001c0103500c0340e12074001d00001400d007081c4031450548522881e400c07290a0018040708844078a01d02186400303114402c81140c3e000c000032500d500756140281020300303085800450404141e002c105403110b80b07500e03080075500400c08000150783c01012140e44501124004034034422a0302c4100e003144603942004025280c0400042011348415001406442e4281c078200f02d00c0b07445000301507503401988101da0000e01840320100c441c2c041a400707000302c0041810b005111050000c008000ca4001c2c9078440c00a9005000c10424464100b00045d0724040c15190196941210400302d4088101e001c405259010b01c50300e40f00c50202c2e2003040716003003000403134001c220240d540d4101d060185a05e1041c00150b00306101b444c11840c103001490f000c5c0d10341c16062103160b440b07100582c0c05008241000d0754001d07401d100750001e1090920038041802483d20300140e85407010300d440050301071160090045040009200c5009903040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 856218857 1250 856217607 856217627
    0x50424022a090408190c0b0f010f06050d090204060b091e03120313081b0f01060b16020103060e010801062303061305012301080f0f061807052809050106 67
    0x1c0d1050b8007655600d0911140e14070a89210710b40000e80140c1c910441a800300e401b0b190701e4401d403aa40e125860300615004620400c5c050907050802d8041d0400c05640aa0b004024000707179144003140103a495000a001c480c500c1d84644035400d0b0001e030040007460084031070b510400031000d1441d03044000601180d0f035410560103a0780c010b240000850700360064680c00c40703140d40d4040c40300c5903904010108604c001c03120b80c2d5404521b02c03c5540760581d429040c041d00b03080d20750030b000d0035040000901c401c003003201d80503000741c0c181640d5120104100983d0704038035018204c2c80001088403403510742800d0568150300c100c402070b00c0024402a00c942d4000c075035650450710401140300b0110040c189280100540c0b045c2106d0b1000c00c144100c40446015086412501550141c80c0c40443c01c428903500c50b94a42c480740300e00e07013003440000d22192804803000d58142100c01203400e090740754008161480c0d0301e250010061620a0045605070b200c405011014100308081406154506880a441b071024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 856220107 1250 856218857 856218859
    0x1e32011805030f0c0a0609050313080d05030a0504021809011b0518010c0813180b01080720031b010605040e19060207080f0d0b0f0312070f03050424022a 67
    0x7000600194404d0100964561103412003810000c00b0700302e00d0103513540c3d03001c00b034428240040090f0024601e2000f007100030b1200b485840b1145195501285c0500509005000f02da00010350b2000b03070f00d507030040320100e446014040d00016200401719041c43c4424205100401001410402008041c50003903c41110b180d0a00b81341810361854503205107180100f0312140100c02002d03a00241200f405072208007200440035080080c0d1051070011500080110f82d94404640e540c2e41d0216101e4082c1031740d428902403034040c1c0c0d040c090b02c55496080302c5284a0881040c1e916050188000e140174800c9006140ca494000d01d0864083e42107180c1c0281e803050040c0c0002e5021139600c05000007502203c410f4200d4a550581c0d07500d02041c000e00805e4012205401034542c240004464100059400704800c5d07442e14070380c05c090762503480c2000000102c800710304206c824000001d0010310b0300ba21001040303461540480070000c400000f072400e10b0315140c01d132800f60400e45980e508080345880e080ca4480c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 856221357 1250 856220107 856220137
    0x6160512090f2406042306040f06030c0513020c150702100c0210050a020429091203040312030212040f060905250803071e3201180503 59
    0x968240414101420840d070000d1030b00404803c0a031540c2e03555404a40c0000150094000c0d8550350b060100700ca14840310101c900d00c2950074518080a06002254000d0f0700070408201d11100d40145810344680d60f0040343c003142840c80c1807140c0e107440c068100104c1c3c4415000c50502007012080d0303545001010b50a40a1405100400c00861081c04540307075600000100b88031801c007060000b5694031450405495491801000c0398106000e802220102c903404038041007000442501c0941c410b500521200350700d00c00b00421450b030f0311000014154400000301454586245081c81180b07810100da0000070188104100005011801d00032900543c00c241d200c11240718070301e403150061a000310040d10034800da0541ca950382c3c0000c2d4100d084080c9500c03036602d51a55904c1c900c0c2d501d015812005001c141a020000320b00721100c09c013030f04900c0c000ea40c17262035507a020301500d141030241c2d1440305039440c02d11030303640044100b40070f2001c3c80d81e180810700c4400746454031201d4481c007440340360001d025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 856222607 1250 856221357 856221361
    0x5010f060f03170733090b1f0b0d0b0a03020306090a021903051f0906140a0c050702030303060909070b040602011b020d021e010b060f071a04210909140105010206160512 74
    0x202d002405d5402e00c030485d103c00c001c010aa424a03155032101120b04141e040c070011014088a400710002c01c1c00c40c0c084a00c41c42c1070100030381241c00a02007805400e600701c10340000010150340c2c100030701c80c011403802c00501400070f040d0040c0161481e100000c540c0054511104000040c0005a0310000e0340f0b803502e0030540c58602955043c0940340004001d420541801c000540c0b0618100f9018010301c4008420018a50440c0081d02c1c140a42080a0b515420038000202c0d41e00b0b107500e04d294003119001c140c401e45070700c81c011021640c10030303040880140e40d101c14040300e01d1192286420620210700051114140000c07009550345481d0007010f0080b0b0320f14030740403540f940c250001e801220380241800c0c1c513450003032420074403500a06015210000500180700b1508a0404854020340d0803031141c642171600821401801d280d946000801c2040c071580000f001d0465204803c0e201005014110b03040d498180021302e000005441c5c1030584500741080e42405403c20110741000e83d905220054035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 856223857 1250 856222607 856222673
    0x170c01050105090f01150e060a0305060a05010c0b0a050c1303030203180a05090406090819080f011e030f050c060a08060a060801051e041401081501061d04050405010f060f031707 78
    0x9652400b00c00352308000b02165081010340c25400241c8140401d403800d1102990321001100d0185225a000d0303d90700020380410070a110365048990300504e070740c00072481c20b600e90010017800303d9141e1003a4016080840e01d14545e484134000c600451604440101d219420b000c001046080054001090907a6a00c40607081001c500152242e101d403045425502d091841c41c080e01141003103e03017400300b80c80e02c400401c840e000301c4088071000c440c030382420700c1c0c050030341e52440c011035009030094407284074030052542180c3c0c41000804400701a55910f4081d418000248107a00034103406c0f001c00d000d40c3e0300c014400ca4a0f9450302105600301d95141581000d154000314000f0f1142c105001d00d1403071960004107401200280340c550103090341070301c103065070ba8900f0b04813101080388180700003140481615001070700d2f042e04070b203030020700038000040d0404218800c034084800c954841d10b9041200d0300c0070020300a2110b418010800c4c00008a85008502e50317460280440100c3d40c040000320a02440601c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 856225107 1250 856223857 856223867
    0x70f0f0c0c0f0b2a060423060a0b0102010b0906090c180d0305030910110a120b1e0301061a0304080f07140a0b18070b0c0109170c01050105090f0115 65
    0x510000d05801c2100b521000881d0b119408001d01c1e07004001c000302e440c1410204c0c0d8070948902c202100c054001600d46603180c44064140e03039988100318100707410304891b00d00b00780407944c002c50040da00090280705080003e400c1d05c451500c0e1a204004602c100704a6494a0340c80540c08103180546a60310203484407d561644102c01400360001e0021251604054006c401940150b10600803140c0d807c071100704031426580309001e000800e22041c030030051540d010b0240c0400d45c45403d0004204005100f003c40c1025420b407441e8500341e07011700914034181c04c003032180324094644100c02c180940300ca9500c40c0081d100180000301016800a105406107440405035100d90340d006940c1100c0d41030702003c1a5846034460300a5510070500000314482c00300300c0788009005d804a0014200740703441c11003800142c0c3c201100840d10f0755201e5a0072000121442d000d5545200c0341504591a040c00e0a581030071101d0507040140101180c00600c420750b01c3d241d50040c1101d646211406600c005c008040f99 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 856226357 1250 856225107 856225109
    0x40c17010f0f050f090d050901120204030203150f18251203091d06010818070b070605010e0606040b07060509030d05092b1b021c031205070f0f0c0c 65
    0x205240081501e09801d85801050040c031138595411001d883c0c4040090b15920b60302c51000104008001000c0254003460040c0718100e15101e0041c01c203640ea0b00440d080540521059071500500310420a1800e4080b041503003040c01d035114a010034140d01c00050b501d0807000e200f206070b080810a03a008425212084d00301070814040d078201e503108a4980039050b500320b8001c102e41034120070ba28400c105183d10405200754016903030000b07242c0300d9405046401c0c1c010680025a0f0040b040b0100d40300e0042710040010324401d100008540d8907050b4032403003901010300014420b0700100f0040007001000e07000d94524980141c4001116210b44919030301d14403811500004090524041001502c80410744041c0c0054042c0301c8122a950030b0040164502e1440d424000f0070034200960488680407441d9100c1107102901c0509500d07458840d449400c41003403c00c0300068294207000744c201109026070354012513181003100900001c1e0602030003500103850303a1410081c18680d14014408c001d40000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 856227607 1250 856226357 856226381
    0x307020c010e130204080d09060309080901110a06050c18120d0f0e03060705070203010b0a05090a0914031b07080d1d04020702130c1404120809031f150608040c1701 72
    0x40d0346682d00d02009841d07042d01d0001c0e40229500000c0020a48d00ae4007e461655074080d0031342e0310340032200c40190799070440c0595800191040d030004100107203c074482c03623005003801e41156460b0580800c3c0c004e00f10040b90200313800740d0901304005601c102c0005454100400d282032015400d00726800c22940c3c543d80c030030a80da241c4035040522091540200080c403501e40240c3c028170951050100b40006480c00703101c0c3e150040303056000160301c049540d0125024502c41c200302c5801110381c4001c1442d6401061310300d905507464240b00341c5229000c01c41040240f0105015000081e40c00034044c2000381004044043d18146d80380c440e540b41d440b0303070454080e00e07401041d08003044400002c280081c0300c40110140480c0407400c084044018003800d035030403980400d10050000b1250364a500c8030b0740000d90380580500c565a00002400c210410103100d100d82d4070b03c00100c04590840c00800d41c0400d034051402c0c010a181400041280303842e00701c003500d5050301030814400ba100c81c03403070040018480340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 856228857 1250 856227607 856227611
    0x5060102210403061109130c0504230414041a041406090a14072d030f0f020f0f01080601080403050c071d0105040b0d0f020103020418020912030307020c010e13 70
    0x120741240e40c0041e005584c020344042160f01d540c138250800174826500b0143d403250460b500d000314441c82e0b800204410301946400e42c205541c42035a54000f81d00d00560380d0520400d034200210302d003054495013849131150f0304551000e01301920b401e0f00342c86040c80d07101110001180010144601c40c02015038003449001100d10fa131425400d00c949680340c0503012a07180782e625039070074158030000030200c0c142d0312900445a158814003200d400005120311620b071603200b0001d000400300d595100c20b484c0490007641c0e03004007400e851040000050322501160311480d9611805101646d1118a05074015002e090100c16621036007001d841601a43c001c0c58083e105607007002c50b11030782000d045182100d0700844030045036200e504001c1a9480b01003070030b8010181125003004980c225100085040c0181001854992900e6106441c00000302c100103c040d00091003403001d081c034140f1529061401400b0311700310b0500c4003000b5101c07078900d03800d10304008414051a466035034680b41020607640071441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 856230107 1250 856228857 856228903
    0x5031b0309030706060501023c060414071a04050d020d050d05091c0506070f09031a0402030615061b030d0603030f0908070e2e092c07060305060102 65
    0x10041d82ea51000301c00315226400c0210000b0a94000260b001030100c090f06903000c500c600d0a0800c907910800e400f80540c5100920540490388030a01c026806071f80030781c036000900b0105c0e520051030903806038081c600e001d0210300702402d1080103405550070744004492809040c819400000e800166408002e800b41c007800e6003407485250060000c1060305000e07240501c5190300210032140f49103030803101401c0e90304000006400c062042300701401100190034814400354980c1c4076101c58014500c1459800c040340b109000a603d030800c00b0384d5025109881c641c42c61251400411464040c824001d0310700100c030550682c4140c001e00a42e20140c5400404011490356401c0050a0803c540100d0f400318812207001b040076407000ca511000d949807480340c443c503511110001070319a1041002c00f41140300d01d804040e080040e800c001c000074481c140f03012404e40c0d0451074140c02c01e40d00c2c0d8034440c580c5400900000c20f1040204824003141c120b828005180d40d501c0005030304050101c098200001c51030700c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 856231357 1250 856230107 856230121
    0x90108040f1b0b04180509030d15030c060909050a090f02040b040b061303030e031c1b0204050a0c020705030106061706040b06072f031b031006140f010203040b0a05031b03 75
    0x283c001c8070b8000e089140c451042e9050b00003114010303140000140c10402900c800054207401c00c1081452915004032b10a0341c035122280c860029820000010340041020040d80c10701c3d005c0c060b003241450100f080500002d540b44441ea80c90940001e01480d107407014031455960329403040b260390402400d0035a80b030300761561a4454414602040f0041121000600070038240021b0007000011b4130f0001c2071219051005c1500c201d511420341e8103007001c0e441c005d8401a110390080034054a691180800e8074800844080c1c140800f981110340207030300d0514100030181d440f4203980108401c0c003a20080903182d60020501a281c1d0526003500003100141c103804000c10b49449130510203800040040302c43c910100000c0020642118a61562103111580700040d1748560000b003c241c001d0485d8461180301d84104280c07046035005001c2c41c640c02d180103000b400c1040001c60300c480300b440a03500d01802c0080441b90380c059203221804200f0040000361070f003074100d400640182c40d126203c1e92207140c649 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 856232607 1250 856231357 856231379
    0x609040c092c011d010306050c041a03040b0c130902090310020408030307030c090e0708070e120d0905092e36050405070603151a040302010f05090108040f1b 69
    0x403642400c60741204000141e4840040d07008441030b072182d5014403543e4a0341c2c40701c07000b6080190110b40009d50400001450382140725804905265100740ca94507440c060504104940005040094102c009c00c031a82c090f50203504004242d030300c140c400684841241000ca45018443c2e0140780e50248001400300d00c625000000d984140c0171650140a40d03541c1400c00c131072400039482010700481d0828040f4000e2802154211361191140c508041d180c100031000400803201c04012128640103442c0c10300056610000b0b210150005898004450410703040701640034114540d24164070300001044d4a1480c8030703c0c410741c028400010006052803c229094500444900e00d41d4600c207103607105060302845070b00809118903001006818220310b46841680905400711101c07014034011917010650f940719420400030000c0b071882254a8030304500c000342c410048001c0107000e21500f40000a502e070fa0010440c2c2e48117601074201d5800d090a441c0007005003248542c5003044010030070b40421030341202 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 856233857 1250 856232607 856232669
    0x9010506090c0f16122d0c020603061804211d040903020f010504080a08090a020a0302040b0f13050702151302060901092102031b030a062301030317060406050609040c09 74
    0x103401c4180310041300c2011080f4821941b00c04030f003c6212581ca800151404602840d40040050020110245091001a260310b002c503000c54142203952000d840b0400752038070b40c1c00003501d541001d0401401c41ea4244060303034041c082c0c80d8812915010cc2c0001c05209100e5031078241a4000240001d007402c0ca080030181d000040400001591800043c04144001074020325260300500f903015003a06540a00000d000200030301c075040b086e00b00a90000d0317110309541421110900c10009624242030070021b041a0f60b000c11114413121031424000c8000b84440038001c42030f4100c1d54940c1e0b41c2c61a20041c0d505251680c0718400403c0f8511031407c40140380350b40e142d00d4500c21801da5222006400389860b0700101a511980c056215901c0300300003e200713502a50071024140d149218004c004a0703051610b52003608200d0004032004500c40106580071080d0b40c010108880500200f41040041003640c018290385034030031915200390900c410b0060105002604030070448040071288418030300c581c0c0c0703c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 856235107 1250 856233857 856233887
    0x15032405010e150304030e03011104090203010521030a0e03010902060d091101030c02190507030206031003060e07050d2301060f06080c0c030a120b030d0809010506090c0f1612 77
    0x581e03441101c924201980712070100c3d803d110141540c4950710115a04090107041d907800d5961000002d0002c2e42101c0a0700042881001c0075941c0e60421051014429020041034210300020410300c06030400441903d110799201d141030056180200b00180c050130b0700080103504014001415148882107030000d0000034001c000c114420940d00004404403042101c641e001030700210a2035a9480300e06200c0030b030260256044410143c0ca0b81c0001d10b699205661002248050a00401c1001075501940305010300c91000b800005190402054020720141001481c44507658000c1000e00d0700d800f02c00e01c003030055000801c4001e80705c4000c17290783d103c103009a402080c1c03c0c20000e5814881d0302c0c100c488100c080d5028500300b070038a5030103461201d00d010031201d020340c40b1580c45804d034a0412008840c00010364542c000780c28801a0942111400f42840c4d0040041000b04141c01900108444001100b46400ba40d210011901d102c945c00791200d004003100b40c40d030b05d6882030039813200400c4d0308024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 856236357 1250 856235107 856235117
    0xc070f0c0f09060e1506180117010801021b010b03030f031f0803090315100509040305040b0d0c1b05070509150a08030705060f070207050d2112060605131503240501 72
    0x142d0217070a0174804c030b2a040f11035002900308800c030006404c8407a034036046207041c1019883d0700340d85402e0100a40d000d0300221036681d030200700354900e8801852100006030840d0b00803c2180c10501c0400d40384c0c411b10900151154000000c90081c04205a00c240e41c00207103410036061076241c03080329444c0d60018030780780e01ca403151100525030340026103e1240078840350035041e40309a290130240b050b01c200003041501444010701000071013821000040c0302082080b40001011100d070070016110252a801a9403c0030b221605c40c00000e000080c41400e03141c0c02c40e162607407583d40c11440172030740040751072050304482039035000103d0f100000050400c440c480c50039244641d44100749100d0b107041c1203901c0001640007003020000742c02c0040c0e1125405008410410f0380203e07251444c1d080600480c3c5290004494600013101c0d0340d49441040f000e8803003441c01920f003010031407aa24400d20035005010440041c1d07001c4000e514000c2d84105e01803014050b17100002200c000c4000f0390002135208a0340865 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 856237607 1250 856236357 856236361
    0x5160305060703020906030609040602161406010e04050309040b0301061502070e0f070804030309151a090f013017030f01090c0c140c031e0111030c070f0c0f09060e 72
    0x6030084c02980c0f000600982400c1c01c6586407010400e4102000e40140c0c0d01660030010002c2d00040d10551b050a00e0040910b010b040402030304142ca4024164400b43d100710b0b04100740320009071b020003102c40500d81140c000c100d4920f8080000e00508869100c01110f000224002011580205501c02240c492000d211071540d20701380c0743c002854044a0b882d0004030031500040001c0d00036404944e8031400360072450080c807000940c0c0e1040750301004486000c0b00c40c80005610524005002d00d41c4400d4031004400381e07515000250030f40680740d200f1400d011a000350300101040c2a02c1c0760400c102d8000e00240080c0b89041500d403030755403042c2c645581041165001150b0020070303004c2c88060385910350303d0048560881c0c44540000c22040c40c00b0b8405e014901c1d41110941e4200221514120410000300e4002c0071801341c1c03421540c140c1020b41921406108004021290106540311285c00100c040303280a440e00d06058404800e8128007003181c0448800301d814500750303001905607020f0148170581c0c0e03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 856238857 1250 856237607 856237621
    0xf0b0f0a0e0f0403090b0414120f060612010e012a020607050a1101020702030706110f0a0c0302040903020712080d0608032d09040905100c1107210516030506 69
    0x20403a40505450300d60244046028210b0040340c0c40c1d84603002e0300d4454070241e140d075007861855007c0e51041514032012a8964210705e800001d03403040700640401403015a40d80700c005030700e032080140224494801d801032503003840402e4100c1c40c00305840c1c0000300030014075120322012110000300c0c41c3e0b400d14221705600404074000502c160040d09251511414030170465821a10754038040c02022540d5001d00004005803820020200a4034240d00c680c070500549005180c68030a482d550346030b0310380c040c40c14040820302d84019101900c4e0103540100395a0a81d09007640b800303980d680490454040396030030384240080d80010b040c020704801d4042c0900b079a40d8000b6039603405505100d00e0491106844010030541d081d400c9000c114507001d1103414614950005012607d00150907516a0040d40ca000881406407040491810031403c2184106442c00e510941d81c0d08507009410b0648000101190f003c61500c0245510552023804c880300461070310a01035501e0340b580320403560b034444d02c408a885 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 856240107 1250 856238857 856238869
    0x51605071a0c07140f1309021c020d060221070c23030a0e191d0a020c0319020a0b070302120108010c02120d0603080301260c0d060510090f0b0f 63
    0x1545695200403e0031030b080c2046907807003160030018160b000b0101825a40035172281d002d0b560600b205c01c1d000241170515801803009118180b0500d54010f50a0420440141d540c2000a0916038000d40016181d4100c4d00b03508550801c082c0113281c1e112222004c0021303032980b185101d11030f188649888441c00301405000104c184100c03801c1c000c190000d0180340d00d0713240314481c2e5036000f440003071400452075408805105600c101d40c1110100e10314920070749a6170545400865084140c40c0400c5203840000c405841d141d00845400009641c0381040d0440c07200d00c20021100e80580100e000402814061070103030087d03110f20540c05a0f07250320000000c2c0f90350103115082041e032450300a01700c00c46120044140640c8401d10003640c40c2d03036441000c00800d902d03c001d18040e11001d003505245440903d400c10001e100444814001e0b0700c62402240d031900e03903130340345039045901c5400424240c4a41403804c0c108125600030f180d6180c54134112600d00d10858101d01c6103404140d4503807110741201401c1c058 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 856241357 1250 856240107 856240117
    0xf0f0d0f02031308070204060312020f071508070809030702090f040203010e010603030504120c090903090f14130c050c060703200306100822030207090606030e0c01080601051605071a 80
    0xb0100d80403c01c00c0040740d080c40c0200380c52440180300042c816160781c0d5405089510500301d50060344001062074004004100e800050101030484038911071100c48010402d0700700920709000c003d06000820700008041090b02d54981d4010810541c40ca0400000c1000f100100ca05034031960825840395040703034040c800c07242030300d40650f01c480c54035040c003141e040d00d0a42e038241117414413024040011045a107100b800300355031180da9075406103440c01c008030600b0b03c3c403900301c018200713030389500513580d5a940300300c505d03118a418402040111100350165424054881d200700c5038010003007040141e0764180d01084810101c0305158221080300788443c002808201e41c0190040111400000840e02a080e415408441501485a142d02c81c98880c00680c280320001c03005a408007105000182050240d04041c02d960b15003040094045000d8a6440c60300b40001c505000801d00800c1c3d00d64899000c5400c0c0e030307a40d18245c403400c54152500d80d40d900700e24450728000001003444408840c100c601116 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 856242607 1250 856241357 856241371
    0x606050618060901090504050f04020a06050c33100509090a0209060904060b130510170a0204200408061512031909150f020c04111206060f0f0d0f0203 66
    0x2010907030048280b0032154041c001940c1440b9501500280c00d07070311800307114450150072061a0150901e031040c4001c5494903040f484c244a0f007030069144103040000e0064100c1c050402c03000c0b080d541c40d480d10f17611189020f1980b03116076503401041005052480c0c050100c8006030b07182d103000ea03503603004140c5038600c060000754421001004620f103454501001c0c2e8001d402602e000039000011f00020b90380b000c1050b5444481c903110800c00c00c60807100c4d00788a00038080c001c41c40316500301512083d5200c5103840c6000303204d20b40d51254060040074400c0c95045003860418003a0b903458660100c11380d902c44c00c561a00300468206040c1006080555145100300c448500440c1024042c0e205590050803806e1100100500c02e00e0028450744030224145800304075845080c9000f0840e1002400c010700000b509008500701031300010000266811613800c0d4a01e0b40c2e0040241c1c8a200020b202d43c407a01d00e611000d940045440703906e03071003540010100d4080c0d81d1401c00c1a1484c40c400d0b00c2c1079010442d450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 856243857 1250 856242607 856242637
    0x180905070506131a0408010501060c0b060f0607083f060319141525020a120f0c15050121080a0806121006081e0309010f0c060903030906060506 63
    0x80065505000c82c50413035aa100e03079503504107034450640c203084036026402580084d003004211424040e20101c100d030400402c1e00c000c0580846240811228440c0c0f600c01020807000084064076542d480041003814810440302e80380300080340b810030300005a525800000302d0f60420229010b4980000e0800c00c40319030b04640708508540b61905100d0301ca500124000307034002c624161000280382c0b07120030f02c00d282c110303585244c808040703032808140300b1200e01c10400e66214180340404981e00c80c818101410f040d2520004103903109404071600901c425006181c44c8005010712058001508881d0594802c1d20800b20b00a0221030007600801c0840c101901d022000c008145240d81709a014640c4180301803e4541c03201c22214000346000d440301e524400340ba6803503d0a120b04003061203280c1142c4048400400c86460800e205910781c866512900c2c18480455480c5c0c038114000e07080b0b202c0c4150040c50030070401100c0d0501030080d203a20403044540c1d07450328201140d01d16040c0b0694056820361420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 856245107 1250 856243857 856243859
    0x3091801050901051507050709022107080406020901020a05030d0905060c070309060509180a0e07170309040504030e060414010801060c1e060f0f09052407120618090507050613 77
    0x920010039105c1e144488000303070800414001c50410440e020081440030070046c1d60311071460026502040c50b40d4410004010003041c402001c0d40710412582082c0c1043c1c00507541c44120700140d14011041200034141d00010036181d40c0c080183e03200c0c0c0a4a4054001e50320250b4911400086512828100038085414080305000c420f1291019140c01c50020301014014440c0c002008074a40003100c01065075611420140000841444220000d08858849010741c52902070b2441c0c4178012400114011590f41d800101414441c0100001c1c1c8540030701141d40d0b440d1250801c8411010017400076000c0b8900c4800001c0c494868007041c0191034100c0b40c11242914022035a00d04461280c0040e1103880e20f8080a1116401500c11080a58115100015a030007540340c41410144004002800c003550600c0410006003044600366109080b46009440021202a91401004541c0011039011100340c03446034108100e51001e04010701420480d00d62654583c2008164403a030b20b58a8210710078140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 856246357 1250 856245107 856245109
    0x60d090b091c020d1d0a090c1106130204020f040312080702150f190e010e0a29040803071403040b0129180301091407261f0209030f0309180105090105 66
    0x941080c82000045d03400c103010031000095641e10943c0000c9405036444400401550304007c0508440385000041c142602d800d140c0304005042c22800a0301030b5800040e070345103105a42e42224040c5034840715080f078000700c008004010400c01c8504e44e01510504a45101050400341054842c080c030424030303031095450343d01003600e0152005285540b40e80312102d0841e509070071700401d0b0940020384001c000300d0030f950925000d44031502545100c580aa40048845850859410f0303501a41001c00ca581d01e40766403004540c400b840600303145501002005120030820000c2400381200d40c204034407a05183c160022001c1c0c0786005018081030481000740d54854800107141c0104013030b00400000c0e080b070f07c50704c81360540c441c0c02500c0741440d0803c02b002e110303210309055208001b0250281d00c20b0320428500107241d4070781600300f03000050700d91048403482109058048803600c01c0040c0076a075543c00e50180e030740da40380c04c03c00e01c00703200d020707100e14244007501c0d4407007854101c8200030700d070f504c940c0d01e008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 856247607 1250 856246357 856246367
    0x30c071e020d03052512032012061305270609060105090c12010f06020f07081b0a031a010806150f060904060b0f1c090302030a0e060d090b091c020d 65
    0x1c0100ea0042c1400c1982c01c0c03600c00002c00d00317070f8854021101c1d070749150800b14000341110400c440001e0513481d101c1c003d40e06090810152144a2107031107840c8050703156000000c203040251100d031000341e4200002c00050003081c1581c90034440803820102c5010350806540c07601c68100700c45103592984110010010703440d001051903040207468000900c0c20712040110300d030f83d9600340c002c01440f1f0100c110801100398104030000c00c03c0f1000c0041e1505908080c5c9154550030b805240d22051542e02540021964030a1604001558000e6524500421403401c089808a091040d9105401000000f540a030030000180e901c0800003021005030070b000004000c8581c02c299112a00a030f56940085038540c00800141601000d140c00a510b4049540642d80080c0c910001400d656050407410000250004141d45601c1e490707090224a41c904040860014003e07000d052402c82d04005051047c8540000264024070400e002c2d51407a410a068900342900301441242c011f83c01481c080121a100e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 856248857 1250 856247607 856247617
    0x10050a0e041820031002030907080307080304120917160501081315150e0429060607060b06031005010914030c0105071509080306040e1506060c0f0102030c071e020d0305 74
    0x10b0714000551510f070001013441d002d1249200c0c0d07582c560010600c16100410060180141090001140303041a50743d1110b8142c000940700600d2031640944140c00b40d0f02400c0c8090282118001036580c00c103036006050340d545e0540719144d0000241010224095101300c843c9481116103038403008445400b80c0d00c408107e50184502c2d00303d03951703d603140c42d0010302401e4804020607082002e980705007044d04154101e10009220903406488a1039880222000c040c0030983c0000300b11140d0b9102d00007400c0a90251041510040c0d1104001081102004058440f501525402e80c1c800040035111001521485a5202207a80c103a001d0f4010180944c8039030014003032684540c1d1192004903040c03200e00180c4030721010071540305201008005860420740b02d0300c2d40041d5400000c0024902c0c5801d1562060320103007000d400b49000180b46482d12130108004100100f90700000c555916181c40e400485401c4800103c41001c3c00100d2820030781c00d5206074551241c1c004024220b40d4007141d50030b403425805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 856250107 1250 856248857 856248893
    0x1d03090d020d060230040b060f01110f0d0e0102120403060c0c080705030a030b0405040b010b0310030b090c0a050901030512070c0b070b06010e0a0608180102040510050a0e0418 77
    0x2c001c1a40001100e500181408095040c1c80442041c0381568088806150f84d42411102410f0002c00001c180700c0c0c203125420000a4070500035000c9800300403103c03100c003032004c49218850b000c04c1d42508540080d009850071603a030380d503103d0300341320100480c0c95031013801800d003242c6000e000c1030011a81d503900407000e0030540d0030900c00c00b40c500d507141c42107a0400201a5640c0c0c03c0410b41b4550700d13415009075410217034115010400d6140c10350b01c401020206029010b410790020001a4401c2c4500300e00c1005150018442c4bd003078945181d45507a64100d00014a00409030040c001465081a42c2c1c018141c039400809400c0c140003204042c040798221440c2038582030410600050f000514200030301c0440d002e0840c9034042c2ca8076000141881da444a560780c0680c282c820b08200150340214400d41281d2009401d0401c006131884060190040d070304100e900040c200384442c40c15410000030001c0e0502c6403a00d038400e0940708100404c49003400f920040840300310505000141d2490800c000e4109 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 856251357 1250 856250107 856250119
    0x31005060120030a1d0d0303050702010b030304081b01032307020312160329010507081e070b071701051002100f021b0c010e06131d0a1d03090d02 64
    0x1004220a80b2240d041031004a410000e8950545540070312202034110003510540c0d203200f801c8001c80d412580c1c0d800043c0415135144003040300e2900c00c0d000203480042c0181100d464948031810f01d5220303046c4e81c0e544d141d1950301d145000400c3d40031340514a0103c0040340c21701c0802d00800f103403c0946c0f400912403401c600040018a4900d042e2500040c091a40c4901c440880360b84c0050280451710780e81200324241d00c0070301c6035881f14004420603100f100c3d402c0c60120344442292400700101e0051f000e11525440b07032030300411500f03a0f105d00a0050300c0d0080104d200162900c04081d220440707140d5406071000c3c4110014030a50130071b11000d12520240344120303100000e21340000d03000c03291400700e114140c0380c0005950380308080701c030030541c89541610040c1c01e00c40d01a4001802e1201109815809036201140c0e0840e803440102c20b420081503600900c004801c909041c40b286203d089589c40646803403e90364640c0344441c0c51052000c5132841000b146441c001400b00044003902844c00c9074014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856252607 1250 856251357 856251377
    0x5090609090a20090a1e110d110f03070206190b100f0203070506010f080c010306051c020a03050a03020d08070e0d0b0a06050402190215151504050603090f060c090310050601 76
    0xb84906000d01d01c5054910000141205924100c000b0b4440249044000c10304045600703040b1f039100003c6410011145400058003001e41d0040c0505006031107803080410030220802680a4021421900c52134000250380181401c3d05444400c0345d441c200c81070742101c1140b104804040c0070b92004060504117004580c1405000d5403140e03e400380c02d802400d0680f10b00340741000440002c00c001946007000f403c060107014206404980c49c5014220341c541215000d0710880700350b444114610024503004001c2c2c0795100310341d08000e5601c907440c010490014452900043c0d078103205264684000700c1c0140310f071481c11b98681740c008803140d001d0f02484040ba5100000507040e9200d20085c0006128a46c00d10b02c54040500041d04080071124034a0000b9103180c1000702c03581c0f00c40343c1d5484507101143d030f801030411240382c041d145000e40d4005d2134001c2d41c0001404040da800203900340001c8000710071114296240e0082d4600344c083d8806043d0140d110b003003003e40f1412142c0082e0361141041c50903180e80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 856253857 1250 856252607 856252609
    0x207020907030605031c050f070201090e0a02090a0e070804020910080a031808030405090109090c0302040204060509040c0e2d09011203080a0c120b010c02060f0405090609090a20 78
    0x1404090750558082a0b40351010032050405201d811b00300362105907544209042028068018410620701c801401000200b4008684c0035088400c040c100048440a031490109039420003035004440b02c611528641c3d40000b0004c5c00385a6091245e41541d807840c1144e1610b50070f11003100c2002d070900e40c00403061a40400c02c81c00c00c0242c001b00d14081d0b900d0302c0b00380b00507540031903051031150400f87c140d030003c11051200e62513a0351082e044607002c400028154106041c14000740e240742d000213500a00014000803a02d602101412a5950480c3c04124062401006030b5152641c02c0f070003a000705112486111004e000d44041d8044402e4400f1001480c60040000e00ba4600c00d03000403039480b03050510101810340c8405010351201100008001c888464800a03040300381d41e13041c0503421900c0d88a2588203900c5540764201070b0360b01070700243c0c0303409078124400c40c640c11901078540503081c8080001c160385820600307a4040c4035660f010b4501c281c59074540850780355590301d1a00031180780b4102a102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 856255107 1250 856253857 856253869
    0x4060c170c07140a0f0308070f060f0603030210140613022808070c0c0b0a051605011d0102040f2c0a05011412071404090507080f0c0114071203020702 66
    0x26601d000302418032070b800d0508403481e08018950060050700080d406121018149801e9401d40350800001c1e5143d4030149005054111170f004001c0000e03090140c00500000c0d90b401802c240c0b88290259108120f4541054044035016038604a042807060082242800c28200a40d060052444094a01240d1440c1500c0d42031000f0701112110144400040210758000c2865030481c031503243c01108120107481e004040d0019006103050380724000745200c001801202129110503031881d0101696819040181c000c006165491421040380c0701d80309003c0506100b1601500c4802e9604040d803030415091000b250030801002004210302015140e0003500c99400601c5150520030105440d81003a0f008136403810000007840c040e1485090070120840c0109599080d1a04584000f45a984540016010703003010b120181c00c50198100c0410303400c4010460341000d0201504940040300315000443d0303042850380c01003007a86c005001c09000144980100c010340c0140b403402600340030268001540c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 856256357 1250 856255107 856255117
    0xa140a091707030308010f120602090f040509060a0501060504060816020a1a090c0406030b131e0302011d030415180e131a1302012106030b1f0302010504060c17 70
    0x4401c1c0e104460400c101345e800849039002d041e61648151241b40781804440a000d1803940060507076402240c030390034a40750855044460200100f05100303900f4543e07030040d169a000c5d0b4500002c4c50900001050690084d02218101c84080d0358066607a1b40e680d40b203007102e46078108614110700402003074201040c910f1010404c0050740c141e03070000e1070a0110001c1c0c54010150030b814000c7d820500c0400c08104020f030310320b5004081200101c880c420358907102030111007194100f5210304041031640e061660540c03180350803007560640824400c4040c00c01e242c1e80c1c0a5032007440381c2d01d000381e10303421b4280717114403070f04400d444044811003562303a292104c0340c0f09080103c54080e8920889070b034480604c5009018440542c1410140d43c00605041103052410010080040d040c0080c0c6005844c080c1e00701414001c020341c144104124864a91030107004402d030545012410903804c1c1c6200c4001d0000d003041c1c3c5c2c2200d1741611000c0c901481c00030203940c22081114240c40c203450004c1200e11010340080105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 856257607 1250 856256357 856256399
    0x9030c0f0a15180603060b07020405043305150603061509060703051c14180c060f03040302060c0405010c060c0513030302010509071710020c1c020a170a140a09 70
    0x1080c0b203402641403000c0c4400f5600080406003005070420440210404541d0303216010f580c041526601c0b0300f00208a20340040c03900d0100ba001c542c0303020b0503a061341c2140742c0a401d080c50500c01501e420155040c03d07440404001c2d40300c4401c0010520a02d80b00700e1003107684c0380e07481003075041c001000c00080c1c0a4002a005a003c83c50015003000e0805100c42894210f64000380c0800203c0c1c0d0302907a044000b2001480805080c1f40ca90204804240804c070b40004410300074032160343c4451070340184c0c1154009440c00c07005446980c2c08603500035591000e0390b00342c44060356080c420a90580307905015080c44039903601448802c012145000c6050030808014500a40010450f1708054140310b290983c01c1d445144414845a0003843c050320114103002880310240c0c001d43c480480704807031030a110a008609185c1c4520020584103039802180c440340031406040c01003c400c0c3c20300200e06203882901948400241c45228040600000c00e002e00001912032400c031030300e541c454101c0d620507d1014841 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 856258857 1250 856257607 856257617
    0xe0c030303221b15020f0c040b060f041d090a031d0f0d0501272307050a180b01050309060711160e0a1a010909180209070309150209030c0f0a15 63
    0x50140018562400d10000954801803007038540086d545500d84550300c011500c9581c075201003c4460760b07414103036900034201c0c0582b035542d10b640e01c80780c140b911014140509040681000a12100310100d40f000d500e94158440f1601032480800e001c040b400e21800030755008001030034024141d114000c80000703ca04c05c1000180140a00080740044a0f08440d00304100380c0c1100b9003000143c40c41c00c0f031101540601d28151801482e050010300780f038070a0b004142c01c0fa201035000034010409201c9080c0c0c00015100c00c014510550004490a1200315201d2074294000e40100340305070b1040c0c06843c00d5510000a4910302105031540022400281d400100f44040d00380500a5070715843c441c90381054142c80e80141002100e00000e4208603040c4190302e2200c0d0381c7d04020010110307003038070802400c4e4000c00e180300501c3c09d0039010b8005d000d20242600c1c00f0003000d080c0050101a803085401c0300000500420b40c3c0314154040ac840459142d5985410006204c00080c42d46209103d0442400322500c45c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 856260107 1250 856258857 856258859
    0x1090803011e170309130e010e0313050307050901030f0c03080a0f080108070e19390305010f140409021009050907080c0d1107140606040e0c030303221b 67
    0x8a4425240143c01c5140c0b0804504031004030300d00000101c40c51044140c1d4010900f401c50f420301d0000788a950302016265017410248205000b000c40182800741d20110807180035601c4409040d92141c1a0284542207131800700140049091107171050300301c6100c1c0341c00303071101074999442644a80000800c040403540500300007600d51b4000b00080d000d86071031402860100e01d050200c40603614050141d520325041c0000034640300c0810380020b401e42d0088030341ca00c048080380310101001248800c184225002c001a005003c0d482402018100c426070403245030542e0070301d0454121095440d00c11680710341d9070800307030b03006072580f02110a00f10103684a146001b4580014413074010340003407000041005e00010000d82c0030302030041d0307800c9071640300e0300007070346031010301008000c0c032550201900048500700c05100103100014003504c9100151014403040e400100c039156200c0300e840700240c0c19001400041c002502c0c201b207030709070040703550014000c40c0081d48400f652809a000008891240480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 856261357 1250 856260107 856260149
    0x30206160f20030a230a14071508090a020f010203160b040203070605190806060412150f06030b190b102307050a0f0804180e070e1012050109080301 65
    0x400b40e0000d50065001c0d0518400b04c1c0d441c10007030780c0d1310b11a02c0301e00e2145186070380010104203c1c80c43e1460340040d0800d8003100b4522017036942c100e203109013070040389070032411095244540c04680c0104130040c01440204020350801c44415001013070503046100500c0b2003007014410400000360036025094400c658201f40c01810b061440d2608448180001005141518003141c1d55841d91900145002071094842d0800250240300b207602001240d40070342034980500203070056020440c04822020010b20030301c6180401980c500e84009043d8001001c00601c6406140000102010411a0029480c400c0301c0001d00302c86102e4450400050803501000c0d0a100460341c80081210984d074030604001e810380d0759542e00c65146a000b0144001050603a080010080568000c0e00380c140907500c20310182c00460300105109113030580f05102e90400001c0e101e0b40c1990315402000c10288841100e81000d000107542c0000b071350226030540d41d4111000115020f0b2000c0c501030100850703115042b4001c2d0b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 856262607 1250 856261357 856261403
    0x31e060f04082229040b0a1b030509040b0306011a0d1b0207081203010e0c07020310020c010903140f030c03090c040f0b010e040e030d0c17070e030610050901030206160f 74
    0x1400c00003200d800c0c3e0003c4013684640802e580072507640b8007000ba0b403059400c4003180e0100c56200e00124800c041480c0f0010103400401900b02c8a01c2654204a00100b0808159648000b88903400c00004115550275074050524014007d0b0702e03071900d001ca410071a50746620901070400c40d05d440160040f2200f13200c2c1250612058a10080d181c90391411035041441010603400060300794140b407800000e2440440d10305008082c42c07035800003011500d0748902e20321700d4084c044c0140c0880005522800540c00d02c010700040c0c0751503480300704055046640d0b6034808030300380e0b10144c01d150a0303210301c12080e1160799440c050082d503124504404103081c60341310000751103400400820741c4614149807218620020010036542900e01038100428021504d04c001c2d0b4081601310181c1800c12014020040c1064000e480101d800c0004d90459040e540d0346440c0070710b507001600403664007040080c01003016140c442c0103046000b10004211354098593340d41c1010403c0380c00c0b0100d4000307842d107a100202841c05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 856263857 1250 856262607 856262639
    0x60509042901030c0506161a011d150f0a0902030c120c070b07030b01030e060a050f07020604030801030f06020f0c0f010f090206040b0705120408010209031e060f040822 74
    0x501c40c2116505540d40c9100010150080c5400f502c070100d034015091a00b110710a00c0c458000302c00510b8001c1813607484a480009003d50b01d41c001c0910742d080d40102119502e20b10580030f10890f0038002500c0c00420a80c8200d030281c559100c0e06006001c0b41c0540f81d440158003440940700200e603194203074428507000c5440140010983d000070300440780818401d010181c0d104609140000d164000000143c0090444566550042c410002001000c0050364007081c00713080d548080c01e000755503c01080f80d443c1c00031a00140007501103001080025107042c1054121842078401504101c0698a522000e40010307054450a0703100803412401501c0a214096000c181c0b50700a21001d480d030340128006100320312900c0d1064200003000403d00206001e114624030310ac510380d07580c0c3c540d1105914040c3d000220700e684a4000c0c1c40404a10814070000d10401a1111b0050043d5685981354440d07a0704005100f47e80c0c41c40700b001640c0d100000301ca46034102d03000e070314454102c0c4c1d402c207100701c8032003118 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 856265107 1250 856263857 856263923
    0x7081810080f06333606071a06060d0f0b0a0f060912080c0601030503040f090c0905010509280602011103070c02100306050301020301170d0327020406050904 69
    0x90151301c0109103002c5075203003038900c15900e1010162640e044842c28540300f1401411454a800c1d007003258020011004149441e141041c80907500e907200301008050300c501800100070740e40c00351410300550740c00b5100c00d0b8024001049036040c0b240c070002c01029030b952400c40c6040c07141c1c1c40d0b08e0151a0b1070000d0660b0302401c0c81e40d0f10a0915410100082e101e030a690080200016602410030200801c84080350380c00000e01c07080d207081c0c0d6581d1402c950741e50441e000302c2078910200711010804d41c035107100d6001c002d100c81d510101e00e90310304401540c4552080c000c1c950408039503a0050121400660a6070021460703102c050300940c1f4045009084881078210f0640c800c20030400c1c004907070f40c8440790f0f42d081070b01102d01c50b03080a06500150004d2806034000c0d42c0550000c0300014802d40b009040307446070300a4109480c910b0b01084011030441c2c002c03940041c103812036004002000350000705040d244620160000600c00d4039600080d1041030100c604480041e50b4001d80c100c10700303456017100312080d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 856266357 1250 856265107 856265119
    0xf0607020706031a030f210702030601090506010309020301110a1119030e03030d05070801060f02030c070e06040f020d0221010b1204061d150603070b07081810080f06 73
    0x2450040251100c2903031003928105500c071004800440400a095154240002c00301c40c02510761003950340c0c842c0324056040d004521020341c0c4500103540842161001c039402000f400c20b682c2042010002440b01400d080d0402d503482c0c11800050b03e0074801c000a04500c3c0c03075216240d0b030000b0b02c02030a800c0120302000207a001464484e04140200e1b00240703606070701d0b0400c6551001c08001080c95400380c1b6650403d114100010312020640048101d4160b900079a20086103c4818100f80d0b42e80c42091458a11f03a44035200412114580c460ba40707400410041010820007401d0038180141d030410b055039480954002b424400c450f14211219418101c0180c02e05007541c9400c2c82e1600500800044482c0701080200240c01c0002a910003c40020a0101c2109030f03c2101141540e0b4201107040502100c08400841c20a15000910104507802c3c10fa61501c0c15103955030b004010303009500300124034070064143c2e0070700307595036062038440314100d1b610301c4003520300340001817000c20000d014180030b46 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 856267607 1250 856266357 856266361
    0xc4d0d0f11060c061f050a15140d060602060f010509091509011808090a06020c060a0c0c09291c1e17040e01091b0804030302040e0a0e0f06 61
    0xe29540e98a91003503008450451150025808144188074620301d03081c480c080c10040108903400074404441e05034804d0540c102507512007051003c0b8003810301032401d2100074201c0000b03400b44160020a14800e004410b80c0c200301ca2508401c09039134144c2c0110000d45c0000e010000402410a0388500510302107559041c0c42c18925074060721071001041251480180c01d0000f81c410b1001d4004c000380c4507000c0c0200c5032100880c00e0214031a00510340b028402c1c102c2e0640007030b403240f000806894420300240010300e07041701c450b4203030b9200811140884050107050710000b090f046512510300000d145030344001c6ea8941c0c50582d02c41802e00384228500c600300135400260820f4a046041d0030842d8031030b10f0440079159210f81031108010250005103103040c0c040382008a08443da0140c4210b40300200b84050036600d41b86210151034650f0700031035558500c0500b5803101403180100c180c0003030107070030018070703098071040d59502c81001103e50b0140651030721f19030050080d0030840b0010001113140036182ea4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 856268857 1250 856267607 856267613
    0x4021305040507150e362e080f010902010212130e010b040f1502070e13060501170f0105090309042c0a0b010501030b090a0b03010e24070801060c4d0d 66
    0x24020300388100300d8802c3d985001640301005400d0f07003542d840b00303041c0d444040710100c18154428407050123490035034042d443e46c0c42c20569050003840e0340c482c2d05801070500200d01070461402600102408030a0380c1b403140d8006050b00ca0050010701a003804603030680d9413800c211a41c5103205055100b841200401903100140030380c003290305c6060b214400c0c2d81104503103e501101204689201010b001940f502c4000110000c4002c0301c04400c4480f841680c0201c075146155500b2254212601c2c600741d0020000d00109284c00e0f0b001e503003131b1030368940054081070070741040300a11900c80300e4100c0d50703074070810f040400d00034602031541c010942442c1c01c2c0000c0400902150300e290002c6c00615005480e08041d4000ba1340c2074001d1206060350b002119902d00101c89031003c00c3c41c10f0010700410010f40404221060b01c0381c01c40d2410b07244c00d1b488a0382042110307a151560342d50095414446040707a1121071608080d004280c0107019542e1140021403529030601361015a1010400e601c01d02e1020070444c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 856270107 1250 856268857 856268929
    0x60c03090c0415081006060908030405010903060b0d050a0b0702011a060a030b1201141b0306100f180605031b040f03080c010902180a050108030304021305040507150e 73
    0x11a01e00781e07400300340001c0c42c50100b82c4802c0680c226543c0c0380503030000400c0c051500e9100300100e407419039411030aa980d80a0154070f9202e41e00500c0c0c005405010240080740b0740c3d42040b00c00072000380c00000543c806807606824164118800c83d01001041c041c0000aa42402040d003810400f0340d111040c01065400101503104110718002415102c00100a4035551400250001510721009000691880e0075181c03107100121004080d0b150a864440e040005480036a8031034140039101038005901d010050f5507440301c07c0070600400c41510880307407440032180748042c0104099211581c80f8101060a208440310342050007580c40010f00041001d8004075840c0000c4a401420090340d401c00020315901500c81900080d421400300514032480e141e80c40b590600c140040c800410050b6201c200c1580c6911081c1e4029510011074100c0c1c03030a09103141e20054005109800310f401e440d0355001c101c040c1690811008011030b1410002200e58180405000341754a840d444050345010340c0300410701 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 856271357 1250 856270107 856270123
    0xf100209010e210d050a030608010b060304021513151115130501020c1b031b01080609060d020409050709061e140a090e01021911151302040e060702060c0309 69
    0xc032524000006080f01c1c844885215000c03141d00c0c05a50b4041c08501010b03115a0010365140700103440d0800000d0460b10610600c1c01087e030003001d003442e680b919000c01110500ca1210800702c41020000704a058441035000b03030003040ea444401144022000f00502007c1e83d83c001d12603640c0004c030400720129001c0502d180d04c00e80c0000381c01d44540807070914a00a014907400d4a04620034684081096883c840c0f85041c03101044080310342c03042d44503c15040d0342c1d1040035004d0200c0d142d5404140340e8604800035031361015000e80350640b4030f41542c00140689144113400d4440350400d45050005103242d000700e5026101d075840700c20f00841c10140d4445101400e10032080081d010410914076655070068600051a040c00148040000d03551954003e5011405001a00304160380165981e0b015125848400e04c604e40079001840c1a100f48080d96100108140001040f00c0c01e4400143d03218801d1036076150000000341420314000740003a14007100a84080041034040c402c01021820000d4602 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 856272607 1250 856271357 856271359
    0x603110304120f02070f0e01030611130504180210082d18010b0a0330050910050412061b171503160303021506040c1d150403050f100209010e 62
    0x1400307140c650500b24141552031b041580f41032103801d03002503014041c110141c142d900465042110124070002c5102c41c1c458200d81541c1c00030041c90801c00323480c0c41d500003a10580b44420b1241c1c00782d00751b40007403000b0704990f00c480c001c00d41d41400c3c0132040603801701519941c1d5445484400d0060807010400b180c00300106103081002c1405400e102c116000e412032000110040c0c9a5504e59880e0301d002001502c142c2d001e42074040c0700d47e1744210326009140c1101003e07070841d141e06140482d001d050060b91024244141c0038488100070016080b4050341c103200029004010004407a044100d040007241d043d02ca0321b5007084490f25401110b241318011f171680081d0301026800c0c103600b051003c2070505141203440d144610203204004145500491003070052000804180402c1d0340b40010070044521503484140004c403511a1580c1404100881584468008010040d44c182011140b4090b80c03054200301da49070410b81c58032035004010010995250f81c5400b040d424240800d000170034880700d8948113 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 856273857 1250 856272607 856272617
    0x109060e15040e24011803150b090a0c030b040209010503010e090a0b04150506090903180f04020a09061b050d0c0816060e071e1a0d1401060311030412 66
    0x2039421403003001d007200c0050030501075032480b0b4a0601141100c07101484201038908107000f035807144541c40340c0c586084008181d00092005030454840d032100d007075241414042566510390764401562444201403040411030b6020504031070400004098840100219024500500540505a80040550f4107440c1000d24900703480d92132040746440c182c49100c000d0202c1e00000c09010501110001c1d6002c03180d80c80005008503140c1070140300710b20b001101d551089400c240020041c00c1e040300ea08001e44400245035102040c2d100d0002000c03a400040c0b0303280441c00c40c070400c1200682040d403240200410000000c1d5030841521055198032030080a81e007045040402d180c104418403047eaa00d038044c19074545410102407404000409052158100c0380c403a10500055010601107004125041c40c9082040c1501c6c18084035582e680d08861004010700600c520b0007002c1c050b12074107441c000504c2c40d102c4039524221000d0101c50100498440e2610204100404101074155030440c1c0320080c40c103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 856275107 1250 856273857 856273879
    0x127030507020904152904090302070b0a09051516030e03010e0712140a030c0809040f1a0f0d050c0d0f020d0b270a12141620010219030315080d030b0109060e 69
    0x800c80c0bc0c56240e030805c2d0841113001c146c10380740550242c0e82a0669100b070b51480944d042e02042d261700713401703030300c141140302e01000c03129200003442107907200d43c40f803405000804d060224220180c02d1801a400410700d2102032140181409404440300c12907558001c080c1c40143c0701034170000e081060b80d81c0003900c0b803880080c614403240c070b80307078400240300080c03401c00c00500130001007585401180040d5503100b203040b010007041c149007512410580644c42070042200d074242d01d0130b0003000364210101340c0740020070800542c0513898a810721140300d40700b548026110301d071105c80c071680c10301103c225085100b0006444004001d0024045407000c1e0800101c20345040c190310210703a490f0803406440d0081c080460b045500d00a0100203210061103070581d1803201e5240160b0b0308204103200d401e81d00503440303014040e0710759003401d5020304024000e00d004500b81c1046021145146404c1c0c4c441002980309000864046605104d014112482441c203113100e145410f800900941e11104028814000019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 856276357 1250 856275107 856275113
    0x40b09040501120b072d020d17060117060a08011e05010f2607080d0201020702150f070305070f06090c03021c33060801060e09012703050702090415290409 68
    0x456407851101480b122006e0110502c40252141c11151626004c41c8102d0350066480651082c418070076007040c0c1d501050302504207441c208580c0d0140a180c1c01c09019a07002c50410004c2c01014004c1442144031918a0224004d81f02126016401101044c0382c0010501200080c00544c029460740300600310040c949001405040c00441d5100a003284980c5014018044e019005003540360b00032218082569400c8102c030f80244074a003082c40000d2810096640044d0041010784001303030180c08a114020503a96565044802e0180107171681491038008208520304960f000300150006000512080c19a580380101c0d55803150135804520095009886d009911b5412124060700c01007060101543c0d4005450081001c5d000d104032841c48000000c050f904140522900002e0105540414074448000f540b141e910220045040080c104013010240c0d5071441024000c5004092404900c104640400c1c103c03030040c4090301d030601c0650f0b24020445600c60181030000002d8501048000541c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 856277607 1250 856276357 856276397
    0x2717010209011e020c2d1e0432060a090b0d0b091614270106030b0402280807030b03060c0702030304030b070504060e04051909020303040902040b09040501120b07 71
    0x42c0380c00d0300481b41e1003081141407100141700c106914400343c50311040303180f00144882104800c03146240e8400d03000c8000b0702418903611082c01c800c814403402c00d07007400c5441d00c550318454042a060740445020300740025450550420f01c01001c101704100441588a000b1540885d00d0510140072030f034184c000503c0c240001c1c000306400850000e00f0523442c503216100c0d0848130310135a124501541040340e0580f440c10b6800c50320000e03090003401a401607840c145085001d018888200354000ea02402005020210b51400c440400407034280c080c043e130701c80744004200c8840204407001301801e003079910803d9240400c1003904100078102180d40c0d280c003400403d15501c41c40d4402803d503513403881004002179100001d030040d944140c0d5000841c0178203000300700595070142e601058034000948400c4200c1c00a502907403807184041c0c107484c107060b6a4586d1508a80040d40b20200b1280300007039a4000c0d180030310a00340941052440c14146a000d6151070140410003000d410503c2050810071504104074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 856278857 1250 856277607 856277623
    0x2070e060d1e05010f11030a140603060c03070302040504020a05092404170c03070e15040204240c050706020109170703081303020c0d03090e1006140a2717010209011e02 74
    0x605c800e0018030216184407006a008507028a6110302e08541e01101500f040c01d4640101d100034002c01d802c0c2c0b01c00d1015905640080c0110040c142e003000001040c2c0c440d80040c140324422511a01e4440400d01c060144114004603811401009182c0768410030080c0001d4405542030102140a01c1d90b80d03101840c40c0c204001c24031681441220380008650700303481170541c0310340d114590702405600d24009000070fa02842c047d48560b28220312110100a0b0060f10004a110b403620f0b001204048645503103003001116008640180d444a1500301409421083c2164000020000d41c0c40c002403610018625030f0041c00301c4d003001207001040c809140c401c00045580442c0140030480200d014030300a4009111446113102c41221000008c104444140fa0401100e01e55203170982000105081551260b0041c012038041c0588c0000b00d410300040310008900c904000c902c5075602609086000311a40000000c16440c4ea00400001c1c8940e41e1003034512030a0f00881d0886480038444002c00c0e4244120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 856280107 1250 856278857 856278881
    0x201021002040f061103180f061603020c0423220c080a0b09010c0914190b09030f0604030504030b130228060e01050301031202010e060702070e060d1e0501 68
    0x204000c6031034070600c0995000c440144c0c861740d9480c01041c07400d035180e014141040e10303861a104041c0c1228146000d82080c001d000074070107490185000590710032038007010b2090300143c0c000c51800a00b82003604c9125100e80703000e50b42c12501c0f000d48003642245140208040301c00b00038520083d00c16450616000221a40982900407554440c8569a030384c8a9103801510f1004021780450840030062048280212080d96004840d6080c0410300041016668086800024040c8508480c2c9403d102d1000a841c881e58410b40e40c0c92298105031400300e440c1c40f04030164002170140800680c03c2421078080302e5202045034082d40da510b001200103c244807010f9004440e10f01d00303101040071003940204c07500040e0b1141a00f0b07600c8800407940714415100c01c0e404134404000520114100e00800007d2070107910004c0341c150b0040b590182000e800f0f582100159010803424440000350715201680001e003030310006c0034104a900c41c0650348645608a13604c0300090403400f014400d080d0400900c01031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 856281357 1250 856280107 856280111
    0x513020a050708040e040b1302060304060b130c09081e06070309031e2106050a0308090f030a080a080f0f0c130e2d07020c130b092503151202010210 65
    0x540e9540601d42245d044401726098484000000c02c401d402c50400707002e1603005049281903948681d122002011038000d40ea0340075007050030201c2029500e01400260038440c1d0b442003000ea20b480c1d0164500404100e103404209034162442c1040c000010b03d4a9108541c0e10b40460603020504042d6000c0d0081980710b090b0f101c62902450415401c5020f110700c40c00118000312078400c0099130f190440b1624001c6c0d581c0181000300c00c10215212401504040c28014540e041194602d0b0009207041032540e41104d20b9440820900c40c500d80100e580e652000702c151085840703103010341300d05a140342c0051090400c01000705419080700c0009040b24081e01442e040c80c60380381415940202000b1400310790340025624207240030514049200610300078201500104448100d007000c10684402480382c0c4182907948030b1700103030943c0e01c40d5025801421580340c14251048140c00d507410724903200c1480014503050042c020390300e040c0140110100c0c3d0120441700c62003001e610040307003419100301490501174 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 856282607 1250 856281357 856281359
    0x909031e0c06110a110106140609040b040606170f070c14010e01050907151407020f0d05010908030703050117060406110903061f050312160309090203040b0702070506040513020a05070804 82
    0x501d031000f0500c4a04c980c444150b0002c410105c6800d031031082c01581e4409070114031850342c030b0a280c1c001e400320200050000c182c3c40807150104003203a00c40c2d4843c0380084c440303003400c1c4901d551004056410000348468900716261000d0080d01c3d40104003002421841015260300d00f0100030b41c005445039039058028031803800c12944084d5644098010003101580c11103803072040d28065200000c0061001e442c0f0350074000c013a02002003c2010042150704004200789160000d41c0070302c030b90424031707110700302a81c0c403802d1405000341203c205030004a0250301d40092108002d00c0024007581c05944542c01040c88a5031110344402c42c0079214403150144034000501203a000d0b50341c042c081e20080c1400802e06241d6400800d591900e05044850f01404100b00340344000620684c200e003031b1030003414160702c10380c1c1d41c140c0d0000300c0c2d00072201502e81d0035600040c0109640d040c8a100700425044a405003082e0800340081d440c42c0e646502d0480842d4009030910301d141c00351007950340d140e03004543c0a85076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 856283857 1250 856282607 856282631
    0x4181404030305040318061407140f0a0b0c070312090206190509180c0412080f0d020715020301081513020307030c03050d050f0d0905070906080102090405010909031e0c06 75
    0x43c080a480890101e5159a1055007aa50100b024411105a0380c5c4402d242c0300b4001e0341e048583d2103100d056404a00140d1000480c6104000c404106010400103081003d01401c1c002c204d5140500404146501000348a001c40da114110000e003100000d0001800205440054034512544181c0c1c03001c0c3c82c0f46000510501d40180c0500300c0240c094450700d03941a00c0c0c102074012000103d4116015040622040c80f4041107501e88a44c9248100896441c04c84401100ba5050b00480e603070f001040e40010344101044036108044083e00f50240741541594100003003180c8510108181c0c0416410240002d00500d0308041000700c4190083c0568051645a007004023440d8801d01040d2558030500c4400c0c0b1410344070b1021038080000f4441c0280c1031a0008038088050201b03c1d0059a45210f10074012841da4540c0c03158070000c21901c000142c0c1c82e16008180810b03110140d20080ba8030745000114000300b50040100c0c1105020f842c00b46a1024418505881d540c803078110240c0810310700f070ba4038484 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 856285107 1250 856283857 856283861
    0xb03181c0201050f01081c14120403030b0307031502070c050901151112031303032009040f020915090a080a1211191704081515010c08041814040303 65
    0x18442a0350083c4407682c1c0304c0c20610844802072103001c0c03041e807208a4140500c061203491703c84043d414a090504941000c1841201e600180002c020710605141404205034140c411021000c0c000e80143c41000d2540e101c40e01e80c9008901080d241a400080308001c00a9407c400800b03058010040d00003961900703400b400d005880721141c008a180400e81c1c0200c0400001c1c85250f05030201501403a503500c03240c1100d0303203021002048041c10749800c1e1059091000d1100902403014660349940c603030500e4400c010558180502501519104200c1c402e10754403a4000c000c0d140d0b220111403540e9221460110b25071082c99404000c20f40114034807201000b0907003203102e18052481e0f171108916440041c80700d45480c1c414002d0b82c10000789244640c00508644200510300c0302c00c0466500b0260b440413040d042c00380c004c3c00d260803080310070b00b0004498200d0049410401c0e003880d000f04400b8180c4e4490000348214000ca211045554040508480aa030010645100e005980108a080500d40500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 856286357 1250 856285107 856285153
    0xf16020a0503030711060d090605160f09261908040e01050108090d2a05101a1c260a02010f0b1309170c030c010606050906040b0318 58
    0x4421965403000280902e000000c1e10a0541c02c5492500c0ca03c0380c0038100013040c3c0c0081c1c0304901c00b0351940d1510004c07035040c1c41001d20814005424915840031349000800b814a400c0b241c205000088809100300c42d6181245440103a210240d400c2000090601d1880d0100e00454002d80d5602078980d030b010085100058000c44107003000e0b048560345c8580042d1100641100c40f100c0590054030f40002c41703442403554a4803042e0400300713106100800a03000c40c0d01e60803401c05903050791000303e8050300e144440c4a003100e2455507003224091110001d00082100060710842600c4a601040e420103001c1d5580a0307a040c2c0c20025071402c007200d9002c40b4090107400c8020710801651800301e2a01110480b80255402070400502c020070140c03c0c100040011310345950240c4100040342030050524201034001c10b10300390400003c40e10b0301388604117142940c02c940c01c000304110042c0300c804220f442d4403068500303440b03000980c19100c0c2d03a6044003040d0051003560542d0315100b003211520050b03280d01e00303d032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 856287607 1250 856286357 856286359
    0xf03180705041a061c02040b120f011410050910030b010f080103170a03110d1409030f0a030b0310110405010f09080d0f0c0b09011a01030e0c12030f1602 67
    0x30340e1166601e04000c100e070600c008200c541841800d01d440d0350300e013080050000006014405080a4192203060b00720b8206801c124075040c80020702005140202c0b400035409000d15540c02c0481d03041400c90340c0140d4407445018000c241b000244075110340030f00700b640e1003448094620002200000340090150507040e21a0340421110800143e17954403400d02039060329000710ba543d4200d07904000d059920781c00340c007200c1c003016540d07002001160b04000060400d80d1840700c010412244550f50001c2c58074018001040c503034000c0001e40e44001080060f10a441103a041c0001e000c4000c00202c3d041086e040365803482e061030429055143c101441c0a8415943d080c1d03034440461800d540b050384c0c2c500083c041c01d819a40320200740741e5414440c540380d0104003918501400548000d0b45c580c8071140b004d860782c1500341d444600c00c0d410350200740ea5402a0001c24a070074401c00154010300f03529400020f07881c0c0c0c0130703444420b801103500c80108200c40b600c40421407941c0c0e03580701c150303294507488040890403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 856288857 1250 856287607 856287613
    0x1e03060607051f3b071a220e13140a0c06030614010207090b040b090109050106030f11071101051c0203060a0902090306130c050a0306021b011512080f0318 68
    0x30880c4000300c0d0800c020400710740050303150140814a02c1d005000c4c84505810401e01c5212004103d04084d0790440480c11200095107840b9040c4007110f54003003107062042c0d1400414000104844400d801144d5045a030745050501c42c083d403030500000c1d20703440b24042000c61048030200300030402004501c10031603500e80c0d410040300751114581c2e00341051505072240180c1c4104405c0c00030200543c007034201148000c1c4000781c8245c444005c10010807013640044811a80d54004000454050148000d001100b0a08200d460301440b414480f034000e20724060030229107500c03100c60b1640110211035614805051030211010501d07000406540100c2d4940c3c0034074030000c4002044e624034001e41d5408c0c04000c01800d02907455100744940350440301720950300350745040030014090f11604207240146010f00c1c005a40d0b800a50342050728201041d24082040e890f01da0003960040001035242d059446101c1074202d2400702d03041030b081d280510700c0c1d011601c00d400002c1c81a4981c3c2c5c061302c0d079a002d0702c810507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 856290107 1250 856288857 856288871
    0x1e1e060b0f060403060e01060e0903070b01050f0a0b03090106090f061403061b0d06090903122406030e03070b10170601060504050904020d0c0303050901030e031e03060607051f 77
    0x81c0400c10005900140e00078000307000c10b00025100c0d412800081180d03800001d040e82d503800703910003030100641e0b10102c2e90b000000d00f2024400841e800030302510060301d03501499000384010907002211807050104001b000702c08a05180000c1d008070001f403840ca5403e2000200d00c955201c01081c00340b140450800d900b40000a05013808140180704114628894010602e0b501c092000e0341c3c003604941304a0b41d65641c01044541d518821412118000e55500b031a1000c1c4d24960012280100d11190b10401c0e9255400e105c0340410740c545040d280b4905d004101c5201031038a9501e1070158160041c504140141003140c612403419076481140c101340d42c86000d02c200c1003815612801c080c0101c40000348108000e121034107000090b2074020b4405080500d013080661500b0b030010045030001c800162000444212540e494001c021400c602540510300d400780e050311405090010078039000c40a80040000754495440300103540005d60008245c0d10b0b140060803a18035040e410f4418040c8140c50081c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 856291357 1250 856290107 856290109
    0x5150a021b12070f02220903030b01030e0d0f050405180a0c05130e100504020a09080c2b0305130e0702010f1a28170c0907020a1e1e060b 60
    0x1401c10410520ba2540d92a0205544134945031007040d0340e0517a00f024034031001407020b080d04904540022440400081e030f500561800505039610105500c3c105410b01104021a010106510207d007106041c014034480310b140090b5050b0245600c220340c07000315440740405011003601c6840c0b0882203003070100500140312106582c51f004d6a00c956a40c801624024010340c140b918800760089038079804105096039034000101640d0051003400c0000e14044400c0055100800020040c0001201c02c03110010400c02202032881c0c1041210340f09d0440c03480314a042c94050403c40d02c42111141c4130403a019150f180d003d4226000303851107001903103084100b03002040706200340c00021488804945200b5420070030032400e900c010040062403c404003003039800b18210424100100650380049403414024140d0909265580c601071b030091700a0303800c014040f40d02041002d80c036540010103100610121000801d60048080001d0208a1040c0d0414080b11103041c44000944101c00a0216901d903070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 856292607 1250 856291357 856291363
    0x20309090a06030b0a0906020d0f0209240f0315040615230d0e0c0405011203120c021903121e050a0902010503180c091e010603020301051c05150a021b 66
    0x71001411002941001c9500924140c001030340847c002e41d405414041c1c410200800c03101c883e500301d12800e500007040b014070f0070b000003ea01e59402c0030307010402221004803006918468058003960b405c80010010380b45010550700d0800c0914003031300401c03100b610b8915109481b1030810298001c1580100c503440d2040040c0c244c2840c1700781c414482418460200301c00e80c054803844000c003415004009038a17285440780d00c10075009080d240160555000c480c2400380ca081003102010a0417030400700078019440e000502007101500c1c424540f01004d09038203045400840c00705543d10028200821160300300190a60440400c03002001003100342c9454260808507089403a00070701080d010f2000540e83e01607010074080c03011210342a10315a0039020001540164200c8035610302403526041d6000e0f2031500300980c4e0251445040c00c500e1541000001480c44c102d40050000101d4020850803c0140c00e10502461850001c8182428140341081078080d422980105440d00c402d0000790307080039400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 856293857 1250 856292607 856292609
    0x20c0f0f0304060c15090605060f0103110301030b0613050405011b030218041d12072d1b0306020a020105011a07170d060305030435030a08040c09060303020309090a06 73
    0x211004626041c034090040d81c24881d51381d420b46020380c02c07404401c40750109008104d01e241c0704403c00240b510300f0304c0800124104150200d0704042c988501150501600801c407030549802c106003070360b43c1c6d461000040407054542d10011960740ac01d8184400c00c0415000500840c038604000d04900b103580c10101c08030701401c80504480d0006044c049410700701548510800c2c1480f0012a02c55503805007080d1a115030901d14181c1e040340062502d0500001100b20140c41c90f03280560f044400f080350320007405e480c0c00c0380060112582c210586400d1980e00658800440d888942951101071100020f4001c0000f485804081c143e104035450740380c2d01130380841d0207042d03000144401c0c0c8510030090a4141d0060440b07070724120380d103800210100e401007018100030704100c8070344409040011807440b1284024404418591515070703840c15030310380c00700c20b5880318421454810308980e01da082280e200d6105a00544510b03103071075004070038150b020000f0316290303d00741d07820315403a113843c1f000c4000c96240d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 856294964 1107 856293857 856293883
    0x1505060a0504030210141801020127051522170f041805010b1801020c0901120501060b03011203120b04020a08180706050a0f0912030201020c0f 63
    0x50500100b558441c0e80c0c1b50040140c140200224810301030102084150958113005003400e0340300b540807400c0c0e018140c43c01c4490000910f076864108100c190191881e0103141d40c80c541600214001038045d00800c4044a000207a00021070480e0f00110b40c12658030208202110407004884060300c142585031600b640d4a500e400c800c0302c00c058000c0f40c507116403418400104032540c9050182c42c44006881e007443c9140c002040101d040144585507540e009940800104844900000c41203401c1d2068000b0004152590f0010075071340402d100c2c442d440940d003040c60700000d10514140d14501030203c00451258200d10016042c0c2c0c10803d508000a00e050041100c06407000401003111110071018104890400300010f00303901c00c200c012414480210090992140308200d41c0004120300320401000d90b00c83d1500034080d600082540e003052040180c0c1d55104580070503d901c3d0036103 = true := by decide +kernel

theorem cover : BRFrame.Cov 856115107 856294964 := by
  have h0 := BRFrame.cov_init 856115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 856115107 ≤ n) (h2 : n < 856294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
