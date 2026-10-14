-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1335
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:26:23.751615+00:00
-- url     : https://prove2.me/submissions/0f6a1dc8-ea06-4d4f-ac6f-549ad47f6337

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 239928057 ≤ n < 240107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 239929307 1250 239928057 239928079
    0x904060b13060e09071d040b040201032c100219050f130e07030612171317030c070821070809040510051c02090601110c0a08071e0311 59
    0x1440c038051252003084001e1510b0710004070f12021450480c460501501901c1826982e122011440081855607920880703c5030005000034030b42c2600550018010704d4000340701aa000740301011010107074202100c1011820fa06560117404004440035a480c00d4400d44c07d1080f951103030003e1505c074100d24018400089098954500c203502500d18800c030340c80440150582c0c41204404a0078103890000019040600201d40b04400103030300c102c02a4071880b07100c00d00e100d2108040554024a1480b917240014980028901c1d020320060030b141c4a0040196540c0d0742c140c1e92003450901181e01030750154200b100c1541e28407448030345606003035048600c0309584010601e418a2684030b98039020740e01500c0c21060208204413021080d054920a0301c00a10000103002c1209501303805040082d44140084001011544035502100d02540c12804503452100c2a000060758036a058000751500e60001c44100800e40304175400400000151405201c16030950f103814001001018070b050190a25000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 239930557 1250 239929307 239929309
    0x504050d11040f050105100e060d0c111b0414040209072003030903180d0f08090307030c1e060f080a0504030905041d06060a0e01092d0917090904060b 66
    0x48109040140308101c0081c010f2952001024280945c90142c0324111004225902500c5102c104410083c0070a041c00084081e90002c0d10b80340480004114400400c4c01492a080026104022000000b03040e0508108140021184c4c8492001c843c0800801440090f032107512006030004414505220706000001010b590b42e422003c542d5214440042081281e980200103043c210180c08258410000660208442d0f411a42e8020388020540c41202c000142c001e4010b040044000e070a40e10055601c0e125210014010360084410101603049000a84001030b0158068178650400700142c0141c01c5009141d94001072000c04415642d10115040c540210240401801700030400c0c801440c042c4001d4803946240d65200d4407601c162800b01e03141d45440d0004d001585c0c044000c0c030146a1801d038821001d021981d00290303c5480e410b0380c285c1201d000c5081240c401c0b00c42c03180440d50801c903143c6250400c10070726506400a00030311500350726647d00c07004140c000e60856000b1604d000840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 239931807 1250 239930557 239930573
    0x1804030203070519171c0e120c060f090a1212151205010509010e1906060305192006070b0907051f080906010b0a08151915020d0504050d 60
    0x42e002d0320034413511012010204041c1c0c0811022840740c1220300c1020a010000c68160080c0142c0100d00d0200380d80071808800c0030351203118008107910403900e04005a00040000381d001c2900741107160482e00030416500004000150072041040040c07082c140551190070000c0402c448100402456410294030a10f00d03410001281c466000e0740c00306030b95039003055078450394000030844040d400d000009a0196040c401c040032000004003410b031600c5e400c4600d084094080204403580c40da0359002001159081110050107040385407424a0704001f4103003a00000250700240c040241844a0440300351079038001d40b00188d030312036600500794482d101d207141001d0081d00550b400c00c5202c031107044041e40c0e894240303000041e13a49566181c0d4556825050701c840003406101d442c18420003565000e20f2241d2609039002101603d05030504486400003101d0300c01c503007900194440201024448090407041d61039050130070b4001461101e00701103020306580101e12440e8442e800b84202d010502070a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 239933057 1250 239931807 239931817
    0x20706200622060204090203011e141908030c010204030203100606020c0f030f0d030f0f091e0507120303060e010b0a170604060305030304060f06060c21030219020606041503021804030203 82
    0x713645403a161050b9038000d400034411107188500b000300e560315182e010b107156000d8810000d0b12503120a20181407159810103e100c510204041810000c1d5a00041c0058041c0f41a4000003580d500d00d503004140ca8805258401c8022a01c3c04000b0405260001000d141d408000d446111191402800090501a904c4100c2034640a01100c21001d5949603109030000506050700304400100480c0386021504490001040c480a00000c0700034041e4400c1000e4115205e8000c47c0c8206498220000c1c0c8105c0d006c0c0200c0110f521000284581903010703800601402041d21072900300021508020528620300c0061b0f0101103202000c00c500d511541c01000266800108a0740c0c0c034100351406c8070041c11180081018280303003240208a03184a810700403903083d00529040e011040241070070102203107002200d07052590030030052089401004254000b2040c5802030b01c1381d46007038014842941c0000e06001c40007401020240b00596458032170391002018070b5410745a82d9943d25041e4614498 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 239934307 1250 239933057 239933063
    0x3070b0c1f06120b04020108011710020d06030507030807020102060f060105090f0f0604060e030706020a0b0406020c01090f060f05010905010f09090215120103060b060720031507020706200622 84
    0x40c0303002d003c043c800701c40c4e44680918401c0c0d8884843e07a90740c8540c0c10268080d442c0c078503038540260400500c1c421040c0c001e4450300c02c1c0b0a40004001d5a00d6940c00c2c40d0000560084400400204480040d0368043c401103600c00b64068050003a0b1400000082184c0302c0e0712009403050407114440c41c1e40762101e00c4c03a20102c010280400e81e840351030700d101804040e60510068803921400070003041c641d1000c80c1c0d40079600da02a1700240795807078543e2014040c0d00030741c03c3d803900c6640c1c5143c2c0c0000b040b148010a800c03035004031170014400303c6581050054900c1608003583e02420a00100a90000d040c8401c08903840038200141c0103025100250394549000c0900c1e82c070b1900400c0d20703204542140783c00c904030fa01c104820032040c41264140503c2d8059284080d1a50200c0d0780504118180154403006101d401030030f80b40400f1808501c06032100b070907210080140d01c0a403061000581042c1d044000103132040f800000c00ca070358002135035a000d005106c40001560350703060069007150b24505400e081c0d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 239935557 1250 239934307 239934329
    0x3010e0f04210c020f0409111201090c0b09040f09050309010c080d1505190308040b0a1707021c020313031704080a030302131d010603110c0303011403070b0c1f06 71
    0x1148040c000e01c08820f5440a034402c06005281c0c03282483c0c50700c604e1a15691001d0000c45083c0310700204120400306040c403058554840f000407000450059240003c0e11501d000c0d280c0710321589007804100c602e6070a4510001c1e10340050b1f000852000000e40d800d1340e10919080f0f40c0e40d400e516050035280036680c0320340c0005052200f29000003044880c2d00080d10015540040045a000302c05801d1480310312020300310030310810040c0981100c40c0024007541ca0181020039004012491116034403808440d0380d401070700b00c0b8040f1040002c0d5503c454001c524944003c0d410200030b140244090710131844000e00860071a4851820240c4010541d8000d040440c10b550103a00c40c3c0c14094069130090741441c0b05180524004241c2902030b0303401191410784144040440d82c24030030242c0081c14139000c1d0021b403400030301c006209950200006c60280560b04018004001080103043c505103da802c4104072150501403584c0e0400700007860310016264882c4681e80d00b02e52070058004050f0740d04840d841e01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 239936807 1250 239935557 239935613
    0x7020a03051c0203190315270606030606080a1805070305030325050a030509071a07050d0e100c020105070606030501022a0c01120b030d0c110603010e0f04 68
    0x1c000c03072490034205890889228201c80c451080740c4910640c0354400d080b50301c4000031420140300b0760248282c1e03c8442c00210303c4c079440303074074054020980b059108001c03910000c0b4040c070070700d40e401140010134442c02d05211032801c6c040701a0201d48010700ca1a4840d55411581c0c2e101ca48550611a100e6006400d0b101c9407516420f286440e6402260000342c0524000c46100d4480406000a851408165215420070721700c00c01c100c016000140c0074005900c00c81c940422031040420040641d45100381c41c0b5a628006403600e10f09140d4155001030a014031540d40080d9a1a4003909054220140c6040054007080b0301c0180c1f01c5001d04e80e40074100031b190610100400005600030102003141c1a01603412500460410080040342407404606400103602d400c500c1d4003400424075041ca0300e51001c0344120081001c01e1901c10444804000641107649001c1400127465084c0c3c04a101500ca0510351b606140c10b20001c03d10141c14580ca001101001505005100c00601030140360368864690354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 239938057 1250 239936807 239936813
    0x4140301020d0c050c01240b0a030605120f010615200304081504060b090105060a0f0203090d030e0a0f0e040f05010e0708061b0712031503060606051b0109210507020a03 74
    0xe5000102c1e0602c4035071030010741341080400992901440d0080d0214409582c5c1801c0030104c02790050080360301416190341c00841c06544140710601e180315031500400020001e0110282981c401d580420840c0111100551059074130030a41d090446052200460312403184000c01e24500c40c560042200d40211181e01040d010b101e45818041d60044509000d444400720402508000c00c2c411140c0c40030040001c4128203000c1c0d41d08200e4920700d401528100018038000c140141900d07001180010880041d8a1151030601c2d184005800921003100c034090401070103146024001d08040c202d80844a207400401000350002141e001c0d03040140c0701c01d00d40d02d43e500750b9600b5041c0d0304c100c0d200c0c0f4007071035641c4c0d032480b504155030340e40b50400d011107003542aa02e0158001c040c030080700a800c802e094004000325025002e400c00400ba140c0c0c1e0641d55412404081c10b201c002110403c499904104519001c201c4142ca101140d1010749403c200610300c0c280140d85030b12450800a4201d0a819000024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 239939307 1250 239938057 239938067
    0x1b0a0306020a080f01150c1101030902060408031b0609070504021614100e010c021b0d14150c09060a21110301080f0309180604111c0b010503090304140301020d0c 71
    0x520f13014640b080e80c80e41c03288600d0180031402c04c0703601e000500c001b800d400450181e0076002c48086060400080740480c40d000300351241c3c01500820402e60000a09a12246041001e44506011480a0105814202c503040d840b540c6038072580340b14640210319040c1c9282c40b40000d6088075444040b060304030840071032258840758a08104001c20785083c00071602d880301030041802500c0341e0380c003030540c001c4209482e10029840440041c1c201200c90740d0880007988002c02c61541200e030744001c10818110420000420100070b0001d000600f040c8205d18060b00c0c0d4030107503408407125041c6106120820a01e0307924001b902101400c100f42007800c00808014038100075030680d00c024080c3c40350102114443c035542d1040c004000d070888941c0482d906548070040c48103800c04130041020917209901e21401c040c0790440f0090308445049600c4812855a2911410148000c00e0030014114604200c0e45902c0740614410440c01103c0e8a00011582d0340a40c100c5190302ca040074208020f180e20000180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 239940557 1250 239939307 239939311
    0xf06020f0601090c2307020907020604050d050f0715090606060504060201060b0f0913020c01051608060d030207060c0611041d0c03240316060807201b0a0306020a08 72
    0x626004030700021410007103c0c003400e640340c51181c0752005508810f054001c11a0314014802040d035000b4800000182d407004c408074011031540d4000c000e04d041a007131290901e50b4000742841444000c0042002d0141c0000c10345904036000381012441c5600782170304201400c45080020a442e15144000c68050741004c0075000391000c0e075008010041c0c84040080c418800e1071a000100c07142840000300500c0c000d0043c41c040ca40e07203140541800c1c0142a180e083d60000e840c1d41d2078401c038444100740b50903440203400750700c491704484580101549440194981d140ba009810400c0304035291042404202d80044040c101015181541d9076a18000f185003045d044052035040d030403041c00301d1100e8615170305403030050403030706459616101c1044d442c080d54580505c406402d0b02820700d0700002d009052400b04003c01194031031411a1400650080052a0728a01d030403000c0c88074044007000480001d40000b03240c5042c41011424034000300007645545941d03100030b000e03a00000b01c025010b54082c4000d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 239941807 1250 239940557 239940583
    0x915020a030b060c070e060114031015030b0901230d0c05011b080405040b220e010e010c0c0b0705040803040b0a09140907140c0109140724050708040f0602 68
    0x10030a080c4003002194460f000c202c262990004000703100081400386d03403d0b041001414070385c504c40f0345000e401e02c064104031190303050252101070411240403541c1c00201c2b51041864100030003d0610b002691072030042c044d100c0c2010b20489216901001d4903410700109400410120440c2c00fa450102280354103406114001450011f8440e0052004500503c40c2e075030203e0050b060900f02403d03c0300911840904991200310500411400702041044901c1030010b2440415010581c45000e42903580446003818281e2500c1d000031a0f456108081113001544014444540d440303801044445010703640080c0a0740c00b000070f000804050b5080109084d100ca51501038095a542210740e80060808400341d8100f044031b4005110b048c4500803410702c800c1d411006500f803c00e2581f04a08584401000306c0c1e0302c1c0780094a4440844007046880c008000720140c415000c961402515180b012040340e0720180800803d41d5003c02c408642650094410747e500c0e8440c0d1596910025a518181b403424 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 239943057 1250 239941807 239941811
    0x20408030c030301050a12020a0e060d0804181d03090d020609040c1e05070b0109050a203606070f0b15091819050106080106060512070203030415050a0915020a03 71
    0x142c0030306203211100656400819000361640380c4200ad0000386001000301c1e0b4404102da01e0b4400240c40c00001d403018140c0212009075442c5c400c0e4000b4216903440b8800c0b118921030481502c80c220700041103c11140e01616100400e40640c0f0214041c0d00802c50810703405070600c9020f0300c0c008c1e03002d071040702445201800c800c410208900c0c155800c2c460054040e0195200130018001d42c41560083ca8001002c1600001c00180d46001d41c0c6e10f91111064664114600040030004019842d44c2041c12444480d0b003405070850b4900c0d014511850240400c3c01894089401024000c242e003228204a42243c000c0c001807411240c96800c80c0c82402c100c42c03017180f1801c0420b081015034a00a00c2c815101001850120803011f10a2480b0320502d80c1100d9940d04d554010844070020701a1000812154071400e454801c40e44d58041607103801400c010843d4002d01c20440030481c5000841d510b48030303c1c04000b81e107417903030007595010300101080500004426803205c044080194001d00c1e103040d042e071301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 239944307 1250 239943057 239943059
    0x103050c090a05040308061c060c0216170a03030b1f09210201090512121204030e031207032114090c01020d080a11040e1f090501030b040f0204020408030c030301050a 73
    0x11040c1110004d80d8060000f8200b140080ca25060030200e02d5850f050418810341c00d00c103e42e8070074060302c50140400005800403102c3d0302007000903907203480240c4400c51f006a110f0402c20b0b000c070b82c1c40c051034401070205034842489c2d5903541c84d41c0d106001008001c1c0c80c946180e03401003c014040c0061441004922100c0c2d501c9032280070003500d851210300b035050350350301d110a15060400c010791054076520581c0d03020b802100256a0305480040013421b80d217a134207040d14505401e016151642805515001713410000690740403200b65811a2007030303581810241111240c2c41141e9040e0010100c107030407007514106c50554664070f00000180f140d20031008035428010100e004a848004080c44a0042024600412418002c40c0c018600c0310f407003c00c9850034280e8807400381c522070394140d80207480060380082d103500c082d400141c840064810100240881d51542d030703803240300410091014003102010b41c0107004544c2d59404440c0105280d404172034a82444070866502c0e540f003072144901c61100800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 239945557 1250 239944307 239944321
    0xa061d040506090f040510020a0c0b06030304081c0201060e01030f11061e0304020607020a180e060609070c02030f030f090a080a03200c0315070215010302100f03020d050103050c09 79
    0xe054482d210180000c0602d4a070003400c0100c2e004003500403130701c0380103a050002001c0c080340b001d4400e4503181e54804100b1035403414080188034001e8005400782c2c00800061209110001da101c0c50b0300341260b031121004103000c00c203c0c01032415400912100041600002c1440007016502003014000c0502c41e400c403e400302004620702c140d90304900031160309a100d0000c00100b1002d16406400500340500d8100280d000030084041038000c2030200865420040300c040b581c0c4520120402c1610080040e4280340c0001400e19400030030b2101003140c03100869046450a00c0252903083c004000c69444800810700348000f03420280c03582e030103124018000202040c000880e4070b011601501d80d000d5245a03e040c89641184c0106054554429a41805105d840c00c200d90b82c04602c1000c40250203017800140281084030803106d00500d500802c00600c00344e034440d43c0c2c01409000742d0070030b408601c04918064000e4050700b18030484031480d1800000a0001c041401106100111050b05041da0341030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 239946807 1250 239945557 239945561
    0x5040b060f01110d2303010e090d0f02060412020109120f020c1c0b180a0302031818072304151e0c0209040f0f050c0108010f030b0a0b0d020a061d04 65
    0x40f040100380d4060100342c1c04150040d40c07080031881a4a100e00403407400014414000d5100ba4041007400d40a91700308184100f06101c09035000c2c0003450849600c8505c1301009550700c9018202414503500350a00f0b04015000350301c015041a80005861001040381001401c06604000701c02c0140c01071040000740c0b85020480301003e44a00012500030800a441d41100d4040090000f011811f00c00301d010b0310340c0000c00002400c0c51280d4021036880c040780100107014008201c0c90780c022990700000d2088041d074a076481341d00c41e00c585800701c4030f6007282400d5005910352a03d40070001500240202d0050b6869050310303a000709036115070343c0030000403041c10b412104208007170000030340010342c0708010714050483c41c1e000303400381500009481c0152580012082d11010403596580444606c82c030958024040600501011a42c074170101d01d103444070040e440000b08071881840d5200d03480e00345641d4a008501d442500070700203038071480e00c40c00d010b0103885078003030008406000c0042c00e1203686014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 239948057 1250 239946807 239946827
    0x50102070612050411030609030301240f031a0d1a010e220c0f0b03060f040b010f0503100b03010f0314070f0e0a060b0c011406040c091e050405040b060f01 68
    0x169442da600e8800c060210382c018400030308100e03a0001807102e100d980b0b50342000381602815603103020316505e514080446605076050784200b045201c201c0d60540d14550081e00c0c6110003031306030801244212207080b5441941002440c0c0507404044078600d1414040075440325441052481205070b500d98030350000a070006411070381c1c0f102e540321451442d008585880c00c040c000e02d124103403003d84651110307902d00b252006a002120208008000c100031481d11641d1810b40d1481624104a00c21440740020700704e805120342641401070000204000080d2550044004d014522091351a2758444503003152020341484152030184003040e00c0c1325070707040101c2c9140482e00010003103034420303240800d012031241c002090070080740d41c0e0743c40c0002d520040800402c50b1218841c00040d100780040b04150390000050034280c0030f1071505150800d01a000020a803d860100c1000da1035000c150040c4a050b0455401035500f043c2008184420040640e00d424051103003154055904c611100c01119400700c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 239949307 1250 239948057 239948069
    0x120909130c030f0503040e0c1c050412030b0d0501050a0c080114030604030c151b03150e0c162108010506070c03030806010306050a0308030603120f0703030218090703060e0105010207 80
    0x2040d90304000140f840540c140c0c04600c148152030602e0f81d15440c074481000202c5464000c00400182e0b039503d8001e03101c080203403800f019410042030409890f12101010351680031001d05030341d104400455030301d150354902640c0d4811700078071852905600f940040c180c8640e40c800032440c8140003080480d0141340c01c0d1080343d0301400411007992551030403a03000d140c011b01174074194849400b003c004030080c00b421941d1a40c03040d07002015404070000500711441c0c1e07a0406040340340c00300c0910014a001d01c10175003001000341e00d01d450b1801003004000300003990600030403820800c00c001103a402041c01c1802d883c034440d150008240c1e621810f210340e610a00070010701e0072141ca402840040c3c02811300d41e0b002201031500140e415110004150500401d800507121184003200b0040c0ca8a420805002d20b003650050701420300b17181007520a6680a002c10080030b05401003464820360440040b40030080e0390080c40c401140c1465500500141403e014000482c402e103400401c20f5400000c0500072200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 239950557 1250 239949307 239949323
    0x5090f07030207020d0b070e030d03110301140109080a0605010e0708150108040606081e0d09060210020304081c02030702010c18060311040305060115020c101202091212090913 77
    0x5210030044009500050080fa0302412810718880801c8050304020b00c20030a54032400340304442a01018604008030807100205410441e040030102d00500640c1d04440015500500b11002c1c4401a100c02803503411445007442100c2240c1d090017400d801580c100c9001203020341540e1510742040724000021548121000c0741c9050200d0706500c00d624096105d0f01807440010810344450441c0c1c2410005400840c9a11448007150720704c000520041c000003c850900c0907080345031010107034442d05002443c42859034080001000c0c048900c00f103a4412944100000d4400420102c010080d00161840401586080300017825280075043d0640807800052001101602d0031004030060044c050740000440c0c8280310020004d1010040c442c042c0624a034010741064401400914281203038600502c1400d2601640003580e030001180d580c10b00d242c1e900580d44180354404110460b8070034814a04a22038485c0500d0140003040c0500703508801194000b8940c0c60760400011180028000a000342c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 239951807 1250 239950557 239950561
    0x10140102060126070b0307050c0118020a18240e0603010501060e0d03030209060a02060105030607020307080a110a02130515090c121308030a1d030a02060a0509010905071e05090f 78
    0x440c00b601440624912004440305a92604020175940e002a190080030410100364404198000e000f0600d504042c24602e0388520780d02d8000802862a40c803c010408001034011a07001d1501c0c1c025100a000c03400c424510400110640700c1101a40c0c03107891080704810011420300d01c0e041c06254100c81031075517080781c0c082c2108100000d11002d000100c0030306500b040300030740c540c441c0e401070440d0000c0354000d808035601d0041490306003400100b490b401c64208000750740000f40030340240e900b0303109589040511110450300380d13490850903081c06540b060740304010181700c0c502a00214032400f44251202d10001d411403c5c0a04901d050754000102d150502c00c0d260384c108001800ca82c800c519800442030041d5179200c4c8402c1d54020f50743c0c5070501d0785035200c1c0e0b029212065110f00606145200075844d04035480802502e0f0a0090115428292503070045401000c094100040c055001819103442e15550a1491800310340030012040c900506c680006591500c1c8000710f00c50181c21349049029 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 239953057 1250 239951807 239951849
    0x51314070e04090219240c060b01030b03161503020408031821010218010804080313080904020f090a0f06050a050708040b071109061906080a0e0105101401020601 71
    0x600390405599800a6650034043c2c05a541c038100070102101080404072aa800c0410742ca0740c0e012a80c0c0c0c00641305900c01a003081036944422188501e68200740c0000d460400400101c0151000c9818181e05115402015a42d600f240012808944008013485042602c0080582c11703801141300c0e2560300d4005100d58819450020090884401c0042040c0000e443c021104040761180c10584001603601007030008a10844000750081080f00f403c1020203850250750343c10300340c0700040074032840300400b41880b0b04020014044d903500c004028410354840f4200b5145200700d41040c16258440c1d512400009080344028000600341c5000b80d03030305031510300b9072181030701d00381d101035001c41d809541040002110f1400c0805442070a00c0740011a400b1018030381004002c01c0080e09492080d9510841c940d00f9030f420418040c00c86401d82011015651034058100c010b040038000d074060740d420101002000650392451b0800d0307800002402e05102e206100490791818240195644410212011518 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 239954307 1250 239953057 239953067
    0x1801021b12072606100b0706020a030914160b0339040902090120060105010e030a021309032006130f0609030503010501140c031603020f010e0705131407 67
    0x81101c05822074104664408070291200c1684402e2100c8050542481c24014010b010403904802c8030401d001150f81420030810952151210003030441e84e0014045c0340c183d01030f81050313088a0701b240b010158030032101007542d224a150101c80d9403002c0640c0c000300d21140d200b016a4000d01e20741e8460465040005a446440d81b10101d207403c8a03480c00084680c0120608010406440720302005a103484034140003401190904402c10403e0304a80180650348000141c0c2a04544003440c000602d410107074046801c04491741e02c040d40000b048001948400c090342c104c00c0c0c010b403081e0359609002200e070303081d41088900e505403680f0070b0b040380d00403e001d24049626054424098030b11151480c0d455a102c6c0c0c116808144206c001c641d02000412403981c1103010000c0503100c0710802c40c6041e11580b0300a8891080503062030018500340900400d040c400c0022640c00d201d8040200160340c44100c13515600c030420321645100d88544010100140c0e4140181c40901442c848190040d4494110a8030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 239955557 1250 239954307 239954329
    0x14121c050a020a0b010909030306090506030c0f1c06020414010518011d031501090510030f062007050f0607030608060412050d1104090c0801050105040b0c011508031801021b 76
    0x1c01c6102d07000710740021460030302000d802014000c8000802204a14000e42074401030350101a0303980c908002c103d0180c13004141134040707083c1215181c1c1200020700004541255450041c0652084489200d04001143d03008006444284140400f61580c1c04011070f4144a0100e02070800e9031140c1e607109065004003a11051340c03842200b03840d014050340c0f000c0782c90401404c0007a82071088403001007281004074440e03690401200455a80307420b0441c2c507101400f0505810040c10365994400017410100d0710007180040c10350b42481941d1b260051700b07084c1d66800c1850004003441c0256004603000c01d029108001c2114541c1000d000136a80e10f84544501d02d00e0200c2000c1441010020000e2038150391040e501517500000907661a01d0511848034100c6001c00c40e844240f1083c0e00040c80f55a030824103035421554408513459070790b400405440c0c050000a4090005a601440081210800031015184280c02400303441c2106c0c000c000120307a182005c401a1070815013040100040f8240f48070504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 239956807 1250 239955557 239955577
    0x20f0a0c0215040b0d02301b0c1213120515241002010f0e0d02070801050405150a02040b190324090e03090d05150a020901080106030e0f060114121c05 66
    0x1581c5400390403071104c1f9900f9070000f9403021072649800c001403c0b40764520a103c004095443c0350401c0c3e06605060340c1c07007010b1801c0788405d510128286510303800710314014020303103444680445455000d191243c0e0300c80150b502405103450440000d0203030025071400c641d51404002d2000e012900460511817500c103074800c000d0442d520380701003100c00c40b418040c4127600081c9800030503410803803041c02420040503400c10140b81e41020305020120750005000c00070107141c86e083c5e2074940c80b4007910308001d110300da0000281c0040815540400b00070080d140c40186090380b8140b01028030540740d45909808054000413041049005002d480f803968049040d400d200340485e07207040d1180300003814190545104032207540c040b180001c08422645d0000313802828480c425030038400c8050004e408144140201c408050f0340ba0001c6450030b00410100c042080072000740d50003561580752001490505084080c000c02c07000300841401400001d0082d2a00114040c2c0a0215140034045500b980004110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 239958057 1250 239956807 239956837
    0x10311070605040b061302090a030b0907080106091a10090b03130c0e0105030c091b16060e0c01110307050c1908060a02090405060103111c020f0a0c0215040b0d02 71
    0x40000035505209030760185020364103113481480c0c4801080100340c0380c02c2a044440c4c4c010b104d50b1802c2c0e12000d800703034192503100c0411004d9954001680e440d10301d01ba0300c02e40340381d070800c00b0001d480d4049038050060160041d01c2084444d044a0034007482008a504440001c0e9080c40301f044a201c908000c1d54009040307010303141b01d032203894598116440e0b80350042c0310100d15401c0100514a0b0802920b115880c00350b41c0c5200c20b142c4007101c1000d90307040107030a090303d0200090011490700d15900e1001d030325612a400700b000b0800c00d01d1440d0b50354501d540c2503000c1003e081035000311800c00825030b545168883c000b0a000031642c0140710300ca080c4003208610b5404800400310700b0703e000344005841007000fa400113231107a51a400700826284094105814149010071000060200382c00b1180e5410000b1075002242040d482060000c1c4070f440700c3c4611200d404615100169448680382d60428000c440e41c03007102c43c0780300c0121020321680c418803140800800102511503c1390300070f001b0242c0e202e400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 239959307 1250 239958057 239958067
    0x6120a110406020f0607031506210515031608030a12020408010509100b1008070f020a020406060c1406060f10020c030109030905130c0e011803051005090607031109010311 75
    0x500d00ea422a40050b00940c100d280d02c41c0d10703018104000c9a00caa810f03c2e0501034802214104180204107004030300421170107600c26082e0000003540b1068841c00c202e400c006a29040181c60380b104c08489409129020303052844071007070f81a0650707a00b0380e81c0d584099440c100628100b51010f42070080301a244d29004c0c407000900302d41c00c2c40b03903600c9403200101810500541000c00022650900400742c442c40380c9940c80c03028158001d90290f844415400d100c1c01d4142100400c0c1e16050b06240025030103428002c011901d29030241003400242d03c1102e4042c422038408004507241d00b401c5403416041800e004802e03210745006c3c1e103c4441c51b0141d006541e0322a2041307005c6429a0b40c4c2200075008109144000c02042c104000b042903000c2440074200a40802c00e0001442070031400d50076410801c0000c0031505c2c8040c080040801158007000700c40514004214180180a04942d4103e0358043c4500003284a402802142541d1440041c8940707050078040054004100e1301074114410344003401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 239960557 1250 239959307 239959331
    0x40b0a030606060f180b030c030c0712110c24070c09020310030201090806062d0a1203090806010806061e1306080c010309020a050409031106100504051506120a 70
    0x102d040082c0096a444c0080d110058030080c0c102c48411149052128200c00208103808101d02aa40c001404250207580c0782c940004103052405088000b82158a1140c074540f0b500343c00c5503000f00411320010540304088950b00801c40189021542090600c0c00c040d001d0700300b840c0180041940c10310070112a01500d443d424084103c4e0411030340f003442d01d4034124040c000e660700102c030b1800508241004103041d240407004500801c404018080d26408600c03100f04007001c03040ca4182803800c024042c0b41c0301d50780e00d901011508039408419400705450078000b0407410300128899050743c002c00014510b94841005100b24440158018034002481000c4403c0940d01c3c4141e41140b030602c003002084480c10b15034054100b88550512038181850304c0311031401a1520688241113460880c0e002480040b1814280c40e10420920f0041d080c1c0100c500700310481d00f40c150030000303032102560100010b98500304040441d10884604c25400780d01408612400300c0c880c07400715881b0b04054408900990020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 239961807 1250 239960557 239960561
    0x11010203071a07080f071704111503011701090b07080c19080403020f0c0a05060903010e011503050706030b0d060504030e100f080c090a0b0703090518091009030905040b0a0306 77
    0x600788000c0d09845403d000303a041d130192001d5003112144010100c00c0c01d00c62809406c2c026a03014811880414800180910445480348607201034040d14400c400211040904e11543c000d00990303c900c1000802400351b5401441080f00300b690004002c045511280c0069034a1080101b009603540030422000d8268541060704000c24031064861a0203400d00746070280c203098078002543d1940d40000349426841d581c0003200e03002c40d0426100c42c1d80e40e116000102e03000d4203040284100a42c01e01d022403207881d0300b500c80a801c48e0b0041c0c050750368558a0341d10443c19120030b0710b40360fa4001c6091410b0008100207901c06a0031500c07034140000441e4503000441d501c207030000560700116404509607041c00d80c000424a0780150400c0d1514640a0810001001c205542c040d0a84102c00030a000c02014054403032900904001041440400b2100345824045541207410300000d014400c40202e22120fa8040d003440c06606886d2440c2c91401d07e028000100881c0741026445800301ca8000003040443c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 239963057 1250 239961807 239961833
    0x10201290603042402120601030e120c01111204150911011407020907110f060402030d050c03040b030c0406030b0102160b0d09020402130306050c03070512061f020d0e0604030b041101020307 83
    0x14407001368651031624046c24140e04002d0034103042c942004407d2542c8040428a03400708121840001e4460780c549980600400c207030007056140c40400141d541e451840c001e0303401d00c40da00c07502c80c001e000020b0125100540d00e81000050845000050700701380f82d8042d40007a02035030301c203422060619419400103148640d082d40c80e0400720b1401100b100d14a0424008118010403d070002c140c541801e501107561038004640d8103040100c042180f90388280309108403001049000703030540d102c0c100030701c00c08801d42c003070321034070020901c0c041c2c081314654004900303040f0317a0101c0b46082040c50f02d0b2243c4d41c0c99580c0483d15540c0306030b036900390000050f51248060700c07040d0080002d1440f918114604030003262009807100d00500800e104002e1010340c800100c6000f14085454008282ca501003c20541a819103808001c0d1300e5041c2307040750203903000405000c148030b00d9036200c131420742c40e1003031001510a81c000504a03c10041c0001d020508441c0c98012804040c41140d180c00101d440d038400795a00c17 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 239964307 1250 239963057 239963123
    0x80402011713030809030408100f02090316080106060807020309010f02030910180f05090c070c031707060606050f16020a0504020c0a06050703110a1b02060d02040501020129060304 79
    0x300d0a4040030f05501030780703056204221000443ca000d00345044959500001103403140e420303440354068145400190151458868007504495a030f00406148480c271120302e000300c000942c0b0b05000000c1d00ca2190702814050720700c0e42c02552526820400450741c880c010000e01041d448108105c9806440d0300304030000b2083c280c0e40d0501008202504242c0902e0350b5805103a0000c1a108144916a510b00700c4541110034400350668030103840ca00008101c200d40c0c005003070104282c1c1500c800740c40c80c0c0b0007815214441e40c4100841a2070b00e8099541d4000d000000240c0380040c0510000000c185446005c0d960000f480005c4080d0b40b5400a001c0e40d21a50f00254140c208280b0300081150a00070150425041d0505010b91441e810122050780281c89a80c400c001c00079521040804034042c00307a440b207070094013980d504c621000000020b54424410680103618204e03004800302141c5401a00d01911007440300030043e002c4040000f07907000640140d924448030710407140d06c11100410300c83c501107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 239965557 1250 239964307 239964331
    0x409050d0e0a0b070b0708041407032409080405010c1104090f021f0503040b060103140f1614040b0c03040b0d06180e060109020d140405061f0e070804020117 69
    0x1c1c0501481080e000030ba00200c60207805001003030000300103200c22540b018151504a50658a605011042c0403413050b041e59180200760010040c0511540c070205111918041c10442080d03070101542241c8500001414a8009100030700583d0701c64032005030a00e0103191880d0050070040d0004d03084550940040341c441c04d540030801e0450500c0a02092002080012003541c1101c29030b000d01684001403004000010343c00025059a000e07a04c00c40144011616402d158507028442582c1002c003603a02a90008041c6003280c280307885000c3c8240c0070356045212501b414500300081601c3d4002c03c0003202180014080401c0c003011400c0900b14580e405d000c0450114035103070310301140360070303000c0c90403000e50030100c08003003068000850360304483c0705400050b544c00c4091040d1005084c0c00000d40e507241588014070061041c002820380c000e4044010007004540080e4a08480e4241441104e40002c220300004003414001c4542e15400b90040c144000c44801502c01120260b00490f041c5c0c84482d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 239966807 1250 239965557 239965577
    0x40515092e050c030121020d1b0801110f070b0901062d0e13020f0103060914010f05060a09090b01050d020a020f060108070f030b0402121203090f010501031205090409050d 75
    0x403580c024203400905010302e0380e10755414400e50b28196002440694800c10200c2810001c5441320414481849d4100c030072440e404916900b00700440c01c99104100c1c140d0300b0311040101400c480e400b150060121003061a140c100035940701411030b14010440d8500b550380e84000141115031040c591034107038003004401c1514041c80c440c07046400c415001441540f000030304110b15102c11103001401690100c4402001219040040300a01120340140322000d003000e5008840c944600c14080c1030b20290b400c1c000902d6142e42c01d207c2940504440180000e651400422500140e6130000c21a03400603d000ca18102d44444c0d20000d0380d000010020042e0b03c04042042409003d20055016000c2034001c0e0055030f160500c5040741e0611380c00040c104400f83d401003000c42d600c1d682c038094168800802c3d0388090041006800051300f0131281c3d8840c90040fa0100356002070b040c070406058a502054401d011f0842040072141d85d0000380b100c6070042e039100c0c1c00c3e00100c0c1d0208a400d500081070380e070b00702a607 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 239968057 1250 239966807 239966893
    0xc1b03020d03051b01140123030706050d0e0c06070f0303020c16090e0c0a090c030f06060831030c0302190c1d0c1605150108071d04051509 61
    0x1002078000b030407001740d24200d44e0841400c903c1c8101b81c11100c80c120410307140c1952002d4594a00801c0848552500c1689400181280c00502405c8188100c00003004000e0720760501545411292007495070056040280c0c00018100314000f1022034000e14006050488a20440c1e10380f170409a081200d4a401d00b0082020011a019085203d803080025040710590b0350701113102d0725100d01940300d0407501d50840f525240d00c42c0e4024001c1014424090041d10782d0388102514456050321002200c0d0001e03084d507000d02d00c0100364000034040503215001d01242d203440468800241344070450031400361058a1400030b922070058550b107070203000c2d0250583d140243c0301040e01e030700c04010010302c041e1008018955134103409540c680d1021090068000c191031803e01c1c10500c9000000c10404140303400420700e02d500103000b4040e500411091107200c0140661001d02c1541100e00410070703807148013110300415549141541204003042201d00400d400441c180078084196181c080c001c44025210b040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 239969307 1250 239968057 239968087
    0x708130e06030109030e040b01021f0606090b0c070603021c0504060b010f02120d0e0705190614090f150c070806040515040c03080304050312070815060306010c1b03020d0305 76
    0x1e04034002c20a161942e500601440c460352402c520865842d51940c6480e402401141220820320003900c0700070920644150040c41d00740501b0300050b80c080b10100d94a5101c10441e2482c01c2c03240001c0407c40d00d8031404034003940c040080c500c96400e4201d0f03d824504900d0141c0c80c045c0e441002c0200c2c001c2d000c040014003901518040808640c841503524040d8070364581103542e141c2c80307813070040b4140d643d45000d00c2c901030711b551101c1e400c031215a51038249480030305044004da0b10641e840c09285014040f61842d207004090980781d02040d40780400a091070000c921060181c03c04541d2414420504140b5080201c40d91228100780c20013020001042810f000400000c20f0b000c400310a90f007001d44410440f04c080e1302008044c0c0000002050600a0403c10303541c0d401003a54111407180351040f001007622805a4445500740c4015505000f11300d03214040d2441010b060f504c4018204580e140c1405080c000300e00c4042a00d4014004005a2514120031610501079140d40c7d03920007581d041707445 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 239970557 1250 239969307 239969311
    0x903070b100b070b0604020912030a03150e0a02090409140102040905060612041403190e031e06061908030d0618061203050306040212040b010501020d0509030709020f0708130e 77
    0x3801c415005101c03140c1c80409450f561500244014071030b64030130000c60700900c030711107010350300c0034891400700d510800020042c09103808a650a02000d01c0c8004100c862191501440141084440005100c216154003403c90548014404165101162943d680001d4121440b03841a50002070074000309400307004994204100791052450940101c00c00386130300c1005400100010003e982103900800c00b00141c40c0c41c81c484003182d14258882039005000d100c00384c5020b60180c002e808046c0c0151035074126408184203200090922550303210704201d60402060009202030311080d8002c13408140400207407942450512002440c1d904116050614400b5807440c06240d0b82047c005010840082c1c000e04881513050030039540382d0f1601c0c000100640110900c0b0000502d110007044140010408898100c90f02038007a980040c0f80b0307001c03c4034244907290007507816601c148001c020015060f030041160f2a42090058107200b05959a400c0c40c1c1c0c030000296410620540f4144019800810415 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 239971807 1250 239970557 239970571
    0x20d03052203050a0206031e090d14030402030d0813081215030703051203060a150903060e01061a070309170a060b01030b01170a0b060706051503011107060c0509090903070b 76
    0x306110b03142d556580c0e40c3c1c180d541c8000f800f070301002c80030a001114016521811510301c510816151810305040d5a458031002c6214000070014880359141c2c01c00501140c0c0078503005005000ea840b200e50080e204002e000c2c091b000035030b100303d00c101c0c04101500068040449400c0b400f403140d04000520050644000003001c0c0309820010b0100002a00007400d0320b0115500d2000c03d40725500c0713400160541c2211761001c0e0105142140030a5043d41c045d2580f03090700d00c21401040b511001814080c00c90309580946001c80c10320101040c2c038040700f80c02074000c1134403c0c03600d4a41c05480b00505413107d2514028840329920030940c3da001c2140501034030b0761640017840c00300300001400000814400e5a1901d0354004030643c0082108059560440900002e014045030b69a001c0c6250000c0248000c580002950748659210300031803070180100c0c205046060056402d181c4541c40354070041c41c50350b00c000b007400030400c465190b644840c01c160f4841d000d60405140c4900f86810140c03041c0c1d900070040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 239973057 1250 239971807 239971867
    0x150509040b090601300c0302030417031006030504022701320616020405070c0b06030106030803010b0f120f04030818100b030109050307060e15010501020d0f0c020d0305 74
    0x15590748081680c459005008040044866041c8a01806034820011720070807030a1500342d8091a0b056001107000d80c1c07140321400004a181117142c402c40c00f0070b48995645604103a410012640700b608a280c000303000418121624003003100c10220303882c0310b040400750490480c004000320a03017403101460244460780d00003546588000c440b00c01c1381d41c200a091181c80040b940e94a0030b4120032041407842e5019200300101d04003104040c002004802d4100c1e56480d002c40010514103060040318202c2e540207000ca400e6908044000b1202d400000d21525031303030402c0c05000715040d054080d080c0160450400b07000305080c207003402020751034002c100c107920a200c00c42c1d240c0d42c0c0700c0000b210220114444400103101c411600068050450004003038003070320011132082c2c02d0000f1907004280e000d400c1c504541d80440b1400646a15039400d12039640903070803002607801414000e2200c051010f403107161048010445500041c1c141034810070540c000b41000c210200c22015040e0003105405030304100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 239974307 1250 239973057 239973061
    0x624080702030a110a061508070603061d071103030f010501030507020307020904021c080d020c0d110601090b060f0d05091b0d0807030207080303011e0e0105010c0609050304150509040b09 82
    0x40e540c1c3c49030181c0881000800901c401c50400244000046594485c0c020301440c503036001995002c22550250100078055164005603160007071146008031040910f11801078056400345109040e8000e21034014441e00315808441040b0070300081d17210350070041c0948c055505010005049030f10081125082d90f00800124001d6525141c072130b035209904952005503410040000c040122030200b005250650100701c0c401c03500074907005001401ca82c002110004010071208462040c0b1150500c0f40a0704030342e0052010303034403a4005165090b405401c3c2c515041390200d5818403940500c42c9400c820369181c060107043d05003031201c0c0c0402d0304404907010300003404800107641450040001400d4940005441c004c1500034001040144840b07000c2d00d4596079590100c00e03502c04e00d4426010619510040424180401211107040c2da006a594281203012551008024842000207540b00d10090100181c566282d51240d0800c0b100c41d078806840c0c607400c200340405c3c0c4034141021845620080e007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 239975557 1250 239974307 239974321
    0xa090b0c0a0b180c09190c080412090b19050f03070305060103050a020a0905120a0506040b040605100f0b09220e0c06070503091c1a09060708160e0102010f062408 71
    0x500c840094408a421000f203842d9011310301d0280c1c07a40c8050790401420310213a440555000054140b241340251079000c95066840c01c100c0368010703d400341e1500d140e424000123700100da04150a0080c0726424040d14240f40514242c1440e0001c0b1112000a6160010400309507814050b03190400c0e4202c0081d41031550101c009001c080b45401801d00440000d80002035856040002c40c03981908041506c032141454100452034000455040c3c1d542e908100111b00400c4400b1064000c8440d990010314a60303050002c1d05a540c0d03c803080306540406904001c130f56090030101c482c0c0d00014103040005500c24108400c90600c0d0200e00140e10403103007403004001262010040b2054008211946800c450742c0010804c0c400714003180c0075050f00d61704882c0c803118142e8009003074012a46141241d80b41da4800c0d00848507804c0c100c0342c4044a65201032810801401029202000801400049082c240c0c0d40c008800721000e551000045001001919510140030f030459408105e003031500311100d10b4a01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 239976807 1250 239975557 239975563
    0x302130608211c060b0d0203071e0206060d03050c070905060102071d01060302030606040f030f020f030a03020a17040e15010e01170f040618050106051002030405090c0a090b0c0a0b18 80
    0x802086a00200080080f040002c19409400542165005682c54031314445880d4025041200c2c80400b0a03a00e0944030303944442160301c86481d0103130744e001b488242d4401081c030212840642084060000a008130007812006000d10342c050488145d000901c0c0c9041d0000a141c0001c070f5001c140c2e400c0340121100541d8590f00321060540300203040141c3c1c1c0b51903101c08120548251351100080c0903003071601004004090460401580c021144201880080c90805480310400040100564040d103004130000305006070008540038450212801c040e5181c800003003c5100300c0e901e02005403242d80c5004150b03040a80c01d440c00100307107094010420084100b0820307080c0901007a0301312414a00082c1004030741d402c00704010300035040601558240b0b1500501824040c0174603031003240c070710803c5041c8920000c1074030110350004005c5c031403075110180108420390000d01e00600b0048018030125100c50307910001c01280d420403004051514481c10010840f80c809002000700c0c069001807035083c40c03000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 239978057 1250 239976807 239976817
    0x2190b0c0c07031e0b160e0d29011815090902130c080901050f130b0405070e070f020c060f0a030c032c060f04020303030f10030213060821 61
    0x8841a0381e40c610012151410369180e00050040b081804200040e240210140b107059210324842040d50b2030308080c103190100821460030014100480d088030fa40740214504d0075182c000d0841000040c442c000c416030340340c0e51943c0008801d91f0400104042c6059400707022080522890402c0185100008203540d031103244152049103448141c039500355522949100c00780c888000041141103400c841c05070550404840c6c0a165500e41000251240d461280f074500c0b942d82c03078480703880080080e6031702420148050b00030303109071248803004034259260f241010f0140f907041e201c5000b000020300000b460111a24409030048500f40f02d68201c2950200c20b030341040406040110310041518000c400401010149001c0718154a13000c000b07085000d03a050031b10b01c43e49c4050307c0013980c5006995051100644000303406a1040000900443c049842c01d03801151150200407810ba80380c00161325481070202c01c1d0100345d582d00b001c01203d902084180520b1400c512052002c1c044015000780d58018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 239979307 1250 239978057 239978071
    0x3051605091603060b03010f1701060b040b07140102070812010f0b0415210b040c09031a060a1205030d230408030601030b030f1c170a0914010504050d02190b 69
    0x40750b8040d80000b03000350082800b8061107824661290f03942d02d1b03581104c8500c0d01c00e45070b8012809942c55203620b41801100d0a903220400c0461030a0700c0c003240040075501240c01598800b030003280540c07204c542030000780000c90045414503124203566200482144042c0d10031401c044050744100700342024501074800700c80703961801d1140d071104510107032403d600307420406540c0c00000c26000e23481036407a40142e2801030156020040346d203c07403200307541651a9010240c00140903050550210707152003503241c0e00c404040c280b03000140ea14044283c408042c3c400896441e000810241014005031043c00039003602400481078950400ca0f15022141003e0005480310500000040d100d034006e402013140c840307001d8100e400760406440d03160703200c4540d982d20400702030111810401c4e2a00c980380440310715401c213002940544079504058002c1c070080b80d080340c040c1c44e00c2c16403d81c1608284a11403040e40140081d12001c440e050000b4280760920f5140c415201c0741280306800b00304002a00d41d80450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 239980557 1250 239979307 239979331
    0xf0105040b2d070512070807140a090b0a02070f060302041409060f12010b100309060e01060303050d05090a06020408100b030d02100504050c0a060f020c030c060a0e15030108070305160509 82
    0x95080f001c84003407162981c0980c41078482d800b440b51242d4403140035442445550707105100f620307807942c0d00441c42c802c0d0304416000a440c40c40c14081c0094440003419940450300484148541c0c0e44080c0820f038107558492400300764042000c000d9440c1800d1401c00e80c0600710b80454552518900080c0070b1003048814a0050f907180714a041074290951004510000050150007807404800005026014400084455604001d00910900c1c2d05000e000b040d40c0d40b6496060903c4070440414005140c0200f00c01100d00c01e2071744000114106200030070280500310050b003100c0181c1c0704040140c8441d1200a8082e504c1261039440c2d82e903000c19580d61021140d80080788680780e41c10004c1c908142450724551081c14840c0015006410107002141c041c0203800703640342c085088081685070803203807011640040040048106851050040105661000348070041140301c0300401c0c40c694200741c129042c00d5014800034010300c40104003000c0130151540651220f50b00300f001045c038401026141031050301e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 239981807 1250 239980557 239980561
    0x1b0111040e180f0f0c031c051e040b0a030b0306010b04290a05030f0112020306011a16060509010b040b0307050105030606070b090a120216060e030106080f0105040b2d 73
    0x40802c111400c4071026a0046074540c24210001c0e0341c031401a05011081441484449001c0341008648040200c904418061300c1c8214041c0507111684226850304101e07481c880b90200900c151000b820141c440300440f1602c032084580d028044490880c1c030355109501030001042121260307012174003036030f403c00210410702031100281c00c1c2c0415009048402c015010503a01000e991000c0070b940700b490104856461031342e0b40c0b01c189403d40c0c02c2c8400a90113811007801444040345944a1103014403815000310302d0443c01800c003056800c05100c0449038261200c090191161090113280032a401c1258104001020200000d0b920310f89031180a041c0140400040d003956940010f9888054008040b08620b18106421940b604c20a41080794240541c89402c1001840010002c8401a4013000781040c00c2c10070308117441c003451002d0304561640d2102400315107108217101d4001d015006000104081c20246455181c00034010080d9201da20300d250707070b990306039412890803810303c400d0549a03c10f6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 239983057 1250 239981807 239981821
    0x2701050103230417211b040332102a05070b04020102011d0102280c0b0907120501052505070803040f170a030f0501050d02091305010c051b0111040e 65
    0xb8000c9000c114220441c061600d100c100e0714072071a41c45006400d400711b40321040040304041034002c1c1d00014008298001c500200005520030132260044034070a08410408403c1c07040b450301351060005021aa100c48180d1004203d00c104c40d0701070390741e04843d80c42030450100010818040c00710081c00c010b021070081810f5900170b5102c03103012100c42c0008042030684d0302c8960b0207544501039014440c3d05052025840d101440c0807054105010341d41c00c030b00c21140b9220080b1241001d4480101405120302c0000c4020881c4040526103220300004506071901d07180880310801c203518015005d45d02941e255040c65808412102041d62221070030b0384030348803404d21205007482d8101c02480440d1141c08003044000d84000b51500340c40070382c0d05011107503d1803401300940b07a00b0301c60150820a62004400180752400703002c0d03841508014900d507609076a8541398291014243c840b00455000200c0340740c020188090300500010540003880046200310f031110851107180314040001989001203804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 239984307 1250 239983057 239983103
    0x6050d051807080a050601060203030c121e070906020606030a03050415030b1804060b31111b0f06040b0f0601020a02130605012a02060927010501032304 67
    0x44003041046401290311008065031324105400207541034400c2200018150303100108a80c810071030103101904188001ca180802c1c00c40240004050f003080305035445186400c5c942480c0b066801e035641c0c03001e5605e4484080e00f410700292040340039800c240c010201103074100003118100d516038403045029400b9160110300811042100310341c00b51080003003000582c107010166000341d02542c82005036014140400c050349500940800304492100c0c900c0311030009a2528864900540c8000b040c01030b00390b1030214140d40035040c0d650300e26480ca550038000c4402008000d01204034007005101908141d162201d18620041510f81c0300310100b030006040d0f034803c0c071049100c80d5010b00310201200f20317507480c000070307000030f028042c0028156080d0108140748510402000d803603007845004000095001e100340b55110b402c0c1c05400c4018400d04445100390b10300b0384440e2040c88020005554104400141526200c8080021112105203d0088111580061500250300440704003940703150040b5080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 239985557 1250 239984307 239984341
    0x3041707141507140a021e161707231e04020d0b0f010c0308010b07110a08011b091419090213050a0b0f030a0207020604050406090207020a0602060106050d05 69
    0x241c0c50003050300c96880c03518501c0005004002d00c1c1c9071981620714000c2c4000d00c6001d26550400183d0195076455503900448400010701e8000c4000d039441c1041e0001c5013a0f155499500903251000000c0400c0707244001840682d0141c80c00323041e9040c00d120000c600200009640c002c0c144a90264a2003000c114107000b41350b40b044001402c15500c2d03080741d40d0540010082012030034020038402280b50015885900107450780395064036014560b03400c0c00314400742d5030400f04048914240210480301036503140d007a018020083c1c0400400c104070b40d43c40b000d2020540a4040d070034454004000e200f4050f07889502d0398a284203482c00010041180c0b60200400780651080e91414030000d09101100c01c4400040c056403816203403d1300080c0d03543d400941e540309000090144040a1010074013141142e0001c02040340007c1c845800d15440354001421180a40c3c0180c5603c1d070700103449002c40c00e012107000010645400980f07110341c5040d0f00a403451150300b0700840d0155031130b000503000c01e80d0b00442c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 239986807 1250 239985557 239985593
    0x4020a23070f03020d0e0319060b0a03020d14010b01170705030702011104091a0a0803090603280209090f0415090201021009080a1103032202040b03010f02031b03041707 74
    0x6842c0c50403410060b40703135956241c03500d0005605d0701e83c05c00103040008422800700c041c02c4501541d0345654540c20018000440090350040700068004050b0b43d40c07002c048001401070901c0102ca81c1031000e402d0849030603460860500580c0002804000c0e05a148141e1105c2070703040583d0390b5503803110103c1c01840c003840c0d0455003042c045408654903140b82d0103040c0b039070b003101540019801494100700701210303d44151042a8000c00c40e100340703030038460041e54214500b2200140a200c11400d200d48400d4000103e20b05141d0201e2500e0080c508603000a4009668543e82840c90500751a8045d070400241d400320320300740d15072007035104591007001201ca0458910008104682c0e252400341c489074064004c5400240c85000802035041c4003000f01c038000c1ea030f6402044202010809040d41e00c2c182c0308401d0703030f00c503030f450511341e909403001e01641400d100180d030010b80c1d0b40b600c001c41d01202c101001c54541c1c80002841000006403000c00412034801543d9146600c460040c136120341150030400c040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239988057 1250 239986807 239986823
    0x5040f061508070504050603030304030f141222051002130302130f05061906080403111b0109080a0201020c0d2324070f180803070311010b04020a2307 66
    0x8441c088410340842415034011400755440199660b041006441090300c0f01c5915410800200e40000d02030344401c1500c28145c14403040301e891840301c4080d25009a41082c1100c4145000c01c1480294040c1c5c0c114a80702c03860604421000a8859556500380300306c01800301540000c0100405c80c0c0c0082c44001150700400000342c8000c50005c0380080d002c0d506601714000d0400022640a2a008040a110260400119040602d0000100c0d000030000c0c20950a2101c0302403000052a03090000c00000291100f000c0050102d0301d000400c8c1419030b90080c01290003245c00300e00140e03400702d02c10b42c103d1412500140ca10752113041c0701c151240902d01d605450300c0710000341c500e6180003050012901182e481044200410701e0343c0100d0110084500000041001166401240c0100107242c80c1c0d4000e4807400d12100e443e0720303810349181d02c03c002c240c01180181c012483c00000900a10b0301d45201541c0550401c00072100160000303100c1c401480c840d0b40400c0c4400b0a13a4030001c04c0e203d00c0da802c4140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 239989307 1250 239988057 239988071
    0xe010b2107062c1c14060a06051c110607060b0f010822061d06010303031b080604020d140c0d0e07060228020a17010b0114090f01020f030f0301060906020604020a050405040f06 77
    0x5c520740882c0e016510390b2560090000255040006114910884001900400700141c0c4801481050142210308071303400f4203800d4240c045519803001400d00180f0601001803081044003c010072604c0751107001e130400180c1c408100c0120880700915402c64280d82006c844000b1510340580500030109910803020240000c0000307202000914904803406a1402c0040c011101c49021030b194004c0000804562404046606401c0540c0141500b290a00000070205c4222071048a0107400b6075201500a00114920340d405156204910030200d03001d00800751940340010284d01c50107485001000b00804884481c1c124240929007200c0a5009100500c429190541c034081059401c3c020703204d641c6483c0450300c0c15400b41500400720f12002c2d031001e040c0824101003081d071442c3c0d10085070443c0030300d000d071103a002030400103001c00080c1506801c3d20307581805002001c0c02000d902c008215801074040c8005a101c29814000351001581e0204840d034890803d503608500001d4010b14142c50301107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 239990557 1250 239989307 239989313
    0x50d1517060106081608040308150405041101020f010b030a0308092104060e010309020306190908032707030312200c070f050a0f05040e010b2107062c1c 67
    0x2031000e043c1c60860b12440d8650b02c40700300c0085c41406412480740803e03400c00202d80443e00400181d68040b070741018035034032541c135040803801741c442c141d40484071519541100e80d00b9680502103030152869080081060031102000240d0703c2444010180a01450201217070282d9014822000400120311001c2074420801400d000306a0003841401c0000f00e0b441605001c6600c00e001d41808213070018024204de0f251090803010000142030f41c82c40036a03840c4803460010b81c0c00c101541c0304d0b002109800130800c2d8000d10301c4070400d0760200c1107805ea030030082007031001a400042900044800303090002c1d171103080e049650a07101d0140c0e1400010700001c078098a1901c070020349501031b528940d20810344150383d1000e1048800203809035021205d40840117000701e0510350311012110699200120b110030b0202d010400283c910107010001041209140d010100c0420004001b27180078680980b442d500940c14044490741c4001203403070702c800e016080c00c10fa642c60707003038400d41e0184050210300f0650358a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 239991807 1250 239990557 239990563
    0x140d0b181509010b040e0712181a0a1803050a090f080a0201020d0f050f130312120501061d120708030d0f05060307080718090b0f06040f0c050d1517 65
    0x7901d407501c1288031100200b1aa900702040c0d804503540d04011180688540000383c0b400c908080c0d0440304c00340e0700c51142d518a42d1600142e070f140c90286800b05200104e05410802400008062008042c00c0c00c1c05c1c1c540346199620000c50250f01803502a840c1d5400140890b9440c0943e802440403102c90031000c280303d40041900c000145c800d80840d640e50340d6000003517031000c0909100c0c4011850901a00704402c1e1144010614010b0005528030b05613225a034440b2421510b00b000c0300000c00c140400e40400e02c040c4500c42c05420380f420603989001c01600c0b81441e1220501090340602d04c11150265240420040d40000d44820000c2e01c0d250b07546065034070010100c141c001410f05043c803008c0340c06401c0102e0203c0944035004068141c0c1803c040c1c0c910041c20402406280c400d40e26211003010844076000385024041125145c03400303092080401003503840c2900300060052030072201c111485e402030102c40300c455010b4008600380d4940c0444e075410300503581c0010503001c000d5a0070b075204d41003c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 239993057 1250 239991807 239991841
    0x506010210090209060f04090c091e02030906060409020607060e0607030b040902030705100207150c0b0105100c11010306050301020705030a080906090a060f0b040c090e0106140d0b18 80
    0xc0e4222034040752454020010368032403190213900303c0d0152021401078280b024a10000d11401b500201340d80f2810b41c2c0381420009c4a5200303108890340c40c94a03169507052401a0b40804002d040150f0a41c1000592651145c1001d0001d61007281e0311440c040443d01c411003610a031540244007040900048043c0c582c6902044541c1d00020b071a05081030380130314040c13003030301c544c980c0103802400c00901b4481446000c03441c16928900f980b0a418001401034006480f1000b0040b190352580824103881c0390000400d101a000140301d0364400420360812980080c480d001c00b5048444881c186500100603002804190410b40e0103500006000c2c062140000041402a00300c1e0717141082ca50310640300f2502d542064810802035046455800c000c03410b142c001d11611404904002440c02120700001c080ba8083d840e608041000d159040045280c80800e55004102904128280340502010141903100f000301458840381d84510488554440081014800010640c2022241041502040c0c00c03011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 239994307 1250 239993057 239993059
    0xb01090803040f03060203180f0304300f020604080d0c170705031803010605130e0607020d0f140f0301030f120f050a0813020402030a06090b1002120703030b04050a0506 74
    0x1200004192000008940850f0b603109809843c03642540d0f5054003940c8058080c0c54020141e00c02c5001e500c405006144100140318000c40c0d0b900d2400103d0464280d14000d0100e04c3d45885030640304508603a1f991075040e03640300c00c020106903184e10009031140215044100c041c0b255024070130352103800100c82102140540c106251202e0075151800480c0310b4424001c0941d00240407001907114004000c401805e8020b00201c0c04540f15808036401c14450310b601d0741280d40383e600c8031154070000d1014a4104c411440030b05058001c401002c0c02d4018050004800c000040304c02e111500300f004140e071910003d40d01390b65a00d5070b403401e206012402002e4286c0e07020015603c00c5901d14001d05400c40c10345051345403c0e0074000f10890940f80820000c00e82401005500030040050b501d03072004505c80c044480c00080c9050601000c0b0080728039119555010300c1125911840441d000a5005020341500031015030b00e440d2440c0803806404015081a040340c14141844001d032070b290000c502c9000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 239995557 1250 239994307 239994317
    0x30f0406021b061209010b061c0c0201060312050c0102041505090102060c1e031512160512030f09010c05010c03090b0604091101050d1103040c03050601060215070305070c020409060b01 81
    0x1182c0ca20526610541c2c07401c190f44284100400301c002900c0c221150740c084003650000860002d4813000c20a290b1150540051052000c0042c5040d00c0c03c07880b5486440031140b00800005045668190100744078080071010f2050214030300e1aa0042501200c001e04481d1044169607042600043c1c03d40d000444000d015000e50b0000030203112805041d220f810000c40700382c490442c94810702c2c0f901e592001c0d01041080c01603105a000517200c081000d504a40048001e0580640034000d8003092103180d00180e2151f102400c0e4000411400030a4580c1150741e809241c7d0348200e0f60340140c400d2600804d00611a5003024101c00750590144e00103180b2502136050340100ea91039000b0482201c244c3e00e40240b0341800b007008600c2951068000e0714a61038412000200f6007501050806a60821281100c04000200003030040050902c5003c5c01000c1c1c0d40014052000780307c503030035160140200302a041640d01e1002441d0305200e50607421a00e03802034001c011010243c10640013a084400b0313010301041d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 239996807 1250 239995557 239995573
    0x9050c10080c042105012316171e090a2013050709051804021002150a090f0210110601080f15150a1503110301030b06010f11030f040602 60
    0x150007030003614412403048114a182504200040102030f03442c0d6107050034125260312641c00103200344100ea03d100c100000c0d881c041c0b0001c1c07021610b0790000400c1443e60103154101160b2540d00140801900c1d50a100c03404440e03074900300d02181c07000c1d01108200c0c0d00c4090b5024400140000b08041c120540103080156801c400d074031002c00811551824103800190401001030210800d622542d003286840c079003418156995000500b2490070758420000c84070328842030004502d0300400454a40030580050400c018000d06458100100180801009074844480d00d0401008408000441d90700904402964400c108024a862071003000078209219100004c00e20070700014a07690b007410078000608602c130a41c00c200040c07220142101c448840b01c7d60b400c844a581d410154000f42c2007441899141c01c0512030014150741d808815803864400420040c00800c4109038095481703034007806d20071005904800101c440100c0404d0462041c0404585200c0e9001c401000f0001c0300c985900301e808103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 239998057 1250 239996807 239996839
    0x20f03030f0a031506090e180708031b0607090b0c010e120a02150f011a1e220803040605070503130e01050f040218210109030c20010e09061309050c 65
    0x7010b25014017004105842d00811003d1245c00c203c541c0252940e0091229100707103115185001c1064015007855000071848031924440c400c1000c071950381c00c4004080c18100303180007404041c60783c06641c809400020f25025a158250000343e031008200b42118201070041800703c51607084140048010b004240c082550007040a030140d00031840501120741d81e0740b8246900d40f400e800341c0c00c004803225082c080c0260305682100c2e9510b80124841c4241d41d501c50110101c101401164806415003114680c14080c0038000410b0340c0580d40d03107080903aa0780c0b0f20707420254914040c000102881d4518041d0118520720f620130b4050407210240d61261020301e150042000b43e00540302c4880c8650200b02c00d100321032034180600311602c035008608039107164144840a00b559100c0d10140c011442c11020003040080f641050780c20001d50312900d0b504041000c00003080f520000b89440d101c3d00300d07a40401c000b80c1d5140d9404404881c481003c004003051ba1074400d86038411450380500c2603402c0020070f400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 239999307 1250 239998057 239998091
    0x30f060a050604050604201602090115030b030604241103090c120307020f090601090b030114090a0c020307031202041509090c020c0108010e07050d06091a012109020f03030f0a03 78
    0x400c0d1803005000c207031f03402485001030464010365110301c1c40c03018807100c1e040981c035131110180c06026004403101441096a502801b501c411700c007150b00913480301d002c22010420710307490041954800e20340c8560541c55440007001500000462100594002060201a0000007121800540252281880601c0040c0195241d014100c00030b5000703494501c2d005002d10303010750f2075603000c9814141030508e075440e4200324007650801d0b00460120080d49007210010701c2e11a0b141c07988440700c10424480c3c00101c4000a45a006903007004041c00031154410f44803081c544c0540c0c0103081c162506988003503004900814840440c440e94400c2450a45148546480401c121101c0101031b181d4043d9a4a8910010311410300109480300b00f002c1803010701200c41c00c5000f8103000300743c926008030f00c004440000c0e04100b16880301a506010580120801240000203e5402001d0707215000030701e02c2c058008150303900800c2401581c180400a13480851201d014003a01064400e99010410103040082c0008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 240000557 1250 239999307 239999321
    0x2070201091a04120c0909031205060a12060c03090821010e010b07030c0516090c0f0f1b020f030105010e01030c1d060909011415010f080112060b030f060a050604050604 74
    0x59484100700a000309100c104450200391703c14000106170b260341d54591401c80d113012a04600160090650310414901c60049580111003100c2c0d40c0c0c9020315003201c500c6000181c8500602c060746803068940c205029a01441f00c0c142c000c0e003003950724149011034404480700085000c0004aa440012840b200c1c1c10f00032a050b1095804a0303450710f58aa1006c0c0d45840a10101715100c1c410030803000d962041c200084801080c0c902000f280140b4681c102030a00059070503884200a850300c10040700ba503001d40c0782d00c500f00740c108064031680e15600100300c003124510b4400350150b003003000025140e45107010081c101c0c2c2c0207030403080103d52102c0c1c42040f00440c00400180304800c14000c40c80b1850101803c9410862080001820302c2840e41c1c6409100b50458264010a011080710405560030282080141c069490b00d04d01c2c56040811010342c01001d031502424140c1d44594442c40340e14200401540000d0070b0049603c04d107000704281d0080c060440e0018002c60800e00420903509183c01a26 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 240001807 1250 240000557 240000599
    0xb01090f11090603092103071b03022a060304110909070303080114010509130504030e03030424050c0f100f05150d0606120308060301050106020c030a0803090106090e010207020109 79
    0xa160642c1d020030015103030009050f0301d60740d029074240000030034001c254442c040041403490f1503ea00d0302210181c401c9010a2060a80c200075070255000607a0115521944860711709103140c2080c10007145111181c240001103422510000c240300501464804450181504840c4c00003079035207000c0400d0312a2030f20720004011070700e0480140014440c1ea12090100c40f010b1501d9414154128009880004006010743e0761965034002d00c010305a0044254041e200b054008600c1c0618101603e07a000300043d5095080400100445006d035104100300d42c10205114201c130100914090515110540d400c02a0006481d01c800c480c5000e996008040c40781503800940040583c0703800a10410040c009021120700e80e0b20040819040c1809101404440c0207598a641600c0c00406050841d50180c022405550086880c04900c0c2d41c000380b46480f135584840030940700d8941c00c040e240501125088034000e40c0c2484031403100c6240540c0030380400c5000b6640c600803150f9a030003003401a0700500d002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 240003057 1250 240001807 240001841
    0x4090c030c24081506040306020319060803090f040207020402130e07031b0e010e1903170c0703170403020312070203010f060b16140303040b01082b2a0b01090f 70
    0xb220840d014081c52680904005603038180e1809400000d49298040e4104441c036903404410f0000407007045400c0309104011010410030076049c013440035602e0185403a224846e8543c01c2c030411084c0c640d50180d4071103990151040d901d41e141c00418410b4107803070b406003080f403076500e0002841e01c610034003602402c45402103028523412100c038412a400c92a0395401d034180170b0380c1e41d550162512129158054401d201a6038401c0c50b05500e0300d1101d55842d003240c01c5080c1001d00080407100000300d01081201d6010b00040580d040c0440c3c015818003c5505c00780d458040c2480002d0f01500d08401003040c0e07031003280200181043c0841600841e4030901920710004418405d1030011428031240c0f00546001e91415160205000c00c1107165034422182203400309902801000071301c0c400c00400c06807001072640c48809062400403040c121070341c424501c04200078105a0b1440c00e03240301c0000d11480701051040c0c0401c1d45420050b0760b4072400c3c81042d0b80740f441c21101c02a004003e110702001c5031001441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 240004307 1250 240003057 240003119
    0x30610030c1d013617070504150806040305041a070f031101020c071e17060708041a040516050307051c03030e2e0504150903020c04090c030c 62
    0x240c80c803604103102900f07061000d610000403100d18030840d003200c020940e415544400d51044408502c101c419032000e030300d488006000c2e0444c000041058801d45030251400142941d41c41c0c88100c0d012100c0c0e1140400f40134240c01d0006040d400002403003030b5945143c0c2500c81c0070322002840303024407496070301030030070301309000317a140081d03ca5604111083c0210002600b40120341c101c135814898680d003d403030301c403000b0020b07801020803c140c5800280503078071406c3c02c680060301110303454441c0240114100002600001c0400440e081349068541d8900b01e030011910b0a4607100c0e136582c3d81c00845003150000e00c24001058640050810240d5102401508900015204840004404003422024152251010f80c03000f2000c1001d201014403030b60540c2106003c050744c0002e4968130040c0701c4030207800c00d020880401d1034000003500c0f100c0d4104000034405100d060490405c51f0110309a2f500a00b814208004d21400e20a4030044e2400303100300d14425030b510581d5021117107151903070031981c10843d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 240005557 1250 240004307 240004337
    0x1407021305090c100305180105011d0613020309011a061608070203010b03060c07030801091b210204120507090203040308130f020904060504061a061e0409050c030610030c 75
    0x281e030401d2482c0b0480b1072101243d00040c0c40610070010100009a99608003c1d0040101841c01d94441c0440c008114650404580c03100c2e4142944000c000e166402000c03d40540303824180c02503e81854104645a0800c41080d0340a800000c0d4082981340c107034035a400703084c500315080312080c0700190341d4000306040542c9d81c444245c00502c4282d0f85956103403150304058509220b105d21444043c0f041c40d940320041d1402400780007042e040b0200e41850050155280d01801a2104500b0107504205101c00140c0e61030100d20780350701c10740c040b94600108001550013030b01c00200040764400c4060351100c42e1541c952a0890008070382c0540001c480344049402440351000780c1080500070441102103c1c080c1d0003103060f00344107440880360280d4030b104000602181c1d22401841c6002e858803031000300301d41c00000d1520300070b45414044081c82c580c03404d1990070241003100d0040c08504024841f030300d48400c1e81502900200c8406005550300400c8040480c841d1103030030040c1f501601e43c0c800010301a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 240006807 1250 240005557 240005561
    0xb031605030c04110d1505120703030f0c080d060e151c021c0c060503150108090d031e0504080702030c091902031b1902011d07090203060607021f14070213 68
    0x44188103240340810952030f21419a001b99148078906d1503030007803010b10b80824400441c02ca030749642ca2070381009800303000207035000c038080455500614044101005074103208226106030700300018014a010b0380014640d500c65580b51103107099a15a161034980b9009000c80070780300c0305802c640b050901198000501e021a1032076258400c1e2419442090440e070345842c080341154000d507005c14004810410980c3c20400c04100c00002031034200c465003024080709598a03036000714841850b0302c2d038010031014013a1081c01c1480c10100030081c081c81c18141401411903005030803d81c081c2c058000c5100030b0341028110035004400c0180710300c824000002562000703400207801001800d0325504890007504a05000e0008004a040d00210310398850b0400b038211503400d4000701ca18507103004801940100480d402c821117200c464050f0f52640d800002a80c03612032800b0096000310000c05030320710303041c03850444440c42020352108641184889050700440c0200c1070001d40c825842c40c1d0036515400c091b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 240008057 1250 240006807 240006821
    0x1091703101e0f050f010e09060402160305071a06090705070501110a110705010801080c090406111201060f020613021018120b011203020a17070203030d0b031605030c04 74
    0xa068216001c0d00c400030203010220703070000b00080802c522820302120100b040346900402c41160b0860140343c1060000e00b10b81c64107200c180c0b0038044030000036a580c0320350701115080601851581082e903554500035100c0e4100340d00985501c180081086a120400d000352405000004d003010b580da65803280440d09a88904012100c954966190001540440018100821071519507450807031000d003c06d40390070019803040781040000c800420007014085250744503080c0640383d10040c0e0360380303007010030203019502a62000164001410181c0641c1c50700094141d600a940314890000303d040c0407030780d0b0382094802540c007840600144005290107507003030300040311500b42121440f000a44a03804039007240e00420210300105000701c100320103000880d0241545040c07440d0b801a4540303000b5582c015802d0001d0146940c408075460104c1c100003658245a802001c0741c0c1d941c0034078810b07613029041100300c1c0e074020f100d102214001e850038000541c080e140040d00400040c1340890810000c0c09070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 240009307 1250 240008057 240008071
    0x303090604140f030307030504060b030a02010503180309032e110d020d0e0f0309040e06010f0b03070c0b0408090925031d01090609030806010c080f030606160507060206060301091703 80
    0x500000311600d40040c00550302c11b5040d82c0b0002610b00d003d0130a80142c0300e0b201200c44c80780d0080700b04100113030703040030a0300d4003c200303840384221043c0c0c1e8007000c52551203440380035913140c8955018000c90302c3c08140d008403850019250400319044d450041c1e01135445503840312102d24400c0c006446040c00c1507000d4003802e82900d00200d00c00d082c000c2e845060010b401c40c548440d400001c0e20701020704007809000f103101000c40043c440c075807500c24584c2802510303020326080b1110010102c0d4121780325454030f80364140c002c60505041e0400c3d2410711241d44c80812000d018902200000b5000500c0402c40304010082d80c10320500807440003030031402030840d481c040700d90050780d00000010520900c03401540ba0b109400025800764a420054100c034001071a882c100080c440701b0500142280d000e6409820400350007907100e84980303001070306500441c1208d901c2c0b2610128042c0a00000084950440f62542c0035034256446d0007060600f0380e02c81031340c0500424030120b0000c010307200341e800440d44805 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 240010557 1250 240009307 240009313
    0xf0103021b0703030f090501080c07050307051b0a232407081c110406111203090a030305070e0109050909030d1d250e0a090c0b070311030309060414 65
    0x101034220a101c021654034031141c941c48800107000301038109602001e10390b00c6080949007580382c4000200f0400000f025040100c50106162007049004c00640788001e030302c00c2c20b4a0800c128014a0f06202e41000e078440e219001c05440000c5215404010b0600600401a10601c103c1c001041c400e0103001030b110703c0702c10445006160344050300080904042c3c3c3c401c41c4650746c4d84285c00c0401c403170070100001e07080b2032a1030f0100d24454907200314115811210141094441c009900c40804d003002c0e5581e8241484000000c100080303d00302040040059219441c10002a10344000445e03226071a501001e002c5054840c0500551900c5050141d0240c91001100c1c43c0243e0310014809540110103070106102007500707030462800e400e220460500030042e0140d0a512031404d004030400c0f10610940c0c1e400c0c210b400104d00712046503005011420f41221589881c250307521100081a440040282c001440000e080c0e00c540c2c90203c21280181c0c6c001d0000c0461341c84913190383c00042c0c04010350300c400344 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 240011807 1250 240010557 240010567
    0xd0305070c020405180607030b0111060603030313050304051302070201080a15050609120d050a110f0d1d0a1e0f0f1a070c030b1605030403140d0e0106181b0801050f010302 75
    0x7031750130800340384100001c4e9400b00300340c0c03007450015250006d81c0d2103090540e0003030701c10040d454400009480e8090140352610001041505100d42103204542020350011140c040110064046400402c07401c1d100ba03035031f5000c030381d2004805030883c6c898541c00580c0483d00380c8100240e1408101802c0710107002400782e2a2420801da00c0303440d141c113519140c8081000810051195a0800175031140781094101811104040c07500a03030f20f07414088441001d00c2980300d4014203030030031030880d54809200134140c60725107912000000b0325010001d20070340c00c0602e06c80021410602401c040001c560f0602c44840d801410a550340c071005803441d508800108041c00003101040c08994068000d41c0284024a09800d21303000b0203120400b0142080c0a004c010814080025406811002c001003481d40840d00c0f0b402980e00e07035020b0f1001944a00746507080200108040c000c6501000301d01c00f80300307010030087d0307000c90640748004580d40c6403801182a07000100706034142000b00d038124140c140b400600d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 240013057 1250 240011807 240011851
    0x71106161404050a0909170a08160905030313080613022b080f0d1107020f12030d060605090306010816090507140c030702120115030201051c0c050a020d0305070c020405 74
    0x1080c194800b1a03081e498103074040c14003c1050700340b209510300c07c41007440c1002c809030180c61400040d00300d0540060025030411054400c0018102400740107058075562070f003541c210b02c0b0107840f5000d102040d01a11001c50840070080b02c1c20503c1560140034000a070316a02007101110250408114080c8205011603001412040051104038840000c0544680034180c440085401090980d032031084104508005070780d40303c402149059003140c2900380403213511a014110f000361825007100394140300f404a40da54000d406440340c06025000c80740d03d6a42ca8142580e201c50440f0300200b4001403010a1043c00907607088543d008100b0309280c2050260185480410741c8130588100c0c09030000300d1030700e08601d402419040402c5060000b4401074a80844402003203c1d684002410701c48001ba132030342c40c081c43c040845002040248100239030780b100031001d002584040505401070081c8540f600746035009200c2d40d40201060b40e105000c0c0461982400300424002c0c0c03a08000400c080820210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 240014307 1250 240013057 240013069
    0x30503100803190905030d05030114130f0e12031b030c040b12010503010c080c18030a0203010f0c090603020a0f0c050a02151c06030f0b100305010507050307110616140405 75
    0xb100c450000940303e261401080109244030540280e4402d401059882d01800e90044c150303410740300440808a0301060010008001d000b220445030296402d185641c40c82001592005001101545c29510085072703010081d8241d1100301d455428040c042e41a03069000c4848018561015030b00031164074240e10340b0f1810a0a41140d80400320243e0f4401c0140a20306007130107007411060950800d1300b00790070600c41daa507040c081c4a03444a528004031540e02e8072940d04000051445401900030480034004810000291038044200b0020544403100014101e110f8422a8000178041e901c1186012030a00d045600700004001a00c0d40c0c89260b40a80241c0c0d581142000100030096071555100440c1c0000034901c0ea960007a180e25502e040000c2001c0b0385e02501c201d18469000c0c1e20040e0581da01c000146590740f050f00080d00540c40c5c2020054202d40050003140540c1c51500c40741460700e44076040c2e0f43e8030503040300e21960002041014241c038900a40d02d03c3c551039458032419003000d8591001c642 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 240015557 1250 240014307 240014317
    0x9040b0711031603031d0a020105090102100608070501031b020604030305100504020a090503010507091202100504030c0905040b13050a03080a020c030a09091b02070b0705070306051906060906020a030503100803 92
    0x241e504184500b015014840c0d1202e11b41489110034102404d007282c0c545030741859801906000d000204d0040c1e42c5c2c4203225408600300c81003020403540e6110060aaa103000318081c56010a00d0590240c0c00c85044801c00d01036085160700404907991950740403009080041d00284241010000200303090365640041c1041c82029540c00c00e405280030700705801d60b00c001d0105000c0c4034502d00213100d5002000041600035806413950440c0c0e8607065021101482254800761440e0002000480c1601c00c64100d2740c0194080c01c4c04240c1078071000300882310b0240ca0040141070360f00ca20441c0b40001d02035003090341d104803450b01c0141060191009282980e01c080343e80c0300001e00300344051029070000c3c800e104214040d02109101c0c3c917111040030f581c2d0005405107028011001c100d02d002c00100300300020195034071000500841c107014213040446020b24490501c1c60b810104c0100f24548a1494481251483d030b00600c5440d0207038a050324103a00180caa5000060301242c04a204041000102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 240016807 1250 240015557 240015577
    0xf090b040515010608101a13030503040905060a0b270a090b03060f10170a0203010603031d0306040c0504151a09011106010e0a0b040b130605040e030909040b071103 72
    0x10166000414400008110581086050001d07940600a010440003100300a4540d05035029181c000c0b003118814040c0230300d80104555813000c1101008110010015000b107038100d403824480b0380c23542400c0000c01c100314054002ca00205202c118a04034100401c1c0030302e01c00885601010303251074404103462031a103030440c68441e51614900d2140d0b00302002600c0c0c0c04621901d5045003402c04800203c08658903101d64103155485003800c0658140601c20581c51a03130041c000c0000503901d140242c480c420305603c003040480d10341c203000cc081c2000700f442c80c8184c0c0c1c40040119114140303c10840181082c801541206100040200c2d0728900d0512800c00350303507900201c688850444000408a00b030305409102541c0111004100c40c68020030078030380066811101103081c10002e804140105041140140c3c40304103c090718800d24092303805201619004d560074401c5109441c203031596403043c1140240c11058a2000a0100d244051910b40010940c648003482031006241c84c0e00e5a0041c4a440c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 240018057 1250 240016807 240016813
    0xb0d0f0501020c0706030e19052406010806060c1f0e070806060f1e06030417120a06050409021518060c0d0305010509062101020903010e0304140906130f090b0405 71
    0x1444401420132500c0c008202c50701d401c0c420b0760380c0c184000d51150700e44004411454030500440080007420301c09100321030103651040c84580b582e00c441c03c1c03603844265001c1c0d0102c2c103418080303000b50400c2007c80354140c030400003e10a0894000070018850791545401c1c2d0f03502d6441d540d003481100c0901c001c000034613030000102003d0400034100011002c07503802c1d04c0d108021320184000803c0111103120800b1404031045a01c17a0b03a05c0c02c0000402c554644150450071001a20014030b0208018040c0a01d481e1041000226114003e210880b08500000303035010b8140c00c541c084036071052004085511804c1c525041000041f03000c111076400c07100d08048141c0003101d599001c0e0780d2501c222030050604940e246460b09044001c1907040400802c0d1550103a41014004200703002501290740104025000700b008092855016440e5001401151003c20302402824190720b84150898056400207024400c2034000c40c030f800c801880000c64000c80d094560314007801040792441c50501c518051405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 240019307 1250 240018057 240018067
    0x3060306130b07030903200a12091a0c07030219090510050d060510030b010f08060c040b03160903080409050906061206070e0301060b0307050705100b130b0d0f050102 73
    0x101414540000c0080003020605520314000c80c2205081036003210f07060800240b068441e0a00319a249484005c4001400940030b0200403100c0006003d10002d020b0003580d2541c5c1000d8008455603a090b100c0d2040903849070507000c5000a2031002021181400001c40704511398a031f010a1f000d5480b52041c0d01410360200d0b0801a1010502420344d114000101c03441c00c203400c0c000000e441401d00903000c4c003000e5031480015074a079400c5210382c015582240c4043d4180d07035981e4030148084414020700708607001d64000720b84082514400d907420b03180c0d045400e40c1160b0703450000289445c0005152002c1001d941c1d00000130640b010001c0026140c6540c01045500d0540d00e414905000500030301d0207807001b070084039041d10ac04180c0a4003d075036460b10500045411002a0242c0241d42141030b0001c800802d1114454004008012413846101a6021011045800000c07510700c50f045c5500054900501c3c1440d8003554094102480300801041c45003206466a00040ca90264101d03a0f030ba44c0061 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 240020557 1250 240019307 240019309
    0x60501081507020c0a0905070e0306040809011106101202010203042d0503030306180c04031509060605010f09090c1e03140a020703050f030a0209120a030f0503011217090a06050306 79
    0x145a9440b046600007401c1207000003000c500d0840692060000340703a80c510206550510480d465003540704010102e95903801d1500b071090551b480f80300d00718007080542d000c0318551200455024483d030217080413003071664500205403010003090081241140000c04c0b021278440d0002044030104160080100d40d81003410708801c4000825410440c8a0b52043c400c0003040c2d60350122110b181159441ea480c00d030b80b616021080c3c98010b80d000240f050101c80322140400100e5800702d59024002d02061203010390798401956032640f1a00d542c400600186000c1c014400c40d5006580b00030114a0242e11619441c01c92403184040030030040000b94841d04039401010110380720319040550050110300d00000c0d9500984140b02e1400203651211020000503941603195040d42d0071a04c2c081d0040c0304844281030600c0e20b031403242c3c0048002c180074551581d0f12621400c03e4905940c8007540d0071500d5074a0fa225490b616501c2c1e521400d4034141089500025214803030300000805007a21081d45904001c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 240021807 1250 240020557 240020593
    0xc160308150604030b0604090519050c09150a03080a0c0204061202010801060807020304030f02370b04150315080f0706030b0d1214070605010f0509070f020304060e0102070306050108 80
    0xe10307203500c01c0c1030034442800400c100c000302c10341103282210001618404c4d8034105041c0b0444241c10041803126806240901101182d003d00313142080f1440f0445a4905a603402542003201d038a81d040062030005100244058000b440c00190600340b1284030031041d8002019a6840d4120040716441c3c141101c1c110358001c0b8160b4090001303806d0043d03040c13800280080d924011484060015042d5844040541d200c11040c0e4408118954224100406040d1240c403017842e0056440d580d2079050b0000940220484c0948054a514500c3c1817003d80c940036084014040000042800d08295100090170f8901046201800e10305c1401a10f03041c1e18050700642250850b030119801074106405e5400000d46450010010b81e0041c10084040c800e01d18403d012400380e060f00074071030780c42d080001c40c00510503042e110071103a0845012007030703541c1e40c01d00711456031001150f000580e106020501c001f074050141c00191034410310464002c541d4a890f124180c9100b0b0384000c0d000c0e0001801d40030410703030035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 240023057 1250 240021807 240021841
    0xf1a180105062b170409050910050402061b0c030d0e01030f11070201030c050d0501080102190c0201080604051306020d0b0109060f05030a020307031d01060e1b0906030c160308 77
    0x3224120702c2a40c0e118000515185205100640300f81001c04080820507500c00c60603070392481640d280d841302d80703d844c42e0004100960ba1940c251080380c4079102229198000d162040368064405400c041c0f058018101c03250805031840440c1c0560045043c40d51820820010120115950308481003080d50014003101c00c080201c5040b28142404070781c2118001b0100d1740c0c001d80c2881c002403800c40d00d500403101c0303014204404120f80d0030b103800011b003090150042c002240940d54000b0f44034138012400c0d2250748903800000d02080260002800c01d1500340d2110b80d2114075170f0502003051243d079031103070101d80c400d40002c46419030354130b030614555074880c074103402404d103600b0500501001c0c1c080141890100800401c0d0a80d000000140000d220f900103a002d17403d0000c0c10500c0840007807806020780114000d00c0542c4503010002003290381c1c5c42d800030000c1e08281014510b4840118240300065000070f20206015408101083c070b6611800c0441800314087e42d00c45803e8100107001c07101c44169 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 240024307 1250 240023057 240023059
    0xe0411040e030a0509060c011407020708160e070c080405030d09030b060a030b040f02190303021515060a030203220f030e030606102304090e06090a03020a0f1a18010506 74
    0x1c0c00f0f94100749800c2800c44080b070608449450b100d8805580240c007501081d03240b4000c0d102d01c14144881103400044e20701c259408001920441d941c41c242c00100c2e0440d501c10348180e8501440800c800d240520614441180500103a0740742545500c00f0a03e01040f030750890000030b1030082c04005004142010541101045410f031601c0c3c0d01c0d684401c034007040c000e00090060341c40000840301319a540c4400304002d6690781451141d1a0f92030402a444080c0380340d070981d80b41a12000620040d91000264503440801802d070f40c10300c00010b0007240250002001f0b81e070103e440c01544042074842d1103170081c5180c810980101c01c4141c502d80200180031440195000703901000c01c1c050255101000820780500701e14051484003021418001204848229018034220024000c241c090701604290a2004100101c884030340b22000b0195031500100d4000e40144c002041c1e00e8001061200d080c40080d008824010701d0100709200d103c43d00006444844121242c079081c40d282c45028055079500100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 240025557 1250 240024307 240024313
    0xe0901080606010809030c01110306130606020601120503090604030503091912080a0219060506150f040b1b120703030c0c05070504180602030f0403021c12090305040e0411040e 77
    0x4502119541e0310306010700780300e050001140001d10610403c0040c0d8004102082c000d00000d0300100b00c94544c0d40c02502c5041c000d10000c60020500101401081700311603155008099584c031300390810301d10601a00c000c55041c0002c100060150b91602d014102540c00740020b141d0f00c2d00e2500c204120580041280f68001d159080b0800032441e4000a0740c0a8580041c00d01d0b0342c43c800715604a08040100c4031480c500380070762241d041803107034640c0704911441c800d4849103000d03000b0342039030701c40f600418090354803610b005c11061045402c0000513117055941100c0b90141403040805460905059901d500c45d02c0c103000c0f5080c4140340c1e041c002c460201580c1e082103401d2440548986403901e44c207003d514042d0341c45005410b101c0100e1441442120340005007151642480000030062050540e401c3d801841040420306020545141c1515a15007039221280344a03090400040609134004003503051103424040003070803407010045540b2651240b52410300100030070040104862001d80c00018540c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 240026807 1250 240025557 240025559
    0x507090b0703051b150906070207051c030c080307030e0606060306100f09231003151e05040c12110a0903021507080406020a12022d10021305010e0901 66
    0x1026030401c8600140c0c00d8a4059a030314002c1d13443c06420a140c12920035075100c0c80c80307581840b51003500581d00440020301920380c1070700c60f00f50803a40da2800c0e009a0381d0040b40c10100c0144c401803027541850440c400d040a901440b82c5031101203507500b0450300000441c0c0c656120303107840320342408015800381c81142e81900798100354001c01c2c80010b143c0031110a220b41d8108a008250141d080072006241d410b90f26180c0222036030b81d10442c580a0b50f24140204e809803d4a10300c0740c0a40030b0b440c2980344008101d18520314042c0041e043d90010000051512010400450641c54900803590504030360748a03402e10000c5c1d4903900044640028100440301418417003030b50601e91180541c01103c1c0c0444202145841d802d0211505115090300180f20050009000644a40100300004038a00440c078603460b142c084031003a42c0301c1801260f14907000d0704580740442650700007014110321200e490210b0750791660b040001022a84811000ea41640044804011941c1c1c00842e10b0600c00040c0e0f801a10741d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 240028057 1250 240026807 240026819
    0xd09060201090b0604020c010f02040801060311030c06160303022101030b0603060106210b0d06060f14060d020708070506071107061106070804021f030c08180715030e01060f0801050709 81
    0x88080a0144e6101ea030700040c01090a074425008201d1003c0250000c42d0388a55500845000b400d2a200031940e801c1c001b40c04001c20328021642c1c0c007000001a14182c0303450200d403103846d124448580200c00b0b069080c41080d40d0441c01d2000406e00e50b41d84108800079504604107100300e10b00007011a44030f03610442c01030107499404507080c240701401011044940030303414a2a405840f268002b184c10820142c2c0400074064141c11000868411002c43c6440315143e07007074035007220500116070303401210810414042010a42c000c010041c06400c046041c50113030740e956405d1502c103849910000d0206011402c00000c248152030080843d42071443c1200c1e040801d142d240e45004041c4030034404c041b00040d0540d110300d00c82900d0b0300d0440c05144c0b005900024040e0041c01e0721507071400050701d0b0340005900e03c5800a042480c602040380102182e0740703840300c245d21382c0003070842e500201512034400150b124000d005031800f529041ea403955085091444050844600038030303030810007029000c20848 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 240029307 1250 240028057 240028073
    0x50a0b06070f1415040803010608010e07091e050d0f050615031b0a050a03120f0c08030402130f0216140114010e04020d1709030f01020a09051908010603050d0906020109 74
    0x8810f03444201c00e11025a8020180e04140007400365021921081c410441049a81001503060710b000c0d485842460741c036000c440018a40c12034480c004a003542e031080c0041010512241080e0010500304840303030f40c40700d0120f00d0000d03903508104c0c4c01d001071600c1901040b40610140d0303400800c854a800400c021a03000030742e9074a4240125040b00303a00c1040010544131003400d5009840d0107000c1401e03d550f0380c40e2000310740707003441014000280c201c1a41c01da4507200d2400200f419802405c000c1c1191100c0c2c0030450641d104515500c82640d40b42d10400810419001078011514090030b6180394040c503040c0600034400316603248000b07924003144003506c011000291419101c007190922126611480030501250580401400b1a80c0480c01d1f1704070b110071400200b40528041e42604c3d03d840c000c120310f070300340c0c050364078101d000c40d8031250140240d0428000041030403070304001c50706000d03507511519401c441441d0001d44007030304100000303c0d1050300140e00354000e1207584000c000e013044684655803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 240030557 1250 240029307 240029333
    0x30e010311070b060d02040213030b0903190806040605040f0c02010b0f09180109021306061806050a0c0227040b010e0702031e190e13052e09020d050a0b0607 69
    0x15803031009001c501d6940394685005170956000c0e10456403010120300885443c40540703c104c401805110016080b0480442500e103100c0c22044a02c840078030140c81914511001010b080d0055074416000640b03940d40c1c080c125402104600008040400d14002403d403208031076864041c0f2034513040214643c40312848140c0c403c00c145182c46500702030000040c0034101c2e81401a41c403000c050721000c034401459000200b142c40340e03240d101115103101c1c1d04040d03c2d1000d215030004210b003404240881d07406400d00100e814802000303074120058418070000c1628961109038211591070040004101042d14210b024102100d00c018080c504124020351b00d11078100c8500a00050404c2c441012615800380c6001c0380d4640c4045085140c0c48100602c82905841c18501c0341d107080e20721408100040c4034080c0208e10301082007013030003125104d040890030690006d40d45c10b4501c000c00034001341240302030021a5040103003c40d50b030801204070030503504541006445160304000ea880090b4481030b000c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 240031807 1250 240030557 240030563
    0x60f010c08130b0a0e030c0904030f02070308030f1609030f060209010e040c08250c0f05070e180c0a08030a18092307090f0915170a030e01031107 64
    0x5212525145400001402044045042c042021001090400c4814040d040300b071003030303501c0e80418a08441015a11640d4542041d0804450780c04200070034070400f90b409104505004442800303030350340c0c2d03040400c0d4002c5400c00d0a0309900e42c02d02ca012000c46200b030b0ba502d401c516280c0031260664032500024801e07040003d081d503900152b4000564010300b690507101c00020000c01c816010030a000d020003000b00c400c102c02c01e04042820800e0f1a01c6e0460b000c0a12043e91103502040d4140d40e9581c120301c1906042d6031030b01c03440720000b41c3c411000d40110300c1070b0b9811550760981c20b03051555619144068541c00d120303c2d13001d041400000b03400000e80b1224001c03858541d80c01640b81c060103e036404150003403225141400c84180c4e0b40b4484202050b030076401c0108007e800d6a4001c0300320780005981c007e101c0f0343c0091900401c400c1d1080e4108803001000c289424103502c0d6644034611418401c11000015074005420000c24181c02c690b8580e561082802e01b13010300c1c142044121140c0c42190707001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 240033057 1250 240031807 240031817
    0x40b0a020c01110f0c120f04030602031806090718060b0a030b0a0e09250b0f070c0806010e0603060906071b0303060e071e0504060503190b030601032405060f01 70
    0x41440e00000b50490680d00d040c00c2d400c035030b507014070100452442d0b10045107118148100c1b28148100c201c4002190610011540101d003802d0440d542d00000c1d5201408061000d80038541c9054010b4017031160501070031503140101800d601d01485082d5100301c2e02c800a00c05854420104036940080701110708000592030001504110701c0002a41813549401c240c0c201c0324075004100d110b960000304031400101070481502c103200b42c48600c090a5040c3d02450b001050223000e503904014140014001c81ca1103495904206074072802c14a03d0400300340e008982543e080740501c12641400e0080c1500300d103180d00a4100c034078140401601102c02c100e003400400c5c0d036410700041494420ba104001804016842c8402ea00b4000790050070403420310551545400008102c80b103041c0140215021680e0980728079003160b9840c00005640602400c0d8500c0301a12100c650304160b60034021503000e0341c424100d2505c0c1e00c5644017001e4400c89032004010006142405100032517440314607000300c80a003443c1c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 240034307 1250 240033057 240033067
    0x1080403030b010c0c030b0105040f0b0a0504021e0708040312030b0a05010f0201110c030903150108101a370f05040f021306050702150703120b0102070810020c010b0306040b0a02 78
    0x100c800eaa1034540284c400005d05030040f0811200c010624102c9400329400d0020300c1900000c44101c03000055200e60241940204220b1428950080c142c0229402c00049032010380b030038002040c0c0d02c040c00407140d4800c00075041c02002603140034402c2c900c2c0b041c9401c00a0b03064110100e070381d41407640034250501034100c0e58100c0441c801d4100451281490b921251240c642a2145549070004a0518441d000740b140240412852441d00c0d4121416440141400c00001c45504010140441130442c8d07024180d030300c582c2580b20a04201420821400100c2d401e100a1510810f50880344466010007180342c0c4080050305020006003050340c0007110002003c480320714621000344980c6000c40382c060842040000d130b0702e400c078000c1c0a4480c000d58001c1d40401d80444c00380d515100c3d0000c0103000c00e070000d00c1403882460075800174840d00010300481d0b9015480b40c140c01d10f0601e40707a140d0010030f900082c013180740103003e00941010403426401007401c1e060540e601c003569440145100c0000f540422 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 240035557 1250 240034307 240034309
    0x6060902122e0303031509020309060c070609060507260105030d0305060a170d03050c04060903150e1207060e01020306030a0219030f0c06020c0102060610140d110a08010b0901080403030b 82
    0x5803207024028080902c0d42d500c1c0d03240f5010f005803404e045510020912040c00007042e00321802100d1103140407034040d200307d5455101300f14164001030415281d43e5560851030300010320903c1124011050f5403903041d83e00d04045280000b801c415030150349940240d10040003a51000512804450b007103080100c0c9070b60300c030404201540405d601101321046007e40e0580e14103c003040300c42d00c42125907070034081c070b5030b58225412051185121300400658030010402c0810b00c41c0d0008403601000c0100803030f5120042d1126450300300380221885404c4000035868040102910031140203200580080d4107611301200069101d0000c0400030b07015000d0500020010000141c00801440d84142a603000c0200c90401c603100c0145802010051310405641c0c003115030001410134810003008140151103083e04d9012150100e400640c4010713070600b4064030111018600035002c07642a40c3d032030b407038440030744103001002400d06a2040225140c100401149a640b18280c683c0c000d8142c1004a124602d2034 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 240036807 1250 240035557 240035611
    0x30c050409022203080c280f081b01020405010f020c030d141c1b081504020f040b03090a02090106050307080a1a1f080106020c0307140312040602010203040606090212 73
    0x3028018150050440c0031017000b0780440a0030b10004000200c0300b45000ba42104c40c044840e181c04540000352143c00c000029900c0d200d24000140b1030024035040080c079079030321000e1400032140021140d40216090006590141f070a5100440520003080c802603e00702080e121400702c0280d50400803194080c40c00000e61008a40041a42001601c0745220100c0c09400908004040d0715640c1ca4420b800d43c803251148042c140900341c0c142185a04150010070400250701a0707500f8140741c3e03018000000c4961004c00650b11494800028020341c511920401c5100c000c160131400a000c0e0910601584a612188443c0d01c1803c422000034a40010701c058132600e1040036980f60701080346100c1c42c1c006020181078102c4003050303032074030040343e622500c1c1644c403100000a030070b40640c8117400130072410030085141045204042d00b03031039aaa02c20341540c402c0d41c0c8180c00c1040941c0d0004184000c200251041000030126000300b14242180c1c542840e800c0c01001e0302c9031005411216504548410368 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 240038057 1250 240036807 240036847
    0xc07030c020904061a0406050117090106120309030c0e13060c030b04020a0e090a0b030c0f150f0703080601210905150a060905060607021c051609020d0c030c05040902 73
    0x9111580c1464240791500c003a040d481103040c000002c0040085d154205401150240da038144c44075401d401001e0010610006c0c003d2000300290f40758000001c00b400080c4003050464065540c3d0300340a0300f981003480091015030b10801d501c01c1180200700c2c1d000214180005095030040005c02d9460f20340313104a01400240ca01242e0292001030a0f051440d00182841d41c40b00c0291502030440d9507148520041301c220b4a41143c158210070074242e00b81c5451410004807900c01001c605981c80d95442501050700308004820769644000383d02014503400a05140e1b1082c0c0034606400c2c800240c0d00b40e4410010802525400d840c1c50761003a0040020070300c00c0d041160300407010800c1d0b503e07001c2c0082c80900b0081c0300c0e889001d860310010810700c2c00c0010440395640d40103411003c9034001311491303581c0300c2d583d0300d0203642a00969074155200c00c040a0404000d214454000d6120310301032007410f0446002040d803400345458009540400c98100055404440c4004401a01d41d0440341800f100c90102c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 240039307 1250 240038057 240038059
    0x1030b0403020a0c0b0c0c01030509100b060d020406022b050910170403020705040b03060103020d08030c04091802010311030601120e01020705010f020c0105060108130605060d020319110402040e0c07030c02 90
    0x681c14045040c1e00f000e80648400182c00f01101c0740801031f000190101c0354155030041d011380108100c070381091441e07000110380701c1018004071328040441c8001800c0382c1051b0005001604078422030f0f2120101a1440d4280c1e400494151881c004158005401c40c4109440c4900400c403071011b082c4510b0142d22001c031800c01d120700e0805c8502c2d29240094032400c060007658440c5240100c42002402c0010f07210781038075406425844148810f46a540d00b07500000c05001c8038040801000c1100035441c080c044880d54032032400140031440c0d20014040e285c0080d681c0c08101c005108005084e079005802001d100c000000001d610b1074503400d02d601a05c03446078064265803c00740c40c0a030000240d402031040c00c519030300070081912030b02c004442d111400e94106800070020840c8101050b481e03401550848002011074246510341d034042401d0549082c1c0c840c000d00740c1d640008090046490380b8020702030042b2011440c00e4100000c0741710206000d0410380c030702400440c481c001c060040d408985140c0e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 240040557 1250 240039307 240039323
    0xc0f0f0f0b01030308010603020f0412050c130b0915060d090204060519080601050609060a0503091612050c100f030504020d020306040c14060702010503040303020d06030b0114180f01030b0403020a 86
    0xe038184044400001e1104074001080c0b030000003209440f0341b096608000e0700c03e4065107032510b03000ca0304000c2c00c5034038810b54180c040d40040000701d030b0313840b48090101d0035101c0010030300000640c104006031400a11a01400c0100040c6411036615603040b036034145001c1000103802e8450703001050041280381c2205402c014005800c1d0241440100e640d8100d51000781150896030f01c4105100c054055000c0e04d640080c403d000d010000d034000c602540c0d00441e080111b8404103046c1c4180c0702040e0701c82d03000da02c82d241e40c40c800070140070701031044003000541170303502121094407541e0041840448510300410140d840f070104007150b65085a08203031540003001c841080c10982003524100c0d100b442800c003d018001901e0712a0700741a02610480e81d0140c49190456a4607101500a540900b40c100501e039a50381000c07000419401c0d02d01d0107400300f0401e40d405410f2407000c1c0710560000b0603400718001c2c80c3c60200005501c1c84c54049055035440321840030070b5203c0e803070242d240542c0910b0043c0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 240041807 1250 240040557 240040583
    0x5120109080f250503090d08090303360108130f02031c021b010503010905060d1211010f020f040603020c030c0601031b0510170c0c0f010606110d0c0f0f 67
    0x34810180241c82c4948841d4000c1c20401614003c0d0510250307401440f581040c400170b182e03440c007042103d0120f80594030b89803825804000081c21580300629000e03018840689080e495a5480c0c4400c50301403185034080112020040040e080380d2000304000385482202118004010f00c2000401c6043d6010781159141c5c10910b0411070a00700142c81c800052103134590301c010340340880751250b0400c04c040e15414030b5642003800c3c0308050100106599080620000e42800050905004003c00b414903500c1d1040c040361071050030700f900c1000003000a014014802d00c0d28089480381150112401c6080050303603030040d08010390460145102100150040b60000001c1c00324100d50391140705c603181c0ca00200c00762074004000321006040090030024408020040030045050714031b03904580010300c52030505a0487d50680707040c1d85008088266511514200580d6800c41c0300380f00d45013000c1000e8030042080a0005004111000c0068014100560f16200744000d20b0b099950940c0c00007451150b0fa = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 240043057 1250 240041807 240041827
    0xc140a0c031a0702030711090714120a061502070905151809011805030d05090304090903110706110d0e01050714030a0e0402091509031c0f09090c090512010908 70
    0x110b002c8010031614030480d40001203000340301004680c1595800368100000700c0c079200a00484d003000502407403d0000f2900d03d500700001310000b4181c02000000f1507522803034841c0c001015214554042419000c0030740d6100703401900420ba46040d228410000035490fa5040c50244080d106042d250303801c40b80540080b0b40003808840342078400c110000c024000c54414084030418080200c2020300a500300344200c28407414984c0002d034205070950112403c03e6101d026402c00c0300d44041e070403000715240341c00b020685072003409003000410780d41c00e20145108941c540c2540b225200c8072034070208506036010041c0c40c0e00401c02e640c44145c2200c403142844411044950343c0307078040c4401d04041084c203030840c1c89928041c003c40304a440c025040d119408401c2000f943c80c0c0e044001072640c140900921160741d0a4180032000101640781d950070f404280107c00a421059507801c120241810600726400e41c6c0d82000d000e100700c0701c080d42c01844d0300610703071410340c01802006401454910001000c01c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 240044307 1250 240043057 240043073
    0x501091d15121e0309060403060c02010e030d061a0c06010605030c1e0904050f15010c0602070204020706050f0109020f1b16060513170a02040903020a050601060207030b070f0c140a0c03 81
    0x14050001c0c010034403034583d8141d60380075a030340c2560300c41403c00c07090000079111b401058000246000220310507107811070350350035608400e030b003804060381c3c4200421020b0034880a0040107083c0c102c0c55807607c000300780c98070785030001400759105200000000c1a140c0210301d0464820380a007604c80782114900101c095510351041c101ca91050b130926011490b0400c0c990783d654010b8a03140c0705040010301850056803001c070341c41c03401d642c00f0703a003030256030b000d80c07903038001800d07030b10300c41c040014080c82d050513490124041a001001c60328814400502c3c00400c600c00ca8607030f41600c00c04440018881c2280e546840d00f0b032404600c07841012200081c0441c0c008014000500340501400380301038481e0740300c6140c1c410f401090710b0241e01507004440503007800e03070100080501901c10b881c0741805a440301440e2000a1f40460300603804402e081040c006040d2100750000c6291034500340541c4203000041c0045c2ca2204040c000084103806240020010000c00391010342c0a40300101040e130742d04110304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 240045557 1250 240044307 240044323
    0x903070807061e031a01030b030a1a06010206010806040f030e1f02010605030f0c030307060c0504051002060604050a3b10061706040f0b0a0b040504080a090501091d1512 74
    0x19546581150140ca900d004e40551a40c103192900300c0c10314420751000440261042c1007100f6054000e980c007241c08541e0040f4480303010024440000d89038140207000a10b03140c2c0c144c4c451506c0750880703010300000071b03040000d400c04203815150007a0180140c40008040d080700f400c05001d88a0448903004500c1e806420000449008400b525520b409001140b030325a80d14000c0349915800401801000501c01d83c88140c901030303079281c2542001d4485010481601c0092198800f50f4040010440d4501d01400385030350040102c002801503402010756540c010170741030507800300d0b600621480107025020030b1075681e40314500382c1281c1000c801000c100c00240803034050340c0c4041c03c81486000c8059400900356000f99480a61022094842c2d110048140c102501400000341ca610a100c0d140d82c490044a000e180280442e0b130360303401c0d1854080d1a0f0501c2d0f6100505200c40d900d020070074003560442551100c0122000403500390365031911117400003440442c5c190300001c14a07030302912001c0010105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 240046807 1250 240045557 240045587
    0xa0f09030e0a1a0a030510030606030b19090f020d020f0301241d06060d0f060b1804050106020d0309031e08040b0c0f0306011110061814010803030c090307080706 71
    0x420020307101c81403c41e0048000c024024840b000b004800c26003486070380f0540c1d0003900858007880319501c941e80c40080d144240c0c82603e001c5210400c1c408141c0e000c0440e202d0313030009802c040124030b101e40d65072842009100030280c0700c1d0000b0a080300a5486041c01c03803852950080003000440c402060310500801c081d003844000d044a02404152011135034140b00c29001c01685c4803050b5610002046415440700c0502440c2030b494035544400b4801342c0c052040505010b00400f52640d505010b4103600c0d503c0c000741c41d481541070038010000150007194140303003100f4616000c1103610060030259107241c402d4403544a90300c4010382214026a01401031401240b2401000e1000e4403404402e5241d03014160104030924820800326842d503014a11151300655050165607204a5480d540c41c21030b40c003907025081c0303454000201e0021f040706100f25012000c60442880d819410080d1482c4e50740402040823030041400110b40400755800c0105a006000c1c80f0111500242c40b00e8004001141200001d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 240048057 1250 240046807 240046819
    0x3020a0905150d14150609181608010c030509010213060f0e0307030503030f090a050d180305060f070e04090f0204020c0304260606010c0201020c0112150602030702131808030a0f09030e 81
    0x21210481c0c545c0103490241c24000c02d11200c9480c0d400d5603500c4103207244007200c03080c8074084c00858a01a1501e04200514600b0000903c0100d81c1c400a825904010248001c0b83d104001070300da4600d4201403103081c0ca42510300700014101d032103000d6508000c9164070329418411950f001080080001c001c51059550721500340903500c0d40642d003550744002510007086a0000c400600040703101d8058000c0404038400c0110b449aa40c0c2c40302428544180d8004100d0810740c0d040040306034020742e40c2e00e0302c0b00c82a40c0400442d01151036898a55468080007841140c000a017a4940c0d81c4c04c005680240c000c0c5004c040400c030740290118010003040030044001d00940002800039802190741148154041c1c0291000140020044600c0e402441210041d513507105c00f03644040b40540e21000103008150000d40d91101030340100000540145890784403a402c0c5087c5590510390600c025400341d9020080e15107079126a00010f003e000c11500d241c10180c9007002410038181e010324038021108060b036503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 240049307 1250 240048057 240048073
    0x20412021504080a0602070f0b01151e021f020f0a050406030501082107061b0e011101020405030a120203040503060f04060e0c01210902031519020403020a0905150d14 73
    0xa40403030003070744510151500589103100c045000c5c2d8004080751440b856448205c0b1019568103c09040300307030410b1820301482e501612101c5c2c0c01c410358030042561520100341c0718402c014001d655058100010320190300411100f50342850640584403200078414100703490745e044102c000e00b160024422000080e0501d000040c00c0900421030705030030505400d68807000000c1500945455100101c01c540c8981e80c1e0213003404010180300854171071138056848000142c10180010b1150a20043c0c9210f1644100f000300400d69001451002441c0e0050105070340081c4020706906500540d07012540501a500c10401c80d012040c0341c403481144214420845c04070308441c82c40e40c8040b00e01e515808544105030392501980d05c0090b01100e2002c428010070210000d9000c00e04065819114043c1d82040c1d03014011a14164010540c000e131000c00308505091540c0c00181114640d0301c10601140d696030042900510303c4140403965000c0900110320100480c5071200031803401800904090041d110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 240050557 1250 240049307 240049339
    0x1b0a122312060118030b0402040207031704142a0d0804091a1003050f0103030e03010f14040507120b010b07060204080303070c060b0301020f030604020d0902100519050408150603030d02041202 84
    0x1366107403e032600610072055590b40ca03424003000b0340c0140801c1c0c042c0200709180600752056038000a00c2140310720f4480c400c3d0b5103013080c00f52604440a001c3c82c4024036080810500545020307524540302800c581401c442c86081c00e00500303501c50390b0040800b081c1000c507002c030900304003000400070780c00c291003004201d0803c0030210200c5030700b070703490445400f031480042012038460500d0050001004000051800341641d00328101e490a0114140c0a41c04204000500c5400c0c45020001d08030741c0381d01c3c4040070380c1ea034810034000c4050007002442e1801003580c0041c400c2c1c0c2d905440151450710704030f036030f217060001000d0403000503000212510b501740924032983d41810b0003070300d032501d2614240d00e0464075418204000fa400210810841540c1c9400b080003580e01c06081c00d0509440703403246a41c07810314141c100115010040b8401c14464200820030082d0303400070345800c94580e03c1c01c10049030f49858000a0561044a6615000314008900810841c40401c035001806108942409400401e04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 240051807 1250 240050557 240050597
    0x603151f0f08070c12110f070e01090b0d1203020f2104020909012702030307240b04060308070209060a1a0408192a0f09021b0a1223120601 61
    0x214000c0251142039125117085000e41207040007520640c080e03840305040d42c80c5982c038092599012414440c804001004820b81900c80c0c9110054203581000c0604c104d0f071204180c0142c034003509030030154006440c0440c0c0c8070070810365030090394044a159458814023004100c0f40c6d01943c089e03210701138820200b80c2e0b142c0f0500c40c042180119500320038400c0f54001e00e441080307480d800300366018003003000450000783e24080050700381c81d07600d5222000440310078106030484240448a9005516000040c00410680800d89000560440e804d1100d81c0d541d2010a480d0a40350b03010a103080e1464400c409010160b60282003034a2400c01201d1703d194500c1544141e000e40140094801221960a0000507020b0240840c46003c0820864a2150703150840408400603070b02220300154045520009a400d0300360041106402c28010440c2d8542c0703859014a000c4244120424810300300c00c0d100901112107460042e070f40da000300c1c1d00d4680007401c030030b000000d40807a030241c00151034041c800c0703c20351b00f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 240053057 1250 240051807 240051827
    0x1140301062d0e0109020403121407021c050f010507020d03090803072a050d08010b1317010f0e0109020a050102070e0411040615020c10030b0603151f0f0807 69
    0x500c8120106500c0c803090000c005200410101c5a100d41c002c540310b014009418002c090100005035554234609002c1400401800c8401c1040121080c40b03003107030000e9040e629095012201071282c0064101d5a0440654085008010303020300c0c1d4006248130b506500c020b10628158090310000c090b10303d81141121481c00700181419410300101c1c440d80d108001e0341000d000212100c196031098108184003840c85801c0888007503000f0401000540d03440000f581c01000e010903003500309000c046102128005070300440003441d25078004412002030075002400602418030302008024800003030309010380481301e01030380145d00750780f40010785510000d03038031049885d540d901c40c0168542c1d50b2182c0d642c01d0840d940d603901580380c4c0d00102c1c035a01c8145045614400503002400500c5a5006001c85181c2000402042c10310b0703c414805252107004c103c0f58044411004007403ca000703680010300960b500500703113001001c50002d00d0461743e0010404141c2219645540b000f55984030000c9071541c2c3c035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 240054307 1250 240053057 240053069
    0xa0b061203041418180d030507050a0f030b060d02040509070516030c02010212040810050c0406020a020d06150315063c05030d180b120c031801140114030106 69
    0x4108810040c0043e01c901102503c9002405000429203001c8559001c040544522900c68501c0352034005036841041140c2c07038642c407800c0a00080c40c0401c006042800f03442e0386201881000e0680700c010742d100b40d0040034a102c0041c05940c80d0035600740d604c002034009015440c040d102c0c1501081f500c81c05002034074140fa461044180c0052412b42d000c07600303c0b004007412415489041505204104001c4c05040541648070043c4112101000c0503001d440d800340101864031410082400b100382d0218803410015019910035040001c2072130990010f185240000c018550240c101108001c200c080c456040c98101205215941c1c8420016008a0805420038280c000d0550074102d0b5440c49004030004901c4c0c2c00e080c02c0100e03134403008070f41000038990355240002c0800e404400c245100c071154102078100c129046080095506000c0b1810101802c5c020000e440440002ca25a014006100c074810850000f484060359145000c040000280242d00c404100d4400d810910708051003003000300c40e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 240055557 1250 240054307 240054313
    0x309200a14060301170304030206030f06030d080c0406050a1205011d07020c010c061e110309151311030703080408060118021c0203070513080703050c030f0c04050a090210020a0b0612 80
    0x40703401d980460b41703050b580489013180010300000025035a210040c0d0b109400403100c0180529100d8101410408030800d010300f440310f104140150040d1501c25a41507990a007021a6038001458090395a03103c08240340b6895814030300049880b22440d8034100d69000b01c089502c07507030340360f1403c02da840c1c0048581c02800628001102c0e0040340c00c68124200780a07031010080717000d031081d4800d80141d070354a00401c0307601403000091002940c8200031002100c0c06500300c0390134605207054004405248000040d05a4040c4e003c5442196018403500c0015540081034130b540d01e5640c82a1511180244581e544800b4000580c18031291716008480340c0d8075603541e4000101001004a100039000500140100303c0305010fa035208983c0040040c000d009100c009200310382c1b4602d0110302e0203425403a202c2c080c0d000b04810034a55a00096900340f07a040c100c90101d5a070307489108031001040e4403040039510403049500152541d40116580c54003a01582d90040f003503490505000b4003030402d10032443c0ca64 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 240056807 1250 240055557 240055559
    0xc09050307150306080d080a150902072a03030c0b060301061d0103060b010306050f13022a0d0e1c03170a020c07240318080a1d0316150309200a14060301 67
    0x2d0303802c0c9d12180050211030060802d013512800c4c40c1702240c101c0c2e101220030301c03803c3c2000100341d149400030111742490701c0b440f0085d250441e80c1c010240359081c2c100801c4064420007045007039600b0340140b4007421074101c0480c0700c3d2200b1148020414400e11094410626069021081c0c3d4800e00802098600103080c00540081e2001409025014410b1900426a0034403d40081041484000f20700030700d02c040501c0007480030b085090404035008212800d0000c42c0b1501202c1351540c000340000d4550110075031b981d110b860304054980340f8800b4681c40c001860760040014080f600d42c09414240d100070116850039448142c81060003403000c0d04101c00503003114001031100c1c842e81003811050284104825032640ca80d071605035903000108068045120407007030401158500451000b0690201c00500207410280c0c1152840c0200b40540446071082900f86c80f0b0041c042c1c2c1001400b1035010a807141141080311210440c2c000114910744580340c804030010303550740b03050740c01c030449a4000d144528503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 240058057 1250 240056807 240056821
    0x1208070c0807260c0106050604380304030801081606020615030705100332060402030601022b1101050f070507140105070206041505090a02040c09050307150306080d08 73
    0x764101d8401103606414800307100036541d0641403e4082d0108840700c9a4840382c1d0f034070095007543d01039040b90313000d400c06000400041c2054410f466083c03041045008541e00c900364030f01c2c0403151146084400380d100106001c1016030120001e412a9008401d91300c54070a800881181415148500001a44280c2c003281c5800c10400003216001002011144d40d29a01c9000c9402c02011001c424046603681c0c0900c071483c501c001410501865542c0c4420000c0358109a04041c0780025105d28062903000c8006003059008016000811800c19000e03a181803900c1c034451003462200e114000010f12801e00b10070840c0050142e903004101121f00380000daa81d9403403c0b00c154000305000d481c03072000e0000e540c07442c0b2001e114490240c003543d4050400c504e85401e000b0300d6450310f00d0f80c0e03000441c03401c1d0412120b10320100b5040546541110701040415000400b00c0b03004840341c111552501404000141401c415080e150003400662400d112403a51110407580b100410300103080407907054000a203074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 240059307 1250 240058057 240058073
    0x903110d090e0609091015030510091101020d14090103060b030a05061201090c030209040203030f2106010f0c060507180e01030512120115021e0607030b100e0603180a08071208070c 79
    0xc0002800b040343c1d1f5180c0e41e07260f480c43c021601004590642d0b644404405100b000030b810119003c0a000900c941e0141903001080008a0150302e0701d03020000c10611407a0b0b100387c21040080800120940d201d0500100c50f40040c84c1c19100d00344074002032100c1c00d1551606004214003150012001001e9528640a11407483c50003042242d240c0070070400803030030554200181051280c14103140c400344a425440c010303c84d10182045040c82103260482498660015100d42550340c02840440d80f0344401200740c441000180441000015480c00851216401c100050489000354110f5003460360b4a2075a40d480c0c4515521400c0d160307400300050041c4a6241c41a20760136040d0300c1150340300344e10720550504134908242418982c0d00041e05001240e6410300030408881411600080300710403071000644520200900c1a02031403001c000242d00701186103c0c5030001e482d40d000e48074032542e40d18200c041031b40f1421303049030150030640285841920a00040b88245515107400d0003140c041c0d113403100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 240060557 1250 240059307 240059321
    0xd03061206090f05030c0a06060f050a260d02030a0801090204240c02180103020f1203030112050304050301020a05210601080a0b030a0516060311090d02040903110d090e06090910 78
    0xf42070f8500801182c00980c0c104010000701d442c100107041802020300e440401e40704076a12443c0190740185081c407055481c403007143d003119a140c5180e0018003e81c004a40c0d00c0742c41002824150180c00d00e003800391500800140300304400c2e5951036405031389401401c03041380501d002c2c0b2203488840141f941181002d8119400c01140d80e405d10000303418081d4009203038004001943d003c09504c2c100100114100a0742042510400b10b800411202d00c401e18560b59000502c60185500c0350311540707030180320040c421540940300140c02036545e00803005015000758060300ea40c02000c91080c500c200004202d4400390702518059644128030340b240100d00380940002e82e10164940940d0349480009041000b1882803101e44c282002c0d9002e10380b0001404992404032290070103042040254482d5443c010300d291110340c110f900250f00c0d903c0341000c998094681005208500c03c0e8032601c52610b4001c4201c0d81261340320410f85030196581c1043c0501c071b9030300707440e003a80ca507200001c01c62003200703e504429 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 240061807 1250 240060557 240060563
    0x4080c040203130b15010f050a1205060a0314010225050c091806150f040e060103080c0a0b09010506031b031b0f03030a080f0f2e090504030f020d0306120609 69
    0xf142100702515110b001d4070090f10000c1c515001d401003451203503001b1440e0a01c04100e42400c3e03090500c200030140003e00d1400e104414159104002803650b03685520b40b50285400500180246282c4080c40307001350b01145c10840d14100d202400721102d280400c0f4412119482806001e0035545407090112410b0060640003009a00a0761084d14a13001c0081c07a05c034003038004000c48804549810300c001030074080e00e031500583c1090b0010f00b6240000600c181101c0e440005240c0d5092598203541c14a4000d54005005940e58001d120303040d5415004580143d03c110f040e909240c51000d82846419503d401140d010781040300c20708601001100b2000800030080c00c0b107081c0340200d20009040d51300000c1008040303007040042c05080007400b40781316400040040d0940803810020244400c9540d0590340c044d51000ca128400a008007081c10340f0000c0c400807000b4070490419180203040020400c24500c0103108100d0032281c020311a0081c201201e62051000d4074152840d01e0341e1000d0400e01d8426 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 240063057 1250 240061807 240061831
    0xa0503060406051201020a0909180f0609140f1504030e01051804050709060e0904020a0302060309071d090105310305070807030503010f0e06222a0f0504080c040203 72
    0xf6041d10b40240b6805068510340005035030340307030000002c1d050300c00c80d4100f001c08600c1d01d06c3c04d0010114800c0c4203541960003920040116241e443c00e000078207100c1200400e0440c000300982043d06c40000e00d041c4a0071048103403004940c0b4034500c015640800c0301e02800040d0b4401038160194042d0700108141d0030070142d22400d0082c540041025500b0a03155400000c010301c10070000640d001d00702ea40c0720079080f104400381c2e0400380c0004090900d1030002922656002010804108081111900800451030301a000740c541c410141c480c1b1b001166207410300c0d42888009140d900d40480200750b03260301d16240040100c00200c1040c00348190300c0b011424080704201c114042410713403000e0000742d40b00b551016a070750b05006c0185c41d141c00030f6100780c1c0805003110a1200d01c0d62054903108841c0d200c01108600b041c6100d4a510103070248554402e008421030f182c03109a9000440030000281040d01c03010750400011a040f50b0382e2085200d500760039003000c440082d0030f00d002d80095800480c40c48113 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 240064307 1250 240063057 240063059
    0x31101020601170303011202130e0c03070803070b061012060305061b03090d181a04050312030c03220b0906060a06020a03050f07061d010608060a060b1210080d020304080714060a0503060406 83
    0x1211041300d064076111042680f1100103062f540c5010403c2c1c00290880c00702030f42c104091a980c82013048405000e17144201f00061042d1605886005141450052400144802d90307407403c0035601c1d4601540d514a000482d00401c8240103140c0c801c0740d000303000003802441d0001c107503402200c40188000b03085551041402001a6a90b09440b5100b031506c45070024607621807030305041514044031401031211301c3c0ca087c0708000498850b0f9081d40d510440c20250310410403d0100d907400e1080c03510800130400710801c01800703102030b0002100ea11880341a5103d00c0784645404099070740f0714841c480180010710170405800da40c0428000b52050f244151004038028064000300032200c40d5003200110282c0d510b0004004c1284100a0b0981040d8514010003003223050100f4442c05102d12001c105000c842c24000c1400e812050640e03e00900c403d8042e510140c01114000b0f490343d1040c442e00240340710307160001c00c0344005100c084510b035400030034075458074850040589168000a00b50f551042e40d5880c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 240065557 1250 240064307 240064339
    0x2706090f031207051b0406081b03100c03090b090c13180204050c030a051506180a0b040603020705070504051510030603050625030e1b0415031101020601170303011202 73
    0x4041d08185104030301818450240c2d05d0180351101c041da0f8224404c909100042000d4080419843c07550380b90b540d9100190726110010074a806040c161468007130380b03031042c2c41b08000c1c2c0c10b03400020450b209032448522512243c026650b1400d080ea00140e015030b5140d0700d410a01420b6105001c2c800100c4081c4101c11040d800040031101c0c00c0300e402030f040c04004208000401c030b61091907071104e209940c00d002131550070b0100b00503024203103004071811061480b460a9507594100d40d0010300441000d00d503516200d180c0100030b0340081d07104030384510900c1800300d0b1625050040c2403040f90504284400e004032141003103220001e582040d414141d503a000440407560a00105215078901180c40d078100c241550f607280074021303801c0c1d0300e400c00d0b00c0d160141c5600c2c040800c00211603400c1c03a000d1001c9031120000500103006028041c1c21500000700000108581403880030b1010b17500b46c083d55084da1740c550740d031414403840c8014001c207908100014401d0002140c040e500c82c0340050892922050100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 240066807 1250 240065557 240065593
    0x3050a2003070c03020316030f08090301090b07031d0312040318080f011506020c0f040e030405130603060c1407060c03060806070903020307060c050715110706052706090f03 76
    0x18058902d1002c001040c001e6050070021f4605070034181c0c03060222039140d901c44241c2c1384c051050041040034002000c04290390250800b00d0b80d0b6400c225442d66a04000c0c0c4042c0050040307940518851030100c5043c0d04103032001c4103440c185503412254211503035442d030b4111510008085030b200c00b003501c52400701d0304501c1000429078890b000700c00001c00f4002d001030300c4404007055010000f150300440b80900c26032074010004c1e4403814140d60105070320b180c0d900c22505500442d046160088400900355410403096009070048900804041044070100442100d620b4251085001100c108010007000200c4a6012103071164242c940007400c662950300c01400c208041d140307240040c09003002403065140c01d1051310300602c068281007881d10300c555100c0c1e881d4500e500ca07451040d16100e4040c00c4060054800b8a10b441c80c20007940d40c016250000034120b90403051400c80d008001079501201030881c8000c80320b58107030040005046c80142010040c14046180c3d0081c0c150080c49035140e06000c0301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 240068057 1250 240066807 240066817
    0x2030c0f03040804061404140f0a0909080706050702030f03010312030908180f01050316032a0503070206090318040e0a060e1e0c09060d030507081c0c020a03050a2003 73
    0x43c04200350354502d4401c00414400807440d41d02c12903a01004100004410f04681200c241d81c282c840c0c000824500c00041c0405c042c0b64444440c9030304000004c070030054800d0040008510400c004c011548911000701d03620700600c0740c2203800002c108018404100e14019075152a900d600c2c1c00305a05440b90368100158014544005001480ca42c4a002900d06840d07443d10041c4d00b032915500310320385004840d42da0442d290b150024940c0d50011400c046e4002c00710200565004900400710b90500c080041c03840c2d0084400344010301981000c21090750307000c070803145030b01c500d1548110f00f00703600400c000003406000001c840901c20042d2001c00201607001e070407002d20440c0081c1c000c0591079003030200b81c15160076811001da00480e0040c803407582c41d485550f070440b50589041e001480c031841c064030b0034801c0d40005040300401264024901c01d269040c2030110300a840d0a0040e41c0e889401030380d40340318140c002400b040050040704445880394042d16248031514260917580c0320701d4108282140c0c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 240069307 1250 240068057 240068063
    0x9030901020c1c0c380a1d060414180c040314030c01050109020405131401030b0c0403060504050703022806030b0d0f060501050108060a030809060901051b0c0307091a0402030c0f0304 80
    0xd0f590259001ca55118000c05e20080414000300d4100c02e561030401c2ca910900c8000c00501502d0140e0309840031028944404241c0d001d005a6070362500c07010100400c1545d544030038030544030b042114603200c903107044c1c00f0701406281e041c1c02d082a045680e041054503140c4001d5078541300601500c2c5000740d00340900340c002d2040e07000c0143d0f201c0c03c00041c4914003888075154151141489600300d2100c1c2d48a00d4181141d800ca45075500c181c0b61000c40318110310039580050f180b14104004d003c00d2141c08244c50046030f00c200c6101c01c0c0b02154070030020000d0300324442200e0000d03240e501044654029005101c046100030404040307492a540c3c0c100c04c000f413224080e2f030305c10b96810041c041c41d40c00155036074012804070b80c2ca214103413543e42c92010328410188100d014260100b101c82c0181d0050040c0d442ca0035032001c0c2c40d12050b64140300c15a551185000c064800e10904400040b0117110703100f840f21244401009250324940c1e402440080c3d84060f080300c841c21810014040011103140186020700d00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 240070557 1250 240069307 240069329
    0x90f0b0414010e07050c03090415150522030f021e1002010204030c080303060a03030f20060f0c1303030809070305150f010609050d0b181e010509030901020c1c0c 71
    0x41081ca03291083ca0780208044140101049560712030200042a54905041101c000c5035600119000400341e6070369601004054841c070a0491031a030704000a4000610144248140942014181405031646200103029902c02175032003070242c1000c181a07004113015101341d4240d1180900464103910084019500603540490140f0810007000010310040c42504001d40c214280000049c00103080c0744801403e101c4002c15059840303005183d01340341d0003900348070f00c200790f40040248c54840e4400c4902d20102800c4400048215204209031410441c0351811306070807a05542d42514031900c0a061000341c0d20541c8400400a40b00b04181d080308003036500721600c07508100c0c508000014060f080907043c008088402d00194445450980000ba00080b01e605240c0b12100095100c0603c607509010038028148c0b00c60000c1e5000c0d003840194013900000708055610342071440d80701d0090042060050700440400106403820b040c19001c1083e6440f440d141e01826030390344100071005035001454040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 240071807 1250 240070557 240070559
    0x30a02100609050103031b06140109020d0e01060b0910090e04080a0f0207050306040809040209030f0102091e1c081324050325030b030106090f060807060207090f0b041401 75
    0xc8640c05038000908000506006950441d030700a011405034010311000e400c209100d02c0d0502c90103811180304003071264980c110650711901c8110283d031103107801d10403031403c114001020290501c110402c5a903481c120a08042c000020048a50300344c2800000300a07a03154080703101d060740c0c20700328055441070704031030340c0d42d2260100540080d228200b0070b001c3d07401c554020802501d020401b1940107a004541a03a5191260f0014000780030b07100b2030380e40500c2070300140b00c0c01d081d0550043ca21141c0441d80580742d5145080060550005440e00c03982000342500e1290710440602d03d481c0f40c0500c40c1191904098040904101108941e4855407400380008500c0e03802046401d0a040d80320010320b0001d25625084480c1f00d6407003c1c0c41079100480e01d820400c00d007514400d0703100310070000d00180280710980c2d4031a14075000e00340c612980c882e41440e0203030000390f445c00003c00400f1200c5030707009403000d10714086010f00244911851194225100c450018840e0b42c1c511840710708440d401c28042c215 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 240073057 1250 240071807 240071833
    0x100e06120c070b0c0414131b170a090804120303020417060403030606140a080402030f1b030f0f0706050306060d06030303020309010b04181103011b0c1a1b070c0503030a02 75
    0x10950242032182c0300d1504000031b210340301d400ca019200040e01928515074146a081d07040300188500c41c2981403560080d0110314980b5403000d2a5025081080049209912924024400c40354901e0008000315001c10080049140850070300005034040d04006003030a65070343d88002445803000100d035250b040181000105501441104003604503440d003000c418210b02080c030042d00c102404241407000143c00141150390420040030807162040940e20001d0306800d8517200940302a0304148207008800e81036240001c00260000d41c0742c800802400981c0c505981521164805401280c10240c1045a1a14030300340d800340d00c1c0258440d9a0061340c0380760031000c8908440f01d40c4072186c411420515481010500003040b0f001c00e54105d109801030401030000a4010034840b405486805a4000500301e1507421803c034004031400b8030710044550205003105401c1c1c440c2100e403a001a418007110b0109186003c000d0310342540f007031522000454907000001d103160088002e03100140d015038081001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 240074307 1250 240073057 240073073
    0xa170d020f130e0c04030602070f15060306060b0903072108070b0429010b09180718150203030f040f0510060f080105090c060a051e040303031406100e06120c07 70
    0x3450032403c40001800d02c25100ca1051280e8880501060740104810090116040030f200c03200c2d51007035468180b0210b0307000394800307064148030584403a80b070700c240040c0c03c500707074030484440c003030020040c00c607440c00d05880c1a44407106540a03800c4240000d178038800182080010803001e4050300c800641442c1c80e2622060940802c22070300c81c04407403003004810851000042ca41540e2000299544590140000c10381c54400102a0110142c8420902c030110360000a440c00760000c80e0f00440d543d0380c450101c806d842d0441200a00142d00400015100c842280740980c4c010307208681e248401d400d15191245071a0140c2c500d9142a607498108010b280441070385070008248410003400140390008207903403903011180295000746000a24110140e100340d08641c2012040180e5540110400c1280c0096030442c0c041100803901e060307401014050b4a0030300903c0390000628981c5122a0305c0b03402c40d4560301162046070424000e008011707810280460030762103041c1440d400d5480314414100413403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 240075557 1250 240074307 240074309
    0xd1e020a0201020706050c01140109020705010c0809070501030903050d0218040e07120b04031e02060717251e02030c07120201140f0d020703200606030a170d020f13 72
    0x940d40100e8240c001030341c02041001c11120a0304104d62a4030612404501600d004403022140308140000400c440316542d028090141c001c000070030203000404801d032072007c8143c42000740c035481034004010661298004c8040f46110345412400c0c00c0d00c8005100590304a2102c0c5c8a1a0068000f4000d15041c6842014140c40614000340100307490012488065680310030b01410f4205071200140c181030050540c1112072180d400c0c4d80c0024040d070b40d0300030348414040e61500c0026000c18034451410501c2c0a00b01c1c082d0b145940d4541c412060490038000c1c82d1a4610300a0134020072581c032940e0b580c61700e0300d080000d00850700510f9880d840342e03046a0614240d50002002c030010320950b107000d030b40d222840e5041c59021840203982d40201185c0b80500b0300031000c07011400d03400021030790101a40604400420390984544424240410150070b85605044500c507806600054120740454900c0a00c17184030400b80c82d419181651440e03855040c2e034000c1c0c0d07418001c01c2d40000c80c0a412000c4500583c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 240076807 1250 240075557 240075617
    0x304060209100807140d06240815152a010c3e0109060906090209060901030305091507021c0b09070f06030e030d0501090f0b0319061d0d 60
    0x1010761420f060003070424004a80245c04a00011880b54448425644110040c0c0b003582045001c40303040a01800695250399101c0b000a86a4000328030207a45140500101c0240282200541144003004c041141c000c402080c0095010b540c0202d01c0c00540c20505544030022000450801841a03002d05010552044d0080031201c580c40725028401e51305070a517048882e080021003404400c00c0e01c601403e903040000c0e000b603180010b0541044071130340c0009501442130318183d50581e245400c200343c43c0c00034440030340403074010821810185014407058080a4038101984d060842d00d40225114413200110494500300c0711018509101005a1841e8020b01c080002c00426040c85201c140041203845240c1c1415120141840a01e0040c0161104880141d50400c0340750303540c94014015112991010460901c0c25506a410381004079103940242000c1584000000081c0d031610003e00440c8000404000d845014003081e4200b4400c0324851100c550340c100459800407074078100a10009080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 240078057 1250 240076807 240076817
    0x9110d0c080c0f10030902030f0f0c0f04150b1b010e060a18030e0906040e030a02010b0111150420060301060f031406010f0c08090d051e060f040609020312030406020910 74
    0x207469031390340d4064003000412052501280c1007403a8804689400000c92040e0f000b80900015082030b0034000401c084031185c03c5070140000041034042c8011070356440014003200e108000c050003e8049075006044020b0150340c00c0454000d0380210b103084a4125600e100113400110912940c070204d802a0094101c540d220f49400f401c803654084e01840d0f2110307920340500c5541c000600f0b541e032540e01c0640c0c40b07400c2a0960360f8410313490f01b0084c02810700401441c003058940040860307400c0c00007924058000078403860f0f00c1544503a02c0d80700d12070015140f08c103c000c0c1003030030545564841c0c00180d4003d1002d51140c404228902c0e45c0a0161807060080c24080180d0408208440e81d01003800c0c2000b040506001440310004d08010110b44511450f850308602c03402070388001c001c000501400c40802005514440303014000c54591102030a0304c0545030140b04002140110303003154059040d6500c0141103e42008403100850310366002110f05442d0701d035012031544901d01f400030701022440564030b00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 240079307 1250 240078057 240078079
    0x6090303190c081b0607090810020706020f04030c210308070813020306190f0501080703031b200301050f0402130c0c0804080307140a02031009110d0c080c 68
    0x42540ca01a00c842041e000c141100811501e900803942c40541c41d82000046540e00501d011424030050380c10400640ca10a507070000e40424400d2000500307496448001d82038405ca0768030342e00042d400007c0c3c288c54441d420408054401180c90040008601c01c2c000c1c480b002d858070610740740d03609401c0701001d803d20f01076a06400203175201c4010380e030008a42c100784145803a015030005030084040070080d05031080714244a2540a0703000c1a1801017480c11042c00201140c980702001d0b02d03020b1040c121158000c000034000a0f004001051050524480440040085840c0e4840d10200508070f030101380e14003050309205017004e019448c4e100c5c90140a11055041982c0400da45002c0110710340040b0b0f96880d039409240f40300f07100b0000d02d1600240307100d03150ba80720340390310b80c030396000800c2200ea8031402c400701a60000080341d10300c10729800901810000200007181005070110316001c0301d884288404100c00c03551000c03202c1e62510f000d603108404213420f0002c09441c002c1d0300e1100030720524080d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 240080557 1250 240079307 240079309
    0x501140702150a0c0c03060f0c0e030c010503040510060e06010f1b08180312030702070f032f03030a0e0102010c030204030b01171c030207030315061211040b160605060609 75
    0x303654019080030b440715503560401004456060003c50014400d1980600c00030912010f0380100100c4011928108402404120f081d0795041c05582d100740c054000c003910021a40c0100082c641c440d0140d0292100030300c850744403104841c5035400c641c0215210034240011035900000c01c00308a0510308081e02e03000b070324282c40e82100403040c0c0000c15001000440c0a5517a09800160032804006800c580140105118425031504100d4403640144998100041d03510040403201c0122038100380705c4050040e1280381d009000c08652011610249a01a20030003a00c040000b07040b40c1c40c60b650355032011a0170b5070009003950340b100d0049080600500040c40030600121513141150310840510b081c00103104201820452050b0400002060f9a0380e817200b00f42e019001004002c4c445c0d0340400c030b01c4d401c0d0400c0a1201046000703480000b1401c2480001412551380b00c840414054007086041540e80c18a41815920070014004008259407240040041c0f034020346400c030302c04849450400f00070f60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 240081807 1250 240080557 240080569
    0x10050705030610050f0a0512060f010525021806100e0a05010c02150a0c1e150b01020a021f1209020f190e0a02040302100201110d0b011103040303090501140702 70
    0x3801d080d202d4101c0a0070705101500130001c83e02800030005c003e907103805c030000000d002504518850394800c810310000030340610308120703941c410300e505843c0d1605145151a2002020030b480d4180510040c0088010300560744a12701c036850502c1800d044425841d01606001048182c0310758402400604100c4c02c4c1285d44011120003030722000e00c0c1615105109000183c0e40130949000c03401d4180d00001d902560680c0482117240240c0108000b240b890410b001601070f0304000d0340060000e1060113244008102d5542001c40c00c0c000501c1110030704419500000c0701000307031403250000040c103600908040c03500000900d004000c00e40d001c1001031290b80220380da40402c060001e200d16140126940c0b0000b59404410241c100c1540d588170381d260840b140b030001c2d4880c1c00140d21070040d10350000c0140d48140188103094603a045002d05104100300c0002c050200f1810f19414400301040c3c401e403039102003010380029802655040c0c004d03450301002601c1071091f4101502c5a020803c000744c00358841c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 240083057 1250 240081807 240081811
    0x108060f03030d0e010209030d050703020303040206030603010f05090f07050f0d020910090603032a03141b030309100507020f1b1507050105060a0501050418051e0a0e1005070503 78
    0x64506190254031240001d05600c02d1105140c82a8502400360522500550262500c1e11084c1c085500d03100c418082a192170003034107070050050f402000001c0050030b0100c055600102c0207000070034060400b400500540344102e0345400d5607400510103d0007820100101c100902059400f6114200003901068028400e0b00005c0c3c0111010408105944007189003030300185504882008420b841c0e150003007801d45031900c880b41c40c221003038500078184d0f28078400079a1940d03d46c480c2080150700c401142816007048142c100d0f583c0ca03241c151000064144021880b42c0c00d914050140f59004106c101c040722405032914046501c0380101c00559040040e207042c0c02e8156210f9008103e0300100003600e03e41030344e0451603000c00702040080c1000415003095000e4401101d001e215662100011a0940224403404401c240d0850026000043c69404503412001d00b001011007000c030008450b441200540d51030041c95503074810b010390010700b408454400090540180040e003081000108170f8040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 240084307 1250 240083057 240083059
    0x7060c0828020f04030b2818060e0715091503020a0f052506020703020f160501030509010b04050127091104240b04050a05030f0601060c0c05041505030c010c02010806 73
    0x20009002c2d0580d40f090040c1c4000303550003880101103190120102a0360b0903120344d003854141c62061100d5510310a402100103500c450461082c0011068441101800300c8101461260140d1200803a241a0210320a0b180e88020745507060b41910340f00000c000001c0308001082098030500c041c101c8a984480c0c030144000d20381c034109445540040031400c00001400e10b802e8081a80c0c68540200419034003d001c040d0f0203074083c3c800403946180e5890300d0700144884581020508601800250301a901c980d40203051000005204101900032a080380c2082c1c10090440003040c01c0301c0184418004483c100e41c0803e00b042c04224040d665403c048080103078850700c02d91b00c80c82031208000142403803900c5164696170000300966070f4244203c103607205005240c01108500000320b07250400080010040c1030741ca0080131603030f1a02d00c040300c411225072012500d0f94440d00c000149980d032800b0301d410144900d2820b02469260100301071a2912810100d414000040d28610141c1c1e0045099a40800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 240085557 1250 240084307 240084311
    0xc0f09050d05250b0720011d0607050c030601060e1219080c0307150213170d0f021606080708060f13110702090a0b030d05030103150b0f040207060c0828 67
    0x50303141d9003000c0d400544d03005080e000001244480500c5141400302d4451750069006204008000b0011103404074802003070384207110b8040f005040d03410b00303d0003081c0e01c0d4001d800b500d881c00040c000007814200280d0150740012000c40c001d4690340391081d0810000140c040c01031006481d4400c60781c00550401c44040c00c8014081603c015000042c01220384043e4024421480d03040f04245803402500700d5402242c003108a0400882c1c9884400c03960106000120300610041d611003004075950040190305004500540c003040541c0c0c5005420301c80a04a81e0311358554070700d4040700040004000502c0c0c14810901070040380c04584400c0b103200490b07003001c00c010a04590035802c450070761080400080d0440202070800030544c031507078001c540e500700440940f12180c2040d4001c481500003030201604034910303043c050900600301d9001e2155100e018112111030643d9400040407030700b081c1d00990710340e619040e290706040d030f200760200e0b0700003801d00d0801841c1888580c5181c0305014640c041410301c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 240086807 1250 240085557 240085603
    0x31902030310210510050a0b0102030702030a15060506040807030b2404240b0423280312050c070f1409060a090509100c03060e0f070c060c0f09050d05 66
    0x1c5601c9000700356143d0020200c0b0642041784a0040080c2011660981400c0c58070034a14040d603c0442201c81190f0020001e04041d01c940d100c5614074021a2246a2459543c1e0380005a60300c90201410003800204042c0443c40c0c5107080c440320804000b0500300704042107c40e40d4000002a00d00d0480d654020380780040c103000300a580081200030300c1d007655050420b04000003002c40e1020028800e45000c458074034080c0100400d0a10010440442d02c1d80c840703084241c1031860f84041c440f0b04807001c6140c44659249649403109013007560414450b4001880009110400c4003007005440001e1070816403d20071145001c40b80c40c0c40302c2c1c1c0d80205511999104c000714000341d407980b40140c042c26101308100710b90b09204240c5a41c0301552850b00d0005400c1c02a800c51380350103803050704102c0d013480d070100e5410358480103010000d40008002d24144403c1c101890003141d8244901a6142c1c03183d00c61400004460380003500c1003425a00c00c1d88100850503c1c80b00045c03000c00c50030b4101103600540c20ba00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 240088057 1250 240086807 240086849
    0x40f03020f030c03070309050303040605070f08070206070f0201080717190e0d03061505070f020603041a09070f0b0c120901050708030702070f14090705030603010207060e031902030310 81
    0x49000070358801924071002c200b90140c0100840106244d600c6600c0f00d85640ea80d034011b042d280d014602c60840418810b0080e100842c452a15054005204540052400049600092032900031200558100003620100703400c550300300360030075080380140c28243c4140640c03401d400d8000400a002e441e019040a440c0034604010f60003511440041e1400c2d503001203490301c002002040d4034410884a104502142081240100d040307a80c06c0350820046946808a9000c3c03201d0750340060300850303440101c246c11403c612070036283d5502510300368018000007803414103c03819404841d0041820b04504000d03070745d40148000f900404281c0141d50040d220038a40e001070b0b5440c001e20b1005001514004100400c030755003c5280720680d0850040b9050340c58a6000c1c00300c059850380c00c103d40040202d40402c04881c00740003e587e0003140100007602e000810703903984003070300d1307880348500400e50011502100100e4030f40c40d0346c0710310102c41c802981146803c00304003d00760154840c1d81103010006040300300c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 240089307 1250 240088057 240088063
    0x3120609011d151203070f030e06031e070e130c02010f02090a09090c050307031407060c0503090904020f060409020304021c241409060a060503070b09090a0e0f060901050703050f040f0302 82
    0xc03858040145c1e0b0711148182002070a000f02da400413000034030070780215035a034076001d810b980c003030742d5071440d00720000d080c011070740b881414017420580070b008490007111041d540e8104640c0501d800c0740f001141c007100002001c0e0030754028142d42d203611030040c440f14070030303440da01d540c5800c40700110000b0a090310141003e10174041e00350091600740c00303031860100034040f00c00c924080ba0340204003100d50141e9940011155074001090062143e0010040c1c6011840d0050100390841c1c001800c08503801000c000181d0554081da110702800d607000b02c20001903280048800301d024094014015807811940d43e8a000501c0084140952140c803624114074101144d1140300003000c00e00340301d0f0081c1011803141c0d9a0700011151100f901d4200800400c8c2030401041810454031200180c80c03d00750310038104000c06e00c0c01403d03450300c1ba9a51007100b4040030200318218841e00d415010300150304200b100c00b402c0d80d90003414802490b08150034016280403070102260300640203400740d900c8640918049003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 240090557 1250 240089307 240089329
    0x1d060a0306090b01080607020d050a0f1e0f031503050a0305030a0207081201240905010323040f1b0f050f0103020705010c0e03071719031103120609011d15 68
    0x40500d0802c06504214103212030506860709102241d03225900c00d5412070340c6a086a50a0300050707018004510054054840d14541c03045038240070031581200c0802c404c801a2640105002909504480041e10740500c40c80200c0194542c895409504503120f031940d844030031600400300980000040d080204580c10781e0a070580c4444006d40d54564800079910400080c010b011008407003c0041004144100401c1c0480c40180c07683d01d1180d14000c01500184441120b045141c8905081c1c61070001845058030b1103184100300d0b030403c090b41401e0041d016000d20900e810380700008001030002000032001507003203403001c48050001200c5c01c40100d019001d070090003081e540c00c2241c401087d58200c034024207400419811103040c2c0c4d81e581c0481c0c01100840c0a0607000b0b03003001116294210441046d0602d0072300070708100c9044030070300c20300c180303194024141c0000c3c1c001d0030402e02506150403100c4c60300401c075490030180c00d40f00b40074224a0010000c3c1c4000c42c3c0441802b24181aa2a0014084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 240091807 1250 240090557 240090563
    0x30901080c0d05100306050a02030f04170c0124050114040909031416030e010513030f06090b0c07020102070501090302130506030712111f0233011211030303011d060a03 74
    0x100070360800a83c4c0000801c41408100c900606100c0002d00844403031003524482c0480b0401c1c036600c0d440d0f03521141c20482205401000309001001507c02440090280700f04404c1c80d241c803c1c03640901e40c0f501c0c07400d11840b40c0145041100c94603080100030ba950040c0c41c240c1c0c1c1f000b840055a00136625090302c2001c10044d051101040c0440c9280c03e03002108014020517009071141c400714101000111803901c9103060b0f803100d0400d0100103002103101c2011000c509445050300144d401340b940c64881f441c94080b61220b040c0da0b030008103442156418807044005260030b0074084200c07400d6500141d203500c01d0700348441101e640d401c00920180c3d820803c00740102400c40300000c90131000d040c2642100016503401d405240300891940540011010443c1d200c0500d5001e02040000024040e650b50200204442c0b0150200310541c41d1080c01090f00c2e009224201d0504081700c0340c1c1c903000303242d40541c1202d14400e4000f8401080800c03045030212010f0440c618000e0306694403100025861113840d0809 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 240093057 1250 240091807 240091811
    0x325020d050c0a090e070605210112050f0d080c0d060302040c020106051207080c130b09160201150602100f0e06010306021c020702101101090210051305010809030901080c0d 76
    0x26080c08000700d810107403100309841400e040b640352004001540c10b104107031907051b84505400c01504d403044d800b80c00503e851314202c52124441c14003202c1008000e8004000a043c00c4d1200820490700304800c2c102d0300009000b40c007079442d8829002d800100002d003c0c00001e8000118032000180d9503001c100a1036005204000c6171803100b00003402810f180c020b6031f001d81038048545d00366210015540b0700701c0301040024910000b5820074441c104051040d00328000380c03524004c007020396172044000d11480184c845d001420700007500c001e00b52600c172031b1501e50729202d6102c18810154046105003503108104404259404005244001850700707080311f84003409014004010400e0540081410480c044481c1d81c0d008010b81e4108100d204100000394031040001500c940c43c0e003d0210700b00341215600c00054140083c0d000320304044a0710510000141c3c00264003d5080c0d0003c049202410082c60075840340d20384003811030390303030b01c1161400e60600000d100021003d00e81103040300c000040c1c2d0441 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 240094307 1250 240093057 240093079
    0x6010c17070611180d1515090e2113050616050f0a170a0206010905130605090a030305070e06030402091810020c0606040522080d140105040506090603032502 69
    0x411003d6000100741c10004800164030809030301d02802d61031307041c1e0703000100c103112002d12501e210028070311100300d84260702e1400c0c07001541030110301c14050814004006091816605c014420700f481002c4c4c2a100350b2041480703818a0403c1109820043c3c034810b07941c41750f0b65909624484181c0d000000002c201e0720400c04000300b40d02e004901e01c1e401c64460040044290b29000744a00c642c0982e2150704010b074003040042185080d6a0403c941002d030490b04480c0481003070b11101c09481c01280d4081e015802840101d08040e070503c9400e5010100d442c00d01c483c900044001009803001800c0603128000d403034081340880210303150010b41c10021204a402d81101059003030040d400c9828513807514088c00c0b00181c141c2c01c003802407038442c2d01c500c20790301254689034003000060184c422082d5030b4428113000200c03901120744100e0b0066240c4559840c210741c94101048203980006000c18010070408050000a86000050b120002c40b40d603582040c1c0f10102811400e0451000800303944000c000030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 240095557 1250 240094307 240094331
    0x203100609090b090105071e0c15090c2304020c0102040e1305070e0105060f070302011b03090203010b150a120b10080117010c020d12060e01080c010f020606010c170706 74
    0x102c68896a8071a48500400790b8034540010700303c0390704860b5403010960030140884452400c07205201c0c81511400c0c00c20740c014627501d5a00b41442044156013405030313201e0f0f00310b050180307400608004148060030806000f094050b039030844909030b03205d98019a00030440b003480d440b082d01580c02801c00050002c15034540349031140c455800144060721680200b0f04042a1890079050050580d5005000b4525107210340f1400d03000c1c1e600c00d0000780d046558414000b0442c8428144480210700a42e9011803003c03000d00405084845018450380300c2c0303c034000621100078491081e24004a29410040b1412110032074084c00b502c08118040d5102e8030604010388882d030000007183c1070b110341114211402c68140300040c221482d090400d8096030142111190b101e118a40d1903064a4065602040c40f50b680c0c1c41c92000c800f400c0c2c0114216400071001c29080e96030004902110182a200602041c14208006400301900143c09010210901d05050720380c001e4208481440703034840010410600482 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 240096807 1250 240095557 240095561
    0xf040908090402030907180e0c010804020105130603050117060603070302210712230601050415092a0f0509150f070b04112709010603050a060c0305060a080a0f0203100609 75
    0x1000e1f412165640e0440b900d0503403690321505504180001c0103101c0821101d0041d241460010412810098200080d0040b680f020300480b00511154502081550410f00600b03890380c01144c65840d55440b040030011107680c0014428220b80c3c042d903540ca50444500c42c1d2000d01ca1400000d2004c0307202e078000008046144c100c1c4150050b0080700400c82d200c850f03003d802021119220080c90540c01100180319a14066010130401050044802c4100b41e942c5203580684088900203500e107801403101d0038610841d00c210b103c2c00e20742460b2418245100c500007078214000d5545180c090100354002c1e0180060403005c03102040c1c824040755807140100d00e0400c4902d881150100d0b02c0e040501100d6800781489509903890350240c0742003405100903415903060020b0b00400044007907480d84000000310784140000d0180e10301912002c5124500c141003e010740b140600307498000d0100d01e6040040c20004a02d407440c0c02da001d80e1a4203510b01c0750001070f150043d1864858203c618048001480c2d04151b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 240098057 1250 240096807 240096809
    0x1a060301120c0509060d020120011a090129070203240a1b0c02060705190c06030510051503090a080d020a1e0503071103120c0a1d0f040908090402030907 67
    0x41c2c0540420640c43e0420b00446141c1540d0803508001200c00301d000645c0900c0c1c002d20100c882d00d020a10800600b00c540d401d68030091155081105814190403290802111490160802d880003403c1480518004500740141241c0c00d001ca42c00810b0180455409001c194202c07054881080d0040103030601c0040040f0040e18611181d0b03140c0050700c00340300b070181c64950700c0103101c1d16920042007841c0c00b44070441d84a000125104e00a841840308400c003069060700740c2500034a001d0004904001010b000c8030805072040100300c40c1d0841c1007220365503c4c00c0010380041d05020454480d110360070250300d0706406200c02402000e020030055a21200d50f40135002d90441b55540340c103100c071106156901071206240c0741c00000c40c00c10000f428280180728002c020500d03842240d04c0c08900d181e004511000948003000a8000021841c4000758802514424243e040180000c240100b800160044a445811601641e12012060240281c51041d1030002c07101500540d83ca00e45841c581c0d441d4445 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 240099307 1250 240098057 240098063
    0xb030a0c03150e18010912020a05071403030706111207020f07050d08030c09010504090207060f0b01051c0c02010603081b01051e01090906020903190b0903070c05041a06030112 77
    0x10345480d00c1c0702c41e68a0078515086506549103402e543e00c4400c3c0f100c0b40481148120031003592541d09050004814045040c00040c0541c003030011885a4900282050800d900c020300ea002c00081510007641c02000712220700d0741c082000101ca00070a64101ca803405540c40d456491110303542004419500841c11500145003002550b50850b01c07441040042c4102440180a584023480000c0380030050f14024444070505042c1182001d41d0f65100d5000e0703a0152004940032078984034007042500281c050a50354030000d00701700741015178003150350f0920b01da51482c1c0006903840f6000d03899039074000e5204074095078022003165651015000260342c030703907236248203208507610341000a80c0762000002c0210a101d4107141d8003d603a468010030300c029001d0b5a009440003582045064015502040608480d801e200c055a004080d107080c80d401d011002411500700340c00810111001a00500040007640c170116000a500110140618400355032a00c1d01d541250002002103040e072070440080001c1c500c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 240100557 1250 240099307 240099311
    0x1603180b06030f0d0804020402090114030a14060a08030306040b190806160c02010c0f050c040e010c080c0a02032203060e070f05030a020612070e0423060a06080403080408040b030a0c03 81
    0x80f0509910b5500d5502901040c006030400000c5401890180c000b0b040c0f82d6014034000d0440921a0602400c640c02038030381640207940c0e440c100391004d003010f1400f540050115180902285480b03400c03622440300500715481182d0341c800c01007840d40c07084111071141082040582c00e450700e814520341e840c00c00b900d680c014600c03815464100940704030100c2c0030701903041e034510100c0142030340d0b24503604000d0441140c490081c01030b0482d82d610389200340e804100740c01c4004a10301d14145c0b07024200d95000340440e1070a03c1c0070440b81d00010380002c200e4001c0c0c2c903a030080001d4180ea07c2c001c0d02c0d1100d040c1d0001010503041030f4031621440740014a4800743d40d2401d80200c1800d030744604140c0d48040d00c540080d0421428050aa0900c0c1f0017190258010076506114144d0b404071400030341110f11021484001c1000304800a0400074030b034070001d42c401025215048203074200319001d00b4004004100408100c803080c0058100040c2c60103a4000f400a03508080c0c40b428a00e811034090410101c034400005c2c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 240101807 1250 240100557 240100573
    0xe030307111504081207030f020a090509070206070e0f010c140309150405150a0c0218091006032001021507030501031103061b0f090612010501030e12031603180b0603 73
    0xb414002040e40600e62002d5154038201c40c014204028180041024050640d2000c1941d10326109000509404400740d9810101c10704050400074030074405043c0d1011544040d080204582c1c12074880e1118107000c40b030038401a500c150048821085020000342190b80c0c201d0b882c0c2c82d407440040900340c0c09a00b1031300c0c0080c41c1401180311589025a220b00d59101502c080d0036044084000018400d40e80c07545450070115603a82c0100d00b095540042c55041d01900740300b04018004148494444055071590070b0260500d0350302c4100710082d00302c0b400c10b4843c1c070403460121241e0080025151440c000001100c25161107680075004200900c0240d40c007a20320b0110211514000ca0301501c00c862010306c50500300c184c075604a005c0c0c3c108542480d40c1404c100507036249a074550010f829070107540c0c1058805d540c100340c001811b6801d1915110340541c000c1035500c41c0c207206031080c1c0350f001102c9400b40c940f2566010003100601403004c142245004568011820300c503400b180544540d40070703801c507121700b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 240103057 1250 240101807 240101833
    0x3040c05031c0c0c050d1209090e070b0d1d010203090607030b10030b060d0e01061a040e01030f06020d0204031a0c09030a140102071b140105090603010302010809010e03030711 77
    0xc0e42605507400301407626002d2190380e03103010710003110800d4010b207040301c4850b40f5003000c184017600a49080c0c1c1e003030030024190b12925130b10101d0700e4041d1011410510400d48014000e5584104a0194134140381e40862400c8086085a210171a10020607440100101e00c62803007034004e510940c1c80317000d01d000e010005071009000c0e01800705c04140c00b070301040680100410480041202c0b29107a0350040c3d04101e501c24500300ca000ba040701c080e0300d60000aa0f28500301c28044640c09a02c040001c0d201305000402c411a17240e00400d04594203d41000b4084100707250980c02072085004414001d80b01240100c144041117202c44030b04130344581d507c0c1c07151b00c4d030000c0c0300c3e40380c0500c2151f1070b07055003c0d600c6280022210b400d026041c0220700700242c2004000c0d0350f00c501880184d14640148440d0040c100902da004181e0504111030a00389246070103050001324215200501001c1e041c0403170305020841c000c000350b04c02d0122000803026030b6141d0800c3c0b00e000b04090160301c003085261040707000c00d50782 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 240104307 1250 240103057 240103063
    0x2d16240f0503010e0702100c020102180d031e02030c030d0203011509030215070206070605010303110d030e0319020a050a3c021903050a05060621060703020c0106030c0b03040c0503 79
    0x18040c5855880c00c0d680303001c0d81482007000080408017180510000d6036041e940307a024a0030f290a49400258607024800d6001d0401d4004481c036902c201056091940805c1d000402c1501450248400204c0003c600d9000d030b01d9031182640f0f0300018031000a4020000c000c0d0380c0514142e90040083d21110b130364000c0121410205404040d501216101d50ba014540340d0500508045101802850400030107849520803107000342d000b90046006101281001300040c0309a070701c626103e003020004441c1007a401c0e9580d005481c040031690b00c1001c20715800720700812400182543c4041242c82080302d030703e4185d0401c500c81c0300c1c10490b1640ca034444410840f1000c0354268400b06144d210440301e60700d8007000029607400750080452415098044080707901400700042c07044c0100000c114034140501404618040201125043c64018155000c04400030a405400c614240350250701c800007820194014030581e84020800b04600c1c0e40000c40400c0d00000d14840e17400780b0301040850b41e91f07a0600d61 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 240105557 1250 240104307 240104327
    0x3050601092d05060d06060b190f1d062206030b061c0b060f040311030c0603010608061207090f06030c0801050f130f020901091407022d1624 62
    0x20403007240030560701c0c0b11002544070540c4488010082c00e0340002c070352510070455400c4d0b04650b40101000030010b61300484132a588803c0b01c1e0305c3ca02002840c1801400801d000c07403685500242c1c0002103681c0340e40d81d440c402910f00c8100722110b94940507900a20401c0003501c05c2c494480070078102000c0b04800d10308101a00c1044022505810803420f8114145d8020b03c005869030f43c0c00a0103105120031201d400d03024101a5200c0c180c07078584444a081014503005c46c11402500c030703003010001031001700d501075085e0350080c1c41035a02040500c035208006040c054690013082142c0d284c142d2108801119800000490780218591a4511380f00e1141c00d090b039034101c528038000b00321000032845101c02d180251444c18028551240d03000460780c0090540c59003a80301d0101c40d51150b450903040b41c100102d00340c0203001e900040c2005c1e0050000b00d0b1442d111410401c011035003008070354150100605c0b07201040c80e09204200c580350f4079849820f08107010380503103240206d0001c40303043c5190702841b5088 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 240106807 1250 240105557 240105611
    0x20316020715050d0f090c0e0f19020d24170604030203041e0b2106120c1203070215040f06021b040902041404111306150f1103040305060109 62
    0x1460b400400b1419075050784801c80d440c00159403030031200750b004800c0c41200ca046110310021007007075140103507601081002030607880794000482c3c24804400d590b00c2507803282c56100140941c58101010200d001012031501417810010942c00e20710401c2c10041060b0259100002c6000760100c0a2401c00d946a40031203001b005a48108418003000700001c54031445262a0f0441542150301c840e0200d22540000203c0a51b010210102e695900007210039642c2c0f2650a50300941184404804035544e07010681e056405031480c45070081c0d0858050081f5501c468001d0064840003000d8500340e00c05500500c2014194140130358003060aa1010814203035442c41152450b03441e5a03107000b000000c000c060812a07005c0d640b60900c4840540384200c1d64400e500030f0221401c1d41d40807200380700d0b019104020602d80c1034039140b410303c028117010404042c01402e91428001d620940e42007506d0280840f0301e81c1803d844080ba00000f04540000e000381a1001004188800312584148a030a1041d444d800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 240107913 1106 240106807 240106829
    0x3020315060901020a02060d0204090501032111060f061201052806050a180b0904061b09080c091f1815060804120507150203160207 58
    0x540d00303000c00d4612618003200000000d40320000000e00074496003021414801d207812607030550b0040c000100007048a940c4905004180394084c10b00788005446a01c00c000b1031910814501c2c0c2c40501040041c0b0060701c8210f5212105d280080590341c216600388441e41c80d0b5102401228002c0d504441b1008510741142c81e0070481c14844c0b01031022031421b000082103240c449040799011103444034a86a0b070f000b140d42e0301d04007400054100c02c1d4010004001e1006111203984a02c1c8000d40b43c2541c20407905400c1029a0029181c1c495505150049103061005080c0101c28903403000c0148100d800586030000c0c0311101d11141e8003c2c40c01400e16140c20340030b1040c070b4401c040340d09400c0482c1c4400c2c0d516003840105404c034028030040c559400da0540802c400d001e00d0070b030b54010b6031201804c075950104100c010001d400c1140c072221400d03000c8020000d501c2c000b00b40707141079500300151 = true := by decide +kernel

theorem cover : BRFrame.Cov 239928057 240107913 := by
  have h0 := BRFrame.cov_init 239928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 239928057 ≤ n) (h2 : n < 240107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
