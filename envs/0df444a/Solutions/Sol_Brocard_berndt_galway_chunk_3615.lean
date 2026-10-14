-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3615
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:03.926538+00:00
-- url     : https://prove2.me/submissions/1b2c5b1f-3530-41b9-9fbe-819339821374

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 650000000 ≤ n < 650179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 650001250 1250 650000000 650000009
    0x1a040501030e030705071a0d020c0105071b15020a1b050a1b050a0b0c0f060a050412050405090403032705010b04060e06010207060804111002010b0108090601050f041107080f0301 78
    0xc102d0003103900d1110381c41e4000c40100401c0c0d9002654200010504d070392010780d00c9084050f040e841c0c800d002020307004983c000e0b04005680e944035020015070640201034400154045501c0b40c1010940d80d403080308106030065605d80055001c0341d840c00c0380c0e1142801040380e0074500c2840d84406180e0802c141d403074401e18001c07685088030761118200b00111260550841d000038001244903400e1100d507624a411090303588086110b40b103032141d40c00c0f1080041c00e008010307a410018540c00c0c5070410841e0310008050751020300104000c20841038441e200c94507030241e014500059442440350003500044640c3c108172003084102c070002028090107500400915400b02d40400c803290740c0b044620004e00003169200d025800c00d220070880540900c07400e40c0e1261265012264102600000400325003a1003c07200041c1c1d5191640700c125604002030b19005903004000f03181a42c0341500290240c260218850300440c1c44051101c5117480c41820348504503840144140c0b591220717800504d894009205 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 650002500 1250 650001250 650001257
    0xf06090b0106140f0702120304030b0f010e071d01020c0a06030b12070303020706080a0605040603140d09240203070c030b0f100e161e1d0103180b101a040501 69
    0x10b103240c0140b201c0840700c143c00d0300543c01c02950a20645660700f0200e010303600190044040301c4100c02c113000400c040c4d841424141500c2c2071116190550b080141c00c8280d034400b403401484180346d040101c01201d1a003c1c1d40d02051080c4040040b41004400840c00341c00c188000404a074282d05500200b584500a0780c2a81d24009048000e030340d14546480007401607000500203000301031049140329400b039081400420202d9440005c501100c4540d482a03640502109260b13030455410301080c02c101200386403102015042c1800744003011074030540148411903603201c2c981c58a00900a84176095040129014a15030701d040080801c842129a500c10312071001c000b90ac0c400805117140d060743d60201d001090fa07600c00001030090000d981040c014000303115120300c00045610138140741c003a2207603200e04880b0f829002039003602c3d1000790701c00e05140c184490aa401c42003100041d40c03440e0066044603080e180d00c807100710b00d100707550001c2000c0c210085000741280350600003001103410030381c2d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 650003750 1250 650002500 650002523
    0x901020d230708070b040b04020f03060403021f060b1b070501020f03180a0801020313030305060109050d0807060e10020c070626070e03160302040606050909220f0609 73
    0x101c41d4200480300000028007200106804020401c01510350a0702c01c20450f450300d1015104e83d405090103c604507004e55204c01040304600304501c030184420001c2d001042682069a000784d10780c100101540020f00c82180d8510143c2c0e541d8001c0c1c3e00501008450940e212140a1502000300d100140c1e00f21601c1030000015055200281215803400070308050350400101c00035254445d030220b5001a0321920014012844e000280700640c02120140d01d1011001d4041c90302400341c0b5002481c0301c3c18041019820000e035107440400203407507980a40310a50f5241580391150051043c0c5a40003006c0c4281034a140d035241c2c6590040500c1d1303104070304950b1103581d949000c8803403095505800884543e40000f00d40301100801410707405c039049017081d2403e80311000101e0300c0e2500042520030021500e003020415400e0921440000d0406440e182c1e141c01d0661010603400c1d100605480600143d1f40da03440c0d042d455094000c103541358040814445d2480d01d00f4214042c0241c29000d840031745200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 650005000 1250 650003750 650003773
    0x6050f060703120b060918070e1005040611030d050108060f10060c0809180a150f150815030610031b0513020d33060c1a060f100203090102 61
    0x5542040e941a0f4820310158280000700000c1d150103c072103900f0900605c4112080e9440c1d030001c0050607032011a66000740f5188800030030288070526024010070303038107156a440326488000c54080c5d03240c5040080c03102524070300c810b186d44908640d10b00384514000c00818071900c041419401600c0c1c00b00e07001c040d41c5481410721003180ca5441101f008c0f441c10880301c4000782550000c0e00034480c00034010140384004c801c112400010490380c8030000f0f952410200420380300744115a0181c040c40525080d2682810144002c42d024030020b2424400400005405040c50502501c15100c0150070f40d401c030f003840210074121000c030340800c82d1440031100f09004504504410304080b07940c010860a180c0c003855010318003e6002c441c0050070030340c44a150a0b105464104090420b040c071030702265040002284804c40495130343c01420810804c15034440c042f070211a902d40001c00c040c5d0510016484440003e42c0207440070620540000b55500c03902c11641e00403000c0d0680c0178080e02910036100d0350 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 650006250 1250 650005000 650005009
    0x260106021b0d020d0521130e091002130f06030b0103060e16050c0c04020f0901020715050405130b040c08010306110702030a080306010c082209020306130504110a03050106050f 77
    0x1c200010b904054191404030151801d0b540030300c0c07014026402d0754010907030700480b072192500c1c1c3c000b140083c0000050714280c150100000000078401c02c180e5180074184500c0c902c3e12400c500300da170100c1d1a0081160513140214103450401000740305060382d02155503e10280c0a842a01140ca0110303280000003c1c0c45005a54094460bc0c100d80320204400c4844806031001d4000241840aa20490007a13011980b41c1e44014101505104c4a99482e801500002460030b442d42d000650741090072141920442c0d08a4107860039258101c9011101411541d030003030090100c00c80e4664000c2c1040300340c0940d19049030315207060700d00820742446181d56450f4640254850b410000303415174080d0700b04202081c1a03030041c0da0846014900302d40f411401d80c1364040c1c140c2282141080c03803a090036000799040240d0700842e004007503500f030550640c5401c200003000c0105c2c020101c03260648540006080200350001c80e080c010340201082d038081d840c2d05045000f00154081c00340116a00c1c0c4003d40940703403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 650007500 1250 650006250 650006293
    0x326030408090108070219030210061e0306180807030c1205030606120a150f06020d09120b06150f070215391005090c040e06130326010602 61
    0x820006007807400c0200b000440b400003005000700d0450144010b078201501c8001000141d59000368010300c0400041e1803803404461403544030340075a240c1c542054190710340b2400000304484d00420700041d00b16000c04140400c140040e002008590b001441343c0405402c0841d4071001d03406110002e010044c00c003003e4600f0701c000c1c1c0b20303184e0001080c405007100220311421964408030091012941501e5413900002014443d048900c5102c2040020b00c040f650410a08403544105d1500c42013040c5050049071851802d024042c0481001c140020b000751100c80000f500c1e8410b18a1080d910528030320b40b046a900715100c00c0f841140380401604144036141d096601d111603540075500000c8981d100c501d0b06401c1080b0307242c001940907410780034440d000c0c0500b510940040c000801c071864009411400d00031000100c1c0d106170728019a0a004260002d1655803001d2002c0082020419504040c0d86403003a02c06440040c500030041c0030101c01408141368101d80b81a001c82e1450310700c24484035115071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 650008750 1250 650007500 650007503
    0x190e010b0109050d11031212070206042f03070306060501020f01050f01171002070510050601051c0213080f030414090112021c080a110c100806060a0302040f03260304 73
    0x3412102e06000b907241c8002c07080742c000c2c407034160140740007501c40c0820300304410740c01c407101c0440c0d0106100240c1141c401e08140c0c08070140c400780c000f5207031a40c2d501c0210980d83c1400e410302c14000424012030754244503c842441c3c8010203c400580e43c91802d0700c041c09490250b00d005000d800400059003405010310b6014217040104400d0680c02e00400480c1c1c501000c9140a4500c100d01c1c0d2610903203c180300501d9910f021b14007401c0240c0c1400b03906019200042c040a04018040040354001c40d2400c09284a0296103034025079075a0340200103c142c0102c0350407040c000d0003a404a04c80d0310074004006c200312540c08050307040361041e107400c012a01109100c2d039006015101142c10052a0030400030031b80c040c203000001005401600d5032000c0390080303130074100407030004102070009480402501c00245400c49615802510070b400080002801501c11405181e002c0740d000416402078040d00c010300356802542801580c0c0e4100b01d5802c68110400c035440700a80603a1a8529682070b00701c07407149 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 650010000 1250 650008750 650008757
    0x50f060a150f12060b10080126060a05041110051b070b040b0a02152a0a0c110f19091b0905060703030b0901180e0703020a060c1406190e010b01 63
    0x903180144200440304041c6044841c185d6982c1c48108541d00e880e88460300e12040d60b217206283d818441d00500045007044102c0200303082e00010aa0f0b403000160141e07100c1d950010105503601c0301d16101801480000d115035200c01500e071196182d0b0b41c46400f5000011200c00d660102c00103003500a038554082e40a40c10142c0c0c41008103101c0000e440f402820700e043e0074411500c0c244502070440500c0d82050b41c0036070550440f109518821000e030015112240c0c017901800e0308d13240e29494060000000000018510344160441d04d1595032006002504804080c01700550041041098a000c0071a4081c140c0f00b2840e20296070301d070014000703080e445070310b580e00c840a500c1c0c103040070400284c000d05000c90401d03880b09030111094640080041c02040b42d040e2a01090901850000682d4a040c0c1140c0140c1e01c2030701d080025a450000e070308121080c81c2440300e500e10b558100044924001104c0090f6817040006100841c80e015484119580c0c40c2401080781c0822244d99030b0a8079280801107001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 650011250 1250 650010000 650010029
    0x7260403200c031605120d0905120705060307020a0507060908070e0a020705150703060b0c03120714070302161d16030207140304090509030a0206011a07050f060a15 72
    0x100407500220031004541408641c40e010321200000c0c50028103810044d01c155082c4010044c41c141040201e20501d6020083c1981d805080301c0180301d055688103080c40780700184001008044144040000b4100c003510315aaa880c1001d0080c1d41c55400840881d550701c1021000640948070301d007604280c030300b450058040645030645c0048502e00180c0f150001950800440c00012010004110710319508055040103241c0b20402504981c425841070048407000c1200b03168a5101008490300001c01d000f5030407190b00c640e4411031b810012040b0f40c4008084c000303501e1f0103041e00000c00603030240c0032112006000761180c0c4402d42041d02800314080141342680130444450b070040c403c010b40e41c171038503005080800d540c455020084005212a1890700005018001d0035514080d442e4440d04840040d40351200e41c5200a6840a051113003003444c030403401c0c040104003441170031182d00d141c20400326200350700c0c1d6462080d00c0d44002c3c1c6036041034074903041d43e01c1c0386d10000c015100101d9107840b091440c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 650012500 1250 650011250 650011277
    0x10e060103020d1410031403090625140a02090109020a0509090718060905040e01060e07210c1106090106060f1101060e0903070507050306040c2105030307260403 71
    0x40d40001403001c60081d101c21314840304030b0482c9200751003030202d0000040340500d54100720030718180400010b803554004100408007501e4410448a245183c14440244142d1084181981c1682414010f00450303408100d01c58642d4005080c001710340c02160528440c0c0d0380c42807020100e2040081e40d06c0800d4050000041600c0c110320038550000d4142050040300d0310413804008003240c00c0d044000031403120003050100e81040d100719105040480001c01143d03051203050302109000500e001c0030084802c4007240400005140c2c00d144028002c0c0034050318007400d40107041420028014007891052200003411014140640012100144c540b83c90a0040010485000c00e941800005540d03c4510000e11500c20b06000ba02c10704003880555244c3c0323454941181403440300e5101d540309038071440901c8080f461002001d41125007484520084150b2119a01c000e14881c0d2401b4185000210401c1600d40d00012050f220b83c0c8400c2090141d001c0f03e181f4046c5d008420f0310058009880d440100c00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 650013750 1250 650012500 650012507
    0x609060f031b0503031603020f2b09120b061c020609010f0e0a030303090209070f050a030902030a200112020705060705091f050d0507030c1e12140105030d08010e0601 73
    0x101a02e81c0221180d5141c1e48400100c0d1035980258481028800c5030380300700040c55410300030a40c1030b95510780a0861010400d41d85106400403844606460a07000c10b124003250040c5008401400076400703010030b00c8943c0c10722200400c001c4480b603000d01c0d030b480c030a001c0000e41d1007100d54401d036000344040c0c1003031510001181c034154101511014040c0a014030850382c1d84d85641100203600c2030b0b4001c030f81e078403c0b0f02c184481510040d0000081c8440c1d0000c00c181c46400c48140c03419580503280025201d002030000919001050300040c140421007680303500b11f1038102d807500c0750310b032000c0e220312501d02603021710901203105c0c0c03440143c102c0d0454404103845503c20401081d003d41c0003400307a280010001544000c1800b4850712030041400000c09aa0840b01ca0040c160700018900f01013000300300c0c00303c01601c062245601d1541d501c00454290b2a8030303010b0303454528240030300341c0700300301249505185c0304003c2000c1c0241071123442480600b01c8041e11030001981070300c040704c290710a103444400054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 650015000 1250 650013750 650013773
    0xc0a1407140d12031107150609110a080604111605060a0c05040518060f1203030f0f06010c150f020412020f0301020408070b071104020c10060f061b080f0712030609060f03 75
    0x2400c90945c1001724101007030030040e00d484a43d80c81400024100e02c2c00c510201164410311018010400070300003015a50b8102203910740c004001c0d5030110b0242a80c1030301c034030f25114540410004030300b40381c094800d01c1000101c2c030b48140384042042005001819003075030305000d40e1061540c45540c00c00c034001e0350b10b00000041d80080014203040211544240010490410190614110781c0040b040103c103010380c2c0c05075600145801d004104038149080000d21003800500e000d850f5400090480b003c0c020550300120091103240021521551510030951400d15103201c180d05c542d01c0704070070800a1806108442c216a111001401520f16116101d146900a03000940d1800c0100c206c58034942c885000815a54280384050702c0702c0c056280e0720200300e40454001c8495044c18030b00a01505401104040783ca403201c200c240e00380941c500c0c10390103510900001c000d60480c003080340f034104114104105c5c5600e25a0303e00344407940e100c0d040d1004559182c824002c00c20700700700040011a0402950 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 650016250 1250 650015000 650015021
    0x602070b07061d0a03080a05011215020c0a02030d030b01180b041a1c09021c0b0604020f041a04051201050c04140402070c03140c030703170c0a1407140d1203 69
    0x100d014030f9a031000d013400e0011201c401c0d00416101c20402106a410340b0956003d461480c100600140703d03501d070035181c0c1c0103075030340d240901e6030019804e04154010070898010b294000d08480102d1140305004028200310000680820041550035401582c5081c0944c141d4100c014441e003001e2800541c204000d242480000c18914200035a08403012256803a060390a06c9000108100300e05206001c0e070b030342c011a01040350112075000c0c100020b01401c601034002c00c0c1140c0160b1240c01d5030310b402e8828403d44d4403455500c1d4004601c8140e503402c2502030800c62310200d03000c01d01d86d264040d481d07090780c0c001c80e1084900c2c42c08000138000c0000c000000180c000019100509003041961050501c5140350826102402500c607404501ea0080003040c5840d501074000e842841d24594414100580c1850740c00b42014012400100541d402c12224027400c0d00000d40d418030101040800351a10194000c1e02500d269400c601181414020082043e0b40e602015060b0a40c1c182a401c8000b40021103d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 650017500 1250 650016250 650016281
    0x901020f19110a1707061b03020619020405040203101a040f030201141b0a0c08030903060f06030307121d0a060c0f0302031b1509010519020d060e0c0c0105010602070b0706 75
    0x14080b40b0005104e10200010700404d00a1140c103040c00b4010b8206015181078443c80040038400c00700017580410b0807030b003281c4610031038104e030080750111344083d001e55001243c01604c08020054a045001c0d80300d0f080311f01e1606140b141010040c0e000c2da0702d200d107000c0c411140342c49840400055110300d48050050300c40b4843d50707042c90821600314a290308402c28402040e0301050740c20f0140806080440300501500e401545051780602c0483d4440d02c0080c081d6103201317000c80000e41c2a45050040b2420254002a10403403900311003006080003104040002c0d644249084041e0b540c104403050405880c0e094440e2500300205603546603220340c4030795084045020034820407403003c0b40e980c001d031107409208019284025040980300c405120003809e9580036814401403004245074000050039a0361610303000750791880c800380701201400e00340d07205200882c2840d08002008584101505104072180020f0002d640d030b480c0c0881e500e030224003952940117410000704000410700d0340002c041646803e07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 650018750 1250 650017500 650017519
    0xf0f09112e03020f07051623040e070317030f10030807060203070309060606020705120102040e010b07030e060a11010b010804020f060d0b060f0a142d1204080901020f1911 75
    0x6182c481e132504a96400c941c254844a0301c1719a84401017030200182c058040180302001600c000c1040103e6480760aa000d20f0369148000c0005400340002ea0242d900309904030580b542c103c0c610381c0c0c5c6510803100c0f24800c40c1e007080468600c40e62411840201e0fa084900ca904041460315044001d50002d07007050145543c0d5011080001c10038004c0030010480b58001d820124601428803184a0701034080500302e03441040203000b0440010441815250303403000950716081e86180a0310720010106403164458004a8102c407021340c0040e491200c43c40100c002d100b001d2412005540b50b1100740c80003544241c913540325240a04103a400390450928024000c90305c1c2c8402000300718241e021806004210100044004401ea04902c203418105104e61009142c180b004040d25004c9100d1061031a0042030421280329200c020000d448d40d900070b0700b00040c4142080d160001311a0310000b00d060260042c0340a44620800200c2e1280c070300300d10340741003110b90811a60340f00001c40300101c489070b200e2803c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 650020000 1250 650018750 650018767
    0x7030201120b09040803090f0304050a1509080709091101020d080606090607060203090d0207080a030504262506020a03050414010504080a0b09210d0e010f0f09112e0302 74
    0x800b50f0303030301aa02a030308241c0d6034104405e0b002d0a11a12042d111500d40c0200720801460700d072a80214110b512080a4441720000e1341002c4505410075400070240344200303900440c10380380b203900480d40248100c40200010302800c005a0300c030080b80c5ca22801160b40d440c005090307810204000e24400c0320040c98503141001e03e1351610100c1c2c0040e6081c1c6544e90001441e12401d0303404020310405010040000d00d4440100e0b900201540300710b01884801040d41c004048240c940c41e1114442d00c1c84180a80d115000c03000807862002c442030031540c44550714088000350550020604034140c5070190303204d82c5130905100940340d00d6407000802c9810400c0800000607148002d0159180d92486007845031a0b60a020700380318500720048240030190742c05050081682c044500071a6820310344042d0206000886030b40c0e00307006000007003007420b2040c1440c010081c1e44426501c0f0f05003079489040c03c00548035148040c413082075840184816105103007030b0b0f00c1081c40c08003102d84440d004039240c00351070031217030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 650021250 1250 650020000 650020009
    0x110703050d170910150f14130506090c180a031214090a0909020a050a0b0c010c0201020406171003293108040302130e061e070309050a050d0f08071107030201120b 71
    0x80d8010703144c411f01306068500500d030000d09003020401c020418806030038401e00007020079002614420f455000043c2e4400f00c0082070400b821300640c02001c41410750b5803410103101c01840702000e80000740303000940b201d44204840c00e44941c0360000e020020300f103041c41141c40003070600c3c0304140c0e88165040d500088903074400000001400702c0c0500c0e41d0321801c0b401e01c014250340b0b10240e0841503900501c03003031014907403054840b006a28011100c1c2e000f41c0381c402d0012460303034140c1c002504608419440103181342c0c0c0b0042d00c550100a508956805070368408020700c2d03501000703400804156003204502517882908e6810400240903207480d41c985580c030b07030006540c464070320b4410402c11345900700d2580101c1c00b4072103103a205840281c00d01c3c1d820341882403601c104900800e010103050b40c6005480500c1310810038418840d611208407501c08e42c0d1214060810f0121203600000110400b00003050b0503c18252860703021200c2d00200982404d550042d80e580121401da0044281e40d00c40c0c0c01440e50f039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 650022500 1250 650021250 650021279
    0x1d0c12120c07060210020708070213021314190b0306090415020403060609060501080601082d100807080d0c0b130f0303090b0619090c110703050d17091015 68
    0x10200280b0800f890700902a0a01d020030f41180140ca00c1440314001041d00d000456440a504807038201b22642c2d4030a9000007030055056110210b400b500020400004a004852121030111240030450240f03c11041500d0750500960040c2d0703a003800421110b08080740c1090300103108240721140004e0f12120007003241c00650003902d03001d0f03c3d900b042205000902c030f09006403100f86040302c0c0503d0100300180072418064410344905031010514443c1c405082d24040403114611098181d0b400c105a00b070350000c80038000e0351000d004c0e0013800100c0b10030001c0d21030425441ca0702c070f0580c80d80c01c9441d0b4034080b01c00200b4620b01e5000030266400090381c09084a60594440c3d20001145203045c1013004a100d40245102d0003400c4080040b070302c00b13464684c244201c0c0d100c01c402058103a404c1c2030441c1c01400d4285021a80c0c032840d80d01004006010925004c80c06c3d0607924802603c1031840356440c00c4402391000e50702500510b40c81e07507402c0c406421030000032410800038a02c07943ea50702c480c010190b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 650023750 1250 650022500 650022517
    0x702010905150601030c0e031f11160b090d0c0b071b061d03031311030316050703060b0603040b04030f111c09050d08091009090c0908011d0c1212 64
    0x18011030402100d1340e09441095000c09441c40c10111301c1d210a03010980d64098141c58240c4c5201c95054803044841c40d801c8003058294802d40f40c0e480e050142d4080305064040d0004450328a0964001110341030000b5810040c01c80740d5803006c03648405c2d078940032080d44c400342000007000f5421400342d50411942008040c4c051068000044250307180312900318420b814449212b00b60810028032071001001d81200003019003051000d0382c180508d10000c0c0c6540304d41c3c000d40c05040c1506040da0144440030610303008980c0201010310403454600300300b0031644400c0b1307002014804203901080c0884c0c4120b00d8110444018208010349203580040e04d40307442e44046017160303c06645046c0342c1c50598007490980040806132032900b6403108690326085580134002c03080d4012051211820900742c883c1040c1c500502b221a803c11103074050341b000801d07008941c05051225802d05203444400410a4902c20070b0705401d20103442c00325851010802c2501440813441e030701d07200d0280c01e1a0b044c00139000030030400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 650025000 1250 650023750 650023783
    0x60803030f0f0a0b180a2a05130906031103070603051323060a05070e03070503030d021c1509110c06041202100203100f05060c0601181b0306090617030f030702010905 73
    0x286041d50811017034030003145071b0141f82c0b038007036905845c404501e4545811015803810540d0302c074145000c101004e408160310040d03000303040c0800001400f20084100305a90001e84c1a2aa5151106025002d84506480c115040000304121001088241c810003000c44610000e50030100c2c0040d050300d01d0714106a030380b10060783d070320000c0c06400d41d001030980b4a4690150040c211852a083c000394490080704c060400c0d03150006a050043c25000303101c0040071801140c01c120140e4503141c109650003060144020540c54524408500e40e002d10940b010b02c0b01e040e000301001d680d6962100a08500b60032058154810301c0c003446402d008a00107180b0035145080081382300e0b440c1c04150380c0040c086030300c218081c507000c1002e10002c220100f015070544a400c0e000b10031301aa4905083c00034a0444051604070b4800e215810605505400ca58101c40c0319100074800e00d5210401070680070810f502e0388060307a04c10423410a03007600c01c00156034046440d00001890b841d00d511400d042038940013090030750 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 650026250 1250 650025000 650025049
    0x30e010504080109031d010306050d0602092103030108010506060405130e070902040b2122020a030606060201050f060a150e0f09010f180b01080730090204060803030f0f0a0b 76
    0x910aa800e110701c0508008d2900707000300742c0740902144102e40700c020b028041c1500001d00c83704640343c0541603190a10f800311070541d001c9400740c000c4d441e03030802e000721000c950804020a10602c1c2010540d002d40d80c000f402980e200c40001001d0008081071061213903280195038000900e03440c0b40c400340c40201800c80d91950781e00b20301c03003941400079170800602c8090344540090000000a81d115629161550000c80d8052503090002480319141d540c4024119403c000e00421026419042180100203459640545440b260108a0040e046000300120400604070000009106503010300001c0b0002c0d00400310a002400440c12074030098001c502880da00740410460000a84481071808624041c1041180c0b82a4002851484050706090130400892519900d00d0640480700c810001602c10510074440d858402c18081c14910300d0681c491858040c001501311008000c070303442881100e24210981e41c584c203a500c0300800252048036450b42d40da00750b0300c0c2c40d118602d4204080402101c141603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 650027500 1250 650026250 650026277
    0x120705120304030209220b0c16060614010f0f030c0306030f0605040b0c0903030f030c12240303120109050910050c0304141902102304050a06050412030e01050408010903 74
    0x41d17000141c016480512000c0c0d070340401138800320b001a1201d9212640042982315079038a48030794090540d40b0781d102c0714000300170700070409294080740c100e80c0109100800d803215900152005201503c1c0c0401140c20040c2121803a4401c0d40920031000031b5080004035030341c582c0c8900000300c0e24008201c1d50a6505c000740b02c2480001298294131094200f0400c3c5003425000c042502c0b0b0107401703001a0080000700203d0311001c000c00540300c109900864041640c50892076943c00c0a242142c2040b800c40f10702031405140c00c0100844400c1c204a000d01e0305941d1030310001c0380092000420103001400743e04140068500140661800b840490111580706d0516040130060030046030040425948141620485095211900c100607030f01114041d14a05014030256400480841148030980ca0003811422119180000d0025180113513180e00341d668a81c5002c2c0c40c54401c50003101500b030212a080c10001c0e00c95000303800a9001850450f04142e900e0b140d850940310034000441c08209162004007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 650028750 1250 650027500 650027509
    0x201050903070f0605070314040507050109080a030801210c1404060b0405010f0804061e1a010801032303130e090d030209063009060403030c0212091207051203040302 73
    0x54200d12420007542c0b916410b40d460700903803010088002d010546990001d080c081c040c0e40605400d4681e03650300c2c1440e00d0249405a03c0e200540141404207207080300108510b02d001501d0342e0020303459120800755074241815035051030b511050502180b1000400c100c00074082c0f05000004000400703101d0503040d40581080141d0f15540c200300b00c1c40c50180400c004d90780c0c0c00710458507500e0460030a41020380303460410001910640c48a004d0b2240c0010300940c00c0a003542c048481c0512204614241a1006c001103809a00a100c050700200d94248040480140304d5010419280200c0c100c03490120360f020b049401001c6540100329810420040000501d010301c00040d070f0700f02e02e160441c44c05500d00c00003070b101d01505041c88110380080c1300340d0101c000d40b030004584800740000d48185504c0c105580c690317220300403074040300000e0409002c88400c500018400d020a0030f1030b00b019003049010018403e81441c01e09180101d0b03c81d01038006140d49450020714186030000001d140d882d8254014007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 650030000 1250 650028750 650028761
    0x1a1018050303030f0403030c020c041b02010f020304170f12010335191404141206060303090f0d0204050705040f170d11030f120a05250f03090b01080307030201 70
    0x1d009030401c10800c600300c060030244903401a031600b0001000041c0401c100d29200402e500c1c0d0b07400615140005412404100c41146d01280540c000e001c0c01000d4500700040e40800d440040044050302d845d2000c055018000d4007503c0141e96045003402c440084002d003d4600380e01c180d40442c0c40300040700c000c01d00d40284405038100154800400072500ca0103030240c3c82114121000702d005c98000500e0540300e0302c800880e038264400040d07241d0f51900c05510b02c0d0100c51004500c80d607061170460340b8601e8081540c134410107006026506103000070080c0314881c0242c07280d00760b100c400494410010390b214442d00340201d00700e640d000c0c0c80c0c6040c00c0300c0003244111078000d4200d079038403011001043c08000494042c1c1d0311451800e1490061050300e082e196002c2c0c206c20240c040d50200d040080c18001d0b0760039610a804000080c04161111110320309009000508500032444010800482c140a0b00340003048074654500001d07269440c5c2c81d40031308841c080e0060003a50304000b03055418580d09001d070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 650031250 1250 650030000 650030009
    0x70c0e011202031e0c0904060e1e060103061505060c0d0327020f01111002071109090307020409150207030206040b06010801080613230f060c03010f091a1018 69
    0x7900d5680c42d00081e50b01c0400281480c1c140b06a008007420400c2c042c0030364142c9401c003a103545850b040925010019000c5005c10001c2403240160160304010031080000300210420040e003256420364550b10302800500320302c405404001171000030705c1c0d210b180040110285007000380086908001008096400c2100501890320520480418100602c094401c0d8258112000c00d50200c0b51001030307807040030304800d0031054042c600c5005000740d4a1380051a109108201e0600042581c03001c000091806898944060740140718690050402c5d43c05402280e000e0320f02181c00c00c4424115509aa220740386c00c50040e0000b0b82404104607502044030340110003400d0404e00c640c180303c0e107140c0c0c9003030084c00d0007a20340d40d0850303103814407101c0790010300413802203c80030a06981c130030050340da0b54120a42802061150400141e01304c8200030940e4180c80040444442c01441c10894070003a00d0030445416000c09171742c40b00e0710165141120800860450746440d01840c41c1d840700c03080652242c0d0310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 650032500 1250 650031250 650031269
    0x702120408070b0d0b090112030801061404260303090304140a05010f120e0a0809100908060a0c02030c070f0e010807050d060e01140f190216030f02030708070c0e01 72
    0x10600c04024080349600a46095420154464000354200d4010745145c030b02454000082034004a81c0f10a14040d082c01c9a002c0e0319a143c040e666458103c0d96006c21410310803003c0d00a00c400d0040d084098032104d4507800601c034036003000d5206072016086034400c7d40c0b4120325030303c006401c03c074940510303c0c0a0030344070381252917882e1140341c10300103006d4a0040c3c00380410884880107004c0742107101d5014039100c805800c102c0340713049903d240003d01b562200d400d075840740d041800c01c1411b2500c1031000030150341c0c3c1e91000e04181d4480c50b01030790180400a040c070701075001c140009140340f00300b00b2400004017084c01001588500c3d0001c0340c0840c20040e080641c180d001104140140e44403654452042944844002000e0001c140c0541c0100541c42e00360064410350014004100040c51015008800c0b03620b003032007a044508415002ca1140440014200c2e40f0201c0000200f8024000c0d00c000341442c1c01520326005035923640c03000b2540300944c00c850100d803406082c40848034000030207016052080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 650033750 1250 650032500 650032507
    0xb0402090a0b0306011209080703080a05093c0105012603070b0a11030a05040c080a02030606040e150a0606020d031a040c050c0d17060609010903080d02190503070212 73
    0x100301a01c81c10301031803214000000c0482c401764884c006414400c44008010072444c0d03250300c0c00414980c480d8105500254001000c91290380390751003032070f006400080c020084000c40081602200903070842201c1c4011602001201000c0392a400c0c200441000300001200d605080c112841a07510141200400a100700c07449030300c030000811a40a02c1d0002042074035950f5008105028022a820104441c4004014401540d01e0741d04402e0046100c2c00340000e6140e1902d000903518046200045d601d07a0042d00403500d5401d0591002c0a00600e42e002e8032491440c100c0001d82c40340c0140c40014503640e82d894100711480d414404082d603840c080c64180548401c945d2a1420325411881040c811562814900724181c000c0c0111058050202d05071641c039000032502420305060300a0000c840007000e80000c90b5450030a0450701c4001c03051310780c1031380c460940d140c40d04107400c0f0880400580d035003004075420030400c4400500c0f4441d4035907078443d0b883c0780400000382401c0303002400c844209410f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 650035000 1250 650033750 650033767
    0x60705160b0408030d0b281d0717090307060e1e190303020d06031704031406060d12030b091504060911190c08071202010c020a0503041202030c2701080303040b010e06030313060e040b0402 82
    0x40344ac40307000c0780c032640c007407207589880340b00a045100c0c0b000d008060f54605121740c002003401080702c1d800ca40c182540500e2210310480542c4d2241620032000c0b80b0210203480a50000e4001d0740a00442d0301852400130b4034039101e540e0300b20340c02007443d108034146034086000c008114020030f0441038900c24202404403400e02c04040303602c0140c0240018100c1c581c5da01c0c2140900d100e68000e803402c0c00000c001c003000e42030031042c0030120101d03105d11500840c1000000300740c03071050303014014107941c240004a1500e100d2900208109140310b5950040028802001000c264540d01038121640520491200e01c80c8080c0c0c0642102d031490b00c0300d01076401140b080d102003078012050301c04850102903404288031092000a041c0714840070170661284014440e070b034401034414140300c3ca10001079410565a40c9030282c03a03a4a0004440090042d01100014800c0d100c1c0fa40d106900024080c0489090200c400c1010719094000e400990005000194019551500b0701409041501c2624110328003c80c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 650036250 1250 650035000 650035007
    0x705030a0c150b0d0312090b070509040f05042d0b010803030a05010504050915071101020301080c1206011a0d020708070308060301051b1b0c060705160b0408030d0b281d07 75
    0x62075000d428001001d071602c01c1080c0c2500421240c45d0300c40c801506d40c9c03505030005040c42d00308903c118040d80c070300203c040e100310705441810301940d0000105090750013400000c050162011200b0365203101801401c3c00010358040300b0034043c00015001d10386a00e402d61075076080f6103050b40064442c509001c2400380580021801c00c03030f10580000a46103907695050107460344580360060a440350b00c0040001040ca1000c01d41740c50009007145c43c1180d0b000d602d24a55600e8800380140794428000901c0008500015070080c07202c46c86952001d42403840c913031549059604070007816404501d03400200300843c5801e04c00c06911050404062450152000d0780c0b0499000c1c04507003400003c803000402105020403c000380aa400042c0000d075140524541540c40340070071109607d040a07080f0b0007180d82ca81810a807429142554025824040b039004000050600407144030b07007140e9070501394020103401c1d4800300c0707401001103140380c69a803810001140456030a1910040c181d070141c1444049a031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 650037500 1250 650036250 650036269
    0x30e18060f06090d0b0109050f0f010b07020f0d0f120f0540060e0d0305180d020a09022511120f070f080f010c0909110705030a0c150b 59
    0x4181c071004000e038421008510316120720b00c41c1990003424030405030308010010900c03134185c2d02c11902c01c3c041a22440c414195040d07058503e28a080d0b01600184a036107188000740281a000030094807000b50b2050104800c504251400d440d965010340c0d4110074001c05460f072542020741d40c94030b0110801a00b900802501804200952005103055034980781c100403205040400103108100d0969001d03c4020410342d440b9100d0840802d4501d64481e847c1d01c0c10710b02114010b50944c4440d481e050701100720445810316800c5a03039002c0c0c0031840410240e15a030000c00080c10082d5070050751401c59038840c05181328008940c00988002503001000507144890211043e102a10b045181314000b808403030600311526880301141c031030450300003003100c18288140704403004034041c2c440d1440c0c04188a4284c0e005000c1d42404205204410049a90143d01c240c410082201156042404640c2e440f42160b00001d003880001ea2281100014414031040307448002d000304508221980e02100850091072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 650038750 1250 650037500 650037511
    0x30a02090a05150c070905060f010c1a040312060509060d11060c16060801080c09010311010201150f08150f0a020901050702060a0c11010c080d0507090b03040b04030e18 74
    0x64020580d10141d403220154200a404018018000031007840400f400720b4000d18501242441083e0001800300c4807031203164041c49004d043d07040d507581800c0054808400880003115000c46043c181b005801c103041030280120310031307aa030348461032901440c5029034606801040c41400100107100c17083e40d481c1d41d080612503001000045444c0600001012405215004081805220b4221f4a80701000e00004282c1350242c641c4034003a40c070b50415941d2004040e040319000f04542005001207406101803050140c3d052001080103d03005802c80032120f10f87d070250100c0a4030700024011a4410303c0700071403c1c07042c09840803461420b0714229000c504007500d98071401c0d5000401c0070b556442036080307035841a00500b540740d544007061401040310700380c6002920420182801e0380030f02d61160140c0f421154000070707124100201950481c00500d4003408a40500210202c0041c0704001080914840d500505449a00b031a150501500707481480004920803c045003804880081445000d41c110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 650040000 1250 650038750 650038771
    0xc160e01150909270309030b07050405061605010e10050a1d0a030c0312060e19112a0703081b0705220608010e0705013905030409020412032303 63
    0x21204010042c4c5014450400e015a281d260584040c03540013590a0220703845000c940ea000d035510f81c81100e49000b0b07400b0f500d80c0120104803012600e0003402c50840c80c00c1c002c000005030302204581c2c00f450140c0180d180361003aa2a0f03001c01001005910441e100d0115120113110504010901c15443e030300d030180000e0501601000c03c10074580320b51040b6071410840c06040203003546428502d00039000c210b81c1e40c00c58201d084d050848070b144a015031816a08144101800e2002c18450380440c01c0500000b800540241450349034820401c02140c0010360144140aa42d846400388600609624001114203035121141c00c004a40300c4a054121818150303000d0262001001514400b80c05a540f21403011340c2005407902c0c0d50007000c1440812160240c84a18009058041030300e030071284101c0210489150f41c120a40b010100d841e540c10061144080d0f07440d140e00c9401c00300c1203800c590840b001005d241d503c0c0004041c0c2282124030444007028052480e244018605030140c4001400e00280 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 650041250 1250 650040000 650040011
    0xd0902040b03010c050f07110334030b0612010207061407090f0302060d0e01090215090406050d080d09020105070c06080f0702010e0c01050c010b13150518070807050c160e01150909 79
    0x900503024023652011200600f907442400c140701104c81e005044000900148101c0c41041544020306000442229400501124140e80740c104005006040b460151450b5400304207000001e0b1a6200b00c449a4140d81164030031400c01e580c000304240302c10b070003c01190001d400d090025903141da068030441c00282c400803070380c0c18541300b0b1039000d0320054030021741100840800c204007035038440c050b064a52045d1410000d5560710400c0114542c403607000504203080810482500d2400f5070410700f040c60040c1070003031030545545d036420302c0c0443c80da129400003680e440078050203030515511aa00409030788003e000c05100c20f4452a141c07038050f818641440340004903100c0312002900081c0d0080002491118074046101e410000343c510040f45510f0350480d000049454603010708a03020000d0b180182610a40da00c02043e03403402805420502030000500c9056000503080200c101301041c0e1030100d01505242003000c40001c03a040e040210682c0304400f101c800305030b10510308003c80720b0045000c100c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 650042500 1250 650041250 650041253
    0x7050121050403091d0123060d0e15180706030c020c0d021c060e0606062107030f09260405030a11060c030408060118050712020705070b0d0902040b03010c050f07 71
    0x40c4800c03540c5c0960115440d1000c041c1804603800324503812540b0009072640d140e801684c0b0070140c03003040110305500000a0120b1048014182d0001031744007407003c1200c5e0214000742d1254041102114100071504c0d51450940701c0000901142c4010003441c201444040194480651103140005d6080d015a5540042d0003e568401000141c20300f91910745201c001c00e41d082480c06400300103095000e922450000c120282840c404030340b400201088480a20804214464880b0700302610000405480d070200c40c2602c11988543c0054610441d242c1602d1080f5500e0342c0c180d0201c1450700b0100d50340c00c0c0004c000a0300d0124204100755441107200c02d81b00042c2001030b0b514040c164044066120109012411840c000354460598036103260748d8104842c070401d1102a55000c96140700080c1c05980614a2444180c02410006105405450015449401000050b04a61941c020203612402640290708082c460040a20400ea000384038010100d00c02400600c20480000001e0b00d00066070030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 650043750 1250 650042500 650042507
    0x2060415031b02010204030506160f050d0204051525170a051c0b03060901060b0f0a030b30010b0306150118030b07030606080f16030608060f040507050121050403 71
    0x36a418100350b4944448a040c20020300035009804212030324401c44003c038a1104996150000b051055610700310025a283c0c81190f4541000d40801003564003400082129950381000742d441219141c0e00a4a50f01410100080510b000b03039407009080d007541304000400c40007101403c0540340420200e03907405181d0812034088c40360034501c10703459400040c05c002c22003240d00403000310b50342102190302e543c5440410078203d825520a1419481c401c1001c42104a1075001070001250141000a084c40000003c500c1e40c051f00032082241c00c1d1714030420301140e1303c01c821515403034594100030001034410310040f955580e0050a00499000154603003071090b0701c036200301c0c0071030440c02c810340e017215949240041d00a1000c1e1b64500c0440d05101c000300e07845100340c00d01407048000500c035490b03d86403034142004030816940c184081680b42da0001ca030001c020071459000e200c10b00c100c29454505418010f0170010390f908124104102032200c101040e0001091004107220b0a03c00640c82e25540b0b03094 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 650045000 1250 650043750 650043761
    0x522031e050d0203011401030605100f1805030607020105090f16120807020d05030c1507080609040203100c020f070603020304030c110315040b0403120c0f14040b1b010b0303070206041503 82
    0x842c14a4000000032645421000c61a50700d01c000b82c0741840b003251607208104100b42031600450018811960910307500703205030195194581100c3c1c0802207a82c550021030300300f89040342c040c00541e4584060046200f410818600c0d0030741940040c2c100010701c1c40f194104181c0b40d200700810990000c9460061003030042c12905107c2d401000300c42801c209203092a2240c02615200840f8011007060300800d00040b409a407040106954001c8140d071170b54100321581390094400e80e094890f0b405041426a200d00c40d081e88008250002c0051328820340f00b080c90003c5a800203020540180f05120010381c000b060540b0641c2c0c0b129808004c1c01d500c0c40400d180216100c0e5540e91681100144014081405100e0340100c2c0650740d400700066103810f40d80103880040303014000043e49070b040c5055081c030500c2002c44811b5402c030014602691240c020149030080d0310b902d0b001748070022861901d0310302445000d810361400c0d0041d5084c2031141c0c002078998040c0307200746032229030010380074040c0c2440703075112 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 650046250 1250 650045000 650045017
    0x90e0108030d020f04080d09031109190c11071d1e0105010c14062d01030201020714030c1e09010806012121030b0a06080f151c05010522031e05 63
    0x32500405400d00d4008d18103c2148001e4800540c0716582220314101640030512510241c5002d40c04840081c202000400c40340806400300280c06840c2d20341100c083c80520000c05182001c0408401182c0702e202c403595001e49184003503001c984002460003052440c0b14110307482400c2c40081d0225a0400540400901405151b54019001086605c0c00d0500c1304404200b412044441c64011468480d031006a0a000190240e0b200351420003265188030345028203200e000e415560b401540202203040e0480c80d09120528055540889401e4101070385003600502c50b04006206a5150100c01c003804189450540e2250002d1407904003032040c0d1001d1040708040740500b800f501308407000c0c014010410071150921400c010f00000500c02e104000c0c141c0a510600706803070890301d402c81d15100800d000d1414681140c2200855100064601000300025009900100f018581a04000c02c2402046600e6140808074080f40000c40e40c40040002081120f03103000c0c0c040007817020150782070f0144440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 650047500 1250 650046250 650046253
    0x909060a1e0e01150902120c21011202030c030d0e060904060e09010f0f0b0a0b130503030705151303020303040f060f0204060c060e0c060d0f0908070b07090e0108030d020f0408 77
    0x1840110440150310102800c84e120039440704940d107a44a0009038030842018505256041011491100850005240003001c01ca0102043d40079112002c2d42d03000300344e209c0310700074203010080e0095040502c0300160070b0328118090481e610300307201c015003c58007140a03540284030129803e442d50321641e0001c6e024001c0407400c0c0c5d00503e05141114043c00710201011003280c05d0031182c07a0308003210b0051481c840345c000c00003084281416541c044942050002c0301d09082e4003900010662418001080454003480240002a03104003650b4900c1c4005800c40c483c60144450b4036020a5020058980003944200e441c400c11040e41800340140610f0b11402000390310004001640036003040800d500980300b25402d011610071a00a43e4540e051003082581003541000022030045803a441020011140c0c0000109080191034031011600302810480e0ba0144140030300c540150401c840800a15000c0306108040d0705004180340c9038050000c0c00004580c000c101500072070022001d03030b00682039910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 650048750 1250 650047500 650047511
    0x121503190b010512030a121409010902030c010216060507020f0a06050414090115200613020103291201180803010302130504020f1003091b030308090106230321180909060a1e 76
    0x807080c9d4000d21f0500340482c0b0a100d0580c1e000c0c2503500220f03803017020b101e550807840c140d1460540141e0302c9038070094040342c0c070100301103501c0f83c0ca41d198016000500b58a1343c0b05500d860038010650b404104400560b0300c0762000800420030f4040806260403002034910704048a005452000708001401050f140c0d018000c0b02c0c02c02c6048001c03c0303a0100554001d0703030140010108016132100c400b4209841207080d0301e44003407060b01424041080d00f50034140000010340c80301c114046001d4240d41050480341400000010819032610185241007204c081d5000c00490400390b00040c04824070b030104c01d0140c203121001c01e040034000d03842081e459401a0b080b010203844403440c070b078184480c1d01085010650b1080410310304201482030b2030507034010070074000780c081c039845021400700c6c081001c042e8103101d008150800300c1e0f00c0c1c440d0410b544420344c2c0c07155250124824400050040948020b016221100c1005400413001845542110f2416800203160004030903c102c402c1114407814001414030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 650050000 1250 650048750 650048761
    0x304110409150b100c020315070504090218010e090f071103070507030602210702070b0f090619030b18010e06120a031101110f121503190b010512030a1214 68
    0x5801543c04914119013120005074020026030300e014220b40003030b40640c80361002c040f9800c2607200164200c011414068102562051040c042c0d900c900e00000d14984a0461880035517004008604685022101003019142100848001c039100604040c10000c0d4400c10703d0b5026014030403074001a0300042965101522403c0c072001a52000104c01c03d000c44000c031600000d41c2c000e1196010b0711081d4050018a49403060450494200c09030080c0e20000c100000042c540c1c544c03004010250303c0034000b400c11aa84080941142e100b0700b8200e005064900164000b006641880b50540c2d41050700c0503075079150b4038046460504d54504c0540c0b03a2184900d20024150400001c1d0841d6041000900410140c4603502006000d082942d4042d82070600c4903120008881c0456a804018903261194401d00d50001a01e8496a42c41c0c407401c0c41010040b0b0010321400b44070140c00b511703054a083d1606078010800f5a50380c8610345c104c40410203011584810030905400c000ca00c070400c403040c0c040d1802c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 650051250 1250 650050000 650050043
    0x10c1401093009060302030a020909090a03121802040e12030408040e150108040201030c030e0d120615020c10020709090803010603050a0c350705090108090a080304110409 75
    0xd446040340d5202c00842500400046010100380850041ea2140005458000306030042d400182c0140e1000740c0030322400b841905c440681a01c225058030081003a00000d040240540407111081c0846506100381c04e107084101c9885000c401ea03064800003100e0601d5900c190070440710b40d0a03c0d980c8030001050001b4808010003410944000060180c42c6843d5507100c0408032840f5009180401c1415000801541c000d910200f00c051050402040e11031418900794101410410301c200415100100b482c000012441032a004c1c014254000e503210304950800381d9924070301d50319544500540f513028542c140c402d01000d402440c13400c00621509000d0f2508000c250024003e00c00044d281400203140801c0c1d0b030040010208075500c443c80140010080c00981c5042401501002000c080c040001c1440c009591343c8141c0013692420746030100000010f1a142000d0300001d5664083c1c0c107004046019402102e801560010107a01c0d2004c00320045805032904c400301801c02000014056044400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 650052500 1250 650051250 650051273
    0xb043909091805070905011203030b0f090115030c030b0604030b18070603020a0809011806020c19080405040b03030403210e06120106022107020f030a080c0106050f090106020c010c140109 82
    0x1140d8180c419540d29400d0f45c4040b200e09209000400b141d0381d0708600071900030381c8030f4150100e004c0e00003070350703c0524004950000002c0c0d024a01c0e900150208100055052080b03210315801858180829410540040c0c807a00650001500c054140340110f1000b204282c4029441408041030f03802c0c080d43c036100030700250410321803500441c04003400548080010304c540c07581800d0500e60b0010400302c035101d80c002900200c1030425035110704000848441c450780800f408e09403003555010b52b83c0d410402480259071950101c2e901990080c4014000916030b181c1c4e030391003070080180700004201d40f403c04070f40624103802000c0e004100003c0900301400202d4070203060f90760030340841c0d8040d069080402a03904007144116110381c000d000840052a140300501c6095200034110740d00e42c062506c0b1110280c0c0601959041030b0b55401c1c00f0031240c1854141c0605005040720041c8980d032600d440a500c407804020001e040100001995003040301c0c03040c21b030010702c50310b1008001130310451500005065 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 650053750 1250 650052500 650052503
    0x103051303090e181e10050c07231b03010b04020319090c0f15030e0f030715060509010f15050f0306100c06111e0c03220302130b0439090918 62
    0x244080103076810762980120390080444008c11441c0c5401030b2140780b00384414658640302d05041d2101e03003221010401083d2180c031140c11078000850342010070142114071990301540113034010b004005201c4890b080c11a89018800e0006c240001145020030000301d0a1b001040f08005491002c500780700100041c0200d21040e45003003210603061280d15658203400108402a944100700203030008814152108809101c5500498601e0b242d0001aa98450903040020f4100024004011303e0142c2c80b420840724429040c03a078900404443c00503180d02c0000c00142c080c4004101131100a4450f044440c9926044002003001111510380c400d0540c2c0081c2c0000710042d16030001c01c405480903000c650780c0c1010100254503100e2744038000746078041620044941e04e00714541c000013680303481105440290749844001020f02d04d540400048a00e0951104201702d0310a0a01c8031f64509500c0b00300a50f10258410940c00d82c800d0011500c0d07c905400144605003811481e00503059a401042e6105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 650055000 1250 650053750 650053753
    0xf0e2211040e070b0306301c090605030a051302041a0109080c0d11011e020a150516031e1404020306061012110904020c06060103051303090e181e 64
    0x901402c0c070180d85004500400d1010801003000c1034003480d00805a00699090140d94082514210600741d07945404800c0c044a83d040724080840a40c0c150004100752940e03800c00d4030006042c250300421500000301000b2100d0b55a0300420a2a400401c08100c2c10341d000700140141d41d010030b0008601c6c8407401d0041c0c01700782c07000808196504046103440d55040040c0084110f41c030703503031590440c44031070b00341050501c08880381c40c0000c09036001c003200d0001d580340c00401603000140390010340b080420202c1c42c101c5243c04240880e03214008030006a480c000d190114000300c034803c1081c1800444103a44032107516110044919640300072010344658000c42c1a154140c2d1018180008035032810031725800104180d0b15905800c085034025841d101c0100640707410080c11801140c100d0703200e05034031004da51113501005860b6a145c003071217501c0072101441d0701c181240da079005006a8203a000b402803c007600400554180d9040424035080d081d94402c507800c0e003940c5140350000c00320501101015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 650056250 1250 650055000 650055011
    0x2309010b071a150a06030218040c170c1b0105010806070e0d031b0b010905062b20060f070605060603010f0312030905030d240f0e221104 60
    0x4030460001601d41180e00440c1ca9219803030380001e0140050001006000d06024108501e500307a2520764110b8082e150319100180e4030703e01d406032512404040152288640d04002e40420155801a074554203996004401006a01c801d2415a80c5008208000007540704044082d5234a1405400c031504984803c3c0c00d6403450345807420210340a03200f03c088540c100b03240418040004e4402c084030700140d602e50304190414081070745d4024a1000a03800840d025844078107004651400b2003140e981020000f03ca4050340282d00000c524054070340380003910000c900341d5030380e040304100401031890110003814269601c0d518502212950050202034032080c1c6803000140c0181041c1c2c0c01c6a0680700e803419003641c001e1030b6540301280200848810702c01c060303d404030300c00010410009040601101c010220780310703131802100000c2a0301c194440c3c2200064090410090154500960680c0c0c00390711101460350b40c440156101d0399842c0e1100c261582e07c2d51078003042c070060780b981c01d0b81b00200b00c40070b009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 650057500 1250 650056250 650056259
    0x30907050109080c09010b0c07090203070804050c030f120904090204091202100203040c0b0f1b06010533090105040e0c07020114120105041503020a0b070b010b0a02070519230901 78
    0x65860400c011035800510641c0180305044507c406410a00115402c803100207841e0120002642c0080d11281d0115100500707020402c04180a084212001900240035103400d96503d144c0c5d03188041c0c05000d82c2100001c894102e52520742003a115035401030400d001c0b4141e2803401d005200b03503c2501c10018014040035903002800f80c000c0700d000b6604010b0b01c481260a000510055034005190023540c54420080c1c000014a01c00c04d0001620100c4083c169035850881800900071884d9114030301d40482c0b04114503940d0034034004c0008802600e450b03680386c0700354100603a0188110781055552036041d6080040c202060402051201e100703a8901e254202c003c0240c0c0e400b40038040c1e400908144000040c052030910741d01880c12003406003000c41990380c0d00d8000c43d4064140d40c00c150003e41c0c00041c1075051004440c070300c0d0300402079000c141d8901031001e42c00a480307000e64050079100700001881040707800d900003401009404000c408040300d40040800c003011460312403a00b400362a00300d00008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 650058750 1250 650057500 650057503
    0x15120f011107120302090d15050124080f220804090c030603030512190603110325030809030109140f0d020d300c051201052710080303090705010908 65
    0x3800b50750300c0300301c02c0e4040d01c249400760083c1d0060380002c0c0c2c03c40c0c00c680c1d0716000704e00c01440303038006521003280014495040110301c005074000c81a4040a2100d8105484003240e441214242c1c4040040e480d02c056490300045042512880210311400803409004002030004102c018000c4940001c01000003a0600c079068059400c50f12024001c24018006010445488641254004802075017000121017415115084a81641040d1502096606945141c1c141000a50700301050741e68561050303240c0c1480000101c0e12030000601c40704000c10b0460854500350440c3d000c0390343c040442100c240b00e04516640c0c0b400c038064402424450300c1d6075099244d001181d0208103186540d00c90401c0c081c203c0710b0032200d000d60400c0342c0a031980c00f440d120000c10184a9603806140c0f0796642590f80540590403e4201c2040e0420b91080005160208555040c00076149013103052001842705035071004440d200c07501c0d155102c44102e02000042041d00340c0d01003403c80644d03a0076201e0018490300e805109 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 650060000 1250 650058750 650058757
    0x6030605030604320d020c010207050607080406050d0e0d0c12080106020d110c12010606080a140412050d0c120617120c0f011505041802090a0515120f0111 68
    0x50002035041c2c6100844035202c44e000e04400200383e010303a403480e01c0b03a224286800c400100c5140142c00c1b580d0207106035039050080c400200030403141c02d824240745848a01d018400c5204480a1000001e40041b240b601c41e084081d450340c0d040e083d01c6e020303800081c0141c10000d02c40c06c00c485122922400c00c92550180c0380d114140c1d0810342c000c0441689084003030300c2400550b40400100e21546034060745c180c0d103121441084100d40c3e000494074528001e0081c0084038041c01140e456404e003c9021201c80c2500c1c1200d40c0150010007003441c0c805600783c10340d540d2103072810b040480c03400c01c034080d0440e0390813141034400b10703444440801640740d03104140d2006140801c02c01070107401454503080703419081c40c080c101400340403042e59400c4051130007c44c00c4595080100031482e208402c10022450b0504c140c104810000da03110a0007083c0c1d0f0300007031550000604500342540d840780841c05051a0001a0041c02d6001e08071852001c01c0301d10340340d520359800848404540c2030202030300c045604181034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 650061250 1250 650060000 650060003
    0x303012402060f060d080c030d0516050304030507020103060306090b0615270105041d0601120204271805030c06061c080d14040f031701050a231005030106030605030604 74
    0x34102a880b01c00b445901d40f40098409644000d820b078416020600800c0200b41c048800700065940b030350119819420307644020800001c0c80c81c02141400816001000c4075801585407400c55034401c003510041c2c0c0100080d80001c0e01d92850310703058004008a1507025170158600700d030b411030350400e45d90b078600051042c13101c0900c0070900801500050b008043d000c49054205061403410207407a00c54504013000b0000e0b00c17400c0c05071071310203200007940c001c0040320071030300c0c00d223419840c0505007400040c500280001d060302d03698018180c07003a0025950b00840001c0d00714000303100f40881e43d042503940c903002001400c07094010303c00403408500d400041c0500420040d0030340704400b40e4948803450300390480400aa861529281c1c24030400d400420030f01c1c45135201e240310a031544900d04005002008164110015210f103c0c010700036607407400b801c581101c040120903406c100c00d02000c8961300010840f02504510b544400303601042d0008041c5060321900d0303808108090f40c0d03c0400d0340c3c8203800e030f80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 650062500 1250 650061250 650061253
    0x6050a0905061608030a0b0303070b011d0f06010e030106030c08071e0e010e100504060e0f090d090909020a03061a030f0309011205061f030c0210050108030414210303012402 76
    0x1901c0f0014130501c002d507a00101c1c001e4009908100c141c0481e0845c1c2c0526000c4a14102c031400501c81c0d114641d0b00c40045201e03040e020340062030418201100c00c070000c0c0c1014180301448a00001f503603002d40010016542c0300351030103d515907038210030350b540d01c440c01104d0a501d0f980103000311200200c400c0c0d40482c0c2d41d000f44440a41d28010884417424406004009246c40c0c0120200d00d0f5103a600a1000a1984c0c1c081c140491905140550040d90040c2100750750703410001165110a900c140721100381c031004000024100d030303148001207030004640e200510107414000f452201c079581c1090210a210158240c0c0d49100c1c01300107a580300e2103404212404201010b83c1c7d00c1d81d600d96548107582c003100280444c042003044900b14542c00075500e844a0010ba280c0c0d0802080d698180304000d06c1c0c1d40740382130074803540d410040078035202d007e00c1c000d512070351045409000c05540e5124140342a0840c111424038042040d1009545a603c24025468039405010702e201401c80d074a002c445804000d5030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 650063750 1250 650062500 650062537
    0x90f2a08010b21060628060507060b0913021207030b0a0203040606080304030c060503060f060c0a050d021f0e010605060403060608060f2703190504080c010509061b120406050a090506 80
    0x20412022000070311b130900d0368001c850100041d81e00700c0600c44014111580740c0ca510745442d45041410b41e22441103d42c0120200001d000c11154600d0304404440d5048402d11415140380b10b441d80350945662025000c2c01825090101c1c02c19503034000d60045000f50418020b190711001036a0b5a4810380c440142007100e00c01d001c06c50075104801540d000380f001040c81909042b600f00280190b0820000caa0136500410007a1080010400241800355081e002800203c1200c182c02c1c490200c2030811001103d0b11400f40c0041d80c1c000f036004501030300000700310035113450300c03410b061004045a01988200d44545404185450480740c003541c8a0b54400704180d1014102c8810590207040225071403040b44401c3c455040d54059012010805602d240d54841d1141d1900f240740f460100d012030582c0c103201040201c2807868813807004880007610740182c200d00451540d0029480c044148800d000c00c61404140800d0341c83d8004000c000d0180603940d40054182c450303080044c41e10810140c403483c10b01740e8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 650065000 1250 650063750 650063761
    0x305010312030b0103020403020406080303060a1e0614040801060e0a0606090e130c030501050a0e070e06010503340c03230904110d050112031101090f2a08010b2106 72
    0x783c000804a034018900581080e83e00d40c0890b09645180e002906150801300420030182440295200280240e051480e00c40d1000c803540002c1082d6800b4500800109403900340014445204880c014641c0c18000c015403560f850a07034000d61402d50715130b0714842c00c01c1d00c00140e940c481c540c84d205540202c48090101d072245803440722405440c11045550551707510b00080800c1707007841381a10600c140c01f00416424002d007480c0d424801c094108087c0c900c00d4500307020083c5d03401000c0e6540a0317840e0a440303600507030310002080f0302c100290300c1a584002e180c030706241890740414644a524402c0c0c0b07440d40e6400c00900c0c1c0360300381285000c40ca8985201070180c541c1c00d182c650032400caa4243c04c1c075200c0c50a400705074070500381c450903000103916504c000e409004156020030041c070048100c000800951202d03959100348084412000b5040c104c0003144400154044040306400c049804214462207560b9181c0a002c0c081d03216242c2d20802414507400c51000604a4505c3ca804040c4003514440c0d445 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 650066250 1250 650065000 650065007
    0x506340b07030e1507120c0203040503120408121605101406041a040c03111815070f08030408040e2a070201023f073003050703020f040e090601060305010312 69
    0x9056100f00408041921b400030348a225110000049a000d1a601c038140320a1514288242448003a00402007004000d64040850300d0501c680f1200051a9108095008010100c600c2d8601a0272030003801d01c400c81000d015401181101040441c5518581e245020001103449041d1340301034100f444030800c41c440c90158031100c3c0c4a4183d082c0042c0e0300305000810350b440d4118000c8080c034075110284191503171074094840c500c10800300c804180b078500e107640c0340d41055010001c010400d10700030022904000040054601620a20300400002d241c030014081c000f503007501104541c01c041c051020f00801d001d00031104400d8060f00180b80d00f15004405c2c42c032204a842c1040c0c041000c0e8800c0032180c0c10701c03444450980460300440ba4031210b42c3d0034100304400b140d00c8001b01005d54001024030350401c4a40101203a4468100040c3c240d030b80c07000980c060300c00d50390050603138a00020003081c5113aa960350741d0b0280d041c910441d000350b038803601d040c1d04a039020300000d0208000d040020541510 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 650067500 1250 650066250 650066293
    0xf0302060a0e03101806140c0703050901140a05120601140703110a050d0815041e0c030902120d0201060b090306430e040b09010506340b07030e 63
    0x40c013114107001c107035080c0c00c08070350440c1d9006468600180004080c0860f0303008654498101034440b11341403e20110700d04e018402c3c404001c0c1070007408101d0207166801003549848500b60006003503995414544003c0c8664440d602581c28900c41c10089a035651282c000f000c00302c07046030712680c50a5659241903d400d40160203a1101d480342141500009d80c007400b0060002c034440d207a000850405447c419038103000122854050b62078440c01d100c0003054035443d1581942000c40010b41c02e0300368034089000d000009400b82d0024070f00760b080300790700d00000307102032014203913038002c0000d1515000511460700c40d80109aa040c0c2c0b2030380118103c10307551150315040311647c66500c821560250280826640707046582d07607100b40e41c855442141034001d184047c0903142100d04211442800c000a07403600c1c010f0040a0040c840803503074a40d030740b009603501c416100380386004100c3d80c10071443d01d400611000104580c10344161010891a42c00380c001e00c0e90009044000e001d00003594820102c1004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 650068750 1250 650067500 650067527
    0x11030a050f04171c030c08011a120c042c0a0518010516030516020d080624130f1206051e1609120c090231030605010f0302060a 56
    0xc08010018400d51003110000784180c0f448003038030446410310308110341c5010501c507440c14181030501d80300035076034040c0c0303214103403400e0a81d44c0040d4620041c107140107018007800580c000c2c0c14901404000711041c00079000700ea42403040401140311504c42101800c2c8803041c11020b500f14540419052015030700900e520142158401c031010b8100e0a610342503c405450320b00441d9901c0e51035044480d0305000d1982d00c18161100e4032007107106801c00030360f542c070050001c604010808010800540e20200582c2010083d03090381505d41e0f00500030340d1019402081c103107990644001c070014007000301d00d0310782e411a45410410705100703410b80c80304805054003c0942040c0d0124010849017511082211401848040204400031086140c0589075180700e821580e24007541c4545480091128003840094402580c4c2c056119480000081d0042013102c0f0300031034810420300c006054100c510780e40f0007120b0141d03101b4000c50340e81c0d02c003803001d500f090f000c040e400c11420031800100d0741c0070b02035081708174 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 650070000 1250 650068750 650068777
    0x3140102090303070213230609070801030f021011070e180604120c1502030901020a0815060405120f0f06330409020111070b090126041401060b04141011030a05 70
    0x2403141f87d00445403402114449010a0f0b100c060112030300b0002c405c20350103842410000380075415038403034103a441c19100e4000c1c440d008200842c09c4042c0b0400204031040387d1076049900650b00c034449207540003c1215003810f88040c50074521540c40000802c18056900010502c8941c0901c00c1d044031321001301082910f10f07100407448003000360b00901c000c620900c1008001600c40e94230040040c200c51001c0c082101c240070304440740d140303039480c0c104407400c54000f11026056130000c1030f942d504210300316a5000007406031030124200d000010800f1442101e4122080d20030300160b5250486680d2a10030b02d10a50b0200d5006010f5410540d10103a01c1a00506208005080710040d0a151444903003060301400d1010a40340d0715135810110881400d03400c0c00c4d401c0c08410064011001d10301c0010030203030180c0c814850301c0d9881c090a5200c2e0018041810840755125111040004000d0240030028021070344080250182807140455940c0b0f40b40c03060245140c05824601260b258008075562002c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 650071250 1250 650070000 650070011
    0x20d0e011b051e040b18040623010201090b09010b15120403030e01020c070f1a031306110d0903080402011115010e06031002070501200406050406080a090b070903140102090303070213 80
    0x2001c04038084c1c8010b00c0c660b60034980e03e401e8103518040561500700741d640502e041010910090810402ca00e040d103007000346c4a90704030903c500403409010310000c09071455111a0510800500642010880c0703042942d0002c1c40e001c07080c280c500640f080042c4800f080780c0341d40c08100040c0c401c3c1c0141142035004d5001504003101d62840c241440340765845180c0c1185659420011410102c440c00d40146007030055604500c0c1080791041c070510b0348400105a51354a079106110700a00400b40c07102c0110181c01001070803a103150140400100751000d0f0b011550115902d20389090016201091070301c40310070308500c0d91800780c444000e050080d1141d9414020b00d14005c101c10039601c06040d549000380b0000c203015601d4403054152020052001c90700301c2d810401403003038981180459003290900d140c80c440c141c2c1c0d4958151300900c004079000380002112400e0055184c3e200b058203003604d0140782e020f94920b07070340c020103401c038424031041d02d0301034205014010151804803a200c225458428000c00c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 650072500 1250 650071250 650071297
    0x10b120a0b1314070203040b180415230907050d111b0304050405011a12040611030a021b0105160507020a0902190201060608011d10150201020d0e011b05 67
    0x69091481e90038030304803030740c540040f5a5144000a11608682d80b070001e5440d090030f00b114070320310348104205485640648000440340b51626400f15802a2140f008801001c0d02c800c045101c2e50000b4010320041290a1011007003450a4807032540514401d85807240b50400b110a080c0190010054412200d0030600c50319007500c0018400c0c13088903100ba0042d5541d94201401c01040300e0060f007100d11030900800303031b010411500400319808480d0407200c02c40f15607039070320707084002d880c181000018140c00032061003013048031500509035804440c440c4c4c01114140c24002402c0300c00c100c0311030848000722450070310642c0c052002000664005090781e00740503111020341d03069070b0010381c0940018100c0103d0519842d0b0a10801000d8030a51074844a03c1d4074040301601003a1a0b00c00300ea0001e0389000c00700305507080c1141c0080041c484101020660100560081d000b50031449030003080c20b042c1036100030b951030180b1590a000d0751418110f03811a02520084030150001d909202100e642c2006010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 650073750 1250 650072500 650072509
    0x1201120303270303050f06010504170304030c0b040e060d05030406050a030b0306040b01050312030411040b010e0307031b0e041505040507091b11010e0c040e0307060501031a0609010b120a0b 83
    0x2071042d0107658214070300d200546002400c45034010b010b4000d1015050910030030faa4014129422200022825810310b1a078080650540c4116480189010501c040000c5c11482d008082c204550203519088516a03609007801300c17003652140000d0140d041040180440c41c0114090140e41040b850005002090080824500f42d016501a142e0044100040229181c10080c401040107800c0c130711070940c109561180900d01c2d01c560324900c82e9484800da10280d074810306100c920054010120f55a03595203040410409100a2100505245003d400b240c0340c101c41a17210b004543c0010030503514100c01208200410b0050811511030140900014004d0070705e004494684070406e107145130100c10311401501d0b80252000c4204564107066002100c0100840d0002d088201a02c011640008003000d25042d072082180c000d00441c6424004810710480e405003a0410aa0f0540d01503580c03034075410803840503024071820307006000420244804640500001e6080000300001040c80c0034000d0014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 650075000 1250 650073750 650073791
    0x5030a02030a060c05090d2607080a08250f03060803071716020604240305070c030e0a090e240f011202061204052a0a0902031807150f051201120303 65
    0x26512010046260303403044070301d00c0d10300306400c00100c2d0f41b27850002d0507030781c800f0300e8065250050300340890403000421030041880078400500300303001c10450800d9a1613000e00b44010903100b01001914015020640702c40c00001c40321b0b0142c10141c00380d25a282d240380d00a55500c040c04194144058905603c0182c844c0c0c40588050100f0103c428001074600614045801d42d803a0840201800c003c18012010340110f818a2484c4e01440c0400c8400c1c01a0003080600d10a030b4485162985030040a082800d004110320300d10308103007981c03108240100118a0f040d040142c07078000340d2079603000c0104020368001d11400c414500c040c1110b410401e64448013408000110f03002e5509401c5028100d200c10016124034545400941041c0043c03041e4170042250a80603000340401c032580003002c115440000700c0328050150f610300c00c80f05095101c6146082c60f030a109804008920b01800120800340510305407030b40c034028003034402c003e40e19200440080046031001a000d055492501228545110354032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 650076250 1250 650075000 650075003
    0x2c0301110403060f06140108130804060314010f08031b0a0f060902012304060509130c090302031c08060103020f07020a03030305160305160f0908030a02100605030a02030a060c05090d 80
    0x4240e00c9502d1814008141d03100b00d60030080e900c2c0f8217a014422002640b009a060312420328000c44035550320201d49194031074024000c0c285410200d00001c4041e4140c2180d100030741e104000074500d90384c42c6d60000c0c0d5120030780a8102c15070014031123515954a074007452150b809509040781c50426154845003c0024445010f4925a8031050210299600b10f4007d0503100c240301c4d405140c245040388440c0e098000d5001c0c920420070001840c6407140d4407220b200d070303011840b517908108000038103902074034141084c40200d000b0b0203802c100e010008034403507205d480e0345070548038542540e8851004400030340c800c04445021040c1485103a0142e10742c00a00400345100761000242800c2105e668503120076109041c07001c0600781420001840c0900d00000344944440c102003101c0f8807600010340d06071403d504024064880841d83c8143d140d40007440c4400802011030400543e500c0e074052546031038514202a4240e070000c2d0075940020000d42c07004403000c040b49040c50400a0020004d540006103910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 650077500 1250 650076250 650076281
    0x11202011808031308030c061b12090105041a071d01050c0102031810020408030403151d030315100215091c030b090108150c090103020403081b070b0a2c0301 69
    0xc19084801d0000341c0030001c5d02038000110700f085503000140c0e5440000406821003c2400c400803806000c0041c2601e4000c5242040d210585c9050780242d8000c140032201514800c1214504441d50b149030401540901035070b5603000100c0d03024002500403a5002110725041100c100280d41071040c003171014500982d900303d82140d59041c82c0714038600d0320310050304002c5401c0c810441044a828000708a0f004c4130b40c0b100110030000d8080310618014456420600c041411540074100d160102000441c400c01c900c41d2410300040042061005c20340c5a8800903001d64440c1c0424810307a54400a8a075000b615001290070f1401c401c0040020304207551341190105e6141c498001c1a40340c050250f502400405000300b0074810400304411100780701404c0c0425050000483d68400e92194040318061904004d42c103035940d0905403081702210740b800400c21a4066520f001c42c07464407507003c54250f40c0640c0d43d0780980d407004400465070700c4241c00e00580364044400640c2d203e51803e0084404400e611613 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 650078750 1250 650077500 650077507
    0x6030c04091208100b0412080721090902040f0e1938010c0320030f030a0c0f020319020a1401021b06160e061c06050102010b01030b0901120201180803 66
    0x104040c00e240f1014000003d114150f500620480c201501643c04895941105c07034030a1400b130030801450300c0f41003005000c40c2d006504009005440b2024605d098500740c0d84c1051043c3e075019203104a010314061a801003101c0c450401440c40b4072242260000e03004249281d601807400700d07110440d0720180101480581000c0c0f19800305654100e01c40403c143e4920740041c0035001e400003895490f18104c02030902c840c00b02202c030301346985254840382d482c01e00200c0b55180001c003240e42c4190021920307002e44a04141c0640c001601c41c1c0c1039020080b116400540c00d10301a00b400300d181d00310903d00740c011480313485003180125207881c16000d00c11650500043e646c0e00302800f2140f00c0b407030a03942e0403102e41c1f000c8184103061140c80041808441e0b10716000650240c1400001c065114003414640070500707c1004031140c9a05034041d0b0300301c401c260000c000c421b41000040d41500c0b11440c6040e1f008418100401a0f110480c60980400b0301c1454104c0322a050b4a0322458040c6141e0407a0b20240d1011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 650080000 1250 650078750 650078783
    0x61c0c03110301030b040201081e0906010302040c0c02090f060607080412020901062303071b1a0919080903120a0921121d0a06120c05090303040b0306030c0409 70
    0x511900c1051028805024a1913056480e0000d0f00f05000c2c1c4000d04200308080002d1071400f45e41060340c4107071020000c45c01103003031041c0010703520300c0d003804240d1041303250001c0700492078014403c06c602c02d5405084005284e035064082c0d010b0050042001d5003000e010002c1500041c8548010710203805034042d04916180c1e035005010b480c407016000402030040c0402801354800920300304000601048e112140c1d280c4d548038040b0f0f41048403c0e441401c9101c0c40340c101c030402190b042441c120300c2d00000804032640d00c110216030f603580710a05401500002401910101d4007010040c05400005812072304070040c50b0708821241e0b070140280c0170000d4146a414013190012802d03c410303d0409440750008400340351241905052000c1140303050000b4990107400300c0844c20304500302220014a803407000c3d6602c40c00a014800c007050104411450302c001cac400c803c0d0080090300c000071805402036081c85d0800281060940c0040d0285500d4403c078600900c4940d114000d203807420341300d2011380c408030150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 650081250 1250 650080000 650080007
    0x13210908120d0e0619050c2502100e010c080d0209061303171809070207081207150507170405010605130902010215060319020f0406030303140a0b01050a0e061c0c 71
    0x16040e0f005002c0d0010340501403603841e203510403900d08040100010715501d580c4a8540b4610542009484440d8021b28040301c0380c03440e11548402900a0360034003601e140300601210440c1360f01201c10b0102d00018000c50210b164000505400d0301c1c1080014607040c09540011040d401400780c1440440144209004203c00c481c0c240f50a044407a00250070611410440c000001c031112034980207550b41400945624401c100900080c1083d0040d40c04001c40810000d58a91107144240c1f11100c00c2c01d20540701c13040038801c1501c21559035540c0d080d079142d50004198806009801510b80c2d42d22044007080f25aa11134200540c20703640d4000042c907030000e20000e400c1c401080c0c0441d8a1110010800c449501c000c9003441d5401071142d14899000000e04c009888091921a034a0300280381410100801d501175006800070341214120601590320106500d003515034651020340041c000340803014840c1e00584a45901c514000e00c01403c1140009c29024452101c1c000c0358851520741c40c030000710940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 650082500 1250 650081250 650081261
    0x50f0105090705100503060306070e0409230d090b0702040207030908010606020a11241303080c030301091503030f03050606160b011404111602060c150106020613210908120d 76
    0x126801c5c854154500710380000d4461100400e00c80c2404500008030003a43d4865109028041c1e0000680d10085041d800c2c0001102407000140e0301c2c0d10801700780d8006d00c1e0050741107a08680307002c1071091a200c515800c1c04040d42100c101201809010380303010800305000e01035200a020160300900040c4524201300c100091383e94800da01501165500c0000005030005c210141da05041d2056603c0103a00518400c22a40b030380054104040400c06aa01e0070001c0002c50490b06049000c1c0700e03d0350464456198420030340702c004d010501c00600000514025040181c0c0440c0c010b1000381456030300701c2d01699121040404540040545006000c07044140710403660b204000d8504101440e27152651003c40d00c1603a00035205041000c41d004c0071951450b00f00c0b00704905110a9031082a081420240620028003510026006900009201d01d242c00f4070341641c0340d005620319807144003191808244000785007941d0104000c0901c0071805000801002640403981c80c0c815a0710500034130a60200c0300b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 650083750 1250 650082500 650082529
    0xb0f061311030601232205041107120c0f0503070b0c03100e04050115080a050d0f050a030c020a0813080c04090206030705030c0c0106060305041a0121050f0105090705 73
    0x245000e500c080c14001141c00c0e25800802803c081c4030180e41c040ea910340519220409031070f10040040d40c01550580103980a40d0310813030f00c2101c00002c0d00c9404100544040c402107540494040c02200041104c2c0c64071448032424900f0221002140343d21601c47c0202034190544840d40b0020703440301000680c0640c035034882c0800c0405429030401084804c90000d540c410464280e10100118041c0042917001001039462103455507251a964a0714a031a00203208084d5070754080c0b0826070f20f0342801180701c400e010070703140d03209494041d06200a40080000950400451160f0140040082d542400402d442c000ca800d814203150304d01020700d440d2000c2e15102c0e0b8022401c08400100503111441902d41201c103c2c10300c1a280e9883e0000c00c280e5004400083e0351660800383d00085940d016400140228003038405807018461810400203000d07006e1140b44403450b0b6400546c81040c40074100407814500c50310035034070b8401e24076a00c642542c2056409440c1908401e408120701c3c0b501015118608 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 650085000 1250 650083750 650083789
    0xd0605040c2006060f1002010b120a031409090c03040302010f0c020102090a0f0b0403080a0c0f0f0201090b03130b06060906030a0b0f0306100e04020f0402070b10140d0807030c0b0f06 80
    0x6250030f1011501181175484e520340201704801003008110300039000820340c102c01900414901842d40049541c1e00040003082e404510a21000442541c580003207a988840c082c016540c0c0303440d05284105140e00081054045550b0341c01541c2c5e07808003d0182d8075644409a00160b02e0394854000c2020b0481c1d2a8400710010800c0c581c200401e818036020f50341106d03000007242d0f0322003854010035200c4100d0000010b01d003004100c003407010407005010b6503442d24000e0307031101180760f03c50883e0445032100362200f400c0b0384912085c01d400620b80a141c1036010308003a001500385220b0b40003054a9820644000394195182d0380c28080340d0404c4c404080c2c4407041140205035a003400f1074600010902e502501c0e42c98160500003e0a5407151059141f0079400074104650310f10180c104520000010351b5100d074541800b0100140711401d03402002c18124000740b03425071841540e519408954410101201030110301c942d04804201002030841c03007940c1c061000656407800c50200601e000300240500700b44c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 650086250 1250 650085000 650085013
    0x6040603030e06160b0903030f07030b030c0907021218120307030c0b060a0f0b19090b0a080415020705030d051012020f0a080118021c03020c01050d0605040c20 70
    0x71a40c80703000300c01e00b0501a0b4030103a030307900c2c0c0c035401d400007100540300503000b081039205000728080004001d41c41030100d500d12240c65103941c0d200300d09607000e1a0103540d059000e00c0b88800740f407900b04180d98100f0b15900480700b140390402c0b0100540d4208660500c45805000000381c0da60804e008466510000500a14a050f150f036a000e015501c4080010340303914065030009003143c9890b000c16000e485100044045150360300740a031155449080040d0300400d0207502810300300e006544410903140904201c5003041c50a0070100c48906000b082618032240031510304803400303040d20007410341c04d006101a40c0e4421840d031130301c000d03100d0207002c501c04401100d030200301d038000214800c410b481e812140040c010b1602030002c5c0c002d081540084403e9440d01000070082e90707101d1001d80486200f551040d00c10554100402c0c880c030340361307000907002da0051064144550300c290020000d2180c40d080000b03405881d00c001c5812210f0b205100c80200da0001304c0b5038040085c500075503c5070350441004240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 650087500 1250 650086250 650086253
    0xc0a170c0f0d0818090c03040201110a0309170c060c061f0305070504110c0609010614011d01030522080703140711010806061e09010f081003150908070c03050606040603 74
    0xc020500c000d0241880f00041400c030450144054156000310000b0300c0c800c02c5050500c4e034040300f82e006980481c042007181502c052600d07000704100c2e51198254980060662901d00c0000054801c0c0c03490004600070420201e08641c0c400c80135144180c2c902d4020801c0380ba0404445108004903003c08507004500c4108000040000940c20107990003030300d0200307040000c0481448103019001055055015000070008020301c1540040100c4030030103610070055104400640d96250000e54240007079000d002c0400c41540030390002178002d070800c00450154007035401300c802c400521070803c0340c0d56040060850103055118650794441e403030350300031503141443c96500c43da0b038240d0710403016041c0081400011003581c1c590b02034815807240d40104440c01c065085610b500c070303407281b02ca5601144a0302030100d100d6202d80c01c1c0d00c4c421035020322149000390460301d85440203030341c60303015504041c3c0b16281c09000441920141031054466075540400390b08500d401070601000a11a601851901c4400c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 650088750 1250 650087500 650087509
    0x302060418050711210d0e010e0106090b0607061508101a0a210615080c090f01050a0e0a090c0608040c060e010516060e0d0f18180e0c0a170c0f 63
    0x514030145c1103800c08001518602800b281c0c051209054035141c9040740800700c580041d00001540c1d100200200100e039118071880c0308458200386821382080081c0a60800928654001512000001c2c1451012580c0f052610324145010540e810056180c2d408c00e44040d11b00034120b034140004550301e040250030055a005840701c203101850403607010298407030a103c0146e02c05498490032012210045444084d090780c2d40c000724501c24020b460340000141c1c080340d05d440c81410f03108000d00c822790315864404068095100a000140086e42e680e403480b00140d078090503040109425150422246082d0800760b50032076180d4006001e0060351281411b45aa03c481210345a0318004403408040399281002c10003400742d048010100d220b8079280d024415007000701400c20304c6003035171020b41b21580c1c0718010f0b141d4841803082152a10300f50111815840f1035400c0100443d00c20400c03180840c05400004000c0b405590012014051814000f50304c03034410f210105c0d10030420765405540048140c0480c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 650090000 1250 650088750 650088763
    0x21303060903200d082e1d0105042007030e0a09140906090303280207050604020a090908030402060a030e060c0c071d010b071502070305041d0601020c010f090302060418050711 77
    0x30300916034000e80c0702c0c45803031800c5585181c520394020184c104070b8487c03800700004071149103410038a003100b0000080a08d014002d82001418204100b220307000b02000d5800c190700002003c406011807040350000035100d24504900610300d0803000326035040e0745c2006580044024000d0707941c680105003002031300d0f200041181d0f000b110030100c440480720606c15440302c1d0000341071520015400041c0d40e4082c01000590341c0e0040c0d000322030381d41e0115691048401121088032009080300d01c00c1c800607015151032005442d4420140c20042082e940b81ea0520b401d00d0b40c05ca42800c0b20f801c01191002c041403082004d00c000c1c10711404111101250400d8504800d0414412903070544000240c401c1000744915074502c40b80304441042d5100d045500c1d0207011074002d40503480084022050544000103401c040038024541a00038084d0401078600454a6081b00101c0c1ca0620140c2c1c51f0000058503100e0080c8000c100e80e051201c4086504018142626400750400b42008003107168030000c0000401c50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 650091250 1250 650090000 650090011
    0xc0c1a1b0304030e011103090405100801110703090303030522050d080a0903090b030601020f0d02071e0b0a0e060c0706030b030c0301050f0f0a061a0c01110f0d021303060903200d08 79
    0x6c801d0004151000713a2951082d07502c00c070b82150400c424040e8101c80b0b410400151101d100c003d002c4180742480594442c00340b42800380004804060070408240607511003500b201010000c3c500680241d018040440075913001150603034370801001e040150300801c1581c0040c180d4505221109468074020710210150061402d0154000302181c842d80c0208540c600000089094a00c0c02c01c101d04044d40ba050140f0600340f54000520a8205100c0d08010758411303660301c6040c3d241409100002214907800001005030803100401900b528072004200392401080c0740da801046220f604d5043c103061015515009000c0c1e8102002d1000c00040103040035480810081d20142c00d0b036804010398083c4c040e551003403440d034054894032908684800000c0c030403403200c00020300c500b00c2ca202104d200d5100d502170345420300c00c0503c03144100c003205800a1030009694406405050b46035142c038001c40710020000c60100b041240a5103e50404400b507141d5041d0483c060848290030601c0505040e000a14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 650092500 1250 650091250 650091257
    0x109050112110d0506160e01020d080a0e0a0206030a06090e0d02060f0a200304060c02070e0604020708041509081605031207051e070f120f060c0c1a1b0304030e01 71
    0x18074612644481003550f0000341c00138215001d908200c0c91034581201e000c945440051521032015106500019444820b00602c1d40c9564650744c0c3c0c4000d150003040703c08450075003030042c10408405a543c640c081c1d030080002c0c0800080480c6030040c1c140071600c18204081c066003107100c816800f030707801190069100c1c602881405680c0d03140500c8100522503403402580c5100b031010315440781100c0c80c0240d8400e0303110700c1d8100305400312400180d1b42c6210ba8400c40e45000c58000c002804c80c10b00342c010305a541d02c0303400c001e8100340c0c4491700c9840e0680c0c008540380016501700c00400044500b040540680010480d500483e58103104c003080e1140c0300c00e001b1684d1601c00260940c20044200241d0384146600e04180b170740e801a441d2502c1d255400ca11458249140141c80401c9024031a13a2111141e58000d8181c988030075165101c0020b04049403084042c003041e1060900421148182c5003664911a400c41c14140350050b0711143c283d5202500350f44007901401003100007900480c04026208003400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 650093750 1250 650092500 650092523
    0x15050307080c0906040b1201050109060509070804200607060e010e0c090f01060309080426010f0b030a0210110d21090b04021905060f0403110d12030c0315031a0109050112 75
    0x10108000f1801f5035944d01581d03207007000018080e11180e01c440260349086070488809d499901c3e048692840c1a500075001710400c00c2000e140301540d005a951480c0040d089500f080b02e507455440c122401c1540b102c0352030b5114000f140e070303425050050f0400358808403201c911500b080e02c413468041805004142c103040e41c1d00000c03014132400805031001440211005007400322030910001c5a141f41001c113822170741c2851045540d12646014031003203140007a0040c1aa01e281d0340070004134003904200501480494861404840c0341440900e03a210143e1b10394185956803515e107211901441124110340500d80840000081e00c035503c0a42c0058044505005e408480c09032303070903495103c1c1e00c5190b000c200007540c040b00c11a0b00001d881261f004009850302c0030300d2203091040704a0782420041480e00103282c1f008006010b0b5220501d50b45c803a1500190a056491200f036152026400946885542000c1111212a900902030140c01d40b05400d000355490942c03d000039150f911350041c041c01141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 650095000 1250 650093750 650093771
    0x902090c1c050705070c03030e13020c250f03030203130f0510030f1512140105060f12011107030c1101031505011413030c21030c0b090307020415050307080c090604 72
    0x90b4140c07407410b5049584090015924640545035012212001c0e0152b580c08041814942c2c03544213803041403200a000e80704c100d02180108201d140c1c240e502085401e9414000306140e01342c1078268001d14440c1d0001c650301c1521200307840070039210b0b0344860304c24003401c58240141e440d18564180c907003147d818081b03259003030246000081c01c031116074413211411360103001521000d003545000203d809080c4a84100302001d40307150a0f05d5007110495041003164117000c0720350821440400c5040c00032400000c400c60040000d000c0c1b9071203450250001001c04150006000c04400c0d070a0700340c0d82c2400d082000e2400000343d11001c0e01540b180c076050100541034001281040b208840b074420b6a030341d00005964072072034200004c08041c000c0314060221621104030410604104140c0e01d900741c2c5031440383c655603655481032001d0062001c42940024440d040c01a2a00c3c0034900003001c0201c8a40f51103400e14041c541b918030307141e1020030700e540321901c01e401c03030b88444a4503074101d02d0030782c0d0114044000c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 650096250 1250 650095000 650095007
    0x150d05010e06090d12060b0a0c050a0602030411010909090201080c0a091a040905010803030c09090408090619030b18041403130303020309030607030e030a080411030d02010902090c1c0507 82
    0x700950488038000d4004103c0030601c0441d07500c003203a0306600c4458210000443c200200c640e240510424280b003000300a100c81d003d100b00100c0305105404941a041850f503034101660820f560813100c0241d01c010b0304080b903800c400400041c109211080044500b55000200044800303031655880039000211010b4492043c410f2030042c01d2030f03102d1018040d00d0791100f0070303099209201c3c0c0f03003c030791801c07001241008010041300d000e8000b4940503414561400200300c2c100320094403c82d044042080119443e40314070000d015104000c000c3c1901e500c40d500310280550741c0c0390344803074491840c070b10b01e1114180845640c2500581c004504104940c0303445126441c52080301608600d4842c11800002090f40c0080202640b840039402c0d601140ca950405a05a628103182c24215030070034001c1070545031041c800c80e42c1c01809040000315404001011a00b810303548401d10005035169245074041d41040b22065400c41d80315056245030440c0d01d0500d855100d500c401e1088038a450340042480e9912 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 650097500 1250 650096250 650096261
    0x30d0e010e220b0f0411130801022701090f0b1218100203150a03141203070c0210031e2f04060c1b06080613140a0b040906060602031b0303150d0501 65
    0x18080d0041110514001b2014070035040701450400d54040760b00c020030714000c1802610780c01914808a07284940c10b82c82028400d41c81e0001850401030905c800041131175a40c10781a0007009000040d90707542c0d0f164031a10340d4500c801440000943d91041f030020b00c81600007201701e07a411024500503229100c5000342c4404111101410364811174200022040c011083c070740c00d100070ad1207411074010150105d000203071400120307095800300d026040340c4030160500d1040202d03812910300e0001790032100310100420000d0842d19600d01a030340c4040004408400346a6020701c0b8968840180009402800f1308100c0d1040d0300501082000c3d5030322000400202c01500c4483e40d05016800f2070b85500c030300c0000d100190440d00c081c4295102e5154141620980c03240081140341584c40700d2a13070380e803c0c0034240540901a500394005540d64201c0021031400c0c41280c01400c09580903640d07408041134408030380d41046c1520100f640081007800711904402d006558107000989483c44070000b01d04120f0b00410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 650098750 1250 650097500 650097529
    0x12010c1b1b03032a0c060807030b0301092004020301050a1511010f0f060b0c0607210e070602010b06031905270c030706050c0c09060a05030d0e010e220b 67
    0x2150801c000c410542c02022110b5408900c01501c2c031400c0c0380c1c003100039410600c41400ba0401c40021000e00102d40320b400c00c10b81c0405e4a00340072038551181c001090844c0e041480507628181c0a20f40ca01c01c0d845548500c040400040f903041d81954100b84c00101d002007184194140c14408888600700780d07000c0c1004140c40034480000b007294200b103081d0311018240c45010a0b122921748031010500049102c1604c035400c0c21070b0001c061507034503200203980281d02c1c01d43c3e0070040b41c40b040d84015124050702030380308002c1d00340d03022740652440d0020290940f030701c1c5595240710340402d008008451f000da0300000000e4158080100c1c09465122450300140001030b0506003408000584c0c803d002c20010702000c0082c0309400302c0c0e8101e0f6540204440c103001d42410b08406420080b6448181e00d004582e80e41c0000e0001d181d2018076a45800092a1050358040040410003030102c1800568004070200540c07001520b003158040303002070014443e06c3d88410007482441c1d4038606011a40c642101040e004c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 650100000 1250 650098750 650098793
    0xd0b0d02030601030b0a06090e06070815120f0c03122203021810060206090d0c1a0f01080601051009290a090e090a050d050307120203130212010c1b 65
    0x55840f41001c82012408940b1000107038104540086c1c5c0a03124490b00016401040140ae20b503212940c0448000c1c13406003101201e1840c412404889644110a0b0100c9081040c0108420b000f444c08541c10300c0c0140c41d0b128845e0300200c10180449442c8004c0320002c1101e05804040c5d4103c0400c0103ca41e01c0c1c1d41c0000c1d4001060064094100000f02c4401e4040d11142680c4801740759500001c82c0e81d4138013181d0310107694101c030000b070741113070b01654040d1040c074400d0b50400c4202100074101240342e01d0071103032002d004903071000400a07002c3c280720b80c501500003502e80200c4040e04d510042c00580c0140b15000c05d00d03000c8c06049179210380d0303510041c0303520200300d107501c1d81c03544480070007048a4000d001d142d280208900108400d5080002c01551072030340480900b801d00f042c600203030b030140c00c02090b11003401920034280304007000602c002c520400d400b140d03001d2650400e0060045d1480c0018284d0541d85c540f0415000b11500b15400c46a101280511101c4a1030240b90410f0f007142c0d0300e5010000d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 650101250 1250 650100000 650100013
    0x170c0d0903140109030e04090f080a0903020907090302061206030f07030b151909050601020f010501032628030e15060108090706090320220c03020901050d0b0d0203 72
    0x1240ea01105400489026101c121004000e8008440c01c0390000c2e036004001c529824500651400c054201c15669401500071b10300000d16511200e086a200001e801c000071a203000910031031910034281600a10b8038a04824400c0c103680c0407816902c0b0302c0c0d8840d401946d109001401907030b0204200b511002540099a080e240c1d2464038010400040d56149004098095840102d0501d40900410511284a03003903025141075030560040502500307207411406150328084002009000f0079009522a1341030150001081503074001200c050420340c0d060100811200b800800340040c203194503c40c03000d40000c600d44014007540141a04031098420340a4600108400380a00d220184140d60a803036100d0180e8840008945400742802160045030078003606001040070840c4000042e201c0c9800c0c140058003500014020140d150700ba0303040d0038041804103040b05014020100700702850300303040d810418840b0000c1c0160207010686516140d031221313084003694a10101780c000c10b8000c0c003070f80c25 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 650102500 1250 650101250 650101273
    0x1203020708100b0102100203040203070518070e100518031c0e0316060c080a0302040b04080c03010e060105150d0212131109070804080c0703060f020c060105120a170c 73
    0x12909428071600003140210400700c407450825005141e0000c00582c090804040186441802500701030800d9070580300d80d01020420f51555001c2d500c14481c1054511810320702500001c16041001040c14080d882034044c500ea41038100c000c1d01c03e80545076110281c10ba0011011a240503188400c1200142d0030b915000c8007203030081042124440103400755180f401c002004125800614070070000091400700c204d0010500c0d0707001919849002c1d2070058a01a03959070403584580207034118001c2500038160000d098a8248a001075016a19019200300d61502000501d03800308500e504900820008140b80d0400159045588400c030700010410a42007485030440c101d5000e4000700c9214000315042141d51422102d2107110b116130740e139850400e40e0307540d85110ba550030503440700e01e4511420001100140c043d002e8503519900040c001a00c4041498200c2d107070001c180d0009000750b1520440000802d03000c90303036141c2e041e000b140720350b208085400d40e60114804c88001080a0040c16103612 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 650103750 1250 650102500 650102503
    0x403140307050c0114011a0d020403060f020c010b04050c09060f0d05091c09290c010f0b040b0d0807020f0a1d1e070f0e0d0203100207171c090c120302 66
    0x904100f0100007000206030010905010403428000c00d4000c5280c40f005031182c009100c010071640094100c054102a07403503a592041d21400300210501d25000308101040200c248204230848800301c90074810f070b0420704440c140501c40d0a039058041c840004001100c1903880041303808002400c032017008545800590b0a45510304003501c049c4807082c8961481c600751184034008142d61003424083c06910107041d014030000744006c001202c03090309110284c4a9030b42846110084c4211107000b05603900e0740001c100c121160321800503c2010611a40b80c0403030400f90030ba600c0194107680b03a6111050000006109210b61340c00301c6000c02030103040c241e0146c1e035440e046009040300e000b500d0055a2008050b0713a440022a103480c001070300b041803d84274078840c6503800c0c6008009880c20206100d02d4020900708003241c140b40a1150f000500b080800404009420446070405da0a50500195080c142d680424900c00d00303e007d919801c0c0c040030b000d8100290401408030840c002086035241c98040d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 650105000 1250 650103750 650103757
    0xf0302031308131703270a12110306070203040e010519030b090120072a0f0e10090b0901120203100608011a0a0b1204050309030102130e0109020406090e040314030705 73
    0x4600308848442860b0100000005890281241000030703070061b06c010700d1400e4120904216558441c4011000184140350030010039411030241115051002217003090502c0c0080c0502200c04541c01008208005030110b504c071815604c0031a204805035402d0b82c5c001c60380300000e800103041000030304140441c9240550005003c03070050350100603100c014000001c258000c50704050b203540151180c1090408120b680711803c50040304036504c5854413900b048180303074165042a2101a001030900000d80c03540d2410500900d0010014440e02030444042108103406109804402181c5060a0219501440403c820a0482600300b20319562402c0c12806043c0658014039000416924194941407400c6081c06840155403207a1031305000c81031011038a14000c0c8295038a010900c09000c260b40d0a000400e1420b03c010031510243d401c01d004640000c20691144c1511481004200700041e0800c06030811201b0b03a511010855540b828161090041d1030320b94901d1a030000104030019400c40e019 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 650106250 1250 650105000 650105009
    0x90a170304120e090103030302070f0b070f020609010203070504180209031609241809120e130209010f030911090c0c0106170a020607050f0304090f0b0301020304030f030203130813 79
    0x701c40160803648003c0d19800d1001c0030080d0012a030800600119004e90020074005100d0107014403240d110707440d083c244040a42e580000550070301b00e40035585504003c0b054100900754001c61650511950151180c45180f142c01a090f4045120b841d04c0701e56913041da40000000380c1601d132414403280d103a4050000320f008130102949000d151100c003051100a03502c0866084012a0b00c0c541044080d100e540c0c9000410329001e92552070440005461102156641c0c0003516a80380000300312003042100ca01048810001034070501c01003a480e82c0c8820220140c1d0054100014001e00d58100007010a000406003038001c100601400006a124001031010914042c020489503480e0b416019004c00c00740c2c560303142907000f4421341c409841c1810051140d144180c044840c1422030f84001400d60300700342e200134089a40c1d102078046e103102601540c10307582c500303d000318610b20705035401408002d180340319482015400b100103590880300d04540103202e6003140b00581c444081205004102d43e00b4000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 650107500 1250 650106250 650106263
    0x8040b0f09011218021905041e05070813021c0605070e04182307150c1a090a120207080106081b030604030c26161406100608090a170304 60
    0x41c489001c880510030f1113a003214800b030b02401443c0300c0e003c00111952488100c2043c0e6414540010a584c4910402d19842250b40c0d89480c003101e185030060803030364010444824450310100300320b0010031604e080085281d044405103038000c5190340301c1c21803c01c2100b00918451425091110b0285c000c3c6030381c010501d04440a102043c1441e0190340317190302c49a4018400000c5000d03c44510351201d02c10440b0701c52004c200c2e4003a47c0d40d400c08120f10307010049017a001c14030440f4020203016045214010300d400c2039a0f481090b003800103445a8404602c400035005030070545070041c0461084c840c40c0000d01d64080217002c541e0300c91100d1a12541000e400c011241b00b100311036071240c2000302e6410f1145403d0f8591360410b12076911451200c5422022001000262a410f662100c1001000c0c10400050b203120340750141880c900682030300100c40070f1100300d501490800803824048a050000e80d8002d183c216403075294481800c0c500703099010300411001c403001541400040900c05544624062138 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 650108750 1250 650107500 650107517
    0x1b0c03120f0a030504060902030a0312110a050702060325022b0503010303050c01060905010f031101030e06070f0c0f0305030f10121415010305010618050c030f0408040b0f0901 77
    0x39100200c61040a0000c0c40100042c480304140d603002e40d001540c0070703011300c501207410052540080e01300000e8034002c030040313040b41d208a07003100d62510030b80304500d484142c0b01c2d2421503459005444c03409000d80c0288281c50000000740135521142c2e03848074261881e6001822019500800780d1540d05100355889615106260400009c40d02c1505420924254032070707a103182d0858800301c4a65111141080c075664907080001007404607449400e0081407044000700c425801c1d8900003208817028510541010305150260594003004900242c1200c041d082084031b11030102801d544481746240007812040d03080091105154100c40254802c00d408590b49075076a40f91001c400301810140503000d03082c45070540e440e00180e601c3c0314820030850714504882d128071884a0b9106e40d01400d0b007040742c1c60f035101c0e001001500040c9580c401103140b2203a081c4503a16100303540145030300000304079080554500010a09011460084038050f001c44030000340e4910307816071910240d91020f0141c0e4000f0b003141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 650110000 1250 650108750 650108773
    0x161703040e0609040201140f0d0e0c030d051b2401050a08030307030c09170a050c030a0201140703032901020d212c0a0c0b04050a09050a021b0c03 64
    0x401220306444600d41c400c8082d450320000c2c0515a080188120705000c2c0c140c040d600000039030005490220410004180d554064094420590300620703e403254503404102c3c2d01203503550100c0c0d010304108442c07400c152189007a1407480c02440c05000603848034094010070b1b40410324800c142103050032a107014200240daa0f0340031302181c8401485490803581090001c1f5030318a100e41c101c69049403507850020309598407100d81d00802400303807007e2102d80e40140140d0b410820240a007006644044015100810309034002900c95800d002202d024010002903004c2003500a030300010a03008814103d00325004c81c840d40b032600c001d000c140300d4007511482200c00c051301d1080c907042d0000340140780710040040703501d4401006005040c4621400060864448400000b00303600d0500d4195590000d180240d050f042102c0040d07065007284108560401c001e010070380340c0740303551001c03540c3c1103100240310b95aa40c0c8c1c6c40c0082c000e40c094080072403080034803240e0f0318000180c007154002c01107081d41c40e5040c50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 650111250 1250 650110000 650110003
    0x606030522080417011d06091006060e2101020a2a020f0f040605030f16080a0309150c06060b04031a0712090c0803030c041809050304050d0609051617 66
    0x201540204900703400c003c20320104010034034400c5601840390012400f0340520080c0198500070f4951900c0325440300c6c0810a070b40c002044103e5100b14660300406c441c40c2028001040d004a146101780107090600d5400f40c103a1952900688180a11008648602c41ca540050102c555040e0349a0900c000300c6c03919061200000c8000c080e2a0700400c000709080425081c49420409034003920361241c0d4502d000505901c00b44641d0311040c1002e005041a242110401174062070b00d600704907807550001201c540025000216201030300e12a161031000c100024204441c4d4002c0c449005040c14106003001500005d110302030000c2e41d201d404003121070b12815491048010007151020009170b80b1041d00040705030103500c00a0100e014034000340810341c440801d5851680b040e074074840c5400000600f008031410305a4108000c1c492044188402400e03a00d4056403402903006d054032034140c03ca0f81c002045480c1c1d020004041d40142555509684038482c661108528071440c07800090407000070034a40750 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 650112500 1250 650111250 650111311
    0x80c01021c0c030309061808130e040f0f080c03040603020406140a080105040e2107020906030316080d060312081501090509150d0c080a052a010c020a050406060305 72
    0x14140c2d9001c0142d291a242103020b060760050a0303e4450f030701c10500366028504aa98860180141011603032403049141000343c00c4208e502032118480c0c1340c0e085c080083c09218028019030b403ca8440020414103060040c114801c0589003000341c80005000110550150090f008480440d1034454244c43c0b181d4500c5101d10490181c280000d081a005003c40e1030281e1210303070b0307100842081701e0070569005a550902440000b0607040168086010b0741140b804480e100e500040c141c014500700403a00886800c0c0360b040100042000d400030600b522100c3c0c06901032002903400100a4000d141004c0c005003414205030384400a0417000c0d400724403194050203520381111400b41c00c4018a98400d0614140c0075284540240e016581c800c0030000f0440c9401c0850141c58004042c10381564245132036450b04000700200088068820300480b04241040760070342544e41c00382007050742080d5510010b0720810044c0c01072503001e0302d41000424450741c50340c8200d102d80c100c28840c189044100b42c6081d0181c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 650113750 1250 650112500 650112553
    0xc0a0c060f030519200f1e16120215040b041b08030403020402180405041a06010806061218030a120f0b060a2001020415020c01030605030c0f0102030c0106080c0102 72
    0x1c0c140d074444803000034540c400c945294108201c10010392050b0034121050784036070640721b0258404518070743e2034900082500360742c8200071384032403030984806040b907a80484032001404003404401889100c6000b40080100c5a0800309506003a150030f10300120040c000b80d038103640c141c5c0c10041070a6103400c20f644800654103400c004500702031030b5900300006540f0180c1d550104061480d0040c8440e1101e0140d03e003d00e1182e4550500c20740310200c3c10641d00030080a144c100002001803240f40c0e200c9008440045504500c80d08869840303401031485424510074084d054440012000c4100e42d201c0280300d500091040107000c000c40032034a907000d680004054039400303001000b40300c010078081d102000e92104100001c015107a000400c00c0e0882e003083e8040910080c2e05d00c01035a1071a0706004814440200b420b08001803820301c004240e0790501d40101a0141c9071500c0e07000a168003c000341c8482c03d4000700240030258840d4149511294443e800501520546500044000039050035100c3e06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 650115000 1250 650113750 650113771
    0xc03041511150103021f0e040204120b0f060a0905060f12030a09080c03062208160204060506030f010509060d140714010908120d1b0207171914030c0a0c060f0305 71
    0xc0120014101d48905540c81c00402d01c04042c400310304a032541d001070402002586003003081e55040c0d09014a00cc1001020011a02d00c05d81c108401c956491041c0000e80304107450004296446102052240401501807603200e911030411403000c1c14000001d00500289944080c002a135640e005a44c44040c01c1809502d5045800000c110a00007020f01b1000c0119484a0203890352984a8200b00c1d88115420441310300b040740b15400794141401102c8c010841039030640e18524000504241420041c01350500c01e0318035a02245907695122200c4401980003440c01c62008501c500155480c0010304c20702c0240c42c03a60900200e95802500d40c04101c40c1c01c480501180d415808403161240d00c4841152011640c030030003001d1114081e02c2e05800301e201c0c0c3d0010150b4500703144000c420b0502c404050149a07000b50030048940398400840072400b90301400100c50380e180c22614031f0031406402002251752240910000901c0450200b000840d040382d11958181c40c12008110103607481165000c841 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 650116250 1250 650115000 650115019
    0x803130810020c0c06030a150306020406020c060a0210240f0302180c0d050907030f05100b040e0a08071119060f022103060312130801150e0103080c0304151115010302 73
    0x2608144004540c01f20070b030000002ca5224910807030380252031603002134440da540030605002c02501040f5900005030121401400c041041300000c1d50341c44021812002c203904e400d001e00c2c00b0401416a402850900030242c000c03142c44124100b00c0f02c980d4803080c0e2080c40e00e503189050500e0500c074031901a80c0003001d020703e800d9000c80740310040c25010b04011224131038201e000000c41c0030181e40c00c0c140303440b40002d420030500c032494800a4951907104584075901d00301429001d0440010640e02d9158410700417515249a82007402a4550345820240c04c404c0846002c003a01200d01e034008103403102e50301d030410906010b01e0200c2e82d403c03400711601d20140c00e2903801c140c0310340c855028560181c8002c0c00c544e0071100f264502c1007030f42c01c20400d103102c11000c0c0e00d0034400c484083c00307034200841042540b40501c528040d02c0480300d03001840013401d82c000c006110006000280103c4020b41603059000b03240c181c0168008091345503410347c80f0050b0241d44950140c0e101c00040903030480350010107400b131 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 650117500 1250 650116250 650116273
    0x90c14160204020d0f0515030706030f0204180c080a050412080402120d0e27011502030408031611041401060f05040e0f07170721060803130810020c 65
    0x40660060240e1810020000c0484005035030700c0c0003d010044090300c021584030942880c900c107948001c1c1010441e410020480c0e48251400281a01111503918020070310750040d14108000744141e1300321205c00031401c030002203040d407981c1282c001128999100305a950300c203076904c0100e41d01590300400c121180019407641501ca6030a40d500940001c04c20442000e11402003840c2020204c01c040100c2c05141d01c00b030070341c64070409500040d0800701251341d103480f100c109800300d0032050080100c0c4103000c480d9446e01520030019074015010240880c0d030345034000001c031404104090421030f51102c200075a10514100703802852114000002c4144ca242d00380384050329540300d0080040f04000c001d110028444201407c01c5015294078401520b29080131039000701001003040111901c4405c4000b8490580d42c0648a0012200703110568160110006000c9001d0300c1e203030f40014481d1101240f5183c8840c05040300508999150b42119400702c03134076000000ba80a0748425400700e403c044045070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 650118750 1250 650117500 650117537
    0x150c0309060e1804121d010207030204090f1a01152a141b03010f0213060f03060b0a020609010606081b090f101101060609030c060309061b05070201030501090c 70
    0x5007500700c020000d030f1809807800c0510b156081c0c215415510b905950041e040c0c0f140c0c00001141c1d034101813903d1100d6540402d00080e50b20710f85840000d0149648513882020302c07000f41400c454503a8042d60359160000c54182180c50300100b80506000c42d101411000304031409160f546c140d81500800e400c00b4910034503d001d5444044020948a600c82c40e031061082c3d450500c200c490050840200c400310450140c145800c41d01c0586441913400c1c41000407101000b0500c1c80101150221701c0d142d000860f104600f1400340981d50700110032402c01089108038160089000d6114061144c0200700da03541c0c0d04022140c8050584d81d02c20200d284e881a00054480b5000408518401070403409a01e02c8910129888862211400e170001d03a914a000e05100303004e00410004044900e4201c113218210340398644c0061540c410003041c1943c0d14149000c01a464000701100c1e40d4000521010480510340500690b215000c102d00085c0303420004503404100d4032407a00486055516030040c42078041030781 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 650120000 1250 650118750 650118767
    0xd050304020a0306053c0a020f1207030b030d030b27150f0315071106010303140705160303230c03030117070909060605040b01020d0c15140907150c030906 68
    0x1c00000c2945641c07000210b03841c40c080300c000080c02e40500081c0300e442c008100114801f404200009004000d024042e007604025112503d009074250142c503140c1c50010f40080c0b4580342c00303a03014001c05042c0c0d15140d41543c0305040142060710002d4a912018140d8504602a45c90300c9034107074242008070768000c02c040c200806114001d00b00d4400303450340000203450505100e40203928606a00104006958840d0002000c00410001000c1d0355040d135134043c000c494000c8410b070421002040724418030804001d04620070400d540c0345203009860307080007070000f924041d2040212030034a0f11240030360b02c08000c84040610900240d07003076900b0009030120703107106618850b9080c4114040802c208140d03218507030407076200b9400010040c1c544000e00046d1180c1c0c034400c6040d500b10560f010070761600082e03904031a65004d15002c0c0030240e030400c0b80000b000b442c0c1c40005200c034a0f0301004443c0c1400980001131380c800c040313040f520106400c0103d81c50103800c00e0003070004460740d0301089243c1c0960b081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 650121250 1250 650120000 650120011
    0x5070f110304120c050307150f0507030504030602120703150f141210020c0d050903030315040204080d050c010f15150e100f0e01020705010c0f021c140d050304020a030605 75
    0x1d89242c6543c43c40f40003407100e0742e10410340f010380c00b0700d400f0429440d080101100501e4902c0100070600c3c007024020384840c4800301c0310403c6c0a000550042054400c00c1101c01031a8440011904d8401c40c101100700300808451002c0460714108910184202060300e83e0120f42400118618941c20100b00210100c0fa510001c1d40225030840e241344480c109000303400251106140c016159010021040c3c90302442c00919002d1240401200001c2e0320040110f82d403088030508408482109600818000d10556112044074000c26008064543e03201000f481c0303500c020002400080d04045034081201d4202c0a849944484450304200d08030000100c040c0e002410304106d000c1400e41804240300410030f1549000242d03481e10640310668000300703004074051083c402802c82c00e003400c001804a4240001c054800c1c40c1e50041e600456859000000000d51000000103400c6031521b0308814490b00148540300502465890202d0345100f10300b81c0344910b40080200d29880d1540d107498004240107000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 650122500 1250 650121250 650121253
    0xf091218040606080712020a080105240a03092108041203140c03010e16020c190b0a0806031905120903150106050a020c01030b03033a091505070f11 65
    0xd80390305948a00c200c00090003a512403100c1d61500391401055201c41e00c41d0540f400c0d00c1030000850196021321a141999016281c10624030201400188481010782004800d0840040c0f10340185c1d80c503400441d130003842041f464260380d8182c40701007002840c0d81054000200d50000090101c3d4000005606411050030000f800d00035043d0305c404a01000c61f00c2c004c24020003c010000c0c0d404030240c65521425186880201034503d00c402501c840d00300402510820b0910104605a8030090800001b8282202c0c0b031030380c1d40680000504065421242c0501c02d00a113007182008140184820b102c0c01d5008001d400202500e01d0070034419003090000a4040c4240404081c0d40031321500750340c0c0a41840d07110551100f110000007450101034206403810507051170090551600c00009490041d240781c20030b4800b03240000040782d40510355a01d804c0702c40e483c600c44000c02010a921005503107011300c240010100e030002c842c2d402d6541c1901c0c40d0001030003030120341d81510700c81c405034500b0303041810 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 650123750 1250 650122500 650122537
    0xf06071404031a060f0f0306010608060604080102120106030b09041a150d030201240e0f09010216060b03010605040506010e0f12100e0f12040b160f0506040303050f0912 74
    0x2c030703030381c3c103241151116540c000410b006000183ca408440c0070880310045816841404d0f0b00c0021a48540040c49003009202009012400d607540e01d138251405011050001c41d00c071070f40d071100c424a0300c40a10910001c07034a407103a444103038140001c0c014030558210350a070840940262041640700c0d80245180e446c4c603404101844103542e00141490b00d240030350300111b010300100101001c0e0070005c2094a912060381d0038100000c402283c2c510b1340c0070f038603003034203510701d54507100143d01a10038038212007100460340395184100700e4103605c0b102d400c0000360b000300540f0781c80300c0501003115010b60b40b590100341280110110307880d0070b4060001c03108001e09800c070400281e001180c9459000f401102881d512100c8400340030070204117491100307260000400307035181c0c0c0c41188101445140a5402e440c500020540c542c0080740207040542c03a44110150520905414010b4498900355022400a802e050100c0d800400240400707000308941c5000c1d1040f600c5401942c0400d50203c0391012001500c035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 650125000 1250 650123750 650123753
    0x250305070b0135121303061e0c020c010e060c0a02090c22030b24100c0302060f09030a030b03010605041803020f0f07150c020405070e0109080f0607140403 68
    0x1141958001d1041c02042400d0180f05080d400074803804004440590403403000700040c0c610005012140c82d107041c1c031180d5543c0d11042c4881030000240e00003070110750618240100c804050320054020040600d001c00280c8600d42d0101d84070400412901d0000e106140384001e9440d0604c010b01401d5020030403142c0312610381d40400d0b10306030121010380704c60b0008075000c180c110141740c100000d9082000e82285c0141940c2d540070484101074400c0c5003080f400c0d9030100000e829400c032101380340c42c000d081036005104040300402440301c81804600502501011800d02c0001c3c0000902a82c9038002540c2000c14042d000c6009100d003483d802d51541d00d803240002c043d00c4900c100d41c1c91181c031844282c0030000340e0a0103443d0100241d80043c503580101030182071082c0120b20082550001442c00000024000007154a03141688000e5840f51511051041d43d64001d82c0700c0c2c0c001e00c02170702e52503001a030701c2c02c4031038559480300c0a000c0650401c0c400101c8085c0700c0d80c0700c00c02a401e0b000015050907200d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 650126250 1250 650125000 650125013
    0x30c150f141c1a180f01031b090204030b0610020f06010e0a060b0d0c0e01021603020f151c06051c061d150703050c0702030a0212011e09150225030507 66
    0x840044900c07211085020050825034180d07805400701404504d41818055032076000000d05210242400103008010541068130540c4003000f8a0916000d544998503410070540c454000d60b0b0301442062042c10002c42d50380007240300b0b0101c0a4840260003240e1030104035a4003000700402c00307040541da401c2e0104c1c0e400019805492147e03511240018112200140604030064200110f4190743c840c6148075003aa001c112010107896054072031303040508507500031506000c00b0700c042004240000c600800c1c00034900702c10300c011140c4003100b4407903507940308180001e00d40060030750302ca800f07442e02c1d54401144064100a459007082031f407030700c91040b0048509090000c030125150700c0b941c00c801031294840c1c1c10300605130040c00f04803185d8500000f55000968a4601800007800344120040500800100f94000000d0b15810071041e480317a4900f0300610018503202008881d08000749805d04d000e4895071007650104640310400786d003030908952114545249050085003080810090303013000402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 650127500 1250 650126250 650126261
    0x1120812070320090f180a2f071a060303030a020d140a090b0c0f07020f0d0c0f03050115060f0f090504020409062402070e09030f07060204091802060a030c05040807030c150f141c 78
    0x45d400030f88d03611054030381f52003c1404820b600880c07011481c1010b026031a90048100d2ba00644049401a42c0d401c800d01803101501ca00c0b540b85140c0500301d01080303654640c0c4c2e000310484a00c0390807031680554070005000128011001c1c5000012010300500b0f0050402c104a864000c0004140c0c1481d643c181d581c04e00301c5d00d141e8000c4c00501401100c02c00c1005001d00500e0000401e480d0448201800c200000300341c0e12118214004008011034075051490007a50498050400988155501d0303856400c50005404244940346140c0e520341020681d50002d08a10800c0c106141c1c0503007489460480620a40140589181030902080280c01e003000008401040395601c65403016844038941a20f242c00c0342c0072071660381450f8013106400c60050303503103904603100d06400d4140002d0795082d280c0225258000c03500001c80c40d21921758048140a0600034040403100035075050241800364030700440d950302c840c6e1601c00114000c19000c1d02c0380c103220400782c030424940c8107080c0e07002e61052050b0401c3e141c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 650128750 1250 650127500 650127581
    0x702100c090b1c020f0a1209110d11031b0a0509040803010911041509060e01080403020d05030a090501150f170a030f0c0203030a1701120812070320090f180a 69
    0xc0006c10b9007803550001410200c140000764100143c9895488080f107224140720081c0c401c49004122408003c4c9904c04000288009002c44180865034040c0c0c0d55809031200ca081c0c070030b4000c043c00142501d44a80d00c18451544409445c2c11079282c0340c0300c10b0103082c1d074042c0c4100e0700c80c4c140310100d1080c025800340400c910041d543c03444040d06d040e0300501400d118000103810404880200004660001100c4003e60746600c1e04980c2c0e687c80c0c0c00d20400034002004010b10f55401e200800c00c1c030170441542902650082110b04102079518204000c50034610304180380380750043c82124011a000d1043c02181441030705007400889101c0d800a419688180c094001003880c16080c40c03410510b151440780540a808550031350302580307844a088a00502800c0016802c0300390001d02c00c1da110340c12007601800c5000e081001c0310081d2050440b690480d5500e40d014400c5216070b48450704c0c1100c640c0c4841c1480340c40241440d129020305002421540c03103220101c11003408500c0110b20703022044c40181 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 650130000 1250 650128750 650128777
    0x604031205030a0513030e0f010e03070605120a050103020a030303020c0102091c05010f0b01121e0504030522050d030c031404060207140607121b06050f0702100c090b1c02 75
    0x81c60300303d250004450001e004101445e0002202c1d00001e1341103071181c55804022513454108119040040b601e100c1030382e84803505401040030004a0940280180a504200c3d084030f007010350b102a05881201c80920010794807045480c0200301083c080da00501c40d0549400015240c0390400003c5000115000521703012481041050818802c080c801c1c010f18400c60350301401b10903000d0300001d040101d504904440070f40d446001e10504000301c21100121500c03110f0a00c840d180509001d07010f5040048103605040f0420ba0150420f058400c1d07200030b541c00203107240403480b516102190080c41141c400c84c240100072130b484003500b100c0b1000d00002d00c900e0340200907060412000c0e03003444000307034200b80c054441400184c002495201000c81581e8841c0b50a08041854040c0e110803802041e0002e0003442c40c0c1802d0100306e84080c848984a00030039021504460341804c03400e0b0403955500c80c148000380c41d004007444545000d00c01488003824400e0744d4048015400220740490740300b0315981d500c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 650131250 1250 650130000 650130007
    0x30403090617010f1a070203060c1e030105060a3506040b010e06030a0b030a0c06032a0f030510080f031305090f0606030a0f0509060601030f27020604031205 69
    0x455102c00344001851042000800e07551610400c0100ba0001d4000c00c010700403148241501001081c0079590400c2e0000c040707078001d06040500240d554080b080c1620401c04c003005841b0001c51080c03c490480b28050300c070034039005040744210341083c03a030140040051007080301071003151201e2001840385842c14070580b00c9820300900f0401103a80c5d000705241440403028400c5155501e50040c0d990103048404045203d4400c0c5001a040c0401208002c1c001c1c907403c00c010610b19455071218402185484002000042400d1040c1008503400074200000d004502e030740040030f01c2900080c3d080b000300010a040035440340401402c000d02c000701000d5550011800030810600e40c071520004200650b004541800c05521103684460000c2042e070003040004040b950b041c6440d88842c0742020b46a40401c843c0c113281c0f01a980303c18048c0da209000a003000342d150403101c2148520003200110300d03007000b003030100519020032801d5079640681c0e11100a01001001c103c00c0c554540c50b85c1c100c3e907220340c0e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 650132500 1250 650131250 650131259
    0x3070e0d030807030609060317070c03020d0b0603060a0504020d061109040207051c05090603160c020406080309191401081f08100e06062d040204061706030d08042603040309 76
    0x4441c5c00d80d019041d5035003080002c201180c98082468404e5a21584e00f540e034003205d00706829050040c1d40000d40000088500030140410000603a004410072420f840b400e4032909085400d444042d90041d5010302e00e010034000203019640822115000907404074140440e000c00a070882e041240142d034070b03400103c54500402e9041500381c100c0003081c1803031401d0040c0d000220f5480d002c010314100e500c4200150011640b40110b10142c3c0a950050003030000540303428030b060712a080245081d000d690103440320b481c0c0500310410181030f908207801d42d143e540c061400448444101900b02d0110841e002c003400000c035848844000584140401000890450044070044546000a030640c9411903410302c2082d41d511400710680e0003009103218210b40000603101d50801c80302c000194801c0c03001400046003a007003620035849050241d14100c00f45e5401c0c081c5a11140030043c00d20004103098001400504610040031485d00c110001c125010011001550998402c0d0b03410740120b102d82c02d0412 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 650133750 1250 650132500 650132507
    0x1f0504050a120309150e0a0b0a0810032d050d020f100c0e010528080a0608010209030a03050a0c05060114090108011404080f090d080d06060903080f03070e0d030807 72
    0x401030400180b04030314019030b81c800400006003070050780c4000e80490707000c02401e41700d08200105804010710417003210f50b0380d821b44d0610b03034044003050000c2094400080d0215003c54020400c5030341211038030315002d010071405005a603001404203240301c01c0d26040f102203442005200040c500039001086007210b0070301d840b450004044103510105050850b89205650300142d0442c01c41305c02e007001600c1301c944010200c050880110741a2144100b014446142a406008039001e404c803c2400c001440d00c55203003d0a0b4441d01d40351a4143d8015102240000e2150004013040b0400c0d1504161010490761f4080c02c1c0042a0b10000c4925000d00b40410306181c12003840c2d0040c81d8140c001c00041c102e80f0703401d0102820052024000c3c040c04240703651514985012900e02c010010200501a03400f4030f8080f0f0b10350032240d1028a00361070f0000c04100c41d809206100c0560703410001c828240b2041c1c59800c5000d07440100003004210100d00f00186645a822403c1070355446500c030a071503807134041c038000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 650135000 1250 650133750 650133769
    0x30f1201032a05091909050c0111010905060f0411060a0302040e0609010501021f0e030412060f0b0102060c0d0f0207030e0321041205031318060e0403080609061f050405 74
    0xd0160110b940c00110840c40b10310700c20403503400740c4038001e0568490074000301a000c18040d075403080342844400410000003087e0704c1128103003601c4400c103032032000700010700303c400e081d000502550100001c55600c07842200e440303a00600c10001c01d055242160301243c080d420442418010a40200d014030184004241c1c2c2c590102040d64182055850000000e6580c0392001b0074449030010b80c480440002000e0b000300307601522250480769140d80e00c3c17905040c50304246200741c071440d240a0248203501d241d809101c0254205a00070b180c1611503025036602a405903a4940d000307542c5070380c010b681ca0a5400680b080c00c0c000c0d220300b46112482018503050441ca0007010603410107841101601c0f03801901503809645448040d11030340e10389850320600e14410814400074070301c3c904000080d09202085107900c075080081e0280b241c0d568980800400380010703940200861004800108141404a1b407954480390052600d03240d1030720f003000c01004581e15907240c000201e002034148000e08120101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 650136250 1250 650135000 650135033
    0x1a030f07080c0d08030103020f040f0204141203400b0a120519020d0b09010329060a09110706060b04210f08030405070315020d0c020a050d11030f120103 67
    0x8142840d42540c4d42241611050000a10842d03000d9000030321a200e9610480720596480d07411983c40d602c5440d00030b284072085007400d01c1162500c0642001540c04001e941c0c09100c0d901c1000d4045404020310412103244e40c48155030901a0b0002c2c44660b080310740c0140040003002410350752050184401441130382d81c02c140011071405e002c2445285181c4c44120030250310b02c02c2006031580000907981000c1c12040c03141e25440030340c12002005010100100400c2c4c008180340c04c2d0f2000340b040e0040100706000315101940040c018108210300703076803a082000f622100f10b007694034055941d5516403c440803504962140d000106040c003022145124142019440c1081c428a600391036540c2c0381d02000d2188018159280440130404000d01000600061075000303050b400850411003c420003900320002911425081070803c007030360f03030002c1500312031150050050500100010010fa4882c030b4015589890b80c80104002c500f4490700a000e405010f41040c1030b060f595145040c40404415036244 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 650137500 1250 650136250 650136259
    0xc03120f0c090b07200d06020d02040e101a0a030f0f0501060f110a060b0d0b13030210061401080907170c040606020304051e0a090504050a031806121a030f07080c 71
    0x18801042019098058420f40c01d0f1307964030b1417141e0304040f89000c520140000c001c00c2c00840c1c0301514a0180c1c01a100350342030305003203176001d1f500c508076648510218030131404004980740e0380700b16801681000f045001b0450601003800d5800c003106c1c00840d641070301400715099598005001c166800800401c90846911342855481c920711a030304c0d01e0390242c4500800150740d0f105119040e0b10745074600050350340c10404036081803600189100c41c2c0c40d401e1000701c0c014020150401b00c640c02910800040d03c030000c013031900083c00c54005561029029010144500c80d1000000c0c0d1001400300f94100c81c05044040d028401d12a0140310036500550000c06c01d43d0020701042c4040e80341c550443d800507103c042c5641d11310206030045a0b5a80c04c0780c202200c110f04000402050020001c1c0b2026064444d0b5110100310000350440d24000c06c09002d150002070101c0314580c0c1429050704802400c003c5041905500891400080d245c49450102555036401c0304208001c00d070030034001071740701c1d40b029507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 650138750 1250 650137500 650137507
    0x618040b1f140c1e0f150124080103020d032304030213050903030415140403170a060501081f08060103030c030801060f05090d08130b090a050303190c03120f0c090b 72
    0x3209500e410190b05a203a400300326640103284c0c05420450158140c02c0c840c2640c2182d440101804454107003402000128924101043c04410307449021089910540c1ea035404c0c2c903400c5508100c104006482c040e401c0107040c90307100c994450247c1d00d01305480510380c2c00580c6c0300d1452050101e190410030840042c03914100800c41d800300301200320b961056001d80c0144102180002c600c0c010b21041055031001e0726200100420135410031442d1800e01c01548045001f6070301c21840106944a0780541c0b80094200000302d15212059003c2644c08070681d070303109041c0c50b26109040d1500500f40d1060300002c1007025210180f6405c200400d025010350f2401d40c101d0101c0c044060214800e281219008040c00300341402400117540945000f54081c110b0740503aa0380d21022101ca54003c00c0700d1038440e40d04900006000d140c000119401c040d0329199940c59451000c01c01c1d2199014168103600b030021007140c1d02d800440500c00ca1581c0c0014401c00140e50308070200007071a061039608074080714007042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 650140000 1250 650138750 650138767
    0x213230108160f050f0a022a1318080d140108060114100306090e0c01020d0323130f0609110a06020303180709020a0206190504020618040b1f14 63
    0x2e00e02044184040d0404443c1200118000c542510600415010b4071201054218505a000c1000801c0030700a1120807581808000a8014501c80718503c0d03500031a6410196201d00e01a0802c4084405401030828190f0894482c1034095019111960042c0d56801840128005d00c80c3d0b81c43c0545400f0004054560525404515110b400f4400714407511050455401040c03094006401910705082c00b0710210399180f5019640c1d00e41c14031618054041d0f90f80e1244168404c1c401c8a409402180500d1020503011454480c030180181482518016400041010034408440d1030701940c0b19410000d040c4603241000421481d0301002d55101d110b1100040100307650000541c0e42109a582200340b002e040340241902e8a60385900905271140040780a10750140c001c94401e100c1d8104900c80070960208415030303030803118101e0b00254003e02c1441001d80684240398485138051000c0c000045a100c0d450026001464210803940d440c40c03552903a07100207500a0041090900c4a0001c0d418800a07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 650141250 1250 650140000 650140021
    0x50702190b0d0e011b020607080c031605071e0f1401050f0604020a0e030708031b0109050325060906090203010b01080c090d0f0c03050601150e13050a0213230108 71
    0x310b01c95280002d888203241181c0701002c0d40011208003041403849900ea0004e64041e40f00c807401c48024000c901b0140014a400f4202801c0780c2c41400c0310b0521413020404070400341c80a401080303080d103907404c80c220b0034032030501042810040d990050030840d90704005071510400e0a4003c00c01c0611590502092002580c2152807494020360111409605e62107511412202f03100c800f61543e5042c850f241e400038100d0070110080c44001c0f4441240030400c4051902c0740c3c01c4e43c80ca031800803d035034802c010340e40c003900e10010141d02040e580c5d04015203020344d5071a140d0a541d01c001003034828603565191402140380134441c0c60301d454800e0804a015103001c1d00c040b41140500250380c6d000d020a86500d90800100c0002c0e0ba4645512900d6107403980d460b403d00c1661024240200680e046090308500301d0a4003031042c4400e06007005000e0400c9a0801390321001920000d40320100d07544d001d00824881c0e0401e041da400251040098031481040400100e4042060111106050200c80014004039145 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 650142500 1250 650141250 650141257
    0x1b0405061206040207060f020310050102011808070302071701022701080f070909050408041e03050307110d0221060a1e0e03120a061a27010207050a0303050702190b 72
    0x10418481d15280c0d5912001c01c010307103e8000000c1c806407600949001e03400d0184c2c0654000c0782c020310199445a110390069007207074080302825101505a0300e6040029848500902c40f86100e84140d804082e500c61000b00c03c12850400500c4a07500840c45007510300710303903481001200450030080301c8a01000d0020345981d80180052b8003034910403000854a6000f2100f100c010a03800c2e0081000e49400e040c40c1286401c14005c4e020000050990025800c02c0c1c0740189d0141c94014019602c0d00a2596803106c050500e4414160071210300080d040250b621200442d00c1745104440c4441940f0114000c1424501d00412000b4503520f809100c0203040c4541a03820582c1c0c0a62000040d9540c2c055400c0385580aa0034801840d038091004222000781c050700f04004460b00b440090348401c48090b0303100c0359400b03162603135865003a4006202041c4c070341d1700480040304036060040d90754035900c070300204a000e851500180c001ca81c0000e00d100460078000c24010310607505003031161070346080c002c9060040c031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 650143750 1250 650142500 650142517
    0x5030402013504110307030b18011b02030309150c0a050d092312070f0b10181a030c0619050c0a031e0f08071107080f061b040506 57
    0x104000200c08100541c0032441202107041c0c0a040c0c00942100c880d2604040444013161013951003012444a4100000d1040917aa4400d440210f5036807099038042001149107500b032810340d243c06416a0501c1c0d0200c001c0a402e001c2d5010703581c0c9250200d001d61401301d490400100010598041007400d040b02c0d410b032618443e030307440c02a40c0c030940c1c150303003001801943d40003070030340001d041000820713040c0c0c0c0c03280c403012490b41410344020f11140f84491b50a4007607204081c00d02d411980452000806c81c501c45a44030101c0c8515400441d140c6910790420681d00c890841e00b15640c1e0300348048200c480c0000c03c40d60800b01d0061092105400c0416807031301400310301881140181c005018103038010703401d42d40140d29020480741504450b00300100540145840c0c525140391081c03105c503146200c1d071080300b0281c0540e100c050084c0c44995045894942800c460f039503c2c0501400031505001c20b10000302c10800640081c4000d081c000075030458041d02c28085013200408000070016901c40c0f105440c801d9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 650145000 1250 650143750 650143757
    0x2011d0715030f11190206070905040e0f0f0105010816051e06210a050105041406010f050d0204080a0302070602030310051c020909100e030702030a0f05160315050c0a0503040201 78
    0x2014881d41c2500a0724810103460240c6040c0621032132542d0000c0007a1001c0e2140491702c01c0c2d44802d03010706985461047d100d890019481c0c090502440c04c150304003251a0460b281194482590b500109040038007021100034a80d44070001000b02010420901d441e80010300300b80491549404002440381c01e80a14030421800786808200303c9994200c2502c02210109071b08181c092648040054078440072204142c00030300d001c00116003410305100e0b01c4038070000300001000c6c6441d9000151403890512460204000d0f0030090100c500401d0b0011b44010b050400003032004511500d0080e04103c0c09801c241e046601c203108000c1605500700d401c00858a05413103620302a84c42c00e03415440304106110280d000814001400b141160004030003140d10921032041113100d80f0946420b80b64414000d029505911908111000c81c4880c008606401d2103032088820049209e544541c2201581c0d01c241c5202c60000700480340410360b8000e09a116a0041c101c80c40d1104089010f41203000203000681003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 650146250 1250 650145000 650145029
    0x1505060f12070233010b04060e010e0411160b01060f120c12111801020c010c110604080115060323040f02130608100b04060602190503040509041202011d07 68
    0x1500d0003030040b41104c10340016040000711020940c0c021030b8120382100d4078032054003000024a0126a801e13201520402e42d1281c2e1205148001110855903003082a45d2280e17580c0c80c91042c00030480000d220000000f03607180b0b2406541d0030715101c0c44c1016031103001448180246015003942c820350100b00c01050300000103030743c0f456000444021029950850655141540c1c0050a450400107031045256094000c0743e2201d840700126200ea408801c458007142800d8041c3d400607542d00303814190600c1c050700c074600349a61480d606080d110f02000c442415542070400744601e07903250041d10f42500d110352510920484054047c0d05c1e84d40010406000c0e040940049000c550398058140300f4038020303040038002503450340c500302e480c5c000c040107131101189411803190050030f0074020501210303100e40142408101d980141c4803034080d420b0f4100c803540170400c000b04950780c0b07801c85507009600030075034078100802d1014080d00311181403491404000f0001c5a9640304140043d0301400d5805a0380003400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 650147500 1250 650146250 650146261
    0x111602090406063f021e151902060f1506071b082401081b0a0b0301031505150d0213090203010e0303040b100e0a0903140307031505060f12 61
    0xb80b00b5908101c44580041c003881d4080e203426003004131880200114000301c5614140307507541c144440e590007034104100e1040031b000380e1640720740b0421019020f0400003900141802000b041c1c1d01007854280305009508180110703941c100b1070715601c01d25034504062a824001d40c10f41d18410450001d0788944400203210041058074139207410300c000c10185a4001c2070300c1d20807141e15a075403100c403075800d0401080d845030800342c103c402e01e0403943c00c4001703455250100401004a0210041c019801c41c2c8000c1c070018001c032002000310b000f180541c0c15203041e00c6510700c840099030400390a100e1a8101c0403071044442d0340d281c4040c0c88240c0d04880103444980c0c1c84440300c3c040c08a400000e0350552911003120940d80780840103600c620b11848402000e0350701c00c071802c04010114055510480442c0001a01c2ca030b0065224650301400b0741090311590360394219032a01580111400c1001a40f42c0e0070480400c45d9891005010700400c94250b800d104100c0c00d16a19070042c0070404030408062000301d030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 650148750 1250 650147500 650147513
    0x7050a14131706091b0616060605030f0a0305030105040b0a032108010605190c060e030a021b0604060c15090b090318060405100309060e030c0313210305180a0611011116020904 77
    0x6410039008187e0203030000e40e0341855002050b141c81164041d00440100c540c0444d004901181d05507499140d060440e402c000512006002002a83d034224040c03060200c0890500210740d41c011180304440418100c00c000000c011020690000f01406018030070902201c00000182200d0354051510603164543c6040550160403201103a401e6400001030300e401156000c01c04001d000c00c0100c0703102c0b88550030800d0002501c50340c410310001901c807282e03000009165a071103400d804010900030070010b5083d190764601020940707005401e5800040c0030300050b040d050004040c0c8070226501d034203151604000c5901160080920303c10155520140c504211059100960b20780e201e40841740c84044c1a07030007640c0c070b5003c05100b022580c2185400208450043c403400e4810508a0000b000650b1a6070281c0d074a8100304048000111021041d040e10340703078004000001c4c1602d50714000c0d80000c01c7d500c182161201e0440d400140402c10a65480c0400d005e140e40015a05a9a43e00160349508012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 650150000 1250 650148750 650148757
    0x6180e13060e0a0614010e010506070503090315071e021906090605040b0f090102040f030303020c0a0506090624030c012001291807050a14131706091b06 67
    0x781210300c0e11410200750307240002c14503105480307008200820b42e50038603546100d440c00d01ca2040800000382c014001ca04100e40a055003070710801c1182d041429040001b4103103081c01c81c0200c07041412804001c8219403115403c4418040c03840184070102070000e000351980e6204507d408500480030100e01000300d0b580c0414040781c0c0040d0204004d04080c40c0101c1c045000b602e030110400c540d4000310300e0703040061085a00311030b0f00e00320110810349195402d501942010101440e640170700030104001ca0014810320b44214040b0000c0c003100d190031103507119121040d459401c442001014540c489840000b0704402c0d00c0d1003400d0600010744200240d40d18030403085600c80d0a54240354200800f00c0342034084020040740c1808594220703001409001404030a51103940314481c0c030340301180005001d4001081c9418032071a04181c0321400031f941d050343e42c0c0400081c07244d21030011410006103212782102031002c9140030103041369041c28000c1580c2e55441074001c5680c00101200e09030f00d035a429046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 650151250 1250 650150000 650150003
    0x30b1215091615030b011e18090c09150c0c0e090a0c06090312030516180b0708030a060e06030d080903090904081306090b0f25081306180e13 62
    0x707904480b602c404112840292a19200010034180b81142409601460300c007025807200000c03030315070403031f0b6114101d54031020200c0541c1c1303903858a0000318402c0e000b80500124500543c4a07024141d19200113242c1ea40b850600b1082000485209000020044410481203548a51500310b03140c80b28000b02d8100034030088000e102c08514280040c42d070707800c28071501c00c582c02816811046101407405a040d6201100c05425002d0021180840603008101c1c5034240c1401480302c0c400143c540c1985011948815010f0303520000100401ca42c502541c0100c6001d00310342d0030065250300309100400d548104d131141c04404d10031004002216000d0800a079601c41c07d0040c030207100c83c107150503c000c0c5a1701a00341c000210301802c030003290180c001c540060071640d0720b504981c80e01c2404c501c1c050241c1c000c11b0440d5413222110b5000c030703101003410085603074060103044004c1e03a07409000e14900c20310b035041d0b001100340300c020100d4201d041d40340d9044c907044881c40c020a03955a51a04000321030440d11500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 650152500 1250 650151250 650151283
    0xa172a03061e0115090b03040501060312022803090302090c1315020f01270302010b1e1206010503100207050a0c06030507020c0603101e18020703030b121509 69
    0x100241c400011104121580601070b0780e03082c990325400410031042c1c2140c40c0ba004101c0004080260f10a0680107540c050300480c00041c0b0301d0307146d650304a82c02c0d84200142005a02a00c0048401801003003900c00d011413042c0c9079018080282c0d0f0242c0300544d5484003a10820040000800e0118107800700c91890300f08001c07200da400d44840d002e0311103a00d07008059006102d0360000c0b0311040300501c524907081c1606501e030081c0d400b0001c4a44818203000c03400700c00315526251103c0f036907103980f400312500c0716049044280c03403c00342c014007440c22443c0e00444070b50382c0314034010001d40c0c82c00b04000b8a600c1c11100301503900c240300c0c2001407400c0c046140041501080000001e0aa649035000b14000c405660a8602c140240d03020010f05002c1a2000045c42c1200b21080040102e90030703c0003420343c480d07645018a03c1e5034a2041c541140e040041c0845560002101410180d051081301c100c40401c4a0900c1d150300364181c0e19603100c040c01090704130010700b4808110400c40030421001c003070b48003c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 650153750 1250 650152500 650152513
    0x10911061309060305100e010903080c0d060902030a02030121030504062604050c0f030a0803240303040b0a0306060305040f0f020111010e0a0501060b0c0a1121010203060a172a03 78
    0x14015986c0e904180e007000c003281c03800c1007100902c2c2045c0110301c442d41e0541d0b14112152904444d050044d40550340240c0341d56a5400e0019000c00e040c00503511900c04c1213030040e1079615140c5041e9950f040b0140c44204030180180200020742c10100b95400ea528518103c01d01104002c52005000551400d00b2500c0084000700000c210000400a54620007550706540301170010041c19aa0001644000c04441082c00006e442d41c0217101d003003006010000500d5a25000c41c40130904550160300a000040e01c0001e00b495415010300521005105070f28040101d845e080c0c036200c1200400d24801042804040100029a84650881c9803030180984c000c1011010580d04295035031203880b8115029403c1c00750010f00c1e000c90700255100d080c05030015000350051a69103a41c1e802c03d40308580d13800100c1d01c000018003020b0000f54482c02510000040e600d0034035a0412844041681c01701c003648140c1d4000c3d08228401150b002425040b0000301c0941d0f503040d40f00401118890362640750140b2806 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 650155000 1250 650153750 650153753
    0x120f0304110a0b0406081f0e0f0705040506091903081605121e130b0403030906120509100209030114090303060a06030504030206040b061801060203030709080109110613090603 77
    0x1002140aa4030905080004010240a110050b90207226185510b00240401c004a5001784a110741c844c403055a8400741000c68080d0211550003a0058691401c018080003002580c1124140d041282e60a00c00c2c00c1c03501c0c0c0700000d5641c0c8540c2c200d2a00803a84a400382c04440907503545a8040d541c40403074207865a40040382902c450744414401d0700ca034030403682181c010f0480d4804a41c40500c60604d280c0080d103042008004c95400080e16070180c5400f00e800082c211001070103400918400d9071015030517498100002d0001c0100f0013101c080d107150406119104c00c3c002051000b40c0c07481c402c0507885117200030000f40109520b9540300800044c080800c45440c0020000b540f0801b01200c110101d00c0e1210801c504843d070844000340941e0120b00403501107409220320311b0b403080c2c0c024000c1c2114542caa00011000d4001c1e4007030341c003590011043c4490349810003160005040f040c0000c0010308030544900c189413907404041070183e00c2c005052410400502520300160810030828480305507207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 650156250 1250 650155000 650155027
    0x13031211101506090308071403070c1203081f0303030e121c2313140a030806030706050f120a0204170f06072f19060911030114010b07030212 62
    0x4154920b8160600100045852805008610203072a00f0610301400c101050303841c455804081e40d14140c09200038000d13580014480ca4280c00078001000200c902c5100790f05e0064400400500104402c818812000381000c6841403000212501481c0200b8164090300e000e030704011000400003000c07800040c159401d8040240815030110b0400000c001c2c00c650681c90341c410360444840f101c0511002d2010414a0803520390300b0481c54003801c610b030700800402020030724140180e8011008070b50075a0410040745802d0085200504180c10454506881990307218541e104a0081c05100c0342e6213400300343c4805055041c1d401800280c41144403496180c6400340c0d55842401d0320703a000380f0400f000035070010300c540b10300d00240341c1d080002030320740e41070b280e000700c0c3c0790020008ca09052040003802d40c001c440309406011551702078200020f004000c0e007002c2525280c01c00c40d40c1c0c02681000a99450180c140280e81c3c119420884040e4a0718480d14040b0709010312050340043c100000304107181000d14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 650157500 1250 650156250 650156261
    0x10050411030613060807141f17060603010810021b060405031e091f030f020313050f060609041202070e01150305060a0b0a140405040c021f021303121110 67
    0x4032640030343c400d100c80c2c010341aa0218080e194068000a1042051103c0051290000e410040266000700c9407581c4a28030f080110700950000b8120b030a030420700e1010005a0341d0040ba0aa035000d29541c10b0804650303944401d80900400305900003107481080001e680391441e21041a0161106401d060910541d42d822800072001d00b82c0d80a000b106603407141c1d404a0f01000b10160103940c03200141c2d8401003800b503c080c0c2c61000d05485820700d4010100f00c1c40110301c0742c0d50b858501400d00610f818194600701d071410080d00598068024000e65903210b8001c198441c0e40030562100710800c025049040c160280d110a410026000000c40d1050b541e8101240c003151759503040000350744031002c12541c107030700c1e00c40c0041d070100805c003c01c18280324030806800c0c440d01c684460f1500796150085030031a1a201c84000058001d94101401c02104201840000040c51010f42c100000300036101025a103a00c0014502c103c818001e82855015040780c8c0780e1107458000351409540c0003c0c41402410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 650158750 1250 650157500 650157511
    0x2220e0106090c0809061b0a12320c0706020c0307060e0304090e06070c031101060519080c061903180f1a06100219020d2018090606091005041103 64
    0x44c126000241c002d8800151039200e40300d100710715506070040320301c0c0f00540d40c040c030030754800c20820320050840a0401d004540400a000030b0740c079041c400240310743c0d41c0043d0401d210001c50401b02d0500038800d42010a036032126401000041c1e60b2428001c00c0d518500c83e031240107001c00c2c105414503e000b113010014104481c194441407003054034005015446400446000c0c010a40000b0890301181c4107524040c42048084000945140c607000000d270594000070764120076640c900400c0c040e000062080d6000390b5401c0c3c804505016201d011031038541c0d4211b0782d100c10196284000b03581340c518949204140b41c0c0021003c141001b4500b4014500800c42088025101d050720100f030341410280c0f8010a07400044d800340c684c0300324080c5402840d00c181d44080c1d1b8072550f00d81003100070a603807403802c103040540c0c410444240c01003001840320142c046180301c800c1383c0e5400201301a080b000300e041513000a0407591044150756500c034a4028488036009550807502d000c1d600603418499070015801003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 650160000 1250 650158750 650158757
    0x20c13060e0c0c01151d2809060e0303060303070602070f0215090901050f0a14030a1a07090503010908070f06140a0f1b0c15020d0c032702220e0106090c 67
    0x4000400d0b4462170000c0700c1c4500d609800d030800307102040c450800800c0d90000c0d83c240b0113200e1003000a44481c0740d0010b02c0306c031030041c654a0380618200100d41c42205090003848001d1420f500c1d00500080e100e0040c85c00c003504036600041c0311002c0006521510380c1782540184100204905505c0160b0740f5044001e48078065011a03002069034507015040c8018080010302c02140795040120000c3c1d6440000720483d0944203030361001307000560000351081021241c0400301d0342480d2558009000340c825038800b42c02645001c402102240220b8200d8203a9030300050951154141480d0820041541203d900c80245101060000d110b00d103800021440109210074414a0516040c2c001c6903245075030f180b00800e4580030b10f00006402404000c80c2c26580590060814800c41c0540060b1104603114400103940d5017000018030b030002104010700c0c4200c41c10b540d00c40a8903404900120546c4801c00d2000d15010801000b4810940100303500d41030300002401426980e6016402500c000000e18012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 650161250 1250 650160000 650160011
    0x1d090703090203300702060f120609220b151003020901021e0c0405040807060501090915020c0618030702120a03080906040308070c020a03060510030b0115020c13060e0c0c01 76
    0x14203124280c04080242c040d200496603040f0300c9100131465100179800c90b040803061080c4070340440c03180e018080400e24071a0380b50282c0b500400300020214000e24a0424901c90841075480314a21042e1000b81c0354810b00d401c0e8642c0f02d02c2c080c0f0711320410700b4040903489450440c41c48007003940f54004e03080003807083e000c844c0d21210307000b020b14411009040400c1e0680c008642e0b000c4c02c1c40c007504000c1e081030064070007624000031500d03644183d03007007604004d00c0161a90b0b000410400040110b0b030f907806030039208509119a0380101621444050050b0710100840d40c904201e80c0c00c01c0c0100c03500f080c0c0c0100324101e0a601e00b1101a01c415a000040e804200b2920008640c0c5002240c5140b1860341a946ca074440c0e80c40c06000c2d581d210789400141e0704825200c00110024440b4072a0341e018018038151a02041d14528010426070f4058102072141001c80018035900c43d00011102ca02440840b0f4108003403c00703804030002841950b01c06900c1c685003c0034040c945400000a00c41003110b48003d004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 650162500 1250 650161250 650161273
    0x828110d0f062705060d020a0e15040b06030402010e150a0201060513090503030f0c040909030804060b030f12070204200c0f0d08010314100515010e03010608030a1d090703090203 78
    0x1d8014140d0844184043c0444101a4007041036001c69408403009046000600c3d181d004640525a580c120003846031101082c13116070481d24420921520041718107000b40c20b08500072500b03034000500f00905005030b50419000c03550f11400088070344c941800d54a40c03102c08000d0001d0103000c0c0792103035031300414140034135284200d0039005090307540350404002d43c44c684401200e03521b0203100900801c4511020b000110311107140380218030006000c1e5803039072034604050420074100c40080503180d20a9201e40e0314440400f0700401c900a403510880c000c9525003c0782d0020601074a825017004803061509000491900710ec440680360902c001c1d01100c40d45100d8580066441c505000d0304400b007001200100001001d89aaa0300c9240c9000c1c1640c05a80601103684250340741520f801c1210320700d4462002180d640105038001c0118200c000307000e42490300400f44c1c1c40e0302c245082c01d010401080c03500404596640703110a80e60001510706001d81c034140f00d00130010b100c21141284280104a81c204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 650163750 1250 650162500 650162519
    0x140903030108030f0a230a03050f061309152a090308030c030901020d0c09061815080c04080f0c131b0f0e130504060c0828110d0f06 58
    0xa041c0c2c0d40c10b030011450004280043c0b00c03a600f1140e0703807001b00002070b01c01000c1030142c0b60401e80c1821074640c2054440103810740140644000400410700718440d20f0030024903548003030002400e00c2c400c80001500c040381e401e002c0184540074504045607802c1030752b007000d0403c80c0088000801e100d840311040058290030100c94100b400d2102400c001001c7c80462810703036440d0010b540145001000503c0c008000700807030143d505c404048004152800c00405c0104d8111043c202101c3c5082c00003803041e41805075036014600391500c021b0070004034600141c88800b4000c11074014003142c008039a5502d800c007815980d00c1c1c0c01091850301a00c2911400904050180901c000e111f00b6800c0e00e114400c28100100d0782c82c0c95070101e1500301704021041c240c998642d00318880c0300b0120340c18049210310b481d0616000f81e0740e02d604c1d0001000120410440d00450f2103200080144a0b01c0340b800812501d891840b000c0d224880300a0040c041c006240e880c18112a406160034101011080c01607944d18000d80c3e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 650165000 1250 650163750 650163757
    0x501080601110307020915030d031e020423040e1501091a1f180902031803030408180a05090a0e07060e0312071412070507090902010c060c030905060901140903 70
    0xb400c0980c414440c1100610701a10b03400d03400100b158181c0006d0b001c030b60001c2d25180130f01c06401c000c2659281500c000e10544004554104400b41c5c09514080c94500c1502010725014842032000c5c0b0950b075640101da80e990032110100303021000b12000c103401c2c4104140f01020a106480020380313000807103440640d01074104400500e00506102041d800503031031030070500703c3c0000740c010454882035843c0c6841200a0001c06401400001a200c5c54404c55100030300d030f4100f1181d582c0342d000f8410800003805031003c075110310180c4548e03094110511004036070021120f41280758000101d00800001144070350140c00740060007000c4594407543c451060f116035044404240c1c05401c0440c0200c900d00021005064413485404881465208281020304000e520f44502c030725814002080b50034001c0030081709000d040254420028040785900291102012860040065445000002110b8001d030700c042042d58005044d60300c6403510024040c001c5c41c16455654070040c0803404945010400800d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 650166250 1250 650165000 650165027
    0x10060506040b0702010e040c0f02060609010807270606051c050601050f0a0c0f0516090501060801030210050c0703110319021806030a08070501050a050a1e11040b040f0501080601 78
    0x124a0181803042c101d2441d801000c060341840f04403540c00c00d181d04c6034408c044809640e96240d18091100d054000d080000143c80320f0f10402c003010040c04031007004641c181c12180c0c0044010300d90741c800c80d0070400d0311038800c9800d800380345016400030701a900b0a00601d6910002c000c0f058007031031303140c074941c1c219031040c0c035010f000640a0000c07040d1040203a004141c0c04e0703802c0c1840c10844180e0342d5854130780751403410700302c07825007115054605d0400160702c40e00180104101c140181e6044c840b0041644105100c041c0c4681071400000d040240206d00300e40f01184100d0561304a5512410005c018100d079003502402031240716200d14000c80c0d80b860580d00158014540b1300d01668000c01c8544e02440508550f6150007500b2080c0b00059880005008051142d0004511407130000c55510844600601c400b142e41e0509050540e8220150160003003071500366400206c07006000c4030800117000b980c2004464040019020524002c3c101d40e290844800366500c01190713407070000444514881d80e14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 650167500 1250 650166250 650166259
    0x20a050a02090c0d060b0714060112111f0903171809060307170c03060109050103050319020c030a050a050c101202091516030801140d03080a0e0a14100605 68
    0x1410041c42c00150080d005002c0c02d000b142000c200742c00a8003182c0c5241d1001c0c1040c5400101d200420050385004010b000440c00036105940c5000341890403a00c03144401400d02544080c000c0080c0e8079803407454807400f13030315070080c4003a5000b65010f440c501c41d5001c15107510015442281050103c5411940000c044d105a41c841541c11000d001d1b0791080540a02d80c14012014041180d00040352041942c01c0c0540082c9501100d00080c18109603040e000340781021305040060011510005c21501c01004c281c10a10451049041c201d0034000091141d03a8540603081241c810711400040d1425042d007d90195069001441c1c10410410019000310b00456804400e1b203c1100b0280e0140c2010000038005202d07900e802214412a5402500010307000205800d2400502d40e00504240c0034124401000c04141d14080001d01e10417502c02c00241089641000078a00c00425080b200f4100d84000c21561048140d190007211a910284240164850401c0c120740380400d0303018000440e40e0140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 650168750 1250 650167500 650167513
    0x8160c0807361433090a09140a05100c0c0f0c05131d0703080315030a080409020a0212070305040e0a200904060e06031c09150e010e01020a05 62
    0x1500720022500d800c004600c1510800b118800003186002d62071600381900040c2000745841c0c4c415041c3c82503c50202e05003440800102c08001401801003608040102c60305011030390b400000308007070083c01030010401c040c0914032071401000011108402489901581e21032541022404100c65804545000042a5884074004190103d025846d074038010001850b8950301e62021841d54002c0301000c00c0040c0d035407151440c042011210740070310201c00038060281e10f0b1031a00c500d6040d0102034110083c0c24203100e440a41c07a5800c01115441d203500c510b92a0300c1d80d42d0340000d140290850f104540150040100d161540c141e48022500543c0d41034a8087c10700c0d0074643c0501100d080104489003640d07490030b8083c0c1d8089240c1d040358000041380441503840c4051424807080e1100c551102c5c400c200c21005001035130790003042c0e0106a0300c20b0484240d400e034042104a5110345581c0c0521502100700c100300c1b2382558040720350803a0003c01e8842c110b84003c203c004a030f9520b00220b02804507001007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 650170000 1250 650168750 650168789
    0xf02030402100e030a1218060c0201020a02190503011122060804240219142d0915030603010b0a06080a11090415231507020d08160c0807 60
    0x1904040010f002c00740c100c81e012405941d801c5644c070981c5402601041c0041401c10b564400320841001424030343c907060499042e198000313907070b60f2034082d0000e11540c2596505902c1880c41071036540180343c018000e000703118007034107152065488030321100e250320030036a010318081100c080f0103001c171882c41d6101007155031182c8626101c0c070418000d43e001040d0203108042e41580c0d0340040c0c1040075407022000250720140ba006440e034640c2d120a091044414801000700304604604140030f060101c0d040d20000320800c00700b05a80c854111350716800b5075a0603090040c1d00d038407005148654401d800810a0b030f0440410000400e48602c82c0350000782c2d5000014040c48503640246a1090325011610b0034030b034020000405441000c4010704011044d540b0030080c040311910300b00c0040e0f8000b0109075120700c442c0d010030400a50b24800241003200001c40c20215102c18401071000c60700700c000300d41c83c2c005211403007210706003c1006988c1d100c00c00e48080385588011801d40122000d5140704c040740d0340700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 650171250 1250 650170000 650170007
    0xf050627130c0909030f0809190f080702180114060f2a0f0a170315011112030a0f0b0316050103090201091509061107051818100f0f0203040210 63
    0x25540211a01003035070400085084860081c02004d9110792942c00384460308840040c060b220040c00900341d648a000a030019120007402d00c1c250a400c824100385400243c04d0580c030920071200025008078940b642003203007601a00c6558180c1d00c03010340c0c01149848060412541d4010403100c54912a810411030341c84085500760803103004202c0240c83c100015100e1042e003441c400ca45120501e0704800102c00c20400c0b99007020725403100c8407104904508000300140090010481000c0c18040011040800101c0c01c200d911560705002d44110707960700d044c1100401602260405072501400c1c01c122074030614010500d401c091250381c44030306040e4904001100501003001c0140c0c18801c2402c07003c240713040114400241d1544545860103403d1030100d00910000f403150382010b0941180b10184070030b40d00c009030b0101141300220801c0040d00c50314080e10780f2a40075003110b0350900c580200b584469100e03400070840003116034001c100045002d820181a03100888000354412110a49004190301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 650172500 1250 650171250 650171281
    0x5090f04020418050606040f1a151905040e01080105060f040f0603020d080405030d0903030c1101141207080c09030a0f060e07090b0a09060311220f050627 68
    0xc0c004a442050007801c07808007820f42c6801d03903544d0400410003010781484c0c001d4080c4003005000400009540081d68154407040c840703a00c0c402c2001c4012201d0010040080d80c03441c2200c0210324603205160f09000c1c000c0c5e88180f00f404503041861300000740401044c401da84c400c031405482c202c0b1604960f01040010905000d2f00c000550356180b020016890345114125040d11a8240a03529400d1004044c40d0100e0720780c0840800444110034400640c1c00207031408155070190f03040c00a06111001610019943c0300da00114400101c7c203183c41d104034948041c05442c80d41c881e501641c80720300c20801d0510071101204d40541c000b02c451000107003d00a42095035004590004802e0303410b40d24503040010340d5009089064035040203460030300c0d10b000700b00c0c0207000001042102c0c03455652641c1071300003034003209403095080302410303c2c00e1600c040401e0058510141d04000c421215403000000700310580f0b55601130300d108548a05149203031402003980304245041c0503500c0e940d428000d040e8a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 650173750 1250 650172500 650172503
    0x717090d020607030c0c140f0a0b0f0609091e010605060f030709090e030f07080909131e150b130e0d020705030334050106030f12031505010c0309080609031c0605090f04 74
    0x20848c0001c0002030810f020040443d031256004001a00b070020302420481e10191941d032080d09504140620001e00051026848002c000f02800a107905424180184000e6001ca5080b0f02d00168a654003d00d000043d8428811a124040c0c000d446151400031030f22421900121503204005a1144a0548024016051084402038907040c105008105002429038042c17030051200d000350740c200700b03160740d03010021a5041e2208000300029118440d0300902e0001c480c541590701c88800f905600c81c91310001c5001c401030024800c01d900c40720394550302e0180b1020b13900140102d060100b03003071a020007140c800120342d5100c108503a940903c844501e03140080a120011070b205d00802c005882030003250021806480250002e800504100302d01014084400302050302c2c00b20301102807461001f040058070800c1c40c002c560110149810360f41d10103140c010b001d140c80340a0400c424a04000020081e040b000307030002c0e080780741c21640c001c01d59041e03006040d44680d038080000c05070f0702d480c0c0407694007030b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 650175000 1250 650173750 650173753
    0x3120f050c160c0f09090c08010515100e04090309060e030c030d08100f03050303071409130b010315171516030b010e1314010506070803010e0717090d020607030c0c14 73
    0x43d5900d03051512150015407101341e04580310003160060001c0009604000d02803000280030501d41644090442c50001d01c0d0140b1802070440c103c240107118054940a0b8400540100304880240c200504500c103507200380400203c1c501761001c15030078042044018040301500030217016100f95415a4000c900400d0001c0300b04103660001145094030320007000540c0104081c4d03641c1d0401500080c81261511000d100410b0700f000240140c0c0c0f42c4c50303002454492810b4000500800480040f4007030091082e1207c000350349800c000c40c01c002c1c0030b04500c912445120860703ea041d40c13121a000d6902044805450381d800480c440d41659002ea0040d051203c4145000c1085099040000303101036000c400c0040301c1503a805904410406851850340900800c4231224109803880e03a90300c000c1c0c8814000c2800501d084400714510743d02a00703d81c0120409044404c80d28940303202087c0d9183c4123408544010710403040405d40c5280a44981c00c500700842c2e6405030003813804e454080d01140c8251501445 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 650176250 1250 650175000 650175023
    0x509041a0901030305220302060a03050c16060f050601030c0c171c021b07151d0907020f0114040c051c05060a1e050c07030c0c0302040903120f050c16 66
    0x4507503424456a000e1803003500d403140c03034044407141d101c0b1012411801740102c000c690700500143e5122419074620f00103616020800e6620100035020071300520f2000d442395580010340d4410030100742c0181c165000c3d2035408100703503134840d4011070582c0c2840010001003041180c0e6800861413504411120312440d0103000d241440d0307056030100c0c46004c5040f13100e0b0664046000380008001181803441030f03240b84010b1182a050a40d403006c00500d10514034180104100c885074084a0002040304c5010024500d64051030503000194542542006180c010351030300343e0040c00181030900850099800070682d08405080c803081c003020420010003401060210308190000a10801c82584514000140414040720849031001d04481d154070900909040008000c2103e07000003c0d41e4207241c161604088500d42820001c1441c8440d0f00040e40050804080005041d0829800b040f0a100d0f514100301c00029241c030641118010340d026001d001040143c01c200c0c000d18481003030098014201d4400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 650177500 1250 650176250 650176301
    0x317030a020c0a06090204150e010920120702070e0f0703020c0c03101b1d0922060209120f1209060d050f2a0f0f070501180606060c03050904 62
    0x240c621401800c580594480084901b1800c00340a03030003c178200076480300e80c41814039003c01101401400368845180c2e031481000b03000304080801d000c1586140000e241d60f140c0c2501004200b0302d0484181e40588a84540000d03070b03801e4080070910440035299400b510740c994400c12400fa40c072003104d01007184119200d014055900344425901948580300005514105001110191860319506418841d00c10700312212041d200c0081c1030504400c403400741060746e507824585030a1a28820319643d4030340c819004420045954000c1080a030308550b205007007034001401a9503400302c1e03408a10345420548420035031a100300041c0281450003000141040c03a0500c4900c01c5030000c031011207182041c0300920180505558000c145c488c40100781c801c4044013841c54512a00c584e590142d54001c3c0050b40c502031800c21410303500308685c0b060007880703c2c0b28030064030004084041800d0790714529000700050810b00800101031115856200ca5042544000400c002000e4286146a104404210511 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 650178750 1250 650177500 650177503
    0x71d010509180906090c010201020a1e0c120203040614090127050d031e08010e0408030a2d0b0105041202010309081e0304060506040908040510140a0201020406080f010317030a020c 79
    0x500c561066001131026140078110185880c101d52089415039104001c44a01e03d0ba005903c05031240645136405a0b1844d2004116051081c2880c0a003504002000340b40c0400c0d40440244112942e560340c240c048503010088010920940180c1c9011820742041500b510004416183c1c80710910380850744416a1030001c41c09012004408800180c4999a0802d0b5801050103840090960703150004207903042002c000303407102025001404081d400300c001403203601103070846a604007510b850343d82820a070071804501d039812102ca8107030071030030030a43e420b255200e1001d0f0780884a9181c5d07602c1d411112500150001c01314a003096600100400c5803e44413000700c41a8070100584152482d0b036840e15003484802c9541c0a002c091103181400c4071342d0302180400341582c040d10421681030105c9a04031406562600b640341d030307003505240082400301c011a01907000d881115556295414556940070b1a50380e0b0300000d0100a0540c410318901c00844502c0310301540d8480c40b520001482c204d030b04a0a01d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 650179856 1106 650178750 650178799
    0x1030212030903100b100305040804061b020d051515030c04180b0c1c0b0904081606020301141c110f03161d071d010509 53
    0x25044140240308889038042c00508031150000b90400540c0605603500c50700748074182e044039030400c1e28080d0240500c20f80e0300c101c000d0b1901c0d09015042c0c070b5081201c980640801d01c440300000060b1150b50201d00018020401052141319400111b544004010100c51804000d4007100116403030006c0d080080031000c43e008070300c142d40da0f124039001c0070041c403001e0541c40c020824040c07503000d144004c0c0b030350643d0303414800e003803601d09521501950503942c0400c2e0046400800280031031440400341c03003c14000049088111801d40700c11003039030030031382240641c83c9203407940d01d0303492815102042010341d04030302c0d203403488032070b0341721802c00341d003030f2070f410360080542105124099809111034201e41042e440c407810700c207407610105040e0301d1424042854881100001c1a1007500072114908200e54004078200a540c00000444441d00000c066a400c011245003400c090500c8039034a = true := by decide +kernel

theorem cover : BRFrame.Cov 650000000 650179856 := by
  have h0 := BRFrame.cov_init 650000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 650000000 ≤ n) (h2 : n < 650179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
